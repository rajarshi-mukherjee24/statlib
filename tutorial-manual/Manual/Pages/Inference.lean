import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "../"
set_option verso.exampleModule "Statlib.Inference"

#doc (Manual) "Motivation and Background" =>
%%%
htmlSplit := .never
%%%

These tutorial notes develop a decision-theoretic setup for statistical
inference and connect the definitions to the Lean interface in
`Statlib.Inference`.

# A general setup

The chapter studies statistical inference as a sequence of decision problems.
For each $`n \ge 1`, let $`(\Omega_n,\mathcal A_n)` be a measurable space. Let
$`\mathcal X_n` be a normed vector space equipped with a sigma-algebra
$`\mathcal B_n`, and let $`\mathcal M_{\mathrm{pr},n}` be a class of probability
measures equipped with a topology $`\tau_n`. The Borel sigma-algebra on
$`\mathcal M_{\mathrm{pr},n}` is denoted $`\mathcal B_{\mathrm{pr},n}`.

Given measurable spaces $`(S_n,\mathcal F_n)` and subsets
$`\mathcal P_n \subseteq \mathcal M_{\mathrm{pr},n}`, an $`S_n`-valued
statistical functional is a measurable map
$`\Psi_n : \mathcal P_n \to S_n`.

The data are measurable maps $`X_n : \Omega_n \to \mathcal X_n`. Their
distribution is the push-forward measure $`P_n \circ X_n^{-1}` on
$`(\mathcal X_n,\mathcal B_n)`.

Given a decision space $`(\mathcal Y_n,\mathcal D_n)`, a randomized decision
rule is a Markov kernel

$$`T_n : \mathcal X_n \times \mathcal D_n \to [0,1].`

For each observation $`x_n`, $`T_n(x_n,\cdot)` is a probability measure on
$`(\mathcal Y_n,\mathcal D_n)`, and for each measurable decision event
$`D_n`, the map $`T_n(\cdot,D_n)` is measurable.

A loss function is a jointly measurable map

$$`\ell : \mathcal Y_n \times S_n \to [0,+\infty].`

The conditional loss of a rule $`T_n`, given data value $`x_n`, is

$$`\int \ell(y_n,s_n)\,dT_n(x_n,dy_n).`

The risk of estimating $`\Psi_n(P_n)` using $`T_n` applied to data $`X_n` is

$$`\operatorname{Risk}(T_n,S_n;P_n) =
   \int\!\int \ell(y_n,s_n)\,dT_n(X_n(\omega),dy_n)\,dP_n(\omega).`

This is the object formalized by `InferenceModelofMeasure.conditionalRisk`.

# Measure-indexed model in Lean

The first Lean structure takes the model class to be a set of measures. The
displayed code below is pulled from the checked Lean module.

```anchor inferenceModelofMeasure
structure InferenceModelofMeasure (ι : Type*) (Ω S X Y : ι → Type)
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (S i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)] where
  domain (i : ι) : Set (Measure (Ω i))
  functional (i : ι) : domain i → S i
  measurable_functional (i : ι) : Measurable (functional i)
  data (i : ι) : Ω i → X i
  measurable_data (i : ι) : Measurable (data i)
  decision_rule (i : ι) : Kernel (X i) (Y i)
  loss_function (i : ι) : Y i → S i → ℝ≥0∞
  measurable_loss_function (i : ι) : Measurable (loss_function i).uncurry
```

The corresponding risk is the iterated lower Lebesgue integral.

```anchor measureConditionalRisk
noncomputable def conditionalRisk (I : InferenceModelofMeasure ι Ω S X Y) {i : ι}
    {μ : Measure (Ω i)} (hμ : μ ∈ I.domain i) : ℝ≥0∞ :=
  ∫⁻ ω : Ω i, ∫⁻ y : Y i,
    I.loss_function i y (I.functional i ⟨μ, hμ⟩) ∂(I.decision_rule i) (I.data i ω) ∂μ
```

The consistency predicates then say that this risk tends to zero along a filter
on the index type.

```anchor measureConsistencyPredicates
def IsConsistent (l : Filter ι) (I : InferenceModelofMeasure ι Ω S X Y) : Prop :=
  ∀ (μ : ∀ i, Measure (Ω i)), (hμ : ∀ i, μ i ∈ I.domain i) →
    Tendsto (fun i => conditionalRisk I (hμ i)) l (𝓝 0)

def IsUniformlyConsistent (l : Filter ι) (I : InferenceModelofMeasure ι Ω S X Y) : Prop :=
  Tendsto
    (fun i =>
      ⨆ (μ : ∀ i, Measure (Ω i)),
        ⨆ (hμ : ∀ i, μ i ∈ I.domain i), conditionalRisk I (hμ i))
    l (𝓝 0)

def HasRateOfConvergence (l : Filter ι) (I : InferenceModelofMeasure ι Ω S X Y)
    (r : ι → ℝ≥0∞) : Prop :=
  0 <
      l.liminf
        (fun i =>
          (⨆ (μ : ∀ i, Measure (Ω i)),
              ⨆ (hμ : ∀ i, μ i ∈ I.domain i), conditionalRisk I (hμ i)) /
            r i) ∧
    l.limsup
        (fun i =>
          (⨆ (μ : ∀ i, Measure (Ω i)),
              ⨆ (hμ : ∀ i, μ i ∈ I.domain i), conditionalRisk I (hμ i)) /
            r i) <
      ∞
```

# Markov-kernel model

The same statistical problem can be formulated directly in terms of sample
spaces indexed by parameters. Let $`(\Theta_n,\mathcal A_n)` and
$`(\Omega_n,\mathcal G_n)` be measurable spaces, and let
$`\mathcal M_{\mathrm{mk},n}(\Theta_n \times \mathcal G_n)` be a class of
probability Markov kernels.

In this form:

* a statistical functional is a measurable map
  $`\Psi_n : \tilde{\Theta}_n \to S_n`;
* the data are measurable maps $`X_n : \Omega_n \to \mathcal X_n`;
* the conditional distribution of the data is the pushed-forward kernel
  $`K_n \circ X_n^{-1}`;
* the conditional risk at parameter $`\theta_n` is

$$`\operatorname{Risk}(T_n,S_n;K_n;\theta_n) =
   \int\!\int \ell(y_n,s_n)\,dT_n(X_n(\omega),dy_n)\,dK_n(\theta_n,d\omega).`

The corresponding Lean structure is {anchorName inferenceModelofKernel}`InferenceModelofKernel`.

```anchor inferenceModelofKernel
structure InferenceModelofKernel (ι : Type*) (θ Ω S X Y : ι → Type)
    [∀ i, MeasurableSpace (θ i)] [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, MeasurableSpace (Y i)] where
  domain (i : ι) : Set (Kernel (θ i) (Ω i))
  functional (i : ι) : domain i → S i
  measurable_functional (i : ι) : Measurable (functional i)
  data (i : ι) : Ω i → X i
  measurable_data (i : ι) : Measurable (data i)
  decision_rule (i : ι) : Kernel (X i) (Y i)
  loss_function (i : ι) : Y i → S i → ℝ≥0∞
  measurable_loss_function (i : ι) : Measurable (loss_function i).uncurry
```

The conditional risk now evaluates the model kernel at a parameter value.

```anchor kernelConditionalRisk
noncomputable def conditionalRisk (I : InferenceModelofKernel ι θ Ω S X Y) {i : ι}
    (t : θ i) {κ : Kernel (θ i) (Ω i)} (hκ : κ ∈ I.domain i) : ℝ≥0∞ :=
  ∫⁻ ω : Ω i, ∫⁻ y : Y i,
    I.loss_function i y (I.functional i ⟨κ, hκ⟩) ∂(I.decision_rule i) (I.data i ω) ∂κ t
```

# Consistency and rates

The chapter asks three basic questions.

* Does there exist $`T_n` that is pointwise consistent?
* Given $`\tilde{\mathcal P}_n \subseteq \mathcal P_n`, does there exist
  $`T_n` that is uniformly consistent over $`\tilde{\mathcal P}_n`?
* Given a candidate rate $`r_n(\tilde{\mathcal P}_n)`, does there exist a rule
  with that rate of convergence?

In Lean, the measure-indexed predicates are exactly the definitions shown
above. The kernel-indexed version has the same shape, with an explicit
parameter value.

```anchor kernelConsistencyPredicates
def IsConsistent (l : Filter ι) (I : InferenceModelofKernel ι θ Ω S X Y) : Prop :=
  ∀ (t : ∀ i, θ i) (κ : ∀ i, Kernel (θ i) (Ω i)), (hκ : ∀ i, κ i ∈ I.domain i) →
    Tendsto (fun i => conditionalRisk I (t i) (hκ i)) l (𝓝 0)

def IsUniformlyConsistent (l : Filter ι) (I : InferenceModelofKernel ι θ Ω S X Y) : Prop :=
  ∀ (t : ∀ i, θ i),
    Tendsto
      (fun i =>
        ⨆ (κ : ∀ i, Kernel (θ i) (Ω i)),
          ⨆ (hκ : ∀ i, κ i ∈ I.domain i), conditionalRisk I (t i) (hκ i))
      l (𝓝 0)
```

# Parametric models

For parametric problems, let $`\Theta_n \subseteq \mathbb R^p`. A parametric
model indexed by $`\Theta_n` is a class of Markov kernels

$$`\mathcal P_n(\Theta_n) : \Theta_n \times \mathcal A_n \to [0,1]`

such that for each $`\theta_n`, $`P_{\theta_n}` is a probability measure, and
for each measurable event $`A_n`, the function
$`\theta_n \mapsto P_{\theta_n}(A_n)` is measurable.

The product-kernel construction is the bridge from a one-observation model to
independent data. If $`K_1,\ldots,K_n` are Markov kernels on a common parameter
space and observation sigma-algebras $`\mathcal C_1,\ldots,\mathcal C_n`, the
product kernel $`K^{\otimes n}` is characterized by:

* for each parameter value, it is the product probability measure;
* for each product-measurable set, evaluation is measurable in the parameter.

This is the formal target for later chapters on i.i.d. data and parametric
models.

# Elements of asymptotic probability

Convergence in probability is introduced as:

$$`Z_n \xrightarrow{P} Z
   \quad\Longleftrightarrow\quad
   P(|Z_n-Z|>\epsilon)\to 0
   \quad\text{for every }\epsilon>0.`

Convergence in distribution is convergence of distribution functions at
continuity points of the limiting distribution.

The chapter records the law of large numbers, the central limit theorem, the
continuous mapping theorem, and the delta method as the asymptotic tools that
connect estimators, transformations, and limiting risk.

# Delta method on Euclidean space

The main theorem stated in the notes is:

*Delta method.* Suppose $`T_n` is a sequence of $`\mathbb R^d`-valued random
vectors on probability spaces $`(\Omega_n,\mathcal A_n,P_n)`, and
$`r_n \to \infty` satisfies

$$`r_n(T_n-\theta)\rightsquigarrow T.`

If $`g:\mathbb R^d\to\mathbb R^k` is differentiable at $`\theta`, then

$$`r_n(g(T_n)-g(\theta))\rightsquigarrow g'(\theta)T.`

The proof writes

$$`f(h)=
   \begin{cases}
   \dfrac{g(\theta+h)-g(\theta)-g'(\theta)h}{\|h\|}, & h\ne 0,\\
   0, & h=0,
   \end{cases}`

uses differentiability to get $`f(h)\to 0` as $`h\to 0`, applies Slutsky's
theorem to $`T_n-\theta=r_n^{-1}r_n(T_n-\theta)`, and then concludes that the
remainder term is negligible.

# Current formalization boundary

The Lean file currently formalizes the model interfaces, risk definitions,
consistency predicates, and rate predicate. The conversion from measure-indexed
models to kernel-indexed models is intentionally left as a TODO because it
requires a clean measurable-embedding story for {anchorName measureToKernelTodo}`Kernel.of_measure`.

```anchor measureToKernelTodo
def of_InferenceModelofMeasure (I : InferenceModelofMeasure ι Ω S X Y) :
    InferenceModelofKernel ι θ Ω S X Y where
  domain (i : ι) := (Kernel.of_measure (θ i)) '' (I.domain i)
  -- TODO: show `Kernel.of_measure` is a measurable embedding.
  functional (i : ι) := sorry
  measurable_functional (i : ι) := sorry
  data := I.data
  measurable_data := I.measurable_data
  decision_rule := I.decision_rule
  loss_function := I.loss_function
  measurable_loss_function := I.measurable_loss_function
```
