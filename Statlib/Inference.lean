/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

module

public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Decision.Risk.Defs

/-!
# Statistical Inference

This file records the first Lean interface for the decision-theoretic
setup used in the tutorial chapter.
-/

@[expose] public section

open scoped ENNReal Topology

open MeasureTheory ProbabilityTheory Filter

-- ANCHOR: inferenceModelofMeasure
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
-- ANCHOR_END: inferenceModelofMeasure

namespace InferenceModelofMeasure

variable {ι : Type*} {Ω S X Y : ι → Type} [∀ i, MeasurableSpace (Ω i)]
  [∀ i, MeasurableSpace (S i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, MeasurableSpace (Y i)]

-- ANCHOR: measureConditionalRisk
noncomputable def conditionalRisk (I : InferenceModelofMeasure ι Ω S X Y) {i : ι}
    {μ : Measure (Ω i)} (hμ : μ ∈ I.domain i) : ℝ≥0∞ :=
  ∫⁻ ω : Ω i, ∫⁻ y : Y i,
    I.loss_function i y (I.functional i ⟨μ, hμ⟩) ∂(I.decision_rule i) (I.data i ω) ∂μ
-- ANCHOR_END: measureConditionalRisk

-- ANCHOR: measureConsistencyPredicates
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
-- ANCHOR_END: measureConsistencyPredicates

end InferenceModelofMeasure

/-- Each measure induces a constant kernel. -/
def ProbabilityTheory.Kernel.of_measure (θ : Type*) {Ω : Type*} [MeasurableSpace θ]
    [MeasurableSpace Ω] (μ : Measure Ω) : Kernel θ Ω where
  toFun := fun _ => μ
  measurable' := measurable_const

instance (θ Ω : Type*) [MeasurableSpace θ] [MeasurableSpace Ω] :
    MeasurableSpace (Kernel θ Ω) :=
  ⨆ (t : θ), Measure.instMeasurableSpace.comap fun κ => κ t

-- ANCHOR: inferenceModelofKernel
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
-- ANCHOR_END: inferenceModelofKernel

namespace InferenceModelofKernel

variable {ι : Type*} {θ Ω S X Y : ι → Type} [∀ i, MeasurableSpace (θ i)]
  [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (S i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]

-- ANCHOR: measureToKernelTodo
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
-- ANCHOR_END: measureToKernelTodo

-- ANCHOR: kernelConditionalRisk
noncomputable def conditionalRisk (I : InferenceModelofKernel ι θ Ω S X Y) {i : ι}
    (t : θ i) {κ : Kernel (θ i) (Ω i)} (hκ : κ ∈ I.domain i) : ℝ≥0∞ :=
  ∫⁻ ω : Ω i, ∫⁻ y : Y i,
    I.loss_function i y (I.functional i ⟨κ, hκ⟩) ∂(I.decision_rule i) (I.data i ω) ∂κ t
-- ANCHOR_END: kernelConditionalRisk

-- ANCHOR: kernelConsistencyPredicates
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
-- ANCHOR_END: kernelConsistencyPredicates

end InferenceModelofKernel
