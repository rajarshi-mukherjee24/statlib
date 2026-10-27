/-
Copyright (c) 2026 Rajarshi Mukherjee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rajarshi Mukherjee
-/
module

public import Statlib.Testing.NeymanPearson
public import TestingLowerBounds.Testing.Binary

/-!
# The sum-of-errors minimax risk is the Bayes risk of binary testing

This file connects the Neyman–Pearson development in `Statlib.Testing` to the
statistical-decision-theory development in Rémy Degenne's `TestingLowerBounds`
library.

The sum-of-errors objective `errSum P Q t T = ∫⁻ T dP + t · ∫⁻ (1 - T) dQ` is,
after identifying a randomized test `T : Ω → [0,1]` with the Markov kernel
`Ω → Bool` sending `ω` to `Bool.boolMeasure (1 - T ω) (T ω)` (reject with
probability `T ω`), exactly the Bayes objective of the simple binary hypothesis
testing problem `{P, Q}` under the prior `Bool.boolMeasure 1 t` (mass `1` on the
null, `t` on the alternative). Hence the least achievable sum of errors over all
randomized tests is `ProbabilityTheory.bayesBinaryRisk P Q` at that prior.

## Main definitions

* `Statlib.Testing.minimaxRiskAt` — `⨅ φ : Test Ω, errSum P Q t φ`, the least
  achievable sum of errors over all randomized tests, at weight `t`.
* `Statlib.Testing.kernelOfTest` — the Markov kernel `Ω → Bool` associated to a test.

## Main results

* `Statlib.Testing.errSum_indicator` — the sum of errors of the indicator test of a
  rejection region `E` is `P E + t · Q Eᶜ`.
* `Statlib.Testing.minimaxRiskAt_le_bayesBinaryRisk` and
  `Statlib.Testing.bayesBinaryRisk_le_errSum` — the two inequalities.
* `Statlib.Testing.minimaxRiskAt_eq_bayesBinaryRisk` — for `t ≠ ∞`,
  `⨅_φ errSum P Q t φ = bayesBinaryRisk P Q (boolMeasure 1 t)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory ENNReal

namespace Statlib.Testing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **two-point minimax risk at weight `t`**: the least achievable sum of the two
error probabilities over all randomized tests `φ : Test Ω`. At `t = 1` this is the
Bayes risk of the symmetric two-point problem `= 1 - TV(P, Q)`. -/
noncomputable def minimaxRiskAt (P Q : Measure Ω) (t : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ φ : Test Ω, errSum P Q t φ.toFun

/-- The sum of errors of the **indicator test** of a measurable rejection region `E`:
reject (output `1`) exactly on `E`. Its Type I error is `P E` and its Type II error is
`Q Eᶜ`, so `errSum P Q t 𝟙_E = P E + t · Q Eᶜ` — the summand minimized in Rémy's
`bayesBinaryRisk_eq_iInf_measurableSet`. -/
lemma errSum_indicator (P Q : Measure Ω) (t : ℝ≥0∞) {E : Set Ω} (hE : MeasurableSet E) :
    errSum P Q t (E.indicator (1 : Ω → ℝ≥0∞)) = P E + t * Q Eᶜ := by
  have hcompl : (fun ω => 1 - E.indicator (1 : Ω → ℝ≥0∞) ω)
      = Eᶜ.indicator (1 : Ω → ℝ≥0∞) := by
    ext ω; by_cases h : ω ∈ E <;> simp [Set.indicator, h]
  rw [errSum, lintegral_indicator_one hE, hcompl, lintegral_indicator_one hE.compl]

/-- The indicator test of a measurable set, bundled as a `Test`. -/
noncomputable def indicatorTest {E : Set Ω} (hE : MeasurableSet E) : Test Ω where
  toFun := E.indicator (1 : Ω → ℝ≥0∞)
  measurable := measurable_const.indicator hE
  le_one ω := by by_cases h : ω ∈ E <;> simp [Set.indicator, h]

/-- **Upper bound via deterministic tests.** The randomized minimax risk is at most the
Bayes binary risk: every measurable rejection region gives an indicator test whose sum of
errors is the corresponding summand of `bayesBinaryRisk_eq_iInf_measurableSet`. -/
lemma minimaxRiskAt_le_bayesBinaryRisk (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (t : ℝ≥0∞) (ht : t ≠ ⊤) :
    minimaxRiskAt P Q t ≤ bayesBinaryRisk P Q (Bool.boolMeasure 1 t) := by
  have : IsFiniteMeasure (Bool.boolMeasure (1 : ℝ≥0∞) t) := by
    refine ⟨?_⟩
    simp only [Bool.boolMeasure, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      Measure.dirac_apply, smul_eq_mul]
    exact (ENNReal.add_lt_top.2 ⟨by simp, by simp [lt_top_iff_ne_top, ht]⟩)
  rw [bayesBinaryRisk_eq_iInf_measurableSet]
  simp only [Bool.boolMeasure_apply_false, Bool.boolMeasure_apply_true, one_mul]
  refine le_iInf fun E => le_iInf fun hE => ?_
  calc minimaxRiskAt P Q t
      ≤ errSum P Q t (indicatorTest hE).toFun := iInf_le _ (indicatorTest hE)
    _ = P E + t * Q Eᶜ := errSum_indicator P Q t hE

/-! ### The randomized test as a Markov kernel to `Bool`, and the reverse bound -/

/-- The **Markov kernel associated to a randomized test** `φ`: at `ω` it outputs `true`
(reject) with probability `φ ω` and `false` (accept) with probability `1 - φ ω`. This is the
identification under which `errSum` becomes Rémy's Bayes objective. -/
noncomputable def kernelOfTest (φ : Ω → ℝ≥0∞) (hφ : Measurable φ) : Kernel Ω Bool where
  toFun ω := Bool.boolMeasure (1 - φ ω) (φ ω)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Bool.boolMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact ((hφ.const_sub 1).mul_const _).add (hφ.mul_const _)

@[simp] lemma kernelOfTest_apply (φ : Ω → ℝ≥0∞) (hφ : Measurable φ) (ω : Ω) :
    kernelOfTest φ hφ ω = Bool.boolMeasure (1 - φ ω) (φ ω) := rfl

/-- `kernelOfTest φ` is a Markov kernel when `φ` is `[0,1]`-valued. -/
lemma isMarkovKernel_kernelOfTest {φ : Ω → ℝ≥0∞} (hφ : Measurable φ) (hφ1 : ∀ ω, φ ω ≤ 1) :
    IsMarkovKernel (kernelOfTest φ hφ) := by
  refine ⟨fun ω => ⟨?_⟩⟩
  simp only [kernelOfTest_apply, Bool.boolMeasure, Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, measure_univ, mul_one]
  exact tsub_add_cancel_of_le (hφ1 ω)

/-- Pushing `kernelOfTest φ` through `μ`, the mass on `true` is the Type I-style integral
`∫⁻ φ dμ`. -/
lemma kernelOfTest_comp_apply_true (μ : Measure Ω) {φ : Ω → ℝ≥0∞} (hφ : Measurable φ) :
    (kernelOfTest φ hφ ∘ₘ μ) {true} = ∫⁻ ω, φ ω ∂μ := by
  rw [Measure.bind_apply (measurableSet_singleton _) (Kernel.measurable _).aemeasurable]
  simp [Bool.boolMeasure]

/-- Pushing `kernelOfTest φ` through `μ`, the mass on `false` is the Type II-style integral
`∫⁻ (1 - φ) dμ`. -/
lemma kernelOfTest_comp_apply_false (μ : Measure Ω) {φ : Ω → ℝ≥0∞} (hφ : Measurable φ) :
    (kernelOfTest φ hφ ∘ₘ μ) {false} = ∫⁻ ω, (1 - φ ω) ∂μ := by
  rw [Measure.bind_apply (measurableSet_singleton _) (Kernel.measurable _).aemeasurable]
  simp [Bool.boolMeasure]

/-- **Lower bound via the kernel identification.** For every randomized test `φ`, the Bayes
binary risk is at most its sum of errors — because `φ`'s kernel realizes that objective. -/
lemma bayesBinaryRisk_le_errSum (P Q : Measure Ω) (t : ℝ≥0∞) (φ : Test Ω) :
    bayesBinaryRisk P Q (Bool.boolMeasure 1 t) ≤ errSum P Q t φ.toFun := by
  rw [bayesBinaryRisk_eq]
  simp only [Bool.boolMeasure_apply_false, Bool.boolMeasure_apply_true, one_mul]
  calc ⨅ (κ : Kernel Ω Bool) (_ : IsMarkovKernel κ),
          t * (κ ∘ₘ Q) {false} + (κ ∘ₘ P) {true}
      ≤ t * (kernelOfTest φ.toFun φ.measurable ∘ₘ Q) {false}
          + (kernelOfTest φ.toFun φ.measurable ∘ₘ P) {true} :=
        iInf₂_le (kernelOfTest φ.toFun φ.measurable)
          (isMarkovKernel_kernelOfTest φ.measurable φ.le_one)
    _ = errSum P Q t φ.toFun := by
        rw [kernelOfTest_comp_apply_false, kernelOfTest_comp_apply_true, errSum, add_comm]

/-- **The two-point minimax risk is Rémy Degenne's Bayes binary risk.** For `t ≠ ∞`, the least
sum of errors over all randomized tests equals the Bayes risk of the simple binary hypothesis
testing problem `{P, Q}` under the prior `boolMeasure 1 t`:
`⨅_φ errSum P Q t φ = bayesBinaryRisk P Q (boolMeasure 1 t)`. -/
theorem minimaxRiskAt_eq_bayesBinaryRisk (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (t : ℝ≥0∞) (ht : t ≠ ⊤) :
    minimaxRiskAt P Q t = bayesBinaryRisk P Q (Bool.boolMeasure 1 t) :=
  le_antisymm (minimaxRiskAt_le_bayesBinaryRisk P Q t ht)
    (le_iInf fun φ => bayesBinaryRisk_le_errSum P Q t φ)

end Statlib.Testing
