/-
Copyright (c) 2026 Rajarshi Mukherjee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rajarshi Mukherjee
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Auxiliary `ℝ≥0∞` and `∫⁻` lemmas for the Neyman–Pearson development

Small, general facts used across the testing files. None mention tests: they are
candidates for `ForMathlib`/mathlib.

## Main results

* `Statlib.Testing.two_min_add_absDiff` — `2·min a b + |a − b| = a + b` in `ℝ≥0∞`.
* `Statlib.Testing.sq_add_one` — `a² + 1 = |a − 1|² + 2a` (subtraction-safe χ² identity).
* `Statlib.Testing.lintegral_le_sqrt_sq` — Cauchy–Schwarz `∫ f ≤ (∫ f²)^(1/2)` for `∫⁻`.
* `Statlib.Testing.tvIdentity_of` — `∫ min(f,g) = 1 − ½ ∫ |f − g|` for unit-mass densities.
-/

@[expose] public section

open MeasureTheory ENNReal

namespace Statlib.Testing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `2·min a b + ((a − b) + (b − a)) = a + b` in `ℝ≥0∞` (`(a−b)+(b−a) = |a−b|`). -/
lemma two_min_add_absDiff (a b : ℝ≥0∞) :
    2 * min a b + ((a - b) + (b - a)) = a + b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, tsub_eq_zero_of_le h, zero_add, two_mul, add_assoc,
      add_tsub_cancel_of_le h]
  · rw [min_eq_right h, tsub_eq_zero_of_le h, add_zero, two_mul, add_assoc,
      add_tsub_cancel_of_le h, add_comm]

/-- If `2M + D = 2` with `D ≠ ⊤`, then `M = 1 − ½ D` in `ℝ≥0∞`. -/
lemma np_arith (M D : ℝ≥0∞) (hD : D ≠ ⊤) (h : 2 * M + D = 2) : M = 1 - 2⁻¹ * D := by
  have h2 : M + 2⁻¹ * D = 1 := by
    have hh : 2⁻¹ * (2 * M + D) = 2⁻¹ * 2 := by rw [h]
    rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul] at hh
    simpa using hh
  rw [← h2, ENNReal.add_sub_cancel_right (by finiteness)]

/-- Subtraction-safe χ² identity in `ℝ≥0∞`: `a² + 1 = ((a−1)+(1−a))² + 2a`. -/
lemma sq_add_one (a : ℝ≥0∞) : a ^ 2 + 1 = ((a - 1) + (1 - a)) ^ 2 + 2 * a := by
  rcases le_total 1 a with h | h
  · rw [tsub_eq_zero_of_le h, add_zero]
    obtain ⟨c, rfl⟩ := exists_add_of_le h
    rw [add_comm 1 c, ENNReal.add_sub_cancel_right one_ne_top]; ring
  · rw [tsub_eq_zero_of_le h, zero_add]
    have hs : a + (1 - a) = 1 := add_tsub_cancel_of_le h
    have hfin : a * (1 - a) ≠ ⊤ :=
      ENNReal.mul_ne_top (ne_top_of_le_ne_top one_ne_top h)
        (ne_top_of_le_ne_top one_ne_top tsub_le_self)
    have key1 : a ^ 2 + a * (1 - a) = a := by rw [sq, ← mul_add, hs, mul_one]
    have key2 : (1 - a) ^ 2 + a * (1 - a) = 1 - a := by rw [sq, ← add_mul, add_comm, hs, one_mul]
    have e1 : a ^ 2 + (1 - a) + a * (1 - a) = 1 := by rw [add_right_comm, key1, hs]
    have e2 : (1 - a) ^ 2 + a + a * (1 - a) = 1 := by rw [add_right_comm, key2, add_comm, hs]
    have heq : a ^ 2 + (1 - a) = (1 - a) ^ 2 + a := by
      rw [← ENNReal.add_sub_cancel_right (a := a ^ 2 + (1 - a)) hfin,
          ← ENNReal.add_sub_cancel_right (a := (1 - a) ^ 2 + a) hfin, e1, e2]
    calc a ^ 2 + 1 = a ^ 2 + (a + (1 - a)) := by rw [hs]
      _ = (a ^ 2 + (1 - a)) + a := by ring
      _ = ((1 - a) ^ 2 + a) + a := by rw [heq]
      _ = (1 - a) ^ 2 + 2 * a := by rw [two_mul]; ring

/-- Cauchy–Schwarz for `∫⁻` over a probability measure: `∫ f ≤ (∫ f²)^(1/2)`. -/
lemma lintegral_le_sqrt_sq {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) :
    ∫⁻ ω, f ω ∂P ≤ (∫⁻ ω, f ω ^ 2 ∂P) ^ ((1:ℝ)/2) := by
  have hconj : (2:ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hg : AEMeasurable (fun _ : Ω => (1:ℝ≥0∞)) P := aemeasurable_const
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hconj hf hg
  simp only [Pi.mul_apply, mul_one, one_rpow, lintegral_one, measure_univ] at h
  have hrw : ∫⁻ ω, f ω ^ (2:ℝ) ∂P = ∫⁻ ω, f ω ^ 2 ∂P :=
    lintegral_congr fun ω => by rw [ENNReal.rpow_two, sq]
  rwa [hrw] at h

/-- General total-variation identity: for two `ν`-densities integrating to `1`,
`∫ min(f,g) dν = 1 − ½ ∫ |f − g| dν`. -/
lemma tvIdentity_of {ν : Measure Ω} {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hf1 : ∫⁻ ω, f ω ∂ν = 1) (hg1 : ∫⁻ ω, g ω ∂ν = 1) :
    ∫⁻ ω, min (f ω) (g ω) ∂ν = 1 - 2⁻¹ * ∫⁻ ω, ((f ω - g ω) + (g ω - f ω)) ∂ν := by
  have key : 2 * (∫⁻ ω, min (f ω) (g ω) ∂ν)
      + (∫⁻ ω, ((f ω - g ω) + (g ω - f ω)) ∂ν) = 2 := by
    rw [← lintegral_const_mul 2 (hf.min hg),
      ← lintegral_add_left ((hf.min hg).const_mul 2),
      lintegral_congr (fun ω => two_min_add_absDiff (f ω) (g ω)),
      lintegral_add_left hf, hf1, hg1]
    norm_num
  have hDne : (∫⁻ ω, ((f ω - g ω) + (g ω - f ω)) ∂ν) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (le_of_le_of_eq le_add_self key)
  exact np_arith _ _ hDne key

/-- **Lebesgue-decomposition integral split** (Strasser 1.5(8)): for `μ ≪`-decomposed
against `ν`, `∫ f dμ = ∫ f·(dμ/dν) dν + ∫ f d(μ.singularPart ν)`. The first term is
the absolutely-continuous contribution, the second the singular one. -/
lemma lintegral_eq_rnDeriv_add_singularPart (μ ν : Measure Ω) [μ.HaveLebesgueDecomposition ν]
    {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f ω ∂μ
      = (∫⁻ ω, f ω * μ.rnDeriv ν ω ∂ν) + ∫⁻ ω, f ω ∂(μ.singularPart ν) := by
  conv_lhs => rw [← μ.rnDeriv_add_singularPart ν]
  rw [lintegral_add_measure,
    lintegral_withDensity_eq_lintegral_mul _ (μ.measurable_rnDeriv ν) hf]
  congr 1
  exact lintegral_congr fun ω => by rw [Pi.mul_apply, mul_comm]

end Statlib.Testing
