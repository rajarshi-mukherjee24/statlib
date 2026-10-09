/-
Copyright (c) 2026 Rajarshi Mukherjee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rajarshi Mukherjee
-/
module

public import Statlib.Testing.NeymanPearson

/-!
# Minimal testing error at `t = 1`: total variation and the χ² bound

At equal weights `t = 1` the minimal sum of errors is `1 − TV(P, Q)`, and under a
one-sided absolute continuity it is bounded below using the χ²-divergence via
Cauchy–Schwarz. No absolute-continuity hypothesis is needed for the total-variation
identity itself; `|p − q|` denotes `(p − q) + (q − p)` (truncated subtraction).

## Main definitions

* `Statlib.Testing.totalVariation` — `TV(P,Q) = ½ ∫ |p − q| dμ` (integral form).

## Main results

* `Statlib.Testing.npTest_error_one_eq` — minimal error `= 1 − TV(P, Q)`.
* `Statlib.Testing.npTest_error_one_eq_llr` — likelihood-ratio form under `P ≪ Q`.
* `Statlib.Testing.npTest_error_one_ge_chi` — χ²-divergence lower bound (`Q ≪ P`).
* `Statlib.Testing.lintegral_absDiff_le_sqrt_chiSq` — the χ² Cauchy–Schwarz bound.
-/

@[expose] public section

open MeasureTheory ENNReal

namespace Statlib.Testing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- At `t = 1`, the pointwise cost at the NP test value is `min p q`. -/
private lemma cost_npTest_one (P Q : Measure Ω) (η : ℝ≥0∞) (hη : η ≤ 1) (ω : Ω) :
    cost (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) 1 (npTest P Q 1 η ω)
      = min (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) := by
  set p := P.rnDeriv (P + Q) ω
  set q := Q.rnDeriv (P + Q) ω
  rcases lt_trichotomy p (1 * q) with h | h | h
  · have hv : npTest P Q 1 η ω = 1 := by rw [npTest, if_pos h]
    rw [one_mul] at h
    rw [hv]; simp only [cost, mul_one, tsub_self, mul_zero, add_zero, min_eq_left h.le]
  · have hnlt : ¬ p < 1 * q := by rw [h]; exact lt_irrefl _
    have hv : npTest P Q 1 η ω = η := by rw [npTest, if_neg hnlt, if_pos h]
    rw [one_mul] at h
    rw [hv, h, min_self]
    simp only [cost]
    calc q * η + 1 * (q * (1 - η)) = (η + (1 - η)) * q := by ring
      _ = q := by rw [add_tsub_cancel_of_le hη, one_mul]
  · have hnlt : ¬ p < 1 * q := not_lt.mpr h.le
    have hne : ¬ p = 1 * q := (ne_of_gt h)
    have hv : npTest P Q 1 η ω = 0 := by rw [npTest, if_neg hnlt, if_neg hne]
    rw [one_mul] at h
    rw [hv]; simp only [cost, mul_zero, zero_add, tsub_zero, mul_one, one_mul, min_eq_right h.le]

/-- With `t = 1`, the error of the NP test is the integral of `min(p,q)`. -/
lemma errSum_one_eq_lintegral_min (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (η : ℝ≥0∞) (hη : η ≤ 1) :
    errSum P Q 1 (npTest P Q 1 η)
      = ∫⁻ ω, min (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) ∂(P + Q) := by
  rw [errSum_eq_lintegral_cost P Q 1 (measurable_npTest P Q 1 η)]
  exact lintegral_congr (fun ω => cost_npTest_one P Q η hη ω)

/-- Total-variation identity: `∫ min(p,q) dμ = 1 − ½ ∫ |p − q| dμ`. -/
lemma lintegral_min_eq_one_sub_half (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ∫⁻ ω, min (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) ∂(P + Q)
      = 1 - 2⁻¹ * ∫⁻ ω, ((P.rnDeriv (P + Q) ω - Q.rnDeriv (P + Q) ω)
          + (Q.rnDeriv (P + Q) ω - P.rnDeriv (P + Q) ω)) ∂(P + Q) := by
  have hP1 : ∫⁻ ω, P.rnDeriv (P + Q) ω ∂(P + Q) = 1 := by
    have hP : P ≪ P + Q := Measure.AbsolutelyContinuous.add_right .rfl Q
    have := lintegral_rnDeriv_mul hP (f := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
    simpa using this
  have hQ1 : ∫⁻ ω, Q.rnDeriv (P + Q) ω ∂(P + Q) = 1 := by
    have hQ : Q ≪ P + Q := Measure.AbsolutelyContinuous.add_right' .rfl P
    have := lintegral_rnDeriv_mul hQ (f := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
    simpa using this
  exact tvIdentity_of (Measure.measurable_rnDeriv P (P + Q))
    (Measure.measurable_rnDeriv Q (P + Q)) hP1 hQ1

/-- The **total-variation distance** `TV(P,Q) = ½ ∫ |p − q| dμ` (integral form,
`μ = P + Q`). -/
noncomputable def totalVariation (P Q : Measure Ω) : ℝ≥0∞ :=
  2⁻¹ * ∫⁻ ω, ((P.rnDeriv (P + Q) ω - Q.rnDeriv (P + Q) ω)
      + (Q.rnDeriv (P + Q) ω - P.rnDeriv (P + Q) ω)) ∂(P + Q)

/-- **Minimal sum of errors at `t = 1`.** The error of the Neyman–Pearson test equals
`1 − ½ ∫ |p − q| dμ`, i.e. one minus the total-variation distance. -/
theorem npTest_error_one_eq (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (η : ℝ≥0∞) (hη : η ≤ 1) :
    errSum P Q 1 (npTest P Q 1 η)
      = 1 - 2⁻¹ * ∫⁻ ω, ((P.rnDeriv (P + Q) ω - Q.rnDeriv (P + Q) ω)
          + (Q.rnDeriv (P + Q) ω - P.rnDeriv (P + Q) ω)) ∂(P + Q) :=
  (errSum_one_eq_lintegral_min P Q η hη).trans (lintegral_min_eq_one_sub_half P Q)

/-- Likelihood-ratio form of the `t = 1` minimal error: under `P ≪ Q`, with
`L = dP/dQ`, the error equals `1 − ½ ∫ |L − 1| dQ`. -/
theorem npTest_error_one_eq_llr (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (η : ℝ≥0∞) (hη : η ≤ 1) :
    errSum P Q 1 (npTest P Q 1 η)
      = 1 - 2⁻¹ * ∫⁻ ω, ((P.rnDeriv Q ω - 1) + (1 - P.rnDeriv Q ω)) ∂Q := by
  rw [errSum_one_eq_lintegral_min P Q η hη]
  have hL : Measurable (P.rnDeriv Q) := Measure.measurable_rnDeriv P Q
  have hLint : ∫⁻ ω, P.rnDeriv Q ω ∂Q = 1 := by
    have := lintegral_rnDeriv_mul hPQ (f := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
    simpa using this
  have hbridge : ∫⁻ ω, min (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) ∂(P + Q)
      = ∫⁻ ω, min (P.rnDeriv Q ω) 1 ∂Q := by
    have hchain : P.rnDeriv Q * Q.rnDeriv (P + Q) =ᵐ[P + Q] P.rnDeriv (P + Q) :=
      Measure.rnDeriv_mul_rnDeriv hPQ
    have hae : (fun ω => min (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω))
        =ᵐ[P + Q] (fun ω => Q.rnDeriv (P + Q) ω * min (P.rnDeriv Q ω) 1) := by
      filter_upwards [hchain] with ω hω
      have hpq : P.rnDeriv Q ω * Q.rnDeriv (P + Q) ω = P.rnDeriv (P + Q) ω := hω
      rw [← hpq]
      calc min (P.rnDeriv Q ω * Q.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω)
          = min (P.rnDeriv Q ω * Q.rnDeriv (P + Q) ω) (1 * Q.rnDeriv (P + Q) ω) := by rw [one_mul]
        _ = min (P.rnDeriv Q ω) 1 * Q.rnDeriv (P + Q) ω :=
            (Monotone.map_min (f := fun x => x * Q.rnDeriv (P + Q) ω)
              (fun a b hab => by dsimp only; gcongr)).symm
        _ = Q.rnDeriv (P + Q) ω * min (P.rnDeriv Q ω) 1 := mul_comm _ _
    rw [lintegral_congr_ae hae]
    have hQμ : Q ≪ P + Q := Measure.AbsolutelyContinuous.add_right' .rfl P
    exact lintegral_rnDeriv_mul hQμ (hL.min measurable_const).aemeasurable
  rw [hbridge, tvIdentity_of hL measurable_const hLint (by simp)]

/-- **χ² Cauchy–Schwarz bound.** For `μ ≪ ν`, `∫ |dμ/dν − 1| dν ≤ √(∫ (dμ/dν)² dν − 1)`. -/
theorem lintegral_absDiff_le_sqrt_chiSq (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ ≪ ν) :
    ∫⁻ ω, ((μ.rnDeriv ν ω - 1) + (1 - μ.rnDeriv ν ω)) ∂ν
      ≤ ((∫⁻ ω, (μ.rnDeriv ν ω) ^ 2 ∂ν) - 1) ^ ((1:ℝ)/2) := by
  have hL : Measurable (μ.rnDeriv ν) := Measure.measurable_rnDeriv μ ν
  have hLint : ∫⁻ ω, μ.rnDeriv ν ω ∂ν = 1 := by
    have := lintegral_rnDeriv_mul h (f := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
    simpa using this
  have habs : Measurable (fun ω => (μ.rnDeriv ν ω - 1) + (1 - μ.rnDeriv ν ω)) :=
    (hL.sub measurable_const).add (measurable_const.sub hL)
  have hChi : ∫⁻ ω, ((μ.rnDeriv ν ω - 1) + (1 - μ.rnDeriv ν ω)) ^ 2 ∂ν
      = (∫⁻ ω, (μ.rnDeriv ν ω) ^ 2 ∂ν) - 1 := by
    have hint : (∫⁻ ω, (μ.rnDeriv ν ω) ^ 2 ∂ν) + 1
        = (∫⁻ ω, ((μ.rnDeriv ν ω - 1) + (1 - μ.rnDeriv ν ω)) ^ 2 ∂ν) + 2 := by
      have h1 : ∫⁻ ω, ((μ.rnDeriv ν ω) ^ 2 + 1) ∂ν = (∫⁻ ω, (μ.rnDeriv ν ω) ^ 2 ∂ν) + 1 := by
        rw [lintegral_add_right _ measurable_const]; simp
      have h2 : ∫⁻ ω, (((μ.rnDeriv ν ω - 1) + (1 - μ.rnDeriv ν ω)) ^ 2 + 2 * μ.rnDeriv ν ω) ∂ν
          = (∫⁻ ω, ((μ.rnDeriv ν ω - 1) + (1 - μ.rnDeriv ν ω)) ^ 2 ∂ν) + 2 := by
        rw [lintegral_add_left (habs.pow_const 2), lintegral_const_mul 2 hL, hLint, mul_one]
      calc (∫⁻ ω, (μ.rnDeriv ν ω) ^ 2 ∂ν) + 1
          = ∫⁻ ω, ((μ.rnDeriv ν ω) ^ 2 + 1) ∂ν := h1.symm
        _ = ∫⁻ ω, (((μ.rnDeriv ν ω - 1) + (1 - μ.rnDeriv ν ω)) ^ 2 + 2 * μ.rnDeriv ν ω) ∂ν :=
            lintegral_congr fun ω => sq_add_one (μ.rnDeriv ν ω)
        _ = (∫⁻ ω, ((μ.rnDeriv ν ω - 1) + (1 - μ.rnDeriv ν ω)) ^ 2 ∂ν) + 2 := h2
    have hcancel : (∫⁻ ω, ((μ.rnDeriv ν ω - 1) + (1 - μ.rnDeriv ν ω)) ^ 2 ∂ν) + 1
        = ∫⁻ ω, (μ.rnDeriv ν ω) ^ 2 ∂ν := by
      have hthis := hint.symm
      rw [show (2:ℝ≥0∞) = 1 + 1 from by norm_num, ← add_assoc] at hthis
      exact WithTop.add_right_cancel one_ne_top hthis
    exact ENNReal.eq_sub_of_add_eq one_ne_top hcancel
  have hCS := lintegral_le_sqrt_sq (P := ν) habs.aemeasurable
  rwa [hChi] at hCS

/-- **Cauchy–Schwarz / χ² bound on the error at `t = 1`.** Under `Q ≪ P`, with
`L = dQ/dP`, the error is at least `1 − ½√(E_P[L²] − 1)` (`χ²(Q‖P) = E_P[L²] − 1`). -/
theorem npTest_error_one_ge_chi (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQP : Q ≪ P) (η : ℝ≥0∞) (hη : η ≤ 1) :
    1 - 2⁻¹ * ((∫⁻ ω, Q.rnDeriv P ω ^ 2 ∂P) - 1) ^ ((1:ℝ)/2)
      ≤ errSum P Q 1 (npTest P Q 1 η) := by
  have hL : Measurable (Q.rnDeriv P) := Measure.measurable_rnDeriv Q P
  have hbridge : ∫⁻ ω, min (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) ∂(P + Q)
      = ∫⁻ ω, min (Q.rnDeriv P ω) 1 ∂P := by
    have hchain : Q.rnDeriv P * P.rnDeriv (P + Q) =ᵐ[P + Q] Q.rnDeriv (P + Q) :=
      Measure.rnDeriv_mul_rnDeriv hQP
    have hae : (fun ω => min (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω))
        =ᵐ[P + Q] (fun ω => P.rnDeriv (P + Q) ω * min (Q.rnDeriv P ω) 1) := by
      filter_upwards [hchain] with ω hω
      have hqp : Q.rnDeriv P ω * P.rnDeriv (P + Q) ω = Q.rnDeriv (P + Q) ω := hω
      rw [← hqp]
      calc min (P.rnDeriv (P + Q) ω) (Q.rnDeriv P ω * P.rnDeriv (P + Q) ω)
          = min (1 * P.rnDeriv (P + Q) ω) (Q.rnDeriv P ω * P.rnDeriv (P + Q) ω) := by rw [one_mul]
        _ = min 1 (Q.rnDeriv P ω) * P.rnDeriv (P + Q) ω :=
            (Monotone.map_min (f := fun x => x * P.rnDeriv (P + Q) ω)
              (fun a b hab => by dsimp only; gcongr)).symm
        _ = P.rnDeriv (P + Q) ω * min (Q.rnDeriv P ω) 1 := by rw [min_comm]; ring
    rw [lintegral_congr_ae hae]
    have hPμ : P ≪ P + Q := Measure.AbsolutelyContinuous.add_right .rfl Q
    exact lintegral_rnDeriv_mul hPμ ((hL.min measurable_const).aemeasurable)
  have hA : errSum P Q 1 (npTest P Q 1 η)
      = 1 - 2⁻¹ * ∫⁻ ω, ((Q.rnDeriv P ω - 1) + (1 - Q.rnDeriv P ω)) ∂P := by
    have hLint : ∫⁻ ω, Q.rnDeriv P ω ∂P = 1 := by
      have := lintegral_rnDeriv_mul hQP (f := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
      simpa using this
    rw [errSum_one_eq_lintegral_min P Q η hη, hbridge,
      tvIdentity_of hL measurable_const hLint (by simp)]
  rw [hA]
  have hCS := lintegral_absDiff_le_sqrt_chiSq Q P hQP
  gcongr

end Statlib.Testing
