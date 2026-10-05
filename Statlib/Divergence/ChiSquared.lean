/-
Copyright (c) 2026 Rajarshi Mukherjee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rajarshi Mukherjee
-/
module

public import Statlib.Divergence.Basic
public import Statlib.Testing.MinimalError

/-!
# Total variation is bounded by the χ²-divergence

`TV(P, Q) ≤ ½ √(χ²(P ‖ Q))`, the equal-weight comparison of the `f`-divergences
`f = ½|t − 1|` and `f = (t − 1)²`. Total variation is written in its integral form
`½ ∫⁻ |dP/dQ − 1| dQ` (an integral form of `TV`), and the bound is the
Cauchy–Schwarz step `Statlib.Testing.lintegral_absDiff_le_sqrt_chiSq`.
-/

@[expose] public section

open MeasureTheory ENNReal

namespace Statlib.Divergence

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Total variation is bounded by the χ²-divergence.** For `P ≪ Q`,
`TV(P, Q) ≤ ½ √(χ²(P ‖ Q))`, where total variation is written in the integral form
`½ ∫⁻ |dP/dQ − 1| dQ`. -/
theorem tv_le_chiSq (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : P ≪ Q) :
    2⁻¹ * ∫⁻ ω, ((P.rnDeriv Q ω - 1) + (1 - P.rnDeriv Q ω)) ∂Q
      ≤ 2⁻¹ * (chiSqDiv P Q) ^ ((1 : ℝ) / 2) := by
  have hCS := Statlib.Testing.lintegral_absDiff_le_sqrt_chiSq P Q h
  calc 2⁻¹ * ∫⁻ ω, ((P.rnDeriv Q ω - 1) + (1 - P.rnDeriv Q ω)) ∂Q
      ≤ 2⁻¹ * ((∫⁻ ω, (P.rnDeriv Q ω) ^ 2 ∂Q) - 1) ^ ((1 : ℝ) / 2) := by gcongr
    _ = 2⁻¹ * (chiSqDiv P Q) ^ ((1 : ℝ) / 2) := rfl

end Statlib.Divergence
