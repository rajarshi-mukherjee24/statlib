/-
Copyright (c) 2026 Rajarshi Mukherjee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rajarshi Mukherjee
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# f-divergences

The general `f`-divergence `D_f(P ‖ Q) = ∫⁻ f(dP/dQ) dQ` and the two members not
yet in Mathlib: the χ²-divergence and the Hellinger affinity (Bhattacharyya
coefficient). Kullback–Leibler is available in Mathlib as
`MeasureTheory.klDiv` (module `Mathlib.InformationTheory.KullbackLeibler.Basic`)
and is reused directly rather than redefined.

Everything is `ℝ≥0∞`-valued using the Lebesgue integral `∫⁻`, matching the risk
codomain of `Statlib.Inference`.

PROVISIONAL. `fDiv`/`chiSqDiv`/`hellingerAffinity` here are lightweight stopgaps
valid under absolute continuity (`P ≪ Q`); they omit the singular-part term of
the general Csiszár f-divergence. The full, general theory (convexity,
non-negativity, data-processing, Pinsker) exists in
`RemyDegenne/testing-lower-bounds` (`f : ℝ → ℝ`, `EReal`-valued, singular-part
aware) and is being upstreamed to mathlib — `MeasureTheory.klDiv` has already
landed and is reused directly. Do NOT re-derive that framework here; swap these
shims for the mathlib API as the upstreaming progresses. See the strategy note.

## Main definitions

* `Statlib.Divergence.fDiv` — the general `f`-divergence `∫⁻ f(dP/dQ) dQ`.
* `Statlib.Divergence.chiSqDiv` — the χ²-divergence `E_Q[(dP/dQ)²] − 1`.
* `Statlib.Divergence.hellingerAffinity` — the Bhattacharyya affinity `∫⁻ √(p·q) dμ`.
-/

@[expose] public section

open MeasureTheory ENNReal

namespace Statlib.Divergence

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **general `f`-divergence** `D_f(P ‖ Q) = ∫⁻ f(dP/dQ) dQ`, for a
"divergence generator" `f : ℝ≥0∞ → ℝ≥0∞` (typically convex with `f 1 = 0`). The
χ²-divergence, squared Hellinger distance, total variation and Kullback–Leibler
divergence are all instances for particular `f`. -/
noncomputable def fDiv (f : ℝ≥0∞ → ℝ≥0∞) (P Q : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ ω, f (P.rnDeriv Q ω) ∂Q

/-- The **χ²-divergence** `χ²(P ‖ Q) = E_Q[(dP/dQ)²] − 1`. Under `P ≪ Q` this equals
`∫⁻ (dP/dQ − 1)² dQ` (the `f`-divergence for `f x = (x − 1)²`), written here in the
subtraction-safe `ℝ≥0∞` form using `∫⁻ (dP/dQ) dQ = 1`. -/
noncomputable def chiSqDiv (P Q : Measure Ω) : ℝ≥0∞ :=
  (∫⁻ ω, (P.rnDeriv Q ω) ^ 2 ∂Q) - 1

/-- The **Hellinger affinity** (Bhattacharyya coefficient) `∫⁻ √(p·q) dμ`, with
densities `p = dP/dμ`, `q = dQ/dμ` against the common dominating measure
`μ = P + Q`. The squared Hellinger distance is `1 − affinity` (up to
normalisation); the affinity form is `ℝ≥0∞`-subtraction-free. -/
noncomputable def hellingerAffinity (P Q : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ ω, (P.rnDeriv (P + Q) ω * Q.rnDeriv (P + Q) ω) ^ ((1 : ℝ) / 2) ∂(P + Q)

/-- `fDiv` unfolds to the integral of `f` against the Radon–Nikodym derivative. -/
lemma fDiv_eq (f : ℝ≥0∞ → ℝ≥0∞) (P Q : Measure Ω) :
    fDiv f P Q = ∫⁻ ω, f (P.rnDeriv Q ω) ∂Q := rfl

/-- The χ²-divergence is the `f`-divergence for `f x = x²`, shifted by one:
`χ²(P ‖ Q) = fDiv (· ^ 2) P Q − 1`. -/
lemma chiSqDiv_eq_fDiv_sub_one (P Q : Measure Ω) :
    chiSqDiv P Q = fDiv (· ^ 2) P Q - 1 := rfl

end Statlib.Divergence
