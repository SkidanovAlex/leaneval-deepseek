import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxFlatCount_eq_sum_compT
import Submission.Work.BoseFixB1S.boxQInd_boxCompT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.BoxHopDefs` — the **hopping (children-mass) layer**

The rung-4 target `Work.BoseFixB1.boxQSum_ge_a0Main_add_A2` reduces (see
`Submission/Work/BoseFixB1/FINDING_boxHopLayer.md`) to a *sharp* bound on the cross pair

    (V/2) · (boxCrossPart − 2μ P̃) = Σᵢ ⟨QᵢΦ , f(xᵢ) (nᵢ − m) PᵢΦ⟩ ,   f := fib₁ − ⦵_A fib₁ , m := μV ,

which — unlike every *slot-diagonal* Cauchy–Schwarz — must pair each slot's `Q`-side with the
weight of the **child** joint component `c_i(c) = (S_c ∖ {i}, T_c ∪ {i})` obtained by moving the slot
`i` from `P` to `Q`.

The joint components `ψ_{S,T} = boxCompT V A S T Φ` (the commuting family `(Pᵢ, Qᵢ, Rᵢ)ᵢ`) and
their orthogonality are in `Submission/Work/BoseFixB1S/BoxSpectralDefs.lean`,
`boxCompT_orth.lean`, `boxPInd_boxCompT.lean`; the counts identities
`S = Σ_{(S,T)}|S|∫ψ²` (`boxFlatCount_eq_sum_compT`) and `n₊ = Σ_{(S,T)}|T|∫ψ²` are proved.

This module only *defines* the two objects the sharp bound is stated with:

* `boxCompTMass` — the mass `∫_{abox}|ψ_{S,T}|²` of a joint component;
* `boxChildW` — the **children mass**

      Σ_{(S,T)} Σ_{i∈S} ‖ψ_{S∖i,T∪i}‖² · (|S| − 1 − m)²  ,

  restricted to the *realised* edges (both the slot's `P`-component and its child component of
  positive mass), which is exactly what the sharp Cauchy–Schwarz over the edge set produces.

The restriction to realised edges is essential: without it the sum equals the lossy
`Σ_{(S,T)}|T|(|S|−m)²‖ψ_{S,T}‖²`, whose use makes the required constant grow without bound in `N`
(the `p`-grid traps recorded in `FINDING_boxQSum_hoppingChain.md` §4, §9, §10).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The finset of **disjoint pairs** `(S,T)` indexing the joint components `ψ_{S,T}` of the
commuting family `(Pᵢ, Qᵢ, Rᵢ)ᵢ` (`Rᵢ = 1 − 1_A(xᵢ)`), `S ∪ T ∪ U = univ`. -/
def disjPairs (N : ℕ) : Finset (Finset (Fin N) × Finset (Fin N)) :=
  (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter (fun p => Disjoint p.1 p.2)

theorem mem_disjPairs {N : ℕ} {p : Finset (Fin N) × Finset (Fin N)} :
    p ∈ disjPairs N ↔ Disjoint p.1 p.2 := by
  simp [disjPairs]

/-- The mass `∫_{abox}|ψ_{S,T}|²` of the joint component `ψ_{S,T} = boxCompT V A S T Φ`. -/
def boxCompTMass {N : ℕ} (volA ℓ : ℝ) (A : Set E3)
    (c : Finset (Fin N) × Finset (Fin N)) (Φ : Submission.BoseGases.X N → ℝ) : ℝ :=
  ∫ x in Submission.BoseGases.abox N ℓ,
    (Work.BoseFixB1S.boxCompT volA A c.1 c.2 Φ x) ^ 2

/-- The **children mass** of the cross pair: for every joint component `(S,T)` and every slot
`i ∈ S`, the mass of the child component `(S∖i, T∪i)` times `(|S|−1−m)²`, summed over the
*realised* edges (both `(S,T)` and its child of positive mass). -/
def boxChildW {N : ℕ} (volA ℓ : ℝ) (A : Set E3) (m : ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) : ℝ :=
  ∑ c ∈ disjPairs N, ∑ i ∈ c.1,
    (if 0 < boxCompTMass volA ℓ A c Φ
        ∧ 0 < boxCompTMass volA ℓ A (c.1.erase i, insert i c.2) Φ
      then boxCompTMass volA ℓ A (c.1.erase i, insert i c.2) Φ * ((c.1.card : ℝ) - 1 - m) ^ 2
      else 0)

/-- The **parent mass over the realised edges** of the same edge set as `boxChildW`:
for every joint component `(S,T)` and every slot `i ∈ S` whose child component `(S∖i, T∪i)` has
positive mass, the mass of `(S,T)`, summed over the realised edges. -/
def boxChildP {N : ℕ} (volA ℓ : ℝ) (A : Set E3)
    (Φ : Submission.BoseGases.X N → ℝ) : ℝ :=
  ∑ c ∈ disjPairs N, ∑ i ∈ c.1,
    (if 0 < boxCompTMass volA ℓ A c Φ
        ∧ 0 < boxCompTMass volA ℓ A (c.1.erase i, insert i c.2) Φ
      then boxCompTMass volA ℓ A c Φ
      else 0)

/-- The parent mass over the realised edges is non-negative. -/
theorem boxChildP_nonneg {N : ℕ} (volA ℓ : ℝ) (A : Set E3)
    (Φ : Submission.BoseGases.X N → ℝ) : 0 ≤ boxChildP volA ℓ A Φ := by
  unfold boxChildP
  refine Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun i _ => ?_
  split_ifs with h
  · exact h.1.le
  · exact le_refl 0

/-- The `L²`-size of the **centred fibre** `f = fib₁ − ⦵_A fib₁`:
`boxHopF2 = √(⦵_A f²) = √((1/V)∫_A (fib₁ − M₁/V)²)`.  This is the *exact* operator norm of the
one-slot map `Q_i · f(x_i) · P_i` (`‖Q_i f P_i‖ = ‖f‖_{L²(A)}/√V`), hence the sharp constant of the
hopping matrix element `⟨ψ_{S∖i,T∪i}, f(x_i) ψ_{S,T}⟩ = boxHopF2 · ‖ψ_{S∖i,T∪i}‖ · ‖ψ_{S,T}‖`. -/
def boxHopF2 (volA ℓ : ℝ) (A : Set E3)
    (w₁ : E3 → E3 → ℝ) : ℝ :=
  Real.sqrt ((1 / volA) * ∫ z in A,
    (Submission.BoseGases.w1Fibre ℓ w₁ z
      - Work.BoseFixB1S.boxM1 ℓ A w₁ / volA) ^ 2)

/-- The mass of a joint component is non-negative. -/
theorem boxCompTMass_nonneg {N : ℕ} (volA ℓ : ℝ) (A : Set E3)
    (c : Finset (Fin N) × Finset (Fin N)) (Φ : Submission.BoseGases.X N → ℝ) :
    0 ≤ boxCompTMass volA ℓ A c Φ :=
  MeasureTheory.integral_nonneg fun _ => sq_nonneg _

/-- The children mass is non-negative. -/
theorem boxChildW_nonneg {N : ℕ} (volA ℓ : ℝ) (A : Set E3) (m : ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) : 0 ≤ boxChildW volA ℓ A m Φ := by
  unfold boxChildW
  refine Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun i _ => ?_
  split_ifs with h
  · exact mul_nonneg h.2.le (sq_nonneg _)
  · exact le_refl 0

end Work.BoseFixB1
