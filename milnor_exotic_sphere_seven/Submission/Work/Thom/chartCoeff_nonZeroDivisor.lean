import Mathlib
import Submission.Work.Thom.chartCoeffAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-!
# The coefficient of a Thom class over a chart piece is a non-zero-divisor

Let `Z → B` be a real bundle of rank `n`, `T` an (integral) Thom class of `Z`, `i` a chart index,
`W ⊆ Z.baseSet i` a subset of a chart piece and `e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)` a linear
equivalence exhibiting the fibre.  Write `τ''` for the *explicit chart class*
`Work.Thom.localThomOfChart`, a local Thom class over `W`.  Given `c ∈ H⁰(W;ℤ)` with

`T.τ|_W = π_W^*(c) ⌣ τ''`,

the goal is: `c` is a **non-zero-divisor** in the ring `H⁰(W;ℤ)`:

`∀ x, x ⌣ c = 0 → x = 0`.

Since `H⁰(X;ℤ) ≅ ℤ^{π₀(X)}` with pointwise multiplication, this says that `c` does not vanish at
any point of `W`; equivalently the Thom class never dies on a fibre.

## The route

Everything is read off from the *pointwise evaluations* of degree-zero classes (the toolkit in
`Submission/Work/Thom/chartCoeffAux.lean`):

* `ptEv p x ∈ ℤ` is the evaluation of `x ∈ H⁰` at the point `p`; the evaluations jointly detect
  classes (`ptEv_ext`), are multiplicative (`ptEv_cup`) and natural under pullback
  (`ptEv_pullback`).

* **Pointwise form of the hypothesis.**  Restricting the defining equation of `c` to a point
  `b ∈ W` (`PieceRes_singleton_eq`, `localThomMap_piece_pt`) and using the unit law of the local
  Thom map (`localThomMap_oneH`, `CohMap_ptIncl_smul`) gives
  `bad b ↔ ptEv b c = 0` (`bad_iff_ptEv`), where `bad b` means "the restriction of `T.τ` to the
  fibre over `b` vanishes".

* **The Thom class never dies on a fibre.**  If `α ∈ H⁰(B)` is the indicator class of the path
  component of `b` (`ptIndicator`, `Indicator.lean`), then `π^*(α) ⌣ T.τ ≠ 0` (the Thom iso), so
  by the separating property of the Thom pair in degree `0 + n` some chart piece carries a nonzero
  piece of it; detecting that piece on fibres (`eq_zero_of_fibre_eq_zero`) produces a point `b'`
  joined to `b` with `¬ bad b'` (`exists_good_point_of_separation`).  Hence `¬ bad b` for all `b`
  (`bad_eq_of_joined`).

* The separating property is `Work.Thom.openThom_zero_of_baseSet_zeroAdd` for `n ≥ 1` and the
  elementary degree-`0` cover argument `Work.Thom.openThom_zero_of_baseSet_zero` for `n = 0`
  (via `relCoh_zero_of_cover`).

* Multiplicativity of `ptEv` finishes: `0 = ptEv b (x ⌣ c) = ptEv b x · ptEv b c` forces
  `ptEv b x = 0` for all `b ∈ W`, so `x = 0` by `ptEv_ext`.

The assembly is `Work.Thom.crux_of_separation`.
-/

namespace Work.Thom

open Work.TangentClasses Work.Cohomology
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

theorem chartCoeff_nonZeroDivisor {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} [FiniteDimensional ℝ F]
    (Z : Work.TangentClasses.RealBundle B F ι) {n : ℕ} (hrank : Z.rank = n)
    (T : Work.Thom.ThomClass Z n) (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (c : Work.Thom.Coh ℤ 0 ↥W)
    (hc : (Work.Thom.PieceRes Z W n).hom T.τ
        = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W
            (Work.Thom.localThomOfChart Z n e i W hW).τ 0 c)) :
    ∀ x : Work.Thom.Coh ℤ 0 ↥W,
      Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0 x c = 0 → x = 0 := by
  by_cases hn : 1 ≤ n
  · exact crux_of_separation Z n hrank
      (fun z hz => openThom_zero_of_baseSet_zeroAdd Z n hrank hn z hz) e T i W hW c hc
  · have hn0 : n = 0 := by omega
    subst hn0
    have hF : Subsingleton F := (Module.finrank_zero_iff).mp hrank
    exact crux_of_separation Z 0 hrank
      (fun z hz => openThom_zero_of_baseSet_zero Z hF z hz) e T i W hW c hc

end

end Work.Thom
