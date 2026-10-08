import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.commute_entries
import Submission.Work.L2F.Mat2.det_smul_one_add_smul
import Submission.Work.L2F.Mat2.centralizer_aux
import Submission.Work.L2F.Mat2.nonempty_hypTorus_mulEquiv_centralizer
import Submission.Work.L2F.Mat2.natCard_normalizer_centralizer_le
import Submission.Work.L2F.Conic.hypTorus_cyclic
import Submission.Work.L2F.Conic.hypTorus_card
import Submission.Work.L2F.Conic.hypTorus_card_sq
import Submission.Work.L2F.Conic.mem_hypTorus
import Submission.Work.L2F.Torus.Defs

namespace Work.L2F.Mat2

/-- **The centralizer of a semisimple element of `SL(2,F)`.**  Let `F` be a finite field with
`(2 : F) ≠ 0` and let `x ∈ SL(2,F)` have `(tr x)^2 ≠ 4` (`x` is then a non-central semisimple
element: its characteristic polynomial `X^2 - (tr x) X + 1` has two distinct roots).  Then

* `C_{SL(2,F)}(x)` is cyclic;
* its order is `q - 1` or `q + 1`, `q = |F|`;
* its normalizer has order at most twice that.

Intended proof.  Put `t := tr x`, `X := x - (t/2) • 1` (traceless, `det X = 1 - t^2/4 ≠ 0`) and
`d := t^2/4 - 1 ≠ 0`, so that `X * X = d • 1` (Cayley–Hamilton).  (1) `Y ∈ SL(2,F)` commutes with
`X` iff `Y = a • 1 + b • X` with `a^2 - d b^2 = 1`; this is the `commute_entries` computation of
`Mat2.centralizer_sq_neg_one` with the relation `X 0 0 ^ 2 = -X.det` in place of `X 0 0 ^ 2 = -1`,
i.e. with `det X = 1 - t^2/4` in place of `det X = 1` (the general statement being: a matrix `Y`
with `det Y = 1` commuting with a traceless `X` with `det X = δ ≠ 0` is `a • 1 + b • X` with
`a^2 + δ b^2 = 1`, using `det_smul_one_add_smul`).  (2) The map `(a,b) ↦ a • 1 + b • X` is a group
isomorphism from `{a^2 - d b^2 = 1}` (with the law `(a,b)(c,e) = (ac + d be, ae + bc)`) onto
`C(x)`; the same law is the multiplication of `hypTorus F d = {!![a, d*b; b, a] | a^2 - d b^2 = 1}`
(`Conic.mem_hypTorus`), so `C(x) ≅ hypTorus F d` and cyclicity follows from
`Conic.hypTorus_cyclic` (`d ≠ 0`).  (3) `|C(x)| = |hypTorus F d|`: for `d` a nonsquare this is
`Conic.hypTorus_card` (`= q + 1`); for `d = μ^2` a square the conic `a^2 - μ^2 b^2 = 1` is in
bijection with `Fˣ` via `u ↦ ((u + u⁻¹)/2, (u - u⁻¹)/(2μ))`, giving `q - 1`.  (4) For
`g ∈ N(C(x))` we have `tr (g x g⁻¹) = tr x = t`, and by (1) the elements of `C(x)` of trace
`t` are exactly `x` and `x⁻¹ = t/2 • 1 - X`; hence `N(C(x)) ⊆ C(x) ∪ {g | g x g⁻¹ = x⁻¹}`, and the
second set is empty or a coset of `C(x)`, so `|N(C(x))| ≤ 2 |C(x)|`. -/
theorem centralizer_sl2_structure (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : ((x : Matrix (Fin 2) (Fin 2) F)).trace ^ 2 ≠ 4) :
    IsCyclic (Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) ∧
    (Nat.card (Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) =
        Nat.card F - 1 ∨
     Nat.card (Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) =
        Nat.card F + 1) ∧
    Nat.card (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) :
          Set (Matrix.SpecialLinearGroup (Fin 2) F)))
      ≤ 2 * Nat.card (Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) := by
  classical
  have hdisc : Work.L2F.Torus.disc F x ≠ 0 := by
    rw [Work.L2F.Torus.disc_apply]
    exact sub_ne_zero.mpr hx
  -- the centralizer is the torus `hypTorus F (disc F x)`
  obtain ⟨e⟩ := nonempty_hypTorus_mulEquiv_centralizer F h2 x hx
  refine ⟨?_, ?_, natCard_normalizer_centralizer_le F h2 x hx⟩
  · exact (MulEquiv.isCyclic e).mp
      (Work.L2F.Conic.hypTorus_cyclic F h2 (Work.L2F.Torus.disc F x) hdisc)
  · have hcard : Nat.card (Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F)))
        = Nat.card (Work.L2F.hypTorus F (Work.L2F.Torus.disc F x)) :=
      Nat.card_congr e.toEquiv.symm
    rcases Classical.em (∃ μ : F, Work.L2F.Torus.disc F x = μ ^ 2) with ⟨μ, hμ⟩ | hns
    · left
      have hμ0 : μ ≠ 0 := fun h => hdisc (by rw [hμ, h, pow_two, mul_zero])
      rw [hcard, Work.L2F.Conic.hypTorus_card_sq F h2 (Work.L2F.Torus.disc F x) μ hμ0 hμ]
    · right
      rw [hcard, Work.L2F.Conic.hypTorus_card F h2 (Work.L2F.Torus.disc F x) hdisc
        (fun a ha => hns ⟨a, by rw [← ha, pow_two]⟩)]

end Work.L2F.Mat2
