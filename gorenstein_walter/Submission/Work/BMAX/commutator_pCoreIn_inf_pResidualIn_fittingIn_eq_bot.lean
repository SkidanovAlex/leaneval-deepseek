/-
# BMAX — `⁅O_p(B) ⊓ A, O^p(B ⊓ F(A))⁆ = 1`

Target (the statement the area asked for):

  `Work.BMAX.commutator_pCoreIn_inf_pResidualIn_fittingIn_eq_bot`:
  for *arbitrary* subgroups `A`, `B` of a finite group `G` and a prime `p`,

    `⁅O_p(B) ⊓ A, O^p(B ⊓ F(A))⁆ = 1`.

Unlike the other commutator lemmas of the area this one needs no simplicity, no coatom
and no `D`-group hypothesis: it is pure finite-group theory.

## Mathematics

Write `Q := O_p(B) ⊓ A`, `N := B ⊓ F(A)`, `R := O^p(N) = O^p(B ⊓ F(A))`.

* `Q ≤ N_G(N)`: `Q ≤ B` normalizes `B`, and `Q ≤ A` normalizes `F(A) ⊴ A`.
* Hence `Q ≤ N_G(R)` (`O^p` of a normalised subgroup is normalised; `R` is characteristic
  in `N`), so `⁅Q, R⁆ ≤ R`.
* Also `⁅Q, R⁆ ≤ O_p(B)` (`Q ≤ O_p(B) ⊴ B`, `R ≤ N ⊆ B`) and `⁅Q, R⁆ ≤ N`
  (`Q ≤ A`, `R ≤ F(A) ⊴ A`).
* `O_p(B) ⊓ N = O_p(B) ⊓ B ⊓ F(A)` is a `p`-subgroup of the nilpotent group `F(A)`, hence
  lies in `O_p(F(A))`.  So `⁅Q, R⁆ ≤ O_p(F(A))`.
* `R ≤ O^p(F(A))` by monotonicity, so `⁅Q, R⁆ ≤ O^p(F(A))`.
* `O_p(F(A)) ⊓ O^p(F(A)) = 1` because `F(A)` is finite nilpotent.

Hence `⁅Q, R⁆ = 1`.
-/
import Mathlib
import Submission.Work.BMAX.D17Defs
import Submission.Work.BMAX.inf_fittingIn_le_pCoreIn_of_le_pCoreIn
import Submission.Work.BMAX.nilpotent_pCoreIn_inf_pResidualIn_eq_bot
import Submission.Work.BMAX.centralizer_pResidualIn_witness_le
import Submission.Work.BMAX.pCoreIn_inf_pResidualIn_fittingIn_eq_bot
import Submission.Work.BMAX.pCoreIn_commutator_layerIn

namespace Work.BMAX

open Subgroup

set_option linter.style.haveILetI false

theorem commutator_pCoreIn_inf_pResidualIn_fittingIn_eq_bot {G : Type} [Group G] [Finite G]
    (A B : Subgroup G) (p : ℕ) (hp : p.Prime) :
    ⁅Work.GW2.pCoreIn p B ⊓ A, Work.BMAX.pResidualIn p (B ⊓ Work.GW2.fittingIn A)⁆ = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hFnil : Group.IsNilpotent ↥(Work.GW2.fittingIn A) := Work.BMAX.isNilpotent_fittingIn A
  set N : Subgroup G := B ⊓ Work.GW2.fittingIn A with hN
  set Q : Subgroup G := Work.GW2.pCoreIn p B ⊓ A with hQ
  set R : Subgroup G := Work.BMAX.pResidualIn p N with hR
  -- containment facts
  have hNF' : N ≤ Work.GW2.fittingIn A := by rw [hN]; exact inf_le_right
  have hNB : N ≤ B := by rw [hN]; exact inf_le_left
  have hQB : Q ≤ B := by
    rw [hQ]; exact inf_le_left.trans (pcl_pCoreIn_le_self p B)
  have hQA : Q ≤ A := by rw [hQ]; exact inf_le_right
  have hQpc : Q ≤ Work.GW2.pCoreIn p B := by rw [hQ]; exact inf_le_left
  have hRN : R ≤ N := by rw [hR]; exact Work.BMAX.pResidualIn.le N
  have hRB : R ≤ B := hRN.trans hNB
  have hRF : R ≤ Work.GW2.fittingIn A := hRN.trans hNF'
  -- `Q` normalizes `N`
  have hQN : Q ≤ Subgroup.normalizer (N : Set G) := by
    have h1 : Q ≤ Subgroup.normalizer (B : Set G) := hQB.trans Subgroup.le_normalizer
    have h2 : Q ≤ Subgroup.normalizer ((Work.GW2.fittingIn A : Subgroup G) : Set G) :=
      hQA.trans (Work.BMAX.le_normalizer_fittingIn A)
    have h4 : Q ≤ Subgroup.normalizer ((B ⊓ Work.GW2.fittingIn A : Subgroup G) : Set G) :=
      (le_inf h1 h2).trans (Work.BMAX.pcl_normalizer_inf_le B (Work.GW2.fittingIn A))
    simpa only [hN] using h4
  -- `Q` normalizes `R`
  have hQR : Q ≤ Subgroup.normalizer (R : Set G) :=
    Work.BMAX.le_normalizer_pResidualIn_of_le_normalizer (p := p) hQN
  -- `⁅Q, R⁆ ≤ R`
  have hleR : ⁅Q, R⁆ ≤ R := (Subgroup.le_normalizer_iff_commutator_le_right).mp hQR
  -- `⁅Q, R⁆ ≤ O^p(F(A))`
  have hleResF : ⁅Q, R⁆ ≤ Work.BMAX.pResidualIn p (Work.GW2.fittingIn A) :=
    hleR.trans (Work.BMAX.pResidualIn.mono hNF')
  -- `⁅Q, R⁆ ≤ O_p(B)`
  have hleCoreB : ⁅Q, R⁆ ≤ Work.GW2.pCoreIn p B := by
    have hcB : ⁅(Work.GW2.pCoreIn p B : Subgroup G), B⁆ ≤ Work.GW2.pCoreIn p B := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.le_normalizer_iff_commutator_le_right).mp
        (Work.BMAX.le_normalizer_pCoreIn B p)
    exact (Subgroup.commutator_mono hQpc hRB).trans hcB
  -- `⁅Q, R⁆ ≤ F(A)`
  have hleF : ⁅Q, R⁆ ≤ Work.GW2.fittingIn A := by
    have hcF : ⁅A, (Work.GW2.fittingIn A : Subgroup G)⁆ ≤ Work.GW2.fittingIn A :=
      (Subgroup.le_normalizer_iff_commutator_le_right).mp (Work.BMAX.le_normalizer_fittingIn A)
    exact (Subgroup.commutator_mono hQA hRF).trans hcF
  -- `⁅Q, R⁆ ≤ N`
  have hleN : ⁅Q, R⁆ ≤ N := by
    rw [hN]; exact le_inf (le_trans (Subgroup.commutator_mono hQB hRB)
      ((Subgroup.le_normalizer_iff_commutator_le_right).mp Subgroup.le_normalizer)) hleF
  -- `⁅Q, R⁆ ≤ O_p(F(A))`
  have hleCoreF : ⁅Q, R⁆ ≤ Work.GW2.pCoreIn p (Work.GW2.fittingIn A) := by
    have h3 : ⁅Q, R⁆ ≤ Work.GW2.pCoreIn p B ⊓ Work.GW2.fittingIn A :=
      le_inf hleCoreB (hleN.trans hNF')
    have h4 : Work.GW2.pCoreIn p B ⊓ Work.GW2.fittingIn A ≤
        Work.GW2.pCoreIn p (Work.GW2.fittingIn A) :=
      Work.BMAX.le_pCoreIn_of_isPGroup_of_isNilpotent (Work.GW2.fittingIn A) inf_le_right
        ((Work.BMAX.isPGroup_pCoreIn_of_finite p B).to_le inf_le_left)
    exact h3.trans h4
  -- conclude
  have hfin : ⁅Q, R⁆ ≤ Work.GW2.pCoreIn p (Work.GW2.fittingIn A) ⊓
      Work.BMAX.pResidualIn p (Work.GW2.fittingIn A) := le_inf hleCoreF hleResF
  rw [Work.BMAX.nilpotent_pCoreIn_inf_pResidualIn_eq_bot (Work.BMAX.isNilpotent_fittingIn A) hp]
    at hfin
  exact le_bot_iff.mp hfin

end Work.BMAX
