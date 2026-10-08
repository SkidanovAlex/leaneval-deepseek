/-
# `O_p(B) ∩ A ≤ C_G(E(A))`  when `E(A) ≤ B`

The statement proved here is

  `Work.BMAX.pCoreIn_inf_le_centralizer_layerIn`:
  for a finite group `G`, subgroups `A, B ≤ G` with `E(A) = layerIn A ≤ B` and a prime `p`,

    `O_p(B) ∩ A ≤ C_G(E(A))`.

## Mathematics

Put `M := O_p(B) ∩ A`.

* `M` is *solvable*: `O_p(B) ≤ F(B)` (`pCoreIn_le_fittingIn`) and `F(B)` is nilpotent
  (`isNilpotent_fittingIn`), so `M`, being a subgroup of the nilpotent group `F(B)`, is
  nilpotent, hence solvable.  (`E(A)` is in general *not* solvable, so this step really uses the
  `p`-core hypothesis.)
* `A` normalises `E(A)` (`le_normalizer_layerIn`), so `M ≤ A` normalises `E(A)`.
* `E(A)` normalises `M = O_p(B) ∩ A`: it lies in `B` by hypothesis, whence in `N_G(O_p(B))`
  (`le_normalizer_pCoreIn`), and in `A`, whence in `N_G(A)`; the intersection of normalisers
  normalises the intersection (`inf_normalizer_le_normalizer_inf`).

Then the "solvable subgroup normalising and normalised by the layer centralises it" lemma
(`layerIn_le_centralizer_of_solvable`) gives `E(A) ≤ C_G(M)`, which by symmetry of the
centraliser relation (`Subgroup.le_centralizer_iff`) is `M ≤ C_G(E(A))`.

No simplicity/maximality of `A` and no `D`-group hypothesis is needed: only the two mutual
normalising conditions, which here come from `E(A) ≤ B`.
-/
import Mathlib
import Submission.Work.BMAX.D17Defs
import Submission.Work.BMAX.layerIn_le_centralizer_of_solvable
import Submission.Work.BMAX.centralizer_pResidualIn_witness_le
import Submission.Work.BMAX.Bender17i_dedekind_basic

set_option linter.style.haveILetI false

namespace Work.BMAX

theorem pCoreIn_inf_le_centralizer_layerIn {G : Type} [Group G] [Finite G]
    (A B : Subgroup G) (p : ℕ) (hp : p.Prime) (hEB : Work.GW2.layerIn A ≤ B) :
    Work.GW2.pCoreIn p B ⊓ A ≤ Subgroup.centralizer ((Work.GW2.layerIn A : Subgroup G) : Set G) := by
  set M : Subgroup G := Work.GW2.pCoreIn p B ⊓ A with hM
  -- `M ≤ F(B)`, and `F(B)` is nilpotent, so `M` is solvable
  have hMle : M ≤ Work.GW2.fittingIn B :=
    le_trans inf_le_left (Work.BMAX.pCoreIn_le_fittingIn B hp)
  have hF : Group.IsNilpotent ↥(Work.GW2.fittingIn B) := Work.BMAX.isNilpotent_fittingIn B
  have hMnil : Group.IsNilpotent ↥M :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hMle)).mp
      (Subgroup.isNilpotent (M.subgroupOf (Work.GW2.fittingIn B)))
  haveI := hF
  haveI := hMnil
  have hMsol : Group.IsSolvable ↥M := IsNilpotent.to_isSolvable
  -- `E(A)` normalises `M = O_p(B) ∩ A`
  have hEn : Work.GW2.layerIn A ≤ Subgroup.normalizer (M : Set G) := by
    rw [hM]
    refine le_trans ?_
      (Subgroup.inf_normalizer_le_normalizer_inf (H := Work.GW2.pCoreIn p B) (K := A))
    intro x hx
    exact Subgroup.mem_inf.mpr
      ⟨Work.BMAX.le_normalizer_pCoreIn B p (hEB hx),
       (Subgroup.le_normalizer (H := A)) (Work.GW2.layerIn_le_self A hx)⟩
  -- `M` normalises `E(A)`, so `E(A)` centralises `M`; flip the centraliser
  have hcen : Work.GW2.layerIn A ≤ Subgroup.centralizer (M : Set G) :=
    Work.BMAX.layerIn_le_centralizer_of_solvable hMsol
      (le_trans inf_le_right (Work.BMAX.le_normalizer_layerIn A)) hEn
  have hthis := Subgroup.le_centralizer_iff.mp hcen
  rwa [hM] at hthis

end Work.BMAX
