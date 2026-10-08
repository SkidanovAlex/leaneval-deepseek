/-
# BMAX — the commutator witness `[O_p(B), O^p(S)] = 1`

Final assembly of `Work.BMAX.CommutatorWitnessFinal`:

  `G` finite simple, `A` coatomic, `B ≠ ⊤` with `E(A) ≤ S ≤ B`, `S ≤ F*(A)`,
  `Z(F(A)) ≤ S`, and `p` a prime with `p ∈ π(F(A))`
  ⟹  `⁅O_p(B), O^p(S)⁆ = ⊥`.

The proof is the Thompson-on-`N₀` reduction
(`Work.BMAX.commutator_pCoreIn_pResidualIn_of_coatom_facts`) together with the crux

  `⁅O_p(B) ⊓ A, O^p(S)⁆ = ⊥`   (`commutator_pCoreIn_inf_pResidualIn_witness`).

For the crux one uses the witness `S ≤ B` (rather than `F*(A) ≤ B`): with
`F' = F(A) ⊓ S ≤ S ≤ B` and `R' = O^p(F')` one has `O^p(S) ≤ R' ⊔ E(A)` (the
`O^p`-of-a-join engine applied inside `S`), and each half is centralised by `D = O_p(B) ⊓ A`:

* `⁅D, E(A)⁆ = ⊥` — the layer centralises the solvable `D` that it normalises and by which it
  is normalised (`Work.BMAX.layerIn_le_centralizer_of_solvable`), since
  `E(A) ≤ S ≤ B` and `O_p(B) ◁ B`;
* `⁅D, R'⁆ = ⊥` — `⁅D, R'⁆ ≤ O_p(A)` (as `R' ≤ S ≤ B` makes `⁅D,R'⁆ ≤ O_p(B)`, while
  `⁅D,R'⁆ ≤ A ⊓ F(A)`, and `pCoreIn p B ⊓ A ⊓ F(A) ≤ pCoreIn p A`), and
  `⁅D, R'⁆ ≤ O^p(F(A))` (as `O^p` is characteristic in `F(A) ◁ A`), while
  `O_p(A) ⊓ O^p(F(A)) = ⊥`.
-/
import Mathlib
import Submission.Work.BMAX.D17Defs
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.commutator_pCoreIn_pResidualIn_witness
import Submission.Work.BMAX.pResidualIn_fstarIn_eq_sup
import Submission.Work.BMAX.inf_fittingIn_le_pCoreIn_of_le_pCoreIn
import Submission.Work.BMAX.pCoreIn_inf_pResidualIn_fittingIn_eq_bot
import Submission.Work.BMAX.le_normalizer_pCoreIn_zcenterIn_fittingIn
import Submission.Work.BMAX.layerIn_le_centralizer_of_solvable
import Submission.Work.BMAX.map_pResidual_subgroupOf_eq

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Work.BMAX

open Subgroup

/-! ## 1. Two elementary facts about normalizers and centralizers -/

/-- `N(X) ⊓ N(Y) ≤ N(X ⊓ Y)`. -/
theorem le_normalizer_inf {G : Type} [Group G] {X Y Z : Subgroup G}
    (hX : Z ≤ Subgroup.normalizer (X : Set G)) (hY : Z ≤ Subgroup.normalizer (Y : Set G)) :
    Z ≤ Subgroup.normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  intro z hz
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hX hz) x).mp h1,
           (Subgroup.mem_normalizer_iff.mp (hY hz) x).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hX hz) x).mpr h1,
           (Subgroup.mem_normalizer_iff.mp (hY hz) x).mpr h2⟩

/-- A subgroup contained in the centralizer of `X` and of `Y` is contained in the centralizer
of `X ⊔ Y`. -/
theorem le_centralizer_sup_aux {G : Type} [Group G] {V X Y : Subgroup G}
    (hX : V ≤ Subgroup.centralizer (X : Set G)) (hY : V ≤ Subgroup.centralizer (Y : Set G)) :
    V ≤ Subgroup.centralizer ((X ⊔ Y : Subgroup G) : Set G) := by
  rw [Subgroup.le_centralizer_iff] at hX hY ⊢
  exact sup_le hX hY

/-! ## 3. `S = (F(A) ⊓ S) · E(A)` -/

/-- If `E ≤ S ≤ A`, `F, E ◁ A` (i.e. `A ≤ N(F)`, `A ≤ N(E)`) and `S ≤ F ⊔ E`, then
`S ≤ (F ⊓ S) ⊔ E`.

The element decomposition `x = f · e` uses that `F` and `E` are normal in `A`: inside the group
`↥A` the subgroup `E.subgroupOf A` is normal, so an element of `F.subgroupOf A ⊔ E.subgroupOf A`
is a product `f · e`. -/
theorem le_sup_inf_of_normal_aux {G : Type} [Group G] {S F E A : Subgroup G}
    (hFA : F ≤ A) (hEA : E ≤ A)
    (hAF : A ≤ Subgroup.normalizer (F : Set G))
    (hAE : A ≤ Subgroup.normalizer (E : Set G))
    (hSA : S ≤ A) (hSF : S ≤ F ⊔ E) (hES : E ≤ S) :
    S ≤ (F ⊓ S) ⊔ E := by
  haveI hFn : (F.subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hAF
  haveI hEn : (E.subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hAE
  intro x hx
  have hxA : x ∈ A := hSA hx
  have hxFE : (⟨x, hxA⟩ : ↥A) ∈ F.subgroupOf A ⊔ E.subgroupOf A := by
    rw [← Subgroup.subgroupOf_sup hFA hEA, Subgroup.mem_subgroupOf]
    exact hSF hx
  obtain ⟨f, hf, e, he, hfe⟩ := Subgroup.mem_sup_of_normal_right.mp hxFE
  have hfF : (f : G) ∈ F := Subgroup.mem_subgroupOf.mp hf
  have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp he
  have hval : (f : G) * (e : G) = x := by
    simpa using congrArg (fun z : ↥A => (z : G)) hfe
  have hfS : (f : G) ∈ S := by
    have hfe' : (f : G) = x * (e : G)⁻¹ := by
      rw [← hval]; group
    rw [hfe']
    exact S.mul_mem hx (S.inv_mem (hES heE))
  have hx' : x = (f : G) * (e : G) := hval.symm
  rw [hx']
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hfF, hfS⟩)) (Subgroup.mem_sup_right heE)

/-! ## 4. `O^p` of a join, in the ambient group -/

/-- The engine `Work.BMAX.pResidual_le_sup_pResidualIn`, transported to the ambient group:
if `F, E ≤ X`, `F, E ◁ X` and `X ≤ F ⊔ E`, then
`O^p(X) ≤ O^p(F) ⊔ E` (all subgroups of the ambient `G`). -/
theorem pResidualIn_le_sup_pResidualIn_ambient {G : Type} [Group G] [Finite G]
    {X F E : Subgroup G} (hF : F ≤ X) (hE : E ≤ X)
    (hFn : X ≤ Subgroup.normalizer (F : Set G)) (hEn : X ≤ Subgroup.normalizer (E : Set G))
    (hXFE : X ≤ F ⊔ E) (p : ℕ) (hp : p.Prime) :
    Work.BMAX.pResidualIn p X ≤ Work.BMAX.pResidualIn p F ⊔ E := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hFn' : (F.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hFn
  haveI hEn' : (E.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hEn
  have hFE : F.subgroupOf X ⊔ E.subgroupOf X = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hF hE]
    exact (Subgroup.subgroupOf_eq_top).mpr hXFE
  have hmain := Work.BMAX.pResidual_le_sup_pResidualIn (X := ↥X)
    (F := F.subgroupOf X) (E := E.subgroupOf X) hFn' hEn' hFE p hp
  have hmap := Subgroup.map_mono (f := X.subtype) hmain
  have hFeq : Subgroup.map X.subtype (Work.BMAX.pResidualIn p (F.subgroupOf X)) =
      Work.BMAX.pResidualIn p F := by
    conv_lhs => rw [Work.BMAX.pResidualIn.eq_map (F.subgroupOf X)]
    rw [Subgroup.map_map, Work.BMAX.map_pResidual_subgroupOf_eq p F X, inf_eq_left.mpr hF]
  have hEeq : Subgroup.map X.subtype (E.subgroupOf X) = E := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hE]
  rw [Subgroup.map_sup, hFeq, hEeq, ← Work.BMAX.pResidualIn.eq_map X] at hmap
  exact hmap

/-! ## 5. The crux: `⁅O_p(B) ⊓ A, O^p(S)⁆ = ⊥` -/

theorem commutator_pCoreIn_inf_pResidualIn_witness {G : Type} [Group G] [Finite G]
    (A B S : Subgroup G) (hSB : S ≤ B) (hSf : S ≤ Work.GW2.fstarIn A)
    (hSl : Work.GW2.layerIn A ≤ S) (p : ℕ) (hp : p.Prime) :
    ⁅Work.GW2.pCoreIn p B ⊓ A, Work.BMAX.pResidualIn p S⁆ = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hSA : S ≤ A := hSf.trans (Work.GW2.fstarIn_le_self A)
  have hFA : Work.GW2.fittingIn A ≤ A := Work.GW2.fittingIn_le_self A
  have hEA : Work.GW2.layerIn A ≤ A := Work.GW2.layerIn_le_self A
  have hAF : A ≤ Subgroup.normalizer ((Work.GW2.fittingIn A : Subgroup G) : Set G) :=
    Work.BMAX.le_normalizer_fittingIn A
  have hAE : A ≤ Subgroup.normalizer ((Work.GW2.layerIn A : Subgroup G) : Set G) :=
    Work.BMAX.le_normalizer_layerIn A
  have hAR : A ≤ Subgroup.normalizer
      ((Work.BMAX.pResidualIn p (Work.GW2.fittingIn A) : Subgroup G) : Set G) :=
    le_normalizer_pResidualIn_of_le_normalizer hAF
  -- ### the decomposition `O^p(S) ≤ O^p(F(A) ⊓ S) ⊔ E(A)`
  have hSFE : S ≤ Work.GW2.fittingIn A ⊔ Work.GW2.layerIn A := by
    rw [← Work.GW2.fstarIn_eq_sup]; exact hSf
  have hSF' : S ≤ (Work.GW2.fittingIn A ⊓ S) ⊔ Work.GW2.layerIn A :=
    le_sup_inf_of_normal_aux hFA hEA hAF hAE hSA hSFE hSl
  have hFn2 : S ≤ Subgroup.normalizer
      (((Work.GW2.fittingIn A ⊓ S : Subgroup G)) : Set G) :=
    le_normalizer_inf (X := Work.GW2.fittingIn A) (Y := S) (Z := S)
      (hSA.trans hAF) Subgroup.le_normalizer
  have hdecomp : Work.BMAX.pResidualIn p S ≤
      Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S) ⊔ Work.GW2.layerIn A :=
    pResidualIn_le_sup_pResidualIn_ambient (X := S) (F := Work.GW2.fittingIn A ⊓ S)
      (E := Work.GW2.layerIn A) inf_le_right hSl hFn2 (hSA.trans hAE) hSF' p hp
  -- ### the two halves
  have hR'A : Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S) ≤ A :=
    (Work.BMAX.pResidualIn.le _).trans (le_trans inf_le_right hSA)
  have hR'R : Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S) ≤
      Work.BMAX.pResidualIn p (Work.GW2.fittingIn A) :=
    Work.BMAX.pResidualIn.mono inf_le_left
  have hR'B : Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S) ≤ B :=
    (Work.BMAX.pResidualIn.le _).trans (le_trans inf_le_right hSB)
  -- (ii) `⁅D, O^p(F(A) ⊓ S)⁆ = ⊥`
  have hR'F : Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S) ≤ Work.GW2.fittingIn A :=
    (Work.BMAX.pResidualIn.le _).trans inf_le_left
  have h2 : ⁅Work.GW2.pCoreIn p B ⊓ A,
      Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S)⁆ = ⊥ := by
    have hOpB : ⁅Work.GW2.pCoreIn p B ⊓ A,
        Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S)⁆ ≤ Work.GW2.pCoreIn p B :=
      (Subgroup.commutator_mono inf_le_left le_rfl).trans
        ((Subgroup.le_normalizer_iff_commutator_le_left
          (H := Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S))
          (K := Work.GW2.pCoreIn p B)).mp
          (hR'B.trans (Work.BMAX.le_normalizer_pCoreIn_of_primeFirst p B)))
    have hA : ⁅Work.GW2.pCoreIn p B ⊓ A,
        Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S)⁆ ≤ A :=
      (Subgroup.commutator_le_sup
        (Work.GW2.pCoreIn p B ⊓ A) (Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S))).trans
        (sup_le inf_le_right hR'A)
    have hF : ⁅Work.GW2.pCoreIn p B ⊓ A,
        Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S)⁆ ≤ Work.GW2.fittingIn A :=
      (Subgroup.commutator_mono inf_le_right hR'F).trans
        ((Subgroup.le_normalizer_iff_commutator_le_right
          (H := A) (K := Work.GW2.fittingIn A)).mp hAF)
    have h1 : ⁅Work.GW2.pCoreIn p B ⊓ A,
        Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S)⁆ ≤ Work.GW2.pCoreIn p A :=
      (le_inf (le_inf hA hOpB) hF).trans
        (Work.BMAX.inf_fittingIn_le_pCoreIn_of_le_pCoreIn A B
          (A ⊓ Work.GW2.pCoreIn p B) p hp inf_le_right inf_le_left)
    have h3 : ⁅Work.GW2.pCoreIn p B ⊓ A,
        Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S)⁆ ≤
        Work.BMAX.pResidualIn p (Work.GW2.fittingIn A) :=
      (Subgroup.commutator_mono inf_le_right hR'R).trans
        ((Subgroup.le_normalizer_iff_commutator_le_right
          (H := A) (K := Work.BMAX.pResidualIn p (Work.GW2.fittingIn A))).mp hAR)
    exact le_bot_iff.mp ((le_inf h1 h3).trans
      (le_of_eq (Work.BMAX.pCoreIn_inf_pResidualIn_fittingIn_eq_bot A p hp)))
  -- (iii) `⁅D, E(A)⁆ = ⊥`
  have hDpg : IsPGroup p ↥(Work.GW2.pCoreIn p B ⊓ A) :=
    (Work.BMAX.isPGroup_pCoreIn B).to_le inf_le_left
  have h3 : ⁅Work.GW2.pCoreIn p B ⊓ A, Work.GW2.layerIn A⁆ = ⊥ := by
    haveI : Group.IsNilpotent ↥(Work.GW2.pCoreIn p B ⊓ A) := hDpg.isNilpotent
    haveI : Group.IsSolvable ↥(Work.GW2.pCoreIn p B ⊓ A) := IsNilpotent.to_isSolvable
    have hcent : Work.GW2.layerIn A ≤ Subgroup.centralizer
        (((Work.GW2.pCoreIn p B ⊓ A : Subgroup G)) : Set G) :=
      Work.BMAX.layerIn_le_centralizer_of_solvable (A := A)
        (L := Work.GW2.pCoreIn p B ⊓ A) inferInstance
        (inf_le_right.trans hAE)
        (le_normalizer_inf (X := Work.GW2.pCoreIn p B) (Y := A) (Z := Work.GW2.layerIn A)
          ((hSl.trans hSB).trans (Work.BMAX.le_normalizer_pCoreIn_of_primeFirst p B))
          ((hSl.trans hSA).trans Subgroup.le_normalizer))
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp hcent
  -- ### assembly
  have hDZ : Work.GW2.pCoreIn p B ⊓ A ≤ Subgroup.centralizer
      (((Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S) ⊔
        Work.GW2.layerIn A : Subgroup G)) : Set G) :=
    le_centralizer_sup_aux
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)
  have hZW : ⁅Work.GW2.pCoreIn p B ⊓ A,
      Work.BMAX.pResidualIn p (Work.GW2.fittingIn A ⊓ S) ⊔ Work.GW2.layerIn A⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDZ
  exact le_bot_iff.mp
    ((Subgroup.commutator_mono le_rfl hdecomp).trans (le_of_eq hZW))

/-! ## 6. The target -/

theorem CommutatorWitnessFinal {G : Type} [Group G] [Finite G]
    (hG : IsSimpleGroup G) (A B S : Subgroup G) (hA : IsCoatom A) (hB : B ≠ ⊤)
    (hA_dih : Work.GW2.DihOrCycSylow A) (hA_D : Work.GW2.IsDGroup A)
    (hB_dih : Work.GW2.DihOrCycSylow B) (hB_D : Work.GW2.IsDGroup B)
    (hSB : S ≤ B) (hSf : S ≤ Work.GW2.fstarIn A)
    (hSl : Work.GW2.layerIn A ≤ S) (hZs : Work.GW2.zcenterIn (Work.GW2.fittingIn A) ≤ S)
    (p : ℕ) (hp : p.Prime) (hpi : p ∈ Work.GW2.primesOf (Work.GW2.fittingIn A)) :
    ⁅Work.GW2.pCoreIn p B, Work.BMAX.pResidualIn p S⁆ = ⊥ := by
  refine Work.BMAX.commutator_pCoreIn_pResidualIn_of_coatom_facts A B S p hp ?_ ?_ ?_ hSB ?_
  · exact (Work.BMAX.pCoreIn_le_self p (Work.GW2.zcenterIn (Work.GW2.fittingIn A))).trans
      (hZs.trans hSB)
  · exact (Work.BMAX.pCoreIn_le_self p (Work.GW2.zcenterIn (Work.GW2.fittingIn A))).trans
      (Work.BMAX.zcenterIn_fittingIn_le_centralizer hSf)
  · exact Work.BMAX.centralizer_pCoreIn_zcenterIn_fittingIn_le_coatom hG A hA p hp hpi
  · exact commutator_pCoreIn_inf_pResidualIn_witness A B S hSB hSf hSl p hp

end Work.BMAX
