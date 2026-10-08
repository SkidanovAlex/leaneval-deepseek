import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.map_fittingPiIn_le
import Submission.Work.DSTR.fittingPiIn_subgroupOf
import Submission.Work.DSTR.fittingPiIn_map_conj
import Submission.Work.DSTR.conj_pCoreIn_le_sup_of_mem
import Submission.Work.DSTR.mem_fittingPiIn_of_mem_fittingIn_of_odd_order
import Submission.Work.DSTR.fittingPiIn_conj_hard_not_mem_sup

/-! GW design 25, part C: `fittingPiIn_centralizer_transfer` with `Odd (Nat.card N)`; verbatim copy of
the DSTR proof except the hard case, which is now `Core25a.fittingPiIn_conj_le_sup_of_not_mem_sup_odd`. -/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.DSTR

open Subgroup
open scoped Pointwise

/-- Conjugation by an element of `N ◁ G` carries a subgroup into `H ⊔ N`.  (Local restatement of
`Work.DSTR.map_conj_le_sup_of_mem`.) -/
theorem map_conj_le_sup_of_mem' {G : Type*} [Group G] (N H : Subgroup G) [N.Normal] {n : G}
    (hn : n ∈ N) : H.map (MulAut.conj n).toMonoidHom ≤ H ⊔ N :=
  map_conj_le_sup_of_mem N hn H

/-- **Case 1 of the key step.**  If `y ∈ N ⊔ C_G(t)` then conjugating `F_{2'}(C_G(t))` by `y`
lands in `F_{2'}(C_G(t)) ⊔ N`. -/
theorem fittingPiIn_map_conj_le_sup_of_mem_sup {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (t y : G)
    (hy : y ∈ N ⊔ Subgroup.centralizer ({t} : Set G)) :
    (Work.GW2.fittingPiIn ({k : ℕ | k ≠ 2} : Set ℕ)
        (Subgroup.centralizer ({t} : Set G))).map (MulAut.conj y).toMonoidHom
      ≤ Work.GW2.fittingPiIn ({k : ℕ | k ≠ 2} : Set ℕ)
          (Subgroup.centralizer ({t} : Set G)) ⊔ N := by
  classical
  set K : Subgroup G := Subgroup.centralizer ({t} : Set G) with hK
  set F : Subgroup G := Work.GW2.fittingPiIn ({k : ℕ | k ≠ 2} : Set ℕ) K with hF
  -- decompose `y = k * n` with `k ∈ K`, `n ∈ N`
  have hy' : y ∈ (K ⊔ N : Subgroup G) := by rw [sup_comm]; exact hy
  have hy'' : y ∈ (K : Set G) * (N : Set G) := by
    rw [← Subgroup.mul_normal K N]; exact hy'
  obtain ⟨k, hk, n, hn, hkn⟩ := hy''
  -- conjugation by `k ∈ K` fixes `K`, hence `F`
  have hKm : K.map (MulAut.conj k).toMonoidHom = K := by
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      show k * w * k⁻¹ ∈ K
      exact K.mul_mem (K.mul_mem hk hw) (K.inv_mem hk)
    · intro z hz
      refine Subgroup.mem_map.mpr ⟨k⁻¹ * z * k, ?_, ?_⟩
      · exact K.mul_mem (K.mul_mem (K.inv_mem hk) hz) hk
      · show k * (k⁻¹ * z * k) * k⁻¹ = z
        group
  have hNm : N.map (MulAut.conj k).toMonoidHom = N := by
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      show k * w * k⁻¹ ∈ N
      simpa using Subgroup.Normal.conj_mem inferInstance w hw k
    · intro z hz
      refine Subgroup.mem_map.mpr ⟨k⁻¹ * z * k, ?_, ?_⟩
      · simpa using Subgroup.Normal.conj_mem inferInstance z hz k⁻¹
      · show k * (k⁻¹ * z * k) * k⁻¹ = z
        group
  have hmapk : F.map (MulAut.conj k).toMonoidHom = F := by
    rw [hF, fittingPiIn_map_conj, hKm]
  have hconj_mul : MulAut.conj y = MulAut.conj k * MulAut.conj n := by
    rw [← hkn, map_mul]
  have hcomp : (MulAut.conj k * MulAut.conj n).toMonoidHom
      = (MulAut.conj k).toMonoidHom.comp (MulAut.conj n).toMonoidHom :=
    MonoidHom.ext fun z => by
      show (MulAut.conj k * MulAut.conj n) z = (MulAut.conj k) ((MulAut.conj n) z)
      rfl
  calc F.map (MulAut.conj y).toMonoidHom
      = F.map (MulAut.conj k * MulAut.conj n).toMonoidHom := by rw [hconj_mul]
    _ = F.map ((MulAut.conj k).toMonoidHom.comp (MulAut.conj n).toMonoidHom) := by rw [hcomp]
    _ = (F.map (MulAut.conj n).toMonoidHom).map (MulAut.conj k).toMonoidHom := by
          rw [Subgroup.map_map]
    _ ≤ (F ⊔ N).map (MulAut.conj k).toMonoidHom :=
          Subgroup.map_mono (map_conj_le_sup_of_mem N hn F)
    _ = F ⊔ N := by rw [Subgroup.map_sup, hmapk, hNm]

/-- **Fitting transfer with centralizers (self-contained version).**  Let `G` be a finite group,
`N ◁ G` and `t ∈ G` with `t² = 1`.  Then the image of `F_{2'}(C_G(t))` under `G →* G ⧸ N` lies in
`F_{2'}(C_{G⧸N}(t N))`.

This is the crux step of `D110iiProp`: the centralizer of `tN` in the quotient can be strictly
larger than the image of `C_G(t)`, so the argument must use that `π(C_G(t))` is *normal* in
`C_{G/N}(tN)` (which holds since `t` is an involution), and then that the image of the normal
nilpotent `2'`-subgroup `O_{2'}(F(C_G(t)))` is a normal nilpotent `2'`-subgroup there. -/
theorem fittingPiIn_centralizer_transfer_odd {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N)) (t x : G) (ht : orderOf t = 2)
    (hxK : x ∈ Subgroup.centralizer ({t} : Set G))
    (hx : x ∈ Work.GW2.fittingPiIn {n : ℕ | n ≠ 2} (Subgroup.centralizer ({t} : Set G))) :
    (QuotientGroup.mk' N) x ∈ Work.GW2.fittingPiIn {n : ℕ | n ≠ 2}
      (Subgroup.centralizer ({(QuotientGroup.mk' N) t} : Set (G ⧸ N))) := by
  classical
  set f : G →* G ⧸ N := QuotientGroup.mk' N with hf
  set K : Subgroup G := Subgroup.centralizer ({t} : Set G) with hK
  set J : Subgroup (G ⧸ N) := Subgroup.centralizer ({f t} : Set (G ⧸ N)) with hJ
  set F : Subgroup G := Work.GW2.fittingPiIn ({n : ℕ | n ≠ 2} : Set ℕ) K with hF
  set H : Subgroup G := J.comap f with hH
  have hxK' : x ∈ K := by rw [hK]; exact hxK
  have hx' : x ∈ F := by rw [hF]; exact hx
  -- `F ≤ K ≤ H`
  have hFK : F ≤ K := by rw [hF, hK]; exact Subgroup.map_subtype_le _
  have hKH : K ≤ H := by
    intro z hz
    rw [hH, Subgroup.mem_comap, hJ, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subgroup.mem_centralizer_iff.mp hz t rfl)
  have hxH : x ∈ H := hKH (hFK hx')
  by_cases hFN : F ≤ N
  · -- trivial case: `x ∈ N`, so the image of `x` is `1`
    have hxN : x ∈ N := hFN hx'
    have hx1 : f x = 1 := by
      rw [hf]
      exact (QuotientGroup.eq_one_iff x).mpr hxN
    rw [hx1]
    exact Subgroup.one_mem _
  · -- main case
    -- key step: for `y ∈ H`, conjugation by `y` keeps `F` inside `F ⊔ N`
    have hconj : ∀ y ∈ H, F.map (MulAut.conj y).toMonoidHom ≤ F ⊔ N := by
      intro y hyH
      by_cases hyNK : y ∈ N ⊔ K
      · rw [hF, hK]
        exact fittingPiIn_map_conj_le_sup_of_mem_sup N t y hyNK
      · -- hard case: `y ∉ C_G(t) ⊔ N`
        have hyJ : f y ∈ J := Subgroup.mem_comap.mp (by rw [← hH]; exact hyH)
        have hcomm : f y * f t = f t * f y :=
          (Subgroup.mem_centralizer_iff.mp hyJ (f t) (Set.mem_singleton _)).symm
        have h1 : f (y * t * y⁻¹) = f t := by
          rw [map_mul, map_mul, map_inv, hcomm]
          group
        have h3 : f (y * t * y⁻¹ * t⁻¹) = 1 := by
          rw [map_mul, h1, map_inv, mul_inv_cancel]
        have hyN : y * t * y⁻¹ * t⁻¹ ∈ N := by
          rw [hf] at h3
          exact (QuotientGroup.eq_one_iff _).mp h3
        have hynot : y ∉ K ⊔ N := by
          intro hmem
          exact hyNK (by rw [sup_comm]; exact hmem)
        have hle : F.map (MulAut.conj y).toMonoidHom ≤ F ⊔ N := by
          rw [hK] at hynot
          rw [hF, hK] at hFN ⊢
          exact fittingPiIn_conj_le_sup_of_not_mem_sup_odd N hNodd t y ht hyN hynot hFN
        exact hle
    -- `F̄ = F.map f` is normal in `↥J`
    have hFJ : F.map f ≤ J := by
      rintro z ⟨w, hw, rfl⟩
      exact Subgroup.mem_comap.mp (hKH (hFK hw))
    have hNbot : N.map f = ⊥ := by
      refine le_antisymm ?_ bot_le
      rintro z ⟨w, hw, rfl⟩
      rw [hf]
      exact (QuotientGroup.eq_one_iff w).mpr hw
    have hnormJ : ((F.map f).comap J.subtype).Normal := by
      refine ⟨fun z hz j => ?_⟩
      rw [Subgroup.mem_comap] at hz ⊢
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N (j : G ⧸ N)
      obtain ⟨m, hm, hmz⟩ := Subgroup.mem_map.mp hz
      have hyH : y ∈ H := by
        rw [hH, Subgroup.mem_comap, hf, hy]
        exact j.2
      have hmF : m ∈ F := by rwa [hF] at hm
      have hmem : y * m * y⁻¹ ∈ F ⊔ N := hconj y hyH ⟨m, hmF, rfl⟩
      have hfin : f (y * m * y⁻¹) ∈ F.map f := by
        have h2 : (F ⊔ N).map f = F.map f := by
          rw [Subgroup.map_sup, hNbot, sup_bot_eq]
        rw [← h2]
        exact Subgroup.mem_map.mpr ⟨y * m * y⁻¹, hmem, rfl⟩
      have heq : J.subtype (j * z * j⁻¹) = f (y * m * y⁻¹) := by
        change ((j * z * j⁻¹ : ↥J) : G ⧸ N) = f (y * m * y⁻¹)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          show ((j : ↥J) : G ⧸ N) = f y from hy.symm,
          show ((z : ↥J) : G ⧸ N) = f m from hmz.symm, hf]
        simp only [map_mul, map_inv]
      rw [heq]
      exact hfin
    -- nilpotency of `F`
    haveI hnilFit : Group.IsNilpotent ↥(Work.GW2.fitting ↥K) := by
      rw [FittingPiImg.fitting_eq_isaacsFitting (G := ↥K)]
      exact OddOrder.Isaacs.Ch01.fitting.isNilpotent
    haveI hnilFI : Group.IsNilpotent ↥(Work.GW2.fittingIn K) := by
      rw [Work.GW2.fittingIn]
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.equivMapOfInjective (Work.GW2.fitting ↥K) K.subtype K.subtype_injective)
    have hFle : F ≤ Work.GW2.fittingIn K := by
      rw [hF, Work.GW2.fittingIn]
      exact Subgroup.map_mono (Subgroup.map_subtype_le _)
    haveI hnilF : Group.IsNilpotent ↥F := by
      haveI : Group.IsNilpotent ↥(F.subgroupOf (Work.GW2.fittingIn K)) := inferInstance
      exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFle)
    haveI hnilFbar : Group.IsNilpotent ↥(F.map f) := by
      refine Group.nilpotent_of_surjective
        ((f.comp F.subtype).codRestrict (F.map f) (fun w => Subgroup.mem_map_of_mem f w.2)) ?_
      rintro ⟨z, hz⟩
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      exact ⟨⟨w, hw⟩, rfl⟩
    haveI hnilFbarJ : Group.IsNilpotent ↥((F.map f).comap J.subtype) := by
      rw [Subgroup.comap_subtype]
      exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFJ).symm
    have hsub : ((F.map f).comap J.subtype) ≤ Work.GW2.fitting ↥J := by
      haveI : ((F.map f).comap J.subtype).Normal := hnormJ
      refine Subgroup.normal_le_normalCore.mpr (le_sSup ⟨inferInstance, ?_⟩)
      exact hnilFbarJ
    -- conclusion
    have hle : F.map f ≤ Work.GW2.fittingPiIn ({n : ℕ | n ≠ 2} : Set ℕ) J := by
      intro z hz
      have hzJ : z ∈ J := hFJ hz
      have hzfit : z ∈ Work.GW2.fittingIn J := by
        rw [Work.GW2.fittingIn]
        exact Subgroup.mem_map.mpr ⟨⟨z, hzJ⟩, hsub hz, rfl⟩
      have hzodd : Odd (orderOf z) := by
        have h1 : z ∈ Work.GW2.fittingPiIn ({n : ℕ | n ≠ 2} : Set ℕ) (K.map f) :=
          map_fittingPiIn_le f (QuotientGroup.mk'_surjective N) K (by rw [← hF]; exact hz)
        exact Work.DSTR.M110.oddOrderOf_mem_fittingPiIn _ z h1
      exact mem_fittingPiIn_of_mem_fittingIn_of_odd_order J hzfit hzodd
    exact hle (Subgroup.mem_map.mpr ⟨x, hx', rfl⟩)

end Work.DSTR
