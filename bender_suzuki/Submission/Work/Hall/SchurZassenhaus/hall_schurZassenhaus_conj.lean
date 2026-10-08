import Mathlib
import Submission.Work.Hall.Basic
import Submission.Work.Hall.MinimalNormal.hall_minimalNormal_isElementaryAbelian
import Submission.Work.Hall.SchurZassenhaus.hall_sz_conj_abelian
import Submission.Work.Hall.HallAPI.hall_card_comap_mk
import Submission.Work.Hall.HallAPI.hall_isHall_eq_of_le
import Submission.Work.Hall.Transport.hall_map_mulAut_conj
import Submission.Work.Hall.SchurZassenhaus.sz_complement_map_mk
import Submission.Work.Hall.SchurZassenhaus.sz_card_map_mk_lt
import Submission.Work.Hall.SchurZassenhaus.sz_exists_minimalNormal_le
import Submission.Work.Hall.SchurZassenhaus.sz_abelian_step_coprime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Schur--Zassenhaus: conjugacy of complements of a solvable normal Hall subgroup

If `N` is a normal Hall subgroup of a finite group `G` (that is, `|N|` is coprime to its
index `[G : N]`) and `N` is solvable, then any two complements of `N` are conjugate.

The proof is by strong induction on `|N|`.

* If `N = ⊥` the two complements are both `⊤`.
* If `N` is abelian we apply the abelian Schur--Zassenhaus theorem (`hall_sz_conj_abelian`).
* Otherwise pick a nontrivial minimal normal subgroup `M ≤ N` (`sz_exists_minimal_normal_le`).
  As `N` is solvable, `M` is abelian.  Both complements have the same image in `G ⧸ M`
  (`sz_complement_map_mk`), and the induction hypothesis conjugates them there; after lifting
  the conjugating element to `G` the two complements generate the same subgroup `L = M ⊔ H`
  on which `M` is an abelian normal Hall subgroup, and the abelian case (`sz_abelian_step_coprime`)
  finishes the job.
-/

open scoped Pointwise

set_option linter.style.haveILetI false

namespace Work.Hall.SchurZassenhaus

theorem sz_solvable_map_mk {G : Type*} [Group G] {N M : Subgroup G} [M.Normal]
    (h : Group.IsSolvable ↥N) : Group.IsSolvable ↥(N.map (QuotientGroup.mk' M)) := by
  haveI : Group.IsSolvable ↥N := h
  let f : ↥N →* ↥(N.map (QuotientGroup.mk' M)) :=
    { toFun := fun x => ⟨(QuotientGroup.mk' M) (x : G), ⟨x, x.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one (QuotientGroup.mk' M))
      map_mul' := fun a b => Subtype.ext (map_mul (QuotientGroup.mk' M) (a : G) (b : G)) }
  exact Group.isSolvable_of_surjective (f := f) (fun y => by
    obtain ⟨n, hn, hnk⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨n, hn⟩, Subtype.ext hnk⟩)

theorem sz_coprime_map_mk {G : Type*} [Group G] [Finite G] {N M : Subgroup G} [N.Normal] [M.Normal]
    (hMN : M ≤ N) (hc : (Nat.card ↥N).Coprime N.index) :
    (Nat.card ↥(N.map (QuotientGroup.mk' M))).Coprime (N.map (QuotientGroup.mk' M)).index := by
  have hidx : (N.map (QuotientGroup.mk' M)).index = N.index :=
    Subgroup.index_map_eq N (QuotientGroup.mk'_surjective M)
      (by rw [QuotientGroup.ker_mk']; exact hMN)
  rw [hidx]
  refine hc.coprime_dvd_left ⟨Nat.card ↥M, ?_⟩
  have h1 : Nat.card ↥N = Nat.card ↥M * Nat.card ↥(N.map (QuotientGroup.mk' M)) := by
    rw [← Work.Hall.HallAPI.hall_card_comap_mk (N := M) (Hbar := N.map (QuotientGroup.mk' M)),
      Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hMN]
  rw [h1, Nat.mul_comm]

universe u

private theorem sz_conj_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G] (N : Subgroup G), N.Normal →
      Group.IsSolvable ↥N → Nat.card ↥N = n → (Nat.card ↥N).Coprime N.index →
      ∀ H K : Subgroup G, N.IsComplement' H → N.IsComplement' K →
      ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro G _ _ N hNnorm hsol hcard hc H K hH hK
    haveI : N.Normal := hNnorm
    by_cases hNbot : N = ⊥
    · have hHtop : H = ⊤ := Subgroup.isComplement'_bot_left.mp (hNbot ▸ hH)
      have hKtop : K = ⊤ := Subgroup.isComplement'_bot_left.mp (hNbot ▸ hK)
      refine ⟨1, ?_⟩
      rw [hHtop, hKtop]
      exact (Subgroup.map_top_of_surjective _ (MulAut.conj (1 : G)).surjective).symm
    · by_cases hab : IsMulCommutative ↥N
      · exact hall_sz_conj_abelian hc hH hK
      · obtain ⟨M, hMmin, hMN⟩ := sz_exists_minimalNormal_le (G := G) hNbot
        have hMnorm : M.Normal := hMmin.1
        have hMne : M ≠ ⊥ := hMmin.2.1
        haveI : M.Normal := hMnorm
        have hMsolv : Group.IsSolvable ↥M := by
          haveI : Group.IsSolvable ↥N := hsol
          let f : ↥(M.comap N.subtype) →* ↥M :=
            { toFun := fun x => ⟨(x : ↥N), Subgroup.mem_comap.mp x.2⟩
              map_one' := Subtype.ext rfl
              map_mul' := fun a b => Subtype.ext rfl }
          exact Group.isSolvable_of_surjective (f := f) (fun m =>
            ⟨⟨⟨(m : G), hMN m.2⟩, Subgroup.mem_comap.mpr m.2⟩, Subtype.ext rfl⟩)
        have hMcomm : IsMulCommutative ↥M :=
          Work.Hall.MinimalNormal.isMulCommutative_of_isMinimalNormal_of_isSolvable hMmin hMsolv
        haveI : IsMulCommutative ↥M := hMcomm
        have hNqnorm : (N.map (QuotientGroup.mk' M)).Normal :=
          Subgroup.Normal.map hNnorm (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
        have hHq : (N.map (QuotientGroup.mk' M)).IsComplement' (H.map (QuotientGroup.mk' M)) :=
          sz_complement_map_mk hMN hH
        have hKq : (N.map (QuotientGroup.mk' M)).IsComplement' (K.map (QuotientGroup.mk' M)) :=
          sz_complement_map_mk hMN hK
        have hsolq : Group.IsSolvable ↥(N.map (QuotientGroup.mk' M)) := sz_solvable_map_mk hsol
        have hcq : (Nat.card ↥(N.map (QuotientGroup.mk' M))).Coprime
            (N.map (QuotientGroup.mk' M)).index := sz_coprime_map_mk hMN hc
        have hcardlt : Nat.card ↥(N.map (QuotientGroup.mk' M)) < n := by
          rw [← hcard]; exact sz_card_map_mk_lt hMN hMne
        haveI : Finite (G ⧸ M) :=
          Finite.of_surjective (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
        obtain ⟨gq, hgq⟩ := ih (Nat.card ↥(N.map (QuotientGroup.mk' M))) hcardlt (G ⧸ M)
          (N.map (QuotientGroup.mk' M)) hNqnorm hsolq rfl hcq
          (H.map (QuotientGroup.mk' M)) (K.map (QuotientGroup.mk' M)) hHq hKq
        obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective M gq
        rw [← hx] at hgq
        rw [Work.Hall.Transport.hall_map_mulAut_conj (QuotientGroup.mk' M) H x] at hgq
        have hsup : (H.map (MulAut.conj x).toMonoidHom) ⊔ M = K ⊔ M := by
          have hA : (K.map (QuotientGroup.mk' M)).comap (QuotientGroup.mk' M) = K ⊔ M := by
            rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
          have hB : ((H.map (MulAut.conj x).toMonoidHom).map (QuotientGroup.mk' M)).comap
              (QuotientGroup.mk' M) = (H.map (MulAut.conj x).toMonoidHom) ⊔ M := by
            rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
          rw [← hA, ← hB, hgq]
        have hHd : (H.map (MulAut.conj x).toMonoidHom) ⊓ M = ⊥ := by
          rw [← le_bot_iff]
          rintro z ⟨hzH, hzM⟩
          obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp (show z ∈ Subgroup.map (MulAut.conj x).toMonoidHom H from hzH)
          have hzN : (MulAut.conj x) h ∈ N := hMN hzM
          have hhN : h ∈ N := by
            have h2 := hNnorm.conj_mem ((MulAut.conj x) h) hzN x⁻¹
            rw [MulAut.conj_apply] at h2
            have heq : x⁻¹ * (x * h * x⁻¹) * (x⁻¹)⁻¹ = h := by group
            rwa [heq] at h2
          have h1 : h = 1 := Subgroup.mem_bot.mp
            (disjoint_iff_inf_le.mp hH.disjoint (show h ∈ N ⊓ H from ⟨hhN, hh⟩))
          subst h1
          exact map_one _
        have hKd : K ⊓ M = ⊥ := by
          rw [← le_bot_iff]
          rintro z ⟨hzK, hzM⟩
          exact Subgroup.mem_bot.mp
            (disjoint_iff_inf_le.mp hK.disjoint (show z ∈ N ⊓ K from ⟨hMN hzM, hzK⟩))
        have hcardH : Nat.card ↥H = N.index := Subgroup.IsComplement.card_right hH
        have hcardHx : Nat.card ↥(H.map (MulAut.conj x).toMonoidHom) = N.index := by
          rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hcardH]
        have hMdiv : Nat.card ↥M ∣ Nat.card ↥N :=
          ⟨M.relIndex N, by rw [← Work.Hall.HallAPI.relIndex_mul_card_of_le hMN]; exact Nat.mul_comm _ _⟩
        have hc' : (Nat.card ↥M).Coprime (Nat.card ↥(H.map (MulAut.conj x).toMonoidHom)) := by
          rw [hcardHx]; exact hc.coprime_dvd_left hMdiv
        obtain ⟨y, hy⟩ := sz_abelian_step_coprime hc' hsup hHd hKd
        refine ⟨y * x, ?_⟩
        calc K = (H.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom := hy
          _ = H.map (MulAut.conj (y * x)).toMonoidHom := by
                rw [Subgroup.map_map]
                congr 1
                ext h
                simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
                group

theorem hall_schurZassenhaus_conj {G : Type*} [Group G] [Finite G] {N H K : Subgroup G} [N.Normal]
    (hsol : Group.IsSolvable N) (hc : (Nat.card N).Coprime N.index) (hH : N.IsComplement' H)
    (hK : N.IsComplement' K) : ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom :=
  sz_conj_aux (Nat.card N) G N inferInstance hsol rfl hc H K hH hK

end Work.Hall.SchurZassenhaus
