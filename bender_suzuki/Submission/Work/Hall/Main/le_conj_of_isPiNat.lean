import Mathlib
import Submission.Work.Hall.Basic
import Submission.Work.Hall.MinimalNormal.hall_exists_isMinimalNormal
import Submission.Work.Hall.MinimalNormal.hall_minimalNormal_isElementaryAbelian
import Submission.Work.Hall.MinimalNormal.hall_isPiNat_card_of_isElementaryAbelian
import Submission.Work.Hall.MinimalNormal.hall_isElementaryAbelian_prime_dvd_card
import Submission.Work.Hall.PiNat.hall_coprime_of_isPiNat
import Submission.Work.Hall.PiNat.hall_eq_one_of_isPiNat
import Submission.Work.Hall.HallAPI.hall_isHall_map_mk
import Submission.Work.Hall.HallAPI.hall_isHall_comap_mk
import Submission.Work.Hall.HallAPI.hall_card_comap_mk
import Submission.Work.Hall.HallAPI.hall_isHall_relIndex
import Submission.Work.Hall.Transport.hall_map_mulAut_conj
import Submission.Work.Hall.Transport.hall_map_subtype_comap_of_le
import Submission.Work.Hall.Transport.hall_card_comap_subtype_of_le
import Submission.Work.Hall.Transport.hall_relIndex_sup_right_of_normalizes
import Submission.Work.Hall.Transport.hall_map_subtype_mulAut_conj
import Submission.Work.Hall.SchurZassenhaus.hall_sz_conj_abelian

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `D_π` (P. Hall): every `π`-subgroup lies in a conjugate of a given Hall `π`-subgroup

`Work.Hall.Main.le_conj_of_isPiNat` is the "conjugacy part" of P. Hall's theorem `D_π` for a finite
solvable group `G`: if `H` is a Hall `π`-subgroup of `G` and `K` is any `π`-subgroup of `G`
(`|K|` is a `π`-number), then `K` is contained in a conjugate of `H`.

The proof is by strong induction on `|G|`, using a minimal normal subgroup `N` of `G` (which is
elementary abelian because `G` is solvable), the case distinction `p ∈ π` / `p ∉ π` for the
prime `p` associated with `N`, and Schur–Zassenhaus (abelian case) when both `K` and `H` are
complements of `N`.

This module is self-contained: the few auxiliary facts it needs (which are private to the
argument) are proved below rather than imported from a mutable scratch file.
-/

set_option maxHeartbeats 1600000

open scoped Pointwise

open Work.Hall

universe u

namespace Work.Hall.Main

open Subgroup
/-- In a group in which `⊤` is a minimal normal subgroup and which is abelian (which is the case
for a solvable group in which `⊤` is minimal normal), every subgroup is `⊥` or `⊤`. -/
private theorem eq_bot_or_eq_top_of_minimalNormal_top {G : Type*} [Group G] [IsMulCommutative G]
    (h : IsMinimalNormal (⊤ : Subgroup G)) (M : Subgroup G) : M = ⊥ ∨ M = ⊤ := by
  by_cases hM : M = ⊥
  · exact Or.inl hM
  · exact Or.inr (le_antisymm le_top (h.2.2 M inferInstance le_top hM))

/-- In a subsingleton group all subgroups are equal. -/
private theorem subgroup_eq_of_subsingleton {G : Type*} [Group G] [Subsingleton G] (H K : Subgroup G) :
    H = K := by
  refine le_antisymm ?_ ?_ <;> intro x _ <;> rw [Subsingleton.elim x 1] <;> exact Subgroup.one_mem _

/-- If `L ≤ X` has `π`-number order and `[X : L]` is a `π'`-number, then `L` is a Hall
`π`-subgroup of `X`. -/
private theorem isHall_comap_of_isPiNat {G : Type*} [Group G] {π : ℕ → Prop} {X L : Subgroup G}
    (hLX : L ≤ X) (hcard : IsPiNat π (Nat.card L))
    (hidx : IsPiNat (fun p => ¬ π p) (L.relIndex X)) : IsHall π (L.comap X.subtype) :=
  ⟨hcard.of_eq (Transport.hall_card_comap_subtype_of_le hLX),
    hidx.of_eq (rfl : (L.comap X.subtype).index = L.relIndex X)⟩

/-- If `N` is an elementary abelian `p`-subgroup with `p ∉ π`, then `|N|` is a `π'`-number. -/
private theorem isPiNat_card_of_isElementaryAbelian_compl {G : Type*} [Group G] [Finite G] {p : ℕ}
    {π : ℕ → Prop} {N : Subgroup G} (hE : IsElementaryAbelian p N) (hp : p.Prime)
    (hpπ : ¬ π p) : IsPiNat (fun q => ¬ π q) (Nat.card N) :=
  (MinimalNormal.hall_isPiNat_card_of_isElementaryAbelian hE hp).of_eq_prime_compl hpπ

/-- If `N` is an elementary abelian `p`-subgroup with `p ∈ π`, then `|N|` is a `π`-number. -/
private theorem isPiNat_card_of_isElementaryAbelian_pi {G : Type*} [Group G] [Finite G] {p : ℕ}
    {π : ℕ → Prop} {N : Subgroup G} (hE : IsElementaryAbelian p N) (hp : p.Prime)
    (hpπ : π p) : IsPiNat π (Nat.card N) :=
  (MinimalNormal.hall_isPiNat_card_of_isElementaryAbelian hE hp).of_eq_prime hpπ

/-- If `A ≤ B` then `|A|` divides `|B|`. -/
private theorem card_dvd_card_of_le {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B) :
    Nat.card ↥A ∣ Nat.card ↥B := by
  refine ⟨(A.subgroupOf B).index, ?_⟩
  have h1 : Nat.card ↥(A.subgroupOf B) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have h2 : (A.subgroupOf B).index * Nat.card ↥(A.subgroupOf B) = Nat.card ↥B :=
    Subgroup.index_mul_card (A.subgroupOf B)
  rw [h1, mul_comm] at h2
  exact h2.symm

/-- If `N ⊓ Z = ⊥` then `N.subgroupOf Z = ⊥`. -/
private theorem subgroupOf_eq_bot_of_inf_eq_bot {G : Type*} [Group G] {N Z : Subgroup G}
    (h : N ⊓ Z = ⊥) : N.subgroupOf Z = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  refine Subtype.ext (Subgroup.mem_bot.mp ?_)
  rw [← h]
  exact Subgroup.mem_inf.mpr ⟨hx, x.2⟩

/-- If `N ⊓ Z = ⊥` then `N.relIndex Z = |Z|`. -/
private theorem relIndex_eq_card_of_inf_eq_bot {G : Type*} [Group G] {N Z : Subgroup G}
    (h : N ⊓ Z = ⊥) : N.relIndex Z = Nat.card ↥Z := by
  rw [Subgroup.relIndex, subgroupOf_eq_bot_of_inf_eq_bot h, Subgroup.index_bot]

/-- If `Z` and `K` both complement a normal subgroup `N` inside the same subgroup `Y`, then
`|Z| = |K|`. -/
private theorem card_eq_of_sup_eq_of_inf_eq {G : Type*} [Group G] {N Z K Y : Subgroup G} [N.Normal]
    (hZ : N ⊔ Z = Y) (hK : N ⊔ K = Y) (hZi : N ⊓ Z = ⊥) (hKi : N ⊓ K = ⊥) :
    Nat.card ↥Z = Nat.card ↥K := by
  have h1 : N.relIndex Z = N.relIndex Y := by
    rw [← hZ, sup_comm]
    exact (Subgroup.relIndex_sup_right (H := Z) (K := N)).symm
  have h2 : N.relIndex K = N.relIndex Y := by
    rw [← hK, sup_comm]
    exact (Subgroup.relIndex_sup_right (H := K) (K := N)).symm
  rw [← relIndex_eq_card_of_inf_eq_bot hZi, h1, ← h2, relIndex_eq_card_of_inf_eq_bot hKi]

/-- If `N ⊔ K = ⊤` and `N ⊓ K = ⊥` with `N` normal, then `K` is a complement of `N`. -/
private theorem isComplement'_of_sup_eq_top_of_inf_eq_bot {G : Type*} [Group G] {N K : Subgroup G}
    [N.Normal] (hsup : N ⊔ K = ⊤) (hinf : N ⊓ K = ⊥) : N.IsComplement' K := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (by rw [disjoint_iff]; exact hinf) ?_
  refine Set.eq_univ_iff_forall.mpr fun y => ?_
  have hy : y ∈ (N ⊔ K : Subgroup G) := by rw [hsup]; exact Subgroup.mem_top y
  obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  exact Set.mem_mul.mpr ⟨n, hn, k, hk, hnk⟩

/-- `D_π` (P. Hall) by strong induction on `|G|`: every `π`-subgroup of a finite solvable group is
contained in a conjugate of a given Hall `π`-subgroup. -/
private theorem le_conj_of_isPiNat_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → Group.IsSolvable G →
      ∀ {π : ℕ → Prop} {H K : Subgroup G}, IsHall π H → IsPiNat π (Nat.card K) →
        ∃ g : G, K ≤ H.map (MulAut.conj g).toMonoidHom := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro G _ _ hG hsol π H K hH hK
    letI : Group.IsSolvable G := hsol
    rcases subsingleton_or_nontrivial G with hsub | hntriv
    · haveI : Subsingleton G := hsub
      exact ⟨1, le_of_eq (subgroup_eq_of_subsingleton K _)⟩
    · haveI : Nontrivial G := hntriv
      obtain ⟨N, hNmin⟩ := MinimalNormal.hall_exists_isMinimalNormal (G := G)
      haveI hNnorm : N.Normal := hNmin.1
      obtain ⟨p, hp, hE⟩ :=
        MinimalNormal.hall_minimalNormal_isElementaryAbelian hNmin inferInstance
      have hpiN : IsPiNat (fun q => q = p) (Nat.card N) :=
        MinimalNormal.hall_isPiNat_card_of_isElementaryAbelian hE hp
      by_cases htop : N = ⊤
      · have hEt : IsElementaryAbelian p (⊤ : Subgroup G) := htop ▸ hE
        haveI hcommT : IsMulCommutative ↥(⊤ : Subgroup G) := hEt.1
        haveI : IsMulCommutative G := IsMulCommutative.of_comm fun a b =>
          congrArg Subtype.val (mul_comm' (⟨a, trivial⟩ : ↥(⊤ : Subgroup G)) ⟨b, trivial⟩)
        have hdich : ∀ M : Subgroup G, M = ⊥ ∨ M = ⊤ := fun M =>
          eq_bot_or_eq_top_of_minimalNormal_top (htop ▸ hNmin) M
        by_cases hpπ : π p
        · rcases hdich H with hHb | hHt
          · rcases hdich K with hKb | hKt
            · subst hHb; subst hKb; exact ⟨1, by simp⟩
            · exfalso
              have h1 : IsPiNat π (Nat.card G) := by
                rw [← Subgroup.card_top, ← hKt]
                exact hK
              have h2 : IsPiNat (fun q => ¬ π q) (Nat.card G) := by
                rw [← Subgroup.index_bot, ← hHb]
                exact hH.2
              have hc :=
                PiNat.hall_eq_one_of_isPiNat h1 h2 (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
              haveI := (Nat.card_eq_one_iff_unique.mp hc).1
              obtain ⟨a, b, hab⟩ := exists_pair_ne G
              exact hab (Subsingleton.elim a b)
          · subst hHt
            exact ⟨1, by simp⟩
        · have hNpi' : IsPiNat (fun q => ¬ π q) (Nat.card N) :=
            isPiNat_card_of_isElementaryAbelian_compl hE hp hpπ
          have hKdvd : Nat.card K ∣ Nat.card G :=
            ⟨K.index, by rw [mul_comm, Subgroup.index_mul_card]⟩
          have hNpiG : IsPiNat (fun q => ¬ π q) (Nat.card G) := by
            rw [← Subgroup.card_top, ← htop]
            exact hNpi'
          have hKcard : Nat.card K = 1 :=
            PiNat.hall_eq_one_of_isPiNat (π := π) hK (hNpiG.of_dvd hKdvd)
              (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
          have hKbot : K = ⊥ := (Subgroup.eq_bot_iff_card K).mpr hKcard
          refine ⟨1, ?_⟩
          rw [hKbot]
          simp
      · have hNne : N ≠ ⊥ := hNmin.2.1
        have hcardN1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNne
        have hN0 : Nat.card N ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
        have hcardQ : Nat.card (G ⧸ N) < n := by
          rw [← hG, ← Subgroup.index_eq_card]
          calc N.index = N.index * 1 := (Nat.mul_one _).symm
            _ < N.index * Nat.card N :=
                Nat.mul_lt_mul_of_pos_left hcardN1
                  (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
            _ = Nat.card G := Subgroup.index_mul_card N
        by_cases hpπ : π p
        · -- `p ∈ π`: `K ≤ H' ⊔ N = H'`
          have hNpi : IsPiNat π (Nat.card N) := isPiNat_card_of_isElementaryAbelian_pi hE hp hpπ
          obtain ⟨x, hx⟩ := ih (Nat.card (G ⧸ N)) hcardQ (G ⧸ N) rfl inferInstance
            (HallAPI.hall_isHall_map_mk hNpi hH)
            (hK.of_dvd (Subgroup.card_map_dvd K (QuotientGroup.mk' N)))
          obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N x
          set H' : Subgroup G := H.map (MulAut.conj g).toMonoidHom with hH'def
          have hH'hall : IsHall π H' := hH.map_mulAut (MulAut.conj g)
          have hx' : (K.map (QuotientGroup.mk' N)) ≤ H'.map (QuotientGroup.mk' N) := by
            refine hx.trans (le_of_eq ?_)
            rw [← hg, hH'def]
            exact Transport.hall_map_mulAut_conj (QuotientGroup.mk' N) H g
          have hKle : K ≤ H' ⊔ N := by
            have h := Subgroup.comap_mono (f := QuotientGroup.mk' N) hx'
            rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
            exact le_sup_left.trans h
          have hnorm : H' ≤ Subgroup.normalizer (N : Set G) := by
            rw [Subgroup.normalizer_eq_top_iff.mpr hNnorm]; exact le_top
          have hrelH'p : IsPiNat π (H'.relIndex (H' ⊔ N)) := by
            rw [sup_comm, Transport.hall_relIndex_sup_right_of_normalizes hnorm]
            exact hNpi.of_dvd (Subgroup.relIndex_dvd_card H' N)
          have hrelH'c : IsPiNat (fun q => ¬ π q) (H'.relIndex (H' ⊔ N)) :=
            hH'hall.2.of_dvd (Subgroup.relIndex_dvd_index_of_le (show _ ≤ _ ⊔ _ from le_sup_left))
          have hrel1H : H'.relIndex (H' ⊔ N) = 1 := by
            refine PiNat.hall_eq_one_of_isPiNat hrelH'p hrelH'c ?_
            intro h0
            have hd := Subgroup.relIndex_dvd_index_of_le (H := H') (show H' ≤ H' ⊔ N from le_sup_left)
            rw [h0] at hd
            exact Subgroup.index_ne_zero_of_finite (Nat.eq_zero_of_zero_dvd hd)
          have hXle : H' ⊔ N ≤ H' := Subgroup.relIndex_eq_one.mp hrel1H
          exact ⟨g, hKle.trans hXle⟩
        · -- `p ∉ π`
          have hNpi' : IsPiNat (fun q => ¬ π q) (Nat.card N) :=
            isPiNat_card_of_isElementaryAbelian_compl hE hp hpπ
          haveI : IsMulCommutative ↥N := hE.1
          obtain ⟨x, hx⟩ := ih (Nat.card (G ⧸ N)) hcardQ (G ⧸ N) rfl inferInstance
            (isHall_map_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hH)
            (hK.of_dvd (Subgroup.card_map_dvd K (QuotientGroup.mk' N)))
          obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N x
          set H' : Subgroup G := H.map (MulAut.conj g).toMonoidHom with hH'def
          have hH'hall : IsHall π H' := hH.map_mulAut (MulAut.conj g)
          have hH'conj : ∀ a : G,
              H'.map (MulAut.conj a).toMonoidHom = H.map (MulAut.conj (a * g)).toMonoidHom := by
            intro a
            rw [hH'def, Subgroup.map_map]
            congr 1
            ext h
            simp [MonoidHom.comp_apply, MulAut.conj_apply, mul_assoc]
          have hx' : (K.map (QuotientGroup.mk' N)) ≤ H'.map (QuotientGroup.mk' N) := by
            refine hx.trans (le_of_eq ?_)
            rw [← hg, hH'def]
            exact Transport.hall_map_mulAut_conj (QuotientGroup.mk' N) H g
          have hKle : K ≤ H' ⊔ N := by
            have h := Subgroup.comap_mono (f := QuotientGroup.mk' N) hx'
            rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
            exact le_sup_left.trans h
          have hHN : H' ⊓ N = ⊥ := by
            refine Subgroup.eq_bot_of_card_eq (H' ⊓ N) ?_
            refine PiNat.hall_eq_one_of_isPiNat (π := π) ?_ ?_
              (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
            · exact hH'hall.1.of_dvd (card_dvd_card_of_le inf_le_left)
            · exact hNpi'.of_dvd (card_dvd_card_of_le inf_le_right)
          have hKN : K ⊓ N = ⊥ := by
            refine Subgroup.eq_bot_of_card_eq (K ⊓ N) ?_
            refine PiNat.hall_eq_one_of_isPiNat (π := π) ?_ ?_
              (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
            · exact hK.of_dvd (card_dvd_card_of_le inf_le_left)
            · exact hNpi'.of_dvd (card_dvd_card_of_le inf_le_right)
          by_cases hXG : H' ⊔ N = ⊤
          · by_cases hYG : K ⊔ N = ⊤
            · -- both `K` and `H'` are complements of `N` in `G`: Schur–Zassenhaus
              have hcompK : N.IsComplement' K :=
                isComplement'_of_sup_eq_top_of_inf_eq_bot (K := K) (by rw [sup_comm]; exact hYG)
                  (by rw [inf_comm]; exact hKN)
              have hcompH : N.IsComplement' H' :=
                isComplement'_of_sup_eq_top_of_inf_eq_bot (K := H') (by rw [sup_comm]; exact hXG)
                  (by rw [inf_comm]; exact hHN)
              have hidx : N.index = Nat.card H' := by
                have h1 : Nat.card N * N.index = Nat.card N * Nat.card H' := by
                  rw [Subgroup.card_mul_index, hcompH.card_mul_card]
                exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hN0) h1
              have hc : (Nat.card N).Coprime N.index := by
                rw [hidx]
                exact (PiNat.hall_coprime_of_isPiNat hH'hall.1 hNpi'
                  (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩) hN0).symm
              obtain ⟨y, hy⟩ := SchurZassenhaus.hall_sz_conj_abelian hc hcompK hcompH
              refine ⟨(y : G)⁻¹ * g, ?_⟩
              have h1 : H.map (MulAut.conj ((y : G)⁻¹ * g)).toMonoidHom =
                  H'.map (MulAut.conj ((y : G)⁻¹)).toMonoidHom := by
                rw [hH'def, Subgroup.map_map]
                congr 1
                ext h
                simp [MulAut.mul_apply, MonoidHom.comp_apply, MulAut.conj_apply, mul_assoc]
              have h2 : H'.map (MulAut.conj ((y : G)⁻¹)).toMonoidHom = K := by
                rw [hy, Subgroup.map_map]
                congr 1
                ext h
                simp [MulAut.mul_apply, MonoidHom.comp_apply, MulAut.conj_apply, mul_assoc]
              exact le_of_eq (h1.trans h2).symm
            · -- `H' ⊔ N = G`, `K ⊔ N < G`: induction inside `K ⊔ N`
              set Y : Subgroup G := K ⊔ N with hYdef
              have hYlt : Nat.card ↥Y < n := by
                have h := Subgroup.card_lt_of_lt (lt_of_le_of_ne le_top hYG)
                rwa [show Nat.card ↥Y = Nat.card ↥(K ⊔ N) from by rw [hYdef],
                  Subgroup.card_top, hG] at h
              have hZsup : (H' ⊓ Y) ⊔ N = Y := by
                refine le_antisymm ?_ ?_
                · rw [sup_le_iff]
                  exact ⟨inf_le_right, by simpa [hYdef] using le_sup_right (a := K) (b := N)⟩
                · intro y hy
                  obtain ⟨h, hh, m, hm, hmn⟩ := Subgroup.mem_sup_of_normal_right.mp
                    (show y ∈ H' ⊔ N from by rw [hXG]; exact Subgroup.mem_top y)
                  have hhy : h ∈ Y := by
                    have hhY : h = y * m⁻¹ := by rw [← hmn, mul_inv_cancel_right]
                    rw [hhY]
                    exact Y.mul_mem hy (Y.inv_mem (by rw [hYdef]; exact (le_sup_right : N ≤ K ⊔ N) hm))
                  exact Subgroup.mem_sup_of_normal_right.mpr ⟨h, ⟨hh, hhy⟩, m, hm, hmn⟩
              have hZinf : (H' ⊓ Y) ⊓ N = ⊥ :=
                le_bot_iff.mp ((inf_le_inf inf_le_left le_rfl).trans (le_of_eq hHN))
              have hZcard : Nat.card ↥(H' ⊓ Y) = Nat.card ↥K := by
                have h1 : N ⊔ (H' ⊓ Y) = Y := by rw [sup_comm]; exact hZsup
                have h2 : N ⊔ K = Y := by rw [hYdef, sup_comm]
                have h3 : N ⊓ (H' ⊓ Y) = ⊥ := by rw [inf_comm]; exact hZinf
                have h4 : N ⊓ K = ⊥ := by rw [inf_comm]; exact hKN
                exact card_eq_of_sup_eq_of_inf_eq h1 h2 h3 h4
              have hZrel : IsPiNat (fun q => ¬ π q) ((H' ⊓ Y).relIndex Y) := by
                have h1 : (H' ⊓ Y).relIndex Y = (H' ⊓ Y).relIndex N := by
                  have hsupY : N ⊔ (H' ⊓ Y) = Y := by rw [sup_comm]; exact hZsup
                  have hh := Transport.hall_relIndex_sup_right_of_normalizes (H := N) (K := H' ⊓ Y)
                    (by rw [Subgroup.normalizer_eq_top_iff.mpr hNnorm]; exact le_top)
                  rwa [hsupY] at hh
                rw [h1]
                exact hNpi'.of_dvd (Subgroup.relIndex_dvd_card (H' ⊓ Y) N)
              have hZhall : IsHall π ((H' ⊓ Y).comap Y.subtype) :=
                isHall_comap_of_isPiNat inf_le_right (hZcard ▸ hK) hZrel
              have hKpi : IsPiNat π (Nat.card (K.comap Y.subtype)) :=
                hK.of_eq (Transport.hall_card_comap_subtype_of_le (by rw [hYdef]; exact le_sup_left))
              obtain ⟨m, hm⟩ := ih (Nat.card ↥Y) hYlt (↥Y) rfl inferInstance hZhall hKpi
              refine ⟨(m : G) * g, ?_⟩
              have hmap : K ≤ (H' ⊓ Y).map (MulAut.conj (m : G)).toMonoidHom := by
                have hmono := Subgroup.map_mono (f := Y.subtype) hm
                rwa [Transport.hall_map_subtype_comap_of_le (by rw [hYdef]; exact le_sup_left),
                     Transport.hall_map_subtype_mulAut_conj inf_le_right m] at hmono
              refine (hmap.trans (Subgroup.map_mono inf_le_left)).trans ?_
              rw [hH'def, Subgroup.map_map]
              exact le_of_eq (by
                congr 1
                ext h
                simp [MonoidHom.comp_apply, MulAut.conj_apply, mul_assoc])
          · -- `H' ⊔ N < G`: induction inside `H' ⊔ N`
            have hXlt : Nat.card ↥(H' ⊔ N) < n := by
              have h := Subgroup.card_lt_of_lt (lt_of_le_of_ne le_top hXG)
              rwa [Subgroup.card_top, hG] at h
            have hH'leX : H' ≤ H' ⊔ N := le_sup_left
            have hH'hallX : IsHall π (H'.comap (H' ⊔ N).subtype) :=
              isHall_comap_of_isPiNat hH'leX hH'hall.1
                (by
                  rw [sup_comm, Transport.hall_relIndex_sup_right_of_normalizes (H := N) (K := H')
                    (by rw [Subgroup.normalizer_eq_top_iff.mpr hNnorm]; exact le_top),
                    relIndex_eq_card_of_inf_eq_bot (N := H') (Z := N) hHN]
                  exact hNpi')
            have hKpi : IsPiNat π (Nat.card (K.comap (H' ⊔ N).subtype)) :=
              hK.of_eq (Transport.hall_card_comap_subtype_of_le hKle)
            obtain ⟨y, hy⟩ := ih (Nat.card ↥(H' ⊔ N)) hXlt (↥(H' ⊔ N)) rfl inferInstance
              hH'hallX hKpi
            refine ⟨(y : G) * g, ?_⟩
            have hmap : K ≤ H'.map (MulAut.conj (y : G)).toMonoidHom := by
              have hmono := Subgroup.map_mono (f := (H' ⊔ N).subtype) hy
              rwa [Transport.hall_map_subtype_comap_of_le hKle,
                   Transport.hall_map_subtype_mulAut_conj hH'leX y] at hmono
            exact hmap.trans (le_of_eq (hH'conj (y : G)))

/-- `D_π` (P. Hall): every `π`-subgroup of a finite solvable group is contained in a conjugate of a
given Hall `π`-subgroup. -/
theorem le_conj_of_isPiNat {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] {π : ℕ → Prop}
    {H K : Subgroup G} (hH : Work.Hall.IsHall π H) (hK : Work.Hall.IsPiNat π (Nat.card K)) :
    ∃ g : G, K ≤ H.map (MulAut.conj g).toMonoidHom :=
  le_conj_of_isPiNat_aux (Nat.card G) G rfl inferInstance hH hK

end Work.Hall.Main
