/-
# `C_π` (P. Hall): conjugacy of Hall `π`-subgroups

For a finite solvable group `G` and a set of primes `π`, any two Hall `π`-subgroups of `G` are
conjugate.  This is Theorem `C_π` of P. Hall, one of the three basic theorems (`E_π`, `C_π`, `D_π`)
on Hall subgroups of finite solvable groups used in the first chapter of Feit–Thompson.

The proof is by strong induction on `|G|`.  Let `N ◁ G` be a minimal normal subgroup; it is
elementary abelian of exponent some prime `p`.

* If `N = ⊤` then `G` is abelian and every subgroup of `G` is `⊥` or `⊤`, which settles this case.
* If `p ∈ π`, then `|N|` is a `π`-number, and a relative-index argument shows that a Hall
  `π`-subgroup `H` of `G` satisfies `H ⊔ N = H`, i.e. `N ≤ H`; descending to `G ⧸ N` and using the
  induction hypothesis gives the result.
* If `p ∉ π`, then `|N|` is a `π'`-number, so a Hall `π`-subgroup meets `N` trivially.  If two Hall
  `π`-subgroups `H` and `K` generate `G` together with `N`, they are complements of `N` in `G` and
  the abelian case of Schur–Zassenhaus applies; otherwise induction applies inside the proper
  subgroup `K ⊔ N`.

The conclusion is phrased with `Subgroup.map (MulAut.conj g).toMonoidHom`, the form in which the
rest of the development uses conjugation of subgroups.
-/
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
import Submission.Work.Hall.HallAPI.hall_isHall_eq_of_le
import Submission.Work.Hall.Transport.hall_map_mulAut_conj
import Submission.Work.Hall.Transport.hall_map_subtype_comap_of_le
import Submission.Work.Hall.Transport.hall_card_comap_subtype_of_le
import Submission.Work.Hall.Transport.hall_relIndex_sup_right_of_normalizes
import Submission.Work.Hall.Transport.hall_isHall_comap_subtype
import Submission.Work.Hall.Transport.hall_map_subtype_mulAut_conj
import Submission.Work.Hall.SchurZassenhaus.hall_sz_conj_abelian

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000

set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.Hall.Main

open Classical

universe u

/-! ## Elementary facts about Hall subgroups needed below -/

/-- In a group in which `⊤` is a minimal normal subgroup and which is abelian (which is the case
for a solvable group in which `⊤` is minimal normal), every subgroup is `⊥` or `⊤`. -/
private theorem eq_bot_or_eq_top_of_minimalNormal_top {G : Type*} [Group G] [IsMulCommutative G]
    (h : Work.Hall.IsMinimalNormal (⊤ : Subgroup G)) (M : Subgroup G) : M = ⊥ ∨ M = ⊤ := by
  by_cases hM : M = ⊥
  · exact Or.inl hM
  · exact Or.inr (le_antisymm le_top (h.2.2 M inferInstance le_top hM))

/-- In a subsingleton group all subgroups are equal. -/
private theorem subgroup_eq_of_subsingleton {G : Type*} [Group G] [Subsingleton G]
    (H K : Subgroup G) : H = K := by
  refine le_antisymm ?_ ?_ <;> intro x _ <;> rw [Subsingleton.elim x 1] <;>
    exact Subgroup.one_mem _

/-- Conjugating a subgroup by the identity leaves it unchanged. -/
private theorem map_conj_one {G : Type*} [Group G] (A : Subgroup G) :
    A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  ext x
  simp [Subgroup.mem_map]

/-- If `N` is an elementary abelian `p`-subgroup with `p ∈ π`, then `|N|` is a `π`-number. -/
private theorem isPiNat_card_of_isElementaryAbelian_pi {G : Type*} [Group G] [Finite G] {p : ℕ}
    {π : ℕ → Prop} {N : Subgroup G} (hE : Work.Hall.IsElementaryAbelian p N) (hp : p.Prime)
    (hpπ : π p) : Work.Hall.IsPiNat π (Nat.card N) :=
  (Work.Hall.MinimalNormal.hall_isPiNat_card_of_isElementaryAbelian hE hp).of_eq_prime hpπ

/-- If `N` is an elementary abelian `p`-subgroup with `p ∉ π`, then `|N|` is a `π'`-number. -/
private theorem isPiNat_card_of_isElementaryAbelian_compl {G : Type*} [Group G] [Finite G] {p : ℕ}
    {π : ℕ → Prop} {N : Subgroup G} (hE : Work.Hall.IsElementaryAbelian p N) (hp : p.Prime)
    (hpπ : ¬ π p) : Work.Hall.IsPiNat (fun q => ¬ π q) (Nat.card N) :=
  (Work.Hall.MinimalNormal.hall_isPiNat_card_of_isElementaryAbelian hE hp).of_eq_prime_compl hpπ

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

/-- If `L ≤ X` has `π`-number order and `[X : L]` is a `π'`-number, then `L` is a Hall
`π`-subgroup of `X`. -/
private theorem isHall_comap_of_isPiNat {G : Type*} [Group G] {π : ℕ → Prop} {X L : Subgroup G}
    (hLX : L ≤ X) (hcard : Work.Hall.IsPiNat π (Nat.card L))
    (hidx : Work.Hall.IsPiNat (fun p => ¬ π p) (L.relIndex X)) :
    Work.Hall.IsHall π (L.comap X.subtype) :=
  ⟨hcard.of_eq (Work.Hall.Transport.hall_card_comap_subtype_of_le hLX),
    hidx.of_eq (rfl : (L.comap X.subtype).index = L.relIndex X)⟩

/-- Every subgroup is contained in the normalizer of a normal subgroup. -/
private theorem le_normalizer_of_normal {G : Type*} [Group G] {A B : Subgroup G} [A.Normal] :
    B ≤ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : A.Normal)]
  exact le_top

/-- If `N ⊔ K = ⊤` and `N ⊓ K = ⊥` with `N` normal, then `N.IsComplement' K`. -/
private theorem isComplement'_of_sup_eq_top_of_inf_eq_bot {G : Type*} [Group G] {N K : Subgroup G}
    [N.Normal] (hsup : N ⊔ K = ⊤) (hinf : N ⊓ K = ⊥) : N.IsComplement' K := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (by rw [disjoint_iff]; exact hinf) ?_
  refine Set.eq_univ_iff_forall.mpr fun y => ?_
  have hy : y ∈ (N ⊔ K : Subgroup G) := by rw [hsup]; exact Subgroup.mem_top y
  obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  exact Set.mem_mul.mpr ⟨n, hn, k, hk, hnk⟩

/-- Conjugating by `a` and then by `b` is conjugating by `b * a`. -/
private theorem map_conj_mul {G : Type*} [Group G] (A : Subgroup G) (a b : G) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      A.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

/-! ## The main induction -/

/-- `C_π` (P. Hall) for groups of order `n`: two Hall `π`-subgroups of a finite solvable group
of order `n` are conjugate. -/
theorem isHall_conj_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → Group.IsSolvable G →
      ∀ {π : ℕ → Prop} {H K : Subgroup G}, Work.Hall.IsHall π H → Work.Hall.IsHall π K →
        ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro G _ _ hG hsol π H K hH hK
    letI : Group.IsSolvable G := hsol
    rcases subsingleton_or_nontrivial G with hsub | hntriv
    · -- `G` is trivial: all subgroups are equal.
      haveI : Subsingleton G := hsub
      exact ⟨1, subgroup_eq_of_subsingleton K (H.map (MulAut.conj (1 : G)).toMonoidHom)⟩
    · haveI : Nontrivial G := hntriv
      obtain ⟨N, hNmin⟩ := Work.Hall.MinimalNormal.hall_exists_isMinimalNormal (G := G)
      haveI hNnorm : N.Normal := hNmin.1
      obtain ⟨p, hp, hE⟩ :=
        Work.Hall.MinimalNormal.hall_minimalNormal_isElementaryAbelian hNmin inferInstance
      by_cases htop : N = ⊤
      · -- `N = ⊤`: then `G` is abelian, and every subgroup is `⊥` or `⊤`.
        have hEt : Work.Hall.IsElementaryAbelian p (⊤ : Subgroup G) := htop ▸ hE
        haveI hcommT : IsMulCommutative ↥(⊤ : Subgroup G) := hEt.1
        haveI : IsMulCommutative G := IsMulCommutative.of_comm fun a b =>
          congrArg Subtype.val (mul_comm' (⟨a, trivial⟩ : ↥(⊤ : Subgroup G)) ⟨b, trivial⟩)
        have hdich : ∀ M : Subgroup G, M = ⊥ ∨ M = ⊤ := fun M =>
          eq_bot_or_eq_top_of_minimalNormal_top (htop ▸ hNmin) M
        rcases hdich H with hHb | hHt <;> rcases hdich K with hKb | hKt
        · subst hHb; subst hKb
          exact ⟨1, by rw [map_conj_one]⟩
        · -- `H = ⊥`, `K = ⊤` is impossible: `|G|` would be both a `π`- and a `π'`-number.
          subst hHb; subst hKt
          exfalso
          have h1 : Work.Hall.IsPiNat π (Nat.card G) := by simpa [Subgroup.card_top] using hK.1
          have h2 : Work.Hall.IsPiNat (fun q => ¬ π q) (Nat.card G) := by
            simpa [Subgroup.index_bot] using hH.2
          have hc : Nat.card G = 1 :=
            Work.Hall.PiNat.hall_eq_one_of_isPiNat h1 h2
              (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
          haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hc).1
          obtain ⟨a, b, hab⟩ := exists_pair_ne G
          exact hab (Subsingleton.elim a b)
        · subst hHt; subst hKb
          exfalso
          have h1 : Work.Hall.IsPiNat π (Nat.card G) := by simpa [Subgroup.card_top] using hH.1
          have h2 : Work.Hall.IsPiNat (fun q => ¬ π q) (Nat.card G) := by
            simpa [Subgroup.index_bot] using hK.2
          have hc : Nat.card G = 1 :=
            Work.Hall.PiNat.hall_eq_one_of_isPiNat h1 h2
              (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
          haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hc).1
          obtain ⟨a, b, hab⟩ := exists_pair_ne G
          exact hab (Subsingleton.elim a b)
        · subst hHt; subst hKt
          exact ⟨1, by rw [map_conj_one]⟩
      · -- `N ≠ ⊤` is a nontrivial proper normal subgroup.
        have hNne : N ≠ ⊥ := hNmin.2.1
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
        · -- ## `p ∈ π`: `N` lies in every Hall `π`-subgroup, and we descend to `G ⧸ N`.
          have hNpi : Work.Hall.IsPiNat π (Nat.card N) :=
            isPiNat_card_of_isElementaryAbelian_pi hE hp hpπ
          obtain ⟨x, hx⟩ := ih (Nat.card (G ⧸ N)) hcardQ (G ⧸ N) rfl inferInstance
            (Work.Hall.HallAPI.hall_isHall_map_mk hNpi hH)
            (Work.Hall.HallAPI.hall_isHall_map_mk hNpi hK)
          obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N x
          set H' : Subgroup G := H.map (MulAut.conj g).toMonoidHom with hH'def
          have hH'hall : Work.Hall.IsHall π H' := hH.map_mulAut (MulAut.conj g)
          have hx' : K.map (QuotientGroup.mk' N) = H'.map (QuotientGroup.mk' N) := by
            rw [hx, ← hg, hH'def]
            exact Work.Hall.Transport.hall_map_mulAut_conj (QuotientGroup.mk' N) H g
          have hXeq : K ⊔ N = H' ⊔ N := by
            have h := congrArg (Subgroup.comap (QuotientGroup.mk' N)) hx'
            rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
          -- The relative index `[H' ⊔ N : H']` is a `π`-number (it divides `|N|`) and a
          -- `π'`-number (it divides `[G : H']`), hence equals `1`, i.e. `N ≤ H'`.
          have hrel_eq : H'.relIndex (H' ⊔ N) = H'.relIndex N := by
            rw [sup_comm]
            exact Work.Hall.Transport.hall_relIndex_sup_right_of_normalizes le_normalizer_of_normal
          have hrel1 : H'.relIndex (H' ⊔ N) = 1 := by
            refine Work.Hall.PiNat.hall_eq_one_of_isPiNat (π := π) ?_ ?_ ?_
            · exact (hNpi.of_dvd (Subgroup.relIndex_dvd_card H' N)).of_eq hrel_eq
            · exact Work.Hall.HallAPI.hall_isHall_relIndex hH'hall le_sup_left
            · intro h0
              have hd := Subgroup.relIndex_dvd_card H' N
              rw [← hrel_eq, h0] at hd
              exact hN0 (Nat.eq_zero_of_zero_dvd hd)
          have hKleH' : K ≤ H' := by
            have h1 : K ≤ K ⊔ N := le_sup_left
            rw [hXeq] at h1
            exact h1.trans (Subgroup.relIndex_eq_one.mp hrel1)
          exact ⟨g, Work.Hall.HallAPI.hall_isHall_eq_of_le hK hH'hall hKleH'⟩
        · -- ## `p ∉ π`: `|N|` is a `π'`-number, so `H ⊓ N = K ⊓ N = ⊥`.
          have hNpi' : Work.Hall.IsPiNat (fun q => ¬ π q) (Nat.card N) :=
            isPiNat_card_of_isElementaryAbelian_compl hE hp hpπ
          haveI : IsMulCommutative ↥N := hE.1
          obtain ⟨x, hx⟩ := ih (Nat.card (G ⧸ N)) hcardQ (G ⧸ N) rfl inferInstance
            (Work.Hall.isHall_map_of_surjective (QuotientGroup.mk' N)
              (QuotientGroup.mk'_surjective N) hH)
            (Work.Hall.isHall_map_of_surjective (QuotientGroup.mk' N)
              (QuotientGroup.mk'_surjective N) hK)
          obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N x
          set H' : Subgroup G := H.map (MulAut.conj g).toMonoidHom with hH'def
          have hH'hall : Work.Hall.IsHall π H' := hH.map_mulAut (MulAut.conj g)
          have hx' : K.map (QuotientGroup.mk' N) = H'.map (QuotientGroup.mk' N) := by
            rw [hx, ← hg, hH'def]
            exact Work.Hall.Transport.hall_map_mulAut_conj (QuotientGroup.mk' N) H g
          have hXeq : K ⊔ N = H' ⊔ N := by
            have h := congrArg (Subgroup.comap (QuotientGroup.mk' N)) hx'
            rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
          have hHN : H' ⊓ N = ⊥ := by
            refine Subgroup.eq_bot_of_card_eq (H' ⊓ N) ?_
            refine Work.Hall.PiNat.hall_eq_one_of_isPiNat (π := π) ?_ ?_
              (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
            · exact hH'hall.1.of_dvd (card_dvd_card_of_le inf_le_left)
            · exact hNpi'.of_dvd (card_dvd_card_of_le inf_le_right)
          have hKN : K ⊓ N = ⊥ := by
            refine Subgroup.eq_bot_of_card_eq (K ⊓ N) ?_
            refine Work.Hall.PiNat.hall_eq_one_of_isPiNat (π := π) ?_ ?_
              (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
            · exact hK.1.of_dvd (card_dvd_card_of_le inf_le_left)
            · exact hNpi'.of_dvd (card_dvd_card_of_le inf_le_right)
          by_cases hXG : K ⊔ N = ⊤
          · -- `K` and `H'` are complements of `N` in `G`: Schur–Zassenhaus.
            have hcompK : N.IsComplement' K :=
              isComplement'_of_sup_eq_top_of_inf_eq_bot (K := K)
                (by rw [sup_comm]; exact hXG) (by rw [inf_comm]; exact hKN)
            have hsupNH : N ⊔ H' = ⊤ := by rw [sup_comm, ← hXeq]; exact hXG
            have hcompH : N.IsComplement' H' :=
              isComplement'_of_sup_eq_top_of_inf_eq_bot (K := H') hsupNH
                (by rw [inf_comm]; exact hHN)
            have hidx : N.index = Nat.card H' := by
              have h1 : Nat.card N * N.index = Nat.card N * Nat.card H' := by
                rw [Subgroup.card_mul_index, hcompH.card_mul_card]
              exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hN0) h1
            have hc : (Nat.card N).Coprime N.index := by
              rw [hidx]
              exact (Work.Hall.PiNat.hall_coprime_of_isPiNat hH'hall.1 hNpi'
                (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩) hN0).symm
            obtain ⟨y, hy⟩ := Work.Hall.SchurZassenhaus.hall_sz_conj_abelian hc hcompH hcompK
            refine ⟨(y : G) * g, ?_⟩
            rw [hy, hH'def]
            exact map_conj_mul H g (y : G)
          · -- `K ⊔ N` is proper: induct inside it.
            have hXlt : Nat.card ↥(K ⊔ N) < n := by
              have h := Subgroup.card_lt_of_lt (lt_of_le_of_ne le_top hXG)
              rwa [Subgroup.card_top, hG] at h
            have hH'leX : H' ≤ K ⊔ N := by rw [hXeq]; exact le_sup_left
            have hKhall : Work.Hall.IsHall π (K.comap (K ⊔ N).subtype) :=
              isHall_comap_of_isPiNat le_sup_left hK.1
                (Work.Hall.HallAPI.hall_isHall_relIndex hK le_sup_left)
            have hH'hallX : Work.Hall.IsHall π (H'.comap (K ⊔ N).subtype) :=
              Work.Hall.Transport.hall_isHall_comap_subtype hH'leX hH'hall
            obtain ⟨y, hy⟩ := ih (Nat.card ↥(K ⊔ N)) hXlt (↥(K ⊔ N)) rfl inferInstance
              hH'hallX hKhall
            refine ⟨(y : G) * g, ?_⟩
            have hmap := congrArg (Subgroup.map (K ⊔ N).subtype) hy
            rw [Work.Hall.Transport.hall_map_subtype_mulAut_conj hH'leX y,
              Work.Hall.Transport.hall_map_subtype_comap_of_le le_sup_left] at hmap
            refine hmap.trans ?_
            rw [hH'def]
            exact map_conj_mul H g (y : G)

/-- `C_π` (P. Hall): two Hall `π`-subgroups of a finite solvable group are conjugate. -/
theorem isHall_conj {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] {π : ℕ → Prop}
    {H K : Subgroup G} (hH : Work.Hall.IsHall π H) (hK : Work.Hall.IsHall π K) :
    ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom :=
  isHall_conj_aux (Nat.card G) G rfl inferInstance hH hK

end Work.Hall.Main
