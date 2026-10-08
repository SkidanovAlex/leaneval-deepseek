import Mathlib
import Submission.Work.Hall.Basic
import Submission.Work.Hall.PiNat.hall_coprime_of_isPiNat
import Submission.Work.Hall.PiNat.hall_eq_one_of_isPiNat
import Submission.Work.Hall.MinimalNormal.hall_exists_isMinimalNormal
import Submission.Work.Hall.MinimalNormal.hall_minimalNormal_isElementaryAbelian
import Submission.Work.Hall.MinimalNormal.hall_isPiNat_card_of_isElementaryAbelian
import Submission.Work.Hall.MinimalNormal.hall_isElementaryAbelian_prime_dvd_card
import Submission.Work.Hall.HallAPI.hall_isHall_map_mk
import Submission.Work.Hall.HallAPI.hall_isHall_comap_mk
import Submission.Work.Hall.HallAPI.hall_card_comap_mk
import Submission.Work.Hall.HallAPI.hall_isHall_card_coprime_index
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

/-!
# Hall subgroups of finite solvable groups

P. Hall's theorems for a finite solvable group `G` and a set of primes `π`:

* `Work.Hall.exists_isHall` — `E_π` : `G` has a Hall `π`-subgroup;
* `Work.Hall.isHall_conj` — `C_π` : any two Hall `π`-subgroups are conjugate;
* `Work.Hall.le_conj_of_isPiNat` — `D_π` : every `π`-subgroup is contained in a conjugate of a
  given Hall `π`-subgroup.

The proofs are by strong induction on `|G|`, using the fact that a minimal normal subgroup of a
solvable group is elementary abelian
(`Work.Hall.MinimalNormal.hall_minimalNormal_isElementaryAbelian`), Schur–Zassenhaus, and the usual
case distinction `p ∈ π` / `p ∉ π`.
-/

set_option maxHeartbeats 1600000

open scoped Pointwise

namespace Work.Hall

open Subgroup

universe u

variable {G : Type*} [Group G] [Finite G] {π : ℕ → Prop} {H K : Subgroup G}

/-- In a group in which `⊤` is a minimal normal subgroup and which is abelian (which is the case
for a solvable group in which `⊤` is minimal normal), every subgroup is `⊥` or `⊤`. -/
theorem eq_bot_or_eq_top_of_minimalNormal_top {G : Type*} [Group G] [IsMulCommutative G]
    (h : IsMinimalNormal (⊤ : Subgroup G)) (M : Subgroup G) : M = ⊥ ∨ M = ⊤ := by
  by_cases hM : M = ⊥
  · exact Or.inl hM
  · exact Or.inr (le_antisymm le_top (h.2.2 M inferInstance le_top hM))

/-- In a subsingleton group all subgroups are equal. -/
theorem subgroup_eq_of_subsingleton {G : Type*} [Group G] [Subsingleton G] (H K : Subgroup G) :
    H = K := by
  refine le_antisymm ?_ ?_ <;> intro x _ <;> rw [Subsingleton.elim x 1] <;> exact Subgroup.one_mem _

/-- If `L ≤ X` has `π`-number order and `[X : L]` is a `π'`-number, then `L` is a Hall
`π`-subgroup of `X`. -/
theorem isHall_comap_of_isPiNat {G : Type*} [Group G] {π : ℕ → Prop} {X L : Subgroup G}
    (hLX : L ≤ X) (hcard : IsPiNat π (Nat.card L))
    (hidx : IsPiNat (fun p => ¬ π p) (L.relIndex X)) : IsHall π (L.comap X.subtype) :=
  ⟨hcard.of_eq (Transport.hall_card_comap_subtype_of_le hLX),
    hidx.of_eq (rfl : (L.comap X.subtype).index = L.relIndex X)⟩

/-- If `N` is an elementary abelian `p`-subgroup with `p ∉ π`, then `|N|` is a `π'`-number. -/
theorem isPiNat_card_of_isElementaryAbelian_compl {G : Type*} [Group G] [Finite G] {p : ℕ}
    {π : ℕ → Prop} {N : Subgroup G} (hE : IsElementaryAbelian p N) (hp : p.Prime)
    (hpπ : ¬ π p) : IsPiNat (fun q => ¬ π q) (Nat.card N) :=
  (MinimalNormal.hall_isPiNat_card_of_isElementaryAbelian hE hp).of_eq_prime_compl hpπ

/-- If `N` is an elementary abelian `p`-subgroup with `p ∈ π`, then `|N|` is a `π`-number. -/
theorem isPiNat_card_of_isElementaryAbelian_pi {G : Type*} [Group G] [Finite G] {p : ℕ}
    {π : ℕ → Prop} {N : Subgroup G} (hE : IsElementaryAbelian p N) (hp : p.Prime)
    (hpπ : π p) : IsPiNat π (Nat.card N) :=
  (MinimalNormal.hall_isPiNat_card_of_isElementaryAbelian hE hp).of_eq_prime hpπ

/-- If `A ≤ B` then `|A|` divides `|B|`. -/
theorem card_dvd_card_of_le {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B) :
    Nat.card ↥A ∣ Nat.card ↥B := by
  refine ⟨(A.subgroupOf B).index, ?_⟩
  have h1 : Nat.card ↥(A.subgroupOf B) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have h2 : (A.subgroupOf B).index * Nat.card ↥(A.subgroupOf B) = Nat.card ↥B :=
    Subgroup.index_mul_card (A.subgroupOf B)
  rw [h1, mul_comm] at h2
  exact h2.symm

/-- If `N ⊓ Z = ⊥` then `N.subgroupOf Z = ⊥`. -/
theorem subgroupOf_eq_bot_of_inf_eq_bot {G : Type*} [Group G] {N Z : Subgroup G}
    (h : N ⊓ Z = ⊥) : N.subgroupOf Z = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  refine Subtype.ext (Subgroup.mem_bot.mp ?_)
  rw [← h]
  exact Subgroup.mem_inf.mpr ⟨hx, x.2⟩

/-- If `N ⊓ Z = ⊥` then `N.relIndex Z = |Z|`. -/
theorem relIndex_eq_card_of_inf_eq_bot {G : Type*} [Group G] {N Z : Subgroup G}
    (h : N ⊓ Z = ⊥) : N.relIndex Z = Nat.card ↥Z := by
  rw [Subgroup.relIndex, subgroupOf_eq_bot_of_inf_eq_bot h, Subgroup.index_bot]

/-- If `Z` and `K` both complement a normal subgroup `N` inside the same subgroup `Y`, then
`|Z| = |K|`. -/
theorem card_eq_of_sup_eq_of_inf_eq {G : Type*} [Group G] {N Z K Y : Subgroup G} [N.Normal]
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
theorem isComplement'_of_sup_eq_top_of_inf_eq_bot {G : Type*} [Group G] {N K : Subgroup G}
    [N.Normal] (hsup : N ⊔ K = ⊤) (hinf : N ⊓ K = ⊥) : N.IsComplement' K := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (by rw [disjoint_iff]; exact hinf) ?_
  refine Set.eq_univ_iff_forall.mpr fun y => ?_
  have hy : y ∈ (N ⊔ K : Subgroup G) := by rw [hsup]; exact Subgroup.mem_top y
  obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  exact Set.mem_mul.mpr ⟨n, hn, k, hk, hnk⟩

/-- `E_π` (P. Hall): a finite solvable group has a Hall `π`-subgroup. -/
theorem exists_isHall_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → Group.IsSolvable G →
      ∀ π : ℕ → Prop, ∃ H : Subgroup G, IsHall π H := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro G _ _ hG hsol π
    letI : Group.IsSolvable G := hsol
    rcases subsingleton_or_nontrivial G with hsub | hntriv
    · refine ⟨⊥, ?_, ?_⟩
      · rw [Subgroup.card_bot]; exact IsPiNat.one
      · rw [Subgroup.index_bot, Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩]
        exact IsPiNat.one
    · haveI : Nontrivial G := hntriv
      obtain ⟨N, hNmin⟩ := MinimalNormal.hall_exists_isMinimalNormal (G := G)
      haveI hNnorm : N.Normal := hNmin.1
      obtain ⟨p, hp, hE⟩ :=
        MinimalNormal.hall_minimalNormal_isElementaryAbelian hNmin inferInstance
      have hpiN : IsPiNat (fun q => q = p) (Nat.card N) :=
        MinimalNormal.hall_isPiNat_card_of_isElementaryAbelian hE hp
      by_cases htop : N = ⊤
      · have hEt : IsElementaryAbelian p (⊤ : Subgroup G) := htop ▸ hE
        have hprime : ∀ q, q.Prime → q ∣ Nat.card G → q = p := fun q hq hd =>
          MinimalNormal.hall_isElementaryAbelian_prime_dvd_card hEt hp hq
            (by rwa [Subgroup.card_top])
        by_cases hpπ : π p
        · refine ⟨⊤, ?_, ?_⟩
          · rw [Subgroup.card_top]
            exact fun q hq hd => (hprime q hq hd) ▸ hpπ
          · rw [Subgroup.index_top]; exact IsPiNat.one
        · refine ⟨⊥, ?_, ?_⟩
          · rw [Subgroup.card_bot]; exact IsPiNat.one
          · rw [Subgroup.index_bot]
            exact fun q hq hd hπ => hpπ ((hprime q hq hd) ▸ hπ)
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
        · obtain ⟨Hbar, hHall⟩ := ih (Nat.card (G ⧸ N)) hcardQ (G ⧸ N) rfl inferInstance π
          exact ⟨Hbar.comap (QuotientGroup.mk' N),
            HallAPI.hall_isHall_comap_mk (isPiNat_card_of_isElementaryAbelian_pi hE hp hpπ) hHall⟩
        · obtain ⟨Hbar, hHall⟩ := ih (Nat.card (G ⧸ N)) hcardQ (G ⧸ N) rfl inferInstance π
          set H : Subgroup G := Hbar.comap (QuotientGroup.mk' N) with hHdef
          have hNH : N ≤ H := by
            intro x hx
            rw [hHdef, Subgroup.mem_comap,
              show (QuotientGroup.mk' N) x = 1 from by
                rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hx]
            exact Hbar.one_mem
          have hcardH : Nat.card H = Nat.card N * Nat.card Hbar := HallAPI.hall_card_comap_mk Hbar
          have hmapH : H.map (QuotientGroup.mk' N) = Hbar := by
            rw [hHdef, Subgroup.map_comap_eq,
              MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N), top_inf_eq]
          have hHindex : H.index = Hbar.index := by
            rw [← hmapH,
              Subgroup.index_map_eq H (QuotientGroup.mk'_surjective N)
                (by rw [QuotientGroup.ker_mk']; exact hNH)]
          have hB0 : Nat.card Hbar ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
          have hcardN' : Nat.card (N.comap H.subtype) = Nat.card N :=
            Transport.hall_card_comap_subtype_of_le hNH
          have hindexN' : (N.comap H.subtype).index = Nat.card Hbar := by
            have h1 : (N.comap H.subtype).index * Nat.card (N.comap H.subtype) = Nat.card ↥H :=
              Subgroup.index_mul_card _
            rw [hcardN', hcardH] at h1
            exact Nat.mul_right_cancel (Nat.pos_of_ne_zero hN0) (by rw [h1, mul_comm])
          have hcop : Nat.Coprime (Nat.card (N.comap H.subtype)) (N.comap H.subtype).index := by
            rw [hcardN', hindexN']
            exact (PiNat.hall_coprime_of_isPiNat hHall.1
              (isPiNat_card_of_isElementaryAbelian_compl hE hp hpπ) hB0 hN0).symm
          obtain ⟨L, hL⟩ :=
            Subgroup.exists_right_complement'_of_coprime (N := N.comap H.subtype) hcop
          refine ⟨L.map H.subtype, ?_, ?_⟩
          · have hcardL : Nat.card L = Nat.card Hbar := by
              have h1 := hL.card_mul_card
              rw [hcardN', hcardH] at h1
              exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hN0) h1
            rw [Subgroup.card_subtype H L, hcardL]
            exact hHall.1
          · rw [Subgroup.index_map_subtype L]
            have hLidx : L.index = Nat.card N := by rw [hL.index_eq_card, hcardN']
            rw [hLidx, hHindex]
            exact (isPiNat_card_of_isElementaryAbelian_compl hE hp hpπ).mul hHall.2

/-- `E_π` (P. Hall): a finite solvable group has a Hall `π`-subgroup. -/
theorem exists_isHall (G : Type u) [Group G] [Finite G] [Group.IsSolvable G] (π : ℕ → Prop) :
    ∃ H : Subgroup G, IsHall π H :=
  exists_isHall_aux (Nat.card G) G rfl inferInstance π

end Work.Hall
