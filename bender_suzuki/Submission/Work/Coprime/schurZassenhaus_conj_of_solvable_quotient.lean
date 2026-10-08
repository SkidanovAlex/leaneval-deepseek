import Mathlib
import Submission.Work.Hall.Basic
import Submission.Work.Hall.HallMain
import Submission.Work.Hall.Transport.hall_map_mulAut_conj
import Submission.Work.Hall.Transport.hall_map_subtype_mulAut_conj
import Submission.Work.Hall.Transport.hall_card_comap_subtype_of_le
import Submission.Work.Hall.HallAPI.hall_card_comap_mk
import Submission.Work.Coprime.SZUtil.exists_normal_ne_bot_ne_top
import Submission.Work.Coprime.SZUtil.isSolvable_quotient_map_mk
import Submission.Work.Coprime.SZUtil.conj_of_index_prime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Schur–Zassenhaus: conjugacy of complements when the quotient is solvable

If `N` is a normal Hall subgroup of a finite group `G` (i.e. `|N|` is coprime to `[G : N]`)
and the quotient `G ⧸ N` is solvable, then any two complements of `N` in `G` are conjugate.

This is the conjugacy part of the Schur–Zassenhaus theorem in the form needed for the
coprime-action part of the Feit–Thompson proof.  The proof is by strong induction on `|G|`.

* If `N = ⊤` the two complements are both `⊥`.
* If `[G : N] = p` is prime, the complements have order `p`, so they are Sylow
  `p`-subgroups and Sylow's theorem applies (`Work.Coprime.SZUtil.conj_of_index_prime`).
* Otherwise `G ⧸ N` is solvable of non-prime order `≠ 1`, so it has a nontrivial proper normal
  subgroup `Ā`; let `M` be its preimage in `G`.  The induction hypothesis applies to `M`
  (`N ⊴ M` is a normal Hall subgroup with `M ⧸ N ≅ Ā` solvable), giving `m ∈ M` with
  `K ⊓ M = (H^m) ⊓ M`.  Writing `H' = H^m` and `A = K ⊓ M = H' ⊓ M`, either the normalizer
  `N_G(A)` of `A` is proper --- then `N_G(A) = (N ∩ N_G(A)) ⋊ H'` and induction in `N_G(A)`
  finishes --- or `A ⊴ G`, and then induction in `G ⧸ A` finishes.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.Coprime

/-! ## Elementary transport of complements -/

/-- A complement of `N` in `G` restricts to a complement of `N` in any intermediate subgroup. -/
theorem isComplement'_subgroupOf_of_le {G : Type*} [Group G] {N M H : Subgroup G} [N.Normal]
    (hNM : N ≤ M) (hH : N.IsComplement' H) :
    (N.subgroupOf M).IsComplement' (H.subgroupOf M) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hxN, hxH⟩
    have hxN' : (x : G) ∈ N := hxN
    have hxH' : (x : G) ∈ H := hxH
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subgroup.mem_bot.mp ((disjoint_iff_inf_le.mp hH.disjoint) ⟨hxN', hxH'⟩))
  · rw [Set.eq_univ_iff_forall]
    intro m
    have hm : (m : G) ∈ (N : Set G) * (H : Set G) := by rw [hH.mul_eq]; exact Set.mem_univ _
    obtain ⟨n, hn, h, hh, hnh⟩ := Set.mem_mul.mp hm
    refine Set.mem_mul.mpr ⟨⟨n, hNM hn⟩, hn, ⟨h, ?_⟩, hh, Subtype.ext hnh⟩
    have hEq : h = n⁻¹ * (m : G) := by rw [← hnh]; group
    rw [hEq]
    exact M.mul_mem (M.inv_mem (hNM hn)) m.2

/-- Complements of `N` inside `Y` give complements in a quotient by a normal subgroup `A ≤ H`
below `N`... concretely: if `A ⊴ G` with `A ≤ H` and `H` complements `N`, then the images of
`N` and `H` in `G ⧸ A` are complements. -/
theorem isComplement'_map_mk_of_le {G : Type*} [Group G] {A N H : Subgroup G} [A.Normal] [N.Normal]
    (hAH : A ≤ H) (hH : N.IsComplement' H) :
    (N.map (QuotientGroup.mk' A)).IsComplement' (H.map (QuotientGroup.mk' A)) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hxN, hxH⟩
    obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hxN
    obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp hxH
    rw [Subgroup.mem_bot]
    have hAn : n⁻¹ * h ∈ A := QuotientGroup.eq.mp (hnx.trans hhx.symm)
    have hnH : n ∈ H := by
      have : n = h * (n⁻¹ * h)⁻¹ := by group
      rw [this]; exact H.mul_mem hh (H.inv_mem (hAH hAn))
    have hn1 : n = 1 := Subgroup.mem_bot.mp ((disjoint_iff_inf_le.mp hH.disjoint) ⟨hn, hnH⟩)
    rw [← hnx, hn1, map_one]
  · rw [Set.eq_univ_iff_forall]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective A y
    have hg : g ∈ (N : Set G) * (H : Set G) := by rw [hH.mul_eq]; exact Set.mem_univ _
    obtain ⟨n, hn, h, hh, hnh⟩ := Set.mem_mul.mp hg
    refine Set.mem_mul.mpr ⟨(QuotientGroup.mk' A) n, Subgroup.mem_map_of_mem _ hn,
      (QuotientGroup.mk' A) h, Subgroup.mem_map_of_mem _ hh, ?_⟩
    rw [← map_mul, hnh]

/-- Equality of subgroups can be tested after mapping to a quotient by a normal subgroup
contained in both. -/
theorem eq_of_map_mk'_eq {G : Type*} [Group G] {A H K : Subgroup G} [A.Normal]
    (hAH : A ≤ H) (hAK : A ≤ K)
    (h : H.map (QuotientGroup.mk' A) = K.map (QuotientGroup.mk' A)) : H = K := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have hx' : (QuotientGroup.mk' A) x ∈ K.map (QuotientGroup.mk' A) := by
      rw [← h]; exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨k, hk, hkq⟩ := Subgroup.mem_map.mp hx'
    have ha : x⁻¹ * k ∈ A := QuotientGroup.eq.mp hkq.symm
    have hkK : x⁻¹ * k ∈ K := hAK ha
    have : x = k * (x⁻¹ * k)⁻¹ := by group
    rw [this]; exact K.mul_mem hk (K.inv_mem hkK)
  · have hx' : (QuotientGroup.mk' A) x ∈ H.map (QuotientGroup.mk' A) := by
      rw [h]; exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨k, hk, hkq⟩ := Subgroup.mem_map.mp hx'
    have ha : x⁻¹ * k ∈ A := QuotientGroup.eq.mp hkq.symm
    have hkH : x⁻¹ * k ∈ H := hAH ha
    have : x = k * (x⁻¹ * k)⁻¹ := by group
    rw [this]; exact H.mul_mem hk (H.inv_mem hkH)

/-- Conjugation preserves the property of being a complement of a normal subgroup. -/
theorem isComplement'_map_conj {G : Type*} [Group G] {N H : Subgroup G} [N.Normal] (g : G)
    (h : N.IsComplement' H) : N.IsComplement' (H.map (MulAut.conj g).toMonoidHom) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hxN, hxH⟩
    obtain ⟨h', hh', hh'x⟩ := Subgroup.mem_map.mp hxH
    rw [Subgroup.mem_bot]
    have hhN : h' ∈ N := by
      have hEq : h' = g⁻¹ * x * g := by
        have : g * h' * g⁻¹ = x := hh'x
        rw [← this]; group
      simpa [hEq] using (inferInstance : N.Normal).conj_mem x hxN g⁻¹
    have h1 : h' = 1 := Subgroup.mem_bot.mp ((disjoint_iff_inf_le.mp h.disjoint) ⟨hhN, hh'⟩)
    rw [← hh'x, h1, map_one]
  · rw [Set.eq_univ_iff_forall]
    intro x
    have hx : g⁻¹ * x * g ∈ (N : Set G) * (H : Set G) := by rw [h.mul_eq]; trivial
    obtain ⟨n, hn, h', hh', hnh⟩ := Set.mem_mul.mp hx
    refine Set.mem_mul.mpr ⟨g * n * g⁻¹, (inferInstance : N.Normal).conj_mem n hn g,
      (MulAut.conj g) h', Subgroup.mem_map.mpr ⟨h', hh', rfl⟩, ?_⟩
    show (MulAut.conj g) n * (MulAut.conj g) h' = x
    rw [← map_mul, hnh, MulAut.conj_apply]
    group

/-- A normal subgroup is fixed by conjugation. -/
theorem map_conj_eq_self_of_normal {G : Type*} [Group G] {A : Subgroup G} (hA : A.Normal) (g : G) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact hA.conj_mem y hy g
  · intro x hx
    exact Subgroup.mem_map.mpr ⟨(MulAut.conj g⁻¹) x, hA.conj_mem x hx g⁻¹,
      by show g * (g⁻¹ * x * (g⁻¹)⁻¹) * g⁻¹ = x; group⟩

/-- `(H ⊓ M).map (conj g) = (H.map (conj g)) ⊓ M` for a normal subgroup `M`. -/
theorem map_inf_conj_eq {G : Type*} [Group G] {M : Subgroup G} [M.Normal] (H : Subgroup G) (g : G) :
    (H ⊓ M).map (MulAut.conj g).toMonoidHom
      = (H.map (MulAut.conj g).toMonoidHom) ⊓ M := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective]
  congr 1
  exact map_conj_eq_self_of_normal (inferInstance : M.Normal) g

/-- The coprimality hypothesis descends to subgroups. -/
theorem coprime_card_subgroupOf_index {G : Type*} [Group G] [Finite G] {N M : Subgroup G}
    [N.Normal] (hNM : N ≤ M) (hc : (Nat.card N).Coprime N.index) :
    (Nat.card (N.subgroupOf M)).Coprime (N.subgroupOf M).index := by
  have hcard : Nat.card (N.subgroupOf M) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hidx : (N.subgroupOf M).index = N.relIndex M := rfl
  rw [hcard, hidx]
  refine hc.coprime_dvd_right ?_
  rw [← Subgroup.relIndex_sup_right (H := M) (K := N)]
  exact Subgroup.relIndex_dvd_index_of_le le_sup_right

/-- The coprimality hypothesis descends to arbitrary subgroups (not necessarily containing `N`). -/
theorem coprime_card_subgroupOf_index' {G : Type*} [Group G] [Finite G] {N Y : Subgroup G}
    [N.Normal] (hc : (Nat.card N).Coprime N.index) :
    (Nat.card (N.subgroupOf Y)).Coprime (N.subgroupOf Y).index := by
  have hcard : Nat.card (N.subgroupOf Y) = Nat.card ↥(N ⊓ Y : Subgroup G) := by
    rw [← Subgroup.subgroupOf_map_subtype N Y]
    exact (Subgroup.card_map_of_injective (f := Y.subtype) (Subgroup.subtype_injective Y)).symm
  have hidx : (N.subgroupOf Y).index = N.relIndex Y := rfl
  rw [hcard, hidx]
  have hdvd : Nat.card ↥(N ⊓ Y : Subgroup G) ∣ Nat.card ↥N :=
    Work.Hall.card_dvd_card_of_le (inf_le_left : (N ⊓ Y : Subgroup G) ≤ N)
  refine (hc.coprime_dvd_left hdvd).coprime_dvd_right ?_
  rw [← Subgroup.relIndex_sup_right (H := Y) (K := N)]
  exact Subgroup.relIndex_dvd_index_of_le le_sup_right

/-- A quotient of `G` by `N` which is a quotient of `Y ⧸ (N ⊓ Y)`: solvability of `G ⧸ N`
implies solvability of `Y ⧸ N.subgroupOf Y`. -/
theorem isSolvable_quotient_subgroupOf_of_isSolvable {G : Type*} [Group G] {N Y : Subgroup G}
    [N.Normal] (hsol : Group.IsSolvable (G ⧸ N)) :
    Group.IsSolvable (Y ⧸ N.subgroupOf Y) := by
  haveI : Group.IsSolvable (G ⧸ N) := hsol
  let f : Y →* G ⧸ N := (QuotientGroup.mk' N).comp Y.subtype
  have hfker : f.ker = N.subgroupOf Y := by
    ext y
    simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have hs : Group.IsSolvable (Y ⧸ f.ker) :=
    Group.isSolvable_of_isSolvable_injective (f := QuotientGroup.kerLift f)
      (QuotientGroup.kerLift_injective f)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (QuotientGroup.quotientMulEquivOfEq hfker).symm.toMonoidHom)
    (QuotientGroup.quotientMulEquivOfEq hfker).symm.injective

/-- Two complements of `N` generate the whole group. -/
theorem sup_eq_top_of_isComplement' {G : Type*} [Group G] {N H : Subgroup G}
    (h : N.IsComplement' H) : N ⊔ H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : g ∈ (N : Set G) * (H : Set G) := by rw [h.mul_eq]; trivial
  obtain ⟨n, hn, k, hk, rfl⟩ := Set.mem_mul.mp hg
  exact Subgroup.mul_mem_sup hn hk

/-- Subgroups that complement each other in the ambient group and live in `Y` complement each
other inside `Y`. -/
theorem isComplement'_subgroupOf_of_sup_eq_top {G : Type*} [Group G] {N H Y : Subgroup G}
    [N.Normal] (hHY : H ≤ Y) (hsup : N ⊔ H = ⊤) (hinf : N ⊓ H = ⊥) :
    (N.subgroupOf Y).IsComplement' (H.subgroupOf Y) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hxN, hxH⟩
    have hxN' : (x : G) ∈ N := hxN
    have hxH' : (x : G) ∈ H := hxH
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subgroup.mem_bot.mp ((disjoint_iff_inf_le.mp (disjoint_iff.mpr hinf)) ⟨hxN', hxH'⟩))
  · rw [Set.eq_univ_iff_forall]
    intro y
    have hy : (y : G) ∈ N ⊔ H := by rw [hsup]; exact Subgroup.mem_top _
    obtain ⟨n, hn, h, hh, hnh⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    refine Set.mem_mul.mpr ⟨⟨n, ?_⟩, hn, ⟨h, hHY hh⟩, hh, Subtype.ext hnh⟩
    have : n = (y : G) * h⁻¹ := by rw [← hnh]; group
    rw [this]; exact Y.mul_mem y.2 (Y.inv_mem (hHY hh))

/-- The coprimality of `|N|` with `[G : N]` passes to the images in a quotient `G ⧸ A` with
`A ≤ H` and `H` a complement of `N`. -/
theorem coprime_map_mk {G : Type*} [Group G] [Finite G] {A N H : Subgroup G} [A.Normal] [N.Normal]
    (hAH : A ≤ H) (hH : N.IsComplement' H) (hc : (Nat.card N).Coprime N.index) :
    (Nat.card (N.map (QuotientGroup.mk' A))).Coprime (N.map (QuotientGroup.mk' A)).index := by
  have hAN : A ⊓ N = ⊥ := by
    rw [← le_bot_iff]
    rintro x ⟨hxA, hxN⟩
    exact (disjoint_iff_inf_le.mp hH.disjoint) ⟨hxN, hAH hxA⟩
  have hcard : Nat.card (N.map (QuotientGroup.mk' A)) = Nat.card N := by
    rw [← Subgroup.relIndex_ker (K := N) (f := QuotientGroup.mk' A), QuotientGroup.ker_mk']
    exact Work.Hall.relIndex_eq_card_of_inf_eq_bot hAN
  have hidx : (N.map (QuotientGroup.mk' A)).index ∣ N.index :=
    Subgroup.index_map_dvd N (QuotientGroup.mk'_surjective A)
  rw [hcard]
  exact hc.coprime_dvd_right hidx

/-! ## The main induction -/

universe u

private theorem sz_conj_aux (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G] (N : Subgroup G) [N.Normal] (H K : Subgroup G),
      Nat.card G = n → (Nat.card N).Coprime N.index → Group.IsSolvable (G ⧸ N) →
      N.IsComplement' H → N.IsComplement' K → ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro G _ _ N _ H K hcard hc hsol hH hK
    by_cases hQ1 : N.index = 1
    · rw [Subgroup.index_eq_one] at hQ1
      have hHb : H = ⊥ := Subgroup.isComplement'_top_left.mp (hQ1 ▸ hH)
      have hKb : K = ⊥ := Subgroup.isComplement'_top_left.mp (hQ1 ▸ hK)
      exact ⟨1, by rw [hHb, hKb, Subgroup.map_bot]⟩
    · by_cases hp : N.index.Prime
      · exact SZUtil.conj_of_index_prime hc hp hH hK
      · have h1 : Nat.card (G ⧸ N) ≠ 1 := by rw [← Subgroup.index_eq_card]; exact hQ1
        have hp' : ¬ (Nat.card (G ⧸ N)).Prime := by rw [← Subgroup.index_eq_card]; exact hp
        obtain ⟨Ā, hĀnorm, hĀbot, hĀtop⟩ := SZUtil.exists_normal_ne_bot_ne_top hsol h1 hp'
        haveI : Ā.Normal := hĀnorm
        let M : Subgroup G := Ā.comap (QuotientGroup.mk' N)
        have hNM : N ≤ M := by
          intro x hx
          show (QuotientGroup.mk' N) x ∈ Ā
          rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
          exact Ā.one_mem
        have hMneN : M ≠ N := by
          intro hMN
          apply hĀbot
          rw [eq_bot_iff]
          rintro q hq
          obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
          have hgM : g ∈ M := hq
          rw [hMN] at hgM
          rw [Subgroup.mem_bot]
          exact (QuotientGroup.eq_one_iff g).mpr hgM
        have hMne_top : M ≠ ⊤ := by
          intro htop
          apply hĀtop
          rw [eq_top_iff]
          intro q _
          obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
          have hgM : g ∈ M := by rw [htop]; exact Subgroup.mem_top g
          exact hgM
        haveI : M.Normal := hĀnorm.comap (QuotientGroup.mk' N)
        have hcardlt : Nat.card M < n := by
          rw [← hcard]
          have h := Subgroup.card_lt_of_lt (H := M) (K := ⊤) (lt_top_iff_ne_top.mpr hMne_top)
          rwa [Subgroup.card_top] at h
        have hHM : (N.subgroupOf M).IsComplement' (H.subgroupOf M) :=
          isComplement'_subgroupOf_of_le hNM hH
        have hKM : (N.subgroupOf M).IsComplement' (K.subgroupOf M) :=
          isComplement'_subgroupOf_of_le hNM hK
        have hcM : (Nat.card (N.subgroupOf M)).Coprime (N.subgroupOf M).index :=
          coprime_card_subgroupOf_index hNM hc
        have hsolM : Group.IsSolvable (M ⧸ N.subgroupOf M) :=
          isSolvable_quotient_subgroupOf_of_isSolvable (Y := M) hsol
        obtain ⟨m, hm⟩ := ih (Nat.card M) hcardlt M (N.subgroupOf M) (H.subgroupOf M)
          (K.subgroupOf M) rfl hcM hsolM hHM hKM
        have hm2 : K ⊓ M = (H ⊓ M).map (MulAut.conj (m : G)).toMonoidHom := by
          have h := congrArg (Subgroup.map M.subtype) hm
          rw [Subgroup.subgroupOf_map_subtype] at h
          rw [show H.subgroupOf M = (H ⊓ M).subgroupOf M from
            (Subgroup.inf_subgroupOf_right H M).symm] at h
          rw [← Subgroup.comap_subtype] at h
          rw [Work.Hall.Transport.hall_map_subtype_mulAut_conj (H := H ⊓ M) (X := M)
            inf_le_right m] at h
          exact h
        let H' : Subgroup G := H.map (MulAut.conj (m : G)).toMonoidHom
        have hH'comp : N.IsComplement' H' := isComplement'_map_conj (m : G) hH
        let A : Subgroup G := K ⊓ M
        have hKM' : A = H' ⊓ M := by
          show K ⊓ M = H' ⊓ M
          rw [hm2, map_inf_conj_eq H (m : G)]
        have hH'nA : H' ≤ Subgroup.normalizer (A : Set G) := by
          rw [hKM']
          rw [Subgroup.le_normalizer_iff]
          intro h hh x hx
          rw [Subgroup.mem_inf] at hx ⊢
          exact ⟨H'.mul_mem (H'.mul_mem hh hx.1) (H'.inv_mem hh),
            (inferInstance : M.Normal).conj_mem x hx.2 h⟩
        have hKnA : K ≤ Subgroup.normalizer (A : Set G) := by
          rw [Subgroup.le_normalizer_iff]
          intro k hk x hx
          rw [Subgroup.mem_inf] at hx ⊢
          exact ⟨K.mul_mem (K.mul_mem hk hx.1) (K.inv_mem hk),
            (inferInstance : M.Normal).conj_mem x hx.2 k⟩
        by_cases hNGlt : Subgroup.normalizer (A : Set G) < ⊤
        · -- `N_G(A)` is a proper subgroup
          let Y : Subgroup G := Subgroup.normalizer (A : Set G)
          have hH'Y : H' ≤ Y := hH'nA
          have hKY : K ≤ Y := hKnA
          have hXYc : (N.subgroupOf Y).IsComplement' (H'.subgroupOf Y) :=
            isComplement'_subgroupOf_of_sup_eq_top hH'Y (sup_eq_top_of_isComplement' hH'comp)
              (disjoint_iff.mp hH'comp.disjoint)
          have hKYc : (N.subgroupOf Y).IsComplement' (K.subgroupOf Y) :=
            isComplement'_subgroupOf_of_sup_eq_top hKY (sup_eq_top_of_isComplement' hK)
              (disjoint_iff.mp hK.disjoint)
          have hcY : (Nat.card (N.subgroupOf Y)).Coprime (N.subgroupOf Y).index :=
            coprime_card_subgroupOf_index' hc
          have hsolY : Group.IsSolvable (Y ⧸ N.subgroupOf Y) :=
            isSolvable_quotient_subgroupOf_of_isSolvable (Y := Y) hsol
          have hcardYlt : Nat.card Y < n := by
            rw [← hcard]
            have h := Subgroup.card_lt_of_lt (H := Y) (K := ⊤) hNGlt
            rwa [Subgroup.card_top] at h
          obtain ⟨y, hy⟩ := ih (Nat.card Y) hcardYlt Y (N.subgroupOf Y) (H'.subgroupOf Y)
            (K.subgroupOf Y) rfl hcY hsolY hXYc hKYc
          have hy2 : K = H'.map (MulAut.conj (y : G)).toMonoidHom := by
            have h := congrArg (Subgroup.map Y.subtype) hy
            rw [Subgroup.subgroupOf_map_subtype] at h
            rw [← Subgroup.comap_subtype] at h
            rw [Work.Hall.Transport.hall_map_subtype_mulAut_conj hH'Y y] at h
            rw [inf_eq_left.mpr hKY] at h
            exact h
          refine ⟨(y : G) * (m : G), ?_⟩
          rw [hy2]
          show (H.map (MulAut.conj (m : G)).toMonoidHom).map (MulAut.conj (y : G)).toMonoidHom
              = H.map (MulAut.conj ((y : G) * (m : G))).toMonoidHom
          rw [Subgroup.map_map]
          congr 1
          ext x
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        · -- `A` is normal in `G`
          have hNormTop : Subgroup.normalizer (A : Set G) = ⊤ := by
            by_contra hne
            exact hNGlt (lt_top_iff_ne_top.mpr hne)
          have hAnorm : A.Normal := Subgroup.normalizer_eq_top_iff.mp hNormTop
          haveI : A.Normal := hAnorm
          have hAH' : A ≤ H' := by rw [hKM']; exact inf_le_left
          have hAK : A ≤ K := inf_le_left
          have hAne : A ≠ ⊥ := by
            have hcardM : Nat.card ↥M = Nat.card ↥N * Nat.card ↥A := by
              have h1 := hKM.card_mul_card
              rw [show Nat.card ↥(N.subgroupOf M) = Nat.card ↥N from
                    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv] at h1
              rw [show Nat.card ↥(K.subgroupOf M) = Nat.card ↥A from by
                    show Nat.card ↥(K.subgroupOf M) = Nat.card ↥(K ⊓ M)
                    rw [← Subgroup.subgroupOf_map_subtype K M]
                    exact (Subgroup.card_map_of_injective (f := M.subtype)
                      (Subgroup.subtype_injective M)).symm] at h1
              exact h1.symm
            intro hbot
            have h1 : Nat.card ↥A = 1 := by rw [hbot]; simp
            rw [h1, mul_one] at hcardM
            exact hMneN (Subgroup.eq_of_le_of_card_ge hNM (le_of_eq hcardM)).symm
          have hcardAlt : Nat.card (G ⧸ A) < n := by
            rw [← hcard, ← Subgroup.index_eq_card A]
            have h2 : 1 < Nat.card ↥A := (Subgroup.one_lt_card_iff_ne_bot A).mpr hAne
            have hpos : 0 < A.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
            calc A.index < Nat.card ↥A * A.index := lt_mul_of_one_lt_left hpos h2
              _ = Nat.card G := by rw [mul_comm, Subgroup.index_mul_card]
          have hcomp'H : (N.map (QuotientGroup.mk' A)).IsComplement'
              (H'.map (QuotientGroup.mk' A)) :=
            isComplement'_map_mk_of_le hAH' hH'comp
          have hcomp'K : (N.map (QuotientGroup.mk' A)).IsComplement'
              (K.map (QuotientGroup.mk' A)) :=
            isComplement'_map_mk_of_le hAK hK
          have hcA : (Nat.card (N.map (QuotientGroup.mk' A))).Coprime
              (N.map (QuotientGroup.mk' A)).index :=
            coprime_map_mk hAH' hH'comp hc
          have hsolA : Group.IsSolvable ((G ⧸ A) ⧸ (N.map (QuotientGroup.mk' A))) :=
            SZUtil.isSolvable_quotient_map_mk (A := A) hsol
          obtain ⟨gA, hgA⟩ := ih (Nat.card (G ⧸ A)) hcardAlt (G ⧸ A)
            (N.map (QuotientGroup.mk' A)) (H'.map (QuotientGroup.mk' A))
            (K.map (QuotientGroup.mk' A)) rfl hcA hsolA hcomp'H hcomp'K
          obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective A gA
          rw [Work.Hall.Transport.hall_map_mulAut_conj (QuotientGroup.mk' A) H' g] at hgA
          have hAH'g : A ≤ H'.map (MulAut.conj g).toMonoidHom := by
            rw [← map_conj_eq_self_of_normal hAnorm g]
            exact Subgroup.map_mono hAH'
          have hgK : K = H'.map (MulAut.conj g).toMonoidHom :=
            eq_of_map_mk'_eq hAK hAH'g hgA
          refine ⟨g * (m : G), ?_⟩
          rw [hgK]
          show (H.map (MulAut.conj (m : G)).toMonoidHom).map (MulAut.conj g).toMonoidHom
              = H.map (MulAut.conj (g * (m : G))).toMonoidHom
          rw [Subgroup.map_map]
          congr 1
          ext x
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group


theorem schurZassenhaus_conj_of_solvable_quotient {G : Type*} [Group G] [Finite G]
    {N H K : Subgroup G} [N.Normal] (hc : (Nat.card N).Coprime N.index)
    (hsol : Group.IsSolvable (G ⧸ N)) (hH : N.IsComplement' H) (hK : N.IsComplement' K) :
    ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom :=
  sz_conj_aux (Nat.card G) G N H K rfl hc hsol hH hK

end Work.Coprime
