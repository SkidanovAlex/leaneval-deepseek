/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Joins of normal pro-`p` subgroups are pro-`p`

`NK.LocalTame.IsProP p G` says that every normal subgroup of `G` of finite index has index a
power of `p` (`Submission/Work/LocalTame/Basic.lean`).  This file shows that the class of
pro-`p` groups is closed under joins of normal subgroups:

* `isProP_sup_of_normal_aux` : the binary case `IsProP p H → IsProP p K → IsProP p (H ⊔ K)`
  for `K` normal;
* `isProP_iSup_of_normal` : the general case `IsProP p (⨆ i, N i)` for `N i` normal and pro-`p`.

The mathematical content is the classical "product of two normal `p`-subgroups" argument, in the
finite-quotient formulation: if `H, K ⊴ G` and `R ≤ H ⊔ K` is normal of finite index, then
`[H ⊔ K : R] = [H ⊔ K : R ⊔ K] · [R ⊔ K : R]`, the two factors being `[H : H ⊓ (R ⊔ K)]` and
`[K : K ⊓ R]` by the second isomorphism theorem, hence both powers of `p`.

For the infinite join one first reduces to the quotient `S/M` (`M ⊴ ⨆ i, N i` of finite index),
where only finitely many of the `N i` matter: the images `P i` of the `N i` generate the finite
group `S/M`, so some finite set of indices already has join `⊤`, and the binary case applied
along the finite set finishes the job.
-/
import Mathlib
import Submission.NK.LocalTame.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

universe u v

namespace NK.LocalTame.ProP

open NK.LocalTame

/-! ## Closure of pro-`p`-ness under quotients -/

/-- **A surjective image of a pro-`p` group is pro-`p`**: preimages of normal finite index
subgroups have the same index (`Subgroup.index_comap_of_surjective`). -/
theorem isProP_of_surjective {p : ℕ} {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (h : IsProP p G) : IsProP p H := by
  intro N hNN hfin
  haveI : (N.comap f).Normal := Subgroup.Normal.comap hNN f
  have hfi' : (N.comap f).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Subgroup.index_comap_of_surjective N hf]
    exact (Subgroup.finiteIndex_iff (H := N)).mp hfin
  obtain ⟨k, hk⟩ := h (N.comap f) hfi'
  exact ⟨k, by rw [← Subgroup.index_comap_of_surjective N hf]; exact hk⟩

/-- **The range of a homomorphism out of a pro-`p` group is pro-`p`.** -/
theorem isProP_range {p : ℕ} {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H)
    (h : IsProP p G) : IsProP p ↥f.range :=
  isProP_of_surjective f.rangeRestrict f.rangeRestrict_surjective h

/-! ## Index computations -/

/-- **The second isomorphism theorem in index form**: for `M ⊴ G` and `B ≤ G`, the index of `M`
inside the subgroup `M ⊔ B` equals the index of `M ⊓ B` inside `B`. -/
theorem index_subgroupOf_eq_of_normal {G : Type u} [Group G] {M B : Subgroup G}
    (hM : M.Normal) : (M.subgroupOf B).index = (M.subgroupOf (M ⊔ B)).index := by
  haveI : (M.subgroupOf (M ⊔ B)).Normal := Subgroup.Normal.comap hM (M ⊔ B).subtype
  haveI : (M.subgroupOf B).Normal := Subgroup.Normal.comap hM B.subtype
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card, sup_comm M B]
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient B M).toEquiv

/-- **`comap` of an injective homomorphism commutes with joins of subgroups** (the two agree
as soon as the subgroups lie in the range of the map). -/
theorem comap_iSup_of_injective {A : Type u} {B : Type v} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) {ι : Type*} (s : ι → Subgroup B) (hs : ∀ i, s i ≤ f.range) :
    (⨆ i, s i).comap f = ⨆ i, (s i).comap f := by
  refine le_antisymm ?_ (Subgroup.iSup_comap_le f s)
  have h1 : (⋃ i, (s i : Set B)) ⊆ ((⨆ i, (s i).comap f).map f : Set B) := by
    rintro y hy
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
    obtain ⟨x, hx⟩ : ∃ x, f x = y := MonoidHom.mem_range.mp (hs i hyi)
    exact ⟨x, Subgroup.mem_iSup_of_mem i (by rw [Subgroup.mem_comap, hx]; exact hyi), hx⟩
  calc (⨆ i, s i).comap f = (Subgroup.closure (⋃ i, (s i : Set B))).comap f := by
        rw [Subgroup.iSup_eq_closure]
    _ ≤ ((⨆ i, (s i).comap f).map f).comap f :=
        Subgroup.comap_mono ((Subgroup.closure_le _).mpr h1)
    _ = ⨆ i, (s i).comap f := by
        rw [Subgroup.comap_map_eq, f.ker_eq_bot hf, sup_bot_eq]

/-! ## The binary case -/

/-- **The join of two normal pro-`p` subgroups is pro-`p`.** -/
theorem isProP_sup_of_normal_aux {p : ℕ} {G : Type u} [Group G] {H K : Subgroup G}
    (hK : K.Normal) (hH : IsProP p ↥H) (hKp : IsProP p ↥K) : IsProP p ↥(H ⊔ K) := by
  haveI := hK
  set T : Subgroup G := H ⊔ K with hT
  set H' : Subgroup ↥T := H.subgroupOf T with hH'def
  set K' : Subgroup ↥T := K.subgroupOf T with hK'def
  have hH' : IsProP p ↥H' :=
    (isProP_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : H ≤ T)) p).mpr hH
  have hK' : IsProP p ↥K' :=
    (isProP_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : K ≤ T)) p).mpr hKp
  haveI hK'norm : K'.Normal := Subgroup.Normal.comap hK T.subtype
  have htop : H' ⊔ K' = ⊤ := by
    have h := Subgroup.subgroupOf_sup (le_sup_left : H ≤ T) (le_sup_right : K ≤ T)
    rw [← hT] at h
    rw [← hH'def, ← hK'def] at h
    rw [← h]
    exact Subgroup.subgroupOf_self T
  have hsup_top : ∀ R : Subgroup ↥T, (R ⊔ K') ⊔ H' = ⊤ := by
    intro R
    refine eq_top_iff.mpr ?_
    rw [← htop]
    exact sup_le le_sup_right (le_trans le_sup_right le_sup_left)
  have hsub_top : ∀ M : Subgroup ↥T, (M.subgroupOf (⊤ : Subgroup ↥T)).index = M.index :=
    fun M => Subgroup.relIndex_top_right (H := M)
  intro R hRnorm hRfin
  haveI := hRnorm
  have hRne : R.index ≠ 0 := hRfin.index_ne_zero
  have hrel : R.relIndex (R ⊔ K') * (R ⊔ K').index = R.index :=
    Subgroup.relIndex_mul_index le_sup_left
  have hrelne : R.relIndex (R ⊔ K') ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hrel; exact hRne hrel.symm
  have hsupK'ne : (R ⊔ K').index ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hrel; exact hRne hrel.symm
  have hK'fin : (R.subgroupOf K').FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, index_subgroupOf_eq_of_normal hRnorm]
    exact hrelne
  obtain ⟨a, ha⟩ := hK' (R.subgroupOf K') hK'fin
  have hA : R.relIndex (R ⊔ K') = p ^ a := by
    change (R.subgroupOf (R ⊔ K')).index = p ^ a
    rw [← index_subgroupOf_eq_of_normal hRnorm, ha]
  haveI : (R ⊔ K').Normal := Subgroup.sup_normal R K'
  have hTfin : ((R ⊔ K').subgroupOf H').FiniteIndex := by
    rw [Subgroup.finiteIndex_iff,
      index_subgroupOf_eq_of_normal (inferInstance : (R ⊔ K').Normal), hsup_top R, hsub_top]
    exact hsupK'ne
  obtain ⟨b, hb⟩ := hH' ((R ⊔ K').subgroupOf H') hTfin
  have hB : (R ⊔ K').index = p ^ b := by
    rw [← hb, index_subgroupOf_eq_of_normal (inferInstance : (R ⊔ K').Normal),
      hsup_top R, hsub_top]
  refine ⟨a + b, ?_⟩
  calc R.index = R.relIndex (R ⊔ K') * (R ⊔ K').index := hrel.symm
    _ = p ^ a * p ^ b := by rw [hA, hB]
    _ = p ^ (a + b) := (pow_add p a b).symm

/-- **The join of a finite family of normal pro-`p` subgroups is pro-`p`** (induction on the
finite set, using the binary case). -/
theorem isProP_finset_sup {p : ℕ} {Q : Type u} [Group Q] {ι : Type*} (P : ι → Subgroup Q)
    (hPnorm : ∀ i, (P i).Normal) (hPpro : ∀ i, IsProP p ↥(P i)) (t : Finset ι) :
    IsProP p ↥(t.sup P) := by
  classical
  induction t using Finset.induction with
  | empty =>
      rw [Finset.sup_empty]
      intro R hRnorm hRfin
      refine ⟨0, ?_⟩
      have htop : R = ⊤ := (Subgroup.eq_top_iff' R).mpr fun x => by
        rw [Subsingleton.elim x 1]
        exact R.one_mem
      rw [htop, Subgroup.index_top, pow_zero]
  | insert a t ha ih =>
      rw [Finset.sup_insert, sup_comm]
      exact isProP_sup_of_normal_aux (hPnorm a) ih (hPpro a)

/-! ## The join of an arbitrary family of normal pro-`p` subgroups -/

/-- **A join of normal pro-`p` subgroups is pro-`p`.**

For `M ⊴ ⨆ i, N i` of finite index, the quotient `S/M` is generated by the images `P i` of the
`N i`; as `S/M` is finite, some finite subfamily already has join `⊤`, and the finite case
`isProP_finset_sup` computes that `Nat.card (S/M)` is a power of `p`. -/
theorem isProP_iSup_of_normal {G : Type*} [Group G] {ι : Type*} {p : ℕ} (N : ι → Subgroup G)
    (hN : ∀ i, (N i).Normal) (hp : ∀ i, IsProP p ↥(N i)) : IsProP p ↥(⨆ i, N i) := by
  classical
  set S : Subgroup G := ⨆ i, N i with hS
  have hNle : ∀ i, N i ≤ S := fun i => le_iSup (fun i => N i) i
  intro M hMnorm hMfin
  haveI := hMnorm
  let Q := ↥S ⧸ M
  haveI hQfin : Finite Q := Subgroup.finiteIndex_iff_finite_quotient.mp hMfin
  let π : ↥S →* Q := QuotientGroup.mk' M
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective M
  let P : ι → Subgroup Q := fun i => ((N i).subgroupOf S).map π
  have hPnorm : ∀ i, (P i).Normal := by
    intro i
    haveI : ((N i).subgroupOf S).Normal := Subgroup.Normal.comap (hN i) S.subtype
    exact Subgroup.Normal.map inferInstance π hπ
  have hPpro : ∀ i, IsProP p ↥(P i) := by
    intro i
    have hr : (π.comp (Subgroup.inclusion (hNle i))).range = P i := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    have h2 := isProP_range (π.comp (Subgroup.inclusion (hNle i))) (hp i)
    rwa [hr] at h2
  have hgen : ⨆ i, P i = ⊤ := by
    have h1 : ⨆ i, (N i).subgroupOf S = ⊤ := by
      have h := comap_iSup_of_injective S.subtype S.subtype_injective (fun i => N i)
        (fun i => by rw [Subgroup.range_subtype]; exact hNle i)
      rw [show (⨆ i, (N i).subgroupOf S) = ⨆ i, (N i).comap S.subtype from rfl, ← h, ← hS]
      exact Subgroup.subgroupOf_self S
    have hP : (⨆ i, P i) = (⨆ i, (N i).subgroupOf S).map π := by
      rw [Subgroup.map_iSup]
    rw [hP, h1, Subgroup.map_top_of_surjective π hπ]
  have hDfin : (Set.range (fun t : Finset ι => t.sup P)).Finite :=
    Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  obtain ⟨N₀, hN₀max⟩ := Finset.exists_maximal (s := hDfin.toFinset) (by
    refine ⟨⊥, ?_⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨∅, Finset.sup_empty⟩)
  obtain ⟨t₀, ht₀⟩ := (Set.Finite.mem_toFinset hDfin).mp hN₀max.1
  have ht₀' : t₀.sup P = N₀ := ht₀
  have hall : ∀ i, P i ≤ N₀ := by
    intro i
    have hmem : P i ⊔ N₀ ∈ hDfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨insert i t₀, by simp only [Finset.sup_insert, ht₀']⟩
    exact le_sup_left.trans (hN₀max.2 hmem le_sup_right)
  have htop : t₀.sup P = ⊤ := by
    rw [ht₀']
    exact le_antisymm le_top (le_trans (le_of_eq hgen.symm) (iSup_le hall))
  have hIsProP : IsProP p ↥(t₀.sup P) := isProP_finset_sup P hPnorm hPpro t₀
  rw [htop] at hIsProP
  have hbotfin : (⊥ : Subgroup ↥(⊤ : Subgroup Q)).FiniteIndex := inferInstance
  obtain ⟨k, hk⟩ := hIsProP ⊥ hbotfin
  refine ⟨k, ?_⟩
  calc M.index = Nat.card Q := Subgroup.index_eq_card M
    _ = Nat.card ↥(⊤ : Subgroup Q) := (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
    _ = (⊥ : Subgroup ↥(⊤ : Subgroup Q)).index := (Subgroup.index_bot).symm
    _ = p ^ k := hk

end NK.LocalTame.ProP
