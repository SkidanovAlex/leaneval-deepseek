/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `p`-torsion of the profinite completion of a commutative group

`NK.LocalReciprocity.completionUnits κ` is the profinite completion `κˣ^{∧}` of the (discrete)
group `κˣ`, i.e. the limit of the finite quotients `κˣ ⧸ N` over the finite-index normal
subgroups `N` (`ProfiniteGrp.ProfiniteCompletion.completion`).  This file proves the two general
facts about such a completion which reduce the arithmetic statement "the `p`-torsion of `κˣ^{∧}`
is `μ_p(κ)`" (`NK.PTorsionTop.UnitsTorsion`) to computations inside the discrete group `κˣ`.

Throughout, `A` is a **commutative** group (in the application `A = κˣ`) and `p` a prime.

## The two facts

**(1) No new `p`-torsion (`completion_pow_eq_one_of`).**  If `A` has no element of order `p`
(`∀ y, y ^ p = 1 → y = 1`) and `A ⧸ A ^ p` is finite, then the profinite completion has no
element of order `p` either.  This direction is the one that is *not* formal: a `ℤ/p`-quotient of
a group does not produce `p`-torsion (`ℤ ↠ ℤ/p` with `ℤ` torsion-free).  The proof uses the
levels `A^{p^k}`:

* the transition `A ⧸ A^{p^{k+1}} → A ⧸ A^{p^k}` is **zero on `p`-torsion**
  (`map_pow_range_pow_eq_one`): if `y ^ p ∈ A^{p^{k+1}}` then `y ∈ A^{p^k}`, because
  `y ^ p = c^{p^{k+1}} = (c^{p^k})^p` and `A` has no `p`-torsion;
* hence an element `x` of order `p` in the completion has trivial component at every level
  `A^{p^k}`;
* for an arbitrary finite-index `N`, compatibility of the family at the three levels `N`,
  `N ⊔ A^{p^K}` and `A^{p^K}` puts the component `x_N` into the subgroup
  `L_K = (A^{p^K} N)/N` of the *finite* group `A ⧸ N`; choosing `K` with `L_{K+1} = L_K` (which
  exists because `A ⧸ N` is finite) gives `L_K = L_K^p`, so the `p`-th power map on `L_K` is
  injective and `x_N`, being `p`-torsion in `L_K`, is `1`.

**(2) `p`-torsion does survive (`hasPTorsion_completion_of_exponent`).**  If `ζ ∈ A` has order
dividing `p` and is not a `p^{N+1}`-th power — for instance if `ζ` is a `p`-power root of unity
whose order is bounded by `p ^ N`, which is the case for the roots of unity of a `p`-adic field —
then its image in the completion is non-trivial of order dividing `p`.

## Main results

* `NK.PTorsionTop.completion_pow_eq_one_of` — no new `p`-torsion;
* `NK.PTorsionTop.hasPTorsion_completion_of_exponent` — `p`-torsion survives;
* `NK.PTorsionTop.finite_quot_pow_range_pow`, `NK.PTorsionTop.map_pow_range_pow_eq_one`,
  `NK.PTorsionTop.powRange`, `NK.PTorsionTop.Subgroup.eq_of_le_of_natCard_eq`.
-/
import Mathlib
import Submission.NK.PTorsionTop.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.PTorsionTop

universe u

noncomputable section

abbrev completion (A : Type u) [Group A] : Type u :=
  (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A)).toProfinite.toTop

abbrev completionEta (A : Type u) [Group A] : A →* completion A :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of A)).hom

variable {A : Type u} [CommGroup A]

section

theorem completion_mul_apply (x y : completion A) (N : FiniteIndexNormalSubgroup (GrpCat.of A)) :
    (x * y).1 N = x.1 N * y.1 N := rfl

theorem completion_eq_one_iff (x : completion A) : x = 1 ↔ ∀ N, x.1 N = 1 := by
  constructor
  · intro h N; rw [h]; rfl
  · intro h; exact Subtype.ext (funext h)

theorem completionEta_apply (a : A) (N : FiniteIndexNormalSubgroup (GrpCat.of A)) :
    (completionEta A a).1 N = QuotientGroup.mk a := rfl

theorem completion_pow_apply (x : completion A) (n : ℕ)
    (N : FiniteIndexNormalSubgroup (GrpCat.of A)) :
    (x ^ n).1 N = (x.1 N) ^ n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, completion_mul_apply, ih]

end

theorem pow_range_succ_le (A : Type u) [CommGroup A] (p k : ℕ) :
    (powMonoidHom (p ^ (k + 1)) : A →* A).range ≤ (powMonoidHom (p ^ k) : A →* A).range := by
  rintro _ ⟨a, rfl⟩
  refine ⟨a ^ p, ?_⟩
  simp only [powMonoidHom_apply]
  rw [pow_succ', pow_mul]

theorem finite_quot_pow_range_pow (A : Type u) [CommGroup A] {p : ℕ}
    (h : Finite (A ⧸ (powMonoidHom p : A →* A).range)) (k : ℕ) :
    Finite (A ⧸ (powMonoidHom (p ^ k) : A →* A).range) := by
  induction k with
  | zero =>
    have htop : (powMonoidHom (p ^ 0) : A →* A).range = ⊤ := by
      rw [pow_zero]
      refine eq_top_iff.mpr fun x _ => ⟨x, by simp⟩
    rw [htop]
    infer_instance
  | succ k ih =>
    haveI := ih
    set B : Subgroup A := (powMonoidHom (p ^ k) : A →* A).range with hB
    set C : Subgroup A := (powMonoidHom (p ^ (k + 1)) : A →* A).range with hC
    have hCB : C ≤ B := pow_range_succ_le A p k
    have hBidx : B.index ≠ 0 :=
      (Subgroup.finiteIndex_iff (H := B)).mp (Subgroup.finiteIndex_of_finite_quotient (H := B))
    have hfB : ∀ a : A, (powMonoidHom (p ^ k) : A →* A) a ∈ B := fun a => ⟨a, rfl⟩
    let g : A →* B := ((powMonoidHom (p ^ k) : A →* A)).codRestrict B hfB
    let f : A →* B ⧸ C.subgroupOf B := (QuotientGroup.mk' (C.subgroupOf B)).comp g
    have hfker : (powMonoidHom p : A →* A).range ≤ f.ker := by
      rintro _ ⟨b, rfl⟩
      rw [MonoidHom.mem_ker]
      show (QuotientGroup.mk' (C.subgroupOf B)) (g (b ^ p)) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      show (powMonoidHom (p ^ k)) (b ^ p) ∈ C
      refine ⟨b, ?_⟩
      simp only [powMonoidHom_apply]
      rw [pow_succ', pow_mul]
    let ψ : A ⧸ (powMonoidHom p : A →* A).range →* B ⧸ C.subgroupOf B :=
      QuotientGroup.lift _ f hfker
    have hψ : Function.Surjective ψ := by
      intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf B) y
      obtain ⟨a, ha⟩ := y.2
      refine ⟨QuotientGroup.mk a, ?_⟩
      rw [QuotientGroup.lift_mk]
      show (QuotientGroup.mk' (C.subgroupOf B)) (g a) = _
      rw [QuotientGroup.mk'_apply]
      refine congrArg _ (Subtype.ext ?_)
      simp only [g, MonoidHom.codRestrict, MonoidHom.coe_mk, OneHom.coe_mk, powMonoidHom_apply]
      exact ha
    have hfinBC : Finite (B ⧸ C.subgroupOf B) := Finite.of_surjective ψ hψ
    have hrel : C.relIndex B ≠ 0 := by
      rw [Subgroup.relIndex, Subgroup.index_ne_zero_iff_finite]
      exact hfinBC
    have hidx : C.index ≠ 0 := by
      rw [← Subgroup.relIndex_mul_index hCB]
      exact Nat.mul_ne_zero hrel hBidx
    rw [Subgroup.index_ne_zero_iff_finite] at hidx
    exact hidx

section Zero

variable {p : ℕ}

theorem pow_range_succ_le_comap (A : Type u) [CommGroup A] (p k : ℕ) :
    (powMonoidHom (p ^ (k + 1)) : A →* A).range ≤
      Subgroup.comap (MonoidHom.id A) ((powMonoidHom (p ^ k) : A →* A).range) :=
  fun a ha => pow_range_succ_le A p k ha

theorem map_pow_range_pow_eq_one (hp : p.Prime) (htf : ∀ y : A, y ^ p = 1 → y = 1) (k : ℕ)
    (y : A ⧸ (powMonoidHom (p ^ (k + 1)) : A →* A).range) (hy : y ^ p = 1) :
    QuotientGroup.map ((powMonoidHom (p ^ (k + 1)) : A →* A).range)
      ((powMonoidHom (p ^ k) : A →* A).range) (MonoidHom.id A)
      (pow_range_succ_le_comap A p k) y = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
    ((powMonoidHom (p ^ (k + 1)) : A →* A).range) y
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
  obtain ⟨c, hc⟩ := hy
  simp only [powMonoidHom_apply] at hc
  have hd : a ^ p = (c ^ (p ^ k)) ^ p := by
    rw [← hc, pow_succ', mul_comm, pow_mul]
  have ha : a = c ^ (p ^ k) := by
    have h1 : (a * (c ^ (p ^ k))⁻¹) ^ p = 1 := by
      rw [mul_pow, inv_pow, hd, mul_inv_cancel]
    exact mul_inv_eq_one.mp (htf _ h1)
  have hgoal : (QuotientGroup.map ((powMonoidHom (p ^ (k + 1)) : A →* A).range)
      ((powMonoidHom (p ^ k) : A →* A).range) (MonoidHom.id A)
      (pow_range_succ_le_comap A p k)) ((QuotientGroup.mk' _) a) = 1 := by
    simp only [QuotientGroup.map_mk']
    exact QuotientGroup.eq_one_iff _ |>.mpr ⟨c, by
      simp only [MonoidHom.id_apply, powMonoidHom_apply]
      exact ha.symm⟩
  exact hgoal

end Zero

end

end NK.PTorsionTop

namespace NK.PTorsionTop

universe u

noncomputable section

section Main

variable {A : Type u} [CommGroup A] {p : ℕ}

/-- For subgroups of a **finite** group, containment plus equality of cardinality is equality. -/
theorem Subgroup.eq_of_le_of_natCard_eq {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H ≤ K) (hcard : Nat.card H = Nat.card K) : H = K := by
  haveI : Nonempty G := ⟨1⟩
  have hcardG : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h1 : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
  have h2 : Nat.card ↥K * K.index = Nat.card G := Subgroup.card_mul_index K
  have hidx : H.index = K.index := by
    have h3 : Nat.card ↥H * H.index = Nat.card ↥H * K.index := by
      rw [h1, hcard, h2]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
  have hKne : K.index ≠ 0 := by
    intro h
    rw [h, mul_zero] at h2
    exact hcardG h2.symm
  have hrel : H.relIndex K = 1 := by
    have h5 : H.relIndex K * K.index = 1 * K.index := by
      rw [one_mul, Subgroup.relIndex_mul_index hHK, hidx]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hKne) h5
  exact le_antisymm hHK (Subgroup.relIndex_eq_one.mp hrel)

/-- The `k`-th `p`-power level of `A`. -/
def powLevel (A : Type u) [CommGroup A] (p k : ℕ)
    [Finite (A ⧸ (powMonoidHom (p ^ k) : A →* A).range)] :
    FiniteIndexNormalSubgroup (GrpCat.of A) :=
  haveI : ((powMonoidHom (p ^ k) : A →* A).range).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  FiniteIndexNormalSubgroup.ofSubgroup ((powMonoidHom (p ^ k) : A →* A).range)

/-- **The completion of a group without `p`-torsion has no `p`-torsion.** -/
theorem completion_pow_eq_one_of (hp : p.Prime)
    (hfin : Finite (A ⧸ (powMonoidHom p : A →* A).range))
    (htf : ∀ y : A, y ^ p = 1 → y = 1) (x : completion A) (hx : x ^ p = 1) : x = 1 := by
  haveI : ∀ k, Finite (A ⧸ (powMonoidHom (p ^ k) : A →* A).range) :=
    fun k => finite_quot_pow_range_pow A hfin k
  have hzero : ∀ k, x.1 (powLevel A p k) = 1 := by
    intro k
    have hle : powLevel A p (k + 1) ≤ powLevel A p k := by
      intro y hy
      exact pow_range_succ_le A p k hy
    have hpt : (x.1 (powLevel A p (k + 1))) ^ p = 1 := by
      rw [← completion_pow_apply, hx]
      rfl
    have h := map_pow_range_pow_eq_one hp htf k (x.1 (powLevel A p (k + 1))) hpt
    rw [← x.2 hle.hom]
    exact h
  rw [completion_eq_one_iff]
  intro N
  by_contra hN
  haveI hQfin : Finite (A ⧸ N.toSubgroup) := Nat.finite_of_card_ne_zero (by
    rw [← Subgroup.index_eq_card]
    exact (Subgroup.finiteIndex_iff (H := N.toSubgroup)).mp N.isFiniteIndex')
  let L : ℕ → Subgroup (A ⧸ N.toSubgroup) := fun k =>
    Subgroup.map (QuotientGroup.mk' N.toSubgroup) ((powMonoidHom (p ^ k) : A →* A).range)
  have hL0 : L 0 = ⊤ := by
    show Subgroup.map (QuotientGroup.mk' N.toSubgroup) ((powMonoidHom (p ^ 0) : A →* A).range) = ⊤
    rw [pow_zero]
    have htop : (powMonoidHom 1 : A →* A).range = ⊤ := by
      refine eq_top_iff.mpr fun a _ => ⟨a, by simp⟩
    rw [htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hmono : ∀ k, L (k + 1) ≤ L k := fun k =>
    Subgroup.map_mono (pow_range_succ_le A p k)
  -- the descending chain of subgroups of the finite group `A ⧸ N` stabilises
  obtain ⟨K, hK⟩ : ∃ K, L (K + 1) = L K := by
    by_contra hcon
    push_neg at hcon
    have hstrict : ∀ k, Nat.card (L (k + 1)) < Nat.card (L k) := by
      intro k
      refine lt_of_le_of_ne (Nat.card_le_card_of_injective
        (fun a : ↥(L (k + 1)) => (⟨(a : A ⧸ N.toSubgroup), hmono k a.2⟩ : ↥(L k)))
        (fun a b hab => Subtype.ext (show (a : A ⧸ N.toSubgroup) = (b : A ⧸ N.toSubgroup) from
          congrArg (fun z : ↥(L k) => (z : A ⧸ N.toSubgroup)) hab))) ?_
      intro hcard
      exact hcon k (Subgroup.eq_of_le_of_natCard_eq (H := L (k + 1)) (K := L k) (hmono k) hcard)
    have hle : ∀ k, Nat.card (L k) + k ≤ Nat.card (L 0) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have := hstrict k
        omega
    have := hle (Nat.card (L 0) + 1)
    omega
  -- the component of `x` at the level `N` lies in `L K`
  let q : A ⧸ N.toSubgroup := x.1 N
  have hxL : q ∈ L K := by
    have hsup : N ≤ N ⊔ powLevel A p K := le_sup_left
    have hsup' : powLevel A p K ≤ N ⊔ powLevel A p K := le_sup_right
    have h1 : (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of A)).map hsup.hom q = 1 := by
      show (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of A)).map hsup.hom (x.1 N) = 1
      rw [x.2 hsup.hom, ← x.2 hsup'.hom, hzero K]
      rfl
    have hmem : q ∈ ((N ⊔ powLevel A p K).toSubgroup).map
        (QuotientGroup.mk' N.toSubgroup) := by
      have hker := QuotientGroup.ker_map (N := N.toSubgroup) ((N ⊔ powLevel A p K).toSubgroup)
        (MonoidHom.id A) (fun a ha => hsup ha)
      rw [Subgroup.comap_id] at hker
      rw [← hker, MonoidHom.mem_ker]
      exact h1
    have hbot : N.toSubgroup.map (QuotientGroup.mk' N.toSubgroup) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      rintro y ⟨w, hw, rfl⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hw
    have hsup_eq : ((N ⊔ powLevel A p K).toSubgroup).map (QuotientGroup.mk' N.toSubgroup)
        = L K := by
      rw [show (N ⊔ powLevel A p K).toSubgroup
          = N.toSubgroup ⊔ (powLevel A p K).toSubgroup from rfl,
        Subgroup.map_sup, hbot, bot_sup_eq]
      rfl
    rw [hsup_eq] at hmem
    exact hmem
  -- `L K` is stable under the `p`-th power map
  have hpow : ∀ y : ↥(L K), ∃ z : ↥(L K), z ^ p = y := by
    intro y
    have hy : (y : A ⧸ N.toSubgroup) ∈ L (K + 1) := by
      rw [hK]
      exact y.2
    rw [show L (K + 1) = Subgroup.map (QuotientGroup.mk' N.toSubgroup)
      ((powMonoidHom (p ^ (K + 1)) : A →* A).range) from rfl] at hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨w, hw, hwy⟩ := hy
    rw [MonoidHom.mem_range] at hw
    obtain ⟨v, rfl⟩ := hw
    refine ⟨⟨QuotientGroup.mk' N.toSubgroup (v ^ (p^K)), ?_⟩, ?_⟩
    · change QuotientGroup.mk' N.toSubgroup (v ^ (p^K)) ∈
        Subgroup.map (QuotientGroup.mk' N.toSubgroup) ((powMonoidHom (p ^ K) : A →* A).range)
      exact Subgroup.mem_map_of_mem _ ⟨v, rfl⟩
    · refine Subtype.ext ?_
      change ((QuotientGroup.mk' N.toSubgroup (v ^ (p^K))) ^ p : A ⧸ N.toSubgroup) = _
      rw [← map_pow, show (v ^ (p^K)) ^ p = (powMonoidHom (p^(K+1)) : A →* A) v from by
        simp only [powMonoidHom_apply]
        rw [pow_succ', ← pow_mul, mul_comm], hwy]
  haveI hLfin : Finite ↥(L K) := Finite.of_injective _ (fun a b h => Subtype.ext h)
  have hinj : Function.Injective (fun z : ↥(L K) => z ^ p) :=
    Finite.injective_iff_surjective.mpr hpow
  have hpt : q ^ p = 1 := by
    show (x.1 N) ^ p = 1
    rw [← completion_pow_apply, hx]
    rfl
  have hmem2 : (⟨q, hxL⟩ : ↥(L K)) ^ p = 1 := by
    apply Subtype.ext
    simpa using hpt
  have hone : (⟨q, hxL⟩ : ↥(L K)) = 1 := hinj (by
    show (⟨q, hxL⟩ : ↥(L K)) ^ p = (1 : ↥(L K)) ^ p
    rw [hmem2, one_pow])
  refine hN ?_
  have hq1 : q = 1 := congrArg Subtype.val hone
  show x.1 N = 1
  exact hq1

/-- The `p`-torsion of `A` survives in the completion, provided the `p`-power roots of unity of
`A` are annihilated by `p ^ N`. -/
theorem hasPTorsion_completion_of_exponent [Finite (A ⧸ (powMonoidHom p : A →* A).range)]
    (N : ℕ) (hN : ∀ ζ : A, (∃ m, ζ ^ (p ^ m) = 1) → ζ ^ (p ^ N) = 1)
    (ζ : A) (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1) :
    HasPTorsion p (completion A) := by
  haveI : ∀ k, Finite (A ⧸ (powMonoidHom (p ^ k) : A →* A).range) :=
    fun k => finite_quot_pow_range_pow A ‹_› k
  refine ⟨completionEta A ζ, ?_, ?_⟩
  · intro hcontra
    have h1 : (completionEta A ζ).1 (powLevel A p (N + 1)) = 1 := by rw [hcontra]; rfl
    rw [completionEta_apply] at h1
    have h1' : (QuotientGroup.mk ζ : A ⧸ (powLevel A p (N + 1)).toSubgroup) = 1 := h1
    rw [QuotientGroup.eq_one_iff] at h1'
    obtain ⟨w, hw⟩ := h1'
    have hw' : w ^ (p ^ (N + 1)) = ζ := by simpa only [powMonoidHom_apply] using hw
    have htor : ∃ m, w ^ (p ^ m) = 1 := ⟨N + 2, by
      have h3 : p ^ (N + 2) = p ^ (N + 1) * p := pow_succ _ _
      rw [h3, pow_mul, hw', hζp]⟩
    have hwN : w ^ (p ^ N) = 1 := hN w htor
    refine hζ1 ?_
    rw [← hw', show p ^ (N + 1) = p ^ N * p from pow_succ _ _, pow_mul, hwN, one_pow]
  · rw [← map_pow, hζp, map_one]

end Main


end
end NK.PTorsionTop
