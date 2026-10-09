/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The number of index-`p` subgroups is a profinite-completion invariant

For a commutative group `A` and a prime `p`, the number of subgroups of index `p` of `A` equals
the number of subgroups of index `p` of its profinite completion `A^∧`.

The proof splits into two cases, according to the size of the maximal elementary abelian
`p`-quotient `E(A) = A ⧸ A^p`.

* **`E(A)` finite.**  Then the `p`-th power subgroup of the completion is exactly the kernel of
  the continuous map `A^∧ ↠ E(A)` extending the quotient map `A ↠ A ⧸ A^p`; indeed the kernel
  is open, the `p`-th power subgroup is closed, and on the dense image of `A` the two agree, so
  density identifies them.  Hence `E(A^∧) ≅ E(A)` and both counts equal `(|E(A)| - 1)/(p - 1)`,
  the number of hyperplanes of the elementary abelian `p`-group `E(A)`.

* **`E(A)` infinite.**  Then `E(A)` is an infinite `𝔽_p`-vector space, so it has infinitely many
  hyperplanes, and pulling them back along `A ↠ E(A)` shows that `A` has infinitely many index-`p`
  subgroups.  These inject into the index-`p` subgroups of the completion, by sending `K` to the
  kernel of the lift of the quotient map `A ↠ A/K`.  Hence both sets are infinite and both
  `Nat.card`s vanish.

The mathematics is elementary; the formal work is the interplay of `Nat.card` with the (possibly
infinite) sets of subgroups, and the construction of the lifts through the universal property of
the profinite completion.
-/
import Mathlib
import Submission.NK.LocalAnabelian.All
import Submission.NK.LocalInputs.CommGroupRank.hasFrattiniRank_of_natCard_quot_powSubgroup
import Submission.NK.LocalAnabelian.Counting.natCard_indexP_subgroups_of_exp_p
import Submission.NK.LocalInputs.CommGroupRank.infinite_indexP_subgroups_of_infinite_exp_p

namespace NK.LocalInputs.CommGroupRank

open scoped Classical
open scoped IsMulCommutative

noncomputable section

universe u

/-- The underlying type of the profinite completion of a group `A`. -/
abbrev cpl (A : Type u) [Group A] : Type u :=
  (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A)).toProfinite.toTop

/-- The canonical map `A →* A^∧` from a group to its profinite completion. -/
abbrev cplEta (A : Type u) [Group A] : A →* cpl A :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of A)).hom

/-- The completion of a commutative group is commutative. -/
theorem isMulCommutative_cpl (A : Type u) [CommGroup A] : IsMulCommutative (cpl A) := by
  refine IsMulCommutative.of_comm (fun x y => ?_)
  have hη : Dense (Set.range (cplEta A)) := ProfiniteGrp.ProfiniteCompletion.denseRange _
  have hcont1 : Continuous fun p : cpl A × cpl A => p.1 * p.2 := continuous_fst.mul continuous_snd
  have hcont2 : Continuous fun p : cpl A × cpl A => p.2 * p.1 := continuous_snd.mul continuous_fst
  have hdense : DenseRange fun a : A × A => ((cplEta A a.1, cplEta A a.2) : cpl A × cpl A) := by
    rw [DenseRange, show (fun a : A × A => ((cplEta A a.1, cplEta A a.2) : cpl A × cpl A))
      = Prod.map (cplEta A) (cplEta A) from rfl, Set.range_prodMap]
    exact Dense.prod hη hη
  have heq : (fun p : cpl A × cpl A => p.1 * p.2) ∘ (fun a : A × A => ((cplEta A a.1, cplEta A a.2) : cpl A × cpl A))
      = (fun p : cpl A × cpl A => p.2 * p.1) ∘ (fun a : A × A => ((cplEta A a.1, cplEta A a.2) : cpl A × cpl A)) := by
    funext a
    exact (show cplEta A a.1 * cplEta A a.2 = cplEta A a.2 * cplEta A a.1 by
      rw [← map_mul, ← map_mul, mul_comm])
  have hfun := DenseRange.equalizer hdense hcont1 hcont2 heq
  exact congrFun hfun (x, y)

/-- The profinite completion of a commutative group is a commutative group. -/
instance instIsMulCommutativeCpl (A : Type u) [CommGroup A] : IsMulCommutative (cpl A) :=
  isMulCommutative_cpl A

/-- Counting index-`p` subgroups of a commutative group with finite `C ⧸ C^p`. -/
theorem numIndexSubgroups_eq_card_quot (C : Type u) [CommGroup C] {p : ℕ} (hp : p.Prime)
    [Finite (C ⧸ (powMonoidHom p : C →* C).range)] :
    NK.LocalAnabelian.numIndexSubgroups p C =
      (Nat.card (C ⧸ (powMonoidHom p : C →* C).range) - 1) / (p - 1) := by
  rw [NK.LocalAnabelian.numIndexSubgroups, natCard_indexP_eq_natCard_quot_powSubgroup]
  exact NK.LocalAnabelian.Counting.natCard_indexP_subgroups_of_exp_p _ p hp (fun x => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (powMonoidHom p : C →* C).range x
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩)

/-- In the finite case the maximal elementary abelian `p`-quotients of `A` and of its profinite
completion are equinumerous. -/
theorem natCard_quot_pow_cpl_eq_of_finite (A : Type u) [CommGroup A] {p : ℕ} (hp : p.Prime)
    [Finite (A ⧸ (powMonoidHom p : A →* A).range)] :
    Nat.card (cpl A ⧸ (powMonoidHom p : cpl A →* cpl A).range) =
      Nat.card (A ⧸ (powMonoidHom p : A →* A).range) := by
  have hmc : IsMulCommutative (cpl A) := isMulCommutative_cpl A
  let Λ : Subgroup A := (powMonoidHom p : A →* A).range
  let E := A ⧸ Λ
  let q : A →* E := QuotientGroup.mk' Λ
  have hq_surj : Function.Surjective q := QuotientGroup.mk'_surjective Λ
  have hq_ker : q.ker = Λ := QuotientGroup.ker_mk' Λ
  let P : ProfiniteGrp := ProfiniteGrp.ofFiniteGrp (FiniteGrp.of E)
  let φ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A) ⟶ P :=
    ProfiniteGrp.ProfiniteCompletion.lift (P := P) (GrpCat.ofHom (q : A →* ↑P.toProfinite.toTop))
  let φm : cpl A →* E := φ.hom.toMonoidHom
  have hφη : φm.comp (cplEta A) = q := by
    refine MonoidHom.ext (fun a => ?_)
    have h := CategoryTheory.ConcreteCategory.congr_hom (ProfiniteGrp.ProfiniteCompletion.lift_eta
      (P := P) (f := GrpCat.ofHom (q : A →* ↑P.toProfinite.toTop))) a
    exact h
  have hsurj : Function.Surjective φm := by
    intro y
    obtain ⟨a, ha⟩ := hq_surj y
    exact ⟨cplEta A a, by
      rw [show φm (cplEta A a) = (φm.comp (cplEta A)) a from rfl, hφη, ha]⟩
  have hqa : ∀ a : A, φm (cplEta A a) = q a := fun a =>
    congrArg (fun f : A →* E => f a) hφη
  have hNcomap : φm.ker.comap (cplEta A) = Λ := by
    ext a
    rw [Subgroup.mem_comap, MonoidHom.mem_ker, hqa a, ← MonoidHom.mem_ker, hq_ker]
  -- `E` has exponent `p`
  have hEexp : ∀ z : E, z ^ p = 1 := by
    intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Λ z
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr ⟨w, rfl⟩
  -- the `p`-th power subgroup is contained in the kernel
  have hge : (powMonoidHom p : cpl A →* cpl A).range ≤ φm.ker := by
    rintro x ⟨y, rfl⟩
    change φm (y ^ p) = 1
    rw [map_pow]
    exact hEexp (φm y)
  -- the kernel is open: it is closed and of finite index
  haveI hker_fin : φm.ker.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj]
    exact Nat.card_ne_zero.mpr ⟨⟨⟨1, Subgroup.mem_top 1⟩⟩, inferInstance⟩
  have hopen : IsOpen ((φm.ker : Set (cpl A))) := by
    refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
    have hEq : (φm.ker : Set (cpl A)) = φm ⁻¹' ({1} : Set E) := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [hEq]
    exact isClosed_singleton.preimage (φ.hom.continuous_toFun)
  -- the `p`-th power subgroup is closed
  have hclosed : IsClosed (((powMonoidHom p : cpl A →* cpl A).range : Subgroup (cpl A)) :
      Set (cpl A)) := by
    convert (isCompact_range (continuous_pow (M := cpl A) p)).isClosed using 1
    ext x
    simp
  have hη : Dense (Set.range (cplEta A)) := ProfiniteGrp.ProfiniteCompletion.denseRange _
  -- the reverse inclusion, by density
  have hle : φm.ker ≤ (powMonoidHom p : cpl A →* cpl A).range := by
    intro x hx
    have hST : ((cplEta A) '' (Λ : Set A)) ⊆
        ((powMonoidHom p : cpl A →* cpl A).range : Set (cpl A)) := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, rfl⟩ := ha
      exact ⟨cplEta A b, by
        simp only [powMonoidHom_apply]
        exact (map_pow (cplEta A) b p).symm⟩
    refine (IsClosed.closure_subset_iff hclosed).mpr hST ?_
    rw [mem_closure_iff]
    intro U hU hxU
    have hUopen : IsOpen (U ∩ (φm.ker : Set (cpl A))) := hU.inter hopen
    have hne : (U ∩ (φm.ker : Set (cpl A))).Nonempty := ⟨x, hxU, hx⟩
    obtain ⟨z, hzrange, hzU, hzN⟩ := hη.exists_mem_open hUopen hne
    obtain ⟨a, rfl⟩ := hzrange
    have haΛ : a ∈ Λ := by
      have h1 : a ∈ (φm.ker).comap (cplEta A) := hzN
      rwa [hNcomap] at h1
    exact ⟨cplEta A a, hzU, ⟨a, haΛ, rfl⟩⟩
  have hN : φm.ker = (powMonoidHom p : cpl A →* cpl A).range := le_antisymm hle hge
  rw [← hN]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φm hsurj).toEquiv

/-- If the maximal elementary abelian `p`-quotient of `A` is infinite, then `A` has infinitely
many subgroups of index `p`. -/
theorem infinite_indexP_of_infinite_quot (A : Type u) [CommGroup A] {p : ℕ} (hp : p.Prime)
    (h : Infinite (A ⧸ (powMonoidHom p : A →* A).range)) :
    Infinite {K : Subgroup A // K.index = p} := by
  let Λ : Subgroup A := (powMonoidHom p : A →* A).range
  let f : A →* A ⧸ Λ := QuotientGroup.mk' Λ
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective Λ
  have hexp : ∀ z : A ⧸ Λ, z ^ p = 1 := by
    intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Λ z
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr ⟨w, rfl⟩
  have hh : Infinite (A ⧸ Λ) := h
  haveI : Infinite {K : Subgroup (A ⧸ Λ) // K.index = p} :=
    infinite_indexP_subgroups_of_infinite_exp_p hp hh hexp
  refine Infinite.of_injective (fun K : {K : Subgroup (A ⧸ Λ) // K.index = p} =>
    (⟨K.1.comap f, (Subgroup.index_comap_of_surjective K.1 hf).trans K.2⟩ :
      {K : Subgroup A // K.index = p})) ?_
  intro K K' hKK
  have h3 : K.1.comap f = K'.1.comap f := congrArg Subtype.val hKK
  have h1 : (K.1.comap f).map f = K.1 := Subgroup.map_comap_eq_self_of_surjective hf K.1
  have h2 : (K'.1.comap f).map f = K'.1 := Subgroup.map_comap_eq_self_of_surjective hf K'.1
  refine Subtype.ext ?_
  rw [← h1, ← h2, h3]

/-- **The injection from index-`p` subgroups of `A` into those of its profinite completion**:
`K` is sent to the kernel of the lift of the quotient map `A ↠ A/K` to the (finite) completion. -/
theorem infinite_indexP_cpl_of_infinite (A : Type u) [CommGroup A] {p : ℕ} (hp : p.Prime)
    (h : Infinite {K : Subgroup A // K.index = p}) :
    Infinite {L : Subgroup (cpl A) // L.index = p} := by
  haveI hfin : ∀ K : {K : Subgroup A // K.index = p}, Finite (A ⧸ K.1) := fun K =>
    Nat.finite_of_card_ne_zero (by
      rw [← Subgroup.index_eq_card K.1, K.2]
      exact hp.ne_zero)
  let P : {K : Subgroup A // K.index = p} → ProfiniteGrp := fun K =>
    ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (A ⧸ K.1))
  let ψ : ∀ K : {K : Subgroup A // K.index = p},
      ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A) ⟶ P K := fun K =>
    ProfiniteGrp.ProfiniteCompletion.lift (P := P K)
      (GrpCat.ofHom (QuotientGroup.mk' K.1 : A →* ↑(P K).toProfinite.toTop))
  have hpt : ∀ (K : {K : Subgroup A // K.index = p}) (a : A),
      (ψ K).hom.toMonoidHom (cplEta A a) =
        (QuotientGroup.mk' K.1 a : ↑(P K).toProfinite.toTop) := by
    intro K a
    exact CategoryTheory.ConcreteCategory.congr_hom (ProfiniteGrp.ProfiniteCompletion.lift_eta
      (P := P K) (f := GrpCat.ofHom (QuotientGroup.mk' K.1 : A →* ↑(P K).toProfinite.toTop))) a
  have hsurj : ∀ K : {K : Subgroup A // K.index = p}, Function.Surjective (ψ K).hom.toMonoidHom := by
    intro K y
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective K.1 y
    exact ⟨cplEta A a, by rw [hpt K a, ha]⟩
  have key : ∀ K : {K : Subgroup A // K.index = p},
      (ψ K).hom.toMonoidHom.ker.comap (cplEta A) = K.1 := by
    intro K
    have hker : (QuotientGroup.mk' K.1).ker = K.1 := QuotientGroup.ker_mk' K.1
    ext a
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    exact Iff.trans
      (show ((ψ K).hom.toMonoidHom (cplEta A a) = 1) ↔
        ((QuotientGroup.mk' K.1) a = 1) from by rw [hpt K a]; rfl)
      (show ((QuotientGroup.mk' K.1) a = 1) ↔ (a ∈ K.1) from by
        rw [← MonoidHom.mem_ker, hker])
  refine Infinite.of_injective (fun K : {K : Subgroup A // K.index = p} =>
    (⟨(ψ K).hom.toMonoidHom.ker, ?_⟩ : {L : Subgroup (cpl A) // L.index = p})) ?_
  · have h1 : ((ψ K).hom.toMonoidHom.ker).index = Nat.card (A ⧸ K.1) := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (hsurj K)]
      exact Nat.card_congr (Subgroup.topEquiv (G := A ⧸ K.1)).toEquiv
    exact h1.trans ((Subgroup.index_eq_card K.1).symm.trans K.2)
  · intro K K' hKK
    have h1 : (ψ K).hom.toMonoidHom.ker = (ψ K').hom.toMonoidHom.ker := congrArg Subtype.val hKK
    refine Subtype.ext ?_
    rw [← key K, ← key K', h1]

/-- **The number of index-`p` subgroups is a profinite-completion invariant** for commutative
groups: it depends only on the profinite completion. -/
theorem numIndexSubgroups_profiniteCompletion {A : Type*} [CommGroup A] {p : ℕ} (hp : p.Prime) :
    NK.LocalAnabelian.numIndexSubgroups p
      ((ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of A)).toProfinite.toTop) =
      NK.LocalAnabelian.numIndexSubgroups p A := by
  by_cases hfin : Finite (A ⧸ (powMonoidHom p : A →* A).range)
  · haveI hF₀ : Finite (A ⧸ (powMonoidHom p : A →* A).range) := hfin
    have hcard := natCard_quot_pow_cpl_eq_of_finite A hp
    haveI hF₁ : Finite (cpl A ⧸ (powMonoidHom p : cpl A →* cpl A).range) :=
      Nat.finite_of_card_ne_zero (by
        rw [hcard]
        exact Nat.card_ne_zero.mpr ⟨Nonempty.intro (1 : A ⧸ (powMonoidHom p : A →* A).range), hF₀⟩)
    rw [numIndexSubgroups_eq_card_quot (cpl A) hp, numIndexSubgroups_eq_card_quot A hp, hcard]
  · have hEinf : Infinite (A ⧸ (powMonoidHom p : A →* A).range) :=
      not_finite_iff_infinite.mp hfin
    haveI hinfA : Infinite {K : Subgroup A // K.index = p} :=
      infinite_indexP_of_infinite_quot A hp hEinf
    haveI hinfC : Infinite {L : Subgroup (cpl A) // L.index = p} :=
      infinite_indexP_cpl_of_infinite A hp hinfA
    rw [NK.LocalAnabelian.numIndexSubgroups, NK.LocalAnabelian.numIndexSubgroups,
      Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite]


end

end NK.LocalInputs.CommGroupRank
