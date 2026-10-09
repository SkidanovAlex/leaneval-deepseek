import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finitely many open-kernel homomorphisms `Gal(K'/k) →* Multiplicative (ZMod l)`

The aim is `Work.SSGRoute.finite_homs_of_finite_galoisFields`: for a separable closure `K'` of a
field `k`, a prime `l`, and the hypothesis that there are only finitely many intermediate fields
`k ≤ L ≤ K'` that are Galois of degree `l` over `k`, there are only finitely many group
homomorphisms `χ : Gal(K'/k) →* Multiplicative (ZMod l)` with open kernel (for the Krull
topology).

The mathematical content is the following.  A homomorphism `χ` with open kernel has image of
cardinality dividing `l`, hence `1` or `l`; the kernel is a closed normal subgroup, and the degree
of the fixed field `L := fixedField (ker χ)` over `k` equals the index of `ker χ` in `Gal(K'/k)`,
which is `Nat.card χ.range`, so it is `1` or `l`.  If `χ ≠ 1` then the degree is exactly `l`, so
`L` belongs to the finite set given by the hypothesis.  A homomorphism `χ` on `Gal(K'/k)` with
`ker χ = L.fixingSubgroup` factors as the quotient map `Gal(K'/k) → Gal(K'/k) ⧸ L.fixingSubgroup`
followed by a unique homomorphism on the quotient; hence two such `χ` with the same `L` are equal
as soon as they induce the same homomorphism on the quotient.  So the fibre over a fixed `L`
injects into the (finite) set of homomorphisms out of `Gal(K'/k) ⧸ L.fixingSubgroup`, and the
trivial homomorphism is handled separately.
-/

open scoped Topology

namespace Work.SSGRoute

/-! ## Auxiliary facts -/

/-- `Multiplicative (ZMod l)` has `l` elements. -/
lemma natCard_multiplicative_zmod (l : ℕ) [NeZero l] :
    Nat.card (Multiplicative (ZMod l)) = l := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

/-- For an intermediate field `L` of a Galois extension `K/k`, the quotient of `Gal(K/k)` by the
fixing subgroup of `L` has `[L : k]` elements. -/
lemma natCard_quotient_fixingSubgroup_eq_finrank {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsGalois k K] (L : IntermediateField k K) :
    Nat.card (Gal(K/k) ⧸ L.fixingSubgroup) = Module.finrank k L := by
  rw [← Subgroup.index_eq_card]
  exact (IntermediateField.finrank_eq_fixingSubgroup_index K L).symm

/-- The fixing subgroup of a Galois intermediate field is normal. -/
instance fixingSubgroup_normal_of_isGalois {k K : Type*} [Field k] [Field K] [Algebra k K]
    [IsGalois k K] (L : IntermediateField k K) [IsGalois k L] : (L.fixingSubgroup).Normal :=
  (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance

/-- The fixed field of `ker χ` is Galois over the base field. -/
lemma isGalois_fixedField_ker {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    [IsSepClosure k K'] (l : ℕ) (χ : Gal(K'/k) →* Multiplicative (ZMod l)) :
    IsGalois k (IntermediateField.fixedField χ.ker) := by
  haveI : (χ.ker).Normal := MonoidHom.normal_ker χ
  exact IsGalois.of_fixedField_normal_subgroup χ.ker

/-- For a homomorphism `χ` with open kernel, the fixed field of `ker χ` has degree over `k` equal
to the cardinality of the image of `χ`. -/
lemma finrank_fixedField_ker_eq_card_range {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    [IsSepClosure k K'] (l : ℕ) (χ : Gal(K'/k) →* Multiplicative (ZMod l))
    (hopen : IsOpen (χ.ker : Set Gal(K'/k))) :
    Module.finrank k (IntermediateField.fixedField χ.ker) = Nat.card χ.range := by
  have hfix : (IntermediateField.fixedField χ.ker).fixingSubgroup = χ.ker :=
    InfiniteGalois.fixingSubgroup_fixedField
      (⟨χ.ker, χ.ker.isClosed_of_isOpen hopen⟩ : ClosedSubgroup Gal(K'/k))
  have h1 : (IntermediateField.fixedField χ.ker).fixingSubgroup.index = Nat.card χ.range := by
    rw [hfix, Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv
  rw [IntermediateField.finrank_eq_fixingSubgroup_index K' (IntermediateField.fixedField χ.ker)]
  exact h1

/-- For a **non-trivial** homomorphism `χ : Gal(K'/k) →* Multiplicative (ZMod l)` with open kernel
and `l` prime, the fixed field of `ker χ` has degree exactly `l` over `k`. -/
lemma finrank_fixedField_ker_eq_prime {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    [IsSepClosure k K'] (l : ℕ) (hl : l.Prime)
    (χ : Gal(K'/k) →* Multiplicative (ZMod l)) (hopen : IsOpen (χ.ker : Set Gal(K'/k)))
    (hne : χ ≠ 1) :
    Module.finrank k (IntermediateField.fixedField χ.ker) = l := by
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have h1 := finrank_fixedField_ker_eq_card_range l χ hopen
  have h2 : Nat.card χ.range ∣ l := by
    have h3 := Subgroup.card_subgroup_dvd_card χ.range
    simpa [natCard_multiplicative_zmod l] using h3
  rcases hl.eq_one_or_self_of_dvd (Nat.card χ.range) h2 with h | h
  · exfalso
    have hbot : χ.range = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hss : Subsingleton χ.range := (Nat.card_eq_one_iff_unique.mp h).1
      have hx1 : (⟨x, hx⟩ : χ.range) = 1 := Subsingleton.elim _ _
      simpa using congrArg Subtype.val hx1
    exact hne (MonoidHom.range_eq_bot_iff.mp hbot)
  · exact h1.trans h

/-! ## The classification of the homomorphisms -/

/-- The set of open-kernel homomorphisms `Gal(K'/k) →* Multiplicative (ZMod l)`. -/
abbrev SSGHomSet (k K' : Type*) [Field k] [Field K'] [Algebra k K'] (l : ℕ) : Type _ :=
  {χ : Gal(K'/k) →* Multiplicative (ZMod l) // IsOpen (χ.ker : Set Gal(K'/k))}

/-- The set of degree-`l` Galois intermediate fields `k ≤ L ≤ K'`. -/
abbrev SSGBase (k K' : Type*) [Field k] [Field K'] [Algebra k K'] (l : ℕ) : Type _ :=
  {L : IntermediateField k K' // IsGalois k L ∧ Module.finrank k L = l}

/-- The classification map: the trivial homomorphism goes to `none`, every other open-kernel
homomorphism `χ` goes to the fixed field of `ker χ`, which is a degree-`l` Galois extension. -/
noncomputable def classifyFun {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    [IsSepClosure k K'] (l : ℕ) (hl : l.Prime) (χ : SSGHomSet k K' l) :
    Option (SSGBase k K' l) := by
  classical
  exact if h : χ.1 = 1 then none
    else some ⟨IntermediateField.fixedField χ.1.ker,
      isGalois_fixedField_ker l χ.1,
      finrank_fixedField_ker_eq_prime l hl χ.1 χ.2 h⟩

lemma classifyFun_of_eq_one {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    [IsSepClosure k K'] (l : ℕ) (hl : l.Prime) {χ : SSGHomSet k K' l} (h : χ.1 = 1) :
    classifyFun l hl χ = none :=
  dif_pos h

lemma classifyFun_of_ne_one {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    [IsSepClosure k K'] (l : ℕ) (hl : l.Prime) {χ : SSGHomSet k K' l} (h : χ.1 ≠ 1) :
    classifyFun l hl χ = some ⟨IntermediateField.fixedField χ.1.ker,
      isGalois_fixedField_ker l χ.1,
      finrank_fixedField_ker_eq_prime l hl χ.1 χ.2 h⟩ :=
  dif_neg h

lemma classifyFun_eq_none_iff {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    [IsSepClosure k K'] (l : ℕ) (hl : l.Prime) (χ : SSGHomSet k K' l) :
    classifyFun l hl χ = none ↔ χ.1 = 1 := by
  constructor
  · intro hc
    by_contra hne
    rw [classifyFun_of_ne_one l hl hne] at hc
    exact absurd hc (by simp)
  · exact classifyFun_of_eq_one l hl

lemma fixingSubgroup_eq_ker_of_classifyFun_eq_some {k K' : Type*} [Field k] [Field K']
    [Algebra k K'] [IsSepClosure k K'] (l : ℕ) (hl : l.Prime) (L : SSGBase k K' l)
    (χ : SSGHomSet k K' l) (hχ : classifyFun l hl χ = some L) :
    (L.1).fixingSubgroup = χ.1.ker := by
  have hne : χ.1 ≠ 1 := by
    intro h
    rw [classifyFun_of_eq_one l hl h] at hχ
    exact absurd hχ (by simp)
  have hval : IntermediateField.fixedField χ.1.ker = L.1 := by
    rw [classifyFun_of_ne_one l hl hne] at hχ
    exact congrArg Subtype.val (Option.some.inj hχ)
  rw [← hval]
  exact InfiniteGalois.fixingSubgroup_fixedField
    (⟨χ.1.ker, χ.1.ker.isClosed_of_isOpen χ.2⟩ : ClosedSubgroup Gal(K'/k))

/-- The fibre of the classification over a fixed `L` injects into the homomorphisms out of the
finite quotient `Gal(K'/k) ⧸ L.fixingSubgroup`: an open-kernel `χ` with `fixedField (ker χ) = L`
factors through that quotient, and the induced map determines `χ`. -/
noncomputable def fibreToQuotient {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    [IsSepClosure k K'] (l : ℕ) (hl : l.Prime) (L : SSGBase k K' l) [IsGalois k L.1]
    (χ : {χ : SSGHomSet k K' l // classifyFun l hl χ = some L}) :
    (Gal(K'/k) ⧸ (L.1).fixingSubgroup) →* Multiplicative (ZMod l) :=
  QuotientGroup.lift (L.1).fixingSubgroup χ.1.1
    (le_of_eq (fixingSubgroup_eq_ker_of_classifyFun_eq_some l hl L χ.1 χ.2))

lemma fibreToQuotient_comp_mk {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    [IsSepClosure k K'] (l : ℕ) (hl : l.Prime) (L : SSGBase k K' l) [IsGalois k L.1]
    (χ : {χ : SSGHomSet k K' l // classifyFun l hl χ = some L}) :
    (fibreToQuotient l hl L χ).comp (QuotientGroup.mk' (L.1).fixingSubgroup) = χ.1.1 := by
  have hfun : fibreToQuotient l hl L χ
      = QuotientGroup.lift (L.1).fixingSubgroup χ.1.1
          (le_of_eq (fixingSubgroup_eq_ker_of_classifyFun_eq_some l hl L χ.1 χ.2)) := rfl
  rw [hfun]
  ext g
  simp

lemma fibreToQuotient_injective {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    [IsSepClosure k K'] (l : ℕ) (hl : l.Prime) (L : SSGBase k K' l) [IsGalois k L.1] :
    Function.Injective (fibreToQuotient l hl L) := by
  intro a b hab
  have ha := fibreToQuotient_comp_mk l hl L a
  have hb := fibreToQuotient_comp_mk l hl L b
  rw [hab] at ha
  exact Subtype.ext (Subtype.ext (ha.symm.trans hb))

/-! ## The main theorem -/

/-- **Finitely many open-kernel homomorphisms `Gal(K'/k) →* Multiplicative (ZMod l)` from
finitely many degree-`l` Galois extensions** (`l` prime, `K'` a separable closure of `k`).

Suggested route.  A hom `χ` with open kernel has kernel of index `1` or `l` (its image is a
subgroup of `Multiplicative (ZMod l)`), so `ker χ` is an open normal subgroup.
* The trivial hom is one element; handle it separately (e.g. via `Option`).
* For `χ ≠ 1`, `ker χ` has index `l`, so by the infinite Galois correspondence
  `L := fixedField (ker χ)` is a degree-`l` Galois extension of `k`
  (`InfiniteGalois.fixingSubgroup_fixedField` for the closed subgroup `ker χ` (open, hence
  closed), `IsGalois.finrank_eq_fixingSubgroup_index`, `IsGalois.of_fixedField_normal_subgroup`).
* The fibre over a fixed `L` injects into the finite set of homs
  `Gal(K'/k) ⧸ L.fixingSubgroup →* Multiplicative (ZMod l)` (which is finite because
  `Nat.card (Gal(K'/k) ⧸ L.fixingSubgroup) = L.fixingSubgroup.index = l`): for `χ` in the fibre,
  `ker χ = L.fixingSubgroup`, and `χ` is the composite of the quotient map
  `Gal(K'/k) →* Gal(K'/k) ⧸ L.fixingSubgroup` with the induced map on the quotient, which
  determines `χ`.
Conclude by a `Sigma`-type finiteness argument over the finite set `h` (e.g.
`Finite.of_injective` into a sigma of finite types, or `Fintype.ofFinite` on the base and on each
fibre). -/
theorem finite_homs_of_finite_galoisFields {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    [IsSepClosure k K'] (l : ℕ) (hl : l.Prime)
    (h : Finite {L : IntermediateField k K' // IsGalois k L ∧ Module.finrank k L = l}) :
    Finite {χ : Gal(K'/k) →* Multiplicative (ZMod l) // IsOpen (χ.ker : Set Gal(K'/k))} := by
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : Finite (SSGBase k K' l) := h
  have hfib : ∀ x : Option (SSGBase k K' l),
      Finite {χ : SSGHomSet k K' l // classifyFun l hl χ = x} := by
    intro x
    cases x with
    | none =>
      have hsub : Subsingleton {χ : SSGHomSet k K' l // classifyFun l hl χ = none} :=
        ⟨fun a b => by
          have ha : a.1.1 = 1 := (classifyFun_eq_none_iff l hl a.1).mp a.2
          have hb : b.1.1 = 1 := (classifyFun_eq_none_iff l hl b.1).mp b.2
          exact Subtype.ext (Subtype.ext (ha.trans hb.symm))⟩
      exact Finite.of_injective
        (fun _ : {χ : SSGHomSet k K' l // classifyFun l hl χ = none} => ())
        (fun a b _ => hsub.elim a b)
    | some L =>
      haveI : IsGalois k L.1 := L.2.1
      have hcard : Nat.card (Gal(K'/k) ⧸ (L.1).fixingSubgroup) = l := by
        rw [natCard_quotient_fixingSubgroup_eq_finrank (K := K') L.1, L.2.2]
      haveI : Finite (Gal(K'/k) ⧸ (L.1).fixingSubgroup) :=
        (Nat.card_pos_iff.mp (by rw [hcard]; exact hl.pos)).2
      haveI : Finite ((Gal(K'/k) ⧸ (L.1).fixingSubgroup) →* Multiplicative (ZMod l)) :=
        Finite.of_injective
          (fun f : (Gal(K'/k) ⧸ (L.1).fixingSubgroup) →* Multiplicative (ZMod l) =>
            (f : (Gal(K'/k) ⧸ (L.1).fixingSubgroup) → Multiplicative (ZMod l)))
          (fun f g hh => MonoidHom.ext (congrFun hh))
      exact Finite.of_injective (fibreToQuotient l hl L) (fibreToQuotient_injective l hl L)
  haveI : ∀ x : Option (SSGBase k K' l),
      Finite {χ : SSGHomSet k K' l // classifyFun l hl χ = x} := hfib
  exact (Equiv.sigmaFiberEquiv (classifyFun l hl)).finite_iff.mp inferInstance

end Work.SSGRoute
