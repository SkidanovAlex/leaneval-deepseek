import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Pointwise

set_option linter.unusedSectionVars false

namespace Work.CurveBasics.Order

/-- If a submodule `N` and the quotient `M ⧸ N` are of finite length, then so is `M`:
`IsFiniteLength` is closed under extensions. -/
lemma isFiniteLength_of_submodule_quotient {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N : Submodule R M} (hN : IsFiniteLength R N) (hQ : IsFiniteLength R (M ⧸ N)) :
    IsFiniteLength R M := by
  obtain ⟨hNn, hNa⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hN
  obtain ⟨hQn, hQa⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hQ
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨(isNoetherian_iff_submodule_quotient N).mpr ⟨hNn, hQn⟩,
    (isArtinian_iff_submodule_quotient N).mpr ⟨hNa, hQa⟩⟩

/-- The "third isomorphism theorem" form of the extension property: if `S ≤ T` are submodules of
`M`, and both `T ⧸ S` (viewed as a submodule of `M ⧸ S`) and `M ⧸ T` are of finite length, then so
is `M ⧸ S`. -/
lemma isFiniteLength_quotient_of_map_le {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {S T : Submodule R M} (hST : S ≤ T) (hS : IsFiniteLength R (T.map S.mkQ))
    (hT : IsFiniteLength R (M ⧸ T)) : IsFiniteLength R (M ⧸ S) := by
  have h1 : IsFiniteLength R ((M ⧸ S) ⧸ Submodule.map S.mkQ T) :=
    (Submodule.quotientQuotientEquivQuotient S T hST).symm.isFiniteLength hT
  obtain ⟨hNn, hNa⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hS
  obtain ⟨hQn, hQa⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h1
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨(isNoetherian_iff_submodule_quotient (T.map S.mkQ)).mpr ⟨hNn, hQn⟩,
    (isArtinian_iff_submodule_quotient (T.map S.mkQ)).mpr ⟨hNa, hQa⟩⟩

variable {A : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]

/-- One step of the induction: if `B ⧸ d • ⊤` has finite length and `q` is irreducible (so that
`(q)` is maximal), then `B ⧸ (q * d) • ⊤` has finite length. -/
lemma isFiniteLength_quotSMulTop_mul_of_irreducible
    (h : ∀ p : Ideal A, p.IsMaximal → IsFiniteLength A (B ⧸ (p • (⊤ : Submodule A B))))
    {d q : A} (hq : Irreducible q)
    (ih : IsFiniteLength A (B ⧸ (d • (⊤ : Submodule A B)))) :
    IsFiniteLength A (B ⧸ ((q * d) • (⊤ : Submodule A B))) := by
  set S : Submodule A B := (q * d) • (⊤ : Submodule A B) with hSdef
  set T : Submodule A B := d • (⊤ : Submodule A B) with hTdef
  -- `S ≤ T` because `q * d ∈ (d)`
  have hST : S ≤ T := by
    rw [hSdef, hTdef]
    have hle : Ideal.span ({q * d} : Set A) ≤ Ideal.span ({d} : Set A) := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact Ideal.mul_mem_left _ q (Ideal.mem_span_singleton_self d)
    simpa only [Submodule.ideal_span_singleton_smul] using
      (Submodule.smul_mono_left hle (M := B) (N := (⊤ : Submodule A B)))
  -- `T ⧸ S` is a quotient of `B ⧸ (q)•⊤` via multiplication by `d`
  have hS : IsFiniteLength A (T.map S.mkQ) := by
    let m : B →ₗ[A] T.map S.mkQ :=
      (S.mkQ.comp (LinearMap.lsmul A B d)).codRestrict _ (fun b => by
        apply Submodule.mem_map.mpr
        exact ⟨d • b, Submodule.smul_mem_pointwise_smul b d (⊤ : Submodule A B) trivial, rfl⟩)
    have hm_surj : Function.Surjective m := by
      intro y
      obtain ⟨t, ht, ht2⟩ := Submodule.mem_map.mp y.2
      obtain ⟨b, hb, rfl⟩ :=
        (Submodule.mem_smul_pointwise_iff_exists t d (⊤ : Submodule A B)).mp ht
      refine ⟨b, ?_⟩
      apply Subtype.ext
      simpa [m, LinearMap.lsmul_apply] using ht2
    have hker : Ideal.span {q} • (⊤ : Submodule A B) ≤ m.ker := by
      rw [Submodule.smul_le]
      intro r hr n hn
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hr
      rw [LinearMap.mem_ker, ← ha]
      rw [Subtype.ext_iff]
      simp only [m, LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearMap.lsmul_apply,
        Submodule.mkQ_apply, Submodule.coe_zero]
      rw [Submodule.Quotient.mk_eq_zero]
      rw [hSdef]
      have hEq : d • ((a • q) • n) = (q * d) • (a • n) := by
        rw [smul_smul, smul_smul, smul_eq_mul]; ring_nf
      rw [hEq]
      exact Submodule.smul_mem_pointwise_smul (a • n) (q * d) (⊤ : Submodule A B) trivial
    have h0 : IsFiniteLength A (B ⧸ (Ideal.span {q} • (⊤ : Submodule A B))) :=
      h _ (PrincipalIdealRing.isMaximal_of_irreducible hq)
    let F : (B ⧸ (Ideal.span {q} • (⊤ : Submodule A B))) →ₗ[A] T.map S.mkQ :=
      (Ideal.span {q} • (⊤ : Submodule A B)).liftQ m hker
    have hF : Function.Surjective F := fun y => by
      obtain ⟨b, hb⟩ := hm_surj y
      exact ⟨Submodule.Quotient.mk b, by rw [Submodule.liftQ_apply]; exact hb⟩
    exact IsFiniteLength.of_surjective h0 hF
  exact isFiniteLength_quotient_of_map_le hST hS ih

/-- Inductively, `B ⧸ (m.prod) • ⊤` has finite length whenever all elements of the multiset `m`
are irreducible. -/
lemma isFiniteLength_quotSMulTop_prod_multiset
    (h : ∀ p : Ideal A, p.IsMaximal → IsFiniteLength A (B ⧸ (p • (⊤ : Submodule A B))))
    (m : Multiset A) (hm : ∀ q ∈ m, Irreducible q) :
    IsFiniteLength A (B ⧸ (m.prod • (⊤ : Submodule A B))) := by
  induction m using Multiset.induction_on with
  | empty =>
      rw [Multiset.prod_zero, one_smul]
      exact IsFiniteLength.of_subsingleton
  | cons q m ih =>
      rw [Multiset.prod_cons]
      exact isFiniteLength_quotSMulTop_mul_of_irreducible h (hm q (Multiset.mem_cons_self q m))
        (ih (fun x hx => hm x (Multiset.mem_cons_of_mem hx)))

theorem isFiniteLength_quotient_of_ne_zero
    {A : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    (h : ∀ p : Ideal A, p.IsMaximal → IsFiniteLength A (B ⧸ (p • (⊤ : Submodule A B))))
    (a : A) (ha : a ≠ 0) :
    IsFiniteLength A (B ⧸ (Ideal.span {a} • (⊤ : Submodule A B))) := by
  obtain ⟨hirr, hassoc⟩ := PrincipalIdealRing.factors_spec a ha
  have hspan : (Ideal.span ({a} : Set A)) =
      Ideal.span ({(PrincipalIdealRing.factors a).prod} : Set A) :=
    (Ideal.span_singleton_eq_span_singleton).mpr hassoc.symm
  rw [hspan, Submodule.ideal_span_singleton_smul]
  exact isFiniteLength_quotSMulTop_prod_multiset h (PrincipalIdealRing.factors a) hirr

end Work.CurveBasics.Order
