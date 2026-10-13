import Mathlib
import Submission.Work.DSM2p.One
import Submission.Work.DSM2p.ConstructionPos
import Submission.Work.DSM2p.CSAlgPosAux

/-!
# The comparison `Λ₁[1/ϖ] → Λ[1/ϖ]` for the one-polynomial construction

Fix a monic polynomial `F : A[T]` of positive degree.  The one-polynomial construction of
`Submission/Work/DSM2p/One.lean` and the full construction of
`Submission/Work/DSM2p/ConstructionPos.lean` are related by the `A`-algebra map
`Λ₁ = A[T^{1/p^∞}] → Λ = A[T_{F'}^{1/p^∞} | F' ∈ 𝒫⁺]` which sends the root variable
`T = T^{1/p^0} ∈ Λ₁` to the root variable `T_F = X_{(F,0)} ∈ Λ`
(and consequently `T^{1/p^n} ↦ X_{(F,n)}`).

* `quotient_liftₐ_mk_apply` — the `AlgHom`-quotient `Ideal.Quotient.liftₐ` evaluated on a class.
* `ker_aeval_rootClosureIdeal_rename`, `rootClosureMapAlgHom`,
  `rootClosureMapAlgHom_mk_X` — functoriality of the root closure
  `rootClosure A p ι →ₐ[A] rootClosure A p ι'` induced by a map of index types `ι → ι'`;
  it sends `X_{(i,n)}` to `X_{(σ i, n)}`.
* `eq_invSelf_of_mul_eq_one` — uniqueness of the inverse of the inverted element in a localization
  away from a single element.
* `exists_ringHom_Lam1Loc_to_RootAlgLocPos` — the resulting map at the level of the
  localizations `Λ₁[1/ϖ] → Λ[1/ϖ]`, and the key property that it carries the `p`-integral
  closure `A'_F = pIntClosure p (Λ[F(T)/ϖ^m])` of the one-polynomial construction into
  `A' = pIntClosure p (Λ[F'(T_{F'})/ϖ^m])`.  This is what lets a theorem proved for the
  one-polynomial cover be transferred to the full cover (the "one `F` at a time" reduction of
  `area_M2pos1`).

The main theorem is used in `Submission/Work/DSM2p/DSM2pLF`- and `DSM2pCF`-style arguments: the
image of the one-polynomial integral closure under `φ` lies in `A' ⊆ B`, and `B` has the
frobenius/perfectoid properties needed for the flatness lemma.
-/

open scoped Classical

namespace Work.DSM2p

universe u

/-! ## `Ideal.Quotient.liftₐ` on classes -/

/-- The `AlgHom`-version of `Ideal.Quotient.lift` evaluated on a class. -/
theorem quotient_liftₐ_mk_apply {R : Type*} [CommRing R] {A' : Type*} [CommRing A']
    [Algebra R A'] {B : Type*} [CommRing B] [Algebra R B] (I : Ideal A') [I.IsTwoSided]
    (f : A' →ₐ[R] B) (hI : ∀ a ∈ I, f a = 0) (x : A') :
    Ideal.Quotient.liftₐ I f hI (Ideal.Quotient.mk I x) = f x := by
  rw [Ideal.Quotient.liftₐ_apply]
  exact Ideal.Quotient.lift_mk I (f : A' →+* B) hI

/-! ## Functoriality of the root-system ring -/

/-- The polynomial-ring map `X_{(i,n)} ↦ X_{(σ i, n)}` kills the defining relations
`X_{(i,n+1)}^p - X_{(i,n)}` of `rootClosure A p ι`. -/
theorem ker_aeval_rootClosureIdeal_rename (A : Type u) [CommRing A] (p : ℕ) {ι ι' : Type u}
    (σ : ι → ι') :
    ∀ a ∈ rootClosureIdeal A p ι,
      (MvPolynomial.aeval (fun q : ι × ℕ =>
        Ideal.Quotient.mk (rootClosureIdeal A p ι') (MvPolynomial.X (σ q.1, q.2)))) a = 0 := by
  have hspan : rootClosureIdeal A p ι ≤
      RingHom.ker (MvPolynomial.aeval (fun q : ι × ℕ =>
        Ideal.Quotient.mk (rootClosureIdeal A p ι') (MvPolynomial.X (σ q.1, q.2)))).toRingHom := by
    rw [rootClosureIdeal, Ideal.span_le]
    rintro _ ⟨q, rfl⟩
    show MvPolynomial.aeval (fun q : ι × ℕ =>
        Ideal.Quotient.mk (rootClosureIdeal A p ι') (MvPolynomial.X (σ q.1, q.2)))
      (MvPolynomial.X (q.1, q.2 + 1) ^ p - MvPolynomial.X q) = 0
    rw [map_sub, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_X, sub_eq_zero]
    exact rootClosure.X_pow A p ι' (σ q.1) q.2
  exact fun a ha => RingHom.mem_ker.mp (hspan ha)

/-- **Functoriality of the root-system ring.**  A map of index types `σ : ι → ι'` induces an
`A`-algebra homomorphism `A[X_i^{1/p^n}] → A[X_{i'}^{1/p^n}]` sending `X_{(i,n)}` to
`X_{(σ i, n)}`. -/
noncomputable def rootClosureMapAlgHom (A : Type u) [CommRing A] (p : ℕ) {ι ι' : Type u}
    (σ : ι → ι') : rootClosure A p ι →ₐ[A] rootClosure A p ι' :=
  Ideal.Quotient.liftₐ (rootClosureIdeal A p ι)
    (MvPolynomial.aeval (fun q : ι × ℕ =>
      Ideal.Quotient.mk (rootClosureIdeal A p ι') (MvPolynomial.X (σ q.1, q.2))))
    (ker_aeval_rootClosureIdeal_rename A p σ)

/-- The value of `rootClosureMapAlgHom` on the variables: `X_{(i,n)} ↦ X_{(σ i, n)}`. -/
theorem rootClosureMapAlgHom_mk_X (A : Type u) [CommRing A] (p : ℕ) {ι ι' : Type u}
    (σ : ι → ι') (i : ι) (n : ℕ) :
    rootClosureMapAlgHom A p σ
        (Ideal.Quotient.mk (rootClosureIdeal A p ι) (MvPolynomial.X (i, n)))
      = Ideal.Quotient.mk (rootClosureIdeal A p ι') (MvPolynomial.X (σ i, n)) := by
  rw [rootClosureMapAlgHom, quotient_liftₐ_mk_apply, MvPolynomial.aeval_X]

/-! ## Uniqueness of `invSelf` -/

/-- In a localization away from `y`, an element `q` with `algebraMap y * q = 1` is
`IsLocalization.Away.invSelf y`. -/
theorem eq_invSelf_of_mul_eq_one {P : Type*} [CommRing P] {Q : Type*} [CommRing Q]
    [Algebra P Q] (y : P) [IsLocalization.Away y Q] {q : Q} (h : (algebraMap P Q y) * q = 1) :
    q = IsLocalization.Away.invSelf y :=
  IsUnit.mul_left_cancel (IsLocalization.Away.algebraMap_isUnit y)
    (h.trans (IsLocalization.Away.mul_invSelf y).symm)

/-! ## The comparison map and its effect on the integral closures -/

theorem exists_ringHom_Lam1Loc_to_RootAlgLocPos (A : Type*) [CommRing A] (p : ℕ) (ϖ : A)
    (F : Polynomial A) (hF : F.Monic) (hFd : 0 < F.natDegree) :
    ∃ φ : Lam1Loc A p ϖ →+* RootAlgLocPos A p ϖ,
      (∀ a : A, φ (algebraMap A (Lam1Loc A p ϖ) a) = algebraMap A (RootAlgLocPos A p ϖ) a) ∧
      (CSIntegralClosureOne A p ϖ F ≤ (CSIntegralClosurePos A p ϖ).comap φ) := by
  classical
  -- the index of `F` in the full index set `𝒫⁺`
  let qF : MonicPolysPos A := ⟨F, hF, hFd⟩
  -- the functoriality map `Λ₁ → Λ` sending `T^{1/p^n}` to `X_{(F,n)}`
  let ψ : Lam1 A p →ₐ[A] RootAlgPos A p := rootClosureMapAlgHom A p (fun _ : PUnit => qF)
  -- and its composite with `Λ → Λ[1/ϖ]`
  let ψ₂ : Lam1 A p →+* RootAlgLocPos A p ϖ :=
    (algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ)).comp (ψ : Lam1 A p →+* RootAlgPos A p)
  have hψT : ψ (T1 A p 0) = rootVarPos A p qF := by
    change rootClosureMapAlgHom A p (fun _ : PUnit => qF)
      (Ideal.Quotient.mk (rootClosureIdeal A p PUnit) (MvPolynomial.X (PUnit.unit, 0))) =
      Ideal.Quotient.mk (rootClosureIdeal A p (MonicPolysPos A)) (MvPolynomial.X (qF, 0))
    rw [rootClosureMapAlgHom_mk_X]
  -- `ψ` carries the evaluation of `F` at `T` to the evaluation at the root variable `T_F`
  have hψeval : ψ (Polynomial.aeval (T1 A p 0) F) = Polynomial.aeval (rootVarPos A p qF) F := by
    rw [← Polynomial.aeval_algHom_apply ψ (T1 A p 0) F, hψT]
  have hψa : ∀ a : A, ψ (algebraMap A (Lam1 A p) a) = algebraMap A (RootAlgPos A p) a :=
    fun a => AlgHom.commutes ψ a
  have hunit : IsUnit (ψ₂ (algebraMap A (Lam1 A p) ϖ)) := by
    have h2 : ψ₂ (algebraMap A (Lam1 A p) ϖ) =
        algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ) (algebraMap A (RootAlgPos A p) ϖ) := by
      show algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ)
        (ψ (algebraMap A (Lam1 A p) ϖ)) = _
      rw [hψa]
    rw [h2]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap A (RootAlgPos A p) ϖ)
  -- the induced map of localizations `Λ₁[1/ϖ] → Λ[1/ϖ]`
  let φ : Lam1Loc A p ϖ →+* RootAlgLocPos A p ϖ :=
    IsLocalization.Away.lift (g := ψ₂) (algebraMap A (Lam1 A p) ϖ) hunit
  have hφ : ∀ y : Lam1 A p,
      φ (algebraMap (Lam1 A p) (Lam1Loc A p ϖ) y) =
        algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ) (ψ y) :=
    fun y => IsLocalization.Away.lift_eq (g := ψ₂) (algebraMap A (Lam1 A p) ϖ) hunit y
  have hφa : ∀ a : A, φ (algebraMap A (Lam1Loc A p ϖ) a) =
      algebraMap A (RootAlgLocPos A p ϖ) a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A (Lam1 A p) (Lam1Loc A p ϖ) a, hφ, hψa,
      IsScalarTower.algebraMap_apply A (RootAlgPos A p) (RootAlgLocPos A p ϖ) a]
  -- `φ` is compatible with `invSelf`, i.e. with the elements `1/ϖ^m`
  have hφinv : φ (IsLocalization.Away.invSelf (algebraMap A (Lam1 A p) ϖ)) =
      IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) := by
    refine eq_invSelf_of_mul_eq_one (algebraMap A (RootAlgPos A p) ϖ) ?_
    rw [← IsScalarTower.algebraMap_apply A (RootAlgPos A p) (RootAlgLocPos A p ϖ) ϖ, ← hφa ϖ,
      IsScalarTower.algebraMap_apply A (Lam1 A p) (Lam1Loc A p ϖ) ϖ, ← map_mul,
      IsLocalization.Away.mul_invSelf, map_one]
  -- the generators of `CSAlgOne` land in `A'`
  have hgen : CSAlgOne A p ϖ F ≤ (CSIntegralClosurePos A p ϖ).comap φ := by
    rw [CSAlgOne]
    refine Subring.closure_le.mpr ?_
    rintro y (hy | hy)
    · obtain ⟨y₀, rfl⟩ := hy
      change φ ((algebraMap (Lam1 A p) (Lam1Loc A p ϖ)) y₀) ∈ CSIntegralClosurePos A p ϖ
      rw [hφ]
      exact le_pIntClosure p (CSAlgPos A p ϖ)
        (Subring.subset_closure (Set.mem_union_left _ ⟨ψ y₀, rfl⟩))
    · obtain ⟨m, rfl⟩ := hy
      change φ (frac A p ϖ ((Polynomial.aeval (T1 A p 0)) F) m) ∈ CSIntegralClosurePos A p ϖ
      rw [frac, map_mul, map_pow, hφ, hψeval, hφinv]
      exact le_pIntClosure p (CSAlgPos A p ϖ)
        (Subring.subset_closure (Set.mem_union_right _ ⟨(qF, m), rfl⟩))
  refine ⟨φ, hφa, ?_⟩
  -- `comap φ A'` is `p`-integrally closed, so it contains the `p`-integral closure of `A_∞`
  refine pIntClosure_le hgen ?_
  intro x hx
  rw [Subring.mem_comap] at hx
  rw [map_pow] at hx
  exact CSIntegralClosurePos_isPIntegrallyClosed A p ϖ (φ x) hx

end Work.DSM2p
