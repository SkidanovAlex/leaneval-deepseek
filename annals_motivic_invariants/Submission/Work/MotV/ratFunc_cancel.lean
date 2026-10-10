import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV.isAlgebraic_mem_base
import Submission.Work.MotV.exists_eq_algebraMap_fin_zero
import Submission.Work.MotV.trdeg_fractionRing_mvPolynomial

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Node CAN: cancellation of rational function fields

`Work.MotV.ratFunc_cancel`: if `F₁` is constants-only over `𝕜` and
`F₁(y₁,…,y_m) ≅ F₂(y₁,…,y_m)` as `𝕜`-algebras (as fraction fields of polynomial algebras), then
`F₁ ≅ F₂` over `𝕜`.

## Proof

`constants_image` is the key input: every `𝕜`-algebra map
`F₁ → FractionRing (MvPolynomial (Fin m) M)` into a rational function field over a field `M` has
image in `M`.  It is proved by induction on `m`, using `stepAlgEquiv` to write
`M(x₁,…,x_{n+1})` as `RatFunc (M(x₁,…,x_n))` (a rational function field over the *field*
`FractionRing (MvPolynomial (Fin n) M)`, to which the hypothesis `ConstantsOnly 𝕜 F₁` applies
directly) and then the induction hypothesis.

For the theorem, put `A_i = FractionRing (MvPolynomial (Fin m) F_i)` and `φ = e ∘ algebraMap F₁ A₁`.
By `constants_image`, `φ` factors through a `𝕜`-algebra map `ψ : F₁ →ₐ[𝕜] F₂`; we show `ψ` is
surjective.  Installing `Algebra F₁ F₂` along `ψ` (the induced `F₁`-algebra structure on
`A₂ = FractionRing (MvPolynomial (Fin m) F₂)` is then the canonical one), the isomorphism `e`
becomes an isomorphism of `F₁`-algebras.  Transcendence degrees give
`trdeg F₁ F₂ + trdeg F₂ A₂ = trdeg F₁ A₂ = trdeg F₁ A₁ = m`, so `trdeg F₁ F₂ = 0`, i.e. `F₂` is
algebraic over `F₁`.  Finally, if `u ∈ F₂`, then `e⁻¹ (algebraMap F₂ A₂ u) ∈ A₁` is algebraic over
`F₁`, hence a constant by `isAlgebraic_mem_base`, which forces `u = ψ c`.
-/

namespace Work.MotV

open Polynomial

set_option autoImplicit false

/-- **`Frac(D[X]) ≅ RatFunc (Frac D)`**: the fraction field of the polynomial ring over a domain is
the rational function field over its fraction field, and the equivalence commutes with the
constants.

Route: `(Frac D)[X]` is the localization of `D[X]` at the (non-zero-divisor) image of the
non-zero-divisors of `D` (`Polynomial.isLocalization`); localizing twice
(`IsLocalization.localizationLocalization_isLocalization`) exhibits `RatFunc (Frac D)` as a
localization of `D[X]` at a submonoid of non-zero-divisors, which `IsLocalization.of_le` upgrades to
the fraction field structure; finally `FractionRing.algEquiv` gives the equivalence and the
compatibility is an `IsScalarTower` computation. -/
theorem fractionRing_polynomial_ratFunc (𝕜 D : Type) [Field 𝕜] [CommRing D] [IsDomain D]
    [Algebra 𝕜 D] :
    ∃ Φ : FractionRing (Polynomial D) ≃ₐ[𝕜] RatFunc (FractionRing D),
      ∀ c : D, Φ (algebraMap D (FractionRing (Polynomial D)) c)
        = RatFunc.C (algebraMap D (FractionRing D) c) := by
  letI : Algebra (Polynomial D) (Polynomial (FractionRing D)) :=
    Polynomial.algebra D (FractionRing D)
  haveI hloc : IsLocalization ((nonZeroDivisors D).map Polynomial.C)
      (Polynomial (FractionRing D)) :=
    Polynomial.isLocalization (nonZeroDivisors D) (FractionRing D)
  have hMle : (nonZeroDivisors D).map Polynomial.C ≤ nonZeroDivisors (Polynomial D) := by
    rintro x ⟨d, hd, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact fun h0 => nonZeroDivisors.ne_zero hd (Polynomial.C_injective (by simpa using h0))
  have hinjPoly : Function.Injective
      (algebraMap (Polynomial D) (Polynomial (FractionRing D))) :=
    IsLocalization.injective (Polynomial (FractionRing D)) hMle
  haveI hfrac : IsFractionRing (Polynomial (FractionRing D)) (RatFunc (FractionRing D)) :=
    inferInstance
  haveI hcomp : IsLocalization
      (IsLocalization.localizationLocalizationSubmodule ((nonZeroDivisors D).map Polynomial.C)
        (nonZeroDivisors (Polynomial (FractionRing D)))) (RatFunc (FractionRing D)) :=
    IsLocalization.localization_localization_isLocalization
      ((nonZeroDivisors D).map Polynomial.C)
      (nonZeroDivisors (Polynomial (FractionRing D))) (RatFunc (FractionRing D))
  have hM' : IsLocalization.localizationLocalizationSubmodule ((nonZeroDivisors D).map Polynomial.C)
      (nonZeroDivisors (Polynomial (FractionRing D))) = nonZeroDivisors (Polynomial D) := by
    ext x
    rw [IsLocalization.mem_localizationLocalizationSubmodule]
    constructor
    · rintro ⟨y, z, h⟩
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro hx0
      have hz0 : algebraMap (Polynomial D) (Polynomial (FractionRing D)) (z : Polynomial D) ≠ 0 := by
        obtain ⟨d, hd, hCd⟩ := Submonoid.mem_map.mp z.2
        rw [← hCd, Polynomial.C_eq_algebraMap d,
          ← IsScalarTower.algebraMap_apply D (Polynomial D) (Polynomial (FractionRing D)) d,
          Polynomial.algebraMap_apply]
        exact fun h0 => nonZeroDivisors.ne_zero hd
          ((IsFractionRing.injective D (FractionRing D))
            (Polynomial.C_injective (by simpa using h0)))
      rw [hx0, map_zero] at h
      exact hz0 ((mul_eq_zero.mp h.symm).resolve_left (nonZeroDivisors.ne_zero y.2))
    · intro hx
      rw [mem_nonZeroDivisors_iff_ne_zero] at hx
      refine ⟨⟨algebraMap (Polynomial D) (Polynomial (FractionRing D)) x, ?_⟩,
        ⟨1, Submonoid.one_mem _⟩, ?_⟩
      · rw [mem_nonZeroDivisors_iff_ne_zero]
        exact fun h0 => hx (hinjPoly (by rw [h0, map_zero]))
      · simp
  haveI hfin : IsFractionRing (Polynomial D) (RatFunc (FractionRing D)) :=
    IsLocalization.of_le
      (IsLocalization.localizationLocalizationSubmodule ((nonZeroDivisors D).map Polynomial.C)
        (nonZeroDivisors (Polynomial (FractionRing D))))
      (nonZeroDivisors (Polynomial D)) (le_of_eq hM') fun r hr => by
        rw [mem_nonZeroDivisors_iff_ne_zero] at hr
        refine isUnit_iff_ne_zero.mpr fun h0 => hr ?_
        have h2 : (algebraMap (FractionRing D)[X] (RatFunc (FractionRing D)))
            (algebraMap (Polynomial D) (Polynomial (FractionRing D)) r) = 0 := by
          rw [← IsScalarTower.algebraMap_apply (Polynomial D) (Polynomial (FractionRing D))
            (RatFunc (FractionRing D)) r]
          exact h0
        have h4 : algebraMap (Polynomial D) (Polynomial (FractionRing D)) r = 0 :=
          RatFunc.algebraMap_injective (FractionRing D) (by rw [h2, map_zero])
        exact hinjPoly (by rw [h4, map_zero])
  refine ⟨(FractionRing.algEquiv (Polynomial D) (RatFunc (FractionRing D))).restrictScalars 𝕜, ?_⟩
  intro c
  change (FractionRing.algEquiv (Polynomial D) (RatFunc (FractionRing D)))
      (algebraMap D (FractionRing (Polynomial D)) c)
    = RatFunc.C (algebraMap D (FractionRing D) c)
  rw [    IsScalarTower.algebraMap_apply D (Polynomial D) (FractionRing (Polynomial D)) c,
    AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply D (Polynomial D) (RatFunc (FractionRing D)) c,
    ← RatFunc.algebraMap_eq_C,
    ← IsScalarTower.algebraMap_apply D (FractionRing D) (RatFunc (FractionRing D)) c]

/-- **The one-variable decomposition of a rational function field**, in `MvPolynomial` form:
`M(x₁,…,x_{n+1}) ≅ M(x₁,…,x_n)(x_{n+1})` over `𝕜`, compatible with the constants `M`.  This is
`fractionRing_polynomial_ratFunc` transported along `MvPolynomial.finSuccEquiv`. -/
theorem stepAlgEquiv (𝕜 M : Type) [Field 𝕜] [Field M] [Algebra 𝕜 M] (n : ℕ) :
    ∃ Φ : FractionRing (MvPolynomial (Fin (n+1)) M) ≃ₐ[𝕜]
        RatFunc (FractionRing (MvPolynomial (Fin n) M)),
      ∀ c : M, Φ (algebraMap M (FractionRing (MvPolynomial (Fin (n+1)) M)) c)
        = RatFunc.C (algebraMap M (FractionRing (MvPolynomial (Fin n) M)) c) := by
  obtain ⟨Φ, hΦ⟩ := fractionRing_polynomial_ratFunc 𝕜 (MvPolynomial (Fin n) M)
  refine ⟨((IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.finSuccEquiv M n)).restrictScalars 𝕜).trans
    Φ, ?_⟩
  intro c
  change Φ (IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.finSuccEquiv M n)
      (algebraMap M (FractionRing (MvPolynomial (Fin (n+1)) M)) c)) = _
  rw [AlgEquiv.commutes,
    IsScalarTower.algebraMap_apply M (Polynomial (MvPolynomial (Fin n) M))
      (FractionRing (Polynomial (MvPolynomial (Fin n) M))) c,
    IsScalarTower.algebraMap_apply M (MvPolynomial (Fin n) M)
      (Polynomial (MvPolynomial (Fin n) M)) c,
    ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) M)
      (Polynomial (MvPolynomial (Fin n) M))
      (FractionRing (Polynomial (MvPolynomial (Fin n) M)))
      (algebraMap M (MvPolynomial (Fin n) M) c),
    hΦ (algebraMap M (MvPolynomial (Fin n) M) c),
    IsScalarTower.algebraMap_apply M (MvPolynomial (Fin n) M)
      (FractionRing (MvPolynomial (Fin n) M)) c]


/-- **(P1)**: every `𝕜`-algebra map `F₁ → FractionRing (MvPolynomial (Fin m) M)` with `F₁`
constants-only has image in the base field `M`. -/
theorem constants_image {𝕜 F₁ : Type} [Field 𝕜] [Field F₁] [Algebra 𝕜 F₁]
    (h₁ : ConstantsOnly 𝕜 F₁) :
    ∀ (m : ℕ) (M : Type) [Field M] [Algebra 𝕜 M]
      (φ : F₁ →ₐ[𝕜] FractionRing (MvPolynomial (Fin m) M)) (x : F₁),
      ∃ c : M, φ x = algebraMap M (FractionRing (MvPolynomial (Fin m) M)) c := by
  intro m
  induction m with
  | zero =>
      intro M _ _ φ x
      exact exists_eq_algebraMap_fin_zero 𝕜 M (φ x)
  | succ n ih =>
      intro M hM hMalg φ x
      obtain ⟨Φ, hΦ⟩ := stepAlgEquiv 𝕜 M n
      let φ' : F₁ →ₐ[𝕜] RatFunc (FractionRing (MvPolynomial (Fin n) M)) :=
        Φ.toAlgHom.comp φ
      have hconst : ∀ y : F₁, ∃ b : FractionRing (MvPolynomial (Fin n) M),
          φ' y = RatFunc.C b := by
        intro y
        obtain ⟨b, hb⟩ := h₁ (FractionRing (MvPolynomial (Fin n) M)) φ' y
        exact ⟨b, by rw [← hb, RatFunc.algebraMap_eq_C]⟩
      choose ψ₀ hψ₀ using hconst
      have hinj : Function.Injective
          (RatFunc.C (K := FractionRing (MvPolynomial (Fin n) M))) :=
        RatFunc.C_injective (K := FractionRing (MvPolynomial (Fin n) M))
      let ψ : F₁ →ₐ[𝕜] FractionRing (MvPolynomial (Fin n) M) :=
        { toFun := ψ₀
          map_one' := hinj (by rw [← hψ₀ 1]; simp)
          map_mul' := fun a b => hinj (by rw [← hψ₀ (a * b)]; simp only [map_mul, hψ₀ a, hψ₀ b])
          map_zero' := hinj (by rw [← hψ₀ 0]; simp)
          map_add' := fun a b => hinj (by rw [← hψ₀ (a + b)]; simp only [map_add, hψ₀ a, hψ₀ b])
          commutes' := fun r => hinj (by
            rw [← hψ₀ (algebraMap 𝕜 F₁ r), AlgHom.commutes,
              IsScalarTower.algebraMap_apply 𝕜 (FractionRing (MvPolynomial (Fin n) M))
                (RatFunc (FractionRing (MvPolynomial (Fin n) M))) r, RatFunc.algebraMap_eq_C]) }
      obtain ⟨c, hc⟩ := ih M ψ x
      refine ⟨c, ?_⟩
      have hφ' : φ' x = RatFunc.C
          (algebraMap M (FractionRing (MvPolynomial (Fin n) M)) c) := by
        rw [hψ₀ x]
        exact congrArg RatFunc.C hc
      rw [show φ x = Φ.symm (φ' x) from (AlgEquiv.symm_apply_apply Φ (φ x)).symm, hφ',
        ← hΦ c, AlgEquiv.symm_apply_apply]

/-- Node CAN, main step: the `𝕜`-algebra isomorphism `e` between the rational function fields
forces `F₁ ≃ₐ[𝕜] F₂`. -/
theorem ratFunc_cancel_aux {𝕜 F₁ F₂ : Type} [Field 𝕜] [Field F₁] [Field F₂]
    [Algebra 𝕜 F₁] [Algebra 𝕜 F₂] (h₁ : ConstantsOnly 𝕜 F₁) (m : ℕ)
    (e : FractionRing (MvPolynomial (Fin m) F₁) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin m) F₂)) :
    Nonempty (F₁ ≃ₐ[𝕜] F₂) := by
  have hφ : ∀ x : F₁, ∃ c : F₂,
      e (algebraMap F₁ (FractionRing (MvPolynomial (Fin m) F₁)) x)
        = algebraMap F₂ (FractionRing (MvPolynomial (Fin m) F₂)) c := by
    intro x
    exact constants_image h₁ m F₂
      ((e.toAlgHom).comp
        (IsScalarTower.toAlgHom 𝕜 F₁ (FractionRing (MvPolynomial (Fin m) F₁)))) x
  choose ψ₀ hψ₀ using hφ
  have hinj₂ : Function.Injective
      (algebraMap F₂ (FractionRing (MvPolynomial (Fin m) F₂))) :=
    FaithfulSMul.algebraMap_injective F₂ _
  let ψ : F₁ →ₐ[𝕜] F₂ :=
    { toFun := ψ₀
      map_one' := hinj₂ (by rw [← hψ₀ 1]; simp)
      map_mul' := fun a b => hinj₂ (by rw [← hψ₀ (a * b)]; simp only [map_mul, hψ₀ a, hψ₀ b])
      map_zero' := hinj₂ (by rw [← hψ₀ 0]; simp)
      map_add' := fun a b => hinj₂ (by rw [← hψ₀ (a + b)]; simp only [map_add, hψ₀ a, hψ₀ b])
      commutes' := fun r => hinj₂ (by
        rw [← hψ₀ (algebraMap 𝕜 F₁ r),
          ← IsScalarTower.algebraMap_apply 𝕜 F₁
            (FractionRing (MvPolynomial (Fin m) F₁)) r,
          e.commutes r, IsScalarTower.algebraMap_apply 𝕜 F₂
            (FractionRing (MvPolynomial (Fin m) F₂)) r]) }
  letI : Algebra F₁ F₂ := ψ.toRingHom.toAlgebra
  haveI : FaithfulSMul F₁ F₂ :=
    (faithfulSMul_iff_algebraMap_injective F₁ F₂).mpr ψ.injective
  have heF₁ : ∀ c : F₁,
      e (algebraMap F₁ (FractionRing (MvPolynomial (Fin m) F₁)) c)
        = algebraMap F₁ (FractionRing (MvPolynomial (Fin m) F₂)) c := by
    intro c
    rw [IsScalarTower.algebraMap_apply F₁ F₂ (FractionRing (MvPolynomial (Fin m) F₂)) c]
    exact hψ₀ c
  let eF₁ : FractionRing (MvPolynomial (Fin m) F₁) ≃ₐ[F₁]
      FractionRing (MvPolynomial (Fin m) F₂) :=
    AlgEquiv.ofBijective
      { e.toRingEquiv.toRingHom with commutes' := heF₁ }
      ⟨e.injective, e.surjective⟩
  have ht1 : Algebra.trdeg F₁ (FractionRing (MvPolynomial (Fin m) F₁))
      = Cardinal.mk (Fin m) := trdeg_fractionRing_mvPolynomial F₁ m
  have ht2 : Algebra.trdeg F₁ (FractionRing (MvPolynomial (Fin m) F₂))
      = Cardinal.mk (Fin m) := by
    rw [← ht1, AlgEquiv.trdeg_eq eF₁]
  have ht3 : Algebra.trdeg F₂ (FractionRing (MvPolynomial (Fin m) F₂))
      = Cardinal.mk (Fin m) := trdeg_fractionRing_mvPolynomial F₂ m
  have htower : Algebra.trdeg F₁ F₂
      + Algebra.trdeg F₂ (FractionRing (MvPolynomial (Fin m) F₂))
      = Algebra.trdeg F₁ (FractionRing (MvPolynomial (Fin m) F₂)) :=
    trdeg_add_eq F₁ F₂
  have hle : Algebra.trdeg F₁ F₂ ≤ Cardinal.mk (Fin m) := by
    rw [← ht2, ← htower]
    exact le_add_right le_rfl
  have hlt : Algebra.trdeg F₁ F₂ < Cardinal.aleph0 := by
    refine lt_of_le_of_lt hle ?_
    rw [Cardinal.mk_fin]
    exact Cardinal.natCast_lt_aleph0 (n := m)
  have hnat : (Algebra.trdeg F₁ F₂).toNat = 0 := by
    have h1 : (Algebra.trdeg F₁ F₂).toNat + m = m := by
      have h2 : Algebra.trdeg F₁ F₂
          + (Cardinal.mk (Fin m)) = Cardinal.mk (Fin m) := by
        rw [← ht3, htower, ht2, ht3]
      have h3 := congrArg Cardinal.toNat h2
      rw [Cardinal.mk_fin] at h3
      rw [Cardinal.toNat_add hlt (Cardinal.natCast_lt_aleph0 (n := m)),
        Cardinal.toNat_natCast] at h3
      exact h3
    omega
  have hzero : Algebra.trdeg F₁ F₂ = 0 := by
    rcases (Cardinal.toNat_eq_zero.mp hnat) with h | h
    · exact h
    · exact absurd h (not_le.mpr hlt)
  have halg : Algebra.IsAlgebraic F₁ F₂ := (trdeg_eq_zero_iff).mp hzero
  have hsurj : Function.Surjective ψ := by
    intro u
    have hu : IsAlgebraic F₁ (algebraMap F₂ (FractionRing (MvPolynomial (Fin m) F₂)) u) :=
      IsAlgebraic.algebraMap (S := F₂) (halg.isAlgebraic u)
    have hz : IsAlgebraic F₁
        (eF₁.symm (algebraMap F₂ (FractionRing (MvPolynomial (Fin m) F₂)) u)) := by
      obtain ⟨p, hp, hp0⟩ := hu
      refine ⟨p, hp, ?_⟩
      have key : aeval (eF₁ (eF₁.symm (algebraMap F₂ (FractionRing (MvPolynomial (Fin m) F₂)) u))) p
          = eF₁ (aeval (eF₁.symm (algebraMap F₂ (FractionRing (MvPolynomial (Fin m) F₂)) u)) p) :=
        congrArg (fun f : Polynomial F₁ →ₐ[F₁] FractionRing (MvPolynomial (Fin m) F₂) => f p)
          (Polynomial.aeval_algEquiv eF₁
            (eF₁.symm (algebraMap F₂ (FractionRing (MvPolynomial (Fin m) F₂)) u)))
      rw [eF₁.apply_symm_apply] at key
      exact eF₁.injective (by rw [← key, hp0, map_zero])
    obtain ⟨c, hc⟩ := isAlgebraic_mem_base (F := F₁) m _ hz
    refine ⟨c, ?_⟩
    apply hinj₂
    show algebraMap F₂ (FractionRing (MvPolynomial (Fin m) F₂)) (ψ₀ c)
      = algebraMap F₂ (FractionRing (MvPolynomial (Fin m) F₂)) u
    rw [← hψ₀ c, ← hc]
    change eF₁ (eF₁.symm (algebraMap F₂ (FractionRing (MvPolynomial (Fin m) F₂)) u))
      = algebraMap F₂ (FractionRing (MvPolynomial (Fin m) F₂)) u
    rw [eF₁.apply_symm_apply]
  exact ⟨AlgEquiv.ofBijective ψ ⟨ψ.injective, hsurj⟩⟩

/-- Node CAN: cancellation of rational function fields.  If `F₁` is constants-only over `𝕜` and
`F₁(y₁,…,y_m)` is `𝕜`-isomorphic to `F₂(y₁,…,y_m)` (as fraction fields of polynomial algebras over
`F₁` resp. `F₂`), then `F₁ ≅ F₂` over `𝕜`. -/
theorem ratFunc_cancel {𝕜 F₁ F₂ : Type} [Field 𝕜] [Field F₁] [Field F₂] [Algebra 𝕜 F₁]
    [Algebra 𝕜 F₂] (h₁ : ConstantsOnly 𝕜 F₁) (m : ℕ)
    (e : FractionRing (MvPolynomial (Fin m) F₁) ≃ₐ[𝕜] FractionRing (MvPolynomial (Fin m) F₂)) :
    Nonempty (F₁ ≃ₐ[𝕜] F₂) :=
  ratFunc_cancel_aux h₁ m e

end Work.MotV
