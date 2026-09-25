import Mathlib
import Submission.Work.WingbergRoute.Defs
import Submission.Work.WingbergRoute.gsM_aut_exp_two
import Submission.Work.QuadraticFields.CertificateRealSummary
import Submission.Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card

/-!
# The Galois group of the certificate extension `M / F` is `(ℤ/2)⁶`

`Work.QuadraticFields.gsM = ℚ(√5, √13, √17, √29, √37, √41, √53)` is the multiquadratic field of the
totally real numerical certificate and `Work.QuadraticFields.gsF = ℚ(√(5·13·17·29·37·41·53))` is the
real quadratic base field singled out inside it
(`Submission/Work/QuadraticFields/CertificateRealSummary.lean`).

Because `M/ℚ` is Galois (`Work.QuadraticFields.multiQuad_isGalois`) *and* abelian of exponent `2`
(`Work.WingbergRoute.gsM_aut_exp_two`: every `ℚ`-automorphism of a multiquadratic field squares to
the identity), the group `Gal(M/F)` of `F`-algebra automorphisms of `M` is an elementary abelian
`2`-group.  Since `[M : F] = 2 ^ 6` (`Work.QuadraticFields.gs_finrank`), it is an `𝔽₂`-vector space
of dimension `6`, hence isomorphic to `(Fin 6 → ℤ/2)` multiplicatively:

```
Gal(M/F) ≃* (Fin 6 → Multiplicative (ℤ/2)).
```

Equivalently: `F` has exactly six independent unramified quadratic extensions inside `M`, and every
quadratic subextension of `M/F` is one of their composita.  This is the group-theoretic form of the
`d ≥ 6` input of the unramified (Wingberg) route: the six generators of `Gal(M/F)` exhibit six
independent quadratic characters of the absolute Galois group of `F`, i.e. six independent
unramified quadratic extensions of `F`.

## Main result

* `Work.WingbergRoute.gsM_aut_gsF_equiv_pi`.
-/

set_option linter.style.haveILetI false

namespace Work.WingbergRoute

noncomputable section

/-- `Multiplicative (ι → A) ≃* (ι → Multiplicative A)`: the multiplicative structure on an
`ι`-indexed product of additive groups is the pointwise one. -/
private def piMulEquiv (ι : Type*) :
    Multiplicative (ι → ZMod 2) ≃* (ι → Multiplicative (ZMod 2)) where
  toFun x i := Multiplicative.ofAdd (Multiplicative.toAdd x i)
  invFun y := Multiplicative.ofAdd (fun i => Multiplicative.toAdd (y i))
  left_inv x := by ext i; rfl
  right_inv y := by ext i; rfl
  map_mul' x y := by ext i; rfl

/-- Every `F`-algebra automorphism of `M` has order dividing `2`: it restricts to a `ℚ`-algebra
automorphism of the multiquadratic field `M`, and such automorphisms square to the identity
(`Work.WingbergRoute.gsM_aut_exp_two`). -/
private theorem gsM_aut_gsF_sq_eq_one
    (σ : Work.QuadraticFields.gsM ≃ₐ[↥Work.QuadraticFields.gsF] Work.QuadraticFields.gsM) :
    σ ^ 2 = 1 := by
  have h : (AlgEquiv.restrictScalarsHom ℚ σ) * (AlgEquiv.restrictScalarsHom ℚ σ) = 1 :=
    gsM_aut_exp_two (AlgEquiv.restrictScalarsHom ℚ σ)
  have h2 : σ * σ = 1 := by
    apply AlgEquiv.restrictScalarsHom_injective ℚ
    show (AlgEquiv.restrictScalarsHom ℚ) (σ * σ) = (AlgEquiv.restrictScalarsHom ℚ) 1
    rw [map_mul, h, map_one]
  rw [pow_two]
  exact h2

/-- **The Galois group of the certificate extension is elementary abelian of rank `6`.**

`Gal(M/F)` is an elementary abelian `2`-group of order `[M : F] = 64 = 2 ^ 6`: every element is an
involution, and the order is the degree because `M/ℚ` is Galois.  A finite commutative group of
exponent `2` and order `2 ^ k` is an `𝔽₂`-vector space of dimension `k`
(`Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card`),
and `𝔽₂^k` is `(Fin k → ℤ/2)` multiplicatively. -/
theorem gsM_aut_gsF_equiv_pi :
    Nonempty ((Work.QuadraticFields.gsM ≃ₐ[↥Work.QuadraticFields.gsF] Work.QuadraticFields.gsM) ≃*
      (Fin 6 → Multiplicative (ZMod 2))) := by
  -- `M/ℚ` is Galois, so `M/F` is Galois (an intermediate extension of a Galois extension is).
  haveI : IsGalois ℚ Work.QuadraticFields.gsM :=
    Work.QuadraticFields.multiQuad_isGalois Work.QuadraticFields.gsPrimesQ
  -- every element of `Gal(M/F)` is an involution ...
  have hexp : ∀ σ : Work.QuadraticFields.gsM ≃ₐ[↥Work.QuadraticFields.gsF]
      Work.QuadraticFields.gsM, σ ^ 2 = 1 := gsM_aut_gsF_sq_eq_one
  -- ... hence `Gal(M/F)` is commutative ...
  have hcomm : ∀ a b : Work.QuadraticFields.gsM ≃ₐ[↥Work.QuadraticFields.gsF]
      Work.QuadraticFields.gsM, a * b = b * a := by
    intro a b
    have hb : b * b = 1 := by rw [← pow_two]; exact hexp b
    have ha : a * a = 1 := by rw [← pow_two]; exact hexp a
    have h1 : a * b * (a * b) = 1 := by rw [← pow_two]; exact hexp (a * b)
    have h2 : a * b * (b * a) = 1 := by
      calc a * b * (b * a) = a * (b * b) * a := by simp only [mul_assoc]
        _ = a * 1 * a := by rw [hb]
        _ = 1 := by rw [mul_one, ha]
    exact mul_left_cancel (h1.trans h2.symm)
  haveI : IsMulCommutative
      (Work.QuadraticFields.gsM ≃ₐ[↥Work.QuadraticFields.gsF] Work.QuadraticFields.gsM) :=
    IsMulCommutative.of_comm hcomm
  -- ... and its order is `[M : F] = 64 = 2 ^ 6` (Galois correspondence).
  have hcard : Nat.card (Work.QuadraticFields.gsM ≃ₐ[↥Work.QuadraticFields.gsF]
      Work.QuadraticFields.gsM) = 2 ^ 6 := by
    rw [IsGalois.card_aut_eq_finrank (↥Work.QuadraticFields.gsF) Work.QuadraticFields.gsM,
      Work.QuadraticFields.gs_finrank]
    norm_num
  -- A finite commutative group of exponent two and order `2 ^ k` is `(ℤ/2) ^ k`.
  obtain ⟨e⟩ :=
    Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card
      hexp hcard
  exact ⟨e.trans (piMulEquiv (Fin 6))⟩

end

end Work.WingbergRoute
