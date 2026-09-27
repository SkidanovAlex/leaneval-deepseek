import Mathlib
import Submission.Work.KT.Defs

/-!
# `Work.KT.Fund.Laurent` — Laurent polynomials on `X × S¹`

The algebra of Laurent polynomials `C(X, ℂ)[T; T⁻¹]` maps into `C(X × S¹, ℂ)` by sending the
coefficients to their pullbacks along the projection and `T` to the tautological unit `z`
(the coordinate of the unit circle).  This is the ring in which the Laurent approximation of
clutching functions over `X × S¹` is phrased (`Work.KT.Fund.laurent_approx`).
-/

namespace Work.KT

noncomputable section

open Matrix

variable (X : Type) [TopologicalSpace X]

lemma z_ne_zero (p : X × Sph ℂ) : ((p.2 : ℂ)) ≠ 0 := by
  have h' := Metric.mem_sphere.mp p.2.2
  rw [dist_eq_norm, sub_zero] at h'
  intro h
  rw [h, norm_zero] at h'
  exact one_ne_zero h'.symm

/-- The coordinate function `z` on `X × S¹`, as a *unit* of `C(X × S¹, ℂ)`
(its inverse is `z ↦ z⁻¹`, continuous because `‖z‖ = 1` on the circle). -/
def zUnit : (C(X × Sph ℂ, ℂ))ˣ where
  val := ⟨fun p => (p.2 : ℂ), by fun_prop⟩
  inv := ⟨fun p => ((p.2 : ℂ))⁻¹,
    (continuous_subtype_val.comp continuous_snd).inv₀ (z_ne_zero X)⟩
  val_inv := by ext p; exact mul_inv_cancel₀ (z_ne_zero X p)
  inv_val := by ext p; exact inv_mul_cancel₀ (z_ne_zero X p)

@[simp] lemma zUnit_apply (p : X × Sph ℂ) : (zUnit X : C(X × Sph ℂ, ℂ)) p = (p.2 : ℂ) := rfl

/-- The `ℂ`-algebra map `C(X)[T;T⁻¹] → C(X × S¹, ℂ)`: coefficients are pulled back along the
projection, `T` goes to the coordinate `z`. -/
def laurentMap : LaurentPolynomial C(X, ℂ) →+* C(X × Sph ℂ, ℂ) :=
  LaurentPolynomial.eval₂ (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom (zUnit X)

@[simp] lemma laurentMap_C (a : C(X, ℂ)) :
    laurentMap X (LaurentPolynomial.C a) = pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X)) a :=
  LaurentPolynomial.eval₂_C _ _ _

@[simp] lemma laurentMap_T (k : ℤ) :
    laurentMap X (LaurentPolynomial.T k) = ((zUnit X) ^ k).val :=
  LaurentPolynomial.eval₂_T _ _ _

end

end Work.KT
