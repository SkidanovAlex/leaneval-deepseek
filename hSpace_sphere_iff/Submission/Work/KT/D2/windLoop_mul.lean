import Mathlib
import Submission.Work.KT.D2.Winding

namespace Work.KT.D2

open Matrix

noncomputable section

/-- The determinant loop of a matrix loop `γ` at an idempotent `e`: the continuous function
`x ↦ det (e * γ x * e + (1 - e))` on `S¹ ⊂ ℝ²`. -/
def wlmDet (n : ℕ) (e : Matrix (Fin n) (Fin n) ℂ)
    (γ : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), Matrix (Fin n) (Fin n) ℂ)) :
    C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), ℂ) :=
  ⟨fun x => Matrix.det (e * γ x * e + (1 - e)), by
    have hcont : Continuous fun x : Work.KT.Sph (EuclideanSpace ℝ (Fin 2)) =>
        e * γ x * e + (1 - e) := by fun_prop
    exact hcont.matrix_det⟩

@[simp] lemma wlmDet_apply (n : ℕ) (e : Matrix (Fin n) (Fin n) ℂ)
    (γ : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), Matrix (Fin n) (Fin n) ℂ))
    (x : Work.KT.Sph (EuclideanSpace ℝ (Fin 2))) :
    wlmDet n e γ x = Matrix.det (e * γ x * e + (1 - e)) := rfl

/-- `degNZ` depends on the loop and on the non-vanishing proof only through the loop: two loops
which are equal as continuous maps have equal winding, whatever the proofs of non-vanishing. -/
lemma wlmDegNZcongr {f g : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), ℂ)} (H : f = g)
    (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0) : degNZ f hf = degNZ g hg := by
  subst H
  exact degNZ_proof_irrel f hf hg

/-- The corner identity behind multiplicativity: for a ring element `e` which is idempotent
(`e * e = e`) and elements `a`, `b` commuting with `e`, the "restriction to `im e`, with `1 - e` on
the complement" of the product is the product of the restrictions. -/
lemma wlmCornerMul {R : Type*} [Ring R] {e a b : R} (he : e * e = e) (ha : a * e = e * a)
    (hb : b * e = e * b) :
    e * (a * b) * e + (1 - e) = (e * a * e + (1 - e)) * (e * b * e + (1 - e)) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  have ha' : e * a * e = e * a := by rw [mul_assoc, ha, ← mul_assoc, he]
  have hb' : e * b * e = e * b := by rw [mul_assoc, hb, ← mul_assoc, he]
  rw [ha', hb']
  have h4 : e * a * (e * b) = e * (a * b) * e := by rw [← hb]; noncomm_ring
  have hR : (e * a + (1 - e)) * (e * b + (1 - e)) = e * a * (e * b) + (1 - e) := by
    rw [add_mul, mul_add, mul_add]
    rw [show e * a * (1 - e) = 0 from by rw [← ha', mul_assoc, h1, mul_zero],
        show (1 - e) * (e * b) = 0 from by rw [← mul_assoc, h2, zero_mul], h3]
    noncomm_ring
  calc e * (a * b) * e + (1 - e)
      = e * a * (e * b) + (1 - e) := by rw [h4]
    _ = (e * a + (1 - e)) * (e * b + (1 - e)) := hR.symm

/-- The winding function of a loop is `degNZ` of the determinant loop. -/
lemma windLoop_eq_degNZ (n : ℕ) (e : Matrix (Fin n) (Fin n) ℂ)
    (γ : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), Matrix (Fin n) (Fin n) ℂ))
    (h : ∀ x, Matrix.det (e * γ x * e + (1 - e)) ≠ 0) :
    windLoop n e γ h = degNZ (wlmDet n e γ) h := rfl

/-- **Multiplicativity of the winding of a loop of units at an idempotent.**  For loops `γ`, `γ'`
of matrices on `S¹ ⊂ ℝ²` that commute with an idempotent `e` (pointwise), the winding at `e`
(`Work.KT.D2.windLoop`, the degree of the determinant of the restriction to `im e`) is additive
under the pointwise product.

Route: `e * (γ x * γ' x) * e + (1 - e) = (e * γ x * e + (1 - e)) * (e * γ' x * e + (1 - e))`
(using `e * e = e` and `γ' x * e = e * γ' x`), `det` is multiplicative, and the winding is the
degree of a `ℂˣ`-valued loop (`Work.KT.D2.degNZ`), which is additive
(`Work.KT.D2.degNZ_mul`; use `Work.KT.D2.degNZ`'s proof-irrelevance to handle the two proofs of
non-vanishing). -/
theorem windLoop_mul (n : ℕ) (e : Matrix (Fin n) (Fin n) ℂ) (he : e * e = e)
    (γ γ' : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), Matrix (Fin n) (Fin n) ℂ))
    (hγ : ∀ x, γ x * e = e * γ x) (hγ' : ∀ x, γ' x * e = e * γ' x)
    (h : ∀ x, Matrix.det (e * γ x * e + (1 - e)) ≠ 0)
    (h' : ∀ x, Matrix.det (e * γ' x * e + (1 - e)) ≠ 0)
    (h2 : ∀ x, Matrix.det (e * (γ * γ') x * e + (1 - e)) ≠ 0) :
    Work.KT.D2.windLoop n e (γ * γ') h2
      = Work.KT.D2.windLoop n e γ h + Work.KT.D2.windLoop n e γ' h' := by
  have hfun : wlmDet n e (γ * γ') = wlmDet n e γ * wlmDet n e γ' := by
    apply ContinuousMap.ext
    intro x
    simp only [wlmDet_apply, ContinuousMap.mul_apply, wlmCornerMul he (hγ x) (hγ' x),
      Matrix.det_mul]
  have h2' : ∀ x, (wlmDet n e γ * wlmDet n e γ') x ≠ 0 := hfun ▸ h2
  calc windLoop n e (γ * γ') h2
      = degNZ (wlmDet n e (γ * γ')) h2 := windLoop_eq_degNZ n e (γ * γ') h2
    _ = degNZ (wlmDet n e γ * wlmDet n e γ') h2' := wlmDegNZcongr hfun h2 h2'
    _ = degNZ (wlmDet n e γ) h + degNZ (wlmDet n e γ') h' :=
        degNZ_mul (wlmDet n e γ) (wlmDet n e γ') h h' h2'
    _ = windLoop n e γ h + windLoop n e γ' h' := by
        rw [windLoop_eq_degNZ n e γ h, windLoop_eq_degNZ n e γ' h']

end

end Work.KT.D2
