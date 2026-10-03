import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpMulLinear

/-!
# `Op_{φ;E}` as a linear map on finitely supported sequences

`OpArcDefs.opArc φ hφ E f hf` needs a proof `hf : Memℓp f 2`, so it is only defined on `ℓ²(ℤ)`.
For the interpolation step of Tao's `ortho-apply`(ii) (`ellp_vector_interpolation_family`) the
operator has to be a genuine `ℂ`-linear map on the finitely supported sequences; that is the
content of `opArcLM` below (`memℓp_finsupp` supplies the `ℓ²`-proof, and `ftLp_congr_memℓp`,
`ftLp_add`, `ftLp_smul` of `OpMulLinear.lean` give the additivity/homogeneity, exactly as for
`opMulLM`).
-/

open MeasureTheory
open scoped lp BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- A finitely supported complex sequence is in `ℓ²(ℤ)`. -/
theorem memℓp_finsupp (f : ℤ →₀ ℂ) : Memℓp (⇑f) 2 := by
  refine memℓp_gen (p := 2) (summable_of_ne_finset_zero (s := f.support) (fun i hi => ?_))
  rw [Finsupp.notMem_support_iff.mp hi, norm_zero]
  simp

/-- Pointwise equality of finitely supported sequences is transported by `Finsupp.coe`. -/
theorem coe_finsupp_congr {f g : ℤ →₀ ℂ} (h : ∀ n : ℤ, f n = g n) : (⇑f : ℤ → ℂ) = ⇑g :=
  funext h

/-- **The modulated multiplier `Op_{φ;E}` as a `ℂ`-linear map on finitely supported sequences.** -/
def opArcLM (φ : Circle → ℂ) (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset Circle) : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun f := opArc φ hφ E (⇑f) (memℓp_finsupp f)
  map_add' f g := by
    have hft : ftLp (⇑(f + g)) (memℓp_finsupp (f + g))
        = ftLp (⇑f) (memℓp_finsupp f) + ftLp (⇑g) (memℓp_finsupp g) :=
      (ftLp_congr_memℓp (f := ⇑(f + g)) (g := ⇑f + ⇑g)
          (by funext i; simp) (memℓp_finsupp (f + g))
          ((memℓp_finsupp f).add (memℓp_finsupp g))).trans
        (ftLp_add (memℓp_finsupp f) (memℓp_finsupp g))
    funext n
    simp only [opArc, opMul, opMulLp]
    rw [hft, Lp.add_smul, map_add]
    rfl
  map_smul' c f := by
    have hft : ftLp (⇑(c • f)) (memℓp_finsupp (c • f))
        = c • ftLp (⇑f) (memℓp_finsupp f) :=
      (ftLp_congr_memℓp (f := ⇑(c • f)) (g := c • ⇑f)
          (by funext i; simp) (memℓp_finsupp (c • f))
          ((memℓp_finsupp f).const_smul c)).trans (ftLp_smul c (memℓp_finsupp f))
    funext n
    simp only [opArc, opMul, opMulLp]
    rw [hft, ← Lp.smul_comm c (arcSymbolLp φ hφ E) (ftLp (⇑f) (memℓp_finsupp f)),
      map_smul]
    rfl

/-- The coefficients of `opArcLM φ hφ E f` are those of `opArc φ hφ E f`. -/
theorem opArcLM_apply (φ : Circle → ℂ) (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset Circle) (f : ℤ →₀ ℂ) (n : ℤ) :
    opArcLM φ hφ E f n = opArc φ hφ E (⇑f) (memℓp_finsupp f) n := rfl

end

end Work.BourgainPlan.IonescuWainger
