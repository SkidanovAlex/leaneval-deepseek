import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs

/-!
# The multiplier `Op_{φ;E}` as a linear map of `ℓ²(ℤ)`

`OpArcDefs.lean` defines `opMul Φ f hf` on sequences carrying a proof of `Memℓp f 2`.  For the
interpolation step of Tao's `ortho-apply`(ii) (`vector_valued_lp_interpolation_count`) one needs the
operator as an honest **linear map** of the Hilbert space `ℓ²(ℤ) = lp (fun _ : ℤ => ℂ) 2`.  This
file supplies it: `opMulLM Φ` is the multiplier with symbol `Φ ∈ L^∞(𝕋)` acting on `ℓ²(ℤ)`, with
`opMulLM_apply`.
-/

open MeasureTheory
open scoped lp BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- `ftLp` only depends on the underlying sequence (the `Memℓp` proof is irrelevant). -/
theorem ftLp_congr_memℓp {f g : ℤ → ℂ} (hfg : f = g) (hf : Memℓp f 2) (hg : Memℓp g 2) :
    ftLp f hf = ftLp g hg := by
  subst hfg
  unfold ftLp
  simp only

/-- `ftLp` is additive in the sequence. -/
theorem ftLp_add {f g : ℤ → ℂ} (hf : Memℓp f 2) (hg : Memℓp g 2) :
    ftLp (f + g) (hf.add hg) = ftLp f hf + ftLp g hg := by
  unfold ftLp
  rw [show (⟨f + g, hf.add hg⟩ : lp (fun _ : ℤ => ℂ) 2) = ⟨f, hf⟩ + ⟨g, hg⟩ from rfl]
  exact map_add _ _ _

/-- `ftLp` is homogeneous in the sequence. -/
theorem ftLp_smul (c : ℂ) {f : ℤ → ℂ} (hf : Memℓp f 2) :
    ftLp (c • f) (hf.const_smul c) = c • ftLp f hf := by
  unfold ftLp
  rw [show (⟨c • f, hf.const_smul c⟩ : lp (fun _ : ℤ => ℂ) 2) = c • ⟨f, hf⟩ from rfl]
  exact map_smul _ _ _

/-- **The multiplier with symbol `Φ ∈ L^∞(𝕋)` as a linear map of `ℓ²(ℤ)`**: the linear version of
`opMul`, needed to apply the vector-valued interpolation of Tao's `ortho-apply`(ii). -/
def opMulLM (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) :
    lp (fun _ : ℤ => ℂ) 2 →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  toFun v := ⟨opMul Φ v.1 v.2, opMul_memℓp Φ v.1 v.2⟩
  map_add' v w := by
    ext n
    have h1 : ftLp ((v + w : lp (fun _ : ℤ => ℂ) 2)).1 (v + w).2
        = ftLp v.1 v.2 + ftLp w.1 w.2 :=
      (ftLp_congr_memℓp (f := ((v + w : lp (fun _ : ℤ => ℂ) 2)).1)
        (g := v.1 + w.1) rfl (v + w).2 (v.2.add w.2)).trans (ftLp_add v.2 w.2)
    simp only [opMul, opMulLp]
    calc (fourierBasis (T := 1)).repr (Φ • ftLp (v + w).1 (v + w).2) n
        = (fourierBasis (T := 1)).repr (Φ • (ftLp v.1 v.2 + ftLp w.1 w.2)) n := by
          rw [h1]
      _ = (fourierBasis (T := 1)).repr (Φ • ftLp v.1 v.2 + Φ • ftLp w.1 w.2) n := by
          rw [Lp.add_smul]
      _ = (fourierBasis (T := 1)).repr (Φ • ftLp v.1 v.2) n
            + (fourierBasis (T := 1)).repr (Φ • ftLp w.1 w.2) n := by
          rw [map_add]; rfl
  map_smul' c v := by
    ext n
    have h1 : ftLp ((c • v : lp (fun _ : ℤ => ℂ) 2)).1 (c • v).2 = c • ftLp v.1 v.2 :=
      (ftLp_congr_memℓp (f := ((c • v : lp (fun _ : ℤ => ℂ) 2)).1)
        (g := c • v.1) rfl (c • v).2 (v.2.const_smul c)).trans (ftLp_smul c v.2)
    simp only [opMul, opMulLp]
    calc (fourierBasis (T := 1)).repr (Φ • ftLp (c • v).1 (c • v).2) n
        = (fourierBasis (T := 1)).repr (Φ • (c • ftLp v.1 v.2)) n := by rw [h1]
      _ = (fourierBasis (T := 1)).repr (c • (Φ • ftLp v.1 v.2)) n := by
          rw [← Lp.smul_comm c Φ (ftLp v.1 v.2)]
      _ = (c • (fourierBasis (T := 1)).repr (Φ • ftLp v.1 v.2)) n := by
          rw [map_smul]

/-- The coefficients of `opMulLM Φ v` are those of `opMul Φ v.1 v.2`. -/
theorem opMulLM_apply (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (v : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    opMulLM Φ v n = opMul Φ v.1 v.2 n := rfl

/-- The coefficients of `opMulLM` are linear. -/
theorem opMulLM_add_apply (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (v w : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    opMulLM Φ (v + w) n = opMulLM Φ v n + opMulLM Φ w n := by
  rw [map_add]
  rfl

end

end Work.BourgainPlan.IonescuWainger
