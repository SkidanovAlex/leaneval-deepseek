import Mathlib
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.Table4.HB82
import Submission.Work.ZeroFreeTables.Table4Derive
import Submission.Work.ZeroFreeTables.Table4.HB83
import Submission.Work.LinnikAreas.DhRepel.dhTrianglePtH
import Submission.Work.LinnikAreas.boxMaxZeroH

namespace Work.ZeroFreeTables

open DirichletCharacter Complex
open scoped Classical BigOperators

open Work.LinnikContract

/-- The Table-4 row `λ₁ ≤ 0.35 ⟹ λ₀ ≥ 2.195` is an entry of `tableR hbTable4`. -/
theorem mem_tableR_hbTable4_row35 : ((35 : ℝ) / 100, (2195 : ℝ) / 1000) ∈ tableR hbTable4 := by
  norm_num [tableR, hbTable4]

/-- A complex number with vanishing imaginary part equals its conjugate. -/
theorem conj_eq_self_of_im_eq_zero {z : ℂ} (h : z.im = 0) : starRingEnd ℂ z = z := by
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im, h]

/-- **B1 (non-real second zero of `χ₁`), reduced to the `P₃` engine of HB Lemma 8.3.**

With HB's `P₃` engine (`HBLemma8_3`, i.e. Table 4 for a *non-real* second zero of a real
character) the row `λ₁ ≤ 0.35 ⟹ λ₀ ≥ 2.195` of Table 4 applies: a real character `χ₁` with a real
exceptional zero `ρ₁`, `λ(ρ₁) < 0.348`, cannot have a non-real zero `ρ` with `λ(ρ) < 0.348`. -/
theorem B1Nonreal_of_HB83 (h83 : HBLemma8_3) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
    zeroMult χ₁ ρ₁ = 1 →
    lamOf q ρ₁ < (348 : ℝ) / 1000 →
    IsZ χ₁ ρ → ρ ≠ ρ₁ → ρ.im ≠ 0 →
    lamOf q ρ < (348 : ℝ) / 1000 → False := by
  obtain ⟨q₀, hq₀⟩ := t4_cover h83 Table4.HB82
  refine ⟨max q₀ 3, ?_⟩
  intro q hq _inst χ₁ ρ₁ ρ hm hsq him _hsimple hlt hZ hne _himne hltρ
  have hq₀' : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hZ₁ : IsZ χ₁ ρ₁ := hm.1.1
  have hχ1 : χ₁ ≠ 1 := hZ₁.1
  have hcov := hq₀ q hq₀' χ₁ ρ₁ hm hsq hχ1 him hZ₁
  have hrow : ((2195 : ℝ) / 1000) ≤ lamOf q ρ :=
    hcov.2 ρ hZ hne (fun _ => by rw [conj_eq_self_of_im_eq_zero him]; exact hne)
      ⟨(35 : ℝ) / 100, (2195 : ℝ) / 1000⟩ mem_tableR_hbTable4_row35 (by linarith)
  linarith

/-- **The requested statement** (`Work.ZeroFreeTables.B1Nonreal`): the non-real second zero of
`χ₁` with `λ < 0.348` is impossible when the exceptional zero is real, simple and globally
`λ`-minimal.  It follows from `B1Nonreal_of_HB83` and the `P₃` engine `Table4.HB83` (HB Lemma 8.3). -/
theorem B1Nonreal : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
    Work.LinnikContract.zeroMult χ₁ ρ₁ = 1 →
    Work.LinnikContract.lamOf q ρ₁ < (348 : ℝ) / 1000 →
    Work.LinnikContract.IsZ χ₁ ρ → ρ ≠ ρ₁ → ρ.im ≠ 0 →
    Work.LinnikContract.lamOf q ρ < (348 : ℝ) / 1000 → False :=
  B1Nonreal_of_HB83 Table4.HB83

end Work.ZeroFreeTables
