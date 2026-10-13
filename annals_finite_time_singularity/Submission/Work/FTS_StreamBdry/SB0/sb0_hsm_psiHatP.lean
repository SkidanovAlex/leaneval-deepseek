import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB0

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.StreamBdryIface (oddPerS psiHatP psiP)

set_option autoImplicit false

/-- `psiHatP` agrees with the odd-extended `U`-slot part of the canonical slice on the
half-plane `w > 0` (on `w ≤ 0` it is identically `0` by definition). -/
lemma psiHatP_eq_oddPerS {αG : ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam} {τ : ℝ} :
    ∀ w θ : ℝ, 0 < w →
      psiHatP αG Φs E g w θ τ = oddPerS (psiP αG (slice (PsiCan Φs E g) τ)) w θ := by
  intro w θ hw
  simp [psiHatP, hw]

theorem sb0_hsm_psiHatP {a : ℝ} (ha : 0 < a) {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hPsm : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 2
      (Function.uncurry (Work.FTS.StreamBdryIface.oddPerS
        (Work.FTS.StreamBdryIface.psiP (Work.FTS.Regularity.pExp a)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))))
      (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)))
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ w θ : ℝ, 0 < w → 0 < θ → θ < Real.pi / 2 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ =>
        Work.FTS.StreamBdryIface.psiHatP (Work.FTS.Regularity.pExp a) Φs E g p.1 p.2 τ) (w, θ) := by
  intro w θ hw _hθ _hθlt
  -- the half-strip `Ioi 0 ×ˢ Ioo (-(π/2)-1) (π/2+1)` is an open neighbourhood of `(w,θ)`
  have hopen : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hmem : (w, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1) :=
    ⟨hw, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  -- on that half-strip `psiHatP` coincides with the uncurried `oddPerS ∘ psiP` (since `w' > 0` there)
  have hcongr : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ =>
        Work.FTS.StreamBdryIface.psiHatP (Work.FTS.Regularity.pExp a) Φs E g p.1 p.2 τ)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)) :=
    (hPsm τ hτ).congr (by
      rintro ⟨p1, p2⟩ ⟨hp1, -⟩
      simp only [Function.uncurry]
      exact psiHatP_eq_oddPerS p1 p2 hp1)
  exact hcongr.contDiffAt (hopen.mem_nhds hmem)

end Work.FTS_StreamBdry.SB0
