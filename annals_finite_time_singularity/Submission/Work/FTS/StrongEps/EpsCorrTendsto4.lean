import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Ring.Basic
import Submission.Work.FTS.StrongEps.L12_Jeps_sub_le4
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

theorem EpsCorr_tendsto_zero4 {α Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε : ℕ → ℝ} {G : ℕ → Fam} {τ : ℝ}
    (hρ : IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (_hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hε : ∀ n : ℕ, 0 < ε n) (hε1 : ∀ n : ℕ, ε n ≤ 1)
    (hεt : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ (ε n) Φs E (G n) τ))
    (h4 : ∀ n : ℕ, Work.Spaces.HkMem α 4 (epsWP α ρ (ε n) Φs E (G n) τ))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 4 (epsWP α ρ (ε n) Φs E (G n) τ) ≤ B)
    (h0 : ∀ n : ℕ, Work.Construction.L12 (epsWP α ρ (ε n) Φs E (G n) τ) 0 = 0) :
    Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12
        (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) τ)) 0 / pzNorm)
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hkey⟩ := L12_Jeps_sub_le4 ρ hρ
  have hbd : ∀ n : ℕ,
      |Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) τ)) 0|
        ≤ C * ε n * B := by
    intro n
    have h := hkey α hα (epsWP α ρ (ε n) Φs E (G n) τ) (hsm n) (h4 n) (ε n) ⟨hε n, hε1 n⟩
    rw [h0 n, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hb n) (mul_nonneg hCpos.le (hε n).le))
  have hzero : Filter.Tendsto (fun n : ℕ => C * ε n * B) Filter.atTop (nhds 0) := by
    have := ((hεt.const_mul C).mul_const B)
    simpa using this
  have habs : Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) τ)) 0)
      Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun n => by simpa [Real.norm_eq_abs] using hbd n) hzero
  simpa using habs.div_const pzNorm

end Work.FTS.StrongEps
