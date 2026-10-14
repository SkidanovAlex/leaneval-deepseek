import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtBAux.SlotsM
import Submission.Work.FTS.StrongEps.TenOfEight.GainAll
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.ptBoundDz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools

open Function Set

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem ptBoundDz (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA KA : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth A z θ| ≤ KA) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
          ≤ K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ
            + K * (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
            + K * KA ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + K * (Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 1 1 f z θ
                * Work.Spaces.Wt α z θ) ^ 2
            + K * (Work.Spaces.mixed 1 1 A z θ * Work.Spaces.DzIter 5 f z θ
                * Work.Spaces.Wt α z θ) ^ 2
            + K * (Work.Spaces.Dth A z θ * Work.Spaces.DzIter 5 f z θ
                * Work.Spaces.Wt α z θ) ^ 2
            + K * (Work.Spaces.DthIter 2 A z θ * Work.Spaces.DzIter 5 f z θ
                * Work.Spaces.Wt α z θ) ^ 2 := by
  obtain ⟨CPw, hCPwpos, hPwAny⟩ := Work.FTS.StrongPersist.N6.PwAny6
  refine ⟨10 ^ 13 * max CPw 1, by positivity, ?_⟩
  intro A f MA KA hAO hfO hA6 hf6 hf7 hMA hKA z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hPwA : PtB.SupPw α CPw A := fun b a hab z θ hz hθ =>
    hPwAny α A b a hα hα1 hAO hA6 hab z hz θ hθ
  have hPwf : PtB.SupPw α CPw f := fun b a hab z θ hz hθ =>
    hPwAny α f b a hα hα1 hfO hf6 hab z hz θ hθ
  have hMnn : 0 ≤ PtB.Maj α A f MA KA z θ := PtB.Maj_nonneg hα A f MA KA z θ
  have hCMpos : 0 < max CPw 1 := lt_of_lt_of_le hCPwpos (le_max_left _ _)
  -- the pure `D_z`-sum
  have hzsum : ∑ i ∈ Finset.range 7,
      (Work.Spaces.DzIter i (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 7 * (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ) := by
    have hstep : ∀ i ∈ Finset.range 7,
        (Work.Spaces.DzIter i (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ 10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ :=
      fun i hi => PtB.zslot_le hα hα1 hAO hfO hMA hPwA hPwf hCPwpos i
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) z θ hz hθ0 hθ1
    calc ∑ i ∈ Finset.range 7,
          (Work.Spaces.DzIter i (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ ∑ _i ∈ Finset.range 7, (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ) :=
          Finset.sum_le_sum hstep
      _ = 7 * (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  -- the mixed sum
  have hmsum : ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
      (if 1 ≤ i ∧ i + j ≤ 6 then
        (Work.Spaces.mixed j i (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
          * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ 49 * (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ) := by
    have hper : ∀ i ∈ Finset.range 7, ∀ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then
          (Work.Spaces.mixed j i (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ 10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ 6
      · rw [if_pos hc]
        exact PtB.mslot_le hα hα1 hAO hfO hMA hKA hPwA hPwf hCPwpos i j hc.1 hc.2
          z θ hz hθ0 hθ1
      · rw [if_neg hc]
        exact mul_nonneg (by positivity) hMnn
    have hsum2 : ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then
          (Work.Spaces.mixed j i (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ∑ _i ∈ Finset.range 7, ∑ _j ∈ Finset.range 7,
            (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ) :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hper i hi j hj))
    calc ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ∑ _i ∈ Finset.range 7, ∑ _j ∈ Finset.range 7,
            (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ) := hsum2
      _ = 49 * (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  rw [Work.Spaces.HkIntegrand]
  refine le_trans (add_le_add hzsum hmsum) ?_
  have hXnn : 0 ≤ max CPw 1 * PtB.Maj α A f MA KA z θ :=
    mul_nonneg (le_of_lt hCMpos) hMnn
  have hfin : 7 * (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ)
      + 49 * (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ)
      ≤ 10 ^ 13 * max CPw 1 * PtB.Maj α A f MA KA z θ := by
    nlinarith [hXnn]
  refine le_trans hfin (le_of_eq ?_)
  simp only [PtB.Maj, PtB.Maj1, PtB.Maj2, PtB.Maj3, PtB.Maj4, PtB.Maj5, PtB.Maj6, PtB.Maj7]
  ring

end

end Work.FTS.StrongEps.E4R3.Nblock6.Tools
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsLocalPStar

open Work.FTS.Galerkin (Fn Fam slice famOf)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The pre-mollified right-hand side of the projected scheme as a function of the **single
profile** `w` on which everything is evaluated (`F = F_* + w`, `Φ = Φ_s + E w`, modulation
constants `μ, λ` and the elliptic coefficients all at `w`). -/
noncomputable def profRHS (α : ℝ) (Φs : Fn) (E : Fn → Fn) (w : Fn) : Fn :=
  fun z θ => Work.FTS.StrongPersist.linPart α w z θ
    + Work.FTS.StrongPersist.rhsOf α
        (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w)))
          (famOf (fun _ => w)) 0)
        (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w)))
          (famOf (fun _ => w)) 0)
        (Work.Construction.Ftot α w) (fun z θ => Φs z θ + E w z θ) w z θ

/-- **The `τ`-elimination**: the projected scheme's right-hand side at the profile `u` is the
projection of the mollified pre-mollified right-hand side `profRHS` evaluated at the
projected-mollified profile `Pz (Jeps ρ ε u)`. -/
theorem epsRHPSlice_eq_profRHS (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn)
    (τ : ℝ) (u : Fn) :
    epsRHPSlice α ρ ε Φs E τ u
      = Pz (Jeps ρ ε (profRHS α Φs E (Pz (Jeps ρ ε u)))) := by
  set w : Fn := Pz (Jeps ρ ε u) with hwdef
  have hWs : slice (JfamP ρ ε (famOf (fun _ : ℝ => u))) τ = w := rfl
  have hW0s : slice (famOf (fun _ => w)) 0 = w := rfl
  have hPhi : slice (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε (famOf (fun _ : ℝ => u)))) τ
      = slice (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w))) 0 := by
    funext z θ
    simp only [Work.FTS.Nonlin.PsiCan, Work.FTS.Galerkin.slice_apply, hWs, hW0s]
  have hF : Work.Construction.Ftau α (JfamP ρ ε (famOf (fun _ : ℝ => u))) τ
      = Work.Construction.Ftau α (famOf (fun _ => w)) 0 := by
    funext z θ
    simp only [Work.Construction.Ftau]
    rw [show JfamP ρ ε (famOf (fun _ : ℝ => u)) z θ τ = w z θ from
        congrFun (congrFun hWs z) θ]
    rfl
  have hmu : Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε (famOf (fun _ : ℝ => u))))
      (JfamP ρ ε (famOf (fun _ : ℝ => u))) τ
      = Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w)))
          (famOf (fun _ => w)) 0 := by
    rw [Work.FTS.Galerkin.muDyn_eq, Work.FTS.Galerkin.muDyn_eq, hF, hWs, hW0s, hPhi]
  have hlam : Work.FTS.Galerkin.lamDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (JfamP ρ ε (famOf (fun _ : ℝ => u))))
      (JfamP ρ ε (famOf (fun _ : ℝ => u))) τ
      = Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w)))
          (famOf (fun _ => w)) 0 := by
    rw [Work.FTS.Galerkin.lamDyn, Work.FTS.Galerkin.lamDyn, hmu]
  have hFt : Work.Construction.Ftau α (famOf (fun _ => w)) 0 = Work.Construction.Ftot α w := rfl
  have hPs : slice (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w))) 0
      = fun z θ => Φs z θ + E w z θ := rfl
  have key : epsWP α ρ ε Φs E (famOf (fun _ : ℝ => u)) τ = profRHS α Φs E w := by
    funext z θ
    simp only [epsWP, profRHS, Work.FTS.StrongPersist.dynLin_eq_linPart,
      Work.FTS.StrongPersist.dynRHS_eq_rhsOf, hF, hWs, hW0s, hPhi, hmu, hlam, hFt, hPs]
  rw [epsRHPSlice, epsRHSP, key]


end Work.FTS.StrongEps.EpsLocalPStar
end
end
