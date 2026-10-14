import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaData
import Submission.Work.FTS.StrongEps.L12_Jeps_sub_le4
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzSlot
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.SupOpenH2
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.Xn_JfamP_lip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The repaired statement (per-slice regularity added) -/


/-! ## The requested statement (kept verbatim; see the header for why its hypotheses are
insufficient) -/


end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.hWc_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option maxHeartbeats 2000000

/-- The difference of two open-quadrant smooth profiles is open-quadrant smooth. -/
theorem smoothOpen_sub {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ - g z θ) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
  intro m
  have h1 := (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf m
  have h2 := (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mp hg m
  have hfun : Function.uncurry (fun z θ => f z θ - g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p - Function.uncurry g p := rfl
  rw [hfun]
  exact h1.sub h2

/-- **The `ε`-free `ℋ⁵`-bound for the projected-mollified difference.** -/
theorem hkNorm5_Wp_sub_le_fam {α : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    {ε : ℕ → ℝ} (hε : ∀ k : ℕ, ε k ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ {u v : Fn},
      Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
      Work.Spaces.HkMem α 6 u → Work.Spaces.HkMem α 6 v →
      Work.Spaces.HkNorm α 5 (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ (ε k) u z θ
          - Work.FTS.StrongEps.EpsRLX.Wp ρ (ε k) v z θ)
        ≤ C * Work.Spaces.HkNorm α 5 (fun z θ => u z θ - v z θ) := by
  obtain ⟨A, hApos, hA⟩ := hkNorm_Pz_le_five
  obtain ⟨Cj, hCjpos, hCj⟩ := Work.FTS.StrongEps.HkSq_Jeps_le ρ hρ.moll
  refine ⟨A * Real.exp (Cj / 2), by positivity, ?_⟩
  intro k u v hsu hsv hm6u hm6v
  have hεk := hε k
  have hDc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (fun z θ => u z θ - v z θ))
      Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (smoothOpen_sub hsu hsv)
  have hsmD : Work.FTS.EllipticEst.SmoothOpen (fun z θ => u z θ - v z θ) := smoothOpen_sub hsu hsv
  have hm6D : Work.Spaces.HkMem α 6 (fun z θ => u z θ - v z θ) :=
    Work.FTS.GalBasis.hkMem_sub_open α 6 hsu hsv hm6u hm6v
  have hm5D : Work.Spaces.HkMem α 5 (fun z θ => u z θ - v z θ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmD 5 (by norm_num) hm6D
  have hWp : (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ (ε k) u z θ
        - Work.FTS.StrongEps.EpsRLX.Wp ρ (ε k) v z θ)
      = Work.FTS.StrongEps.EpsRLX.Wp ρ (ε k) (fun z θ => u z θ - v z θ) :=
    Work.FTS.StrongEps.EpsRLX.Wp_sub_eq hα hρ hεk.1 hsu hsv hm6u hm6v
  rw [hWp]
  have hsmJ : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.Jeps ρ (ε k) (fun z θ => u z θ - v z θ)) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hεk.1 hDc
  have hm5J : Work.Spaces.HkMem α 5
      (Work.FTS.StrongEps.Jeps ρ (ε k) (fun z θ => u z θ - v z θ)) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hεk.1 hDc hm5D
  have hPz : Work.Spaces.HkNorm α 5
        (Work.FTS.StrongEps.EpsRLX.Wp ρ (ε k) (fun z θ => u z θ - v z θ))
      ≤ A * Work.Spaces.HkNorm α 5
        (Work.FTS.StrongEps.Jeps ρ (ε k) (fun z θ => u z θ - v z θ)) :=
    hA α hα _ hsmJ hm5J
  have hJ : Work.Spaces.HkNorm α 5
        (Work.FTS.StrongEps.Jeps ρ (ε k) (fun z θ => u z θ - v z θ))
      ≤ Real.exp (Cj / 2)
        * Work.Spaces.HkNorm α 5 (fun z θ => u z θ - v z θ) := by
    have hsq := hCj α hα 5 (ε k) hεk.1 hεk.2 (fun z θ => u z θ - v z θ) hDc hm5D hm5J
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 5
          (Work.FTS.StrongEps.Jeps ρ (ε k) (fun z θ => u z θ - v z θ)))
        ≤ Real.sqrt (Real.exp (Cj * ε k)
            * Work.Spaces.HkSq α 5 (fun z θ => u z θ - v z θ)) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (Real.exp (Cj * ε k))
            * Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => u z θ - v z θ)) :=
          Real.sqrt_mul (Real.exp_pos _).le _
      _ = Real.exp (Cj * ε k / 2) * Work.Spaces.HkNorm α 5 (fun z θ => u z θ - v z θ) := by
          rw [Real.exp_half, Work.Spaces.HkNorm]
      _ ≤ Real.exp (Cj / 2) * Work.Spaces.HkNorm α 5 (fun z θ => u z θ - v z θ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkNorm_nonneg _ _ _)
          exact Real.exp_le_exp.mpr (by nlinarith [hεk.2, hCjpos])
  calc Work.Spaces.HkNorm α 5
        (Work.FTS.StrongEps.EpsRLX.Wp ρ (ε k) (fun z θ => u z θ - v z θ))
      ≤ A * Work.Spaces.HkNorm α 5
        (Work.FTS.StrongEps.Jeps ρ (ε k) (fun z θ => u z θ - v z θ)) := hPz
    _ ≤ A * (Real.exp (Cj / 2)
          * Work.Spaces.HkNorm α 5 (fun z θ => u z θ - v z θ)) :=
        mul_le_mul_of_nonneg_left hJ hApos.le
    _ = A * Real.exp (Cj / 2) * Work.Spaces.HkNorm α 5 (fun z θ => u z θ - v z θ) := by ring

end Work.FTS.StrongEps.E5G
end
end
