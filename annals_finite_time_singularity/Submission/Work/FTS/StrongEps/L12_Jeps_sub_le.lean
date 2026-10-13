import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.L12_lipschitz_field
import Submission.Work.FTS.StrongEps.EpsApprox.HkNorm_Jeps_sub_le
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.HkMem_JepsSub
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem L12_Jeps_sub_le (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (f : Work.FTS.Galerkin.Fn),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 5 f →
      ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 →
        |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε f) 0
            - Work.Construction.L12 f 0| ≤ C * ε * Work.Spaces.HkNorm α 5 f := by
  -- the `ℋ⁴`-Lipschitz continuity of the zero mode, and the mollifier approximation estimate
  obtain ⟨C₁, hC₁pos, hLip⟩ := L12_lipschitz_field
  obtain ⟨C₂, hC₂pos, hApp⟩ :=
    Work.FTS.StrongEps.EpsApprox.HkNorm_Jeps_sub_le ρ hρ.moll
  refine ⟨C₁ * C₂, mul_pos hC₁pos hC₂pos, ?_⟩
  intro α hα f hf hmem5 ε hε
  have hαpos : 0 < α := hα.1
  -- smoothness of `f` in the two equivalent shapes
  have hfQ0 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf
  have hfQuad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad := by
    intro n
    simpa only [Quad, Work.FTS.EllipticEst.Q0] using hfQ0 n
  -- the three profiles and their certificates
  have hJso : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε f) :=
    smoothOpen_Jeps ρ hρ hε.1 hfQuad
  have hmem4f : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf 4 (by norm_num) hmem5
  have hmem5J : Work.Spaces.HkMem α 5 (Jeps ρ ε f) :=
    HkMem_Jeps hρ.moll hα hε.1 hfQuad hmem5
  have hmem4J : Work.Spaces.HkMem α 4 (Jeps ρ ε f) :=
    Work.FTS.OpenPkg.HkMem_mono_open hJso 4 (by norm_num) hmem5J
  have hsubso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Jeps ρ ε f z θ - f z θ) := by
    have hfun : Function.uncurry (fun z θ => Jeps ρ ε f z θ - f z θ)
        = Function.uncurry (Jeps ρ ε f) - Function.uncurry f := by
      funext p; rfl
    rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
    exact hJso.sub hf
  have hsubmem : Work.Spaces.HkMem α 4 (fun z θ => Jeps ρ ε f z θ - f z θ) :=
    Work.FTS.GalBasis.hkMem_sub_open α 4 hJso hf hmem4J hmem4f
  have hlip := hLip α hαpos (Jeps ρ ε f) f ⟨hJso, hmem4J⟩ ⟨hf, hmem4f⟩ ⟨hsubso, hsubmem⟩
  have happ := hApp α hα 4 ε hε f hfQ0 hmem5 hmem4J
  calc |Work.Construction.L12 (Jeps ρ ε f) 0 - Work.Construction.L12 f 0|
      ≤ C₁ * Work.Spaces.HkNorm α 4 (fun z θ => Jeps ρ ε f z θ - f z θ) := hlip
    _ ≤ C₁ * (C₂ * ε * Work.Spaces.HkNorm α 5 f) :=
        mul_le_mul_of_nonneg_left happ (le_of_lt hC₁pos)
    _ = (C₁ * C₂) * ε * Work.Spaces.HkNorm α 5 f := by ring

end Work.FTS.StrongEps
