import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup_corr
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup_corr_fam
import Submission.Work.FTS.StrongEps.EpsProfileLip
import Submission.Work.FTS.StrongEps.EpsProfileLip_of_epsWP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem EpsProfileLip_of_epsWP_corr {α T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    (hsol : ∀ n : ℕ, Work.FTS.StrongEps.IsEpsSolP α ρ (ε n) T Φs E g₀ (G n))
    (hcont : ∀ n : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
        (Set.Icc 0 T))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hwin : ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
      (∀ n : ℕ, ∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ ε n → |q.2| ≤ ε n →
        (Work.FTS.StrongEps.zShift p.1 q.1, Work.FTS.StrongEps.thShift p.2 q.2) ∈ K') ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc 0 T,
        ∀ p ∈ K', |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)
          p.1 p.2| ≤ C)
    (hcorr : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ (ε n)
        (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) 0| ≤ C)
    (hreg : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ∀ τ' ∈ Set.Icc (0 : ℝ) T,
        |Work.FTS.Galerkin.slice (G n) τ p.1 p.2 - Work.FTS.Galerkin.slice (G n) τ' p.1 p.2|
          ≤ C * |τ - τ'| := by
  -- `EpsRHSP_slotSup_corr_fam` bounds every mixed slot `D_z^j D_θ^i (epsRHSP · s)`, `j + i ≤ 4`,
  -- on the compact `K`, uniformly in the family index `n`: this is exactly the hypothesis
  -- `hbdd` of `slice_lip_of_rhsSup` after reading off the `(j, i) = (0, 0)` slot.
  obtain ⟨C, hC, hbound⟩ :=
    Work.FTS.StrongEps.EpsRHSP_slotSup_corr_fam hα hρ hε hreg hK hKQ hwin hcorr
  -- The slices are the time-integral of `epsRHSP` (`epsSol_eq_integralP`), so their difference
  -- is an interval integral of a uniformly bounded integrand.
  refine Work.FTS.StrongEps.slice_lip_of_rhsSup hsol hcont hKQ ⟨C, hC, ?_⟩
  intro n s hs p hp
  simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
    using hbound n 0 0 (by omega) s hs p hp

end Work.FTS.StrongEps
