import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.StrongEps.EpsE4Thr.StepDataO
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2_succ
import Submission.Work.FTS.IPGen.IP4Add
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.Dth_Lhat_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz
import Submission.Work.FTS.StrongPersist.H6Aux.LhatCommOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

theorem Comm2_succ_O (α : ℝ) (hα : 0 < α) (n : ℕ)
    {IP : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ} {c₁ c₂ : ℝ}
    (hc : Work.FTS.StrongEps.EpsE4Thr.Comm2O α n IP) :
    Work.FTS.StrongEps.EpsE4Thr.Comm2O α (n + 1)
      (Work.Coercivity.HkIPStep c₁ c₂ IP) := by
  -- The two commutator clauses mention neither `n` nor `IP`: they are inherited verbatim.
  refine ⟨?congr, ?add, hc.dthC, hc.dzC⟩
  case congr =>
    -- Congruence: the derivative is local and the open quadrant is open, so agreement on
    -- `Qd` propagates to `D_θ` and `D_z`, and the three `congr` clauses of `IP` apply.
    intro f f' g hfg
    have e0 := hc.congr f f' g hfg
    have e1 := hc.congr (Work.Spaces.Dth f) (Work.Spaces.Dth f') (Work.Spaces.Dth g)
      (Work.FTS.IPGen.Dth_congr_Qd hfg)
    have e2 := hc.congr (Work.Spaces.Dz f) (Work.Spaces.Dz f') (Work.Spaces.Dz g)
      (Work.FTS.IPGen.Dz_congr_Qd hfg)
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
  case add =>
    intro f₁ f₂ g hf₁ hf₂ hg
    -- descent of the class from level `n+1` to level `n`
    have h₁ : RegQo α n f₁ := regQo_mono (Nat.le_succ n) hf₁
    have h₂ : RegQo α n f₂ := regQo_mono (Nat.le_succ n) hf₂
    have h₃ : RegQo α n g := regQo_mono (Nat.le_succ n) hg
    have e0 := hc.add f₁ f₂ g h₁ h₂ h₃
    have h1n : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have hbadd : Work.FTS.CoercivityFix.Assembly.BlocksAdd (n + 1) f₁ f₂ :=
      Work.FTS.IPGen.BlocksAdd_of_smoothOpen (k := n + 1) hf₁.1 hf₂.1
    have e1 : IP (Work.Spaces.Dth (f₁ + f₂)) (Work.Spaces.Dth g)
        = IP (Work.Spaces.Dth f₁) (Work.Spaces.Dth g)
          + IP (Work.Spaces.Dth f₂) (Work.Spaces.Dth g) := by
      rw [hc.congr (Work.Spaces.Dth (f₁ + f₂))
        (Work.Spaces.Dth f₁ + Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        (Work.FTS.IPGen.Dth_add_of_blocksAdd hbadd h1n)]
      exact hc.add (Work.Spaces.Dth f₁) (Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        (regQo_dth_dz hα hf₁).1 (regQo_dth_dz hα hf₂).1 (regQo_dth_dz hα hg).1
    have e2 : IP (Work.Spaces.Dz (f₁ + f₂)) (Work.Spaces.Dz g)
        = IP (Work.Spaces.Dz f₁) (Work.Spaces.Dz g)
          + IP (Work.Spaces.Dz f₂) (Work.Spaces.Dz g) := by
      rw [hc.congr (Work.Spaces.Dz (f₁ + f₂))
        (Work.Spaces.Dz f₁ + Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        (Work.FTS.IPGen.Dz_add_of_blocksAdd hbadd h1n)]
      exact hc.add (Work.Spaces.Dz f₁) (Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        (regQo_dth_dz hα hf₁).2 (regQo_dth_dz hα hf₂).2 (regQo_dth_dz hα hg).2
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
    ring

end Work.FTS.StrongEps.EpsE4Thr
