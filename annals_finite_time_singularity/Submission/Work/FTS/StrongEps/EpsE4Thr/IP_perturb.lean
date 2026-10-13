import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

theorem IP_perturb {α α₂ cc clo Cup Ccs ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ} {w x : Work.FTS.Galerkin.Fn}
    (hIP : Work.FTS.Nonlin.UnifIP IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂)
    (hw : Work.FTS.Nonlin.RegQ α 4 w)
    (hJw : Work.FTS.Nonlin.RegQ α 4 (Work.FTS.StrongEps.Jeps ρ ε w))
    (hdiff : Work.FTS.Nonlin.RegQ α 4 (fun z θ => Work.FTS.StrongEps.Jeps ρ ε w z θ - w z θ))
    (hx : Work.FTS.Nonlin.RegQ α 4 x) :
    |IP α (Work.FTS.StrongEps.Jeps ρ ε w) x - IP α w x|
      ≤ Ccs * Work.Spaces.HkNorm α 4 (fun z θ => Work.FTS.StrongEps.Jeps ρ ε w z θ - w z θ)
        * Work.Spaces.HkNorm α 4 x := by
  -- The difference of the two pairings is the pairing of the difference `J_ε w - w`:
  -- write `d := J_ε w - w`; then `d + w = J_ε w` pointwise, so `UnifIP.add_fst` gives
  -- `IP α (J_ε w) x = IP α d x + IP α w x`, i.e. `IP α (J_ε w) x - IP α w x = IP α d x`.
  have hadd : IP α ((fun z θ => Work.FTS.StrongEps.Jeps ρ ε w z θ - w z θ) + w) x
      = IP α (fun z θ => Work.FTS.StrongEps.Jeps ρ ε w z θ - w z θ) x + IP α w x :=
    hIP.add_fst α hα (fun z θ => Work.FTS.StrongEps.Jeps ρ ε w z θ - w z θ) w x hdiff hw hx
  have hsplit : (fun z θ => Work.FTS.StrongEps.Jeps ρ ε w z θ - w z θ) + w
      = Work.FTS.StrongEps.Jeps ρ ε w := by
    funext z θ
    simp only [Pi.add_apply]
    ring
  rw [hsplit] at hadd
  -- Cauchy–Schwarz (`UnifIP.cs`) applied to the difference.
  have hcs : |IP α (fun z θ => Work.FTS.StrongEps.Jeps ρ ε w z θ - w z θ) x|
      ≤ Ccs * Work.Spaces.HkNorm α 4 (fun z θ => Work.FTS.StrongEps.Jeps ρ ε w z θ - w z θ)
        * Work.Spaces.HkNorm α 4 x :=
    hIP.cs α hα (fun z θ => Work.FTS.StrongEps.Jeps ρ ε w z θ - w z θ) x hdiff hx
  have hmain : IP α (Work.FTS.StrongEps.Jeps ρ ε w) x - IP α w x
      = IP α (fun z θ => Work.FTS.StrongEps.Jeps ρ ε w z θ - w z θ) x := by
    rw [hadd]; ring
  rw [hmain]
  exact hcs

end Work.FTS.StrongEps.EpsE4Thr
