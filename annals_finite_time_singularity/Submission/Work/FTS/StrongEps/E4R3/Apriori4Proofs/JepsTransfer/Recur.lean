import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.WordCongr
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.Dth_Jeps
import Submission.Work.FTS.StrongEps.Commute
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.TransportS.IPFixDefs
import Submission.Work.FTS.StrongPersist.N6TransPriced
import Submission.Work.FTS.StrongPersist.IP6_cs_coeffs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsTransfer/Recur.lean` — the recursion of the pairing `IPn`

`Work.FTS.TransportS.IPn α n` is the coercive recursion `IPn α (n+1) = HkIPStep 1 1 (IPn α n)`
started at `H1IP α`; the level-six pairing `IP6o α = IP6 1 … 1 α` of the a-priori chapter is
`IPn α 5`.  This module records the two structural facts that turn the estimate for the base
pairing `H1IP` into the estimate for `IPn α 5`:

* `IPn_congr` — `IPn α n` only sees its two arguments on the open quadrant (the `H1IP`-base of
  the induction is the already proved `H1IP_congr_Q0`, and the two derivative operators preserve
  equality on the quadrant);
* `IPn_succ_Jeps` — the recursion of the transfer defect
  `Δₙ(u,v) = IPn α n (J_ε u) v − IPn α n u (J_ε v)`, using `D_θ J_ε = J_ε D_θ` and
  `D_z J_ε = J_ε D_z` on the open quadrant.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The recursion step of `IPn`, as an unfolding lemma. -/
theorem IPn_succ_eq (α : ℝ) (n : ℕ) :
    Work.FTS.TransportS.IPn α (n + 1)
      = Work.Coercivity.HkIPStep 1 1 (Work.FTS.TransportS.IPn α n) := rfl

/-- The recursion step of `HkIPStep`, as an unfolding lemma. -/
theorem HkIPStep_eq (c₁ c₂ : ℝ) (IP : Fn → Fn → ℝ) (f g : Fn) :
    Work.Coercivity.HkIPStep c₁ c₂ IP f g
      = IP f g + c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)
        + c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g) := rfl

/-- **`IPn α n` only sees its two arguments on the open quadrant.** -/
theorem IPn_congr (α : ℝ) : ∀ (n : ℕ) {X X' Y Y' : Fn},
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → X z θ = X' z θ) →
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Y z θ = Y' z θ) →
    Work.FTS.TransportS.IPn α n X Y = Work.FTS.TransportS.IPn α n X' Y' := by
  intro n
  induction n with
  | zero =>
      intro X X' Y Y' hX hY
      exact Work.FTS.StrongEps.EpsE4Thr.H1IP_congr_Q0 α hX hY
  | succ n ih =>
      intro X X' Y Y' hX hY
      have hXth : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
          Work.Spaces.Dth X z θ = Work.Spaces.Dth X' z θ :=
        fun z θ h => Work.FTS.CoercivityStep.Base.Dth_congr_Qd (f := X) (f' := X') hX z θ h
      have hYth : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
          Work.Spaces.Dth Y z θ = Work.Spaces.Dth Y' z θ :=
        fun z θ h => Work.FTS.CoercivityStep.Base.Dth_congr_Qd (f := Y) (f' := Y') hY z θ h
      have hXz : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
          Work.Spaces.Dz X z θ = Work.Spaces.Dz X' z θ :=
        fun z θ h => Work.FTS.CoercivityStep.Base.Dz_congr_Qd (f := X) (f' := X') hX z θ h
      have hYz : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
          Work.Spaces.Dz Y z θ = Work.Spaces.Dz Y' z θ :=
        fun z θ h => Work.FTS.CoercivityStep.Base.Dz_congr_Qd (f := Y) (f' := Y') hY z θ h
      show Work.FTS.TransportS.IPn α n X Y
          + 1 * Work.FTS.TransportS.IPn α n (Work.Spaces.Dth X) (Work.Spaces.Dth Y)
          + 1 * Work.FTS.TransportS.IPn α n (Work.Spaces.Dz X) (Work.Spaces.Dz Y)
        = Work.FTS.TransportS.IPn α n X' Y'
          + 1 * Work.FTS.TransportS.IPn α n (Work.Spaces.Dth X') (Work.Spaces.Dth Y')
          + 1 * Work.FTS.TransportS.IPn α n (Work.Spaces.Dz X') (Work.Spaces.Dz Y')
      rw [ih hX hY, ih hXth hYth, ih hXz hYz]

/-- **The recursion of the transfer defect `Δₙ`.** -/
theorem IPn_succ_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε α : ℝ} (hε : 0 < ε)
    {u v : Fn} (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Quad)
    (hv : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v) Quad) (n : ℕ) :
    (Work.FTS.TransportS.IPn α (n + 1) (Work.FTS.StrongEps.Jeps ρ ε u) v
      - Work.FTS.TransportS.IPn α (n + 1) u (Work.FTS.StrongEps.Jeps ρ ε v))
    = (Work.FTS.TransportS.IPn α n (Work.FTS.StrongEps.Jeps ρ ε u) v
        - Work.FTS.TransportS.IPn α n u (Work.FTS.StrongEps.Jeps ρ ε v))
      + (Work.FTS.TransportS.IPn α n (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dth u))
            (Work.Spaces.Dth v)
          - Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u)
              (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dth v)))
      + (Work.FTS.TransportS.IPn α n (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dz u))
            (Work.Spaces.Dz v)
          - Work.FTS.TransportS.IPn α n (Work.Spaces.Dz u)
              (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dz v))) := by
  have hsu : Work.FTS.StrongEps.SmQ u := Work.FTS.StrongEps.smQ_of_forall_nat hu
  have hsv : Work.FTS.StrongEps.SmQ v := Work.FTS.StrongEps.smQ_of_forall_nat hv
  have hDthU : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε u) z θ
        = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dth u) z θ := by
    intro z θ h
    exact Work.FTS.StrongEps.Dth_Jeps ρ hρ.moll hε hsu.one hsu.pth.continuousOn h.1 h.2
  have hDthV : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε v) z θ
        = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dth v) z θ := by
    intro z θ h
    exact Work.FTS.StrongEps.Dth_Jeps ρ hρ.moll hε hsv.one hsv.pth.continuousOn h.1 h.2
  have hDzU : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε u) z θ
        = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dz u) z θ := by
    intro z θ h
    exact Work.FTS.StrongEps.Dz_Jeps hρ.moll hε hsu.one hsu.pz.continuousOn h.1 h.2
  have hDzV : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε v) z θ
        = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.Dz v) z θ := by
    intro z θ h
    exact Work.FTS.StrongEps.Dz_Jeps hρ.moll hε hsv.one hsv.pz.continuousOn h.1 h.2
  have e1 : Work.FTS.TransportS.IPn α (n + 1) (Work.FTS.StrongEps.Jeps ρ ε u) v
      = Work.FTS.TransportS.IPn α n (Work.FTS.StrongEps.Jeps ρ ε u) v
        + Work.FTS.TransportS.IPn α n (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε u))
            (Work.Spaces.Dth v)
        + Work.FTS.TransportS.IPn α n (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε u))
            (Work.Spaces.Dz v) := by
    rw [IPn_succ_eq, HkIPStep_eq]
    ring
  have e2 : Work.FTS.TransportS.IPn α (n + 1) u (Work.FTS.StrongEps.Jeps ρ ε v)
      = Work.FTS.TransportS.IPn α n u (Work.FTS.StrongEps.Jeps ρ ε v)
        + Work.FTS.TransportS.IPn α n (Work.Spaces.Dth u)
            (Work.Spaces.Dth (Work.FTS.StrongEps.Jeps ρ ε v))
        + Work.FTS.TransportS.IPn α n (Work.Spaces.Dz u)
            (Work.Spaces.Dz (Work.FTS.StrongEps.Jeps ρ ε v)) := by
    rw [IPn_succ_eq, HkIPStep_eq]
    ring
  rw [e1, e2]
  rw [IPn_congr α n hDthU (fun _ _ _ => rfl), IPn_congr α n (fun _ _ _ => rfl) hDthV,
    IPn_congr α n hDzU (fun _ _ _ => rfl), IPn_congr α n (fun _ _ _ => rfl) hDzV]
  ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
