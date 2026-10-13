/-
Copyright: work module for the Elgindi finite-time singularity project.

# `IPGen/IP4Smul.lean` — homogeneity of the coercive `IP4` in its first argument

The `smul`/`neg` clauses of the corrected contract `N4ExtraQ` (`IPGen/Defs.lean`), for the
concrete `Assembly.IP4 c₁ … c₂''`.  **No regularity hypothesis at all is needed**: `D_θ` and
`D_z` commute with scalar multiplication *unconditionally*
(`Coercivity.Dth_smul`, `Coercivity.Dz_smul`, proved from `deriv_const_mul_uncond`), and the
base pairing `H1IP α (c·f) g = c·H1IP α f g` is unconditional (`Coercivity.H1IP_homog`, from
`wip_smul_left`).  So the recursion inherits homogeneity by pure rewriting, and both the
`HQo`- and the `RegQ`-versions of the clause follow immediately from the unrestricted one
below (`ip4_smul`, `ip4_neg`).

Everything here is `sorry`-free.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.IPGen.Defs
import Submission.Work.Coercivity.H1IP_homog
import Submission.Work.FTS.CoercivityFix.Assembly.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.IPGen

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)

set_option autoImplicit false

/-- **One step of the recursion is homogeneous**: if `IP (c·f) g = c·IP f g`, then the same
holds for `HkIPStep c₁ c₂ IP`. -/
theorem HkIPStep_homog (c₁ c₂ c : ℝ) (IP : Fn → Fn → ℝ)
    (hIP : ∀ f g : Fn, IP (fun z θ => c * f z θ) g = c * IP f g) (f g : Fn) :
    Work.Coercivity.HkIPStep c₁ c₂ IP (fun z θ => c * f z θ) g
      = c * Work.Coercivity.HkIPStep c₁ c₂ IP f g := by
  have hdth : Work.Spaces.Dth (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.Dth f z θ := Work.Coercivity.Dth_smul c f
  have hdz : Work.Spaces.Dz (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.Dz f z θ := Work.Coercivity.Dz_smul c f
  simp only [Work.Coercivity.HkIPStep, hdth, hdz, hIP]
  ring

/-- Homogeneity of the iterated recursion `IPnG c₁ c₂ α n`. -/
theorem IPnG_homog (c₁ c₂ c α : ℝ) :
    ∀ (n : ℕ) (f g : Fn),
      IPnG c₁ c₂ α n (fun z θ => c * f z θ) g = c * IPnG c₁ c₂ α n f g := by
  intro n
  induction n with
  | zero => intro f g; exact Work.Coercivity.H1IP_homog α c f g
  | succ n ih =>
      intro f g
      exact HkIPStep_homog c₁ c₂ c (IPnG c₁ c₂ α n) ih f g

/-- Homogeneity of `IP2`. -/
theorem IP2_homog (c₁ c₂ c α : ℝ) (f g : Fn) :
    Work.FTS.CoercivityFix.Assembly.IP2 c₁ c₂ α (fun z θ => c * f z θ) g
      = c * Work.FTS.CoercivityFix.Assembly.IP2 c₁ c₂ α f g :=
  IPnG_homog c₁ c₂ c α 1 f g

/-- Homogeneity of `IP3`. -/
theorem IP3_homog (c₁ c₂ c₁' c₂' c α : ℝ) (f g : Fn) :
    Work.FTS.CoercivityFix.Assembly.IP3 c₁ c₂ c₁' c₂' α (fun z θ => c * f z θ) g
      = c * Work.FTS.CoercivityFix.Assembly.IP3 c₁ c₂ c₁' c₂' α f g :=
  HkIPStep_homog c₁' c₂' c (IPnG c₁ c₂ α 1) (IPnG_homog c₁ c₂ c α 1) f g

/-- **Homogeneity of the coercive `IP4` in its first argument**, with no regularity
hypothesis. -/
theorem IP4_homog (c₁ c₂ c₁' c₂' c₁'' c₂'' c α : ℝ) (f g : Fn) :
    Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => c * f z θ) g
      = c * Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g :=
  HkIPStep_homog c₁'' c₂'' c (Work.Coercivity.HkIPStep c₁' c₂' (IPnG c₁ c₂ α 1))
    (HkIPStep_homog c₁' c₂' c (IPnG c₁ c₂ α 1) (IPnG_homog c₁ c₂ c α 1)) f g

/-- The `smul` clause of `N4ExtraQ` for `Assembly.IP4`, in its strongest form (no `HQo`
hypothesis, no restriction on `α`). -/
theorem ip4_smul (c₁ c₂ c₁' c₂' c₁'' c₂'' c α : ℝ) (f g : Fn) :
    Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => c * f z θ) g
      = c * Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g :=
  IP4_homog c₁ c₂ c₁' c₂' c₁'' c₂'' c α f g

/-- The `neg` clause of `N4ExtraQ` for `Assembly.IP4` (the `c = -1` instance of `ip4_smul`). -/
theorem ip4_neg (c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) (f g : Fn) :
    Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => -f z θ) g
      = -Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g := by
  have h := IP4_homog c₁ c₂ c₁' c₂' c₁'' c₂'' (-1) α f g
  simpa using h

end Work.FTS.IPGen
