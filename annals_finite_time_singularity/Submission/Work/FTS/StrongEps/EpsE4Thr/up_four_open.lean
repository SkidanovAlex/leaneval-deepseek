import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Assembly.V_bounds
import Submission.Work.FTS.StrongPersist.IP6_lo_coeffs
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.LoFourOpen
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.StrongEps.EpsE4Thr.ef_le_efEta_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.normSub_SO
import Submission.Work.FTS.StrongEps.EpsE4Thr.H1IP_upper_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `up_four_open` — the `up` clause of the level-four coercivity, on the **open** class

`Work.FTS.StrongEps.EpsE4Thr.RegQo α k f = SmoothOpen f ∧ HkMem α k f ∧ BdryTraces α k f`
is the open-quadrant version of the frozen `Work.FTS.Nonlin.RegQ`: it asks for `C^∞` of `f`
on the open quadrant `(0,∞) × (0,π/2)` instead of the *strip* `(-1,∞) × (0,π/2)` of
`LocData.SmoothQuad`.  The weaker class is the one the level-four barrier can actually be run
against (`OpenBarrier.coerAdmO_slice_JfamP`), and it is exactly what the interior
integrations by parts of the coercivity consume.

This file supplies the upper comparison of the level-four inner product

  `IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α = HkIPStep c₁'' c₂'' (HkIPStep c₁' c₂'
      (HkIPStep c₁ c₂ (H1IP α)))`

on `RegQo α 5`, i.e. the open-class analogue of `Assembly.V_bounds.up_four` (which is stated
on `RegQ α 5`).  It is one of the four analytic clauses from which
`UnifIPOIP4.unifIPO_IP4_of_open_clauses` assembles the open coercivity interface `UnifIPO`.

## The proof

The recursion is the frozen one, transcribed onto the open class.  One step of the recursion
(`up_step_SO`) trades one level of the class for one level of the norm: if `IP ≼ Cst·|·|²_{ℋⁿ}`
on `{SmoothOpen} ∩ ℋ^{n+1}`, then

  `HkIPStep c₁ c₂ IP ≼ (3·Cst·max 1 (max c₁ c₂))·|·|²_{ℋ^{n+1}}`

on `{SmoothOpen} ∩ ℋ^{n+2}`, because each of the three slots of `HkIPStep` is one order lower
(`normSub_SO`), and the class of the slots is preserved by `D_θ` (`SmoothOpen.Dth`, and
`ℋ^{n+2} ↦ ℋ^{n+1}` by `IPGen.HkMem_descent`) and by `D_z` (`SmoothOpen.Dz`,
`IPGen.HkMem_descent`).  The base of the recursion is the level-`1` comparison

  `H1IP α f f ≤ 10^22·|f|²_{ℋ¹}`  (`H1IP_upper_open`),

which needs the open `ℋ¹`-identity `HkSq_one_eq_SO` and the comparison
`Ef f ≤ EfEta f` on the open honest class (`ef_le_efEta_open`).

Three steps of the recursion (`n = 1, 2, 3`) therefore give the conclusion on
`{SmoothOpen} ∩ ℋ⁵`, and `RegQo α 5` supplies exactly those two clauses.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "IP2" => Work.FTS.CoercivityFix.Assembly.IP2
local notation "IP3" => Work.FTS.CoercivityFix.Assembly.IP3
local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-- **One step of the upper comparison, on the open class.**  If the level-`n` pairing is
dominated by `Cst·|v|²_{ℋⁿ}` on `SmoothOpen ∩ ℋ^{n+1}`, then `HkIPStep c₁ c₂ IP` is dominated
by `(3·Cst·max 1 (max c₁ c₂))·|v|²_{ℋ^{n+1}}` on `SmoothOpen ∩ ℋ^{n+2}`.

The three summands of `HkIPStep` are handled by the one-sided `ℋⁿ`-vs-`ℋ^{n+1}` comparison
`hnorm` of the three slots (`normSub_SO` in the applications), the regularity of the slots
coming from `SmoothOpen.Dth`/`SmoothOpen.Dz` and the descent `IPGen.HkMem_descent`.  With
positive coefficients the loss of the step is `3·max 1 (max c₁ c₂)`. -/
theorem up_step_SO {α : ℝ} (hα : 0 < α) {n : ℕ}
    {IP : Fn → Fn → ℝ} {c₁ c₂ Cst : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hCst : 0 < Cst)
    (hnorm : ∀ v : Fn, Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α (n + 1) v →
      Work.Spaces.HkSq α n v ≤ Work.Spaces.HkSq α (n + 1) v ∧
        Work.Spaces.HkSq α n (Work.Spaces.Dth v) ≤ Work.Spaces.HkSq α (n + 1) v ∧
        Work.Spaces.HkSq α n (Work.Spaces.Dz v) ≤ Work.Spaces.HkSq α (n + 1) v)
    (h : ∀ v : Fn, Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α (n + 1) v →
      IP v v ≤ Cst * Work.Spaces.HkSq α n v) :
    ∀ v : Fn, Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α (n + 2) v →
      Work.Coercivity.HkIPStep c₁ c₂ IP v v
        ≤ (3 * Cst * max 1 (max c₁ c₂)) * Work.Spaces.HkSq α (n + 1) v := by
  intro v hs hm
  have hmv : Work.Spaces.HkMem α (n + 1) v :=
    Work.FTS.OpenPkg.HkMem_mono_open hs (n + 1) (by omega) hm
  obtain ⟨-, hmd, hmz⟩ :=
    Work.FTS.IPGen.HkMem_descent (α := α) (k := n + 1) (by linarith) hs hm
  have h0 := h v hs hmv
  have h1 := h (Work.Spaces.Dth v) hs.Dth hmd
  have h2 := h (Work.Spaces.Dz v) hs.Dz hmz
  obtain ⟨hn0, hn1, hn2⟩ := hnorm v hs hmv
  have hT : 0 ≤ Work.Spaces.HkSq α (n + 1) v := Work.Spaces.HkSq_nonneg α (n + 1) v
  have e0 : IP v v ≤ Cst * Work.Spaces.HkSq α (n + 1) v :=
    le_trans h0 (mul_le_mul_of_nonneg_left hn0 hCst.le)
  have e1 : IP (Work.Spaces.Dth v) (Work.Spaces.Dth v)
      ≤ Cst * Work.Spaces.HkSq α (n + 1) v :=
    le_trans h1 (mul_le_mul_of_nonneg_left hn1 hCst.le)
  have e2 : IP (Work.Spaces.Dz v) (Work.Spaces.Dz v)
      ≤ Cst * Work.Spaces.HkSq α (n + 1) v :=
    le_trans h2 (mul_le_mul_of_nonneg_left hn2 hCst.le)
  have hm1 : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
  have hm2 : c₁ ≤ max 1 (max c₁ c₂) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hm3 : c₂ ≤ max 1 (max c₁ c₂) := le_trans (le_max_right _ _) (le_max_right _ _)
  rw [Work.Coercivity.HkIPStep]
  have hcomb : IP v v + c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v)
      + c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v)
      ≤ (Cst * (1 + c₁ + c₂)) * Work.Spaces.HkSq α (n + 1) v := by
    have hc1 : c₁ * IP (Work.Spaces.Dth v) (Work.Spaces.Dth v)
        ≤ c₁ * (Cst * Work.Spaces.HkSq α (n + 1) v) :=
      mul_le_mul_of_nonneg_left e1 hc₁.le
    have hc2 : c₂ * IP (Work.Spaces.Dz v) (Work.Spaces.Dz v)
        ≤ c₂ * (Cst * Work.Spaces.HkSq α (n + 1) v) :=
      mul_le_mul_of_nonneg_left e2 hc₂.le
    nlinarith [e0, hc1, hc2, hT, hCst, hc₁, hc₂]
  refine le_trans hcomb ?_
  have hcoef : Cst * (1 + c₁ + c₂) ≤ 3 * Cst * max 1 (max c₁ c₂) := by
    nlinarith [hCst, hm1, hm2, hm3]
  exact mul_le_mul_of_nonneg_right hcoef hT

/-- **The upper comparison of the level-four inner product on the open coercivity class** —
the open-class analogue of `Assembly.up_four`.  The constant is explicit:
`3·(3·(3·10^22·max 1 (max c₁ c₂))·max 1 (max c₁' c₂'))·max 1 (max c₁'' c₂'')`, the three
factors being the losses of the three steps of the recursion. -/
theorem up_four_open {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 < c₁) (h₂ : 0 < c₂) (h₁' : 0 < c₁') (h₂' : 0 < c₂')
    (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ Cup : ℝ, 0 < Cup ∧ ∀ (α : ℝ), 0 < α → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.EpsE4Thr.RegQo α 5 f →
        Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f
          ≤ Cup * Work.Spaces.HkSq α 4 f := by
  set D₁ : ℝ := 3 * (10 : ℝ) ^ 22 * max 1 (max c₁ c₂) with hD₁
  set D₂ : ℝ := 3 * D₁ * max 1 (max c₁' c₂') with hD₂
  set D₃ : ℝ := 3 * D₂ * max 1 (max c₁'' c₂'') with hD₃
  have hm₁ : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
  have hm₂ : (1 : ℝ) ≤ max 1 (max c₁' c₂') := le_max_left _ _
  have hm₃ : (1 : ℝ) ≤ max 1 (max c₁'' c₂'') := le_max_left _ _
  have hD₁pos : 0 < D₁ := by rw [hD₁]; nlinarith [hm₁]
  have hD₂pos : 0 < D₂ := by rw [hD₂]; nlinarith [hD₁pos, hm₂]
  have hD₃pos : 0 < D₃ := by rw [hD₃]; nlinarith [hD₂pos, hm₃]
  refine ⟨D₃, hD₃pos, ?_⟩
  intro α hα f hf
  -- the base of the recursion: the level-`1` upper comparison on `SmoothOpen ∩ ℋ¹`
  have hbase : ∀ v : Fn, Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α 1 v →
      Work.Coercivity.H1IP α v v ≤ (10 : ℝ) ^ 22 * Work.Spaces.HkSq α 1 v :=
    fun v hs hm => H1IP_upper_open (α := α) hα hs hm (ef_le_efEta_open hs hm)
  -- three steps of the recursion, `n = 1, 2, 3`
  have u2 := up_step_SO (α := α) hα (n := 1)
    (IP := Work.Coercivity.H1IP α) h₁ h₂ (by norm_num : (0 : ℝ) < 10 ^ 22)
    (fun v hs hm => normSub_SO hα hs hm)
    (fun v hs hm => hbase v hs (Work.FTS.OpenPkg.HkMem_mono_open hs 1 (by norm_num) hm))
  have u3 := up_step_SO (α := α) hα (n := 2)
    (IP := IP2 c₁ c₂ α) h₁' h₂' hD₁pos
    (fun v hs hm => normSub_SO hα hs hm)
    (fun v hs hm => by rw [hD₁]; exact u2 v hs hm)
  have u4 := up_step_SO (α := α) hα (n := 3)
    (IP := IP3 c₁ c₂ c₁' c₂' α) h₁'' h₂'' hD₂pos
    (fun v hs hm => normSub_SO hα hs hm)
    (fun v hs hm => by rw [hD₂]; exact u3 v hs hm)
  exact u4 f hf.1 hf.2.1

end Work.FTS.StrongEps.EpsE4Thr
