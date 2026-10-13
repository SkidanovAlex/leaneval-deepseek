/-
Copyright: work module for the Elgindi finite-time singularity project.

# `IPGen/IP4Add.lean` — additivity of the coercive `IP4` on the open class `HQo α 4`

The `add` clause of the corrected contract `N4ExtraQ` (`IPGen/Defs.lean`) asks for additivity
of `Assembly.IP4 c₁ … c₂''` in its first argument on the *open* class
`HQo α 4 = SmoothOpen ∧ HkMem α 4` (interior `C^∞` plus honesty, **no** boundary traces and
**no** smoothness through `z = 0`).

The `RegQ`-based clause `Assembly.V_core` cannot be used: `RegQ` contains `SmoothQuad`
(genuine `C^∞` on `z > -1`).  The right induction is `Comm2w`'s: the package

  `Comm2o α n IP`  —  `congr` (on `Qd`, no membership) plus `add` with hypotheses
  `SmoothOpen` and `HkMem α (n+1)`,

which climbs one level under `HkIPStep c₁ c₂` (`Comm2o_succ`), the descent of the honesty
along `D_θ`/`D_z` being supplied *from the interior smoothness* by
`IPGen/OpenBasic.lean` (`HkMem_descent`), and the block hypotheses by
`BlocksCont_of_smoothOpen`/`BlocksAdd_of_smoothOpen`.

This is `CoercivityFix.Assembly.Comm2w_succ`/`Comm2w_L1` with the descent hypotheses
*discharged* for `SmoothOpen` data — `Comm2w_succ` itself cannot be instantiated here because
its `hdown` (`HkMem α (n+1) f → HkMem α n (D_zf)`) is false without smoothness.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.IPGen.Defs
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.CoercivityFix.Assembly.V_core
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2_levels
import Submission.Work.FTS.CoercivityFix.StepAssembly.H1IP_congr_qd
import Submission.Work.FTS.CoercivityFix.Transfer.H1IP_add_weak

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

set_option autoImplicit false

/-! ## Locality and linearity of the two derivatives on the open quadrant -/

/-- Two functions that agree on the open quadrant have the same `D_θ` there (the derivative is
local and `Qd` is open in the `θ`-variable). -/
theorem Dth_congr_Qd {f f' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  intro z θ hzθ
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have heq : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => f' z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h z θ' ⟨hzθ.1, hθ'⟩
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [heq.deriv_eq]

/-- Two functions that agree on the open quadrant have the same `D_z` there. -/
theorem Dz_congr_Qd {f f' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (0 : ℝ) := hzθ.1
  have heq : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => f' z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' θ ⟨hz', hzθ.2⟩
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [heq.deriv_eq]

/-- The `(a,b) = (1,0)` block of `BlocksAdd`: `D_θ` is additive on the open quadrant. -/
theorem Dth_add_of_blocksAdd {k : ℕ} {f₁ f₂ : Fn}
    (h : Work.FTS.CoercivityFix.Assembly.BlocksAdd k f₁ f₂) (hk : 1 ≤ k) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (f₁ + f₂) z θ
        = (Work.Spaces.Dth f₁ + Work.Spaces.Dth f₂) z θ := by
  intro z θ hzθ
  have h0 := h 1 0 hk z θ hzθ
  simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
    Pi.add_apply] using h0

/-- The `(a,b) = (0,1)` block of `BlocksAdd`: `D_z` is additive on the open quadrant. -/
theorem Dz_add_of_blocksAdd {k : ℕ} {f₁ f₂ : Fn}
    (h : Work.FTS.CoercivityFix.Assembly.BlocksAdd k f₁ f₂) (hk : 1 ≤ k) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (f₁ + f₂) z θ
        = (Work.Spaces.Dz f₁ + Work.Spaces.Dz f₂) z θ := by
  intro z θ hzθ
  have h0 := h 0 1 hk z θ hzθ
  simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Pi.add_apply] using h0

/-! ## The open-class additivity package -/

/-- **The open-class additivity package at level `n`.**  `IP` is the `n`-fold `HkIPStep`
iterate above `H1IP`; the `add` clause takes the interior class `SmoothOpen` and the honesty
`HkMem α (n+1)` — the level at which the pairing `IP (f₁+f₂) g` is consumed. -/
structure Comm2o (α : ℝ) (n : ℕ) (IP : Fn → Fn → ℝ) : Prop where
  /-- congruence in the first argument on the open quadrant, with no membership -/
  congr : ∀ f f' g : Fn,
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP f g = IP f' g
  /-- additivity in the first argument on the open class -/
  add : ∀ f₁ f₂ g : Fn, Work.FTS.EllipticEst.SmoothOpen f₁ →
    Work.FTS.EllipticEst.SmoothOpen f₂ → Work.FTS.EllipticEst.SmoothOpen g →
    Work.Spaces.HkMem α (n + 1) f₁ → Work.Spaces.HkMem α (n + 1) f₂ →
    Work.Spaces.HkMem α (n + 1) g → IP (f₁ + f₂) g = IP f₁ g + IP f₂ g

/-- **The base case**: additivity of `H1IP` on the open class, which is
`Transfer.H1IP_add_weak` with the block hypotheses discharged by
`BlocksCont_of_smoothOpen`/`BlocksAdd_of_smoothOpen`. -/
theorem Comm2o_zero (α : ℝ) :
    Comm2o α 0 (Work.Coercivity.H1IP α) := by
  refine ⟨fun f f' g h => Work.FTS.CoercivityFix.StepAssembly.H1IP_congr_qd α h, ?_⟩
  intro f₁ f₂ g hf₁ hf₂ hg hm₁ hm₂ hmg
  have hbadd : Work.FTS.CoercivityFix.Assembly.BlocksAdd 1 f₁ f₂ :=
    (BlocksAdd_of_smoothOpen hf₁ hf₂ : Work.FTS.CoercivityFix.Assembly.BlocksAdd 1 f₁ f₂)
  exact Work.FTS.CoercivityFix.Transfer.H1IP_add_weak α hm₁ hm₂ hmg
    (hf₁.continuousOn) (hf₂.continuousOn) (hg.continuousOn)
    ((Work.FTS.EllipticEst.SmoothOpen.Dz hf₁).continuousOn)
    ((Work.FTS.EllipticEst.SmoothOpen.Dz hf₂).continuousOn)
    ((Work.FTS.EllipticEst.SmoothOpen.Dz hg).continuousOn)
    ((Work.FTS.EllipticEst.SmoothOpen.Dth hf₁).continuousOn)
    ((Work.FTS.EllipticEst.SmoothOpen.Dth hf₂).continuousOn)
    ((Work.FTS.EllipticEst.SmoothOpen.Dth hg).continuousOn)
    (Dz_add_of_blocksAdd hbadd (le_refl 1)) (Dth_add_of_blocksAdd hbadd (le_refl 1))

/-- **The induction step**: `Comm2o` climbs one level under `HkIPStep c₁ c₂`, the descent of
the honesty and of the block packages being supplied by the interior smoothness of the
arguments (`IPGen/OpenBasic.lean`). -/
theorem Comm2o_succ (α : ℝ) (hα : -(1 / 10 : ℝ) ≤ α) (n : ℕ)
    {IP : Fn → Fn → ℝ} {c₁ c₂ : ℝ} (hc : Comm2o α n IP) :
    Comm2o α (n + 1) (Work.Coercivity.HkIPStep c₁ c₂ IP) := by
  have h1n : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  refine ⟨?_, ?_⟩
  · intro f f' g hfg
    have e0 := hc.congr f f' g hfg
    have e1 := hc.congr (Work.Spaces.Dth f) (Work.Spaces.Dth f') (Work.Spaces.Dth g)
      (Dth_congr_Qd hfg)
    have e2 := hc.congr (Work.Spaces.Dz f) (Work.Spaces.Dz f') (Work.Spaces.Dz g)
      (Dz_congr_Qd hfg)
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
  · intro f₁ f₂ g hf₁ hf₂ hg hm₁ hm₂ hmg
    -- descent of the honesty from level `n+2` to level `n+1`
    obtain ⟨hm₁', hmth₁, hmz₁⟩ := HkMem_descent hα hf₁ hm₁
    obtain ⟨hm₂', hmth₂, hmz₂⟩ := HkMem_descent hα hf₂ hm₂
    obtain ⟨hmg', hmthg, hmzg⟩ := HkMem_descent hα hg hmg
    have hsf₁ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth f₁) :=
      Work.FTS.EllipticEst.SmoothOpen.Dth hf₁
    have hsf₂ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth f₂) :=
      Work.FTS.EllipticEst.SmoothOpen.Dth hf₂
    have hsg : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth g) :=
      Work.FTS.EllipticEst.SmoothOpen.Dth hg
    have hzf₁ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz f₁) :=
      Work.FTS.EllipticEst.SmoothOpen.Dz hf₁
    have hzf₂ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz f₂) :=
      Work.FTS.EllipticEst.SmoothOpen.Dz hf₂
    have hzg : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) :=
      Work.FTS.EllipticEst.SmoothOpen.Dz hg
    have hbadd : Work.FTS.CoercivityFix.Assembly.BlocksAdd (n + 1) f₁ f₂ :=
      (BlocksAdd_of_smoothOpen hf₁ hf₂ : Work.FTS.CoercivityFix.Assembly.BlocksAdd (n + 1) f₁ f₂)
    have e0 := hc.add f₁ f₂ g hf₁ hf₂ hg hm₁' hm₂' hmg'
    have e1 : IP (Work.Spaces.Dth (f₁ + f₂)) (Work.Spaces.Dth g)
        = IP (Work.Spaces.Dth f₁) (Work.Spaces.Dth g)
          + IP (Work.Spaces.Dth f₂) (Work.Spaces.Dth g) := by
      rw [hc.congr (Work.Spaces.Dth (f₁ + f₂))
        (Work.Spaces.Dth f₁ + Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        (Dth_add_of_blocksAdd hbadd h1n)]
      exact hc.add (Work.Spaces.Dth f₁) (Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        hsf₁ hsf₂ hsg hmth₁ hmth₂ hmthg
    have e2 : IP (Work.Spaces.Dz (f₁ + f₂)) (Work.Spaces.Dz g)
        = IP (Work.Spaces.Dz f₁) (Work.Spaces.Dz g)
          + IP (Work.Spaces.Dz f₂) (Work.Spaces.Dz g) := by
      rw [hc.congr (Work.Spaces.Dz (f₁ + f₂))
        (Work.Spaces.Dz f₁ + Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        (Dz_add_of_blocksAdd hbadd h1n)]
      exact hc.add (Work.Spaces.Dz f₁) (Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        hzf₁ hzf₂ hzg hmz₁ hmz₂ hmzg
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
    ring

/-! ## The three levels up to `IP4` -/

theorem Comm2o_one (α : ℝ) (hα : -(1 / 10 : ℝ) ≤ α) {c₁ c₂ : ℝ} :
    Comm2o α 1 (Work.FTS.CoercivityFix.Assembly.IP2 c₁ c₂ α) :=
  Comm2o_succ α hα 0 (Comm2o_zero α)

theorem Comm2o_two (α : ℝ) (hα : -(1 / 10 : ℝ) ≤ α) {c₁ c₂ c₁' c₂' : ℝ} :
    Comm2o α 2 (Work.FTS.CoercivityFix.Assembly.IP3 c₁ c₂ c₁' c₂' α) :=
  Comm2o_succ α hα 1 (Comm2o_one α hα)

theorem Comm2o_three (α : ℝ) (hα : -(1 / 10 : ℝ) ≤ α) {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} :
    Comm2o α 3 (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α) :=
  Comm2o_succ α hα 2 (Comm2o_two α hα)

/-- **Additivity of the coercive `IP4` on the open class `HQo α 4`** — the `add` clause of the
corrected contract `N4ExtraQ`. -/
theorem ip4_add_HQo {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} :
    ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn,
      Work.FTS.VocabO.HQo α 4 f₁ → Work.FTS.VocabO.HQo α 4 f₂ → Work.FTS.VocabO.HQo α 4 g →
      Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (f₁ + f₂) g
        = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₁ g
          + Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₂ g := by
  refine ⟨1, one_pos, ?_⟩
  intro α hα f₁ f₂ g h₁ h₂ h₃
  exact (Comm2o_three α (by linarith [hα.1])).add f₁ f₂ g h₁.1 h₂.1 h₃.1 h₁.2 h₂.2 h₃.2

/-- **Congruence of `IP4` in its first argument on the open quadrant**, with no membership at
all: the `congr` clause of the `Comm2`-package for `IP4` (`Assembly.Comm2_levels`). -/
theorem ip4_congr_Qd {c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ} (hα : 0 < α) {f f' g : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g
      = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f' g :=
  (Work.FTS.CoercivityFix.Assembly.Comm2_levels α hα).2.2.congr f f' g h

end Work.FTS.IPGen
