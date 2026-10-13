import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2_levels
import Submission.Work.FTS.CoercivityFix.Assembly.H1IP_core_Q
import Submission.Work.Coercivity.H1IP_nonneg
import Submission.Work.Coercivity.H1IP_homog
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Assembly/V_core.lean` — the five algebraic clauses of `IP4`

`IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α` is the paper's recursion
`HkIPStep c₁'' c₂'' (HkIPStep c₁' c₂' (HkIPStep c₁ c₂ (H1IP α)))` of `Assembly/Defs.lean`.
This file delivers the five *level-`4`* clauses of the corrected obligation
`Work.FTS.Nonlin.UnifIP` (`Submission/Work/FTS/Vocab.lean`) for it:

* **symmetry** for all profiles `(f,g)` (no membership): `H1IP` is symmetric because the
  integrand is literally symmetric in its two arguments, and `HkIPStep` inherits symmetry
  with no hypothesis at all (`vc_symm`);
* **additivity** and **congruence on the open quadrant** on the class `RegQ α 4`, which are
  the `add` / `congr` clauses of `Assembly.Comm2 α 4 (IP4 ...)` (`Comm2_levels`, built from
  the base `H1IP_core_Q` through three applications of `Comm2_succ`);
* **homogeneity** in the first argument for all profiles (no membership): `D_θ` and `D_z`
  are scalar homogeneous *unconditionally* (`Work.Coercivity.Dth_smul`, `Dz_smul`), and
  `H1IP` is unconditionally homogeneous (`Work.Coercivity.H1IP_homog`), so `HkIPStep`
  inherits homogeneity (`vc_smul`);
* **nonnegativity of the diagonal** for all profiles, from the pointwise nonnegativity of
  `H1IP`'s integrand (`Work.Coercivity.H1IP_nonneg`) and the nonnegativity of the step
  coefficients (`vc_nonneg`).
-/

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)

/-! ## The three clauses inherited by the recursion `HkIPStep c₁ c₂` -/

/-- **Symmetry is inherited by the recursion.**  If `IP` is symmetric then so is
`HkIPStep c₁ c₂ IP`: the three summands are `IP f g`, `IP (D_θ f) (D_θ g)` and
`IP (D_z f) (D_z g)`, and each is symmetric by hypothesis.  No regularity is needed. -/
theorem vc_symm {c₁ c₂ : ℝ} {IP : Fn → Fn → ℝ} (h : ∀ f g : Fn, IP f g = IP g f) :
    ∀ f g : Fn, Work.Coercivity.HkIPStep c₁ c₂ IP f g
      = Work.Coercivity.HkIPStep c₁ c₂ IP g f := by
  intro f g
  simp only [Work.Coercivity.HkIPStep, h f g,
    h (Work.Spaces.Dth f) (Work.Spaces.Dth g), h (Work.Spaces.Dz f) (Work.Spaces.Dz g)]

/-- **Homogeneity in the first argument is inherited by the recursion.**  The two inner
pairings see the derivatives of `fun z θ => c * f z θ`, and `D_θ`, `D_z` commute
unconditionally with scalar multiplication (`Work.Coercivity.Dth_smul`, `Dz_smul`). -/
theorem vc_smul {c₁ c₂ c : ℝ} {IP : Fn → Fn → ℝ}
    (h : ∀ u v : Fn, IP (fun z θ => c * u z θ) v = c * IP u v) :
    ∀ f g : Fn, Work.Coercivity.HkIPStep c₁ c₂ IP (fun z θ => c * f z θ) g
      = c * Work.Coercivity.HkIPStep c₁ c₂ IP f g := by
  intro f g
  simp only [Work.Coercivity.HkIPStep]
  rw [Work.Coercivity.Dth_smul, Work.Coercivity.Dz_smul, h f g,
    h (Work.Spaces.Dth f) (Work.Spaces.Dth g), h (Work.Spaces.Dz f) (Work.Spaces.Dz g)]
  ring

/-- **Nonnegativity of the diagonal is inherited by the recursion**, with nonnegative step
coefficients: the three summands are `IP f f`, `c₁·IP (D_θ f) (D_θ f)` and
`c₂·IP (D_z f) (D_z f)`. -/
theorem vc_nonneg {c₁ c₂ : ℝ} (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) {IP : Fn → Fn → ℝ}
    (h : ∀ u : Fn, 0 ≤ IP u u) :
    ∀ f : Fn, 0 ≤ Work.Coercivity.HkIPStep c₁ c₂ IP f f := by
  intro f
  have h0 : 0 ≤ IP f f := h f
  have h1 : 0 ≤ IP (Work.Spaces.Dth f) (Work.Spaces.Dth f) := h _
  have h2 : 0 ≤ IP (Work.Spaces.Dz f) (Work.Spaces.Dz f) := h _
  have hm1 : 0 ≤ c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth f) := mul_nonneg h₁ h1
  have hm2 : 0 ≤ c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz f) := mul_nonneg h₂ h2
  simp only [Work.Coercivity.HkIPStep]
  linarith

/-! ## The five clauses of `IP4` -/

theorem V_core {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ}
    (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (h₁' : 0 ≤ c₁') (h₂' : 0 ≤ c₂')
    (h₁'' : 0 ≤ c₁'') (h₂'' : 0 ≤ c₂'') :
    (∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
        Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g
          = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α g f) ∧
    (∀ (α : ℝ), 0 < α → ∀ (f₁ f₂ g : ℝ → ℝ → ℝ),
        Work.FTS.Nonlin.RegQ α 4 f₁ → Work.FTS.Nonlin.RegQ α 4 f₂ →
        Work.FTS.Nonlin.RegQ α 4 g →
        Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (f₁ + f₂) g
          = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₁ g
            + Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₂ g) ∧
    (∀ (α : ℝ), 0 < α → ∀ (c : ℝ) (f g : ℝ → ℝ → ℝ),
        Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
        Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (fun z θ => c * f z θ) g
          = c * Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g) ∧
    (∀ (α : ℝ), 0 < α → ∀ (f f' g : ℝ → ℝ → ℝ),
        Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
        (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) →
        Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g
          = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f' g) ∧
    (∀ (α : ℝ), 0 < α → ∀ (f : ℝ → ℝ → ℝ), Work.FTS.Nonlin.RegQ α 4 f →
        0 ≤ Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f) := by
  -- Symmetry, by three applications of `vc_symm` from the base `H1IP_comm`.
  have hsymm : ∀ (α : ℝ) (f g : Fn),
      IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α g f := by
    intro α
    exact vc_symm (c₁ := c₁'') (c₂ := c₂'') (vc_symm (c₁ := c₁') (c₂ := c₂')
      (vc_symm (c₁ := c₁) (c₂ := c₂) (fun f g => H1IP_comm α f g)))
  -- Homogeneity, by three applications of `vc_smul` from `H1IP_homog`; the regularity
  -- hypotheses of the clause are not needed and are discarded.
  have hsmul : ∀ (α : ℝ), 0 < α → ∀ (c : ℝ) (f g : Fn),
      Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
      IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (fun z θ => c * f z θ) g
        = c * IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g := by
    intro α _hα c f g _ _
    exact (vc_smul (c₁ := c₁'') (c₂ := c₂'') (vc_smul (c₁ := c₁') (c₂ := c₂')
      (vc_smul (c₁ := c₁) (c₂ := c₂)
        (fun u v => Work.Coercivity.H1IP_homog α c u v)))) f g
  -- Nonnegativity, by three applications of `vc_nonneg` from `H1IP_nonneg`; again the
  -- regularity hypothesis is not needed.
  have hnonneg : ∀ (α : ℝ), 0 < α → ∀ f : Fn, Work.FTS.Nonlin.RegQ α 4 f →
      0 ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f f := by
    intro α _hα f _
    exact (vc_nonneg h₁'' h₂'' (vc_nonneg h₁' h₂' (vc_nonneg h₁ h₂
      (fun u => Work.Coercivity.H1IP_nonneg α u)))) f
  refine ⟨hsymm, ?_, hsmul, ?_, hnonneg⟩
  · intro α hα f₁ f₂ g hf₁ hf₂ hg
    exact (Comm2_levels α hα).2.2.add f₁ f₂ g hf₁ hf₂ hg
  · intro α hα f f' g hf hg hfg
    exact (Comm2_levels α hα).2.2.congr f f' g hfg

end Work.FTS.CoercivityFix.Assembly
