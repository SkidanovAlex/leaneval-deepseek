/-
Copyright: work module for the Elgindi finite-time singularity project.

# `dthU_pow_Gam_sharp`: the sharp angular bound for the jet of `Γ`

The paper's angular weight is `Γ(θ) = (sin θ · cos²θ)^{α/3}` and `D_θ = sin(2θ)∂_θ`.  We prove
that there is a universal constant `C` with

  `|D_θ^m Γ(θ)| ≤ C · α · Γ(θ) · (α + sin 2θ)`

for every `0 < α ≤ 1`, every `θ ∈ Iθ = [0, π/2]` and every `2 ≤ m ≤ 5`.

The point of the factor `α + sin 2θ` is that the right-hand side is small near the two
endpoints `θ = 0`, `θ = π/2` (where `Γ` itself vanishes), which is what the applications
(weighted `ℋ^k`-estimates) need; the crude bound `|D_θ^m Γ| ≤ C α Γ` is far too lossy there.

## Route

`Work.Spaces.dthU_iter_Gam` identifies the angular jet on the open interval,

  `D_θ^{j+1} Γ = α · Tfun j α · Γ`   on `(0, π/2)`,

and `Γ ≥ 0` on `Iθ`, so the claim is the *uniform in α* bound

  `|Tfun j α θ| ≤ C · (α + sin 2θ)`,   `θ ∈ Iθ`,   `j ≤ 4`.

Since `Tfun 0 = qfun` and `Tfun (j+1) α = dthU (Tfun j α) + α · qfun · Tfun j α`
(`Tfun_succ`), we run the induction `Hyp j` of `GamSharpAux.lean`, which controls every
`dthU`-iterate of `Tfun j α` down to order `4 - j` by `KB j · (α + sin 2θ)`:

* the base case `Hyp 1` uses `Tfun 1 α = dthU qfun + α · qfun²` and the crude bounds
  `|dthU^i qfun| ≤ 1000` (`i ≤ 4`) of `DthQfunBound` / `abs_qfun_le` for the `α`-weighted
  Leibniz corrections, together with the endpoint-vanishing bound
  `|dthU^{k+1} qfun θ| ≤ 1000 sin 2θ` of `GamSharpAux.dthU_qfun_le_sin`;
* the induction step `Hyp j → Hyp (j+1)` (`j ≤ 3`) differentiates the recursion once and
  controls the Leibniz corrections `dthU^k (α qfun · Tfun j α)` by
  `GamSharpAux.alpha_qfun_leibniz_abs_le` against the hypothesis at the lower orders;
* the constants close geometrically: `KB (j+1) = 20000 · KB j ≥ 16001 · KB j`.

At the endpoints `θ = 0`, `θ = π/2` the left-hand side vanishes identically because
`sin 2θ = 0` (`dthU_iter_eq_zero_of_sin_eq_zero'`), and the right-hand side is non-negative.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The base case of the induction -/

/-- `Hyp 1`: all `dthU`-iterates of `Tfun 1 α` of order `≤ 3` are `O(α + sin 2θ)`. -/
lemma Hyp_one : Hyp 1 := by
  intro α θ hα hα1 hθ k hk
  have hk3 : k ≤ 3 := by omega
  have hk4 : k ≤ 4 := by omega
  have h0 : (fun t : ℝ => Work.Spaces.Tfun 0 α t) = Work.Spaces.qfun := by
    funext t; rw [Work.Spaces.Tfun_zero]
  have hT : Work.Spaces.Tfun 1 α = Work.Spaces.dthU Work.Spaces.qfun
      + (fun θ => α * Work.Spaces.qfun θ) * Work.Spaces.qfun := by
    funext t
    rw [Work.Spaces.Tfun_succ, h0, Work.Spaces.Tfun_zero]
    simp only [Work.Spaces.dthU_apply, Pi.add_apply, Pi.mul_apply]
  have hf : ContDiff ℝ (⊤ : ℕ∞) (Work.Spaces.dthU Work.Spaces.qfun) :=
    Work.Spaces.dthU_smooth Work.Spaces.qfun_smooth
  have hfα : ContDiff ℝ (⊤ : ℕ∞) (fun θ => α * Work.Spaces.qfun θ) :=
    contDiff_const.mul Work.Spaces.qfun_smooth
  have hg : ContDiff ℝ (⊤ : ℕ∞)
      ((fun θ => α * Work.Spaces.qfun θ) * Work.Spaces.qfun) :=
    hfα.mul Work.Spaces.qfun_smooth
  have hval : Work.Spaces.dthU^[k] (Work.Spaces.Tfun 1 α) θ
      = Work.Spaces.dthU^[k + 1] Work.Spaces.qfun θ
        + ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
            * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
              * Work.Spaces.dthU^[k - i] Work.Spaces.qfun θ) := by
    rw [hT, Work.Spaces.dthU_iter_add k _ _ hf hg,
      Work.Spaces.dthU_iter_comp k Work.Spaces.qfun]
    simp only [Pi.add_apply]
    rw [dthU_iter_mul_apply k (fun θ => α * Work.Spaces.qfun θ) Work.Spaces.qfun hfα
      Work.Spaces.qfun_smooth θ]
  rw [hval]
  have hs := sinTwo_mem_Icc hθ
  have hαs : 0 ≤ α + Real.sin (2 * θ) := by linarith [hα, hs.1]
  have hA : |Work.Spaces.dthU^[k + 1] Work.Spaces.qfun θ|
      ≤ 1000 * (α + Real.sin (2 * θ)) := by
    have h1 := dthU_qfun_le_sin (i := k + 1) (by omega) (by omega) hθ
    have h2 : Real.sin (2 * θ) ≤ α + Real.sin (2 * θ) := by linarith [hα]
    linarith [h1, h2]
  have hQ : ∀ m : ℕ, m ≤ k → |Work.Spaces.dthU^[m] Work.Spaces.qfun θ| ≤ 1000 :=
    fun m hm => qfun_iter_abs_le (by omega) hθ
  have hB := alpha_qfun_leibniz_abs_le k hk4 hα hθ (Q := Work.Spaces.qfun) (KX := 1000) hQ
  have hkey : 1000 * (α + Real.sin (2 * θ)) + 16000 * α * 1000
      ≤ 17001000 * (α + Real.sin (2 * θ)) := by
    have h2 : 16000 * α * 1000 ≤ 16000 * 1000 * (α + Real.sin (2 * θ)) := by
      have h0 : (0 : ℝ) ≤ 16000 * 1000 := by norm_num
      calc 16000 * α * 1000 = (16000 * 1000) * α := by ring
        _ ≤ (16000 * 1000) * (α + Real.sin (2 * θ)) :=
              mul_le_mul_of_nonneg_left (by linarith [hα, hs.1]) h0
    linarith [h2]
  have hfin : (17001000 : ℝ) * (α + Real.sin (2 * θ))
      ≤ KB 1 * (α + Real.sin (2 * θ)) :=
    mul_le_mul_of_nonneg_right KB_one_ge hαs
  calc |Work.Spaces.dthU^[k + 1] Work.Spaces.qfun θ
        + ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
            * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
              * Work.Spaces.dthU^[k - i] Work.Spaces.qfun θ)|
      ≤ |Work.Spaces.dthU^[k + 1] Work.Spaces.qfun θ|
        + |∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
            * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
              * Work.Spaces.dthU^[k - i] Work.Spaces.qfun θ)| := abs_add_le _ _
    _ ≤ 1000 * (α + Real.sin (2 * θ)) + 16000 * α * 1000 := add_le_add hA hB
    _ ≤ KB 1 * (α + Real.sin (2 * θ)) := le_trans hkey hfin

/-! ## The induction step -/

/-- `Hyp j → Hyp (j+1)` for `1 ≤ j ≤ 3`: differentiate the recursion
`Tfun (j+1) α = dthU (Tfun j α) + α qfun Tfun j α` `k` times and apply the Leibniz rule. -/
lemma Hyp_succ (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) (h : Hyp j) : Hyp (j + 1) := by
  intro α θ hα hα1 hθ k hk
  have hk3 : k ≤ 3 := by omega
  have hk4 : k ≤ 4 := by omega
  have hk1 : k + 1 ≤ 4 - j := by omega
  have hT : Work.Spaces.Tfun (j + 1) α = Work.Spaces.dthU (Work.Spaces.Tfun j α)
      + (fun θ => α * Work.Spaces.qfun θ) * Work.Spaces.Tfun j α := by
    funext t
    rw [Work.Spaces.Tfun_succ]
    simp only [Work.Spaces.dthU_apply, Pi.add_apply, Pi.mul_apply]
  have hf : ContDiff ℝ (⊤ : ℕ∞) (Work.Spaces.dthU (Work.Spaces.Tfun j α)) :=
    Work.Spaces.dthU_smooth (Work.Spaces.Tfun_smooth j α)
  have hfα : ContDiff ℝ (⊤ : ℕ∞) (fun θ => α * Work.Spaces.qfun θ) :=
    contDiff_const.mul Work.Spaces.qfun_smooth
  have hg : ContDiff ℝ (⊤ : ℕ∞)
      ((fun θ => α * Work.Spaces.qfun θ) * Work.Spaces.Tfun j α) :=
    hfα.mul (Work.Spaces.Tfun_smooth j α)
  have hval : Work.Spaces.dthU^[k] (Work.Spaces.Tfun (j + 1) α) θ
      = Work.Spaces.dthU^[k + 1] (Work.Spaces.Tfun j α) θ
        + ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
            * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
              * Work.Spaces.dthU^[k - i] (Work.Spaces.Tfun j α) θ) := by
    rw [hT, Work.Spaces.dthU_iter_add k _ _ hf hg,
      Work.Spaces.dthU_iter_comp k (Work.Spaces.Tfun j α)]
    simp only [Pi.add_apply]
    rw [dthU_iter_mul_apply k (fun θ => α * Work.Spaces.qfun θ) (Work.Spaces.Tfun j α) hfα
      (Work.Spaces.Tfun_smooth j α) θ]
  rw [hval]
  have hs := sinTwo_mem_Icc hθ
  have hαs : 0 ≤ α + Real.sin (2 * θ) := by linarith [hα, hs.1]
  have hKBj : 0 ≤ KB j := (KB_pos j).le
  have hA : |Work.Spaces.dthU^[k + 1] (Work.Spaces.Tfun j α) θ|
      ≤ KB j * (α + Real.sin (2 * θ)) := h α θ hα hα1 hθ (k + 1) hk1
  have hQ : ∀ m : ℕ, m ≤ k → |Work.Spaces.dthU^[m] (Work.Spaces.Tfun j α) θ|
      ≤ KB j * (α + Real.sin (2 * θ)) := fun m hm => h α θ hα hα1 hθ m (by omega)
  have hB := alpha_qfun_leibniz_abs_le k hk4 hα hθ
    (Q := Work.Spaces.Tfun j α) (KX := KB j * (α + Real.sin (2 * θ))) hQ
  have hkey : KB j * (α + Real.sin (2 * θ))
        + 16000 * α * (KB j * (α + Real.sin (2 * θ)))
      ≤ 16001 * (KB j * (α + Real.sin (2 * θ))) := by
    have h2 : 16000 * α * (KB j * (α + Real.sin (2 * θ)))
        ≤ 16000 * (KB j * (α + Real.sin (2 * θ))) := by
      have h0 : (0 : ℝ) ≤ 16000 * (KB j * (α + Real.sin (2 * θ))) := by positivity
      calc 16000 * α * (KB j * (α + Real.sin (2 * θ)))
          = (16000 * (KB j * (α + Real.sin (2 * θ)))) * α := by ring
        _ ≤ (16000 * (KB j * (α + Real.sin (2 * θ)))) * 1 :=
              mul_le_mul_of_nonneg_left hα1 h0
        _ = 16000 * (KB j * (α + Real.sin (2 * θ))) := by ring
    linarith [h2]
  have hfin : (16001 : ℝ) * (KB j * (α + Real.sin (2 * θ)))
      ≤ KB (j + 1) * (α + Real.sin (2 * θ)) := by
    rw [KB_succ]
    have hmul : 0 ≤ KB j * (α + Real.sin (2 * θ)) := mul_nonneg hKBj hαs
    nlinarith [hmul]
  calc |Work.Spaces.dthU^[k + 1] (Work.Spaces.Tfun j α) θ
        + ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
            * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
              * Work.Spaces.dthU^[k - i] (Work.Spaces.Tfun j α) θ)|
      ≤ |Work.Spaces.dthU^[k + 1] (Work.Spaces.Tfun j α) θ|
        + |∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
            * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
              * Work.Spaces.dthU^[k - i] (Work.Spaces.Tfun j α) θ)| := abs_add_le _ _
    _ ≤ KB j * (α + Real.sin (2 * θ)) + 16000 * α * (KB j * (α + Real.sin (2 * θ))) :=
        add_le_add hA hB
    _ ≤ KB (j + 1) * (α + Real.sin (2 * θ)) := le_trans hkey hfin

/-! ## The target lemma -/

theorem dthU_pow_Gam_sharp :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ, ∀ m : ℕ,
      2 ≤ m → m ≤ 5 →
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        ≤ C * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by
  refine ⟨KB 4, KB_pos 4, ?_⟩
  intro α hα hα1 θ hθ m hm2 hm5
  have h1 : Hyp 1 := Hyp_one
  have h2 : Hyp 2 := Hyp_succ 1 le_rfl (by norm_num) h1
  have h3 : Hyp 3 := Hyp_succ 2 (by norm_num) (by norm_num) h2
  have h4 : Hyp 4 := Hyp_succ 3 (by norm_num) (by norm_num) h3
  have hm1 : 1 ≤ m - 1 := by omega
  have hm1' : 1 ≤ m := by omega
  have hmle : m - 1 ≤ 4 := by omega
  have hsel : Hyp (m - 1) := by
    have hmc : m - 1 = 1 ∨ m - 1 = 2 ∨ m - 1 = 3 ∨ m - 1 = 4 := by omega
    rcases hmc with hmc | hmc | hmc | hmc <;> rw [hmc]
    exacts [h1, h2, h3, h4]
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hs := sinTwo_mem_Icc hθ
  rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
  · rcases lt_or_eq_of_le hθ.2 with hθ1 | hθ1
    · -- interior of `Iθ`: use the jet identity and `Hyp (m-1)`
      have hid := Work.Spaces.dthU_iter_Gam (m - 1) α hα
        (show θ ∈ Set.Ioo 0 (Real.pi / 2) from ⟨hθ0, hθ1⟩)
      rw [show m - 1 + 1 = m from by omega] at hid
      have hT : |Work.Spaces.Tfun (m - 1) α θ|
          ≤ KB (m - 1) * (α + Real.sin (2 * θ)) := hsel α θ hα hα1 hθ 0 (by omega)
      have hKB : KB (m - 1) ≤ KB 4 := KB_mono hmle
      have hαs : 0 ≤ α + Real.sin (2 * θ) := by linarith [hα, hs.1]
      have hb : |α * Work.Spaces.Tfun (m - 1) α θ * Work.Spaces.Gam α θ|
          = α * |Work.Spaces.Tfun (m - 1) α θ| * Work.Spaces.Gam α θ := by
        rw [abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hGam0]
      rw [hid, hb]
      have hmul : α * (KB (m - 1) * (α + Real.sin (2 * θ)))
          ≤ α * (KB 4 * (α + Real.sin (2 * θ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKB hαs) hα.le
      calc α * |Work.Spaces.Tfun (m - 1) α θ| * Work.Spaces.Gam α θ
          ≤ α * (KB (m - 1) * (α + Real.sin (2 * θ))) * Work.Spaces.Gam α θ := by
            apply mul_le_mul_of_nonneg_right _ hGam0
            exact mul_le_mul_of_nonneg_left hT hα.le
        _ ≤ KB 4 * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by
            calc α * (KB (m - 1) * (α + Real.sin (2 * θ))) * Work.Spaces.Gam α θ
                ≤ (α * (KB 4 * (α + Real.sin (2 * θ)))) * Work.Spaces.Gam α θ :=
                  mul_le_mul_of_nonneg_right hmul hGam0
              _ = KB 4 * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by ring
    · -- `θ = π/2`
      subst hθ1
      rw [Work.Spaces.dthU_iter_eq_zero_of_sin_eq_zero' (fun t => Work.Spaces.Gam α t) hm1'
            (by rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]), abs_zero]
      have hsin : 0 ≤ Real.sin (2 * (Real.pi / 2)) := by
        rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
      exact mul_nonneg (mul_nonneg (mul_nonneg (KB_pos 4).le hα.le) hGam0)
        (by linarith [hα, hsin])
  · -- `θ = 0`
    subst hθ0
    rw [Work.Spaces.dthU_iter_eq_zero_of_sin_eq_zero' (fun t => Work.Spaces.Gam α t) hm1'
          (by simp only [mul_zero, Real.sin_zero]), abs_zero]
    have hsin : 0 ≤ Real.sin (2 * (0 : ℝ)) := by simp only [mul_zero, Real.sin_zero, le_refl]
    exact mul_nonneg (mul_nonneg (mul_nonneg (KB_pos 4).le hα.le) hGam0)
      (by linarith [hα, hsin])

end Work.FTS.Nonlinear.Pieces.RNP
