/-
Copyright: work module for the Elgindi finite-time singularity project.

# `DthFstar_W`: the `𝒲^{4,∞}`-bound for `D_θ F_*`

This proves the design statement `DthFstar_W` of `FTS/N45_DESIGN_LEAD.md` §3.2 (one row of
the `F_*`-package of `Submission/Work/FTS/Nonlinear/NOTES_N4.md`):

  `𝒲^{4,∞}(D_θ F_*) ≤ C α²`, with `C` universal, for every `0 < α ≤ 1`,

where `F_*(z,θ) = α (Γ(θ)/c) · 2z/(1+z)²` is the profile of `Work.Construction.Fstar`
(paper tex 1334) and `Γ(θ) = (sin θ cos²θ)^{α/3}`.

## Mathematics

Writing `F_* = (2α/c) · Γ ⊗ hKer` (with `hKer z = z/(1+z)²`, so `FM.Fstar = 2·hKer`), the
angular operator `D_θ = sin(2θ)∂_θ` acts only on `Γ`, while `∂_z` acts only on `hKer`:

  `∂_z^k (D_θ^{j+1} F_*)(z,θ) = (2α/c) · hKer^{(k)}(z) · D_θ^{j+1}Γ(θ)`
  (`FstarDthFactor`).

So the `𝒲^{4,∞}`-summands factorize into a radial part `(z+1)^k hKer^{(k)}(z)`, bounded by
`k!(k+1)` (`pzIter_hKer_bound`), a constant `|2α/c| ≤ 20α` (`c ≥ 1/10`, `c_bounds`), and an
angular part.  For the `z`-derivative summands the angular part is `|D_θ Γ| ≤ α tBound 0 0`
(`dthU_Gam_le`), which already gives `O(α²)`.  For the mixed summands the angular part is
`|D_θ^{j+1}Γ| · sin(2θ)^{-α/5}/(α + sin 2θ)` with `2 ≤ j+1 ≤ 5`, and the pointwise bound

  `|D_θ^m Γ(θ)| · sin(2θ)^{-α/5}/(α + sin 2θ) ≤ K α`,   `2 ≤ m ≤ 5`,

(`dthGamWeightLe`) is the heart of the proof.  The naive bound `|D_θ^mΓ| ≤ α tBound(m-1)0 · Γ`
(`dthU_Gam_le`) combined with `α Γ w ≤ 1` (`Gam_mul_weight_le`) only gives `O(1)`; the extra
factor `α` comes from the Leibniz expansion of `D_θ^{m+1}Γ = α D_θ^m(qΓ)` (`q = cos 2θ - 1/3`),
in which every summand acquires a second factor `α` that is absorbed by the weights:

* the `i = 0` summand is controlled by the induction hypothesis,
* the summands `1 ≤ i ≤ m-1` use `|D_θ^i q| ≤ 1000 sin²2θ` (`DthQfunBound`) against the crude
  bound `|D_θ^{m-i}Γ| ≤ α tBound(m-i-1)0 Γ` and the weight `α Γ w ≤ 1`,
* the summand `i = m` uses `sin²2θ · Γ w ≤ 1` (from `Γ ≤ sin(2θ)^{α/5}`).

All coefficients are made explicit (`TM`, `CM`, `Bstep`, `K2`--`K5`), so the final constant
`KD K + 1` is a concrete real number.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.FTS.Nonlinear.FstarPkg.GamSinRpowMulLeOne

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace DthAux

/-- The angular weight `sin(2θ)^{-α/5}/(α + sin 2θ)` of the `𝒲^{l,∞}`-norm. -/
noncomputable def Wt (α θ : ℝ) : ℝ :=
  (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))

lemma Wt_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Wt α θ :=
  Work.Spaces.gamma_weight_nonneg α θ hα hθ

lemma alpha_Gam_Wt_le_one {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    α * Work.Spaces.Gam α θ * Wt α θ ≤ 1 := by
  rw [Wt, ← mul_div_assoc]
  exact Work.Spaces.Gam_mul_weight_le α θ hα hθ

lemma sin_sq_Gam_Wt_le_one {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ * Wt α θ ≤ 1 := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : θ ≤ π/2 := hθ.2
  set s := Real.sin (2*θ) with hs
  have hs0 : 0 ≤ s := by
    rw [hs, Real.sin_two_mul]
    have h1 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [Real.pi_pos]⟩
    have h2 : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
    positivity
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hA : Work.Spaces.Gam α θ * (Real.sin (2*θ)) ^ (-(α / 5)) ≤ 1 :=
    GamSinRpowMulLeOne hα hα1 hθ
  have hden : 0 < α + s := by linarith
  have hnum : s^2 * (Work.Spaces.Gam α θ * (Real.sin (2*θ)) ^ (-(α / 5))) ≤ s^2 * 1 :=
    mul_le_mul_of_nonneg_left hA (sq_nonneg s)
  have hss : s^2 ≤ 1 := by
    rw [hs]
    have := Real.abs_sin_le_one (2*θ)
    nlinarith [sq_abs (Real.sin (2*θ)), abs_nonneg (Real.sin (2*θ))]
  have hkey : s^2 * Work.Spaces.Gam α θ * Wt α θ
      = s^2 * (Work.Spaces.Gam α θ * (Real.sin (2*θ)) ^ (-(α / 5))) / (α + s) := by
    rw [Wt, hs]
    ring
  rw [hkey, div_le_one hden]
  nlinarith [hnum, hss, hs0]

lemma abs_qfun_le (θ : ℝ) : |Work.Spaces.qfun θ| ≤ 4/3 := by
  rw [Work.Spaces.qfun]
  have h1 := Real.abs_cos_le_one (2*θ)
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

/-- `Γ(θ) = (sinθ·cos²θ)^{α/3}` is `C^∞` on the open interval `(0,π/2)`. -/
lemma contDiffOn_Gam_Ioo' (α : ℝ) :
    ContDiffOn ℝ ⊤ (fun θ => Work.Spaces.Gam α θ) (Set.Ioo 0 (π/2)) := by
  show ContDiffOn ℝ ⊤ (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
    (Set.Ioo 0 (π / 2))
  have hbase : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo 0 (π / 2)) :=
    (Real.contDiff_sin.contDiffOn).mul ((Real.contDiff_cos.contDiffOn).pow 2)
  refine hbase.rpow_const_of_ne (fun θ hθ => ?_)
  have h1 : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  positivity

/-! ## Locality of `dthU^m` and the Leibniz rule on the open interval -/

lemma dthU_iter_congr_open {U : Set ℝ} (hU : IsOpen U) :
    ∀ (m : ℕ) (f g : ℝ → ℝ), Set.EqOn f g U →
      Set.EqOn (Work.Spaces.dthU^[m] f) (Work.Spaces.dthU^[m] g) U := by
  intro m
  induction m with
  | zero => intro f g h; exact h
  | succ m ih =>
      intro f g h
      have hd : Set.EqOn (Work.Spaces.dthU f) (Work.Spaces.dthU g) U := by
        intro θ hθ
        rw [Work.Spaces.dthU_apply, Work.Spaces.dthU_apply]
        congr 1
        exact Filter.EventuallyEq.deriv_eq (h.eventuallyEq_of_mem (hU.mem_nhds hθ))
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih _ _ hd

lemma DthIter_rad (a : ℕ) (f : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter a (fun _ θ => f θ) z θ = Work.Spaces.dthU^[a] f θ := by
  have h := Work.Spaces.DthIter_decomp a f (fun _ : ℝ => (1:ℝ)) z θ
  simpa using h

lemma dthU_iter_mul_Ioo (m : ℕ) (f g : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π/2))
    (hf : ContDiffOn ℝ ⊤ f (Set.Ioo 0 (π/2))) (hg : ContDiffOn ℝ ⊤ g (Set.Ioo 0 (π/2))) :
    Work.Spaces.dthU^[m] (f * g) θ =
      ∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
        (Work.Spaces.dthU^[a] f θ * Work.Spaces.dthU^[m-a] g θ) := by
  have h := Work.Spaces.DthIter_mul m (fun _ θ => f θ) (fun _ θ => g θ) 0 (Set.Ioo 0 (π/2))
    isOpen_Ioo (by simpa using hf) (by simpa using hg) θ hθ
  have hfun : (fun (z : ℝ) (θ : ℝ) => f θ * g θ) = (fun (_ : ℝ) (θ : ℝ) => (f * g) θ) := rfl
  rw [hfun] at h
  simp only [DthIter_rad] at h
  exact h

lemma hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(Real.sin (2 * θ)) * 2) θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h := (Real.hasDerivAt_cos (2 * θ)).comp θ h2
  simpa [Function.comp_def] using h

lemma dthU_comp_cos (P : ℝ → ℝ) (θ : ℝ) (hP : DifferentiableAt ℝ P (Real.cos (2*θ))) :
    Work.Spaces.dthU (fun t => P (Real.cos (2*t))) θ
      = -2 * (1 - (Real.cos (2*θ))^2) * deriv P (Real.cos (2*θ)) := by
  rw [Work.Spaces.dthU_apply]
  have hcos := hasDerivAt_cos_two θ
  have hcomp : HasDerivAt (fun t : ℝ => P (Real.cos (2*t)))
      (deriv P (Real.cos (2*θ)) * (-(Real.sin (2*θ)) * 2)) θ := by
    have h := hP.hasDerivAt.comp θ hcos
    simpa [Function.comp_def] using h
  rw [hcomp.deriv]
  have hs : (Real.sin (2*θ))^2 = 1 - (Real.cos (2*θ))^2 := by
    have := Real.sin_sq_add_cos_sq (2*θ); linarith
  linear_combination (-2 * deriv P (Real.cos (2*θ))) * hs

lemma deriv_poly2 (c : ℝ) : deriv (fun c : ℝ => -2*(1-c^2)) c = 4*c := by
  have h : HasDerivAt (fun c : ℝ => -2*(1-c^2)) (4*c) c := by
    have h1 : HasDerivAt (fun c : ℝ => (1:ℝ) - c^2) (-(2*c)) c := by
      have hp : HasDerivAt (fun c : ℝ => c^2) (2*c^(2-1)) c := hasDerivAt_pow 2 c
      have hc : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 c := hasDerivAt_const c 1
      have := hc.sub hp
      convert this using 1 <;> ring
    have h2 := h1.const_mul (-2:ℝ)
    convert h2 using 1 <;> ring
  exact h.deriv

lemma deriv_poly3 (c : ℝ) : deriv (fun c : ℝ => -8*c*(1-c^2)) c = -8 + 24*c^2 := by
  have h : HasDerivAt (fun c : ℝ => -8*c*(1-c^2)) (-8 + 24*c^2) c := by
    have h1 : HasDerivAt (fun c : ℝ => (1:ℝ) - c^2) (-(2*c)) c := by
      have hp : HasDerivAt (fun c : ℝ => c^2) (2*c^(2-1)) c := hasDerivAt_pow 2 c
      have hc : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 c := hasDerivAt_const c 1
      have := hc.sub hp
      convert this using 1 <;> ring
    have ha : HasDerivAt (fun c : ℝ => -8*c) (-8) c := by
      have := (hasDerivAt_id c).const_mul (-8:ℝ)
      simpa using this
    have h2 := ha.mul h1
    convert h2 using 1 <;> ring
  exact h.deriv

lemma deriv_poly4 (c : ℝ) :
    deriv (fun c : ℝ => 16*(1-c^2)*(1-3*c^2)) c = 16*(-8*c + 12*c^3) := by
  have h : HasDerivAt (fun c : ℝ => 16*(1-c^2)*(1-3*c^2)) (16*(-8*c + 12*c^3)) c := by
    have h1 : HasDerivAt (fun c : ℝ => (1:ℝ) - c^2) (-(2*c)) c := by
      have hp : HasDerivAt (fun c : ℝ => c^2) (2*c^(2-1)) c := hasDerivAt_pow 2 c
      have hc : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 c := hasDerivAt_const c 1
      have := hc.sub hp
      convert this using 1 <;> ring
    have h3 : HasDerivAt (fun c : ℝ => (1:ℝ) - 3*c^2) (-(6*c)) c := by
      have hp : HasDerivAt (fun c : ℝ => 3*c^2) (3*(2*c^(2-1))) c :=
        (hasDerivAt_pow 2 c).const_mul 3
      have hc : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 c := hasDerivAt_const c 1
      have := hc.sub hp
      convert this using 1 <;> ring
    have ha : HasDerivAt (fun c : ℝ => 16*(1-c^2)) (16 * (-(2*c))) c := h1.const_mul 16
    have h2 := ha.mul h3
    convert h2 using 1 <;> ring
  exact h.deriv

-- the four iterates of qfun
lemma dthU_qfun_eq (θ : ℝ) :
    Work.Spaces.dthU Work.Spaces.qfun θ = -2 * (Real.sin (2*θ))^2 := by
  rw [Work.Spaces.dthU_apply]
  have h : HasDerivAt (fun θ' : ℝ => Work.Spaces.qfun θ') (-(Real.sin (2*θ) * 2)) θ := by
    have := (hasDerivAt_cos_two θ).sub_const (1/3 : ℝ)
    simpa [Work.Spaces.qfun, Function.comp_def] using this
  rw [h.deriv]
  ring

lemma dthU_qfun_eq2 (θ : ℝ) :
    Work.Spaces.dthU^[2] Work.Spaces.qfun θ
      = -8 * (Real.sin (2*θ))^2 * Real.cos (2*θ) := by
  have h1 : Work.Spaces.dthU Work.Spaces.qfun
      = fun θ' => -2*(1 - (Real.cos (2*θ'))^2) := by
    funext θ'
    rw [dthU_qfun_eq θ']
    have hs : (Real.sin (2*θ'))^2 = 1 - (Real.cos (2*θ'))^2 := by
      have := Real.sin_sq_add_cos_sq (2*θ'); linarith
    rw [hs]
  rw [show Work.Spaces.dthU^[2] Work.Spaces.qfun
      = Work.Spaces.dthU (Work.Spaces.dthU Work.Spaces.qfun) from rfl, h1]
  rw [dthU_comp_cos (fun c : ℝ => -2*(1-c^2)) θ (by fun_prop)]
  rw [deriv_poly2]
  have hs : (Real.sin (2*θ))^2 = 1 - (Real.cos (2*θ))^2 := by
    have := Real.sin_sq_add_cos_sq (2*θ); linarith
  rw [hs]; ring

lemma dthU_qfun_eq3 (θ : ℝ) :
    Work.Spaces.dthU^[3] Work.Spaces.qfun θ
      = 16*(1-(Real.cos (2*θ))^2)*(1-3*(Real.cos (2*θ))^2) := by
  have h1 : Work.Spaces.dthU^[2] Work.Spaces.qfun
      = fun θ' => -8*(Real.cos (2*θ'))*(1 - (Real.cos (2*θ'))^2) := by
    funext θ'
    rw [dthU_qfun_eq2 θ']
    have hs : (Real.sin (2*θ'))^2 = 1 - (Real.cos (2*θ'))^2 := by
      have := Real.sin_sq_add_cos_sq (2*θ'); linarith
    rw [hs]; ring
  rw [show Work.Spaces.dthU^[3] Work.Spaces.qfun
      = Work.Spaces.dthU (Work.Spaces.dthU^[2] Work.Spaces.qfun) from rfl, h1]
  rw [dthU_comp_cos (fun c : ℝ => -8*c*(1-c^2)) θ (by fun_prop)]
  rw [deriv_poly3]
  ring

lemma dthU_qfun_eq4 (θ : ℝ) :
    Work.Spaces.dthU^[4] Work.Spaces.qfun θ
      = 128*(Real.cos (2*θ))*(1-(Real.cos (2*θ))^2)*(2-3*(Real.cos (2*θ))^2) := by
  have h1 : Work.Spaces.dthU^[3] Work.Spaces.qfun
      = fun θ' => 16*(1 - (Real.cos (2*θ'))^2)*(1 - 3*(Real.cos (2*θ'))^2) :=
    funext (fun θ' => dthU_qfun_eq3 θ')
  rw [show Work.Spaces.dthU^[4] Work.Spaces.qfun
      = Work.Spaces.dthU (Work.Spaces.dthU^[3] Work.Spaces.qfun) from rfl, h1]
  rw [dthU_comp_cos (fun c : ℝ => 16*(1-c^2)*(1-3*c^2)) θ (by fun_prop)]
  rw [deriv_poly4]
  ring

lemma sin_sq_two (θ : ℝ) : 1 - (Real.cos (2*θ))^2 = (Real.sin (2*θ))^2 := by
  have := Real.sin_sq_add_cos_sq (2*θ); linarith

lemma DthQfunBound {i : ℕ} (hi : 1 ≤ i) (hi4 : i ≤ 4) (θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[i] Work.Spaces.qfun θ| ≤ 1000 * (Real.sin (2 * θ)) ^ 2 := by
  have hs : 0 ≤ (Real.sin (2*θ))^2 := sq_nonneg _
  have hc : |Real.cos (2*θ)| ≤ 1 := Real.abs_cos_le_one _
  have hc2 : (Real.cos (2*θ))^2 ≤ 1 := by
    nlinarith [hc, sq_abs (Real.cos (2*θ)), abs_nonneg (Real.cos (2*θ))]
  have h4 : |1 - 3*(Real.cos (2*θ))^2| ≤ 4 := by
    rw [abs_le]
    constructor <;> nlinarith [hc2, sq_nonneg (Real.cos (2*θ))]
  have h5 : |2 - 3*(Real.cos (2*θ))^2| ≤ 5 := by
    rw [abs_le]
    constructor <;> nlinarith [hc2, sq_nonneg (Real.cos (2*θ))]
  interval_cases i
  · rw [Function.iterate_one, dthU_qfun_eq]
    rw [show |(-2:ℝ) * (Real.sin (2*θ))^2| = 2 * (Real.sin (2*θ))^2 by
      rw [abs_mul, show |(-2:ℝ)| = 2 by norm_num, abs_of_nonneg hs]]
    nlinarith
  · rw [dthU_qfun_eq2]
    rw [abs_mul, abs_mul, show |(-8:ℝ)| = 8 by norm_num, abs_of_nonneg hs]
    have := mul_le_of_le_one_right (by positivity : (0:ℝ) ≤ 8 * (Real.sin (2*θ))^2) hc
    linarith
  · rw [dthU_qfun_eq3, sin_sq_two θ]
    rw [abs_mul, abs_mul, show |(16:ℝ)| = 16 by norm_num, abs_of_nonneg hs]
    nlinarith [h4, hs]
  · rw [dthU_qfun_eq4, sin_sq_two θ]
    rw [abs_mul, abs_mul, abs_mul, show |(128:ℝ)| = 128 by norm_num, abs_of_nonneg hs]
    have hstep : |Real.cos (2*θ)| * (Real.sin (2*θ))^2 * |2 - 3*(Real.cos (2*θ))^2|
        ≤ 5 * (Real.sin (2*θ))^2 := by
      have h1 : |Real.cos (2*θ)| * (Real.sin (2*θ))^2 ≤ 1 * (Real.sin (2*θ))^2 :=
        mul_le_mul_of_nonneg_right hc hs
      have h2 : |Real.cos (2*θ)| * (Real.sin (2*θ))^2 * |2 - 3*(Real.cos (2*θ))^2|
          ≤ (1 * (Real.sin (2*θ))^2) * 5 :=
        mul_le_mul h1 h5 (abs_nonneg _) (by positivity)
      linarith
    nlinarith [hstep, hs]



/-! ## The constant bookkeeping -/

/-- `TM m` dominates every `tBound j 0`, `j < m`. -/
noncomputable def TM (m : ℕ) : ℝ := (∑ j ∈ Finset.range m, Work.Spaces.tBound j 0) + 1

lemma TM_pos (m : ℕ) : 0 < TM m := by
  rw [TM]
  have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range m) => Work.Spaces.tBound_nonneg j 0)
  linarith

lemma TM_nonneg (m : ℕ) : 0 ≤ TM m := le_of_lt (TM_pos m)

lemma tBound_le_TM {j m : ℕ} (hj : j < m) : Work.Spaces.tBound j 0 ≤ TM m := by
  rw [TM]
  have h : Work.Spaces.tBound j 0 ≤ ∑ k ∈ Finset.range m, Work.Spaces.tBound k 0 :=
    Finset.single_le_sum (fun k _ => Work.Spaces.tBound_nonneg k 0) (Finset.mem_range.mpr hj)
  linarith

/-- The uniform bound for a single summand of the Leibniz expansion. -/
noncomputable def CM (m : ℕ) (K : ℝ) : ℝ :=
  (2:ℝ)^m * ((4/3)*K + 1000*TM m + 1000)

/-- The constant for index `m+1` given the bound `K` at index `m`. -/
noncomputable def Bstep (m : ℕ) (K : ℝ) : ℝ := ((m:ℝ)+1) * CM m K

lemma Bstep_nonneg {m : ℕ} {K : ℝ} (hK : 0 ≤ K) : 0 ≤ Bstep m K := by
  rw [Bstep, CM]
  have h1 : 0 ≤ (4/3)*K + 1000*TM m + 1000 := by
    have := TM_pos m
    linarith
  positivity

/-! ## The main weighted estimate -/

/-- `Good m K` asserts the weighted bound for all orders `2 ≤ m' ≤ m`. -/
def Good (m : ℕ) (K : ℝ) : Prop :=
  ∀ m' : ℕ, 2 ≤ m' → m' ≤ m → ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.dthU^[m'] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α

/-- The bound for a single summand of the Leibniz expansion. -/
lemma summand_le (m : ℕ) (hm : 2 ≤ m) (hm4 : m ≤ 4) {K : ℝ} (hK0 : 0 ≤ K)
    (hKm : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    {a : ℕ} (ha : a ≤ m) :
    |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
        Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
      ≤ (4/3)*K + 1000*TM m + 1000 := by
  have hW : 0 ≤ Wt α θ := Wt_nonneg hα hθ
  have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    simp only [Function.iterate_zero_apply, Nat.sub_zero]
    have hIH := hKm α hα hα1 θ hθ
    have hq := abs_qfun_le θ
    have hstep : |Work.Spaces.qfun θ| * (|Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        * Wt α θ) ≤ (4/3) * (K * α) := by
      have h1 : |Work.Spaces.qfun θ| * (|Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
            * Wt α θ)
          ≤ (4/3) * (K * α) := by
        have := mul_le_mul hq hIH (mul_nonneg (abs_nonneg _) hW) (by norm_num)
        linarith [this]
      exact h1
    have h2 : (4/3) * (K * α) ≤ (4/3) * K := by
      nlinarith [hK0, hα, hα1]
    have h3 : (0:ℝ) ≤ 1000*TM m + 1000 := by
      have := TM_pos m; linarith
    calc |Work.Spaces.qfun θ * Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
        = |Work.Spaces.qfun θ| * (|Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
            * Wt α θ) := by rw [abs_mul]; ring
      _ ≤ (4/3) * K := le_trans hstep h2
      _ ≤ (4/3)*K + 1000*TM m + 1000 := by linarith
  · rcases eq_or_lt_of_le ha with ham | ham
    · -- `a = m`
      have ham2 : a = m := ham
      rw [ham2]
      simp only [Nat.sub_self, Function.iterate_zero_apply]
      have hB := DthQfunBound (i := m) (by omega) hm4 θ hθ
      have hs := sin_sq_Gam_Wt_le_one hα hα1 hθ
      have hs0 : 0 ≤ (Real.sin (2*θ))^2 := sq_nonneg _
      have h1 : |Work.Spaces.dthU^[m] Work.Spaces.qfun θ * Work.Spaces.Gam α θ| * Wt α θ
          ≤ 1000 * ((Real.sin (2*θ))^2 * Work.Spaces.Gam α θ * Wt α θ) := by
        rw [abs_mul]
        have h2 : |Work.Spaces.dthU^[m] Work.Spaces.qfun θ| ≤ 1000 * (Real.sin (2*θ))^2 := hB
        have h3 : 0 ≤ 1000 * (Real.sin (2*θ))^2 := by positivity
        calc |Work.Spaces.dthU^[m] Work.Spaces.qfun θ| * |Work.Spaces.Gam α θ| * Wt α θ
            ≤ (1000 * (Real.sin (2*θ))^2) * |Work.Spaces.Gam α θ| * Wt α θ := by
              apply mul_le_mul_of_nonneg_right _ hW
              exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
          _ = 1000 * ((Real.sin (2*θ))^2 * Work.Spaces.Gam α θ * Wt α θ) := by
              rw [abs_of_nonneg hG0]; ring
      have h4 : 1000 * ((Real.sin (2*θ))^2 * Work.Spaces.Gam α θ * Wt α θ) ≤ 1000 := by
        nlinarith [hs]
      have h5 : (0:ℝ) ≤ (4/3)*K + 1000*TM m := by
        have := TM_pos m
        nlinarith [hK0]
      linarith [h1, h4, h5]
    · -- `1 ≤ a ≤ m-1`
      have ha1 : 1 ≤ a := hapos
      have ham' : a ≤ m - 1 := by omega
      have hm1 : 1 ≤ m - a := by omega
      have hB := DthQfunBound (i := a) ha1 (by omega) θ hθ
      have hCrude := Work.Spaces.dthU_Gam_le (m-a) hm1 α hα hα1 θ hθ
      have htB : Work.Spaces.tBound (m - a - 1) 0 ≤ TM m := tBound_le_TM (by omega)
      have hs0 : 0 ≤ (Real.sin (2*θ))^2 := sq_nonneg _
      have hkey : |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
            Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
          ≤ 1000 * (Work.Spaces.tBound (m - a - 1) 0) * (α * Work.Spaces.Gam α θ * Wt α θ)
            * (Real.sin (2*θ))^2 := by
        rw [abs_mul]
        have h2 : |Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ|
            ≤ α * Work.Spaces.tBound (m - a - 1) 0 * Work.Spaces.Gam α θ := hCrude
        have h3 : 0 ≤ α * Work.Spaces.tBound (m - a - 1) 0 * Work.Spaces.Gam α θ :=
          mul_nonneg (mul_nonneg (le_of_lt hα) (Work.Spaces.tBound_nonneg _ _)) hG0
        calc |Work.Spaces.dthU^[a] Work.Spaces.qfun θ| *
              |Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
            ≤ (1000 * (Real.sin (2*θ))^2) *
              (α * Work.Spaces.tBound (m - a - 1) 0 * Work.Spaces.Gam α θ) * Wt α θ := by
              apply mul_le_mul_of_nonneg_right _ hW
              exact mul_le_mul hB h2 (abs_nonneg _) (by positivity)
          _ = 1000 * (Work.Spaces.tBound (m - a - 1) 0)
                * (α * Work.Spaces.Gam α θ * Wt α θ) * (Real.sin (2*θ))^2 := by ring
      have hw1 := alpha_Gam_Wt_le_one hα hθ
      have hfin : 1000 * (Work.Spaces.tBound (m - a - 1) 0) * (α * Work.Spaces.Gam α θ * Wt α θ)
            * (Real.sin (2*θ))^2 ≤ 1000 * TM m := by
        have hs1 : (Real.sin (2*θ))^2 ≤ 1 := by
          have h' := Real.abs_sin_le_one (2*θ)
          nlinarith [h', sq_abs (Real.sin (2*θ)), abs_nonneg (Real.sin (2*θ))]
        have hnum : α * Work.Spaces.Gam α θ * Wt α θ ≤ 1 := hw1
        have hc0 : 0 ≤ 1000 * Work.Spaces.tBound (m - a - 1) 0 * (α * Work.Spaces.Gam α θ * Wt α θ) :=
          mul_nonneg (mul_nonneg (by norm_num) (Work.Spaces.tBound_nonneg _ _))
            (mul_nonneg (mul_nonneg (le_of_lt hα) hG0) hW)
        calc 1000 * (Work.Spaces.tBound (m - a - 1) 0) * (α * Work.Spaces.Gam α θ * Wt α θ)
              * (Real.sin (2*θ))^2
            ≤ 1000 * (Work.Spaces.tBound (m - a - 1) 0) * (α * Work.Spaces.Gam α θ * Wt α θ) * 1 :=
              mul_le_mul_of_nonneg_left hs1 hc0
          _ = 1000 * (Work.Spaces.tBound (m - a - 1) 0) * (α * Work.Spaces.Gam α θ * Wt α θ) := by ring
          _ ≤ 1000 * (Work.Spaces.tBound (m - a - 1) 0) * 1 := by
              apply mul_le_mul_of_nonneg_left hnum
              exact mul_nonneg (by norm_num) (Work.Spaces.tBound_nonneg _ _)
          _ ≤ 1000 * TM m := by
              have : Work.Spaces.tBound (m - a - 1) 0 ≤ TM m := htB
              nlinarith [this]
      have h5 : (0:ℝ) ≤ (4/3)*K + 1000 := by nlinarith [hK0]
      linarith [hkey, hfin, h5]


/-- The Leibniz step: the bound at order `m+1` from the bound at order `m`. -/
lemma step_bound (m : ℕ) (hm : 2 ≤ m) (hm4 : m ≤ 4) {K : ℝ} (hK0 : 0 ≤ K)
    (hKm : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[m+1] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ Bstep m K * α := by
  have hW0 : 0 ≤ Wt α θ := Wt_nonneg hα hθ
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  by_cases hI : θ ∈ Set.Ioo 0 (π/2)
  · have hGam_diff : ContDiffOn ℝ ⊤ (fun t => Work.Spaces.Gam α t) (Set.Ioo 0 (π/2)) :=
      contDiffOn_Gam_Ioo' α
    have hq_diff : ContDiffOn ℝ ⊤ Work.Spaces.qfun (Set.Ioo 0 (π/2)) := by
      show ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.cos (2*θ) - 1/3) (Set.Ioo 0 (π/2))
      fun_prop
    have hEqOn : Set.EqOn (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t))
        (fun t => α * (Work.Spaces.qfun t * Work.Spaces.Gam α t)) (Set.Ioo 0 (π/2)) := by
      intro t ht
      rw [Work.Spaces.dthU_Gam α t hα ht]; ring
    have hmain : Work.Spaces.dthU^[m+1] (fun t => Work.Spaces.Gam α t) θ
        = α * (∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
            (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
              Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ)) := by
      rw [Function.iterate_succ_apply]
      rw [dthU_iter_congr_open isOpen_Ioo m (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t))
        (fun t => α * (Work.Spaces.qfun t * Work.Spaces.Gam α t)) hEqOn hI]
      simp only [Work.Spaces.dthU_iter_const_mul]
      rw [show (fun θ : ℝ => Work.Spaces.qfun θ * Work.Spaces.Gam α θ)
          = (Work.Spaces.qfun * fun θ : ℝ => Work.Spaces.Gam α θ) from rfl]
      rw [dthU_iter_mul_Ioo m Work.Spaces.qfun (fun θ : ℝ => Work.Spaces.Gam α θ) hI
        hq_diff hGam_diff]
    have hsum : |∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
            (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
              Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ)| * Wt α θ
        ≤ ((m:ℝ)+1) * CM m K := by
      have habs : |∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
            (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
              Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ)|
          ≤ ∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
              |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ| := by
        calc |∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
              (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ)|
            ≤ ∑ a ∈ Finset.range (m+1), |(m.choose a : ℝ) *
                (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                  Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
                |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                  Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ| := by
              apply Finset.sum_congr rfl
              intro a _
              rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (m.choose a))]
      have h2 : (∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
              |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ|) * Wt α θ
          ≤ ((m:ℝ)+1) * CM m K := by
        rw [Finset.sum_mul]
        calc ∑ a ∈ Finset.range (m+1), ((m.choose a : ℝ) *
                |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                  Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ|) * Wt α θ
            ≤ ∑ _a ∈ Finset.range (m+1), CM m K := by
              apply Finset.sum_le_sum
              intro a ha
              have ham : a ≤ m := by
                have := Finset.mem_range.mp ha
                omega
              have hX := summand_le m hm hm4 hK0 hKm hα hα1 hθ ham
              have hb : (m.choose a : ℝ) ≤ (2:ℝ)^m := by
                exact_mod_cast Nat.choose_le_two_pow m a
              have hX0 : 0 ≤ |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                  Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ :=
                mul_nonneg (abs_nonneg _) hW0
              have hCM0 : 0 ≤ CM m K := by
                rw [CM]
                have h1 : 0 ≤ (4/3)*K + 1000*TM m + 1000 := by
                  have := TM_pos m
                  linarith
                positivity
              calc ((m.choose a : ℝ) *
                    |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                      Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ|) * Wt α θ
                  = (m.choose a : ℝ) *
                      (|Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                        Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ) := by
                    ring
                _ ≤ (2:ℝ)^m * ((4/3)*K + 1000*TM m + 1000) :=
                    mul_le_mul hb hX hX0 (by positivity)
                _ = CM m K := by rw [CM]
          _ = ((m:ℝ)+1) * CM m K := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              push_cast
              ring
      exact le_trans (mul_le_mul_of_nonneg_right habs hW0) h2
    rw [hmain, abs_mul, abs_of_pos hα]
    calc α * |∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
              (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ)| * Wt α θ
        = α * (|∑ a ∈ Finset.range (m+1), (m.choose a : ℝ) *
              (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m-a] (fun t => Work.Spaces.Gam α t) θ)| * Wt α θ) := by ring
      _ ≤ α * (((m:ℝ)+1) * CM m K) := mul_le_mul_of_nonneg_left hsum hα.le
      _ = Bstep m K * α := by rw [Bstep]; ring
  · -- angular endpoints: the weight vanishes
    have hs : Real.sin (2*θ) = 0 := by
      rcases lt_or_eq_of_le hθ.1 with h0 | h0
      · have h1 : θ = π/2 := le_antisymm hθ.2 (le_of_not_gt (fun h => hI ⟨h0, h⟩))
        rw [h1, show 2*(π/2) = π by ring, Real.sin_pi]
      · rw [← h0]; simp
    have hWz : Wt α θ = 0 := by
      rw [Wt, hs, Real.zero_rpow (by linarith : -(α/5) ≠ 0)]
      simp
    rw [hWz, mul_zero]
    exact mul_nonneg (Bstep_nonneg hK0) hα.le


lemma dthU_congr_open {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → ℝ} (h : Set.EqOn f g U) :
    Set.EqOn (Work.Spaces.dthU f) (Work.Spaces.dthU g) U := by
  intro θ hθ
  simpa using (dthU_iter_congr_open hU 1 f g h hθ)

/-- The base case: order `2`. -/
lemma Good_two : Good 2 (2 + 16/9) := by
  intro m' hm2 hm2' α hα hα1 θ hθ
  obtain rfl : m' = 2 := le_antisymm hm2' hm2
  have hW0 : 0 ≤ Wt α θ := Wt_nonneg hα hθ
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  by_cases hI : θ ∈ Set.Ioo 0 (π/2)
  · have hident : Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ
        = α * (α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ
            - 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ) := by
      show Work.Spaces.dthU (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t)) θ = _
      have hEq : Set.EqOn (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t))
          (fun t => α * (Work.Spaces.qfun t * Work.Spaces.Gam α t)) (Set.Ioo 0 (π/2)) :=
        fun t ht => by rw [Work.Spaces.dthU_Gam α t hα ht]; ring
      rw [dthU_congr_open isOpen_Ioo hEq hI, Work.Spaces.dthU_const_mul]
      simp only []
      have hdiffq : DifferentiableAt ℝ Work.Spaces.qfun θ :=
        (Work.Spaces.qfun_smooth.differentiable (by simp)).differentiableAt
      have hdiffG : DifferentiableAt ℝ (fun t => Work.Spaces.Gam α t) θ :=
        Work.Spaces.Gam_differentiableAt α θ hI.1 hI.2
      rw [show Work.Spaces.dthU (fun t : ℝ => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ
          = Work.Spaces.dthU (Work.Spaces.qfun * fun t : ℝ => Work.Spaces.Gam α t) θ from rfl]
      rw [Work.Spaces.dthU_mul_apply Work.Spaces.qfun (fun t : ℝ => Work.Spaces.Gam α t) θ
        hdiffq hdiffG]
      rw [dthU_qfun_eq, Work.Spaces.dthU_Gam α θ hα hI]
      ring
    rw [hident, abs_mul, abs_of_pos hα]
    have hq2 : (Work.Spaces.qfun θ)^2 ≤ 16/9 := by
      have h := abs_qfun_le θ
      nlinarith [abs_nonneg (Work.Spaces.qfun θ), sq_abs (Work.Spaces.qfun θ)]
    have hw1 := alpha_Gam_Wt_le_one hα hθ
    have hw2 := sin_sq_Gam_Wt_le_one hα hα1 hθ
    have hs0 : 0 ≤ (Real.sin (2*θ))^2 := sq_nonneg _
    have hbound : α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ * Wt α θ
        ≤ (16/9) := by
      have h2 : (Work.Spaces.qfun θ)^2 * (α * Work.Spaces.Gam α θ * Wt α θ) ≤ (16/9) * 1 :=
        mul_le_mul hq2 hw1 (mul_nonneg (mul_nonneg (le_of_lt hα) hG0) hW0) (by norm_num)
      linarith [h2]
    have hbound2 : 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ * Wt α θ ≤ 2 := by
      have h0 : 0 ≤ (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ * Wt α θ :=
        mul_nonneg (mul_nonneg hs0 hG0) hW0
      nlinarith [hw2, h0]
    have hX0 : 0 ≤ α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ := by positivity
    have hY0 : 0 ≤ 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ := by positivity
    have htri : |α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ
          - 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ| * Wt α θ
        ≤ (α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ) * Wt α θ
          + (2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ) * Wt α θ := by
      have h1 : |α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ
            - 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ|
          ≤ (α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ)
            + (2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ) := by
        have h := abs_add_le (α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ)
          (-(2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ))
        rw [abs_neg, abs_of_nonneg hX0, abs_of_nonneg hY0] at h
        simpa [sub_eq_add_neg] using h
      calc |α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ
            - 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ| * Wt α θ
          ≤ ((α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ)
            + (2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ)) * Wt α θ :=
              mul_le_mul_of_nonneg_right h1 hW0
        _ = (α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ) * Wt α θ
            + (2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ) * Wt α θ := by ring
    have ha0 : 0 ≤ α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ := by positivity
    have hb0 : 0 ≤ 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ := by positivity
    calc α * |α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ
            - 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ| * Wt α θ
        = α * (|α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ
            - 2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ| * Wt α θ) := by ring
      _ ≤ α * ((α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ) * Wt α θ
            + (2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ) * Wt α θ) :=
            mul_le_mul_of_nonneg_left htri hα.le
      _ = α * ((α * (Work.Spaces.qfun θ)^2 * Work.Spaces.Gam α θ * Wt α θ)
            + (2 * (Real.sin (2*θ))^2 * Work.Spaces.Gam α θ * Wt α θ)) := by ring
      _ ≤ α * ((16/9) + 2) := by
            apply mul_le_mul_of_nonneg_left _ hα.le
            linarith [hbound, hbound2]
      _ = (2 + 16/9) * α := by ring
  · have hs : Real.sin (2*θ) = 0 := by
      rcases lt_or_eq_of_le hθ.1 with h0 | h0
      · have h1 : θ = π/2 := le_antisymm hθ.2 (le_of_not_gt (fun h => hI ⟨h0, h⟩))
        rw [h1, show 2*(π/2) = π by ring, Real.sin_pi]
      · rw [← h0]; simp
    have hWz : Wt α θ = 0 := by
      rw [Wt, hs, Real.zero_rpow (by linarith : -(α/5) ≠ 0)]
      simp
    rw [hWz, mul_zero]
    have : (0:ℝ) < 2 + 16/9 := by norm_num
    exact mul_nonneg this.le hα.le

/-- One step of the induction. -/
lemma Good_step (m : ℕ) (hm : 2 ≤ m) (hm4 : m ≤ 4) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : Good m K) : Good (m+1) (max K (Bstep m K)) := by
  intro m' hm2 hm' α hα hα1 θ hθ
  by_cases hle : m' ≤ m
  · have h1 := hK m' hm2 hle α hα hα1 θ hθ
    exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  · have hm'eq : m' = m+1 := by omega
    rw [hm'eq]
    have h2 := step_bound m hm hm4 hK0 (hK m hm (le_refl m)) α hα hα1 θ hθ
    exact le_trans h2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hα.le)

noncomputable def K2 : ℝ := 2 + 16/9
noncomputable def K3 : ℝ := max K2 (Bstep 2 K2)
noncomputable def K4 : ℝ := max K3 (Bstep 3 K3)
noncomputable def K5 : ℝ := max K4 (Bstep 4 K4)

lemma K2_pos : 0 < K2 := by rw [K2]; norm_num

lemma Good_three : Good 3 K3 := by
  have := Good_step 2 (by norm_num) (by norm_num) (le_of_lt K2_pos) Good_two
  simpa [K3, K2] using this

lemma Good_four : Good 4 K4 := by
  have h3 : 0 ≤ K3 := le_of_lt (lt_of_lt_of_le K2_pos (le_max_left _ _))
  have := Good_step 3 (by norm_num) (by norm_num) h3 Good_three
  simpa [K4] using this

lemma Good_five : Good 5 K5 := by
  have h4 : 0 ≤ K4 := le_of_lt (lt_of_lt_of_le K2_pos (le_trans (le_max_left _ _) (le_max_left _ _)))
  have := Good_step 4 (by norm_num) (by norm_num) h4 Good_four
  simpa [K5] using this

lemma K5_pos : 0 < K5 := by
  have h : 0 < K2 := K2_pos
  have h3 : 0 < K3 := lt_of_lt_of_le h (le_max_left _ _)
  have h4 : 0 < K4 := lt_of_lt_of_le h3 (le_max_left _ _)
  exact lt_of_lt_of_le h4 (le_max_left _ _)

/-- The weighted bound for the `D_θ`-iterates of `Γ`. -/
theorem dthGamWeightLe :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → m ≤ 5 → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α := by
  refine ⟨K5, K5_pos, fun m hm hm5 α hα hα1 θ hθ => ?_⟩
  exact Good_five m hm (by omega) α hα hα1 θ hθ



lemma Fstar_eq (α : ℝ) : Work.Construction.Fstar α
    = fun z θ => ((2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ) * Work.Spaces.hKer z := by
  funext z θ
  simp only [Work.Construction.Fstar, Work.FM.Fstar, Work.Spaces.hKer]
  ring

lemma DthIter_Dth (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter j (Work.Spaces.Dth f) = Work.Spaces.DthIter (j + 1) f := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have h : Work.Spaces.DthIter (j+1) (Work.Spaces.Dth f)
          = Work.Spaces.Dth (Work.Spaces.DthIter (j+1) f) := by
        rw [Work.Spaces.DthIter_succ, ih]
      rw [h]
      exact (Work.Spaces.DthIter_succ (j+1) f).symm

lemma FstarDthFactor (α : ℝ) (j k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ
      = (2 * α / Work.Spaces.c α) * deriv^[k] Work.Spaces.hKer z
          * Work.Spaces.dthU^[j + 1] (fun t => Work.Spaces.Gam α t) θ := by
  have h1 : Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))
      = fun z θ => Work.Spaces.dthU^[j+1]
            (fun t => 2 * α / Work.Spaces.c α * Work.Spaces.Gam α t) θ
          * Work.Spaces.hKer z := by
    rw [DthIter_Dth, Fstar_eq]
    funext z θ
    exact Work.Spaces.DthIter_decomp (j+1) _ _ z θ
  rw [h1]
  rw [show Work.Spaces.dthU^[j+1] (fun t => 2 * α / Work.Spaces.c α * Work.Spaces.Gam α t)
      = fun t => (2 * α / Work.Spaces.c α)
          * Work.Spaces.dthU^[j+1] (fun s => Work.Spaces.Gam α s) t from
    Work.Spaces.dthU_iter_const_mul (j+1) (2 * α / Work.Spaces.c α)
      (fun s => Work.Spaces.Gam α s)]
  rw [show Work.Spaces.pzIter k (fun z θ => ((2 * α / Work.Spaces.c α)
          * Work.Spaces.dthU^[j+1] (fun s => Work.Spaces.Gam α s) θ) * Work.Spaces.hKer z) z θ
      = ((2 * α / Work.Spaces.c α)
          * Work.Spaces.dthU^[j+1] (fun s => Work.Spaces.Gam α s) θ)
          * deriv^[k] Work.Spaces.hKer z from
    Work.Spaces.pzIter_decomp k
      (fun t => (2 * α / Work.Spaces.c α)
        * Work.Spaces.dthU^[j+1] (fun s => Work.Spaces.Gam α s) t) Work.Spaces.hKer z θ]
  ring

/-! ## The two pointwise bounds for `D_θ F_*` -/

lemma Fstar_coef_leD' (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    |2 * α / Work.Spaces.c α| ≤ 20 * α := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hnum : 0 ≤ 2 * α := by linarith
  rw [abs_of_nonneg (div_nonneg hnum (le_of_lt hcpos)), div_le_iff₀ hcpos]
  nlinarith

lemma DthFstar_z_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z+1)^k * Work.Spaces.pzIter k (Work.Spaces.Dth (Work.Construction.Fstar α)) z θ|
      ≤ (20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k+1))) * α^2 := by
  change |(z+1)^k * Work.Spaces.pzIter k
      (Work.Spaces.DthIter 0 (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ| ≤ _
  rw [FstarDthFactor α 0 k z θ]
  have hker : |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z| ≤ (k.factorial : ℝ) * (k + 1) :=
    Work.Spaces.pzIter_hKer_bound k z hz
  have hcoef := Fstar_coef_leD' α hα hα1
  have hdth := Work.Spaces.dthU_Gam_le 1 (by norm_num) α hα hα1 θ hθ
  have hGam := Work.Spaces.Gam_bounds α θ hα hθ
  have hloc : (z + 1) ^ k * ((2 * α / Work.Spaces.c α) * deriv^[k] Work.Spaces.hKer z
        * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ)
      = (2 * α / Work.Spaces.c α) * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z)
        * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ := by ring
  rw [hloc, abs_mul, abs_mul]
  have h1 : |Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * Work.Spaces.tBound 0 0 := by
    refine le_trans hdth ?_
    exact mul_le_of_le_one_right (mul_nonneg (le_of_lt hα) (Work.Spaces.tBound_nonneg _ _)) hGam.2
  have h2 : |2 * α / Work.Spaces.c α| * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
      ≤ (20 * α) * ((k.factorial : ℝ) * (k + 1)) :=
    mul_le_mul hcoef hker (abs_nonneg _) (by positivity)
  have h3 : (20 * α) * ((k.factorial : ℝ) * (k + 1)) * |Work.Spaces.dthU^[1]
      (fun t => Work.Spaces.Gam α t) θ|
      ≤ (20 * α) * ((k.factorial : ℝ) * (k + 1)) * (α * Work.Spaces.tBound 0 0) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : |2 * α / Work.Spaces.c α| * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
      * |Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ|
      ≤ (20 * α) * ((k.factorial : ℝ) * (k + 1)) * (α * Work.Spaces.tBound 0 0) :=
    le_trans (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)) h3
  calc |2 * α / Work.Spaces.c α| * |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z|
        * |Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ|
      ≤ (20 * α) * ((k.factorial : ℝ) * (k + 1)) * (α * Work.Spaces.tBound 0 0) := h4
    _ = (20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k + 1))) * α^2 := by ring

lemma DthFstar_mixed_bound {K : ℝ}
    (hK : ∀ m : ℕ, 2 ≤ m → m ≤ 5 → ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (j k : ℕ) (hj : 1 ≤ j) (hj4 : j ≤ 4)
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z+1)^k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ
        * (Real.sin (2*θ)) ^ (-(α/5)) / (α + Real.sin (2*θ))|
      ≤ (20 * K * ((k.factorial : ℝ) * (k+1))) * α^2 := by
  rw [show (z + 1) ^ k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ
        * (Real.sin (2*θ)) ^ (-(α/5)) / (α + Real.sin (2*θ))
      = (z + 1) ^ k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ * Wt α θ from by
    rw [Wt]; ring]
  rw [FstarDthFactor α j k z θ]
  have hker : |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z| ≤ (k.factorial : ℝ) * (k + 1) :=
    Work.Spaces.pzIter_hKer_bound k z hz
  have hcoef := Fstar_coef_leD' α hα hα1
  have hKer0 : 0 ≤ (k.factorial : ℝ) * (k + 1) := by positivity
  have hW0 : 0 ≤ Wt α θ := Wt_nonneg hα hθ
  have hdth := hK (j+1) (by omega) (by omega) α hα hα1 θ hθ
  have hloc : (z + 1) ^ k * ((2 * α / Work.Spaces.c α) * deriv^[k] Work.Spaces.hKer z
        * Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ) * Wt α θ
      = (2 * α / Work.Spaces.c α) * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z)
        * (Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ) := by ring
  have hmain : |(2 * α / Work.Spaces.c α) * ((z+1)^k * deriv^[k] Work.Spaces.hKer z)
        * (Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ)|
      ≤ (20 * K * ((k.factorial : ℝ) * (k+1))) * α^2 := by
    rw [abs_mul]
    have hAB : |(2 * α / Work.Spaces.c α) * ((z+1)^k * deriv^[k] Work.Spaces.hKer z)|
        ≤ 20 * α * ((k.factorial : ℝ) * (k + 1)) := by
      rw [abs_mul]
      exact mul_le_mul hcoef hker (abs_nonneg _) (by positivity)
    have hdW : |Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ| ≤ K * α := by
      rw [abs_mul, abs_of_nonneg hW0]
      exact hdth
    calc |(2 * α / Work.Spaces.c α) * ((z+1)^k * deriv^[k] Work.Spaces.hKer z)|
          * |Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ|
        ≤ (20 * α * ((k.factorial : ℝ) * (k + 1))) * (K * α) :=
          mul_le_mul hAB hdW (abs_nonneg _) (by positivity)
      _ = (20 * K * ((k.factorial : ℝ) * (k + 1))) * α^2 := by ring
  rw [hloc]
  exact hmain


/-! ## Assembly -/

/-- The universal constant of the estimate. -/
noncomputable def KD (K : ℝ) : ℝ :=
  (∑ k ∈ Finset.range 5, 20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k + 1)))
    + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
        (if 1 ≤ j ∧ k + j ≤ 4 then 20 * K * ((k.factorial : ℝ) * (k + 1)) else 0)

lemma KD_nonneg {K : ℝ} (hK : 0 ≤ K) : 0 ≤ KD K := by
  rw [KD]
  refine add_nonneg (Finset.sum_nonneg fun k _ => ?_)
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_)
  · exact mul_nonneg (mul_nonneg (by norm_num) (Work.Spaces.tBound_nonneg _ _)) (by positivity)
  · split_ifs with h
    · exact mul_nonneg (mul_nonneg (by norm_num) hK) (by positivity)
    · norm_num

lemma WlInfMem_DthFstar {K : ℝ}
    (hK : ∀ m : ℕ, 2 ≤ m → m ≤ 5 → ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) := by
  constructor
  · intro k hk
    refine ⟨20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k + 1)) * α^2,
      fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact DthFstar_z_bound α hα hα1 k z θ hz hθ
  · intro j hj k hk hj1 hjk
    refine ⟨20 * K * ((k.factorial : ℝ) * (k + 1)) * α^2, fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact DthFstar_mixed_bound hK α hα hα1 j k hj1 (by omega) z θ hz hθ

lemma WlInf_DthFstar_le {K : ℝ} (hKpos : 0 < K)
    (hK : ∀ m : ℕ, 2 ≤ m → m ≤ 5 → ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ KD K * α^2 := by
  have h2 : KD K * α^2 =
      (∑ k ∈ Finset.range 5,
          20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k + 1)) * α^2)
        + ∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
            (if 1 ≤ j ∧ k + j ≤ 4 then
              20 * K * ((k.factorial : ℝ) * (k + 1)) * α^2 else 0) := by
    rw [KD, add_mul]
    congr 1
    · rw [Finset.sum_mul]
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs with h <;> ring
  rw [Work.Spaces.WlInf, h2]
  apply add_le_add
  · exact Finset.sum_le_sum fun k hk =>
      Work.Spaces.supAbs_le fun z hz θ hθ => DthFstar_z_bound α hα hα1 k z θ hz hθ
  · apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    split_ifs with hcond
    · exact Work.Spaces.supAbs_le fun z hz θ hθ =>
        DthFstar_mixed_bound hK α hα hα1 j k hcond.1 (by omega) z θ hz hθ
    · simp

end DthAux

theorem DthFstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C * α ^ 2 := by
  obtain ⟨K, hKpos, hK⟩ := DthAux.dthGamWeightLe
  refine ⟨DthAux.KD K + 1, by linarith [DthAux.KD_nonneg (le_of_lt hKpos)],
    fun α hα hα1 => ⟨?_, ?_⟩⟩
  · exact DthAux.WlInfMem_DthFstar hK α hα hα1
  · refine le_trans (DthAux.WlInf_DthFstar_le hKpos hK α hα hα1) ?_
    have h0 : 0 ≤ α^2 := sq_nonneg α
    nlinarith [DthAux.KD_nonneg (le_of_lt hKpos), h0]

end Work.FTS.Nonlinear.FstarPkg
