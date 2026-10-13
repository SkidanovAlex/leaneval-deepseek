import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstCrux
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `rhoProf_ae_le` — the angular profile `rhoProf α k` is essentially bounded

The angular profile of the moment correction,

`rhoProf α k θ = ∑_{i ≤ k} (D_θ^i ρ (θ))² · (sin(2θ)^{−γ} + sin(2θ)^{−η})`,

(`Work.FTS.PhiStar.Honesty.CptApp.rhoProf`) is a *fixed* finite quantity: the profile
`ρ = crho⁻¹ · rhoAux` vanishes for `θ ≤ 1` and for `3/2 ≤ θ`, hence so does every one of
its `D_θ`-iterates (they are built from derivatives, and each iterate is zero on the open
complement of `[1, 3/2]` by `Filter.EventuallyEq.deriv_eq`).  Thus `rhoProf α k` vanishes
off the compact interval `[1, 3/2]`, while on that interval it is continuous (the factor
`sin(2θ)^{−γ} + sin(2θ)^{−η}` is bounded there since `sin(2θ) ∈ [sin 3, 1]`, and
`sin(2θ) > 0` on `[1, 3/2] ⊂ (0, π/2)`).  Compactness then gives the bound.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.Est

open Work.FTS.PhiStar.Honesty.CptApp

/-! ## The support of the moment profile `ρ` -/

theorem rhoAux_eq_zero_of_le_one {θ : ℝ} (h : θ ≤ 1) : rhoAux θ = 0 := by
  simp only [rhoAux, cut01,
    Real.smoothTransition.zero_of_nonpos (show 2 * θ - 2 ≤ 0 by linarith), zero_mul]

theorem rhoAux_eq_zero_of_three_halves_le {θ : ℝ} (h : 3 / 2 ≤ θ) : rhoAux θ = 0 := by
  simp only [rhoAux, cut01,
    Real.smoothTransition.zero_of_nonpos (show 3 - 2 * θ ≤ 0 by linarith), mul_zero]

theorem rho_eq_zero_of_le_one {θ : ℝ} (h : θ ≤ 1) : rho θ = 0 := by
  rw [rho, rhoAux_eq_zero_of_le_one h, mul_zero]

theorem rho_eq_zero_of_three_halves_le {θ : ℝ} (h : 3 / 2 ≤ θ) : rho θ = 0 := by
  rw [rho, rhoAux_eq_zero_of_three_halves_le h, mul_zero]

theorem contDiff_rhoAux (n : ℕ) : ContDiff ℝ n rhoAux := by
  unfold rhoAux cut01
  fun_prop

/-! ## The `D_θ`-iterates of `ρ` as functions of `θ` alone

`ρ` is a function of `θ` only, so `D_θ^i ρ` (applied to the lifted profile
`(z,θ) ↦ ρ θ`) is again a function of `θ` alone; it is the recursion
`rphi 0 = ρ`, `rphi (i+1) θ = sin(2θ) · (rphi i)' θ`. -/

/-- The `i`-th iterate `D_θ^i ρ` of the angular profile, as a function of `θ`. -/
def rphi : ℕ → ℝ → ℝ
  | 0 => rho
  | i + 1 => fun θ => Real.sin (2 * θ) * deriv (rphi i) θ

theorem rphi_zero : rphi 0 = rho := rfl

theorem rphi_succ (i : ℕ) :
    rphi (i + 1) = fun θ => Real.sin (2 * θ) * deriv (rphi i) θ := rfl

/-- The lifted iterates agree with `rphi`. -/
theorem DthIter_rho_val (i : ℕ) :
    ∀ θ : ℝ, Work.Spaces.DthIter i (fun _ θ' : ℝ => rho θ') 0 θ = rphi i θ := by
  induction i with
  | zero => intro θ; rfl
  | succ i ih =>
      intro θ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      have h2 : Work.Spaces.pth
          (Work.Spaces.DthIter i (fun _ θ' : ℝ => rho θ')) 0 θ = deriv (rphi i) θ := by
        show deriv (fun θ' => Work.Spaces.DthIter i (fun _ θ' : ℝ => rho θ') 0 θ') θ
          = deriv (rphi i) θ
        congr 1
        funext θ'
        exact ih θ'
      rw [h2, rphi_succ]

/-- Every iterate is smooth. -/
theorem contDiff_rphi (i : ℕ) : ∀ n : ℕ, ContDiff ℝ n (rphi i) := by
  induction i with
  | zero =>
      intro n
      have h : ContDiff ℝ n rho := by
        unfold rho rhoAux cut01
        fun_prop
      simpa [rphi] using h
  | succ i ih =>
      intro n
      have hsin : ContDiff ℝ n (fun θ : ℝ => Real.sin (2 * θ)) :=
        Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
      have hd : ContDiff ℝ n (deriv (rphi i)) := (ih (n + 1)).deriv'
      simpa [rphi] using hsin.mul hd

/-- **The key support fact**: every `D_θ`-iterate of `ρ` vanishes for `θ < 1` and for
`3/2 < θ`. -/
theorem rphi_eq_zero (i : ℕ) :
    ∀ θ : ℝ, θ < 1 ∨ 3 / 2 < θ → rphi i θ = 0 := by
  induction i with
  | zero =>
      intro θ hθ
      rcases hθ with h | h
      · exact rho_eq_zero_of_le_one h.le
      · exact rho_eq_zero_of_three_halves_le h.le
  | succ i ih =>
      intro θ hθ
      have hderiv : deriv (rphi i) θ = 0 := by
        rcases hθ with h | h
        · have hnb : Set.Iio (1 : ℝ) ∈ 𝓝 θ := isOpen_Iio.mem_nhds h
          have hev : rphi i =ᶠ[𝓝 θ] (0 : ℝ → ℝ) := by
            filter_upwards [hnb] with x hx using ih x (Or.inl hx)
          simpa using hev.deriv_eq
        · have hnb : Set.Ioi (3 / 2 : ℝ) ∈ 𝓝 θ := isOpen_Ioi.mem_nhds h
          have hev : rphi i =ᶠ[𝓝 θ] (0 : ℝ → ℝ) := by
            filter_upwards [hnb] with x hx using ih x (Or.inr hx)
          simpa using hev.deriv_eq
      rw [rphi_succ]
      simp [hderiv]

/-- `rhoProf` vanishes off the compact interval `[1, 3/2]`. -/
theorem rhoProf_eq_zero_of_not_mem {α : ℝ} {k : ℕ} {θ : ℝ}
    (hθ : θ ∉ Set.Icc (1 : ℝ) (3 / 2)) : rhoProf α k θ = 0 := by
  have hlt : θ < 1 ∨ 3 / 2 < θ := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hθ
    exact hθ
  unfold rhoProf
  refine Finset.sum_eq_zero fun i _ => ?_
  have hφ : Work.Spaces.DthIter i (fun _ θ' : ℝ => rho θ') 0 θ = 0 := by
    rw [DthIter_rho_val i θ]
    exact rphi_eq_zero i θ hlt
  simp [hφ]

theorem rhoProf_ae_le (k : ℕ) (α : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ ≤ C := by
  have hcont : ContinuousOn (rhoProf α k) (Set.Icc (1 : ℝ) (3 / 2)) :=
    (continuousOn_rhoProf α k).mono fun θ hθ =>
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_gt_three]⟩
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C₁ 0, le_max_right _ _, ?_⟩
  refine Filter.Eventually.of_forall fun θ => ?_
  by_cases hθ : θ ∈ Set.Icc (1 : ℝ) (3 / 2)
  · have h1 : ‖rhoProf α k θ‖ ≤ C₁ := hC₁ θ hθ
    have h2 : rhoProf α k θ ≤ C₁ :=
      le_trans (le_abs_self _) (by simpa using h1)
    exact le_trans h2 (le_max_left _ _)
  · rw [rhoProf_eq_zero_of_not_mem hθ]
    exact le_max_right _ _

end Work.FTS.PhiStar.Honesty.CptApp.Est
