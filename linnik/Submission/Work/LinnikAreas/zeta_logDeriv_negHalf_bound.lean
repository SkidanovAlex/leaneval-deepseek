import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_re_ge_three_halves_bound
import Submission.Commons.NumberTheory.Linnik.tentMellin_bridge_scale

/-!
# The logarithmic derivative of `ζ` on the line `Re s = -1/2`

We prove that `‖ζ'/ζ(-1/2 + i t)‖ ≲ log(|t|+2)` uniformly in `t`.

Route: iterate the functional equation of `ζ` at the point `-1/2 + i t`.
Writing `w = -1/2 + i t` and `u = 1 - w = 3/2 - i t`, the functional equation says

    ζ(w) = 2 · (2π)^{-u} · Γ(u) · cos (π u / 2) · ζ(u).

Taking logarithmic derivatives and using that the completed zeta satisfies
`logDeriv Λ w = - logDeriv Λ (1 - w)` we get

    logDeriv ζ w = - logDeriv Gammaℝ u - logDeriv ζ u - logDeriv Gammaℝ w,

where all the points `u` (with `Re u = 3/2`) and `w` (with `Re w = -1/2`) are evaluated with
the already available bounds.  On `Re = 3/2` the point `u` is in the half-plane of convergence,
where `‖logDeriv ζ u‖ ≤ 20` and the archimedean factor satisfies a `log`-bound; on `Re = -1/2`
the same holds for `Gammaℝ` by the same lemmas applied to the trivial Dirichlet character.
-/

open Complex Filter
open scoped Real Topology

namespace Work.LinnikAreas

noncomputable section

/-- The archimedean gamma factor of the (unique) Dirichlet character mod `1` is `Gammaℝ`. -/
private lemma gammaFactor_one_eq :
    DirichletCharacter.gammaFactor (1 : DirichletCharacter ℂ 1) = Complex.Gammaℝ := by
  funext s
  have h : (1 : DirichletCharacter ℂ 1).Even := by
    show (1 : DirichletCharacter ℂ 1) (-1) = 1
    exact map_one _
  exact DirichletCharacter.Even.gammaFactor_def h s

/-- `Gammaℝ` is differentiable at every point where it does not vanish. -/
private lemma GammaR_diff_of_ne_zero {z : ℂ} (hz : Complex.Gammaℝ z ≠ 0) :
    DifferentiableAt ℂ Complex.Gammaℝ z := by
  have h : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z :=
    Complex.differentiable_Gammaℝ_inv.differentiableAt
  have hinv : DifferentiableAt ℂ (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹)⁻¹) z :=
    h.inv (inv_ne_zero hz)
  have hfun : (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹)⁻¹) = Complex.Gammaℝ := by
    funext s; rw [inv_inv]
  rwa [hfun] at hinv

/-- `Gammaℝ` does not vanish on the vertical line `Re s = -1/2`. -/
private lemma GammaR_ne_zero_of_neg_half (t : ℝ) :
    Complex.Gammaℝ ((-(1/2) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  intro h
  rw [Complex.Gammaℝ_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hre := congrArg Complex.re hn
  simp at hre
  have hn' : (n : ℝ) = 1/4 := by linarith
  have h' : ((4*n : ℕ) : ℝ) = 1 := by push_cast; linarith
  have h4 : (4*n : ℕ) = 1 := by exact_mod_cast h'
  omega

/-- The logarithmic derivative of the completed zeta satisfies the functional equation
`logDeriv Λ w = - logDeriv Λ (1 - w)` away from the poles `0, 1` of `Λ`. -/
private lemma logDeriv_completedRiemannZeta_eq_neg (w : ℂ) (h0 : 1 - w ≠ 0) (h1 : 1 - w ≠ 1) :
    logDeriv completedRiemannZeta w = -logDeriv completedRiemannZeta (1 - w) := by
  have hd : DifferentiableAt ℂ completedRiemannZeta (1 - w) := differentiableAt_completedZeta h0 h1
  have hld : logDeriv completedRiemannZeta w
      = logDeriv (completedRiemannZeta ∘ (fun z : ℂ => 1 - z)) w := by
    have hev : completedRiemannZeta =ᶠ[𝓝 w] (completedRiemannZeta ∘ (fun z : ℂ => 1 - z)) :=
      Filter.Eventually.of_forall (fun z => (completedRiemannZeta_one_sub z).symm)
    exact (logDeriv_congr_nhds hev).self_of_nhds
  rw [hld, logDeriv_comp (f := completedRiemannZeta) (g := fun z : ℂ => 1 - z) (x := w) hd
    (by fun_prop)]
  rw [show deriv (fun z : ℂ => 1 - z) w = -1 by simp]
  simp

/-- **The logarithmic derivative of `ζ` on the line `Re s = -1/2` is `O(log |t|)`.**

There is a constant `C > 0` with `‖ζ'/ζ(-1/2 + i t)‖ ≤ C (1 + log(|t| + 2))` for every real
`t`. -/
theorem zeta_logDeriv_negHalf_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖logDeriv riemannZeta ((-(1 / 2) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + Real.log (|t| + 2)) := by
  refine ⟨47, by norm_num, ?_⟩
  intro t
  set w : ℂ := (-(1/2) : ℂ) + (t : ℂ) * Complex.I with hw
  set u : ℂ := ((3/2 : ℝ) : ℂ) - (t : ℂ) * Complex.I with hu
  have huw : 1 - w = u := by rw [hw, hu]; push_cast; ring
  have hure : u.re = 3/2 := by rw [hu]; simp
  have hwre : w.re = -(1/2) := by rw [hw]; simp
  have hu_ne0 : u ≠ 0 := by
    intro h; have hh := congrArg Complex.re h; rw [hure] at hh; norm_num at hh
  have hu_ne1 : u ≠ 1 := by
    intro h; have hh := congrArg Complex.re h; rw [hure] at hh; norm_num at hh
  have hw_ne0 : w ≠ 0 := by
    intro h; have hh := congrArg Complex.re h; rw [hwre] at hh; norm_num at hh
  have hw_ne1 : w ≠ 1 := by
    intro h; have hh := congrArg Complex.re h; rw [hwre] at hh; norm_num at hh
  have hG_u : Complex.Gammaℝ u ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hure]; norm_num)
  have hG_w : Complex.Gammaℝ w ≠ 0 := by
    rw [hw]; exact GammaR_ne_zero_of_neg_half t
  have hGdiff_u : DifferentiableAt ℂ Complex.Gammaℝ u := GammaR_diff_of_ne_zero hG_u
  have hGdiff_w : DifferentiableAt ℂ Complex.Gammaℝ w := GammaR_diff_of_ne_zero hG_w
  have hζu : riemannZeta u ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hure]; norm_num)
  have hΛu_ne : completedRiemannZeta u ≠ 0 := by
    intro hΛ; apply hζu
    rw [riemannZeta_def_of_ne_zero hu_ne0, hΛ, zero_div]
  have hΛw_ne : completedRiemannZeta w ≠ 0 := by
    intro hΛ; apply hΛu_ne
    rw [← huw, completedRiemannZeta_one_sub w, hΛ]
  -- split `logDeriv ζ w` using `ζ = Λ / Gammaℝ`
  have hsplit1 : logDeriv riemannZeta w =
      logDeriv completedRiemannZeta w - logDeriv Complex.Gammaℝ w := by
    have hev : riemannZeta =ᶠ[𝓝 w] (fun z => completedRiemannZeta z / Complex.Gammaℝ z) := by
      filter_upwards [eventually_ne_nhds hw_ne0] with z hz
      exact riemannZeta_def_of_ne_zero hz
    rw [(logDeriv_congr_nhds hev).self_of_nhds]
    exact logDeriv_div w hΛw_ne hG_w (differentiableAt_completedZeta hw_ne0 hw_ne1) hGdiff_w
  -- split `logDeriv Λ u` using `Λ = ζ * Gammaℝ` on `Re > 1`
  have hsplit2 : logDeriv completedRiemannZeta u =
      logDeriv Complex.Gammaℝ u + logDeriv riemannZeta u := by
    have hnhds : ∀ᶠ z : ℂ in 𝓝 u, (1 : ℝ) < z.re := by
      have hopen : IsOpen {z : ℂ | (1:ℝ) < z.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      exact hopen.mem_nhds (by change (1:ℝ) < u.re; rw [hure]; norm_num)
    have hev : completedRiemannZeta =ᶠ[𝓝 u] (fun z => riemannZeta z * Complex.Gammaℝ z) := by
      filter_upwards [eventually_ne_nhds hu_ne0, hnhds] with z hz0 hz1
      have hGz : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
      rw [riemannZeta_def_of_ne_zero hz0, div_mul_cancel₀ _ hGz]
    rw [(logDeriv_congr_nhds hev).self_of_nhds]
    erw [logDeriv_mul u hζu hG_u (differentiableAt_riemannZeta hu_ne1) hGdiff_u]
    ring
  -- functional equation for the completed zeta
  have hfe : logDeriv completedRiemannZeta w = -logDeriv completedRiemannZeta u := by
    have h := logDeriv_completedRiemannZeta_eq_neg w (by rw [huw]; exact hu_ne0)
      (by rw [huw]; exact hu_ne1)
    rwa [huw] at h
  have hmain : logDeriv riemannZeta w =
      -(logDeriv Complex.Gammaℝ u) - logDeriv riemannZeta u - logDeriv Complex.Gammaℝ w := by
    rw [hsplit1, hfe, hsplit2]; ring
  -- the three bounds
  have hBu : ‖logDeriv Complex.Gammaℝ u‖ ≤ Real.log (2 + |t|) / 2 + 14 := by
    have h := Commons.NumberTheory.Linnik.norm_logDeriv_gammaFactor_at_three_halves
      (χ := (1 : DirichletCharacter ℂ 1)) t
    rw [gammaFactor_one_eq] at h
    simpa [hu] using h
  have hZu : ‖logDeriv riemannZeta u‖ ≤ 20 := by
    have h32 : (3:ℝ)/2 ≤ u.re := by rw [hure]
    have h := Commons.NumberTheory.DirichletCharacter.logDeriv_LFunction_re_ge_three_halves_bound
      (1 : DirichletCharacter ℂ 1) (s := u) h32
    simpa using h
  have hBw : ‖logDeriv Complex.Gammaℝ w‖ ≤ 13 * (Real.log (2 + |t|) + 1) := by
    have h := Commons.NumberTheory.Linnik.norm_logDeriv_gammaFactor_left
      (χ := (1 : DirichletCharacter ℂ 1)) t
    rw [gammaFactor_one_eq] at h
    have hw' : w = (↑(-1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by rw [hw]; push_cast; ring
    rw [hw']
    exact h
  have hbnd : ‖logDeriv riemannZeta w‖ ≤
      Real.log (2 + |t|) / 2 + 14 + 20 + 13 * (Real.log (2 + |t|) + 1) := by
    rw [hmain]
    calc ‖-(logDeriv Complex.Gammaℝ u) - logDeriv riemannZeta u - logDeriv Complex.Gammaℝ w‖
        ≤ ‖-(logDeriv Complex.Gammaℝ u) - logDeriv riemannZeta u‖ +
            ‖logDeriv Complex.Gammaℝ w‖ := norm_sub_le _ _
      _ ≤ (‖logDeriv Complex.Gammaℝ u‖ + ‖logDeriv riemannZeta u‖) +
            ‖logDeriv Complex.Gammaℝ w‖ := by
          gcongr
          simpa using norm_sub_le (-(logDeriv Complex.Gammaℝ u)) (logDeriv riemannZeta u)
      _ ≤ (Real.log (2 + |t|) / 2 + 14 + 20) + 13 * (Real.log (2 + |t|) + 1) :=
          add_le_add (add_le_add hBu hZu) hBw
      _ = Real.log (2 + |t|) / 2 + 14 + 20 + 13 * (Real.log (2 + |t|) + 1) := by ring
  have hfin : Real.log (2 + |t|) / 2 + 14 + 20 + 13 * (Real.log (2 + |t|) + 1) ≤
      47 * (1 + Real.log (|t| + 2)) := by
    have hc : 2 + |t| = |t| + 2 := by ring
    rw [hc]
    have hl : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
    nlinarith
  exact hbnd.trans hfin

end

end Work.LinnikAreas
