import Mathlib
import Submission.Work.Transfer.Setup
import Submission.Work.Normal.montel_omits_three
import Submission.Work.Transfer.not_isNormalFamily_div
import Submission.Work.Transfer.tendsto_norm_critOrbit_atTop_of_not_mem

/-!
# The "hit" step of the transfer argument (`Work.Transfer.hit`)

Step 1 of Shishikura's Lemma 3.2 / the MSS Lemma III.2 transfer argument: at a boundary
parameter `c₀` of the Mandelbrot set carrying a holomorphic motion `phi` of its dynamical IFS,
some point of the critical orbit `critOrbit m c` is realised by the limit set: there are
`m : ℕ`, `c₁ ∈ ball c₀ ρ` and a code `w` with `critOrbit m c₁ = phi c₁ w`.

The proof is a Montel ("two omitted values") argument on the preconnected disc `ball c₀ ρ`.
Assuming no hit exists, pick two distinct codes `x1 ≠ x2` (here `N ≥ 2`); then for every `m` the
holomorphic function `c ↦ (critOrbit m c - phi c x1)/(phi c x2 - phi c x1)` omits `0` and `1`,
so its family is normal.  But at `c₀ ∈ M` the values `critOrbit m c₀` stay bounded by `2`, while
at a point `c'` of the disc outside `M` (which exists because `c₀ ∈ ∂M`) the critical orbit
escapes, so the divided family is unbounded at `c'`.  Both alternatives of normality are
impossible; this is the content of `not_isNormalFamily_div`.
-/

open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter Topology
open Classical

noncomputable section

namespace Work.Transfer

theorem hit {c₀ : ℂ} (hM : MandelDim.MsetStatement)
    (hc₀ : c₀ ∈ frontier LeanEval.Dynamics.MandelbrotBoundary.Mandelbrot)
    {N : ℕ} (hN : 2 ≤ N) {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {ρ a : ℝ}
    {phi : ℂ → (ℕ → Fin N) → ℂ} (hρ : 0 < ρ)
    (hMD : Work.Transfer.MotionData c₀ N τ n p ρ a phi) :
    ∃ (m : ℕ) (c₁ : ℂ) (w : ℕ → Fin N), c₁ ∈ Metric.ball c₀ ρ ∧
      Work.Transfer.critOrbit m c₁ = phi c₁ w := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  -- two distinct codes
  set x1 : ℕ → Fin N := fun _ => ⟨0, by omega⟩ with hx1
  set x2 : ℕ → Fin N := fun _ => ⟨1, by omega⟩ with hx2
  have hx12 : x1 ≠ x2 := by
    intro h
    have h0 : x1 0 = x2 0 := congrFun h 0
    rw [hx1, hx2] at h0
    have h01 : (0 : ℕ) = 1 := Fin.ext_iff.mp h0
    exact absurd h01 (by decide)
  -- the moving denominators never vanish
  have hden : ∀ c ∈ Metric.ball c₀ ρ, phi c x2 - phi c x1 ≠ 0 := by
    intro c hc h
    exact hx12 ((hMD.inj c hc (sub_eq_zero.mp h)).symm)
  -- the divided family is holomorphic ...
  have hWdiff : ∀ m : ℕ, DifferentiableOn ℂ
      (fun c => (critOrbit m c - phi c x1) / (phi c x2 - phi c x1)) (Metric.ball c₀ ρ) := by
    intro m
    have h1' : DifferentiableOn ℂ (fun c => critOrbit m c - phi c x1) (Metric.ball c₀ ρ) :=
      (differentiableOn_critOrbit m (Metric.ball c₀ ρ)).sub (hMD.diff x1)
    have h2' : DifferentiableOn ℂ (fun c => phi c x2 - phi c x1) (Metric.ball c₀ ρ) :=
      (hMD.diff x2).sub (hMD.diff x1)
    exact h1'.div h2' hden
  -- ... and omits the two values `0` and `1`, so it is normal (Montel)
  have hnorm : Work.Normal.IsNormalFamily
      (Set.range fun m : ℕ => fun c : ℂ => (critOrbit m c - phi c x1) / (phi c x2 - phi c x1))
      (Metric.ball c₀ ρ) := by
    refine Work.Normal.montel_two_omitted (a := (0:ℂ)) (b := 1) zero_ne_one
      Metric.isOpen_ball (convex_ball c₀ ρ).isPreconnected ?_ ?_
    · rintro f ⟨m, rfl⟩
      exact hWdiff m
    · rintro f ⟨m, rfl⟩ z hz
      constructor
      · intro h
        rw [div_eq_zero_iff] at h
        rcases h with h | h
        · exact hcon m z x1 hz (sub_eq_zero.mp h)
        · exact hden z hz h
      · intro h
        rw [div_eq_one_iff_eq (hden z hz)] at h
        refine hcon m z x2 hz ?_
        have h' := congrArg (fun t => t + phi z x1) h
        simpa using h'
  -- a point of the disc outside `M`
  obtain ⟨c', hc'ball, hc'M⟩ := exists_not_mem_ball_of_frontier hc₀ hρ
  -- the values at `c₀ ∈ M` are bounded
  have hc₀M : c₀ ∈ Mandelbrot := frontier_subset_mandelbrot hM hc₀
  have hbdd : ∃ B : ℝ, ∀ m : ℕ,
      ‖(critOrbit m c₀ - phi c₀ x1) / (phi c₀ x2 - phi c₀ x1)‖ ≤ B := by
    refine ⟨(2 + ‖phi c₀ x1‖) / ‖phi c₀ x2 - phi c₀ x1‖, fun m => ?_⟩
    have hbd : ‖critOrbit m c₀‖ ≤ 2 := by
      rw [critOrbit_eq_iterate_zero]
      exact hM.2.2.1 c₀ hc₀M (m + 1)
    have hδ : 0 < ‖phi c₀ x2 - phi c₀ x1‖ :=
      norm_pos_iff.mpr (hden c₀ (mem_ball_self hρ))
    rw [norm_div]
    refine div_le_div_of_nonneg_right ?_ hδ.le
    calc ‖critOrbit m c₀ - phi c₀ x1‖ ≤ ‖critOrbit m c₀‖ + ‖phi c₀ x1‖ := norm_sub_le _ _
      _ ≤ 2 + ‖phi c₀ x1‖ := by linarith
  -- while at `c' ∉ M` the critical orbit escapes
  have hden' : phi c' x2 ≠ phi c' x1 := fun h => hx12 ((hMD.inj c' hc'ball h).symm)
  have hesc : Tendsto (fun m : ℕ => ‖critOrbit m c'‖) atTop atTop :=
    tendsto_norm_critOrbit_atTop_of_not_mem hM hc'M
  exact not_isNormalFamily_div (V := fun n => critOrbit n) (U := Metric.ball c₀ ρ)
    (c₀ := c₀) (c' := c') (h1 := fun c => phi c x1) (h2 := fun c => phi c x2)
    (mem_ball_self hρ) hc'ball hbdd hden' hesc hnorm

end Work.Transfer
