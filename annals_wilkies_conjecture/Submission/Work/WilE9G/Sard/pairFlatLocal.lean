import Mathlib
import Submission.Work.WilE9G.Sard.pairFlatOrderSucc
import Submission.Work.WilE9G.Sard.exists_cutoff_supp_infty

/-!
# Local pairwise flatness of order `J + 2` on the `(J+1)`-flat set

If `f : ℝᵈ → ℝᵏ` is only assumed to be `C^{J+2}` on a ball around a point `x`, and all iterated
derivatives of `f` of orders `1, …, J+1` vanish at every point of a set `A` containing `x`, then
`f` is flat of order `J + 2` along `A` at `x`, with an arbitrarily small constant:

`‖f y - f x‖ ≤ ε ‖y - x‖^{J+2}`   for all `y ∈ A` close enough to `x`.

This is the local companion of the global `Work.WilE9G.Sard.pairFlatOrderSucc`.  The passage from
the local hypothesis `ContDiffOn ℝ (J+2) f (ball x R)` to the global one is done with a smooth
cutoff: for a bump `χ` which equals `1` on a ball around `x` and whose support is contained in
`ball x R`, the product `z ↦ χ z • f z` is globally `C^{J+2}` and agrees with `f` in a neighbourhood
of `x`.  Since `iteratedFDeriv` is a local operation, the flatness hypothesis transfers to the
product on the part of `A` lying in that neighbourhood, and the global `pairFlatOrderSucc` applies.
-/

namespace Work.WilE9G.Sard

open MeasureTheory Metric Filter
open scoped Topology

set_option autoImplicit false

theorem pairFlatLocal {d k J : ℕ} (f : (Fin d → ℝ) → (Fin k → ℝ)) (A : Set (Fin d → ℝ)) {x : Fin d → ℝ}
    (hxA : x ∈ A) {R : ℝ} (hR : 0 < R)
    (hf : ContDiffOn ℝ ((J + 2 : ℕ) : WithTop ℕ∞) f (Metric.ball x R))
    (hA : A ⊆ {z : Fin d → ℝ | ∀ i, 1 ≤ i → i ≤ J + 1 → iteratedFDeriv ℝ i f z = 0}) :
    ∀ ε > 0, ∃ ρ > 0, ∀ y ∈ A, ‖y - x‖ ≤ ρ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ (J + 2) := by
  -- A smooth bump which is `1` on a ball around `x` and supported in the ball where `f` is smooth.
  obtain ⟨g, r, hrpos, hgsm, hg1, hgsupp⟩ :=
    exists_bump_nhds (W := Metric.ball x R) Metric.isOpen_ball (Metric.mem_ball_self hR)
  set G : (Fin d → ℝ) → (Fin k → ℝ) := fun z => g z • f z with hGdef
  have hgcont : ContDiff ℝ ((J + 2 : ℕ) : WithTop ℕ∞) g := hgsm.of_le (by simp)
  -- ## `G` is globally `C^{J+2}`
  have hGcd : ContDiff ℝ ((J + 2 : ℕ) : WithTop ℕ∞) G := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ Metric.ball x R
    · -- inside the ball both factors are smooth
      have hfz : ContDiffAt ℝ ((J + 2 : ℕ) : WithTop ℕ∞) f z :=
        hf.contDiffAt (Metric.isOpen_ball.mem_nhds hz)
      have hgz : ContDiffAt ℝ ((J + 2 : ℕ) : WithTop ℕ∞) g z := hgcont.contDiffAt
      rw [hGdef]
      exact hgz.smul hfz
    · -- outside the support of `g` the product vanishes near `z`
      have hz' : z ∉ tsupport g := fun h => hz (hgsupp h)
      have hop : (tsupport g)ᶜ ∈ 𝓝 z := (isClosed_tsupport g).isOpen_compl.mem_nhds hz'
      have hzero : G =ᶠ[𝓝 z] (fun _ => (0 : Fin k → ℝ)) := by
        filter_upwards [hop] with w hw
        simp only [hGdef]
        rw [image_eq_zero_of_notMem_tsupport hw, zero_smul]
      rw [hGdef]
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hzero
  -- ## `G` satisfies the flatness hypothesis on `A ∩ ball x r`
  set A' : Set (Fin d → ℝ) := A ∩ Metric.ball x r with hA'def
  have hA'sub : A' ⊆ {z : Fin d → ℝ |
      ∀ i, 1 ≤ i → i ≤ J + 1 → iteratedFDeriv ℝ i G z = 0} := by
    intro z hz i hi hiJ
    obtain ⟨hzA, hzr⟩ := hz
    have hzeq : G =ᶠ[𝓝 z] f := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzr] with w hw
      simp only [hGdef]
      rw [hg1 w hw, one_smul]
    have hGz : G z = f z := by simp only [hGdef, hg1 z hzr, one_smul]
    have key : iteratedFDeriv ℝ i G z = iteratedFDeriv ℝ i f z := by
      have h2 := Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℝ) (s := Set.univ)
        (by simpa only [nhdsWithin_univ] using hzeq) hGz i
      simpa only [iteratedFDerivWithin_univ] using h2
    rw [key]
    exact hA hzA i hi hiJ
  -- ## Apply the global flatness lemma to `G`
  intro ε hε
  have hpair := pairFlatOrderSucc (f := G) (j := J) hGcd A' hA'sub
  obtain ⟨ρ, hρpos, hρ⟩ := hpair x ⟨hxA, Metric.mem_ball_self hrpos⟩ ε hε
  refine ⟨min ρ (r / 2), lt_min hρpos (by linarith), fun y hyA hyρ => ?_⟩
  have hyρ' : ‖y - x‖ ≤ ρ := le_trans hyρ (min_le_left _ _)
  have hyr : ‖y - x‖ < r := by
    have h2 : ‖y - x‖ ≤ r / 2 := le_trans hyρ (min_le_right _ _)
    linarith
  have hyA' : y ∈ A' := ⟨hyA, Metric.mem_ball.mpr hyr⟩
  have h1 := hρ y hyA' hyρ'
  -- replace `G` by `f`, which they are equal to on the ball of radius `r`
  have hyG : G y = f y := by simp only [hGdef, hg1 y (Metric.mem_ball.mpr hyr), one_smul]
  have hxG : G x = f x := by simp only [hGdef, hg1 x (Metric.mem_ball_self hrpos), one_smul]
  rwa [hyG, hxG] at h1

end Work.WilE9G.Sard
