import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.PertU.geom
import Submission.Work.PertU.asymp
import Submission.Work.PertU.inj_of_deriv_close

/-! Guidance from the project lead (the requester):

AREA PERT-UNPERT (lead, piece of PERT (4.2.5) at f = f₀). Contracts: Submission/Work/Interfaces/Parabolic.lean (ParabData, Dsm, QLeft, tau0).
Route:
(i) Dsm(±η) = closedBall(±iη, η/4) ⊆ QLeft ξ₀ for η large: every w in it has |arg(w + ξ₀)| ∈ (π/2 - 0.26, π/2 + 0.26) once η ≫ ξ₀, and π/3 < π/2 - 0.26.
(ii) φ_asymp gives tau0(d.φ w) = w + a log(-w) + b + o(1) on QLeft. On Dsm(±η) this is |tau0∘φ - w| ≤ |a| log(2η) + |b| + 1 ≤ η/80 for η large.
(iii) Derivative: h(w) := tau0(d.φ w) - w is holomorphic on QLeft with |h(w)| ≤ |a| log|w| + C. The disc of radius η/10 around any point of Dsm(±η) lies in QLeft, so Cauchy's estimate gives |h'| ≤ 10(|a| log(3η) + C)/η < 2/5.
(iv) Injectivity on the convex disc: from |(tau0∘φ)' - 1| < 2/5 < 1 (mean value inequality).
Needs only ParabData.φ_asymp, φ_holo, Q_sub and the chain rule for tau0 ∘ φ (φ ≠ 0 on QLeft: tau0 ∘ φ ≈ w is large).

The three ingredients below are delegated:
* `Work.PertU.geom` — the geometric containment `Dsm(±η) ∪ (radius η/10) ⊆ QLeft ξ₀` and the
  bracket `η/2 ≤ ‖z‖ ≤ 2η` on the fattened set;
* `Work.PertU.asymp` — the pointwise bound `‖tau0(φ w) - w‖ ≤ |a| log(2η) + |a| π + |b| + 1` on
  that set, together with the two arithmetic consequences for large `η`;
* `Work.PertU.inj_of_deriv_close` — a complex map with `‖f' - 1‖ ≤ 1/2` on a convex set is
  injective there.
The Cauchy estimate on the radius-`η/10` disc, the holomorphy of `w ↦ tau0 (d.φ w) - w` (which
uses `d.φ w ≠ 0`, obtained from the pointwise bound), and the assembly are below.
-/

namespace Work.PertU

open MandelDim Metric Set

theorem pert_unpert : ∀ (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (d : ParabData f₀ D₀), IsParabolicGerm f₀ D₀ →
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, η₁ ≤ η →
      Dsm η ∪ Dsm (-η) ⊆ QLeft d.ξ₀ ∧
      InjOn (fun w => tau0 (d.φ w)) (Dsm η) ∧ InjOn (fun w => tau0 (d.φ w)) (Dsm (-η)) ∧
      ∀ w ∈ Dsm η ∪ Dsm (-η), ‖tau0 (d.φ w) - w‖ ≤ |η| / 80 ∧
        3 / 5 < ‖deriv (fun u => tau0 (d.φ u)) w‖ ∧ ‖deriv (fun u => tau0 (d.φ u)) w‖ < 3 / 2 := by
  intro f₀ D₀ d _
  obtain ⟨a, b, hasymp⟩ := d.φ_asymp
  obtain ⟨ηg, hηg, hgeom⟩ := geom d.ξ₀
  obtain ⟨ηa, hηa, hasym⟩ := asymp (ψ := d.φ) (ξ := d.ξ₀) (a := a) (b := b) hasymp
  refine ⟨max ηg ηa, lt_of_lt_of_le hηg (le_max_left _ _), ?_⟩
  intro η hη
  have hg : ηg ≤ η := le_trans (le_max_left _ _) hη
  have ha : ηa ≤ η := le_trans (le_max_right _ _) hη
  obtain ⟨hsub, hballQ, hballN⟩ := hgeom η hg
  obtain ⟨hbound, harith1, harith2⟩ := hasym η ha
  have hηpos : 0 < η := lt_of_lt_of_le hηg hg
  have habs : |η| = η := abs_of_pos hηpos
  set M : ℝ := ‖a‖ * Real.log (2 * η) + ‖a‖ * Real.pi + ‖b‖ + 1 with hMdef
  have hMlt : M < η / 25 := by
    have h10 : 10 * M < (2 / 5) * η := by rw [hMdef]; exact harith1
    linarith
  have hM80 : M ≤ η / 80 := by rw [hMdef]; exact harith2
  -- the fattened set
  have hQ_of : ∀ z : ℂ, (∃ w ∈ Dsm η ∪ Dsm (-η), z ∈ closedBall w (η / 10)) →
      z ∈ QLeft d.ξ₀ := by
    rintro z ⟨w, hw, hz⟩; exact hballQ w hw hz
  have hN_of : ∀ z : ℂ, (∃ w ∈ Dsm η ∪ Dsm (-η), z ∈ closedBall w (η / 10)) →
      η / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * η := by
    rintro z ⟨w, hw, hz⟩; exact hballN w hw z hz
  have hbound_of : ∀ z : ℂ, (∃ w ∈ Dsm η ∪ Dsm (-η), z ∈ closedBall w (η / 10)) →
      ‖tau0 (d.φ z) - z‖ ≤ M := by
    rintro z ⟨w, hw, hz⟩
    have := hbound z (hballQ w hw hz) (hballN w hw z hz).1 (hballN w hw z hz).2
    rwa [hMdef]
  have hne_of : ∀ z : ℂ, (∃ w ∈ Dsm η ∪ Dsm (-η), z ∈ closedBall w (η / 10)) → d.φ z ≠ 0 := by
    rintro z hz hzero
    have h1 := (hN_of z hz).1
    have h2 := hbound_of z hz
    have h3 : tau0 (d.φ z) - z = -z := by simp [hzero, tau0]
    rw [h3, norm_neg] at h2
    linarith
  have hF_of : ∀ z : ℂ, (∃ w ∈ Dsm η ∪ Dsm (-η), z ∈ closedBall w (η / 10)) →
      DifferentiableAt ℂ (fun u => tau0 (d.φ u)) z := by
    rintro z hz
    have hzD : z ∈ d.Dφ := d.Q_sub (hQ_of z hz)
    have hdphi : DifferentiableAt ℂ d.φ z :=
      d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hzD)
    have ht : DifferentiableAt ℂ tau0 (d.φ z) :=
      (differentiableAt_const (-1)).div differentiableAt_id (hne_of z hz)
    exact ht.comp z hdphi
  have hself : ∀ w ∈ Dsm η ∪ Dsm (-η), w ∈ closedBall w (η / 10) := by
    intro w hw
    simp only [mem_closedBall, dist_self]
    linarith
  -- main pointwise statement
  have key : ∀ w ∈ Dsm η ∪ Dsm (-η),
      ‖tau0 (d.φ w) - w‖ ≤ M ∧
      ‖deriv (fun u => tau0 (d.φ u)) w - 1‖ ≤ 1 / 2 ∧
      3 / 5 < ‖deriv (fun u => tau0 (d.φ u)) w‖ ∧
      ‖deriv (fun u => tau0 (d.φ u)) w‖ < 3 / 2 := by
    intro w hw
    have hR : 0 < η / 10 := by linarith
    have hdiff : DifferentiableOn ℂ (fun u => tau0 (d.φ u) - u) (closedBall w (η / 10)) := by
      intro z hz
      have hzT : ∃ w' ∈ Dsm η ∪ Dsm (-η), z ∈ closedBall w' (η / 10) := ⟨w, hw, hz⟩
      exact ((hF_of z hzT).sub differentiableAt_id).differentiableWithinAt
    have hsphere : ∀ z ∈ sphere w (η / 10), ‖tau0 (d.φ z) - z‖ ≤ M := by
      intro z hz
      exact hbound_of z ⟨w, hw, sphere_subset_closedBall hz⟩
    have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
      (hdiff.diffContOnCl_ball subset_rfl) hsphere
    have hrat : M / (η / 10) < 2 / 5 := by
      have h10 : 10 * M < (2 / 5) * η := by rw [hMdef]; exact harith1
      rw [div_div_eq_mul_div, div_lt_iff₀ hηpos]
      linarith
    have hder : ‖deriv (fun u => tau0 (d.φ u) - u) w‖ < 2 / 5 := lt_of_le_of_lt hcau hrat
    have hwT : ∃ w' ∈ Dsm η ∪ Dsm (-η), w ∈ closedBall w' (η / 10) := ⟨w, hw, hself w hw⟩
    have hFeq : deriv (fun u => tau0 (d.φ u)) w
        = deriv (fun u => tau0 (d.φ u) - u) w + 1 := by
      have h2 : HasDerivAt (fun u : ℂ => tau0 (d.φ u))
          (deriv (fun u : ℂ => tau0 (d.φ u)) w) w := (hF_of w hwT).hasDerivAt
      have h3 : HasDerivAt (fun u : ℂ => tau0 (d.φ u) - u)
          (deriv (fun u : ℂ => tau0 (d.φ u)) w - 1) w := h2.sub (hasDerivAt_id w)
      rw [h3.deriv]; ring
    refine ⟨hbound_of w hwT, ?_, ?_, ?_⟩
    · rw [hFeq]; ring_nf; linarith
    · rw [hFeq]
      have h2 : (1 : ℝ) - ‖deriv (fun u => tau0 (d.φ u) - u) w‖
          ≤ ‖deriv (fun u => tau0 (d.φ u) - u) w + 1‖ := by
        have h3 : ‖(1 : ℂ)‖ ≤ ‖deriv (fun u => tau0 (d.φ u) - u) w + 1‖
            + ‖deriv (fun u => tau0 (d.φ u) - u) w‖ := by
          have := norm_sub_le (deriv (fun u => tau0 (d.φ u) - u) w + 1)
            (deriv (fun u => tau0 (d.φ u) - u) w)
          simpa using this
        simpa using h3
      linarith
    · rw [hFeq]
      have h2 : ‖deriv (fun u => tau0 (d.φ u) - u) w + 1‖
          ≤ ‖deriv (fun u => tau0 (d.φ u) - u) w‖ + 1 := by
        have := norm_add_le (deriv (fun u => tau0 (d.φ u) - u) w) (1 : ℂ)
        simpa using this
      linarith
  have key' : ∀ w ∈ Dsm η ∪ Dsm (-η),
      ‖tau0 (d.φ w) - w‖ ≤ |η| / 80 ∧
      3 / 5 < ‖deriv (fun u => tau0 (d.φ u)) w‖ ∧
      ‖deriv (fun u => tau0 (d.φ u)) w‖ < 3 / 2 := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := key w hw
    refine ⟨?_, h3, h4⟩
    rw [habs]
    exact le_trans h1 hM80
  have hinj : ∀ r ∈ ({η, -η} : Set ℝ), InjOn (fun w => tau0 (d.φ w)) (Dsm r) := by
    intro r hr
    have hr' : r = η ∨ r = -η := by simpa using hr
    rcases hr' with rfl | rfl
    · refine inj_of_deriv_close (by unfold Dsm; exact convex_closedBall _ _) ?_ ?_
      · intro z hz
        exact hF_of z ⟨z, Or.inl hz, hself z (Or.inl hz)⟩
      · intro z hz
        exact (key z (Or.inl hz)).2.1
    · refine inj_of_deriv_close (by unfold Dsm; exact convex_closedBall _ _) ?_ ?_
      · intro z hz
        exact hF_of z ⟨z, Or.inr hz, hself z (Or.inr hz)⟩
      · intro z hz
        exact (key z (Or.inr hz)).2.1
  exact ⟨hsub, hinj η (by simp), hinj (-η) (by simp), key'⟩

end Work.PertU
