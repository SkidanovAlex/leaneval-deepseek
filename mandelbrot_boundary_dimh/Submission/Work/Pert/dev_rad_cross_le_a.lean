import Mathlib
import Submission.Work.Pert.CoordDefs
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.dev_deriv_bound_jourA
import Submission.Work.Pert.dev_arith_rad_cross_a

namespace Work.Pert

/-- The oscillation of `dev Ψ = Ψ - id` for a Fatou coordinate `Ψ` of the near-translation
`F = liftF u σ α` on the gate `Qm ξ₁ α`, in the form the `PertCoordClose` assembly consumes.

`JourA η` (in `CoordDefs.lean`) is `Om η = closedBall (iη) (13η/40) ∪ closedBall (-iη) (13η/40)`
together with the two chords joining `±iη` to `-η`; it is connected, so it carries a path
`iη → -η → -iη`.

ROUTE.  Put `v = F - id`, `ṽ = v - 1`; from `hvt` `‖v - 1‖ ≤ 1/32` on `JourA`, so
`‖D'‖ = ‖Ψ' - 1‖ ≤ ‖Ψ' - 1/v‖ + ‖1/v - 1‖ ≤ 1/10⁴ + (32/31)‖ṽ‖` on `JourA` (the points of
`JourA` are in `Qc` by `hJc`, so `hder` applies), and by `hvl` plus `hbdd`/`hτ`
`‖ṽ‖ ≤ (3/2)(2‖τ_f‖ + δu) ≤ (3/2)(2·(4/η) + δu)`, so
`‖D'‖ ≤ 1/10⁴ + 3.1·(4/η) + 1.548 δu` on `JourA`.
* Radial part: for `ζ ∈ closedBall (iη) (13η/40)` integrate along the segment `[iη, ζ]`
  (length `≤ 0.325η`, the segment lies in the convex disc `⊆ JourA`): this gives
  `≤ (1.5 δu + 1/3000) η + 20`.
* Cross part: integrate `D'` along the two chords `iη → -η` and `-η → -iη` (each of length
  `η√2`): this gives `‖D(iη) - D(-iη)‖ ≤ (5 δu + 1/1000) η + 100`.
The constants are what matter: the final assembly has only ≈ 1.15 of margin. -/
theorem dev_rad_cross_le_a {ξ₁ η rr δu : ℝ} {u : ℂ → ℂ} {σ α : ℂ} {Ψ : ℂ → ℂ}
    (hη : 100 ≤ η) (hξ₁ : 0 < ξ₁) (h2ξ : 2 * ξ₁ < η) (hδu : 0 ≤ δu)
    (hΨ : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Ψ (Work.Pert.Qm ξ₁ α))
    (hder : ∀ ζ ∈ Work.Pert.Qc η ξ₁ α,
      ‖deriv Ψ ζ - 1 / (Work.Pert.liftF u σ α ζ - ζ)‖ ≤ 1 / 10000)
    (hbdd : ∀ z ∈ Metric.ball 0 rr, ‖u z‖ ≤ 2)
    (hvt : ∀ ζ ∈ Work.Pert.JourA η, ‖Work.Pert.liftF u σ α ζ - (ζ + 1)‖ ≤ 1 / 32)
    (hJc : ∀ ζ ∈ Work.Pert.JourA η, ζ ∈ Work.Pert.Qc η ξ₁ α)
    (hτ : ∀ ζ ∈ Work.Pert.JourA η, Work.Pert.tauC σ α ζ ∈ Metric.ball 0 rr)
    (hτb : ∀ ζ ∈ Work.Pert.JourA η, ‖Work.Pert.tauC σ α ζ‖ ≤ 4 / η)
    (hvl : ∀ ζ ∈ Work.Pert.JourA η,
      ‖Work.Pert.liftF u σ α ζ - (ζ + 1)‖ ≤
        (3 / 2) * (‖Work.Pert.tauC σ α ζ‖ * ‖u (Work.Pert.tauC σ α ζ)‖ + δu)) :
    (∀ ζ ∈ Metric.closedBall (Complex.I * (η : ℂ)) (13 * η / 40),
        ‖Work.Pert.dev Ψ ζ - Work.Pert.dev Ψ (Complex.I * (η : ℂ))‖
          ≤ (3 / 2 * δu + 1 / 3000) * η + 20) ∧
    (∀ ζ ∈ Metric.closedBall (-(Complex.I * (η : ℂ))) (13 * η / 40),
        ‖Work.Pert.dev Ψ ζ - Work.Pert.dev Ψ (-(Complex.I * (η : ℂ)))‖
          ≤ (3 / 2 * δu + 1 / 3000) * η + 20) ∧
    (‖Work.Pert.dev Ψ (Complex.I * (η : ℂ)) - Work.Pert.dev Ψ (-(Complex.I * (η : ℂ)))‖
        ≤ (5 * δu + 1 / 1000) * η + 100) := by
  have hη0 : (0 : ℝ) < η := by linarith
  obtain ⟨hdQ, hdb⟩ := dev_deriv_bound_jourA hη hΨ hder hbdd hvt hJc hτ hτb hvl
  obtain ⟨harithrad, harithcross⟩ := dev_arith_rad_cross_a hη hδu
  have hC0 : 0 ≤ 1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu) := by
    have h1 : (0 : ℝ) < 12 / η := div_pos (by norm_num) hη0
    nlinarith [hδu]
  have hJ1 : ∀ z ∈ Metric.closedBall (Complex.I * (η : ℂ)) (13 * η / 40),
      z ∈ Work.Pert.JourA η := by
    intro z hz
    simp only [Work.Pert.JourA, Work.Pert.Om, Set.mem_union, Set.mem_ofPred_eq]
    tauto
  have hJ2 : ∀ z ∈ Metric.closedBall (-(Complex.I * (η : ℂ))) (13 * η / 40),
      z ∈ Work.Pert.JourA η := by
    intro z hz
    simp only [Work.Pert.JourA, Work.Pert.Om, Set.mem_union, Set.mem_ofPred_eq]
    tauto
  have hJs1 : ∀ z ∈ segment ℝ (Complex.I * (η : ℂ)) (-(η : ℂ)), z ∈ Work.Pert.JourA η := by
    intro z hz
    rw [segment_eq_image] at hz
    obtain ⟨t, ht, htz⟩ := hz
    simp only [Work.Pert.JourA, Work.Pert.Om, Set.mem_union, Set.mem_ofPred_eq]
    refine Or.inl (Or.inr ⟨t, ht, ?_⟩)
    rw [← htz]
    simp only [Complex.real_smul]
    push_cast
    ring
  have hJs2 : ∀ z ∈ segment ℝ (-(η : ℂ)) (-(Complex.I * (η : ℂ))), z ∈ Work.Pert.JourA η := by
    intro z hz
    rw [segment_eq_image] at hz
    obtain ⟨t, ht, htz⟩ := hz
    simp only [Work.Pert.JourA, Work.Pert.Om, Set.mem_union, Set.mem_ofPred_eq]
    refine Or.inr ⟨t, ht, ?_⟩
    rw [← htz]
    simp only [Complex.real_smul]
    push_cast
    ring
  have hrad : ∀ c : ℂ,
      (∀ ζ ∈ Metric.closedBall c (13 * η / 40), ζ ∈ Work.Pert.JourA η) →
      ∀ ζ ∈ Metric.closedBall c (13 * η / 40),
        ‖Work.Pert.dev Ψ ζ - Work.Pert.dev Ψ c‖ ≤ (3 / 2 * δu + 1 / 3000) * η + 20 := by
    intro c hsub ζ hζ
    have hMVT := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := Work.Pert.dev Ψ) (s := Metric.closedBall c (13 * η / 40))
      (C := 1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu))
      (fun z hz => (hdQ z (hsub z hz)).sub differentiableAt_id)
      (fun z hz => hdb z (hsub z hz))
      (convex_closedBall c (13 * η / 40))
      (Metric.mem_closedBall_self (by linarith)) hζ
    have hdist : ‖ζ - c‖ ≤ 13 * η / 40 := by
      have h := Metric.mem_closedBall.mp hζ
      rwa [dist_eq_norm] at h
    calc ‖Work.Pert.dev Ψ ζ - Work.Pert.dev Ψ c‖
        ≤ (1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu)) * ‖ζ - c‖ := hMVT
      _ ≤ (1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu)) * (13 * η / 40) :=
          mul_le_mul_of_nonneg_left hdist hC0
      _ ≤ (3 / 2 * δu + 1 / 3000) * η + 20 := harithrad
  refine ⟨hrad (Complex.I * (η : ℂ)) hJ1, hrad (-(Complex.I * (η : ℂ))) hJ2, ?_⟩
  have hle1 : ‖-(η : ℂ) - Complex.I * (η : ℂ)‖ ≤ 3 * η / 2 := by
    have he : -(η : ℂ) - Complex.I * (η : ℂ) = (η : ℂ) * (-(1 + Complex.I)) := by ring
    rw [he, norm_mul, norm_neg]
    have hηn : ‖(η : ℂ)‖ = η := by
      rw [show ‖(η : ℂ)‖ = |η| from RCLike.norm_ofReal η, abs_of_nonneg (le_of_lt hη0)]
    rw [hηn]
    have hI : ‖(1 : ℂ) + Complex.I‖ ≤ 3 / 2 := by
      have h2 : ‖(1 : ℂ) + Complex.I‖ ^ 2 = 2 := by
        rw [Complex.sq_norm]; norm_num [Complex.normSq, Complex.ext_iff]
      nlinarith [norm_nonneg ((1 : ℂ) + Complex.I), h2]
    nlinarith [hI, hη0]
  have hle2 : ‖-(Complex.I * (η : ℂ)) - -(η : ℂ)‖ ≤ 3 * η / 2 := by
    have he : -(Complex.I * (η : ℂ)) - -(η : ℂ) = (η : ℂ) * ((1 : ℂ) - Complex.I) := by ring
    rw [he, norm_mul]
    have hηn : ‖(η : ℂ)‖ = η := by
      rw [show ‖(η : ℂ)‖ = |η| from RCLike.norm_ofReal η, abs_of_nonneg (le_of_lt hη0)]
    rw [hηn]
    have hI : ‖(1 : ℂ) - Complex.I‖ ≤ 3 / 2 := by
      have h2 : ‖(1 : ℂ) - Complex.I‖ ^ 2 = 2 := by
        rw [Complex.sq_norm]; norm_num [Complex.normSq, Complex.ext_iff]
      nlinarith [norm_nonneg ((1 : ℂ) - Complex.I), h2]
    nlinarith [hI, hη0]
  have hc1 : ‖Work.Pert.dev Ψ (Complex.I * (η : ℂ)) - Work.Pert.dev Ψ (-(η : ℂ))‖
      ≤ (1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu)) * (3 * η / 2) := by
    have hMVT := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := Work.Pert.dev Ψ) (s := segment ℝ (Complex.I * (η : ℂ)) (-(η : ℂ)))
      (C := 1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu))
      (fun z hz => (hdQ z (hJs1 z hz)).sub differentiableAt_id)
      (fun z hz => hdb z (hJs1 z hz))
      (convex_segment _ _) (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    calc ‖Work.Pert.dev Ψ (Complex.I * (η : ℂ)) - Work.Pert.dev Ψ (-(η : ℂ))‖
        = ‖Work.Pert.dev Ψ (-(η : ℂ)) - Work.Pert.dev Ψ (Complex.I * (η : ℂ))‖ := norm_sub_rev _ _
      _ ≤ (1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu))
            * ‖-(η : ℂ) - Complex.I * (η : ℂ)‖ := hMVT
      _ ≤ (1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu)) * (3 * η / 2) :=
          mul_le_mul_of_nonneg_left hle1 hC0
  have hc2 : ‖Work.Pert.dev Ψ (-(η : ℂ)) - Work.Pert.dev Ψ (-(Complex.I * (η : ℂ)))‖
      ≤ (1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu)) * (3 * η / 2) := by
    have hMVT := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := Work.Pert.dev Ψ) (s := segment ℝ (-(η : ℂ)) (-(Complex.I * (η : ℂ))))
      (C := 1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu))
      (fun z hz => (hdQ z (hJs2 z hz)).sub differentiableAt_id)
      (fun z hz => hdb z (hJs2 z hz))
      (convex_segment _ _) (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    calc ‖Work.Pert.dev Ψ (-(η : ℂ)) - Work.Pert.dev Ψ (-(Complex.I * (η : ℂ)))‖
        = ‖Work.Pert.dev Ψ (-(Complex.I * (η : ℂ))) - Work.Pert.dev Ψ (-(η : ℂ))‖ := norm_sub_rev _ _
      _ ≤ (1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu))
            * ‖-(Complex.I * (η : ℂ)) - -(η : ℂ)‖ := hMVT
      _ ≤ (1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu)) * (3 * η / 2) :=
          mul_le_mul_of_nonneg_left hle2 hC0
  have htri := norm_add_le (Work.Pert.dev Ψ (Complex.I * (η : ℂ)) - Work.Pert.dev Ψ (-(η : ℂ)))
    (Work.Pert.dev Ψ (-(η : ℂ)) - Work.Pert.dev Ψ (-(Complex.I * (η : ℂ))))
  rw [show Work.Pert.dev Ψ (Complex.I * (η : ℂ)) - Work.Pert.dev Ψ (-(η : ℂ))
        + (Work.Pert.dev Ψ (-(η : ℂ)) - Work.Pert.dev Ψ (-(Complex.I * (η : ℂ))))
      = Work.Pert.dev Ψ (Complex.I * (η : ℂ)) - Work.Pert.dev Ψ (-(Complex.I * (η : ℂ))) by ring] at htri
  calc ‖Work.Pert.dev Ψ (Complex.I * (η : ℂ)) - Work.Pert.dev Ψ (-(Complex.I * (η : ℂ)))‖
      ≤ (1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu)) * (3 * η / 2)
        + (1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu)) * (3 * η / 2) := by
          linarith [htri, hc1, hc2]
    _ = (1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu)) * (3 * η) := by ring
    _ ≤ (5 * δu + 1 / 1000) * η + 100 := harithcross


end Work.Pert
