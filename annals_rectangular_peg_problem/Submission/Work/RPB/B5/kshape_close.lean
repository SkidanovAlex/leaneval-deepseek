import Mathlib
import Submission.Work.RPB.B5.kappaSmallAux
import Submission.Work.RPB.B5.kshape_near_close
import Submission.Work.RPB.B5.kshape_far_close

/-!
# B5: the glued shape `kshape` is uniformly `C¹`-close to the reference curve `√2·CI.c`

On the range `σ ∈ [0, δ]` the glued shape
`kshape = (1 - kblf δ σ) · knear + kblf δ σ · kfsh` is a convex combination of its two branches:

* the near branch `knear` is the reduced coordinate of the chart at the clamped level
  `kclamp δ σ` (so that `ρh` is only evaluated on `(-δ,δ) ⊆ (-κ,κ)`), together with the `τ = 0`
  correction which fades out at `σ ≥ 0`;
* the far branch `kfsh` has saturated at `σ ≤ δ` to the rescaled curve `krd σ · CI.c τ`.

The two branch estimates are `Work.RPB.B5.kshape_near_close` (which uses the hypothesis `hchart`
that the chart slice is `C¹`-close to `√2 · CI.c τ`, and gives the bound `3A/8`) and
`Work.RPB.B5.kshape_far_close` (which gives the bound `A/8`, from `|krd σ - √2| ≤ √2 σ` and the
uniform bound `‖deriv CI.c‖ ≤ M`).  Since `0 ≤ kblf ≤ 1`, the convex combination obeys
`≤ max (3A/8) (A/8) ≤ 3A/8 < A`.
-/

namespace Work.RPB.B5

theorem kshape_close (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ) (A : ℝ) (hA : 0 < A) (M : ℝ) (hM : 0 < M)
    (hδ : 0 < δ) (hM1 : 1 ≤ M) (hδM : Real.sqrt 2 * δ * M ≤ A / 8)
    (hchart : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, |σ| ≤ δ → ∀ t : ℝ,
      ‖Work.RPV.uproj (W τ t (ρh τ t σ)) - (Real.sqrt 2 : ℂ) * CI.c τ t‖ < A / 8 ∧
      ‖deriv (fun u : ℝ => Work.RPV.uproj (W τ u (ρh τ u σ))) t
        - deriv (fun u : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ u) t‖ < A / 8)
    (hslice : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, |σ| ≤ δ →
      ContDiff ℝ 1 (fun t : ℝ => Work.RPV.uproj (W τ t (ρh τ t σ))))
    (hbound : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖CI.c τ t‖ ≤ M ∧ ‖deriv (fun s : ℝ => CI.c τ s) t‖ ≤ M) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ ∈ Set.Icc (0 : ℝ) δ, ∀ t : ℝ,
      ‖Work.RPB.B5.kshape CI W ρh δ k τ σ t - (Real.sqrt 2 : ℂ) * CI.c τ t‖ < A ∧
      ‖deriv (fun s : ℝ => Work.RPB.B5.kshape CI W ρh δ k τ σ s) t
        - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t‖ < A := by
  have _hm : 0 < M := hM
  intro τ hτ σ hσ t
  -- `√2 · σ ≤ √2 · δ ≤ √2 · δ · M ≤ A/8` for `σ ≤ δ` and `M ≥ 1`
  have hδA : Real.sqrt 2 * δ ≤ A / 8 := by
    have h2 : 0 ≤ Real.sqrt 2 * δ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hM1 h2, hδM]
  obtain ⟨hdn, hvn, hdn'⟩ :=
    kshape_near_close CI W ρh δ A k hδ hA hδA hchart hslice τ hτ σ hσ t
  obtain ⟨hdf, hvf, hdf'⟩ :=
    kshape_far_close CI δ A M k hδ hA hM1 hbound hδM τ hτ σ hσ t
  have hb1 : 0 ≤ 1 - kblf δ σ := by linarith [kblf_le_one δ σ]
  have hb2 : 0 ≤ kblf δ σ := kblf_nonneg δ σ
  refine ⟨?_, ?_⟩
  · -- value: the convex combination of the two branch estimates
    have hdec : kshape CI W ρh δ k τ σ t - (Real.sqrt 2 : ℂ) * CI.c τ t
        = ((1 - kblf δ σ : ℝ) : ℂ) * (knear CI W ρh δ k τ σ t - (Real.sqrt 2 : ℂ) * CI.c τ t)
          + ((kblf δ σ : ℝ) : ℂ) * (kfsh CI δ k τ σ t - (Real.sqrt 2 : ℂ) * CI.c τ t) := by
      simp only [kshape]
      push_cast
      ring
    rw [hdec]
    have h1 : ‖((1 - kblf δ σ : ℝ) : ℂ)
          * (knear CI W ρh δ k τ σ t - (Real.sqrt 2 : ℂ) * CI.c τ t)‖
        ≤ (1 - kblf δ σ) * (3 * A / 8) := by
      have hnorm1 : ‖((1 - kblf δ σ : ℝ) : ℂ)‖ = |1 - kblf δ σ| :=
        RCLike.norm_ofReal (K := ℂ) (1 - kblf δ σ)
      rw [norm_mul, hnorm1, abs_of_nonneg hb1]
      exact mul_le_mul_of_nonneg_left hvn hb1
    have h2 : ‖((kblf δ σ : ℝ) : ℂ) * (kfsh CI δ k τ σ t - (Real.sqrt 2 : ℂ) * CI.c τ t)‖
        ≤ kblf δ σ * (A / 8) := by
      have hnorm2 : ‖((kblf δ σ : ℝ) : ℂ)‖ = |kblf δ σ| :=
        RCLike.norm_ofReal (K := ℂ) (kblf δ σ)
      rw [norm_mul, hnorm2, abs_of_nonneg hb2]
      exact mul_le_mul_of_nonneg_left hvf hb2
    have h2' : kblf δ σ * (A / 8) ≤ kblf δ σ * (3 * A / 8) :=
      mul_le_mul_of_nonneg_left (by linarith) hb2
    have hfold : (1 - kblf δ σ) * (3 * A / 8) + kblf δ σ * (3 * A / 8) = 3 * A / 8 := by ring
    have htot := norm_add_le (((1 - kblf δ σ : ℝ) : ℂ)
          * (knear CI W ρh δ k τ σ t - (Real.sqrt 2 : ℂ) * CI.c τ t))
        (((kblf δ σ : ℝ) : ℂ) * (kfsh CI δ k τ σ t - (Real.sqrt 2 : ℂ) * CI.c τ t))
    linarith [htot, h1, h2, h2', hfold, hA,
      norm_nonneg (((1 - kblf δ σ : ℝ) : ℂ)
          * (knear CI W ρh δ k τ σ t - (Real.sqrt 2 : ℂ) * CI.c τ t)),
      norm_nonneg (((kblf δ σ : ℝ) : ℂ)
          * (kfsh CI δ k τ σ t - (Real.sqrt 2 : ℂ) * CI.c τ t))]
  · -- derivative: differentiate the convex combination and apply the branch estimates
    have hSn : HasDerivAt (fun s : ℝ => knear CI W ρh δ k τ σ s)
        (deriv (fun s : ℝ => knear CI W ρh δ k τ σ s) t) t := hdn.hasDerivAt
    have hSf : HasDerivAt (fun s : ℝ => kfsh CI δ k τ σ s)
        (deriv (fun s : ℝ => kfsh CI δ k τ σ s) t) t := hdf.hasDerivAt
    have hS : HasDerivAt (fun s : ℝ => kshape CI W ρh δ k τ σ s)
        (((1 - kblf δ σ : ℝ) : ℂ) * deriv (fun s : ℝ => knear CI W ρh δ k τ σ s) t
          + ((kblf δ σ : ℝ) : ℂ) * deriv (fun s : ℝ => kfsh CI δ k τ σ s) t) t := by
      have hcomb := (hSn.const_mul ((1 - kblf δ σ : ℝ) : ℂ)).add
        (hSf.const_mul ((kblf δ σ : ℝ) : ℂ))
      have hfun : (fun s : ℝ => kshape CI W ρh δ k τ σ s)
          = fun s : ℝ => ((1 - kblf δ σ : ℝ) : ℂ) * knear CI W ρh δ k τ σ s
              + ((kblf δ σ : ℝ) : ℂ) * kfsh CI δ k τ σ s := by
        funext s
        simp only [kshape]
        push_cast
        ring
      rw [hfun]
      exact hcomb
    have hderivS : deriv (fun s : ℝ => kshape CI W ρh δ k τ σ s) t
        = ((1 - kblf δ σ : ℝ) : ℂ) * deriv (fun s : ℝ => knear CI W ρh δ k τ σ s) t
          + ((kblf δ σ : ℝ) : ℂ) * deriv (fun s : ℝ => kfsh CI δ k τ σ s) t := hS.deriv
    rw [hderivS]
    have hdec2 : ((1 - kblf δ σ : ℝ) : ℂ) * deriv (fun s : ℝ => knear CI W ρh δ k τ σ s) t
          + ((kblf δ σ : ℝ) : ℂ) * deriv (fun s : ℝ => kfsh CI δ k τ σ s) t
          - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t
        = ((1 - kblf δ σ : ℝ) : ℂ)
            * (deriv (fun s : ℝ => knear CI W ρh δ k τ σ s) t
                - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t)
          + ((kblf δ σ : ℝ) : ℂ)
            * (deriv (fun s : ℝ => kfsh CI δ k τ σ s) t
                - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t) := by
      push_cast
      ring
    rw [hdec2]
    have h1 : ‖((1 - kblf δ σ : ℝ) : ℂ)
          * (deriv (fun s : ℝ => knear CI W ρh δ k τ σ s) t
              - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t)‖
        ≤ (1 - kblf δ σ) * (3 * A / 8) := by
      have hnorm1 : ‖((1 - kblf δ σ : ℝ) : ℂ)‖ = |1 - kblf δ σ| :=
        RCLike.norm_ofReal (K := ℂ) (1 - kblf δ σ)
      rw [norm_mul, hnorm1, abs_of_nonneg hb1]
      exact mul_le_mul_of_nonneg_left hdn' hb1
    have h2 : ‖((kblf δ σ : ℝ) : ℂ)
          * (deriv (fun s : ℝ => kfsh CI δ k τ σ s) t
              - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t)‖
        ≤ kblf δ σ * (A / 8) := by
      have hnorm2 : ‖((kblf δ σ : ℝ) : ℂ)‖ = |kblf δ σ| :=
        RCLike.norm_ofReal (K := ℂ) (kblf δ σ)
      rw [norm_mul, hnorm2, abs_of_nonneg hb2]
      exact mul_le_mul_of_nonneg_left hdf' hb2
    have h2' : kblf δ σ * (A / 8) ≤ kblf δ σ * (3 * A / 8) :=
      mul_le_mul_of_nonneg_left (by linarith) hb2
    have hfold : (1 - kblf δ σ) * (3 * A / 8) + kblf δ σ * (3 * A / 8) = 3 * A / 8 := by ring
    have htot := norm_add_le (((1 - kblf δ σ : ℝ) : ℂ)
          * (deriv (fun s : ℝ => knear CI W ρh δ k τ σ s) t
              - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t))
        (((kblf δ σ : ℝ) : ℂ)
          * (deriv (fun s : ℝ => kfsh CI δ k τ σ s) t
              - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t))
    linarith [htot, h1, h2, h2', hfold, hA,
      norm_nonneg (((1 - kblf δ σ : ℝ) : ℂ)
          * (deriv (fun s : ℝ => knear CI W ρh δ k τ σ s) t
              - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t)),
      norm_nonneg (((kblf δ σ : ℝ) : ℂ)
          * (deriv (fun s : ℝ => kfsh CI δ k τ σ s) t
              - deriv (fun s : ℝ => (Real.sqrt 2 : ℂ) * CI.c τ s) t))]

end Work.RPB.B5
