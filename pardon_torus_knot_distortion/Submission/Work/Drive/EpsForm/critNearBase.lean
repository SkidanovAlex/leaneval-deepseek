import Mathlib
import Submission.Work.Drive.EpsForm.no_crit_off_balls
import Submission.Work.Drive.EpsForm.goodHeight_exists

/-!
# Critical points of nearby height directions

Fix a diffeomorphism `ψ` of `ℝ³` (the surface is `ψ` of the standard torus) and a direction
`n₀ ∈ ℝ³`.  The height of the surface in the direction `n`, read in the parameter plane of the
parametrisation `par ψ`, is

  `q ↦ inner ℝ n (par ψ q)`,

whose critical points are the zeros of `fderiv ℝ (fun q => inner ℝ n (par ψ q))`.

This file proves that **critical points in the fundamental square depend upper semi-continuously on
the direction**: for every `ε > 0` there is `δ > 0` such that every critical point `p ∈ [0,2π]²` of
the height in a direction `n` with `‖n - n₀‖ < δ` is within `ε` of a critical point of the height
in the direction `n₀`.

No Morse (nondegeneracy) hypothesis is needed: the argument is a compactness one.  Writing
`D p = fderiv ℝ (par ψ) p` for the derivative of the parametrisation, the derivative of the height
in direction `n` is the continuous linear form `(innerSL ℝ n) ∘L D p`, and

  `(innerSL ℝ n) ∘L D p = (innerSL ℝ n₀) ∘L D p + (innerSL ℝ (n - n₀)) ∘L D p`,

the correction being bounded by `‖n - n₀‖ · sup ‖D‖`.  So on the compact set of points of the
square that are at distance `≥ ε` from every critical point of the height at `n₀` — where the norm
of `(innerSL ℝ n₀) ∘L D` has a positive lower bound — the derivative in direction `n` cannot
vanish for `n` close to `n₀`.

This is the statement `critNearBase` consumed by the sideways-sweep argument of Pardon's proof
(the sweep moves the direction continuously and the critical points do not jump out of the square).
-/

open scoped Topology

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-- The derivative of the parametrisation of the surface, as a map on the parameter plane. -/
def parDeriv (ψ : Submission.Diffeo) : ℝ × ℝ → (ℝ × ℝ →L[ℝ] R3) :=
  fderiv ℝ (Work.BoxShrink.Pinch.par ψ)

/-- The derivative of the parametrisation is continuous (the parametrisation is `C^∞`). -/
theorem parDeriv_continuous (ψ : Submission.Diffeo) : Continuous (parDeriv ψ) := by
  show Continuous (fderiv ℝ (Work.BoxShrink.Pinch.par ψ))
  exact (Work.BoxShrink.Pinch.par_contDiff ψ).continuous_fderiv (by norm_num)

/-- The derivative of the height in direction `n` is `(innerSL ℝ n)` composed with the derivative
of the parametrisation. -/
theorem fderiv_height_eq (ψ : Submission.Diffeo) (n : R3) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p
      = (innerSL ℝ n) ∘L parDeriv ψ p := by
  show fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p
      = (innerSL ℝ n) ∘L fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p
  have hd : DifferentiableAt ℝ (Work.BoxShrink.Pinch.par ψ) p :=
    ((Work.BoxShrink.Pinch.par_contDiff ψ).differentiable (by simp)).differentiableAt
  refine ContinuousLinearMap.ext fun y => ?_
  have h := fderiv_inner_apply (𝕜 := ℝ) (x := p) (G := ℝ × ℝ) (E := R3)
    (f := fun _ : ℝ × ℝ => n) (g := Work.BoxShrink.Pinch.par ψ)
    (differentiableAt_const n) hd y
  rw [h]
  simp only [ContinuousLinearMap.comp_apply]
  rw [innerSL_apply_apply]
  have hzero : fderiv ℝ (fun _ : ℝ × ℝ => n) p = 0 := by simp
  rw [hzero]
  simp

/-- **Critical points nearby directions stay near critical points of the base direction.**

Let `D : ℝ² → (ℝ² →L[ℝ] E)` be continuous, `K` compact and `r > 0`.  Then for all directions `n`
close enough to `n₀`, every zero in `K` of the linear form `(innerSL ℝ n) ∘L D` is within `r` of a
zero of `(innerSL ℝ n₀) ∘L D` (which may be anywhere). -/
theorem critNear_of_continuous (D : ℝ × ℝ → (ℝ × ℝ →L[ℝ] R3)) (hD : Continuous D)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (n₀ : R3) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : R3, ‖n - n₀‖ < δ → ∀ p ∈ K,
      ((innerSL ℝ n) ∘L D p) = 0 →
      ∃ x : ℝ × ℝ, ((innerSL ℝ n₀) ∘L D x) = 0 ∧ ‖p - x‖ < r := by
  classical
  -- the `r`-neighbourhood of the critical set of the base direction, and its complement in `K`
  set U : Set (ℝ × ℝ) :=
    ⋃ x ∈ {x : ℝ × ℝ | ((innerSL ℝ n₀) ∘L D x) = 0}, Metric.ball x r with hUdef
  set A : Set (ℝ × ℝ) := K \ U with hAdef
  have hUopen : IsOpen U := by rw [hUdef]; exact isOpen_biUnion fun x _ => Metric.isOpen_ball
  have hAclosed : IsClosed A := by rw [hAdef]; exact hK.isClosed.sdiff hUopen
  have hAcomp : IsCompact A := hK.of_isClosed_subset hAclosed Set.sdiff_subset
  have hmemU : ∀ p : ℝ × ℝ, p ∈ U ↔ ∃ x, ((innerSL ℝ n₀) ∘L D x) = 0 ∧ ‖p - x‖ < r := by
    intro p
    rw [hUdef, Set.mem_iUnion₂]
    constructor
    · rintro ⟨x, hx, hpx⟩
      exact ⟨x, hx, by rwa [Metric.mem_ball, dist_eq_norm] at hpx⟩
    · rintro ⟨x, hx, hpx⟩
      exact ⟨x, hx, by rwa [Metric.mem_ball, dist_eq_norm]⟩
  by_cases hAne : A.Nonempty
  · -- `A` carries no critical point of the base direction, so `‖(innerSL ℝ n₀) ∘L D‖` is bounded
    -- below on `A` by a positive constant
    have hcont0 : Continuous (fun p : ℝ × ℝ => (innerSL ℝ n₀) ∘L D p) :=
      ((((ContinuousLinearMap.compL ℝ (ℝ × ℝ) R3 ℝ) (innerSL ℝ n₀))).continuous).comp hD
    obtain ⟨c, hcA, hcmin⟩ := hAcomp.exists_isMinOn hAne hcont0.continuousOn.norm
    have hcA' : c ∈ K ∧ c ∉ U := by simpa [hAdef] using hcA
    have hm_pos : 0 < ‖((innerSL ℝ n₀) ∘L D c)‖ := by
      rw [norm_pos_iff]
      intro hcrit
      exact hcA'.2 (by
        rw [hUdef]
        exact Set.mem_iUnion₂.mpr ⟨c, hcrit, Metric.mem_ball_self hr⟩)
    -- the derivative of the parametrisation is bounded on `A`
    obtain ⟨M, hM⟩ := hAcomp.exists_bound_of_continuousOn hD.continuousOn
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM c hcA)
    refine ⟨‖((innerSL ℝ n₀) ∘L D c)‖ / (2 * (M + 1)), ?_, ?_⟩
    · apply div_pos hm_pos; linarith
    · intro n hn p hpK hcrit
      by_contra hcon
      have hcon' : ∀ x, ((innerSL ℝ n₀) ∘L D x) = 0 → r ≤ ‖p - x‖ := by
        intro x hx
        by_contra hlt
        exact hcon ⟨x, hx, not_le.mp hlt⟩
      have hpnotU : p ∉ U := fun hmem => by
        obtain ⟨x, hx, hpx⟩ := (hmemU p).mp hmem
        exact absurd hpx (not_lt.mpr (hcon' x hx))
      have hpA : p ∈ A := by rw [hAdef]; exact ⟨hpK, hpnotU⟩
      -- the two derivatives differ by the `n - n₀` correction
      have hdecomp : (innerSL ℝ n) ∘L D p =
          ((innerSL ℝ n₀) ∘L D p) + ((innerSL ℝ (n - n₀)) ∘L D p) := by
        refine ContinuousLinearMap.ext fun y => ?_
        simp only [add_apply, ContinuousLinearMap.comp_apply]
        rw [innerSL_apply_apply, innerSL_apply_apply, innerSL_apply_apply, inner_sub_left]
        ring
      have hb : ‖(innerSL ℝ (n - n₀)) ∘L D p‖ ≤ ‖n - n₀‖ * M := by
        calc ‖(innerSL ℝ (n - n₀)) ∘L D p‖
            ≤ ‖(innerSL ℝ (n - n₀))‖ * ‖D p‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ = ‖n - n₀‖ * ‖D p‖ := by rw [innerSL_apply_norm]
          _ ≤ ‖n - n₀‖ * M := mul_le_mul_of_nonneg_left (hM p hpA) (norm_nonneg _)
      have hδpos : 0 < ‖((innerSL ℝ n₀) ∘L D c)‖ / (2 * (M + 1)) := by
        apply div_pos hm_pos; linarith
      have hδM : (‖((innerSL ℝ n₀) ∘L D c)‖ / (2 * (M + 1))) * M
          ≤ ‖((innerSL ℝ n₀) ∘L D c)‖ / 2 := by
        have h1 : (‖((innerSL ℝ n₀) ∘L D c)‖ / (2 * (M + 1))) * M
            ≤ (‖((innerSL ℝ n₀) ∘L D c)‖ / (2 * (M + 1))) * (M + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hδpos.le
        have h2 : (‖((innerSL ℝ n₀) ∘L D c)‖ / (2 * (M + 1))) * (M + 1)
            = ‖((innerSL ℝ n₀) ∘L D c)‖ / 2 := by
          rw [div_mul_eq_mul_div, mul_comm (‖((innerSL ℝ n₀) ∘L D c)‖) (M + 1),
            mul_comm 2 (M + 1)]
          exact mul_div_mul_left _ 2 (by linarith)
        linarith
      have hlt : ‖n - n₀‖ * M < ‖((innerSL ℝ n₀) ∘L D c)‖ := by
        have h1 : ‖n - n₀‖ * M ≤ (‖((innerSL ℝ n₀) ∘L D c)‖ / (2 * (M + 1))) * M :=
          mul_le_mul_of_nonneg_right (le_of_lt hn) hMnn
        have h2 : ‖((innerSL ℝ n₀) ∘L D c)‖ / 2 < ‖((innerSL ℝ n₀) ∘L D c)‖ := by linarith
        linarith
      -- so the derivative in direction `n` does not vanish at `p ∈ A`
      have hnorm : 0 < ‖(innerSL ℝ n) ∘L D p‖ := by
        rw [hdecomp]
        have htri : ‖((innerSL ℝ n₀) ∘L D p)‖ ≤
            ‖((innerSL ℝ n₀) ∘L D p) + ((innerSL ℝ (n - n₀)) ∘L D p)‖
              + ‖(innerSL ℝ (n - n₀)) ∘L D p‖ := by
          calc ‖(innerSL ℝ n₀) ∘L D p‖
              = ‖(((innerSL ℝ n₀) ∘L D p) + ((innerSL ℝ (n - n₀)) ∘L D p))
                  - ((innerSL ℝ (n - n₀)) ∘L D p)‖ := by rw [add_sub_cancel_right]
            _ ≤ ‖((innerSL ℝ n₀) ∘L D p) + ((innerSL ℝ (n - n₀)) ∘L D p)‖
                  + ‖(innerSL ℝ (n - n₀)) ∘L D p‖ := norm_sub_le _ _
        have hmin : ‖((innerSL ℝ n₀) ∘L D c)‖ ≤ ‖((innerSL ℝ n₀) ∘L D p)‖ := hcmin hpA
        linarith
      exact (norm_pos_iff.mp hnorm) hcrit
  · -- `A` is empty: every point of `K` is already close to a critical point of the base direction
    refine ⟨1, one_pos, ?_⟩
    intro n hn p hpK hcrit
    have hpU : p ∈ U := by
      by_contra hmem
      exact hAne ⟨p, by rw [hAdef]; exact ⟨hpK, hmem⟩⟩
    exact (hmemU p).mp hpU

theorem critNearBase (ψ : Submission.Diffeo) (n₀ : LeanEval.KnotTheory.PardonDistortion.R3) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n : LeanEval.KnotTheory.PardonDistortion.R3, ‖n - n₀‖ < δ → ∀ p : ℝ × ℝ,
        p ∈ Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi) →
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p = 0 →
        ∃ x : ℝ × ℝ,
          fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n₀ (Work.BoxShrink.Pinch.par ψ q)) x = 0 ∧
          ‖p - x‖ < ε := by
  classical
  intro ε hε
  obtain ⟨δ, hδ, hspec⟩ := critNear_of_continuous (parDeriv ψ) (parDeriv_continuous ψ)
    (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)) (isCompact_Icc.prod isCompact_Icc) n₀ hε
  refine ⟨δ, hδ, ?_⟩
  intro n hn p hp hcrit
  have hcrit' : (innerSL ℝ n) ∘L parDeriv ψ p = 0 := by
    rw [← fderiv_height_eq ψ n p]; exact hcrit
  obtain ⟨x, hx, hxr⟩ := hspec n hn p hp hcrit'
  exact ⟨x, by rw [fderiv_height_eq]; exact hx, hxr⟩

end

end Work.Drive.EpsForm
