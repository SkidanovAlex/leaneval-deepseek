import Mathlib
import Submission.Work.Drive.Mono.Geom3Defs
import Submission.Work.Drive.Final.LTypes
import Submission.Work.Drive.Mono.Band.BandChartDefs

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set

/-!
# The corner-direction bad set is null

`Work.Drive.Final.crossDir v k = v × e_k` is the corner push direction attached to the vertical box
face with free coordinate `σ k` (`Work.Drive.Final.AnyEventDefs`), and
`Work.Drive.Mono.Band.dirOf τ a₀ b₀` is the unit vector along `τ • a₀ + b₀`, the wall normal of the
band at projective coordinate `τ` (`Work.Drive.Mono.Band.BandChartDefs`).

This file proves `Work.Drive.Mono.g3_corner_dir_bad_null`: the set of pairs `(h, τ)` for which some
*corner direction* `v × e_{σ i}` (`i ≠ 2`) is annihilated by the wall normal `dirOf τ a₀ b₀` is
Lebesgue-null in `ℝ²`.  The `h`-coordinate is irrelevant, so the statement is really about the
`τ`-slice.

## The mathematics

Fix `i ≠ 2` and write `w = v × e_{σ i}`, `A = ⟪a₀, w⟫`, `B = ⟪b₀, w⟫`.  Since
`dirOf τ a₀ b₀ = ‖τ • a₀ + b₀‖⁻¹ • (τ • a₀ + b₀)` and the normalising factor never vanishes,

`⟪dirOf τ a₀ b₀, w⟫ = 0  ⟺  τ A + B = 0`.

So the `τ`-fibre is a *singleton* whenever `(A, B) ≠ (0, 0)`, and the whole set is null.

The pair `(A, B)` cannot vanish: `w` is orthogonal to `v` (it is a cross product with `v`), so if
also `A = B = 0` then `w` is orthogonal to the orthonormal triple `(v, a₀, b₀)`, hence `w = 0` —
this is exactly `Work.Drive.Mono.Band.projV_coord_eq_zero`.  But `v × e_{σ i} = 0` forces `v` to be a
multiple of `e_{σ i}`, which is precisely what `haxis` forbids (after normalising `v ↓ b • e_k` with
`‖v‖ = 1` gives `e_k = b⁻¹ • v`).
-/

variable {a₀ b₀ : R3}

/-- **The second factor of a vanishing corner direction.**  If `v × e_k = 0` then `v` is a multiple
of the coordinate vector `e_k`. -/
theorem crossDir_eq_zero_imp_exists_smul_single (v : R3) (k : Fin 3)
    (h : Work.Drive.Final.crossDir v k = 0) :
    ∃ b : ℝ, v = b • EuclideanSpace.single k (1 : ℝ) := by
  fin_cases k
  · refine ⟨v.ofLp 0, ?_⟩
    have h1 : v 2 = 0 := by
      have := congrArg (fun x : R3 => x.ofLp 1) h
      simpa [Work.Drive.Final.crossDir] using this
    have h2 : v 1 = 0 := by
      have := congrArg (fun x : R3 => x.ofLp 2) h
      simpa [Work.Drive.Final.crossDir] using this
    apply PiLp.ext
    intro m
    fin_cases m <;> simp [h1, h2]
  · refine ⟨v.ofLp 1, ?_⟩
    have h0 : v 2 = 0 := by
      have := congrArg (fun x : R3 => x.ofLp 0) h
      simpa [Work.Drive.Final.crossDir] using this
    have h2 : v 0 = 0 := by
      have := congrArg (fun x : R3 => x.ofLp 2) h
      simpa [Work.Drive.Final.crossDir] using this
    apply PiLp.ext
    intro m
    fin_cases m <;> simp [h0, h2]
  · refine ⟨v.ofLp 2, ?_⟩
    have h0 : v 1 = 0 := by
      have := congrArg (fun x : R3 => x.ofLp 0) h
      simpa [Work.Drive.Final.crossDir] using this
    have h1 : v 0 = 0 := by
      have := congrArg (fun x : R3 => x.ofLp 1) h
      simpa [Work.Drive.Final.crossDir] using this
    apply PiLp.ext
    intro m
    fin_cases m <;> simp [h0, h1]

/-- The corner direction `v × e_k` is orthogonal to `v`. -/
theorem inner_v_crossDir (v : R3) (k : Fin 3) :
    inner ℝ v (Work.Drive.Final.crossDir v k) = 0 := by
  fin_cases k <;> simp [Work.Drive.Final.crossDir, PiLp.inner_apply, Fin.sum_univ_three] <;> ring

/-- **The wall normal against a fixed vector.**  The normalising factor `‖τ • a₀ + b₀‖⁻¹` is
irrelevant for the vanishing of the pairing: the equation `⟪dirOf τ a₀ b₀, w⟫ = 0` is the *linear*
equation `τ ⟪a₀,w⟫ + ⟪b₀,w⟫ = 0` in `τ`. -/
theorem inner_dirOf_eq_inv_mul (a₀ b₀ w : R3) (τ : ℝ) :
    inner ℝ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) w
      = (‖τ • a₀ + b₀‖)⁻¹ * (τ * inner ℝ a₀ w + inner ℝ b₀ w) := by
  rw [Work.Drive.Mono.Band.dirOf, real_inner_smul_left, inner_add_left, real_inner_smul_left]

/-- **`Work.Drive.Mono.g3_corner_dir_bad_null`.**  For an orthonormal pair `(a₀, b₀)` orthogonal to
the unit wall normal `v`, and a unit `v` not parallel to any coordinate axis, the pairs
`(h, τ)` at which some corner direction `v × e_{σ i}` (`i ≠ 2`) is killed by the wall normal
`dirOf τ a₀ b₀` form a Lebesgue-null set. -/
theorem g3_corner_dir_bad_null (v a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3))
    (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    (haxis : ∀ i : Fin 3, ∀ a : ℝ, EuclideanSpace.single (σ i) (1 : ℝ) ≠ a • v) :
    MeasureTheory.volume {x : ℝ × ℝ | ∃ i : Fin 3, i ≠ 2 ∧
      (innerSL ℝ) (Work.Drive.Mono.Band.dirOf x.2 a₀ b₀)
        (Work.Drive.Final.crossDir v (σ i)) = 0}
      = 0 := by
  classical
  -- the two coefficients `⟪a₀, v × e_{σ i}⟫`, `⟪b₀, v × e_{σ i}⟫` cannot both vanish
  have hpair : ∀ i : Fin 3, i ≠ 2 →
      ¬(inner ℝ a₀ (Work.Drive.Final.crossDir v (σ i)) = 0 ∧
        inner ℝ b₀ (Work.Drive.Final.crossDir v (σ i)) = 0) := by
    intro i hi hboth
    have hwv : inner ℝ v (Work.Drive.Final.crossDir v (σ i)) = 0 := inner_v_crossDir v (σ i)
    have hw0 : Work.Drive.Final.crossDir v (σ i) = 0 :=
      Work.Drive.Mono.Band.projV_coord_eq_zero hv ha hb hab hva hvb hwv hboth.1 hboth.2
    obtain ⟨b, hb'⟩ := crossDir_eq_zero_imp_exists_smul_single v (σ i) hw0
    have hbne : b ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hb'
      rw [hb', norm_zero] at hv
      norm_num at hv
    exact haxis i b⁻¹ (by rw [hb', smul_smul, inv_mul_cancel₀ hbne, one_smul])
  -- each `i ≠ 2` contributes a null set
  have hnull_i : ∀ i : Fin 3, i ≠ 2 → volume {x : ℝ × ℝ |
      (innerSL ℝ) (Work.Drive.Mono.Band.dirOf x.2 a₀ b₀)
        (Work.Drive.Final.crossDir v (σ i)) = 0} = 0 := by
    intro i hi
    -- the linear equation in `τ` read off a vanishing pairing
    have key : ∀ s : ℝ, (innerSL ℝ) (Work.Drive.Mono.Band.dirOf s a₀ b₀)
        (Work.Drive.Final.crossDir v (σ i)) = 0 →
          s * inner ℝ a₀ (Work.Drive.Final.crossDir v (σ i))
            + inner ℝ b₀ (Work.Drive.Final.crossDir v (σ i)) = 0 := by
      intro s hs
      rw [innerSL_apply_apply, inner_dirOf_eq_inv_mul] at hs
      exact (mul_eq_zero.mp hs).resolve_left
        (inv_ne_zero (norm_ne_zero_iff.mpr (Work.Drive.Mono.Band.dirOf_denom_ne_zero ha hb hab s)))
    -- the `τ`-fibre is a subsingleton
    have hsing : ({τ : ℝ | (innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)
        (Work.Drive.Final.crossDir v (σ i)) = 0} : Set ℝ).Subsingleton := by
      intro τ hτ τ' hτ'
      have h1 := key τ hτ
      have h2 := key τ' hτ'
      have hA : inner ℝ a₀ (Work.Drive.Final.crossDir v (σ i)) ≠ 0 := by
        intro hA0
        rw [hA0, mul_zero, zero_add] at h1
        exact hpair i hi ⟨hA0, h1⟩
      have h3 : (τ - τ') * inner ℝ a₀ (Work.Drive.Final.crossDir v (σ i)) = 0 := by linarith
      have : τ - τ' = 0 := (mul_eq_zero.mp h3).resolve_right hA
      linarith
    -- a subsingleton is null, and the product with `ℝ` is null
    have hmeas := hsing.measure_zero (volume : Measure ℝ)
    rw [show {x : ℝ × ℝ | (innerSL ℝ) (Work.Drive.Mono.Band.dirOf x.2 a₀ b₀)
        (Work.Drive.Final.crossDir v (σ i)) = 0}
        = Set.univ ×ˢ {τ : ℝ | (innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)
          (Work.Drive.Final.crossDir v (σ i)) = 0} from by ext x; simp]
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, hmeas, mul_zero]
  rw [show {x : ℝ × ℝ | ∃ i : Fin 3, i ≠ 2 ∧
        (innerSL ℝ) (Work.Drive.Mono.Band.dirOf x.2 a₀ b₀)
          (Work.Drive.Final.crossDir v (σ i)) = 0}
      = ⋃ i : {i : Fin 3 // i ≠ 2}, {x : ℝ × ℝ |
          (innerSL ℝ) (Work.Drive.Mono.Band.dirOf x.2 a₀ b₀)
            (Work.Drive.Final.crossDir v (σ i.1)) = 0} from by
    ext x; simp [Set.mem_iUnion, Subtype.exists]]
  exact measure_iUnion_null fun i => hnull_i i.1 i.2

end Work.Drive.Mono
