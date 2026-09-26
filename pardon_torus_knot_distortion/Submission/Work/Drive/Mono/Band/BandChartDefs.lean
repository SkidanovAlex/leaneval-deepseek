import Mathlib
import Submission.Work.Drive.Mono.Band.BadFaceDefs
import Submission.Work.Drive.Mono.BoxWidth

/-!
# The projective chart of the Gauss normal of the thin slab

For the band data one fixes a unit direction `v` (the slab direction) and an orthonormal pair
`a₀, b₀` of `v^⊥`.  Every direction `n ⊥ v` is then `cos θ • a₀ + sin θ • b₀` for a unique `θ`
modulo `π`, i.e. is described by the *projective* coordinate `cot θ`.

The Gauss normal of the surface of the challenge, projected orthogonally to `v`, is
`projVv ψ v p = N p - ⟪v, N p⟫ • v` (parallel to `v × N p`); on the open set where its `b₀`-component
`betaV ψ v b₀ p` does not vanish, the *projective direction* of that projection is the chart

  `bandChart ψ v a₀ b₀ p = (⟪v, par ψ p⟫, alphaV ψ v a₀ p / betaV ψ v b₀ p)`.

The point of the chart is the identity

  `⟪v × n, N p⟫ = 0  ⟺  projV p` is parallel to `n`  ⟺  `alphaV/betaV = cot θ`

for `n = cos θ • a₀ + sin θ • b₀` with `sin θ ≠ 0`, so that the "bad face points" for the slab
direction `v` and the wall normal `n` are exactly the points whose `bandChart` value is
`(⟪v, par p⟫, cot θ)`.
-/

namespace Work.Drive.Mono.Band

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-- The Gauss normal of the challenge surface, projected orthogonally to the direction `v`. -/
abbrev projVv (ψ : Submission.Diffeo) (v : R3) : ℝ × ℝ → R3 :=
  projV (Work.BoxShrink.Pinch.par ψ) v

/-- The `a₀`-component of the normal projected to `v^⊥`. -/
def alphaV (ψ : Submission.Diffeo) (v a₀ : R3) : ℝ × ℝ → ℝ :=
  fun p => inner ℝ a₀ (projVv ψ v p)

/-- The `b₀`-component of the normal projected to `v^⊥`. -/
def betaV (ψ : Submission.Diffeo) (v b₀ : R3) : ℝ × ℝ → ℝ :=
  fun p => inner ℝ b₀ (projVv ψ v p)

/-- The height in the direction `v` of the parametrised surface, read in the parameter plane. -/
def heightV (ψ : Submission.Diffeo) (v : R3) : ℝ × ℝ → ℝ :=
  fun p => inner ℝ v (Work.BoxShrink.Pinch.par ψ p)

/-- **The projective chart of the Gauss normal.** -/
def bandChart (ψ : Submission.Diffeo) (v a₀ b₀ : R3) : ℝ × ℝ → ℝ × ℝ :=
  fun p => (heightV ψ v p, alphaV ψ v a₀ p / betaV ψ v b₀ p)

/-- The open set on which the chart is defined: the `b₀`-component of the projected normal does not
vanish. -/
def chartDomain (ψ : Submission.Diffeo) (v b₀ : R3) : Set (ℝ × ℝ) :=
  {p | betaV ψ v b₀ p ≠ 0}

theorem par_contDiff_three' (ψ : Submission.Diffeo) :
    ContDiff ℝ 3 (Work.BoxShrink.Pinch.par ψ) := par_contDiff_three ψ

/-- The projected normal is `C²`. -/
theorem contDiff_projVv (ψ : Submission.Diffeo) (v : R3) :
    ContDiff ℝ 2 (projVv ψ v) :=
  contDiff_projV (par_contDiff_three ψ) v

/-- The `a₀`-component is `C²`. -/
theorem contDiff_alphaV (ψ : Submission.Diffeo) (v a₀ : R3) :
    ContDiff ℝ 2 (alphaV ψ v a₀) := by
  unfold alphaV
  exact (innerSL ℝ a₀).contDiff.comp (contDiff_projVv ψ v)

/-- The `b₀`-component is `C²`. -/
theorem contDiff_betaV (ψ : Submission.Diffeo) (v b₀ : R3) :
    ContDiff ℝ 2 (betaV ψ v b₀) := by
  unfold betaV
  exact (innerSL ℝ b₀).contDiff.comp (contDiff_projVv ψ v)

/-- The height in direction `v` is `C²`. -/
theorem contDiff_heightV (ψ : Submission.Diffeo) (v : R3) :
    ContDiff ℝ 2 (heightV ψ v) := by
  have h3 : ContDiff ℝ 2 (Work.BoxShrink.Pinch.par ψ) :=
    (par_contDiff_three ψ).of_le (by norm_num)
  unfold heightV
  exact (innerSL ℝ v).contDiff.comp h3

/-- **A vector orthogonal to the three vectors of an orthonormal triple vanishes.** -/
theorem projV_coord_eq_zero {v a₀ b₀ X : R3} (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0)
    (hvX : inner ℝ v X = 0) (haX : inner ℝ a₀ X = 0) (hbX : inner ℝ b₀ X = 0) : X = 0 := by
  have h2' := Work.Drive.Mono.Band.crossExpansion (X := b₀) hv ha hva
  rw [hvb, hab] at h2'
  have h2 : (inner ℝ (Work.Drive.Generic.crossE v a₀) b₀)
      • (Work.Drive.Generic.crossE v a₀) = b₀ := by
    simpa using h2'
  set c : ℝ := inner ℝ (Work.Drive.Generic.crossE v a₀) b₀ with hc
  have hc0 : c ≠ 0 := by
    intro h0
    have h3 : b₀ = 0 := by rw [← h2, h0, zero_smul]
    rw [h3] at hb
    simp at hb
  have hcross : Work.Drive.Generic.crossE v a₀ = c⁻¹ • b₀ := by
    rw [← h2, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have h1' := Work.Drive.Mono.Band.crossExpansion (X := X) hv ha hva
  rw [hvX, haX, hcross] at h1'
  rw [real_inner_smul_left, hbX, mul_zero, zero_smul] at h1'
  simp only [zero_smul, add_zero] at h1'
  exact h1'.symm

theorem chartDomain_isOpen (ψ : Submission.Diffeo) (v b₀ : R3) :
    IsOpen (chartDomain ψ v b₀) :=
  isOpen_ne.preimage (contDiff_betaV ψ v b₀).continuous

/-! ## The unit direction of a given projective coordinate -/

/-- **The unit direction of projective coordinate `τ`** in the orthonormal pair `(a₀,b₀)`: the unit
vector in the direction `τ • a₀ + b₀`.  Its `a₀`- and `b₀`-components have ratio `τ`. -/
noncomputable def dirOf (τ : ℝ) (a₀ b₀ : R3) : R3 :=
  (‖τ • a₀ + b₀‖)⁻¹ • (τ • a₀ + b₀)

variable {a₀ b₀ : R3}

theorem inner_b₀_add_dirOf (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) (τ : ℝ) :
    inner ℝ b₀ (τ • a₀ + b₀) = 1 := by
  rw [inner_add_right, real_inner_smul_right]
  rw [show inner ℝ b₀ a₀ = 0 from by rw [real_inner_comm]; exact hab]
  rw [real_inner_self_eq_norm_sq, hb]
  ring

theorem dirOf_denom_ne_zero (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) (τ : ℝ) :
    τ • a₀ + b₀ ≠ 0 := by
  intro h0
  have h1 := inner_b₀_add_dirOf ha hb hab τ
  rw [h0, inner_zero_right] at h1
  exact one_ne_zero h1.symm

theorem norm_dirOf (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) (τ : ℝ) :
    ‖dirOf τ a₀ b₀‖ = 1 :=
  norm_smul_inv_norm (dirOf_denom_ne_zero ha hb hab τ)

theorem dirOf_ne_zero (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) (τ : ℝ) :
    dirOf τ a₀ b₀ ≠ 0 := by
  intro h0
  have h1 := norm_dirOf ha hb hab τ
  rw [h0, norm_zero] at h1
  exact one_ne_zero h1.symm

theorem inner_a₀_dirOf (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) (τ : ℝ) :
    inner ℝ a₀ (dirOf τ a₀ b₀) = τ * (‖τ • a₀ + b₀‖)⁻¹ := by
  rw [dirOf, real_inner_smul_right, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, ha]
  rw [show inner ℝ a₀ b₀ = 0 from hab]
  ring

theorem inner_b₀_dirOf (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) (τ : ℝ) :
    inner ℝ b₀ (dirOf τ a₀ b₀) = (‖τ • a₀ + b₀‖)⁻¹ := by
  rw [dirOf, real_inner_smul_right, inner_add_right, real_inner_smul_right]
  rw [show inner ℝ b₀ a₀ = 0 from by rw [real_inner_comm]; exact hab]
  rw [real_inner_self_eq_norm_sq, hb]
  ring

theorem inner_v_dirOf {v : R3} (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) (τ : ℝ) :
    inner ℝ v (dirOf τ a₀ b₀) = 0 := by
  rw [dirOf, real_inner_smul_right, inner_add_right, real_inner_smul_right, hva, hvb]
  ring

theorem norm_add_basis (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) :
    ‖a₀ + b₀‖ = Real.sqrt 2 := by
  have h : ‖a₀ + b₀‖ ^ 2 = 2 := by
    rw [norm_add_sq_real, ha, hb]
    rw [show inner ℝ a₀ b₀ = 0 from hab]
    norm_num
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

theorem dirOf_one (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) {n : R3}
    (hn : n = (Real.sqrt 2)⁻¹ • (a₀ + b₀)) : dirOf 1 a₀ b₀ = n := by
  rw [dirOf, one_smul, norm_add_basis ha hb hab, hn]

/-- The second coordinate of the chart is `C¹` on its domain. -/
theorem contDiffOn_chart_snd (ψ : Submission.Diffeo) (v a₀ b₀ : R3) :
    ContDiffOn ℝ 1 (fun p => alphaV ψ v a₀ p / betaV ψ v b₀ p) (chartDomain ψ v b₀) := by
  refine ContDiffOn.div ?_ ?_ ?_
  · exact (contDiff_alphaV ψ v a₀).contDiffOn.of_le (by norm_num)
  · exact (contDiff_betaV ψ v b₀).contDiffOn.of_le (by norm_num)
  · intro p hp
    exact hp

/-- The chart is `C¹` on its domain. -/
theorem contDiffOn_bandChart (ψ : Submission.Diffeo) (v a₀ b₀ : R3) :
    ContDiffOn ℝ 1 (bandChart ψ v a₀ b₀) (chartDomain ψ v b₀) :=
  ((contDiff_heightV ψ v).contDiffOn.of_le (by norm_num)).prodMk
    (contDiffOn_chart_snd ψ v a₀ b₀)

end

end Work.Drive.Mono.Band
