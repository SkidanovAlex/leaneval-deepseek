import Mathlib

/-!
# Pushing a continuous ball-to-sphere map up one dimension (suspension)

`Work.RPCore.Port.Whitney.exists_retraction_succ`: given a continuous `F : ℝ^d → ℝ^d` which fixes the
unit sphere and maps the closed unit ball onto the sphere, there is a continuous
`G : ℝ^(d+1) → ℝ^(d+1)` with the same two properties.

The proof is the classical **unreduced suspension**: writing a point of `ℝ^(d+1)` as a pair
`(t, y)` with `t : ℝ` the first coordinate and `y : ℝ^d` the complementary block, put
`s = √(1 - t²)` and

  `G (t, y) = (t, s • F (s⁻¹ • y))`.

On the closed unit ball `‖(t, y)‖ ≤ 1` one has `‖y‖ ≤ s`, so `‖s • F (s⁻¹ • y)‖ = s` and
`‖G (t, y)‖² = t² + s² = 1`; on the unit sphere `‖y‖ = s`, so `F (s⁻¹ • y) = s⁻¹ • y` and
`G (t, y) = (t, y)`.  Continuity is the only delicate point: the formula is evaluated at the
argument `s⁻¹ • y`, which blows up when `s = 0` (the two poles `t = ±1`), the compensation being
that the prefactor `s` tends to `0`; for this we first spread `F` to a globally defined map
`Fc = F ∘ (radial clamp into the closed unit ball)`, which is continuous, still equals `F` on the
closed unit ball, and satisfies `‖Fc z‖ = 1` for *every* `z`.  The scaled map
`(σ, y) ↦ σ • Fc (σ⁻¹ • y)` is continuous by a squeeze argument at `σ = 0` (`squeeze_zero_norm`)
and by composition elsewhere.

No topology beyond continuity is used: the statement is proved by exhibiting the above `G` as a
function of `F`; in particular it is *vacuously* applicable, as the hypotheses can only hold when
no such `F` exists in the first place.
-/

namespace Work.RPCore.Port.Whitney

open scoped Topology
open Set Metric Filter

namespace RetractionSucc

variable {d : ℕ}

/-! ### Splitting off the first coordinate -/

/-- The tail `(y₁, …, y_d)` of a vector `(t, y₁, …, y_d) ∈ ℝ^(d+1)`. -/
noncomputable def tailE (x : EuclideanSpace ℝ (Fin (d + 1))) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j : Fin d => x j.succ)

/-- The vector `(a, f) ∈ ℝ^(d+1)` with first coordinate `a` and tail `f`. -/
noncomputable def consE (a : ℝ) (f : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 (Fin.cons a f.ofLp)

lemma tailE_ofLp (x : EuclideanSpace ℝ (Fin (d + 1))) :
    (tailE x).ofLp = fun j : Fin d => x j.succ := by
  simp [tailE]

lemma consE_ofLp (a : ℝ) (f : EuclideanSpace ℝ (Fin d)) :
    (consE a f).ofLp = Fin.cons a f.ofLp := by
  simp [consE]

lemma consE_head_tail (x : EuclideanSpace ℝ (Fin (d + 1))) : consE (x 0) (tailE x) = x := by
  rw [← WithLp.toLp_ofLp (p := 2) x]
  ext i
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · subst h; simp [consE, tailE]
  · simp [consE, tailE]

lemma continuous_tailE : Continuous (tailE (d := d)) := by
  change Continuous
    (fun x : EuclideanSpace ℝ (Fin (d + 1)) => WithLp.toLp 2 (fun j : Fin d => x j.succ))
  refine (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp (continuous_pi (fun j => ?_))
  exact (continuous_apply (Fin.succ j)).comp (PiLp.continuous_ofLp 2 (fun _ : Fin (d + 1) => ℝ))

lemma continuous_head : Continuous (fun x : EuclideanSpace ℝ (Fin (d + 1)) => x 0) :=
  (continuous_apply (0 : Fin (d + 1))).comp (PiLp.continuous_ofLp 2 (fun _ : Fin (d + 1) => ℝ))

/-! ### Pythagorean decompositions -/

/-- `‖(a, f)‖² = a² + ‖f‖²` for the pairing of a real number with a vector. -/
lemma norm_sq_consE (a : ℝ) (f : EuclideanSpace ℝ (Fin d)) :
    ‖consE a f‖ ^ 2 = a ^ 2 + ‖f‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, consE_ofLp, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [← EuclideanSpace.norm_sq_eq f]
  simp [Real.norm_eq_abs, sq_abs]

/-- `‖x‖² = (x 0)² + ‖tail x‖²`: the Pythagorean decomposition in the first coordinate. -/
lemma norm_sq_head_tail (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ‖x‖ ^ 2 = (x 0) ^ 2 + ‖tailE x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  congr 1
  · simp [Real.norm_eq_abs, sq_abs]
  · rw [EuclideanSpace.norm_sq_eq]
    simp [tailE_ofLp]

/-! ### Radial clamp and the global sphere-valued spreading of `F` -/

/-- The radial projection of `ℝ^d` onto its closed unit ball. -/
noncomputable def radialClamp (z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (max 1 ‖z‖)⁻¹ • z

lemma continuous_radialClamp : Continuous (radialClamp (d := d)) := by
  change Continuous (fun z : EuclideanSpace ℝ (Fin d) => (max 1 ‖z‖)⁻¹ • z)
  refine ((continuous_const.max continuous_norm).inv₀ ?_).smul continuous_id
  intro z
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

lemma radialClamp_eq_of_le_one {z : EuclideanSpace ℝ (Fin d)} (hz : ‖z‖ ≤ 1) :
    radialClamp z = z := by
  rw [radialClamp, max_eq_left hz, inv_one, one_smul]

lemma norm_radialClamp_le (z : EuclideanSpace ℝ (Fin d)) : ‖radialClamp z‖ ≤ 1 := by
  have hpos : 0 < max 1 ‖z‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h1 : ‖radialClamp z‖ = (max 1 ‖z‖)⁻¹ * ‖z‖ := by
    rw [radialClamp, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
  rw [h1]
  calc (max 1 ‖z‖)⁻¹ * ‖z‖ ≤ (max 1 ‖z‖)⁻¹ * (max 1 ‖z‖) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr hpos.le)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)

/-- `F` spread to a globally defined map, by first clamping the argument into the closed unit
ball.  It agrees with `F` on the closed unit ball and takes values in the unit sphere
*everywhere*. -/
noncomputable def Fc (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  F (radialClamp z)

lemma continuous_Fc {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hcont : Continuous F) : Continuous (Fc F) :=
  hcont.comp continuous_radialClamp

lemma Fc_eq_of_norm_le {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {z : EuclideanSpace ℝ (Fin d)} (hz : ‖z‖ ≤ 1) : Fc F z = F z := by
  rw [Fc, radialClamp_eq_of_le_one hz]

lemma norm_Fc {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hball : ∀ z, ‖z‖ ≤ 1 → ‖F z‖ = 1) (z : EuclideanSpace ℝ (Fin d)) : ‖Fc F z‖ = 1 := by
  rw [Fc]
  exact hball _ (norm_radialClamp_le z)

/-! ### The scaled (suspension) map `(σ, y) ↦ σ • Fc (σ⁻¹ • y)` -/

/-- The suspension map on pairs, before inserting the coordinate `σ = √(1 - t²)`. -/
noncomputable def suspPhi (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : ℝ × EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  p.1 • Fc F (p.1⁻¹ • p.2)

/-- `suspPhi` is continuous: away from `σ = 0` it is a composition of continuous maps, and at
`σ = 0` it is squeezed to zero by `‖σ • Fc (σ⁻¹ • y)‖ ≤ |σ|`. -/
lemma continuous_suspPhi {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hcont : Continuous F) (hball : ∀ z, ‖z‖ ≤ 1 → ‖F z‖ = 1) :
    Continuous (suspPhi F) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s, y⟩
  by_cases hs : s = 0
  · have hb : ∀ p : ℝ × EuclideanSpace ℝ (Fin d), ‖suspPhi F p‖ ≤ |p.1| := by
      intro p
      rw [suspPhi, norm_smul, Real.norm_eq_abs, norm_Fc hball (p.1⁻¹ • p.2)]
      simp
    have ht : Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin d) => |p.1|) (𝓝 (s, y)) (𝓝 0) := by
      have h := (continuous_fst.abs).continuousAt (x := (s, y))
      rw [ContinuousAt] at h
      simpa [hs] using h
    have h2 : Tendsto (suspPhi F) (𝓝 (s, y)) (𝓝 0) := squeeze_zero_norm hb ht
    have h0 : suspPhi F (s, y) = 0 := by simp [suspPhi, hs]
    simpa [ContinuousAt, h0] using h2
  · have h_inv : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin d) => p.1⁻¹) (s, y) :=
      continuous_fst.continuousAt.inv₀ hs
    have h1 : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin d) => p.1⁻¹ • p.2) (s, y) :=
      h_inv.smul continuous_snd.continuousAt
    have h2 : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin d) => Fc F (p.1⁻¹ • p.2)) (s, y) :=
      (continuous_Fc hcont).continuousAt.comp h1
    exact continuous_fst.continuousAt.smul h2

/-- On the unit sphere the suspension map is the identity: if `‖y‖² = 1 - t²` then
`suspPhi F (√(1 - t²), y) = y`. -/
lemma suspPhi_eq_self_of_norm_sq {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hfix : ∀ x, ‖x‖ = 1 → F x = x)
    {t : ℝ} {y : EuclideanSpace ℝ (Fin d)} (hy : ‖y‖ ^ 2 = 1 - t ^ 2) :
    suspPhi F (Real.sqrt (1 - t ^ 2), y) = y := by
  set s := Real.sqrt (1 - t ^ 2) with hs_def
  have hs : s = ‖y‖ := by
    rw [hs_def, ← hy]
    exact Real.sqrt_sq (norm_nonneg y)
  by_cases hs0 : s = 0
  · have hy0 : y = 0 := norm_eq_zero.mp (by rw [← hs, hs0])
    rw [hy0, hs0]
    simp [suspPhi]
  · have hspos : 0 < s := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs0)
    have hnorm : ‖s⁻¹ • y‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspos), hs]
      exact inv_mul_cancel₀ (by simpa [hs] using hs0)
    calc suspPhi F (s, y) = s • Fc F (s⁻¹ • y) := rfl
      _ = s • F (s⁻¹ • y) := by rw [Fc_eq_of_norm_le (le_of_eq hnorm)]
      _ = s • (s⁻¹ • y) := by rw [hfix _ hnorm]
      _ = y := by rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]

/-- The norm of the suspension map is exactly `√(1 - t²)`, because `Fc` is sphere valued. -/
lemma norm_suspPhi_sqrt {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hball : ∀ z, ‖z‖ ≤ 1 → ‖F z‖ = 1) (t : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    ‖suspPhi F (Real.sqrt (1 - t ^ 2), y)‖ = Real.sqrt (1 - t ^ 2) := by
  rw [suspPhi, norm_smul, Real.norm_eq_abs, norm_Fc hball, mul_one,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-! ### The suspension `G` -/

/-- **The suspended map.**  `G (t, y) = (t, √(1 - t²) • F ((√(1 - t²))⁻¹ • y))`. -/
noncomputable def Gfun (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin (d + 1))) : EuclideanSpace ℝ (Fin (d + 1)) :=
  consE (x 0) (suspPhi F (Real.sqrt (1 - (x 0) ^ 2), tailE x))

lemma continuous_Gfun {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hcont : Continuous F) (hball : ∀ z, ‖z‖ ≤ 1 → ‖F z‖ = 1) : Continuous (Gfun F) := by
  have hhead := continuous_head (d := d)
  have htail := continuous_tailE (d := d)
  have hs : Continuous (fun x : EuclideanSpace ℝ (Fin (d + 1)) => Real.sqrt (1 - (x 0) ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.sub (hhead.pow 2))
  have hpair : Continuous (fun x : EuclideanSpace ℝ (Fin (d + 1)) =>
      (Real.sqrt (1 - (x 0) ^ 2), tailE x)) := Continuous.prodMk hs htail
  have hphi : Continuous (fun x : EuclideanSpace ℝ (Fin (d + 1)) =>
      (suspPhi F (Real.sqrt (1 - (x 0) ^ 2), tailE x)).ofLp) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).comp
      ((continuous_suspPhi hcont hball).comp hpair)
  have hc := Continuous.finCons (n := d) (A := fun _ : Fin (d + 1) => ℝ) hhead hphi
  change Continuous (fun x : EuclideanSpace ℝ (Fin (d + 1)) =>
    WithLp.toLp 2 (Fin.cons (x 0)
      (suspPhi F (Real.sqrt (1 - (x 0) ^ 2), tailE x)).ofLp : Fin (d + 1) → ℝ))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (d + 1) => ℝ)).comp hc

/-- `G` fixes the unit sphere. -/
lemma Gfun_eq_self {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hfix : ∀ x, ‖x‖ = 1 → F x = x)
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : ‖x‖ = 1) : Gfun F x = x := by
  have h : (x 0) ^ 2 + ‖tailE x‖ ^ 2 = 1 := by
    rw [← norm_sq_head_tail x, hx]; norm_num
  have hy : ‖tailE x‖ ^ 2 = 1 - (x 0) ^ 2 := by linarith
  change consE (x 0) (suspPhi F (Real.sqrt (1 - (x 0) ^ 2), tailE x)) = x
  rw [suspPhi_eq_self_of_norm_sq hfix hy, consE_head_tail]

/-- `G` maps the closed unit ball onto the unit sphere. -/
lemma norm_Gfun {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hball : ∀ z, ‖z‖ ≤ 1 → ‖F z‖ = 1)
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : ‖x‖ ≤ 1) : ‖Gfun F x‖ = 1 := by
  have ht2 : (x 0) ^ 2 ≤ 1 := by
    have h := norm_sq_head_tail x
    have h1 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    nlinarith [norm_nonneg (tailE x), sq_nonneg (x 0)]
  have hsq : ‖Gfun F x‖ ^ 2 = 1 := by
    change ‖consE (x 0) (suspPhi F (Real.sqrt (1 - (x 0) ^ 2), tailE x))‖ ^ 2 = 1
    rw [norm_sq_consE, norm_suspPhi_sqrt hball, Real.sq_sqrt (by linarith)]
    ring
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact h
  · exfalso
    have := norm_nonneg (Gfun F x)
    rw [h] at this
    norm_num at this

end RetractionSucc

theorem exists_retraction_succ {d : ℕ}
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hcont : Continuous F) (hfix : ∀ x, ‖x‖ = 1 → F x = x)
    (hball : ∀ x, ‖x‖ ≤ 1 → ‖F x‖ = 1) :
    ∃ G : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)),
        Continuous G ∧ (∀ x, ‖x‖ = 1 → G x = x) ∧ (∀ x, ‖x‖ ≤ 1 → ‖G x‖ = 1) :=
  ⟨RetractionSucc.Gfun F, RetractionSucc.continuous_Gfun hcont hball,
    fun x hx => RetractionSucc.Gfun_eq_self (x := x) hfix hx,
    fun x hx => RetractionSucc.norm_Gfun (x := x) hball hx⟩

end Work.RPCore.Port.Whitney
