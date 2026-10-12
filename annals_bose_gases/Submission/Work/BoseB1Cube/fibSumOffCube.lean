import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.perBoxF_localised
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `fibSumOffCube` — the fibre sum vanishes off the fixed cube `acube ((1+d)/d)`

The localised fibre integral `Work.BoseFixB1.fibSum h M ℓ d u Φ` integrates the state against
`∑ᵢ ∫_{acube ℓ} w_{1,B(u)}(xᵢ,y) dy`, where the one-body kernel
`wSmall1Pair = wSmallPair` carries the *two-factor* cutoff
`χ_{B(u)}(z) = chiSmallB M ℓ d u z = χ(z/ℓ)·χ_M(z/(ℓd) − u)` as a factor in **both**
particle arguments.  If the sliding centre `u` lies outside the fixed cube
`acube ((1+d)/d)`, then both factors vanish identically (`chiSmallB ≈ 0`), hence so does the
whole integrand, hence the integral.

The geometric content is packaged in the auxiliary lemma
`chiSmallB_eq_zero_of_notMem_acube`: the support of `χ_{B(u)}` in `z` forces
`|z_j| ≤ ℓ/2` and `|(z/(ℓd) − u)_j| ≤ 1/2`, so `|u_j| ≤ (1+d)/(2d)`, i.e.
`u ∈ acube ((1+d)/d)`.
-/

namespace Work.BoseB1Cube

/-- **The cube window vanishes off the fixed cube.**  If `u ∉ acube ((1+d)/d)` then the
two-factor cutoff `chiSmallB M ℓ d u` is the zero function: its support enforces
`z ∈ acube ℓ` and `z − (ℓd)•u ∈ acube (ℓd)`, which for each coordinate gives
`ℓd|u_j| ≤ ℓ/2 + ℓd/2 = ℓ(1+d)/2`. -/
theorem chiSmallB_eq_zero_of_notMem_acube {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) {u : EuclideanSpace ℝ (Fin 3)} (hu : u ∉ Submission.BoseGases.acube ((1 + d) / d))
    (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
  by_contra h
  apply hu
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  rw [Submission.BoseGases.mem_acube_iff]
  intro m
  have hbig : |z.ofLp m| ≤ ℓ / 2 := Submission.BoseGases.chiSmallB_support_big_box hM hℓ h m
  have hsmall : |((ℓ * d)⁻¹ • z - u).ofLp m| ≤ 1 / 2 :=
    Submission.BoseGases.chiSmallB_support_small_box hM h m
  have hco : ((ℓ * d)⁻¹ • z - u).ofLp m = (ℓ * d)⁻¹ * z.ofLp m - u.ofLp m := by
    simp [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hco] at hsmall
  have hub : |u.ofLp m| ≤ (1 + d) / (2 * d) := by
    have h1 : (ℓ * d)⁻¹ * |z.ofLp m| ≤ (ℓ * d)⁻¹ * (ℓ / 2) :=
      mul_le_mul_of_nonneg_left hbig (le_of_lt (inv_pos.mpr hld))
    have h2 : (ℓ * d)⁻¹ * (ℓ / 2) = 1 / (2 * d) := by field_simp
    have h4 : 1 / (2 * d) + 1 / 2 = (1 + d) / (2 * d) := by field_simp
    have h3 : |u.ofLp m| ≤ (ℓ * d)⁻¹ * |z.ofLp m| + 1 / 2 := by
      have ht : |u.ofLp m| ≤
          |u.ofLp m - (ℓ * d)⁻¹ * z.ofLp m| + |(ℓ * d)⁻¹ * z.ofLp m| := by
        have h := abs_sub_le (u.ofLp m) ((ℓ * d)⁻¹ * z.ofLp m) 0
        simpa using h
      have hts : |u.ofLp m - (ℓ * d)⁻¹ * z.ofLp m| = |(ℓ * d)⁻¹ * z.ofLp m - u.ofLp m| :=
        abs_sub_comm _ _
      have hmul : |(ℓ * d)⁻¹ * z.ofLp m| = (ℓ * d)⁻¹ * |z.ofLp m| := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hld)]
      rw [hts, hmul] at ht
      linarith
    linarith
  have hb : ((1 + d) / d) / 2 = (1 + d) / (2 * d) := by ring
  rw [Set.mem_Icc]
  constructor
  · rw [neg_div, hb]; linarith [neg_abs_le (u.ofLp m), hub]
  · rw [hb]; linarith [le_abs_self (u.ofLp m), hub]

/-- **Off the fixed cube the fibre sum vanishes.**  Every fibre
`∫_{acube ℓ} w_{1,B(u)}(xᵢ,y) dy` carries the factor `χ_{B(u)}(xᵢ)`, which is zero because
`u ∉ acube ((1+d)/d)`; hence the state integrand vanishes pointwise and the integral is `0`. -/
theorem fibSumOffCube {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∉ Submission.BoseGases.acube ((1 + d) / d)) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    Work.BoseFixB1.fibSum h M ℓ d u Φ = 0 := by
  rw [Work.BoseFixB1.fibSum]
  have hfun : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y) = fun _ => (0 : ℝ) := by
    funext x
    have hzero : ∀ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y = 0 := by
      intro i
      trans ∫ y in Submission.BoseGases.acube ℓ, (0 : ℝ)
      · apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
        intro y hy
        rw [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair]
        rw [chiSmallB_eq_zero_of_notMem_acube hM hℓ hd hu (x i)]
        ring
      · simp
    rw [Finset.sum_congr rfl (fun i _ => hzero i)]
    simp
  rw [hfun]
  simp

end Work.BoseB1Cube
