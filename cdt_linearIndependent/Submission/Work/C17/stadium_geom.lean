import Mathlib
import Submission.Work.C17.logPw_setup
import Submission.Work.C17.stadium_re_ge
import Submission.Work.C17.stadium_ne_half
import Submission.Work.C17.stadium_subset_ball

/-!
# The stadium `stadiumSet c δ ρ` (area C17, geometry for `logPw_continuation`)

For `3/4 ≤ c < 1`, `δ = min ((1-c)/2) (1/64)` and `ρ = 1/64`, the set

`stadiumSet c δ ρ = ⋃_{t ∈ [0,1]} ball ((1-t)c + t·p₀) ((1-t)δ + tρ)`,  `p₀ = 1/4 + i/5`,

is the convex open "stadium" joining the disc of radius `δ` around the cusp value `c`
to the disc of radius `ρ` around `p₀`.  This file collects the elementary geometry:
it is convex and open, contains `ball c δ` and `p₀`, is contained in the unit disc,
stays away from the three exceptional points `0`, `1/2`, `1` of the pullback
equation, and is contained in the region `{‖w z‖ ≥ 3/32}` (`w z = z/(z-1)`) where
the unlikely series `logP` cannot converge.
-/

namespace Work.C17

open Complex

/-- The stadium as a union of a `[0,1]`-parametrised family of discs with affine
centre `(1-t) • a + t • b` and affine radius `(1-t) * r + t * s`.  This is the
`ℝ`-module (smul) form of `stadiumSet (c) δ ρ` with `a = (c:ℂ)`, `b = p0C`. -/
def stadBall (a b : ℂ) (r s : ℝ) : Set ℂ :=
  ⋃ t ∈ Set.Icc (0 : ℝ) 1, Metric.ball ((1 - t) • a + t • b) ((1 - t) * r + t * s)

/-- `stadBall` is exactly `stadiumSet`, with the complex numbers written in the
`ℝ`-module notation. -/
theorem stadiumSet_eq (c δ ρ : ℝ) : stadiumSet c δ ρ = stadBall (c : ℂ) p0C δ ρ := by
  ext z
  simp only [stadiumSet, stadBall, Set.mem_iUnion, Metric.mem_ball]
  constructor
  · rintro ⟨t, ht, hz⟩
    refine ⟨t, ht, ?_⟩
    rw [Complex.real_smul, Complex.real_smul, ← Complex.ofReal_mul]
    exact hz
  · rintro ⟨t, ht, hz⟩
    refine ⟨t, ht, ?_⟩
    rw [Complex.real_smul, Complex.real_smul] at hz
    rw [Complex.ofReal_mul]
    exact hz

/-- `stadBall a b r s` is open: it is a union of open discs. -/
theorem stadBall_isOpen (a b : ℂ) (r s : ℝ) : IsOpen (stadBall a b r s) := by
  rw [stadBall]
  exact isOpen_biUnion (fun _ _ => Metric.isOpen_ball)

/-- `stadBall a b r s` is convex: for `z₁` in the disc at time `t₁` and `z₂` in the disc
at time `t₂`, the segment joining them stays in the disc at the intermediate time
`λ t₁ + μ t₂`, because both the centre and the radius are *affine* in `t`. -/
theorem stadBall_convex (a b : ℂ) (r s : ℝ) : Convex ℝ (stadBall a b r s) := by
  rw [convex_iff_forall_pos]
  intro x hx y hy lam mu hlam hmu hsum
  simp only [stadBall, Set.mem_iUnion] at hx hy ⊢
  obtain ⟨t1, ht1, hx1⟩ := hx
  obtain ⟨t2, ht2, hy1⟩ := hy
  rw [Metric.mem_ball, dist_eq_norm] at hx1 hy1
  refine ⟨lam * t1 + mu * t2, ⟨?_, ?_⟩, ?_⟩
  · nlinarith [ht1.1, ht1.2, ht2.1, ht2.2, le_of_lt hlam, le_of_lt hmu]
  · nlinarith [ht1.1, ht1.2, ht2.1, ht2.2, le_of_lt hlam, le_of_lt hmu]
  · rw [Metric.mem_ball, dist_eq_norm]
    have key : lam • x + mu • y - ((1 - (lam * t1 + mu * t2)) • a + (lam * t1 + mu * t2) • b)
        = lam • (x - ((1 - t1) • a + t1 • b)) + mu • (y - ((1 - t2) • a + t2 • b)) := by
      simp only [Complex.real_smul]
      push_cast
      have hsumC : (lam : ℂ) + (mu : ℂ) = 1 := by exact_mod_cast hsum
      linear_combination a * hsumC
    have h1t : lam * ((1 - t1) * r + t1 * s) + mu * ((1 - t2) * r + t2 * s)
        = (1 - (lam * t1 + mu * t2)) * r + (lam * t1 + mu * t2) * s := by
      have h : (1 : ℝ) - (lam * t1 + mu * t2) = lam * (1 - t1) + mu * (1 - t2) := by nlinarith
      rw [h]; ring
    rw [key, ← h1t]
    calc ‖lam • (x - ((1 - t1) • a + t1 • b)) + mu • (y - ((1 - t2) • a + t2 • b))‖
        ≤ ‖lam • (x - ((1 - t1) • a + t1 • b))‖
            + ‖mu • (y - ((1 - t2) • a + t2 • b))‖ := norm_add_le _ _
      _ = lam * ‖x - ((1 - t1) • a + t1 • b)‖ + mu * ‖y - ((1 - t2) • a + t2 • b)‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (le_of_lt hlam),
              Real.norm_of_nonneg (le_of_lt hmu)]
      _ < lam * ((1 - t1) * r + t1 * s) + mu * ((1 - t2) * r + t2 * s) :=
            add_lt_add (mul_lt_mul_of_pos_left hx1 hlam) (mul_lt_mul_of_pos_left hy1 hmu)

/-- The disc of radius `δ` around `c` is the `t = 0` slice of the stadium. -/
theorem ball_subset_stadiumSet (c δ ρ : ℝ) :
    Metric.ball ((c : ℝ) : ℂ) δ ⊆ stadiumSet c δ ρ := by
  intro z hz
  exact ⟨0, ⟨le_refl _, zero_le_one⟩, by simpa using hz⟩

/-- The point `p₀ = 1/4 + i/5` is the centre of the `t = 1` slice of the stadium. -/
theorem p0C_mem_stadiumSet {c δ ρ : ℝ} (hρ : ρ = 1 / 64) : p0C ∈ stadiumSet c δ ρ := by
  refine ⟨1, ⟨zero_le_one, le_refl _⟩, ?_⟩
  rw [Metric.mem_ball]
  simp only [sub_self, zero_mul, Complex.ofReal_zero, Complex.ofReal_one, zero_add, one_mul]
  rw [dist_self, hρ]
  norm_num


/-- **Geometry of the stadium.**  For `3/4 ≤ c < 1`, `δ = min ((1-c)/2) (1/64)` and
`ρ = 1/64` the stadium is convex and open, joins the disc around `c` to `p₀`,
lies in the unit disc, in the half plane `Re z ≥ 15/64` and in `{‖z/(z-1)‖ ≥ 3/32}`,
and avoids `0`, `1/2` and `1`. -/
theorem stadium_geom {c δ ρ : ℝ} (hc : 3 / 4 ≤ c) (hc1 : c < 1)
    (hδ : δ = min ((1 - c) / 2) (1 / 64)) (hρ : ρ = 1 / 64) :
    Convex ℝ (stadiumSet c δ ρ) ∧ IsOpen (stadiumSet c δ ρ) ∧
      Metric.ball ((c : ℝ) : ℂ) δ ⊆ stadiumSet c δ ρ ∧ p0C ∈ stadiumSet c δ ρ ∧
      stadiumSet c δ ρ ⊆ Metric.ball 0 1 ∧
      (∀ z ∈ stadiumSet c δ ρ, (15 / 64 : ℝ) ≤ z.re) ∧
      (∀ z ∈ stadiumSet c δ ρ, (3 / 32 : ℝ) ≤ ‖wfun z‖) ∧
      (∀ z ∈ stadiumSet c δ ρ, z ≠ 0) ∧ (∀ z ∈ stadiumSet c δ ρ, z ≠ 1 / 2) ∧
      (∀ z ∈ stadiumSet c δ ρ, z ≠ 1) := by
  have hre := stadium_re_ge hc hc1 hδ hρ
  have hball := stadium_subset_ball hc hc1 hδ hρ
  have hhalf := stadium_ne_half hc hc1 hδ hρ
  -- `‖w z‖ = ‖z‖ / ‖z - 1‖ ≥ (15/64)/2 > 3/32` for `‖z‖ < 1`, `Re z ≥ 15/64`.
  have hw : ∀ z ∈ stadiumSet c δ ρ, (3 / 32 : ℝ) ≤ ‖wfun z‖ := by
    intro z hz
    have h1 := hre z hz
    have h2 : ‖z‖ < 1 := by
      have h := hball hz
      rwa [Metric.mem_ball, dist_zero_right] at h
    have hz1 : z ≠ 1 := by
      intro h; rw [h] at h2; simp at h2
    have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
    have hzge : (15 / 64 : ℝ) ≤ ‖z‖ := le_trans h1 (re_le_norm z)
    have hle : ‖z - 1‖ ≤ 2 := by
      have h := norm_sub_le z (1 : ℂ)
      simp at h
      linarith
    rw [wfun, norm_div, le_div_iff₀ hpos]
    nlinarith
  refine ⟨?_, ?_, ball_subset_stadiumSet c δ ρ,
    p0C_mem_stadiumSet (c := c) (δ := δ) hρ, hball, hre, hw, ?_, hhalf, ?_⟩
  · rw [stadiumSet_eq]; exact stadBall_convex _ _ _ _
  · rw [stadiumSet_eq]; exact stadBall_isOpen _ _ _ _
  · intro z hz hz0
    have h := hre z hz
    rw [hz0] at h
    norm_num at h
  · intro z hz
    have h2 : ‖z‖ < 1 := by
      have h := hball hz
      rwa [Metric.mem_ball, dist_zero_right] at h
    intro h; rw [h] at h2; simp at h2

end Work.C17
