import Mathlib

/-!
# A continuous logarithm of a holomorphic function is holomorphic

The main result `Work.Analysis.BranchLog.holomorphic_of_exp` states that if `f` is a
continuous function on an open set `U ⊆ ℂ` with `Complex.exp (f z) = g z` for a
holomorphic, nowhere vanishing `g`, then `f` is holomorphic on `U`.

The argument is local: around a point `z₀` we scale by `g z₀` so that
`g z / g z₀` stays inside the open unit disc about `1`, on which the principal
branch `Complex.log` is holomorphic.  The function
`z ↦ log (g z / g z₀) + log (g z₀)` is then a holomorphic logarithm of `g`
near `z₀`; any two continuous logarithms of the same function differ by a
locally constant `2πi ℤ`-valued function, and on the connected ball that
difference is constant.  Hence `f` agrees near `z₀` with a holomorphic
function and is itself holomorphic there.
-/

namespace Work.Analysis.BranchLog

open Set Metric Filter
open scoped Topology

/-- The set of logarithm branches of `1`, namely `2πi ℤ`, is discrete in `ℂ`. -/
lemma isDiscrete_exp_eq_one : IsDiscrete {w : ℂ | Complex.exp w = 1} := by
  have hset : {w : ℂ | Complex.exp w = 1}
      = (AddSubgroup.zmultiples (2 * Real.pi * Complex.I) : Set ℂ) := by
    ext w
    rw [Set.mem_ofPred_eq, Complex.exp_eq_one_iff]
    simp only [SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, by rw [zsmul_eq_mul]⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← hn, zsmul_eq_mul]⟩
  rw [hset]
  exact isDiscrete_iff_discreteTopology.mpr (NormedSpace.discreteTopology_zmultiples _)

/-- Points of the open unit disc about `1` lie in `Complex.slitPlane`, the domain on
which the principal branch of the logarithm is holomorphic. -/
lemma mem_slitPlane_of_norm_sub_one_lt {w : ℂ} (h : ‖w - 1‖ < 1) :
    w ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h1 : |(w - 1).re| ≤ ‖w - 1‖ := Complex.abs_re_le_norm (w - 1)
  rw [Complex.sub_re, Complex.one_re] at h1
  have h2 : |w.re - 1| < 1 := lt_of_le_of_lt h1 h
  rw [abs_lt] at h2
  linarith [h2.1]

/-- On an open set, a continuous logarithm of a holomorphic nowhere-vanishing
function is holomorphic. -/
lemma differentiableOn_of_exp {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hg : DifferentiableOn ℂ g U)
    (hg0 : ∀ z ∈ U, g z ≠ 0) (hexp : ∀ z ∈ U, Complex.exp (f z) = g z) :
    DifferentiableOn ℂ f U := by
  intro z0 hz0
  have hUz0 : U ∈ 𝓝 z0 := hU.mem_nhds hz0
  have hgc : ContinuousAt g z0 := hg.continuousOn.continuousAt hUz0
  have hc : g z0 ≠ 0 := hg0 z0 hz0
  have hA : (fun z : ℂ => g z / g z0 - 1) ⁻¹' (Metric.ball (0:ℂ) 1) ∈ 𝓝 z0 := by
    have hval : g z0 / g z0 - 1 = 0 := by rw [div_self hc]; ring
    have hball : Metric.ball (0:ℂ) 1 ∈ 𝓝 (g z0 / g z0 - 1) := by
      rw [hval]; exact Metric.ball_mem_nhds 0 (by norm_num)
    exact ((hgc.div_const (g z0)).sub continuousAt_const).preimage_mem_nhds hball
  obtain ⟨ε1, hε1pos, hε1⟩ := Metric.mem_nhds_iff.mp hUz0
  obtain ⟨ε2, hε2pos, hε2⟩ := Metric.mem_nhds_iff.mp hA
  set r : ℝ := min ε1 ε2 with hr
  have hrpos : 0 < r := lt_min hε1pos hε2pos
  have hBU : Metric.ball z0 r ⊆ U :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hε1
  have hBε2 : Metric.ball z0 r ⊆ (fun z : ℂ => g z / g z0 - 1) ⁻¹' (Metric.ball (0:ℂ) 1) :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans hε2
  have hz0B : z0 ∈ Metric.ball z0 r := Metric.mem_ball_self hrpos
  have hBopen : IsOpen (Metric.ball z0 r) := Metric.isOpen_ball
  have hBpre : IsPreconnected (Metric.ball z0 r) := (convex_ball z0 r).isPreconnected
  have hHmaps : MapsTo (fun z => g z / g z0) (Metric.ball z0 r) Complex.slitPlane := by
    intro z hz
    have hz2 := hBε2 hz
    rw [Set.mem_preimage, Metric.mem_ball, Complex.dist_eq] at hz2
    exact mem_slitPlane_of_norm_sub_one_lt (by simpa using hz2)
  set Lj : ℂ → ℂ := fun z => Complex.log (g z / g z0) + Complex.log (g z0) with hLj
  have hLdiff : DifferentiableOn ℂ Lj (Metric.ball z0 r) := by
    rw [hLj]
    have hHdiff : DifferentiableOn ℂ (fun z => g z / g z0) (Metric.ball z0 r) :=
      (hg.mono hBU).div_const (g z0)
    have hlogdiff : DifferentiableOn ℂ Complex.log Complex.slitPlane :=
      fun z hz => (Complex.differentiableAt_log hz).differentiableWithinAt
    exact (hlogdiff.comp hHdiff hHmaps).add_const (Complex.log (g z0))
  have hexpLj : ∀ z ∈ Metric.ball z0 r, Complex.exp (Lj z) = g z := by
    intro z hz
    have hHne : g z / g z0 ∈ Complex.slitPlane := hHmaps hz
    rw [hLj]
    rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero hHne), Complex.exp_log hc]
    exact div_mul_cancel₀ (g z) hc
  set d : ℂ := f z0 - Lj z0 with hd
  set Φ : ℂ → ℂ := fun z => f z - (Lj z + d) with hΦ
  have hΦz0 : Φ z0 = 0 := by rw [hΦ, hd]; ring
  have hΦcont : ContinuousOn Φ (Metric.ball z0 r) := by
    rw [hΦ]
    exact (hf.mono hBU).sub (hLdiff.continuousOn.add continuousOn_const)
  have hd1 : Complex.exp d = 1 := by
    rw [hd, Complex.exp_sub, hexp z0 hz0, hexpLj z0 hz0B, div_self hc]
  have hexpΦ : ∀ z ∈ Metric.ball z0 r, Complex.exp (Φ z) = 1 := by
    intro z hz
    have hzU : z ∈ U := hBU hz
    rw [hΦ, Complex.exp_sub, Complex.exp_add, hexp z hzU, hexpLj z hz, hd1, mul_one,
      div_self (hg0 z hzU)]
  have hΦmaps : MapsTo Φ (Metric.ball z0 r) {w : ℂ | Complex.exp w = 1} :=
    fun z hz => hexpΦ z hz
  have hΦzero : ∀ z ∈ Metric.ball z0 r, Φ z = 0 := by
    intro z hz
    have hmem := hBpre.constant_of_mapsTo isDiscrete_exp_eq_one hΦcont hΦmaps hz hz0B
    rw [hΦz0] at hmem
    exact hmem
  have hcongr : DifferentiableOn ℂ f (Metric.ball z0 r) := by
    refine (hLdiff.add_const d).congr (fun z hz => ?_)
    have hz0' : Φ z = 0 := hΦzero z hz
    rw [hΦ] at hz0'
    exact sub_eq_zero.mp hz0'
  exact (hcongr.differentiableAt (hBopen.mem_nhds hz0B)).differentiableWithinAt

theorem holomorphic_of_exp {f g : ℂ → ℂ}
    (hf : ContinuousOn f {z : ℂ | 0 < z.im})
    (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im})
    (hg0 : ∀ z ∈ {z : ℂ | 0 < z.im}, g z ≠ 0)
    (hexp : ∀ z ∈ {z : ℂ | 0 < z.im}, Complex.exp (f z) = g z) :
    DifferentiableOn ℂ f {z : ℂ | 0 < z.im} := by
  exact differentiableOn_of_exp (isOpen_lt continuous_const Complex.continuous_im) hf hg hg0 hexp

end Work.Analysis.BranchLog
