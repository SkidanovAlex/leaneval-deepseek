import Mathlib
import Submission.Work.Horn.flower_defs

/-!
# Petals of a parabolic germ lie in the parabolic basin

Let `f z = z + a z ^ (q+1) + o(z ^ (q+1))` (`q ≥ 1`, `a ≠ 0`) be a parabolic germ on an open set
`D ⊇ ball 0 ρ`, and let `M > 0` be a petal scale with `‖cc q a‖ / M < ρ ^ q` (`cc q a = -1/(q a)`).
Writing `w = chartQ q a z = cc q a / z ^ q` for the Leau–Fatou chart, in which the germ advances
the chart coordinate by at least `3/4` in real part (`Bounds.hchart`), the petals
`petal q a M j = {Re (chartQ q a z) > M}` (up to the `q` branches of the `q`-th root) are
contained in the parabolic basin of `0`.

The point of the statement is the *quantitative uniformity*: for `z` in the `j`-th petal the whole
neighbourhood

`U = petal q a M j ∩ {y | M < Re (chartQ q a y)}`

is mapped into `D` by all iterates of `f` and the iterates converge to `0` *uniformly on* `U`.
Indeed, for `y ∈ U` with `f^[n] y ≠ 0` the chart grows linearly,
`Re (chartQ q a (f^[n] y)) ≥ M + 3n/4`, and then

`‖f^[n] y‖ ^ q = ‖cc q a‖ / ‖chartQ q a (f^[n] y)‖ ≤ ‖cc q a‖ / (M + 3n/4)`,

which tends to `0` uniformly, independently of `y`.  The hypotheses on the petal geometry are
collected in `Flower.PetalFacts`; the only use of `f` itself is the chart estimate
`Flower.Bounds.hchart` together with the invariance hypothesis `hmaps`.

No differentiability of `f` on `D` is needed: `hmaps` supplies the invariance of the petals and
`hchart` the growth, and `MapsTo (f^[n]) U D` follows from `petal ⊆ ball 0 ρ ⊆ D`.
-/

namespace Work.Horn

open Filter
open scoped Topology

/-- `s ∈ DM q a M ↔ M < Re (cc q a / s)` for `s ≠ 0`: the root disc is the set of `s` where the
chart value `cc / s` has real part exceeding `M`. -/
private lemma petal_basin_mem_DM_iff {q : ℕ} {a : ℂ} {M : ℝ} {s : ℂ} (hs : s ≠ 0) :
    s ∈ Flower.DM q a M ↔ M < (Flower.cc q a / s).re := by
  have hns : (0 : ℝ) < Complex.normSq s := Complex.normSq_pos.mpr hs
  have hdiv : (Flower.cc q a / s).re * Complex.normSq s = (Flower.cc q a * star s).re := by
    rw [Complex.div_re, Complex.mul_re]
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im]
    field_simp
    ring
  have hmem : (s ∈ Flower.DM q a M) ↔
      M * Complex.normSq s < (Flower.cc q a * star s).re := Iff.rfl
  rw [hmem, ← hdiv, mul_comm M (Complex.normSq s),
    mul_comm ((Flower.cc q a / s).re) (Complex.normSq s)]
  exact mul_lt_mul_iff_right₀ hns

/-- On a petal the chart coordinate has real part bigger than the petal scale `M`. -/
private lemma petal_basin_chart_re_gt {q : ℕ} {a : ℂ} {M : ℝ}
    (hgeo : Flower.PetalFacts q a M) (j : Fin q) {z : ℂ}
    (hz : z ∈ Flower.petal q a M j) : M < (Flower.chartQ q a z).re := by
  obtain ⟨hzpos, hzqDM, -⟩ := (hgeo.mem_petal_iff j z).mp hz
  have hzq_ne : z ^ q ≠ 0 := pow_ne_zero q (norm_pos_iff.mp hzpos)
  have h := (petal_basin_mem_DM_iff (q := q) (a := a) (M := M) (s := z ^ q) hzq_ne).mp hzqDM
  simpa [Flower.chartQ] using h

/-- A petal is contained in the disc `ball 0 ρ` on which the quantitative bounds hold. -/
private lemma petal_basin_norm_lt {q : ℕ} {a : ℂ} {M ρ : ℝ} (hρ : 0 < ρ)
    (hgeo : Flower.PetalFacts q a M) (hRM : ‖Flower.cc q a‖ / M < ρ ^ q)
    (j : Fin q) {z : ℂ} (hz : z ∈ Flower.petal q a M j) : ‖z‖ < ρ :=
  lt_of_pow_lt_pow_left₀ q (le_of_lt hρ) (lt_trans (hgeo.petal_norm_pow_lt j z hz) hRM)

/-- The norm bound `‖z‖ ^ q ≤ ‖cc‖ / Re (chartQ z)` on the region where the chart real part is
positive. -/
private lemma petal_basin_norm_pow_le {q : ℕ} {a : ℂ} (hcc : Flower.cc q a ≠ 0) {z : ℂ}
    (hz : z ≠ 0) (hpos : 0 < (Flower.chartQ q a z).re) :
    ‖z‖ ^ q ≤ ‖Flower.cc q a‖ / (Flower.chartQ q a z).re := by
  have hzq : z ^ q ≠ 0 := pow_ne_zero q hz
  have h1 : Flower.chartQ q a z * z ^ q = Flower.cc q a := by
    rw [Flower.chartQ]; field_simp
  have h2 : ‖Flower.chartQ q a z‖ * ‖z‖ ^ q = ‖Flower.cc q a‖ := by
    rw [← h1, norm_mul, norm_pow]
  have hcn : Flower.chartQ q a z ≠ 0 := by
    rw [Flower.chartQ]; exact div_ne_zero hcc hzq
  have hnormpos : 0 < ‖Flower.chartQ q a z‖ := norm_pos_iff.mpr hcn
  have hkey : ‖z‖ ^ q = ‖Flower.cc q a‖ / ‖Flower.chartQ q a z‖ := by
    rw [eq_div_iff (ne_of_gt hnormpos), mul_comm]
    exact h2
  rw [hkey]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hpos (Complex.re_le_norm _)

/-- The chart grows linearly along the orbit: as long as `f^[n] y` has not reached `0`, its chart
coordinate has real part at least `Re (chartQ y) + 3n/4`.  Along the way the iterates stay in the
petal `j`, up to the fixed point `0`. -/
private lemma petal_basin_iterate_growth {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hb : Flower.Bounds f D q a ρ) (_hM : 0 < M)
    (hRM : ‖Flower.cc q a‖ / M < ρ ^ q)
    (hgeo : Flower.PetalFacts q a M)
    (hmaps : ∀ j : Fin q, Set.MapsTo f (Flower.petal q a M j) (Flower.petal q a M j ∪ {0}))
    (j : Fin q) {y : ℂ} (hy : y ∈ Flower.petal q a M j) :
    ∀ n : ℕ, f^[n] y ∈ Flower.petal q a M j ∪ {0} ∧
      (f^[n] y ≠ 0 → (Flower.chartQ q a y).re + 3 * (n : ℝ) / 4
        ≤ (Flower.chartQ q a (f^[n] y)).re) := by
  intro n
  induction n with
  | zero =>
    constructor
    · exact Or.inl hy
    · intro _; simp
  | succ k ih =>
    constructor
    · rw [Function.iterate_succ_apply']
      rcases ih.1 with h | h
      · exact hmaps j h
      · rw [Set.mem_singleton_iff.mp h, hb.hfix]; exact Or.inr rfl
    · intro hne
      have hk_ne : f^[k] y ≠ 0 := by
        intro h0
        rw [Function.iterate_succ_apply', h0, hb.hfix] at hne
        exact hne rfl
      have hk_mem : f^[k] y ∈ Flower.petal q a M j := by
        rcases ih.1 with h | h
        · exact h
        · exact absurd (Set.mem_singleton_iff.mp h) hk_ne
      have hklt : ‖f^[k] y‖ < ρ := petal_basin_norm_lt hb.hρ hgeo hRM j hk_mem
      have hkpos : 0 < ‖f^[k] y‖ := norm_pos_iff.mpr hk_ne
      have hchart := hb.hchart (f^[k] y) hkpos hklt
      have hre : 3 / 4 ≤ (Flower.chartQ q a (f (f^[k] y))).re
          - (Flower.chartQ q a (f^[k] y)).re := by
        have h3 := (abs_le.mp (le_trans (Complex.abs_re_le_norm _) hchart)).1
        simp only [Complex.sub_re, Complex.one_re] at h3
        linarith
      have hih := ih.2 hk_ne
      rw [Function.iterate_succ_apply']
      push_cast
      linarith

theorem petal_subset_basin {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hb : Work.Horn.Flower.Bounds f D q a ρ) (hM : 0 < M)
    (hRM : ‖Work.Horn.Flower.cc q a‖ / M < ρ ^ q)
    (hgeo : Work.Horn.Flower.PetalFacts q a M)
    (hmaps : ∀ j : Fin q, Set.MapsTo f (Work.Horn.Flower.petal q a M j)
      (Work.Horn.Flower.petal q a M j ∪ {0})) :
    ∀ j : Fin q, Work.Horn.Flower.petal q a M j ⊆ MandelDim.ParabolicBasin f D := by
  intro j z hz
  have hzre : M < (Flower.chartQ q a z).re := petal_basin_chart_re_gt hgeo j hz
  have hz_ne : z ≠ 0 := norm_pos_iff.mp ((hgeo.mem_petal_iff j z).mp hz).1
  have hzq_ne : z ^ q ≠ 0 := pow_ne_zero q hz_ne
  -- the neighbourhood `U` on which the convergence is uniform
  refine ⟨Flower.petal q a M j ∩ {y : ℂ | M < (Flower.chartQ q a y).re}, ?_, ?_, ?_⟩
  · -- `U` is a neighbourhood of `z`
    have hcont : ContinuousAt (fun y : ℂ => (Flower.chartQ q a y).re) z := by
      have h1 : ContinuousAt (fun y : ℂ => Flower.cc q a / y ^ q) z := by
        refine ContinuousAt.div continuousAt_const (continuousAt_id.pow q) ?_
        simpa [Flower.chartQ] using hzq_ne
      exact Complex.continuous_re.continuousAt.comp h1
    have hset : Set.Ioi M ∈ 𝓝 ((fun y : ℂ => (Flower.chartQ q a y).re) z) :=
      isOpen_Ioi.mem_nhds hzre
    exact Filter.inter_mem ((hgeo.isOpen_petal j).mem_nhds hz) (hcont.preimage_mem_nhds hset)
  · -- every iterate maps `U` into `D`
    intro n y hy
    have hsubρ : Flower.petal q a M j ∪ {0} ⊆ Metric.ball (0 : ℂ) ρ := by
      rintro w (hw | hw)
      · rw [Metric.mem_ball, dist_zero_right]
        exact petal_basin_norm_lt hb.hρ hgeo hRM j hw
      · rw [Set.mem_singleton_iff.mp hw]; exact Metric.mem_ball_self hb.hρ
    exact hb.hsub (hsubρ (petal_basin_iterate_growth hb hM hRM hgeo hmaps j hy.1 n).1)
  · -- the iterates converge to `0` uniformly on `U`
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (4 * ‖Flower.cc q a‖ / (3 * ε ^ q) + 1)
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn y hy => ?_⟩
    have hyre : M < (Flower.chartQ q a y).re := hy.2
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have h1 : (0 : ℝ) < 4 * ‖Flower.cc q a‖ / (3 * ε ^ q) + 1 := by positivity
      linarith
    have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hNpos hnN
    by_cases hzero : f^[n] y = 0
    · rw [hzero, dist_self]; exact hε
    · have hgrowth := (petal_basin_iterate_growth hb hM hRM hgeo hmaps j hy.1 n).2 hzero
      have hgrowth' : M + 3 * (n : ℝ) / 4 ≤ (Flower.chartQ q a (f^[n] y)).re := by
        linarith
      have hden : (0 : ℝ) < M + 3 * (n : ℝ) / 4 := by
        have : (0 : ℝ) ≤ 3 * (n : ℝ) / 4 := by positivity
        linarith
      have hrepos : 0 < (Flower.chartQ q a (f^[n] y)).re := lt_of_lt_of_le hden hgrowth'
      have hn1 : ‖f^[n] y‖ ^ q ≤ ‖Flower.cc q a‖ / (M + 3 * (n : ℝ) / 4) :=
        le_trans (petal_basin_norm_pow_le hgeo.cc_ne_zero hzero hrepos)
          (div_le_div_of_nonneg_left (norm_nonneg _) hden hgrowth')
      have hb1 : ‖Flower.cc q a‖ / (M + 3 * (n : ℝ) / 4)
          ≤ 4 * ‖Flower.cc q a‖ / (3 * (n : ℝ)) := by
        have hle1 : ‖Flower.cc q a‖ / (M + 3 * (n : ℝ) / 4)
            ≤ ‖Flower.cc q a‖ / (3 * (n : ℝ) / 4) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by linarith)
        refine le_trans hle1 (le_of_eq ?_)
        rw [div_eq_div_iff (by positivity) (by positivity)]
        ring
      have hb3 : 4 * ‖Flower.cc q a‖ / (3 * (n : ℝ))
          ≤ 4 * ‖Flower.cc q a‖ / (3 * (N : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      have hb4 : 4 * ‖Flower.cc q a‖ / (3 * (N : ℝ)) < ε ^ q := by
        have h3epos : 0 < 3 * ε ^ q := by positivity
        have h1 : 4 * ‖Flower.cc q a‖ / (3 * ε ^ q) < (N : ℝ) := by linarith
        rw [div_lt_iff₀ h3epos] at h1
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 3 * (N : ℝ))]
        linarith
      have hchain : ‖f^[n] y‖ ^ q < ε ^ q := by linarith
      simpa [dist_eq_norm] using lt_of_pow_lt_pow_left₀ q (le_of_lt hε) hchain

end Work.Horn
