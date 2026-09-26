import Mathlib
import Submission.Work.HFN.BlLow.window_geom

/-!
# The two compact boxes of the low bad-line window bound

This file fixes the two compact sets on which the window (`spike`) lower bound of the
`j`-difference on the low bad-line region `blLowSet = {τ ∈ 𝒟 : 2/5 ≤ Im τ ≤ 1/2, |Re τ| > 3/4}`
is established:

* `ctWin` — the contour window `{|Re| = 0, Im t ∈ [11/40, 5/8]}` (the contour point `i t` of the
  spike bound `Work.Asymptotics.BlLow.window_bound`, cf. `blLow_window_bounds`);

* `blWinBox` — the closed box `{|Re| ≤ 1/4, Im ∈ [1/3, 2/3]}`.  Both points of the
  `SL(2,ℤ)`-orbit of `τ` that the contour meets, the translate pole `zpole τ = τ - tsign τ` and
  the crossed point `crossedPt τ = tsign τ + S·τ`, lie in `blWinBox` for `τ ∈ clBox`
  (`zpole_mem_blWinBox`, `crossedPt_mem_blWinBox`).

The height interval `[1/3, 2/3]` is chosen so that it excludes every elliptic height: the
`SL(2,ℤ)`-orbit of `i` consists of points of height `1/(c² + d²)`, that of `ρ = e^{iπ/3}` of
points of height `(√3/2)/(c² - cd + d²)`; the only height of either kind in `[1/3, 2/3]` is
`1/2` (from the orbit of `i`), and the points of height `1/2` in the orbit of `i` have real part
`≡ 1/2 (mod 1)`, which the bound `|Re| ≤ 1/4` excludes.  Hence `j' ≠ 0` on `blWinBox`
(`Work.Asymptotics.BlLow.jprime_ne_zero_blWinBox`), which is what makes `j` locally bi-Lipschitz
there (`Work.Asymptotics.Tile.tile_jDiff_linear_compact`).
-/

noncomputable section

open UpperHalfPlane

namespace Work.HFN.BlLow
open Work.Asymptotics Work.Asymptotics.BlLow  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Kernels
open Work.Asymptotics.HalfFunnel Work.HFN.HalfFunnel

/-- The contour window: the segment `{i t : 11/40 ≤ t ≤ 5/8}` of the positive imaginary axis
containing the contour point `i t` of the window bound. -/
def ctWin : Set ℍ := {z : ℍ | z.re = 0 ∧ 11 / 40 ≤ z.im ∧ z.im ≤ 5 / 8}

/-- The closed box containing both orbit points of the contour window:
`{|Re| ≤ 1/4, 1/3 ≤ Im ≤ 2/3}`. -/
def blWinBox : Set ℍ := {z : ℍ | |z.re| ≤ 1 / 4 ∧ 1 / 3 ≤ z.im ∧ z.im ≤ 2 / 3}

lemma imagAxis_mem_ctWin (t : ℝ) (ht : 0 < t) (h1 : 11 / 40 ≤ t) (h2 : t ≤ 5 / 8) :
    Work.Kernels.imagAxis t ht ∈ ctWin := by
  have hre : (Work.Kernels.imagAxis t ht).re = 0 := by
    simp [Work.Kernels.imagAxis]
  have him : (Work.Kernels.imagAxis t ht).im = t := by
    simp [Work.Kernels.imagAxis]
  exact ⟨hre, by rw [him]; exact h1, by rw [him]; exact h2⟩

lemma ctWin_bounds {z : ℍ} (hz : z ∈ ctWin) : z.re = 0 ∧ 11 / 40 ≤ z.im ∧ z.im ≤ 5 / 8 := hz

/-! ## Membership of the two orbit points -/

lemma zpole_mem_blWinBox {τ : ℍ} (hτ : τ ∈ clBox) : zpole τ ∈ blWinBox := by
  obtain ⟨h34, h1, hlo, hhi, -, -⟩ := hτ
  have hb := abs_le.mp h1
  have hre := zpole_re τ
  have him : (zpole τ).im = τ.im := zpole_im τ
  refine ⟨?_, by rw [him]; linarith, by rw [him]; linarith⟩
  rcases le_abs.mp h34 with h | h
  · have ht : tsign τ = 1 := (tsign_eq_one_iff τ).mpr (by linarith)
    rw [hre, ht, abs_le]
    constructor <;> linarith
  · have ht : tsign τ = -1 := (tsign_eq_neg_one_iff τ).mpr (by linarith)
    rw [hre, ht, abs_le]
    constructor <;> linarith

/-- The real part bound for the crossed point, for the raw coordinates `x ≥ 3/4`, `y ∈ [2/5,1/2]`:
`|1 - x/(x² + y²)| ≤ 1/4`. -/
private lemma crossedPt_one_sub_abs {x y : ℝ} (hx : 3 / 4 ≤ x) (hx1 : x ≤ 1)
    (hy1 : 2 / 5 ≤ y) (hy2 : y ≤ 1 / 2) :
    |1 - x / (x ^ 2 + y ^ 2)| ≤ 1 / 4 := by
  have hpos : 0 < x ^ 2 + y ^ 2 := by nlinarith [hy1]
  have hle : x / (x ^ 2 + y ^ 2) ≤ 5 / 4 := by
    rw [div_le_iff₀ hpos]
    nlinarith [hx, hx1, hy1, hy2, sq_nonneg (x - 3 / 4), sq_nonneg (y - 2 / 5)]
  have hge : (3 : ℝ) / 4 ≤ x / (x ^ 2 + y ^ 2) := by
    rw [le_div_iff₀ hpos]
    nlinarith [hx, hx1, hy1, hy2, sq_nonneg (x - 3 / 4), sq_nonneg (y - 2 / 5)]
  rw [abs_le]; exact ⟨by linarith, by linarith⟩

/-- The height bounds for the crossed point, for the raw coordinates `x ≥ 3/4`, `y ∈ [2/5,1/2]`:
`1/3 ≤ y/(x² + y²) ≤ 2/3`. -/
private lemma crossedPt_height_bounds {x y : ℝ} (hx : 3 / 4 ≤ x) (hx1 : x ≤ 1)
    (hy1 : 2 / 5 ≤ y) (hy2 : y ≤ 1 / 2) :
    1 / 3 ≤ y / (x ^ 2 + y ^ 2) ∧ y / (x ^ 2 + y ^ 2) ≤ 2 / 3 := by
  have hpos : 0 < x ^ 2 + y ^ 2 := by nlinarith [hy1]
  have hxl : x ^ 2 ≤ 1 := by nlinarith [hx, hx1]
  constructor
  · rw [le_div_iff₀ hpos]
    nlinarith [hxl, hy1, hy2, sq_nonneg (y - 2 / 5)]
  · rw [div_le_iff₀ hpos]
    nlinarith [hx, hy1, hy2, sq_nonneg (y - 1 / 2)]

lemma crossedPt_mem_blWinBox {τ : ℍ} (hτ : τ ∈ clBox) : crossedPt τ ∈ blWinBox := by
  obtain ⟨h34, h1, hlo, hhi, -, -⟩ := hτ
  have hns : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    ring
  have hb : |τ.re| ≤ 1 := h1
  have him : (crossedPt τ).im = τ.im / ‖(τ : ℂ)‖ ^ 2 := crossedPt_im τ
  have hre : (crossedPt τ).re = tsign τ - τ.re / ‖(τ : ℂ)‖ ^ 2 := crossedPt_re τ
  rw [hns] at him hre
  rcases le_abs.mp h34 with h | h
  · -- `τ.re ≥ 3/4`
    have hx1 : τ.re ≤ 1 := by
      have := (abs_le.mp hb).2; linarith
    have ht : tsign τ = 1 := (tsign_eq_one_iff τ).mpr (by linarith)
    refine ⟨?_, ?_, ?_⟩
    · rw [hre, ht]
      exact crossedPt_one_sub_abs h hx1 hlo hhi
    · rw [him]; exact (crossedPt_height_bounds h hx1 hlo hhi).1
    · rw [him]; exact (crossedPt_height_bounds h hx1 hlo hhi).2
  · -- `τ.re ≤ -3/4`
    have hx1 : -τ.re ≤ 1 := by
      have := (abs_le.mp hb).1; linarith
    have hsq : τ.re ^ 2 = (-τ.re) ^ 2 := by ring
    rw [hsq] at him hre
    have ht : tsign τ = -1 := (tsign_eq_neg_one_iff τ).mpr (by linarith)
    have hrew : (crossedPt τ).re = -(1 - (-τ.re) / ((-τ.re) ^ 2 + τ.im ^ 2)) := by
      rw [hre, ht]; field_simp; ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hrew, abs_neg]
      exact crossedPt_one_sub_abs (by linarith) hx1 hlo hhi
    · rw [him]; exact (crossedPt_height_bounds (by linarith) hx1 hlo hhi).1
    · rw [him]; exact (crossedPt_height_bounds (by linarith) hx1 hlo hhi).2


/-! ## Compactness -/

/-- The `j`-orbit-point box is closed. -/
lemma isClosed_blWinBox : IsClosed blWinBox := by
  have h1 : IsClosed {z : ℍ | |z.re| ≤ (1 / 4 : ℝ)} :=
    isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
  have h2 : IsClosed {z : ℍ | (1 / 3 : ℝ) ≤ z.im} :=
    isClosed_le continuous_const UpperHalfPlane.continuous_im
  have h3 : IsClosed {z : ℍ | z.im ≤ (2 / 3 : ℝ)} :=
    isClosed_le UpperHalfPlane.continuous_im continuous_const
  have he : blWinBox = {z : ℍ | |z.re| ≤ (1 / 4 : ℝ)} ∩ {z : ℍ | (1 / 3 : ℝ) ≤ z.im}
      ∩ {z : ℍ | z.im ≤ (2 / 3 : ℝ)} := by
    ext z; simp only [blWinBox, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [he]; exact (h1.inter h2).inter h3

/-- The contour window is closed. -/
lemma isClosed_ctWin : IsClosed ctWin := by
  have h1 : IsClosed {z : ℍ | z.re = 0} := isClosed_eq UpperHalfPlane.continuous_re continuous_const
  have h2 : IsClosed {z : ℍ | (11 / 40 : ℝ) ≤ z.im} :=
    isClosed_le continuous_const UpperHalfPlane.continuous_im
  have h3 : IsClosed {z : ℍ | z.im ≤ (5 / 8 : ℝ)} :=
    isClosed_le UpperHalfPlane.continuous_im continuous_const
  have he : ctWin = {z : ℍ | z.re = 0} ∩ {z : ℍ | (11 / 40 : ℝ) ≤ z.im}
      ∩ {z : ℍ | z.im ≤ (5 / 8 : ℝ)} := by
    ext z; simp only [ctWin, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [he]; exact (h1.inter h2).inter h3

private lemma mem_closedBall_of_bounds {z : ℍ} (hre : |z.re| ≤ 1 / 4)
    (him : |z.im - 1| ≤ 1) (hlo : 1 / 4 ≤ z.im) :
    z ∈ Metric.closedBall (⟨Complex.I, by simp⟩ : ℍ) 3 := by
  rw [Metric.mem_closedBall]
  have hnum : ‖(z : ℂ) - Complex.I‖ ≤ 5 / 4 := by
    have h := Complex.norm_le_abs_re_add_abs_im ((z : ℂ) - Complex.I)
    have hre' : ((z : ℂ) - Complex.I).re = z.re := by simp
    have him' : ((z : ℂ) - Complex.I).im = z.im - 1 := by simp
    rw [hre', him'] at h
    linarith
  have hI : (⟨Complex.I, by simp⟩ : ℍ).im = 1 := by rw [← UpperHalfPlane.coe_im]; simp
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt (z.im * (⟨Complex.I, by simp⟩ : ℍ).im) := by
    rw [hI, mul_one, Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  have hstep : dist z (⟨Complex.I, by simp⟩ : ℍ) ≤
      ‖(z : ℂ) - Complex.I‖ / Real.sqrt (z.im * (⟨Complex.I, by simp⟩ : ℍ).im) := by
    have h := UpperHalfPlane.dist_le_dist_coe_div_sqrt z (⟨Complex.I, by simp⟩ : ℍ)
    simpa [UpperHalfPlane.coe_I, Complex.dist_eq] using h
  calc dist z (⟨Complex.I, by simp⟩ : ℍ)
      ≤ ‖(z : ℂ) - Complex.I‖ / Real.sqrt (z.im * (⟨Complex.I, by simp⟩ : ℍ).im) := hstep
    _ ≤ (5 / 4) / (1 / 2 : ℝ) := div_le_div₀ (by norm_num) hnum (by norm_num) hsqrt
    _ ≤ 3 := by norm_num

lemma isCompact_blWinBox : IsCompact blWinBox :=
  IsCompact.of_isClosed_subset (isCompact_closedBall (⟨Complex.I, by simp⟩ : ℍ) 3)
    isClosed_blWinBox (fun z hz => by
      refine mem_closedBall_of_bounds hz.1 ?_ ?_
      · rw [abs_le]; constructor <;> linarith [hz.2.1, hz.2.2]
      · linarith [hz.2.1])

lemma isCompact_ctWin : IsCompact ctWin :=
  IsCompact.of_isClosed_subset (isCompact_closedBall (⟨Complex.I, by simp⟩ : ℍ) 3)
    isClosed_ctWin (fun z hz => by
      refine mem_closedBall_of_bounds ?_ ?_ ?_
      · rw [hz.1, abs_zero]; norm_num
      · rw [abs_le]; constructor <;> linarith [hz.2.1, hz.2.2]
      · linarith [hz.2.1])

/-- The distance of a point of `blWinBox` to a point of `ctWin` is at most `1`. -/
lemma dist_le_one {z w : ℍ} (hz : z ∈ blWinBox) (hw : w ∈ ctWin) :
    ‖(w : ℂ) - (z : ℂ)‖ ≤ 1 := by
  have h := Complex.norm_le_abs_re_add_abs_im ((w : ℂ) - (z : ℂ))
  have h1 : |((w : ℂ) - (z : ℂ)).re| ≤ 1 / 4 := by
    rw [Complex.sub_re, UpperHalfPlane.coe_re w, UpperHalfPlane.coe_re z, hw.1, zero_sub,
      abs_neg]
    exact hz.1
  have h2 : |((w : ℂ) - (z : ℂ)).im| ≤ 2 / 3 := by
    rw [Complex.sub_im, UpperHalfPlane.coe_im w, UpperHalfPlane.coe_im z, abs_le]
    constructor <;> linarith [hw.2.1, hw.2.2, hz.2.1, hz.2.2]
  linarith

end Work.HFN.BlLow
