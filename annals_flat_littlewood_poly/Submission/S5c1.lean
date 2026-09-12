import Mathlib
import Submission.S5_sHat
import Submission.S5Tele

/-! Claim 1 (paper): `Σ_i |∫_{I_i} sin(2n(θ+θ0))/sin(θ+θ0) dθ| ≤ 1/50` for
`θ0 ∈ [0, π/2]`, `n ≥ 2^16`.

All ingredients are in `Submission.S5` (imported above): the arcs satisfy
`qA n ≤ lo`, `hi ≤ qB n`, lengths are multiples of `π/n` with `len ≤ 6`
(`arc_len_multiple`, `arc_len_le_six`), `arc_theta_domain` gives
`0 < sin(θ+θ0)` on arcs, `arc_sin_inv_bound` bounds `1/sin(θ+θ0) ≤ 1/sin(qA)`,
`arc_sin_sum_lower`, `one_arc_contains`, the phase-shifted periodic bounds
`monotone_sin_shifted`/`antitone_sin_shifted`, and the telescoping lemma
`S5Tele.sum_var_le_mono/anti`. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
set_option autoImplicit false

namespace Submission
namespace S5C1

/-- `c = π/2 − θ0`: the split point where `sin(θ+θ0)` is maximal. -/
def cVal (θ0 : ℝ) : ℝ := Real.pi / 2 - θ0

/-- `g(θ) = 1/sin(θ+θ0)`. -/
def gInv (θ0 : ℝ) (θ : ℝ) : ℝ := 1 / Real.sin (θ + θ0)

/-- value of `g` at the split point: `1/sin(π/2) = 1` -/
lemma gInv_c (θ0 : ℝ) : gInv θ0 (cVal θ0) = 1 := by
  unfold gInv cVal
  have harg : (Real.pi / 2 - θ0) + θ0 = Real.pi / 2 := by ring
  rw [harg, Real.sin_pi_div_two]
  norm_num

/-- `θ0` and quadrant endpoints lie in the quadrant -/
lemma theta0_quad {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    θ0 ∈ Set.Icc 0 (Real.pi / 2) := by
  exact ⟨hθ0a, hθ0b⟩

/-- `sin` is monotone increasing on `[0, π/2]` -/
lemma sin_mono_left : MonotoneOn Real.sin (Set.Icc 0 (Real.pi / 2)) :=
  S5.sin_mono_on_left

/-- `sin` is monotone decreasing on `[π/2, π]` -/
lemma sin_anti_right : AntitoneOn Real.sin (Set.Icc (Real.pi / 2) Real.pi) := by
  intro x hx y hy hxy
  have hx1 : 0 ≤ Real.pi - x := by linarith [hx.2]
  have hx2 : Real.pi - x ≤ Real.pi / 2 := by linarith [hx.1]
  have hy1 : 0 ≤ Real.pi - y := by linarith [hy.2]
  have hy2 : Real.pi - y ≤ Real.pi / 2 := by linarith [hy.1]
  have hle : Real.pi - y ≤ Real.pi - x := by linarith
  have hsin : Real.sin (Real.pi - y) ≤ Real.sin (Real.pi - x) := by
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hx2 hle
  simpa [Real.sin_pi_sub] using hsin

/-- `sin(θ+θ0) ≤ 1` -/
lemma sin_add_le_one (θ θ0 : ℝ) : Real.sin (θ + θ0) ≤ 1 := Real.sin_le_one _

/-- `g(qA) ≥ 0` (indeed > 0): `qA + θ0 ∈ (0, π)` -/
lemma gInv_qA_pos (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0a : 0 ≤ θ0)
    (hθ0b : θ0 ≤ Real.pi / 2) : 0 < gInv θ0 (S5.qA n) := by
  unfold gInv
  have h1 : 0 < S5.qA n + θ0 := by linarith [S5.qA_pos hn16]
  have h2 : S5.qA n + θ0 < Real.pi := by
    have hq : S5.qA n ≤ Real.pi / 4 := S5.qA_le_pi_div_four hn16
    linarith [hθ0b, Real.pi_pos]
  have hs : 0 < Real.sin (S5.qA n + θ0) := Real.sin_pos_of_pos_of_lt_pi h1 h2
  exact one_div_pos.mpr hs

/-- `g(qB) > 0`: `qB + θ0 ∈ (0, π)` -/
lemma gInv_qB_pos (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0a : 0 ≤ θ0)
    (hθ0b : θ0 ≤ Real.pi / 2) : 0 < gInv θ0 (S5.qB n) := by
  unfold gInv
  have h1 : 0 < S5.qB n + θ0 := by
    have hq : 0 < S5.qB n := (S5.qB_bounds hn16).2.1
    linarith
  have h2 : S5.qB n + θ0 < Real.pi := by
    have hq : S5.qB n < Real.pi / 2 := (S5.qB_bounds hn16).2.2
    linarith [hθ0b]
  have hs : 0 < Real.sin (S5.qB n + θ0) := Real.sin_pos_of_pos_of_lt_pi h1 h2
  exact one_div_pos.mpr hs

/-- `qA + θ0 ∈ (0, π/2]` when `qA ≤ c` -/
lemma qA_add_theta0_le_pi_div_two (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ}
    (hq : S5.qA n ≤ cVal θ0) : S5.qA n + θ0 ≤ Real.pi / 2 := by
  dsimp [cVal] at hq
  linarith

/-- `sin(qA + θ0) ≥ sin(qA)`, for `θ0 ∈ [0, π/2]`, `n ≥ 2^16` -/
lemma sin_qA_add_ge_sin_qA (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ}
    (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    Real.sin (S5.qA n) ≤ Real.sin (S5.qA n + θ0) := by
  let q : ℝ := S5.qA n
  have hq0 : 0 ≤ q := (S5.qA_pos hn16).le
  have hq4 : q ≤ Real.pi / 4 := S5.qA_le_pi_div_four hn16
  by_cases hm : q + θ0 ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hm (by linarith [hθ0a])
  · have hle_pi : q + θ0 < Real.pi := by linarith [hq4, hθ0b, Real.pi_pos]
    have hsym : Real.sin (q + θ0) = Real.sin (Real.pi - (q + θ0)) := by
      rw [Real.sin_pi_sub]
    rw [hsym]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith) (by linarith) (by nlinarith [hq4, hθ0b, hq0])

/-- `sin(qB + θ0) ≥ sin(qA)`, for `θ0 ∈ [0, π/2]`, `n ≥ 2^16` -/
lemma sin_qB_add_ge_sin_qA (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ}
    (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    Real.sin (S5.qA n) ≤ Real.sin (S5.qB n + θ0) := by
  let q : ℝ := S5.qA n
  have hq0 : 0 ≤ q := (S5.qA_pos hn16).le
  have hq4 : q ≤ Real.pi / 4 := S5.qA_le_pi_div_four hn16
  have hrew : S5.qB n + θ0 = (θ0 - q) + Real.pi / 2 := by
    dsimp [q]
    rw [S5.qB_eq]
    ring
  rw [hrew, Real.sin_add_pi_div_two]
  have hc2 : Real.cos (Real.pi / 2 - q) ≤ Real.cos (θ0 - q) := by
    by_cases hq : θ0 ≤ q
    · have hc1 : Real.cos (q - θ0) = Real.cos (θ0 - q) := by
        rw [show q - θ0 = -(θ0 - q) by ring]
        rw [Real.cos_neg]
      rw [← hc1]
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · linarith
      · nlinarith [hq4, Real.pi_pos]
      · nlinarith [hq4, hθ0a]
    · apply Real.cos_le_cos_of_nonneg_of_le_pi
      · linarith
      · nlinarith [hq0, Real.pi_pos]
      · linarith [hθ0b]
  have hgoal : Real.sin q ≤ Real.cos (θ0 - q) := by
    simpa [Real.cos_pi_div_two_sub] using hc2
  dsimp [q] at hgoal
  exact hgoal

/-- `sin(qA) > 0` -/
lemma sin_qA_pos (n : ℕ) (hn16 : 2 ^ 16 ≤ n) : 0 < Real.sin (S5.qA n) := by
  have h1 : 0 < S5.qA n := S5.qA_pos hn16
  have h2 : S5.qA n < Real.pi := lt_trans (S5.qA_lt_pi_div_four hn16) (by linarith [Real.pi_pos])
  exact Real.sin_pos_of_pos_of_lt_pi h1 h2

/-- `sin(qA) ≥ 200/n` -/
lemma sin_qA_ge (n : ℕ) (hn16 : 2 ^ 16 ≤ n) : (200 : ℝ) / (n : ℝ) ≤ Real.sin (S5.qA n) := by
  have hq0 : 0 ≤ S5.qA n := (S5.qA_pos hn16).le
  have hq2 : S5.qA n ≤ Real.pi / 2 := S5.qA_le_pi_div_two hn16
  have hm := Real.mul_le_sin hq0 hq2  -- (2/π)·qA ≤ sin qA
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (S5.n_ge_one hn16))
  unfold S5.qA at hm ⊢
  convert hm using 1
  field_simp [hn0, Real.pi_ne_zero]
  ring

/-- `1/sin(qA) ≤ n/200` -/
lemma inv_sin_qA_le (n : ℕ) (hn16 : 2 ^ 16 ≤ n) :
    1 / Real.sin (S5.qA n) ≤ (n : ℝ) / 200 := by
  have hsq : 0 < Real.sin (S5.qA n) := sin_qA_pos n hn16
  have hn0 : 0 < (n : ℝ) := S5.nR_pos hn16
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < Real.sin (S5.qA n)) (by norm_num : (0:ℝ) < 200)]
  have h := sin_qA_ge n hn16
  have hle : (200 : ℝ) ≤ Real.sin (S5.qA n) * (n : ℝ) := (div_le_iff₀ hn0).mp h
  nlinarith

/-- `g(qA) ≤ 1/sin(qA)` -/
lemma gInv_qA_le (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0a : 0 ≤ θ0)
    (hθ0b : θ0 ≤ Real.pi / 2) : gInv θ0 (S5.qA n) ≤ 1 / Real.sin (S5.qA n) := by
  have hs : 0 < Real.sin (S5.qA n) := sin_qA_pos n hn16
  have hle : Real.sin (S5.qA n) ≤ Real.sin (S5.qA n + θ0) := sin_qA_add_ge_sin_qA n hn16 hθ0a hθ0b
  unfold gInv
  exact S5.inv_rev_of_pos hs hle

/-- `g(qB) ≤ 1/sin(qA)` -/
lemma gInv_qB_le (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0a : 0 ≤ θ0)
    (hθ0b : θ0 ≤ Real.pi / 2) : gInv θ0 (S5.qB n) ≤ 1 / Real.sin (S5.qA n) := by
  have hs : 0 < Real.sin (S5.qA n) := sin_qA_pos n hn16
  have hle : Real.sin (S5.qA n) ≤ Real.sin (S5.qB n + θ0) := sin_qB_add_ge_sin_qA n hn16 hθ0a hθ0b
  unfold gInv
  exact S5.inv_rev_of_pos hs hle

/-- `1/sin(qA) ≤ n/200` combined with g: `g(qA)/n ≤ 1/200` -/
lemma gInv_qA_div_n_le (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0a : 0 ≤ θ0)
    (hθ0b : θ0 ≤ Real.pi / 2) : gInv θ0 (S5.qA n) / (n : ℝ) ≤ 1 / 200 := by
  have hn0 : 0 < (n : ℝ) := S5.nR_pos hn16
  calc
    gInv θ0 (S5.qA n) / (n : ℝ) ≤ (1 / Real.sin (S5.qA n)) / (n : ℝ) := by
      exact div_le_div_of_nonneg_right (gInv_qA_le n hn16 hθ0a hθ0b) hn0.le
    _ ≤ ((n : ℝ) / 200) / (n : ℝ) := by
      exact div_le_div_of_nonneg_right (inv_sin_qA_le n hn16) hn0.le
    _ = 1 / 200 := by
      field_simp [ne_of_gt hn0]

/-- `g(qB)/n ≤ 1/200` -/
lemma gInv_qB_div_n_le (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0a : 0 ≤ θ0)
    (hθ0b : θ0 ≤ Real.pi / 2) : gInv θ0 (S5.qB n) / (n : ℝ) ≤ 1 / 200 := by
  have hn0 : 0 < (n : ℝ) := S5.nR_pos hn16
  calc
    gInv θ0 (S5.qB n) / (n : ℝ) ≤ (1 / Real.sin (S5.qA n)) / (n : ℝ) := by
      exact div_le_div_of_nonneg_right (gInv_qB_le n hn16 hθ0a hθ0b) hn0.le
    _ ≤ ((n : ℝ) / 200) / (n : ℝ) := by
      exact div_le_div_of_nonneg_right (inv_sin_qA_le n hn16) hn0.le
    _ = 1 / 200 := by
      field_simp [ne_of_gt hn0]

/-- `12π/n ≤ 1/100` for `n ≥ 2^16` -/
lemma twelve_pi_div_n_le (n : ℕ) (hn16 : 2 ^ 16 ≤ n) : 12 * Real.pi / (n : ℝ) ≤ 1 / 100 := by
  have hn0 : 0 < (n : ℝ) := S5.nR_pos hn16
  have hbig : (1200 * Real.pi : ℝ) ≤ (n : ℝ) := by
    have h' : (2 ^ 16 : ℝ) ≤ (n : ℝ) := S5.nR_ge_pow hn16
    have h1200 : (1200 * Real.pi : ℝ) ≤ 2 ^ 16 := by
      have h4 : Real.pi ≤ 4 := Real.pi_le_four
      norm_num
      nlinarith
    linarith
  rw [div_le_div_iff₀ hn0 (by norm_num : (0:ℝ) < 100)]
  nlinarith


/-- absolute value of the second Dirichlet arc-integral -/
def Iabs (n N : ℕ) (F : Family.Quad n N) (θ0 : ℝ) (i : Fin N) : ℝ :=
  |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.DK2 n θ0 θ|

/-- `DK2 = (1/sin(θ+θ0)) · sin(2n(θ+θ0))` pointwise -/
lemma DK2_eq (n : ℕ) (θ0 θ : ℝ) :
    S5.DK2 n θ0 θ = gInv θ0 θ * Real.sin (2 * (n : ℝ) * (θ + θ0)) := by
  unfold S5.DK2 gInv
  ring

/-- `sin(θ+θ0)` is continuous and nonzero on an arc -/
lemma continuousOn_sin_add_arc (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    (i : Fin N) {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    ContinuousOn (fun θ : ℝ => Real.sin (θ + θ0))
      (Set.Icc (F.arc i).lo (F.arc i).hi) := by
  exact (Real.continuous_sin.comp (Continuous.add continuous_id continuous_const)).continuousOn

/-- `gInv θ0` is continuous on an arc -/
lemma continuousOn_gInv_arc (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    (i : Fin N) {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    ContinuousOn (gInv θ0) (Set.Icc (F.arc i).lo (F.arc i).hi) := by
  unfold gInv
  have hne : ∀ x ∈ Set.Icc (F.arc i).lo (F.arc i).hi, Real.sin (x + θ0) ≠ 0 := by
    intro x hx
    exact (S5.arc_sin_inv_bound n N hn16 F i hθ0a hθ0b hx).2.ne'
  exact ContinuousOn.div continuousOn_const (continuousOn_sin_add_arc n N hn16 F i hθ0a hθ0b) hne

/-- `gInv θ0` antitone on `[qA, c]` -/
lemma gInv_antitone_low (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0a : 0 ≤ θ0) :
    AntitoneOn (gInv θ0) (Set.Icc (S5.qA n) (cVal θ0)) := by
  intro x hx y hy hxy
  have hx0 : 0 < x + θ0 := by linarith [hx.1, S5.qA_pos hn16, hθ0a]
  have hy2 : y + θ0 ≤ Real.pi / 2 := by
    dsimp [cVal] at hy
    linarith [hy.2]
  have hxpi : x + θ0 < Real.pi := by linarith [hy2, hxy, Real.pi_pos]
  have hleSin : Real.sin (x + θ0) ≤ Real.sin (y + θ0) := by
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hx0, Real.pi_pos]) hy2 (by linarith)
  have hpos : 0 < Real.sin (x + θ0) :=
    Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  unfold gInv
  exact S5.inv_rev_of_pos hpos hleSin

/-- `gInv θ0` monotone on `[c, qB]` -/
lemma gInv_monotone_high (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0b : θ0 ≤ Real.pi / 2) :
    MonotoneOn (gInv θ0) (Set.Icc (cVal θ0) (S5.qB n)) := by
  intro x hx y hy hxy
  have hqA0 : 0 < S5.qA n := S5.qA_pos hn16
  have hqBpi : S5.qB n + θ0 ≤ Real.pi - S5.qA n := by
    rw [S5.qB_eq]
    linarith [hθ0b]
  have hxlow : Real.pi / 2 ≤ x + θ0 := by
    dsimp [cVal] at hx
    linarith [hx.1]
  have hylow : Real.pi / 2 ≤ y + θ0 := by linarith [hxlow, hxy]
  have hyhi : y + θ0 < Real.pi := by
    dsimp [cVal] at hy
    linarith [hy.2, hqBpi, hqA0]
  have hxhi : x + θ0 < Real.pi := by linarith [hyhi, hxy]
  have hleSin : Real.sin (y + θ0) ≤ Real.sin (x + θ0) := by
    apply sin_anti_right
    · exact ⟨hxlow, hxhi.le⟩
    · exact ⟨hylow, hyhi.le⟩
    · linarith
  have hpos : 0 < Real.sin (y + θ0) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hylow, Real.pi_pos]) hyhi
  unfold gInv
  exact S5.inv_rev_of_pos hpos hleSin

/-- LOW arc: `sin` monotone on the arc (g antitone) ⇒ per-arc bound -/
lemma arc_DK2_low_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2)
    (hLOW : (F.arc i).hi ≤ cVal θ0) :
    |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.DK2 n θ0 θ|
      ≤ (gInv θ0 (F.arc i).lo - gInv θ0 (F.arc i).hi) / (n : ℝ) := by
  let a : ℝ := (F.arc i).lo
  let b : ℝ := (F.arc i).hi
  have hab : a ≤ b := by dsimp [a, b]; exact (S5.arc_lo_lt_hi hn16 F i).le
  rcases S5.arc_len_multiple hn16 F i with ⟨m, hm6, hm⟩
  have hantiOnArc : AntitoneOn (gInv θ0) (Set.Icc a b) := by
    refine (gInv_antitone_low n hn16 hθ0a).mono ?_
    intro x hx
    dsimp [a, b] at hx
    exact ⟨le_trans (S5.arc_lo_ge_qA hn16 F i) hx.1, le_trans hx.2 hLOW⟩
  have hcont : ContinuousOn (gInv θ0) (Set.Icc a b) := by
    dsimp [a, b]
    exact continuousOn_gInv_arc n N hn16 F i hθ0a hθ0b
  have hanti : ∀ (x y : ℝ), x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      gInv θ0 y ≤ gInv θ0 x := by
    intro x y hx hy hxy
    exact hantiOnArc hx hy hxy
  have hbnd := S5.antitone_sin_shifted n (S5.n_ge_one hn16) a b (-θ0) hab (gInv θ0)
    hcont hanti ⟨m, by dsimp [a, b]; exact hm⟩
  have hI : (∫ θ in a..b, S5.DK2 n θ0 θ)
      = ∫ θ in a..b, gInv θ0 θ * Real.sin (2 * (n : ℝ) * (θ + θ0)) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact DK2_eq n θ0 θ
  have hanti_ab : gInv θ0 b ≤ gInv θ0 a := by
    exact hantiOnArc (by dsimp [a, b]; exact ⟨le_rfl, hab⟩) (by dsimp [a, b]; exact ⟨hab, le_rfl⟩) hab
  have habs : |gInv θ0 b - gInv θ0 a| = gInv θ0 a - gInv θ0 b := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hanti_ab)]
  have hsub : (gInv θ0 a - gInv θ0 b) / (n : ℝ) ≤
      (gInv θ0 (F.arc i).lo - gInv θ0 (F.arc i).hi) / (n : ℝ) := by
    exact le_of_eq (by dsimp [a, b])
  have hbnd' : |∫ θ in a..b, S5.DK2 n θ0 θ|
      ≤ (gInv θ0 a - gInv θ0 b) / (n : ℝ) := by
    rw [hI]
    calc
      |∫ θ in a..b, gInv θ0 θ * Real.sin (2 * (n : ℝ) * (θ + θ0))|
          = |∫ θ in a..b, gInv θ0 θ * Real.sin (2 * (n : ℝ) * (θ - (-θ0)))| := by
            apply congrArg (fun t : ℝ => |t|)
            apply intervalIntegral.integral_congr
            intro θ hθ
            ring
      _ ≤ |gInv θ0 b - gInv θ0 a| / (n : ℝ) := hbnd
      _ = (gInv θ0 a - gInv θ0 b) / (n : ℝ) := by rw [habs]
  exact le_trans (by simpa [a, b] using hbnd') hsub

/-- HIGH arc: `sin` antitone on the arc (g monotone) ⇒ per-arc bound -/
lemma arc_DK2_high_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2)
    (hHIGH : cVal θ0 ≤ (F.arc i).lo) :
    |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.DK2 n θ0 θ|
      ≤ (gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo) / (n : ℝ) := by
  let a : ℝ := (F.arc i).lo
  let b : ℝ := (F.arc i).hi
  have hab : a ≤ b := by dsimp [a, b]; exact (S5.arc_lo_lt_hi hn16 F i).le
  rcases S5.arc_len_multiple hn16 F i with ⟨m, hm6, hm⟩
  have hmonoOnArc : MonotoneOn (gInv θ0) (Set.Icc a b) := by
    refine (gInv_monotone_high n hn16 hθ0b).mono ?_
    intro x hx
    dsimp [a, b] at hx
    exact ⟨le_trans hHIGH hx.1, le_trans hx.2 (S5.arc_hi_le_qB hn16 F i)⟩
  have hcont : ContinuousOn (gInv θ0) (Set.Icc a b) := by
    dsimp [a, b]
    exact continuousOn_gInv_arc n N hn16 F i hθ0a hθ0b
  have hmono : ∀ (x y : ℝ), x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      gInv θ0 x ≤ gInv θ0 y := by
    intro x y hx hy hxy
    exact hmonoOnArc hx hy hxy
  have hbnd := S5.monotone_sin_shifted n (S5.n_ge_one hn16) a b (-θ0) hab (gInv θ0)
    hcont hmono ⟨m, by dsimp [a, b]; exact hm⟩
  have hI : (∫ θ in a..b, S5.DK2 n θ0 θ)
      = ∫ θ in a..b, gInv θ0 θ * Real.sin (2 * (n : ℝ) * (θ + θ0)) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact DK2_eq n θ0 θ
  have hmono_ab : gInv θ0 a ≤ gInv θ0 b := by
    exact hmonoOnArc (by dsimp [a, b]; exact ⟨le_rfl, hab⟩) (by dsimp [a, b]; exact ⟨hab, le_rfl⟩) hab
  have habs : |gInv θ0 b - gInv θ0 a| = gInv θ0 b - gInv θ0 a := by
    exact abs_of_nonneg (sub_nonneg.mpr hmono_ab)
  have hsub : (gInv θ0 b - gInv θ0 a) / (n : ℝ) ≤
      (gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo) / (n : ℝ) := by
    exact le_of_eq (by dsimp [a, b])
  have hbnd' : |∫ θ in a..b, S5.DK2 n θ0 θ|
      ≤ (gInv θ0 b - gInv θ0 a) / (n : ℝ) := by
    rw [hI]
    calc
      |∫ θ in a..b, gInv θ0 θ * Real.sin (2 * (n : ℝ) * (θ + θ0))|
          = |∫ θ in a..b, gInv θ0 θ * Real.sin (2 * (n : ℝ) * (θ - (-θ0)))| := by
            apply congrArg (fun t : ℝ => |t|)
            apply intervalIntegral.integral_congr
            intro θ hθ
            ring
      _ ≤ |gInv θ0 b - gInv θ0 a| / (n : ℝ) := hbnd
      _ = (gInv θ0 b - gInv θ0 a) / (n : ℝ) := by rw [habs]
  exact le_trans (by simpa [a, b] using hbnd') hsub

/-- if `u` is within `π/3` of `π/2` then `sin u ≥ 1/2` -/
lemma sin_ge_one_half {u : ℝ} (hu : |u - Real.pi / 2| ≤ Real.pi / 3) :
    (1 / 2 : ℝ) ≤ Real.sin u := by
  by_cases hle : u ≤ Real.pi / 2
  · have hw0 : 0 ≤ Real.pi / 2 - u := sub_nonneg.mpr hle
    have hw : Real.pi / 2 - u ≤ Real.pi / 3 := by
      have habs : |u - Real.pi / 2| = Real.pi / 2 - u := by
        rw [abs_sub_comm, abs_of_nonneg hw0]
      linarith [hu, habs]
    have hsin : Real.sin u = Real.cos (Real.pi / 2 - u) := by
      rw [Real.cos_pi_div_two_sub]
    rw [hsin]
    have hc : Real.cos (Real.pi / 3) ≤ Real.cos (Real.pi / 2 - u) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · linarith [hw0]
      · linarith [hw, Real.pi_pos]
      · exact hw
    simpa [Real.cos_pi_div_three] using hc
  · have hgt : Real.pi / 2 < u := lt_of_not_ge hle
    have hw0 : 0 ≤ u - Real.pi / 2 := sub_nonneg.mpr hgt.le
    have hw : u - Real.pi / 2 ≤ Real.pi / 3 := by
      have habs : |u - Real.pi / 2| = u - Real.pi / 2 := abs_of_nonneg hw0
      linarith [hu, habs]
    have hsin : Real.sin u = Real.cos (u - Real.pi / 2) := by
      rw [← Real.sin_add_pi_div_two (u - Real.pi / 2)]
      congr 1
      ring
    rw [hsin]
    have hc : Real.cos (Real.pi / 3) ≤ Real.cos (u - Real.pi / 2) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · linarith [hw0]
      · linarith [hw, Real.pi_pos]
      · exact hw
    simpa [Real.cos_pi_div_three] using hc

/-- point `θ` between `a` and `c` and `c` between `a` and `b`: `|θ−c| ≤ b−a` -/
lemma abs_sub_c_le_len {c a b θ : ℝ} (hac : a < c) (hcb : c < b)
    (hθl : a ≤ θ) (hθr : θ ≤ b) : |θ - c| ≤ b - a := by
  by_cases hθc : θ ≤ c
  · have habs : |θ - c| = c - θ := by
      rw [abs_of_nonpos (sub_nonpos.mpr hθc), neg_sub]
    rw [habs]
    linarith
  · have hcθ : c ≤ θ := le_of_not_ge hθc
    have habs : |θ - c| = θ - c := abs_of_nonneg (sub_nonneg.mpr hcθ)
    rw [habs]
    linarith

/-- `DK2` continuous on an arc -/
lemma continuousOn_DK2_arc (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    (i : Fin N) {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    ContinuousOn (S5.DK2 n θ0) (Set.Icc (F.arc i).lo (F.arc i).hi) := by
  unfold S5.DK2
  have hne : ∀ x ∈ Set.Icc (F.arc i).lo (F.arc i).hi, Real.sin (x + θ0) ≠ 0 := by
    intro x hx
    exact (S5.arc_sin_inv_bound n N hn16 F i hθ0a hθ0b hx).2.ne'
  refine ContinuousOn.div ?_ (continuousOn_sin_add_arc n N hn16 F i hθ0a hθ0b) hne
  fun_prop


/-- MID (straddling) arc: crude bound `2·(hi−lo) ≤ 12π/n` -/
lemma arc_DK2_mid_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2)
    (hmid : (F.arc i).lo < cVal θ0 ∧ cVal θ0 < (F.arc i).hi) :
    |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.DK2 n θ0 θ| ≤ 12 * Real.pi / (n : ℝ) := by
  let a : ℝ := (F.arc i).lo
  let b : ℝ := (F.arc i).hi
  have hab : a ≤ b := by dsimp [a, b]; exact (S5.arc_lo_lt_hi hn16 F i).le
  have h6 : b - a ≤ 6 * Real.pi / (n : ℝ) := by
    dsimp [a, b]
    exact S5.arc_len_le_six hn16 F i
  have hn0 : 0 < (n : ℝ) := S5.nR_pos hn16
  have h6pi : 6 * Real.pi / (n : ℝ) ≤ Real.pi / 3 := by
    have hn18 : (18 : ℝ) ≤ (n : ℝ) := by
      have h' : (2 ^ 16 : ℝ) ≤ (n : ℝ) := S5.nR_ge_pow hn16
      norm_num at h' ⊢
      linarith
    rw [div_le_div_iff₀ hn0 (by norm_num : (0:ℝ) < 3)]
    nlinarith [mul_le_mul_of_nonneg_right hn18 Real.pi_pos.le]
  have hpoint : ∀ θ ∈ Set.Icc a b, |S5.DK2 n θ0 θ| ≤ 2 := by
    intro θ hθ
    have hsub : |θ - cVal θ0| ≤ b - a := by
      exact abs_sub_c_le_len hmid.1 hmid.2 hθ.1 hθ.2
    have hdist : |(θ + θ0) - Real.pi / 2| ≤ b - a := by
      have harg : (θ + θ0) - Real.pi / 2 = θ - cVal θ0 := by
        dsimp [cVal]
        ring
      simpa [harg] using hsub
    have hdist3 : |(θ + θ0) - Real.pi / 2| ≤ Real.pi / 3 := le_trans hdist (le_trans h6 h6pi)
    have h12 : (1 / 2 : ℝ) ≤ Real.sin (θ + θ0) := sin_ge_one_half hdist3
    have hpos : 0 < Real.sin (θ + θ0) := lt_of_lt_of_le (by norm_num) h12
    have h1 : |Real.sin (2 * (n : ℝ) * (θ + θ0))| ≤ 1 := Real.abs_sin_le_one _
    have hlow : 1 / Real.sin (θ + θ0) ≤ 2 := by
      have h12p : 0 < (1 / 2 : ℝ) := by norm_num
      have h' : (Real.sin (θ + θ0))⁻¹ ≤ 2 := by
        have h'' := one_div_le_one_div_of_le h12p h12
        norm_num at h''
        simpa using h''
      simpa using h'
    unfold S5.DK2
    rw [abs_div]
    rw [abs_of_pos hpos]
    calc
      |Real.sin (2 * (n : ℝ) * (θ + θ0))| / Real.sin (θ + θ0)
          ≤ 1 / Real.sin (θ + θ0) := div_le_div_of_nonneg_right h1 hpos.le
      _ ≤ 2 := hlow
  have hc1 : ContinuousOn (S5.DK2 n θ0) (Set.Icc a b) := by
    dsimp [a, b]
    exact continuousOn_DK2_arc n N hn16 F i hθ0a hθ0b
  have hI : IntervalIntegrable (S5.DK2 n θ0) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hc1
  have hIabs : IntervalIntegrable (fun θ : ℝ => |S5.DK2 n θ0 θ|) volume a b := hI.abs
  have hI2 : IntervalIntegrable (fun θ : ℝ => (2 : ℝ)) volume a b := by
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (2 : ℝ)) (Set.Icc a b)).intervalIntegrable_of_Icc hab
  have hle1 : |∫ θ in a..b, S5.DK2 n θ0 θ| ≤ ∫ θ in a..b, |S5.DK2 n θ0 θ| :=
    intervalIntegral.abs_integral_le_integral_abs hab
  have hle2 : (∫ θ in a..b, |S5.DK2 n θ0 θ|) ≤ ∫ θ in a..b, (2 : ℝ) := by
    exact intervalIntegral.integral_mono_on hab hIabs hI2 hpoint
  have hle3 : (∫ θ in a..b, (2 : ℝ)) ≤ 12 * Real.pi / (n : ℝ) := by
    rw [intervalIntegral.integral_const]
    rw [smul_eq_mul]
    have hcalc : 6 * Real.pi / (n : ℝ) * 2 = 12 * Real.pi / (n : ℝ) := by
      field_simp [ne_of_gt hn0]
      ring
    calc
      (b - a) * 2 ≤ 6 * Real.pi / (n : ℝ) * 2 :=
        mul_le_mul_of_nonneg_right h6 (by norm_num : (0:ℝ) ≤ 2)
      _ = 12 * Real.pi / (n : ℝ) := hcalc
  exact le_trans hle1 (le_trans hle2 hle3)

/-- LOW arcs (entirely left of `c`): total ≤ `g(qA)/n` -/
lemma low_sum_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i : Fin N, if (F.arc i).hi ≤ cVal θ0 then Iabs n N F θ0 i else 0)
      ≤ gInv θ0 (S5.qA n) / (n : ℝ) := by
  classical
  let Plo : Fin N → Prop := fun i => (F.arc i).hi ≤ cVal θ0
  have hn0 : 0 < (n : ℝ) := S5.nR_pos hn16
  by_cases hq : cVal θ0 < S5.qA n
  · have hset : (Finset.univ.filter Plo) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi hp
      have hlt : (F.arc i).lo < (F.arc i).hi := S5.arc_lo_lt_hi hn16 F i
      have hlo : S5.qA n ≤ (F.arc i).lo := S5.arc_lo_ge_qA hn16 F i
      dsimp [Plo] at hp
      linarith
    have hpos : 0 ≤ gInv θ0 (S5.qA n) := (gInv_qA_pos n hn16 hθ0a hθ0b).le
    calc
      (∑ i : Fin N, if Plo i then Iabs n N F θ0 i else 0)
          = ∑ i ∈ (Finset.univ.filter Plo), Iabs n N F θ0 i := by
            rw [Finset.sum_filter]
      _ = 0 := by simp [hset]
      _ ≤ gInv θ0 (S5.qA n) / (n : ℝ) := by exact div_nonneg hpos hn0.le
  · have hq' : S5.qA n ≤ cVal θ0 := le_of_not_gt hq
    have htele : (∑ i ∈ (Finset.univ.filter Plo),
        |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo|)
        ≤ |gInv θ0 (cVal θ0) - gInv θ0 (S5.qA n)| := by
      exact S5Tele.sum_var_le_anti (s := Finset.univ.filter Plo)
        (lo := fun i : Fin N => (F.arc i).lo) (hi := fun i : Fin N => (F.arc i).hi)
        (A := S5.qA n) (B := cVal θ0) hq'
        (hA := fun i hi => S5.arc_lo_ge_qA hn16 F i)
        (hB := fun i hi => (Finset.mem_filter.mp hi).2)
        (hle := fun i hi => Family.Grid.lo_le_hi (F.arc i))
        (hsep := fun i hi j hj hij =>
          (S5.arc_sep hn16 F hij).elim (fun h => Or.inl (le_of_lt h)) (fun h => Or.inr (le_of_lt h)))
        (h := gInv θ0) (gInv_antitone_low n hn16 hθ0a)
    have hantiAB : gInv θ0 (cVal θ0) ≤ gInv θ0 (S5.qA n) := by
      exact gInv_antitone_low n hn16 hθ0a ⟨le_rfl, hq'⟩ ⟨hq', le_rfl⟩ hq'
    have hgpos : 0 ≤ gInv θ0 (cVal θ0) := by rw [gInv_c θ0]; norm_num
    have habs : |gInv θ0 (cVal θ0) - gInv θ0 (S5.qA n)|
        = gInv θ0 (S5.qA n) - gInv θ0 (cVal θ0) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hantiAB)]
      ring
    have hle1 : |gInv θ0 (cVal θ0) - gInv θ0 (S5.qA n)| ≤ gInv θ0 (S5.qA n) := by
      rw [habs]
      linarith
    calc
      (∑ i : Fin N, if Plo i then Iabs n N F θ0 i else 0)
          = ∑ i ∈ (Finset.univ.filter Plo), Iabs n N F θ0 i := by
            rw [Finset.sum_filter]
      _ ≤ ∑ i ∈ (Finset.univ.filter Plo),
            |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo| / (n : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            have hanti_i : gInv θ0 (F.arc i).hi ≤ gInv θ0 (F.arc i).lo := by
              have harc : AntitoneOn (gInv θ0) (Set.Icc (F.arc i).lo (F.arc i).hi) := by
                refine (gInv_antitone_low n hn16 hθ0a).mono ?_
                intro x hx
                exact ⟨le_trans (S5.arc_lo_ge_qA hn16 F i) hx.1, le_trans hx.2 (Finset.mem_filter.mp hi).2⟩
              exact harc ⟨le_rfl, (S5.arc_lo_lt_hi hn16 F i).le⟩
                ⟨(S5.arc_lo_lt_hi hn16 F i).le, le_rfl⟩ (S5.arc_lo_lt_hi hn16 F i).le
            have habs_i : |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo|
                = gInv θ0 (F.arc i).lo - gInv θ0 (F.arc i).hi := by
              rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hanti_i)]
            calc
              Iabs n N F θ0 i
                  ≤ (gInv θ0 (F.arc i).lo - gInv θ0 (F.arc i).hi) / (n : ℝ) :=
                    arc_DK2_low_bound n N hn16 F i hθ0a hθ0b (Finset.mem_filter.mp hi).2
              _ = |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo| / (n : ℝ) := by rw [habs_i]
      _ = (∑ i ∈ (Finset.univ.filter Plo),
            |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo|) / (n : ℝ) := by
            rw [Finset.sum_div]
      _ ≤ |gInv θ0 (cVal θ0) - gInv θ0 (S5.qA n)| / (n : ℝ) := by
            exact div_le_div_of_nonneg_right htele hn0.le
      _ ≤ gInv θ0 (S5.qA n) / (n : ℝ) := by
            exact div_le_div_of_nonneg_right hle1 hn0.le

/-- HIGH arcs (entirely right of `c`): total ≤ `g(qB)/n` -/
lemma high_sum_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i : Fin N, if cVal θ0 ≤ (F.arc i).lo then Iabs n N F θ0 i else 0)
      ≤ gInv θ0 (S5.qB n) / (n : ℝ) := by
  classical
  let Phi : Fin N → Prop := fun i => cVal θ0 ≤ (F.arc i).lo
  have hn0 : 0 < (n : ℝ) := S5.nR_pos hn16
  by_cases hq : S5.qB n < cVal θ0
  · have hset : (Finset.univ.filter Phi) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi hp
      have hlt : (F.arc i).lo < (F.arc i).hi := S5.arc_lo_lt_hi hn16 F i
      have hhi : (F.arc i).hi ≤ S5.qB n := S5.arc_hi_le_qB hn16 F i
      dsimp [Phi] at hp
      linarith
    have hpos : 0 ≤ gInv θ0 (S5.qB n) := (gInv_qB_pos n hn16 hθ0a hθ0b).le
    calc
      (∑ i : Fin N, if Phi i then Iabs n N F θ0 i else 0)
          = ∑ i ∈ (Finset.univ.filter Phi), Iabs n N F θ0 i := by
            rw [Finset.sum_filter]
      _ = 0 := by simp [hset]
      _ ≤ gInv θ0 (S5.qB n) / (n : ℝ) := by exact div_nonneg hpos hn0.le
  · have hq' : cVal θ0 ≤ S5.qB n := le_of_not_gt hq
    have htele : (∑ i ∈ (Finset.univ.filter Phi),
        |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo|)
        ≤ |gInv θ0 (S5.qB n) - gInv θ0 (cVal θ0)| := by
      exact S5Tele.sum_var_le_mono (s := Finset.univ.filter Phi)
        (lo := fun i : Fin N => (F.arc i).lo) (hi := fun i : Fin N => (F.arc i).hi)
        (A := cVal θ0) (B := S5.qB n) hq'
        (hA := fun i hi => (Finset.mem_filter.mp hi).2)
        (hB := fun i hi => S5.arc_hi_le_qB hn16 F i)
        (hle := fun i hi => Family.Grid.lo_le_hi (F.arc i))
        (hsep := fun i hi j hj hij =>
          (S5.arc_sep hn16 F hij).elim (fun h => Or.inl (le_of_lt h)) (fun h => Or.inr (le_of_lt h)))
        (h := gInv θ0) (gInv_monotone_high n hn16 hθ0b)
    have hmonoAB : gInv θ0 (cVal θ0) ≤ gInv θ0 (S5.qB n) := by
      exact gInv_monotone_high n hn16 hθ0b ⟨le_rfl, hq'⟩ ⟨hq', le_rfl⟩ hq'
    have hgpos : 0 ≤ gInv θ0 (cVal θ0) := by rw [gInv_c θ0]; norm_num
    have habs : |gInv θ0 (S5.qB n) - gInv θ0 (cVal θ0)|
        = gInv θ0 (S5.qB n) - gInv θ0 (cVal θ0) := by
      exact abs_of_nonneg (sub_nonneg.mpr hmonoAB)
    have hle1 : |gInv θ0 (S5.qB n) - gInv θ0 (cVal θ0)| ≤ gInv θ0 (S5.qB n) := by
      rw [habs]
      linarith
    calc
      (∑ i : Fin N, if Phi i then Iabs n N F θ0 i else 0)
          = ∑ i ∈ (Finset.univ.filter Phi), Iabs n N F θ0 i := by
            rw [Finset.sum_filter]
      _ ≤ ∑ i ∈ (Finset.univ.filter Phi),
            |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo| / (n : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            have hmono_i : gInv θ0 (F.arc i).lo ≤ gInv θ0 (F.arc i).hi := by
              have harc : MonotoneOn (gInv θ0) (Set.Icc (F.arc i).lo (F.arc i).hi) := by
                refine (gInv_monotone_high n hn16 hθ0b).mono ?_
                intro x hx
                exact ⟨le_trans (Finset.mem_filter.mp hi).2 hx.1, le_trans hx.2 (S5.arc_hi_le_qB hn16 F i)⟩
              exact harc ⟨le_rfl, (S5.arc_lo_lt_hi hn16 F i).le⟩
                ⟨(S5.arc_lo_lt_hi hn16 F i).le, le_rfl⟩ (S5.arc_lo_lt_hi hn16 F i).le
            have habs_i : |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo|
                = gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo := by
              exact abs_of_nonneg (sub_nonneg.mpr hmono_i)
            calc
              Iabs n N F θ0 i
                  ≤ (gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo) / (n : ℝ) :=
                    arc_DK2_high_bound n N hn16 F i hθ0a hθ0b (Finset.mem_filter.mp hi).2
              _ = |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo| / (n : ℝ) := by rw [habs_i]
      _ = (∑ i ∈ (Finset.univ.filter Phi),
            |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo|) / (n : ℝ) := by
            rw [Finset.sum_div]
      _ ≤ |gInv θ0 (S5.qB n) - gInv θ0 (cVal θ0)| / (n : ℝ) := by
            exact div_le_div_of_nonneg_right htele hn0.le
      _ ≤ gInv θ0 (S5.qB n) / (n : ℝ) := by
            exact div_le_div_of_nonneg_right hle1 hn0.le

/-- MID (at most one straddling) arcs: total ≤ `12π/n` -/
lemma mid_sum_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i : Fin N, if (F.arc i).lo < cVal θ0 ∧ cVal θ0 < (F.arc i).hi
        then Iabs n N F θ0 i else 0) ≤ 12 * Real.pi / (n : ℝ) := by
  classical
  let Pmid : Fin N → Prop := fun i => (F.arc i).lo < cVal θ0 ∧ cVal θ0 < (F.arc i).hi
  let midSet : Finset (Fin N) := Finset.univ.filter Pmid
  have hcard : midSet.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    refine S5.one_arc_contains hn16 F (cVal θ0) a b ?_ ?_
    · exact ⟨(Finset.mem_filter.mp ha).2.1.le, (Finset.mem_filter.mp ha).2.2.le⟩
    · exact ⟨(Finset.mem_filter.mp hb).2.1.le, (Finset.mem_filter.mp hb).2.2.le⟩
  have hper : ∀ i ∈ midSet, Iabs n N F θ0 i ≤ 12 * Real.pi / (n : ℝ) := by
    intro i hi
    exact arc_DK2_mid_bound n N hn16 F i hθ0a hθ0b (Finset.mem_filter.mp hi).2
  have hM0 : 0 ≤ 12 * Real.pi / (n : ℝ) := by positivity
  have hsum : (∑ i ∈ midSet, Iabs n N F θ0 i) ≤ 12 * Real.pi / (n : ℝ) := by
    by_cases hne : midSet = ∅
    · simp [hne, hM0]
    · have hnonempty : midSet.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      rcases hnonempty with ⟨a, ha⟩
      have hsingle : ∀ b ∈ midSet, b = a := by
        intro b hb
        exact (Finset.card_le_one.mp hcard) b hb a ha
      have hsum_a : (∑ i ∈ midSet, Iabs n N F θ0 i) = Iabs n N F θ0 a := by
        apply Finset.sum_eq_single a
        · intro b hb hba
          have : b = a := hsingle b hb
          exact False.elim (hba this)
        · intro ha_not
          exact False.elim (ha_not ha)
      rw [hsum_a]
      exact hper a ha
  calc
    (∑ i : Fin N, if Pmid i then Iabs n N F θ0 i else 0)
        = ∑ i ∈ (Finset.univ.filter Pmid), Iabs n N F θ0 i := by
          rw [Finset.sum_filter]
    _ ≤ 12 * Real.pi / (n : ℝ) := hsum

/-- Claim 1 -/
theorem claim1_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i : Fin N, |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.DK2 n θ0 θ|) ≤ 1 / 50 := by
  classical
  change (∑ i : Fin N, Iabs n N F θ0 i) ≤ 1 / 50
  let Plo : Fin N → Prop := fun i => (F.arc i).hi ≤ cVal θ0
  let Phi : Fin N → Prop := fun i => cVal θ0 ≤ (F.arc i).lo
  let Pmid : Fin N → Prop := fun i => (F.arc i).lo < cVal θ0 ∧ cVal θ0 < (F.arc i).hi
  have htri : ∀ i : Fin N, Plo i ∨ Phi i ∨ Pmid i := by
    intro i
    by_cases h1 : (F.arc i).hi ≤ cVal θ0
    · exact Or.inl h1
    · have hc_hi : cVal θ0 < (F.arc i).hi := lt_of_not_ge h1
      by_cases h2 : cVal θ0 ≤ (F.arc i).lo
      · exact Or.inr (Or.inl h2)
      · have hc_lo : (F.arc i).lo < cVal θ0 := lt_of_not_ge h2
        exact Or.inr (Or.inr ⟨hc_lo, hc_hi⟩)
  have hx12 : ∀ i : Fin N, Plo i → ¬ Phi i := by
    intro i hp hq
    have hlt : (F.arc i).lo < (F.arc i).hi := S5.arc_lo_lt_hi hn16 F i
    linarith
  have hx13 : ∀ i : Fin N, Plo i → ¬ Pmid i := by
    intro i hp hq
    dsimp [Plo, Pmid] at hp hq
    linarith
  have hx23 : ∀ i : Fin N, Phi i → ¬ Pmid i := by
    intro i hp hq
    dsimp [Phi, Pmid] at hp hq
    linarith
  have hdecomp : (∑ i : Fin N, Iabs n N F θ0 i)
      = (∑ i : Fin N, if Plo i then Iabs n N F θ0 i else 0)
      + (∑ i : Fin N, if Phi i then Iabs n N F θ0 i else 0)
      + (∑ i : Fin N, if Pmid i then Iabs n N F θ0 i else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h1 : Plo i
    · have hn2 : ¬ Phi i := hx12 i h1
      have hn3 : ¬ Pmid i := hx13 i h1
      simp [h1, hn2, hn3]
    · by_cases h2 : Phi i
      · have hn1 : ¬ Plo i := h1
        have hn3 : ¬ Pmid i := hx23 i h2
        simp [hn1, h2, hn3]
      · have h3 : Pmid i := by
          rcases htri i with h | h | h
          · exact False.elim (h1 h)
          · exact False.elim (h2 h)
          · exact h
        simp [h1, h2, h3]
  have hL : (∑ i : Fin N, if Plo i then Iabs n N F θ0 i else 0)
      ≤ gInv θ0 (S5.qA n) / (n : ℝ) := by
    simpa [Plo] using low_sum_bound n N hn16 F hθ0a hθ0b
  have hH : (∑ i : Fin N, if Phi i then Iabs n N F θ0 i else 0)
      ≤ gInv θ0 (S5.qB n) / (n : ℝ) := by
    simpa [Phi] using high_sum_bound n N hn16 F hθ0a hθ0b
  have hM : (∑ i : Fin N, if Pmid i then Iabs n N F θ0 i else 0)
      ≤ 12 * Real.pi / (n : ℝ) := by
    simpa [Pmid] using mid_sum_bound n N hn16 F hθ0a hθ0b
  calc
    (∑ i : Fin N, Iabs n N F θ0 i)
        = (∑ i : Fin N, if Plo i then Iabs n N F θ0 i else 0)
          + (∑ i : Fin N, if Phi i then Iabs n N F θ0 i else 0)
          + (∑ i : Fin N, if Pmid i then Iabs n N F θ0 i else 0) := hdecomp
    _ ≤ gInv θ0 (S5.qA n) / (n : ℝ) + gInv θ0 (S5.qB n) / (n : ℝ)
        + 12 * Real.pi / (n : ℝ) := by
          linarith
    _ ≤ 1 / 200 + 1 / 200 + 1 / 100 := by
          have hA : gInv θ0 (S5.qA n) / (n : ℝ) ≤ 1 / 200 := gInv_qA_div_n_le n hn16 hθ0a hθ0b
          have hB : gInv θ0 (S5.qB n) / (n : ℝ) ≤ 1 / 200 := gInv_qB_div_n_le n hn16 hθ0a hθ0b
          have hC : 12 * Real.pi / (n : ℝ) ≤ 1 / 100 := twelve_pi_div_n_le n hn16
          linarith
    _ = 1 / 50 := by norm_num
