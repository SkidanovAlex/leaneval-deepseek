import Mathlib.Analysis.Convex.Slope
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Generic real analysis: pointwise convergent concave functions on a half-line
converge uniformly on *interior* compact intervals.
-/

namespace Submission

open Filter Metric
open scoped Topology

/-- Concave function: value at `x` (to the right of `q`) is bounded above by the secant
extrapolation from `p`, `q`. -/
lemma concaveOn_secant_upper {s : Set ℝ} {φ : ℝ → ℝ} {p q x : ℝ}
    (hφ : ConcaveOn ℝ s φ) (hp : p ∈ s) (hx : x ∈ s) (hpq : p < q) (hqx : q < x) :
    φ x - φ q ≤ (x - q) * ((φ q - φ p) / (q - p)) := by
  have hsl := hφ.slope_anti_adjacent hp hx hpq hqx
  have hxq : 0 < x - q := sub_pos.mpr hqx
  calc
    φ x - φ q = ((φ x - φ q) / (x - q)) * (x - q) := by
      field_simp [hxq.ne']
    _ ≤ ((φ q - φ p) / (q - p)) * (x - q) := mul_le_mul_of_nonneg_right hsl hxq.le
    _ = (x - q) * ((φ q - φ p) / (q - p)) := by ring

/-- Concave function: value at `x` between `p` and `d` lies above the chord. -/
lemma concaveOn_chord_lower {s : Set ℝ} {φ : ℝ → ℝ} {p x d : ℝ}
    (hφ : ConcaveOn ℝ s φ) (hp : p ∈ s) (hd : d ∈ s) (hpx : p < x) (hxd : x < d) :
    ((d - x) / (d - p)) * φ p + ((x - p) / (d - p)) * φ d ≤ φ x := by
  have hpd : p < d := lt_trans hpx hxd
  have hdp : d - p ≠ 0 := by linarith
  let w1 : ℝ := (d - x) / (d - p)
  let w2 : ℝ := (x - p) / (d - p)
  have hw1 : 0 ≤ w1 := by
    dsimp [w1]
    exact div_nonneg (by linarith) (by linarith)
  have hw2 : 0 ≤ w2 := by
    dsimp [w2]
    exact div_nonneg (by linarith) (by linarith)
  have hsum : w1 + w2 = 1 := by
    dsimp [w1, w2]
    field_simp [hdp]
    ring
  have hxcomb : w1 * p + w2 * d = x := by
    dsimp [w1, w2]
    field_simp [hdp]
    ring
  have hφcomb := hφ.2 hp hd hw1 hw2 hsum
  simp [smul_eq_mul, hxcomb] at hφcomb
  simpa [w1, w2, add_comm, add_left_comm, add_assoc] using hφcomb

/-! Specialise to concave functions on the half-line `[0,∞)`, interval `[a,b]`,
`0 < a ≤ b`, reference points `a/2`, `3a/4`, `b + 1`. -/

/-- A concave function on `[0,∞)` bounded by `W` at `a/2` and `3a/4` is bounded above
by `W + (b - 3a/4) * (2W) / (3a/4 - a/2)` on `[a,b]`. -/
lemma concaveOn_upper_Icc {φ : ℝ → ℝ} {a b W : ℝ}
    (h0a : 0 < a) (hab : a ≤ b) (hW : 0 ≤ W)
    (hφ : ConcaveOn ℝ (Set.Ici (0 : ℝ)) φ)
    (hbnd1 : |φ (a / 2)| ≤ W) (hbnd2 : |φ (3 * a / 4)| ≤ W) :
    ∀ x : ℝ, x ∈ Set.Icc a b →
      φ x ≤ W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) := by
  intro x hx
  have hx1 : a ≤ x := hx.1
  have hx2 : x ≤ b := hx.2
  have hqa : 3 * a / 4 < a := by nlinarith [h0a]
  have hqx : 3 * a / 4 < x := lt_of_lt_of_le hqa hx1
  have hpq : a / 2 < 3 * a / 4 := by nlinarith [h0a]
  have hp0 : 0 ≤ a / 2 := by positivity
  have hq0 : 0 ≤ 3 * a / 4 := by positivity
  have hx0 : 0 ≤ x := le_trans (by positivity : 0 ≤ a) hx1
  have hsec := concaveOn_secant_upper (s := Set.Ici 0) hφ hp0 hx0 hpq hqx
  have hdq : 0 < 3 * a / 4 - a / 2 := by nlinarith [h0a]
  have hslAbs : |(φ (3 * a / 4) - φ (a / 2)) / (3 * a / 4 - a / 2)| ≤
      2 * W / (3 * a / 4 - a / 2) := by
    rw [abs_div]
    have hden : |3 * a / 4 - a / 2| = 3 * a / 4 - a / 2 := abs_of_pos hdq
    rw [hden]
    have hbnd1lo : -W ≤ φ (a / 2) := (abs_le.mp hbnd1).1
    have hbnd1hi : φ (a / 2) ≤ W := (abs_le.mp hbnd1).2
    have hbnd2lo : -W ≤ φ (3 * a / 4) := (abs_le.mp hbnd2).1
    have hbnd2hi : φ (3 * a / 4) ≤ W := (abs_le.mp hbnd2).2
    have hnum : |φ (3 * a / 4) - φ (a / 2)| ≤ 2 * W := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    exact div_le_div_of_nonneg_right hnum hdq.le
  have hxq : 0 ≤ x - 3 * a / 4 := by linarith
  have hxqb : x - 3 * a / 4 ≤ b - 3 * a / 4 := by linarith
  have hW2 : 0 ≤ 2 * W / (3 * a / 4 - a / 2) := by positivity
  calc
    φ x ≤ φ (3 * a / 4) + (x - 3 * a / 4) * ((φ (3 * a / 4) - φ (a / 2)) / (3 * a / 4 - a / 2)) := by
      linarith [hsec]
    _ ≤ W + (x - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) := by
      have h1 := mul_le_mul_of_nonneg_left
        (le_trans (le_abs_self ((φ (3*a/4) - φ (a/2)) / (3*a/4 - a/2))) hslAbs) hxq
      have hφqW : φ (3 * a / 4) ≤ W := (abs_le.mp hbnd2).2
      linarith
    _ ≤ W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) := by
      have h2 := mul_le_mul_of_nonneg_right hxqb hW2
      linarith

/-- A concave function on `[0,∞)` bounded by `W` at `a/2` and `b+1` is bounded below
by `-W` on `[a,b]`. -/
lemma concaveOn_lower_Icc {φ : ℝ → ℝ} {a b W : ℝ}
    (h0a : 0 < a) (hab : a ≤ b) (hW : 0 ≤ W)
    (hφ : ConcaveOn ℝ (Set.Ici (0 : ℝ)) φ)
    (hbnd1 : |φ (a / 2)| ≤ W) (hbnd3 : |φ (b + 1)| ≤ W) :
    ∀ x : ℝ, x ∈ Set.Icc a b → -W ≤ φ x := by
  intro x hx
  have hx1 : a ≤ x := hx.1
  have hx2 : x ≤ b := hx.2
  have hpa : a / 2 < a := by nlinarith [h0a]
  have hpx : a / 2 < x := lt_of_lt_of_le hpa hx1
  have hxd : x < b + 1 := by linarith
  have hp0 : 0 ≤ a / 2 := by positivity
  have hd0 : 0 ≤ b + 1 := by nlinarith
  have hden0 : 0 < b + 1 - a / 2 := by nlinarith
  have hden : b + 1 - a / 2 ≠ 0 := ne_of_gt hden0
  have hch := concaveOn_chord_lower (s := Set.Ici 0) hφ hp0 hd0 hpx hxd
  let w1 : ℝ := (b + 1 - x) / (b + 1 - a / 2)
  let w2 : ℝ := (x - a / 2) / (b + 1 - a / 2)
  have hw1 : 0 ≤ w1 := by
    dsimp [w1]
    exact div_nonneg (by linarith) hden0.le
  have hw2 : 0 ≤ w2 := by
    dsimp [w2]
    exact div_nonneg (by linarith) hden0.le
  have hsum : w1 + w2 = 1 := by
    dsimp [w1, w2]
    rw [← add_div]
    have hnum : (b + 1 - x) + (x - a / 2) = b + 1 - a / 2 := by ring
    rw [hnum]
    exact div_self hden
  have hb1 : -W ≤ φ (a / 2) := (abs_le.mp hbnd1).1
  have hb3 : -W ≤ φ (b + 1) := (abs_le.mp hbnd3).1
  have hw1' : w1 * (-W) ≤ w1 * φ (a / 2) := by
    exact mul_le_mul_of_nonneg_left hb1 hw1
  have hw2' : w2 * (-W) ≤ w2 * φ (b + 1) := by
    exact mul_le_mul_of_nonneg_left hb3 hw2
  have hlb : -W ≤ w1 * φ (a / 2) + w2 * φ (b + 1) := by
    calc
      -W = w1 * (-W) + w2 * (-W) := by
        rw [← add_mul, hsum, one_mul]
      _ ≤ w1 * φ (a / 2) + w2 * φ (b + 1) := by nlinarith [hw1', hw2']
  have hch' : w1 * φ (a / 2) + w2 * φ (b + 1) ≤ φ x := by
    simpa [w1, w2, add_comm, add_left_comm, add_assoc] using hch
  linarith

/-- Common Lipschitz constant produced from the two-sided bound `W` at the reference points. -/
noncomputable def concaveLipschitzConst (a b W : ℝ) : ℝ :=
  let U : ℝ := W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2))
  (U + W) / (a - a / 2) + (U + W) / ((b + 1) - b)

/-- A concave function on `[0,∞)`, bounded by `W` at the reference points `a/2`, `3a/4`, `b+1`,
is Lipschitz on `[a,b]` with constant `concaveLipschitzConst a b W`. -/
lemma concaveOn_lipschitzOn_Icc {φ : ℝ → ℝ} {a b W : ℝ}
    (h0a : 0 < a) (hab : a ≤ b) (hW : 0 ≤ W)
    (hφ : ConcaveOn ℝ (Set.Ici (0 : ℝ)) φ)
    (hbnd1 : |φ (a / 2)| ≤ W) (hbnd2 : |φ (3 * a / 4)| ≤ W)
    (hbnd3 : |φ (b + 1)| ≤ W) :
    ∀ x y : ℝ, x ∈ Set.Icc a b → y ∈ Set.Icc a b →
      |φ x - φ y| ≤ concaveLipschitzConst a b W * |x - y| := by
  intro x y hx hy
  let p : ℝ := a / 2
  let q : ℝ := 3 * a / 4
  let D : ℝ := b + 1
  let U : ℝ := W + (b - q) * (2 * W / (q - p))
  let K : ℝ := (U + W) / (a - p) + (U + W) / (D - b)
  have hKeq : concaveLipschitzConst a b W = K := by
    dsimp [concaveLipschitzConst, K, U, p, q, D]
  -- basic geometry
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hpa : p < a := by dsimp [p]; nlinarith [h0a]
  have hqa : q < a := by dsimp [q]; nlinarith [h0a]
  have hpq : p < q := by dsimp [p, q]; nlinarith [h0a]
  have hbD : b < D := by dsimp [D]; linarith
  have hDpos : 0 < D := by dsimp [D]; nlinarith
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hbq : 0 ≤ b - q := by dsimp [q]; nlinarith [h0a]
  have hqp : 0 < q - p := by dsimp [p, q]; nlinarith [h0a]
  have hpa' : 0 < a - p := by dsimp [p]; nlinarith [h0a]
  have hDb : 0 < D - b := by dsimp [D]; linarith
  have hD0 : 0 ≤ D := hDpos.le
  have hUpW0 : 0 ≤ U + W := by
    have hU0 : 0 ≤ U := by
      dsimp [U]
      have h1 : 0 ≤ (b - q) * (2 * W / (q - p)) := by positivity
      nlinarith
    linarith
  have hU : ∀ z : ℝ, z ∈ Set.Icc a b → φ z ≤ U := by
    intro z hz
    have hz' := concaveOn_upper_Icc h0a hab hW hφ hbnd1 hbnd2 z hz
    simpa [U, p, q] using hz'
  have hL : ∀ z : ℝ, z ∈ Set.Icc a b → -W ≤ φ z := by
    exact concaveOn_lower_Icc h0a hab hW hφ hbnd1 hbnd3
  have hbnd1lo : -W ≤ φ p := by
    dsimp [p]
    exact (abs_le.mp hbnd1).1
  have hbnd3lo : -W ≤ φ D := by
    dsimp [D]
    exact (abs_le.mp hbnd3).1
  -- slope estimate for ordered pairs `u < v`
  have hslope : ∀ (u v : ℝ), u ∈ Set.Icc a b → v ∈ Set.Icc a b → u < v →
      |φ u - φ v| ≤ K * (v - u) := by
    intro u v hu hv huv
    have hu1 : a ≤ u := hu.1
    have hu2 : u ≤ b := hu.2
    have hv1 : a ≤ v := hv.1
    have hv2 : v ≤ b := hv.2
    have hpu : p < u := lt_of_lt_of_le hpa hu1
    have hvD : v < D := lt_of_le_of_lt hv2 hbD
    have hpos1 : 0 < v - u := sub_pos.mpr huv
    have hu0 : 0 ≤ u := le_trans (by positivity : 0 ≤ a) hu1
    have hv0 : 0 ≤ v := le_trans hu0 huv.le
    have hDv : 0 < D - v := by linarith
    have hup : 0 < u - p := by dsimp [p]; nlinarith [h0a, hu1]
    have hUu : φ u ≤ U := hU u hu
    have hUpv : φ v ≤ U := hU v hv
    have hLu : -W ≤ φ u := hL u hu
    -- upper bound on the left-hand slope
    have hsa := hφ.slope_anti_adjacent (s := Set.Ici 0) hp0 hv0 hpu huv
    -- hsa : (φ v - φ u)/(v-u) ≤ (φ u - φ p)/(u-p)
    have hdiv1 : (φ u - φ p) / (u - p) ≤ (U + W) / (a - p) := by
      rw [div_le_div_iff₀ hup hpa']
      calc
        (φ u - φ p) * (a - p) ≤ (U + W) * (a - p) := by
          exact mul_le_mul_of_nonneg_right (by linarith [hUu, hbnd1lo]) hpa'.le
        _ ≤ (U + W) * (u - p) := by
          have hxle : a - p ≤ u - p := by dsimp [p]; linarith [hu1]
          exact mul_le_mul_of_nonneg_left hxle hUpW0
    have h1m : φ v - φ u ≤ (v - u) * ((φ u - φ p) / (u - p)) := by
      calc
        φ v - φ u = ((φ v - φ u) / (v - u)) * (v - u) := by field_simp [hpos1.ne']
        _ ≤ ((φ u - φ p) / (u - p)) * (v - u) := mul_le_mul_of_nonneg_right hsa hpos1.le
        _ = (v - u) * ((φ u - φ p) / (u - p)) := by ring
    have h1m' : φ v - φ u ≤ (v - u) * ((U + W) / (a - p)) := by
      exact le_trans h1m (mul_le_mul_of_nonneg_left hdiv1 hpos1.le)
    -- lower bound on the right-hand slope
    have hsb := hφ.slope_anti_adjacent (s := Set.Ici 0) hu0 hD0 huv hvD
    -- hsb : (φ D - φ v)/(D-v) ≤ (φ v - φ u)/(v-u)
    have hdiv2 : (φ v - φ D) / (D - v) ≤ (U + W) / (D - b) := by
      rw [div_le_div_iff₀ hDv hDb]
      calc
        (φ v - φ D) * (D - b) ≤ (U + W) * (D - b) := by
          exact mul_le_mul_of_nonneg_right (by linarith [hUpv, hbnd3lo]) hDb.le
        _ ≤ (U + W) * (D - v) := by
          have hxle : D - b ≤ D - v := by linarith [hv2]
          exact mul_le_mul_of_nonneg_left hxle hUpW0
    have hmul' : (v - u) * ((φ D - φ v) / (D - v)) ≤ φ v - φ u := by
      calc
        (v - u) * ((φ D - φ v) / (D - v)) = ((φ D - φ v) / (D - v)) * (v - u) := by ring
        _ ≤ ((φ v - φ u) / (v - u)) * (v - u) := mul_le_mul_of_nonneg_right hsb hpos1.le
        _ = φ v - φ u := by field_simp [hpos1.ne']
    have hneg : φ u - φ v ≤ -(v - u) * ((φ D - φ v) / (D - v)) := by
      linarith [hmul']
    have hcalc : -(v - u) * ((φ D - φ v) / (D - v)) = (v - u) * ((φ v - φ D) / (D - v)) := by
      field_simp [hDv.ne']
      ring
    have h2m : φ u - φ v ≤ (v - u) * ((U + W) / (D - b)) := by
      rw [hcalc] at hneg
      exact le_trans hneg (mul_le_mul_of_nonneg_left hdiv2 hpos1.le)
    -- combine
    have hK1 : (U + W) / (a - p) ≤ K := by
      dsimp [K]
      have hz : 0 ≤ (U + W) / (D - b) := div_nonneg hUpW0 hDb.le
      linarith
    have hK2 : (U + W) / (D - b) ≤ K := by
      dsimp [K]
      have hz : 0 ≤ (U + W) / (a - p) := div_nonneg hUpW0 hpa'.le
      linarith
    have hA : φ u - φ v ≤ K * (v - u) := le_trans h2m (by
      calc
        (v - u) * ((U + W) / (D - b)) ≤ (v - u) * K := mul_le_mul_of_nonneg_left hK2 hpos1.le
        _ = K * (v - u) := by ring)
    have hB : φ v - φ u ≤ K * (v - u) := le_trans h1m' (by
      calc
        (v - u) * ((U + W) / (a - p)) ≤ (v - u) * K := mul_le_mul_of_nonneg_left hK1 hpos1.le
        _ = K * (v - u) := by ring)
    rw [abs_sub_le_iff]
    exact ⟨hA, hB⟩
  -- turn the RHS constant into `K`
  rw [hKeq]
  -- case split on the order of `x` and `y`
  rcases le_total x y with hxy | hyx
  · rcases eq_or_lt_of_le hxy with rfl | hlt
    · simp
    · have hh := hslope x y hx hy hlt
      calc
        |φ x - φ y| ≤ K * (y - x) := hh
        _ = K * |x - y| := by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hlt.le)]
  · rcases eq_or_lt_of_le hyx with rfl | hlt
    · simp
    · have hh := hslope y x hy hx hlt
      calc
        |φ x - φ y| = |φ y - φ x| := abs_sub_comm _ _
        _ ≤ K * (x - y) := hh
        _ = K * |x - y| := by rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)]

/-- Triangle inequality for absolute values on the reals. -/
lemma abs_sub_le_triangle {a b c : ℝ} : |a - c| ≤ |a - b| + |b - c| := by
  calc
    |a - c| = |(a - b) + (b - c)| := by congr 1; ring
    _ ≤ |a - b| + |b - c| := abs_add_le _ _

lemma exists_nat_within_one (x : ℝ) (hx : 0 ≤ x) :
    ∃ N : ℕ, (N : ℝ) ≤ x ∧ x < (N : ℝ) + 1 := by
  let z : ℤ := Int.floor x
  have hz0 : 0 ≤ z := Int.floor_nonneg.mpr hx
  have hztoNat : (z.toNat : ℝ) = (z : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hz0)
  refine ⟨z.toNat, ?_, ?_⟩
  · calc
      (z.toNat : ℝ) = (z : ℝ) := hztoNat
      _ ≤ x := Int.floor_le x
  · calc
      x < (z : ℝ) + 1 := Int.lt_floor_add_one x
      _ = (z.toNat : ℝ) + 1 := by rw [hztoNat]
lemma exists_index_near_Icc {a b : ℝ} (hab : a < b) (N : ℕ) (hN : 0 < N) :
    ∀ x : ℝ, x ∈ Set.Icc a b →
      ∃ i : ℕ, i < N ∧ |x - (a + (b - a) * (i : ℝ) / N)| ≤ (b - a) / N := by
  intro x hx
  have hx1 : a ≤ x := hx.1
  have hx2 : x ≤ b := hx.2
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hh : 0 < (b - a) / N := by positivity
  have hba : 0 < b - a := by linarith
  have ht : ∀ i : ℕ, (b - a) * (i : ℝ) / N = ((b - a) / N) * (i : ℝ) := by
    intro i
    field_simp [hNpos.ne']
  have hstep : ∀ i : ℕ,
      (b - a) * ((i : ℝ) + 1) / N = (b - a) * (i : ℝ) / N + (b - a) / N := by
    intro i
    field_simp [hNpos.ne']
  rcases lt_or_eq_of_le hx2 with hxb | hxb
  · have hu0 : 0 ≤ (x - a) / ((b - a) / N) := by positivity
    obtain ⟨i, hi1, hi2⟩ := exists_nat_within_one ((x - a) / ((b - a) / N)) hu0
    have hltN : (x - a) / ((b - a) / N) < (N : ℝ) := by
      rw [div_lt_iff₀ hh]
      calc
        x - a < b - a := by linarith
        _ = (N : ℝ) * ((b - a) / N) := by field_simp [hNpos.ne']
    have hiN : i < N := by
      exact_mod_cast (lt_of_le_of_lt hi1 hltN)
    refine ⟨i, hiN, ?_⟩
    have hlo : (b - a) * (i : ℝ) / N ≤ x - a := by
      have hm := mul_le_mul_of_nonneg_right hi1 hh.le
      calc
        (b - a) * (i : ℝ) / N = ((b - a) / N) * (i : ℝ) := ht i
        _ ≤ x - a := by
          have hcancel : ((x - a) / ((b - a) / N)) * ((b - a) / N) = x - a := by
            field_simp [hh.ne', hba.ne']
          simpa [hcancel, mul_comm] using hm
    have hhi : x - a ≤ (b - a) * ((i : ℝ) + 1) / N := by
      have hm := mul_le_mul_of_nonneg_right (le_of_lt hi2) hh.le
      calc
        x - a = ((x - a) / ((b - a) / N)) * ((b - a) / N) := by
          field_simp [hh.ne', hba.ne']
        _ ≤ ((i : ℝ) + 1) * ((b - a) / N) := hm
        _ = (b - a) * ((i : ℝ) + 1) / N := by
          rw [mul_comm]
          field_simp [hNpos.ne']
    have hdist_lo : 0 ≤ x - (a + (b - a) * (i : ℝ) / N) := by linarith
    have hdist_hi : x - (a + (b - a) * (i : ℝ) / N) ≤ (b - a) / N := by
      have htmp : (b - a) * ((i : ℝ) + 1) / N = (b - a) * (i : ℝ) / N + (b - a) / N := hstep i
      linarith
    rw [abs_of_nonneg hdist_lo]
    exact hdist_hi
  · -- x = b
    have hN1 : (1 : ℕ) ≤ N := Nat.succ_le_of_lt hN
    have hiN : N - 1 < N := Nat.sub_lt hN (by norm_num : (0 : ℕ) < 1)
    refine ⟨N - 1, hiN, ?_⟩
    rw [hxb]
    have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      simpa [Nat.cast_sub hN1]
    rw [hcast]
    have hc : (b - a) * ((N : ℝ) - 1) / N = (b - a) - (b - a) / N := by
      field_simp [hNpos.ne']
    rw [hc]
    have hinner : b - (a + ((b - a) - (b - a) / N)) = (b - a) / N := by ring
    rw [hinner]
    rw [abs_of_nonneg hh.le]
lemma uniformOn_Icc_of_equiLipschitz {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {a b K : ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K)
    (hLipF : ∀ᶠ n in atTop, ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |F n x - F n y| ≤ K * |x - y|)
    (hLipG : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |G x - G y| ≤ K * |x - y|)
    (hpt : ∀ x ∈ Set.Icc a b, Tendsto (fun n : ℕ => F n x) atTop (𝓝 (G x))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ Set.Icc a b, |F n x - G x| < ε := by
  intro ε hε
  rcases eq_or_lt_of_le hab with rfl | hab'
  · -- a = b
    have hev : ∀ᶠ n in atTop, |F n a - G a| < ε := by
      have hA := hpt a (by simp)
      rw [Metric.tendsto_atTop] at hA
      rcases hA ε hε with ⟨N, hN⟩
      filter_upwards [eventually_ge_atTop N] with n hn
      simpa [Real.dist_eq] using hN n hn
    filter_upwards [hev] with n hn
    intro x hx
    have hxeq : x = a := by
      linarith [hx.1, hx.2]
    simpa [hxeq] using hn
  · -- a < b
    let η : ℝ := ε / 2
    let ρ : ℝ := (ε - η) / (2 * (K + 1))
    have hη : 0 < η := by dsimp [η]; positivity
    have hηε : ε - η > 0 := by dsimp [η]; linarith
    have hKp : 0 < K + 1 := by linarith
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    obtain ⟨N, hNbig⟩ := exists_nat_gt ((b - a) / ρ)
    have hNpos : 0 < N := by
      have hpos0 : 0 < (b - a) / ρ := by positivity
      exact_mod_cast (lt_trans hpos0 hNbig)
    have hNℝ : 0 < (N : ℝ) := by exact_mod_cast hNpos
    have hhρ : (b - a) / N < ρ := by
      rw [div_lt_iff₀ hNℝ]
      have hm := (div_lt_iff₀ hρ).mp hNbig
      nlinarith
    let t : ℕ → ℝ := fun i => a + (b - a) * (i : ℝ) / N
    have htmem : ∀ i : ℕ, i ≤ N → t i ∈ Set.Icc a b := by
      intro i hi
      have hiN : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
      have hbam : 0 ≤ b - a := by linarith
      constructor
      · have hn0 : 0 ≤ (b - a) * (i : ℝ) / N := by positivity
        dsimp [t]
        linarith
      · have hc : (b - a) * (i : ℝ) / N ≤ b - a := by
          calc
            (b - a) * (i : ℝ) / N ≤ (b - a) * (N : ℝ) / N := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hiN hbam) hNℝ.le
            _ = b - a := by field_simp [hNℝ.ne']
        dsimp [t]
        linarith
    -- pointwise bounds at all mesh points, eventually
    have hmeshEv : ∀ᶠ n in atTop, ∀ i : ℕ, i < N →
        |F n (t i) - G (t i)| < η := by
      have hmeshEv' : ∀ᶠ n in atTop, ∀ i ∈ Finset.range N,
          |F n (t i) - G (t i)| < η := by
        refine (Filter.eventually_all_finset (Finset.range N)).mpr ?_
        intro i hi
        have hm : t i ∈ Set.Icc a b := htmem i (le_of_lt (Finset.mem_range.mp hi))
        have hA := hpt (t i) hm
        rw [Metric.tendsto_atTop] at hA
        rcases hA η hη with ⟨M, hM⟩
        filter_upwards [eventually_ge_atTop M] with n hn
        simpa [Real.dist_eq] using hM n hn
      simpa [Finset.mem_range] using hmeshEv'
    filter_upwards [hLipF, hmeshEv] with n hLipN hmeshN
    intro x hx
    obtain ⟨i, hiN, hidist⟩ := exists_index_near_Icc hab' N hNpos x hx
    have hmemb : t i ∈ Set.Icc a b := htmem i (le_of_lt hiN)
    have hF1 : |F n x - F n (t i)| ≤ K * ((b - a) / N) := by
      have h1 := hLipN x hx (t i) hmemb
      calc
        |F n x - F n (t i)| ≤ K * |x - t i| := h1
        _ ≤ K * ((b - a) / N) := by
          have hm := mul_le_mul_of_nonneg_left (by simpa [t] using hidist) hK
          simpa [mul_comm] using hm
    have hG1 : |G (t i) - G x| ≤ K * ((b - a) / N) := by
      have h1 := hLipG (t i) hmemb x hx
      calc
        |G (t i) - G x| ≤ K * |t i - x| := h1
        _ ≤ K * ((b - a) / N) := by
          have hh1 : |x - t i| ≤ (b - a) / N := by simpa [t] using hidist
          have hh2 : |t i - x| ≤ (b - a) / N := by
            simpa [abs_sub_comm] using hh1
          have hm := mul_le_mul_of_nonneg_left hh2 hK
          simpa [mul_comm] using hm
    have hmid : |F n (t i) - G (t i)| < η := hmeshN i hiN
    have htri : |F n x - G x| ≤ K * ((b - a) / N) + η + K * ((b - a) / N) := by
      have hB : |F n x - G (t i)| ≤ |F n x - F n (t i)| + |F n (t i) - G (t i)| :=
        abs_sub_le_triangle (a := F n x) (b := F n (t i)) (c := G (t i))
      calc
        |F n x - G x| ≤ |F n x - G (t i)| + |G (t i) - G x| :=
          abs_sub_le_triangle (a := F n x) (b := G (t i)) (c := G x)
        _ ≤ (|F n x - F n (t i)| + |F n (t i) - G (t i)|) + |G (t i) - G x| := by
          have hh := add_le_add_right hB (|G (t i) - G x|)
          simpa [add_comm, add_assoc, add_left_comm] using hh
        _ ≤ K * ((b - a) / N) + η + K * ((b - a) / N) := by
          exact add_le_add (add_le_add hF1 (le_of_lt hmid)) hG1
    have hKh : K * ((b - a) / N) ≤ (K + 1) * ((b - a) / N) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity : 0 ≤ (b - a) / N)
    have hsmall : (2 * (K + 1)) * ((b - a) / N) < ε - η := by
      have hmul := mul_lt_mul_of_pos_left hhρ (by positivity : 0 < 2 * (K + 1))
      have hρeq : (2 * (K + 1)) * ρ = ε - η := by
        dsimp [ρ, η]
        field_simp
      linarith
    have hfinal : K * ((b - a) / N) + η + K * ((b - a) / N) < ε := by
      have hA : K * ((b - a) / N) + η + K * ((b - a) / N) ≤
          (2 * (K + 1)) * ((b - a) / N) + η := by nlinarith [hKh, hK]
      have hB : (2 * (K + 1)) * ((b - a) / N) + η < ε := by linarith [hsmall]
      linarith
    exact lt_of_le_of_lt htri hfinal
/-- Pointwise convergent concave functions on `[0,∞)` converge uniformly on
`[a,b]` in the interior (`0 < a ≤ b`): for every `ε > 0`, eventually in `n`
every value on the interval is within `ε` of the limit. -/
lemma concaveOn_uniformOn_Icc {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {a b : ℝ}
    (h0a : 0 < a) (hab : a ≤ b)
    (hf : ∀ n : ℕ, ConcaveOn ℝ (Set.Ici (0 : ℝ)) (f n))
    (hg : ConcaveOn ℝ (Set.Ici (0 : ℝ)) g)
    (hpt : ∀ x : ℝ, 0 ≤ x → Tendsto (fun n : ℕ => f n x) atTop (𝓝 (g x))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x : ℝ, x ∈ Set.Icc a b → |f n x - g x| < ε := by
  intro ε hε
  let W : ℝ := |g (a / 2)| + |g (3 * a / 4)| + |g (b + 1)| + 1
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity
  have hg1 : |g (a / 2)| ≤ W := by
    dsimp [W]
    nlinarith [abs_nonneg (g (3 * a / 4)), abs_nonneg (g (b + 1))]
  have hg2 : |g (3 * a / 4)| ≤ W := by
    dsimp [W]
    nlinarith [abs_nonneg (g (a / 2)), abs_nonneg (g (b + 1))]
  have hg3 : |g (b + 1)| ≤ W := by
    dsimp [W]
    nlinarith [abs_nonneg (g (a / 2)), abs_nonneg (g (3 * a / 4))]
  -- `f n` satisfies the same reference bounds eventually
  have hfEv : ∀ᶠ n in atTop,
      |f n (a / 2)| ≤ W ∧ |f n (3 * a / 4)| ≤ W ∧ |f n (b + 1)| ≤ W := by
    have hb1 : ∀ᶠ n in atTop, |f n (a / 2)| ≤ W := by
      have hconv := hpt (a / 2) (by positivity)
      rw [Metric.tendsto_atTop] at hconv
      rcases hconv 1 (by norm_num) with ⟨M, hM⟩
      filter_upwards [eventually_ge_atTop M] with n hn
      have hd : |f n (a / 2) - g (a / 2)| < 1 := by
        simpa [Real.dist_eq] using hM n hn
      calc
        |f n (a / 2)| = |(f n (a / 2) - g (a / 2)) + g (a / 2)| := by congr 1; ring
        _ ≤ |f n (a / 2) - g (a / 2)| + |g (a / 2)| := abs_add_le _ _
        _ ≤ W := by dsimp [W]; nlinarith [abs_nonneg (g (3 * a / 4)), abs_nonneg (g (b + 1))]
    have hb2 : ∀ᶠ n in atTop, |f n (3 * a / 4)| ≤ W := by
      have hconv := hpt (3 * a / 4) (by positivity)
      rw [Metric.tendsto_atTop] at hconv
      rcases hconv 1 (by norm_num) with ⟨M, hM⟩
      filter_upwards [eventually_ge_atTop M] with n hn
      have hd : |f n (3 * a / 4) - g (3 * a / 4)| < 1 := by
        simpa [Real.dist_eq] using hM n hn
      calc
        |f n (3 * a / 4)| = |(f n (3 * a / 4) - g (3 * a / 4)) + g (3 * a / 4)| := by congr 1; ring
        _ ≤ |f n (3 * a / 4) - g (3 * a / 4)| + |g (3 * a / 4)| := abs_add_le _ _
        _ ≤ W := by dsimp [W]; nlinarith [abs_nonneg (g (a / 2)), abs_nonneg (g (b + 1))]
    have hb3 : ∀ᶠ n in atTop, |f n (b + 1)| ≤ W := by
      have hconv := hpt (b + 1) (by nlinarith)
      rw [Metric.tendsto_atTop] at hconv
      rcases hconv 1 (by norm_num) with ⟨M, hM⟩
      filter_upwards [eventually_ge_atTop M] with n hn
      have hd : |f n (b + 1) - g (b + 1)| < 1 := by
        simpa [Real.dist_eq] using hM n hn
      calc
        |f n (b + 1)| = |(f n (b + 1) - g (b + 1)) + g (b + 1)| := by congr 1; ring
        _ ≤ |f n (b + 1) - g (b + 1)| + |g (b + 1)| := abs_add_le _ _
        _ ≤ W := by dsimp [W]; nlinarith [abs_nonneg (g (a / 2)), abs_nonneg (g (3 * a / 4))]
    exact (hb1.and (hb2.and hb3))
  -- common Lipschitz constant
  let K : ℝ := concaveLipschitzConst a b W
  have hK0 : 0 ≤ K := by
    dsimp [K]
    dsimp [concaveLipschitzConst]
    have hU0 : 0 ≤ W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) := by
      have hbq0 : 0 ≤ b - 3 * a / 4 := by nlinarith [h0a]
      have hqpos : 0 < 3 * a / 4 - a / 2 := by nlinarith [h0a]
      have h1 : 0 ≤ (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) := by
        exact mul_nonneg hbq0 (div_nonneg (by nlinarith) hqpos.le)
      nlinarith
    have hd1 : 0 < a - a / 2 := by nlinarith [h0a]
    have hd2 : 0 < (b + 1) - b := by norm_num
    have ht1 : 0 ≤ (W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) + W) / (a - a / 2) := by
      exact div_nonneg (by linarith) hd1.le
    have ht2 : 0 ≤ (W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) + W) / ((b + 1) - b) := by
      exact div_nonneg (by linarith) hd2.le
    change 0 ≤ (W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) + W) / (a - a / 2) +
      (W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)) + W) / ((b + 1) - b)
    linarith
  have hgLip : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |g x - g y| ≤ K * |x - y| := by
    intro x hx y hy
    have hh := concaveOn_lipschitzOn_Icc h0a hab hW hg hg1 hg2 hg3 x y hx hy
    simpa [K] using hh
  have hfLip : ∀ᶠ n in atTop, ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |f n x - f n y| ≤ K * |x - y| := by
    filter_upwards [hfEv] with n hn
    intro x hx y hy
    have hh := concaveOn_lipschitzOn_Icc h0a hab hW (hf n) hn.1 hn.2.1 hn.2.2 x y hx hy
    simpa [K] using hh
  have hptIcc : ∀ x ∈ Set.Icc a b, Tendsto (fun n : ℕ => f n x) atTop (𝓝 (g x)) := by
    intro x hx
    exact hpt x (le_trans (by positivity : 0 ≤ a) hx.1)
  exact uniformOn_Icc_of_equiLipschitz (F := f) (G := g) hab hK0 hfLip hgLip hptIcc ε hε

/-- The sup-limsup exchange used in the Bose-gas upper bound: under the
hypotheses of `concaveOn_uniformOn_Icc` (with `0 < a`), `limsup` of the
supremum over the compact interval is at most the supremum of the limit. -/
lemma limsup_sup_le_sup_of_concaveOn {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {a b : ℝ}
    (h0a : 0 < a) (hab : a ≤ b)
    (hf : ∀ n : ℕ, ConcaveOn ℝ (Set.Ici (0 : ℝ)) (f n))
    (hg : ConcaveOn ℝ (Set.Ici (0 : ℝ)) g)
    (hpt : ∀ x : ℝ, 0 ≤ x → Tendsto (fun n : ℕ => f n x) atTop (𝓝 (g x))) :
    Filter.limsup (fun n : ℕ => sSup ((f n) '' Set.Icc a b)) atTop ≤
      sSup (g '' Set.Icc a b) := by
  let S : ℝ := sSup (g '' Set.Icc a b)
  have haIcc : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  -- g is bounded above on [a,b], so the image is bounded
  have hS_bdd : BddAbove (g '' Set.Icc a b) := by
    let W : ℝ := |g (a / 2)| + |g (3 * a / 4)|
    have hW : 0 ≤ W := by
      dsimp [W]
      positivity
    have hb1 : |g (a / 2)| ≤ W := by dsimp [W]; nlinarith [abs_nonneg (g (3 * a / 4))]
    have hb2 : |g (3 * a / 4)| ≤ W := by dsimp [W]; nlinarith [abs_nonneg (g (a / 2))]
    have hup := concaveOn_upper_Icc h0a hab hW hg hb1 hb2
    refine ⟨W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)), ?_⟩
    rintro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hup x hx
  have hS_nonempty : (g '' Set.Icc a b).Nonempty := ⟨g a, ⟨a, haIcc, rfl⟩⟩
  -- each f n is bounded above on [a,b]
  have hF_bdd : ∀ n : ℕ, BddAbove ((f n) '' Set.Icc a b) := by
    intro n
    let W : ℝ := |f n (a / 2)| + |f n (3 * a / 4)|
    have hW : 0 ≤ W := by
      dsimp [W]
      positivity
    have hb1 : |f n (a / 2)| ≤ W := by dsimp [W]; nlinarith [abs_nonneg (f n (3 * a / 4))]
    have hb2 : |f n (3 * a / 4)| ≤ W := by dsimp [W]; nlinarith [abs_nonneg (f n (a / 2))]
    have hup := concaveOn_upper_Icc h0a hab hW (hf n) hb1 hb2
    refine ⟨W + (b - 3 * a / 4) * (2 * W / (3 * a / 4 - a / 2)), ?_⟩
    rintro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hup x hx
  have hunif := concaveOn_uniformOn_Icc h0a hab hf hg hpt
  -- uniform convergence gives: eventually the sup of f n is ≤ sup g + ε
  apply le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ n in atTop, sSup ((f n) '' Set.Icc a b) ≤ S + ε := by
    filter_upwards [hunif ε hε] with n hun
    have hnon : ((f n) '' Set.Icc a b).Nonempty := ⟨f n a, ⟨a, haIcc, rfl⟩⟩
    rw [csSup_le_iff (hF_bdd n) hnon]
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h1 : |f n x - g x| < ε := hun x hx
    have h1pos : f n x - g x < ε := (abs_lt.mp h1).2
    have hgx : g x ≤ S := le_csSup hS_bdd ⟨x, hx, rfl⟩
    linarith
  have hlim : Filter.limsup (fun n : ℕ => sSup ((f n) '' Set.Icc a b)) atTop ≤ S + ε := by
    -- need coboundedness of the sequence from below
    have hCob : Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop
        (fun n => sSup ((f n) '' Set.Icc a b)) := by
      have hlow : ∀ᶠ n in atTop, g a - 1 ≤ sSup ((f n) '' Set.Icc a b) := by
        filter_upwards [hunif 1 (by norm_num)] with n hun
        have hmem : f n a ∈ (f n) '' Set.Icc a b := ⟨a, haIcc, rfl⟩
        have hle := le_csSup (hF_bdd n) hmem
        have h1 : |f n a - g a| < 1 := hun a haIcc
        have h1lo : -1 < f n a - g a := (abs_lt.mp h1).1
        linarith
      refine ⟨g a - 1, ?_⟩
      intro x hxu
      have hboth : ∀ᶠ n in atTop, g a - 1 ≤ sSup ((f n) '' Set.Icc a b) ∧
          sSup ((f n) '' Set.Icc a b) ≤ x := hlow.and hxu
      have hxlow : ∀ᶠ n in atTop, g a - 1 ≤ x :=
        hboth.mono (fun n hn => le_trans hn.1 hn.2)
      exact hxlow.exists.choose_spec
    exact Filter.limsup_le_of_le hCob hev
  dsimp [S] at hlim
  linarith

end Submission
