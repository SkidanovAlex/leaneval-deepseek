import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levMulGe
import Submission.Work.Mostow.minkGeoSeg
import Submission.Work.Mostow.minkAxisCompute
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.ematFix
import Submission.Work.Mostow.perpNullUnit

namespace Work.Mostow.gapA

set_option maxHeartbeats 1000000

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Parameters of the pair `(a, b)` of distinct boundary points -/

/-- `L = (1 - ⟪a,b⟫)/2`, the level of the geodesic joining `a` and `b`. -/
def gcL (a b : E n) : ℝ := (1 - inner ℝ a b) / 2

/-- The normalising constant `κ = (2(1-⟪a,b⟫))^{-1/2} = 1/(2√L)` of the geodesic. -/
def gcK (a b : E n) : ℝ := (Real.sqrt (2 * (1 - inner ℝ a b)))⁻¹

/-- The coefficient of `nvec a` in the decomposition of `hlift u`. -/
def gcA (a b u : E n) : ℝ := lev b u / (2 * gcL a b)

/-- The coefficient of `nvec b` in the decomposition of `hlift u`. -/
def gcB (a b u : E n) : ℝ := lev a u / (2 * gcL a b)

/-- The normal component of `hlift u` with respect to the plane spanned by the two null
vectors `nvec a`, `nvec b`. -/
def gcN (a b u : E n) : Fin n ⊕ Fin 1 → ℝ :=
  hlift u - gcA a b u • nvec a - gcB a b u • nvec b

/-- The point of the geodesic joining `a` and `b` at geodesic parameter `s`, as a Minkowski
vector. -/
def gcAxis (a b : E n) (s : ℝ) : Fin n ⊕ Fin 1 → ℝ :=
  gcK a b • (Real.exp s • nvec a + Real.exp (-s) • nvec b)

/-- The chart point of the geodesic joining `a` and `b` at parameter `s`. -/
def gcAxisPt (a b : E n) (s : ℝ) : E n :=
  WithLp.toLp 2 (fun i : Fin n => gcAxis a b s (Sum.inl i))

/-- The foot of the perpendicular from `u` to the geodesic joining `a` and `b`, as a Minkowski
vector. -/
def gcFoot (a b u : E n) : Fin n ⊕ Fin 1 → ℝ :=
  gcK a b • ((Real.sqrt (lev b u) / Real.sqrt (lev a u)) • nvec a
    + (Real.sqrt (lev a u) / Real.sqrt (lev b u)) • nvec b)

/-- The foot of the perpendicular from `u` to the geodesic joining `a` and `b`. -/
def gcFootPt (a b u : E n) : E n :=
  WithLp.toLp 2 (fun i : Fin n => gcFoot a b u (Sum.inl i))

/-! ## Elementary facts about the Minkowski form and boundary null vectors -/

lemma mink_nvec_nvec' (ξ η : E n) : mink (nvec ξ) (nvec η) = inner ℝ ξ η - 1 := by
  simp only [mink, nvec, Sum.elim_inl, Sum.elim_inr]
  rw [show (∑ i : Fin n, ξ i * η i) = inner ℝ ξ η from (Hyper.inner_eq_sum ξ η).symm]
  ring

lemma mink_nvec_self' {ξ : E n} (hξ : ξ ∈ Sph n) : mink (nvec ξ) (nvec ξ) = 0 := by
  rw [mink_nvec_nvec', real_inner_self_eq_norm_sq, (mem_Sph_iff ξ).mp hξ]; norm_num

/-- `lev ξ u = - mink (nvec ξ) (hlift u)`. -/
lemma lev_eq_neg_mink (ξ u : E n) : lev ξ u = - mink (nvec ξ) (hlift u) := by
  rw [mink_nvec_hlift]; ring

lemma mink_hlift_hlift (u v : E n) :
    mink (hlift u) (hlift v) = inner ℝ u v - tpart u * tpart v := by
  rw [mink_eq_mform]; exact mform_hlift_hlift u v

lemma one_le_tpart_mul (u v : E n) : 1 ≤ tpart u * tpart v - inner ℝ u v := by
  have h1 : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
  have h2 : 1 + ‖u‖ * ‖v‖ ≤ tpart u * tpart v := by
    have ha : tpart u * tpart v = Real.sqrt ((1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2)) := by
      rw [tpart, tpart, Real.sqrt_mul (by positivity)]
    rw [ha]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  linarith

lemma cosh_hdist' (u v : E n) : Real.cosh (hdist u v) = tpart u * tpart v - inner ℝ u v := by
  rw [hdist]; exact Real.cosh_arcosh (one_le_tpart_mul u v)

lemma hdist_nonneg' (u v : E n) : 0 ≤ hdist u v := by
  rw [hdist]; exact Real.arcosh_nonneg (one_le_tpart_mul u v)

lemma mink_hlift_neg_cosh' (u v : E n) :
    mink (hlift u) (hlift v) = -Real.cosh (hdist u v) := by
  rw [mink_hlift_hlift]; have h := cosh_hdist' u v; rw [h]; ring

lemma arcosh_cosh_abs' (x : ℝ) : Real.arcosh (Real.cosh x) = |x| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; exact Real.arcosh_cosh h
  · rw [abs_of_nonpos h, ← Real.cosh_neg x]; exact Real.arcosh_cosh (by linarith)

lemma exp_sub_add_exp' (s t : ℝ) :
    Real.exp (s - t) + Real.exp (t - s) = 2 * Real.cosh (s - t) := by
  rw [Real.cosh_eq]; ring

/-! ## Bilinearity helpers for `mink` -/

lemma mink_neg_left' (x y : Fin n ⊕ Fin 1 → ℝ) : mink (-x) y = - mink x y := by
  have h := minkSeg_smul (n := n) (-1) (1 : ℝ) x y
  simpa using h

lemma mink_zero_left (y : Fin n ⊕ Fin 1 → ℝ) : mink (0 : Fin n ⊕ Fin 1 → ℝ) y = 0 := by
  simp [mink]

lemma mink_sub_left' (x y z : Fin n ⊕ Fin 1 → ℝ) : mink (x - y) z = mink x z - mink y z := by
  rw [sub_eq_add_neg, minkSeg_add_left, mink_neg_left']; ring

lemma mink_sub_right' (x y z : Fin n ⊕ Fin 1 → ℝ) : mink x (y - z) = mink x y - mink x z := by
  rw [sub_eq_add_neg, minkSeg_add_right]
  have h : mink x (-z) = - mink x z := by
    rw [minkSeg_comm x (-z), mink_neg_left', minkSeg_comm]
  rw [h]; ring

lemma mink_smul_left'' (r : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) : mink (r • x) y = r * mink x y :=
  mink_smul_left n r x y

lemma mink_smul_right'' (x : Fin n ⊕ Fin 1 → ℝ) (r : ℝ) (y : Fin n ⊕ Fin 1 → ℝ) :
    mink x (r • y) = r * mink x y := by
  have h := minkSeg_smul (n := n) 1 r x y
  simpa using h

/-- Expansion of `mink` on a pair of two-term combinations. -/
lemma mink_expand (U X Y : Fin n ⊕ Fin 1 → ℝ) (α β α' β' : ℝ) :
    mink (U - α • X - β • Y) (U - α' • X - β' • Y)
      = mink U U - α' * mink U X - β' * mink U Y
        - α * mink X U + α * α' * mink X X + α * β' * mink X Y
        - β * mink Y U + β * α' * mink Y X + β * β' * mink Y Y := by
  simp only [mink_sub_left', mink_sub_right', mink_smul_left'', mink_smul_right'']
  ring_nf

/-- Expansion of `mink` on a two-term combination and a vector. -/
lemma mink_expand_l (U X Y Z : Fin n ⊕ Fin 1 → ℝ) (α β : ℝ) :
    mink (U - α • X - β • Y) Z = mink U Z - α * mink X Z - β * mink Y Z := by
  simp only [mink_sub_left', mink_smul_left'']

/-- Expansion of `mink` on two linear combinations of a pair. -/
lemma mink_expand2 (U Z : Fin n ⊕ Fin 1 → ℝ) (A B C D : ℝ) :
    mink (A • U + B • Z) (C • U + D • Z)
      = A * C * mink U U + A * D * mink U Z + B * C * mink Z U + B * D * mink Z Z := by
  simp only [minkSeg_add_left, minkSeg_add_right, minkSeg_smul]
  ring

/-- If `mink N (hlift p) = 0` and `mink N N = 0` then `N = 0`. -/
lemma mink_eq_zero_of_orth_of_self_zero (p : E n) (N : Fin n ⊕ Fin 1 → ℝ)
    (horth : mink N (hlift p) = 0) (hself : mink N N = 0) : N = 0 := by
  have h1 : (∑ i : Fin n, N (Sum.inl i) * p i) = N (Sum.inr 0) * tpart p := by
    have h := horth
    simp only [mink, hlift, Sum.elim_inl, Sum.elim_inr] at h
    linarith
  have h2 : (∑ i : Fin n, N (Sum.inl i) * N (Sum.inl i)) = N (Sum.inr 0) * N (Sum.inr 0) := by
    have h := hself
    simp only [mink] at h
    linarith
  set nsp : E n := WithLp.toLp 2 (fun i : Fin n => N (Sum.inl i)) with hnsp
  have hnspapp : ∀ i, nsp i = N (Sum.inl i) := fun i => rfl
  have hinner : inner ℝ nsp p = N (Sum.inr 0) * tpart p := by
    rw [Hyper.inner_eq_sum]
    rw [show (∑ i, nsp i * p i) = (∑ i, N (Sum.inl i) * p i) from
      Finset.sum_congr rfl fun i _ => by rw [hnspapp i]]
    exact h1
  have hnorm : ‖nsp‖ ^ 2 = N (Sum.inr 0) * N (Sum.inr 0) := by
    rw [Hyper.norm_sq_eq_sum]
    rw [show (∑ i, nsp i * nsp i) = (∑ i, N (Sum.inl i) * N (Sum.inl i)) from
      Finset.sum_congr rfl fun i _ => by rw [hnspapp i]]
    exact h2
  have hcs : (inner ℝ nsp p) ^ 2 ≤ ‖nsp‖ ^ 2 * ‖p‖ ^ 2 := by
    have h := real_inner_mul_inner_self_le nsp p
    rw [show inner ℝ nsp p * inner ℝ nsp p = (inner ℝ nsp p) ^ 2 from by ring,
      real_inner_self_eq_norm_sq nsp, real_inner_self_eq_norm_sq p] at h
    exact h
  rw [hinner, hnorm] at hcs
  have htpar : tpart p ^ 2 = 1 + ‖p‖ ^ 2 := tpart_sq p
  have hz0 : N (Sum.inr 0) = 0 := by
    have hk : N (Sum.inr 0) ^ 2 ≤ 0 := by nlinarith [hcs, htpar]
    nlinarith [sq_nonneg (N (Sum.inr 0))]
  have hnn0 : ‖nsp‖ = 0 := by
    have h := hnorm; rw [hz0] at h; simp only [mul_zero] at h
    nlinarith [norm_nonneg nsp]
  have hzsp : nsp = 0 := norm_eq_zero.mp hnn0
  funext k
  rcases k with i | j
  · have hh := congrArg (fun x : E n => x i) hzsp
    simp only [PiLp.zero_apply] at hh
    rw [hnspapp i] at hh
    exact hh
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    exact hz0

/-- A vector with `mink Y Y = -1` and `mink (hlift w) Y < 0` lies on the upper sheet. -/
lemma upper_of_mink_neg (w : E n) (Y : Fin n ⊕ Fin 1 → ℝ)
    (hself : mink Y Y = -1) (hneg : mink (hlift w) Y < 0) : 0 < Y (Sum.inr 0) := by
  by_contra h
  push_neg at h
  set y : E n := WithLp.toLp 2 (fun i : Fin n => Y (Sum.inl i)) with hy
  have hyapp : ∀ i, y i = Y (Sum.inl i) := fun i => rfl
  have hcoord : ‖y‖ ^ 2 = Y (Sum.inr 0) * Y (Sum.inr 0) - 1 := by
    have hh := hself
    simp only [mink] at hh
    rw [Hyper.norm_sq_eq_sum]
    rw [show (∑ x, y x * y x) = (∑ x, Y (Sum.inl x) * Y (Sum.inl x)) from
      Finset.sum_congr rfl fun i _ => by rw [hyapp i]]
    linarith
  have hy0 : Y (Sum.inr 0) = -tpart y := by
    have hsq : Y (Sum.inr 0) ^ 2 = tpart y ^ 2 := by rw [tpart_sq]; linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h'
    · exfalso
      rw [h'] at h
      exact absurd h (not_le.mpr (tpart_pos y))
    · exact h'
  have hmk : mink (hlift w) Y = inner ℝ w y + tpart w * tpart y := by
    have hsum : (∑ i : Fin n, w i * Y (Sum.inl i)) = inner ℝ w y := by
      rw [Hyper.inner_eq_sum]
    simp only [mink, hlift, Sum.elim_inl, Sum.elim_inr]
    rw [hsum, hy0]; ring
  have hpos : 0 < inner ℝ w y + tpart w * tpart y := by
    have h0 : -‖w‖ * ‖y‖ ≤ inner ℝ w y := by
      have h := abs_real_inner_le_norm w y
      rw [abs_le] at h; linarith [h.1]
    have h2 : ‖w‖ * ‖y‖ < tpart w * tpart y := by
      rw [tpart, tpart, ← Real.sqrt_mul (show (0:ℝ) ≤ 1 + ‖w‖ ^ 2 by positivity),
        ← Real.sqrt_sq (mul_nonneg (norm_nonneg w) (norm_nonneg y))]
      apply Real.sqrt_lt_sqrt (by positivity)
      nlinarith [sq_nonneg (‖w‖ - ‖y‖)]
    linarith
  linarith [hmk, hpos, hneg]

/-! ## Facts about the pair `(a,b)` -/

lemma norm_a (a : E n) (ha : a ∈ Sph n) : ‖a‖ = 1 := (mem_Sph_iff a).mp ha

lemma norm_b (b : E n) (hb : b ∈ Sph n) : ‖b‖ = 1 := (mem_Sph_iff b).mp hb

lemma neg_one_le_inner_ab (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) :
    -1 ≤ inner ℝ a b := by
  have h := abs_real_inner_le_norm a b
  rw [norm_a a ha, norm_b b hb, mul_one] at h
  exact (abs_le.mp h).1

lemma inner_ab_le_one (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) : inner ℝ a b ≤ 1 := by
  have h := abs_real_inner_le_norm a b
  rw [norm_a a ha, norm_b b hb, mul_one] at h
  exact (abs_le.mp h).2

lemma inner_ab_lt_one (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) :
    inner ℝ a b < 1 := by
  refine lt_of_le_of_ne (inner_ab_le_one a b ha hb) ?_
  intro h
  apply hab
  have hzero : inner ℝ (a - b) (a - b) = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    have h1 : inner ℝ a a = 1 := by rw [real_inner_self_eq_norm_sq, norm_a a ha]; norm_num
    have h2 : inner ℝ b b = 1 := by rw [real_inner_self_eq_norm_sq, norm_b b hb]; norm_num
    have h3 : inner ℝ b a = 1 := by rw [real_inner_comm, h]
    linarith
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

lemma two_gcL (a b : E n) : 2 * gcL a b = 1 - inner ℝ a b := by rw [gcL]; ring

lemma gcL_pos (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) :
    0 < gcL a b := by
  rw [gcL]; linarith [inner_ab_lt_one a b ha hb hab]

lemma gcL_ne_zero (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) :
    gcL a b ≠ 0 := ne_of_gt (gcL_pos a b ha hb hab)

lemma two_mul_lt (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) :
    (0 : ℝ) < 2 * (1 - inner ℝ a b) := by linarith [inner_ab_lt_one a b ha hb hab]

lemma gcK_pos (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) :
    0 < gcK a b := by
  rw [gcK]; exact inv_pos.mpr (Real.sqrt_pos.mpr (two_mul_lt a b ha hb hab))

lemma gcK_sq (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) :
    gcK a b ^ 2 * (2 * (1 - inner ℝ a b)) = 1 := by
  have hX : (0 : ℝ) < 2 * (1 - inner ℝ a b) := two_mul_lt a b ha hb hab
  rw [gcK, inv_pow, Real.sq_sqrt (le_of_lt hX), inv_mul_cancel₀ (ne_of_gt hX)]

lemma gcK_sq_four (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) :
    gcK a b ^ 2 * (4 * gcL a b) = 1 := by
  have h := gcK_sq a b ha hb hab
  have h2 := two_gcL a b
  rw [← h2] at h; linarith [h]

lemma two_gcK_sqrt_gcL (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) :
    2 * gcK a b * Real.sqrt (gcL a b) = 1 := by
  have h := gcK_sq_four a b ha hb hab
  have hL : 0 < gcL a b := gcL_pos a b ha hb hab
  have hK : 0 < gcK a b := gcK_pos a b ha hb hab
  have h2 : (2 * gcK a b * Real.sqrt (gcL a b)) ^ 2 = 1 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hL)]
    nlinarith [h]
  rcases sq_eq_one_iff.mp h2 with h' | h'
  · exact h'
  · exfalso
    have hpos : 0 < 2 * gcK a b * Real.sqrt (gcL a b) :=
      mul_pos (mul_pos (by norm_num) hK) (Real.sqrt_pos.mpr hL)
    rw [h'] at hpos; norm_num at hpos

/-! ## The geodesic joining `a` and `b` -/

lemma mink_gcAxis (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (s t : ℝ) :
    mink (gcAxis a b s) (gcAxis a b t) = -Real.cosh (s - t) := by
  rw [gcAxis, gcAxis, minkAxisCompute n (nvec a) (nvec b) (mink_nvec_self' ha)
    (mink_nvec_self' hb)]
  rw [mink_nvec_nvec', exp_sub_add_exp']
  have h := gcK_sq a b ha hb hab
  have hk : gcK a b ^ 2 * (inner ℝ a b - 1) * 2 = -1 := by nlinarith [h]
  linear_combination (Real.cosh (s - t)) * hk

lemma gcAxis_time_pos (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (s : ℝ) :
    0 < gcAxis a b s (Sum.inr 0) := by
  have hK : 0 < gcK a b := gcK_pos a b ha hb hab
  have hsum : 0 < Real.exp s + Real.exp (-s) := by
    linarith [Real.exp_pos s, Real.exp_pos (-s)]
  rw [gcAxis]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, nvec, Sum.elim_inr, mul_one]
  exact mul_pos hK hsum

lemma hlift_gcAxisPt (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (s : ℝ) :
    hlift (gcAxisPt a b s) = gcAxis a b s := by
  have h1 : mform (gcAxis a b s) (gcAxis a b s) = -1 := by
    rw [← mink_eq_mform, mink_gcAxis a b ha hb hab s s, sub_self, Real.cosh_zero]
  exact (eq_hlift_of_upper (gcAxis a b s) h1 (gcAxis_time_pos a b ha hb hab s)).symm

lemma mink_nvec_a_gcAxis (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (s : ℝ) :
    mink (nvec a) (gcAxis a b s) = -2 * gcK a b * gcL a b * Real.exp (-s) := by
  have hXX : mink (nvec a) (nvec a) = 0 := mink_nvec_self' ha
  have hXY : mink (nvec a) (nvec b) = inner ℝ a b - 1 := mink_nvec_nvec' a b
  simp only [gcAxis, mink_smul_right'', minkSeg_add_right, hXX, hXY, mul_zero, zero_mul,
    add_zero, zero_add]
  have h := two_gcL a b
  rw [show inner ℝ a b - 1 = -(2 * gcL a b) from by linarith [h]]
  ring

lemma mink_nvec_b_gcAxis (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (s : ℝ) :
    mink (nvec b) (gcAxis a b s) = -2 * gcK a b * gcL a b * Real.exp s := by
  have hYY : mink (nvec b) (nvec b) = 0 := mink_nvec_self' hb
  have hYX : mink (nvec b) (nvec a) = inner ℝ a b - 1 := by
    rw [mink_nvec_nvec' b a, real_inner_comm]
  simp only [gcAxis, mink_smul_right'', minkSeg_add_right, hYY, hYX, mul_zero, zero_mul,
    add_zero, zero_add]
  have h := two_gcL a b
  rw [show inner ℝ a b - 1 = -(2 * gcL a b) from by linarith [h]]
  ring

lemma lev_a_gcAxisPt (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (s : ℝ) :
    lev a (gcAxisPt a b s) = 2 * gcK a b * gcL a b * Real.exp (-s) := by
  rw [lev_eq_neg_mink, hlift_gcAxisPt a b ha hb hab s, mink_nvec_a_gcAxis a b ha hb hab s]
  ring

lemma lev_b_gcAxisPt (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (s : ℝ) :
    lev b (gcAxisPt a b s) = 2 * gcK a b * gcL a b * Real.exp s := by
  rw [lev_eq_neg_mink, hlift_gcAxisPt a b ha hb hab s, mink_nvec_b_gcAxis a b ha hb hab s]
  ring

lemma lev_mul_exp (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (u : E n) :
    lev a u * lev b u = Real.exp (busemann a u + busemann b u) := by
  rw [lev_eq_exp ha u, lev_eq_exp hb u, Real.exp_add]

lemma gcAxisPt_mem_geodSet (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (s : ℝ) : gcAxisPt a b s ∈ geodSet a b := by
  have hk := gcK_sq a b ha hb hab
  have h2 := two_gcL a b
  have hprod : (2 * gcK a b * gcL a b * Real.exp (-s)) * (2 * gcK a b * gcL a b * Real.exp s)
      = 4 * gcK a b ^ 2 * gcL a b ^ 2 := by
    have hs : Real.exp s ≠ 0 := ne_of_gt (Real.exp_pos s)
    rw [Real.exp_neg]
    field_simp
    ring
  have hmain : 4 * gcK a b ^ 2 * gcL a b ^ 2 = (1 - inner ℝ a b) / 2 := by
    have h4 : 4 * gcK a b ^ 2 * gcL a b = 1 := by nlinarith [hk, h2]
    linear_combination (gcL a b) * h4 + (1 / 2) * h2
  rw [geodSet, Set.mem_setOf_eq, ← lev_mul_exp a b ha hb (gcAxisPt a b s),
    lev_a_gcAxisPt a b ha hb hab s, lev_b_gcAxisPt a b ha hb hab s, hprod, hmain]

lemma distGeod_eq (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (u : E n) :
    distGeod a b u = Real.arcosh (Real.sqrt (lev a u * lev b u / gcL a b)) := by
  rw [distGeod, lev_mul_exp a b ha hb u, gcL]
  congr 1
  rw [div_div_eq_mul_div]; ring_nf

lemma mem_geodSet_iff (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (u : E n) :
    u ∈ geodSet a b ↔ lev a u * lev b u = gcL a b := by
  have h := lev_mul_exp a b ha hb u
  rw [geodSet, Set.mem_setOf_eq, gcL, ← h]

lemma sqrt_levdiv_ge_one (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) : 1 ≤ Real.sqrt (lev a u * lev b u / gcL a b) := by
  have h := levMulGe n ha hb u
  have h2L := two_gcL a b
  have hL : 0 < gcL a b := gcL_pos a b ha hb hab
  rw [Real.one_le_sqrt, le_div_iff₀ hL]
  linarith [h, h2L]

lemma distGeod_nonneg (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    0 ≤ distGeod a b u := by
  rw [distGeod_eq a b ha hb u]
  exact Real.arcosh_nonneg (sqrt_levdiv_ge_one a b ha hb hab u)

lemma arcosh_eq_zero_iff' {y : ℝ} (hy : 1 ≤ y) : Real.arcosh y = 0 ↔ y = 1 := by
  constructor
  · intro h
    have h2 : Real.arcosh y ≤ Real.arcosh 1 := by rw [h, Real.arcosh_zero]
    have h3 : y ≤ 1 := (Real.arcosh_le_arcosh (lt_of_lt_of_le zero_lt_one hy)
      (by norm_num)).mp h2
    linarith
  · intro h; rw [h, Real.arcosh_zero]

lemma distGeod_eq_zero_iff (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) : distGeod a b u = 0 ↔ u ∈ geodSet a b := by
  rw [distGeod_eq a b ha hb u, mem_geodSet_iff a b ha hb u,
    arcosh_eq_zero_iff' (sqrt_levdiv_ge_one a b ha hb hab u), Real.sqrt_eq_one,
    div_eq_one_iff_eq (gcL_ne_zero a b ha hb hab)]

/-! ## The decomposition of `hlift u` -/

lemma gcA_mul (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    gcA a b u * (2 * gcL a b) = lev b u := by
  rw [gcA]
  exact div_mul_cancel₀ (lev b u) (by linarith [gcL_pos a b ha hb hab])

lemma gcB_mul (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    gcB a b u * (2 * gcL a b) = lev a u := by
  rw [gcB]
  exact div_mul_cancel₀ (lev a u) (by linarith [gcL_pos a b ha hb hab])

lemma gcA_pos (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    0 < gcA a b u :=
  div_pos (lev_pos b hb u) (by linarith [gcL_pos a b ha hb hab])

lemma gcB_pos (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    0 < gcB a b u :=
  div_pos (lev_pos a ha u) (by linarith [gcL_pos a b ha hb hab])

lemma gcN_expand (a b u : E n) :
    gcA a b u • nvec a + gcB a b u • nvec b + gcN a b u = hlift u := by
  rw [gcN]; abel

lemma mink_gcN_nvec_a (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    mink (gcN a b u) (nvec a) = 0 := by
  have hXX : mink (nvec a) (nvec a) = 0 := mink_nvec_self' ha
  have hYX : mink (nvec b) (nvec a) = inner ℝ a b - 1 := by
    rw [mink_nvec_nvec' b a, real_inner_comm]
  have hUX : mink (hlift u) (nvec a) = -lev a u := by
    rw [minkSeg_comm]; exact mink_nvec_hlift n a u
  have hB : gcB a b u * (inner ℝ a b - 1) = -lev a u := by
    have h1 := gcB_mul a b ha hb hab u
    have h2 := two_gcL a b
    rw [show inner ℝ a b - 1 = -(2 * gcL a b) from by linarith [h2]]
    linarith [h1]
  rw [gcN, mink_expand_l, hXX, hYX, hUX]
  linear_combination -hB

lemma mink_gcN_nvec_b (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    mink (gcN a b u) (nvec b) = 0 := by
  have hYY : mink (nvec b) (nvec b) = 0 := mink_nvec_self' hb
  have hXY : mink (nvec a) (nvec b) = inner ℝ a b - 1 := mink_nvec_nvec' a b
  have hUY : mink (hlift u) (nvec b) = -lev b u := by
    rw [minkSeg_comm]; exact mink_nvec_hlift n b u
  have hA : gcA a b u * (inner ℝ a b - 1) = -lev b u := by
    have h1 := gcA_mul a b ha hb hab u
    have h2 := two_gcL a b
    rw [show inner ℝ a b - 1 = -(2 * gcL a b) from by linarith [h2]]
    linarith [h1]
  rw [gcN, mink_expand_l, hYY, hXY, hUY]
  linear_combination -hA

lemma mink_nvec_a_gcN (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    mink (nvec a) (gcN a b u) = 0 := by
  rw [minkSeg_comm]; exact mink_gcN_nvec_a a b ha hb hab u

lemma mink_nvec_b_gcN (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    mink (nvec b) (gcN a b u) = 0 := by
  rw [minkSeg_comm]; exact mink_gcN_nvec_b a b ha hb hab u

lemma gcN_self_mink (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    mink (gcN a b u) (gcN a b u) = lev a u * lev b u / gcL a b - 1 := by
  have hXX : mink (nvec a) (nvec a) = 0 := mink_nvec_self' ha
  have hYY : mink (nvec b) (nvec b) = 0 := mink_nvec_self' hb
  have hXY : mink (nvec a) (nvec b) = inner ℝ a b - 1 := mink_nvec_nvec' a b
  have hYX : mink (nvec b) (nvec a) = inner ℝ a b - 1 := by
    rw [mink_nvec_nvec' b a, real_inner_comm]
  have hUU : mink (hlift u) (hlift u) = -1 := by
    rw [mink_hlift_hlift, real_inner_self_eq_norm_sq]; nlinarith [tpart_sq u]
  have hUX : mink (hlift u) (nvec a) = -lev a u := by
    rw [minkSeg_comm]; exact mink_nvec_hlift n a u
  have hUY : mink (hlift u) (nvec b) = -lev b u := by
    rw [minkSeg_comm]; exact mink_nvec_hlift n b u
  have hXU : mink (nvec a) (hlift u) = -lev a u := mink_nvec_hlift n a u
  have hYU : mink (nvec b) (hlift u) = -lev b u := mink_nvec_hlift n b u
  have hne : (1 : ℝ) - inner ℝ a b ≠ 0 := by linarith [inner_ab_lt_one a b ha hb hab]
  rw [gcN, mink_expand, hUU, hUX, hUY, hXU, hYU, hXX, hYY, hXY, hYX, gcA, gcB, gcL]
  field_simp
  ring

lemma gcN_self_nonneg (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    0 ≤ mink (gcN a b u) (gcN a b u) := by
  rw [gcN_self_mink a b ha hb hab u]
  have h := levMulGe n ha hb u
  have h2L := two_gcL a b
  have hL : 0 < gcL a b := gcL_pos a b ha hb hab
  have h1 : (1 : ℝ) ≤ lev a u * lev b u / gcL a b := by
    rw [le_div_iff₀ hL]
    linarith [h, h2L]
  linarith

lemma gcN_eq_zero_of_self (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) (h : mink (gcN a b u) (gcN a b u) = 0) : gcN a b u = 0 := by
  have horth : mink (gcN a b u) (hlift (gcAxisPt a b 0)) = 0 := by
    rw [hlift_gcAxisPt a b ha hb hab 0, gcAxis]
    simp only [Real.exp_zero, neg_zero, one_smul]
    rw [mink_smul_right'', minkSeg_add_right, mink_gcN_nvec_a a b ha hb hab u,
      mink_gcN_nvec_b a b ha hb hab u]
    ring
  exact mink_eq_zero_of_orth_of_self_zero (gcAxisPt a b 0) (gcN a b u) horth h

lemma four_gcL_gcA_gcB (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) :
    4 * gcL a b * gcA a b u * gcB a b u = 1 + mink (gcN a b u) (gcN a b u) := by
  have hne : (1 : ℝ) - inner ℝ a b ≠ 0 := by linarith [inner_ab_lt_one a b ha hb hab]
  rw [gcN_self_mink a b ha hb hab u, gcA, gcB, gcL]
  field_simp
  ring

lemma mink_S0_self (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    mink (gcA a b u • nvec a + gcB a b u • nvec b)
      (gcA a b u • nvec a + gcB a b u • nvec b)
      = -(1 + mink (gcN a b u) (gcN a b u)) := by
  have hXY : mink (nvec a) (nvec b) = inner ℝ a b - 1 := mink_nvec_nvec' a b
  have hYX : mink (nvec b) (nvec a) = inner ℝ a b - 1 := by
    rw [mink_nvec_nvec' b a, real_inner_comm]
  have hXX : mink (nvec a) (nvec a) = 0 := mink_nvec_self' ha
  have hYY : mink (nvec b) (nvec b) = 0 := mink_nvec_self' hb
  have h4 := four_gcL_gcA_gcB a b ha hb hab u
  have h2 := two_gcL a b
  rw [mink_expand2, hXX, hYY, hXY, hYX]
  rw [show inner ℝ a b - 1 = -(2 * gcL a b) from by linarith [h2]]
  nlinarith [h4]

lemma mink_S0_gcN (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    mink (gcA a b u • nvec a + gcB a b u • nvec b) (gcN a b u) = 0 := by
  rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'',
    mink_nvec_a_gcN a b ha hb hab u, mink_nvec_b_gcN a b ha hb hab u]
  ring

lemma mink_hlift_gcN (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    mink (hlift u) (gcN a b u) = mink (gcN a b u) (gcN a b u) := by
  conv_lhs => rw [← gcN_expand a b u]
  rw [minkSeg_add_left, minkSeg_add_left, mink_smul_left'', mink_smul_left'',
    mink_nvec_a_gcN a b ha hb hab u, mink_nvec_b_gcN a b ha hb hab u]
  ring

lemma mink_hlift_S0 (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    mink (hlift u) (gcA a b u • nvec a + gcB a b u • nvec b)
      = -(1 + mink (gcN a b u) (gcN a b u)) := by
  conv_lhs => rw [← gcN_expand a b u]
  rw [minkSeg_add_left, mink_S0_self a b ha hb hab u,
    minkSeg_comm (gcN a b u) (gcA a b u • nvec a + gcB a b u • nvec b),
    mink_S0_gcN a b ha hb hab u, add_zero]

lemma gcN_eq_zero_iff (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) : gcN a b u = 0 ↔ u ∈ geodSet a b := by
  constructor
  · intro h
    rw [mem_geodSet_iff a b ha hb u]
    have h1 := gcN_self_mink a b ha hb hab u
    rw [h, mink_zero_left] at h1
    have hL : gcL a b ≠ 0 := gcL_ne_zero a b ha hb hab
    have h2 : lev a u * lev b u / gcL a b = 1 := by linarith
    rwa [div_eq_one_iff_eq hL] at h2
  · intro h
    rw [mem_geodSet_iff a b ha hb u] at h
    apply gcN_eq_zero_of_self a b ha hb hab u
    rw [gcN_self_mink a b ha hb hab u, h, div_self (gcL_ne_zero a b ha hb hab)]
    norm_num

lemma geodSet_lift_span (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    {u : E n} (hu : u ∈ geodSet a b) :
    hlift u = gcA a b u • nvec a + gcB a b u • nvec b := by
  have h : gcN a b u = 0 := (gcN_eq_zero_iff a b ha hb hab u).mpr hu
  have h2 := gcN_expand a b u
  rw [h, add_zero] at h2
  exact h2.symm

/-! ## The distance to the geodesic is the least hyperbolic distance to it -/

lemma distGeod_le_hdist_of_mem (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) {q : E n} (hq : q ∈ geodSet a b) : distGeod a b u ≤ hdist u q := by
  have hLpos : 0 < gcL a b := gcL_pos a b ha hb hab
  have hCcosh : Real.cosh (distGeod a b u) = Real.sqrt (lev a u * lev b u / gcL a b) := by
    rw [distGeod_eq a b ha hb u]
    exact Real.cosh_arcosh (sqrt_levdiv_ge_one a b ha hb hab u)
  have hCsq : (Real.cosh (distGeod a b u)) ^ 2 = 1 + mink (gcN a b u) (gcN a b u) := by
    rw [hCcosh, Real.sq_sqrt (div_nonneg (mul_nonneg (le_of_lt (lev_pos a ha u))
      (le_of_lt (lev_pos b hb u))) (le_of_lt hLpos))]
    have h := gcN_self_mink a b ha hb hab u
    linarith
  have h4A : 4 * gcL a b * gcA a b u * gcB a b u
      = 1 + mink (gcN a b u) (gcN a b u) := four_gcL_gcA_gcB a b ha hb hab u
  have h4Q : 4 * gcL a b * gcA a b q * gcB a b q = 1 := by
    have h := four_gcL_gcA_gcB a b ha hb hab q
    have hq' : mink (gcN a b q) (gcN a b q) = 0 := by
      rw [(gcN_eq_zero_iff a b ha hb hab q).mpr hq, mink_zero_left]
    rw [hq'] at h; linarith
  have hAGM : (Real.cosh (distGeod a b u)) ^ 2
      ≤ (2 * gcL a b * (gcA a b q * gcB a b u + gcB a b q * gcA a b u)) ^ 2 := by
    have hid : (2 * gcL a b * (gcA a b q * gcB a b u + gcB a b q * gcA a b u)) ^ 2
        = (1 + mink (gcN a b u) (gcN a b u))
          + (2 * gcL a b * (gcA a b q * gcB a b u - gcB a b q * gcA a b u)) ^ 2 := by
      have hk1 : (2 * gcL a b * (gcA a b q * gcB a b u + gcB a b q * gcA a b u)) ^ 2
          - (2 * gcL a b * (gcA a b q * gcB a b u - gcB a b q * gcA a b u)) ^ 2
          = 16 * gcL a b ^ 2 * (gcA a b q * gcB a b u) * (gcB a b q * gcA a b u) := by ring
      have hk2 : 16 * gcL a b ^ 2 * (gcA a b q * gcB a b u) * (gcB a b q * gcA a b u)
          = (4 * gcL a b * gcA a b q * gcB a b q)
            * (4 * gcL a b * gcA a b u * gcB a b u) := by ring
      nlinarith [hk1, hk2, h4A, h4Q]
    rw [hCsq, hid]
    nlinarith [sq_nonneg (2 * gcL a b * (gcA a b q * gcB a b u - gcB a b q * gcA a b u))]
  have hZpos : 0 < 2 * gcL a b * (gcA a b q * gcB a b u + gcB a b q * gcA a b u) := by
    have h1 : 0 < gcA a b q * gcB a b u :=
      mul_pos (gcA_pos a b ha hb hab q) (gcB_pos a b ha hb hab u)
    have h2 : 0 < gcB a b q * gcA a b u :=
      mul_pos (gcB_pos a b ha hb hab q) (gcA_pos a b ha hb hab u)
    nlinarith [hLpos]
  have hCle : Real.cosh (distGeod a b u)
      ≤ 2 * gcL a b * (gcA a b q * gcB a b u + gcB a b q * gcA a b u) := by
    have h1 : 0 ≤ Real.cosh (distGeod a b u) := le_of_lt (Real.cosh_pos _)
    nlinarith [hAGM, hZpos, h1]
  have hpair : -mink (hlift u) (hlift q)
      = 2 * gcL a b * (gcA a b q * gcB a b u + gcB a b q * gcA a b u) := by
    have hspan := geodSet_lift_span a b ha hb hab hq
    rw [hspan, minkSeg_add_right, mink_smul_right'', mink_smul_right'',
      show mink (hlift u) (nvec a) = -lev a u from by
        rw [minkSeg_comm]; exact mink_nvec_hlift n a u,
      show mink (hlift u) (nvec b) = -lev b u from by
        rw [minkSeg_comm]; exact mink_nvec_hlift n b u]
    have hA := gcA_mul a b ha hb hab u
    have hB := gcB_mul a b ha hb hab u
    rw [show lev a u = gcB a b u * (2 * gcL a b) from hB.symm,
      show lev b u = gcA a b u * (2 * gcL a b) from hA.symm]
    ring
  have hneg : -mink (hlift u) (hlift q) = Real.cosh (hdist u q) := by
    rw [mink_hlift_neg_cosh' u q, neg_neg]
  have hch : Real.cosh (hdist u q)
      = 2 * gcL a b * (gcA a b q * gcB a b u + gcB a b q * gcA a b u) := by
    rw [← hneg]; exact hpair
  rw [← hch] at hCle
  rw [Real.cosh_le_cosh] at hCle
  rw [abs_of_nonneg (distGeod_nonneg a b ha hb hab u),
    abs_of_nonneg (hdist_nonneg' u q)] at hCle
  exact hCle

/-! ## The foot of the perpendicular to the geodesic -/

lemma gcFoot_cc_dd (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (u : E n) :
    (Real.sqrt (lev b u) / Real.sqrt (lev a u))
        * (Real.sqrt (lev a u) / Real.sqrt (lev b u)) = 1 := by
  have hsa : Real.sqrt (lev a u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lev_pos a ha u))
  have hsb : Real.sqrt (lev b u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lev_pos b hb u))
  field_simp

lemma gcFoot_cc_lev (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (u : E n) :
    (Real.sqrt (lev b u) / Real.sqrt (lev a u)) * lev a u
      = Real.sqrt (lev a u) * Real.sqrt (lev b u) := by
  have hsa : Real.sqrt (lev a u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lev_pos a ha u))
  have hdiv : lev a u / Real.sqrt (lev a u) = Real.sqrt (lev a u) := by
    rw [div_eq_iff hsa, ← pow_two]
    exact (Real.sq_sqrt (le_of_lt (lev_pos a ha u))).symm
  rw [div_mul_eq_mul_div, mul_div_assoc, hdiv]
  ring

lemma gcFoot_dd_lev (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (u : E n) :
    (Real.sqrt (lev a u) / Real.sqrt (lev b u)) * lev b u
      = Real.sqrt (lev a u) * Real.sqrt (lev b u) := by
  have hsb : Real.sqrt (lev b u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lev_pos b hb u))
  have hdiv : lev b u / Real.sqrt (lev b u) = Real.sqrt (lev b u) := by
    rw [div_eq_iff hsb, ← pow_two]
    exact (Real.sq_sqrt (le_of_lt (lev_pos b hb u))).symm
  rw [div_mul_eq_mul_div, mul_div_assoc, hdiv]

lemma mink_nvec_a_gcFoot (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) :
    mink (nvec a) (gcFoot a b u)
      = -2 * gcK a b * gcL a b * (Real.sqrt (lev a u) / Real.sqrt (lev b u)) := by
  have hXX : mink (nvec a) (nvec a) = 0 := mink_nvec_self' ha
  have hXY : mink (nvec a) (nvec b) = inner ℝ a b - 1 := mink_nvec_nvec' a b
  have h := two_gcL a b
  simp only [gcFoot, mink_smul_right'', minkSeg_add_right, hXX, hXY, mul_zero, zero_mul,
    add_zero, zero_add]
  rw [show inner ℝ a b - 1 = -(2 * gcL a b) from by linarith [h]]
  ring

lemma mink_nvec_b_gcFoot (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) :
    mink (nvec b) (gcFoot a b u)
      = -2 * gcK a b * gcL a b * (Real.sqrt (lev b u) / Real.sqrt (lev a u)) := by
  have hYY : mink (nvec b) (nvec b) = 0 := mink_nvec_self' hb
  have hYX : mink (nvec b) (nvec a) = inner ℝ a b - 1 := by
    rw [mink_nvec_nvec' b a, real_inner_comm]
  have h := two_gcL a b
  simp only [gcFoot, mink_smul_right'', minkSeg_add_right, hYY, hYX, mul_zero, zero_mul,
    add_zero, zero_add]
  rw [show inner ℝ a b - 1 = -(2 * gcL a b) from by linarith [h]]
  ring

lemma mink_hlift_gcFoot (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) :
    mink (hlift u) (gcFoot a b u)
      = -2 * gcK a b * Real.sqrt (lev a u) * Real.sqrt (lev b u) := by
  have hUX : mink (hlift u) (nvec a) = -lev a u := by
    rw [minkSeg_comm]; exact mink_nvec_hlift n a u
  have hUY : mink (hlift u) (nvec b) = -lev b u := by
    rw [minkSeg_comm]; exact mink_nvec_hlift n b u
  have hca : (Real.sqrt (lev b u) / Real.sqrt (lev a u)) * (-lev a u)
      = -(Real.sqrt (lev a u) * Real.sqrt (lev b u)) := by
    rw [mul_neg, gcFoot_cc_lev a b ha hb u]
  have hdb : (Real.sqrt (lev a u) / Real.sqrt (lev b u)) * (-lev b u)
      = -(Real.sqrt (lev a u) * Real.sqrt (lev b u)) := by
    rw [mul_neg, gcFoot_dd_lev a b ha hb u]
  simp only [gcFoot, mink_smul_right'', minkSeg_add_right, hUX, hUY, hca, hdb]
  ring

lemma gcFoot_time_pos (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) : 0 < gcFoot a b u (Sum.inr 0) := by
  have hK : 0 < gcK a b := gcK_pos a b ha hb hab
  have h1 : 0 < Real.sqrt (lev b u) / Real.sqrt (lev a u) :=
    div_pos (Real.sqrt_pos.mpr (lev_pos b hb u)) (Real.sqrt_pos.mpr (lev_pos a ha u))
  have h2 : 0 < Real.sqrt (lev a u) / Real.sqrt (lev b u) :=
    div_pos (Real.sqrt_pos.mpr (lev_pos a ha u)) (Real.sqrt_pos.mpr (lev_pos b hb u))
  rw [gcFoot]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, nvec, Sum.elim_inr, mul_one]
  exact mul_pos hK (add_pos h1 h2)

lemma mink_gcFoot_self (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) : mink (gcFoot a b u) (gcFoot a b u) = -1 := by
  have hXX : mink (nvec a) (nvec a) = 0 := mink_nvec_self' ha
  have hYY : mink (nvec b) (nvec b) = 0 := mink_nvec_self' hb
  have hXY : mink (nvec a) (nvec b) = inner ℝ a b - 1 := mink_nvec_nvec' a b
  have hYX : mink (nvec b) (nvec a) = inner ℝ a b - 1 := by
    rw [mink_nvec_nvec' b a, real_inner_comm]
  have hcd := gcFoot_cc_dd a b ha hb u
  have h4 := gcK_sq_four a b ha hb hab
  have h2 := two_gcL a b
  simp only [gcFoot, minkSeg_smul, mink_expand2, hXX, hYY, hXY, hYX]
  rw [show inner ℝ a b - 1 = -(2 * gcL a b) from by linarith [h2]]
  nlinarith [h4, hcd]

lemma hlift_gcFootPt (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) (u : E n) :
    hlift (gcFootPt a b u) = gcFoot a b u := by
  have h1 : mform (gcFoot a b u) (gcFoot a b u) = -1 := by
    rw [← mink_eq_mform, mink_gcFoot_self a b ha hb hab u]
  exact (eq_hlift_of_upper (gcFoot a b u) h1 (gcFoot_time_pos a b ha hb hab u)).symm

lemma lev_a_gcFootPt (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) :
    lev a (gcFootPt a b u)
      = 2 * gcK a b * gcL a b * (Real.sqrt (lev a u) / Real.sqrt (lev b u)) := by
  rw [lev_eq_neg_mink, hlift_gcFootPt a b ha hb hab u, mink_nvec_a_gcFoot a b ha hb hab u]
  ring

lemma lev_b_gcFootPt (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) :
    lev b (gcFootPt a b u)
      = 2 * gcK a b * gcL a b * (Real.sqrt (lev b u) / Real.sqrt (lev a u)) := by
  rw [lev_eq_neg_mink, hlift_gcFootPt a b ha hb hab u, mink_nvec_b_gcFoot a b ha hb hab u]
  ring

lemma gcFootPt_mem_geodSet (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) : gcFootPt a b u ∈ geodSet a b := by
  have hcd := gcFoot_cc_dd a b ha hb u
  have h4 := gcK_sq_four a b ha hb hab
  have hsq : (2 * gcK a b * gcL a b) ^ 2 = gcL a b := by nlinarith [h4]
  rw [mem_geodSet_iff a b ha hb, lev_a_gcFootPt a b ha hb hab u,
    lev_b_gcFootPt a b ha hb hab u]
  have hcd2 : (Real.sqrt (lev a u) / Real.sqrt (lev b u))
      * (Real.sqrt (lev b u) / Real.sqrt (lev a u)) = 1 := by
    rw [mul_comm]; exact gcFoot_cc_dd a b ha hb u
  have hfac : 2 * gcK a b * gcL a b * (Real.sqrt (lev a u) / Real.sqrt (lev b u))
        * (2 * gcK a b * gcL a b * (Real.sqrt (lev b u) / Real.sqrt (lev a u)))
      = (2 * gcK a b * gcL a b) ^ 2
        * ((Real.sqrt (lev a u) / Real.sqrt (lev b u))
          * (Real.sqrt (lev b u) / Real.sqrt (lev a u))) := by ring
  rw [hfac, hcd2, mul_one, hsq]

lemma hdist_gcFootPt (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (u : E n) : hdist u (gcFootPt a b u) = distGeod a b u := by
  have hmk := mink_hlift_gcFoot a b ha hb hab u
  have h2k : 2 * gcK a b * Real.sqrt (gcL a b) = 1 := two_gcK_sqrt_gcL a b ha hb hab
  have hsL : 0 < Real.sqrt (gcL a b) := Real.sqrt_pos.mpr (gcL_pos a b ha hb hab)
  have hkey : 2 * gcK a b * Real.sqrt (lev a u) * Real.sqrt (lev b u)
      = Real.sqrt (lev a u * lev b u / gcL a b) := by
    rw [Real.sqrt_div (mul_nonneg (le_of_lt (lev_pos a ha u)) (le_of_lt (lev_pos b hb u))),
      Real.sqrt_mul (le_of_lt (lev_pos a ha u))]
    rw [eq_div_iff (ne_of_gt hsL)]
    linear_combination (Real.sqrt (lev a u) * Real.sqrt (lev b u)) * h2k
  rw [distGeod_eq a b ha hb u, hdist_eq_arcosh_mink, hlift_gcFootPt a b ha hb hab u, hmk]
  rw [show -(-2 * gcK a b * Real.sqrt (lev a u) * Real.sqrt (lev b u))
      = 2 * gcK a b * Real.sqrt (lev a u) * Real.sqrt (lev b u) from by ring, hkey]

/-! ## The distance to the geodesic is 1-Lipschitz -/

lemma distGeod_abs_sub_le (a b : E n) (hI : HypIsometryProp n) (ha : a ∈ Sph n)
    (hb : b ∈ Sph n) (hab : a ≠ b) (u v : E n) :
    |distGeod a b u - distGeod a b v| ≤ hdist u v := by
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have h1 : distGeod a b u ≤ hdist u (gcFootPt a b v) :=
    distGeod_le_hdist_of_mem a b ha hb hab u (gcFootPt_mem_geodSet a b ha hb hab v)
  have h2 : hdist v (gcFootPt a b v) = distGeod a b v := hdist_gcFootPt a b ha hb hab v
  have h3 : hdist u (gcFootPt a b v) ≤ hdist u v + hdist v (gcFootPt a b v) :=
    hId.triangle u v _
  have h4 : distGeod a b u - distGeod a b v ≤ hdist u v := by linarith
  have h5 : distGeod a b v - distGeod a b u ≤ hdist u v := by
    have h1' : distGeod a b v ≤ hdist v (gcFootPt a b u) :=
      distGeod_le_hdist_of_mem a b ha hb hab v (gcFootPt_mem_geodSet a b ha hb hab u)
    have h2' : hdist u (gcFootPt a b u) = distGeod a b u := hdist_gcFootPt a b ha hb hab u
    have h3' : hdist v (gcFootPt a b u) ≤ hdist v u + hdist u (gcFootPt a b u) :=
      hId.triangle v u _
    have hsym : hdist v u = hdist u v := hId.symm v u
    linarith
  rw [abs_le]
  exact ⟨by linarith, h4⟩

/-! ## Every point is within distance `1` of a point at distance `≥ 1` from the geodesic -/

lemma exists_near_distGeod_ge_one (a b : E n) (hn : 2 ≤ n) (ha : a ∈ Sph n) (hb : b ∈ Sph n)
    (hab : a ≠ b) (w : E n) : ∃ u : E n, hdist w u ≤ 1 ∧ 1 ≤ distGeod a b u := by
  by_cases hN : gcN a b w = 0
  · obtain ⟨Zv, hZ1, hZ2, hZ3⟩ := perpNullUnit hn ha hb hab
    have hZ1' : mink Zv (nvec a) = 0 := by simpa [mink_eq_mform, nvec_eq_theta] using hZ1
    have hZ2' : mink Zv (nvec b) = 0 := by simpa [mink_eq_mform, nvec_eq_theta] using hZ2
    have hZ3' : mink Zv Zv = 1 := by simpa [mink_eq_mform] using hZ3
    have hZ1'' : mink (nvec a) Zv = 0 := by rw [minkSeg_comm]; exact hZ1'
    have hZ2'' : mink (nvec b) Zv = 0 := by rw [minkSeg_comm]; exact hZ2'
    have hwgeod : w ∈ geodSet a b := (gcN_eq_zero_iff a b ha hb hab w).mp hN
    have hwspan : hlift w = gcA a b w • nvec a + gcB a b w • nvec b :=
      geodSet_lift_span a b ha hb hab hwgeod
    have hlevprod : lev a w * lev b w = gcL a b := (mem_geodSet_iff a b ha hb w).mp hwgeod
    have hUZ : mink (hlift w) Zv = 0 := by
      rw [hwspan, minkSeg_add_left, mink_smul_left'', mink_smul_left'', hZ1'', hZ2'']
      ring
    have hZU : mink Zv (hlift w) = 0 := by rw [minkSeg_comm]; exact hUZ
    set Yb : Fin n ⊕ Fin 1 → ℝ := Real.cosh 1 • hlift w + Real.sinh 1 • Zv with hYb
    have hUU : mink (hlift w) (hlift w) = -1 := by
      rw [mink_hlift_hlift, real_inner_self_eq_norm_sq]; nlinarith [tpart_sq w]
    have hYb_self : mink Yb Yb = -1 := by
      rw [hYb, mink_expand2, hUU, hUZ, hZU, hZ3']
      nlinarith [Real.cosh_sq_sub_sinh_sq 1]
    have hYb_hlift : mink (hlift w) Yb = -Real.cosh 1 := by
      rw [hYb, minkSeg_add_right, mink_smul_right'', mink_smul_right'', hUU, hUZ]
      ring
    have htimeb : 0 < Yb (Sum.inr 0) :=
      upper_of_mink_neg w Yb hYb_self (by rw [hYb_hlift]; exact neg_lt_zero.mpr (Real.cosh_pos 1))
    have hYblift : hlift (WithLp.toLp 2 (fun i : Fin n => Yb (Sum.inl i))) = Yb :=
      (eq_hlift_of_upper Yb (by rw [← mink_eq_mform]; exact hYb_self) htimeb).symm
    refine ⟨WithLp.toLp 2 (fun i : Fin n => Yb (Sum.inl i)), ?_, ?_⟩
    · rw [hdist_eq_arcosh_mink, hYblift, hYb_hlift, neg_neg,
        Real.arcosh_cosh (by norm_num : (0 : ℝ) ≤ 1)]
    · have hleva : lev a (WithLp.toLp 2 (fun i : Fin n => Yb (Sum.inl i)))
          = Real.cosh 1 * lev a w := by
        rw [lev_eq_neg_mink, hYblift, hYb, minkSeg_add_right, mink_smul_right'',
          mink_smul_right'', mink_nvec_hlift n a w, hZ1'']
        ring
      have hlevb : lev b (WithLp.toLp 2 (fun i : Fin n => Yb (Sum.inl i)))
          = Real.cosh 1 * lev b w := by
        rw [lev_eq_neg_mink, hYblift, hYb, minkSeg_add_right, mink_smul_right'',
          mink_smul_right'', mink_nvec_hlift n b w, hZ2'']
        ring
      have hval : Real.sqrt
          (lev a (WithLp.toLp 2 (fun i : Fin n => Yb (Sum.inl i)))
            * lev b (WithLp.toLp 2 (fun i : Fin n => Yb (Sum.inl i))) / gcL a b)
          = Real.cosh 1 := by
        rw [hleva, hlevb,
          show Real.cosh 1 * lev a w * (Real.cosh 1 * lev b w) / gcL a b
            = (Real.cosh 1) ^ 2 * (lev a w * lev b w / gcL a b) from by ring]
        rw [show lev a w * lev b w / gcL a b = 1 from by
            rw [hlevprod, div_self (gcL_ne_zero a b ha hb hab)],
          mul_one, Real.sqrt_sq (le_of_lt (Real.cosh_pos 1))]
      rw [distGeod_eq a b ha hb _, hval, Real.arcosh_cosh (by norm_num : (0 : ℝ) ≤ 1)]
  · have hww_nonneg := gcN_self_nonneg a b ha hb hab w
    have hww_pos : 0 < mink (gcN a b w) (gcN a b w) := by
      rcases lt_or_eq_of_le hww_nonneg with h | h
      · exact h
      · exact absurd (gcN_eq_zero_of_self a b ha hb hab w h.symm) hN
    set dd := distGeod a b w with hdd
    have hdd_nonneg : 0 ≤ dd := distGeod_nonneg a b ha hb hab w
    have hcoshdd : Real.cosh dd = Real.sqrt (lev a w * lev b w / gcL a b) := by
      rw [hdd, distGeod_eq a b ha hb w]
      exact Real.cosh_arcosh (sqrt_levdiv_ge_one a b ha hb hab w)
    have hlv : lev a w * lev b w / gcL a b = 1 + mink (gcN a b w) (gcN a b w) := by
      have h := gcN_self_mink a b ha hb hab w; linarith
    have hcoshdd_sq : Real.cosh dd ^ 2 = 1 + mink (gcN a b w) (gcN a b w) := by
      rw [hcoshdd, Real.sq_sqrt (div_nonneg (mul_nonneg (le_of_lt (lev_pos a ha w))
        (le_of_lt (lev_pos b hb w))) (le_of_lt (gcL_pos a b ha hb hab))), hlv]
    have hsinhdd_sq : Real.sinh dd ^ 2 = mink (gcN a b w) (gcN a b w) := by
      rw [Real.sinh_sq, hcoshdd_sq]; ring
    have hdd_pos : 0 < dd := by
      refine lt_of_le_of_ne hdd_nonneg (fun h0 => hww_pos.ne' ?_)
      rw [← hsinhdd_sq, ← h0, Real.sinh_zero]; norm_num
    have hsinhdd_pos : 0 < Real.sinh dd := Real.sinh_pos_iff.mpr hdd_pos
    set t := dd + 1 with ht
    have htd : t - dd = 1 := by rw [ht]; ring
    set Y : Fin n ⊕ Fin 1 → ℝ :=
      (Real.cosh t / Real.cosh dd) • (gcA a b w • nvec a + gcB a b w • nvec b)
        + (Real.sinh t / Real.sinh dd) • gcN a b w with hY
    have hS0 := mink_S0_self a b ha hb hab w
    have hS0N := mink_S0_gcN a b ha hb hab w
    have hNS0 : mink (gcN a b w) (gcA a b w • nvec a + gcB a b w • nvec b) = 0 := by
      rw [minkSeg_comm]; exact hS0N
    have hUS0 := mink_hlift_S0 a b ha hb hab w
    have hUN := mink_hlift_gcN a b ha hb hab w
    have hcdd : (Real.cosh t / Real.cosh dd) * Real.cosh dd = Real.cosh t :=
      div_mul_cancel₀ _ (ne_of_gt (Real.cosh_pos dd))
    have hsdd : (Real.sinh t / Real.sinh dd) * Real.sinh dd = Real.sinh t :=
      div_mul_cancel₀ _ (ne_of_gt hsinhdd_pos)
    have e1 : (Real.cosh t / Real.cosh dd) * (Real.cosh t / Real.cosh dd) * Real.cosh dd ^ 2
        = Real.cosh t ^ 2 := by
      rw [show (Real.cosh t / Real.cosh dd) * (Real.cosh t / Real.cosh dd) * Real.cosh dd ^ 2
          = ((Real.cosh t / Real.cosh dd) * Real.cosh dd) ^ 2 from by ring, hcdd]
    have e2 : (Real.sinh t / Real.sinh dd) * (Real.sinh t / Real.sinh dd) * Real.sinh dd ^ 2
        = Real.sinh t ^ 2 := by
      rw [show (Real.sinh t / Real.sinh dd) * (Real.sinh t / Real.sinh dd) * Real.sinh dd ^ 2
          = ((Real.sinh t / Real.sinh dd) * Real.sinh dd) ^ 2 from by ring, hsdd]
    have hY_self : mink Y Y = -1 := by
      rw [hY, mink_expand2, hS0, hS0N, hNS0]
      rw [← hcoshdd_sq, ← hsinhdd_sq]
      nlinarith [e1, e2, Real.cosh_sq_sub_sinh_sq t]
    have f1 : (Real.cosh t / Real.cosh dd) * Real.cosh dd ^ 2
        = Real.cosh t * Real.cosh dd := by
      rw [show (Real.cosh t / Real.cosh dd) * Real.cosh dd ^ 2
          = (Real.cosh t / Real.cosh dd) * Real.cosh dd * Real.cosh dd from by ring, hcdd]
    have f2 : (Real.sinh t / Real.sinh dd) * Real.sinh dd ^ 2
        = Real.sinh t * Real.sinh dd := by
      rw [show (Real.sinh t / Real.sinh dd) * Real.sinh dd ^ 2
          = (Real.sinh t / Real.sinh dd) * Real.sinh dd * Real.sinh dd from by ring, hsdd]
    have hY_hlift : mink (hlift w) Y = -Real.cosh 1 := by
      rw [hY, minkSeg_add_right, mink_smul_right'', mink_smul_right'', hUS0, hUN]
      rw [← hcoshdd_sq, ← hsinhdd_sq]
      have hcsub : Real.cosh (t - dd) = Real.cosh 1 := by rw [htd]
      nlinarith [f1, f2, Real.cosh_sub t dd, hcsub]
    have htime : 0 < Y (Sum.inr 0) :=
      upper_of_mink_neg w Y hY_self (by rw [hY_hlift]; exact neg_lt_zero.mpr (Real.cosh_pos 1))
    have hYlift : hlift (WithLp.toLp 2 (fun i : Fin n => Y (Sum.inl i))) = Y :=
      (eq_hlift_of_upper Y (by rw [← mink_eq_mform]; exact hY_self) htime).symm
    refine ⟨WithLp.toLp 2 (fun i : Fin n => Y (Sum.inl i)), ?_, ?_⟩
    · rw [hdist_eq_arcosh_mink, hYlift, hY_hlift, neg_neg,
        Real.arcosh_cosh (by norm_num : (0 : ℝ) ≤ 1)]
    · have hUa : mink (nvec a) (gcA a b w • nvec a + gcB a b w • nvec b) = -lev a w := by
        have hXX : mink (nvec a) (nvec a) = 0 := mink_nvec_self' ha
        have hXY : mink (nvec a) (nvec b) = inner ℝ a b - 1 := mink_nvec_nvec' a b
        simp only [minkSeg_add_right, mink_smul_right'', hXX, hXY, mul_zero, zero_mul,
          add_zero, zero_add]
        have h1 := gcB_mul a b ha hb hab w
        have h2 := two_gcL a b
        rw [show inner ℝ a b - 1 = -(2 * gcL a b) from by linarith [h2]]
        linarith [h1]
      have hUb : mink (nvec b) (gcA a b w • nvec a + gcB a b w • nvec b) = -lev b w := by
        have hYY : mink (nvec b) (nvec b) = 0 := mink_nvec_self' hb
        have hYX : mink (nvec b) (nvec a) = inner ℝ a b - 1 := by
          rw [mink_nvec_nvec' b a, real_inner_comm]
        simp only [minkSeg_add_right, mink_smul_right'', hYY, hYX, mul_zero, zero_mul,
          add_zero, zero_add]
        have h1 := gcA_mul a b ha hb hab w
        have h2 := two_gcL a b
        rw [show inner ℝ a b - 1 = -(2 * gcL a b) from by linarith [h2]]
        linarith [h1]
      have hleva : lev a (WithLp.toLp 2 (fun i : Fin n => Y (Sum.inl i)))
          = (Real.cosh t / Real.cosh dd) * lev a w := by
        rw [lev_eq_neg_mink, hYlift, hY, minkSeg_add_right, mink_smul_right'',
          mink_smul_right'', hUa, mink_nvec_a_gcN a b ha hb hab w]
        ring
      have hlevb : lev b (WithLp.toLp 2 (fun i : Fin n => Y (Sum.inl i)))
          = (Real.cosh t / Real.cosh dd) * lev b w := by
        rw [lev_eq_neg_mink, hYlift, hY, minkSeg_add_right, mink_smul_right'',
          mink_smul_right'', hUb, mink_nvec_b_gcN a b ha hb hab w]
        ring
      have hval : Real.sqrt
          (lev a (WithLp.toLp 2 (fun i : Fin n => Y (Sum.inl i)))
            * lev b (WithLp.toLp 2 (fun i : Fin n => Y (Sum.inl i))) / gcL a b)
          = Real.cosh t := by
        rw [hleva, hlevb]
        rw [show Real.cosh t / Real.cosh dd * lev a w
              * (Real.cosh t / Real.cosh dd * lev b w) / gcL a b
            = (Real.cosh t / Real.cosh dd) ^ 2 * (lev a w * lev b w / gcL a b) from by ring]
        rw [hlv, ← hcoshdd_sq]
        rw [show (Real.cosh t / Real.cosh dd) ^ 2 * Real.cosh dd ^ 2
            = (Real.cosh t / Real.cosh dd * Real.cosh dd) ^ 2 from by ring, hcdd,
          Real.sqrt_sq (le_of_lt (Real.cosh_pos t))]
      rw [distGeod_eq a b ha hb _, hval]
      have htpos : 0 ≤ t := by rw [ht]; linarith
      rw [arcosh_cosh_abs', abs_of_nonneg htpos]
      rw [ht]; linarith

/-! ## The main statement -/

theorem geodFacts (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (a b : Submission.Mostow.E n) (ha : a ∈ Submission.Mostow.Sph n)
    (hb : b ∈ Submission.Mostow.Sph n) (hab : a ≠ b) :
    (∃ u : Submission.Mostow.E n, u ∈ Work.Mostow.geodSet a b) ∧
    (∀ u : Submission.Mostow.E n, 0 ≤ Work.Mostow.distGeod a b u) ∧
    (∀ u : Submission.Mostow.E n, Work.Mostow.distGeod a b u = 0 ↔ u ∈ Work.Mostow.geodSet a b) ∧
    (∀ u v : Submission.Mostow.E n,
      |Work.Mostow.distGeod a b u - Work.Mostow.distGeod a b v| ≤ Submission.Mostow.hdist u v) ∧
    (∀ w : Submission.Mostow.E n, ∃ u : Submission.Mostow.E n,
      Submission.Mostow.hdist w u ≤ 1 ∧ 1 ≤ Work.Mostow.distGeod a b u) :=
  ⟨⟨gcAxisPt a b 0, gcAxisPt_mem_geodSet a b ha hb hab 0⟩,
   fun u => distGeod_nonneg a b ha hb hab u,
   fun u => distGeod_eq_zero_iff a b ha hb hab u,
   fun u v => distGeod_abs_sub_le a b hI ha hb hab u v,
   fun w => exists_near_distGeod_ge_one a b hn ha hb hab w⟩

end

end Work.Mostow.gapA
