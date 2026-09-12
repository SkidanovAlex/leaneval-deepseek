import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Commons.Geometry.Convex.Hadwiger.hausdorffDist_eq_sSup_support
import Submission.Commons.Geometry.Convex.Hadwiger.support_add
import Submission.Commons.Analysis.Real.rpow_root_tendsto_one

namespace Commons.Geometry.Convex.Hadwiger

open Filter Metric Set
open scoped Topology BigOperators Pointwise

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]

/-- Finite-dimensional real normed spaces are proper. -/
instance (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] :
    ProperSpace W := FiniteDimensional.proper ℝ W

/-- The unit ball as a convex body. -/
def ballBody (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ConvexBody V :=
  ⟨closedBall (0 : V) 1, convex_closedBall (0 : V) 1, isCompact_closedBall (0 : V) 1,
    Metric.nonempty_closedBall.mpr (by norm_num)⟩

lemma ballBody_mem (x : V) : x ∈ (ballBody V : Set V) ↔ ‖x‖ ≤ 1 := by
  change x ∈ closedBall (0 : V) 1 ↔ ‖x‖ ≤ 1
  rw [mem_closedBall_zero_iff]

lemma ballBody_symm : (ballBody V : Set V) = -(ballBody V : Set V) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_neg]
    rw [ballBody_mem]
    rw [ballBody_mem] at hx
    simpa [norm_neg] using hx
  · intro hx
    rw [Set.mem_neg] at hx
    rw [ballBody_mem] at hx
    rw [ballBody_mem]
    simpa [norm_neg] using hx

/-- For `δ ≥ 0` the scaled unit ball is the ball of radius `δ`. -/
lemma smul_ballBody_eq_closedBall (δ : ℝ) (hδ : 0 ≤ δ) :
    δ • (ballBody V : Set V) = closedBall (0 : V) δ := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_smul_set] at hx
    rcases hx with ⟨c, hcB, hcx⟩
    rw [mem_closedBall_zero_iff]
    calc
      ‖x‖ = ‖δ • c‖ := by rw [← hcx]
      _ = |δ| * ‖c‖ := norm_smul _ _
      _ = δ * ‖c‖ := by rw [abs_of_nonneg hδ]
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left ((ballBody_mem c).mp hcB) hδ
      _ = δ := by simp
  · intro hx
    rw [Set.mem_smul_set]
    rw [mem_closedBall_zero_iff] at hx
    by_cases h0 : δ = 0
    · subst h0
      have : x = 0 := by simpa using hx
      subst x
      exact ⟨0, (ballBody_mem (0 : V)).mpr (by norm_num), by simp⟩
    · have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm h0)
      refine ⟨δ⁻¹ • x, ?_, ?_⟩
      · rw [ballBody_mem]
        calc
          ‖δ⁻¹ • x‖ = |δ⁻¹| * ‖x‖ := norm_smul _ _
          _ = δ⁻¹ * ‖x‖ := by rw [abs_of_nonneg (inv_nonneg.mpr hδ)]
          _ ≤ 1 := by
            rw [mul_comm]
            exact (div_le_iff₀ hδpos).mpr (by simpa [div_eq_mul_inv, mul_comm] using hx)
      · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hδpos), one_smul]

/-- A symmetric body is symmetric iff membership is closed under negation. -/
lemma symm_iff_neg (K : ConvexBody V) : (K : Set V) = -(K : Set V) ↔
    ∀ x : V, x ∈ (K : Set V) → -x ∈ (K : Set V) := by
  constructor
  · intro h x hx
    rw [h] at hx
    simpa using hx
  · intro h
    ext x
    constructor
    · intro hx
      change -x ∈ (K : Set V)
      exact h x hx
    · intro hx
      change -x ∈ (K : Set V) at hx
      have : -(-x) ∈ (K : Set V) := h (-x) hx
      simpa using this

lemma zero_mem_of_symm (K : ConvexBody V) (hsym : (K : Set V) = -(K : Set V)) :
    (0 : V) ∈ (K : Set V) := by
  have h' : ∀ x : V, x ∈ (K : Set V) → -x ∈ (K : Set V) := (symm_iff_neg K).mp hsym
  obtain ⟨x, hx⟩ := K.nonempty
  rw [show (0 : V) = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x) by simp]
  apply convex_iff_forall_pos.mp K.convex hx (h' x hx)
  all_goals linarith

/-- negation membership in a scaled unit ball (δ ≥ 0). -/
lemma smul_ball_neg_mem (δ : ℝ) (hδ : 0 ≤ δ) (b : V) :
    b ∈ δ • (ballBody V : Set V) ↔ -b ∈ δ • (ballBody V : Set V) := by
  rw [smul_ballBody_eq_closedBall δ hδ]
  rw [mem_closedBall_zero_iff, mem_closedBall_zero_iff]
  simp [norm_neg]

/-- The parallel body `K + δB` of a symmetric `K` is symmetric. -/
lemma parallel_body_symm (K : ConvexBody V) (hsym : (K : Set V) = -(K : Set V)) (δ : ℝ)
    (hδ : 0 ≤ δ) :
    ((K + δ • ballBody V : ConvexBody V) : Set V) =
      -((K + δ • ballBody V : ConvexBody V) : Set V) := by
  ext x
  constructor
  · intro hx
    rw [ConvexBody.coe_add, ConvexBody.coe_smul, Set.mem_add] at hx
    rcases hx with ⟨k, hk, b, hb, hEq⟩
    rw [Set.mem_neg]
    rw [ConvexBody.coe_add, ConvexBody.coe_smul, Set.mem_add]
    refine ⟨-k, (symm_iff_neg K).mp hsym k hk, -b, (smul_ball_neg_mem δ hδ b).mp hb, ?_⟩
    rw [← neg_add]
    rw [hEq]
  · intro hx
    rw [Set.mem_neg] at hx
    rw [ConvexBody.coe_add, ConvexBody.coe_smul, Set.mem_add] at hx
    rcases hx with ⟨k, hk, b, hb, hEq⟩
    rw [ConvexBody.coe_add, ConvexBody.coe_smul, Set.mem_add]
    refine ⟨-k, (symm_iff_neg K).mp hsym k hk, -b, (smul_ball_neg_mem δ hδ b).mp hb, ?_⟩
    rw [← neg_add]
    rw [hEq]
    exact neg_neg x

/-- distance from the `δ`-parallel body to the original body is at most `δ`. -/
lemma dist_parallel_le (K : ConvexBody V) (hK0 : (0 : V) ∈ (K : Set V)) (δ : ℝ) (hδ : 0 ≤ δ) :
    dist (K + δ • ballBody V) K ≤ δ := by
  have h0 : (0 : V) ∈ δ • (ballBody V : Set V) := by
    rw [Set.mem_smul_set]
    exact ⟨0, (ballBody_mem (0 : V)).mpr (by norm_num), by simp⟩
  have h1 : (K : Set V) ⊆ ((K + δ • ballBody V : ConvexBody V) : Set V) := by
    intro x hx
    rw [ConvexBody.coe_add, ConvexBody.coe_smul]
    exact ⟨x, hx, 0, h0, by simp⟩
  have h2 : ∀ y ∈ ((K + δ • ballBody V : ConvexBody V) : Set V),
      Metric.infDist y (K : Set V) ≤ δ := by
    intro y hy
    rw [ConvexBody.coe_add, ConvexBody.coe_smul, smul_ballBody_eq_closedBall δ hδ] at hy
    rcases hy with ⟨a, ha, b, hb, rfl⟩
    have hb' : ‖b‖ ≤ δ := by simpa [mem_closedBall_zero_iff] using hb
    calc
      Metric.infDist (a + b) (K : Set V) ≤ dist (a + b) a := Metric.infDist_le_dist_of_mem ha
      _ = ‖b‖ := by rw [dist_eq_norm, add_sub_cancel_left]
      _ ≤ δ := hb'
  have h3 : ∀ x ∈ (K : Set V), Metric.infDist x ((K + δ • ballBody V : ConvexBody V) : Set V) ≤ δ := by
    intro x hx
    exact le_trans (Metric.infDist_zero_of_mem (h1 hx)).le hδ
  have hhd : Metric.hausdorffDist ((K + δ • ballBody V : ConvexBody V) : Set V) (K : Set V) ≤ δ :=
    Metric.hausdorffDist_le_of_infDist hδ h2 h3
  rw [← ConvexBody.hausdorffDist_coe]
  exact hhd

/-- A finite subset of a compact set that is `δ`-dense. -/
lemma exists_finite_dense {C : Set V} (hC : IsCompact C) (hCn : C.Nonempty) (δ : ℝ)
    (hδ : 0 < δ) :
    ∃ A : Finset V, (∀ a ∈ A, a ∈ C) ∧ ∀ x ∈ C, ∃ a ∈ A, dist x a < δ := by
  classical
  let c : {x : V // x ∈ C} → Set V := fun i => ball (i : V) δ
  have hcov : C ⊆ ⋃ i : {x : V // x ∈ C}, c i := by
    intro x hx
    rw [Set.mem_iUnion]
    exact ⟨⟨x, hx⟩, mem_ball_self hδ⟩
  rcases (hC.elim_finite_subcover c (fun i => isOpen_ball) hcov) with ⟨t, ht⟩
  let e : {x : V // x ∈ C} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨t.map e, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_map.mp ha with ⟨i, hi, rfl⟩
    exact i.property
  · intro x hx
    have hx' : x ∈ ⋃ i ∈ t, ball (i : V) δ := by simpa [c, e] using ht hx
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨i, hi⟩
    rw [Set.mem_iUnion] at hi
    rcases hi with ⟨hit, hix⟩
    exact ⟨i, Finset.mem_map.mpr ⟨i, hit, rfl⟩, mem_ball.mp hix⟩
/-! ## The smooth 1-homogeneous approximant built from a finite net -/

/-- Exponent `2k` (as a real). -/
def pexp (k : ℕ) : ℝ := ((2 * k : ℕ) : ℝ)

/-- The sum of the `(2k)`-th powers of the inner products with the net vectors. -/
def sNat (A : Finset V) (k : ℕ) (u : V) : ℝ := ∑ a ∈ A, (inner ℝ u a) ^ (2 * k)

/-- The smooth even approximating support function: the `(2k)`-root of `sNat`. -/
def fSm (A : Finset V) (k : ℕ) (u : V) : ℝ := (sNat A k u) ^ ((pexp k)⁻¹)

/-- `|z|^(2k)` equals the even natural power `z^(2k)` (so it is smooth in `z`). -/
lemma abs_rpow_even_eq_pow (z : ℝ) (k : ℕ) :
    |z| ^ (pexp k) = z ^ (2 * k) := by
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz]
    rw [pexp]
    rw [Real.rpow_natCast z (2 * k)]
  · have hzneg : z < 0 := lt_of_not_ge hz
    rw [abs_of_neg hzneg]
    rw [pexp]
    rw [Real.rpow_natCast (-z) (2 * k)]
    calc
      (-z) ^ (2 * k) = ((-z) ^ 2) ^ k := by rw [pow_mul]
      _ = (z ^ 2) ^ k := by congr 1; ring
      _ = z ^ (2 * k) := by rw [pow_mul]

/-- The map `z ↦ |z|^(2k)` is smooth everywhere. -/
lemma contDiffOn_abs_rpow_even (k : ℕ) :
    ContDiffOn ℝ ⊤ (fun z : ℝ => |z| ^ (pexp k)) Set.univ := by
  have hEq : (fun z : ℝ => |z| ^ (pexp k)) = fun z : ℝ => z ^ (2 * k) := by
    funext z
    exact abs_rpow_even_eq_pow z k
  rw [hEq]
  exact (contDiffOn_id.pow (2 * k))

/-- `inner u a` as a smooth function of `u`. -/
lemma contDiffOn_inner_left (a : V) : ContDiffOn ℝ ⊤ (fun u : V => inner ℝ u a) Set.univ := by
  simpa [real_inner_comm] using ((innerSL ℝ a : V →L[ℝ] ℝ).contDiff).contDiffOn

/-- `sNat` is a sum of nonnegative terms. -/
lemma sNat_nonneg (A : Finset V) (k : ℕ) (u : V) : 0 ≤ sNat A k u := by
  unfold sNat
  exact Finset.sum_nonneg (fun a ha => by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg (inner ℝ u a)) k)

/-- `sNat` is even in `u`. -/
lemma sNat_even (A : Finset V) (k : ℕ) (u : V) : sNat A k (-u) = sNat A k u := by
  unfold sNat
  apply Finset.sum_congr rfl
  intro a ha
  rw [inner_neg_left]
  calc
    (-inner ℝ u a) ^ (2 * k) = ((-inner ℝ u a) ^ 2) ^ k := by rw [pow_mul]
    _ = (inner ℝ u a ^ 2) ^ k := by ring
    _ = (inner ℝ u a) ^ (2 * k) := by rw [pow_mul]

/-- `sNat` is also the sum of the `(2k)`-th real powers of absolute values. -/
lemma sNat_eq_sum_abs_pow (A : Finset V) (k : ℕ) (u : V) :
    sNat A k u = ∑ a ∈ A, |inner ℝ u a| ^ pexp k := by
  unfold sNat
  apply Finset.sum_congr rfl
  intro a ha
  exact (abs_rpow_even_eq_pow (inner ℝ u a) k).symm

/-- `fSm` is even. -/
lemma fSm_even (A : Finset V) (k : ℕ) (u : V) : fSm A k (-u) = fSm A k u := by
  unfold fSm
  rw [sNat_even]

/-- `sNat` is smooth on the set of vectors that are not orthogonal to every net vector. -/
lemma contDiffOn_sNat (A : Finset V) (k : ℕ) :
    ContDiffOn ℝ ⊤ (fun u : V => sNat A k u) {u : V | u ≠ 0} := by
  have h1 : ContDiffOn ℝ ⊤ (fun u : V => sNat A k u) Set.univ := by
    unfold sNat
    refine ContDiffOn.sum ?_
    intro a ha
    exact ContDiffOn.pow (contDiffOn_inner_left a) (2 * k)
  exact h1.mono (by intro u hu; trivial)

/-- `sNat` is positive away from `0` when the net spans in direction `u`. -/
lemma sNat_pos_of_span (A : Finset V) (k : ℕ) (hk : 1 ≤ k) (u : V) (hu : u ≠ 0)
    (hspan : ∃ a ∈ A, inner ℝ u a ≠ 0) : 0 < sNat A k u := by
  rcases hspan with ⟨a0, ha0, hz⟩
  have hpos : 0 < (inner ℝ u a0) ^ (2 * k) := by
    have hz2 : 0 < (inner ℝ u a0) ^ 2 := sq_pos_of_ne_zero hz
    rw [pow_mul]
    exact pow_pos hz2 k
  have hn : ∀ b ∈ A, 0 ≤ (inner ℝ u b) ^ (2 * k) := by
    intro b hb
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg (inner ℝ u b)) k
  have hle : (inner ℝ u a0) ^ (2 * k) ≤ sNat A k u := by
    unfold sNat
    exact Finset.single_le_sum (s := A) (f := fun b : V => (inner ℝ u b) ^ (2 * k)) hn ha0
  exact lt_of_lt_of_le hpos hle

/-- The support function approximant `fSm` is smooth away from the origin
(when the net spans `V`). -/
lemma contDiffOn_fSm {A : Finset V} {k : ℕ} (hk : 1 ≤ k)
    (hspan : ∀ u : V, u ≠ 0 → ∃ a ∈ A, inner ℝ u a ≠ 0) :
    ContDiffOn ℝ ⊤ (fun u : V => fSm A k u) {u : V | u ≠ 0} := by
  change ContDiffOn ℝ ⊤ (fun u : V => (sNat A k u) ^ ((pexp k)⁻¹)) {u : V | u ≠ 0}
  refine ContDiffOn.rpow (contDiffOn_sNat A k) (contDiffOn_const) ?_
  intro u hu
  exact ne_of_gt (sNat_pos_of_span A k hk u hu (hspan u hu))

/-! ### Abstract `L_p`–`L_q` duality with even integer exponent -/

/-- The dualizing vector for the Lp optimizer. -/
def yvec {ι : Type*} (s : Finset ι) (p : ℝ) (z : ι → ℝ) (N : ℝ) : ι → ℝ :=
  fun i => z i * |z i| ^ (p - 2) / N ^ (p - 1)

lemma sq_eq_rpow_two (z : ℝ) : z ^ 2 = |z| ^ (2 : ℝ) := by
  rw [Real.rpow_two, sq_abs]

lemma z2_mul_abs (z : ℝ) (p : ℝ) (hp2 : 2 ≤ p) : z ^ 2 * |z| ^ (p - 2) = |z| ^ p := by
  by_cases hz : z = 0
  · subst z
    rw [abs_zero]
    by_cases hp2z : p - 2 = 0
    · rw [hp2z, Real.rpow_zero]
      rw [show p = (2 : ℝ) by linarith]
      norm_num
    · rw [Real.zero_rpow hp2z]
      rw [Real.zero_rpow (by linarith : p ≠ 0)]
      norm_num
  · have hx : 0 < |z| := abs_pos.mpr hz
    calc
      z ^ 2 * |z| ^ (p - 2) = |z| ^ (2 : ℝ) * |z| ^ (p - 2) := by rw [sq_eq_rpow_two z]
      _ = |z| ^ ((2 : ℝ) + (p - 2)) := by
          rw [← Real.rpow_add hx (2 : ℝ) (p - 2)]
      _ = |z| ^ p := by congr 1; ring

lemma abs_mul_abs_p (z : ℝ) (p : ℝ) (hp2 : 2 ≤ p) : |z| * |z| ^ (p - 2) = |z| ^ (p - 1) := by
  by_cases hz : z = 0
  · subst z
    rw [abs_zero]
    by_cases hp2z : p - 2 = 0
    · rw [hp2z, Real.rpow_zero]
      rw [show p = (2 : ℝ) by linarith]
      norm_num
    · rw [Real.zero_rpow hp2z]
      rw [Real.zero_rpow (by linarith : p - 1 ≠ 0)]
      norm_num
  · have hx : 0 < |z| := abs_pos.mpr hz
    calc
      |z| * |z| ^ (p - 2) = (|z| ^ (1 : ℝ)) * |z| ^ (p - 2) := by
          congr 1
          rw [Real.rpow_one]
      _ = |z| ^ ((1 : ℝ) + (p - 2)) := by
          rw [← Real.rpow_add hx (1 : ℝ) (p - 2)]
      _ = |z| ^ (p - 1) := by congr 1; ring

lemma abs_y_eq (z : ℝ) (p : ℝ) (hp2 : 2 ≤ p) (N : ℝ) (hNpos : 0 < N) :
    |z * |z| ^ (p - 2) / N ^ (p - 1)| = |z| ^ (p - 1) / N ^ (p - 1) := by
  have hNN : 0 < N ^ (p - 1) := Real.rpow_pos_of_pos hNpos _
  calc
    |z * |z| ^ (p - 2) / N ^ (p - 1)| = |z * |z| ^ (p - 2)| / |N ^ (p - 1)| := by rw [abs_div]
    _ = (|z| * |z| ^ (p - 2)) / N ^ (p - 1) := by
        rw [abs_mul]
        rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg z) _)]
        rw [abs_of_pos hNN]
    _ = |z| ^ (p - 1) / N ^ (p - 1) := by rw [abs_mul_abs_p z p hp2]

lemma conj_exp_mul (p : ℝ) (hp : p ≠ 1) : (p - 1) * (p / (p - 1)) = p := by
  field_simp [hp]

lemma sum_zy_eq {ι : Type*} (s : Finset ι) {p : ℝ} (hp2 : 2 ≤ p) (z : ι → ℝ) {N : ℝ}
    (hNpos : 0 < N) (hNpow : N ^ p = ∑ i ∈ s, |z i| ^ p) :
    ∑ i ∈ s, z i * yvec s p z N i = N := by
  calc
    ∑ i ∈ s, z i * yvec s p z N i
        = ∑ i ∈ s, (z i ^ 2 * |z i| ^ (p - 2)) / N ^ (p - 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [yvec, div_eq_mul_inv]
            ring
    _ = (∑ i ∈ s, z i ^ 2 * |z i| ^ (p - 2)) / N ^ (p - 1) := by
            rw [Finset.sum_div]
    _ = N ^ p / N ^ (p - 1) := by
            rw [show (∑ i ∈ s, z i ^ 2 * |z i| ^ (p - 2)) = ∑ i ∈ s, |z i| ^ p by
              apply Finset.sum_congr rfl
              intro i hi
              exact z2_mul_abs (z i) p hp2]
            rw [hNpow]
    _ = N := by
            rw [← Real.rpow_sub hNpos p (p - 1)]
            rw [show p - (p - 1) = (1 : ℝ) by ring]
            rw [Real.rpow_one]

lemma sum_abs_y_eq_one {ι : Type*} (s : Finset ι) {p : ℝ} (hp2 : 2 ≤ p) (z : ι → ℝ) {N : ℝ}
    (hNpos : 0 < N) (hNpow : N ^ p = ∑ i ∈ s, |z i| ^ p) :
    ∑ i ∈ s, |yvec s p z N i| ^ (p / (p - 1)) = 1 := by
  have hp1 : p ≠ 1 := by linarith
  have hterm : ∀ i ∈ s, |yvec s p z N i| ^ (p / (p - 1)) = |z i| ^ p / N ^ p := by
    intro i hi
    have hnum : (|z i| ^ (p - 1)) ^ (p / (p - 1)) = |z i| ^ p := by
      rw [← Real.rpow_mul (abs_nonneg (z i)) (p - 1) (p / (p - 1))]
      congr 1
      exact conj_exp_mul p hp1
    have hden : (N ^ (p - 1)) ^ (p / (p - 1)) = N ^ p := by
      rw [← Real.rpow_mul hNpos.le (p - 1) (p / (p - 1))]
      congr 1
      exact conj_exp_mul p hp1
    calc
      |yvec s p z N i| ^ (p / (p - 1))
          = (|z i| ^ (p - 1) / N ^ (p - 1)) ^ (p / (p - 1)) := by
              unfold yvec
              rw [abs_y_eq (z i) p hp2 N hNpos]
      _ = |z i| ^ p / N ^ p := by
              rw [Real.div_rpow (Real.rpow_nonneg (abs_nonneg (z i)) _) (Real.rpow_nonneg hNpos.le _)]
              rw [hnum, hden]
  calc
    ∑ i ∈ s, |yvec s p z N i| ^ (p / (p - 1))
        = ∑ i ∈ s, |z i| ^ p / N ^ p := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i hi
    _ = (∑ i ∈ s, |z i| ^ p) / N ^ p := by rw [Finset.sum_div]
    _ = 1 := by
            rw [hNpow]
            have hsumpos : 0 < ∑ i ∈ s, |z i| ^ p := by
              rw [← hNpow]
              exact Real.rpow_pos_of_pos hNpos _
            exact div_self (ne_of_gt hsumpos)

/-! ### The origin-symmetric convex body with support function `fSm` -/

/-- The body whose support function should be `fSm A k`. -/
def Xset (A : Finset V) (k : ℕ) : Set V := {x | ∀ u : V, inner ℝ x u ≤ fSm A k u}

lemma Xset_mem (A : Finset V) (k : ℕ) (x : V) :
    x ∈ Xset A k ↔ ∀ u : V, inner ℝ x u ≤ fSm A k u := Iff.rfl

/-- `fSm` is nonnegative. -/
lemma fSm_nonneg (A : Finset V) (k : ℕ) (u : V) : 0 ≤ fSm A k u := by
  unfold fSm
  exact Real.rpow_nonneg (sNat_nonneg A k u) _

/-- zero lies in `Xset`. -/
lemma Xset_zero_mem (A : Finset V) (k : ℕ) : (0 : V) ∈ Xset A k := by
  intro u
  simp
  exact fSm_nonneg A k u

/-- Natural `(2k)`-powers of a real `z` equal its absolute value power. -/
lemma pow_two_mul_eq_abs (z : ℝ) (k : ℕ) : z ^ (2 * k) = |z| ^ (2 * k) := by
  rw [← abs_rpow_even_eq_pow]
  unfold pexp
  rw [Real.rpow_natCast]

/-- `fSm` is bounded above by a constant times the norm: `f u ≤ C * ‖u‖`. -/
lemma fSm_le_norm_mul (A : Finset V) (k : ℕ) (hk : 1 ≤ k) (u : V) :
    fSm A k u ≤ (∑ a ∈ A, ‖a‖ ^ (2 * k)) ^ ((pexp k)⁻¹) * ‖u‖ := by
  have hkp : 0 < pexp k := by unfold pexp; positivity
  have hroot0 : 0 ≤ (pexp k)⁻¹ := by exact le_of_lt (inv_pos.mpr hkp)
  have hpow : (∑ a ∈ A, (inner ℝ u a) ^ (2 * k)) ≤
      (∑ a ∈ A, (‖u‖ * ‖a‖) ^ (2 * k)) := by
    apply Finset.sum_le_sum
    intro a ha
    have hia : |inner ℝ u a| ≤ ‖u‖ * ‖a‖ := by
      have h := norm_inner_le_norm (𝕜 := ℝ) u a
      simpa using h
    calc
      (inner ℝ u a) ^ (2 * k) = |inner ℝ u a| ^ (2 * k) := pow_two_mul_eq_abs _ k
      _ ≤ (‖u‖ * ‖a‖) ^ (2 * k) := pow_le_pow_left₀ (abs_nonneg _) hia (2 * k)
  have hroot_mono : fSm A k u ≤ (∑ a ∈ A, (‖u‖ * ‖a‖) ^ (2 * k)) ^ ((pexp k)⁻¹) := by
    unfold fSm
    exact Real.rpow_le_rpow (sNat_nonneg A k u) hpow hroot0
  have hfac : (∑ a ∈ A, (‖u‖ * ‖a‖) ^ (2 * k)) = (∑ a ∈ A, ‖a‖ ^ (2 * k)) * ‖u‖ ^ (2 * k) := by
    calc
      (∑ a ∈ A, (‖u‖ * ‖a‖) ^ (2 * k)) = ∑ a ∈ A, (‖a‖ ^ (2 * k)) * (‖u‖ ^ (2 * k)) := by
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = (∑ a ∈ A, ‖a‖ ^ (2 * k)) * ‖u‖ ^ (2 * k) := by rw [← Finset.sum_mul]
  have hrootpow : (‖u‖ ^ (2 * k)) ^ ((pexp k)⁻¹) = ‖u‖ := by
    calc
      (‖u‖ ^ (2 * k)) ^ ((pexp k)⁻¹) = (‖u‖ ^ (pexp k)) ^ ((pexp k)⁻¹) := by
          congr 1
          change ‖u‖ ^ (2 * k) = ‖u‖ ^ (((2 * k : ℕ) : ℝ))
          rw [Real.rpow_natCast]
      _ = ‖u‖ := by
          rw [← Real.rpow_mul (norm_nonneg u) (pexp k) ((pexp k)⁻¹)]
          rw [mul_inv_cancel₀ (ne_of_gt hkp)]
          rw [Real.rpow_one]
  calc
    fSm A k u ≤ (∑ a ∈ A, (‖u‖ * ‖a‖) ^ (2 * k)) ^ ((pexp k)⁻¹) := hroot_mono
    _ = ((∑ a ∈ A, ‖a‖ ^ (2 * k)) * ‖u‖ ^ (2 * k)) ^ ((pexp k)⁻¹) := by rw [hfac]
    _ = (∑ a ∈ A, ‖a‖ ^ (2 * k)) ^ ((pexp k)⁻¹) * (‖u‖ ^ (2 * k)) ^ ((pexp k)⁻¹) := by
        rw [Real.mul_rpow]
        · exact Finset.sum_nonneg (fun a ha => pow_nonneg (norm_nonneg a) (2 * k))
        · exact pow_nonneg (norm_nonneg u) (2 * k)
    _ = (∑ a ∈ A, ‖a‖ ^ (2 * k)) ^ ((pexp k)⁻¹) * ‖u‖ := by rw [hrootpow]

/-- `Xset` is bounded: contained in the ball of radius `C`. -/
lemma Xset_bounded (A : Finset V) (k : ℕ) (hk : 1 ≤ k) :
    ∀ x ∈ Xset A k, ‖x‖ ≤ (∑ a ∈ A, ‖a‖ ^ (2 * k)) ^ ((pexp k)⁻¹) := by
  intro x hx
  by_cases hx0 : x = 0
  · rw [hx0]
    simp
    exact Real.rpow_nonneg (Finset.sum_nonneg (fun a ha => pow_nonneg (norm_nonneg a) (2 * k))) _
  · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    let u : V := (‖x‖⁻¹) • x
    have hu1 : ‖u‖ = 1 := by
      calc
        ‖u‖ = ‖‖x‖⁻¹ • x‖ := rfl
        _ = ‖‖x‖⁻¹‖ * ‖x‖ := norm_smul _ _
        _ = ‖x‖⁻¹ * ‖x‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnorm.le)]
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hnorm)
    have hin : inner ℝ x u = ‖x‖ := by
      calc
        inner ℝ x u = inner ℝ x ((‖x‖⁻¹) • x) := rfl
        _ = (‖x‖⁻¹) * inner ℝ x x := by rw [inner_smul_right]
        _ = (‖x‖⁻¹) * ‖x‖ ^ 2 := by simp
        _ = ‖x‖ := by
            rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hnorm), one_mul]
    calc
      ‖x‖ = inner ℝ x u := hin.symm
      _ ≤ fSm A k u := hx u
      _ ≤ (∑ a ∈ A, ‖a‖ ^ (2 * k)) ^ ((pexp k)⁻¹) * ‖u‖ := fSm_le_norm_mul A k hk u
      _ = (∑ a ∈ A, ‖a‖ ^ (2 * k)) ^ ((pexp k)⁻¹) := by rw [hu1]; ring

/-- `Xset` is convex. -/
lemma Xset_convex (A : Finset V) (k : ℕ) : Convex ℝ (Xset A k) := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  intro u
  calc
    inner ℝ (a • x + b • y) u = a * inner ℝ x u + b * inner ℝ y u := by
        rw [inner_add_left, inner_smul_left, inner_smul_left]
        simp
    _ ≤ a * fSm A k u + b * fSm A k u := by
        exact add_le_add (mul_le_mul_of_nonneg_left (hx u) ha.le) (mul_le_mul_of_nonneg_left (hy u) hb.le)
    _ = fSm A k u := by rw [← add_mul, hab, one_mul]

/-- `Xset` is closed. -/
lemma Xset_closed (A : Finset V) (k : ℕ) : IsClosed (Xset A k) := by
  unfold Xset
  rw [Set.setOf_forall]
  refine isClosed_iInter ?_
  intro u
  have hcont : Continuous (fun x : V => inner ℝ x u) := by
    simpa [real_inner_comm] using ((innerSL ℝ u : V →L[ℝ] ℝ).continuous)
  exact (isClosed_Iic.preimage hcont)

/-- `Xset` is compact. -/
lemma Xset_compact (A : Finset V) (k : ℕ) (hk : 1 ≤ k) : IsCompact (Xset A k) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · exact Xset_closed A k
  · have hsub : Xset A k ⊆ closedBall (0 : V) ((∑ a ∈ A, ‖a‖ ^ (2 * k)) ^ ((pexp k)⁻¹)) := by
      intro x hx
      rw [mem_closedBall_zero_iff]
      exact Xset_bounded A k hk x hx
    exact Bornology.IsBounded.subset isBounded_closedBall hsub

/-- negation maps `Xset` to itself (uses that `fSm` is even). -/
lemma Xset_symm_mem (A : Finset V) (k : ℕ) (x : V) : x ∈ Xset A k ↔ -x ∈ Xset A k := by
  constructor
  · intro hx
    intro u
    have hle : inner ℝ x (-u) ≤ fSm A k u := by
      simpa [fSm_even A k u] using hx (-u)
    calc
      inner ℝ (-x) u = -inner ℝ x u := by rw [inner_neg_left]
      _ = inner ℝ x (-u) := by rw [inner_neg_right]
      _ ≤ fSm A k u := hle
  · intro hx
    intro u
    have hle : inner ℝ (-x) (-u) ≤ fSm A k u := by
      simpa [fSm_even A k u] using hx (-u)
    calc
      inner ℝ x u = inner ℝ (-(-x)) u := by rw [neg_neg]
      _ = -inner ℝ (-x) u := by rw [inner_neg_left]
      _ = inner ℝ (-x) (-u) := by rw [inner_neg_right]
      _ ≤ fSm A k u := hle

/-- `Xset` is symmetric. -/
lemma Xset_symmetric (A : Finset V) (k : ℕ) : (Xset A k : Set V) = -(Xset A k) := by
  ext x
  constructor
  · intro hx
    change -x ∈ Xset A k
    exact (Xset_symm_mem A k x).mp hx
  · intro hx
    rw [Set.mem_neg] at hx
    exact (Xset_symm_mem A k x).mpr hx

/-- The smooth-support body as a convex body. -/
def XB (A : Finset V) (k : ℕ) (hk : 1 ≤ k) : ConvexBody V :=
  ⟨Xset A k, Xset_convex A k, Xset_compact A k hk, ⟨0, Xset_zero_mem A k⟩⟩

@[simp] lemma XB_coe (A : Finset V) (k : ℕ) (hk : 1 ≤ k) :
    ((XB A k hk : ConvexBody V) : Set V) = Xset A k := rfl

/-- The body `XB` is symmetric. -/
lemma XB_symmetric (A : Finset V) (k : ℕ) (hk : 1 ≤ k) :
    ((XB A k hk : ConvexBody V) : Set V) = -((XB A k hk : ConvexBody V) : Set V) := by
  simpa using Xset_symmetric A k

/-! ### The support function of `XB` equals `fSm` -/

/-- The support value of a set in a direction (as in the statement). -/
def supFun (C : Set V) (u : V) : ℝ := sSup ((fun x : V => inner ℝ u x) '' C)

lemma fSm_eq_rpow_sum (A : Finset V) (k : ℕ) (u : V) : fSm A k u =
    (∑ a ∈ A, |inner ℝ u a| ^ (pexp k)) ^ ((pexp k)⁻¹) := by
  unfold fSm
  congr 1
  exact sNat_eq_sum_abs_pow A k u

lemma fSm_zero (A : Finset V) (k : ℕ) (hk : 1 ≤ k) : fSm A k (0 : V) = 0 := by
  unfold fSm
  have hs : sNat A k (0 : V) = 0 := by
    unfold sNat
    rw [Finset.sum_eq_zero]
    intro a ha
    rw [inner_zero_left]
    exact zero_pow (by omega : (2 * k) ≠ 0)
  rw [hs]
  have hpne : pexp k ≠ 0 := by unfold pexp; exact_mod_cast (by omega : (2 * k : ℕ) ≠ 0)
  have hc0 : ((pexp k)⁻¹ : ℝ) ≠ 0 := by
    intro hc
    exact hpne (inv_eq_zero.mp hc)
  exact Real.zero_rpow hc0

/-- `(fSm u)^p = sNat u`. -/
lemma fSm_pow_sNat (A : Finset V) (k : ℕ) (hk : 1 ≤ k) (u : V) :
    (fSm A k u) ^ (pexp k) = sNat A k u := by
  unfold fSm
  have hkp : pexp k ≠ 0 := by unfold pexp; exact_mod_cast (by omega : (2 * k : ℕ) ≠ 0)
  have h0 : 0 ≤ sNat A k u := sNat_nonneg A k u
  calc
    (sNat A k u ^ (pexp k)⁻¹) ^ (pexp k) = sNat A k u ^ (((pexp k)⁻¹) * (pexp k)) := by
        rw [← Real.rpow_mul h0 ((pexp k)⁻¹) (pexp k)]
    _ = sNat A k u := by
        rw [inv_mul_cancel₀ hkp]
        rw [Real.rpow_one]

lemma fSm_pow_sum_abs (A : Finset V) (k : ℕ) (hk : 1 ≤ k) (u : V) :
    (fSm A k u) ^ (pexp k) = ∑ a ∈ A, |inner ℝ u a| ^ (pexp k) := by
  rw [fSm_pow_sNat A k hk u, sNat_eq_sum_abs_pow]

lemma fSm_pos_of_span (A : Finset V) (k : ℕ) (hk : 1 ≤ k) (u : V) (hu : u ≠ 0)
    (hspan : ∃ a ∈ A, inner ℝ u a ≠ 0) : 0 < fSm A k u := by
  unfold fSm
  exact Real.rpow_pos_of_pos (sNat_pos_of_span A k hk u hu hspan) _

/-- The exponent `pexp k` is at least `2` and greater than `1`. -/
lemma pexp_ge_two (k : ℕ) (hk : 1 ≤ k) : (2 : ℝ) ≤ pexp k := by
  unfold pexp
  exact_mod_cast (by omega : 2 ≤ 2 * k)

lemma pexp_gt_one (k : ℕ) (hk : 1 ≤ k) : (1 : ℝ) < pexp k := by
  unfold pexp
  exact_mod_cast (by omega : (1 : ℕ) < 2 * k)

/-- inner product is ℝ-linear in the first argument (helper for sums). -/
lemma inner_sum_left_linear (A : Finset V) (y : V → ℝ) (w : V) :
    inner ℝ (∑ a ∈ A, (y a) • a) w = ∑ a ∈ A, y a * inner ℝ a w := by
  let L : V →L[ℝ] ℝ := innerSL ℝ w
  have hL : ∀ x : V, L x = inner ℝ x w := by
    intro x
    simp [L, real_inner_comm]
  calc
    inner ℝ (∑ a ∈ A, (y a) • a) w = L (∑ a ∈ A, (y a) • a) := by rw [hL]
    _ = ∑ a ∈ A, L ((y a) • a) := by simp [map_sum]
    _ = ∑ a ∈ A, y a * inner ℝ a w := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [← hL]
        simp [L]

/-- For `u ≠ 0` (with the net spanning in direction `u`) there is a point of
`Xset` with inner product `fSm A k u` with `u`. -/
lemma Xset_witness {A : Finset V} {k : ℕ} (hk : 1 ≤ k) (u : V) (hu : u ≠ 0)
    (hspan : ∃ a ∈ A, inner ℝ u a ≠ 0) :
    ∃ x0 : V, x0 ∈ Xset A k ∧ inner ℝ x0 u = fSm A k u := by
  classical
  let z : V → ℝ := fun a => inner ℝ u a
  let N : ℝ := fSm A k u
  let y : V → ℝ := yvec A (pexp k) z N
  let x0 : V := ∑ a ∈ A, (y a) • a
  have hp2 : (2 : ℝ) ≤ pexp k := pexp_ge_two k hk
  have hNpos : 0 < N := by
    dsimp [N]
    exact fSm_pos_of_span A k hk u hu hspan
  have hNpow : N ^ (pexp k) = ∑ a ∈ A, |z a| ^ (pexp k) := by
    dsimp [N, z]
    exact fSm_pow_sum_abs A k hk u
  have hz1 : ∑ a ∈ A, z a * y a = N := by
    dsimp [y]
    exact sum_zy_eq A hp2 z hNpos hNpow
  have hone : ∑ a ∈ A, |y a| ^ ((pexp k) / ((pexp k) - 1)) = 1 := by
    dsimp [y]
    exact sum_abs_y_eq_one A hp2 z hNpos hNpow
  have hmem : x0 ∈ Xset A k := by
    intro w
    calc
      inner ℝ x0 w = ∑ a ∈ A, y a * inner ℝ a w := by
          dsimp [x0]
          exact inner_sum_left_linear A y w
      _ ≤ (∑ a ∈ A, |y a| ^ ((pexp k) / ((pexp k) - 1))) ^ (1 / ((pexp k) / ((pexp k) - 1)))
          * (∑ a ∈ A, |inner ℝ a w| ^ (pexp k)) ^ (1 / (pexp k)) := by
          have hpq : (pexp k).HolderConjugate ((pexp k) / ((pexp k) - 1)) := by
            exact Real.HolderConjugate.conjExponent (pexp_gt_one k hk)
          have hH := Real.inner_le_Lp_mul_Lq (s := A) (f := fun a => y a)
            (g := fun a => inner ℝ a w) hpq.symm
          simpa using hH
      _ = 1 * (∑ a ∈ A, |inner ℝ a w| ^ (pexp k)) ^ (1 / (pexp k)) := by
          rw [hone]
          rw [Real.one_rpow]
      _ = fSm A k w := by
          have hswap : (∑ a ∈ A, |inner ℝ a w| ^ (pexp k)) = ∑ a ∈ A, |inner ℝ w a| ^ (pexp k) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [real_inner_comm]
          have hfac : (∑ a ∈ A, |inner ℝ a w| ^ (pexp k)) ^ (1 / (pexp k)) = fSm A k w := by
            calc
              (∑ a ∈ A, |inner ℝ a w| ^ (pexp k)) ^ (1 / (pexp k))
                  = (∑ a ∈ A, |inner ℝ w a| ^ (pexp k)) ^ (1 / (pexp k)) := by rw [hswap]
              _ = (∑ a ∈ A, |inner ℝ w a| ^ (pexp k)) ^ ((pexp k)⁻¹) := by
                  congr 1
                  rw [one_div]
              _ = fSm A k w := by
                  exact (fSm_eq_rpow_sum A k w).symm
          rw [hfac]
          ring
  have hin : inner ℝ x0 u = N := by
    calc
      inner ℝ x0 u = ∑ a ∈ A, y a * inner ℝ a u := by
          dsimp [x0]
          exact inner_sum_left_linear A y u
      _ = ∑ a ∈ A, y a * z a := by
          apply Finset.sum_congr rfl
          intro a ha
          dsimp [z]
          rw [real_inner_comm]
      _ = N := by
          rw [← hz1]
          apply Finset.sum_congr rfl
          intro a ha
          ring
  refine ⟨x0, hmem, ?_⟩
  simpa [hin, N]

/-- The support value of `XB` in the zero direction is `0`. -/
lemma supFun_XB_zero (A : Finset V) (k : ℕ) (hk : 1 ≤ k) :
    supFun ((XB A k hk : ConvexBody V) : Set V) (0 : V) = 0 := by
  unfold supFun
  apply le_antisymm
  · apply csSup_le
    · exact Set.image_nonempty.mpr ⟨0, Xset_zero_mem A k⟩
    · rintro b ⟨x, hx, rfl⟩
      simp
  · have hmem : (0 : ℝ) ∈ (fun x : V => inner ℝ (0 : V) x) '' ((XB A k hk : ConvexBody V) : Set V) := by
      refine ⟨0, ?_, by simp⟩
      rw [XB_coe]
      exact Xset_zero_mem A k
    exact le_csSup (by
      refine ⟨0, ?_⟩
      rintro b ⟨x, hx, rfl⟩
      simp) hmem

/-- The support function of `XB` is exactly `fSm`. -/
lemma support_XB (A : Finset V) (k : ℕ) (hk : 1 ≤ k)
    (hspan : ∀ u : V, u ≠ 0 → ∃ a ∈ A, inner ℝ u a ≠ 0) :
    ∀ u : V, supFun ((XB A k hk : ConvexBody V) : Set V) u = fSm A k u := by
  intro u
  by_cases hu : u = 0
  · subst u
    rw [supFun_XB_zero A k hk]
    exact (fSm_zero A k hk).symm
  · apply le_antisymm
    · unfold supFun
      apply csSup_le
      · exact Set.image_nonempty.mpr ⟨0, by rw [XB_coe]; exact Xset_zero_mem A k⟩
      · rintro b ⟨x, hx, rfl⟩
        have hx' : x ∈ Xset A k := by simpa [XB_coe] using hx
        simpa [real_inner_comm] using (hx' u)
    · obtain ⟨x0, hmem, hin⟩ := Xset_witness hk u hu (hspan u hu)
      have hmem' : x0 ∈ ((XB A k hk : ConvexBody V) : Set V) := by
        rw [XB_coe]
        exact hmem
      have hmemimg : fSm A k u ∈ (fun x : V => inner ℝ u x) '' ((XB A k hk : ConvexBody V) : Set V) := by
        refine ⟨x0, hmem', ?_⟩
        simpa [real_inner_comm] using hin
      unfold supFun
      exact le_csSup (by
        refine ⟨fSm A k u, ?_⟩
        rintro b ⟨x, hx, rfl⟩
        have hx' : x ∈ Xset A k := by simpa [XB_coe] using hx
        simpa [real_inner_comm] using (hx' u)) hmemimg

/-- The support function of `XB` is smooth away from the origin. -/
lemma contDiffOn_support_XB (A : Finset V) (k : ℕ) (hk : 1 ≤ k)
    (hspan : ∀ u : V, u ≠ 0 → ∃ a ∈ A, inner ℝ u a ≠ 0) :
    ContDiffOn ℝ ⊤ (fun u : V => supFun ((XB A k hk : ConvexBody V) : Set V) u)
      {u : V | u ≠ 0} := by
  rw [show (fun u : V => supFun ((XB A k hk : ConvexBody V) : Set V) u) = fSm A k by
    funext u
    exact support_XB A k hk hspan u]
  exact contDiffOn_fSm (k := k) hk hspan

/-- `fSm` dominates the inner product with any single net vector. -/
lemma fSm_ge_inner (A : Finset V) (k : ℕ) (hk : 1 ≤ k) (u : V) (a : V) (ha : a ∈ A) :
    |inner ℝ u a| ≤ fSm A k u := by
  have hkp : (pexp k) ≠ 0 := by unfold pexp; exact_mod_cast (by omega : (2 * k : ℕ) ≠ 0)
  have hn : ∀ b ∈ A, 0 ≤ (inner ℝ u b) ^ (2 * k) := by
    intro b hb
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg (inner ℝ u b)) k
  have hle : (inner ℝ u a) ^ (2 * k) ≤ sNat A k u := by
    unfold sNat
    exact Finset.single_le_sum (s := A) (f := fun b : V => (inner ℝ u b) ^ (2 * k)) hn ha
  have hmono : ((inner ℝ u a) ^ (2 * k)) ^ ((pexp k)⁻¹) ≤ fSm A k u := by
    unfold fSm
    exact Real.rpow_le_rpow (hn a ha) hle (by exact le_of_lt (inv_pos.mpr (by unfold pexp; positivity)))
  have hroot : ((inner ℝ u a) ^ (2 * k)) ^ ((pexp k)⁻¹) = |inner ℝ u a| := by
    calc
      ((inner ℝ u a) ^ (2 * k)) ^ ((pexp k)⁻¹)
          = (|inner ℝ u a| ^ (pexp k)) ^ ((pexp k)⁻¹) := by
              congr 1
              exact (abs_rpow_even_eq_pow (inner ℝ u a) k).symm
      _ = |inner ℝ u a| ^ ((pexp k) * ((pexp k)⁻¹)) := by
          rw [← Real.rpow_mul (abs_nonneg (inner ℝ u a)) (pexp k) ((pexp k)⁻¹)]
      _ = |inner ℝ u a| := by
          rw [mul_inv_cancel₀ hkp]
          rw [Real.rpow_one]
  rw [← hroot]
  exact hmono
/-! ### Approximation estimates -/

/-- support value of a convex body in a direction (sSup-form). -/
def supportVal (L : ConvexBody V) (u : V) : ℝ := supFun (L : Set V) u

lemma bddAbove_inner_image (L : ConvexBody V) (u : V) :
    BddAbove ((fun x : V => inner ℝ u x) '' (L : Set V)) := by
  refine IsCompact.bddAbove_image L.isCompact ?_
  exact ((innerSL ℝ u).continuous).continuousOn

lemma inner_le_supportVal (L : ConvexBody V) {x : V} (hx : x ∈ (L : Set V)) (u : V) :
    inner ℝ u x ≤ supportVal L u := by
  unfold supportVal supFun
  exact le_csSup (bddAbove_inner_image L u) ⟨x, hx, rfl⟩

lemma abs_inner_le_supportVal (L : ConvexBody V) (u : V) (a : V) (ha : a ∈ (L : Set V))
    (hna : -a ∈ (L : Set V)) : |inner ℝ u a| ≤ supportVal L u := by
  rw [abs_le]
  constructor
  · have h2 := inner_le_supportVal L hna u
    rw [show inner ℝ u (-a) = -inner ℝ u a by simp] at h2
    linarith
  · exact inner_le_supportVal L ha u

lemma supportVal_nonneg (L : ConvexBody V) (h0 : (0 : V) ∈ (L : Set V)) (u : V) :
    0 ≤ supportVal L u := by
  have h := inner_le_supportVal L h0 u
  simpa using h

lemma supportVal_le_norm_bound (L : ConvexBody V) (u : V) (R : ℝ)
    (hR : ∀ x : V, x ∈ (L : Set V) → ‖x‖ ≤ R) : supportVal L u ≤ R * ‖u‖ := by
  unfold supportVal supFun
  apply csSup_le
  · exact Set.image_nonempty.mpr L.nonempty
  · rintro b ⟨x, hx, rfl⟩
    calc
      inner ℝ u x ≤ ‖u‖ * ‖x‖ := real_inner_le_norm u x
      _ = ‖x‖ * ‖u‖ := by rw [mul_comm]
      _ ≤ R * ‖u‖ := mul_le_mul_of_nonneg_right (hR x hx) (norm_nonneg u)

/-- `(x^p)^(1/p) = x` for `x ≥ 0`. -/
lemma rpow_root_id (x : ℝ) (hx : 0 ≤ x) (p : ℝ) (hp : p ≠ 0) : (x ^ p) ^ (p⁻¹) = x := by
  rw [← Real.rpow_mul hx p (p⁻¹)]
  rw [mul_inv_cancel₀ hp]
  rw [Real.rpow_one]

/-- upper estimate: `fSm A k u ≤ m^{1/p} * support L u` when `A ⊆ L` is symmetric
and `0 ∈ L`. -/
lemma fSm_le_card_mul_support (A : Finset V) (k : ℕ) (hk : 1 ≤ k) (L : ConvexBody V)
    (h0L : (0 : V) ∈ (L : Set V)) (hAsub : ∀ a ∈ A, a ∈ (L : Set V))
    (hAsym : ∀ a ∈ A, -a ∈ (L : Set V)) (u : V) :
    fSm A k u ≤ (A.card : ℝ) ^ ((pexp k)⁻¹) * supportVal L u := by
  have hkp : pexp k ≠ 0 := by unfold pexp; exact_mod_cast (by omega : (2 * k : ℕ) ≠ 0)
  have hcpos : 0 < (pexp k)⁻¹ := inv_pos.mpr (by unfold pexp; positivity)
  have hs0 : 0 ≤ supportVal L u := supportVal_nonneg L h0L u
  have hle_s : ∀ a ∈ A, (inner ℝ u a) ^ (2 * k) ≤ (supportVal L u) ^ (2 * k) := by
    intro a ha
    have hia : |inner ℝ u a| ≤ supportVal L u :=
      abs_inner_le_supportVal L u a (hAsub a ha) (hAsym a ha)
    calc
      (inner ℝ u a) ^ (2 * k) = |inner ℝ u a| ^ (2 * k) := pow_two_mul_eq_abs _ k
      _ ≤ (supportVal L u) ^ (2 * k) := pow_le_pow_left₀ (abs_nonneg _) hia (2 * k)
  have hsum : sNat A k u ≤ (A.card : ℝ) * (supportVal L u) ^ (2 * k) := by
    calc
      sNat A k u = ∑ a ∈ A, (inner ℝ u a) ^ (2 * k) := rfl
      _ ≤ ∑ a ∈ A, (supportVal L u) ^ (2 * k) := by
          exact Finset.sum_le_sum (fun a ha => hle_s a ha)
      _ = (A.card : ℝ) * (supportVal L u) ^ (2 * k) := by simp
  have hfp : (fSm A k u) ^ (pexp k) ≤ (A.card : ℝ) * (supportVal L u) ^ (2 * k) := by
    calc
      (fSm A k u) ^ (pexp k) = sNat A k u := fSm_pow_sNat A k hk u
      _ ≤ (A.card : ℝ) * (supportVal L u) ^ (2 * k) := hsum
  have hfs0pow : 0 ≤ (fSm A k u) ^ (pexp k) := by
    rw [fSm_pow_sNat A k hk u]
    exact sNat_nonneg A k u
  have hrootlast : ((supportVal L u) ^ (2 * k)) ^ ((pexp k)⁻¹) = supportVal L u := by
    rw [← Real.rpow_natCast]
    exact rpow_root_id (supportVal L u) hs0 (pexp k) hkp
  have hroot1 : fSm A k u = (fSm A k u ^ (pexp k)) ^ ((pexp k)⁻¹) := by
    symm
    exact rpow_root_id (fSm A k u) (fSm_nonneg A k u) (pexp k) hkp
  calc
    fSm A k u = (fSm A k u ^ (pexp k)) ^ ((pexp k)⁻¹) := hroot1
    _ ≤ ((A.card : ℝ) * (supportVal L u) ^ (2 * k)) ^ ((pexp k)⁻¹) := by
        exact Real.rpow_le_rpow hfs0pow hfp hcpos.le
    _ = (A.card : ℝ) ^ ((pexp k)⁻¹) * supportVal L u := by
        have hm0 : 0 ≤ (A.card : ℝ) := Nat.cast_nonneg _
        rw [Real.mul_rpow hm0 (pow_nonneg hs0 (2 * k))]
        rw [hrootlast]

/-- lower estimate: for a unit vector `u`, `support L u − δ ≤ fSm A k u` when `A`
is a δ-dense subset of the compact `L`. -/
lemma fSm_ge_support_sub (A : Finset V) (k : ℕ) (hk : 1 ≤ k) (L : ConvexBody V)
    (δ : ℝ) (hδ : 0 ≤ δ) (hAdense : ∀ x ∈ (L : Set V), ∃ a ∈ A, dist x a < δ)
    (u : V) (hu : ‖u‖ = 1) : supportVal L u - δ ≤ fSm A k u := by
  obtain ⟨x0, hx0L, hmax⟩ := L.isCompact.exists_isMaxOn (s := (L : Set V)) L.nonempty
    (f := fun x : V => inner ℝ u x) (by exact ((innerSL ℝ u).continuous).continuousOn)
  have hx0eq : supportVal L u = inner ℝ u x0 := by
    apply le_antisymm
    · unfold supportVal supFun
      apply csSup_le
      · exact Set.image_nonempty.mpr L.nonempty
      · rintro b ⟨x, hx, rfl⟩
        exact hmax hx
    · exact inner_le_supportVal L hx0L u
  obtain ⟨a, haA, hadist⟩ := hAdense x0 hx0L
  have hfge : |inner ℝ u a| ≤ fSm A k u := fSm_ge_inner A k hk u a haA
  have hle1 : inner ℝ u x0 - inner ℝ u a ≤ ‖u‖ * dist x0 a := by
    calc
      inner ℝ u x0 - inner ℝ u a = inner ℝ u (x0 - a) := by rw [inner_sub_right]
      _ ≤ ‖u‖ * ‖x0 - a‖ := real_inner_le_norm u (x0 - a)
      _ = ‖u‖ * dist x0 a := by rw [dist_eq_norm]
  have hlt : inner ℝ u x0 - inner ℝ u a < δ := by
    calc
      inner ℝ u x0 - inner ℝ u a ≤ ‖u‖ * dist x0 a := hle1
      _ = dist x0 a := by rw [hu, one_mul]
      _ < δ := hadist
  calc
    supportVal L u - δ ≤ inner ℝ u x0 - δ := by rw [hx0eq]
    _ ≤ inner ℝ u a := by linarith
    _ ≤ |inner ℝ u a| := le_abs_self _
    _ ≤ fSm A k u := hfge

/-- two-sided support difference bound at a unit vector. -/
lemma abs_fSm_sub_support (A : Finset V) (k : ℕ) (hk : 1 ≤ k) (L : ConvexBody V)
    (h0L : (0 : V) ∈ (L : Set V)) (hAsub : ∀ a ∈ A, a ∈ (L : Set V))
    (hAsym : ∀ a ∈ A, -a ∈ (L : Set V)) (δ η : ℝ)
    (hAdense : ∀ x ∈ (L : Set V), ∃ a ∈ A, dist x a < δ)
    (R : ℝ) (hR0 : 0 ≤ R) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hR : ∀ x : V, x ∈ (L : Set V) → ‖x‖ ≤ R)
    (hmc : (A.card : ℝ) ^ ((pexp k)⁻¹) ≤ 1 + η)
    {u : V} (hu : ‖u‖ = 1) :
    |fSm A k u - supportVal L u| ≤ δ + η * (R + 1) := by
  let s : ℝ := supportVal L u
  have hs0 : 0 ≤ s := supportVal_nonneg L h0L u
  have hsR : s ≤ R := by
    calc
      s ≤ R * ‖u‖ := by dsimp [s]; exact supportVal_le_norm_bound L u R hR
      _ = R := by rw [hu, mul_one]
  have hfs : fSm A k u ≤ (A.card : ℝ) ^ ((pexp k)⁻¹) * s := by
    dsimp [s]
    exact fSm_le_card_mul_support A k hk L h0L hAsub hAsym u
  have hfs' : fSm A k u ≤ (1 + η) * s := by
    calc
      fSm A k u ≤ (A.card : ℝ) ^ ((pexp k)⁻¹) * s := hfs
      _ ≤ (1 + η) * s := mul_le_mul_of_nonneg_right hmc hs0
  have hlow : s - δ ≤ fSm A k u := by
    dsimp [s]
    exact fSm_ge_support_sub A k hk L δ hδ hAdense u hu
  have hup : fSm A k u - s ≤ η * (R + 1) := by
    have h1 : fSm A k u - s ≤ η * s := by nlinarith
    have h2 : η * s ≤ η * R := mul_le_mul_of_nonneg_left hsR hη
    have h3 : η * R ≤ η * (R + 1) := by
      exact mul_le_mul_of_nonneg_left (by linarith) hη
    exact le_trans (le_trans h1 h2) h3
  have hnonneg : 0 ≤ η * (R + 1) := mul_nonneg hη (by linarith)
  have hA : fSm A k u - supportVal L u ≤ δ + η * (R + 1) := by nlinarith [hup, hδ]
  have hB : supportVal L u - fSm A k u ≤ δ + η * (R + 1) := by nlinarith [hlow, hnonneg]
  rw [abs_sub_le_iff]
  constructor
  · exact hA
  · exact hB
/-! ### Nets, spanning and the final theorem -/

/-- The parallel body contains the ball of radius `δ`. -/
lemma ball_subset_parallel (K : ConvexBody V) (hK0 : (0 : V) ∈ (K : Set V)) (δ : ℝ)
    (hδ : 0 ≤ δ) :
    (closedBall (0 : V) δ : Set V) ⊆
      ((K + δ • ballBody V : ConvexBody V) : Set V) := by
  intro x hx
  rw [ConvexBody.coe_add, ConvexBody.coe_smul]
  refine ⟨0, hK0, x, ?_, by simp⟩
  rw [Set.mem_smul_set]
  rw [mem_closedBall_zero_iff] at hx
  by_cases h0 : δ = 0
  · subst h0
    have : x = 0 := by simpa using hx
    subst x
    exact ⟨0, (ballBody_mem (0 : V)).mpr (by norm_num), by simp⟩
  · have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm h0)
    refine ⟨δ⁻¹ • x, ?_, ?_⟩
    · rw [ballBody_mem]
      calc
        ‖δ⁻¹ • x‖ = |δ⁻¹| * ‖x‖ := norm_smul _ _
        _ = δ⁻¹ * ‖x‖ := by rw [abs_of_nonneg (inv_nonneg.mpr hδ)]
        _ ≤ 1 := by
            rw [mul_comm]
            exact (div_le_iff₀ hδpos).mpr (by simpa [div_eq_mul_inv, mul_comm] using hx)
    · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hδpos), one_smul]

/-- The original body is contained in the parallel body. -/
lemma K_subset_parallel (K : ConvexBody V) (hK0 : (0 : V) ∈ (K : Set V)) (δ : ℝ)
    (hδ : 0 ≤ δ) : (K : Set V) ⊆ ((K + δ • ballBody V : ConvexBody V) : Set V) := by
  have h0 : (0 : V) ∈ δ • (ballBody V : Set V) := by
    rw [Set.mem_smul_set]
    exact ⟨0, (ballBody_mem (0 : V)).mpr (by norm_num), by simp⟩
  intro x hx
  rw [ConvexBody.coe_add, ConvexBody.coe_smul]
  exact ⟨x, hx, 0, h0, by simp⟩

/-- membership of zero in the parallel body. -/
lemma zero_mem_parallel (K : ConvexBody V) (hK0 : (0 : V) ∈ (K : Set V)) (δ : ℝ)
    (hδ : 0 ≤ δ) : (0 : V) ∈ ((K + δ • ballBody V : ConvexBody V) : Set V) :=
  K_subset_parallel K hK0 δ hδ hK0

/-- A finite symmetric `δ`-dense subset of a compact symmetric nonempty set. -/
lemma exists_symmetric_dense_net' {C : Set V} (hC : IsCompact C) (hCneg : C = -C)
    (hCn : C.Nonempty) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : Finset V, (∀ a ∈ A, a ∈ C) ∧ (∀ a ∈ A, -a ∈ A) ∧
      ∀ x ∈ C, ∃ a ∈ A, dist x a < δ := by
  classical
  obtain ⟨A0, hA0sub, hA0dense⟩ := exists_finite_dense hC hCn δ hδ
  let A : Finset V := A0 ∪ (A0.image (fun x => -x))
  refine ⟨A, ?_, ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_union] at ha
    rcases ha with haA0 | himg
    · exact hA0sub a haA0
    · rcases Finset.mem_image.mp himg with ⟨b, hbA0, hba⟩
      rw [← hba]
      have hbC : b ∈ C := hA0sub b hbA0
      have hbm : b ∈ -C := by
        rw [hCneg] at hbC
        exact hbC
      exact Set.mem_neg.mp hbm
  · intro a ha
    rw [Finset.mem_union] at ha
    rcases ha with haA0 | himg
    · rw [Finset.mem_union]
      right
      exact Finset.mem_image.mpr ⟨a, haA0, by simp⟩
    · rcases Finset.mem_image.mp himg with ⟨b, hbA0, hba⟩
      rw [Finset.mem_union]
      left
      rw [← hba]
      simpa using hbA0
  · intro x hx
    rcases hA0dense x hx with ⟨a, haA0, hda⟩
    refine ⟨a, ?_, hda⟩
    rw [Finset.mem_union]
    left
    exact haA0

/-- A δ₁-dense net of a body containing the ball of radius δ₀ > δ₁ spans. -/
lemma net_span (A : Finset V) (K : ConvexBody V) (hK0 : (0 : V) ∈ (K : Set V))
    (δ₀ δ₁ : ℝ) (hδ0 : 0 < δ₀) (hδ1 : 0 < δ₁) (hδlt : δ₁ < δ₀)
    (hAdense : ∀ x ∈ ((K + δ₀ • ballBody V : ConvexBody V) : Set V), ∃ a ∈ A, dist x a < δ₁)
    (u : V) (hu : u ≠ 0) : ∃ a ∈ A, inner ℝ u a ≠ 0 := by
  classical
  by_contra hnone
  have hall : ∀ a ∈ A, inner ℝ u a = 0 := by
    intro a ha
    by_contra hz
    exact hnone ⟨a, ha, hz⟩
  let e : V := (‖u‖⁻¹) • u
  have he1 : ‖e‖ = 1 := by
    have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
    calc
      ‖e‖ = ‖‖u‖⁻¹ • u‖ := rfl
      _ = |‖u‖⁻¹| * ‖u‖ := norm_smul _ _
      _ = ‖u‖⁻¹ * ‖u‖ := by rw [abs_of_nonneg (inv_nonneg.mpr hu0.le)]
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hu0)
  let p : V := δ₀ • e
  have hball : p ∈ (closedBall (0 : V) δ₀ : Set V) := by
    rw [mem_closedBall_zero_iff]
    calc
      ‖p‖ = |δ₀| * ‖e‖ := by simp [p, norm_smul]
      _ = δ₀ := by rw [abs_of_nonneg hδ0.le, he1, mul_one]
      _ ≤ δ₀ := le_rfl
  have hpK : p ∈ ((K + δ₀ • ballBody V : ConvexBody V) : Set V) :=
    ball_subset_parallel K hK0 δ₀ hδ0.le hball
  obtain ⟨a, haA, hadist⟩ := hAdense p hpK
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hin_e : inner ℝ u e = ‖u‖ := by
    calc
      inner ℝ u e = inner ℝ u ((‖u‖⁻¹) • u) := rfl
      _ = (‖u‖⁻¹) * inner ℝ u u := by rw [inner_smul_right]
      _ = (‖u‖⁻¹) * ‖u‖ ^ 2 := by simp
      _ = ‖u‖ := by
          rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hu0), one_mul]
  have hin_p : inner ℝ u p = δ₀ * ‖u‖ := by
    calc
      inner ℝ u p = inner ℝ u (δ₀ • e) := rfl
      _ = δ₀ * inner ℝ u e := by rw [inner_smul_right]
      _ = δ₀ * ‖u‖ := by rw [hin_e]
  have hbd : |inner ℝ u p - inner ℝ u a| ≤ ‖u‖ * dist p a := by
    calc
      |inner ℝ u p - inner ℝ u a| = |inner ℝ u (p - a)| := by
          congr 1
          rw [inner_sub_right]
      _ ≤ ‖u‖ * ‖p - a‖ := by
          have h := norm_inner_le_norm (𝕜 := ℝ) u (p - a)
          simpa using h
      _ = ‖u‖ * dist p a := by rw [dist_eq_norm]
  have hmain : δ₀ * ‖u‖ ≤ δ₁ * ‖u‖ := by
    calc
      δ₀ * ‖u‖ = |inner ℝ u p - inner ℝ u a| := by
          rw [hin_p, hall a haA, sub_zero]
          exact (abs_of_nonneg (mul_nonneg hδ0.le hu0.le)).symm
      _ ≤ ‖u‖ * dist p a := hbd
      _ ≤ ‖u‖ * δ₁ := mul_le_mul_of_nonneg_left (le_of_lt hadist) hu0.le
      _ = δ₁ * ‖u‖ := by rw [mul_comm]
  exact (not_lt_of_ge hmain) (mul_lt_mul_of_pos_right hδlt hu0)

/-- Hausdorff distance bound from support differences over unit vectors. -/
lemma dist_le_of_support_bound {X L : ConvexBody V} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ u : V, ‖u‖ = 1 → |supportVal X u - supportVal L u| ≤ C) :
    dist X L ≤ C := by
  rw [hausdorffDist_eq_sSup_support V X L]
  change sSup (HausdorffSupport.supportSet X L) ≤ C
  cases (HausdorffSupport.supportSet X L).eq_empty_or_nonempty with
  | inl h0 => rw [h0, Real.sSup_empty]; exact hC
  | inr hn =>
      apply csSup_le hn
      intro r hr
      rcases hr with ⟨u, hu, hr⟩
      rw [hr]
      simpa [HausdorffSupport.support, supportVal, supFun] using h u hu
/-! ### The density theorem -/

/-- Schneider, Convex Bodies, Thm 3.4.1 (origin-symmetric case): every
origin-symmetric convex body is a Hausdorff limit of origin-symmetric convex
bodies whose support functions are `C∞` away from the origin. -/
theorem smoothCentred_dense
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] (K : ConvexBody V)
    (hK : (K : Set V) = -(K : Set V)) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ConvexBody V,
      dist X K < ε ∧ (X : Set V) = -(X : Set V) ∧
      ContDiffOn ℝ ⊤ (fun u : V => sSup ((fun x : V => inner ℝ u x) '' (X : Set V)))
        {u : V | u ≠ 0} := by
  classical
  let δ₀ : ℝ := ε / 4
  let δ₁ : ℝ := ε / 16
  have hε0 : 0 ≤ ε := le_of_lt hε
  have hδ0pos : 0 < δ₀ := by dsimp [δ₀]; linarith
  have hδ1pos : 0 < δ₁ := by dsimp [δ₁]; linarith
  have hδ1lt : δ₁ < δ₀ := by dsimp [δ₀, δ₁]; linarith
  have hK0 : (0 : V) ∈ (K : Set V) := zero_mem_of_symm K hK
  let K' : ConvexBody V := K + δ₀ • ballBody V
  have hK'symm : ((K' : ConvexBody V) : Set V) = -((K' : ConvexBody V) : Set V) := by
    dsimp [K']
    exact parallel_body_symm K hK δ₀ hδ0pos.le
  have hdist0 : dist K' K ≤ δ₀ := by
    dsimp [K']
    exact dist_parallel_le K hK0 δ₀ hδ0pos.le
  have h0K' : (0 : V) ∈ ((K' : ConvexBody V) : Set V) := by
    dsimp [K']
    exact zero_mem_parallel K hK0 δ₀ hδ0pos.le
  obtain ⟨R, hRpos, hR⟩ := (K' : ConvexBody V).isBounded.exists_pos_norm_le
  have hR0 : 0 ≤ R := le_of_lt hRpos
  have hR1 : R + 1 ≠ 0 := by nlinarith
  obtain ⟨A, hAsub, hAsym, hAdense⟩ :=
    exists_symmetric_dense_net' (C := ((K' : ConvexBody V) : Set V))
      ((K' : ConvexBody V).isCompact) hK'symm ((K' : ConvexBody V).nonempty)
      δ₁ hδ1pos
  have hspan : ∀ u : V, u ≠ 0 → ∃ a ∈ A, inner ℝ u a ≠ 0 := by
    intro u hu
    exact net_span A K hK0 δ₀ δ₁ hδ0pos hδ1pos hδ1lt
      (by simpa [K'] using hAdense) u hu
  have hAn : A.Nonempty := by
    rcases (K' : ConvexBody V).nonempty with ⟨x, hx⟩
    rcases hAdense x hx with ⟨a, ha, _⟩
    exact ⟨a, ha⟩
  have hm1 : 1 ≤ A.card := by
    have h0 : 0 < A.card := (Finset.card_pos).mpr hAn
    omega
  let η0 : ℝ := ε / (16 * (R + 1))
  have hη0pos : 0 < η0 := by
    dsimp [η0]
    positivity
  obtain ⟨k, hk1, hrootlt⟩ :=
    Commons.Analysis.Real.rpow_root_tendsto_one A.card hm1 hη0pos
  have hmc : (A.card : ℝ) ^ ((pexp k)⁻¹) ≤ 1 + η0 := by
    change (A.card : ℝ) ^ (((2 * k : ℕ) : ℝ)⁻¹) ≤ 1 + η0
    exact le_of_lt hrootlt
  let X : ConvexBody V := XB A k hk1
  have hdist1 : dist X K' ≤ δ₁ + η0 * (R + 1) := by
    refine dist_le_of_support_bound (C := δ₁ + η0 * (R + 1)) ?_ ?_
    · have hη0 : 0 ≤ η0 := le_of_lt hη0pos
      nlinarith
    · intro u hu
      have hsX : supportVal X u = fSm A k u := by
        dsimp [X, supportVal]
        exact support_XB A k hk1 hspan u
      calc
        |supportVal X u - supportVal K' u| = |fSm A k u - supportVal K' u| := by rw [hsX]
        _ ≤ δ₁ + η0 * (R + 1) :=
            abs_fSm_sub_support A k hk1 K' h0K' hAsub
              (fun a ha => hAsub (-a) (hAsym a ha)) δ₁ η0 hAdense R hR0
              hδ1pos.le hη0pos.le hR hmc hu
  have hdist2 : dist X K < ε := by
    calc
      dist X K ≤ dist X K' + dist K' K := dist_triangle X K' K
      _ ≤ (δ₁ + η0 * (R + 1)) + δ₀ := add_le_add hdist1 hdist0
      _ < ε := by
          have hηmul : η0 * (R + 1) = ε / 16 := by
            dsimp [η0]
            field_simp [hR1]
          dsimp [δ₀, δ₁]
          rw [hηmul]
          ring_nf
          linarith
  have hsym : ((X : ConvexBody V) : Set V) = -((X : ConvexBody V) : Set V) := by
    dsimp [X]
    exact XB_symmetric A k hk1
  have hcd : ContDiffOn ℝ ⊤ (fun u : V => sSup ((fun x : V => inner ℝ u x) '' (X : Set V)))
      {u : V | u ≠ 0} := by
    simpa [X, supFun] using contDiffOn_support_XB A k hk1 hspan
  exact ⟨X, hdist2, hsym, hcd⟩