import Mathlib
import Submission.Work.EKLComp.EucDefs
import Submission.Work.EKLComp.ekl2_primitive_bezout

/-!
# A bounded ℤ-basis of a rank-two lattice with large minimum

Given two linearly independent vectors `u v : Fin 2 → ℝ`, the lattice `L = ℤu + ℤv` has
covolume `D = |det2 u v|` and, by hypothesis, every non-zero lattice vector has sup-norm
`≥ γ`.  We produce a ℤ-basis `(b₁, b₂)` of `L` (i.e. integer coefficient pairs with
determinant `±1`) with

`‖b₁‖, ‖b₂‖ ≤ √D + 2 + 2D/γ`.

The proof is the classical one: Minkowski's theorem gives a non-zero lattice vector of
sup-norm `≤ √D + 1`; dividing by the gcd of its coefficients and applying Bézout produces a
basis `(b₁, b₂)`; finally `b₂` is reduced modulo `b₁` along the `b₁`-direction, so that the
covolume identity `D² = ‖b₁‖₂²‖b₂‖₂² - ⟨b₁,b₂⟩²` bounds `‖b₂‖₂`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.EKLComp

open Matrix
open MeasureTheory

noncomputable section

/-! ## Elementary facts about `dot2`, `det2` and the norm of `Fin 2 → ℝ` -/

/-- The (sup) norm on `Fin 2 → ℝ` is the maximum of the absolute values of the entries. -/
theorem norm_fin2_eq (x : Fin 2 → ℝ) : ‖x‖ = max |x 0| |x 1| := by
  refine le_antisymm ?_ (max_le (norm_le_pi_norm x 0) (norm_le_pi_norm x 1))
  refine (pi_norm_le_iff_of_nonneg (G := fun _ : Fin 2 => ℝ)
    (le_max_of_le_left (abs_nonneg _))).mpr ?_
  intro i; fin_cases i <;> simp

/-- The sup norm is bounded by the Euclidean norm. -/
theorem norm_fin2_le_sqrt (x : Fin 2 → ℝ) : ‖x‖ ≤ Real.sqrt (dot2 x x) := by
  rw [show dot2 x x = x 0 ^ 2 + x 1 ^ 2 by simp only [dot2, Fin.sum_univ_two]; ring]
  rw [norm_fin2_eq]
  apply max_le
  · exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (x 1)])
  · exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (x 0)])

/-- The Euclidean norm is bounded by `√2` times the sup norm. -/
theorem sqrt_dot2_le_sqrt_two_mul_norm (x : Fin 2 → ℝ) :
    Real.sqrt (dot2 x x) ≤ Real.sqrt 2 * ‖x‖ := by
  rw [show dot2 x x = x 0 ^ 2 + x 1 ^ 2 by simp only [dot2, Fin.sum_univ_two]; ring]
  rw [norm_fin2_eq]
  have h0 : |x 0| ^ 2 ≤ (max |x 0| |x 1|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) 2
  have h1 : |x 1| ^ 2 ≤ (max |x 0| |x 1|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) 2
  have hle : x 0 ^ 2 + x 1 ^ 2 ≤ 2 * (max |x 0| |x 1|) ^ 2 := by
    rw [sq_abs] at h0 h1
    nlinarith
  calc Real.sqrt (x 0 ^ 2 + x 1 ^ 2) ≤ Real.sqrt (2 * (max |x 0| |x 1|) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt 2 * max |x 0| |x 1| := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq_eq_abs,
          abs_of_nonneg (le_max_of_le_left (abs_nonneg _))]

theorem dot2_add_left (x y z : Fin 2 → ℝ) : dot2 (x + y) z = dot2 x z + dot2 y z := by
  simp only [dot2, Fin.sum_univ_two, Pi.add_apply]; ring

theorem dot2_smul_left (a : ℝ) (x y : Fin 2 → ℝ) : dot2 (a • x) y = a * dot2 x y := by
  simp only [dot2, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]; ring

theorem dot2_sub_right (x y z : Fin 2 → ℝ) : dot2 x (y - z) = dot2 x y - dot2 x z := by
  simp only [dot2, Fin.sum_univ_two, Pi.sub_apply]; ring

theorem dot2_smul_right (a : ℝ) (x y : Fin 2 → ℝ) : dot2 x (a • y) = a * dot2 x y := by
  simp only [dot2, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]; ring

theorem dot2_self_nonneg (x : Fin 2 → ℝ) : 0 ≤ dot2 x x := by
  simp only [dot2, Fin.sum_univ_two]; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

theorem dot2_self_pos (x : Fin 2 → ℝ) : 0 < dot2 x x ↔ x ≠ 0 := by
  constructor
  · intro h hx; rw [hx] at h; simp [dot2] at h
  · intro hx
    simp only [dot2, Fin.sum_univ_two]
    have : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hh; push_neg at hh
      exact hx (by funext i; fin_cases i <;> simp [hh.1, hh.2])
    rcases this with h | h
    · nlinarith [sq_nonneg (x 1), sq_pos_of_ne_zero h]
    · nlinarith [sq_nonneg (x 0), sq_pos_of_ne_zero h]

/-- The Lagrange identity in dimension two. -/
theorem lagrange_identity (x y : Fin 2 → ℝ) :
    dot2 x x * dot2 y y - dot2 x y ^ 2 = det2 x y ^ 2 := by
  simp only [dot2, det2, Fin.sum_univ_two]; ring

/-- `det2` is alternating-bilinear; on combinations of `u` and `v` it is computed by the
determinant of the coefficient matrix. -/
theorem det2_expand (u v : Fin 2 → ℝ) (a b c d : ℝ) :
    det2 (a • u + b • v) (c • u + d • v) = (a * d - b * c) * det2 u v := by
  simp only [det2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem det2_self (x : Fin 2 → ℝ) : det2 x x = 0 := by
  simp only [det2]; ring

/-- Every real number is within `1/2` of an integer. -/
theorem exists_int_abs_sub_le_half (t : ℝ) : ∃ k : ℤ, |t - (k : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊t + 1 / 2⌋, ?_⟩
  have h1 : ((⌊t + 1 / 2⌋ : ℤ) : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have h2 : t + 1 / 2 < ((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]; constructor <;> linarith


/-- The volume of a closed ball in `Fin 2 → ℝ` (with the sup norm). -/
theorem volume_closedBall_fin2 (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.closedBall (0 : Fin 2 → ℝ) r) = ENNReal.ofReal (4 * r ^ 2) := by
  have hset : Metric.closedBall (0 : Fin 2 → ℝ) r
      = Set.univ.pi (fun _ : Fin 2 => Set.Icc (-r) r) := by
    ext x
    rw [Metric.mem_closedBall, dist_zero_right, Set.mem_univ_pi]
    constructor
    · intro hx i
      have h1 : |x i| ≤ r := by
        have h2 := norm_le_pi_norm x i
        rw [Real.norm_eq_abs] at h2
        linarith
      rw [Set.mem_Icc]
      exact abs_le.mp h1
    · intro hx
      have hr0 : 0 ≤ r := by have h := (hx 0).1; have h2 := (hx 0).2; linarith
      rw [pi_norm_le_iff_of_nonneg (G := fun _ : Fin 2 => ℝ) hr0]
      intro i
      rw [Real.norm_eq_abs]
      exact abs_le.mpr (hx i)
  rw [hset, volume_pi, Measure.pi_pi, Fin.prod_univ_two, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ r - -r)]
  congr 1
  ring

/-- **Minkowski**: a rank-two lattice of covolume `D` contains a non-zero vector of sup-norm
`≤ √D + 1`. -/
theorem exists_short_lattice_vector (u v : Fin 2 → ℝ) (hdet : det2 u v ≠ 0) :
    ∃ m n : ℤ, (m ≠ 0 ∨ n ≠ 0) ∧
      ‖((m : ℝ) • u + (n : ℝ) • v : Fin 2 → ℝ)‖ ≤ Real.sqrt |det2 u v| + 1 := by
  set w : Fin 2 → (Fin 2 → ℝ) := fun i => if i = 0 then u else v with hw
  have hli : LinearIndependent ℝ w := by
    rw [hw, Fintype.linearIndependent_iff]
    intro g hg i
    have hsum : g 0 • u + g 1 • v = 0 := by
      have h := hg
      rw [Fin.sum_univ_two] at h
      simpa using h
    have hu : g 0 = 0 := by
      have h := congrArg (fun z : Fin 2 → ℝ => det2 z v) hsum
      rw [show det2 ((0 : Fin 2 → ℝ)) v = 0 from by simp [det2]] at h
      have h2 : det2 (g 0 • u + g 1 • v) ((0 : ℝ) • u + (1 : ℝ) • v)
          = (g 0 * 1 - g 1 * 0) * det2 u v := det2_expand u v (g 0) (g 1) 0 1
      rw [zero_smul, one_smul, zero_add] at h2
      rw [h2] at h
      exact (mul_eq_zero.mp (by simpa using h)).resolve_right hdet
    have hv : g 1 = 0 := by
      have h := congrArg (fun z : Fin 2 → ℝ => det2 u z) hsum
      rw [show det2 u ((0 : Fin 2 → ℝ)) = 0 from by simp [det2]] at h
      have h2 : det2 ((1 : ℝ) • u + (0 : ℝ) • v) (g 0 • u + g 1 • v)
          = (1 * g 1 - 0 * g 0) * det2 u v := det2_expand u v 1 0 (g 0) (g 1)
      rw [one_smul, zero_smul, add_zero] at h2
      rw [h2] at h
      exact (mul_eq_zero.mp (by simpa using h)).resolve_right hdet
    fin_cases i
    · exact hu
    · exact hv
  set b : Module.Basis (Fin 2) ℝ (Fin 2 → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hli
      (by rw [Module.finrank_fintype_fun_eq_card]) with hb
  have hb0 : b 0 = u := by
    rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank, hw]
    simp
  have hb1 : b 1 = v := by
    rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank, hw]
    simp
  set L : AddSubgroup (Fin 2 → ℝ) := (Submodule.span ℤ (Set.range b)).toAddSubgroup with hL
  haveI hCount : Countable ↥L := by
    have hsurj : Function.Surjective
        (fun c : Fin 2 → ℤ => (⟨∑ i, c i • b i,
          Submodule.sum_mem _ fun i _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))⟩ : ↥L)) := by
      intro x
      have hx : (x : Fin 2 → ℝ) ∈ Submodule.span ℤ (Set.range b) := x.2
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
      exact ⟨c, Subtype.ext hc⟩
    exact hsurj.countable
  have hfund : IsAddFundamentalDomain ↥L (ZSpan.fundamentalDomain b) volume := by
    rw [hL]
    exact ZSpan.isAddFundamentalDomain' b volume
  have hvolF : volume (ZSpan.fundamentalDomain b) = ENNReal.ofReal |det2 u v| := by
    rw [ZSpan.volume_fundamentalDomain b]
    congr 1
    congr 1
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply]
    rw [hb0, hb1]
    simp only [det2]
  set r : ℝ := Real.sqrt |det2 u v| + 1 with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  have hmeas : volume (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ (Fin 2 → ℝ)
      < volume (Metric.closedBall (0 : Fin 2 → ℝ) r) := by
    rw [hvolF, volume_closedBall_fin2 r hrpos.le]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [show (2 : ENNReal) ^ 2 = 4 by norm_num, ← ENNReal.ofReal_ofNat (n := 4),
      ← ENNReal.ofReal_mul (abs_nonneg (det2 u v))]
    rw [ENNReal.ofReal_lt_ofReal_iff (by nlinarith [hrpos] : (0 : ℝ) < 4 * r ^ 2)]
    rw [hr]
    have h2 : (Real.sqrt |det2 u v| + 1) ^ 2
        = |det2 u v| + 2 * Real.sqrt |det2 u v| + 1 := by
      rw [add_sq, Real.sq_sqrt (abs_nonneg (det2 u v))]; ring
    rw [h2]
    nlinarith [Real.sqrt_nonneg |det2 u v|]
  have hsymm : ∀ x ∈ Metric.closedBall (0 : Fin 2 → ℝ) r,
      -x ∈ Metric.closedBall (0 : Fin 2 → ℝ) r := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    rwa [norm_neg]
  obtain ⟨x, hxne, hxmem⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (μ := volume) hfund hsymm (convex_closedBall 0 r) hmeas
  have hxn : ‖((x : ↥L) : Fin 2 → ℝ)‖ ≤ r := by
    rw [Metric.mem_closedBall, dist_zero_right] at hxmem
    exact hxmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp
    (show ((x : ↥L) : Fin 2 → ℝ) ∈ Submodule.span ℤ (Set.range b) from x.2)
  have hcx : ((x : ↥L) : Fin 2 → ℝ) = (c 0 : ℝ) • u + (c 1 : ℝ) • v := by
    rw [← hc, Fin.sum_univ_two, hb0, hb1, ← Int.cast_smul_eq_zsmul ℝ (c 0) u,
      ← Int.cast_smul_eq_zsmul ℝ (c 1) v]
  have hcnz : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨h0, h1⟩ := h
    exact hxne (Subtype.ext (by rw [hcx, h0, h1]; simp))
  exact ⟨c 0, c 1, hcnz, by rw [← hcx]; exact hxn⟩

/-! ## The main lemma -/

theorem exists_bounded_basis_rank2 (u v : Fin 2 → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hdet : Work.EKLComp.det2 u v ≠ 0)
    (hmin : ∀ m n : ℤ, (m ≠ 0 ∨ n ≠ 0) → γ ≤ ‖((m : ℝ) • u + (n : ℝ) • v : Fin 2 → ℝ)‖) :
    ∃ p q r s : ℤ, (p * s - q * r = 1 ∨ p * s - q * r = -1) ∧
      ‖((p : ℝ) • u + (q : ℝ) • v : Fin 2 → ℝ)‖ ≤
        Real.sqrt |Work.EKLComp.det2 u v| + 2 + 2 * |Work.EKLComp.det2 u v| / γ ∧
      ‖((r : ℝ) • u + (s : ℝ) • v : Fin 2 → ℝ)‖ ≤
        Real.sqrt |Work.EKLComp.det2 u v| + 2 + 2 * |Work.EKLComp.det2 u v| / γ := by
  have hDpos : 0 < |det2 u v| := abs_pos.mpr hdet
  have hDγ : 0 ≤ |det2 u v| / γ := div_nonneg (abs_nonneg _) hγ.le
  -- Step 1: a non-zero lattice vector of sup-norm `≤ √D + 1` (Minkowski).
  obtain ⟨m, n, hmn, hshort⟩ := exists_short_lattice_vector u v hdet
  -- Step 2: divide by the gcd and complete to a basis (Bézout).
  obtain ⟨p, q, r, s, g, hgpos, hmp, hnq, hbez⟩ := ekl2_primitive_bezout m n hmn
  have hg1 : (1 : ℤ) ≤ g := hgpos
  set b₁ : Fin 2 → ℝ := (p : ℝ) • u + (q : ℝ) • v with hb₁def
  set b₂ : Fin 2 → ℝ := (r : ℝ) • u + (s : ℝ) • v with hb₂def
  -- (p,q) ≠ 0
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra h
    push_neg at h
    obtain ⟨hp, hq⟩ := h
    rw [hp, mul_zero] at hmp
    rw [hq, mul_zero] at hnq
    rcases hmn with hm | hn
    · exact hm hmp
    · exact hn hnq
  -- bound on `‖b₁‖`
  have hb₁_bound : ‖b₁‖ ≤ Real.sqrt |det2 u v| + 1 := by
    have hscale : ((m : ℝ) • u + (n : ℝ) • v : Fin 2 → ℝ) = (g : ℝ) • b₁ := by
      have hmc : ((m : ℝ)) = (g : ℝ) * (p : ℝ) := by rw [hmp]; simp only [Int.cast_mul]
      have hnc : ((n : ℝ)) = (g : ℝ) * (q : ℝ) := by rw [hnq]; simp only [Int.cast_mul]
      rw [hmc, hnc, hb₁def, smul_add, mul_smul, mul_smul]
    have hb₁_eq : b₁ = ((g : ℝ))⁻¹ • ((m : ℝ) • u + (n : ℝ) • v : Fin 2 → ℝ) := by
      rw [hscale, smul_smul, inv_mul_cancel₀ (by positivity : ((g : ℝ)) ≠ 0), one_smul]
    have hgR : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg1
    have hginv : |((g : ℝ))⁻¹| ≤ 1 := by
      rw [abs_inv, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (g : ℝ))]
      rw [inv_le_one₀ (by linarith : (0 : ℝ) < (g : ℝ))]
      exact hgR
    calc ‖b₁‖ = |((g : ℝ))⁻¹| * ‖((m : ℝ) • u + (n : ℝ) • v : Fin 2 → ℝ)‖ := by
          rw [hb₁_eq, norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * ‖((m : ℝ) • u + (n : ℝ) • v : Fin 2 → ℝ)‖ :=
          mul_le_mul_of_nonneg_right hginv (norm_nonneg _)
      _ = ‖((m : ℝ) • u + (n : ℝ) • v : Fin 2 → ℝ)‖ := one_mul _
      _ ≤ Real.sqrt |det2 u v| + 1 := hshort
  -- lower bound on `‖b₁‖` and positivity of the associated quadratic form
  have hb₁_lower : γ ≤ ‖b₁‖ := by
    simpa only [hb₁def] using hmin p q hpq
  have hb₁ne : b₁ ≠ 0 := by
    intro h0
    have : γ ≤ (0 : ℝ) := by simpa [h0] using hb₁_lower
    linarith
  have hQ₁pos : 0 < dot2 b₁ b₁ := (dot2_self_pos b₁).mpr hb₁ne
  have hγsQ : γ ≤ Real.sqrt (dot2 b₁ b₁) := by
    linarith [hb₁_lower, norm_fin2_le_sqrt b₁]
  -- the determinant of the pair is (up to sign) the covolume
  have hdet_b₂ : det2 b₁ b₂ = det2 u v := by
    rw [hb₁def, hb₂def, det2_expand]
    have h1 : ((p : ℝ)) * ((s : ℝ)) - ((q : ℝ)) * ((r : ℝ)) = 1 := by
      have : ((p * s - q * r : ℤ) : ℝ) = 1 := by rw [hbez]; norm_num
      push_cast at this; linarith [this]
    rw [h1, one_mul]
  -- Step 3: reduce `b₂` by a multiple of `b₁`.
  obtain ⟨k, hk⟩ := exists_int_abs_sub_le_half (dot2 b₁ b₂ / dot2 b₁ b₁)
  have hk' : |dot2 b₁ b₂ - (k : ℝ) * dot2 b₁ b₁| ≤ dot2 b₁ b₁ / 2 := by
    have h2 : |(dot2 b₁ b₂ / dot2 b₁ b₁ - (k : ℝ))| * dot2 b₁ b₁ ≤ (1 / 2) * dot2 b₁ b₁ :=
      mul_le_mul_of_nonneg_right hk hQ₁pos.le
    have h3 : |(dot2 b₁ b₂ / dot2 b₁ b₁ - (k : ℝ)) * dot2 b₁ b₁| ≤ (1 / 2) * dot2 b₁ b₁ := by
      rw [abs_mul, abs_of_nonneg hQ₁pos.le]; exact h2
    have h4 : (dot2 b₁ b₂ / dot2 b₁ b₁ - (k : ℝ)) * dot2 b₁ b₁
        = dot2 b₁ b₂ - (k : ℝ) * dot2 b₁ b₁ := by
      field_simp
    rw [h4] at h3
    linarith
  set b₂' : Fin 2 → ℝ := ((r - k * p : ℤ) : ℝ) • u + ((s - k * q : ℤ) : ℝ) • v with hb₂'def
  have hb₂'eq : b₂' = b₂ - (k : ℝ) • b₁ := by
    rw [hb₂'def, hb₂def, hb₁def]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hdet' : det2 b₁ b₂' = det2 u v := by
    rw [hb₂'def, hb₁def, det2_expand]
    have h1 : ((p : ℝ)) * (((s - k * q : ℤ) : ℝ)) - ((q : ℝ)) * (((r - k * p : ℤ) : ℝ)) = 1 := by
      have hzero : p * (s - k * q) - q * (r - k * p) = p * s - q * r := by ring
      have hcast : (((p * (s - k * q) - q * (r - k * p)) : ℤ) : ℝ) = 1 := by
        rw [hzero, hbez]; norm_num
      push_cast at hcast ⊢
      exact hcast
    rw [h1, one_mul]
  have hc' : dot2 b₁ b₂' = dot2 b₁ b₂ - (k : ℝ) * dot2 b₁ b₁ := by
    rw [hb₂'eq, dot2_sub_right, dot2_smul_right, mul_comm]
  have hc'le : |dot2 b₁ b₂'| ≤ dot2 b₁ b₁ / 2 := by rw [hc']; exact hk'
  -- Lagrange identity for the reduced pair
  have hLag : dot2 b₁ b₁ * dot2 b₂' b₂' = (det2 u v) ^ 2 + (dot2 b₁ b₂') ^ 2 := by
    have h := lagrange_identity b₁ b₂'
    rw [hdet'] at h
    linarith [h]
  have hc'2 : (dot2 b₁ b₂') ^ 2 ≤ (dot2 b₁ b₁) ^ 2 / 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg (dot2 b₁ b₂')) hc'le 2
    rw [sq_abs] at h
    calc (dot2 b₁ b₂') ^ 2 ≤ (dot2 b₁ b₁ / 2) ^ 2 := h
      _ = (dot2 b₁ b₁) ^ 2 / 4 := by ring
  -- the bound on the Euclidean norm of `b₂'`
  have hQ₂'bound : dot2 b₂' b₂'
      ≤ (|det2 u v| / Real.sqrt (dot2 b₁ b₁) + Real.sqrt (dot2 b₁ b₁) / 2) ^ 2 := by
    have hexp : (|det2 u v| / Real.sqrt (dot2 b₁ b₁) + Real.sqrt (dot2 b₁ b₁) / 2) ^ 2
        = (det2 u v) ^ 2 / (dot2 b₁ b₁) + |det2 u v| + (dot2 b₁ b₁) / 4 := by
      have hsne : Real.sqrt (dot2 b₁ b₁) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ₁pos)
      rw [add_sq, div_pow, div_pow, Real.sq_sqrt hQ₁pos.le, sq_abs]
      have hmid : 2 * (|det2 u v| / Real.sqrt (dot2 b₁ b₁)) * (Real.sqrt (dot2 b₁ b₁) / 2)
          = |det2 u v| := by
        field_simp
      rw [hmid]
      norm_num
    rw [hexp]
    have hbdd : dot2 b₂' b₂' ≤ ((det2 u v) ^ 2 + (dot2 b₁ b₁) ^ 2 / 4) / (dot2 b₁ b₁) := by
      rw [le_div_iff₀ hQ₁pos]
      linarith [hLag, hc'2]
    have hsplit : ((det2 u v) ^ 2 + (dot2 b₁ b₁) ^ 2 / 4) / (dot2 b₁ b₁)
        = (det2 u v) ^ 2 / (dot2 b₁ b₁) + (dot2 b₁ b₁) / 4 := by
      field_simp
      try ring_nf
    rw [hsplit] at hbdd
    linarith [hbdd, hDpos.le]
  have hb₂'_bound : ‖b₂'‖ ≤ Real.sqrt |det2 u v| + 2 + 2 * |det2 u v| / γ := by
    have hstep : Real.sqrt (dot2 b₂' b₂')
        ≤ |det2 u v| / Real.sqrt (dot2 b₁ b₁) + Real.sqrt (dot2 b₁ b₁) / 2 := by
      have h := Real.sqrt_le_sqrt hQ₂'bound
      have hnn : 0 ≤ |det2 u v| / Real.sqrt (dot2 b₁ b₁) + Real.sqrt (dot2 b₁ b₁) / 2 :=
        add_nonneg (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
          (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
      rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn] at h
    have hX : |det2 u v| / Real.sqrt (dot2 b₁ b₁) ≤ |det2 u v| / γ :=
      div_le_div_of_nonneg_left (abs_nonneg _) hγ hγsQ
    have hY : Real.sqrt (dot2 b₁ b₁) / 2 ≤ Real.sqrt |det2 u v| + 1 := by
      have h1 : Real.sqrt (dot2 b₁ b₁) ≤ Real.sqrt 2 * ‖b₁‖ :=
        sqrt_dot2_le_sqrt_two_mul_norm b₁
      have h2 : Real.sqrt 2 / 2 ≤ 1 := by
        have h2' : Real.sqrt 2 ≤ 2 := by
          rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
        linarith
      have h3 : Real.sqrt (dot2 b₁ b₁) / 2
          ≤ (Real.sqrt 2 / 2) * (Real.sqrt |det2 u v| + 1) := by
        nlinarith [h1, hb₁_bound]
      have h4 : (Real.sqrt 2 / 2) * (Real.sqrt |det2 u v| + 1) ≤ Real.sqrt |det2 u v| + 1 :=
        mul_le_of_le_one_left (by positivity) h2
      linarith [h3, h4]
    have hgoal : 2 * |det2 u v| / γ = 2 * (|det2 u v| / γ) := by ring
    rw [hgoal]
    calc ‖b₂'‖ ≤ Real.sqrt (dot2 b₂' b₂') := norm_fin2_le_sqrt b₂'
      _ ≤ |det2 u v| / Real.sqrt (dot2 b₁ b₁) + Real.sqrt (dot2 b₁ b₁) / 2 := hstep
      _ ≤ Real.sqrt |det2 u v| + 2 + 2 * (|det2 u v| / γ) := by linarith [hX, hY, hDγ]
  have hB₁ : ‖b₁‖ ≤ Real.sqrt |det2 u v| + 2 + 2 * |det2 u v| / γ := by
    have hgoal : 2 * |det2 u v| / γ = 2 * (|det2 u v| / γ) := by ring
    rw [hgoal]; linarith [hb₁_bound, hDγ]
  refine ⟨p, q, r - k * p, s - k * q, Or.inl ?_, ?_, ?_⟩
  · have hzero : p * (s - k * q) - q * (r - k * p) = p * s - q * r := by ring
    rw [hzero, hbez]
  · simpa only [hb₁def] using hB₁
  · simpa only [hb₂'def] using hb₂'_bound

end

end Work.EKLComp
