import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.opArc_sup_torsion_family
import Submission.Work.BourgainPlan.IonescuWainger.BumpWeightBound
import Submission.Work.BourgainPlan.IonescuWainger.tsum_inv_polyWeight_sq_mul_le
import Submission.Work.IonescuWainger.tsum_ite_dvd_eq_tsum_mul
import Submission.Work.IonescuWainger.disjoint_torsionArc_shift

namespace Work.BourgainPlan

namespace IonescuWainger

open MeasureTheory
open scoped BigOperators ENNReal

/-- The complex weight `1 + ε²n²` has norm the real weight `1 + (εn)²`. -/
private lemma norm_one_add_polyWeight (ε : ℝ) (n : ℤ) :
    ‖(1:ℂ) + (ε:ℂ)^2*(n:ℂ)^2‖ = 1 + (ε*(n:ℝ))^2 := by
  have h : ((1:ℂ) + (ε:ℂ)^2*(n:ℂ)^2) = (((1 + (ε*(n:ℝ))^2 : ℝ)) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- The inverse complex weight `(1 + ε²n²)⁻¹` has norm the real weight `(1 + (εn)²)⁻¹`. -/
private lemma norm_inv_one_add_polyWeight (ε : ℝ) (n : ℤ) :
    ‖((1:ℂ) + (ε:ℂ)^2*(n:ℂ)^2)⁻¹‖ = (1 + (ε*(n:ℝ))^2)⁻¹ := by
  have h : ((1:ℂ) + (ε:ℂ)^2*(n:ℂ)^2) = (((1 + (ε*(n:ℝ))^2 : ℝ)) : ℂ) := by push_cast; ring
  rw [h, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- The majorant `m ↦ (1 + (εm)²)⁻¹` is summable over `ℤ`: it is dominated by
`2(1 + |εm|)⁻²`, which is summable by `int_summable_rpow_inv_two`. -/
private lemma summable_inv_one_add_polyWeight (ε : ℝ) (hε : 0 < ε) :
    Summable (fun n : ℤ => (1 + (ε * (n:ℝ))^2)⁻¹) := by
  have hM : Summable fun l : ℤ => (1 + |ε * (l:ℝ)|) ^ (-(2:ℝ)) := int_summable_rpow_inv_two ε hε
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hM.mul_left 2)
  set t : ℝ := ε * (n:ℝ) with ht
  have h1 : 0 < 1 + |t| := by positivity
  have hsq : (1 + |t|)^2 ≤ 2*(1 + t^2) := by nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (|t|-1)]
  have h3 : (1 + t^2)⁻¹ ≤ 2*((1+|t|)^2)⁻¹ := by
    have h2 : (2*(1+t^2))⁻¹ ≤ ((1+|t|)^2)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le (by positivity : (0:ℝ) < (1+|t|)^2) hsq
    rw [mul_inv] at h2
    nlinarith [h2, inv_nonneg.mpr (by positivity : (0:ℝ) ≤ 1+t^2)]
  rw [Real.rpow_neg (le_of_lt h1), Real.rpow_two]
  exact h3

/-- Real `rpow` algebra: `u · u^{-3/2} = u^{-1/2}` for `u > 0`. -/
private lemma mul_rpow_neg_three_halves {u : ℝ} (hu : 0 < u) :
    u * u ^ (-((3:ℝ)/2)) = u ^ (-((1:ℝ)/2)) := by
  have h := Real.rpow_add hu (1:ℝ) (-((3:ℝ)/2))
  rw [Real.rpow_one] at h
  rw [show (1:ℝ) + (-((3:ℝ)/2)) = -((1:ℝ)/2) by norm_num] at h
  exact h.symm

/-- Real `rpow` algebra: `(u^{-1/2})² = u⁻¹` for `u > 0`. -/
private lemma sq_rpow_neg_half {u : ℝ} (hu : 0 < u) :
    (u ^ (-((1:ℝ)/2)))^2 = u⁻¹ := by
  rw [sq, ← Real.rpow_add hu, show (-((1:ℝ)/2)) + (-((1:ℝ)/2)) = (-1:ℝ) by norm_num,
    Real.rpow_neg_one]

/-- The `n`-th Fourier character has norm one, so it can be dropped from a product inside a norm. -/
private lemma norm_mul_star_fourier_mul (α : Circle) (n : ℤ) (z w x : ℂ) :
    ‖z * ((star (fourier n α) * w) * x)‖ = ‖w * (z * x)‖ := by
  simp only [norm_mul, norm_star, norm_fourier_apply', one_mul]
  ring

/-- **The reindexed inverse polynomial weight over the sublattice `Qℤ`.**  For `ε > 0`, `Q ≥ 1`
and `εQ ≤ 1`, `Σ_n ‖[Q ∣ n]·(1 + ε²n²)⁻¹‖² ≤ 8/(εQ)`.  This is the constant `C₁²` of the
`p = ∞` endpoint of Tao's `ortho-apply`(ii), obtained from `tsum_inv_polyWeight_sq_mul_le` by
reindexing the sum over the multiples of `Q` (`tsum_ite_dvd_eq_tsum_mul`). -/
private theorem tsum_inv_polyWeight_ite_le {ε : ℝ} (hε : 0 < ε) {Q : ℕ} (hQ : 1 ≤ Q)
    (hεQ : ε * (Q:ℝ) ≤ 1) :
    ∑' n : ℤ, ‖(if (Q : ℤ) ∣ n then ((1:ℂ) + (ε:ℂ)^2 * (n:ℂ)^2)⁻¹ else 0)‖ ^ 2
      ≤ 8 / (ε * (Q:ℝ)) := by
  have hQpos : 0 < Q := by omega
  rw [show (∑' n : ℤ, ‖(if (Q : ℤ) ∣ n then ((1:ℂ) + (ε:ℂ)^2 * (n:ℂ)^2)⁻¹ else 0)‖ ^ 2)
      = ∑' n : ℤ, (if (Q:ℤ) ∣ n then ‖((1:ℂ) + (ε:ℂ)^2 * (n:ℂ)^2)⁻¹‖ ^ 2 else 0) from by
    apply tsum_congr; intro n; by_cases h : (Q:ℤ) ∣ n <;> simp [h]]
  rw [Work.IonescuWainger.tsum_ite_dvd_eq_tsum_mul hQpos
    (fun n : ℤ => ‖((1:ℂ)+(ε:ℂ)^2*(n:ℂ)^2)⁻¹‖^2)]
  rw [show (∑' m : ℤ, ‖((1:ℂ) + (ε:ℂ)^2 * ((((Q:ℤ)*m : ℤ) : ℂ))^2)⁻¹‖ ^ 2)
      = ∑' m : ℤ, ‖((1:ℂ) + (ε:ℂ)^2 * ((Q:ℂ)*(m:ℂ))^2)⁻¹‖ ^ 2 from by
    apply tsum_congr; intro m; push_cast; ring_nf]
  exact Work.BourgainPlan.IonescuWainger.tsum_inv_polyWeight_sq_mul_le hε hQ hεQ

/-- **The reindexed weighted kernel sum over the sublattice `Qℤ`.**  For a kernel decaying as
`‖K m‖ ≤ Cε(1 + (εm)²)^{-3/2}`, the weighted `ℓ²`-mass of the *torsion* kernel
`n ↦ Q·K(Qm)·(1 + ε²(Qm)²)` on the multiples of `Q` is at most `8C²εQ`.  This is the constant
`C₂²` of the `p = ∞` endpoint of Tao's `ortho-apply`(ii), and is exactly the `hC₂` hypothesis of
`opArc_sup_torsion_family` (the character factor has modulus one, so the bound is uniform in the
arc point `α`). -/
private theorem tsum_weighted_kernel_ite_le {ε C : ℝ} {Q : ℕ} {K : ℤ → ℂ}
    (hε : 0 < ε) (hQ : 1 ≤ Q) (hεQ : ε * (Q:ℝ) ≤ 1/2)
    (hdecay : ∀ m : ℤ, ‖K m‖ ≤ C * ε / (1 + (ε * (m:ℝ))^2)^((3:ℝ)/2))
    (α : Circle) :
    ∑' n : ℤ, ‖(1 + (ε:ℂ)^2*(n:ℂ)^2) *
        ((star (fourier n α) * (if (Q:ℤ) ∣ n then (Q:ℂ) else 0)) * K n)‖ ^ 2
      ≤ 8 * C^2 * ε * (Q:ℝ) := by
  have hQpos : 0 < Q := by omega
  have hQℝ : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hstep1 : (∑' n : ℤ, ‖(1 + (ε:ℂ)^2*(n:ℂ)^2) * ((star (fourier n α) * (if (Q:ℤ) ∣ n then (Q:ℂ) else 0)) * K n)‖ ^ 2)
      = ∑' n : ℤ, (if (Q:ℤ) ∣ n then ‖(1 + (ε:ℂ)^2*(n:ℂ)^2) * ((star (fourier n α) * (if (Q:ℤ) ∣ n then (Q:ℂ) else 0)) * K n)‖ ^ 2 else 0) := by
    apply tsum_congr; intro n
    by_cases h : (Q:ℤ) ∣ n <;> simp [h]
  rw [hstep1, Work.IonescuWainger.tsum_ite_dvd_eq_tsum_mul hQpos
        (fun n : ℤ => ‖(1 + (ε:ℂ)^2*(n:ℂ)^2) * ((star (fourier n α) * (if (Q:ℤ) ∣ n then (Q:ℂ) else 0)) * K n)‖ ^ 2)]
  have hpt : ∀ m : ℤ,
      ‖(1 + (ε:ℂ)^2*((((Q:ℤ)*m : ℤ)):ℂ)^2) * ((star (fourier ((Q:ℤ)*m) α) * (if (Q:ℤ) ∣ (Q:ℤ)*m then (Q:ℂ) else 0)) * K ((Q:ℤ)*m))‖ ^ 2
      = ‖(Q:ℂ) * ((1 + (ε:ℂ)^2*((Q:ℂ)*(m:ℂ))^2) * K ((Q:ℤ)*m))‖ ^ 2 := by
    intro m
    rw [if_pos (dvd_mul_right (Q:ℤ) m)]
    rw [show ((((Q:ℤ)*m : ℤ)) : ℂ) = (Q:ℂ)*(m:ℂ) by push_cast; ring]
    rw [norm_mul_star_fourier_mul]
  rw [tsum_congr hpt]
  have hdecay' : ∀ m : ℤ, ‖K ((Q:ℤ)*m)‖ ≤ C * ε / (1 + (ε * (Q:ℝ) * (m:ℝ)) ^ 2) ^ ((3:ℝ)/2) := by
    intro m
    have h := hdecay ((Q:ℤ)*m)
    have hcast : ((((Q:ℤ)*m : ℤ)) : ℝ) = (Q:ℝ) * (m:ℝ) := by push_cast; ring
    rw [hcast] at h
    simpa only [mul_assoc] using h
  have := Work.BourgainPlan.IonescuWainger.tsum_weighted_kernel_sq_le_half_mul
    (K := fun m : ℤ => K ((Q:ℤ)*m)) hε hQℝ hεQ hdecay'
  simpa only [Complex.ofReal_natCast] using this

/-- **The `Memℓp` side condition for the inverse polynomial weight** (`hWmem` of
`opArc_sup_torsion_family`): `n ↦ [Q ∣ n]·(1 + ε²n²)⁻¹` is square-summable, by comparison with
`(1 + (εn)²)⁻¹`. -/
private theorem memlp_ite_inv_polyWeight {ε : ℝ} (hε : 0 < ε) {Q : ℕ} :
    Memℓp (fun n : ℤ => if (Q:ℤ) ∣ n then ((1:ℂ) + (ε:ℂ)^2*(n:ℂ)^2)⁻¹ else 0) 2 := by
  refine (memℓp_gen_iff (p := 2) (by norm_num)).mpr ?_
  have hS := summable_inv_one_add_polyWeight ε hε
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (norm_nonneg _) _) (fun n => ?_) hS
  by_cases h : (Q:ℤ) ∣ n
  · rw [if_pos h, norm_inv_one_add_polyWeight]
    rw [show ENNReal.toReal 2 = (2:ℝ) by norm_num, Real.rpow_two]
    nlinarith [inv_pos.mpr (by positivity : (0:ℝ) < 1 + (ε*(n:ℝ))^2),
      inv_le_one_of_one_le₀ (by linarith [sq_nonneg (ε*(n:ℝ))] : (1:ℝ) ≤ 1 + (ε*(n:ℝ))^2)]
  · rw [if_neg h]
    have hzero : ‖(0:ℂ)‖ ^ (ENNReal.toReal 2) = 0 := by simp
    rw [hzero]
    positivity

/-- **The `Memℓp` side condition for the weighted torsion kernel** (`hKv` of
`opArc_sup_torsion_family`): `n ↦ (1 + ε²n²)·(χ_n·[Q ∣ n]Q·K n)` is square-summable, by
comparison with `Q²C²ε²(1 + (εn)²)⁻¹`. -/
private theorem memlp_mul_weighted_kernel {ε C : ℝ} {Q : ℕ} {K : ℤ → ℂ}
    (hε : 0 < ε) (_hC : 0 ≤ C)
    (hdecay : ∀ m : ℤ, ‖K m‖ ≤ C * ε / (1 + (ε * (m:ℝ))^2)^((3:ℝ)/2)) (α : Circle) :
    Memℓp (fun n : ℤ => (1 + (ε:ℂ)^2*(n:ℂ)^2) *
      ((star (fourier n α) * (if (Q:ℤ) ∣ n then (Q:ℂ) else 0)) * K n)) 2 := by
  refine (memℓp_gen_iff (p := 2) (by norm_num)).mpr ?_
  have hS := (summable_inv_one_add_polyWeight ε hε).mul_left ((Q:ℝ)^2 * C^2 * ε^2)
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (norm_nonneg _) _) (fun n => ?_) hS
  rw [show ENNReal.toReal 2 = (2:ℝ) by norm_num, Real.rpow_two]
  by_cases h : (Q:ℤ) ∣ n
  · rw [if_pos h]
    have hu : 0 < 1 + (ε*(n:ℝ))^2 := by positivity
    have hdec : ‖K n‖ ≤ C*ε * (1 + (ε*(n:ℝ))^2)^(-((3:ℝ)/2)) := by
      have hh := hdecay n
      rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hu)] at hh
      exact hh
    have hnorm : ‖(1 + (ε:ℂ)^2*(n:ℂ)^2) * ((star (fourier n α) * (Q:ℂ)) * K n)‖
        = (1 + (ε*(n:ℝ))^2) * ((Q:ℝ) * ‖K n‖) := by
      rw [norm_mul, norm_mul, norm_mul, norm_star, norm_fourier_apply',
        norm_one_add_polyWeight, Complex.norm_natCast, one_mul]
    rw [hnorm]
    have hmain : (1 + (ε*(n:ℝ))^2) * ((Q:ℝ) * ‖K n‖)
        ≤ (Q:ℝ)*C*ε*(1 + (ε*(n:ℝ))^2)^(-((1:ℝ)/2)) := by
      calc (1 + (ε*(n:ℝ))^2) * ((Q:ℝ) * ‖K n‖)
          ≤ (1 + (ε*(n:ℝ))^2) * ((Q:ℝ) * (C*ε * (1+(ε*(n:ℝ))^2)^(-((3:ℝ)/2)))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left hdec (by positivity)
        _ = (Q:ℝ)*C*ε*(1 + (ε*(n:ℝ))^2)^(-((1:ℝ)/2)) := by
            rw [show (1 + (ε*(n:ℝ))^2) * ((Q:ℝ) * (C*ε * (1 + (ε*(n:ℝ))^2)^(-((3:ℝ)/2))))
                = (Q:ℝ)*C*ε*((1 + (ε*(n:ℝ))^2) * (1 + (ε*(n:ℝ))^2)^(-((3:ℝ)/2))) by ring,
              mul_rpow_neg_three_halves hu]
    refine le_trans (pow_le_pow_left₀ (by positivity) hmain 2) (le_of_eq ?_)
    rw [show (Q:ℝ)*C*ε*(1 + (ε*(n:ℝ))^2)^(-((1:ℝ)/2))
        = ((Q:ℝ)*C*ε) * ((1 + (ε*(n:ℝ))^2)^(-((1:ℝ)/2))) by ring, mul_pow,
      sq_rpow_neg_half hu]
    ring
  · rw [if_neg h]
    have hzero : ‖(1 + (ε:ℂ)^2*(n:ℂ)^2) * ((star (fourier n α) * (0:ℂ)) * K n)‖ ^ 2 = 0 := by simp
    rw [hzero]
    positivity

/-- **The `ℓ¹` side condition for the torsion kernel** (`hKi` of `opArc_sup_torsion_family`): the
unweighted kernel `n ↦ χ_n·[Q ∣ n]Q·K n` is absolutely summable, since `‖K n‖ ≤ Cε(1 + (εn)²)^{-1}`
(the exponent `3/2` dominates `1`) and `(1 + (εn)²)⁻¹` is summable. -/
private theorem summable_norm_weighted_kernel {ε C : ℝ} {Q : ℕ} {K : ℤ → ℂ}
    (hε : 0 < ε) (hC : 0 ≤ C)
    (hdecay : ∀ m : ℤ, ‖K m‖ ≤ C * ε / (1 + (ε * (m:ℝ))^2)^((3:ℝ)/2)) (α : Circle) :
    Summable (fun n : ℤ => ‖(star (fourier n α) * (if (Q:ℤ) ∣ n then (Q:ℂ) else 0)) * K n‖) := by
  have hS := (summable_inv_one_add_polyWeight ε hε).mul_left ((Q:ℝ)*C*ε)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hS
  by_cases h : (Q:ℤ) ∣ n
  · rw [if_pos h]
    have hu : 0 < 1 + (ε*(n:ℝ))^2 := by positivity
    have hu1 : 1 ≤ 1 + (ε*(n:ℝ))^2 := by linarith [sq_nonneg (ε*(n:ℝ))]
    have hnorm : ‖(star (fourier n α) * (Q:ℂ)) * K n‖ = (Q:ℝ)*‖K n‖ := by
      rw [norm_mul, norm_mul, norm_star, norm_fourier_apply', Complex.norm_natCast, one_mul]
    rw [hnorm]
    have hdec : ‖K n‖ ≤ C*ε * (1 + (ε*(n:ℝ))^2)^(-((3:ℝ)/2)) := by
      have hh := hdecay n
      rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hu)] at hh
      exact hh
    have hstep : C*ε * (1 + (ε*(n:ℝ))^2)^(-((3:ℝ)/2)) ≤ C*ε * (1+(ε*(n:ℝ))^2)^(-(1:ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num))
        (mul_nonneg hC hε.le)
    calc (Q:ℝ)*‖K n‖ ≤ (Q:ℝ)*(C*ε * (1+(ε*(n:ℝ))^2)^(-((3:ℝ)/2))) :=
          mul_le_mul_of_nonneg_left hdec (by positivity)
      _ ≤ (Q:ℝ)*(C*ε * (1+(ε*(n:ℝ))^2)^(-(1:ℝ))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (Q:ℝ)*C*ε*(1 + (ε*(n:ℝ))^2)⁻¹ := by
          rw [Real.rpow_neg_one]; ring
  · rw [if_neg h]
    simp only [mul_zero, zero_mul, norm_zero]
    have h1 : (0:ℝ) ≤ (Q:ℝ)*C*ε :=
      mul_nonneg (mul_nonneg (show (0:ℝ) ≤ (Q:ℝ) by positivity) hC) hε.le
    exact mul_nonneg h1 (show (0:ℝ) ≤ (1 + (ε*(n:ℝ))^2)⁻¹ by positivity)

end IonescuWainger

/-- **The `p = ∞` endpoint of Tao's `ortho-apply`(ii) with a concrete rapidly decaying bump**
(arXiv:2008.05066, §4, the `p = ∞` paragraph).  This discharges every hypothesis of
`opArc_sup_torsion_family` (arc separation, the two weight-norm constants and the summability
side conditions) for a bump `φ` supported in `B(0,ε)` whose Fourier coefficients decay as
`‖K m‖ ≤ C ε (1 + (εm)²)^{-3/2}`.

Notation: `Q = Q_{A₀} = ∏_{q ∈ A₀} q`; `D : ι → Finset ℕ` indexes the complementary arc sets with
`D i ⊆ S \ A₀`, `|D i| ≤ k - |A₀|`; the operators are the modulated torsion-arc multipliers
`Op_{φ; α i + Σ_{⊆A₀}}` with `α i = a i / Q_{D i}`.

The constant `8C` is `C₁C₂` with `C₁ = √(8/(εQ))` (the restricted inverse-weight norm,
`tsum_inv_polyWeight_sq_mul_le`) and `C₂ = √(8C²εQ)` (`tsum_weighted_kernel_sq_le_half_mul`), so it
is uniform in the arc data: this is the sharp form of the endpoint, as needed by the vector-valued
interpolation `vector_valued_lp_interpolation_count`.

Proof plan (all the ingredients already exist in the workspace):
1. the arc separation is `Work.IonescuWainger.disjoint_torsionArc_shift` (with `h2`, `hS`, `hD`,
   `hDk`, `hinj`, `hmax`, `hsep`);
2. `hC₁ ≤ C₁²` follows from `tsum_inv_polyWeight_sq_mul_le` after reindexing the sum over the
   multiples of `Q` with `Work.IonescuWainger.tsum_ite_dvd_eq_tsum_mul` (and the pointwise identity
   `‖((1:ℂ) + ε²n²)⁻¹‖ = (1 + (εn)²)⁻¹`);
3. `hC₂ ≤ C₂²` is `tsum_weighted_kernel_sq_le_half_mul` after the same reindexing: the `hC₂`
   summand is `(1 + ε²n²)·(star (fourier n α)·(if Q ∣ n then Q else 0)·K n)`, whose modulus depends
   on `n` only through `Q·(1 + ε²(Qm)²)|K(Qm)|` on `n = Qm` (the character has modulus one, so the
   bound is uniform in `i`).  **Do not use `tsum_weighted_kernel_sq_le_half` here** (it bounds the
   sum *without* the torsion factor `Q`, and multiplying its conclusion by `Q²` loses a factor
   `Q` and does not close); the factored version `tsum_weighted_kernel_sq_le_half_mul` is the one
   whose constant `8C²εQ` absorbs the `Q²`;
4. `hWmem` and `hKv` are the `Memℓp` (the `lp`-space predicate, no measure involved) side
   conditions; by `memℓp_gen_iff` (`Memℓp f p ↔ Summable fun i => ‖f i‖ ^ p.toReal` for
   `0 < p.toReal`) they reduce to square-summability, which follows from the bounded sums in 2/3,
   or by the pointwise domination
   `‖(1 + ε²n²)·K_i n‖ ≤ Q·C·ε·(1 + (εn)²)^{-1/2}` and
   `‖[Q ∣ n]·(1 + ε²n²)⁻¹‖ ≤ (1 + (εn)²)^{-1}` together with summability of
   `n ↦ (1 + (εn)²)^{-1}` (comparison with `int_summable_rpow_inv_two` at `a = ε`, via the
   elementary bound `(1 + t²)^{-1} ≤ 2(1 + |t|)^{-2}`);
5. `hKi` (absolute summability of the unweighted kernel) follows from the same decay: on `n = Q m`
   the kernel is `Q·K(Qm)`, so `‖K_i n‖ ≤ Q·C·ε·(1 + (εn)²)^{-1}` (using the exponent `3/2` and
   `(1+x)^{-3/2} ≤ (1+x)^{-1}`), and `Σ_n (1 + (εn)²)^{-1} < ∞` by comparison as in 4;
6. apply `opArc_sup_torsion_family` and simplify `√(8/(εQ)) · √(8C²εQ) = 8C`. -/
theorem opArc_sup_torsion_family_of_bump
    {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A₀ : Finset ℕ} (hA₀ : A₀ ⊆ S) {k : ℕ} (hk₀ : A₀.card ≤ k)
    {ι : Type*} [Fintype ι] (D : ι → Finset ℕ) (a : ι → ℤ)
    (hD : ∀ i, D i ⊆ S \ A₀) (hDk : ∀ i, (D i).card ≤ k - A₀.card)
    (hinj : ∀ i j, i ≠ j →
      Work.BourgainPlan.IonescuWainger.arcPt (Work.BourgainPlan.IonescuWainger.QA (D i)) (a i)
        ≠ Work.BourgainPlan.IonescuWainger.arcPt (Work.BourgainPlan.IonescuWainger.QA (D j)) (a j))
    {qmax : ℕ} (hmax : ∀ q ∈ S, q ≤ qmax)
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {K : ℤ → ℂ} {C ε : ℝ}
    (hC0 : 0 ≤ C) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hφsupp : ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, ε < ‖ξ‖ → φ ξ = 0)
    (hK : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)) = K m)
    (hdecay : ∀ m : ℤ, ‖K m‖ ≤ C * ε / (1 + (ε * (m : ℝ)) ^ 2) ^ ((3:ℝ)/2))
    (hsep : 2 * ε < 1 / (qmax : ℝ) ^ (2 * k))
    (hεQ : ε * (Work.BourgainPlan.IonescuWainger.QA A₀ : ℝ) ≤ 1 / 2)
    (f : ℤ → ℂ) (hf : Memℓp f 2) {C' : ℝ}
    (hC' : ∀ m : ℤ, ‖f m‖ ≤ C') (n : ℤ) :
    (∑ i, ‖Work.BourgainPlan.IonescuWainger.opArc φ hφ
        (Work.BourgainPlan.IonescuWainger.arcShift
          (Work.BourgainPlan.IonescuWainger.sigmaSubAFinset A₀)
          (Work.BourgainPlan.IonescuWainger.arcPt
            (Work.BourgainPlan.IonescuWainger.QA (D i)) (a i))) f hf n‖ ^ 2)
        ^ ((1:ℝ)/2) ≤ 8 * C * C' := by
  classical
  have _hε1test : ε ≤ 1 := hε1
  have hQ1 : 1 ≤ Work.BourgainPlan.IonescuWainger.QA A₀ := by
    show (1:ℕ) ≤ ∏ q ∈ A₀, q
    exact Finset.one_le_prod₀ (fun q hq => by have := h2 q (hA₀ hq); omega)
  have hQpos : 0 < (Work.BourgainPlan.IonescuWainger.QA A₀ : ℕ) :=
    lt_of_lt_of_le Nat.zero_lt_one hQ1
  have hQℝpos : (0:ℝ) < (Work.BourgainPlan.IonescuWainger.QA A₀ : ℝ) := by
    exact_mod_cast hQpos
  have hεQ' : ε * (Work.BourgainPlan.IonescuWainger.QA A₀ : ℝ) ≤ 1 := by linarith [hεQ, hε1]
  have her : (0:ℝ) < ε * (Work.BourgainPlan.IonescuWainger.QA A₀ : ℝ) := mul_pos hε hQℝpos
  set C₁ : ℝ := Real.sqrt (8 / (ε * (Work.BourgainPlan.IonescuWainger.QA A₀ : ℝ))) with hC₁def
  set C₂ : ℝ := Real.sqrt (8 * C^2 * ε * (Work.BourgainPlan.IonescuWainger.QA A₀ : ℝ)) with hC₂def
  let αs : ι → Work.BourgainPlan.IonescuWainger.Circle :=
    fun i => Work.BourgainPlan.IonescuWainger.arcPt
      (Work.BourgainPlan.IonescuWainger.QA (D i)) (a i)
  have hdisj : ∀ i j : ι, i ≠ j →
      Disjoint (closure {ξ : Work.BourgainPlan.IonescuWainger.Circle |
          ∃ β ∈ Work.BourgainPlan.IonescuWainger.sigmaSubAFinset A₀,
          ξ - (β + αs i) ∈ Metric.closedBall (0 : Work.BourgainPlan.IonescuWainger.Circle) ε})
               (closure {ξ : Work.BourgainPlan.IonescuWainger.Circle |
          ∃ β ∈ Work.BourgainPlan.IonescuWainger.sigmaSubAFinset A₀,
          ξ - (β + αs j) ∈ Metric.closedBall (0 : Work.BourgainPlan.IonescuWainger.Circle) ε}) :=
    Work.IonescuWainger.disjoint_torsionArc_shift h2 hS hA₀ hk₀ D a hD hDk hinj hmax hε hsep
  have hC₁ : ∑' n : ℤ, ‖(if (Work.BourgainPlan.IonescuWainger.QA A₀ : ℤ) ∣ n
      then ((1:ℂ) + (ε:ℂ)^2*(n:ℂ)^2)⁻¹ else 0)‖ ^ 2 ≤ C₁ ^ 2 := by
    rw [hC₁def, Real.sq_sqrt (le_of_lt (div_pos (by norm_num) her))]
    exact Work.BourgainPlan.IonescuWainger.tsum_inv_polyWeight_ite_le hε hQ1 hεQ'
  have hWmem : Memℓp (fun n : ℤ => if (Work.BourgainPlan.IonescuWainger.QA A₀ : ℤ) ∣ n
      then ((1:ℂ) + (ε:ℂ)^2*(n:ℂ)^2)⁻¹ else 0) 2 :=
    Work.BourgainPlan.IonescuWainger.memlp_ite_inv_polyWeight hε
  have hC₂ : ∀ i : ι, ∑' n : ℤ, ‖(1 + (ε:ℂ)^2*(n:ℂ)^2) *
      ((star (fourier n (αs i)) * (if (Work.BourgainPlan.IonescuWainger.QA A₀ : ℤ) ∣ n
        then (Work.BourgainPlan.IonescuWainger.QA A₀ : ℂ) else 0)) * K n)‖ ^ 2 ≤ C₂ ^ 2 := by
    intro i
    rw [hC₂def, Real.sq_sqrt (by positivity)]
    exact Work.BourgainPlan.IonescuWainger.tsum_weighted_kernel_ite_le hε hQ1 hεQ hdecay (αs i)
  have hKv : ∀ i : ι, Memℓp (fun n : ℤ => (1 + (ε:ℂ)^2*(n:ℂ)^2) *
      ((star (fourier n (αs i)) * (if (Work.BourgainPlan.IonescuWainger.QA A₀ : ℤ) ∣ n
        then (Work.BourgainPlan.IonescuWainger.QA A₀ : ℂ) else 0)) * K n)) 2 :=
    fun i => Work.BourgainPlan.IonescuWainger.memlp_mul_weighted_kernel hε hC0 hdecay (αs i)
  have hKi : ∀ i : ι, Summable (fun n : ℤ =>
      ‖(star (fourier n (αs i)) * (if (Work.BourgainPlan.IonescuWainger.QA A₀ : ℤ) ∣ n
        then (Work.BourgainPlan.IonescuWainger.QA A₀ : ℂ) else 0)) * K n‖) :=
    fun i => Work.BourgainPlan.IonescuWainger.summable_norm_weighted_kernel hε hC0 hdecay (αs i)
  have hmain := Work.BourgainPlan.IonescuWainger.opArc_sup_torsion_family
    (A := A₀) (αs := αs) φ hφ hK hε (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hφsupp hdisj hC₁ hWmem hC₂ hKv hKi f hf hC' n
  have hCprod : C₁ * C₂ * C' = 8 * C * C' := by
    have h1 : C₁ * C₂ = 8 * C := by
      rw [hC₁def, hC₂def,
        ← Real.sqrt_mul (le_of_lt (div_pos (by norm_num) her))]
      have hsq : 8 / (ε * (Work.BourgainPlan.IonescuWainger.QA A₀ : ℝ)) *
          (8 * C^2 * ε * (Work.BourgainPlan.IonescuWainger.QA A₀ : ℝ)) = (8*C)^2 := by
        field_simp [her.ne']
        try ring
      rw [hsq, Real.sqrt_sq (mul_nonneg (by norm_num) hC0)]
    rw [h1]
  exact hmain.trans (le_of_eq hCprod)

end Work.BourgainPlan
