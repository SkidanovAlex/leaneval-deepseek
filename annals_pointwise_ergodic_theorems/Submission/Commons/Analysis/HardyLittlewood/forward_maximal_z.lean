import Mathlib
import Submission.Commons.Analysis.HardyLittlewood.discrete_forward_maximal
import Submission.Commons.Analysis.HilbertMatrix.lp_bound
open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology
open Classical

namespace Commons.Analysis.HardyLittlewood

noncomputable def fwdMaxZ (g : ℤ → ℝ) (x : ℤ) : ℝ≥0∞ :=
  ⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (x + j)‖ₑ

noncomputable def fwdMaxN (g : ℕ → ℝ) (x : ℕ) : ℝ≥0∞ :=
  ⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (x + j)‖ₑ

lemma fwdMaxZ_shift (g : ℤ → ℝ) (m : ℤ) (n : ℕ) :
    fwdMaxZ g (m + n) = fwdMaxN (fun k : ℕ => g (m + k)) n := by
  unfold fwdMaxZ fwdMaxN
  apply iSup_congr; intro N
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  push_cast
  ring

lemma fwdMaxZ_tail_le {g : ℤ → ℝ} {m : ℤ} (hm : ∀ n, n < m → g n = 0)
    {s : Finset ℤ} (hs : ∀ n, n ∉ s → g n = 0) (y : ℕ) :
    fwdMaxZ g (m - y) ≤
      ENNReal.ofReal (∑' k : ℤ, |g k| / ((k:ℝ) - (m:ℝ) + (y:ℝ) + 1)) := by
  set h : ℤ → ℝ := fun k => |g k| / ((k:ℝ) - (m:ℝ) + (y:ℝ) + 1) with hh
  have hnn : ∀ k, 0 ≤ h k := by
    intro k
    by_cases hk : k < m
    · rw [hh]; simp only; rw [hm k hk, abs_zero, zero_div]
    · rw [hh]; simp only
      apply div_nonneg (abs_nonneg _)
      have h1 : (m:ℝ) ≤ (k:ℝ) := by exact_mod_cast (not_lt.mp hk)
      have h2 : (0:ℝ) ≤ (y:ℝ)+1 := by positivity
      linarith
  have hsum : Summable h :=
    summable_of_ne_finset_zero (s := s) (fun k hk => by
      rw [hh]; simp only; rw [hs k hk, abs_zero, zero_div])
  refine iSup_le fun N => ?_
  rw [Real.enorm_eq_ofReal_abs]
  apply ENNReal.ofReal_le_ofReal
  calc |(N:ℝ)⁻¹ * ∑ j ∈ Finset.range N, g ((m - y) + j)|
      = (N:ℝ)⁻¹ * |∑ j ∈ Finset.range N, g ((m - y) + j)| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (N:ℝ)⁻¹ * ∑ j ∈ Finset.range N, |g ((m - y) + j)| :=
        mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
    _ = ∑ j ∈ Finset.range N, (N:ℝ)⁻¹ * |g ((m - y) + j)| := by rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range N, |g ((m - y) + j)| / ((j:ℝ)+1) := by
        apply Finset.sum_le_sum; intro j hj
        rw [Finset.mem_range] at hj
        have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
        have hthis : (N:ℝ)⁻¹ ≤ ((j:ℝ)+1)⁻¹ := by
          rw [inv_le_inv₀ hNpos (by positivity)]
          exact_mod_cast (by omega : j + 1 ≤ N)
        calc (N:ℝ)⁻¹ * |g ((m - y) + j)| ≤ ((j:ℝ)+1)⁻¹ * |g ((m - y) + j)| :=
              mul_le_mul_of_nonneg_right hthis (abs_nonneg _)
          _ = |g ((m - y) + j)| / ((j:ℝ)+1) := by rw [div_eq_mul_inv, mul_comm]
    _ = ∑ j ∈ Finset.range N, h ((m - y) + j) := by
        apply Finset.sum_congr rfl; intro j hj
        rw [hh]; simp only
        congr 1
        push_cast; ring
    _ = ∑ k ∈ (Finset.range N).image (fun j : ℕ => (m - y) + (j:ℤ)), h k :=
        (Finset.sum_image (s := Finset.range N) (g := fun j : ℕ => (m - y) + (j:ℤ))
          (by intro a _ b _ hab; simp only at hab; omega)).symm
    _ ≤ ∑' k : ℤ, h k := Summable.sum_le_tsum _ (fun k _ => hnn k) hsum

lemma tsum_succ_le (f : ℕ → ℝ≥0∞) : (∑' n, f (n+1)) ≤ ∑' n, f n := by
  rw [ENNReal.tsum_eq_iSup_sum, ENNReal.tsum_eq_iSup_sum]
  apply iSup_le; intro s
  have h : ∑ n ∈ s, f (n+1) = ∑ m ∈ s.image (fun n => n+1), f m :=
    (Finset.sum_image (s := s) (g := fun n => n+1) Nat.succ_injective.injOn).symm
  rw [h]
  exact le_iSup (fun t : Finset ℕ => ∑ m ∈ t, f m) (s.image (fun n => n+1))

lemma shift_Ici (m : ℤ) (f : ℤ → ℝ≥0∞) :
    ∫⁻ x in {x : ℤ | m ≤ x}, f x ∂Measure.count = ∫⁻ n : ℕ, f (m + n) ∂Measure.count := by
  rw [lintegral_countable f (Set.countable_univ.mono (Set.subset_univ _)), lintegral_count]
  have hcount : ∀ a : {x : ℤ | m ≤ x}, Measure.count {(a : ℤ)} = 1 := by
    intro a; rw [Measure.count_singleton]
  simp only [hcount, mul_one]
  let e : ℕ ≃ {x : ℤ | m ≤ x} :=
    { toFun := fun n => ⟨m + n, le_add_of_nonneg_right (Int.natCast_nonneg n)⟩
      invFun := fun x => (x.1 - m).toNat
      left_inv := by
        intro n
        show ((m + (n:ℤ)) - m).toNat = n
        rw [add_sub_cancel_left, Int.toNat_natCast]
      right_inv := by
        intro x
        ext
        show m + (((x:ℤ) - m).toNat : ℤ) = (x:ℤ)
        rw [Int.toNat_sub_of_le (a := (x:ℤ)) (b := m) x.2]; ring }
  rw [← Equiv.tsum_eq e (fun a : {x : ℤ | m ≤ x} => f ↑a)]
  rfl

lemma shift_Iio (m : ℤ) (f : ℤ → ℝ≥0∞) :
    ∫⁻ x in {x : ℤ | x < m}, f x ∂Measure.count = ∫⁻ n : ℕ, f (m - 1 - n) ∂Measure.count := by
  rw [lintegral_countable f (Set.countable_univ.mono (Set.subset_univ _)), lintegral_count]
  have hcount : ∀ a : {x : ℤ | x < m}, Measure.count {(a : ℤ)} = 1 := by
    intro a; rw [Measure.count_singleton]
  simp only [hcount, mul_one]
  let e : ℕ ≃ {x : ℤ | x < m} :=
    { toFun := fun n => ⟨m - 1 - n, by
        rw [show m - 1 - (n:ℤ) = m - (1 + (n:ℤ)) by ring]
        exact sub_lt_self m (by positivity)⟩
      invFun := fun x => (m - 1 - x.1).toNat
      left_inv := by
        intro n
        show (m - 1 - (m - 1 - (n:ℤ))).toNat = n
        rw [show m - 1 - (m - 1 - (n:ℤ)) = (n:ℤ) by ring, Int.toNat_natCast]
      right_inv := by
        intro x
        ext
        show m - 1 - (((m - 1 - (x:ℤ)).toNat) : ℤ) = (x:ℤ)
        have hx : (x:ℤ) ≤ m - 1 := Int.le_sub_one_of_lt x.2
        rw [Int.toNat_sub_of_le (a := m - 1) (b := (x:ℤ)) hx]; ring }
  rw [← Equiv.tsum_eq e (fun a : {x : ℤ | x < m} => f ↑a)]
  rfl

lemma toNat_sub_injOn {m : ℤ} {s : Finset ℤ} (hm_le : ∀ k ∈ s, m ≤ k) :
    Set.InjOn (fun k : ℤ => (k - m).toNat) ↑s := by
  intro a ha b hb hab
  have h2 : ((a - m).toNat : ℤ) = ((b - m).toNat : ℤ) := by exact_mod_cast hab
  rw [Int.toNat_sub_of_le (hm_le a ha), Int.toNat_sub_of_le (hm_le b hb)] at h2
  omega

lemma tail_reindex {g : ℤ → ℝ} {m : ℤ} {s : Finset ℤ} (hs : ∀ n, n ∉ s → g n = 0)
    (hm_le : ∀ k ∈ s, m ≤ k) (y : ℕ) :
    (∑' k : ℤ, |g k| / ((k:ℝ) - (m:ℝ) + (y:ℝ) + 1))
      = ∑ i ∈ s.image (fun k : ℤ => (k - m).toNat), |g (m + i)| / ((i:ℝ) + (y:ℝ) + 1) := by
  rw [tsum_eq_sum (s := s) (fun k hk => by rw [hs k hk, abs_zero, zero_div])]
  rw [Finset.sum_image (s := s) (f := fun i : ℕ => |g (m + i)| / ((i:ℝ) + (y:ℝ) + 1))
    (g := fun k : ℤ => (k - m).toNat) (toNat_sub_injOn hm_le)]
  apply Finset.sum_congr rfl; intro k hk
  have hj : ((k - m).toNat : ℤ) = k - m := Int.toNat_sub_of_le (hm_le k hk)
  have hk_eq : m + ((k - m).toNat : ℕ) = k := by
    show m + (((k - m).toNat : ℕ) : ℤ) = k; rw [hj]; ring
  have hcast : (((k - m).toNat : ℕ) : ℝ) = (k:ℝ) - (m:ℝ) := by
    have hh := congrArg (fun z : ℤ => (z:ℝ)) hj
    push_cast at hh
    exact hh
  rw [hk_eq]
  congr 1
  rw [hcast]

lemma reindex_pow {g : ℤ → ℝ} {m : ℤ} {s : Finset ℤ} (hm_le : ∀ k ∈ s, m ≤ k) (p : ℝ) :
    ∑ i ∈ s.image (fun k : ℤ => (k - m).toNat), |g (m + i)| ^ p = ∑ k ∈ s, |g k| ^ p := by
  rw [Finset.sum_image (s := s) (f := fun i : ℕ => |g (m + i)| ^ p)
    (g := fun k : ℤ => (k - m).toNat) (toNat_sub_injOn hm_le)]
  apply Finset.sum_congr rfl; intro k hk
  have hj : ((k - m).toNat : ℤ) = k - m := Int.toNat_sub_of_le (hm_le k hk)
  have hk_eq : m + ((k - m).toNat : ℕ) = k := by
    show m + (((k - m).toNat : ℕ) : ℤ) = k; rw [hj]; ring
  rw [hk_eq]

lemma lintegral_enorm_pow_eq {p : ℝ} (hp0 : 0 < p) {g : ℤ → ℝ} {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → g n = 0) :
    ∫⁻ x : ℤ, ‖g x‖ₑ^p ∂Measure.count = ENNReal.ofReal (∑ k ∈ s, |g k|^p) := by
  rw [lintegral_count]
  have hsummable : Summable (fun x : ℤ => |g x|^p) :=
    summable_of_ne_finset_zero (s := s) (fun k hk => by rw [hs k hk, abs_zero, Real.zero_rpow hp0.ne'])
  rw [show (∑' x : ℤ, ‖g x‖ₑ^p) = ∑' x : ℤ, ENNReal.ofReal (|g x|^p) from
        tsum_congr (fun x => by rw [Real.enorm_eq_ofReal_abs,
          ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le])]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) p) hsummable]
  congr 1
  rw [tsum_eq_sum (s := s) (fun k hk => by rw [hs k hk, abs_zero, Real.zero_rpow hp0.ne'])]

theorem lp_bound_uniform {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℝ), (∀ n, 0 ≤ a n) → ∀ (s : Finset ℕ),
      (∀ n, n ∉ s → a n = 0) →
      (∑' y : ℕ, (∑ k ∈ s, a k / ((k : ℝ) + (y : ℝ) + 1)) ^ p)
        ≤ C ^ p * ∑ k ∈ s, (a k) ^ p := by
  set q : ℝ := Real.conjExponent p with hqdef
  set α : ℝ := (2*(p+q))⁻¹ with hαdef
  set θ1 : ℝ := p / (2*(p+q)) with hθ1def
  set θ2 : ℝ := q / (2*(p+q)) with hθ2def
  set w : ℕ → ℝ := fun k => ((k:ℝ)+1)^(-α) with hwdef
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpq : p.HolderConjugate q := by rw [hqdef]; exact Real.HolderConjugate.conjExponent hp
  have hq1 : 1 < q := (Real.holderConjugate_iff.mp hpq.symm).1
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hsum_pos : 0 < 2 * (p + q) := by linarith
  have hθ1pos : 0 < θ1 := by rw [hθ1def]; positivity
  have hθ2pos : 0 < θ2 := by rw [hθ2def]; positivity
  have hθ1lt : θ1 < 1 := by rw [hθ1def, div_lt_one hsum_pos]; linarith
  have hθ2lt : θ2 < 1 := by rw [hθ2def, div_lt_one hsum_pos]; linarith
  have hc1pos : 0 < 1/(θ2*(1-θ2)) := one_div_pos.mpr (mul_pos hθ2pos (by linarith))
  have hc2pos : 0 < 1/(θ1*(1-θ1)) := one_div_pos.mpr (mul_pos hθ1pos (by linarith))
  have hαq : α * q = θ2 := by rw [hαdef, hθ2def]; field_simp
  have hαp : α * p = θ1 := by rw [hαdef, hθ1def]; field_simp
  have hwpos : ∀ n, 0 < w n := by intro n; rw [hwdef]; exact Real.rpow_pos_of_pos (by positivity) _
  have hwq : ∀ k, (w k) ^ q = (((k:ℝ)+1) ^ θ2)⁻¹ := by
    intro k
    rw [hwdef, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (k:ℝ)+1) (-α) q,
        show (-α)*q = -θ2 by rw [neg_mul, hαq], Real.rpow_neg (by positivity : (0:ℝ) ≤ (k:ℝ)+1)]
  have hwp : ∀ k, (w k) ^ p = (((k:ℝ)+1) ^ θ1)⁻¹ := by
    intro k
    rw [hwdef, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (k:ℝ)+1) (-α) p,
        show (-α)*p = -θ1 by rw [neg_mul, hαp], Real.rpow_neg (by positivity : (0:ℝ) ≤ (k:ℝ)+1)]
  have h1 : ∀ y : ℕ, ∀ s : Finset ℕ, ∑ k ∈ s, ((k:ℝ)+(y:ℝ)+1)⁻¹ * (w k) ^ q
      ≤ (1/(θ2*(1-θ2))) * (w y) ^ q := by
    intro y s
    calc ∑ k ∈ s, ((k:ℝ)+(y:ℝ)+1)⁻¹ * (w k) ^ q
        = ∑ k ∈ s, ((k:ℝ)+(y:ℝ)+1)⁻¹ * (((k:ℝ)+1) ^ θ2)⁻¹ := by
          apply Finset.sum_congr rfl; intro k _; rw [hwq k]
      _ ≤ (1/(θ2*(1-θ2))) * (((y:ℝ)+1) ^ θ2)⁻¹ :=
          Commons.Analysis.HilbertMatrix.weight_sum_le hθ2pos hθ2lt s y
      _ = (1/(θ2*(1-θ2))) * (w y) ^ q := by rw [hwq y]
  have h2 : ∀ k : ℕ, ∑' y : ℕ, ((k:ℝ)+(y:ℝ)+1)⁻¹ * (w y) ^ p
      ≤ (1/(θ1*(1-θ1))) * (w k) ^ p := by
    intro k
    have hcongr : (fun y : ℕ => ((k:ℝ)+(y:ℝ)+1)⁻¹ * (w y) ^ p)
        = fun y : ℕ => ((y:ℝ)+(k:ℝ)+1)⁻¹ * (((y:ℝ)+1) ^ θ1)⁻¹ := by
      funext y; rw [hwp y]; congr 1; ring
    rw [hcongr]
    calc ∑' y : ℕ, ((y:ℝ)+(k:ℝ)+1)⁻¹ * (((y:ℝ)+1) ^ θ1)⁻¹
        ≤ (1/(θ1*(1-θ1))) * (((k:ℝ)+1) ^ θ1)⁻¹ :=
          Commons.Analysis.HilbertMatrix.weight_tsum_le hθ1pos hθ1lt k
      _ = (1/(θ1*(1-θ1))) * (w k) ^ p := by rw [hwp k]
  have h2s : ∀ k : ℕ, Summable (fun y : ℕ => ((k:ℝ)+(y:ℝ)+1)⁻¹ * (w y) ^ p) := by
    intro k
    have hcongr : (fun y : ℕ => ((k:ℝ)+(y:ℝ)+1)⁻¹ * (w y) ^ p)
        = fun y : ℕ => ((y:ℝ)+(k:ℝ)+1)⁻¹ * (((y:ℝ)+1) ^ θ1)⁻¹ := by
      funext y; rw [hwp y]; congr 1; ring
    rw [hcongr]
    exact Commons.Analysis.HilbertMatrix.weight_summable hθ1pos hθ1lt k
  have hmain : ∀ (a : ℕ → ℝ) (s : Finset ℕ), (∀ n, 0 ≤ a n) →
      ∑' y : ℕ, (∑ k ∈ s, a k * ((k:ℝ)+(y:ℝ)+1)⁻¹) ^ p
        ≤ (1/(θ2*(1-θ2))) ^ (p/q) * (1/(θ1*(1-θ1))) * ∑ k ∈ s, (a k) ^ p :=
    Commons.Analysis.HilbertMatrix.hilbert_schur (K := fun k y : ℕ => ((k:ℝ)+(y:ℝ)+1)⁻¹)
      (w := w) hpq (fun k y => by positivity) hwpos (by positivity) (by positivity) h1 h2 h2s
  set B : ℝ := (1/(θ2*(1-θ2))) ^ (p/q) * (1/(θ1*(1-θ1))) with hBdef
  have hBpos : 0 < B := by
    rw [hBdef]; exact mul_pos (Real.rpow_pos_of_pos hc1pos _) hc2pos
  have hCpow : (B ^ (1/p)) ^ p = B := by
    rw [← Real.rpow_mul (le_of_lt hBpos) (1/p) p,
        show (1:ℝ)/p * p = 1 by rw [one_div]; exact inv_mul_cancel₀ (ne_of_gt hp0), Real.rpow_one]
  refine ⟨B ^ (1/p), Real.rpow_pos_of_pos hBpos _, ?_⟩
  intro a ha s hs
  have hb := hmain a s ha
  calc ∑' y : ℕ, (∑ k ∈ s, a k / ((k : ℝ) + (y : ℝ) + 1)) ^ p
      = ∑' y : ℕ, (∑ k ∈ s, a k * ((k:ℝ)+(y:ℝ)+1)⁻¹) ^ p := by simp_rw [div_eq_mul_inv]
    _ ≤ B * ∑ k ∈ s, (a k) ^ p := hb
    _ = (B ^ (1/p)) ^ p * ∑ k ∈ s, (a k) ^ p := by rw [hCpow]

theorem forward_maximal_z {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℤ → ℝ), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ x, (⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (x + j)‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖g x‖ₑ ^ p ∂Measure.count := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := discrete_forward_maximal hp
  obtain ⟨C_H, hCHpos, hCH⟩ := lp_bound_uniform hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hC1p : 0 < C₁ ^ p := Real.rpow_pos_of_pos hC₁pos p
  have hCHp : 0 < C_H ^ p := Real.rpow_pos_of_pos hCHpos p
  have hApos : 0 < C₁ ^ p + C_H ^ p := by linarith
  refine ⟨(C₁ ^ p + C_H ^ p) ^ (1/p), Real.rpow_pos_of_pos hApos _, ?_⟩
  have hCp : ((C₁ ^ p + C_H ^ p) ^ (1/p)) ^ p = C₁ ^ p + C_H ^ p := by
    rw [← Real.rpow_mul hApos.le (1/p) p, div_mul_cancel₀ 1 hp0.ne', Real.rpow_one]
  intro g hg
  obtain ⟨s, hs⟩ := hg
  set m : ℤ := if h : s.Nonempty then (s.min' h : ℤ) else 0 with hmdef
  have hm_le : ∀ k ∈ s, m ≤ k := by
    intro k hk
    rw [hmdef]
    by_cases hne : s.Nonempty
    · rw [dif_pos hne]; exact Finset.min'_le s k hk
    · rw [dif_neg hne]
      exact absurd hk (by rw [Finset.not_nonempty_iff_eq_empty.mp hne]; exact Finset.notMem_empty k)
  have hg0 : ∀ n, n < m → g n = 0 := by
    intro n hn
    exact hs n (fun hns => absurd (hm_le n hns) (not_le.mpr hn))
  set s'' : Finset ℕ := s.image (fun k : ℤ => (k - m).toNat) with hs''
  set a : ℕ → ℝ := fun i => |g (m + i)| with ha
  have hψsupp : ∀ i, i ∉ s'' → g (m + i) = 0 := by
    intro i hi
    apply hs
    intro hmi
    exact hi (by
      rw [hs'', Finset.mem_image]
      exact ⟨m + i, hmi, by rw [add_sub_cancel_left, Int.toNat_natCast]⟩)
  have ha_supp : ∀ i, i ∉ s'' → a i = 0 := by
    intro i hi
    show |g (m + i)| = 0
    rw [hψsupp i hi, abs_zero]
  have hZm : ∫⁻ x : ℤ, ‖g x‖ₑ^p ∂Measure.count = ENNReal.ofReal (∑ k ∈ s, |g k|^p) :=
    lintegral_enorm_pow_eq hp0 hs
  have hR : ∫⁻ x in {x : ℤ | m ≤ x}, (fwdMaxZ g x)^p ∂Measure.count
      ≤ ENNReal.ofReal (C₁^p) * ∫⁻ x, ‖g x‖ₑ^p ∂Measure.count := by
    rw [shift_Ici m (fun x => (fwdMaxZ g x)^p)]
    have hcong : (fun n : ℕ => (fwdMaxZ g (m+n))^p)
        = (fun n : ℕ => (fwdMaxN (fun k : ℕ => g (m+k)) n)^p) := by
      funext n; rw [fwdMaxZ_shift]
    rw [hcong]
    have hN := hC₁ (fun k : ℕ => g (m + k)) ⟨s'', hψsupp⟩
    refine hN.trans ?_
    apply mul_le_mul_of_nonneg_left _ bot_le
    rw [← shift_Ici m (fun x => ‖g x‖ₑ^p)]
    exact setLIntegral_le_lintegral _ _
  have hHznn : ∀ y : ℕ, 0 ≤ ∑ i ∈ s'', a i / ((i:ℝ)+(y:ℝ)+1) := by
    intro y; apply Finset.sum_nonneg; intro i _
    exact div_nonneg (abs_nonneg _) (by positivity)
  have hT : ∫⁻ x in {x : ℤ | x < m}, (fwdMaxZ g x)^p ∂Measure.count
      ≤ ENNReal.ofReal (C_H^p) * ∫⁻ x, ‖g x‖ₑ^p ∂Measure.count := by
    rw [shift_Iio m (fun x => (fwdMaxZ g x)^p)]
    set Hz : ℕ → ℝ := fun y => ∑ i ∈ s'', a i / ((i:ℝ)+(y:ℝ)+1) with hHz
    have hHznn' : ∀ y, 0 ≤ Hz y := fun y => hHznn y
    have hpsumm : Summable (fun n : ℕ => 1 / (((n:ℝ)+1))^p) := by
      have h := (Real.summable_one_div_nat_rpow (p := p)).mpr hp
      have h2 : (fun n : ℕ => 1 / (((n:ℝ)+1))^p) = (fun n : ℕ => 1 / (((n+1:ℕ):ℝ))^p) := by
        funext n; rw [Nat.cast_add, Nat.cast_one]
      rw [h2]
      exact (summable_nat_add_iff 1).mpr h
    have hA_nn : 0 ≤ ∑ i ∈ s'', a i := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hHzsum : Summable (fun n : ℕ => Hz n ^ p) :=
      Summable.of_nonneg_of_le
        (f := fun n : ℕ => (∑ i ∈ s'', a i)^p * (1 / ((n:ℝ)+1)^p))
        (fun n => Real.rpow_nonneg (hHznn' n) p)
        (fun n => by
          have hb : Hz n ≤ (∑ i ∈ s'', a i) / ((n:ℝ)+1) := by
            rw [hHz]
            calc ∑ i ∈ s'', a i / ((i:ℝ)+(n:ℝ)+1)
                ≤ ∑ i ∈ s'', a i / ((n:ℝ)+1) := by
                  apply Finset.sum_le_sum; intro i hi
                  show |g (m + (i:ℤ))| / ((i:ℝ)+(n:ℝ)+1) ≤ |g (m + (i:ℤ))| / ((n:ℝ)+1)
                  have h1 : (0:ℝ) < (n:ℝ)+1 := by positivity
                  have h2 : (n:ℝ)+1 ≤ (i:ℝ)+(n:ℝ)+1 := by
                    have hi : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i; linarith
                  have h3 : ((i:ℝ)+(n:ℝ)+1)⁻¹ ≤ ((n:ℝ)+1)⁻¹ :=
                    (inv_le_inv₀ (by positivity) h1).mpr h2
                  rw [div_eq_mul_inv, div_eq_mul_inv]
                  exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
              _ = (∑ i ∈ s'', a i) / ((n:ℝ)+1) := by rw [Finset.sum_div]
          calc Hz n ^ p ≤ ((∑ i ∈ s'', a i) / ((n:ℝ)+1)) ^ p :=
                Real.rpow_le_rpow (hHznn' n) hb hp0.le
            _ = (∑ i ∈ s'', a i)^p / ((n:ℝ)+1)^p := Real.div_rpow hA_nn (by positivity) p
            _ = (∑ i ∈ s'', a i)^p * (1 / ((n:ℝ)+1)^p) := by rw [mul_one_div])
        (hpsumm.mul_left ((∑ i ∈ s'', a i)^p))
    have hHilb : (∑' n, Hz n ^ p) ≤ C_H ^ p * ∑ i ∈ s'', a i ^ p := by
      have hh := hCH a (fun i => abs_nonneg _) s'' ha_supp
      have : (∑' y : ℕ, Hz y ^ p) = ∑' y : ℕ, (∑ k ∈ s'', a k / ((k:ℝ)+(y:ℝ)+1))^p := by
        apply tsum_congr; intro y; rw [hHz]
      rw [this]; exact hh
    have hpt : ∀ n : ℕ, (fwdMaxZ g (m - 1 - n))^p ≤ ENNReal.ofReal (Hz (n+1)^p) := by
      intro n
      have hHnn : 0 ≤ Hz (n+1) := hHznn' (n+1)
      rw [← ENNReal.ofReal_rpow_of_nonneg hHnn hp0.le]
      apply ENNReal.rpow_le_rpow _ hp0.le
      have h1 := fwdMaxZ_tail_le hg0 hs (n+1)
      rw [show m - 1 - (n:ℤ) = m - ((n+1:ℕ):ℤ) by push_cast; ring]
      refine h1.trans (le_of_eq ?_)
      rw [hHz, ha, tail_reindex hs hm_le (n+1)]
    calc ∫⁻ n : ℕ, (fwdMaxZ g (m - 1 - n))^p ∂Measure.count
        ≤ ∫⁻ n : ℕ, ENNReal.ofReal (Hz (n+1)^p) ∂Measure.count := lintegral_mono hpt
      _ = ∑' n : ℕ, ENNReal.ofReal (Hz (n+1)^p) := lintegral_count _
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (Hz n ^ p) := tsum_succ_le (fun n => ENNReal.ofReal (Hz n ^ p))
      _ = ENNReal.ofReal (∑' n, Hz n ^ p) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun n => Real.rpow_nonneg (hHznn' n) p) hHzsum).symm
      _ ≤ ENNReal.ofReal (C_H^p * ∑ i ∈ s'', a i^p) := ENNReal.ofReal_le_ofReal hHilb
      _ = ENNReal.ofReal (C_H^p) * ENNReal.ofReal (∑ i ∈ s'', a i^p) :=
          ENNReal.ofReal_mul (Real.rpow_nonneg hCHpos.le p)
      _ = ENNReal.ofReal (C_H^p) * ∫⁻ x, ‖g x‖ₑ^p ∂Measure.count := by
          congr 1
          rw [ha, reindex_pow hm_le p, ← hZm]
  change (∫⁻ x : ℤ, (fwdMaxZ g x)^p ∂Measure.count)
      ≤ ENNReal.ofReal (((C₁^p + C_H^p)^(1/p))^p) * ∫⁻ x, ‖g x‖ₑ^p ∂Measure.count
  rw [hCp]
  have hsmeas : MeasurableSet {x : ℤ | x < m} := measurableSet_lt measurable_id measurable_const
  rw [← lintegral_add_compl (fun x => (fwdMaxZ g x)^p) hsmeas]
  rw [show {x : ℤ | x < m}ᶜ = {x : ℤ | m ≤ x} by ext x; simp [not_lt]]
  refine (add_le_add hT hR).trans ?_
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ bot_le
  rw [← ENNReal.ofReal_add (Real.rpow_nonneg hCHpos.le p) (Real.rpow_nonneg hC₁pos.le p)]
  apply ENNReal.ofReal_le_ofReal
  linarith [hCp]


end Commons.Analysis.HardyLittlewood
