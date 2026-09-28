import Mathlib
import Submission.Work.HP.MDEstimates.geom_min_k_sum

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Work.HP.MDEstimates

variable {γ : Type}

private lemma indicator_inv_prod {c1 c2 c3 c4 : ℝ} {P1 P2 P3 P4 : Prop}
    [Decidable P1] [Decidable P2] [Decidable P3] [Decidable P4] :
    (if P1 then c1 else 0) * (if P2 then c2 else 0) * (if P3 then c3 else 0) * (if P4 then c4 else 0)
      = (c1*c2*c3*c4) * (if (P1 ∧ P2 ∧ P3 ∧ P4) then (1:ℝ) else 0) := by
  by_cases h1 : P1 <;> by_cases h2 : P2 <;> by_cases h3 : P3 <;> by_cases h4 : P4 <;>
    simp_all

private lemma sum2_mul (K L : Finset ℕ) (a : ℝ) (f g : ℕ → ℝ) :
    (∑ k ∈ K, ∑ l ∈ L, a * f k * g l) = a * (∑ k ∈ K, f k) * (∑ l ∈ L, g l) := by
  have h1 : ∀ k, (∑ l ∈ L, a * f k * g l) = (a * f k) * (∑ l ∈ L, g l) := by
    intro k; rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun k _ => h1 k), ← Finset.sum_mul, ← Finset.mul_sum]

private lemma sum4_mul (I J K L : Finset ℕ) (A B C D : ℕ → ℝ) :
    (∑ i ∈ I, A i) * (∑ j ∈ J, B j) * (∑ k ∈ K, C k) * (∑ l ∈ L, D l)
      = ∑ i ∈ I, ∑ j ∈ J, ∑ k ∈ K, ∑ l ∈ L, A i * B j * C k * D l := by
  have e1 : (∑ i ∈ I, A i) * (∑ j ∈ J, B j) = ∑ i ∈ I, ∑ j ∈ J, A i * B j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.mul_sum]
  have e2 : (∑ i ∈ I, ∑ j ∈ J, A i * B j) * (∑ k ∈ K, C k)
      = ∑ i ∈ I, ∑ j ∈ J, ∑ k ∈ K, A i * B j * C k := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j hj
    rw [Finset.mul_sum]
  have e3 : (∑ i ∈ I, ∑ j ∈ J, ∑ k ∈ K, A i * B j * C k) * (∑ l ∈ L, D l)
      = ∑ i ∈ I, ∑ j ∈ J, ∑ k ∈ K, ∑ l ∈ L, A i * B j * C k * D l := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j hj
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k hk
    rw [Finset.mul_sum]
  rw [e1, e2, e3]

private lemma swap4 (S : Finset γ) (I J K L : Finset ℕ)
    (f : γ → ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ p ∈ S, ∑ i ∈ I, ∑ j ∈ J, ∑ k ∈ K, ∑ l ∈ L, f p i j k l)
    = ∑ i ∈ I, ∑ j ∈ J, ∑ k ∈ K, ∑ l ∈ L, ∑ p ∈ S, f p i j k l := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k hk
  rw [Finset.sum_comm]

private lemma card_filter_cast (S : Finset γ) (P : γ → Prop) [DecidablePred P] :
    ((S.filter P).card : ℝ) = ∑ p ∈ S, (if P p then (1:ℝ) else 0) := by
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl; intro p hp
  by_cases h : P p <;> simp [h]

private lemma min_le_rpow_mul {a b θ φ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hsum : θ + φ = 1) : min a b ≤ a^θ * b^φ := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    calc a = a^(θ+φ) := by rw [hsum, Real.rpow_one]
      _ = a^θ * a^φ := Real.rpow_add ha θ φ
      _ ≤ a^θ * b^φ := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ha.le θ)
          exact Real.rpow_le_rpow ha.le h hφ
  · rw [min_eq_right h]
    calc b = b^(θ+φ) := by rw [hsum, Real.rpow_one]
      _ = b^θ * b^φ := Real.rpow_add hb θ φ
      _ ≤ a^θ * b^φ := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hb.le φ)
          exact Real.rpow_le_rpow hb.le h hθ

private lemma rpow_combine {K2 K3 : ℝ} (hK2 : 0 < K2) (hK3 : 0 < K3) (e2 e3 a2 a3 W : ℝ) :
    (2:ℝ)^(-W) * (K2 * (2:ℝ)^a2)^e2 * (K3 * (2:ℝ)^a3)^e3
      = K2^e2 * K3^e3 * (2:ℝ)^(a2*e2 + a3*e3 - W) := by
  rw [Real.mul_rpow hK2.le (Real.rpow_nonneg (by norm_num) a2),
      Real.mul_rpow hK3.le (Real.rpow_nonneg (by norm_num) a3)]
  rw [← Real.rpow_mul (by norm_num) a2 e2, ← Real.rpow_mul (by norm_num) a3 e3]
  rw [show (2:ℝ)^(-W) * (K2^e2 * (2:ℝ)^(a2*e2)) * (K3^e3 * (2:ℝ)^(a3*e3))
      = K2^e2 * K3^e3 * ((2:ℝ)^(-W) * (2:ℝ)^(a2*e2) * (2:ℝ)^(a3*e3)) by ring]
  congr 1
  rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  ring_nf

private lemma dyadic_layercake (z : ℝ) (hz : 1 ≤ z) (m N : ℕ) (hN : z ≤ (2:ℝ)^N) :
    1 / z^m ≤ (2:ℝ)^m * ∑ i ∈ Finset.range (N+1),
      (if z ≤ (2:ℝ)^i then ((2:ℝ)^(m*i))⁻¹ else 0) := by
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hlog0 : 0 ≤ Real.logb 2 z := Real.logb_nonneg (by norm_num) hz
  set i0 : ℕ := Nat.ceil (Real.logb 2 z) with hi0def
  have hzlei0 : z ≤ (2:ℝ)^i0 := by
    have h := (Real.logb_le_iff_le_rpow (show (1:ℝ) < 2 by norm_num) hzpos).mp
      (Nat.le_ceil (Real.logb 2 z))
    rw [← hi0def] at h
    rwa [Real.rpow_natCast] at h
  have hi0leN : i0 ≤ N := by
    rw [hi0def, Nat.ceil_le]
    rw [Real.logb_le_iff_le_rpow (show (1:ℝ) < 2 by norm_num) hzpos, Real.rpow_natCast]
    exact hN
  have h2i0 : (2:ℝ)^i0 ≤ 2 * z := by
    have hlt : ((i0:ℕ):ℝ) < Real.logb 2 z + 1 := by
      rw [hi0def]; exact Nat.ceil_lt_add_one hlog0
    calc (2:ℝ)^i0 = (2:ℝ)^((i0:ℕ):ℝ) := by rw [Real.rpow_natCast]
      _ ≤ (2:ℝ)^(Real.logb 2 z + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hlt.le
      _ = 2 * z := by
          rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hzpos,
              Real.rpow_one]
          ring
  have hi0mem : i0 ∈ Finset.range (N+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi0leN)
  have hnonneg : ∀ i ∈ Finset.range (N+1),
      0 ≤ (if z ≤ (2:ℝ)^i then ((2:ℝ)^(m*i))⁻¹ else 0) := by
    intro i _; split <;> positivity
  have hsingle : ((2:ℝ)^(m*i0))⁻¹ ≤
      ∑ i ∈ Finset.range (N+1), (if z ≤ (2:ℝ)^i then ((2:ℝ)^(m*i))⁻¹ else 0) := by
    rw [show ((2:ℝ)^(m*i0))⁻¹ = (if z ≤ (2:ℝ)^i0 then ((2:ℝ)^(m*i0))⁻¹ else 0)
          from (ite_eq_left hzlei0).symm]
    exact Finset.single_le_sum hnonneg hi0mem
  have hkey : 1 / z^m ≤ (2:ℝ)^m * ((2:ℝ)^(m*i0))⁻¹ := by
    have heq : (2:ℝ)^m * ((2:ℝ)^(m*i0))⁻¹ = ((2:ℝ) / (2:ℝ)^i0)^m := by
      rw [show (2:ℝ)^(m*i0) = ((2:ℝ)^i0)^m by rw [mul_comm, pow_mul]]
      rw [← inv_pow, ← mul_pow]
      rfl
    rw [heq, show (1:ℝ)/z^m = (1/z)^m by rw [div_pow, one_pow]]
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_div_iff₀ hzpos (by positivity)]
    simpa using h2i0
  calc 1 / z^m ≤ (2:ℝ)^m * ((2:ℝ)^(m*i0))⁻¹ := hkey
    _ ≤ (2:ℝ)^m * ∑ i ∈ Finset.range (N+1),
          (if z ≤ (2:ℝ)^i then ((2:ℝ)^(m*i))⁻¹ else 0) :=
        mul_le_mul_of_nonneg_left hsingle (by positivity)

private lemma four_factor_bound (x y z w : ℝ) (d Nx Ny Mz Mw : ℕ)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) (hw : 1 ≤ w)
    (hxN : x ≤ (2:ℝ)^Nx) (hyN : y ≤ (2:ℝ)^Ny)
    (hzM : z ≤ (2:ℝ)^Mz) (hwM : w ≤ (2:ℝ)^Mw) :
    1/(z * w * x^(d-2) * y^(d-2)) ≤ (2:ℝ)^(2*(d-2)+2) *
      (∑ i ∈ Finset.range (Nx+1), ∑ j ∈ Finset.range (Ny+1),
        ∑ k ∈ Finset.range (Mz+1), ∑ l ∈ Finset.range (Mw+1),
        (if (x ≤ (2:ℝ)^i ∧ y ≤ (2:ℝ)^j ∧ z ≤ (2:ℝ)^k ∧ w ≤ (2:ℝ)^l)
          then (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) else 0)) := by
  have hA := dyadic_layercake x hx (d-2) Nx hxN
  have hB := dyadic_layercake y hy (d-2) Ny hyN
  have hC := dyadic_layercake z hz 1 Mz hzM
  have hD := dyadic_layercake w hw 1 Mw hwM
  let Sx : ℝ := ∑ i ∈ Finset.range (Nx+1), (if x ≤ (2:ℝ)^i then ((2:ℝ)^((d-2)*i))⁻¹ else 0)
  let Sy : ℝ := ∑ j ∈ Finset.range (Ny+1), (if y ≤ (2:ℝ)^j then ((2:ℝ)^((d-2)*j))⁻¹ else 0)
  let Sz : ℝ := ∑ k ∈ Finset.range (Mz+1), (if z ≤ (2:ℝ)^k then ((2:ℝ)^k)⁻¹ else 0)
  let Sw : ℝ := ∑ l ∈ Finset.range (Mw+1), (if w ≤ (2:ℝ)^l then ((2:ℝ)^l)⁻¹ else 0)
  have hA' : 1 / x^(d-2) ≤ (2:ℝ)^(d-2) * Sx := hA
  have hB' : 1 / y^(d-2) ≤ (2:ℝ)^(d-2) * Sy := hB
  have hC' : 1 / z ≤ (2:ℝ)^1 * Sz := by simpa only [pow_one, one_mul] using hC
  have hD' : 1 / w ≤ (2:ℝ)^1 * Sw := by simpa only [pow_one, one_mul] using hD
  have hSxnn : 0 ≤ Sx := by
    dsimp only [Sx]; apply Finset.sum_nonneg; intro i _; split <;> positivity
  have hSynn : 0 ≤ Sy := by
    dsimp only [Sy]; apply Finset.sum_nonneg; intro j _; split <;> positivity
  have hSznn : 0 ≤ Sz := by
    dsimp only [Sz]; apply Finset.sum_nonneg; intro k _; split <;> positivity
  have hSwnn : 0 ≤ Sw := by
    dsimp only [Sw]; apply Finset.sum_nonneg; intro l _; split <;> positivity
  have hgp : 1/(z * w * x^(d-2) * y^(d-2)) = (1/x^(d-2)) * (1/y^(d-2)) * (1/z) * (1/w) := by
    field_simp
  rw [hgp]
  have hprod : (1/x^(d-2)) * (1/y^(d-2)) * (1/z) * (1/w)
      ≤ ((2:ℝ)^(d-2) * Sx) * ((2:ℝ)^(d-2) * Sy) * ((2:ℝ)^1 * Sz) * ((2:ℝ)^1 * Sw) := by
    rw [show (1/x^(d-2)) * (1/y^(d-2)) * (1/z) * (1/w)
        = ((1/x^(d-2)) * (1/y^(d-2))) * ((1/z) * (1/w)) by ring]
    rw [show ((2:ℝ)^(d-2) * Sx) * ((2:ℝ)^(d-2) * Sy) * ((2:ℝ)^1 * Sz) * ((2:ℝ)^1 * Sw)
        = (((2:ℝ)^(d-2) * Sx) * ((2:ℝ)^(d-2) * Sy)) * (((2:ℝ)^1 * Sz) * ((2:ℝ)^1 * Sw)) by ring]
    refine mul_le_mul (mul_le_mul hA' hB' (by positivity) (mul_nonneg (by positivity) hSxnn))
      (mul_le_mul hC' hD' (by positivity) (mul_nonneg (by positivity) hSznn))
      (by positivity) (by positivity)
  have hpow : (2:ℝ)^(d-2) * (2:ℝ)^(d-2) * (2:ℝ)^1 * (2:ℝ)^1 = (2:ℝ)^(2*(d-2)+2) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  have hcombine : ((2:ℝ)^(d-2) * Sx) * ((2:ℝ)^(d-2) * Sy) * ((2:ℝ)^1 * Sz) * ((2:ℝ)^1 * Sw)
      = (2:ℝ)^(2*(d-2)+2) * (Sx * Sy * Sz * Sw) := by
    rw [show ((2:ℝ)^(d-2) * Sx) * ((2:ℝ)^(d-2) * Sy) * ((2:ℝ)^1 * Sz) * ((2:ℝ)^1 * Sw)
        = ((2:ℝ)^(d-2) * (2:ℝ)^(d-2) * (2:ℝ)^1 * (2:ℝ)^1) * (Sx * Sy * Sz * Sw) by ring]
    rw [hpow]
  have hsum4 : Sx * Sy * Sz * Sw
      = ∑ i ∈ Finset.range (Nx+1), ∑ j ∈ Finset.range (Ny+1),
        ∑ k ∈ Finset.range (Mz+1), ∑ l ∈ Finset.range (Mw+1),
          (if x ≤ (2:ℝ)^i then ((2:ℝ)^((d-2)*i))⁻¹ else 0)
          * (if y ≤ (2:ℝ)^j then ((2:ℝ)^((d-2)*j))⁻¹ else 0)
          * (if z ≤ (2:ℝ)^k then ((2:ℝ)^k)⁻¹ else 0)
          * (if w ≤ (2:ℝ)^l then ((2:ℝ)^l)⁻¹ else 0) := by
    dsimp only [Sx, Sy, Sz, Sw]
    rw [sum4_mul]
  have hsummand : ∀ i j k l,
      (if x ≤ (2:ℝ)^i then ((2:ℝ)^((d-2)*i))⁻¹ else 0)
      * (if y ≤ (2:ℝ)^j then ((2:ℝ)^((d-2)*j))⁻¹ else 0)
      * (if z ≤ (2:ℝ)^k then ((2:ℝ)^k)⁻¹ else 0)
      * (if w ≤ (2:ℝ)^l then ((2:ℝ)^l)⁻¹ else 0)
      = (if (x ≤ (2:ℝ)^i ∧ y ≤ (2:ℝ)^j ∧ z ≤ (2:ℝ)^k ∧ w ≤ (2:ℝ)^l)
          then (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) else 0) := by
    intro i j k l
    rw [indicator_inv_prod]
    have hc : ((2:ℝ)^((d-2)*i))⁻¹ * ((2:ℝ)^((d-2)*j))⁻¹ * ((2:ℝ)^k)⁻¹ * ((2:ℝ)^l)⁻¹
        = (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) := by
      rw [← mul_inv, ← mul_inv, ← mul_inv]
      rw [← pow_add, ← pow_add, ← pow_add]
      rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
    rw [hc]
    by_cases h : (x ≤ (2:ℝ)^i ∧ y ≤ (2:ℝ)^j ∧ z ≤ (2:ℝ)^k ∧ w ≤ (2:ℝ)^l) <;> simp [h]
  have hsum_eq : (∑ i ∈ Finset.range (Nx+1), ∑ j ∈ Finset.range (Ny+1),
        ∑ k ∈ Finset.range (Mz+1), ∑ l ∈ Finset.range (Mw+1),
          (if x ≤ (2:ℝ)^i then ((2:ℝ)^((d-2)*i))⁻¹ else 0)
          * (if y ≤ (2:ℝ)^j then ((2:ℝ)^((d-2)*j))⁻¹ else 0)
          * (if z ≤ (2:ℝ)^k then ((2:ℝ)^k)⁻¹ else 0)
          * (if w ≤ (2:ℝ)^l then ((2:ℝ)^l)⁻¹ else 0))
      = (∑ i ∈ Finset.range (Nx+1), ∑ j ∈ Finset.range (Ny+1),
        ∑ k ∈ Finset.range (Mz+1), ∑ l ∈ Finset.range (Mw+1),
        (if (x ≤ (2:ℝ)^i ∧ y ≤ (2:ℝ)^j ∧ z ≤ (2:ℝ)^k ∧ w ≤ (2:ℝ)^l)
          then (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) else 0)) := by
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    apply Finset.sum_congr rfl; intro k hk
    apply Finset.sum_congr rfl; intro l hl
    exact hsummand i j k l
  calc (1/x^(d-2)) * (1/y^(d-2)) * (1/z) * (1/w)
      ≤ ((2:ℝ)^(d-2) * Sx) * ((2:ℝ)^(d-2) * Sy) * ((2:ℝ)^1 * Sz) * ((2:ℝ)^1 * Sw) := hprod
    _ = (2:ℝ)^(2*(d-2)+2) * (Sx * Sy * Sz * Sw) := hcombine
    _ = (2:ℝ)^(2*(d-2)+2) * (∑ i ∈ Finset.range (Nx+1), ∑ j ∈ Finset.range (Ny+1),
          ∑ k ∈ Finset.range (Mz+1), ∑ l ∈ Finset.range (Mw+1),
            (if x ≤ (2:ℝ)^i then ((2:ℝ)^((d-2)*i))⁻¹ else 0)
            * (if y ≤ (2:ℝ)^j then ((2:ℝ)^((d-2)*j))⁻¹ else 0)
            * (if z ≤ (2:ℝ)^k then ((2:ℝ)^k)⁻¹ else 0)
            * (if w ≤ (2:ℝ)^l then ((2:ℝ)^l)⁻¹ else 0)) := by rw [hsum4]
    _ = (2:ℝ)^(2*(d-2)+2) * (∑ i ∈ Finset.range (Nx+1), ∑ j ∈ Finset.range (Ny+1),
          ∑ k ∈ Finset.range (Mz+1), ∑ l ∈ Finset.range (Mw+1),
          (if (x ≤ (2:ℝ)^i ∧ y ≤ (2:ℝ)^j ∧ z ≤ (2:ℝ)^k ∧ w ≤ (2:ℝ)^l)
            then (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) else 0)) := by rw [hsum_eq]

private lemma cnt_le_A2 (n : ℕ) (S : Finset γ) (X Y D2 D3 : γ → ℝ) (K2 : ℝ) (i j k l : ℕ)
    (hC2 : ∀ A B Δ : ℝ, 1 ≤ A → 1 ≤ B → 1 ≤ Δ →
      ((S.filter fun p => X p ≤ A ∧ Y p ≤ B ∧ D2 p ≤ Δ).card : ℝ) ≤ K2 * A^2 * B^2 * Δ^(n-1))
    (hmul : ∀ p ∈ S, D2 p ≤ X p * Y p)
    (hY1 : ∀ p ∈ S, 1 ≤ Y p) :
    ((S.filter fun p => X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l).card : ℝ)
      ≤ K2 * (2:ℝ)^(((2*i+2*j+(n-1)*min k (i+j) : ℕ)) : ℝ) := by
  have hcard : (S.filter (fun p => X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)).card
      ≤ (S.filter (fun p => X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^(min k (i+j)))).card := by
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hps, h1, h2, h3, h4⟩ := hp
    refine ⟨hps, h1, h2, ?_⟩
    have hXY : X p * Y p ≤ (2:ℝ)^(i+j) := by
      have h := mul_le_mul h1 h2 (le_trans zero_le_one (hY1 p hps)) (by positivity : (0:ℝ) ≤ (2:ℝ)^i)
      rwa [← pow_add] at h
    have h5 : D2 p ≤ (2:ℝ)^(i+j) := le_trans (hmul p hps) hXY
    have hmin : (2:ℝ)^(min k (i+j)) = min ((2:ℝ)^k) ((2:ℝ)^(i+j)) := by
      rcases le_total k (i+j) with h | h
      · rw [min_eq_left h, min_eq_left (pow_le_pow_right₀ (by norm_num) h)]
      · rw [min_eq_right h, min_eq_right (pow_le_pow_right₀ (by norm_num) h)]
    rw [hmin]; exact le_min h3 h5
  have hcnt := hC2 ((2:ℝ)^i) ((2:ℝ)^j) ((2:ℝ)^(min k (i+j)))
    (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have hcast : ((S.filter (fun p => X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧
      D2 p ≤ (2:ℝ)^(min k (i+j)))).card : ℝ)
      ≤ K2 * ((2:ℝ)^i)^2 * ((2:ℝ)^j)^2 * ((2:ℝ)^(min k (i+j)))^(n-1) := hcnt
  have hpow : K2 * ((2:ℝ)^i)^2 * ((2:ℝ)^j)^2 * ((2:ℝ)^(min k (i+j)))^(n-1)
      = K2 * (2:ℝ)^(((2*i+2*j+(n-1)*min k (i+j) : ℕ)) : ℝ) := by
    rw [Real.rpow_natCast, ← pow_mul, ← pow_mul, ← pow_mul]
    rw [show K2 * (2:ℝ)^(i*2) * (2:ℝ)^(j*2) * (2:ℝ)^(min k (i+j)*(n-1))
        = K2 * ((2:ℝ)^(i*2) * (2:ℝ)^(j*2) * (2:ℝ)^(min k (i+j)*(n-1))) by ring]
    congr 1
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  have h1 : (((S.filter (fun p => X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)).card : ℝ))
      ≤ (((S.filter (fun p => X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^(min k (i+j)))).card : ℝ)) := by
    exact_mod_cast hcard
  linarith [h1, hcast, hpow]

private lemma cnt_le_A3 (n : ℕ) (S : Finset γ) (X Y D2 D3 : γ → ℝ) (K3 : ℝ) (i j k l : ℕ)
    (hC3 : ∀ A B Δ : ℝ, 1 ≤ A → 1 ≤ B → 1 ≤ Δ →
      ((S.filter fun p => X p ≤ A ∧ Y p ≤ B ∧ D3 p ≤ Δ).card : ℝ) ≤ K3 * A^3 * B^3 * Δ^(n-1))
    (hmul : ∀ p ∈ S, D3 p ≤ X p * Y p)
    (hY1 : ∀ p ∈ S, 1 ≤ Y p) :
    ((S.filter fun p => X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l).card : ℝ)
      ≤ K3 * (2:ℝ)^(((3*i+3*j+(n-1)*min l (i+j) : ℕ)) : ℝ) := by
  have hcard : (S.filter (fun p => X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)).card
      ≤ (S.filter (fun p => X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D3 p ≤ (2:ℝ)^(min l (i+j)))).card := by
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hps, h1, h2, h3, h4⟩ := hp
    refine ⟨hps, h1, h2, ?_⟩
    have hXY : X p * Y p ≤ (2:ℝ)^(i+j) := by
      have h := mul_le_mul h1 h2 (le_trans zero_le_one (hY1 p hps)) (by positivity : (0:ℝ) ≤ (2:ℝ)^i)
      rwa [← pow_add] at h
    have h5 : D3 p ≤ (2:ℝ)^(i+j) := le_trans (hmul p hps) hXY
    have hmin : (2:ℝ)^(min l (i+j)) = min ((2:ℝ)^l) ((2:ℝ)^(i+j)) := by
      rcases le_total l (i+j) with h | h
      · rw [min_eq_left h, min_eq_left (pow_le_pow_right₀ (by norm_num) h)]
      · rw [min_eq_right h, min_eq_right (pow_le_pow_right₀ (by norm_num) h)]
    rw [hmin]; exact le_min h4 h5
  have hcnt := hC3 ((2:ℝ)^i) ((2:ℝ)^j) ((2:ℝ)^(min l (i+j)))
    (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have hcast : ((S.filter (fun p => X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧
      D3 p ≤ (2:ℝ)^(min l (i+j)))).card : ℝ)
      ≤ K3 * ((2:ℝ)^i)^3 * ((2:ℝ)^j)^3 * ((2:ℝ)^(min l (i+j)))^(n-1) := hcnt
  have hpow : K3 * ((2:ℝ)^i)^3 * ((2:ℝ)^j)^3 * ((2:ℝ)^(min l (i+j)))^(n-1)
      = K3 * (2:ℝ)^(((3*i+3*j+(n-1)*min l (i+j) : ℕ)) : ℝ) := by
    rw [Real.rpow_natCast, ← pow_mul, ← pow_mul, ← pow_mul]
    rw [show K3 * (2:ℝ)^(i*3) * (2:ℝ)^(j*3) * (2:ℝ)^(min l (i+j)*(n-1))
        = K3 * ((2:ℝ)^(i*3) * (2:ℝ)^(j*3) * (2:ℝ)^(min l (i+j)*(n-1))) by ring]
    congr 1
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  have h1 : (((S.filter (fun p => X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)).card : ℝ))
      ≤ (((S.filter (fun p => X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D3 p ≤ (2:ℝ)^(min l (i+j)))).card : ℝ)) := by
    exact_mod_cast hcard
  linarith [h1, hcast, hpow]


theorem layer_cake_min_sum (n d : ℕ) (hn : 3 ≤ n) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : Type) (S : Finset γ) (X Y D2 D3 : γ → ℝ) (K2 K3 R : ℝ),
      1 ≤ K2 → 1 ≤ K3 → 1 ≤ R →
      (∀ p ∈ S, 1 ≤ X p ∧ X p ≤ R) →
      (∀ p ∈ S, 1 ≤ Y p ∧ Y p ≤ R) →
      (∀ p ∈ S, 1 ≤ D2 p ∧ D2 p ≤ X p * Y p) →
      (∀ p ∈ S, 1 ≤ D3 p ∧ D3 p ≤ X p * Y p) →
      (∀ A B Δ : ℝ, 1 ≤ A → 1 ≤ B → 1 ≤ Δ →
        ((S.filter fun p => X p ≤ A ∧ Y p ≤ B ∧ D2 p ≤ Δ).card : ℝ)
          ≤ K2 * A ^ 2 * B ^ 2 * Δ ^ (n - 1)) →
      (∀ A B Δ : ℝ, 1 ≤ A → 1 ≤ B → 1 ≤ Δ →
        ((S.filter fun p => X p ≤ A ∧ Y p ≤ B ∧ D3 p ≤ Δ).card : ℝ)
          ≤ K3 * A ^ 3 * B ^ 3 * Δ ^ (n - 1)) →
      (∑ p ∈ S, 1 / (D2 p * D3 p * X p ^ (d - 2) * Y p ^ (d - 2)))
        ≤ C * K2 ^ (((n : ℝ) - 2) / ((n : ℝ) - 1)) * K3 ^ (1 / ((n : ℝ) - 1)) *
            R ^ (2 * (((2 * (n : ℝ) - 1) / ((n : ℝ) - 1)) + (n : ℝ) - (d : ℝ) - 1)) *
            (Real.log (2 * R)) ^ 8 := by
  set e2 : ℝ := ((n:ℝ)-2)/((n:ℝ)-1) with he2def
  set e3 : ℝ := 1/((n:ℝ)-1) with he3def
  set E : ℝ := (2*(n:ℝ)-1)/((n:ℝ)-1) + (n:ℝ) - (d:ℝ) - 1 with hEdef
  set Ep : ℝ := 2*e2 + 3*e3 - ((d:ℝ)-2) with hEpdef
  have hnR : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn1pos : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hn1ne : ((n:ℝ) - 1) ≠ 0 := ne_of_gt hn1pos
  have he2nn : 0 ≤ e2 := by rw [he2def]; exact div_nonneg (by linarith) hn1pos.le
  have he3nn : 0 ≤ e3 := by rw [he3def]; positivity
  have he2e3 : e2 + e3 = 1 := by
    rw [he2def, he3def, ← add_div]
    rw [show (n:ℝ)-2+1 = (n:ℝ)-1 by ring, div_self hn1ne]
  have he2n1 : e2 * ((n:ℝ)-1) = (n:ℝ) - 2 := by rw [he2def, div_mul_cancel₀ _ hn1ne]
  have he3n1 : e3 * ((n:ℝ)-1) = 1 := by rw [he3def, div_mul_cancel₀ _ hn1ne]
  have hEpE : Ep + ((n:ℝ)-3) = E := by
    rw [hEpdef, hEdef, he2def, he3def]; field_simp; ring
  have hEpos : 0 < E := by
    rw [hEdef]
    have h1 : (1:ℝ) < (2*(n:ℝ)-1)/((n:ℝ)-1) := by
      rw [lt_div_iff₀ hn1pos]; linarith
    have hnd : (0:ℝ) ≤ (n:ℝ) - (d:ℝ) := by
      have : ((d:ℕ):ℝ) ≤ ((n:ℕ):ℝ) := by exact_mod_cast hdn
      linarith
    linarith
  refine ⟨(2:ℝ)^(2*(d-2)+2) * (2:ℝ)^(2*E) * (64/(Real.log 2)^8), ?_, ?_⟩
  · have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · intro γ S X Y D2 D3 K2 K3 R hK2 hK3 hR hX hY hD2 hD3 hC2 hC3
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hK2pos : 0 < K2 := lt_of_lt_of_le zero_lt_one hK2
    have hK3pos : 0 < K3 := lt_of_lt_of_le zero_lt_one hK3
    set Nn : ℕ := Nat.ceil (Real.logb 2 R) with hNndef
    set Mm : ℕ := Nat.ceil (Real.logb 2 (R^2)) with hMmdef
    have hRN : R ≤ (2:ℝ)^Nn := by
      have h := (Real.logb_le_iff_le_rpow (show (1:ℝ) < 2 by norm_num) hRpos).mp
        (Nat.le_ceil (Real.logb 2 R))
      rw [← hNndef] at h
      rwa [Real.rpow_natCast] at h
    have hRRM : R * R ≤ (2:ℝ)^Mm := by
      have hR2pos : 0 < R^2 := by positivity
      have h := (Real.logb_le_iff_le_rpow (show (1:ℝ) < 2 by norm_num) hR2pos).mp
        (Nat.le_ceil (Real.logb 2 (R^2)))
      rw [← hMmdef] at h
      rw [Real.rpow_natCast] at h
      rwa [pow_two] at h
    have hperpoint : ∀ p ∈ S, 1/(D2 p * D3 p * X p^(d-2) * Y p^(d-2)) ≤
        (2:ℝ)^(2*(d-2)+2) * (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
          ∑ k ∈ Finset.range (Mm+1), ∑ l ∈ Finset.range (Mm+1),
          (if (X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)
            then (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) else 0)) := by
      intro p hp
      obtain ⟨hX1, hXR⟩ := hX p hp
      obtain ⟨hY1, hYR⟩ := hY p hp
      obtain ⟨hD21, hD2XY⟩ := hD2 p hp
      obtain ⟨hD31, hD3XY⟩ := hD3 p hp
      have hXYR : X p * Y p ≤ R * R := mul_le_mul hXR hYR (le_trans zero_le_one hY1) hRpos.le
      exact four_factor_bound (X p) (Y p) (D2 p) (D3 p) d Nn Nn Mm Mm hX1 hY1 hD21 hD31
        (le_trans hXR hRN) (le_trans hYR hRN) (le_trans hD2XY (le_trans hXYR hRRM))
        (le_trans hD3XY (le_trans hXYR hRRM))
    have hsum1 : (∑ p ∈ S, 1/(D2 p * D3 p * X p^(d-2) * Y p^(d-2)))
        ≤ (2:ℝ)^(2*(d-2)+2) * (∑ p ∈ S, (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
          ∑ k ∈ Finset.range (Mm+1), ∑ l ∈ Finset.range (Mm+1),
          (if (X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)
            then (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) else 0))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun p hp => hperpoint p hp)
    have hswap := swap4 S (Finset.range (Nn+1)) (Finset.range (Nn+1))
      (Finset.range (Mm+1)) (Finset.range (Mm+1))
      (fun p i j k l => (if (X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)
          then (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) else 0))
    have hinner : ∀ (i j k l : ℕ), (∑ p ∈ S, (if (X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)
            then (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) else 0))
        ≤ K2^e2 * K3^e3 * (2:ℝ)^(Ep*(i+j) + (((n:ℝ)-2)*((min k (i+j) : ℕ) : ℝ) - (k:ℝ))
            + (((min l (i+j) : ℕ) : ℝ) - (l:ℝ))) := by
      intro i j k l
      let cnt : ℝ := ((S.filter (fun p => X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)).card : ℝ)
      have hcnt2 : cnt ≤ K2 * (2:ℝ)^(((2*i+2*j+(n-1)*min k (i+j) : ℕ)) : ℝ) :=
        cnt_le_A2 n S X Y D2 D3 K2 i j k l hC2 (fun p hp => (hD2 p hp).2) (fun p hp => (hY p hp).1)
      have hcnt3 : cnt ≤ K3 * (2:ℝ)^(((3*i+3*j+(n-1)*min l (i+j) : ℕ)) : ℝ) :=
        cnt_le_A3 n S X Y D2 D3 K3 i j k l hC3 (fun p hp => (hD3 p hp).2) (fun p hp => (hY p hp).1)
      have hcnt : cnt ≤ (K2 * (2:ℝ)^(((2*i+2*j+(n-1)*min k (i+j) : ℕ)) : ℝ))^e2
          * (K3 * (2:ℝ)^(((3*i+3*j+(n-1)*min l (i+j) : ℕ)) : ℝ))^e3 :=
        le_trans (le_min hcnt2 hcnt3)
          (min_le_rpow_mul (by positivity) (by positivity) he2nn he3nn he2e3)
      have h1 : (∑ p ∈ S, (if (X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)
            then (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) else 0))
          = (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) * cnt := by
        rw [show (∑ p ∈ S, (if (X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)
              then (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) else 0))
            = ∑ p ∈ S, (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ))
                * (if (X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)
                    then (1:ℝ) else 0) by
              apply Finset.sum_congr rfl; intro p hp
              by_cases h : (X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)
              <;> simp [h]]
        rw [← Finset.mul_sum]
        congr 1
        exact (card_filter_cast S (fun p => X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)).symm
      rw [h1]
      have hexp : ((2*i+2*j+(n-1)*min k (i+j) : ℕ) : ℝ)*e2
            + ((3*i+3*j+(n-1)*min l (i+j) : ℕ) : ℝ)*e3 - ((d-2)*(i+j)+k+l : ℕ)
          = Ep*(i+j) + (((n:ℝ)-2)*((min k (i+j) : ℕ) : ℝ) - (k:ℝ)) + (((min l (i+j) : ℕ) : ℝ) - (l:ℝ)) := by
        push_cast
        rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ d by omega)]
        push_cast
        simp only [hEpdef, he2def, he3def]
        field_simp
        ring
      calc (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) * cnt
          ≤ (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ))
              * ((K2 * (2:ℝ)^(((2*i+2*j+(n-1)*min k (i+j) : ℕ)) : ℝ))^e2
                 * (K3 * (2:ℝ)^(((3*i+3*j+(n-1)*min l (i+j) : ℕ)) : ℝ))^e3) :=
            mul_le_mul_of_nonneg_left hcnt (by positivity)
        _ = (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ))
              * (K2 * (2:ℝ)^(((2*i+2*j+(n-1)*min k (i+j) : ℕ)) : ℝ))^e2
              * (K3 * (2:ℝ)^(((3*i+3*j+(n-1)*min l (i+j) : ℕ)) : ℝ))^e3 := by ring
        _ = K2^e2 * K3^e3 * (2:ℝ)^(((2*i+2*j+(n-1)*min k (i+j) : ℕ) : ℝ)*e2
              + ((3*i+3*j+(n-1)*min l (i+j) : ℕ) : ℝ)*e3 - ((d-2)*(i+j)+k+l : ℕ)) :=
            rpow_combine hK2pos hK3pos e2 e3 _ _ _
        _ = K2^e2 * K3^e3 * (2:ℝ)^(Ep*(i+j) + (((n:ℝ)-2)*((min k (i+j) : ℕ) : ℝ) - (k:ℝ))
              + (((min l (i+j) : ℕ) : ℝ) - (l:ℝ))) := by rw [hexp]
    have hstep : ∀ (i j k l : ℕ),
        (2:ℝ)^(Ep*(i+j) + (((n:ℝ)-2)*((min k (i+j) : ℕ) : ℝ) - (k:ℝ)) + (((min l (i+j) : ℕ) : ℝ) - (l:ℝ)))
        = (2:ℝ)^(Ep*(i+j)) * (2:ℝ)^(((n:ℝ)-2)*((min k (i+j) : ℕ) : ℝ) - (k:ℝ))
          * (2:ℝ)^(((min l (i+j) : ℕ) : ℝ) - (l:ℝ)) := by
      intro i j k l
      rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num)]
    have hkl : ∀ (i j : ℕ), (∑ k ∈ Finset.range (Mm+1), ∑ l ∈ Finset.range (Mm+1),
          (2:ℝ)^(Ep*(i+j)) * (2:ℝ)^(((n:ℝ)-2)*((min k (i+j) : ℕ) : ℝ) - (k:ℝ))
            * (2:ℝ)^(((min l (i+j) : ℕ) : ℝ) - (l:ℝ)))
        = (2:ℝ)^(Ep*(i+j))
            * (∑ k ∈ Finset.range (Mm+1), (2:ℝ)^(((n:ℝ)-2)*((min k (i+j) : ℕ) : ℝ) - (k:ℝ)))
            * (∑ l ∈ Finset.range (Mm+1), (2:ℝ)^(((min l (i+j) : ℕ) : ℝ) - (l:ℝ))) := by
      intro i j; exact sum2_mul _ _ _ _ _
    have hk : ∀ (i j : ℕ), (∑ k ∈ Finset.range (Mm+1), (2:ℝ)^(((n:ℝ)-2)*((min k (i+j) : ℕ) : ℝ) - (k:ℝ)))
        ≤ (((i+j : ℕ):ℝ)+2) * (2:ℝ)^(((n:ℝ)-3)*((i+j : ℕ):ℝ)) :=
      fun i j => by simpa only [Nat.cast_min] using geom_min_k_sum n Mm (i+j) hn
    have hl : ∀ (i j : ℕ), (∑ l ∈ Finset.range (Mm+1), (2:ℝ)^(((min l (i+j) : ℕ) : ℝ) - (l:ℝ)))
        ≤ (((i+j : ℕ):ℝ)+2) := fun i j => by simpa only [Nat.cast_min] using geom_min_k_sum_count Mm (i+j)
    have hbox : (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
          ∑ k ∈ Finset.range (Mm+1), ∑ l ∈ Finset.range (Mm+1),
          (2:ℝ)^(Ep*(i+j) + (((n:ℝ)-2)*((min k (i+j) : ℕ) : ℝ) - (k:ℝ)) + (((min l (i+j) : ℕ) : ℝ) - (l:ℝ))))
        ≤ ((Nn:ℝ)+1)^2 * (2*(Nn:ℝ)+2)^2 * (2:ℝ)^(2*(Nn:ℝ)*E) := by
      calc (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
              ∑ k ∈ Finset.range (Mm+1), ∑ l ∈ Finset.range (Mm+1),
              (2:ℝ)^(Ep*(i+j) + (((n:ℝ)-2)*((min k (i+j) : ℕ) : ℝ) - (k:ℝ)) + (((min l (i+j) : ℕ) : ℝ) - (l:ℝ))))
          = (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
              ∑ k ∈ Finset.range (Mm+1), ∑ l ∈ Finset.range (Mm+1),
              (2:ℝ)^(Ep*(i+j)) * (2:ℝ)^(((n:ℝ)-2)*((min k (i+j) : ℕ) : ℝ) - (k:ℝ))
                * (2:ℝ)^(((min l (i+j) : ℕ) : ℝ) - (l:ℝ))) := by
              apply Finset.sum_congr rfl; intro i hi
              apply Finset.sum_congr rfl; intro j hj
              apply Finset.sum_congr rfl; intro k hk'
              apply Finset.sum_congr rfl; intro l hl'
              exact hstep i j k l
        _ = (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
              (2:ℝ)^(Ep*(i+j))
                * (∑ k ∈ Finset.range (Mm+1), (2:ℝ)^(((n:ℝ)-2)*((min k (i+j) : ℕ) : ℝ) - (k:ℝ)))
                * (∑ l ∈ Finset.range (Mm+1), (2:ℝ)^(((min l (i+j) : ℕ) : ℝ) - (l:ℝ)))) := by
              apply Finset.sum_congr rfl; intro i hi
              apply Finset.sum_congr rfl; intro j hj
              exact hkl i j
        _ ≤ (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
              (2:ℝ)^(Ep*(i+j)) * ((((i+j : ℕ):ℝ)+2) * (2:ℝ)^(((n:ℝ)-3)*((i+j : ℕ):ℝ)))
                * ((((i+j : ℕ):ℝ)+2))) := by
              apply Finset.sum_le_sum; intro i hi
              apply Finset.sum_le_sum; intro j hj
              exact mul_le_mul (mul_le_mul_of_nonneg_left (hk i j) (by positivity)) (hl i j)
                (by positivity) (by positivity)
        _ = (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
              (((i+j : ℕ):ℝ)+2)^2 * (2:ℝ)^(E*((i+j : ℕ):ℝ))) := by
              apply Finset.sum_congr rfl; intro i hi
              apply Finset.sum_congr rfl; intro j hj
              rw [show (2:ℝ)^(Ep*(i+j)) * ((((i+j : ℕ):ℝ)+2) * (2:ℝ)^(((n:ℝ)-3)*((i+j : ℕ):ℝ)))
                    * ((((i+j : ℕ):ℝ)+2)) = (((i+j : ℕ):ℝ)+2)^2 * (2:ℝ)^(E*((i+j : ℕ):ℝ)) by
                    rw [show (2:ℝ)^(Ep*(i+j)) * ((((i+j : ℕ):ℝ)+2) * (2:ℝ)^(((n:ℝ)-3)*((i+j : ℕ):ℝ))) * ((((i+j : ℕ):ℝ)+2))
                        = ((2:ℝ)^(Ep*(i+j)) * (2:ℝ)^(((n:ℝ)-3)*((i+j : ℕ):ℝ))) * ((((i+j : ℕ):ℝ)+2) * ((((i+j : ℕ):ℝ)+2))) by ring]
                    rw [← Real.rpow_add (by norm_num)]
                    rw [show Ep*(i+j) + ((n:ℝ)-3)*((i+j:ℕ):ℝ) = E*((i+j:ℕ):ℝ) by rw [← hEpE, Nat.cast_add]; ring]
                    ring]
        _ ≤ (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
              ((2*(Nn:ℝ)+2)^2 * (2:ℝ)^(2*(Nn:ℝ)*E))) := by
              apply Finset.sum_le_sum; intro i hi
              apply Finset.sum_le_sum; intro j hj
              have hi' : i ≤ Nn := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
              have hj' : j ≤ Nn := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              have hs : (i:ℝ) + (j:ℝ) ≤ 2*(Nn:ℝ) := by
                have h : i + j ≤ 2*Nn := by omega
                exact_mod_cast h
              refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
              · apply pow_le_pow_left₀ (by positivity)
                push_cast; linarith [hs]
              · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
                rw [Nat.cast_add]
                nlinarith [hEpos.le, hs]
        _ = ((Nn:ℝ)+1)^2 * (2*(Nn:ℝ)+2)^2 * (2:ℝ)^(2*(Nn:ℝ)*E) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              push_cast; ring
    have hcomb2 : (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
          ∑ k ∈ Finset.range (Mm+1), ∑ l ∈ Finset.range (Mm+1),
          ∑ p ∈ S, (if (X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)
            then (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) else 0))
        ≤ K2^e2 * K3^e3 * (((Nn:ℝ)+1)^2 * (2*(Nn:ℝ)+2)^2 * (2:ℝ)^(2*(Nn:ℝ)*E)) := by
      calc (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
              ∑ k ∈ Finset.range (Mm+1), ∑ l ∈ Finset.range (Mm+1),
              ∑ p ∈ S, (if (X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)
                then (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) else 0))
          ≤ (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
              ∑ k ∈ Finset.range (Mm+1), ∑ l ∈ Finset.range (Mm+1),
              K2^e2 * K3^e3 * (2:ℝ)^(Ep*(i+j) + (((n:ℝ)-2)*((min k (i+j) : ℕ) : ℝ) - (k:ℝ))
                + (((min l (i+j) : ℕ) : ℝ) - (l:ℝ)))) := by
              apply Finset.sum_le_sum; intro i hi
              apply Finset.sum_le_sum; intro j hj
              apply Finset.sum_le_sum; intro k hk'
              apply Finset.sum_le_sum; intro l hl'
              exact hinner i j k l
        _ = K2^e2 * K3^e3 * (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
              ∑ k ∈ Finset.range (Mm+1), ∑ l ∈ Finset.range (Mm+1),
              (2:ℝ)^(Ep*(i+j) + (((n:ℝ)-2)*((min k (i+j) : ℕ) : ℝ) - (k:ℝ)) + (((min l (i+j) : ℕ) : ℝ) - (l:ℝ)))) := by
              simp only [Finset.mul_sum]
        _ ≤ K2^e2 * K3^e3 * (((Nn:ℝ)+1)^2 * (2*(Nn:ℝ)+2)^2 * (2:ℝ)^(2*(Nn:ℝ)*E)) :=
              mul_le_mul_of_nonneg_left hbox (by positivity)
    have hpow2N : (2:ℝ)^(2*(Nn:ℝ)*E) ≤ (2:ℝ)^(2*E) * R^(2*E) := by
      have hNnle : (Nn:ℝ) ≤ Real.logb 2 R + 1 := by
        rw [hNndef]; exact le_of_lt (Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hR))
      have hexp : 2*(Nn:ℝ)*E ≤ 2*(Real.logb 2 R)*E + 2*E := by
        have h := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hNnle (by norm_num : (0:ℝ) ≤ 2)) hEpos.le
        nlinarith [h]
      calc (2:ℝ)^(2*(Nn:ℝ)*E) ≤ (2:ℝ)^(2*(Real.logb 2 R)*E + 2*E) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = (2:ℝ)^(2*(Real.logb 2 R)*E) * (2:ℝ)^(2*E) := by rw [Real.rpow_add (by norm_num)]
        _ = R^(2*E) * (2:ℝ)^(2*E) := by
              rw [show 2*(Real.logb 2 R)*E = (Real.logb 2 R)*(2*E) by ring]
              rw [Real.rpow_mul (by norm_num),
                  Real.rpow_logb (by norm_num) (by norm_num) hRpos]
        _ = (2:ℝ)^(2*E) * R^(2*E) := by ring
    have hsq : ((Nn:ℝ)+1)^2 * (2*(Nn:ℝ)+2)^2 ≤ 64/(Real.log 2)^8 * (Real.log (2*R))^8 := by
      have hlog2n : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hL : (0:ℝ) < Real.log (2*R) := Real.log_pos (by linarith only [hR])
      have hLR : Real.log 2 ≤ Real.log (2*R) := Real.log_le_log (by norm_num) (by linarith only [hR])
      have hb : (Real.log 2)^4 ≤ (Real.log (2*R))^4 := pow_le_pow_left₀ hlog2n.le hLR 4
      have hb8 : (Real.log 2)^8 ≤ (Real.log (2*R))^4 * (Real.log 2)^4 := by
        have h1 : (Real.log 2)^4 * (Real.log 2)^4 ≤ (Real.log 2)^4 * (Real.log (2*R))^4 :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        nlinarith [h1]
      have hNnlog : (Nn:ℝ) + 1 ≤ 2 * (Real.log (2*R) / Real.log 2) := by
        have h1 : (Nn:ℝ) < Real.logb 2 R + 1 := by
          rw [hNndef]; exact Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hR)
        have h2 : Real.logb 2 R + 1 = Real.log (2*R)/Real.log 2 := by
          rw [show Real.logb 2 R = Real.log R / Real.log 2 from rfl,
              Real.log_mul (by norm_num) (ne_of_gt hRpos), add_div,
              div_self (ne_of_gt hlog2n)]
          ring
        have h3 : (1:ℝ) ≤ Real.log (2*R)/Real.log 2 := by
          rw [le_div_iff₀ hlog2n]; linarith [hLR]
        linarith
      have h4 : ((Nn:ℝ)+1)^4 ≤ 16 * (Real.log (2*R))^4 / (Real.log 2)^4 := by
        have h := pow_le_pow_left₀ (show (0:ℝ) ≤ (Nn:ℝ)+1 by positivity) hNnlog 4
        rw [show (2 * (Real.log (2*R) / Real.log 2))^4
              = 16 * (Real.log (2*R))^4 / (Real.log 2)^4 by rw [mul_pow, div_pow]; ring] at h
        exact h
      rw [show ((Nn:ℝ)+1)^2 * (2*(Nn:ℝ)+2)^2 = 4 * ((Nn:ℝ)+1)^4 by ring]
      have h5 : 4 * (16 * (Real.log (2*R))^4 / (Real.log 2)^4)
          ≤ 64/(Real.log 2)^8 * (Real.log (2*R))^8 := by
        rw [show (64:ℝ)/(Real.log 2)^8 * (Real.log (2*R))^8
              = 64 * (Real.log (2*R))^8 / (Real.log 2)^8 by ring]
        rw [show (4:ℝ) * (16 * (Real.log (2*R))^4 / (Real.log 2)^4)
              = 64 * (Real.log (2*R))^4 / (Real.log 2)^4 by ring]
        rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (Real.log 2)^4)
              (by positivity : (0:ℝ) < (Real.log 2)^8)]
        have h6 : (Real.log 2)^8 ≤ (Real.log (2*R))^4 * (Real.log 2)^4 := hb8
        have h7 := mul_le_mul_of_nonneg_left h6 (by positivity : (0:ℝ) ≤ 64 * (Real.log (2*R))^4)
        nlinarith [h7]
      linarith [h4, h5]
    have h2 : (2:ℝ)^(2*(d-2)+2) * (K2^e2*K3^e3
          * (((Nn:ℝ)+1)^2 * (2*(Nn:ℝ)+2)^2 * (2:ℝ)^(2*(Nn:ℝ)*E)))
        ≤ (2:ℝ)^(2*(d-2)+2) * (2:ℝ)^(2*E) * (64/(Real.log 2)^8)
          * K2^e2 * K3^e3 * R^(2*E) * (Real.log (2*R))^8 := by
      have hmult : (((Nn:ℝ)+1)^2 * (2*(Nn:ℝ)+2)^2 * (2:ℝ)^(2*(Nn:ℝ)*E))
          ≤ (64/(Real.log 2)^8 * (Real.log (2*R))^8) * ((2:ℝ)^(2*E) * R^(2*E)) :=
        mul_le_mul hsq hpow2N (by positivity) (by positivity)
      have hle : (2:ℝ)^(2*(d-2)+2) * (K2^e2*K3^e3
            * (((Nn:ℝ)+1)^2 * (2*(Nn:ℝ)+2)^2 * (2:ℝ)^(2*(Nn:ℝ)*E)))
          ≤ (2:ℝ)^(2*(d-2)+2) * (K2^e2*K3^e3)
            * ((64/(Real.log 2)^8 * (Real.log (2*R))^8) * ((2:ℝ)^(2*E) * R^(2*E))) := by
        rw [show (2:ℝ)^(2*(d-2)+2) * (K2^e2*K3^e3
              * (((Nn:ℝ)+1)^2 * (2*(Nn:ℝ)+2)^2 * (2:ℝ)^(2*(Nn:ℝ)*E)))
            = (2:ℝ)^(2*(d-2)+2) * (K2^e2*K3^e3)
              * (((Nn:ℝ)+1)^2 * (2*(Nn:ℝ)+2)^2 * (2:ℝ)^(2*(Nn:ℝ)*E)) by ring]
        exact mul_le_mul_of_nonneg_left hmult (by positivity)
      calc _ ≤ _ := hle
        _ = (2:ℝ)^(2*(d-2)+2) * (2:ℝ)^(2*E) * (64/(Real.log 2)^8)
              * K2^e2 * K3^e3 * R^(2*E) * (Real.log (2*R))^8 := by ring
    calc (∑ p ∈ S, 1 / (D2 p * D3 p * X p ^ (d - 2) * Y p ^ (d - 2)))
        ≤ (2:ℝ)^(2*(d-2)+2) * (∑ p ∈ S, (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
            ∑ k ∈ Finset.range (Mm+1), ∑ l ∈ Finset.range (Mm+1),
            (if (X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)
              then (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) else 0))) := hsum1
      _ = (2:ℝ)^(2*(d-2)+2) * (∑ i ∈ Finset.range (Nn+1), ∑ j ∈ Finset.range (Nn+1),
            ∑ k ∈ Finset.range (Mm+1), ∑ l ∈ Finset.range (Mm+1),
            ∑ p ∈ S, (if (X p ≤ (2:ℝ)^i ∧ Y p ≤ (2:ℝ)^j ∧ D2 p ≤ (2:ℝ)^k ∧ D3 p ≤ (2:ℝ)^l)
              then (2:ℝ)^(-(((d-2)*(i+j)+k+l : ℕ) : ℝ)) else 0)) := by rw [hswap]
      _ ≤ (2:ℝ)^(2*(d-2)+2) * (K2^e2*K3^e3
            * (((Nn:ℝ)+1)^2 * (2*(Nn:ℝ)+2)^2 * (2:ℝ)^(2*(Nn:ℝ)*E))) :=
            mul_le_mul_of_nonneg_left hcomb2 (by positivity)
      _ ≤ (2:ℝ)^(2*(d-2)+2) * (2:ℝ)^(2*E) * (64/(Real.log 2)^8) * K2^e2 * K3^e3
            * R^(2*E) * (Real.log (2*R))^8 := h2

end Work.HP.MDEstimates
