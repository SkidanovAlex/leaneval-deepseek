import Mathlib
import Submission.DiscrepancyDefs

/-! Corollary 4.2 of arXiv:1907.09464v1, proved from the partial-colouring lemma
(Theorem 4.1) by the induction described in the paper's Section 4. -/
open scoped BigOperators

noncomputable section
namespace Submission
namespace Discrepancy

/-! ## A small API for `supAbs` (the ℓ∞-norm as an `sSup`) -/

lemma supAbs_eq_range_sSup {n : ℕ} (v : Fin n → ℝ) :
    supAbs v = sSup (Set.range (fun i : Fin n => |v i|)) := by
  unfold supAbs
  congr
  ext x
  simp [eq_comm]

lemma abs_le_supAbs {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : |v i| ≤ supAbs v := by
  rw [supAbs_eq_range_sSup]
  exact le_csSup ((Set.finite_range (fun i : Fin n => |v i|)).bddAbove) ⟨i, rfl⟩

lemma range_empty_fin_zero {β : Type*} (f : Fin 0 → β) : Set.range f = ∅ := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨i, rfl⟩
    exact Fin.elim0 i
  · intro hx
    simp at hx

lemma supAbs_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ supAbs v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [supAbs]
  · let i : Fin n := ⟨0, hn⟩
    exact le_trans (abs_nonneg (v i)) (abs_le_supAbs v i)

lemma supAbs_le_of_forall {n : ℕ} (v : Fin n → ℝ) {M : ℝ} (hM : ∀ i : Fin n, |v i| ≤ M)
    (hM0 : 0 ≤ M) : supAbs v ≤ M := by
  rw [supAbs_eq_range_sSup]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [range_empty_fin_zero]
    simpa using hM0
  · refine csSup_le ?nonempty ?ub
    · exact ⟨|v ⟨0, hn⟩|, ⟨⟨0, hn⟩, rfl⟩⟩
    · intro b hb
      rcases hb with ⟨i, rfl⟩
      exact hM i

/-! ## Euclidean-norm / dot-product bounds -/

lemma le_of_sq_le_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have habs : |a| ≤ |b| := sq_le_sq.mp h
  rwa [abs_of_nonneg ha, abs_of_nonneg hb] at habs

lemma abs_dot_le {n : ℕ} (a v : Fin n → ℝ) : |dot a v| ≤ ∑ i : Fin n, |a i| * |v i| := by
  unfold dot
  calc
    |∑ i : Fin n, a i * v i| ≤ ∑ i : Fin n, |a i * v i| := by
      simpa using (Finset.abs_sum_le_sum_abs (fun i : Fin n => a i * v i) (Finset.univ : Finset (Fin n)))
    _ = ∑ i : Fin n, |a i| * |v i| := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_mul _ _

lemma dot_add_distrib {n : ℕ} (a b v : Fin n → ℝ) :
    dot (fun i => a i + b i) v = dot a v + dot b v := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma eucl_le_sqrt_mul_supAbs {n : ℕ} (v : Fin n → ℝ) : eucl v ≤ Real.sqrt (n : ℝ) * supAbs v := by
  have hsq : (eucl v) ^ 2 ≤ (Real.sqrt (n : ℝ) * supAbs v) ^ 2 := by
    rw [eucl_sq]
    calc
      (∑ i : Fin n, (v i) ^ 2) ≤ ∑ i : Fin n, (supAbs v) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg (v i)) (abs_le_supAbs v i) 2
      _ = (n : ℝ) * (supAbs v) ^ 2 := by simp
      _ = (Real.sqrt (n : ℝ) * supAbs v) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
  exact le_of_sq_le_sq (eucl_nonneg v) (mul_nonneg (Real.sqrt_nonneg _) (supAbs_nonneg v)) hsq

/-! ## The base case (`n ≤ 900`) -/

lemma exists_sign_close {n : ℕ} (x0 : Fin n → ℝ) (hx0 : ∀ i : Fin n, x0 i ∈ Set.Icc (-1) 1) :
    ∃ x : Fin n → ℝ, (∀ i, x i = -1 ∨ x i = 1) ∧ (∀ i, |x i - x0 i| ≤ 1) := by
  let x : Fin n → ℝ := fun i => if (0 : ℝ) ≤ x0 i then 1 else -1
  refine ⟨x, ?_, ?_⟩
  · intro i
    by_cases h : (0 : ℝ) ≤ x0 i
    · right; simp [x, h]
    · left; simp [x, h]
  · intro i
    by_cases h : (0 : ℝ) ≤ x0 i
    · simp [x, h]
      have h1 : -1 ≤ 1 - x0 i := by linarith [(hx0 i).2]
      have h2 : 1 - x0 i ≤ 1 := by linarith [h]
      exact abs_le.mpr ⟨h1, h2⟩
    · simp [x, h]
      have hx0neg : x0 i ≤ 0 := le_of_not_ge h
      have h1 : -1 ≤ -1 - x0 i := by linarith [hx0neg]
      have h2 : -1 - x0 i ≤ 1 := by linarith [(hx0 i).1]
      exact abs_le.mpr ⟨h1, h2⟩

lemma n_le_30_sqrt (n : ℕ) (hn : n ≤ 900) : (n : ℝ) ≤ 30 * Real.sqrt (n : ℝ) := by
  have hs : Real.sqrt (n : ℝ) ≤ 30 := by
    have h1 : Real.sqrt (n : ℝ) ≤ Real.sqrt (900 : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hn)
    have h2 : Real.sqrt (900 : ℝ) = 30 := by norm_num [Real.sq_sqrt]
    rwa [h2] at h1
  have hnonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  calc (n : ℝ) = (Real.sqrt (n : ℝ)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
    _ ≤ 30 * Real.sqrt (n : ℝ) := by
        rw [sq]
        exact mul_le_mul_of_nonneg_right hs hnonneg

/-! ## The log bound needed for `a_j ≤ c_j + 12` -/

lemma log_ratio_196_le_144 {k D : ℕ} (hk : 901 ≤ k) (hD : D = k - (k + 1) / 2) :
    (196 : ℝ) * Real.log ((k : ℝ) / (D : ℝ)) ≤ 144 := by
  have hD450n : 450 ≤ D := by omega
  have hDposn : 0 < D := by omega
  have hk2 : k ≤ 2 * D + 1 := by omega
  have hD450 : (450 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD450n
  have hk2r : (k : ℝ) ≤ 2 * (D : ℝ) + 1 := by exact_mod_cast hk2
  have hD0 : 0 < (D : ℝ) := by exact_mod_cast hDposn
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have h1 : (k : ℝ) * 450 ≤ 901 * (D : ℝ) := by nlinarith [hD450, hk2r]
  have hratio : (k : ℝ) / (D : ℝ) ≤ (901 : ℝ) / 450 := by
    rw [div_le_iff₀ hD0]
    have hswap : (901 : ℝ) / 450 * (D : ℝ) = (901 * (D : ℝ)) / 450 := by ring
    rw [hswap]
    rw [le_div_iff₀ (by norm_num : 0 < (450 : ℝ))]
    nlinarith [h1]
  have hposratio : 0 < (k : ℝ) / (D : ℝ) := div_pos hk0 hD0
  have hmain : (196 : ℝ) * Real.log ((k : ℝ) / (D : ℝ)) ≤
      (196 : ℝ) * Real.log ((901 : ℝ) / 450) := by
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hposratio hratio) (by norm_num)
  have hlt : (196 : ℝ) * Real.log ((901 : ℝ) / 450) < 144 := by
    have h900pos : 0 < (901 / 900 : ℝ) := by norm_num
    have h901 : Real.log ((901 : ℝ) / 450) = Real.log 2 + Real.log ((901 : ℝ) / 900) := by
      have hfac : (901 : ℝ) / 450 = 2 * ((901 : ℝ) / 900) := by norm_num
      have h2nz : (2 : ℝ) ≠ 0 := by norm_num
      have h9nz : ((901 : ℝ) / 900) ≠ 0 := by norm_num
      rw [hfac, Real.log_mul h2nz h9nz]
    have hb : Real.log ((901 : ℝ) / 900) ≤ 1 / 900 := by
      have hb' : Real.log ((901 : ℝ) / 900) ≤ (901 : ℝ) / 900 - 1 :=
        Real.log_le_sub_one_of_pos h900pos
      have hconv : (901 : ℝ) / 900 - 1 = 1 / 900 := by norm_num
      rwa [hconv] at hb'
    rw [h901, mul_add]
    have h2 : (196 : ℝ) * Real.log 2 + 196 / 900 < 144 := by
      have h1' : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
      have h3 : (196 : ℝ) * (0.6931471808 : ℝ) + 196 / 900 < 144 := by norm_num
      linarith
    have hm : (196 : ℝ) * Real.log 2 + (196 : ℝ) * Real.log ((901 : ℝ) / 900) ≤
        (196 : ℝ) * Real.log 2 + 196 / 900 := by
      nlinarith [mul_le_mul_of_nonneg_left hb (by norm_num : 0 ≤ (196 : ℝ))]
    exact lt_of_le_of_lt hm h2
  exact le_trans hmain hlt.le

/-! ## Sum-splitting and reindexing lemmas -/

lemma sum_eq_sum_compl_aux {n : ℕ} (U0 : Finset (Fin n)) (g : Fin n → ℝ)
    (hU : ∀ i ∈ U0, g i = 0) :
    (∑ i : Fin n, g i) = ∑ i ∈ (U0ᶜ : Finset (Fin n)), g i := by
  rw [show (Finset.univ : Finset (Fin n)) = U0 ∪ U0ᶜ by
        ext i
        by_cases hi : i ∈ U0
        · simp
        · simp]
  rw [Finset.sum_union]
  · rw [Finset.sum_eq_zero hU]
    simp
  · exact (Finset.disjoint_left.mpr (by intro a ha; simp [ha]))

lemma sum_attach_eq_type {n : ℕ} (R : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ i ∈ R, f i) = ∑ x : {i : Fin n // i ∈ R}, f x.1 := by
  rw [← Finset.sum_attach R (fun i => f i)]
  have huniv : (Finset.univ : Finset {i : Fin n // i ∈ R}) = R.attach := by
    ext x; simp
  rw [huniv]

/-- If `x` agrees with `y` on `U0` and with `z ∘ e` off `U0`, then the dot-product of
`x - y` with `v` equals the reindexed sum over the recursion coordinates. -/
lemma dot_split_rec {k : ℕ} (U0 : Finset (Fin k))
    (e : {i : Fin k // i ∈ (U0ᶜ : Finset (Fin k))} ≃
      Fin (Fintype.card {i : Fin k // i ∈ (U0ᶜ : Finset (Fin k))}))
    (x y v : Fin k → ℝ) (z : Fin (Fintype.card {i : Fin k // i ∈ (U0ᶜ : Finset (Fin k))}) → ℝ)
    (hxU : ∀ i ∈ U0, x i = y i)
    (hxR : ∀ q : {i : Fin k // i ∈ (U0ᶜ : Finset (Fin k))}, x q.1 = z (e q)) :
    dot (fun i => x i - y i) v =
      ∑ t : Fin (Fintype.card {i : Fin k // i ∈ (U0ᶜ : Finset (Fin k))}),
        (z t - y ((e.symm t).1)) * (v ((e.symm t).1)) := by
  unfold dot
  have hU0 : ∀ i ∈ U0, (x i - y i) * v i = 0 := by
    intro i hi
    simp [hxU i hi]
  rw [sum_eq_sum_compl_aux U0 (fun i => (x i - y i) * v i) hU0]
  rw [sum_attach_eq_type (U0ᶜ) (fun i => (x i - y i) * v i)]
  rw [← Equiv.sum_comp e.symm
        (fun q : {i : Fin k // i ∈ (U0ᶜ : Finset (Fin k))} => (x q.1 - y q.1) * v q.1)]
  apply Finset.sum_congr rfl
  intro t ht
  have hq : x ((e.symm t).1) = z t := by
    have h0 := hxR (e.symm t)
    rwa [Equiv.apply_symm_apply] at h0
  rw [hq]

/-! ## Square-root bound on the reduced dimension -/

lemma sqrtD_le_frac_sqrtk {k D : ℕ} (hD : (D : ℝ) ≤ (k : ℝ) / 2) :
    Real.sqrt (D : ℝ) ≤ (5 / 7 : ℝ) * Real.sqrt (k : ℝ) := by
  have hsq : (Real.sqrt (D : ℝ)) ^ 2 ≤ ((5 / 7 : ℝ) * Real.sqrt (k : ℝ)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ (D : ℝ))]
    rw [mul_pow]
    rw [Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ))]
    have h1 : (D : ℝ) ≤ (25 / 49 : ℝ) * (k : ℝ) := by
      have hk0 : 0 ≤ (k : ℝ) := by positivity
      nlinarith [hD]
    nlinarith [h1]
  exact le_of_sq_le_sq (Real.sqrt_nonneg _)
    (mul_nonneg (by norm_num : 0 ≤ (5 / 7 : ℝ)) (Real.sqrt_nonneg _)) hsq

/-! ## Main theorem (Corollary 4.2) -/

theorem cor42
    (h41 : ∀ (n m : ℕ) (v : Fin m → (Fin n → ℝ)) (x0 : Fin n → ℝ),
      (∀ i : Fin n, x0 i ∈ Set.Icc (-1) 1) →
      ∀ (c : Fin m → ℝ), (∀ j, 0 ≤ c j) →
      (∑ j : Fin m, Real.exp (-(c j) ^ 2 / 16) ≤ (n : ℝ) / 16) →
      ∃ x : Fin n → ℝ,
        (∀ i : Fin n, x i ∈ Set.Icc (-1) 1) ∧
        (∀ j : Fin m, |dot (fun i => x i - x0 i) (v j)| ≤ c j * eucl (v j)) ∧
        (((n + 1) / 2 : ℕ) ≤ Fintype.card {i : Fin n // x i = -1 ∨ x i = 1}))
    (n m : ℕ) (v : Fin m → (Fin n → ℝ)) (x0 : Fin n → ℝ)
    (hx0 : ∀ i : Fin n, x0 i ∈ Set.Icc (-1) 1) (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hsum : ∑ j : Fin m, Real.exp (-(c j) ^ 2 / 196) ≤ (n : ℝ) / 16) :
    ∃ x : Fin n → ℝ,
      (∀ i : Fin n, x i = -1 ∨ x i = 1) ∧
      (∀ j : Fin m, |dot (fun i => x i - x0 i) (v j)| ≤ (c j + 30) * Real.sqrt n * supAbs (v j)) := by
  classical
  let P : ℕ → Prop := fun k => ∀ (m : ℕ) (v : Fin m → (Fin k → ℝ)) (x0 : Fin k → ℝ),
    (∀ i : Fin k, x0 i ∈ Set.Icc (-1) 1) → ∀ (c : Fin m → ℝ), (∀ j, 0 ≤ c j) →
    (∑ j : Fin m, Real.exp (-(c j) ^ 2 / 196) ≤ (k : ℝ) / 16) →
    ∃ x : Fin k → ℝ,
      (∀ i : Fin k, x i = -1 ∨ x i = 1) ∧
      (∀ j : Fin m, |dot (fun i => x i - x0 i) (v j)| ≤ (c j + 30) * Real.sqrt k * supAbs (v j))
  revert hsum hc hx0 c x0 v m
  change ∀ (m : ℕ) (v : Fin m → (Fin n → ℝ)) (x0 : Fin n → ℝ),
    (∀ i : Fin n, x0 i ∈ Set.Icc (-1) 1) → ∀ (c : Fin m → ℝ), (∀ j, 0 ≤ c j) →
    (∑ j : Fin m, Real.exp (-(c j) ^ 2 / 196) ≤ (n : ℝ) / 16) →
    ∃ x : Fin n → ℝ,
      (∀ i : Fin n, x i = -1 ∨ x i = 1) ∧
      (∀ j : Fin m, |dot (fun i => x i - x0 i) (v j)| ≤ (c j + 30) * Real.sqrt n * supAbs (v j))
  -- Now we prove P n by strong induction
  change P n
  refine Nat.strong_induction_on n ?_
  intro k ih m v x0 hx0 c hc hsum
  by_cases hsmall : k ≤ 900
  · -- BASE CASE
    rcases exists_sign_close x0 hx0 with ⟨x, hxsign, hxclose⟩
    refine ⟨x, hxsign, ?_⟩
    intro j
    have hk30 : (k : ℝ) ≤ 30 * Real.sqrt (k : ℝ) := n_le_30_sqrt k hsmall
    have hS : 0 ≤ supAbs (v j) := supAbs_nonneg (v j)
    have hterm : ∀ i : Fin k, |x i - x0 i| * |v j i| ≤ |v j i| := by
      intro i
      simpa using (mul_le_mul_of_nonneg_right (hxclose i) (abs_nonneg (v j i)))
    calc
      |dot (fun i => x i - x0 i) (v j)| ≤ ∑ i : Fin k, |x i - x0 i| * |v j i| := abs_dot_le _ _
      _ ≤ ∑ i : Fin k, |v j i| := Finset.sum_le_sum (by intro i hi; exact hterm i)
      _ ≤ (k : ℝ) * supAbs (v j) := by
          calc ∑ i : Fin k, |v j i| ≤ ∑ i : Fin k, supAbs (v j) :=
              Finset.sum_le_sum (by intro i hi; exact abs_le_supAbs (v j) i)
            _ = (k : ℝ) * supAbs (v j) := by simp
      _ ≤ 30 * Real.sqrt (k : ℝ) * supAbs (v j) := by
          exact mul_le_mul_of_nonneg_right hk30 hS
      _ ≤ (c j + 30) * Real.sqrt (k : ℝ) * supAbs (v j) := by
          have hc0 : 0 ≤ c j := hc j
          have h30 : 30 ≤ c j + 30 := by linarith
          have hpos : 0 ≤ Real.sqrt (k : ℝ) * supAbs (v j) :=
            mul_nonneg (Real.sqrt_nonneg _) hS
          calc 30 * Real.sqrt (k : ℝ) * supAbs (v j) = 30 * (Real.sqrt (k : ℝ) * supAbs (v j)) := by ring
            _ ≤ (c j + 30) * (Real.sqrt (k : ℝ) * supAbs (v j)) := by
                exact mul_le_mul_of_nonneg_right h30 hpos
            _ = (c j + 30) * Real.sqrt (k : ℝ) * supAbs (v j) := by ring
  · -- STEP CASE: k > 900
    have hk901 : 901 ≤ k := by omega
    have hk1 : 1 ≤ k := by omega
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk1
    let b : Fin m → ℝ := fun j => (2 : ℝ) * c j / 7
    have hb0 : ∀ j, 0 ≤ b j := by
      intro j
      dsimp [b]
      nlinarith [hc j]
    have hbexp : ∀ j, Real.exp (-(b j) ^ 2 / 16) = Real.exp (-(c j) ^ 2 / 196) := by
      intro j
      have hcalc : ((2 * c j / 7) ^ 2 / 16) = ((c j) ^ 2 / 196) := by
        field_simp
        ring
      dsimp [b]
      congr 1
      calc -(b j) ^ 2 / 16 = -((b j) ^ 2 / 16) := by ring
        _ = -((c j) ^ 2 / 196) := by rw [hcalc]
        _ = -(c j) ^ 2 / 196 := by ring
    have hbsum : (∑ j : Fin m, Real.exp (-(b j) ^ 2 / 16)) ≤ (k : ℝ) / 16 := by
      calc
        (∑ j : Fin m, Real.exp (-(b j) ^ 2 / 16)) =
            (∑ j : Fin m, Real.exp (-(c j) ^ 2 / 196)) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hbexp j
        _ ≤ (k : ℝ) / 16 := hsum
    rcases h41 k m v x0 hx0 b hb0 hbsum with ⟨y, hyIcc, hyDisc, hyCard⟩
    let good : Finset (Fin k) := Finset.univ.filter (fun i => y i = -1 ∨ y i = 1)
    have hgood_card : good.card = Fintype.card {i : Fin k // y i = -1 ∨ y i = 1} := by
      dsimp [good]
      exact (Fintype.card_ofFinset
        (s := (Finset.univ.filter (fun i : Fin k => y i = -1 ∨ y i = 1)))
        (p := {x : Fin k | y x = -1 ∨ y x = 1}) (fun x => by simp)).symm
    have hG : (k + 1) / 2 ≤ good.card := by
      rw [hgood_card]
      exact hyCard
    rcases Finset.exists_subset_card_eq hG with ⟨U0, hU0sub, hU0card⟩
    let RT : Type := {i : Fin k // i ∈ (U0ᶜ : Finset (Fin k))}
    let D : ℕ := Fintype.card RT
    let eRT : RT ≃ Fin D := Fintype.equivFin RT
    have hDcard : D = k - (k + 1) / 2 := by
      dsimp [D, RT]
      have hRT : Fintype.card {i : Fin k // i ∈ (U0ᶜ : Finset (Fin k))} =
          (U0ᶜ : Finset (Fin k)).card := by
        exact Fintype.card_ofFinset (U0ᶜ : Finset (Fin k)) (fun x => by simp)
      rw [hRT]
      rw [Finset.card_compl, hU0card]
      simp
    have hDlt : D < k := by omega
    have hDle_half : (D : ℝ) ≤ (k : ℝ) / 2 := by
      have h1 : D ≤ k / 2 := by omega
      have h1' : (D : ℝ) ≤ ((k / 2 : ℕ) : ℝ) := by exact_mod_cast h1
      have h2 : (2 : ℝ) * ((k / 2 : ℕ) : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (by omega : 2 * (k / 2) ≤ k)
      have h3 : ((k / 2 : ℕ) : ℝ) ≤ (k : ℝ) / 2 := by
        rw [le_div_iff₀ (by norm_num : 0 < (2 : ℝ))]
        nlinarith
      linarith
    have hD0n : 0 < D := by omega
    have hD0 : 0 < (D : ℝ) := by exact_mod_cast hD0n
    have hlog : (196 : ℝ) * Real.log ((k : ℝ) / (D : ℝ)) ≤ 144 :=
      log_ratio_196_le_144 hk901 hDcard
    have hlog_nonneg : 0 ≤ Real.log ((k : ℝ) / (D : ℝ)) := by
      have hr1 : 1 ≤ (k : ℝ) / (D : ℝ) := by
        have hDle : (D : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : D ≤ k)
        rw [le_div_iff₀ hD0]
        simpa using hDle
      have hlg : Real.log (1 : ℝ) ≤ Real.log ((k : ℝ) / (D : ℝ)) :=
        Real.log_le_log (by norm_num) hr1
      simpa using hlg
    let a : Fin m → ℝ := fun j => Real.sqrt (c j ^ 2 + 196 * Real.log ((k : ℝ) / (D : ℝ)))
    have ha0 : ∀ j, 0 ≤ a j := by
      intro j
      dsimp [a]
      exact Real.sqrt_nonneg _
    have ha_sq : ∀ j, (a j) ^ 2 = (c j) ^ 2 + 196 * Real.log ((k : ℝ) / (D : ℝ)) := by
      intro j
      dsimp [a]
      rw [Real.sq_sqrt]
      nlinarith [sq_nonneg (c j), mul_nonneg (by norm_num : 0 ≤ (196 : ℝ)) hlog_nonneg]
    have hratio_pos : 0 < (k : ℝ) / (D : ℝ) := div_pos hkpos hD0
    have hterm_a : ∀ j, Real.exp (-(a j) ^ 2 / 196) =
        Real.exp (-(c j) ^ 2 / 196) * ((D : ℝ) / (k : ℝ)) := by
      intro j
      have hexp : -(a j) ^ 2 / 196 = -(c j) ^ 2 / 196 - Real.log ((k : ℝ) / (D : ℝ)) := by
        rw [ha_sq j]
        ring
      rw [hexp]
      rw [show -(c j) ^ 2 / 196 - Real.log ((k : ℝ) / (D : ℝ)) =
          -(c j) ^ 2 / 196 + -Real.log ((k : ℝ) / (D : ℝ)) by ring]
      rw [Real.exp_add]
      rw [Real.exp_neg, Real.exp_log hratio_pos, inv_div]
    have hsumA : (∑ j : Fin m, Real.exp (-(a j) ^ 2 / 196)) ≤ (D : ℝ) / 16 := by
      calc
        (∑ j : Fin m, Real.exp (-(a j) ^ 2 / 196)) =
            ∑ j : Fin m, Real.exp (-(c j) ^ 2 / 196) * ((D : ℝ) / (k : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hterm_a j
        _ = ((D : ℝ) / (k : ℝ)) * ∑ j : Fin m, Real.exp (-(c j) ^ 2 / 196) := by
          rw [← Finset.sum_mul, mul_comm]
        _ ≤ ((D : ℝ) / (k : ℝ)) * ((k : ℝ) / 16) := by
          exact mul_le_mul_of_nonneg_left hsum (div_nonneg (by positivity) (by positivity))
        _ = (D : ℝ) / 16 := by
          field_simp [hkpos]
    -- set up recursion on the remaining coordinates
    let vR : Fin m → (Fin D → ℝ) := fun j => fun t => v j ((eRT.symm t).1)
    let yR : Fin D → ℝ := fun t => y ((eRT.symm t).1)
    have hyR0 : ∀ t : Fin D, yR t ∈ Set.Icc (-1) 1 := by
      intro t
      exact hyIcc ((eRT.symm t).1)
    rcases ih D hDlt m vR yR hyR0 a ha0 hsumA with ⟨z, hz1, hz2⟩
    let x : Fin k → ℝ := fun i =>
      if h : i ∈ U0 then y i else z (eRT ⟨i, Finset.mem_compl.mpr h⟩)
    refine ⟨x, ?hxsign, ?hxbound⟩
    · intro i
      by_cases hi : i ∈ U0
      · have hyi : y i = -1 ∨ y i = 1 := by
          exact (Finset.mem_filter.mp (hU0sub hi)).2
        have hx : x i = y i := by simp [x, hi]
        rw [hx]
        exact hyi
      · have hx : x i = z (eRT ⟨i, Finset.mem_compl.mpr hi⟩) := by simp [x, hi]
        rw [hx]
        exact hz1 (eRT ⟨i, Finset.mem_compl.mpr hi⟩)
    · -- discrepancy bounds
      intro j
      let S : ℝ := supAbs (v j)
      have hS0 : 0 ≤ S := by dsimp [S]; exact supAbs_nonneg (v j)
      have hxU : ∀ i ∈ U0, x i = y i := by
        intro i hi
        simp [x, hi]
      have hxR : ∀ q : {i : Fin k // i ∈ (U0ᶜ : Finset (Fin k))}, x q.1 = z (eRT q) := by
        intro q
        have hqnot : q.1 ∉ U0 := Finset.mem_compl.mp q.2
        simp [x, hqnot]
      have hsubsup : supAbs (vR j) ≤ S := by
        dsimp [S, vR]
        exact supAbs_le_of_forall (fun t : Fin D => v j ((eRT.symm t).1)) (by
          intro t
          exact abs_le_supAbs (v j) ((eRT.symm t).1)) (supAbs_nonneg (v j))
      have hsqrtD : Real.sqrt (D : ℝ) ≤ (5 / 7 : ℝ) * Real.sqrt (k : ℝ) :=
        sqrtD_le_frac_sqrtk hDle_half
      have ha_le : a j ≤ c j + 12 := by
        have hsq : (a j) ^ 2 ≤ (c j + 12) ^ 2 := by
          rw [ha_sq j]
          nlinarith [hc j, hlog]
        have ha_nonneg : 0 ≤ a j := ha0 j
        have hc12 : 0 ≤ c j + 12 := by linarith [hc j]
        have hbnd : Real.sqrt ((a j) ^ 2) ≤ c j + 12 := by
          have hmono : Real.sqrt ((a j) ^ 2) ≤ Real.sqrt ((c j + 12) ^ 2) :=
            Real.sqrt_le_sqrt hsq
          have hsq2 : Real.sqrt ((c j + 12) ^ 2) = c j + 12 := by
            rw [Real.sqrt_sq_eq_abs]
            exact abs_of_nonneg hc12
          rwa [hsq2] at hmono
        calc a j = Real.sqrt ((a j) ^ 2) := by
              rw [Real.sqrt_sq_eq_abs]
              exact (abs_of_nonneg ha_nonneg).symm
          _ ≤ c j + 12 := hbnd
      -- part 1 (the y-discrepancy)
      have hpart1 : |dot (fun i => y i - x0 i) (v j)| ≤ (2 * c j / 7) * Real.sqrt (k : ℝ) * S := by
        have h1 := hyDisc j
        have he : eucl (v j) ≤ Real.sqrt (k : ℝ) * supAbs (v j) := eucl_le_sqrt_mul_supAbs (v j)
        have hb : 0 ≤ (2 * c j / 7) := by nlinarith [hc j]
        calc
          |dot (fun i => y i - x0 i) (v j)| ≤ b j * eucl (v j) := h1
          _ = (2 * c j / 7) * eucl (v j) := by dsimp [b]
          _ ≤ (2 * c j / 7) * (Real.sqrt (k : ℝ) * supAbs (v j)) := by
              exact mul_le_mul_of_nonneg_left he hb
          _ = (2 * c j / 7) * Real.sqrt (k : ℝ) * S := by dsimp [S]; ring
      -- part 2 (the recursive discrepancy)
      have hsplit : dot (fun i => x i - y i) (v j) =
          dot (fun t : Fin D => z t - yR t) (vR j) := by
        have h1 := dot_split_rec U0 eRT x y (v j) z hxU hxR
        rw [h1]
        dsimp [yR, vR, dot]
      have hpart2 : |dot (fun i => x i - y i) (v j)| ≤
          (a j + 30) * Real.sqrt (D : ℝ) * supAbs (vR j) := by
        rw [hsplit]
        exact hz2 j
      have hpart2b : (a j + 30) * Real.sqrt (D : ℝ) * supAbs (vR j) ≤
          (c j + 42) * ((5 / 7 : ℝ) * Real.sqrt (k : ℝ)) * S := by
        have h1' : (a j + 30) * Real.sqrt (D : ℝ) ≤ (c j + 42) * ((5 / 7 : ℝ) * Real.sqrt (k : ℝ)) := by
          exact mul_le_mul (by nlinarith [ha_le]) hsqrtD (Real.sqrt_nonneg _) (by nlinarith [hc j])
        exact mul_le_mul h1' hsubsup (supAbs_nonneg (vR j)) (by
          have : 0 ≤ (c j + 42) := by nlinarith [hc j]
          positivity)
      -- triangle inequality and assembly
      have hd1 : |dot (fun i => x i - x0 i) (v j)| ≤
          |dot (fun i => x i - y i) (v j)| + |dot (fun i => y i - x0 i) (v j)| := by
        have hlin : dot (fun i => x i - x0 i) (v j) =
            dot (fun i => x i - y i) (v j) + dot (fun i => y i - x0 i) (v j) := by
          rw [show (fun i : Fin k => x i - x0 i) = fun i => (x i - y i) + (y i - x0 i) by
                funext i
                ring]
          exact dot_add_distrib (fun i => x i - y i) (fun i => y i - x0 i) (v j)
        rw [hlin]
        exact abs_add_le _ _
      calc
        |dot (fun i => x i - x0 i) (v j)| ≤
            |dot (fun i => x i - y i) (v j)| + |dot (fun i => y i - x0 i) (v j)| := hd1
        _ ≤ (c j + 42) * ((5 / 7 : ℝ) * Real.sqrt (k : ℝ)) * S +
            (2 * c j / 7) * Real.sqrt (k : ℝ) * S := by
              exact add_le_add (le_trans hpart2 hpart2b) hpart1
        _ = (c j + 30) * Real.sqrt (k : ℝ) * S := by ring
end Discrepancy
end Submission
