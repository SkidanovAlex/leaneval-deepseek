import Mathlib
import Submission.Commons.LinearAlgebra.Net.incompressible_spread

set_option autoImplicit false
open scoped BigOperators

namespace Commons.LinearAlgebra.Net

open Finset

/-- Squared norm is invariant under coordinate permutations. -/
private lemma sqNorm_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    sqNorm (fun b : Fin n => x (σ b)) = sqNorm x := by
  unfold sqNorm
  exact sum_equiv_left σ (fun c : Fin n => (x c)^2)

/-- Restricting `x∘σ` to `Pre` matches restricting `x` to `Pre.image σ`. -/
private lemma sqNorm_sub_res_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    (Pre : Finset (Fin n)) :
    sqNorm ((fun b : Fin n => x (σ b)) - res Pre (fun b : Fin n => x (σ b))) =
      sqNorm (x - res (Pre.image σ) x) := by
  have hfun : (fun b : Fin n => x (σ b)) - res Pre (fun b : Fin n => x (σ b)) =
      fun b : Fin n => (x - res (Pre.image σ) x) (σ b) := by
    funext b
    by_cases hb : b ∈ Pre
    · have hσb : σ b ∈ Pre.image σ := Finset.mem_image.mpr ⟨b, hb, rfl⟩
      simp [res, hb, hσb]
    · have hσb : σ b ∉ Pre.image σ := by
        intro hm
        rcases Finset.mem_image.mp hm with ⟨a, ha, hσ⟩
        have : a = b := σ.injective hσ
        exact hb (by simpa [this] using ha)
      simp [res, hb, hσb]
  calc
    sqNorm ((fun b : Fin n => x (σ b)) - res Pre (fun b : Fin n => x (σ b)))
        = sqNorm (fun b : Fin n => (x - res (Pre.image σ) x) (σ b)) := by rw [hfun]
    _ = sqNorm (x - res (Pre.image σ) x) := sqNorm_perm σ (x - res (Pre.image σ) x)

/-- Incompressibility: a restriction to any coordinate set of size ≤ δ·n leaves
more than squared `ν` of the mass outside. -/
private lemma sqNorm_sub_res_gt_of_not_compressible {n : ℕ} {δ ν : ℝ} {x : Fin n → ℝ}
    (hx : sqNorm x = 1) (hinc : ¬ compressible δ ν x) (S : Finset (Fin n))
    (hS : (S.card : ℝ) ≤ δ * (n : ℝ)) :
    ν^2 < sqNorm (x - res S x) := by
  by_contra h
  have hle : sqNorm (x - res S x) ≤ ν^2 := le_of_not_gt h
  have hsupp : (supp (res S x)).card ≤ S.card := Finset.card_le_card (supp_res S x)
  have hsuppr : ((supp (res S x)).card : ℝ) ≤ δ * (n : ℝ) :=
    le_trans (by exact_mod_cast hsupp) hS
  exact hinc ⟨hx, ⟨res S x, hle, hsuppr⟩⟩

/-- Cardinality of the set of the first `k` indices of `Fin n`. -/
private lemma card_fin_lt {n k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun a : Fin n => (a : ℕ) < k)).card = k := by
  let A : Finset (Fin n) := (Finset.univ : Finset (Fin k)).image (Fin.castLE hk)
  have hA : A = Finset.univ.filter (fun a : Fin n => (a : ℕ) < k) := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨b, _hb, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact b.isLt
    · intro ha
      have hlt : (a : ℕ) < k := (Finset.mem_filter.mp ha).2
      refine Finset.mem_image.mpr ⟨⟨(a : ℕ), hlt⟩, by simp, ?_⟩
      apply Fin.ext
      rfl
  have hcard : ((Finset.univ : Finset (Fin k)).image (Fin.castLE hk)).card = k := by
    rw [Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin k)))
      (H := (Fin.castLE_injective hk))]
    simp
  calc
    (Finset.univ.filter (fun a : Fin n => (a : ℕ) < k)).card
        = A.card := by rw [hA]
    _ = k := by simpa [A] using hcard

/-- A large sum of squares over a set forces a large term. -/
private lemma exists_sq_gt_of_sum_gt {n : ℕ} (hn : 0 < (n : ℝ)) {T : Finset (Fin n)}
    {ν : ℝ} (hν : 0 < ν) {w : Fin n → ℝ} (hsum : ν^2 < ∑ b ∈ T, (w b)^2) :
    ∃ b ∈ T, (ν / Real.sqrt (n : ℝ))^2 < (w b)^2 := by
  by_contra hnone
  have hle_each : ∀ b ∈ T, (w b)^2 ≤ (ν / Real.sqrt (n : ℝ))^2 := by
    intro b hb
    have : ¬ (ν / Real.sqrt (n : ℝ))^2 < (w b)^2 := by
      intro hgt
      exact hnone ⟨b, hb, hgt⟩
    exact le_of_not_gt this
  have hsumle : (∑ b ∈ T, (w b)^2) ≤ (T.card : ℝ) * (ν / Real.sqrt (n : ℝ))^2 := by
    have h1 : (∑ b ∈ T, (w b)^2) ≤ (∑ b ∈ T, (ν / Real.sqrt (n : ℝ))^2) := by
      exact Finset.sum_le_sum hle_each
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using h1
  have hTle0 : T.card ≤ Fintype.card (Fin n) := Finset.card_le_univ T
  have hTle : (T.card : ℝ) ≤ (n : ℝ) := by
    simpa using (show (T.card : ℝ) ≤ (Fintype.card (Fin n) : ℝ) by exact_mod_cast hTle0)
  have hw2 : 0 ≤ (ν / Real.sqrt (n : ℝ))^2 := sq_nonneg _
  have hcard : (T.card : ℝ) * (ν / Real.sqrt (n : ℝ))^2 ≤ (n : ℝ) * (ν / Real.sqrt (n : ℝ))^2 :=
    mul_le_mul_of_nonneg_right hTle hw2
  have hmain : (n : ℝ) * (ν / Real.sqrt (n : ℝ))^2 = ν^2 := by
    have hsqrt : (Real.sqrt (n : ℝ))^2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hn)
    rw [div_pow, hsqrt]
    field_simp
  have hc : (∑ b ∈ T, (w b)^2) ≤ ν^2 := le_trans (le_trans hsumle hcard) (le_of_eq hmain)
  linarith

/-- `⌊a⌋ ≥ a/2` for `a ≥ 1`. -/
private lemma floor_ge_half {a : ℝ} (ha : 1 ≤ a) : a / 2 ≤ (Nat.floor a : ℝ) := by
  by_cases h2 : a < 2
  · have hfl1 : 1 ≤ Nat.floor a := Nat.le_floor (by simpa using ha)
    have hfl1r : (1 : ℝ) ≤ (Nat.floor a : ℝ) := by exact_mod_cast hfl1
    nlinarith
  · have hlt : a - 1 < (Nat.floor a : ℝ) := by
      have := Nat.lt_floor_add_one a
      linarith
    have ha2 : a / 2 ≤ a - 1 := by nlinarith
    linarith

/-- `|a| ≤ |b| + |a - b|`. -/
private lemma abs_le_abs_add_sub {a b : ℝ} : |a| ≤ |b| + |a - b| := by
  calc
    |a| = |b + (a - b)| := by
      congr 1
      ring
    _ ≤ |b| + |a - b| := by
      have h := abs_sub b (-(a - b))
      have hrew2 : b - (-(a - b)) = b + (a - b) := by ring
      rw [abs_neg] at h
      rw [hrew2] at h
      exact h

/-- `|a| ≤ |b| + |b - a|`. -/
private lemma abs_le_abs_add_sub' {a b : ℝ} : |a| ≤ |b| + |b - a| := by
  have h1 := abs_le_abs_add_sub (a := a) (b := b)
  simpa [abs_sub_comm] using h1

/-- `2^((j+1)/2) = sqrt(2^(j+1))`. -/
private lemma two_rpow_half (j : ℕ) :
    (2 : ℝ) ^ (((j : ℝ) + 1) / 2) = Real.sqrt ((2 : ℝ) ^ (j + 1)) := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast (2 : ℝ) (j + 1)]
  rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)) ((j + 1 : ℕ) : ℝ) (1 / 2)]
  congr 1
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

theorem perm_spreads {n : ℕ} {δ ν : ℝ} (hδ₀ : 0 < δ) (hδ₁₂ : δ ≤ 1 / 2) (hν₀ : 0 < ν)
    (x : Fin n → ℝ) (hx : Commons.LinearAlgebra.Net.sqNorm x = 1)
    (hinc : ¬ Commons.LinearAlgebra.Net.compressible δ ν x)
    {th : ℝ} (hth₀ : 0 < th) (spv : Fin n → ℤ)
    (hspv : ∀ i : Fin n, |(Real.sqrt (n : ℝ) / th) * x i - (spv i : ℝ)| ≤ 1)
    (σ : Equiv.Perm (Fin n))
    (hdom : ∀ j : ℕ, (2 : ℝ) ^ j ≤ δ * (n : ℝ) →
        (let k : ℕ := (⌊δ * (n : ℝ) / (2 : ℝ) ^ j⌋₊);
         ∀ ⦃a b : Fin n⦄, (a : ℕ) < k → k ≤ (b : ℕ) → |x (σ b)| ≤ |x (σ a)|)) :
    (∀ i : Fin n, ((i : ℝ) + 1) ≤ δ * (n : ℝ) → ν / th - 1 < |(spv (σ i) : ℝ)|) ∧
    (∀ j : ℕ, (2 : ℝ) ^ j ≤ δ * (n : ℝ) → ∀ i : Fin n,
        δ * (n : ℝ) / (2 : ℝ) ^ j < ((i : ℝ) + 1) →
        |(spv (σ i) : ℝ)| ≤
          (2 : ℝ) ^ (((j : ℝ) + 1) / 2) / (Real.sqrt δ * th) + 1) := by
  classical
  let y : Fin n → ℝ := fun b : Fin n => x (σ b)
  have hy_sq : sqNorm y = 1 := by
    dsimp [y]
    rw [sqNorm_perm, hx]
  by_cases hδn1 : 1 ≤ δ * (n : ℝ)
  · have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    have hn_pos : 0 < (n : ℝ) := by
      have hhalf : δ * (n : ℝ) ≤ (1 / 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hδ₁₂ hn_nonneg
      nlinarith
    have hδn_nonneg : 0 ≤ δ * (n : ℝ) := mul_nonneg (le_of_lt hδ₀) hn_nonneg
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn_pos
    constructor
    · -- Part A: the first ⌊δn⌋ permuted coordinates have |x| > ν/√n,
      -- hence their `spv` entries exceed ν/th − 1.
      intro i hi
      let k : ℕ := Nat.floor (δ * (n : ℝ))
      have hk_le_dn : (k : ℝ) ≤ δ * (n : ℝ) := Nat.floor_le hδn_nonneg
      have hk_le_n : k ≤ n := by
        have hδ1 : δ ≤ 1 := by linarith
        have hdn_le : δ * (n : ℝ) ≤ (n : ℝ) := by
          simpa [mul_comm] using (mul_le_of_le_one_right hn_nonneg hδ1)
        have hkn : (k : ℝ) ≤ (n : ℝ) := le_trans hk_le_dn hdn_le
        exact_mod_cast hkn
      have hdom0 : ∀ ⦃a b : Fin n⦄, (a : ℕ) < k → k ≤ (b : ℕ) → |x (σ b)| ≤ |x (σ a)| := by
        have hh := hdom 0 (by simpa using hδn1)
        simpa [k] using hh
      let Pre : Finset (Fin n) := Finset.univ.filter (fun a : Fin n => (a : ℕ) < k)
      have hPre_card : Pre.card = k := card_fin_lt hk_le_n
      have hPre_card_r : (Pre.card : ℝ) = (k : ℝ) := by exact_mod_cast hPre_card
      have hPre_le_dn : (Pre.card : ℝ) ≤ δ * (n : ℝ) := by
        rw [hPre_card_r]
        exact hk_le_dn
      have hS_le : ((Pre.image σ).card : ℝ) ≤ δ * (n : ℝ) := by
        rw [Finset.card_image_of_injective Pre σ.injective]
        exact hPre_le_dn
      have htail0 : ν^2 < sqNorm (x - res (Pre.image σ) x) :=
        sqNorm_sub_res_gt_of_not_compressible hx hinc (Pre.image σ) hS_le
      have htailA : ν^2 < sqNorm (y - res Pre y) := by
        have hA : sqNorm (y - res Pre y) = sqNorm (x - res (Pre.image σ) x) := by
          dsimp [y]
          exact sqNorm_sub_res_perm σ x Pre
        exact hA ▸ htail0
      let PreC : Finset (Fin n) := Finset.univ.filter (fun b : Fin n => b ∉ Pre)
      have htail : ν^2 < ∑ b ∈ PreC, (y b)^2 := by
        change ν^2 < ∑ b ∈ (Finset.univ.filter (fun b : Fin n => b ∉ Pre)), (y b)^2
        rw [← incompressible_spread_sqNorm_sub_res Pre y]
        exact htailA
      rcases exists_sq_gt_of_sum_gt hn_pos hν₀ (T := PreC) (w := y) htail with ⟨b0, hb0m, hb0sq⟩
      have hb0_notPre : b0 ∉ Pre := by
        simpa [PreC] using (Finset.mem_filter.mp hb0m).2
      have hb0_ge : k ≤ (b0 : ℕ) := by
        by_contra h
        have hlt : (b0 : ℕ) < k := Nat.lt_of_not_ge h
        exact hb0_notPre (by simpa [Pre] using hlt)
      have hb0_abs : ν / Real.sqrt (n : ℝ) < |x (σ b0)| := by
        have habs : |ν / Real.sqrt (n : ℝ)| < |y b0| := (sq_lt_sq).mp hb0sq
        have hνn0 : 0 ≤ ν / Real.sqrt (n : ℝ) := div_nonneg (le_of_lt hν₀) (Real.sqrt_nonneg _)
        have hlt : ν / Real.sqrt (n : ℝ) < |y b0| := by simpa [abs_of_nonneg hνn0] using habs
        simpa [y] using hlt
      have hi_lt_k : (i : ℕ) < k := by
        have hfloor : δ * (n : ℝ) < (k : ℝ) + 1 := Nat.lt_floor_add_one (δ * (n : ℝ))
        have hir : (i : ℝ) < (k : ℝ) := by nlinarith
        exact_mod_cast hir
      have hdom_i := hdom0 (a := i) (b := b0) hi_lt_k hb0_ge
      have hi_abs : ν / Real.sqrt (n : ℝ) < |x (σ i)| := lt_of_lt_of_le hb0_abs hdom_i
      let s : ℝ := (spv (σ i) : ℝ)
      let u : ℝ := (Real.sqrt (n : ℝ) / th) * x (σ i)
      have hsubu : |u - s| ≤ 1 := by simpa [u, s] using hspv (σ i)
      have hnn_th : 0 ≤ Real.sqrt (n : ℝ) / th := div_nonneg (Real.sqrt_nonneg _) (le_of_lt hth₀)
      have hsqrt_ne0 : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
      have hu_eq : |u| = (Real.sqrt (n : ℝ) / th) * |x (σ i)| := by
        dsimp [u]
        rw [abs_mul, abs_of_nonneg hnn_th]
      have hmul : Real.sqrt (n : ℝ) / th * (ν / Real.sqrt (n : ℝ)) = ν / th := by
        field_simp [hsqrt_ne0, hth₀.ne']
      have hu_gt : ν / th < |u| := by
        have hmul' : Real.sqrt (n : ℝ) / th * (ν / Real.sqrt (n : ℝ)) <
            Real.sqrt (n : ℝ) / th * |x (σ i)| :=
          mul_lt_mul_of_pos_left hi_abs (div_pos hsqrt_pos hth₀)
        rw [hu_eq]
        simpa [hmul] using hmul'
      have hs_ge_m1 : |u| - 1 ≤ |s| := by
        have ht := abs_le_abs_add_sub (a := u) (b := s)
        linarith [hsubu, ht]
      linarith [hu_gt, hs_ge_m1]
    · -- Part B: upper bounds for the tail coordinates.
      intro j h2j i hi
      let c : ℝ := δ * (n : ℝ) / (2 : ℝ) ^ j
      have h2j_pos : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) j
      have hc_ge_1 : 1 ≤ c := by
        dsimp [c]
        rw [one_le_div₀ h2j_pos]
        exact h2j
      have hc_pos : 0 < c := by linarith
      let k : ℕ := Nat.floor c
      have hk_le_c : (k : ℝ) ≤ c := Nat.floor_le (le_of_lt hc_pos)
      have hk_ge_half : c / 2 ≤ (k : ℝ) := floor_ge_half hc_ge_1
      have hk_pos : 0 < (k : ℝ) := by
        have h1n : 1 ≤ Nat.floor c := Nat.le_floor (by simpa using hc_ge_1)
        have h1r : (1 : ℝ) ≤ (k : ℝ) := by
          dsimp [k]
          exact_mod_cast h1n
        linarith
      have hk_le_n : k ≤ n := by
        have h2j_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
        have hδ1 : δ ≤ 1 := by linarith
        have hkr : (k : ℝ) ≤ (n : ℝ) := by
          calc
            (k : ℝ) ≤ c := hk_le_c
            _ ≤ δ * (n : ℝ) := by
              dsimp [c]
              have hdn0 : 0 ≤ δ * (n : ℝ) := mul_nonneg (le_of_lt hδ₀) hn_nonneg
              rw [div_le_iff₀ h2j_pos]
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (mul_le_mul_of_nonneg_left h2j_ge1 hdn0)
            _ ≤ (n : ℝ) := by
                simpa [mul_comm] using (mul_le_of_le_one_right hn_nonneg hδ1)
        exact_mod_cast hkr
      have hdomj : ∀ ⦃a b : Fin n⦄, (a : ℕ) < k → k ≤ (b : ℕ) → |x (σ b)| ≤ |x (σ a)| := by
        have hh := hdom j h2j
        simpa [k, c] using hh
      have hi_k : k ≤ (i : ℕ) := by
        have hk_lt : (k : ℝ) < (i : ℝ) + 1 := by
          dsimp [c] at hk_le_c
          linarith
        have hltn : k < (i : ℕ) + 1 := by exact_mod_cast hk_lt
        exact Nat.le_of_lt_succ hltn
      let Pre : Finset (Fin n) := Finset.univ.filter (fun a : Fin n => (a : ℕ) < k)
      have hPre_card : Pre.card = k := card_fin_lt hk_le_n
      have hPre_card_r : (Pre.card : ℝ) = (k : ℝ) := by exact_mod_cast hPre_card
      have hPre_sub : Pre ⊆ (Finset.univ : Finset (Fin n)) := by
        intro a ha
        simp
      have hsum_le_1 : (∑ a ∈ Pre, (y a)^2) ≤ 1 := by
        have h0 : (∑ a ∈ Pre, (y a)^2) ≤
            (∑ a ∈ (Finset.univ : Finset (Fin n)), (y a)^2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hPre_sub (fun a _ha _hnot => sq_nonneg (y a))
        have h1 : (∑ a ∈ (Finset.univ : Finset (Fin n)), (y a)^2) = sqNorm y := by
          simp [sqNorm]
        rw [h1] at h0
        rw [hy_sq] at h0
        exact h0
      have h_terms : ∀ a ∈ Pre, (y i)^2 ≤ (y a)^2 := by
        intro a ha
        have ha_lt : (a : ℕ) < k := (Finset.mem_filter.mp ha).2
        have hdomia := hdomj (a := a) (b := i) ha_lt hi_k
        have h : |y i| ≤ |y a| := by simpa [y] using hdomia
        exact (sq_le_sq).mpr h
      have hsum_ge : (k : ℝ) * (y i)^2 ≤ (∑ a ∈ Pre, (y a)^2) := by
        have hle_const : (∑ a ∈ Pre, (y i)^2) ≤ (∑ a ∈ Pre, (y a)^2) :=
          Finset.sum_le_sum h_terms
        have hconst : (∑ a ∈ Pre, (y i)^2) = (k : ℝ) * (y i)^2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hPre_card_r]
        rw [hconst] at hle_const
        exact hle_const
      have hk_mul : (k : ℝ) * (y i)^2 ≤ 1 := le_trans hsum_ge hsum_le_1
      have hysq_le : (y i)^2 ≤ 1 / (k : ℝ) := by
        have h' : (y i)^2 * (k : ℝ) ≤ 1 := by
          simpa [mul_comm] using hk_mul
        exact (le_div_iff₀ hk_pos).mpr h'
      have hsqrtk_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hk_pos
      have hysq2 : (y i)^2 ≤ (1 / Real.sqrt (k : ℝ))^2 := by
        have h1 : (1 / Real.sqrt (k : ℝ))^2 = 1 / (k : ℝ) := by
          rw [div_pow, one_pow]
          rw [Real.sq_sqrt (le_of_lt hk_pos)]
        rw [h1]
        exact hysq_le
      have hy_abs : |y i| ≤ 1 / Real.sqrt (k : ℝ) := by
        apply sq_le_of_sq (abs_nonneg (y i)) (by positivity)
        have hsq := hysq2
        rwa [← sq_abs (y i)] at hsq
      have hx_abs : |x (σ i)| ≤ 1 / Real.sqrt (k : ℝ) := by
        simpa [y] using hy_abs
      let s : ℝ := (spv (σ i) : ℝ)
      let u : ℝ := (Real.sqrt (n : ℝ) / th) * x (σ i)
      have hsubu : |u - s| ≤ 1 := by simpa [u, s] using hspv (σ i)
      have hnn_th : 0 ≤ Real.sqrt (n : ℝ) / th := div_nonneg (Real.sqrt_nonneg _) (le_of_lt hth₀)
      have hu_eq : |u| = (Real.sqrt (n : ℝ) / th) * |x (σ i)| := by
        dsimp [u]
        rw [abs_mul, abs_of_nonneg hnn_th]
      have hs1 : |s| ≤ Real.sqrt (n : ℝ) / th * |x (σ i)| + 1 := by
        have htri2 : |s| ≤ |u| + |u - s| := abs_le_abs_add_sub' (a := s) (b := u)
        have h2 : |s| ≤ |u| + 1 := by linarith
        rw [hu_eq] at h2
        exact h2
      have hs2 : |s| ≤ Real.sqrt (n : ℝ) / th * (1 / Real.sqrt (k : ℝ)) + 1 := by
        have hm : Real.sqrt (n : ℝ) / th * |x (σ i)| ≤
            Real.sqrt (n : ℝ) / th * (1 / Real.sqrt (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hx_abs hnn_th
        nlinarith
      -- (√n/√k) ≤ 2^((j+1)/2)/√δ via the floor bound k ≥ δn/2^(j+1)
      have hk_ge_half_c : c / 2 ≤ (k : ℝ) := hk_ge_half
      have hcross : (n : ℝ) * δ ≤ (k : ℝ) * (2 : ℝ) ^ (j + 1) := by
        have hpow2 : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by
          rw [pow_succ]
          ring
        have hm : c / 2 * (2 : ℝ) ^ (j + 1) ≤ (k : ℝ) * (2 : ℝ) ^ (j + 1) :=
          mul_le_mul_of_nonneg_right hk_ge_half_c (by positivity : 0 ≤ (2 : ℝ) ^ (j + 1))
        have hcomp : c / 2 * (2 : ℝ) ^ (j + 1) = δ * (n : ℝ) := by
          dsimp [c]
          rw [hpow2]
          field_simp [h2j_pos.ne']
        rw [hcomp] at hm
        simpa [mul_comm] using hm
      have hn_k : (n : ℝ) / (k : ℝ) ≤ (2 : ℝ) ^ (j + 1) / δ := by
        rw [div_le_div_iff₀ hk_pos hδ₀]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hcross
      have hsqrt_aux : Real.sqrt (n : ℝ) / Real.sqrt (k : ℝ) ≤
          Real.sqrt ((2 : ℝ) ^ (j + 1)) / Real.sqrt δ := by
        apply sq_le_of_sq ?_ ?_ ?_
        · positivity
        · positivity
        · rw [div_pow, div_pow]
          rw [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
          rw [Real.sq_sqrt (le_of_lt hk_pos)]
          rw [Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ) ^ (j + 1))]
          rw [Real.sq_sqrt (le_of_lt hδ₀)]
          exact hn_k
      have hsqrt_le : Real.sqrt (n : ℝ) / Real.sqrt (k : ℝ) ≤
          (2 : ℝ) ^ (((j : ℝ) + 1) / 2) / Real.sqrt δ := by
        rw [two_rpow_half]
        exact hsqrt_aux
      have hM3 : (Real.sqrt (n : ℝ) / Real.sqrt (k : ℝ)) / th ≤
          (2 : ℝ) ^ (((j : ℝ) + 1) / 2) / Real.sqrt δ / th :=
        div_le_div_of_nonneg_right hsqrt_le (le_of_lt hth₀)
      have hM2 : Real.sqrt (n : ℝ) / th * (1 / Real.sqrt (k : ℝ)) ≤
          (2 : ℝ) ^ (((j : ℝ) + 1) / 2) / (Real.sqrt δ * th) := by
        have hl : Real.sqrt (n : ℝ) / th * (1 / Real.sqrt (k : ℝ)) =
            Real.sqrt (n : ℝ) / Real.sqrt (k : ℝ) / th := by
          field_simp [hth₀.ne', (ne_of_gt hsqrtk_pos)]
        have hr : (2 : ℝ) ^ (((j : ℝ) + 1) / 2) / (Real.sqrt δ * th) =
            (2 : ℝ) ^ (((j : ℝ) + 1) / 2) / Real.sqrt δ / th := by
          field_simp [hth₀.ne', (ne_of_gt (Real.sqrt_pos.2 hδ₀))]
        rw [← hl, ← hr] at hM3
        exact hM3
      have hfin : |s| ≤ (2 : ℝ) ^ (((j : ℝ) + 1) / 2) / (Real.sqrt δ * th) + 1 := by
        nlinarith [hs2, hM2]
      simpa [s] using hfin
  · constructor
    · intro i hi
      exfalso
      have hlow : (1 : ℝ) ≤ (i : ℝ) + 1 := by nlinarith [show (0 : ℝ) ≤ (i : ℝ) by positivity]
      nlinarith
    · intro j h2j i hi
      exfalso
      have h2jge1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := by
        exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
      nlinarith

end Commons.LinearAlgebra.Net
