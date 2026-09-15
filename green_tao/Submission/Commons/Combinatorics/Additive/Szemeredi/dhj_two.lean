import Mathlib

namespace Commons.Combinatorics.Additive.Szemeredi

open Finset

/-! ## Elementary facts about `Fin 2` -/

private lemma fin2_le_iff (a b : Fin 2) : a ≤ b ↔ (a = 1 → b = 1) := by
  fin_cases a <;> fin_cases b <;> simp

private lemma fin2_eq_zero_of_le_of_ne {a b : Fin 2} (hle : a ≤ b) (hne : a ≠ b) : a = 0 := by
  fin_cases a <;> fin_cases b <;> simp_all

private lemma fin2_eq_one_of_le_of_ne {a b : Fin 2} (hle : a ≤ b) (hne : a ≠ b) : b = 1 := by
  fin_cases a <;> fin_cases b <;> simp_all

private lemma fin2_eq_of_eq_one_iff {a b : Fin 2} (h : a = 1 ↔ b = 1) : a = b := by
  fin_cases a <;> fin_cases b <;> simp_all

/-! ## The support of a `{0,1}`-point -/

private def supp {n : ℕ} (w : Fin n → Fin 2) : Finset (Fin n) :=
  Finset.univ.filter (fun i => w i = 1)

private lemma mem_supp {n : ℕ} {w : Fin n → Fin 2} {i : Fin n} :
    i ∈ supp w ↔ w i = 1 := by
  simp [supp]

private lemma supp_injective {n : ℕ} : Function.Injective (supp (n := n)) := by
  intro w w' h
  funext i
  exact fin2_eq_of_eq_one_iff (by rw [← mem_supp, h, mem_supp])

private lemma supp_subset_iff {n : ℕ} {x y : Fin n → Fin 2} :
    supp x ⊆ supp y ↔ ∀ i, x i ≤ y i := by
  constructor
  · intro h i
    rw [fin2_le_iff]
    intro hx
    exact mem_supp.mp (h (mem_supp.mpr hx))
  · intro h i hi
    rw [mem_supp] at hi ⊢
    exact (fin2_le_iff _ _).mp (h i) hi

/-! ## From a comparable pair to a combinatorial line -/

private lemma exists_line_of_le {n : ℕ} {T : Finset (Fin n → Fin 2)} {x y : Fin n → Fin 2}
    (hx : x ∈ T) (hy : y ∈ T) (hle : ∀ i, x i ≤ y i) (hne : x ≠ y) :
    ∃ w : Fin n → Fin 2, ∃ P : Finset (Fin n), P.Nonempty ∧
      ∀ v : Fin 2, (fun i => if i ∈ P then v else w i) ∈ T := by
  set P : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ y i) with hP
  have hPmem : ∀ i, i ∈ P ↔ x i ≠ y i := by intro i; rw [hP]; simp
  refine ⟨x, P, ?_, ?_⟩
  · obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hne
    exact ⟨i₀, (hPmem i₀).mpr hi₀⟩
  · intro v
    rcases eq_or_ne v 0 with hv | hv
    · subst hv
      have hpt : (fun i => if i ∈ P then (0 : Fin 2) else x i) = x := by
        funext i
        by_cases h : i ∈ P
        · rw [if_pos h]
          exact (fin2_eq_zero_of_le_of_ne (hle i) ((hPmem i).mp h)).symm
        · rw [if_neg h]
      rw [hpt]; exact hx
    · have hv1 : v = 1 := by fin_cases v <;> simp_all
      subst hv1
      have hpt : (fun i => if i ∈ P then (1 : Fin 2) else x i) = y := by
        funext i
        by_cases h : i ∈ P
        · rw [if_pos h]
          exact (fin2_eq_one_of_le_of_ne (hle i) ((hPmem i).mp h)).symm
        · rw [if_neg h]
          exact not_not.mp (fun hne' => h ((hPmem i).mpr hne'))
      rw [hpt]; exact hy

/-! ## A dense set with no line is an antichain, so it is small -/

private lemma card_le_choose_of_no_line {n : ℕ} {T : Finset (Fin n → Fin 2)}
    (h : ¬ ∃ w : Fin n → Fin 2, ∃ P : Finset (Fin n), P.Nonempty ∧
          ∀ v : Fin 2, (fun i => if i ∈ P then v else w i) ∈ T) :
    T.card ≤ n.choose (n / 2) := by
  have h' : ∀ x ∈ T, ∀ y ∈ T, (∀ i, x i ≤ y i) → x = y := by
    intro x hx y hy hle
    by_contra hne
    exact h (exists_line_of_le hx hy hle hne)
  have hanti : IsAntichain (· ⊆ ·) ((T.image (fun w => supp w) : Finset (Finset (Fin n))) :
      Set (Finset (Fin n))) := by
    intro a ha b hb hab hsub
    rw [Finset.mem_coe, Finset.mem_image] at ha hb
    obtain ⟨x, hxT, rfl⟩ := ha
    obtain ⟨y, hyT, rfl⟩ := hb
    have hle : ∀ i, x i ≤ y i := fun i => (supp_subset_iff.mp hsub) i
    have hxy : x = y := h' x hxT y hyT hle
    exact hab (by rw [hxy])
  have hs := hanti.sperner
  rw [Finset.card_image_of_injective _ (supp_injective (n := n)), Fintype.card_fin] at hs
  exact hs

/-! ## An upper bound for the central binomial coefficient -/

/-- The central binomial coefficient satisfies `(2m+1) * C(2m,m)^2 ≤ 16^m`. -/
private lemma central_sq_le (m : ℕ) :
    (2 * m + 1) * (Nat.centralBinom m) ^ 2 ≤ 16 ^ m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have key := Nat.succ_mul_centralBinom_succ m
    have hsq : (m + 1) ^ 2 * (Nat.centralBinom (m + 1)) ^ 2
        = 4 * (2 * m + 1) ^ 2 * (Nat.centralBinom m) ^ 2 := by
      calc (m + 1) ^ 2 * (Nat.centralBinom (m + 1)) ^ 2
          = ((m + 1) * Nat.centralBinom (m + 1)) ^ 2 := by ring
        _ = (2 * (2 * m + 1) * Nat.centralBinom m) ^ 2 := by rw [key]
        _ = 4 * (2 * m + 1) ^ 2 * (Nat.centralBinom m) ^ 2 := by ring
    have hchain : (m + 1) ^ 2 * ((2 * m + 3) * (Nat.centralBinom (m + 1)) ^ 2)
        = 4 * (2 * m + 3) * (2 * m + 1) *
            ((2 * m + 1) * (Nat.centralBinom m) ^ 2) := by
      rw [show (m + 1) ^ 2 * ((2 * m + 3) * (Nat.centralBinom (m + 1)) ^ 2)
            = (2 * m + 3) * ((m + 1) ^ 2 * (Nat.centralBinom (m + 1)) ^ 2) by ring,
          hsq]
      ring
    have hb : 4 * (2 * m + 3) * (2 * m + 1) * ((2 * m + 1) * (Nat.centralBinom m) ^ 2)
        ≤ 4 * (2 * m + 3) * (2 * m + 1) * 16 ^ m :=
      Nat.mul_le_mul_left _ ih
    have hpol : 4 * (2 * m + 3) * (2 * m + 1) ≤ 16 * (m + 1) ^ 2 := by nlinarith
    have hb2 : 4 * (2 * m + 3) * (2 * m + 1) * 16 ^ m ≤ (m + 1) ^ 2 * 16 ^ (m + 1) := by
      calc 4 * (2 * m + 3) * (2 * m + 1) * 16 ^ m
          ≤ (16 * (m + 1) ^ 2) * 16 ^ m := Nat.mul_le_mul_right _ hpol
        _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by rw [pow_succ]; ring
    have hmain : (m + 1) ^ 2 * ((2 * m + 3) * (Nat.centralBinom (m + 1)) ^ 2)
        ≤ (m + 1) ^ 2 * 16 ^ (m + 1) := by rw [hchain]; exact hb.trans hb2
    have hcancel : (2 * m + 3) * (Nat.centralBinom (m + 1)) ^ 2 ≤ 16 ^ (m + 1) :=
      Nat.le_of_mul_le_mul_left hmain (pow_pos (Nat.succ_pos m) 2)
    have : 2 * (m + 1) + 1 = 2 * m + 3 := by ring
    rwa [this]

/-- `(n+1) * C(n, n/2)^2 ≤ 4^n`. -/
private lemma choose_half_sq (n : ℕ) : (n + 1) * (n.choose (n / 2)) ^ 2 ≤ 4 ^ n := by
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, rfl⟩ := even_iff_exists_two_mul.mp hn
    have h := central_sq_le m
    have h1 : (2 * m).choose m = Nat.centralBinom m :=
      (Nat.centralBinom_eq_two_mul_choose m).symm
    have h2 : 4 ^ (2 * m) = 16 ^ m := by rw [pow_mul]; norm_num
    have hd : (2 * m) / 2 = m := Nat.mul_div_right m (by norm_num)
    rw [hd, h1, h2]; exact h
  · obtain ⟨m, rfl⟩ := odd_iff_exists_bit1.mp hn
    have hI : 2 * (2 * m + 1).choose m = Nat.centralBinom (m + 1) := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      have hss := Nat.choose_succ_succ (2 * m + 1) m
      have hsym : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
        have h := Nat.choose_symm (n := 2 * m + 1) (k := m) (by omega)
        rwa [show 2 * m + 1 - m = m + 1 by omega] at h
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, hss, hsym]; ring
    have hcen := central_sq_le (m + 1)
    have h4 : 4 * ((2 * m + 2) * ((2 * m + 1).choose m) ^ 2) ≤ 4 * 4 ^ (2 * m + 1) := by
      have heq : 4 * ((2 * m + 2) * ((2 * m + 1).choose m) ^ 2)
          = (2 * m + 2) * (Nat.centralBinom (m + 1)) ^ 2 := by
        rw [← hI]; ring
      rw [heq]
      have h43 : (2 * m + 2) * (Nat.centralBinom (m + 1)) ^ 2
          ≤ (2 * (m + 1) + 1) * (Nat.centralBinom (m + 1)) ^ 2 :=
        Nat.mul_le_mul_right ((Nat.centralBinom (m + 1)) ^ 2) (by omega)
      have h45 : 16 ^ (m + 1) ≤ 4 * 4 ^ (2 * m + 1) := by
        rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul]
        rw [show 2 * (m + 1) = 2 * m + 2 by ring]
        rw [show 2 * m + 2 = (2 * m + 1) + 1 by ring, pow_add, pow_one]
        exact le_of_eq (mul_comm _ _)
      exact (h43.trans hcen).trans h45
    have hd : (2 * m + 1) / 2 = m := by omega
    rw [hd]
    exact Nat.le_of_mul_le_mul_left h4 (by norm_num)

/-- `C(n, n/2) ≤ 2^n / sqrt(n+1)`. -/
private lemma choose_half_le (n : ℕ) :
    (n.choose (n / 2) : ℝ) ≤ (2 : ℝ) ^ n / Real.sqrt (n + 1) := by
  have hsq4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    calc (4 : ℝ) ^ n = ((2 : ℝ) ^ 2) ^ n := by rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
      _ = (2 : ℝ) ^ (2 * n) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (n * 2) := by rw [Nat.mul_comm]
      _ = ((2 : ℝ) ^ n) ^ 2 := by rw [pow_mul]
  have hh : Real.sqrt ((4 : ℝ) ^ n / (n + 1)) = (2 : ℝ) ^ n / Real.sqrt (n + 1) := by
    rw [Real.sqrt_div (by positivity) (n + 1), hsq4, Real.sqrt_sq (by positivity)]
  have hsq : ((n.choose (n / 2) : ℝ)) ^ 2 ≤ (4 : ℝ) ^ n / (n + 1) := by
    have hc : ((n : ℝ) + 1) * ((n.choose (n / 2) : ℝ)) ^ 2 ≤ (4 : ℝ) ^ n := by
      have h := choose_half_sq n
      exact_mod_cast h
    have hpos : (0 : ℝ) < (n + 1) := by positivity
    have h := div_le_div_of_nonneg_right hc hpos.le
    rwa [mul_div_cancel_left₀ _ (ne_of_gt hpos)] at h
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (n.choose (n / 2) : ℝ)), ← hh]
  apply Real.sqrt_le_sqrt
  exact hsq

/-- `C(n, n/2) < δ * 2^n` for `n` large. -/
private lemma choose_half_lt (δ : ℝ) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (n.choose (n / 2) : ℝ) < δ * (2 : ℝ) ^ n := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / δ ^ 2)
  refine ⟨n₀ + 1, fun n hn => ?_⟩
  have hlt : 1 / δ ^ 2 < (n + 1 : ℝ) := by
    have : (n₀ : ℝ) < (n : ℝ) := by
      exact_mod_cast (show n₀ < n by omega)
    linarith
  have hδinv_pos : (0 : ℝ) < 1 / δ := by positivity
  have hsqrt : 1 / δ < Real.sqrt (n + 1) := by
    rw [Real.lt_sqrt hδinv_pos.le]
    have : (1 / δ) ^ 2 = 1 / δ ^ 2 := by rw [div_pow]; norm_num
    rw [this]; exact hlt
  have hsqpos : (0 : ℝ) < Real.sqrt (n + 1) := Real.sqrt_pos_of_pos (by positivity)
  have hrec : 1 / Real.sqrt (n + 1) < δ := by
    rw [div_lt_iff₀ hsqpos]
    have h := mul_lt_mul_of_pos_left hsqrt hδ
    rwa [mul_one_div, div_self (ne_of_gt hδ)] at h
  have hle := choose_half_le n
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  calc (n.choose (n / 2) : ℝ) ≤ (2 : ℝ) ^ n / Real.sqrt (n + 1) := hle
    _ = (2 : ℝ) ^ n * (1 / Real.sqrt (n + 1)) := by rw [mul_one_div]
    _ < (2 : ℝ) ^ n * δ := mul_lt_mul_of_pos_left hrec hpos2
    _ = δ * (2 : ℝ) ^ n := by ring

/-! ## The `k = 2` density Hales–Jewett statement -/

/-- **The `k = 2` case of the density Hales-Jewett statement.**  For every `δ > 0` there is
`n₀` such that for `n ≥ n₀` every `T : Finset (Fin n → Fin 2)` with `δ * 2^n ≤ |T|`
contains a combinatorial line, i.e. there are `w : Fin n → Fin 2` and a nonempty wildcard
set `P` such that both the point `w` and the point obtained from `w` by flipping every
coordinate in `P` lie in `T`.  Equivalently: some `x, y ∈ T` differ exactly on a nonempty
set of coordinates.  This is the `k = 2` case of DHJ and is equiderivable with the corners
statement (a dense subset of a product `G × G` of finite abelian groups contains a corner),
for which Mathlib already has a proof. -/
theorem dhj_two (δ : ℝ) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ T : Finset (Fin n → Fin 2),
      δ * (2 : ℝ) ^ n ≤ (T.card : ℝ) →
        ∃ w : Fin n → Fin 2, ∃ P : Finset (Fin n), P.Nonempty ∧
          ∀ v : Fin 2, (fun i => if i ∈ P then v else w i) ∈ T := by
  obtain ⟨n₀, hn₀⟩ := choose_half_lt δ hδ
  refine ⟨n₀, fun n hn T hT => ?_⟩
  by_contra hcon
  have hcard := card_le_choose_of_no_line hcon
  have hR : (T.card : ℝ) ≤ (n.choose (n / 2) : ℝ) := by exact_mod_cast hcard
  have hlt := hn₀ n hn
  linarith

end Commons.Combinatorics.Additive.Szemeredi
