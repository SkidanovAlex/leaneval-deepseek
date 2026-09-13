import Mathlib
import Submission.Commons.Analysis.Inequalities.bonami_beckner_four
import Submission.Commons.Analysis.Inequalities.noise_op_char

namespace Commons.Analysis.Inequalities

open Finset BigOperators

noncomputable section

/-! ## Fourier analysis on the hypercube for the Bonami lemma -/

/-- The sign character of `ZMod 2`, as a real number. -/
def sgn2 (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

/-- The sign character of `ZMod 2`, as a complex number. -/
def sgnC (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : a.val = 0 ∨ a.val = 1 := by have := ZMod.val_lt a; omega
  rcases h with h | h
  · left;  exact ZMod.val_injective 2 (by rw [h, ZMod.val_zero])
  · right; exact ZMod.val_injective 2 (by rw [h, ZMod.val_one 2])

lemma sgn2_zero : sgn2 0 = 1 := by simp [sgn2]
lemma sgn2_one : sgn2 1 = -1 := by simp [sgn2]

lemma sgn2_eq (a : ZMod 2) : sgn2 a = (-1:ℝ)^a.val := by
  rcases zmod2_cases a with h | h <;> rw [h] <;> simp [sgn2, ZMod.val_zero, ZMod.val_one 2]

lemma sgn2_self (a : ZMod 2) : sgn2 a * sgn2 a = 1 := by
  rcases zmod2_cases a with h | h <;> rw [h] <;> simp [sgn2]

lemma sgn2_mul (a b : ZMod 2) : sgn2 a * sgn2 b = sgn2 (a+b) := by
  rcases zmod2_cases a with h | h <;> rcases zmod2_cases b with h2 | h2 <;> rw [h, h2]
  · simp [sgn2]
  · simp [sgn2]
  · simp [sgn2]
  · rw [show (1:ZMod 2)+(1:ZMod 2) = 0 from by decide]; simp [sgn2]

lemma sgn2_of_ne_zero (a : ZMod 2) (h : a ≠ 0) : sgn2 a = -1 := by
  rcases zmod2_cases a with h0 | h1
  · exact absurd h0 h
  · rw [h1]; simp [sgn2]

lemma sgnC_eq (a : ZMod 2) : sgnC a = (-1:ℂ)^a.val := by
  rcases zmod2_cases a with h | h <;> rw [h] <;> simp [sgnC, ZMod.val_zero, ZMod.val_one 2]

lemma sgn2_eq_sgnC (a : ZMod 2) : ((sgn2 a : ℝ) : ℂ) = sgnC a := by
  rcases zmod2_cases a with h | h <;> rw [h] <;> simp [sgn2, sgnC]

lemma sum_zmod2' {M : Type*} [AddCommMonoid M] (F : ZMod 2 → M) : ∑ a, F a = F 0 + F 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0,1} from by decide,
    Finset.sum_pair (by decide : (0:ZMod 2) ≠ 1)]

lemma sum_sgn2 : (∑ a : ZMod 2, sgn2 a) = 0 := by
  rw [sum_zmod2']; simp [sgn2]

lemma add_eq_zero_iff_eq (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    rcases zmod2_cases a with ha | ha <;> rcases zmod2_cases b with hb | hb
    · rw [ha, hb]
    · rw [ha, hb] at h; exact absurd h (by decide)
    · rw [ha, hb] at h; exact absurd h (by decide)
    · rw [ha, hb]
  · intro h; rw [h]
    rcases zmod2_cases b with hb | hb <;> rw [hb] <;> decide

/-- The real hypercube character `χ_S(x) = ∏_{i∈S} sgn(x_i)`. -/
def chiR {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ZMod 2) : ℝ :=
  ∏ i ∈ S, sgn2 (x i)

/-- The complex hypercube character `χ_S(x) = ∏_{i∈S} (-1)^{x_i}`. -/
def chiC {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ZMod 2) : ℂ :=
  ∏ i ∈ S, sgnC (x i)

lemma chiR_eq_exp {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    chiR S x = ∏ i ∈ S, (-1:ℝ)^(x i).val := by
  simp only [chiR, sgn2_eq]

lemma chiC_eq_exp {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    chiC S x = ∏ i ∈ S, (-1:ℂ)^(x i).val := by
  simp only [chiC, sgnC_eq]

lemma chiC_ofReal {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    ((chiR S x : ℝ) : ℂ) = chiC S x := by
  simp only [chiR, chiC, Complex.ofReal_prod]
  exact Finset.prod_congr rfl (fun i _ => sgn2_eq_sgnC (x i))

/-! ### Orthogonality -/

lemma sum_chi_coord {n : ℕ} (S T : Finset (Fin n)) (i : Fin n) :
    (∑ a : ZMod 2, (if i ∈ S then sgn2 a else 1) * (if i ∈ T then sgn2 a else 1))
      = if (i ∈ S ↔ i ∈ T) then 2 else 0 := by
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
  · simp only [hiS, hiT, if_true]
    rw [sum_zmod2']
    simp only [sgn2_self]; norm_num
  · simp only [hiS, hiT, if_true, if_false, mul_one]
    rw [sum_zmod2']; simp [sgn2]
  · simp only [hiS, hiT, if_true, if_false, one_mul]
    rw [sum_zmod2']; simp [sgn2]
  · simp only [hiS, hiT, if_true, if_false, one_mul]
    rw [sum_zmod2']; norm_num

lemma prod_ite_card_eq {n : ℕ} (S T : Finset (Fin n)) :
    (∏ i : Fin n, (if (i ∈ S ↔ i ∈ T) then (2:ℝ) else 0))
      = if S = T then (2:ℝ)^n else 0 := by
  by_cases h : S = T
  · subst h; rw [if_pos rfl]
    rw [show (∏ i : Fin n, (if (i ∈ S ↔ i ∈ S) then (2:ℝ) else 0)) = ∏ _i : Fin n, (2:ℝ) from
      Finset.prod_congr rfl (fun i _ => by rw [if_pos Iff.rfl])]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg h]
    have hex : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact h (Finset.ext hc)
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])

theorem sum_chiR_mul_chiR {n : ℕ} (S T : Finset (Fin n)) :
    (∑ x : Fin n → ZMod 2, chiR S x * chiR T x)
      = if S = T then (2:ℝ)^n else 0 := by
  set G : (i : Fin n) → ZMod 2 → ℝ :=
    fun i a => (if i ∈ S then sgn2 a else 1) * (if i ∈ T then sgn2 a else 1) with hG
  have step1 : ∀ x : Fin n → ZMod 2, chiR S x * chiR T x = ∏ i : Fin n, G i (x i) := by
    intro x
    rw [chiR, chiR, ← Finset.prod_ite_mem_eq S (fun i => sgn2 (x i)),
        ← Finset.prod_ite_mem_eq T (fun i => sgn2 (x i)), ← Finset.prod_mul_distrib]
  simp only [step1]
  rw [show (∑ x : Fin n → ZMod 2, ∏ i : Fin n, G i (x i))
      = ∑ x ∈ (Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod 2)))),
          ∏ i : Fin n, G i (x i) from by rw [Fintype.piFinset_univ]]
  rw [Finset.sum_prod_piFinset]
  have hcoord : (∏ i : Fin n, ∑ a ∈ (Finset.univ : Finset (ZMod 2)), G i a)
      = ∏ i : Fin n, (if (i ∈ S ↔ i ∈ T) then (2:ℝ) else 0) := by
    apply Finset.prod_congr rfl; intro i _
    show (∑ a : ZMod 2, G i a) = _
    exact sum_chi_coord S T i
  rw [hcoord, prod_ite_card_eq S T]

lemma sum_powerset_prod {ι : Type*} [Fintype ι] {R : Type*} [CommSemiring R] (f : ι → R) :
    (∑ t : Finset ι, ∏ i ∈ t, f i) = ∏ i, (1 + f i) := by
  rw [Finset.prod_one_add (Finset.univ : Finset ι), Finset.powerset_univ]

lemma prod_one_add_sgn2 {n : ℕ} (z : Fin n → ZMod 2) :
    (∏ i : Fin n, (1 + sgn2 (z i))) = if (∀ i, z i = 0) then (2:ℝ)^n else 0 := by
  by_cases hz : ∀ i, z i = 0
  · rw [if_pos hz]
    rw [show (∏ i : Fin n, (1 + sgn2 (z i))) = ∏ _i : Fin n, (2:ℝ) from
      Finset.prod_congr rfl (fun i _ => by rw [hz i, sgn2_zero]; norm_num)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hz]
    simp only [not_forall] at hz
    obtain ⟨i, hi⟩ := hz
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [sgn2_of_ne_zero (z i) hi]; norm_num)

theorem sum_chiR_dual {n : ℕ} (x y : Fin n → ZMod 2) :
    (∑ S : Finset (Fin n), chiR S x * chiR S y) = if x = y then (2:ℝ)^n else 0 := by
  have step : ∀ S : Finset (Fin n), chiR S x * chiR S y
      = ∏ i ∈ S, (sgn2 (x i) * sgn2 (y i)) := by
    intro S; rw [chiR, chiR, Finset.prod_mul_distrib]
  simp only [step]
  rw [sum_powerset_prod (f := fun i => sgn2 (x i) * sgn2 (y i))]
  rw [show (∏ i : Fin n, (1 + sgn2 (x i) * sgn2 (y i)))
      = ∏ i : Fin n, (1 + sgn2 (x i + y i)) from
      Finset.prod_congr rfl (fun i _ => by rw [sgn2_mul])]
  rw [prod_one_add_sgn2 (fun i => x i + y i)]
  have hiff : (∀ i, x i + y i = 0) ↔ x = y := by
    constructor
    · intro h; funext i; exact (add_eq_zero_iff_eq (x i) (y i)).mp (h i)
    · intro h i; rw [congrFun h i]; rcases zmod2_cases (y i) with hb | hb <;> rw [hb] <;> decide
  by_cases hxy : x = y
  · rw [if_pos (hiff.mpr hxy), if_pos hxy]
  · rw [if_neg (fun hc => hxy (hiff.mp hc)), if_neg hxy]


/-- Normalised Fourier coefficient of a real function on the cube. -/
def FW {n : ℕ} (w : (Fin n → ZMod 2) → ℝ) (S : Finset (Fin n)) : ℝ :=
  (∑ x, w x * chiR S x) / 2^n

lemma dual_expand {n : ℕ} (w : (Fin n → ZMod 2) → ℝ) (y : Fin n → ZMod 2) :
    (∑ S : Finset (Fin n), (∑ x, w x * chiR S x) * chiR S y) = w y * 2^n := by
  rw [show (∑ S, (∑ x, w x * chiR S x) * chiR S y)
      = ∑ S, ∑ x, (w x * chiR S x) * chiR S y from by
        apply Finset.sum_congr rfl; intro S _; rw [Finset.sum_mul]]
  rw [Finset.sum_comm]
  have hx : ∀ x : Fin n → ZMod 2,
      (∑ S : Finset (Fin n), (w x * chiR S x) * chiR S y)
        = w x * (if x = y then (2:ℝ)^n else 0) := by
    intro x
    rw [show (∑ S, (w x * chiR S x) * chiR S y) = ∑ S, w x * (chiR S x * chiR S y) from
      Finset.sum_congr rfl (fun S _ => by ring)]
    rw [← Finset.mul_sum, sum_chiR_dual x y]
  simp only [hx]
  rw [Finset.sum_eq_single y]
  · rw [if_pos rfl]
  · intro x _ hxy; rw [if_neg hxy, mul_zero]
  · intro hy; exact absurd (Finset.mem_univ y) hy

lemma inversion {n : ℕ} (w : (Fin n → ZMod 2) → ℝ) (y : Fin n → ZMod 2) :
    (∑ S : Finset (Fin n), FW w S * chiR S y) = w y := by
  have h2 : (2:ℝ)^n ≠ 0 := pow_ne_zero n (by norm_num)
  rw [show (∑ S, FW w S * chiR S y)
      = ((2:ℝ)^n)⁻¹ * ∑ S, (∑ x, w x * chiR S x) * chiR S y from by
        simp only [FW, div_eq_mul_inv]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro S _; ring]
  rw [dual_expand, show ((2:ℝ)^n)⁻¹ * (w y * (2:ℝ)^n) = w y from by
      rw [mul_comm (w y) ((2:ℝ)^n), ← mul_assoc, inv_mul_cancel₀ h2, one_mul]]

lemma sum_sq_chi_comb {n : ℕ} (c : Finset (Fin n) → ℝ) :
    (∑ x : Fin n → ZMod 2, (∑ S : Finset (Fin n), c S * chiR S x)^2)
      = 2^n * ∑ S : Finset (Fin n), (c S)^2 := by
  have hsquare : ∀ x : Fin n → ZMod 2, (∑ S, c S * chiR S x)^2
      = ∑ S, ∑ T, (c S * chiR S x) * (c T * chiR T x) := by
    intro x; rw [pow_two, Finset.sum_mul_sum]
  have hL : (∑ x : Fin n → ZMod 2, (∑ S, c S * chiR S x)^2)
      = ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
          c S * c T * (if S = T then (2:ℝ)^n else 0) := by
    simp only [hsquare]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro S _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro T _
    rw [show (∑ x, (c S * chiR S x) * (c T * chiR T x))
        = ∑ x, (c S * c T) * (chiR S x * chiR T x) from
        Finset.sum_congr rfl (fun x _ => by ring)]
    rw [← Finset.mul_sum, sum_chiR_mul_chiR]
  rw [hL]
  have hT : ∀ S : Finset (Fin n),
      (∑ T, c S * c T * (if S = T then (2:ℝ)^n else 0)) = c S * c S * 2^n := by
    intro S
    rw [Finset.sum_eq_single S]
    · rw [if_pos rfl]
    · intro T _ hTS; rw [if_neg (fun h => hTS h.symm), mul_zero]
    · intro hS; exact absurd (Finset.mem_univ S) hS
  simp only [hT]
  rw [← Finset.sum_mul, mul_comm (∑ S : Finset (Fin n), c S * c S) ((2:ℝ)^n)]
  congr 1
  apply Finset.sum_congr rfl; intro S _; ring

lemma parseval_unnorm {n : ℕ} (w : (Fin n → ZMod 2) → ℝ) :
    (∑ S : Finset (Fin n), (∑ x, w x * chiR S x)^2) = (2:ℝ)^n * ∑ x, (w x)^2 := by
  have hsquare : ∀ S : Finset (Fin n), (∑ x, w x * chiR S x)^2
      = ∑ x, ∑ y, (w x * chiR S x) * (w y * chiR S y) := by
    intro S; rw [pow_two, Finset.sum_mul_sum]
  have hL : (∑ S : Finset (Fin n), (∑ x, w x * chiR S x)^2)
      = ∑ x : Fin n → ZMod 2, ∑ y : Fin n → ZMod 2,
          w x * w y * (if x = y then (2:ℝ)^n else 0) := by
    simp only [hsquare]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    rw [show (∑ S, (w x * chiR S x) * (w y * chiR S y))
        = ∑ S, (w x * w y) * (chiR S x * chiR S y) from
        Finset.sum_congr rfl (fun S _ => by ring)]
    rw [← Finset.mul_sum, sum_chiR_dual x y]
  rw [hL]
  have hy : ∀ x : Fin n → ZMod 2,
      (∑ y, w x * w y * (if x = y then (2:ℝ)^n else 0)) = w x * w x * 2^n := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [if_pos rfl]
    · intro y _ hyx; rw [if_neg (fun h => hyx h.symm), mul_zero]
    · intro hx; exact absurd (Finset.mem_univ x) hx
  simp only [hy]
  rw [← Finset.sum_mul, mul_comm (∑ x : Fin n → ZMod 2, w x * w x) ((2:ℝ)^n)]
  congr 1
  apply Finset.sum_congr rfl; intro x _; ring

lemma parseval {n : ℕ} (w : (Fin n → ZMod 2) → ℝ) :
    (∑ S : Finset (Fin n), (FW w S)^2) = (∑ x, (w x)^2) / 2^n := by
  have h2 : (2:ℝ)^n ≠ 0 := pow_ne_zero n (by norm_num)
  have hFW : ∀ S : Finset (Fin n),
      (FW w S)^2 = (∑ x, w x * chiR S x)^2 * ((2:ℝ)^n)⁻¹^2 := by
    intro S; rw [FW, div_eq_mul_inv, mul_pow]
  simp only [hFW]
  rw [← Finset.sum_mul, parseval_unnorm, div_eq_mul_inv]
  field_simp

/-- The noise operator on the hypercube, matching the kernel of `bonami_beckner_four`. -/
def noiseOp (n : ℕ) (ρ : ℝ) (g : (Fin n → ZMod 2) → ℝ) : (Fin n → ZMod 2) → ℝ :=
  fun x => ∑ y : Fin n → ZMod 2,
    (∏ i : Fin n, (if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2)) * g y

lemma noiseOp_chi' {n : ℕ} (ρ : ℝ) (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    (∑ y : Fin n → ZMod 2,
        (∏ i : Fin n, (if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2)) * chiR S y)
      = ρ ^ S.card * chiR S x := by
  rw [show (∑ y : Fin n → ZMod 2,
        (∏ i : Fin n, (if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2)) * chiR S y)
      = ∑ y : Fin n → ZMod 2,
        (∏ i : Fin n, (if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2))
          * (∏ i ∈ S, (-1:ℝ)^(y i).val) from
      Finset.sum_congr rfl (fun y _ => by rw [chiR_eq_exp])]
  rw [noise_op_char, chiR_eq_exp]

lemma noiseOp_chi {n : ℕ} (ρ : ℝ) (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    noiseOp n ρ (chiR S) x = ρ ^ S.card * chiR S x := by
  simp only [noiseOp]; exact noiseOp_chi' ρ S x

lemma noiseOp_sum {n : ℕ} (ρ : ℝ) (cS : Finset (Fin n) → ℝ) (x : Fin n → ZMod 2) :
    noiseOp n ρ (fun y => ∑ S : Finset (Fin n), cS S * chiR S y) x
      = ∑ S : Finset (Fin n), ρ ^ S.card * (cS S * chiR S x) := by
  simp only [noiseOp]
  rw [show (∑ y, (∏ i : Fin n, (if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2))
          * (∑ S, cS S * chiR S y))
      = ∑ y, ∑ S, (∏ i : Fin n, (if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2))
          * (cS S * chiR S y) from by
        apply Finset.sum_congr rfl; intro y _; rw [Finset.mul_sum]]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro S _
  rw [show (∑ y, (∏ i : Fin n, (if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2))
        * (cS S * chiR S y))
      = cS S * ∑ y, (∏ i : Fin n, (if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2))
        * chiR S y from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro y _; ring]
  rw [show (∑ y, (∏ i : Fin n, (if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2)) * chiR S y)
      = ρ ^ S.card * chiR S x from noiseOp_chi' ρ S x]
  ring



lemma c_sq_pow {c : ℝ} (hc2 : c^2 = 3) (k : ℕ) : (c^k)^2 = (3:ℝ)^k := by
  rw [← pow_mul c k 2, mul_comm k 2, pow_mul c 2 k, hc2]

/-- **Bonami's lemma for real functions** on the cube of degree `≤ d`, in unnormalised
(sum) form: `2^n ∑ w^4 ≤ 9^d (∑ w^2)^2`. -/
theorem bonami_real (n d : ℕ) (w : (Fin n → ZMod 2) → ℝ)
    (h : ∀ S : Finset (Fin n), d < S.card → (∑ x, w x * chiR S x) = 0) :
    (2:ℝ)^n * ∑ x, (w x)^4 ≤ (9:ℝ)^d * (∑ x, (w x)^2)^2 := by
  set c : ℝ := Real.sqrt 3 with hc
  set ρ : ℝ := c⁻¹ with hρ
  have hc2 : c^2 = 3 := by rw [hc]; exact Real.sq_sqrt (by norm_num)
  have hcpos : 0 < c := by rw [hc]; exact Real.sqrt_pos.mpr (by norm_num)
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hρ2 : ρ^2 = 1/3 := by rw [hρ, inv_pow, hc2]; norm_num
  have hρc : ρ * c = 1 := by rw [hρ]; exact inv_mul_cancel₀ hcne
  set g : (Fin n → ZMod 2) → ℝ :=
    fun y => ∑ S : Finset (Fin n), c^(S.card) * FW w S * chiR S y with hg
  have hHC : (2:ℝ)^n * ∑ x, (noiseOp n ρ g x)^4 ≤ (∑ x, (g x)^2)^2 := by
    have hb := bonami_beckner_four n ρ (le_of_eq hρ2) g
    simpa only [noiseOp] using hb
  have hTg : noiseOp n ρ g = w := by
    funext x
    rw [show noiseOp n ρ g x
          = ∑ S : Finset (Fin n), ρ^(S.card) * ((c^(S.card) * FW w S) * chiR S x) from by
        rw [hg]; exact noiseOp_sum ρ (fun S => c^(S.card) * FW w S) x]
    rw [show (∑ S, ρ^(S.card) * ((c^(S.card) * FW w S) * chiR S x))
          = ∑ S, FW w S * chiR S x from by
        apply Finset.sum_congr rfl; intro S _
        rw [show ρ^(S.card) * ((c^(S.card) * FW w S) * chiR S x)
              = (ρ^(S.card) * c^(S.card)) * (FW w S * chiR S x) by ring,
            show ρ^(S.card) * c^(S.card) = 1 from by rw [← mul_pow, hρc, one_pow],
            one_mul]]
    rw [inversion]
  have hsumsq : (∑ x, (g x)^2) = (2:ℝ)^n * ∑ S, (c^(S.card) * FW w S)^2 := by
    rw [hg]; exact sum_sq_chi_comb (fun S => c^(S.card) * FW w S)
  have hcoef : (∑ S : Finset (Fin n), (c^(S.card) * FW w S)^2)
      = ∑ S : Finset (Fin n), (3:ℝ)^(S.card) * (FW w S)^2 := by
    apply Finset.sum_congr rfl; intro S _
    rw [mul_pow, c_sq_pow hc2 S.card]
  have hle : (∑ S : Finset (Fin n), (3:ℝ)^(S.card) * (FW w S)^2)
      ≤ (3:ℝ)^d * ∑ S : Finset (Fin n), (FW w S)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro S _
    by_cases hSc : d < S.card
    · rw [show FW w S = 0 from by simp only [FW]; rw [h S hSc]; simp]; simp
    · have hcard : S.card ≤ d := by omega
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard) (sq_nonneg _)
  have hparse : (∑ S : Finset (Fin n), (FW w S)^2) = (∑ x, (w x)^2) / 2^n := parseval w
  have h2n : (2:ℝ)^n ≠ 0 := pow_ne_zero n (by norm_num)
  have hTw : (2:ℝ)^n * ((∑ x, (w x)^2) / 2^n) = ∑ x, (w x)^2 := by
    rw [div_eq_mul_inv, mul_comm (∑ x, (w x)^2) ((2:ℝ)^n)⁻¹, ← mul_assoc,
      mul_inv_cancel₀ h2n, one_mul]
  have h9 : ((3:ℝ)^d)^2 = (9:ℝ)^d := by rw [← pow_mul (3:ℝ) d 2, mul_comm d 2, pow_mul (3:ℝ) 2 d]; norm_num
  calc (2:ℝ)^n * ∑ x, (w x)^4
      = (2:ℝ)^n * ∑ x, (noiseOp n ρ g x)^4 := by rw [← hTg]
    _ ≤ (∑ x, (g x)^2)^2 := hHC
    _ = ((2:ℝ)^n * ∑ S, (c^(S.card) * FW w S)^2)^2 := by rw [hsumsq]
    _ = ((2:ℝ)^n * ∑ S, (3:ℝ)^(S.card) * (FW w S)^2)^2 := by rw [hcoef]
    _ ≤ ((2:ℝ)^n * ((3:ℝ)^d * ∑ S, (FW w S)^2))^2 := by
        apply pow_le_pow_left₀ (by positivity)
        exact mul_le_mul_of_nonneg_left hle (by positivity)
    _ = ((3:ℝ)^d * ((2:ℝ)^n * ∑ S, (FW w S)^2))^2 := by ring
    _ = ((3:ℝ)^d * ((2:ℝ)^n * ((∑ x, (w x)^2) / 2^n)))^2 := by rw [hparse]
    _ = ((3:ℝ)^d * (∑ x, (w x)^2))^2 := by rw [hTw]
    _ = (9:ℝ)^d * (∑ x, (w x)^2)^2 := by rw [mul_pow, h9]



theorem bonami_lemma_cube (n d : ℕ) (f : (Fin n → ZMod 2) → ℂ)
    (h : ∀ S : Finset (Fin n), d < S.card →
      (∑ x : Fin n → ZMod 2, f x * ∏ i ∈ S, ((-1 : ℂ) ^ (x i).val)) = 0) :
    (2 : ℝ) ^ n * ∑ x : Fin n → ZMod 2, ‖f x‖ ^ 4 ≤
      (9 : ℝ) ^ d * (∑ x : Fin n → ZMod 2, ‖f x‖ ^ 2) ^ 2 := by
  set u : (Fin n → ZMod 2) → ℝ := fun x => (f x).re with hu
  set v : (Fin n → ZMod 2) → ℝ := fun x => (f x).im with hv
  have huH : ∀ S : Finset (Fin n), d < S.card → (∑ x, u x * chiR S x) = 0 := by
    intro S hS
    have hkey : (∑ x : Fin n → ZMod 2, f x * chiC S x) = 0 := by
      rw [show (∑ x, f x * chiC S x)
            = ∑ x, f x * (∏ i ∈ S, (-1:ℂ)^(x i).val) from
            Finset.sum_congr rfl (fun x _ => by rw [chiC_eq_exp])]
      exact h S hS
    have hre := congrArg Complex.re hkey
    rw [Complex.re_sum, Complex.zero_re] at hre
    rw [← hre]
    apply Finset.sum_congr rfl; intro x _
    simp only [hu]
    rw [← chiC_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hvH : ∀ S : Finset (Fin n), d < S.card → (∑ x, v x * chiR S x) = 0 := by
    intro S hS
    have hkey : (∑ x : Fin n → ZMod 2, f x * chiC S x) = 0 := by
      rw [show (∑ x, f x * chiC S x)
            = ∑ x, f x * (∏ i ∈ S, (-1:ℂ)^(x i).val) from
            Finset.sum_congr rfl (fun x _ => by rw [chiC_eq_exp])]
      exact h S hS
    have him := congrArg Complex.im hkey
    rw [Complex.im_sum, Complex.zero_im] at him
    rw [← him]
    apply Finset.sum_congr rfl; intro x _
    simp only [hv]
    rw [← chiC_ofReal, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  have hbu := bonami_real n d u huH
  have hbv := bonami_real n d v hvH
  set U2 : ℝ := ∑ x, (u x)^2 with hU2
  set V2 : ℝ := ∑ x, (v x)^2 with hV2
  set U4 : ℝ := ∑ x, (u x)^4 with hU4
  set V4 : ℝ := ∑ x, (v x)^4 with hV4
  set M : ℝ := ∑ x, (u x)^2 * (v x)^2 with hM
  have hU2nn : 0 ≤ U2 := by rw [hU2]; exact Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hV2nn : 0 ≤ V2 := by rw [hV2]; exact Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hU4nn : 0 ≤ U4 := by rw [hU4]; exact Finset.sum_nonneg (fun x _ => by positivity)
  have hV4nn : 0 ≤ V4 := by rw [hV4]; exact Finset.sum_nonneg (fun x _ => by positivity)
  have hMnn : 0 ≤ M := by rw [hM]; exact Finset.sum_nonneg (fun x _ => by positivity)
  have hCu : (2:ℝ)^n * U4 ≤ (9:ℝ)^d * U2^2 := by rw [hU4, hU2]; exact hbu
  have hCv : (2:ℝ)^n * V4 ≤ (9:ℝ)^d * V2^2 := by rw [hV4, hV2]; exact hbv
  have hCS : M^2 ≤ U4 * V4 := by
    rw [hM, hU4, hV4]
    have hcs := sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n → ZMod 2))
        (fun x => (u x)^2) (fun x => (v x)^2)
    refine le_trans hcs (le_of_eq ?_)
    congr 1
    · apply Finset.sum_congr rfl; intro x _; ring
    · apply Finset.sum_congr rfl; intro x _; ring
  have hMle : M ≤ Real.sqrt (U4*V4) :=
    (Real.le_sqrt hMnn (mul_nonneg hU4nn hV4nn)).mpr hCS
  have h9 : ((3:ℝ)^d)^2 = (9:ℝ)^d := by rw [← pow_mul (3:ℝ) d 2, mul_comm d 2, pow_mul (3:ℝ) 2 d]; norm_num
  have h3dnn : 0 ≤ (3:ℝ)^d := pow_nonneg (by norm_num) d
  have h2nM_sq : ((2:ℝ)^n * M)^2 ≤ ((2:ℝ)^n*U4)*((2:ℝ)^n*V4) := by
    nlinarith [hCS, sq_nonneg ((2:ℝ)^n)]
  have h2nM' : (2:ℝ)^n * M ≤ Real.sqrt (((2:ℝ)^n*U4)*((2:ℝ)^n*V4)) := by
    have hnn : 0 ≤ (2:ℝ)^n * M := mul_nonneg (by positivity) hMnn
    calc (2:ℝ)^n * M = Real.sqrt (((2:ℝ)^n*M)^2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt (((2:ℝ)^n*U4)*((2:ℝ)^n*V4)) := Real.sqrt_le_sqrt h2nM_sq
  have hsqrtU : Real.sqrt ((2:ℝ)^n*U4) ≤ (3:ℝ)^d * U2 := by
    rw [Real.sqrt_le_left (mul_nonneg h3dnn hU2nn)]
    calc (2:ℝ)^n*U4 ≤ (9:ℝ)^d * U2^2 := hCu
      _ = ((3:ℝ)^d*U2)^2 := by rw [mul_pow, h9]
  have hsqrtV : Real.sqrt ((2:ℝ)^n*V4) ≤ (3:ℝ)^d * V2 := by
    rw [Real.sqrt_le_left (mul_nonneg h3dnn hV2nn)]
    calc (2:ℝ)^n*V4 ≤ (9:ℝ)^d * V2^2 := hCv
      _ = ((3:ℝ)^d*V2)^2 := by rw [mul_pow, h9]
  have h2nM : (2:ℝ)^n * M ≤ (9:ℝ)^d * U2 * V2 := by
    calc (2:ℝ)^n * M ≤ Real.sqrt (((2:ℝ)^n*U4)*((2:ℝ)^n*V4)) := h2nM'
      _ = Real.sqrt ((2:ℝ)^n*U4) * Real.sqrt ((2:ℝ)^n*V4) :=
            Real.sqrt_mul (by positivity : (0:ℝ) ≤ (2:ℝ)^n*U4) ((2:ℝ)^n*V4)
      _ ≤ ((3:ℝ)^d*U2) * ((3:ℝ)^d*V2) :=
            mul_le_mul hsqrtU hsqrtV (Real.sqrt_nonneg _) (mul_nonneg h3dnn hU2nn)
      _ = (9:ℝ)^d * U2 * V2 := by rw [← h9]; ring
  have hCm : 2 * ((2:ℝ)^n * M) ≤ 2 * ((9:ℝ)^d * U2 * V2) :=
    mul_le_mul_of_nonneg_left h2nM (by norm_num)
  have hnorm2 : ∀ x, ‖f x‖^2 = (u x)^2 + (v x)^2 := by
    intro x
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [hu, hv]; ring
  have hnorm4 : ∀ x, ‖f x‖^4 = ((u x)^2 + (v x)^2)^2 := by
    intro x
    rw [show ‖f x‖^4 = (‖f x‖^2)^2 by ring, hnorm2 x]
  have hsum4 : (∑ x, ‖f x‖^4) = U4 + 2*M + V4 := by
    simp only [hU4, hM, hV4]
    rw [Finset.sum_congr rfl (fun x _ => hnorm4 x)]
    rw [Finset.sum_congr rfl (fun x _ => by ring :
        ∀ x ∈ (Finset.univ : Finset (Fin n → ZMod 2)),
          ((u x)^2 + (v x)^2)^2 = (u x)^4 + 2*((u x)^2*(v x)^2) + (v x)^4)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hsum2 : (∑ x, ‖f x‖^2) = U2 + V2 := by
    rw [hU2, hV2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _; rw [hnorm2 x]
  calc (2:ℝ)^n * ∑ x, ‖f x‖^4
      = (2:ℝ)^n * (U4 + 2*M + V4) := by rw [hsum4]
    _ = (2:ℝ)^n*U4 + 2*((2:ℝ)^n*M) + (2:ℝ)^n*V4 := by ring
    _ ≤ (9:ℝ)^d*U2^2 + 2*((9:ℝ)^d*U2*V2) + (9:ℝ)^d*V2^2 := by
        linarith [hCu, hCv, hCm]
    _ = (9:ℝ)^d * (U2+V2)^2 := by ring
    _ = (9:ℝ)^d * (∑ x, ‖f x‖^2)^2 := by rw [hsum2]

end

end Commons.Analysis.Inequalities
