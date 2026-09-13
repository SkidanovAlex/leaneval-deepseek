import Mathlib
import Submission.Hypercube.Walsh
import Submission.Commons.Analysis.Inequalities.bonami_lemma_cube
import Submission.Commons.Analysis.Complex.norm_sum_sq_le_card_mul
import Submission.Commons.Analysis.Walsh.sum_powerset_neg_one_pow_complex
import Submission.Commons.Combinatorics.Finset.sum_powerset_filter_subset
import Submission.Commons.Analysis.Walsh.sum_norm_sq_chi_orthogonal

/-!
# The resampling / restriction calculus on the cube `𝔽₂ⁿ`

This file builds, for `𝔽₂ⁿ`, the operators appearing in §2 of
arXiv:2209.04243 (the "warm-up" chapter proving a conditional hypercontractive
inequality on `𝔽₂ⁿ`), on top of the Walsh–Fourier calculus of
`Submission.Hypercube.Walsh`:

* `combine T x z` – the vector that equals `x` on the coordinates in `T` and `z` elsewhere;
* `restr T x f` – the restriction `f_{T→x}`, viewed again as a function on the whole cube
  (it only depends on the coordinates outside `T`);
* `extend T y` – the extension of `y : T → 𝔽₂` by zero;
* `ES T f` – the resampling ("expectation") operator `E_T`, averaging over the `T` coordinates;
* `Deg d f` – Efron–Stein degree `≤ d`;
* `mu f`, `mu4 f` – the normalised square `‖f‖₂²` and fourth power `‖f‖₄⁴`;
* `Dfun T x f` – the derivative `D_{T,x}[f] = (L_T[f])_{T→x}`;
* `inflPair T x f`, `inflSet T f` – the influences `I_{T,x}[f]`, `I_T[f]`;
* `Global d ε f` – `(d, ε)`-globalness.
-/

open Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Hypercube

noncomputable section

variable {n : ℕ}

/-! ## Combining coordinates, and restrictions -/

/-- `combine T x z` is the vector that agrees with `x` on the coordinates in `T` and with `z`
elsewhere. -/
def combine (T : Finset (Fin n)) (x z : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => if i ∈ T then x i else z i

@[simp] lemma combine_apply_mem (T : Finset (Fin n)) (x z : Fin n → ZMod 2) {i : Fin n}
    (h : i ∈ T) : combine T x z i = x i := if_pos h

@[simp] lemma combine_apply_notMem (T : Finset (Fin n)) (x z : Fin n → ZMod 2) {i : Fin n}
    (h : i ∉ T) : combine T x z i = z i := if_neg h

lemma combine_self (T : Finset (Fin n)) (x : Fin n → ZMod 2) : combine T x x = x :=
  funext fun i => by by_cases h : i ∈ T <;> simp [combine, h]

lemma combine_combine (T : Finset (Fin n)) (x y z : Fin n → ZMod 2) :
    combine T x (combine T y z) = combine T x z :=
  funext fun i => by by_cases h : i ∈ T <;> simp [combine, h]

/-- The restriction `f_{T → x}` of `f`, as a function on the whole cube: it agrees with `f` on
the slice of vectors that equal `x` on `T`. -/
def restr (T : Finset (Fin n)) (x : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ℂ) :
    (Fin n → ZMod 2) → ℂ :=
  fun z => f (combine T x z)

@[simp] lemma restr_apply (T : Finset (Fin n)) (x z : Fin n → ZMod 2)
    (f : (Fin n → ZMod 2) → ℂ) : restr T x f z = f (combine T x z) := rfl

lemma restr_restr (T : Finset (Fin n)) (x y : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ℂ) :
    restr T x (restr T y f) = restr T y f := by
  funext z; simp only [restr_apply, combine_combine]

@[simp] lemma restr_zero (T : Finset (Fin n)) (x : Fin n → ZMod 2) :
    restr T x (0 : (Fin n → ZMod 2) → ℂ) = 0 := by
  funext z; simp [restr]

lemma restr_add (T : Finset (Fin n)) (x : Fin n → ZMod 2)
    (f g : (Fin n → ZMod 2) → ℂ) : restr T x (f + g) = restr T x f + restr T x g := by
  funext z; simp only [restr_apply, Pi.add_apply]

lemma restr_neg (T : Finset (Fin n)) (x : Fin n → ZMod 2)
    (f : (Fin n → ZMod 2) → ℂ) : restr T x (-f) = -restr T x f := by
  funext z; simp only [restr_apply, Pi.neg_apply]

lemma restr_sub (T : Finset (Fin n)) (x : Fin n → ZMod 2)
    (f g : (Fin n → ZMod 2) → ℂ) : restr T x (f - g) = restr T x f - restr T x g := by
  funext z; simp only [restr_apply, Pi.sub_apply]

lemma restr_smul (T : Finset (Fin n)) (x : Fin n → ZMod 2) (c : ℂ)
    (f : (Fin n → ZMod 2) → ℂ) : restr T x (c • f) = c • restr T x f := by
  funext z; simp only [restr_apply, Pi.smul_apply]

lemma restr_sum (T : Finset (Fin n)) (x : Fin n → ZMod 2) {ι : Type*}
    (s : Finset ι) (f : ι → (Fin n → ZMod 2) → ℂ) :
    restr T x (∑ i ∈ s, f i) = ∑ i ∈ s, restr T x (f i) := by
  funext z; simp only [restr_apply, Finset.sum_apply]

/-- The Walsh character splits under `combine`. -/
lemma chi_combine (R T : Finset (Fin n)) (x z : Fin n → ZMod 2) :
    chi R (combine T x z) = chi (R ∩ T) x * chi (R \ T) z := by
  rw [chi, chi, chi]
  have hsplit : (∏ i ∈ R, ZMod.stdAddChar (combine T x z i))
      = (∏ i ∈ R ∩ T, ZMod.stdAddChar (combine T x z i))
        * (∏ i ∈ R \ T, ZMod.stdAddChar (combine T x z i)) :=
    (Finset.prod_inter_mul_prod_sdiff _ _ _).symm
  rw [hsplit]
  congr 1
  · apply Finset.prod_congr rfl; intro i hi
    rw [Finset.mem_inter] at hi; rw [combine_apply_mem T x z hi.2]
  · apply Finset.prod_congr rfl; intro i hi
    rw [Finset.mem_sdiff] at hi; rw [combine_apply_notMem T x z hi.2]

/-- Restriction of a Walsh character. -/
lemma restr_chi (T U : Finset (Fin n)) (x : Fin n → ZMod 2) :
    restr T x (chi U) = fun z => chi (U ∩ T) x * chi (U \ T) z := by
  funext z; simp only [restr_apply, chi_combine]


/-! ## Extending a function on a coordinate set by zero -/

/-- Extend `y : T → 𝔽₂` by zero to the whole cube. -/
def extend (T : Finset (Fin n)) (y : T → ZMod 2) : Fin n → ZMod 2 :=
  fun i => if h : i ∈ T then y ⟨i, h⟩ else 0

lemma extend_apply_mem (T : Finset (Fin n)) (y : T → ZMod 2) {i : Fin n} (h : i ∈ T) :
    extend T y i = y ⟨i, h⟩ := dif_pos h

lemma extend_apply_notMem (T : Finset (Fin n)) (y : T → ZMod 2) {i : Fin n} (h : i ∉ T) :
    extend T y i = 0 := dif_neg h

lemma extend_mem_of_ne_zero (T : Finset (Fin n)) (y : T → ZMod 2) {i : Fin n}
    (h : extend T y i ≠ 0) : i ∈ T := by
  by_contra hc; exact h (extend_apply_notMem T y hc)

/-- The value of a character on an extended vector. -/
lemma chi_extend_eq (R T : Finset (Fin n)) (y : T → ZMod 2) :
    chi R (extend T y) = ∏ i : T, (if (i : Fin n) ∈ R then ZMod.stdAddChar (y i) else 1) := by
  have h1 : (∏ i : T, (if (i : Fin n) ∈ R then ZMod.stdAddChar (y i) else 1))
      = ∏ i : T, (if (i : Fin n) ∈ R then ZMod.stdAddChar (extend T y i) else 1) := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : (i : Fin n) ∈ R
    · rw [if_pos hi, if_pos hi, extend_apply_mem T y i.2]
    · rw [if_neg hi, if_neg hi]
  have h2 : (∏ i : T, (if (i : Fin n) ∈ R then ZMod.stdAddChar (extend T y i) else 1))
      = ∏ i ∈ T, (if i ∈ R then ZMod.stdAddChar (extend T y i) else 1) :=
    (Finset.prod_subtype T (p := fun x => x ∈ T) (h := fun x => Iff.rfl)
      (f := fun i => if i ∈ R then ZMod.stdAddChar (extend T y i) else 1)).symm
  have h3 : (∏ i ∈ T, (if i ∈ R then ZMod.stdAddChar (extend T y i) else 1))
      = ∏ i ∈ R ∩ T, ZMod.stdAddChar (extend T y i) := by
    rw [← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
  have h4 : (∏ i ∈ R ∩ T, ZMod.stdAddChar (extend T y i))
      = ∏ i ∈ R, ZMod.stdAddChar (extend T y i) := by
    refine Finset.prod_subset (fun x hx => (Finset.mem_inter.mp hx).1) ?_
    intro x hxR hxnot
    have hxT : x ∉ T := fun hc => hxnot (Finset.mem_inter.mpr ⟨hxR, hc⟩)
    rw [extend_apply_notMem T y hxT, ZMod.stdAddChar.map_zero_eq_one]
  rw [chi, h1, h2, h3, h4]

/-- The character sum over a coordinate set: it vanishes unless `R` is disjoint from `T`. -/
lemma sum_extend_chi (R T : Finset (Fin n)) :
    (∑ y : T → ZMod 2, chi R (extend T y))
      = if R ∩ T = ∅ then (2 : ℂ) ^ T.card else 0 := by
  have hmain : (∑ y : T → ZMod 2, chi R (extend T y))
      = ∏ i : T, (∑ a : ZMod 2, (if (i : Fin n) ∈ R then ZMod.stdAddChar a else 1)) := by
    rw [show (∑ y : T → ZMod 2, chi R (extend T y))
        = ∑ y : T → ZMod 2,
            ∏ i : T, (if (i : Fin n) ∈ R then ZMod.stdAddChar (y i) else 1) from
      Finset.sum_congr rfl (fun y _ => chi_extend_eq R T y)]
    exact sum_prod_pi' (κ := fun _ : ↥T => ZMod 2)
      (fun i a => if (i : Fin n) ∈ R then ZMod.stdAddChar a else 1)
  rw [hmain]
  have h2 : ∀ i : T, (∑ a : ZMod 2, (if (i : Fin n) ∈ R then ZMod.stdAddChar a else 1))
      = if (i : Fin n) ∈ R then (0 : ℂ) else 2 := by
    intro i
    by_cases hi : (i : Fin n) ∈ R
    · simp only [if_pos hi]
      exact sum_stdAddChar_zmod_two
    · simp only [if_neg hi]
      simp
  rw [show (∏ i : T, (∑ a : ZMod 2, (if (i : Fin n) ∈ R then ZMod.stdAddChar a else 1)))
      = ∏ i : T, (if (i : Fin n) ∈ R then (0 : ℂ) else 2) from
    Finset.prod_congr rfl (fun i _ => h2 i)]
  by_cases hRT : R ∩ T = ∅
  · rw [if_pos hRT]
    have hmem : ∀ i : T, (i : Fin n) ∉ R := by
      intro i hi
      have hmem' : (i : Fin n) ∈ R ∩ T := Finset.mem_inter.mpr ⟨hi, i.2⟩
      rw [hRT] at hmem'
      exact Finset.notMem_empty _ hmem'
    rw [show (∏ i : T, (if (i : Fin n) ∈ R then (0 : ℂ) else 2)) = ∏ _i : T, (2 : ℂ) from
      Finset.prod_congr rfl (fun i _ => by rw [if_neg (hmem i)])]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  · rw [if_neg hRT]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hRT
    refine Finset.prod_eq_zero (Finset.mem_univ (⟨i, (Finset.mem_inter.mp hi).2⟩ : T)) ?_
    simp only [if_pos (Finset.mem_inter.mp hi).1]

/-! ## The resampling operator `E_T` -/

/-- The resampling ("expectation") operator: average `f` over the coordinates in `T`. -/
def ES (T : Finset (Fin n)) (f : (Fin n → ZMod 2) → ℂ) : (Fin n → ZMod 2) → ℂ :=
  fun x => ((2 : ℂ) ^ T.card)⁻¹ * ∑ y : T → ZMod 2, f (x + extend T y)

lemma ES_apply (T : Finset (Fin n)) (f : (Fin n → ZMod 2) → ℂ) (x : Fin n → ZMod 2) :
    ES T f x = ((2 : ℂ) ^ T.card)⁻¹ * ∑ y : T → ZMod 2, f (x + extend T y) := rfl

@[simp] lemma ES_zero (T : Finset (Fin n)) : ES T (0 : (Fin n → ZMod 2) → ℂ) = 0 := by
  funext x; simp [ES]

lemma ES_add (T : Finset (Fin n)) (f g : (Fin n → ZMod 2) → ℂ) :
    ES T (f + g) = ES T f + ES T g := by
  funext x
  simp only [ES_apply, Pi.add_apply, Finset.sum_add_distrib, mul_add]

lemma ES_smul (T : Finset (Fin n)) (c : ℂ) (f : (Fin n → ZMod 2) → ℂ) :
    ES T (c • f) = c • ES T f := by
  funext x
  simp only [ES_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

lemma ES_sum (T : Finset (Fin n)) {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ZMod 2) → ℂ) :
    ES T (∑ i ∈ s, f i) = ∑ i ∈ s, ES T (f i) := by
  funext x
  simp only [ES_apply, Finset.sum_apply]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- **Translation formula** for the Walsh transform. -/
lemma walshFourier_shift (R : Finset (Fin n)) (e : Fin n → ZMod 2)
    (f : (Fin n → ZMod 2) → ℂ) :
    walshFourier (fun x => f (x + e)) R = chi R e * walshFourier f R := by
  rw [walshFourier, walshFourier]
  have h1 : ∀ x : Fin n → ZMod 2, f (x + e) * chi R x = chi R e * (f (x + e) * chi R (x + e)) := by
    intro x
    rw [chi_add]
    rw [show chi R e * (f (x + e) * (chi R x * chi R e))
        = f (x + e) * chi R x * (chi R e * chi R e) from by ring, chi_self, mul_one]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.addRight e) (fun u => f u * chi R u)

lemma walshFourier_sum {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ZMod 2) → ℂ)
    (R : Finset (Fin n)) :
    walshFourier (∑ i ∈ s, f i) R = ∑ i ∈ s, walshFourier (f i) R := by
  simp only [walshFourier, Finset.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_mul]

/-- The Walsh transform of a resampled function: it keeps the characters disjoint from `T`. -/
theorem walshFourier_ES (T R : Finset (Fin n)) (f : (Fin n → ZMod 2) → ℂ) :
    walshFourier (ES T f) R = if R ∩ T = ∅ then walshFourier f R else 0 := by
  have h2 : ((2 : ℂ) ^ T.card) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hshift : ∀ y : T → ZMod 2, walshFourier (fun x => f (x + extend T y)) R
      = chi R (extend T y) * walshFourier f R := fun y => walshFourier_shift R _ f
  rw [show ES T f = ((2 : ℂ) ^ T.card)⁻¹ • (∑ y : T → ZMod 2, fun x => f (x + extend T y)) from by
    funext x; simp only [ES_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]]
  rw [walshFourier_smul, walshFourier_sum]
  rw [Finset.sum_congr rfl (fun y _ => hshift y)]
  rw [show (∑ y : T → ZMod 2, chi R (extend T y) * walshFourier f R)
      = walshFourier f R * ∑ y : T → ZMod 2, chi R (extend T y) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => by ring)]
  rw [sum_extend_chi]
  by_cases hRT : R ∩ T = ∅
  · rw [if_pos hRT, if_pos hRT, mul_comm (walshFourier f R) ((2 : ℂ) ^ T.card), ← mul_assoc,
      inv_mul_cancel₀ h2, one_mul]
  · rw [if_neg hRT, if_neg hRT]; ring

/-! ## Normalised norms -/

/-- The normalised squared `L²` norm `‖f‖₂²` on `𝔽₂ⁿ`. -/
def mu (f : (Fin n → ZMod 2) → ℂ) : ℝ := ((2 : ℝ) ^ n)⁻¹ * ∑ x, ‖f x‖ ^ 2

/-- The normalised fourth power `‖f‖₄⁴` on `𝔽₂ⁿ`. -/
def mu4 (f : (Fin n → ZMod 2) → ℂ) : ℝ := ((2 : ℝ) ^ n)⁻¹ * ∑ x, ‖f x‖ ^ 4

lemma mu_nonneg (f : (Fin n → ZMod 2) → ℂ) : 0 ≤ mu f :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)

lemma mu_smul (c : ℂ) (f : (Fin n → ZMod 2) → ℂ) : mu (c • f) = ‖c‖ ^ 2 * mu f := by
  rw [mu, mu]
  rw [show (∑ x, ‖(c • f) x‖ ^ 2) = ∑ x, (‖c‖ ^ 2 * ‖f x‖ ^ 2) from
    Finset.sum_congr rfl fun x _ => by
      show ‖c * f x‖ ^ 2 = ‖c‖ ^ 2 * ‖f x‖ ^ 2
      rw [norm_mul, mul_pow]]
  rw [← Finset.mul_sum]
  ring

lemma mu4_nonneg (f : (Fin n → ZMod 2) → ℂ) : 0 ≤ mu4 f :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)


/-! ## The Efron--Stein projection and its linearity -/

/-- The normalised Fourier coefficient, i.e. the coefficient of `chi S` in `f`. -/
def efronCoeff (f : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) : ℂ :=
  ((2 : ℂ) ^ n)⁻¹ * walshFourier f S

lemma efronStein_eq_smul (f : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    efronStein f S = efronCoeff f S • chi S := by
  funext x; simp only [efronStein_apply, efronCoeff, Pi.smul_apply, smul_eq_mul]; ring

@[simp] lemma walshFourier_zero (S : Finset (Fin n)) :
    walshFourier (0 : (Fin n → ZMod 2) → ℂ) S = 0 := by
  simp [walshFourier]

@[simp] lemma efronCoeff_zero (S : Finset (Fin n)) : efronCoeff (0 : (Fin n → ZMod 2) → ℂ) S = 0 := by
  simp [efronCoeff]

@[simp] lemma efronStein_zero (S : Finset (Fin n)) : efronStein (0 : (Fin n → ZMod 2) → ℂ) S = 0 := by
  rw [efronStein_eq_smul]; simp

@[simp] lemma walshFourier_neg (f : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    walshFourier (-f) S = -walshFourier f S := by
  simp only [walshFourier, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

@[simp] lemma efronCoeff_neg (f : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    efronCoeff (-f) S = -efronCoeff f S := by
  simp only [efronCoeff, walshFourier_neg]; ring

lemma efronCoeff_add (f g : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    efronCoeff (f + g) S = efronCoeff f S + efronCoeff g S := by
  simp only [efronCoeff, walshFourier_add, mul_add]

lemma efronCoeff_smul (c : ℂ) (f : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    efronCoeff (c • f) S = c * efronCoeff f S := by
  simp only [efronCoeff, walshFourier_smul]; ring

lemma efronCoeff_sum {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ZMod 2) → ℂ)
    (S : Finset (Fin n)) :
    efronCoeff (∑ i ∈ s, f i) S = ∑ i ∈ s, efronCoeff (f i) S := by
  rw [efronCoeff, walshFourier_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [efronCoeff]

lemma efronStein_add (f g : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    efronStein (f + g) S = efronStein f S + efronStein g S := by
  rw [efronStein_eq_smul, efronStein_eq_smul, efronStein_eq_smul, efronCoeff_add, add_smul]

lemma efronStein_neg (f : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    efronStein (-f) S = -efronStein f S := by
  rw [efronStein_eq_smul, efronStein_eq_smul, efronCoeff_neg, neg_smul]

lemma efronStein_sub (f g : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    efronStein (f - g) S = efronStein f S - efronStein g S := by
  rw [sub_eq_add_neg, efronStein_add, efronStein_neg, sub_eq_add_neg]

lemma efronStein_smul (c : ℂ) (f : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    efronStein (c • f) S = c • efronStein f S := by
  rw [efronStein_eq_smul, efronStein_eq_smul, efronCoeff_smul, mul_smul]

lemma efronStein_sum {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ZMod 2) → ℂ)
    (S : Finset (Fin n)) :
    efronStein (∑ i ∈ s, f i) S = ∑ i ∈ s, efronStein (f i) S := by
  rw [efronStein_eq_smul, efronCoeff_sum, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [efronStein_eq_smul]

/-- Two functions with the same Walsh transform are equal. -/
lemma eq_of_walshFourier_eq {f g : (Fin n → ZMod 2) → ℂ}
    (h : ∀ S : Finset (Fin n), walshFourier f S = walshFourier g S) : f = g := by
  funext y
  have hf := walsh_inversion f y
  have hg := walsh_inversion g y
  have hsum : (∑ S : Finset (Fin n), walshFourier f S * chi S y)
      = ∑ S : Finset (Fin n), walshFourier g S * chi S y :=
    Finset.sum_congr rfl fun S _ => by rw [h S]
  rw [hf, hg] at hsum
  exact mul_left_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0)) hsum

/-! ## Characters and the Laplacian -/

lemma walshFourier_chi (U R : Finset (Fin n)) :
    walshFourier (chi U) R = if R = U then (2 : ℂ) ^ n else 0 := by
  rw [walshFourier, chi_orthogonal]
  by_cases h : R = U
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun hc => h hc.symm]

lemma efronStein_chi (U R : Finset (Fin n)) :
    efronStein (chi U) R = if R = U then chi U else 0 := by
  funext x
  rw [efronStein_apply, walshFourier_chi]
  by_cases h : R = U
  · rw [if_pos h, if_pos h, h, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℂ) ≠ 0)), one_mul]
  · rw [if_neg h, if_neg h]; simp

/-- The Efron--Stein projection of the Laplacian. -/
lemma efronStein_lapS (f : (Fin n → ZMod 2) → ℂ) (S R : Finset (Fin n)) :
    efronStein (lapS f S) R = if S ⊆ R then efronStein f R else 0 := by
  funext x
  rw [efronStein_apply, walshFourier_lapS]
  by_cases h : S ⊆ R
  · rw [if_pos h, if_pos h, efronStein_apply]
  · rw [if_neg h, if_neg h]; simp

/-! ## Restrictions of characters -/

lemma restr_smul_chi (T U : Finset (Fin n)) (x : Fin n → ZMod 2) (c : ℂ) :
    restr T x (c • chi U) = (c * chi (U ∩ T) x) • chi (U \ T) := by
  funext z
  rw [restr_smul, restr_chi]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma efronStein_restr_smul_chi (T U S : Finset (Fin n)) (x : Fin n → ZMod 2) (c : ℂ) :
    efronStein (restr T x (c • chi U)) S
      = if S = U \ T then (c * chi (U ∩ T) x) • chi S else 0 := by
  rw [restr_smul_chi, efronStein_smul, efronStein_chi]
  by_cases h : S = U \ T
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h, smul_zero]

/-! ## The derivative `D_{T,x}` -/

/-- The derivative `D_{T,x}[f] = (L_T[f])_{T → x}`. -/
def Dfun (T : Finset (Fin n)) (x : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ℂ) :
    (Fin n → ZMod 2) → ℂ :=
  restr T x (lapS f T)

lemma Dfun_apply (T : Finset (Fin n)) (x : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ℂ) :
    Dfun T x f = restr T x (lapS f T) := rfl

/-- **Lemma 2.9 of arXiv:2209.04243** (degree reduction): the Efron--Stein components of the
derivative `D_{T,x}[f]` are the restrictions of the components of `f`. -/
theorem efronStein_Dfun (T S : Finset (Fin n)) (hTS : Disjoint T S) (x : Fin n → ZMod 2)
    (f : (Fin n → ZMod 2) → ℂ) :
    efronStein (Dfun T x f) S = restr T x (efronStein f (T ∪ S)) := by
  have hdisj : (T ∪ S) \ T = S := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hnT⟩
      · exact absurd h hnT
      · exact h
    · intro h; exact ⟨Or.inr h, Finset.disjoint_right.mp hTS h⟩
  have hinter : (T ∪ S) ∩ T = T := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_union]
    exact ⟨fun h => h.2, fun h => ⟨Or.inl h, h⟩⟩
  have hlap : lapS f T
      = ∑ V ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun V => T ⊆ V),
          efronCoeff f V • chi V := by
    simp only [lapS]
    exact Finset.sum_congr rfl fun V _ => efronStein_eq_smul f V
  rw [Dfun_apply, hlap, restr_sum, efronStein_sum]
  rw [show (∑ V ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun V => T ⊆ V),
        efronStein (restr T x (efronCoeff f V • chi V)) S)
      = ∑ V ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun V => T ⊆ V),
        (if S = V \ T then (efronCoeff f V * chi (V ∩ T) x) • chi S else 0) from
    Finset.sum_congr rfl fun V _ => efronStein_restr_smul_chi T V S x _]
  rw [Finset.sum_eq_single (T ∪ S)]
  · rw [if_pos hdisj.symm]
    rw [efronStein_eq_smul, restr_smul, restr_chi]
    simp only [hinter, hdisj]
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro V hV hne
    rw [if_neg]
    intro hSV
    refine hne ?_
    rw [hSV]
    exact (Finset.union_sdiff_of_subset (Finset.mem_filter.mp hV).2).symm
  · intro hmem
    refine absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x hx => Finset.mem_union_left S hx⟩) hmem


/-! ## Degree, and the (complex) Bonami bound -/

lemma stdAddChar_zmod_two (a : ZMod 2) : ZMod.stdAddChar a = (-1 : ℂ) ^ (a.val) := by
  rcases Commons.Analysis.Inequalities.zmod2_cases a with h | h
  · rw [h, ZMod.val_zero]; simp
  · rw [h, show ((1 : ZMod 2).val) = 1 from by decide]
    rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) from by simp, ZMod.stdAddChar_coe]
    rw [show (2 * ↑Real.pi * Complex.I * ↑(1 : ℤ) / ↑(2 : ℕ) : ℂ) = ↑Real.pi * Complex.I from by
          push_cast; ring, Complex.exp_pi_mul_I]
    norm_num

lemma chi_eq_prod_neg_one (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    chi S x = ∏ i ∈ S, ((-1 : ℂ) ^ (x i).val) := by
  rw [chi]
  exact Finset.prod_congr rfl fun i _ => stdAddChar_zmod_two (x i)

/-- `f` has Efron--Stein degree at most `d`. -/
def Deg (d : ℕ) (f : (Fin n → ZMod 2) → ℂ) : Prop :=
  ∀ S : Finset (Fin n), d < S.card → walshFourier f S = 0

lemma deg_iff_efronStein {d : ℕ} {f : (Fin n → ZMod 2) → ℂ} :
    Deg d f ↔ ∀ S : Finset (Fin n), d < S.card → efronStein f S = 0 := by
  unfold Deg
  constructor
  · intro h S hS
    rw [efronStein_eq_smul, efronCoeff, h S hS, mul_zero, zero_smul]
  · intro h S hS
    have h2 : ((2 : ℂ) ^ n)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (by norm_num))
    have := h S hS
    rw [efronStein_eq_smul, efronCoeff, smul_eq_zero] at this
    rcases this with h1 | h2'
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · exact absurd h3 h2
      · exact h4
    · have h1 : (1 : ℂ) = 0 := by rw [← chi_zero S, h2']; rfl
      exact absurd h1 one_ne_zero

lemma deg_mono {d d' : ℕ} {f : (Fin n → ZMod 2) → ℂ} (h : d ≤ d') (hf : Deg d f) : Deg d' f :=
  fun S hS => hf S (lt_of_le_of_lt h hS)

/-- **Bonami's lemma on the cube, complex form**: a function of degree `≤ d` satisfies
`‖f‖₄⁴ ≤ 9^d ‖f‖₂⁴`. -/
theorem mu4_le_of_deg (d : ℕ) (f : (Fin n → ZMod 2) → ℂ) (hf : Deg d f) :
    mu4 f ≤ (9 : ℝ) ^ d * (mu f) ^ 2 := by
  have hchi : ∀ S : Finset (Fin n),
      (∑ x, f x * ∏ i ∈ S, ((-1 : ℂ) ^ (x i).val)) = walshFourier f S := by
    intro S
    rw [walshFourier]
    exact Finset.sum_congr rfl fun x _ => by rw [chi_eq_prod_neg_one]
  have hb := Commons.Analysis.Inequalities.bonami_lemma_cube n d f
    (fun S hS => by rw [hchi S]; exact hf S hS)
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h2nn : ((2 : ℝ) ^ n) ≠ 0 := ne_of_gt h2n
  have hA : (∑ x, ‖f x‖ ^ 4) ≤ (9 : ℝ) ^ d * (∑ x, ‖f x‖ ^ 2) ^ 2 / (2 : ℝ) ^ n := by
    rw [le_div_iff₀ h2n]
    simpa [mul_comm] using hb
  calc mu4 f = ((2 : ℝ) ^ n)⁻¹ * ∑ x, ‖f x‖ ^ 4 := rfl
    _ ≤ ((2 : ℝ) ^ n)⁻¹ * ((9 : ℝ) ^ d * (∑ x, ‖f x‖ ^ 2) ^ 2 / (2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ = (9 : ℝ) ^ d * (mu f) ^ 2 := by
        rw [mu, div_eq_mul_inv]
        field_simp
/-! ## Degree reduction -/

/-- The unit vector at a coordinate. -/
def unit (i : Fin n) : Fin n → ZMod 2 := fun j => if j = i then 1 else 0

lemma stdAddChar_one : ZMod.stdAddChar (1 : ZMod 2) = -1 := by
  rw [stdAddChar_zmod_two, show ((1 : ZMod 2).val) = 1 from by decide, pow_one]

lemma chi_unit (S : Finset (Fin n)) (i : Fin n) :
    chi S (unit i) = if i ∈ S then -1 else 1 := by
  by_cases hi : i ∈ S
  · rw [if_pos hi, chi,
      (Finset.mul_prod_erase S (fun j => ZMod.stdAddChar (unit i j)) hi).symm]
    rw [show ZMod.stdAddChar (unit i i) = -1 from by rw [unit, if_pos rfl]; exact stdAddChar_one]
    rw [show (∏ x ∈ S.erase i, ZMod.stdAddChar (unit i x)) = 1 from
      Finset.prod_eq_one fun j hj => by
        rw [Finset.mem_erase] at hj
        rw [unit, if_neg hj.1, ZMod.stdAddChar.map_zero_eq_one]]
    ring
  · rw [if_neg hi, chi]
    exact Finset.prod_eq_one fun j hj => by
      by_cases hji : j = i
      · rw [unit, if_pos hji]
        exact absurd (hji ▸ hj) hi
      · rw [unit, if_neg hji, ZMod.stdAddChar.map_zero_eq_one]

lemma combine_add_unit (T : Finset (Fin n)) (x z : Fin n → ZMod 2) {i : Fin n} (hi : i ∈ T) :
    combine T x (z + unit i) = combine T x z := by
  funext j
  by_cases hj : j ∈ T
  · rw [combine_apply_mem T x (z + unit i) hj, combine_apply_mem T x z hj]
  · rw [combine_apply_notMem T x (z + unit i) hj, combine_apply_notMem T x z hj, Pi.add_apply]
    by_cases hji : j = i
    · exact absurd (hji ▸ hi) hj
    · rw [unit, if_neg hji, add_zero]

/-- A restriction kills every character that is not disjoint from the restricted coordinates. -/
lemma walshFourier_restr_eq_zero (T S : Finset (Fin n)) (x : Fin n → ZMod 2)
    (g : (Fin n → ZMod 2) → ℂ) (hTS : ¬ Disjoint T S) :
    walshFourier (restr T x g) S = 0 := by
  have hne : (T ∩ S).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun h => hTS (Finset.disjoint_iff_inter_eq_empty.mpr h)
  obtain ⟨i, hi⟩ := hne
  have hiT : i ∈ T := (Finset.mem_inter.mp hi).1
  have hiS : i ∈ S := (Finset.mem_inter.mp hi).2
  rw [walshFourier]
  have hA : ∀ z, restr T x g (z + unit i) * chi S (z + unit i)
      = - (restr T x g z * chi S z) := by
    intro z
    rw [restr_apply, restr_apply, combine_add_unit T x z hiT, chi_add, chi_unit S i, if_pos hiS]
    ring
  have hsum : (∑ z, restr T x g (z + unit i) * chi S (z + unit i))
      = ∑ z, restr T x g z * chi S z :=
    Equiv.sum_comp (Equiv.addRight (unit i)) (fun z => restr T x g z * chi S z)
  rw [Finset.sum_congr rfl (fun z _ => hA z), Finset.sum_neg_distrib] at hsum
  have h2 : (2 : ℂ) * (∑ z, restr T x g z * chi S z) = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hsum.symm]
    ring
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

lemma efronStein_restr_eq_zero (T S : Finset (Fin n)) (x : Fin n → ZMod 2)
    (g : (Fin n → ZMod 2) → ℂ) (hTS : ¬ Disjoint T S) :
    efronStein (restr T x g) S = 0 := by
  rw [efronStein_eq_smul, efronCoeff, walshFourier_restr_eq_zero T S x g hTS, mul_zero, zero_smul]

/-- **Degree reduction** (the corollary of Lemma 2.9): the derivative `D_{T,x}` lowers the
Efron--Stein degree by `|T|`. -/
theorem deg_Dfun (d : ℕ) (T : Finset (Fin n)) (x : Fin n → ZMod 2)
    (f : (Fin n → ZMod 2) → ℂ) (hf : Deg d f) :
    Deg (d - T.card) (Dfun T x f) := by
  rw [deg_iff_efronStein] at hf ⊢
  intro S hS
  by_cases hTS : Disjoint T S
  · rw [efronStein_Dfun T S hTS x f]
    have hcard : d < (T ∪ S).card := by
      rw [Finset.card_union_of_disjoint hTS]
      by_cases hTd : T.card ≤ d
      · omega
      · omega
    rw [hf (T ∪ S) hcard, restr_zero T x]
  · rw [Dfun_apply, efronStein_restr_eq_zero T S x (lapS f T) hTS]

/-! ## Influences and globalness -/

/-- The influence of a pair `(T, x)`: `I_{T,x}[f] = ‖D_{T,x}[f]‖₂²`. -/
def inflPair (T : Finset (Fin n)) (x : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ℂ) : ℝ :=
  mu (Dfun T x f)

/-- The influence of a set `T`: `I_T[f] = ‖L_T[f]‖₂²`. -/
def inflSet (T : Finset (Fin n)) (f : (Fin n → ZMod 2) → ℂ) : ℝ := mu (lapS f T)

/-- `(d, ε)`-globalness: every `d`-restriction has squared `L²` norm at most `ε`. -/
def Global (d : ℕ) (ε : ℝ) (f : (Fin n → ZMod 2) → ℂ) : Prop :=
  ∀ T : Finset (Fin n), T.card ≤ d → ∀ x : Fin n → ZMod 2, mu (restr T x f) ≤ ε

lemma lapS_empty (f : (Fin n → ZMod 2) → ℂ) : lapS f ∅ = f := by
  rw [lapS]
  rw [show (Finset.univ : Finset (Finset (Fin n))).filter (fun T => (∅ : Finset (Fin n)) ⊆ T)
      = Finset.univ from by ext T; simp]
  exact sum_efronStein f

lemma combine_empty (x z : Fin n → ZMod 2) :
    combine (∅ : Finset (Fin n)) x z = z := by
  funext i
  exact combine_apply_notMem ∅ x z (Finset.notMem_empty i)

lemma restr_empty (x : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ℂ) : restr ∅ x f = f := by
  funext z
  rw [restr_apply, combine_empty]

lemma Dfun_empty (x : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ℂ) : Dfun ∅ x f = f := by
  rw [Dfun_apply, lapS_empty, restr_empty]

/-- **Theorem 2.5 of arXiv:2209.04243** (`p = 2` case): the conditional hypercontractive
inequality at degree `d`. -/
theorem hyp (d : ℕ) (f : (Fin n → ZMod 2) → ℂ) (hf : Deg d f) :
    mu4 f ≤ (100 * d : ℝ) ^ d *
      ∑ S : Finset (Fin n), ((2 : ℝ) ^ n)⁻¹ * ∑ x, (inflPair S x f) ^ 2 := by
  have hmain := mu4_le_of_deg d f hf
  have h9 : (9 : ℝ) ^ d ≤ (100 * d : ℝ) ^ d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; norm_num
    · have h1 : (9 : ℝ) ≤ 100 * d := by
        have h2 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        nlinarith
      exact pow_le_pow_left₀ (by norm_num) h1 d
  have hterm : ∀ x : Fin n → ZMod 2, inflPair ∅ x f = mu f := by
    intro x; rw [inflPair, Dfun_empty]
  have hcard : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by simp
  have hsum : (mu f) ^ 2 ≤
      ∑ S : Finset (Fin n), ((2 : ℝ) ^ n)⁻¹ * ∑ x, (inflPair S x f) ^ 2 := by
    have hsingle : ((2 : ℝ) ^ n)⁻¹ * ∑ x, (inflPair ∅ x f) ^ 2
        ≤ ∑ S : Finset (Fin n), ((2 : ℝ) ^ n)⁻¹ * ∑ x, (inflPair S x f) ^ 2 :=
      Finset.single_le_sum (f := fun S : Finset (Fin n) => ((2 : ℝ) ^ n)⁻¹ * ∑ x, (inflPair S x f) ^ 2)
        (fun S _ => by positivity) (Finset.mem_univ (∅ : Finset (Fin n)))
    have heq : ((2 : ℝ) ^ n)⁻¹ * ∑ x, (inflPair ∅ x f) ^ 2 = (mu f) ^ 2 := by
      rw [Finset.sum_congr rfl (fun x _ => by rw [hterm x]), Finset.sum_const, Finset.card_univ,
        hcard, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)), one_mul]
    rwa [heq] at hsingle
  calc mu4 f ≤ (9 : ℝ) ^ d * (mu f) ^ 2 := hmain
    _ ≤ (100 * d : ℝ) ^ d * (mu f) ^ 2 := mul_le_mul_of_nonneg_right h9 (by positivity)
    _ ≤ (100 * d : ℝ) ^ d *
          ∑ S : Finset (Fin n), ((2 : ℝ) ^ n)⁻¹ * ∑ x, (inflPair S x f) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)


/-! ## The contraction property of `E_T`, and its interaction with restrictions -/

lemma extend_add (T : Finset (Fin n)) (y y' : T → ZMod 2) :
    extend T (y + y') = extend T y + extend T y' := by
  funext i
  by_cases hi : i ∈ T <;> simp [extend, hi]

lemma zmod2_add_add_self (a b c : ZMod 2) : a + (b + (a + c)) = b + c := by
  rw [show a + (b + (a + c)) = (a + a) + (b + c) from by ring, CharTwo.add_self_eq_zero,
    zero_add]

/-- `E_T f` is invariant under changing the `T`-coordinates of its argument. -/
lemma ES_add_extend (T : Finset (Fin n)) (f : (Fin n → ZMod 2) → ℂ) (z : Fin n → ZMod 2)
    (y' : T → ZMod 2) : ES T f (z + extend T y') = ES T f z := by
  rw [ES_apply, ES_apply]
  congr 1
  have h : (∑ y : T → ZMod 2, f (z + extend T y' + extend T y))
      = ∑ y : T → ZMod 2, f (z + extend T (y + y')) :=
    Finset.sum_congr rfl fun y _ => by
      congr 1
      rw [add_assoc, ← extend_add, add_comm y' y]
  rw [h]
  simpa using Equiv.sum_comp (Equiv.addRight y') (fun v => f (z + extend T v))

lemma norm_inv_two_pow (k : ℕ) : ‖((2 : ℂ) ^ k)⁻¹‖ = ((2 : ℝ) ^ k)⁻¹ := by
  rw [norm_inv, Complex.norm_pow, Complex.norm_ofNat]

lemma norm_inv_two_pow_sq (k : ℕ) : ‖((2 : ℂ) ^ k)⁻¹‖ ^ 2 = ((2 : ℝ) ^ k)⁻¹ ^ 2 := by
  rw [norm_inv_two_pow]

/-- `E_T` is an `L²`-contraction. -/
lemma mu_ES_le (T : Finset (Fin n)) (f : (Fin n → ZMod 2) → ℂ) : mu (ES T f) ≤ mu f := by
  have hcard : Fintype.card (T → ZMod 2) = 2 ^ T.card := by simp
  have hcardR : ((Fintype.card (T → ZMod 2) : ℝ)) = (2 : ℝ) ^ T.card := by
    rw [hcard]; push_cast; ring
  have h2T : (0 : ℝ) < (2 : ℝ) ^ T.card := by positivity
  -- step 1: pointwise Jensen
  have hJ : ∀ x : Fin n → ZMod 2,
      ‖((2 : ℂ) ^ T.card)⁻¹ * ∑ y : T → ZMod 2, f (x + extend T y)‖ ^ 2
        ≤ ((2 : ℝ) ^ T.card)⁻¹ * ∑ y : T → ZMod 2, ‖f (x + extend T y)‖ ^ 2 := by
    intro x
    have h1 : ‖∑ y : T → ZMod 2, f (x + extend T y)‖ ^ 2
        ≤ ((2 : ℝ) ^ T.card) * ∑ y : T → ZMod 2, ‖f (x + extend T y)‖ ^ 2 := by
      have hcardU : ((Finset.univ : Finset (T → ZMod 2)).card : ℝ) = (2 : ℝ) ^ T.card := by
        rw [Finset.card_univ, hcard]; push_cast; ring
      have h0 := Commons.Analysis.Complex.norm_sum_sq_le_card_mul (s := Finset.univ)
        (f := fun y : T → ZMod 2 => f (x + extend T y))
      rwa [hcardU] at h0
    calc ‖((2 : ℂ) ^ T.card)⁻¹ * ∑ y : T → ZMod 2, f (x + extend T y)‖ ^ 2
        = (((2 : ℝ) ^ T.card)⁻¹) ^ 2 * ‖∑ y : T → ZMod 2, f (x + extend T y)‖ ^ 2 := by
          rw [norm_mul, norm_inv_two_pow, mul_pow]
      _ ≤ (((2 : ℝ) ^ T.card)⁻¹) ^ 2 *
            ((2 : ℝ) ^ T.card * ∑ y, ‖f (x + extend T y)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((2 : ℝ) ^ T.card)⁻¹ * ∑ y, ‖f (x + extend T y)‖ ^ 2 := by
          field_simp
  -- step 2: sum over x, and reindex
  have hinner : ∀ y : T → ZMod 2,
      (∑ x : Fin n → ZMod 2, ((2 : ℝ) ^ T.card)⁻¹ * ‖f (x + extend T y)‖ ^ 2)
        = ((2 : ℝ) ^ T.card)⁻¹ * ∑ w : Fin n → ZMod 2, ‖f w‖ ^ 2 := by
    intro y
    rw [← Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp (Equiv.addRight (extend T y)) (fun w => ‖f w‖ ^ 2)
  have hsum : (∑ x : Fin n → ZMod 2, ((2 : ℝ) ^ T.card)⁻¹ *
        ∑ y : T → ZMod 2, ‖f (x + extend T y)‖ ^ 2) = ∑ w : Fin n → ZMod 2, ‖f w‖ ^ 2 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun y _ => hinner y)]
    rw [Finset.sum_const, Finset.card_univ, hcard]
    rw [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt h2T), one_mul]
  calc mu (ES T f) = ((2 : ℝ) ^ n)⁻¹ * ∑ x, ‖ES T f x‖ ^ 2 := rfl
    _ = ((2 : ℝ) ^ n)⁻¹ * ∑ x, ‖((2 : ℂ) ^ T.card)⁻¹ *
          ∑ y : T → ZMod 2, f (x + extend T y)‖ ^ 2 := by
        congr 1
    _ ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ x, ((2 : ℝ) ^ T.card)⁻¹ *
          ∑ y : T → ZMod 2, ‖f (x + extend T y)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hJ x) (by positivity)
    _ = ((2 : ℝ) ^ n)⁻¹ * ∑ w, ‖f w‖ ^ 2 := by rw [hsum]
    _ = mu f := rfl


/-! ## Laplacians as combinations of resamplings -/

/-- The restriction of a resampling is a resampling of a restriction. -/
lemma combine_sdiff_eq (T S : Finset (Fin n)) (hTS : T ⊆ S) (x z : Fin n → ZMod 2)
    (y : T → ZMod 2) :
    combine (S \ T) x (z + extend T y)
      = combine S x z + extend T (y + fun i : ↥T => x i + z i) := by
  funext i
  by_cases hiT : i ∈ T
  · have hiS : i ∈ S := hTS hiT
    have hiST : i ∉ S \ T := fun h => (Finset.mem_sdiff.mp h).2 hiT
    rw [combine_apply_notMem (S \ T) x (z + extend T y) hiST]
    simp only [Pi.add_apply]
    rw [combine_apply_mem S x z hiS]
    simp only [Pi.add_apply, extend_apply_mem T _ hiT]
    exact (add_comm (z i) (y ⟨i, hiT⟩)).trans
      (zmod2_add_add_self (x i) (y ⟨i, hiT⟩) (z i)).symm
  · by_cases hiS : i ∈ S
    · have hiST : i ∈ S \ T := Finset.mem_sdiff.mpr ⟨hiS, hiT⟩
      rw [combine_apply_mem (S \ T) x (z + extend T y) hiST]
      simp only [Pi.add_apply]
      rw [combine_apply_mem S x z hiS]
      simp only [extend_apply_notMem T _ hiT, add_zero]
    · have hiST : i ∉ S \ T := fun h => hiS (Finset.mem_sdiff.mp h).1
      rw [combine_apply_notMem (S \ T) x (z + extend T y) hiST]
      simp only [Pi.add_apply]
      rw [combine_apply_notMem S x z hiS]
      simp only [extend_apply_notMem T y hiT, extend_apply_notMem T _ hiT, add_zero]

/-- Restrictions commute with resamplings. -/
lemma restr_ES (T S : Finset (Fin n)) (hTS : T ⊆ S) (x : Fin n → ZMod 2)
    (f : (Fin n → ZMod 2) → ℂ) :
    restr S x (ES T f) = ES T (restr (S \ T) x f) := by
  funext z
  rw [restr_apply, ES_apply, ES_apply]
  simp only [restr_apply]
  congr 1
  have h : (∑ y : T → ZMod 2, f (combine (S \ T) x (z + extend T y)))
      = ∑ y : T → ZMod 2,
          f (combine S x z + extend T (y + fun i : ↥T => x i + z i)) :=
    Finset.sum_congr rfl fun y _ => by rw [combine_sdiff_eq T S hTS x z y]
  rw [h]
  exact (Equiv.sum_comp (Equiv.addRight (fun i : ↥T => x i + z i))
    (fun v => f (combine S x z + extend T v))).symm

lemma inter_eq_empty_iff_subset_compl (S R : Finset (Fin n)) :
    S ∩ R = ∅ ↔ S ⊆ Rᶜ := by
  rw [← Finset.disjoint_iff_inter_eq_empty, Finset.subset_compl_iff_disjoint_right]

/-- The alternating sum over the subsets of a set. -/
lemma sum_powerset_alt_eq (A : Finset (Fin n)) :
    (∑ T ∈ A.powerset, (-1 : ℂ) ^ T.card) = if A = ∅ then 1 else 0 :=
  Commons.Analysis.Walsh.sum_powerset_neg_one_pow_complex A

/-- **The Laplacians in terms of the resampling operators** (inclusion--exclusion):
`L_T = ∑_{S ⊆ T} (-1)^{|S|} E_S`. -/
theorem lapS_eq_sum_ES (T : Finset (Fin n)) (f : (Fin n → ZMod 2) → ℂ) :
    lapS f T = ∑ S ∈ T.powerset, ((-1 : ℂ) ^ S.card) • ES S f := by
  apply eq_of_walshFourier_eq
  intro R
  rw [walshFourier_lapS, walshFourier_sum]
  rw [Finset.sum_congr rfl (fun S _ => by rw [walshFourier_smul, walshFourier_ES])]
  refine Eq.symm ?_
  rw [show (∑ S ∈ T.powerset, (-1 : ℂ) ^ S.card *
        (if R ∩ S = ∅ then walshFourier f R else 0))
      = ∑ S ∈ T.powerset, (if S ∩ R = ∅ then (-1 : ℂ) ^ S.card * walshFourier f R else 0) from
    Finset.sum_congr rfl fun S _ => by
      rw [Finset.inter_comm]
      by_cases h : S ∩ R = ∅ <;> simp [h]]
  rw [← Finset.sum_filter]
  rw [Finset.filter_congr (fun S _ => inter_eq_empty_iff_subset_compl S R)]
  rw [Commons.Combinatorics.Finset.sum_powerset_filter_subset T Rᶜ
    (fun S => (-1 : ℂ) ^ S.card * walshFourier f R)]
  rw [← Finset.sum_mul]
  rw [sum_powerset_alt_eq (T ∩ Rᶜ)]
  have hcond : (T ∩ Rᶜ = ∅) ↔ (T ⊆ R) := by
    rw [inter_eq_empty_iff_subset_compl, compl_compl]
  by_cases h : T ⊆ R
  · rw [if_pos h, if_pos (hcond.mpr h), one_mul]
  · rw [if_neg h, if_neg (fun hc => h (hcond.mp hc)), zero_mul]


lemma mu_sum_le_card_mul {ι : Type*} (s : Finset ι) (g : ι → (Fin n → ZMod 2) → ℂ) :
    mu (∑ i ∈ s, g i) ≤ (s.card : ℝ) * ∑ i ∈ s, mu (g i) := by
  have hpt : ∀ z : Fin n → ZMod 2,
      ‖(∑ i ∈ s, g i) z‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖g i z‖ ^ 2 := by
    intro z
    have h0 := Commons.Analysis.Complex.norm_sum_sq_le_card_mul s (fun i => g i z)
    rw [Finset.sum_apply]
    exact h0
  calc mu (∑ i ∈ s, g i) = ((2 : ℝ) ^ n)⁻¹ * ∑ z, ‖(∑ i ∈ s, g i) z‖ ^ 2 := rfl
    _ ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ z, ((s.card : ℝ) * ∑ i ∈ s, ‖g i z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => hpt z) (by positivity)
    _ = (s.card : ℝ) * ∑ i ∈ s, mu (g i) := by
        simp only [mu]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun z _ => by ring

/-- **Lemma 2.11 of arXiv:2209.04243**: if all restrictions of `f` to subsets of `S` have small
squared `L²` norm, then the influence of `(S, x)` is small. -/
theorem inflPair_le_of_global (S : Finset (Fin n)) (x : Fin n → ZMod 2)
    (f : (Fin n → ZMod 2) → ℂ) {ε : ℝ}
    (h : ∀ T : Finset (Fin n), T ⊆ S → mu (restr T x f) ≤ ε) :
    inflPair S x f ≤ (2 : ℝ) ^ (2 * S.card) * ε := by
  rw [inflPair, Dfun_apply, lapS_eq_sum_ES]
  have h1 : restr S x (∑ T ∈ S.powerset, ((-1 : ℂ) ^ T.card) • ES T f)
      = ∑ T ∈ S.powerset, ((-1 : ℂ) ^ T.card) • restr S x (ES T f) := by
    rw [restr_sum]
    exact Finset.sum_congr rfl fun T _ => restr_smul S x _ _
  rw [h1]
  have hcardR : ((S.powerset.card : ℕ) : ℝ) = (2 : ℝ) ^ S.card := by
    rw [Finset.card_powerset]; push_cast; ring
  calc mu (∑ T ∈ S.powerset, ((-1 : ℂ) ^ T.card) • restr S x (ES T f))
      ≤ (S.powerset.card : ℝ) * ∑ T ∈ S.powerset, mu (((-1 : ℂ) ^ T.card) • restr S x (ES T f)) :=
        mu_sum_le_card_mul _ _
    _ = (S.powerset.card : ℝ) * ∑ T ∈ S.powerset, mu (restr S x (ES T f)) := by
        congr 1
        exact Finset.sum_congr rfl fun T _ => by
          rw [mu_smul]
          norm_num
    _ ≤ (S.powerset.card : ℝ) * ∑ T ∈ S.powerset, ε := by
        gcongr with T hT
        rw [restr_ES T S (Finset.mem_powerset.mp hT) x f]
        exact le_trans (mu_ES_le T _) (h (S \ T) Finset.sdiff_subset)
    _ = (2 : ℝ) ^ (2 * S.card) * ε := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
        rw [show (2 : ℝ) ^ (2 * S.card) = (2 : ℝ) ^ S.card * (2 : ℝ) ^ S.card by
          rw [← pow_add]; ring]
        push_cast
        ring


/-! ## The explicit form of the derivative -/

lemma efronCoeff_chi (U R : Finset (Fin n)) :
    efronCoeff (chi U) R = if R = U then 1 else 0 := by
  rw [efronCoeff, walshFourier_chi]
  by_cases h : R = U
  · rw [if_pos h, if_pos h, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))]
  · rw [if_neg h, if_neg h, mul_zero]

lemma efronCoeff_efronStein (f : (Fin n → ZMod 2) → ℂ) (T U : Finset (Fin n)) :
    efronCoeff (efronStein f T) U = if U = T then efronCoeff f T else 0 := by
  have h : efronStein f T = efronCoeff f T • chi T := efronStein_eq_smul f T
  rw [h, efronCoeff_smul, efronCoeff_chi]
  by_cases hUT : U = T
  · rw [if_pos hUT, if_pos hUT, mul_one]
  · rw [if_neg hUT, if_neg hUT, mul_zero]

lemma efronStein_efronStein (f : (Fin n → ZMod 2) → ℂ) (T U : Finset (Fin n)) :
    efronStein (efronStein f T) U = if U = T then efronStein f T else 0 := by
  have h : efronStein f T = efronCoeff f T • chi T := efronStein_eq_smul f T
  rw [h, efronStein_smul, efronStein_chi]
  by_cases hUT : U = T
  · rw [if_pos hUT, if_pos hUT]
  · rw [if_neg hUT, if_neg hUT, smul_zero]

/-- The restriction of an Efron--Stein component above `S`. -/
lemma restr_efronStein (S T : Finset (Fin n)) (hST : S ⊆ T) (x : Fin n → ZMod 2)
    (f : (Fin n → ZMod 2) → ℂ) :
    restr S x (efronStein f T) = (efronCoeff f T * chi S x) • chi (T \ S) := by
  have hinter : T ∩ S = S := by
    ext i; simp only [Finset.mem_inter]
    exact ⟨fun h => h.2, fun h => ⟨hST h, h⟩⟩
  rw [efronStein_eq_smul, restr_smul, restr_chi, hinter]
  rw [show (fun z => chi S x * chi (T \ S) z) = chi S x • chi (T \ S) from rfl]
  rw [smul_smul]

/-- The derivative is a sum of multiples of the distinct characters `chi (T \ S)`, `T ⊇ S`. -/
lemma Dfun_eq_sum (S : Finset (Fin n)) (x : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ℂ) :
    Dfun S x f
      = ∑ T ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun T => S ⊆ T),
          (efronCoeff f T * chi S x) • chi (T \ S) := by
  rw [Dfun_apply, lapS, restr_sum]
  exact Finset.sum_congr rfl fun T hT => restr_efronStein S T (Finset.mem_filter.mp hT).2 x f

lemma sdiff_inj_of_subset {S T U : Finset (Fin n)} (hT : S ⊆ T) (hU : S ⊆ U)
    (h : T \ S = U \ S) : T = U := by
  rw [← Finset.union_sdiff_of_subset hT, ← Finset.union_sdiff_of_subset hU, h]



/-! ## Parseval for `mu`, and Lemma 2.10 -/

lemma hcard_univ : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by simp

lemma norm_chi (R : Finset (Fin n)) (x : Fin n → ZMod 2) : ‖chi R x‖ = 1 := by
  rw [chi, norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rcases Commons.Analysis.Inequalities.zmod2_cases (x i) with h | h
  · rw [h, ZMod.stdAddChar.map_zero_eq_one]; norm_num
  · rw [h, stdAddChar_one]; norm_num

lemma mu_chi (R : Finset (Fin n)) : mu (chi R) = 1 := by
  rw [mu]
  rw [show (∑ x : Fin n → ZMod 2, ‖chi R x‖ ^ 2) = ∑ _x : Fin n → ZMod 2, (1 : ℝ) from
    Finset.sum_congr rfl fun x _ => by rw [norm_chi R x]; norm_num]
  rw [Finset.sum_const, Finset.card_univ, hcard_univ, nsmul_eq_mul]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]

/-- `mu (c • chi R) = ‖c‖²`. -/
lemma mu_smul_chi (c : ℂ) (R : Finset (Fin n)) : mu (c • chi R) = ‖c‖ ^ 2 := by
  rw [mu_smul, mu_chi, mul_one]

end

end Submission.Hypercube
