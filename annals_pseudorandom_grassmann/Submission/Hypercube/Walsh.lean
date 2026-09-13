import Mathlib

/-!
# Walsh--Fourier analysis on the cube, indexed by subsets

For the cube `𝔽₂ⁿ = (Fin n → ZMod 2)` we index the characters by *subsets*
`S : Finset (Fin n)` (rather than by vectors), which is the natural indexing for the
Efron--Stein decomposition and for the paper's `f^{=S}`, `f^{≤d}` (arXiv:2209.04243, §2):

  `chi S x = ∏ i ∈ S, ω^{x i}`  (so `chi S x = (-1)^{∑_{i∈S} x i}`).

This file proves the basic algebra of these characters (multiplicativity, that they are
`±1`-valued, the product rule `chi S · chi T = chi (S ∆ T)`), their **orthogonality**

  `∑_x chi S x * chi T x = if S = T then 2^n else 0`

and its dual form `∑_S chi S z = if z = 0 then 2^n else 0`, and the resulting **Fourier
inversion** and **Parseval** identities for the Walsh transform `ŵ f S = ∑_x f x * chi S x`.
-/

open Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Hypercube

noncomputable section

/-! ## The Walsh characters -/

/-- The Walsh character of the cube associated with a set of coordinates `S`. -/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ZMod 2) : ℂ :=
  ∏ i ∈ S, ZMod.stdAddChar (x i)

lemma chi_empty {n : ℕ} (x : Fin n → ZMod 2) : chi (∅ : Finset (Fin n)) x = 1 := by
  simp [chi]

lemma chi_zero {n : ℕ} (S : Finset (Fin n)) : chi S (0 : Fin n → ZMod 2) = 1 := by
  simp only [chi, Pi.zero_apply, AddChar.map_zero_eq_one, Finset.prod_const_one]

lemma chi_add {n : ℕ} (S : Finset (Fin n)) (x y : Fin n → ZMod 2) :
    chi S (x + y) = chi S x * chi S y := by
  simp only [chi, Pi.add_apply, AddChar.map_add_eq_mul]
  rw [Finset.prod_mul_distrib]

/-- The Walsh characters take the values `±1`; in particular they are self-inverse. -/
lemma chi_self {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    chi S x * chi S x = 1 := by
  rw [← chi_add]
  have hx : x + x = (0 : Fin n → ZMod 2) := funext fun i => CharTwo.add_self_eq_zero (x i)
  rw [hx, chi_zero]

lemma chi_inv {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ZMod 2) : (chi S x)⁻¹ = chi S x :=
  inv_eq_of_mul_eq_one_right (chi_self S x)

/-- `chi S · chi T = chi (S ∆ T)`, where `S ∆ T = (S \ T) ∪ (T \ S)` is the symmetric
difference. -/
lemma chi_symmDiff {n : ℕ} (S T : Finset (Fin n)) (x : Fin n → ZMod 2) :
    chi S x * chi T x = chi ((S \ T) ∪ (T \ S)) x := by
  simp only [chi]
  have h1 : (∏ i ∈ S, ZMod.stdAddChar (x i)) =
      (∏ i ∈ S ∩ T, ZMod.stdAddChar (x i)) * (∏ i ∈ S \ T, ZMod.stdAddChar (x i)) :=
    (Finset.prod_inter_mul_prod_sdiff S T _).symm
  have h2 : (∏ i ∈ T, ZMod.stdAddChar (x i)) =
      (∏ i ∈ S ∩ T, ZMod.stdAddChar (x i)) * (∏ i ∈ T \ S, ZMod.stdAddChar (x i)) := by
    rw [Finset.inter_comm]
    exact (Finset.prod_inter_mul_prod_sdiff T S _).symm
  have hsq : (∏ i ∈ S ∩ T, ZMod.stdAddChar (x i)) *
      (∏ i ∈ S ∩ T, ZMod.stdAddChar (x i)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← AddChar.map_add_eq_mul, CharTwo.add_self_eq_zero, AddChar.map_zero_eq_one]
  rw [h1, h2, Finset.prod_union (show Disjoint (S \ T) (T \ S) from by
    rw [Finset.disjoint_left]
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1)]
  linear_combination ((∏ i ∈ S \ T, ZMod.stdAddChar (x i)) *
    (∏ i ∈ T \ S, ZMod.stdAddChar (x i))) * hsq

/-! ## Orthogonality -/

/-- `∑_{a ∈ 𝔽₂} ω^a = 0`. -/
lemma sum_stdAddChar_zmod_two : (∑ a : ZMod 2, ZMod.stdAddChar a) = 0 := by
  have h := AddChar.sum_mulShift (1 : ZMod 2) (ZMod.isPrimitive_stdAddChar 2)
  simpa using h

/-- Fubini for a product of sums over a dependent product type. -/
lemma sum_prod_pi' {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] (f : ∀ i, κ i → ℂ) :
    (∑ g : (∀ i, κ i), ∏ i, f i (g i)) = ∏ i, ∑ a, f i a := by
  classical
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (κ i))) f]
  simp

/-- **Primal orthogonality**: `∑_x chi S x` vanishes unless `S = ∅`. -/
theorem sum_chi {n : ℕ} (S : Finset (Fin n)) :
    (∑ x : Fin n → ZMod 2, chi S x) = if S = ∅ then (2 : ℂ) ^ n else 0 := by
  have h : ∀ x : Fin n → ZMod 2,
      chi S x = ∏ i : Fin n, (if i ∈ S then ZMod.stdAddChar (x i) else 1) := by
    intro x
    rw [chi, Finset.prod_ite_mem_eq S (fun i => ZMod.stdAddChar (x i))]
  rw [Finset.sum_congr rfl (fun x _ => h x),
    sum_prod_pi' (fun i (a : ZMod 2) => if i ∈ S then ZMod.stdAddChar a else 1)]
  have hstep : ∀ i : Fin n, (∑ a : ZMod 2, (if i ∈ S then ZMod.stdAddChar a else (1 : ℂ))) =
      (if i ∈ S then (0 : ℂ) else 2) := by
    intro i
    by_cases hi : i ∈ S
    · have h1 : (∑ a : ZMod 2, (if i ∈ S then ZMod.stdAddChar a else (1 : ℂ))) =
          ∑ a : ZMod 2, ZMod.stdAddChar a :=
        Finset.sum_congr rfl fun a _ => by simp [hi]
      rw [h1, sum_stdAddChar_zmod_two, if_pos hi]
    · have h1 : (∑ a : ZMod 2, (if i ∈ S then ZMod.stdAddChar a else (1 : ℂ))) =
          ∑ _a : ZMod 2, (1 : ℂ) :=
        Finset.sum_congr rfl fun a _ => by simp [hi]
      rw [h1, if_neg hi]
      simp [Finset.sum_const]
  rw [Finset.prod_congr rfl (fun i _ => hstep i)]
  by_cases hS : S = ∅
  · subst hS; simp
  · rw [if_neg hS]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_pos hi])

/-- **Orthogonality of the Walsh characters.** -/
theorem chi_orthogonal {n : ℕ} (S T : Finset (Fin n)) :
    (∑ x : Fin n → ZMod 2, chi S x * chi T x) = if S = T then (2 : ℂ) ^ n else 0 := by
  rw [Finset.sum_congr rfl (fun x _ => chi_symmDiff S T x), sum_chi]
  by_cases h : S = T
  · subst h
    have hempty : (S \ S) ∪ (S \ S) = (∅ : Finset (Fin n)) := by ext i; simp
    rw [hempty, if_pos rfl, if_pos rfl]
  · have hne : (S \ T) ∪ (T \ S) ≠ (∅ : Finset (Fin n)) := by
      intro hh
      have hmem : ∀ i, ¬ (i ∈ (S \ T) ∪ (T \ S)) := fun i => by
        rw [hh]; simp
      exact h (Finset.ext fun i => by
        constructor
        · intro hi
          by_contra hni
          exact hmem i (by simp [hi, hni])
        · intro hi
          by_contra hni
          exact hmem i (by simp [hi, hni]))
    rw [if_neg hne, if_neg h]

/-- **Dual orthogonality**: summing over all characters. -/
theorem sum_chi_index {n : ℕ} (z : Fin n → ZMod 2) :
    (∑ S : Finset (Fin n), chi S z) = if z = 0 then (2 : ℂ) ^ n else 0 := by
  have hexp : (∑ S : Finset (Fin n), chi S z) =
      ∏ i : Fin n, (ZMod.stdAddChar (z i) + 1) := by
    rw [show (∑ S : Finset (Fin n), chi S z) =
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, chi S z from by
      rw [Finset.powerset_univ]]
    rw [Finset.prod_add (fun i : Fin n => ZMod.stdAddChar (z i)) (fun _ => (1 : ℂ)) Finset.univ]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [chi, Finset.prod_const_one, mul_one]
  rw [hexp]
  by_cases hz : z = 0
  · subst hz
    simp only [Pi.zero_apply, AddChar.map_zero_eq_one, Finset.prod_const]
    norm_num
  · rw [if_neg hz]
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hz (funext h)
    have hs : ZMod.stdAddChar (z i) = -1 := by
      have h1 : ZMod.stdAddChar (z i) ≠ 1 := fun h =>
        hi (ZMod.injective_stdAddChar (by rw [h, AddChar.map_zero_eq_one]))
      have h2 : ZMod.stdAddChar (z i) * ZMod.stdAddChar (z i) = 1 := by
        rw [← AddChar.map_add_eq_mul, CharTwo.add_self_eq_zero, AddChar.map_zero_eq_one]
      have h3 : (ZMod.stdAddChar (z i) - 1) * (ZMod.stdAddChar (z i) + 1) = 0 := by
        calc (ZMod.stdAddChar (z i) - 1) * (ZMod.stdAddChar (z i) + 1)
            = ZMod.stdAddChar (z i) ^ 2 - 1 := by ring
          _ = 1 - 1 := by rw [pow_two, h2]
          _ = 0 := by ring
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd (sub_eq_zero.mp h4) h1
      · exact eq_neg_of_add_eq_zero_left h4
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [hs]; ring

/-! ## The Walsh transform -/

/-- The Walsh--Fourier coefficient of `f` at the character indexed by `S`. -/
def walshFourier {n : ℕ} (f : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) : ℂ :=
  ∑ x : Fin n → ZMod 2, f x * chi S x

lemma walshFourier_add {n : ℕ} (f g : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    walshFourier (f + g) S = walshFourier f S + walshFourier g S := by
  simp only [walshFourier, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma walshFourier_smul {n : ℕ} (c : ℂ) (f : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    walshFourier (c • f) S = c * walshFourier f S := by
  rw [walshFourier, walshFourier, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- **Fourier inversion** for the Walsh transform. -/
theorem walsh_inversion {n : ℕ} (f : (Fin n → ZMod 2) → ℂ) (y : Fin n → ZMod 2) :
    (∑ S : Finset (Fin n), walshFourier f S * chi S y) = (2 : ℂ) ^ n * f y := by
  classical
  have hred : ∀ S : Finset (Fin n),
      (∑ x : Fin n → ZMod 2, f x * chi S x) * chi S y =
        ∑ x : Fin n → ZMod 2, f x * chi S x * chi S y := fun S => Finset.sum_mul _ _ _
  simp only [walshFourier]
  rw [Finset.sum_congr rfl (fun S _ => hred S), Finset.sum_comm]
  have hsum : ∀ x : Fin n → ZMod 2,
      (∑ S : Finset (Fin n), chi S x * chi S y) =
        if x + y = (0 : Fin n → ZMod 2) then (2 : ℂ) ^ n else 0 := by
    intro x
    rw [← Finset.sum_congr rfl (fun S _ => chi_add S x y), sum_chi_index]
  have hinner : ∀ x : Fin n → ZMod 2,
      (∑ S : Finset (Fin n), f x * chi S x * chi S y) =
        if x = y then (2 : ℂ) ^ n * f y else 0 := by
    intro x
    rw [Finset.sum_congr rfl (fun S _ => by rw [mul_assoc]), ← Finset.mul_sum, hsum]
    by_cases hxy : x = y
    · subst hxy
      have hxx : x + x = (0 : Fin n → ZMod 2) := funext fun i => CharTwo.add_self_eq_zero (x i)
      rw [if_pos hxx, if_pos rfl]; ring
    · have hyy : y + y = (0 : Fin n → ZMod 2) :=
        funext fun i => CharTwo.add_self_eq_zero (y i)
      have hne : x + y ≠ (0 : Fin n → ZMod 2) := by
        intro hh
        apply hxy
        calc x = x + (y + y) := by rw [hyy, add_zero]
          _ = (x + y) + y := by rw [add_assoc]
          _ = 0 + y := by rw [hh]
          _ = y := zero_add y
      rw [if_neg hne, if_neg hxy]; ring
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  rw [Finset.sum_eq_single y (fun x _ hx => by rw [if_neg hx])
    (fun h => absurd (Finset.mem_univ y) h), if_pos rfl]

/-- **Parseval's identity** for the Walsh transform. -/
theorem walsh_parseval {n : ℕ} (f g : (Fin n → ZMod 2) → ℂ) :
    (∑ S : Finset (Fin n), walshFourier f S * walshFourier g S) =
      (2 : ℂ) ^ n * ∑ x : Fin n → ZMod 2, f x * g x := by
  classical
  have key : ∀ S : Finset (Fin n), walshFourier f S * walshFourier g S =
      ∑ x : Fin n → ZMod 2, ∑ y : Fin n → ZMod 2, f x * g y * chi S (x + y) := by
    intro S
    simp only [walshFourier]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [chi_add]; ring
  calc (∑ S : Finset (Fin n), walshFourier f S * walshFourier g S)
      = ∑ S, ∑ x : Fin n → ZMod 2, ∑ y : Fin n → ZMod 2,
          f x * g y * chi S (x + y) := Finset.sum_congr rfl fun S _ => key S
    _ = ∑ x : Fin n → ZMod 2, ∑ y : Fin n → ZMod 2,
          ∑ S : Finset (Fin n), f x * g y * chi S (x + y) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x : Fin n → ZMod 2, ∑ y : Fin n → ZMod 2,
          f x * g y * (∑ S : Finset (Fin n), chi S (x + y)) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ x : Fin n → ZMod 2, ∑ y : Fin n → ZMod 2,
          f x * g y * (if x + y = (0 : Fin n → ZMod 2) then (2 : ℂ) ^ n else 0) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [sum_chi_index]
    _ = (2 : ℂ) ^ n * ∑ x : Fin n → ZMod 2, f x * g x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hstep : ∀ y : Fin n → ZMod 2,
            f x * g y * (if x + y = 0 then (2 : ℂ) ^ n else 0) =
              if y = x then (2 : ℂ) ^ n * (f x * g x) else 0 := by
          intro y
          by_cases hy : y = x
          · rw [hy]
            have hxx : x + x = (0 : Fin n → ZMod 2) :=
              funext fun i => CharTwo.add_self_eq_zero (x i)
            rw [if_pos hxx, if_pos rfl]; ring
          · have hyy : y + y = (0 : Fin n → ZMod 2) :=
              funext fun i => CharTwo.add_self_eq_zero (y i)
            have hxy : x + y ≠ (0 : Fin n → ZMod 2) := by
              intro hh
              have hxeq : x = y := by
                calc x = x + (y + y) := by rw [hyy, add_zero]
                  _ = (x + y) + y := by rw [add_assoc]
                  _ = 0 + y := by rw [hh]
                  _ = y := zero_add y
              exact hy hxeq.symm
            rw [if_neg hxy, if_neg hy]; ring
        rw [Finset.sum_congr rfl (fun y _ => hstep y)]
        rw [Finset.sum_eq_single x (fun y _ hy => by rw [if_neg hy])
          (fun h => absurd (Finset.mem_univ x) h), if_pos rfl]

/-! ## The Efron--Stein components and the Laplacians

For a function `f` on the cube, the **Efron--Stein component** at `S` is
`f^{=S} = 2^{-n} ŵ f S · chi S`, the orthogonal projection onto the span of the character
`chi S`.  Summing over `S` recovers `f` (Fourier inversion), different components are
orthogonal, and the **Laplacian** `L_S[f] = ∑_{T ⊇ S} f^{=T}` has its Fourier coefficients
cut off by `S ⊆ T`.
-/

/-- The Efron--Stein component of `f` at the coordinate set `S`. -/
def efronStein {n : ℕ} (f : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    (Fin n → ZMod 2) → ℂ :=
  fun x => ((2 : ℂ) ^ n)⁻¹ * (walshFourier f S * chi S x)

lemma efronStein_apply {n : ℕ} (f : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n))
    (x : Fin n → ZMod 2) :
    efronStein f S x = ((2 : ℂ) ^ n)⁻¹ * (walshFourier f S * chi S x) := rfl

/-- The Walsh transform of an Efron--Stein component. -/
theorem walshFourier_efronStein {n : ℕ} (f : (Fin n → ZMod 2) → ℂ)
    (S T : Finset (Fin n)) :
    walshFourier (efronStein f S) T = if S = T then walshFourier f S else 0 := by
  rw [walshFourier]
  have h : ∀ x : Fin n → ZMod 2,
      efronStein f S x * chi T x =
        ((2 : ℂ) ^ n)⁻¹ * walshFourier f S * (chi S x * chi T x) := by
    intro x; rw [efronStein_apply]; ring
  rw [Finset.sum_congr rfl (fun x _ => h x), ← Finset.mul_sum, chi_orthogonal]
  have hc : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  by_cases hST : S = T
  · rw [if_pos hST, if_pos hST, mul_comm ((2 : ℂ) ^ n)⁻¹ (walshFourier f S),
      mul_assoc, inv_mul_cancel₀ hc, mul_one]
  · rw [if_neg hST, if_neg hST, mul_zero]

/-- **Fourier inversion, component by component**: `f = ∑_S f^{=S}`. -/
theorem sum_efronStein {n : ℕ} (f : (Fin n → ZMod 2) → ℂ) :
    (∑ S : Finset (Fin n), efronStein f S) = f := by
  funext y
  rw [Finset.sum_apply]
  have h : ∀ S : Finset (Fin n),
      efronStein f S y = ((2 : ℂ) ^ n)⁻¹ * (walshFourier f S * chi S y) :=
    fun S => efronStein_apply f S y
  rw [Finset.sum_congr rfl (fun S _ => h S), ← Finset.mul_sum, walsh_inversion,
    ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)), one_mul]

/-- Different Efron--Stein components are orthogonal. -/
theorem efronStein_orthogonal {n : ℕ} (f g : (Fin n → ZMod 2) → ℂ)
    {S T : Finset (Fin n)} (hST : S ≠ T) :
    (∑ x : Fin n → ZMod 2, efronStein f S x * efronStein g T x) = 0 := by
  have h : ∀ x : Fin n → ZMod 2,
      efronStein f S x * efronStein g T x =
        (((2 : ℂ) ^ n)⁻¹ * walshFourier f S) * (((2 : ℂ) ^ n)⁻¹ * walshFourier g T) *
          (chi S x * chi T x) := by
    intro x; rw [efronStein_apply, efronStein_apply]; ring
  rw [Finset.sum_congr rfl (fun x _ => h x), ← Finset.mul_sum, chi_orthogonal, if_neg hST]
  ring

/-- The Laplacian `L_S`: it keeps the Efron--Stein components of all `T ⊇ S`. -/
def lapS {n : ℕ} (f : (Fin n → ZMod 2) → ℂ) (S : Finset (Fin n)) :
    (Fin n → ZMod 2) → ℂ :=
  ∑ T ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun T => S ⊆ T), efronStein f T

/-- The Walsh transform of the Laplacian `L_S`. -/
theorem walshFourier_lapS {n : ℕ} (f : (Fin n → ZMod 2) → ℂ) (S T : Finset (Fin n)) :
    walshFourier (lapS f S) T = if S ⊆ T then walshFourier f T else 0 := by
  rw [lapS, walshFourier]
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun U _ => Finset.sum_mul _ _ _), Finset.sum_comm]
  have hinner : ∀ U : Finset (Fin n),
      (∑ x : Fin n → ZMod 2, efronStein f U x * chi T x) =
        if U = T then walshFourier f U else 0 := by
    intro U
    have h2 : (∑ x : Fin n → ZMod 2, efronStein f U x * chi T x) =
        walshFourier (efronStein f U) T := rfl
    rw [h2, walshFourier_efronStein]
  rw [Finset.sum_congr rfl (fun U _ => hinner U), Finset.sum_ite_eq']
  simp [Finset.mem_filter]

end

end Submission.Hypercube
