import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.Defs
import Submission.Work.HP.SlabDefs
import Submission.Work.HP.SlabMono

/-!
# Splitting `∂_k f_b(y)` along the special monomials `x_j^{d-1}x_i`

The coefficient vector `b : Mon d n → ℝ` is split as `b = zeroS d n hd j b` plus the part of `b`
supported on `Sset d n hd j`, which is exactly the range of `i ↦ smon d n hd j i`.

Since `∂_k (y_j^{d-1} y_i) = δ_{i,k} y_j^{d-1}` for `k ≠ j`, while `∂_j(y_j^d) = d y_j^{d-1}` and
`∂_j(y_j^{d-1}y_i) = (d-1)y_j^{d-2}y_i` for `i ≠ j`, the contribution of the special part is an
explicit sum over `i`, which is what `gradF_decomp` records.
-/

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.HP.GradDecomp

/-! ## Derivatives of the special monomials -/

/-- `∂_i (x_i^d) = d x_i^{d-1}`. -/
theorem gradKer_smon_self_self (d n : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    gradKer d n x i (smon d n hd i i) = (d : ℝ) * x i ^ (d - 1) := by
  have hexp : ((smon d n hd i i).1 i : ℕ) = d := by
    rw [smon_self_exp, if_pos rfl]
  have hprod : (∏ l ∈ Finset.univ.erase i, x l ^ (((smon d n hd i i).1 l : ℕ))) = 1 := by
    apply Finset.prod_eq_one
    intro l hl
    rw [smon_self_exp, if_neg (Finset.mem_erase.mp hl).1, pow_zero]
  simp only [gradKer]
  rw [hexp, hprod]
  ring

/-- `∂_i (x_i^{d-1} x_j) = (d-1) x_i^{d-2} x_j` for `j ≠ i`. -/
theorem gradKer_smon_self_other (d n : ℕ) (hd : 1 ≤ d) (i j : Fin (n + 1)) (hji : j ≠ i)
    (x : Fin (n + 1) → ℝ) :
    gradKer d n x i (smon d n hd i j) = ((d : ℝ) - 1) * x i ^ (d - 2) * x j := by
  have hexp : ((smon d n hd i j).1 i : ℕ) = d - 1 := by
    rw [smon_ne_exp d n hd i j i hji, if_pos rfl, if_neg (Ne.symm hji), add_zero]
  have hprod : (∏ l ∈ Finset.univ.erase i, x l ^ (((smon d n hd i j).1 l : ℕ))) = x j := by
    rw [Finset.prod_eq_single j]
    · rw [smon_ne_exp d n hd i j j hji, if_neg hji, if_pos rfl, Nat.zero_add, pow_one]
    · intro b hb hbj
      rw [smon_ne_exp d n hd i j b hji, if_neg (Finset.mem_erase.mp hb).1, if_neg hbj,
        add_zero, pow_zero]
    · intro h
      exact absurd (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) h
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd]
    norm_num
  have hexp2 : d - 1 - 1 = d - 2 := by omega
  simp only [gradKer]
  rw [hexp, hprod, hcast, hexp2]

/-- The derivative in a direction `k ≠ j` of `x_j^{d-1}x_i` is `δ_{i,k} y_j^{d-1}`. -/
theorem gradKer_smon_ne_direction (d n : ℕ) (hd : 1 ≤ d) (j k : Fin (n + 1)) (hkj : k ≠ j)
    (y : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    gradKer d n y k (smon d n hd j i) = if i = k then y j ^ (d - 1) else 0 := by
  by_cases hik : i = k
  · rw [hik]
    rw [if_pos rfl]
    exact gradKer_smon_eq d n hd j k hkj y
  · rw [if_neg hik]
    by_cases hij : i = j
    · rw [hij]
      exact gradKer_smon_self d n hd j k hkj y
    · exact gradKer_smon_ne d n hd j k i hkj hik y

/-- The derivative in the direction `j` of the special monomials `smon d n hd j i`. -/
theorem gradKer_smon_pin_direction (d n : ℕ) (hd : 1 ≤ d) (j : Fin (n + 1))
    (y : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    gradKer d n y j (smon d n hd j i)
      = if i = j then (d : ℝ) * y j ^ (d - 1) else ((d : ℝ) - 1) * y j ^ (d - 2) * y i := by
  by_cases hij : i = j
  · rw [hij]
    rw [if_pos rfl]
    exact gradKer_smon_self_self d n hd j y
  · rw [if_neg hij]
    exact gradKer_smon_self_other d n hd j i hij y

/-! ## Elementary finite-sum manipulations -/

/-- Reindexing a sum over the image of `smon d n hd j`. -/
theorem sum_image_smon (d n : ℕ) (hd : 1 ≤ d) (j : Fin (n + 1)) (F : Mon d n → ℝ) :
    (∑ m ∈ Finset.univ.image (smon d n hd j), F m) = ∑ i : Fin (n + 1), F (smon d n hd j i) := by
  rw [Finset.sum_image (fun a ha b hb hab => smon_injective d n hd j hab)]

/-- A sum of a function supported at a single point. -/
theorem sum_univ_ite_eq {n : ℕ} (k : Fin (n + 1)) (g : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), (if i = k then g i else 0)) = g k := by
  have h1 : (∑ i : Fin (n + 1), (if i = k then g i else 0))
      = ∑ i : Fin (n + 1), (if i ∈ ({k} : Finset (Fin (n + 1))) then g i else 0) :=
    Finset.sum_congr rfl (fun i _ => by
      by_cases hik : i = k
      · rw [if_pos hik, if_pos (by simpa using hik)]
      · rw [if_neg hik, if_neg (by simpa using hik)])
  rw [h1, Finset.sum_ite_mem_eq, Finset.sum_singleton]

/-! ## The decomposition -/

/-- The coefficients of `gradF` split into the part carried by `zeroS d n hd j b` and the part
carried by the `n+1` special monomials `smon d n hd j i`. -/
theorem gradF_zeroS_split (d n : ℕ) (hd : 1 ≤ d) (b : Mon d n → ℝ) (y : Fin (n + 1) → ℝ)
    (j k : Fin (n + 1)) :
    gradF d n b y k = gradF d n (zeroS d n hd j b) y k
      + ∑ i : Fin (n + 1), b (smon d n hd j i) * gradKer d n y k (smon d n hd j i) := by
  have hpoint : ∀ m : Mon d n, b m * gradKer d n y k m =
      zeroS d n hd j b m * gradKer d n y k m
        + (if m ∈ Sset d n hd j then b m * gradKer d n y k m else 0) := by
    intro m
    by_cases hm : m ∈ Sset d n hd j
    · have hz : zeroS d n hd j b m = 0 := by
        show (if m ∈ Sset d n hd j then (0 : ℝ) else b m) = 0
        rw [if_pos hm]
      rw [hz, if_pos hm]
      ring
    · have hz : zeroS d n hd j b m = b m := by
        show (if m ∈ Sset d n hd j then (0 : ℝ) else b m) = b m
        rw [if_neg hm]
      rw [hz, if_neg hm]
      ring
  have hSset : (∑ m : Mon d n, (if m ∈ Sset d n hd j then b m * gradKer d n y k m else 0))
      = ∑ i : Fin (n + 1), b (smon d n hd j i) * gradKer d n y k (smon d n hd j i) := by
    rw [← Finset.sum_filter]
    have hf : (Finset.univ.filter (fun m : Mon d n => m ∈ Sset d n hd j))
        = Finset.univ.image (smon d n hd j) := by
      ext m
      simp [Sset]
    rw [hf]
    exact sum_image_smon d n hd j (fun m => b m * gradKer d n y k m)
  calc gradF d n b y k
      = ∑ m : Mon d n, b m * gradKer d n y k m :=
        gradF_eq_sum_gradKer d n b y k
    _ = ∑ m : Mon d n, (zeroS d n hd j b m * gradKer d n y k m
          + (if m ∈ Sset d n hd j then b m * gradKer d n y k m else 0)) :=
        Finset.sum_congr rfl (fun m _ => hpoint m)
    _ = (∑ m : Mon d n, zeroS d n hd j b m * gradKer d n y k m)
          + ∑ m : Mon d n, (if m ∈ Sset d n hd j then b m * gradKer d n y k m else 0) :=
        Finset.sum_add_distrib
    _ = (∑ m : Mon d n, zeroS d n hd j b m * gradKer d n y k m)
          + ∑ i : Fin (n + 1), b (smon d n hd j i) * gradKer d n y k (smon d n hd j i) := by
        rw [hSset]
    _ = gradF d n (zeroS d n hd j b) y k
          + ∑ i : Fin (n + 1), b (smon d n hd j i) * gradKer d n y k (smon d n hd j i) := by
        rw [gradF_eq_sum_gradKer d n (zeroS d n hd j b) y k]

/-- The special part for `k ≠ j`. -/
theorem sum_gradKer_smon_ne (d n : ℕ) (hd : 1 ≤ d) (b : Mon d n → ℝ) (y : Fin (n + 1) → ℝ)
    (j k : Fin (n + 1)) (hkj : k ≠ j) :
    ∑ i : Fin (n + 1), b (smon d n hd j i) * gradKer d n y k (smon d n hd j i)
      = b (smon d n hd j k) * y j ^ (d - 1) := by
  have hpoint : ∀ i : Fin (n + 1),
      b (smon d n hd j i) * gradKer d n y k (smon d n hd j i)
        = (if i = k then b (smon d n hd j i) * y j ^ (d - 1) else 0) := by
    intro i
    rw [gradKer_smon_ne_direction d n hd j k hkj y i]
    by_cases hik : i = k
    · rw [if_pos hik, if_pos hik]
    · rw [if_neg hik, if_neg hik, mul_zero]
  trans ∑ i : Fin (n + 1), (if i = k then b (smon d n hd j i) * y j ^ (d - 1) else 0)
  · exact Finset.sum_congr rfl (fun i _ => hpoint i)
  · exact sum_univ_ite_eq k (fun i => b (smon d n hd j i) * y j ^ (d - 1))

/-- The special part for `k = j`. -/
theorem sum_gradKer_smon_eq (d n : ℕ) (hd1 : 1 ≤ d) (hd2 : 2 ≤ d) (b : Mon d n → ℝ)
    (y : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    ∑ i : Fin (n + 1), b (smon d n hd1 j i) * gradKer d n y j (smon d n hd1 j i)
      = y j ^ (d - 2) * ((d : ℝ) * b (smon d n hd1 j j) * y j
          + ((d : ℝ) - 1) * ∑ i ∈ Finset.univ.erase j, b (smon d n hd1 j i) * y i) := by
  have hpow : y j ^ (d - 1) = y j ^ (d - 2) * y j := by
    have h : d - 2 + 1 = d - 1 := by omega
    calc y j ^ (d - 1) = y j ^ (d - 2 + 1) := by rw [h]
      _ = y j ^ (d - 2) * y j := pow_succ _ _
  have hpoint : ∀ i : Fin (n + 1),
      b (smon d n hd1 j i) * gradKer d n y j (smon d n hd1 j i)
        = (if i = j then b (smon d n hd1 j i) * ((d : ℝ) * y j ^ (d - 2) * y j) else 0)
          + (if i ∈ Finset.univ.erase j then
              b (smon d n hd1 j i) * (((d : ℝ) - 1) * y j ^ (d - 2) * y i) else 0) := by
    intro i
    rw [gradKer_smon_pin_direction d n hd1 j y i]
    by_cases hij : i = j
    · have hnot : ¬ (i ∈ Finset.univ.erase j) := fun h => (Finset.mem_erase.mp h).1 hij
      rw [if_pos hij]
      rw [if_pos hij]
      rw [if_neg hnot]
      rw [hpow]
      ring
    · have hmem : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
      rw [if_neg hij]
      rw [if_neg hij]
      rw [if_pos hmem]
      ring
  have hstep : (∑ i : Fin (n + 1), b (smon d n hd1 j i) * gradKer d n y j (smon d n hd1 j i))
      = ∑ i : Fin (n + 1),
          ((if i = j then b (smon d n hd1 j i) * ((d : ℝ) * y j ^ (d - 2) * y j) else 0)
            + (if i ∈ Finset.univ.erase j then
                b (smon d n hd1 j i) * (((d : ℝ) - 1) * y j ^ (d - 2) * y i) else 0)) :=
    Finset.sum_congr rfl (fun i _ => hpoint i)
  rw [hstep]
  rw [Finset.sum_add_distrib]
  rw [sum_univ_ite_eq j (fun i => b (smon d n hd1 j i) * ((d : ℝ) * y j ^ (d - 2) * y j))]
  rw [Finset.sum_ite_mem_eq]
  rw [show (∑ i ∈ Finset.univ.erase j,
        b (smon d n hd1 j i) * (((d : ℝ) - 1) * y j ^ (d - 2) * y i))
      = ((d : ℝ) - 1) * y j ^ (d - 2) * ∑ i ∈ Finset.univ.erase j,
          b (smon d n hd1 j i) * y i from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)]
  ring

/-- Splitting `∂_k f_b(y)` into (i) the part of `b` supported on the special monomials
`x_j^{d-1}x_i` and (ii) the rest `zeroS j b`.  With `c i = b (smon j i)`:
`∂_k f_b(y) = ∂_k f_{zeroS j b}(y) + b(smon j k) y_j^{d-1}` when `k ≠ j`, and
`∂_j f_b(y) = ∂_j f_{zeroS j b}(y) + y_j^{d-2} (d · b(smon j j) · y_j + (d-1) ∑_{i≠j} b(smon j i) y_i)`. -/
theorem gradF_decomp (d n : ℕ) (hd1 : 1 ≤ d) (hd2 : 2 ≤ d) (b : Mon d n → ℝ)
    (y : Fin (n + 1) → ℝ) (j k : Fin (n + 1)) :
    gradF d n b y k = gradF d n (zeroS d n hd1 j b) y k +
      (if k = j then
        y j ^ (d - 2) * ((d : ℝ) * b (smon d n hd1 j j) * y j
          + ((d : ℝ) - 1) * ∑ i ∈ Finset.univ.erase j, b (smon d n hd1 j i) * y i)
       else b (smon d n hd1 j k) * y j ^ (d - 1)) := by
  rw [gradF_zeroS_split d n hd1 b y j k]
  by_cases hkj : k = j
  · rw [hkj]
    rw [if_pos rfl]
    rw [sum_gradKer_smon_eq d n hd1 hd2 b y j]
  · rw [if_neg hkj]
    rw [sum_gradKer_smon_ne d n hd1 b y j k hkj]

end Work.HP.GradDecomp
