import Mathlib
import Submission.Commons.Analysis.Fourier.dilation_variation_scalar_l2
import Submission.Commons.Analysis.Fourier.dilation_variation_aemeasurable

namespace Commons.Analysis.Fourier

open scoped BigOperators ENNReal
open MeasureTheory

/-- The windowed dilation operator `T_u` applied to the function `f`, evaluated at `x`. -/
noncomputable def winOp (Ψ : SchwartzMap ℝ ℂ) (f : ℝ → ℂ) (x u : ℝ) : ℂ :=
  ∫ y : ℝ, f y * (u⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / u))

/-- The `s`-variation, over the scale parameter `u > 0`, of the scalar windowed curve `u ↦ T_u f x`. -/
noncomputable def winVar (Ψ : SchwartzMap ℝ ℂ) (f : ℝ → ℂ) (x : ℝ) (s : ℝ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (u : Fin (J + 1) → {t : ℝ // 0 < t}),
    ⨆ (_ : StrictMono (fun j => (u j : ℝ))),
      ENNReal.ofReal ((∑ j : Fin J,
        ‖winOp Ψ f x (u (Fin.castSucc j) : ℝ) - winOp Ψ f x (u (Fin.succ j) : ℝ)‖ ^ s) ^ ((1:ℝ)/s))

/-- The `s`-variation, over the scale parameter `u > 0`, of the vector valued windowed curve
`u ↦ (T_u f k x)_k`, where `Fin K → ℂ` carries the supremum norm. -/
noncomputable def winVarVec (Ψ : SchwartzMap ℝ ℂ) {K : ℕ} (f : Fin K → ℝ → ℂ)
    (x : ℝ) (s : ℝ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (u : Fin (J + 1) → {t : ℝ // 0 < t}),
    ⨆ (_ : StrictMono (fun j => (u j : ℝ))),
      ENNReal.ofReal ((∑ j : Fin J,
        ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
          - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖ ^ s) ^ ((1:ℝ)/s))

section Reduction

/-- Subadditivity of `x ↦ x ^ r` for `0 < r ≤ 1`. -/
private lemma sum_rpow_le_sum_rpow {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ t, 0 ≤ a i) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∑ i ∈ t, a i) ^ r ≤ ∑ i ∈ t, a i ^ r := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Real.zero_rpow hr0.ne']
  | insert x t hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      have hx0 : 0 ≤ a x := ha x (Finset.mem_insert_self x t)
      have ht0 : 0 ≤ ∑ i ∈ t, a i :=
        Finset.sum_nonneg (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      calc (a x + ∑ i ∈ t, a i) ^ r ≤ (a x) ^ r + (∑ i ∈ t, a i) ^ r :=
            Real.rpow_add_le_add_rpow hx0 ht0 hr0.le hr1
        _ ≤ (a x) ^ r + ∑ i ∈ t, a i ^ r := by
            have := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)); linarith

/-- The `ℓ^s ⊂ ℓ²` comparison for `s ≥ 2`, in the form used below. -/
private lemma rpow_comp {ι : Type*} (t : Finset ι) (c : ι → ℝ) (hc : ∀ i ∈ t, 0 ≤ c i)
    {s : ℝ} (hs : 2 ≤ s) : (∑ i ∈ t, c i) ^ (2/s) ≤ ∑ i ∈ t, c i ^ (2/s) :=
  sum_rpow_le_sum_rpow t c hc (by positivity) (by rw [div_le_one (by linarith)]; linarith)

variable {K : ℕ}

/-- Chain-wise comparison: for one chain of scales, the variation of the `Fin K`-valued curve in
the supremum norm is bounded by the `ℓ²` sum of the scalar variations of the coordinates. -/
private lemma chain_le (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) {s : ℝ} (hs : 2 ≤ s)
    (J : ℕ) (u : Fin (J + 1) → {t : ℝ // 0 < t}) :
    ((∑ j : Fin J,
        ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
          - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖ ^ s) ^ ((1:ℝ)/s)) ^ (2:ℝ)
      ≤ ∑ k : Fin K, ((∑ j : Fin J,
          ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
            - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s) ^ ((1:ℝ)/s)) ^ (2:ℝ) := by
  have hs0 : 0 < s := by linarith
  set b : Fin K → ℝ := fun k => ∑ j : Fin J,
    ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
      - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s with hb
  have hb0 : ∀ k : Fin K, 0 ≤ b k := fun k => Finset.sum_nonneg fun j _ => by positivity
  have hstep1 : ∀ j : Fin J,
      ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
          - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖ ^ s ≤ ∑ k : Fin K,
        ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
          - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s := by
    intro j
    have hle : ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
          - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖
        ≤ (∑ k : Fin K, ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
            - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s) ^ ((1:ℝ)/s) := by
      rw [pi_norm_le_iff_of_nonneg
        (Real.rpow_nonneg (Finset.sum_nonneg fun k _ => by positivity) _)]
      intro k
      calc ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
            - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖
          = (‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
              - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s) ^ ((1:ℝ)/s) := by
            rw [← Real.rpow_mul (by positivity), mul_one_div, div_self hs0.ne', Real.rpow_one]
        _ ≤ _ := by
            refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
            exact Finset.single_le_sum
              (f := fun k : Fin K => ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
                - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s) (fun i _ => by positivity)
              (Finset.mem_univ k)
    calc ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
          - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖ ^ s
        ≤ ((∑ k : Fin K, ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
            - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s) ^ ((1:ℝ)/s)) ^ s :=
          Real.rpow_le_rpow (norm_nonneg _) hle hs0.le
      _ = _ := by
          rw [← Real.rpow_mul (Finset.sum_nonneg fun k _ => by positivity),
            one_div, inv_mul_cancel₀ hs0.ne', Real.rpow_one]
  have hstep2 : (∑ j : Fin J,
        ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
          - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖ ^ s) ≤ ∑ k : Fin K, b k := by
    calc (∑ j : Fin J, ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
          - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖ ^ s)
        ≤ ∑ j : Fin J, ∑ k : Fin K, ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
            - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s := Finset.sum_le_sum fun j _ => hstep1 j
      _ = ∑ k : Fin K, ∑ j : Fin J, ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
            - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s := Finset.sum_comm
      _ = ∑ k : Fin K, b k := rfl
  have hsum0 : 0 ≤ ∑ j : Fin J, ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
          - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖ ^ s :=
    Finset.sum_nonneg fun j _ => by positivity
  calc ((∑ j : Fin J,
        ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
          - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖ ^ s) ^ ((1:ℝ)/s)) ^ (2:ℝ)
      = (∑ j : Fin J, ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
          - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖ ^ s) ^ (2/s) := by
        rw [← Real.rpow_mul hsum0,
          show (1:ℝ)/s * 2 = 2 / s by rw [one_div, mul_comm, div_eq_mul_inv]]
    _ ≤ (∑ k : Fin K, b k) ^ (2/s) := Real.rpow_le_rpow hsum0 hstep2 (by positivity)
    _ ≤ ∑ k : Fin K, b k ^ (2/s) := rpow_comp Finset.univ b (fun k _ => hb0 k) hs
    _ = ∑ k : Fin K, ((∑ j : Fin J,
          ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
            - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s) ^ ((1:ℝ)/s)) ^ (2:ℝ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show b k = ∑ j : Fin J, ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
              - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s from rfl]
        rw [← Real.rpow_mul (Finset.sum_nonneg fun j _ => by positivity),
          show (1:ℝ)/s * 2 = 2 / s by rw [one_div, mul_comm, div_eq_mul_inv]]

/-- **Key reduction.**  The vector valued (`Fin K`-indexed, supremum norm) `s`-variation is
dominated, pointwise in `x`, by the `ℓ²` sum of the scalar `s`-variations of the coordinates. -/
theorem winVarVec_sq_le_sum (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ)
    {s : ℝ} (hs : 2 ≤ s) :
    winVarVec Ψ f x s ^ (2:ℝ) ≤ ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) := by
  -- the vector quantity of a single chain, and its scalar counterparts
  have hA : ∀ (J : ℕ) (u : Fin (J + 1) → {t : ℝ // 0 < t})
      (hu : StrictMono (fun j => (u j : ℝ))),
      ENNReal.ofReal ((∑ j : Fin J,
        ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
          - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖ ^ s) ^ ((1:ℝ)/s)) ^ (2:ℝ)
        ≤ ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) := by
    intro J u hu
    have hchain := chain_le Ψ f x hs J u
    have hA0 : 0 ≤ (∑ j : Fin J,
        ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
          - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖ ^ s) ^ ((1:ℝ)/s) :=
      Real.rpow_nonneg (Finset.sum_nonneg fun j _ => by positivity) _
    have hB0 : ∀ k : Fin K, 0 ≤ (∑ j : Fin J,
        ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
          - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s) ^ ((1:ℝ)/s) :=
      fun k => Real.rpow_nonneg (Finset.sum_nonneg fun j _ => by positivity) _
    have h2 : ENNReal.ofReal ((∑ j : Fin J,
        ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
          - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖ ^ s) ^ ((1:ℝ)/s)) ^ (2:ℝ)
        ≤ ∑ k : Fin K, ENNReal.ofReal ((∑ j : Fin J,
          ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
            - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s) ^ ((1:ℝ)/s)) ^ (2:ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hA0 (by norm_num : (0:ℝ) ≤ 2)]
      refine le_trans (ENNReal.ofReal_le_ofReal hchain) ?_
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => Real.rpow_nonneg (hB0 k) (2:ℝ))]
      exact Finset.sum_le_sum fun k _ =>
        le_of_eq (ENNReal.ofReal_rpow_of_nonneg (hB0 k) (by norm_num : (0:ℝ) ≤ 2)).symm
    refine le_trans h2 (Finset.sum_le_sum fun k _ => ?_)
    have hle : ENNReal.ofReal ((∑ j : Fin J,
        ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
          - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s) ^ ((1:ℝ)/s))
        ≤ winVar Ψ (f k) x s := by
      have h1 : ∀ (w : Fin (J + 1) → {t : ℝ // 0 < t})
          (hw : StrictMono (fun j => (w j : ℝ))),
          ENNReal.ofReal ((∑ j : Fin J,
            ‖winOp Ψ (f k) x (w (Fin.castSucc j) : ℝ)
              - winOp Ψ (f k) x (w (Fin.succ j) : ℝ)‖ ^ s) ^ ((1:ℝ)/s))
          ≤ ⨆ (w : Fin (J + 1) → {t : ℝ // 0 < t}), ⨆ (_ : StrictMono (fun j => (w j : ℝ))),
              ENNReal.ofReal ((∑ j : Fin J,
                ‖winOp Ψ (f k) x (w (Fin.castSucc j) : ℝ)
                  - winOp Ψ (f k) x (w (Fin.succ j) : ℝ)‖ ^ s) ^ ((1:ℝ)/s)) := by
        intro w hw
        exact (le_iSup (fun _ : StrictMono (fun j => (w j : ℝ)) => ENNReal.ofReal ((∑ j : Fin J,
            ‖winOp Ψ (f k) x (w (Fin.castSucc j) : ℝ)
              - winOp Ψ (f k) x (w (Fin.succ j) : ℝ)‖ ^ s) ^ ((1:ℝ)/s))) hw).trans
          (le_iSup (fun w : Fin (J + 1) → {t : ℝ // 0 < t} => ⨆ (_ : StrictMono (fun j => (w j : ℝ))),
            ENNReal.ofReal ((∑ j : Fin J,
              ‖winOp Ψ (f k) x (w (Fin.castSucc j) : ℝ)
                - winOp Ψ (f k) x (w (Fin.succ j) : ℝ)‖ ^ s) ^ ((1:ℝ)/s))) w)
      exact (h1 u hu).trans (le_iSup (fun J' : ℕ =>
        ⨆ (w : Fin (J' + 1) → {t : ℝ // 0 < t}), ⨆ (_ : StrictMono (fun j => (w j : ℝ))),
          ENNReal.ofReal ((∑ j : Fin J',
            ‖winOp Ψ (f k) x (w (Fin.castSucc j) : ℝ)
              - winOp Ψ (f k) x (w (Fin.succ j) : ℝ)‖ ^ s) ^ ((1:ℝ)/s))) J)
    exact ENNReal.rpow_le_rpow hle (by norm_num)
  -- manipulate the nested supremum
  have hsup : winVarVec Ψ f x s =
      ⨆ (J : ℕ) (u : Fin (J + 1) → {t : ℝ // 0 < t})
        (hu : StrictMono (fun j => (u j : ℝ))),
        ENNReal.ofReal ((∑ j : Fin J,
          ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
            - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖ ^ s) ^ ((1:ℝ)/s)) := rfl
  have hsq : winVarVec Ψ f x s ^ (2:ℝ) = winVarVec Ψ f x s * winVarVec Ψ f x s := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, sq]
  rw [hsq, hsup]
  simp only [ENNReal.iSup_mul, ENNReal.mul_iSup]
  refine iSup_le fun J => iSup_le fun u => iSup_le fun hu => iSup_le fun J' => iSup_le fun u' =>
    iSup_le fun hu' => ?_
  -- AM-GM for the product of two chain quantities
  rw [mul_comm]
  set A : ℝ := (∑ j : Fin J,
      ‖(fun k : Fin K => winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ))
        - (fun k : Fin K => winOp Ψ (f k) x (u (Fin.succ j) : ℝ))‖ ^ s) ^ ((1:ℝ)/s) with hAdef
  set A' : ℝ := (∑ j : Fin J',
      ‖(fun k : Fin K => winOp Ψ (f k) x (u' (Fin.castSucc j) : ℝ))
        - (fun k : Fin K => winOp Ψ (f k) x (u' (Fin.succ j) : ℝ))‖ ^ s) ^ ((1:ℝ)/s) with hA'def
  have hA0 : 0 ≤ A := Real.rpow_nonneg (Finset.sum_nonneg fun j _ => by positivity) _
  have hA0' : 0 ≤ A' := Real.rpow_nonneg (Finset.sum_nonneg fun j _ => by positivity) _
  have hamgm : A * A' ≤ max (A^2) (A'^2) := by
    have h1 : 2 * (A * A') ≤ A^2 + A'^2 := by nlinarith [sq_nonneg (A - A'), sq_nonneg A, sq_nonneg A']
    have h2 : A^2 + A'^2 ≤ 2 * max (A^2) (A'^2) := by
      rcases le_total (A^2) (A'^2) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    linarith
  calc ENNReal.ofReal A * ENNReal.ofReal A'
      = ENNReal.ofReal (A * A') := (ENNReal.ofReal_mul hA0).symm
    _ ≤ ENNReal.ofReal (max (A^2) (A'^2)) := ENNReal.ofReal_le_ofReal hamgm
    _ = max (ENNReal.ofReal (A^2)) (ENNReal.ofReal (A'^2)) := ENNReal.ofReal_max _ _
    _ = max (ENNReal.ofReal A ^ (2:ℝ)) (ENNReal.ofReal A' ^ (2:ℝ)) := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, ENNReal.rpow_natCast,
          ENNReal.ofReal_pow hA0, ENNReal.ofReal_pow hA0']
    _ ≤ ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) := max_le (hA J u hu) (hA J' u' hu')

end Reduction

section Assembly

/-- **Bourgain's `L²` variational estimate for the dilation family.**  For every Schwartz window
`Ψ` there is a constant `C` such that, for every `s ∈ (2,3]`, every number `K` of functions and
every `f₁, …, f_K ∈ L² ∩ L^∞`,
```
∫⁻_x (V^s_{u>0} (T_u f_k (x))_k)² ≤ (C/(s-2))² ∫⁻_x ∑_k |f_k(x)|² ,
```
where `T_u f = f * (u⁻¹ • Ψ(·/u))` and `V^s` is the `s`-variation over the scale `u > 0`. -/
theorem dilation_variation_l2_sup (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3) (K : ℕ) (f : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MeasureTheory.MemLp (f k) 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) →
      (∀ k : Fin K, MeasureTheory.MemLp (f k) ⊤ (MeasureTheory.volume : MeasureTheory.Measure ℝ)) →
      ∫⁻ x : ℝ, (⨆ (J : ℕ) (u : Fin (J + 1) → {t : ℝ // 0 < t}),
          ⨆ (_ : StrictMono (fun j => (u j : ℝ))),
            (ENNReal.ofReal ((∑ j : Fin J,
              ‖(fun k : Fin K => ∫ y : ℝ, f k y * (((u (Fin.castSucc j) : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((u (Fin.castSucc j) : ℝ)))))
               - (fun k : Fin K => ∫ y : ℝ, f k y * (((u (Fin.succ j) : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((u (Fin.succ j) : ℝ)))))‖ ^ s)
              ^ ((1:ℝ)/s)))) ^ (2 : ℝ)
        ≤ ENNReal.ofReal ((C / (s - 2)) ^ 2) * ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖ ^ 2) := by
  obtain ⟨C, hCpos, hC⟩ := dilation_variation_scalar_l2 Ψ
  refine ⟨C, hCpos, ?_⟩
  intro s hs hs3 K f hf2 hfinf
  -- the scalar `s`-variation of each coordinate is a.e. measurable
  have hmeas : ∀ k : Fin K, AEMeasurable (fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := fun k =>
    (dilation_variation_aemeasurable Ψ s (f k) (hf2 k).aemeasurable (hf2 k)).pow_const _
  have hmeas2 : ∀ k : Fin K, AEMeasurable
      (fun x : ℝ => ENNReal.ofReal (‖f k x‖ ^ 2))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := fun k =>
    ((hf2 k).aemeasurable.norm.pow_const 2).ennreal_ofReal
  calc ∫⁻ x : ℝ, winVarVec Ψ f x s ^ (2:ℝ)
      ≤ ∫⁻ x : ℝ, ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) :=
        MeasureTheory.lintegral_mono fun x => winVarVec_sq_le_sum Ψ f x (le_of_lt hs)
    _ = ∑ k : Fin K, ∫⁻ x : ℝ, winVar Ψ (f k) x s ^ (2:ℝ) :=
        MeasureTheory.lintegral_finsetSum' _ (fun k _ => hmeas k)
    _ ≤ ∑ k : Fin K, ENNReal.ofReal ((C / (s - 2)) ^ 2)
          * ∫⁻ x : ℝ, ENNReal.ofReal (‖f k x‖ ^ 2) :=
        Finset.sum_le_sum fun k _ => hC s hs hs3 (f k) (hf2 k) (hfinf k)
    _ = ENNReal.ofReal ((C / (s - 2)) ^ 2)
          * ∑ k : Fin K, ∫⁻ x : ℝ, ENNReal.ofReal (‖f k x‖ ^ 2) := by
        rw [Finset.mul_sum]
    _ = ENNReal.ofReal ((C / (s - 2)) ^ 2)
          * ∫⁻ x : ℝ, ∑ k : Fin K, ENNReal.ofReal (‖f k x‖ ^ 2) := by
        rw [MeasureTheory.lintegral_finsetSum' _ (fun k _ => hmeas2 k)]
    _ = ENNReal.ofReal ((C / (s - 2)) ^ 2)
          * ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖ ^ 2) := by
        congr 1
        refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only []
        exact (ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
          (f := fun k : Fin K => ‖f k x‖ ^ 2) (fun k _ => by positivity)).symm

end Assembly

end Commons.Analysis.Fourier
