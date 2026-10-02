import Mathlib
import Submission.Work.PARIMPL2.Direct.oidAux
import Submission.Work.PARIMPL2.Direct.orbitCrossBound
import Submission.Work.PARIMPL2.Direct.oidDefs
import Submission.Work.PARIMPL2.Direct.oidCf_abs_le
import Submission.Work.PARIMPL2.Direct.oidCfSign

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

open Finset

/-! ## Elementary helpers for the `cr ≤ 0` weighted-cross bound

These are the elementary product/sum facts used by `oidCrossNegNonpos`: monotonicity of
finite products of nonnegative reals over `ℝ` (which lacks a `MulLeftMono` instance),
the "union bound" `1 - ∏(1-F_i) ≤ ∑F_i`, the crossing index of `λ x` through `π/2`, and
the combination `1 - ∏(1+oidCf_i) ≤ exp(∑oidCg_i) - 1` for `cr ≤ 0`. -/

/-- Product monotonicity for nonnegative real factors. -/
theorem oidcn_prod_le_prod {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  revert hf h
  refine Finset.induction_on s ?_ ?_
  · intro _ _; simp
  · intro a s ha ih hf h
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => h i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
      (le_trans (hf a (Finset.mem_insert_self a s)) (h a (Finset.mem_insert_self a s)))

/-- A product of numbers in `[0,1]` is at most `1`. -/
theorem oidcn_prod_le_one {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ 1) :
    ∏ i ∈ s, f i ≤ 1 := by
  classical
  revert h0 h
  refine Finset.induction_on s ?_ ?_
  · intro _ _; simp
  · intro a s ha ih h0 h
    rw [Finset.prod_insert ha]
    have h1 : ∏ i ∈ s, f i ≤ 1 := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have h2 : f a ≤ 1 := h a (Finset.mem_insert_self a s)
    have h3 : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
    have h4 : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
    nlinarith [h1, h2, h3, h4]

/-- Union bound: `1 - ∏(1-F_i) ≤ ∑F_i` for `F_i ∈ [0,1]`. -/
theorem oidcn_one_sub_prod_le_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ F i) (h1 : ∀ i ∈ s, F i ≤ 1) :
    1 - ∏ i ∈ s, (1 - F i) ≤ ∑ i ∈ s, F i := by
  classical
  revert h0 h1
  refine Finset.induction_on s ?_ ?_
  · intro _ _; simp
  · intro a t hat ih h0 h1
    rw [Finset.prod_insert hat, Finset.sum_insert hat]
    have h0' : ∀ i ∈ t, 0 ≤ F i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1' : ∀ i ∈ t, F i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have ih' := ih h0' h1'
    have hPnn : 0 ≤ ∏ i ∈ t, (1 - F i) :=
      Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (h1' i hi))
    have hPle : ∏ i ∈ t, (1 - F i) ≤ 1 :=
      oidcn_prod_le_one t (fun i => 1 - F i) (fun i hi => sub_nonneg.mpr (h1' i hi))
        (fun i hi => by have := h0' i hi; linarith)
    have hFa0 : 0 ≤ F a := h0 a (Finset.mem_insert_self a t)
    have hFa1 : F a ≤ 1 := h1 a (Finset.mem_insert_self a t)
    nlinarith [ih', hPnn, hPle, hFa0, hFa1]

/-- The crossing index of `λ x` through `π/2`: the first index `j0` with `λ x j ≤ π/2`
(if none, `j0 = n`). -/
theorem oidcn_exists_cross (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (x : ℕ → ℝ)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3) :
    ∃ j0 : ℕ, j0 ≤ n ∧ (∀ j < j0, Real.pi / 2 < lam * x j)
      ∧ (∀ j, j0 ≤ j → j < n → lam * x j ≤ Real.pi / 2) := by
  have hxanti : ∀ b, b ≤ n → ∀ a, a ≤ b → x b ≤ x a := by
    intro b
    induction b with
    | zero => intro _ a ha; simp only [Nat.le_zero] at ha; subst ha; exact le_rfl
    | succ b ih =>
      intro hb a ha
      rcases Nat.eq_or_lt_of_le ha with h | h
      · subst h; exact le_rfl
      · have hab : a ≤ b := by omega
        have hbn : b ≤ n := by omega
        have ih' := ih hbn a hab
        have hd : x (b + 1) ≤ x b := by
          have := hdec b (Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb); linarith
        linarith
  classical
  by_cases hex : ∃ j, j ≤ n ∧ lam * x j ≤ Real.pi / 2
  · refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, ?_⟩
    · intro j hj
      have h1 := Nat.find_min hex hj
      have hjn : j ≤ n := le_trans (le_of_lt hj) (Nat.find_spec hex).1
      by_contra hcon
      exact h1 ⟨hjn, not_lt.mp hcon⟩
    · intro j hj hjn
      have hle : lam * x j ≤ lam * x (Nat.find hex) :=
        mul_le_mul_of_nonneg_left (hxanti j (le_of_lt hjn) (Nat.find hex) hj) hlam.le
      have h2 : lam * x (Nat.find hex) ≤ Real.pi / 2 := (Nat.find_spec hex).2
      linarith
  · refine ⟨n, le_rfl, ?_, ?_⟩
    · intro j hj
      by_contra hcon
      exact hex ⟨j, le_of_lt hj, not_lt.mp hcon⟩
    · intro j hj hjn; omega

/-- For `cr ≤ 0`, `1 - ∏_{i∈s}(1 + oidCf_i) ≤ exp(∑_{i∈s} oidCg_i) - 1`, provided the
coefficients are bounded by `1` in absolute value. -/
theorem oidcn_one_sub_prod_le_exp (lam cr : ℝ) (hlam : 0 < lam) (hcr : cr ≤ 0)
    (x y : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ i ∈ s, |oidCf lam cr x y i| ≤ 1) :
    1 - ∏ i ∈ s, (1 + oidCf lam cr x y i)
      ≤ Real.exp (∑ i ∈ s, oidCg lam |cr| x y i) - 1 := by
  have hCnp : ∀ i ∈ s, oidCf lam cr x y i ≤ 0 := fun i _ => oidCf_nonpos lam cr hlam hcr x y i
  have h0 : ∀ i ∈ s, 0 ≤ |oidCf lam cr x y i| := fun i _ => abs_nonneg _
  have h2 : ∀ i ∈ s, |oidCf lam cr x y i| ≤ oidCg lam |cr| x y i :=
    fun i _ => oidCf_abs_le lam cr hlam x y i
  have hprod : (∏ i ∈ s, (1 + oidCf lam cr x y i))
      = ∏ i ∈ s, (1 - |oidCf lam cr x y i|) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [abs_of_nonpos (hCnp i hi)]; ring
  rw [hprod]
  have hb := oidcn_one_sub_prod_le_sum s (fun i => |oidCf lam cr x y i|) h0 hs
  have hsum : (∑ i ∈ s, |oidCf lam cr x y i|) ≤ ∑ i ∈ s, oidCg lam |cr| x y i :=
    Finset.sum_le_sum (fun i hi => h2 i hi)
  have hEnn : ∀ i ∈ s, 0 ≤ oidCg lam |cr| x y i := fun i _ => by
    rw [oidCg]
    exact mul_nonneg (abs_nonneg _)
      (add_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) (ocDen_nonneg lam x y i)))
  have hEsum : 0 ≤ ∑ i ∈ s, oidCg lam |cr| x y i := Finset.sum_nonneg hEnn
  have hexp := Real.add_one_le_exp (∑ i ∈ s, oidCg lam |cr| x y i)
  linarith

end Work.PARIMPL2.Direct
