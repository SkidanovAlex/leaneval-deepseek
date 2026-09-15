import Mathlib
import Submission.Commons.Combinatorics.Additive.Gowers.gvn_weighted
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_data
import Submission.Commons.Combinatorics.Transference.Unorm_pow
import Submission.Commons.Combinatorics.Transference.Unorm_nonneg

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The `p`-uniform generalised von Neumann theorem from the linear forms condition

Green–Tao prove their generalised von Neumann theorem (Prop. 5.1) using *only* the linear forms
condition: the Cauchy–Schwarz chain `J_d² ≤ P_d J_{d+1}` has `P_d = 1 + o(1)` by the linear forms
condition, and the endpoint `J_{k-1}` is the `ν`-weighted `(k-1)`-cube, which is compared with the
*unweighted* cube by the "`ν` covers its own cubes uniformly" argument (GT Lemma 5.4), again using
only the linear forms condition.

The earlier formalisation (`gvn_weighted_unorm_puniform`) instead extracted the `L^{2^{k-1}}`
moments of the functions `f_i` from the Cauchy–Schwarz chain, which requires an *a priori* bound on
`𝔼 (ν+1)^{2^{k-1}}`; that hypothesis is not satisfied by the Goldston–Yıldırım majorant
(`𝔼 ν² ~ log N`), so this file reproves the theorem with all `ν`-averages supplied by the linear
forms condition.
-/

open Finset
open scoped BigOperators
open GVNW
open GVNgen
open Commons.NumberTheory.Sieve
open Commons.Combinatorics.Transference

namespace GTTrans

variable {p : ℕ} [Fact p.Prime]

/-! ## A one-digit flip on the Boolean cube -/

lemma update_of_eq_self {ι : Type*} [DecidableEq ι] (i : ι) {u : ι → Bool} {b : Bool}
    (h : u i = b) : Function.update u i b = u := by
  funext j
  by_cases hj : j = i
  · subst hj; rw [Function.update_self, h]
  · rw [Function.update_of_ne hj]

/-- The involution flipping the `i`-th digit of a Boolean vector. -/
noncomputable def boolFlip {ι : Type*} [DecidableEq ι] (i : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun ω := Function.update ω i (!ω i)
  invFun ω := Function.update ω i (!ω i)
  left_inv ω := by
    show Function.update (Function.update ω i (!ω i)) i (!(Function.update ω i (!ω i)) i) = ω
    rw [Function.update_self, Bool.not_not, Function.update_idem]
    exact Function.update_eq_self i ω
  right_inv ω := by
    show Function.update (Function.update ω i (!ω i)) i (!(Function.update ω i (!ω i)) i) = ω
    rw [Function.update_self, Bool.not_not, Function.update_idem]
    exact Function.update_eq_self i ω

@[simp] lemma boolFlip_apply {ι : Type*} [DecidableEq ι] (i : ι) (ω : ι → Bool) :
    boolFlip i ω = Function.update ω i (!ω i) := rfl

@[simp] lemma boolFlip_apply_self {ι : Type*} [DecidableEq ι] (i : ι) (ω : ι → Bool) :
    boolFlip i ω i = !(ω i) := by
  rw [boolFlip_apply, Function.update_self]

/-- For a function of the Boolean cube which does not depend on the `i`-th digit, the product
over the whole cube is the product of squares over the half-cube with `i`-th digit `false`. -/
lemma prod_univ_bool_update {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (f : (ι → Bool) → ℝ) (hf : ∀ ω, f (Function.update ω i true) = f ω) :
    (∏ ω : ι → Bool, f ω)
      = ∏ ω ∈ (Finset.univ.filter (fun ω : ι → Bool => ω i = false)), (f ω)^2 := by
  have hfi : ∀ ω b, f (Function.update ω i b) = f ω := by
    intro ω b
    cases b
    · have h1 : Function.update (Function.update ω i false) i true = Function.update ω i true := by
        rw [Function.update_idem]
      have h2 := hf (Function.update ω i false)
      rw [h1, hf ω] at h2
      exact h2.symm
    · exact hf ω
  have hdisj : Disjoint (Finset.univ.filter (fun ω : ι → Bool => ω i = false))
      (Finset.univ.filter (fun ω : ι → Bool => ω i = true)) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
    rw [ha] at ha'; exact Bool.noConfusion ha'
  have hsplit : (Finset.univ : Finset (ι → Bool))
      = (Finset.univ.filter (fun ω : ι → Bool => ω i = false))
        ∪ (Finset.univ.filter (fun ω : ι → Bool => ω i = true)) := by
    ext ω; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
    constructor
    · intro _; by_cases h : ω i = false
      · exact Or.inl h
      · exact Or.inr (by simpa using h)
    · intro _; trivial
  have ht : (∏ ω ∈ (Finset.univ.filter (fun ω : ι → Bool => ω i = true)), f ω)
      = ∏ ω ∈ (Finset.univ.filter (fun ω : ι → Bool => ω i = false)), f ω := by
    rw [Finset.prod_equiv (boolFlip i) (s := Finset.univ.filter (fun ω : ι → Bool => ω i = true))
      (t := Finset.univ.filter (fun ω : ι → Bool => ω i = false)) (g := f)
      (fun x => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, boolFlip_apply_self]
        cases x i <;> simp)
      (fun x _ => by
        show f x = f (Function.update x i (!x i))
        rw [hfi])]
  calc (∏ ω : ι → Bool, f ω)
      = ∏ ω ∈ ((Finset.univ.filter (fun ω : ι → Bool => ω i = false))
          ∪ (Finset.univ.filter (fun ω : ι → Bool => ω i = true))), f ω := by
        rw [← hsplit]
    _ = (∏ ω ∈ (Finset.univ.filter (fun ω : ι → Bool => ω i = false)), f ω)
          * (∏ ω ∈ (Finset.univ.filter (fun ω : ι → Bool => ω i = true)), f ω) :=
        Finset.prod_union hdisj
    _ = (∏ ω ∈ (Finset.univ.filter (fun ω : ι → Bool => ω i = false)), f ω)
          * (∏ ω ∈ (Finset.univ.filter (fun ω : ι → Bool => ω i = false)), f ω) := by rw [ht]
    _ = ∏ ω ∈ (Finset.univ.filter (fun ω : ι → Bool => ω i = false)), (f ω)^2 := by
        rw [← Finset.prod_mul_distrib]; simp only [pow_two]

/-! ## The vertex weight of the weighted cube -/

/-- The argument of the `i`-th half-weight at the cube vertex `ω`, namely
`x + σ_ω(h) - (1+i)·(s + τ_ω(h))`; this is `φ_i` evaluated at the vertex (see `phiZ_vertex`). -/
noncomputable def wArg (k : ℕ) (x s : ZMod p) (h : Fin (k-1) → ZMod p)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) : ZMod p :=
  x + wsig ω h - (((1 + i.val : ℕ) : ZMod p)) * (s + wtau ω h)

/-- The `ν`-weight of the cube in its unpaired (square-root) form. -/
noncomputable def wVsq (k : ℕ) (ν : ZMod p → ℝ) (x s : ZMod p) (h : Fin (k-1) → ZMod p) : ℝ :=
  ∏ ω : Fin (k-1) → Bool, ∏ i : Fin (k-1), Real.sqrt (ν (wArg k x s h i ω))

/-- The `ν`-weight of the cube in paired (polynomial) form. -/
noncomputable def wV (k : ℕ) (ν : ZMod p → ℝ) (x s : ZMod p) (h : Fin (k-1) → ZMod p) : ℝ :=
  ∏ i : Fin (k-1), ∏ ω ∈ (Finset.univ.filter (fun ω : Fin (k-1) → Bool => ω i = false)),
    ν (wArg k x s h i ω)

/-- Expansion of `wArg` as a linear combination of the digits of `ω`. -/
lemma wArg_eq (k : ℕ) (x s : ZMod p) (h : Fin (k-1) → ZMod p) (i : Fin (k-1))
    (ω : Fin (k-1) → Bool) :
    wArg k x s h i ω = x - (((1 + i.val : ℕ)) : ZMod p) * s +
      ∑ j : Fin (k-1), (if ω j then h j else 0)
        * (1 - (((1 + i.val : ℕ)) : ZMod p) * ((j : ZMod p) + 1)⁻¹) := by
  have h1 : wArg k x s h i ω = x + ∑ j : Fin (k-1), (if ω j then h j else 0)
      - (((1 + i.val : ℕ)) : ZMod p)
        * (s + ∑ j : Fin (k-1), (if ω j then h j else 0) / ((j : ZMod p) + 1)) := by
    rw [wArg, wsig, wtau]
  rw [h1, mul_add, Finset.mul_sum, sub_add_eq_sub_sub]
  rw [show x + ∑ j : Fin (k-1), (if ω j then h j else 0)
        - (((1 + i.val : ℕ)) : ZMod p) * s
        - ∑ j : Fin (k-1), (((1 + i.val : ℕ)) : ZMod p)
              * ((if ω j then h j else 0) / ((j : ZMod p) + 1))
      = (x - (((1 + i.val : ℕ)) : ZMod p) * s)
        + (∑ j : Fin (k-1), (if ω j then h j else 0)
          - ∑ j : Fin (k-1), (((1 + i.val : ℕ)) : ZMod p)
              * ((if ω j then h j else 0) / ((j : ZMod p) + 1))) from by ring]
  rw [← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [div_eq_mul_inv]
  ring

/-- The `j = i` coefficient in `wArg_eq` vanishes. -/
lemma wArg_coeff_self (k : ℕ) (hkp : k ≤ p) (i : Fin (k-1)) :
    (1 : ZMod p) - (((1 + i.val : ℕ)) : ZMod p) * ((i : ZMod p) + 1)⁻¹ = 0 := by
  have hlt : 1 + i.val < p := by have := i.isLt; omega
  have hne : (((1 + i.val : ℕ)) : ZMod p) ≠ 0 := by
    intro h
    have hdvd : (p : ℕ) ∣ (1 + i.val) := (CharP.cast_eq_zero_iff (ZMod p) p (1 + i.val)).mp h
    have hdvd' : (p : ℕ) ∣ (Nat.succ i.val) := by simpa [Nat.add_comm] using hdvd
    have := Nat.le_of_dvd (Nat.succ_pos _) hdvd'
    omega
  rw [show ((i : ZMod p) + 1) = (((1 + i.val : ℕ)) : ZMod p) from by push_cast; ring,
    mul_inv_cancel₀ hne, sub_self]

lemma wArg_update (k : ℕ) (hkp : k ≤ p) (x s : ZMod p) (h : Fin (k-1) → ZMod p)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) (b : Bool) :
    wArg k x s h i (Function.update ω i b) = wArg k x s h i ω := by
  rw [wArg_eq, wArg_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, wArg_coeff_self k hkp, mul_zero, mul_zero]
  · rw [Function.update_of_ne hj]

/-- **The square-root pairing**: for `ν ≥ 0` the unpaired weight `wVsq` equals the paired
weight `wV`, because `wArg i` does not depend on the `i`-th digit of `ω`. -/
lemma wVsq_eq_wV (k : ℕ) (hkp : k ≤ p) (ν : ZMod p → ℝ) (hν : ∀ x, 0 ≤ ν x)
    (x s : ZMod p) (h : Fin (k-1) → ZMod p) : wVsq k ν x s h = wV k ν x s h := by
  rw [wVsq, wV, Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [prod_univ_bool_update i (fun ω => Real.sqrt (ν (wArg k x s h i ω)))
    (fun ω => by rw [wArg_update k hkp])]
  apply Finset.prod_congr rfl
  intro ω _
  rw [Real.sq_sqrt (hν _)]

/-- The product of the vertex weights factors into the cube of `g` and the `ν`-weight. -/
lemma prod_wvtx (k : ℕ) (g : ZMod p → ℝ) (ν : ZMod p → ℝ) (x s : ZMod p)
    (h : Fin (k-1) → ZMod p) :
    (∏ ω : Fin (k-1) → Bool, wvtx k g ν x s h ω)
      = (∏ ω : Fin (k-1) → Bool, g (x + wsig ω h)) * wVsq k ν x s h := by
  have hpt : ∀ ω : Fin (k-1) → Bool, wvtx k g ν x s h ω
      = g (x + wsig ω h) * ∏ i : Fin (k-1), Real.sqrt (ν (wArg k x s h i ω)) := by
    intro ω
    simp only [wvtx, wArg]
  rw [Finset.prod_congr rfl (fun ω _ => hpt ω), Finset.prod_mul_distrib, wVsq]

/-- The cube weight `∏_ω ν(x + σ_ω(h))`, which does not depend on `s`. -/
noncomputable def wA (k : ℕ) (ν : ZMod p → ℝ) (x : ZMod p) (h : Fin (k-1) → ZMod p) : ℝ :=
  ∏ ω : Fin (k-1) → Bool, ν (x + wsig ω h)

/-- The unweighted cube `∏_ω g(x + σ_ω(h))`. -/
noncomputable def wG (k : ℕ) (g : ZMod p → ℝ) (x : ZMod p) (h : Fin (k-1) → ZMod p) : ℝ :=
  ∏ ω : Fin (k-1) → Bool, g (x + wsig ω h)

/-- The averaged `ν`-weight `W(x,h) = 𝔼_s V(x,s,h)`. -/
noncomputable def wW (k : ℕ) (ν : ZMod p → ℝ) (x : ZMod p) (h : Fin (k-1) → ZMod p) : ℝ :=
  (p : ℝ)⁻¹ * ∑ s : ZMod p, wV k ν x s h

/-- The unweighted cube is dominated by the `ν`-cube. -/
lemma wG_abs_le_wA (k : ℕ) (g : ZMod p → ℝ) (ν : ZMod p → ℝ) (hg : ∀ x, |g x| ≤ ν x)
    (x : ZMod p) (h : Fin (k-1) → ZMod p) : |wG k g x h| ≤ wA k ν x h := by
  rw [wG, wA, Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro ω _; exact abs_nonneg _
  · intro ω _; exact hg _

/-- **The weighted cube in terms of the averaged weight `wW`.** -/
lemma wcubeZ_eq (k : ℕ) (hkp : k ≤ p) (g : ZMod p → ℝ) (ν : ZMod p → ℝ)
    (hν : ∀ x, 0 ≤ ν x) :
    wcubeZ k g ν = (p : ℝ) * ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
      wG k g x h * wW k ν x h := by
  have hpne : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [wcubeZ]
  simp only [wG, wW]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro h _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _
  have hstep : ∀ s : ZMod p, (∏ ω : Fin (k-1) → Bool, wvtx k g ν x s h ω)
      = (∏ ω : Fin (k-1) → Bool, g (x + wsig ω h)) * wV k ν x s h := by
    intro s; rw [prod_wvtx, wVsq_eq_wV k hkp ν hν]
  rw [Finset.sum_congr rfl (fun s _ => hstep s), ← Finset.mul_sum]
  have harith : (p : ℝ) * ((∏ ω : Fin (k-1) → Bool, g (x + wsig ω h))
        * ((p : ℝ)⁻¹ * ∑ s : ZMod p, wV k ν x s h))
      = (∏ ω : Fin (k-1) → Bool, g (x + wsig ω h)) * ∑ s : ZMod p, wV k ν x s h := by
    field_simp
  linarith [harith]

/-- The cube sum of `g` is the sum of the unweighted cube weights. -/
lemma cubeSum_eq_sum_wG (k : ℕ) (g : ZMod p → ℝ) :
    cubeSum (k-1) g = ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wG k g x h := by
  rw [cubeSum]
  apply Finset.sum_congr rfl; intro h _
  apply Finset.sum_congr rfl; intro x _
  apply Finset.prod_congr rfl; intro ω _
  congr 1

/-- **The weighted cube minus the unweighted cube.** -/
lemma wcubeZ_sub (k : ℕ) (hkp : k ≤ p) (g : ZMod p → ℝ) (ν : ZMod p → ℝ)
    (hν : ∀ x, 0 ≤ ν x) :
    wcubeZ k g ν - (p : ℝ) * cubeSum (k-1) g
      = (p : ℝ) * ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
          wG k g x h * (wW k ν x h - 1) := by
  rw [cubeSum_eq_sum_wG, wcubeZ_eq k hkp g ν hν]
  have h1 : (p : ℝ) * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wG k g x h * wW k ν x h)
      - (p : ℝ) * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wG k g x h)
      = (p : ℝ) * ((∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wG k g x h * wW k ν x h)
        - ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wG k g x h) := by ring
  rw [h1, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro h _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro x _
  ring

/-- **Green–Tao Lemma 5.4 ("`ν` covers its own cubes uniformly"), quantitative form.**
If the cube average of `ν` is `1 + O(ε)` and the second moment of the deviation of `W` is
`O(ε)` (both supplied as hypotheses; they are consequences of the linear forms condition), then
the `ν`-weighted cube differs from `p` times the unweighted cube by `O(ε^{1/2} p^{k+1})`. -/
lemma wcubeZ_close (k : ℕ) (hkp : k ≤ p) (g : ZMod p → ℝ) (ν : ZMod p → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hg : ∀ x, |g x| ≤ ν x) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hA0 : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wA k ν x h ≤ (1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))
    (hA2 : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        wA k ν x h * (wW k ν x h - 1)^2 ≤ 4 * ε * (p:ℝ)^(k-1) * (p:ℝ)) :
    |wcubeZ k g ν - (p : ℝ) * cubeSum (k-1) g|
      ≤ (p : ℝ) * (Real.sqrt (4 * ε * (p:ℝ)^(k-1) * (p:ℝ))
          * Real.sqrt ((1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))) := by
  have hp0 : (0:ℝ) ≤ (p:ℝ) := Nat.cast_nonneg _
  have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hA0nonneg : 0 ≤ ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wA k ν x h := by
    apply Finset.sum_nonneg; intro h _
    apply Finset.sum_nonneg; intro x _
    rw [wA]
    exact Finset.prod_nonneg (fun ω _ => hν _)
  have hA2nonneg : 0 ≤ ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
      wA k ν x h * (wW k ν x h - 1)^2 := by
    apply Finset.sum_nonneg; intro h _
    apply Finset.sum_nonneg; intro x _
    exact mul_nonneg (by rw [wA]; exact Finset.prod_nonneg (fun ω _ => hν _)) (sq_nonneg _)
  -- reindex to the product type
  have hR : (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        |wG k g x h * (wW k ν x h - 1)|)
      = ∑ q : (Fin (k-1) → ZMod p) × ZMod p,
          |wG k g q.2 q.1 * (wW k ν q.2 q.1 - 1)| :=
    (Fintype.sum_prod_type (f := fun q : (Fin (k-1) → ZMod p) × ZMod p =>
      |wG k g q.2 q.1 * (wW k ν q.2 q.1 - 1)|)).symm
  have hF : (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        wA k ν x h * (wW k ν x h - 1)^2)
      = ∑ q : (Fin (k-1) → ZMod p) × ZMod p,
          wA k ν q.2 q.1 * (wW k ν q.2 q.1 - 1)^2 :=
    (Fintype.sum_prod_type (f := fun q : (Fin (k-1) → ZMod p) × ZMod p =>
      wA k ν q.2 q.1 * (wW k ν q.2 q.1 - 1)^2)).symm
  have hG : (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wA k ν x h)
      = ∑ q : (Fin (k-1) → ZMod p) × ZMod p, wA k ν q.2 q.1 :=
    (Fintype.sum_prod_type (f := fun q : (Fin (k-1) → ZMod p) × ZMod p =>
      wA k ν q.2 q.1)).symm
  -- Cauchy–Schwarz on the product type
  have hcs : (∑ q : (Fin (k-1) → ZMod p) × ZMod p,
        |wG k g q.2 q.1 * (wW k ν q.2 q.1 - 1)|)^2
      ≤ (∑ q : (Fin (k-1) → ZMod p) × ZMod p,
            wA k ν q.2 q.1 * (wW k ν q.2 q.1 - 1)^2)
        * ∑ q : (Fin (k-1) → ZMod p) × ZMod p, wA k ν q.2 q.1 := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (Finset.univ : Finset ((Fin (k-1) → ZMod p) × ZMod p))
      (r := fun q => |wG k g q.2 q.1 * (wW k ν q.2 q.1 - 1)|)
      (f := fun q => wA k ν q.2 q.1 * (wW k ν q.2 q.1 - 1)^2)
      (g := fun q => wA k ν q.2 q.1) ?_ ?_ ?_
    · intro q _
      exact mul_nonneg (by rw [wA]; exact Finset.prod_nonneg (fun ω _ => hν _)) (sq_nonneg _)
    · intro q _
      rw [wA]; exact Finset.prod_nonneg (fun ω _ => hν _)
    · intro q _
      have h1 : |wG k g q.2 q.1| ≤ wA k ν q.2 q.1 := wG_abs_le_wA k g ν hg q.2 q.1
      have h2 : wG k g q.2 q.1 ^ 2 ≤ wA k ν q.2 q.1 ^ 2 := by
        calc wG k g q.2 q.1 ^ 2 = |wG k g q.2 q.1| ^ 2 := (sq_abs _).symm
          _ ≤ wA k ν q.2 q.1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      calc |wG k g q.2 q.1 * (wW k ν q.2 q.1 - 1)| ^ 2
          = wG k g q.2 q.1 ^ 2 * (wW k ν q.2 q.1 - 1) ^ 2 := by
            rw [abs_mul, mul_pow]; simp only [sq_abs]
        _ ≤ wA k ν q.2 q.1 ^ 2 * (wW k ν q.2 q.1 - 1) ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = wA k ν q.2 q.1 * (wW k ν q.2 q.1 - 1) ^ 2 * wA k ν q.2 q.1 := by ring
  -- bound the left-hand side
  have hmain : |wcubeZ k g ν - (p : ℝ) * cubeSum (k-1) g|
      ≤ (p : ℝ) * ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
          |wG k g x h * (wW k ν x h - 1)| := by
    rw [wcubeZ_sub k hkp g ν hν, abs_mul, abs_of_nonneg hp0]
    apply mul_le_mul_of_nonneg_left _ hp0
    calc |∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wG k g x h * (wW k ν x h - 1)|
        ≤ ∑ h : Fin (k-1) → ZMod p, |∑ x : ZMod p, wG k g x h * (wW k ν x h - 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
            |wG k g x h * (wW k ν x h - 1)| :=
          Finset.sum_le_sum (fun h _ => Finset.abs_sum_le_sum_abs _ _)
  have hsqrt : (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, |wG k g x h * (wW k ν x h - 1)|)
      ≤ Real.sqrt (4 * ε * (p:ℝ)^(k-1) * (p:ℝ)) * Real.sqrt ((1 + ε) * (p:ℝ)^(k-1) * (p:ℝ)) := by
    have hcs' : (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
          |wG k g x h * (wW k ν x h - 1)|)^2
        ≤ (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
              wA k ν x h * (wW k ν x h - 1)^2)
          * ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wA k ν x h := by
      rw [hR, hF, hG]; exact hcs
    refine le_trans (Real.le_sqrt_of_sq_le hcs') ?_
    rw [Real.sqrt_mul hA2nonneg]
    exact mul_le_mul (Real.sqrt_le_sqrt hA2) (Real.sqrt_le_sqrt hA0)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact le_trans hmain (mul_le_mul_of_nonneg_left hsqrt hp0)


/-! ## The `p`-uniform generalised von Neumann theorem -/

lemma sum_range_two_pow (n : ℕ) : (∑ i ∈ Finset.range n, (2:ℕ)^i) = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have : 1 ≤ 2^n := Nat.one_le_two_pow
    omega

/-- For `A, B ≥ 0` and `n ≥ 1`, `A^n + B^n ≤ (A + B)^n`. -/
lemma add_pow_ge_of_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {n : ℕ} (hn : 1 ≤ n) :
    A^n + B^n ≤ (A + B)^n := by
  rw [add_pow]
  have h1 : A^n = A^n * B^(n-n) * (n.choose n : ℝ) := by simp
  have h2 : B^n = A^0 * B^(n-0) * (n.choose 0 : ℝ) := by simp
  have hpair : (∑ x ∈ ({n, 0} : Finset ℕ), A^x * B^(n-x) * (n.choose x : ℝ))
      = A^n * B^(n-n) * (n.choose n : ℝ) + A^0 * B^(n-0) * (n.choose 0 : ℝ) :=
    Finset.sum_pair (by omega)
  rw [h1, h2, ← hpair]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl <;> simp [Finset.mem_range]
  · intro i hi _
    positivity

theorem gvn_puniform_of_averages {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p)
    {ν : ZMod p → ℝ} (hνpos : ∀ x, 0 < ν x) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hA0 : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wA k ν x h
        ≤ (1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))
    (hA2 : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        wA k ν x h * (wW k ν x h - 1)^2 ≤ 4 * ε * (p:ℝ)^(k-1) * (p:ℝ))
    (hPm : ∀ i ∈ Finset.range (k-1), Pm (ZMod p) k (phiZ (p:=p) k) ν i ≤ 1 + ε) :
    ∀ (f : Fin k → ZMod p → ℝ), (∀ i x, |f i x| ≤ ν x)
      → ∀ γ : ℝ, 0 ≤ γ → Unorm (k-1) (f ⟨0, by omega⟩) ≤ γ
      → |apsumZ k f| ≤ (p:ℝ)^2 * 16 * (γ + ε ^ (((2^k : ℕ) : ℝ))⁻¹) := by
  intro f hf γ hγ hU
  have hp0 : (0:ℝ) ≤ (p:ℝ) := Nat.cast_nonneg _
  have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpne : (p:ℝ) ≠ 0 := ne_of_gt hppos
  have hν0 : ∀ x, 0 ≤ ν x := fun x => le_of_lt (hνpos x)
  set N : ℕ := 2 ^ (k-1) with hNdef
  have hNpos : (0:ℝ) < (N:ℝ) := by rw [hNdef]; positivity
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by rw [hNdef]; exact_mod_cast Nat.one_le_two_pow
  set U : ℝ := Unorm (k-1) (f ⟨0, by omega⟩) with hUdef
  have hU0 : 0 ≤ U := by rw [hUdef]; exact Unorm_nonneg _ (by omega) _
  set q : ℝ := (((2^k : ℕ)) : ℝ)⁻¹ with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by
    rw [hq, inv_le_one₀ (by positivity)]; exact_mod_cast Nat.one_le_two_pow
  -- the weighted von Neumann chain
  have hchain := gvn_weighted_zmod (p:=p) hk hkp f ν hνpos hf
  -- the cube comparison
  have hclose := wcubeZ_close k hkp (f ⟨0, by omega⟩) ν hν0 (fun x => hf _ x) hε0 hA0 hA2
  have hwc : wcubeZ k (f ⟨0, by omega⟩) ν
      ≤ (p:ℝ) * cubeSum (k-1) (f ⟨0, by omega⟩)
        + (p:ℝ) * (Real.sqrt (4 * ε * (p:ℝ)^(k-1) * (p:ℝ))
            * Real.sqrt ((1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))) := by
    have h := abs_le.mp hclose
    have h1 : wcubeZ k (f ⟨0, by omega⟩) ν
        ≤ (p:ℝ) * cubeSum (k-1) (f ⟨0, by omega⟩)
          + (p:ℝ) * (Real.sqrt (4 * ε * (p:ℝ)^(k-1) * (p:ℝ))
              * Real.sqrt ((1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))) := by linarith [h.2]
    exact h1
  -- the cube sum in terms of the Gowers norm
  have hcube : cubeSum (k-1) (f ⟨0, by omega⟩) = U ^ N * (p:ℝ)^k := by
    have hUp := Unorm_pow (G := ZMod p) (k-1) (by omega) (f ⟨0, by omega⟩)
    rw [ZMod.card, show k - 1 + 1 = k from by omega] at hUp
    rw [← hUdef, ← hNdef] at hUp
    rw [hUp, div_mul_cancel₀ _ (by positivity : ((p:ℝ)^k) ≠ 0)]
  -- the `Pm` product
  set P : ℝ := ∏ i ∈ Finset.range (k-1), (Pm (ZMod p) k (phiZ (p:=p) k) ν i)^(2^i) with hPdef
  have hPbound : P ≤ (1 + ε) ^ (N - 1) := by
    rw [hPdef]
    calc (∏ i ∈ Finset.range (k-1), (Pm (ZMod p) k (phiZ (p:=p) k) ν i)^(2^i))
        ≤ ∏ i ∈ Finset.range (k-1), (1 + ε)^(2^i) :=
          Finset.prod_le_prod
            (fun i _ => pow_nonneg (Pm_nonneg (phiZ (p:=p) k) ν hνpos i) _)
            (fun i hi => pow_le_pow_left₀ (Pm_nonneg (phiZ (p:=p) k) ν hνpos i) (hPm i hi) _)
      _ = (1 + ε) ^ (∑ i ∈ Finset.range (k-1), 2^i) := by
          rw [Finset.prod_pow_eq_pow_sum]
      _ = (1 + ε) ^ (N - 1) := by rw [hNdef, sum_range_two_pow]
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    exact Finset.prod_nonneg (fun i _ => pow_nonneg (Pm_nonneg (phiZ (p:=p) k) ν hνpos i) _)
  -- the square-root factor
  have hpk : (p:ℝ)^(k-1) * (p:ℝ) = (p:ℝ)^k := by
    rw [← pow_succ, show k - 1 + 1 = k from by omega]
  have hS : Real.sqrt (4 * ε * (p:ℝ)^(k-1) * (p:ℝ)) * Real.sqrt ((1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))
      = (p:ℝ)^k * Real.sqrt (4 * ε * (1 + ε)) := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 4 * ε * (p:ℝ)^(k-1) * (p:ℝ))]
    rw [show 4 * ε * (p:ℝ)^(k-1) * (p:ℝ) * ((1 + ε) * (p:ℝ)^(k-1) * (p:ℝ))
        = (4 * ε * (1 + ε)) * ((p:ℝ)^k)^2 from by rw [← hpk]; ring]
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 4 * ε * (1 + ε)),
      Real.sqrt_sq (pow_nonneg hp0 k)]
    ring
  -- combine
  have hC0 : 0 ≤ Real.sqrt (4 * ε * (1 + ε)) := Real.sqrt_nonneg _
  have hpow : ((p:ℝ)^2)^N = (p:ℝ)^(2^k) := by
    rw [hNdef, ← pow_mul]
    congr 1
    conv_rhs => rw [show k = (k-1) + 1 from by omega, pow_succ]
    ring
  have hstep1 : |apsumZ k f| ^ N
      ≤ ((p:ℝ)^2)^N * ((U^N + Real.sqrt (4*ε*(1+ε))) * (1+ε)^(N-1)) := by
    refine le_trans hchain ?_
    have h1 : (p:ℝ) ^ (2^k - k - 1) * wcubeZ k (f ⟨0, by omega⟩) ν
        * (∏ i ∈ Finset.range (k-1), (Pm (ZMod p) k (phiZ (p:=p) k) ν i)^(2^i))
        ≤ (p:ℝ) ^ (2^k - k - 1) * ((p:ℝ) * cubeSum (k-1) (f ⟨0, by omega⟩)
            + (p:ℝ) * (Real.sqrt (4 * ε * (p:ℝ)^(k-1) * (p:ℝ))
              * Real.sqrt ((1 + ε) * (p:ℝ)^(k-1) * (p:ℝ)))) * (1 + ε) ^ (N - 1) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hwc (by positivity)) hPbound hP0 ?_
      have hc0 : 0 ≤ cubeSum (k-1) (f ⟨0, by omega⟩) := cubeSum_nonneg (k-1) (by omega) _
      have hs0 : 0 ≤ Real.sqrt (4 * ε * (p:ℝ)^(k-1) * (p:ℝ))
          * Real.sqrt ((1 + ε) * (p:ℝ)^(k-1) * (p:ℝ)) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      positivity
    refine le_trans h1 (le_of_eq ?_)
    rw [hcube, hS]
    rw [show (p:ℝ) * (U^N * (p:ℝ)^k) = (p:ℝ)^(k+1) * U^N from by
        rw [pow_succ]; ring,
      show (p:ℝ) * ((p:ℝ)^k * Real.sqrt (4*ε*(1+ε)))
          = (p:ℝ)^(k+1) * Real.sqrt (4*ε*(1+ε)) from by rw [pow_succ]; ring]
    rw [show (p:ℝ)^(2^k-k-1) * ((p:ℝ)^(k+1) * U^N + (p:ℝ)^(k+1) * Real.sqrt (4*ε*(1+ε)))
        * (1+ε)^(N-1)
        = ((p:ℝ)^2)^N * ((U^N + Real.sqrt (4*ε*(1+ε))) * (1+ε)^(N-1)) from by
      have ha : (2^k - k - 1) + (k+1) = 2^k := by
        rw [Nat.sub_sub, Nat.sub_add_cancel (by have := Nat.lt_two_pow_self (n := k); omega)]
      calc (p:ℝ)^(2^k-k-1) * ((p:ℝ)^(k+1) * U^N + (p:ℝ)^(k+1) * Real.sqrt (4*ε*(1+ε)))
            * (1+ε)^(N-1)
          = ((p:ℝ)^(2^k-k-1) * (p:ℝ)^(k+1)) * (U^N + Real.sqrt (4*ε*(1+ε)))
              * (1+ε)^(N-1) := by ring
        _ = (p:ℝ)^(2^k) * (U^N + Real.sqrt (4*ε*(1+ε))) * (1+ε)^(N-1) := by
            rw [← pow_add, ha]
        _ = ((p:ℝ)^2)^N * ((U^N + Real.sqrt (4*ε*(1+ε))) * (1+ε)^(N-1)) := by
            rw [hpow]; ring]
  -- the exponent `ε^{2^{-k}}` and `√ε`
  have hsqrtε : ε ^ (q * (N:ℝ)) = Real.sqrt ε := by
    have h2kn : q * (N:ℝ) = (2:ℝ)⁻¹ := by
      rw [hq, mul_comm, ← div_eq_mul_inv]
      simp only [hNdef, Nat.cast_pow, Nat.cast_ofNat]
      rw [show (2:ℝ)^k = (2:ℝ)^(k-1) * 2 from by
          calc (2:ℝ)^k = (2:ℝ)^((k-1)+1) := by
                congr 1
                omega
            _ = (2:ℝ)^(k-1) * 2 := pow_succ (2:ℝ) (k-1),
        ← div_div, div_self (by positivity : (2:ℝ)^(k-1) ≠ 0)]
      norm_num
    rw [h2kn, Real.sqrt_eq_rpow, show (2:ℝ)⁻¹ = 1/2 from by norm_num]
  have hεq0 : 0 ≤ ε ^ q := Real.rpow_nonneg hε0 q
  have hεqN : (ε ^ q) ^ N = Real.sqrt ε := by
    have h' : (ε ^ q) ^ N = ε ^ (q * (N:ℝ)) := by
      rw [← Real.rpow_natCast (ε ^ q) N]
      exact (Real.rpow_mul hε0 q (N:ℝ)).symm
    rw [h', hsqrtε]
  -- `C ≤ (8 ε^q)^N`
  have hsqrt8 : Real.sqrt (4 * ε * (1 + ε)) ≤ 8 * Real.sqrt ε := by
    have h1 : (4 * ε * (1 + ε) : ℝ) ≤ (8 * Real.sqrt ε)^2 := by
      rw [mul_pow, Real.sq_sqrt hε0]; nlinarith [hε1, hε0]
    refine le_trans (Real.sqrt_le_sqrt h1) ?_
    rw [Real.sqrt_sq (by positivity)]
  have h8N : (8:ℝ) ≤ 8^N := by
    calc (8:ℝ) = 8^1 := (pow_one 8).symm
      _ ≤ 8^N := pow_le_pow_right₀ (by norm_num) (by exact_mod_cast hN1 : (1:ℕ) ≤ N)
  have hεq_le : Real.sqrt (4 * ε * (1 + ε)) ≤ (8 * ε ^ q)^N := by
    rw [mul_pow]
    calc Real.sqrt (4 * ε * (1 + ε)) ≤ 8 * Real.sqrt ε := hsqrt8
      _ = 8 * (ε ^ q)^N := by rw [hεqN]
      _ ≤ 8^N * (ε ^ q)^N := mul_le_mul_of_nonneg_right h8N (pow_nonneg hεq0 N)
  -- assemble
  have hsum : U^N + Real.sqrt (4 * ε * (1 + ε)) ≤ (8 * (γ + ε ^ q))^N := by
    have h1 : U^N ≤ (8 * γ)^N :=
      le_trans (pow_le_pow_left₀ hU0 hU N) (pow_le_pow_left₀ hγ (by linarith) N)
    refine le_trans (add_le_add h1 hεq_le) ?_
    rw [show (8 * (γ + ε ^ q)) = 8 * γ + 8 * ε ^ q from by ring]
    exact add_pow_ge_of_nonneg (by positivity) (by positivity) (by exact_mod_cast hN1)
  have hfac : (1 + ε)^(N - 1) ≤ 2^N := by
    refine le_trans (pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1 + ε) (Nat.sub_le _ _)) ?_
    exact pow_le_pow_left₀ (by linarith) (by linarith) N
  have hfinal : ((p:ℝ)^2)^N * ((U^N + Real.sqrt (4*ε*(1+ε))) * (1+ε)^(N-1))
      ≤ ((p:ℝ)^2 * 16 * (γ + ε^q))^N := by
    have h1 : (U^N + Real.sqrt (4*ε*(1+ε))) * (1+ε)^(N-1) ≤ (8 * (γ + ε^q))^N * 2^N :=
      mul_le_mul hsum hfac (by positivity) (by positivity)
    have h2 : (8 * (γ + ε ^ q))^N * 2^N = (16:ℝ)^N * (γ + ε ^ q)^N := by
      rw [← mul_pow (8 * (γ + ε ^ q)) 2 N, ← mul_pow (16:ℝ) (γ + ε ^ q) N]
      congr 1
      ring
    calc ((p:ℝ)^2)^N * ((U^N + Real.sqrt (4*ε*(1+ε))) * (1+ε)^(N-1))
        ≤ ((p:ℝ)^2)^N * ((8 * (γ + ε^q))^N * 2^N) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((p:ℝ)^2)^N * ((16:ℝ)^N * (γ + ε^q)^N) := by rw [h2]
      _ = ((p:ℝ)^2 * 16 * (γ + ε^q))^N := by rw [mul_pow, mul_pow]; ring
  have hZ : |apsumZ k f| ^ N ≤ ((p:ℝ)^2 * 16 * (γ + ε^q))^N := le_trans hstep1 hfinal
  have hN0 : N ≠ 0 := by
    have : 1 ≤ N := by exact_mod_cast hN1
    omega
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) hN0).mp hZ

end GTTrans
