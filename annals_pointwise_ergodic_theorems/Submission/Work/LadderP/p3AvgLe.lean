import Mathlib
import Submission.Work.Peluse.LadderP.p2Defs
import Submission.Work.Peluse.LadderP.p2dilateSplit
import Submission.Work.Peluse.LadderP.p3HeartDefs

/-! # The class-averaging step of the level-`n` ladder node

`p3AvgLe` is the level-`n` analogue of the P2 lane's `p2AvgLe` (which is the case `n = 2`,
exponent `4`): from the lower bound `γ ≤ boxAvgA n c M₁ M₂ b N f` of the frozen averaged level-`n`
box norm — with the directions *dilated* by `c` and the full window `symIcc N` — it produces the
lower bound `γ ^ (2 ^ n) ≤ ∑_r w_r · p3BoxAvg_r` of the *class* box averages, where the classes are
the residue classes `S_r = {x ∈ symIcc N : x ≡ r (mod c)}` with `f_r(ξ) = f (r + c ξ)` and
`w_r = |S_r| / |symIcc N|`.

The two ingredients are, exactly as in `p2AvgLe`:

* the dilation-splitting identity `p2dilateSplit` (already proved for a general level `t`):
  `‖f‖^{2^n}_{□^n_{c((a+b_i)[M₂])}(symIcc N)} = ∑_r w_r ‖f_r‖^{2^n}_{□^n_{((a+b_i)[M₂])}(S_r)}`;
* the convexity (power-mean) inequality at the exponent `2 ^ n`
  `(M₁⁻¹ ∑_a p_a)^{2^n} ≤ M₁⁻¹ ∑_a p_a^{2^n}` (`Real.arith_mean_le_rpow_mean`), together with
  `‖f_r‖_{□^n} ≤ 1` (hypothesis `hu1`), which gives `‖f_r‖^{2^n} ≤ ‖f_r‖`.
-/

set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.LadderP

noncomputable section

open Work.Peluse

/-! ## The abstract power-mean assembly at the exponent `2 ^ t` -/

/-- **Abstract power-mean assembly at the exponent `2 ^ t`.**  Let `A`, `Rs` be finite index sets
with `A.card = M₁`, let `w` be a probability weight on `Rs` (`w ≥ 0`, `∑_{r∈Rs} w r = 1`), let
`x a r ≥ 0` and `p a ≥ 0` be such that `p a ^ (2^t) ≤ ∑_{r ∈ Rs} w r * x a r` for every `a ∈ A`.
Then any `γ ≤ M₁⁻¹ ∑_{a∈A} p a` with `γ ≥ 0` satisfies

`γ ^ (2^t) ≤ ∑_{r ∈ Rs} w r * (M₁⁻¹ ∑_{a∈A} x a r)`.

The proof is `γ^{2^t} ≤ (M₁⁻¹∑p)^{2^t} ≤ M₁⁻¹∑ p^{2^t} ≤ M₁⁻¹∑_a ∑_r w_r x_{a,r}
= ∑_r w_r (M₁⁻¹∑_a x_{a,r})`, the middle inequality being the power mean inequality at the exponent
`2^t` (`Real.arith_mean_le_rpow_mean`).  This is the generalisation to `2^t` of
`Work.Peluse.LadderP.powFourAssembly` (the case `t = 2`). -/
theorem powMeanAssembly {M₁ : ℕ} (hM₁ : 1 ≤ M₁) (t : ℕ) (ht : 1 ≤ t) (A Rs : Finset ℕ)
    (w : ℕ → ℝ) (x : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (hAcard : A.card = M₁)
    (hw : ∀ r ∈ Rs, 0 ≤ w r) (hws : ∑ r ∈ Rs, w r = 1)
    (hp0 : ∀ a ∈ A, 0 ≤ p a) (hp : ∀ a ∈ A, p a ^ (2 ^ t) ≤ ∑ r ∈ Rs, w r * x a r)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ ((M₁ : ℝ))⁻¹ * ∑ a ∈ A, p a) :
    γ ^ (2 ^ t) ≤ ∑ r ∈ Rs, w r * (((M₁ : ℝ))⁻¹ * ∑ a ∈ A, x a r) := by
  have hM1pos : (0 : ℝ) < (M₁ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM₁
    linarith
  have hinv0 : 0 ≤ ((M₁ : ℝ))⁻¹ := inv_nonneg.mpr hM1pos.le
  -- the uniform weights `M₁⁻¹` on `A` sum to `1`
  have hwsA : ∑ a ∈ A, ((M₁ : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, hAcard, nsmul_eq_mul]
    exact mul_inv_cancel₀ (ne_of_gt hM1pos)
  -- the exponent conversion, so that the power mean inequality can be fed the natural power `2^t`
  have hcast : (2 : ℝ) ^ t = (((2 ^ t : ℕ)) : ℝ) := by push_cast; ring
  have hrpowN : ∀ a : ℕ, p a ^ ((2 : ℝ) ^ t) = p a ^ (2 ^ t) := by
    intro a
    rw [hcast, Real.rpow_natCast]
  have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ t := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  -- the power mean inequality at the exponent `2 ^ t`
  have hpm : ∑ a ∈ A, ((M₁ : ℝ))⁻¹ * p a
      ≤ (∑ a ∈ A, ((M₁ : ℝ))⁻¹ * p a ^ (2 ^ t)) ^ (1 / ((2 : ℝ) ^ t)) := by
    have h := Real.arith_mean_le_rpow_mean A (fun _ => ((M₁ : ℝ))⁻¹) p
      (fun a _ => hinv0) hwsA (fun a ha => hp0 a ha) hp1
    simpa only [hrpowN] using h
  have hSnn : 0 ≤ ∑ a ∈ A, ((M₁ : ℝ))⁻¹ * p a ^ (2 ^ t) :=
    Finset.sum_nonneg (fun a ha => mul_nonneg hinv0 (pow_nonneg (hp0 a ha) _))
  -- `(M₁⁻¹∑p)^{2^t} ≤ M₁⁻¹∑p^{2^t}`
  have hstep : (((M₁ : ℝ))⁻¹ * ∑ a ∈ A, p a) ^ (2 ^ t)
      ≤ ∑ a ∈ A, ((M₁ : ℝ))⁻¹ * p a ^ (2 ^ t) := by
    have h4 : ((∑ a ∈ A, ((M₁ : ℝ))⁻¹ * p a ^ (2 ^ t)) ^ (1 / ((2 : ℝ) ^ t))) ^ (2 ^ t)
        = ∑ a ∈ A, ((M₁ : ℝ))⁻¹ * p a ^ (2 ^ t) := by
      rw [show (1 : ℝ) / ((2 : ℝ) ^ t) = ((((2 ^ t : ℕ)) : ℝ))⁻¹ by rw [one_div, hcast]]
      exact Real.rpow_inv_natCast_pow hSnn (by positivity)
    calc (((M₁ : ℝ))⁻¹ * ∑ a ∈ A, p a) ^ (2 ^ t)
        ≤ ((∑ a ∈ A, ((M₁ : ℝ))⁻¹ * p a ^ (2 ^ t)) ^ (1 / ((2 : ℝ) ^ t))) ^ (2 ^ t) :=
          pow_le_pow_left₀ (mul_nonneg hinv0 (Finset.sum_nonneg (fun a ha => hp0 a ha)))
            (by simpa only [Finset.mul_sum] using hpm) (2 ^ t)
      _ = ∑ a ∈ A, ((M₁ : ℝ))⁻¹ * p a ^ (2 ^ t) := h4
  have hsum_le : ∑ a ∈ A, ((M₁ : ℝ))⁻¹ * p a ^ (2 ^ t)
      ≤ ∑ a ∈ A, ((M₁ : ℝ))⁻¹ * (∑ r ∈ Rs, w r * x a r) :=
    Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hp a ha) hinv0)
  -- factor `M₁⁻¹` out of the double sum
  have hfactor : ∑ a ∈ A, ((M₁ : ℝ))⁻¹ * (∑ r ∈ Rs, w r * x a r)
      = ∑ r ∈ Rs, w r * (((M₁ : ℝ))⁻¹ * ∑ a ∈ A, x a r) := by
    calc ∑ a ∈ A, ((M₁ : ℝ))⁻¹ * (∑ r ∈ Rs, w r * x a r)
        = ∑ a ∈ A, ∑ r ∈ Rs, ((M₁ : ℝ))⁻¹ * (w r * x a r) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ r ∈ Rs, ∑ a ∈ A, ((M₁ : ℝ))⁻¹ * (w r * x a r) := Finset.sum_comm
      _ = ∑ r ∈ Rs, w r * (((M₁ : ℝ))⁻¹ * ∑ a ∈ A, x a r) := by
          refine Finset.sum_congr rfl (fun r _ => ?_)
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a _ => by ring)
  calc γ ^ (2 ^ t) ≤ (((M₁ : ℝ))⁻¹ * ∑ a ∈ A, p a) ^ (2 ^ t) :=
        pow_le_pow_left₀ hγ0 hγ (2 ^ t)
    _ ≤ ∑ a ∈ A, ((M₁ : ℝ))⁻¹ * p a ^ (2 ^ t) := hstep
    _ ≤ ∑ a ∈ A, ((M₁ : ℝ))⁻¹ * (∑ r ∈ Rs, w r * x a r) := hsum_le
    _ = ∑ r ∈ Rs, w r * (((M₁ : ℝ))⁻¹ * ∑ a ∈ A, x a r) := hfactor

/-! ## The level-`n` class averaging -/

theorem p3AvgLe {n : ℕ} (hn : 1 ≤ n) {c : ℤ} (hc : 0 < c) {M₁ M₂ N : ℕ} (hM₁ : 1 ≤ M₁)
    (hM₂ : 1 ≤ M₂) (b : Fin n → ℤ) (γ : ℝ) {f : ℤ → ℂ} (hcN : c ≤ 2 * (N : ℤ) + 1)
    (hfs : Work.Peluse.FinSuppZ f) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hu1 : ∀ a ∈ Finset.Icc 1 M₁, ∀ r ∈ Finset.range c.natAbs,
      Work.Peluse.boxNorm n (fun i : Fin n => Work.Peluse.arithIcc ((a : ℤ) + b i) M₂)
        (Work.Peluse.LadderP.p2Cls c N r) (Work.Peluse.LadderP.p2ClsFn c r f) ≤ 1)
    (hbox : γ ≤ Work.Peluse.LadderQ.boxAvgA n c M₁ M₂ b N f) :
    γ ^ (2 ^ n) ≤ ∑ r ∈ Finset.range c.natAbs, Work.Peluse.LadderP.p2Wt c N r *
        Work.Peluse.LadderP.p3BoxAvg n M₁ M₂ b (Work.Peluse.LadderP.p2Cls c N r)
          (Work.Peluse.LadderP.p2ClsFn c r f) := by
  classical
  -- the index sets
  set A : Finset ℕ := Finset.Icc 1 M₁ with hA
  set Rs : Finset ℕ := Finset.range c.natAbs with hRs
  -- the class weight, the class box norms `x`, the dilated box powers `y` and dilated box norms `p`
  set w : ℕ → ℝ := fun r => Work.Peluse.LadderP.p2Wt c N r with hw
  set x : ℕ → ℕ → ℝ := fun a r =>
    Work.Peluse.boxNorm n (fun i : Fin n => Work.Peluse.arithIcc ((a : ℤ) + b i) M₂)
      (Work.Peluse.LadderP.p2Cls c N r) (Work.Peluse.LadderP.p2ClsFn c r f) with hx
  set y : ℕ → ℕ → ℝ := fun a r =>
    Work.Peluse.boxNormPow n (fun i : Fin n => Work.Peluse.arithIcc ((a : ℤ) + b i) M₂)
      (Work.Peluse.LadderP.p2Cls c N r) (Work.Peluse.LadderP.p2ClsFn c r f) with hy
  set p : ℕ → ℝ := fun a =>
    Work.Peluse.boxNorm n (fun i : Fin n => Work.Peluse.arithIcc (c * ((a : ℤ) + b i)) M₂)
      (Work.Peluse.symIcc N) f with hp
  have hAcard : A.card = M₁ := by
    rw [hA, Nat.card_Icc]
    omega
  -- the weights are a probability measure on the residue classes
  have hwnn : ∀ r ∈ Rs, 0 ≤ w r := by
    intro r hr
    rw [hw]
    exact Work.Peluse.LadderP.p2Wt_nonneg c N r
  have hwsum : ∑ r ∈ Rs, w r = 1 := by
    rw [hRs, hw]
    exact Work.Peluse.LadderP.p2Wt_sum hc N
  -- the dilation-splitting identity, in the vocabulary of `y`
  have hsplit : ∀ a : ℕ,
      Work.Peluse.boxNormPow n
          (fun i : Fin n => Work.Peluse.arithIcc (c * ((a : ℤ) + b i)) M₂)
          (Work.Peluse.symIcc N) f
        = ∑ r ∈ Rs, w r * y a r := by
    intro a
    rw [Work.Peluse.LadderP.p2dilateSplit (t := n) (c := c) (q := fun i : Fin n => ((a : ℤ) + b i))
      (L := M₂) (N := N) (f := f) hn hc hM₂ hcN hfs]
    rw [hRs]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    simp only [hw, hy, Work.Peluse.LadderP.p2Wt, Work.Peluse.LadderP.p2Cls]
    rfl
  -- `y a r = (x a r) ^ (2 ^ n)` (`boxNorm` is the `2^n`-th root of `boxNormPow`)
  have hy_eq : ∀ a r : ℕ, (x a r) ^ (2 ^ n) = y a r := by
    intro a r
    rw [hx, hy]
    exact Work.Peluse.BoxNorm.boxNorm_pow n _ _ _
  -- the class norms lie in `[0,1]`, hence `y a r = (x a r)^(2^n) ≤ x a r`
  have hx0 : ∀ a ∈ A, ∀ r ∈ Rs, 0 ≤ x a r := by
    intro a ha r hr
    rw [hx]
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hx1 : ∀ a ∈ A, ∀ r ∈ Rs, x a r ≤ 1 := by
    intro a ha r hr
    have ha' : a ∈ Finset.Icc 1 M₁ := by rw [← hA]; exact ha
    have hr' : r ∈ Finset.range c.natAbs := by rw [← hRs]; exact hr
    rw [hx]
    exact hu1 a ha' r hr'
  have hyx : ∀ a ∈ A, ∀ r ∈ Rs, y a r ≤ x a r := by
    intro a ha r hr
    rw [← hy_eq a r]
    have h1 : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
    simpa using pow_le_pow_of_le_one (hx0 a ha r hr) (hx1 a ha r hr) h1
  -- the hypothesis `hp` of the abstract assembly
  have hp4 : ∀ a ∈ A, p a ^ (2 ^ n) ≤ ∑ r ∈ Rs, w r * x a r := by
    intro a ha
    have hpdef : p a
        = Work.Peluse.boxNorm n
            (fun i : Fin n => Work.Peluse.arithIcc (c * ((a : ℤ) + b i)) M₂)
            (Work.Peluse.symIcc N) f := by
      rw [hp]
    calc p a ^ (2 ^ n)
        = Work.Peluse.boxNormPow n
            (fun i : Fin n => Work.Peluse.arithIcc (c * ((a : ℤ) + b i)) M₂)
            (Work.Peluse.symIcc N) f := by
          rw [hpdef]
          exact Work.Peluse.BoxNorm.boxNorm_pow n _ _ _
      _ = ∑ r ∈ Rs, w r * y a r := hsplit a
      _ ≤ ∑ r ∈ Rs, w r * x a r :=
          Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hyx a ha r hr) (hwnn r hr))
  have hp0 : ∀ a ∈ A, 0 ≤ p a := by
    intro a ha
    rw [hp]
    exact Real.rpow_nonneg (norm_nonneg _) _
  -- the box average is `M₁⁻¹ ∑_a p a`
  have hboxA : γ ≤ ((M₁ : ℝ))⁻¹ * ∑ a ∈ A, p a := by
    have h := hbox
    rw [Work.Peluse.LadderQ.boxAvgA] at h
    rw [← hA] at h
    exact h
  -- the abstract assembly
  have hmain := powMeanAssembly hM₁ n hn A Rs w x p hAcard hwnn hwsum hp0 hp4 hγ0 hboxA
  -- identify the goal's right-hand side with the assembly's
  have hgoal : ∑ r ∈ Finset.range c.natAbs, Work.Peluse.LadderP.p2Wt c N r *
        Work.Peluse.LadderP.p3BoxAvg n M₁ M₂ b (Work.Peluse.LadderP.p2Cls c N r)
          (Work.Peluse.LadderP.p2ClsFn c r f)
      = ∑ r ∈ Rs, w r * (((M₁ : ℝ))⁻¹ * ∑ a ∈ A, x a r) := by
    rw [hRs]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [hA, hw, hx, Work.Peluse.LadderP.p3BoxAvg]
  rw [hgoal]
  exact hmain

end

end Work.LadderP
