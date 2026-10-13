/-
  WilG4c / Engine — the analytic engine of BNZ §5.4 (`StepHigher`).

  BNZ §5.4 controls the higher derivatives of a `1`-Lipschitz family with unit `y`-derivatives
  by pulling back along affine `x`-charts (BNZ Corollary 19 = our `F1Affine`), taking a curve
  `t ↦ (t, γ t)` through a near-maximiser `γ` of each mixed derivative, and running an
  induction on the number of `x`-derivatives (BNZ Lemma 22).  This file isolates the two
  analytic ingredients of that step, so that the (heavy) definability bookkeeping can be
  done against a stable interface:

  * `iterDir L G` — the iterated directional derivative of `G` along the list of directions
    `L` (`iterDir [i,j] G = ∂ᵢ∂ⱼG`), and the curve `curveFun γ t = (t, γ t)` in the `(x,y)`
    splitting of `Fin (n+1) → ℝ`.  The chain rule along the curve is
    `hasDerivAt_iterDir_curve`.
  * `tnorm_curve_system` — BNZ Lemma 22 in abstract form: an index `(j, M)` (`j` = number of
    `x`-derivatives, `M` = list of `y`-directions) with the chain-rule relation
    `u (j+1) M = (u j M)' - Σᵢ (u j (i::M)) · γᵢ'` gives the bound
    `tnorm (r-j) (u j M) ≤ e · (r (1 + n e))^j` by induction on `j`.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.Norm
import Submission.Work.WilG2.Tnorm

set_option autoImplicit false
noncomputable section
open Classical Finset

open scoped BigOperators

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Iterated directional derivatives and the curve `t ↦ (t, γ t)` -/

/-- The iterated directional derivative along a list of directions: `iterDir (i :: L) f` is the
derivative of `iterDir L f` in the direction `i`, so the *head* of the list is the outermost
derivative. -/
def iterDir {m : ℕ} : List (Fin m) → ((Fin m → ℝ) → ℝ) → ((Fin m → ℝ) → ℝ)
  | [], f => f
  | i :: L, f => fun z => fderiv ℝ (iterDir L f) z (Pi.single i 1)

@[simp] theorem iterDir_nil {m : ℕ} (f : (Fin m → ℝ) → ℝ) : iterDir [] f = f := rfl

theorem iterDir_cons {m : ℕ} (i : Fin m) (L : List (Fin m)) (f : (Fin m → ℝ) → ℝ) :
    iterDir (i :: L) f = fun z => fderiv ℝ (iterDir L f) z (Pi.single i 1) := rfl

/-- `iterDir` is compatible with concatenation: the left list is applied last. -/
theorem iterDir_append {m : ℕ} (L₁ L₂ : List (Fin m)) (f : (Fin m → ℝ) → ℝ) :
    iterDir (L₁ ++ L₂) f = iterDir L₁ (iterDir L₂ f) := by
  induction L₁ with
  | nil => rfl
  | cons i L ih => simp only [List.cons_append, iterDir_cons, ih]

/-- The curve `t ↦ (t, γ t)` in the `(x,y)` splitting of `Fin (n+1) → ℝ`. -/
def curveFun {n : ℕ} (γ : ℝ → Fin n → ℝ) (t : ℝ) : Fin (n + 1) → ℝ := pt t (γ t)

@[simp] theorem curveFun_zero {n : ℕ} (γ : ℝ → Fin n → ℝ) (t : ℝ) : curveFun γ t 0 = t :=
  pt_zero t (γ t)

@[simp] theorem curveFun_succ {n : ℕ} (γ : ℝ → Fin n → ℝ) (t : ℝ) (j : Fin n) :
    curveFun γ t j.succ = γ t j :=
  pt_succ t (γ t) j

/-! The chain rule along the curve `t ↦ (t, γ t)` — differentiating `t ↦ ∂^L G (t, γ t)`
produces the derivative in the `x`-direction (the extra `0` at the head of the list) plus, for
each `y`-coordinate, the extra `y`-derivative times `γ_j'` — is proved as
`Work.WilkG4c.hasDerivAt_iterDir_curve` in the sibling module
`Submission.Work.WilG4c.hasDerivAt_iterDir_curve` (proved; import it where needed).  It is kept
out of this file so that the engine itself depends only on Mathlib and the frozen vocabulary. -/

/-! ## 2. Jet-norm estimates for one-variable functions -/

/-- **The derivative lowers the order of the jet norm.**  For a function of one real variable,
`tnorm s f' x ≤ (s+1) * tnorm (s+1) f x`: the `k`-th Taylor coefficient of `f'` is the
`(k+1)`-st Taylor coefficient of `f` (`norm_iteratedFDeriv_eq_norm_iteratedDeriv`,
`iteratedDeriv_succ`). -/
theorem tnorm_deriv_le (s : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    tnorm s (fun y => deriv f y) x ≤ ((s : ℝ) + 1) * tnorm (s + 1) f x := by
  rw [tnorm_eq_sum_jetCoeff, tnorm_eq_sum_jetCoeff]
  have h₁ : ∀ k ∈ Finset.range (s + 1),
      jetCoeff k (fun y => deriv f y) x ≤ ((k : ℝ) + 1) * jetCoeff (k + 1) f x := by
    intro k _
    have hfac : 0 < ((k.factorial : ℝ)) := by exact_mod_cast Nat.factorial_pos k
    have hfac' : 0 < (((k + 1).factorial : ℝ)) := by exact_mod_cast Nat.factorial_pos (k + 1)
    rw [jetCoeff, jetCoeff]
    have hnorm : ‖iteratedFDeriv ℝ k (fun y => deriv f y) x‖ ≤
        ‖iteratedFDeriv ℝ (k + 1) f x‖ := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ']
    calc ‖iteratedFDeriv ℝ k (fun y => deriv f y) x‖ / (k.factorial : ℝ)
        ≤ ‖iteratedFDeriv ℝ (k + 1) f x‖ / (k.factorial : ℝ) :=
          div_le_div_of_nonneg_right hnorm hfac.le
      _ = ((k : ℝ) + 1) * (‖iteratedFDeriv ℝ (k + 1) f x‖ / (((k + 1).factorial : ℝ))) := by
          have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
          have hkf : ((k.factorial : ℝ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
          rw [Nat.factorial_succ]
          push_cast
          field_simp
  calc (∑ k ∈ Finset.range (s + 1), jetCoeff k (fun y => deriv f y) x)
      ≤ ∑ k ∈ Finset.range (s + 1), ((k : ℝ) + 1) * jetCoeff (k + 1) f x :=
        Finset.sum_le_sum h₁
    _ ≤ ((s : ℝ) + 1) * ∑ k ∈ Finset.range (s + 1), jetCoeff (k + 1) f x := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hk'' : (k : ℝ) + 1 ≤ (s : ℝ) + 1 := by
          exact_mod_cast Nat.succ_le_succ hk'
        exact mul_le_mul_of_nonneg_right hk'' (jetCoeff_nonneg (k + 1) f x)
    _ ≤ ((s : ℝ) + 1) * ∑ k ∈ Finset.range (s + 2), jetCoeff k f x := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hsub : (Finset.range (s + 1)).image (· + 1) ⊆ Finset.range (s + 2) := by
          intro k hk
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
          simp only [Finset.mem_range] at hj ⊢
          omega
        calc ∑ k ∈ Finset.range (s + 1), jetCoeff (k + 1) f x
            = ∑ k ∈ (Finset.range (s + 1)).image (· + 1), jetCoeff k f x := by
              rw [Finset.sum_image]
              intro a _ b _ hab
              exact Nat.add_right_cancel hab
          _ ≤ ∑ k ∈ Finset.range (s + 2), jetCoeff k f x :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => jetCoeff_nonneg k f x

/-- The jet norm is bounded by a uniform bound on the derivative norms at the point. -/
theorem tnorm_le_mul_exp (r : ℕ) (f : ℝ → ℝ) (x : ℝ) (C : ℝ)
    (hC : ∀ m ≤ r, ‖iteratedFDeriv ℝ m f x‖ ≤ C) :
    tnorm r f x ≤ (∑ k ∈ Finset.range (r + 1), (1 : ℝ) / k.factorial) * C := by
  rw [tnorm_eq_sum_jetCoeff, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [jetCoeff, div_eq_inv_mul, one_div]
  exact mul_le_mul_of_nonneg_left (hC k hk') (inv_nonneg.mpr (Nat.cast_nonneg k.factorial))

/-- The jet norm of a function whose derivative norms up to order `r` are `≤ 1` is `≤ e`. -/
theorem tnorm_le_exp_of_le_one (r : ℕ) (f : ℝ → ℝ) (x : ℝ)
    (h : ∀ m ≤ r, ‖iteratedFDeriv ℝ m f x‖ ≤ 1) : tnorm r f x ≤ Real.exp 1 := by
  refine (tnorm_le_mul_exp r f x 1 h).trans ?_
  have hsum : (∑ k ∈ Finset.range (r + 1), (1 : ℝ) / k.factorial) ≤ Real.exp 1 := by
    have hsummable : Summable (fun k : ℕ => (1 : ℝ) ^ k / k.factorial) :=
      Real.summable_pow_div_factorial 1
    have hle := hsummable.sum_le_tsum (Finset.range (r + 1)) (fun k _ => by positivity)
    have htsum : (∑' k : ℕ, (1 : ℝ) ^ k / k.factorial) = Real.exp 1 := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [htsum] at hle
    simpa using hle
  simpa using hsum

/-! ## 3. BNZ Lemma 22, in abstract form -/

/-- **BNZ Lemma 22 (abstract induction).**  Let `u j M` be the function `t ↦ ∂_x^j ∂_M G(t,γ t)`
along a curve, where `M` is a list of `y`-directions, and let `gd i` be `γᵢ'`.

Inputs:
* `hbase`: the pure-`y` derivatives (`j = 0`) have jet norm `≤ e` up to order `r` — this is the
  input supplied by BNZ's Corollary 19 (our `F1Affine`), applied to the tuple of curves;
* `hchain`: the chain rule `u (j+1) M = (u j M)' - Σᵢ u j (i::M) · γᵢ'` for the jet norms;
* `hgd`: `γᵢ'` is bounded by `1` in all derivative norms up to order `r`;
* smoothness of the functions involved at `t`.

Conclusion: `tnorm (r-j) (u j M) t ≤ e · (r(1 + n e))^j` for all `M` with
`M.length + j ≤ r`.  The factor `r · (1 + n e)` per `x`-derivative is exactly
`r` (from `tnorm_deriv_le`) plus `n · r · e` (from the `n` products with `γᵢ'`). -/
theorem tnorm_curve_system {n r : ℕ} (u : ℕ → List (Fin n) → ℝ → ℝ) (gd : Fin n → ℝ → ℝ)
    (t : ℝ)
    (hsm : ∀ j M, M.length + j ≤ r → ContDiffAt ℝ r (u j M) t)
    (hsmg : ∀ i : Fin n, ContDiffAt ℝ r (gd i) t)
    (hbase : ∀ M, M.length ≤ r → tnorm r (u 0 M) t ≤ Real.exp 1)
    (hchain : ∀ j M, M.length + (j + 1) ≤ r →
      tnorm (r - (j + 1)) (u (j + 1) M) t ≤
        tnorm (r - (j + 1)) (fun s => deriv (u j M) s) t +
        ∑ i : Fin n, tnorm (r - (j + 1)) (fun s => u j (i :: M) s * gd i s) t)
    (hgd : ∀ i : Fin n, ∀ m ≤ r, ‖iteratedFDeriv ℝ m (gd i) t‖ ≤ 1) :
    ∀ j M, M.length + j ≤ r →
      tnorm (r - j) (u j M) t ≤ Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro M hM
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simpa using hbase M (by simpa using hM)
    · obtain ⟨j₀, rfl⟩ : ∃ j₀, j = j₀ + 1 := ⟨j - 1, by omega⟩
      have hj₀ : M.length + j₀ ≤ r := by omega
      have hj₀r : j₀ + 1 ≤ r := by omega
      -- bounds for the derivative term and for the product terms
      have hderiv : tnorm (r - (j₀ + 1)) (fun s => deriv (u j₀ M) s) t ≤
          (r : ℝ) * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) := by
        refine (tnorm_deriv_le (r - (j₀ + 1)) (u j₀ M) t).trans ?_
        have hstep : ((r - (j₀ + 1) : ℕ) : ℝ) + 1 ≤ (r : ℝ) := by
          have : r - (j₀ + 1) + 1 ≤ r := by omega
          exact_mod_cast this
        have hih := ih j₀ (by omega) M hj₀
        have hmono : tnorm (r - (j₀ + 1) + 1) (u j₀ M) t ≤
            Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀ := by
          have heq : r - (j₀ + 1) + 1 = r - j₀ := by omega
          rw [heq]
          exact hih
        calc (((r - (j₀ + 1) : ℕ) : ℝ) + 1) * tnorm (r - (j₀ + 1) + 1) (u j₀ M) t
            ≤ (r : ℝ) * tnorm (r - (j₀ + 1) + 1) (u j₀ M) t :=
              mul_le_mul_of_nonneg_right hstep (tnorm_nonneg _ _ _)
          _ ≤ (r : ℝ) * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) :=
              mul_le_mul_of_nonneg_left hmono (by positivity)
      have hprod : ∀ i : Fin n, tnorm (r - (j₀ + 1)) (fun s => u j₀ (i :: M) s * gd i s) t ≤
          (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) * Real.exp 1 := by
        intro i
        have hlenM : (i :: M).length + j₀ ≤ r := by simp; omega
        have hih := ih j₀ (by omega) (i :: M) hlenM
        have hmul := G2_tnorm_mul_proved (r - (j₀ + 1)) (u j₀ (i :: M)) (gd i) t
          ((hsm j₀ (i :: M) hlenM).of_le (by exact_mod_cast Nat.sub_le r (j₀ + 1)))
          ((hsmg i).of_le (by exact_mod_cast Nat.sub_le r (j₀ + 1)))
        refine hmul.trans ?_
        have h1 : tnorm (r - (j₀ + 1)) (u j₀ (i :: M)) t ≤
            Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀ :=
          (tnorm_mono (by omega) _ t).trans hih
        have h2 : tnorm (r - (j₀ + 1)) (gd i) t ≤ Real.exp 1 :=
          (tnorm_mono (by omega) _ t).trans (tnorm_le_exp_of_le_one r (gd i) t (hgd i))
        exact mul_le_mul h1 h2 (tnorm_nonneg _ _ _) (by positivity)
      have hsum : (∑ i : Fin n, tnorm (r - (j₀ + 1)) (fun s => u j₀ (i :: M) s * gd i s) t) ≤
          (n : ℝ) * ((Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) * Real.exp 1) := by
        calc (∑ i : Fin n, tnorm (r - (j₀ + 1)) (fun s => u j₀ (i :: M) s * gd i s) t)
            ≤ ∑ _i : Fin n, (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) * Real.exp 1 :=
              Finset.sum_le_sum fun i _ => hprod i
          _ = (n : ℝ) * ((Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) * Real.exp 1) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hfin : (r : ℝ) * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) +
            (n : ℝ) * ((Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) * Real.exp 1) ≤
          Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ (j₀ + 1) := by
        have hr1 : (1 : ℝ) ≤ r := by
          have : 1 ≤ r := by omega
          exact_mod_cast this
        have hne : (0 : ℝ) ≤ (n : ℝ) * Real.exp 1 := by positivity
        set X : ℝ := (r * (1 + n * Real.exp 1)) ^ j₀ with hX
        have hX0 : 0 ≤ X := by rw [hX]; positivity
        have hexp0 : 0 < Real.exp 1 := Real.exp_pos 1
        have hineq : r + (n : ℝ) * Real.exp 1 ≤ r * (1 + n * Real.exp 1) := by
          nlinarith [hr1, hne, mul_nonneg (sub_nonneg.mpr hr1) hne]
        calc (r : ℝ) * (Real.exp 1 * X) + (n : ℝ) * ((Real.exp 1 * X) * Real.exp 1)
            = (Real.exp 1 * X) * (r + (n : ℝ) * Real.exp 1) := by ring
          _ ≤ (Real.exp 1 * X) * (r * (1 + n * Real.exp 1)) :=
              mul_le_mul_of_nonneg_left hineq (by positivity)
          _ = Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ (j₀ + 1) := by
              rw [hX, pow_succ]; ring
      calc tnorm (r - (j₀ + 1)) (u (j₀ + 1) M) t
          ≤ tnorm (r - (j₀ + 1)) (fun s => deriv (u j₀ M) s) t +
            ∑ i : Fin n, tnorm (r - (j₀ + 1)) (fun s => u j₀ (i :: M) s * gd i s) t :=
            hchain j₀ M (by omega)
        _ ≤ (r : ℝ) * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) +
            (n : ℝ) * ((Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) * Real.exp 1) :=
            add_le_add hderiv hsum
        _ ≤ Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ (j₀ + 1) := hfin

end Work.WilkG4c
