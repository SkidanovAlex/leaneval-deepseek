import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_iterate_deriv_mul_ge
import Submission.Commons.FieldTheory.RatFunc.frobenius_order_ge
import Submission.Commons.FieldTheory.RatFunc.ordAtT_iterate_deriv_ge
import Submission.Commons.FieldTheory.RatFunc.le_ordAtT_finset_sum
import Submission.Commons.FieldTheory.RatFunc.ordAtT_add_eq_of_le_succ
import Submission.Commons.Algebra.Polynomial.dnum_def

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.Algebra.Polynomial
open Commons.FieldTheory.RatFunc

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

variable {K : Type*} [Field K]


noncomputable def linFactor (α : K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α)

lemma linFactor_ne_zero (α : K) : linFactor (K := K) α ≠ 0 :=
  RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero α)

lemma deriv_linFactor {D : Derivation K (RatFunc K) (RatFunc K)}
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative) (α : K) : D (linFactor (K := K) α) = 1 := by
  rw [linFactor, hd, Polynomial.derivative_X_sub_C, map_one]

lemma fallFact_succ (m : ℤ) (j : ℕ) : fallFact m (j + 1) = fallFact m j * (m - (j : ℤ)) := by
  simp [fallFact, Finset.prod_range_succ]

/-- `D^j (X - α)^m = (m)_j (X - α)^{m-j}`. -/
theorem iterate_deriv_linFactor_zpow {D : Derivation K (RatFunc K) (RatFunc K)}
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (α : K) (m : ℤ) (j : ℕ) :
    ((D : RatFunc K → RatFunc K)^[j]) (linFactor (K := K) α ^ m)
      = ((fallFact m j : ℤ) : RatFunc K) * linFactor (K := K) α ^ (m - j) := by
  induction j with
  | zero => simp [fallFact]
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        Derivation.map_intCast, mul_zero, add_zero]
      rw [Derivation.leibniz_zpow, deriv_linFactor hd α, smul_eq_mul, mul_one, zsmul_eq_mul]
      rw [fallFact_succ]
      push_cast
      ring_nf

/-- `ordAtT` of a `linFactor` power, nonnegative exponent. -/
theorem ordAtT_linFactor_zpow_nat (α : K) (n : ℕ) :
    ordAtT α (linFactor (K := K) α ^ (n : ℤ)) = ((n : ℤ) : WithTop ℤ) := by
  rw [zpow_natCast, linFactor, ← map_pow, ordAtT_X_sub_C_pow]

/-- `ordAtT` of a `linFactor` power. -/
theorem ordAtT_linFactor_zpow (α : K) (m : ℤ) :
    ordAtT α (linFactor (K := K) α ^ m) = (m : WithTop ℤ) := by
  have hZ : linFactor (K := K) α ≠ 0 := linFactor_ne_zero α
  by_cases hm : 0 ≤ m
  · have h : m = (((m.toNat : ℕ)) : ℤ) := (Int.toNat_of_nonneg hm).symm
    rw [h, ordAtT_linFactor_zpow_nat]
  · have hm' : m < 0 := not_le.mp hm
    have h : m = -((((-m).toNat : ℕ)) : ℤ) := by
      have h1 : ((((-m).toNat : ℕ)) : ℤ) = -m := Int.toNat_of_nonneg (by omega)
      omega
    rw [h, zpow_neg, ordAtT_inv _ (zpow_ne_zero _ hZ), ordAtT_linFactor_zpow_nat]
    push_cast
    ring_nf

/-- Multiplying a `linFactor` power by a constant polynomial does not lower its order. -/
theorem le_ordAtT_C_mul_linFactor_zpow (α : K) (a : K) (m : ℤ) :
    (m : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a) * linFactor (K := K) α ^ m) := by
  by_cases ha : a = 0
  · rw [ha, Polynomial.C_0, map_zero, zero_mul]
    simp [ordAtT]
  · have hC0 : (Polynomial.C a : Polynomial K) ≠ 0 := by rwa [Polynomial.C_ne_zero]
    have hC : algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a) ≠ 0 :=
      RatFunc.algebraMap_ne_zero hC0
    calc (m : WithTop ℤ)
        = ordAtT α (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a))
            + ordAtT α (linFactor (K := K) α ^ m) := by
          rw [ordAtT_algebraMap hC0, Polynomial.rootMultiplicity_C, ordAtT_linFactor_zpow]
          simp
      _ ≤ _ := ordAtT_mul_ge α _ _

/-- Constants (elements of `K`) are killed by `D`, so they commute with `D`. -/
lemma deriv_C_mul {D : Derivation K (RatFunc K) (RatFunc K)}
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative) (a : K) (x : RatFunc K) :
    D (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a) * x)
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a) * D x := by
  rw [Derivation.leibniz, hd (Polynomial.C a), Polynomial.derivative_C, map_zero,
    smul_eq_mul, smul_eq_mul, mul_zero, add_zero]

lemma iterate_deriv_C_mul {D : Derivation K (RatFunc K) (RatFunc K)}
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative) (a : K) (x : RatFunc K) (j : ℕ) :
    ((D : RatFunc K → RatFunc K)^[j])
        (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a) * x)
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a)
        * ((D : RatFunc K → RatFunc K)^[j]) x := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, deriv_C_mul hd, Function.iterate_succ_apply']

lemma iterate_map_sub (D : Derivation K (RatFunc K) (RatFunc K)) (j : ℕ) (x y : RatFunc K) :
    ((D : RatFunc K → RatFunc K)^[j]) (x - y)
      = ((D : RatFunc K → RatFunc K)^[j]) x - ((D : RatFunc K → RatFunc K)^[j]) y := by
  induction j with
  | zero => simp
  | succ j ih =>
      simp only [Function.iterate_succ_apply', ih, map_sub]

lemma intCast_eq_algebraMap_C (n : ℤ) :
    ((n : ℤ) : RatFunc K)
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C ((n : ℤ) : K)) := by
  rw [Polynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) ((n : ℤ) : K)]
  simp

lemma algebraMap_C_zsmul (s : ℤ) (a : K) :
    algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (s • a))
      = ((s : ℤ) : RatFunc K)
        * algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a) := by
  rw [zsmul_eq_mul, Polynomial.C_mul, map_mul, ← intCast_eq_algebraMap_C]

/-- **Indicial exactness, one derivative step.**  If `f − c·(X−α)^k` has order at least `k+1`,
then also `f^{(j)} − c·(k)_j·(X−α)^{k−j}` has order at least `k−j+1`. -/
theorem ordAtT_iterate_deriv_leading {D : Derivation K (RatFunc K) (RatFunc K)}
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    {α : K} {c : K} {f : RatFunc K} {k : ℤ}
    (hres : ((k + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (f - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c) * linFactor (K := K) α ^ k))
    (j : ℕ) :
    ((k - (j : ℤ) + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (((D : RatFunc K → RatFunc K)^[j]) f
        - algebraMap (Polynomial K) (RatFunc K)
            (Polynomial.C (c * ((fallFact k j : ℤ) : K))) * linFactor (K := K) α ^ (k - (j : ℤ))) := by
  set g : RatFunc K := f - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c)
      * linFactor (K := K) α ^ k with hg
  have key : ((D : RatFunc K → RatFunc K)^[j]) g
      = ((D : RatFunc K → RatFunc K)^[j]) f
        - algebraMap (Polynomial K) (RatFunc K)
            (Polynomial.C (c * ((fallFact k j : ℤ) : K))) * linFactor (K := K) α ^ (k - (j : ℤ)) := by
    rw [hg, iterate_map_sub, iterate_deriv_C_mul hd, iterate_deriv_linFactor_zpow hd,
      intCast_eq_algebraMap_C, ← mul_assoc, ← map_mul, ← Polynomial.C_mul]
  rw [← key]
  rcases eq_or_ne g 0 with hg0 | hg0
  · rw [hg0, Function.iterate_fixed (map_zero D)]
    simp [ordAtT]
  · have hg1 : ((k + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α g := by rw [hg]; exact hres
    have hk : (k + 1 : ℤ) ≤ ordAt α g := by
      rw [ordAtT_def α hg0] at hg1
      exact_mod_cast hg1
    refine le_trans ?_ (ordAtT_iterate_deriv_lower_bound D hd α hg0 j)
    rw [WithTop.coe_le_coe]
    omega

/-- **Indicial exactness: the product step.**  If `γ − λ (X−α)^e` and `f − r (X−α)^N` have order
at least `e+1` resp. `N+1`, then `γ f − λ r (X−α)^{N+e}` has order at least `N+e+1`. -/
theorem leading_residual_mul {α : K} {γ f : RatFunc K} {e N : ℤ} {lam r : K}
    (hγ : ((e + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (γ - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C lam) * linFactor (K := K) α ^ e))
    (hf : ordAtT α f = (N : WithTop ℤ))
    (hfr : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (f - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r) * linFactor (K := K) α ^ N)) :
    ((N + e + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (γ * f - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam * r))
        * linFactor (K := K) α ^ (N + e)) := by
  have hZ : linFactor (K := K) α ≠ 0 := linFactor_ne_zero α
  have hsplit : γ * f - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam * r))
        * linFactor (K := K) α ^ (N + e)
      = (γ - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C lam)
            * linFactor (K := K) α ^ e) * f
        + algebraMap (Polynomial K) (RatFunc K) (Polynomial.C lam) * linFactor (K := K) α ^ e
          * (f - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
              * linFactor (K := K) α ^ N) := by
    rw [show N + e = e + N by ring, zpow_add₀ hZ e N, Polynomial.C_mul, map_mul]
    ring
  rw [hsplit]
  refine le_trans (le_min ?_ ?_) (ordAtT_add_ge α _ _)
  · have heq : ((N + e + 1 : ℤ) : WithTop ℤ)
        = ((e + 1 : ℤ) : WithTop ℤ) + (N : WithTop ℤ) := by
      rw [← WithTop.coe_add]; congr 1; ring
    refine le_trans (le_of_eq heq) ?_
    exact le_trans (add_le_add hγ (le_of_eq hf.symm))
      (ordAtT_mul_ge α _ f)
  · have heq : ((N + e + 1 : ℤ) : WithTop ℤ)
        = (e : WithTop ℤ) + ((N + 1 : ℤ) : WithTop ℤ) := by
      rw [← WithTop.coe_add]; congr 1; ring
    refine le_trans (le_of_eq heq) ?_
    refine le_trans (add_le_add (le_ordAtT_C_mul_linFactor_zpow α lam e) hfr) ?_
    exact ordAtT_mul_ge α _ _

/-- **Indicial exactness, per index.**  The `j`-th derivative of `γ·f` has an explicit leading
term: `(γ·f)^{(j)} = λ r (N+e)_j (X−α)^{N+e−j} +` (higher order). -/
theorem ordAtT_iterate_deriv_mul_leading {D : Derivation K (RatFunc K) (RatFunc K)}
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    {α : K} {γ f : RatFunc K} {e N : ℤ} {lam r : K}
    (hγ : ((e + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (γ - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C lam) * linFactor (K := K) α ^ e))
    (hf : ordAtT α f = (N : WithTop ℤ))
    (hfr : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (f - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r) * linFactor (K := K) α ^ N))
    (j : ℕ) :
    ((N + e - (j : ℤ) + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (((D : RatFunc K → RatFunc K)^[j]) (γ * f)
        - algebraMap (Polynomial K) (RatFunc K)
            (Polynomial.C (lam * r * ((fallFact (N + e) j : ℤ) : K)))
          * linFactor (K := K) α ^ (N + e - (j : ℤ))) := by
  have h1 := leading_residual_mul (α := α) (γ := γ) (f := f) (e := e) (N := N)
    (lam := lam) (r := r) hγ hf hfr
  have h2 := ordAtT_iterate_deriv_leading (D := D) hd (α := α) (c := lam * r) (f := γ * f)
    (k := N + e) h1 j
  convert h2 using 3

/-- The order of a constant is nonnegative. -/
lemma zero_le_ordAtT_algebraMap_C (α : K) (a : K) :
    (0 : WithTop ℤ) ≤ ordAtT α (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a)) := by
  by_cases ha : a = 0
  · rw [ha, Polynomial.C_0, map_zero]; simp [ordAtT]
  · rw [ordAtT_algebraMap (by rwa [Polynomial.C_ne_zero]), Polynomial.rootMultiplicity_C]
    simp

/-- The order of an integer cast is nonnegative. -/
lemma zero_le_ordAtT_intCast (α : K) (n : ℤ) :
    (0 : WithTop ℤ) ≤ ordAtT α ((n : ℤ) : RatFunc K) := by
  rw [intCast_eq_algebraMap_C n]
  exact zero_le_ordAtT_algebraMap_C α _

/-- Multiplying by an integer constant does not lower the order. -/
lemma le_ordAtT_mul_intCast (α : K) (n : ℤ) (y : RatFunc K) :
    ordAtT α y ≤ ordAtT α (((n : ℤ) : RatFunc K) * y) := by
  have h0 : (0 : WithTop ℤ) ≤ ordAtT α (((n : ℤ) : RatFunc K)) := zero_le_ordAtT_intCast α n
  calc ordAtT α y = (0 : WithTop ℤ) + ordAtT α y := (zero_add _).symm
    _ ≤ ordAtT α (((n : ℤ) : RatFunc K)) + ordAtT α y := add_le_add_left h0 _
    _ ≤ ordAtT α (((n : ℤ) : RatFunc K) * y) := ordAtT_mul_ge α _ _

/-- The exact indicial order of the "adjoint expression" `Σᵢ (−1)ⁱ Dⁱ(γᵢ·b)`.

Let `K` be a field, `D : Derivation K K(X) K(X)` the standard derivation, `α : K`.  Suppose
`b ≠ 0` with `ord_α b = N` and `N`-leading coefficient `r ≠ 0`, and `γᵢ ≠ 0` with
`ord_α γᵢ = eᵢ` and `(eᵢ)`-leading coefficient `λᵢ` (all of these encoded as second-order
"residual" bounds, the standard formalisation of a leading coefficient).  Let `m` be a lower
bound for all `eᵢ − i`.  If the *indicial value*
`Σ_{i : eᵢ−i=m} (−1)ⁱ λᵢ (N+eᵢ)ᵢ` is non-zero (the product being the falling factorial
`∏_{j<i}(N+eᵢ−j)` in `K`), then the order of the whole expression is exactly `N + m`.

Proof: `Dⁱ(γᵢb) = Σ_{k≤i} C(i,k) Dᵏ(γᵢ) D^{i−k}(b)`, whose leading term (order
`eᵢ+N−i`, coefficient `λᵢ r (N+eᵢ)ᵢ`) survives exactly for the indices `i` with `eᵢ−i = m`;
the remaining terms have strictly higher order.  So the coefficient of `(X−α)^{N+m}` is
`r` times the indicial value, which is non-zero.

This is the "indicial exactness" half of the local analysis at a singularity of the CDT
systems (`(onceagain)` of arXiv:2408.15403 §"Products of two logarithms" and the Theorem-A
analogue); combined with `ordAtT_iterate_deriv_mul_ge` (the `≥` half) and
`adjoint_of_firstOrder_system` (the elimination) it yields the local pole-order bounds
`N₀ ≥ 0, N₄ ≥ 2, N_β ≥ 1, N_γ ≥ −1, N_∞ ≤ 5`. -/
theorem ordAtT_adjoint_eq_of_indicial {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (α : K) (b : RatFunc K) (hb : b ≠ 0) (N : ℤ) (hN : ordAt α b = N) (r : K)
    (hr : r ≠ 0)
    (hb' : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (b - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C r)
        * (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ N))
    (γ : Fin 5 → RatFunc K) (e : Fin 5 → ℤ) (lam : Fin 5 → K) (m : ℤ)
    (he : ∀ i, ordAt α (γ i) = e i)
    (hm : ∀ i, m ≤ e i - ((i : ℕ) : ℤ))
    (hlam : ∀ i, (((e i + 1 : ℤ)) : WithTop ℤ) ≤ ordAtT α
      (γ i - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i))
        * (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ (e i)))
    (hP : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = m),
        (-1 : ℤ) ^ (i : ℕ) • (lam i * ∏ j ∈ Finset.range (i : ℕ), ((N + e i - (j : ℤ) : ℤ) : K))) ≠ 0) :
    ordAtT α (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) •
      ((fun x : RatFunc K => D x)^[i] (γ i * b)))
      = ((N + m : ℤ) : WithTop ℤ) := by
  classical
  have hprod : ∀ i : Fin 5, (∏ j ∈ Finset.range (i : ℕ), ((N + e i - (j : ℤ) : ℤ) : K))
      = ((fallFact (N + e i) ((i : ℕ)) : ℤ) : K) := by
    intro i
    simp only [fallFact, Int.cast_prod]
  have hPne : (∑ i ∈ Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = m),
      (-1 : ℤ) ^ (i : ℕ) • (lam i * ((fallFact (N + e i) ((i : ℕ)) : ℤ) : K))) ≠ 0 := by
    simpa only [hprod] using hP
  let FF : Fin 5 → K := fun i => ((fallFact (N + e i) ((i : ℕ)) : ℤ) : K)
  let F : Finset (Fin 5) := Finset.univ.filter (fun i : Fin 5 => e i - ((i : ℕ) : ℤ) = m)
  let V : K := ∑ i ∈ F, (-1 : ℤ) ^ (i : ℕ) • (lam i * FF i)
  have hVne : V ≠ 0 := hPne
  let c : Fin 5 → K := fun i => (-1 : ℤ) ^ (i : ℕ) • (lam i * r * FF i)
  let T : Fin 5 → RatFunc K := fun i =>
      (-1 : ℤ) ^ (i : ℕ) • ((fun x : RatFunc K => D x)^[i] (γ i * b))
  let W : RatFunc K := algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (r * V))
      * linFactor (K := K) α ^ (N + m)
  let g : Fin 5 → RatFunc K := fun i => if e i - ((i : ℕ) : ℤ) = m then
      T i - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (c i))
        * linFactor (K := K) α ^ (N + m) else T i
  -- Per-index expansion.
  have hExp : ∀ i : Fin 5, ((N + e i - ((i : ℕ) : ℤ) + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (((fun x : RatFunc K => D x)^[i]) (γ i * b)
        - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i * r * FF i))
          * linFactor (K := K) α ^ (N + e i - ((i : ℕ) : ℤ))) := by
    intro i
    have hf : ordAtT α b = (N : WithTop ℤ) := by rw [ordAtT_def α hb, hN]
    exact ordAtT_iterate_deriv_mul_leading (D := D) hd (α := α) (γ := γ i) (f := b)
      (e := e i) (N := N) (lam := lam i) (r := r) (hlam i) hf hb' (i : ℕ)
  -- Bound on each `g i`.
  have hgle : ∀ i : Fin 5, ((N + m + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α (g i) := by
    intro i
    by_cases hcond : e i - ((i : ℕ) : ℤ) = m
    · have hexp : ((N + m + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
          (((fun x : RatFunc K => D x)^[i]) (γ i * b)
            - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i * r * FF i))
              * linFactor (K := K) α ^ (N + m)) := by
        have h := hExp i
        have heq : N + e i - ((i : ℕ) : ℤ) = N + m := by omega
        rwa [heq] at h
      have hgi : g i = (((-1 : ℤ) ^ (i : ℕ) : ℤ) : RatFunc K)
          * ((((fun x : RatFunc K => D x)^[i]) (γ i * b)
            - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (lam i * r * FF i))
              * linFactor (K := K) α ^ (N + m))) := by
        have hgu : g i = T i - algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (c i))
            * linFactor (K := K) α ^ (N + m) := by
          simp only [g]
          exact if_pos hcond
        rw [hgu, show c i = (-1 : ℤ) ^ (i : ℕ) • (lam i * r * FF i) from rfl,
          algebraMap_C_zsmul]
        simp only [T, zsmul_eq_mul]
        ring
      rw [hgi]
      have h0 : (0 : WithTop ℤ) ≤ ordAtT α (((-1 : ℤ) ^ (i : ℕ) : ℤ) : RatFunc K) :=
        zero_le_ordAtT_intCast α _
      refine le_trans (le_of_eq ?_)
        (le_trans (add_le_add h0 hexp) (ordAtT_mul_ge α _ _))
      rw [zero_add]
    · have hexp : ((N + m + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
          (((fun x : RatFunc K => D x)^[i]) (γ i * b)) := by
        rcases eq_or_ne (((fun x : RatFunc K => D x)^[i]) (γ i * b)) 0 with h0 | h0
        · rw [h0]; simp [ordAtT]
        · rw [ordAtT_def α h0, WithTop.coe_le_coe]
          have hγne : γ i ≠ 0 := by
            intro hγ0
            exact h0 (by rw [hγ0, zero_mul, Function.iterate_fixed (map_zero D)])
          have hge := ordAtT_iterate_deriv_mul_ge (D := D) hd α (γ i) b hb (i : ℕ)
          rw [ordAtT_def α hγne, he i, hN, ordAtT_def α h0] at hge
          have h1 : (((e i : ℤ) + N - ((i : ℕ) : ℤ) : ℤ) : WithTop ℤ)
              ≤ ((ordAt α (((fun x : RatFunc K => D x)^[i]) (γ i * b)) : ℤ) : WithTop ℤ) := by
            rw [WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.coe_add]
            exact hge
          have h2 : (e i : ℤ) + N - ((i : ℕ) : ℤ)
              ≤ ordAt α (((fun x : RatFunc K => D x)^[i]) (γ i * b)) :=
            WithTop.coe_le_coe.mp h1
          have := hm i
          omega
      have h2 : ordAtT α (((fun x : RatFunc K => D x)^[i]) (γ i * b)) ≤ ordAtT α (T i) := by
        have hTi : T i = (((-1 : ℤ) ^ (i : ℕ) : ℤ) : RatFunc K)
            * (((fun x : RatFunc K => D x)^[i]) (γ i * b)) := by
          simp only [T, zsmul_eq_mul]
        rw [hTi]
        exact le_ordAtT_mul_intCast α _ _
      rw [show g i = T i from by
        simp only [g]
        exact if_neg hcond]
      exact le_trans hexp h2
  -- The sum identity.
  have hcV : (∑ i ∈ F, c i) = r * V := by
    show (∑ i ∈ F, (-1 : ℤ) ^ (i : ℕ) • (lam i * r * FF i))
      = r * (∑ i ∈ F, (-1 : ℤ) ^ (i : ℕ) • (lam i * FF i))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [zsmul_eq_mul]
    ring
  have hsum : (∑ i : Fin 5, g i) = (∑ i : Fin 5, T i) - W := by
    have hg' : ∀ i : Fin 5, g i = T i - (if e i - ((i : ℕ) : ℤ) = m then
        algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (c i))
          * linFactor (K := K) α ^ (N + m) else 0) := by
      intro i
      by_cases h : e i - ((i : ℕ) : ℤ) = m <;> simp [g, h]
    rw [Finset.sum_congr rfl (fun i _ => hg' i), Finset.sum_sub_distrib]
    congr 1
    show (∑ i : Fin 5, (if e i - ((i : ℕ) : ℤ) = m then
        algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (c i))
          * linFactor (K := K) α ^ (N + m) else 0)) = W
    show _ = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (r * V))
        * linFactor (K := K) α ^ (N + m)
    rw [← Finset.sum_filter, ← Finset.sum_mul]
    congr 1
    rw [← map_sum (algebraMap (Polynomial K) (RatFunc K)) (fun i => Polynomial.C (c i)) _]
    congr 1
    simp only [Polynomial.C_eq_algebraMap]
    rw [← map_sum (algebraMap K (Polynomial K)) (fun i => c i) _, hcV]
  -- Order of the leading term.
  have hW : ordAtT α W = ((N + m : ℤ) : WithTop ℤ) := by
    show ordAtT α (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (r * V))
        * linFactor (K := K) α ^ (N + m)) = _
    have hC0 : (Polynomial.C (r * V) : Polynomial K) ≠ 0 := by
      rw [Polynomial.C_ne_zero]; exact mul_ne_zero hr hVne
    have hC : algebraMap (Polynomial K) (RatFunc K) (Polynomial.C (r * V)) ≠ 0 :=
      RatFunc.algebraMap_ne_zero hC0
    rw [ordAtT_mul α hC (zpow_ne_zero _ (linFactor_ne_zero α)), ordAtT_algebraMap hC0,
      Polynomial.rootMultiplicity_C, ordAtT_linFactor_zpow]
    simp
  -- Finish.
  have hgl : ((N + m + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α (∑ i : Fin 5, g i) :=
    le_ordAtT_finset_sum (fun i _ => hgle i)
  have hsum' : (∑ i : Fin 5, T i) = W + ∑ i : Fin 5, g i := by
    rw [hsum]; abel
  change ordAtT α (∑ i : Fin 5, T i) = ((N + m : ℤ) : WithTop ℤ)
  rw [hsum']
  exact ordAtT_add_eq_of_le_succ hW hgl


end Commons.FieldTheory.RatFunc
