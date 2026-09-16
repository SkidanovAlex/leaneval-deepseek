import Mathlib
import Submission.Theorem35i
import Submission.LamDivSum
import Submission.DHLCriterion

open scoped BigOperators Topology
open Finset Filter

set_option maxHeartbeats 4000000

/-!
# The tensor-product sieve weight (Polymath8a §5.2)

Polymath8a (18)/(85) uses the sieve weight

    `ν(n) = (Σ_{j<J} c_j·λ_{f_{1,j}}(n+h_1)···λ_{f_{k,j}}(n+h_k))²`.

This module records the two expansions that turn `Σν` and `Σνθ` into finite
combinations of the objects covered by `theorem36_i` (non-prime sums) and
`theorem35_i` (prime sums), together with the prime collapse `lamDivSum_prime`
of Polymath8a (20).
-/

namespace Commons.NumberTheory.MaynardSieve

attribute [local instance] Classical.propDecidable

/-- `∏ᵢ λ_{fᵢ}(n + Hᵢ)`. -/
noncomputable def prodLamDivSum {k : ℕ} (f : Fin k → ℝ → ℝ) (N D : ℕ) (H : Fin k → ℕ)
    (n : ℕ) : ℝ :=
  ∏ i : Fin k, lamDivSum (f i) N D (n + H i)

/-- The tensor-product combination `Σ_j c_j ∏ᵢ λ_{f_{j,i}}(n + Hᵢ)` (Polymath8a (18)). -/
noncomputable def tpWeight {k J : ℕ} (c : Fin J → ℝ) (f : Fin J → Fin k → ℝ → ℝ)
    (N D : ℕ) (H : Fin k → ℕ) (n : ℕ) : ℝ :=
  ∑ j : Fin J, c j * prodLamDivSum (f j) N D H n

/-- `Σ_{n ∈ window} ∏ᵢ λ_{fᵢ}(n+Hᵢ)·∏ᵢ λ_{gᵢ}(n+Hᵢ)` is the window divisor product of
`Submission.Theorem36i`. -/
theorem sum_prodLamDivSum_mul {k : ℕ} (f g : Fin k → ℝ → ℝ) (H : Fin k → ℕ)
    (W b D N : ℕ) :
    (∑ n ∈ residueWindow N W b,
        (∏ i : Fin k, lamDivSum (f i) N D (n + H i)) *
        (∏ i : Fin k, lamDivSum (g i) N D (n + H i))) =
      windowDivisorProduct f g H W b D N := by
  rw [residueWindow, windowDivisorProduct]
  simp only [lamDivSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.prod_mul_distrib]

/-- **The square expansion for `S₁` (Polymath8a (13)).** -/
theorem weightSum_tpWeight_sq {k J : ℕ} (c : Fin J → ℝ) (f : Fin J → Fin k → ℝ → ℝ)
    (H : Fin k → ℕ) (W b D N : ℕ) :
    weightSum W b N (fun n => (tpWeight c f N D H n) ^ 2) =
      ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
        windowDivisorProduct (f j) (f j') H W b D N := by
  rw [weightSum]
  have hpt : ∀ n ∈ residueWindow N W b, (tpWeight c f N D H n) ^ 2 =
      ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
        ((∏ i : Fin k, lamDivSum (f j i) N D (n + H i)) *
         (∏ i : Fin k, lamDivSum (f j' i) N D (n + H i))) := by
    intro n _
    rw [tpWeight, sq, Finset.sum_mul_sum]
    simp only [prodLamDivSum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    ring
  rw [Finset.sum_congr rfl hpt]
  have hswap : (∑ n ∈ residueWindow N W b, ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
        ((∏ i : Fin k, lamDivSum (f j i) N D (n + H i)) *
         (∏ i : Fin k, lamDivSum (f j' i) N D (n + H i)))) =
      ∑ j : Fin J, ∑ j' : Fin J, ∑ n ∈ residueWindow N W b, c j * c j' *
        ((∏ i : Fin k, lamDivSum (f j i) N D (n + H i)) *
         (∏ i : Fin k, lamDivSum (f j' i) N D (n + H i))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
  rw [hswap]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact sum_prodLamDivSum_mul (f j) (f j') H W b D N

/-- **The square expansion for `S₂` (Polymath8a (14)).**  On the primes
`n + H i₀` the factor `λ_{f_{j,i₀}}(n + H i₀)` collapses to `f_{j,i₀}(0)` by
Polymath8a (20), leaving a `(k-1)`-fold divisor product. -/
theorem thetaWeightSum_tpWeight_sq {J n : ℕ} (c : Fin J → ℝ)
    (f : Fin J → Fin (n + 1) → ℝ → ℝ) (H : Fin (n + 1) → ℕ) (i₀ : Fin (n + 1))
    (W b D N : ℕ) (hD : 1 ≤ D) (hR : 1 < N)
    (hfb : ∀ (j : Fin J) (l : Fin (n + 1)) (t : ℝ), 1 ≤ t → f j l t = 0) :
    thetaWeightSum W b N (fun m => (tpWeight c f N D H m) ^ 2) (H i₀) =
      ∑ j : Fin J, ∑ j' : Fin J, c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
        thetaWindowSum N W b (H i₀) D (fun a => H (i₀.succAbove a))
          (fun a => lamDivWeight (f j (i₀.succAbove a)) N)
          (fun a => lamDivWeight (f j' (i₀.succAbove a)) N) := by
  rw [thetaWeightSum]
  have hsplit : ∀ (j : Fin J) (m : ℕ),
      (∏ i : Fin (n + 1), lamDivSum (f j i) N D (m + H i)) =
        lamDivSum (f j i₀) N D (m + H i₀) *
          ∏ a : Fin n, lamDivSum (f j (i₀.succAbove a)) N D (m + H (i₀.succAbove a)) :=
    fun j m => Fin.prod_univ_succAbove (fun i => lamDivSum (f j i) N D (m + H i)) i₀
  have hcollapse : ∀ (j : Fin J) (m : ℕ), (m + H i₀).Prime → N ≤ m →
      lamDivSum (f j i₀) N D (m + H i₀) = f j i₀ 0 := by
    intro j m hpr hm
    exact lamDivSum_prime hpr (by omega) hR hD (hfb j i₀)
  have hexp : ∀ (m : ℕ), (tpWeight c f N D H m) ^ 2 =
      ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
        ((∏ i : Fin (n + 1), lamDivSum (f j i) N D (m + H i)) *
         (∏ i : Fin (n + 1), lamDivSum (f j' i) N D (m + H i))) := by
    intro m
    rw [tpWeight, sq, Finset.sum_mul_sum]
    simp only [prodLamDivSum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    ring
  have hpt : ∀ m ∈ residueWindow N W b,
      (tpWeight c f N D H m) ^ 2 * thetaNat (m + H i₀) =
        (∑ j : Fin J, ∑ j' : Fin J, c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
          ((∏ a : Fin n, lamDivSum (f j (i₀.succAbove a)) N D (m + H (i₀.succAbove a))) *
           (∏ a : Fin n, lamDivSum (f j' (i₀.succAbove a)) N D (m + H (i₀.succAbove a))))) *
        thetaNat (m + H i₀) := by
    intro m hm
    have hmN : N ≤ m := (mem_residueWindow_iff N W b m).mp hm |>.1
    by_cases hpr : (m + H i₀).Prime
    · rw [hexp m]
      congr 1
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      rw [hsplit j m, hsplit j' m, hcollapse j m hpr hmN, hcollapse j' m hpr hmN]
      ring
    · rw [thetaNat_of_not_prime hpr]
      ring
  have hsum_eq : ∀ j j' : Fin J,
      (∑ m ∈ residueWindow N W b, thetaNat (m + H i₀) *
          ((∏ a : Fin n, lamDivSum (f j (i₀.succAbove a)) N D (m + H (i₀.succAbove a))) *
           (∏ a : Fin n, lamDivSum (f j' (i₀.succAbove a)) N D (m + H (i₀.succAbove a))))) =
        thetaWindowSum N W b (H i₀) D (fun a => H (i₀.succAbove a))
          (fun a => lamDivWeight (f j (i₀.succAbove a)) N)
          (fun a => lamDivWeight (f j' (i₀.succAbove a)) N) := by
    intro j j'
    rw [residueWindow, thetaWindowSum]
    simp only [lamDivSum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl hpt]
  have hL : (∑ m ∈ residueWindow N W b,
        (∑ j : Fin J, ∑ j' : Fin J, c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
          ((∏ a : Fin n, lamDivSum (f j (i₀.succAbove a)) N D (m + H (i₀.succAbove a))) *
           (∏ a : Fin n, lamDivSum (f j' (i₀.succAbove a)) N D (m + H (i₀.succAbove a))))) *
        thetaNat (m + H i₀)) =
      ∑ m ∈ residueWindow N W b, ∑ j : Fin J, ∑ j' : Fin J,
        c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
          ((∏ a : Fin n, lamDivSum (f j (i₀.succAbove a)) N D (m + H (i₀.succAbove a))) *
           (∏ a : Fin n, lamDivSum (f j' (i₀.succAbove a)) N D (m + H (i₀.succAbove a)))) *
        thetaNat (m + H i₀) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Finset.sum_mul]
  rw [hL]
  have hstep1 : (∑ m ∈ residueWindow N W b, ∑ j : Fin J, ∑ j' : Fin J,
        c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
          ((∏ a : Fin n, lamDivSum (f j (i₀.succAbove a)) N D (m + H (i₀.succAbove a))) *
           (∏ a : Fin n, lamDivSum (f j' (i₀.succAbove a)) N D (m + H (i₀.succAbove a)))) *
        thetaNat (m + H i₀)) =
      ∑ j : Fin J, ∑ j' : Fin J, c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
        ∑ m ∈ residueWindow N W b, thetaNat (m + H i₀) *
          ((∏ a : Fin n, lamDivSum (f j (i₀.succAbove a)) N D (m + H (i₀.succAbove a))) *
           (∏ a : Fin n, lamDivSum (f j' (i₀.succAbove a)) N D (m + H (i₀.succAbove a)))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hstep1]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  rw [hsum_eq j j']

/-! ## The real form of Theorem 3.6(i) and the pair sums -/

/-- The main term of `theorem36_i` in real form. -/
noncomputable def mainTargetR {k : ℕ} (F G : Fin k → ℝ → ℝ) (W : ℕ → ℕ) (x : ℕ) : ℝ :=
  mainScale k W x * ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0, deriv (F j) t * deriv (G j) t)

theorem mainTarget_eq_ofReal {k : ℕ} (F G : Fin k → ℝ → ℝ) (W : ℕ → ℕ) (x : ℕ) :
    ((mainTargetR F G W x : ℝ) : ℂ) = mainTarget F G W x := by
  rw [mainTargetR, mainTarget, mainScale, Complex.ofReal_mul, Complex.ofReal_prod]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [← Complex.ofReal_mul]
  exact (integral_ofReal).symm

/-- **Polymath8a Theorem 3.6(i), real form.** -/
theorem theorem36_i_real {k : ℕ} (hk : 1 ≤ k) (H : Fin k → ℕ)
    (hHinj : Function.Injective H)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ i, HasCompactSupport (F i))
    (hsmF : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (F i)) (hcsG : ∀ i, HasCompactSupport (G i))
    (hsmG : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (G i))
    (M : Fin k → ℝ) (hMnn : ∀ i, 0 ≤ M i)
    (hsupp : ∀ i t, M i < |t| → F i t = 0 ∧ G i t = 0)
    (hσ1 : 2 * (∑ i, M i) < 1)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ (∑ i, M i) ≤ (D x : ℝ))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ x : ℕ, x₀ ≤ x →
      |windowDivisorProduct F G H (W x) (b x) (D x) x - mainTargetR F G W x| ≤
        ε x * mainScale k W x := by
  obtain ⟨x₀, ε, hε, hb⟩ :=
    theorem36_i hk H hHinj F G hcsF hsmF hcsG hsmG M hMnn hsupp hσ1 W hW w hw hsmall hlq
      D hD b hbW
  refine ⟨x₀, ε, hε, fun x hx => ?_⟩
  have h := hb x hx
  have key : (((windowDivisorProduct F G H (W x) (b x) (D x) x - mainTargetR F G W x : ℝ) : ℂ)) =
      (((windowDivisorProduct F G H (W x) (b x) (D x) x : ℝ)) : ℂ) - mainTarget F G W x := by
    rw [Complex.ofReal_sub, mainTarget_eq_ofReal]
  rw [← key, norm_ofReal_complex] at h
  exact h

/-- The coefficient `α` of the tensor-product sieve: `Σ_{j,j′} c_j c_{j′} ∏ᵢ ∫₀^∞ f′_{j,i}f′_{j′,i}`
(Polymath8a §5.2). -/
noncomputable def tpAlpha {k J : ℕ} (c : Fin J → ℝ) (f : Fin J → Fin k → ℝ → ℝ) : ℝ :=
  ∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
    ∏ i : Fin k, (∫ t : ℝ in Set.Ioi 0, deriv (f j i) t * deriv (f j' i) t)

/-- The coefficient `β_i` of the tensor-product sieve:
`Σ_{j,j′} c_j c_{j′} f_{j,i}(0) f_{j′,i}(0) ∏_{l≠i} ∫₀^∞ f′_{j,l}f′_{j′,l}`
(Polymath8a §5.2, using (20)). -/
noncomputable def tpBeta {k J : ℕ} (c : Fin J → ℝ) (f : Fin J → Fin k → ℝ → ℝ)
    (i : Fin k) : ℝ :=
  ∑ j : Fin J, ∑ j' : Fin J, c j * c j' * (f j i 0) * (f j' i 0) *
    ∏ l ∈ (Finset.univ.erase i),
      (∫ t : ℝ in Set.Ioi 0, deriv (f j l) t * deriv (f j' l) t)

/-- `prefOne` and `mainScale` agree (both are `B^{-k}N/W`). -/
theorem prefOne_eq_mainScale (N W k : ℕ) : prefOne N W k = mainScale k (fun _ => W) N := by
  rw [prefOne, mainScale, prefactor]
  simp only [Nat.totient_one]
  ring


/-! ## The bound (13) for the tensor-product weight -/

/-- **The `S₁` bound for the tensor-product sieve weight** (Polymath8a (13)),
**pairwise form**: `Σ_{n ≡ b (W)} ν(n) ≤ (α + o(1))·B^{-k}·x/W` where
`ν = (Σ_j c_j ∏ᵢ λ_{f_{j,i}}(·+Hᵢ))²` and `α = tpAlpha c f`.  Assembled from
`theorem36_i_real` applied to each of the `J²` pairs `(j, j′)`; the errors of the
pairs are combined into a single `ε → 0`.

The hypothesis is only the *pairwise* support condition
`2·(∑ i, max (M j i) (M j′ i)) < 1` (Polymath8a §5.3 (87): for the tensor products
produced by the `ε`-enlargement one only has
`S(f_{1,j}) + ⋯ + S(f_{k,j}) ≤ (1+ε)ϑ/2`, so the per-component bound `ϑ/2` is *not*
available; only pairs with `(1+ε)ϑ < 1` are controlled). -/
theorem weightSum_tpWeight_le_pairwise {k J : ℕ} (hk : 1 ≤ k) (hJ : 1 ≤ J)
    (c : Fin J → ℝ) (f : Fin J → Fin k → ℝ → ℝ) (H : Fin k → ℕ)
    (hHinj : Function.Injective H)
    (hcs : ∀ j i, HasCompactSupport (f j i)) (hsm : ∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j i))
    (M : Fin J → Fin k → ℝ) (hMnn : ∀ j i, 0 ≤ M j i)
    (hsupp : ∀ j i t, M j i < |t| → f j i t = 0)
    (hMpair : ∀ j j', 2 * (∑ i, max (M j i) (M j' i)) < 1)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ (2 * (∑ j, ∑ i, M j i)) ≤ (D x : ℝ))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ x, 0 ≤ ε x) ∧
      ∀ x : ℕ, x₀ ≤ x →
      weightSum (W x) (b x) x (fun m => (tpWeight c f x (D x) H m) ^ 2) ≤
        (tpAlpha c f + ε x) * prefOne x (W x) k := by
  classical
  have hpair : ∀ p : Fin J × Fin J,
      ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ x : ℕ, x₀ ≤ x →
        |windowDivisorProduct (f p.1) (f p.2) H (W x) (b x) (D x) x -
          mainTargetR (f p.1) (f p.2) (fun _ => W x) x| ≤
          ε x * mainScale k (fun _ => W x) x := by
    intro p
    have hmax : (∑ i, max (M p.1 i) (M p.2 i)) ≤ (∑ i, M p.1 i) + (∑ i, M p.2 i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ =>
        max_le (le_add_of_nonneg_right (hMnn p.2 i)) (le_add_of_nonneg_left (hMnn p.1 i))
    have hMps1 : 2 * (∑ i, max (M p.1 i) (M p.2 i)) < 1 := hMpair p.1 p.2
    have hDp : ∀ᶠ x : ℕ in atTop,
        (x : ℝ) ^ (∑ i, max (M p.1 i) (M p.2 i)) ≤ (D x : ℝ) := by
      have hle : (∑ i, max (M p.1 i) (M p.2 i)) ≤ 2 * (∑ j, ∑ i, M j i) := by
        have h2 : (∑ i, M p.1 i) ≤ ∑ j, ∑ i, M j i :=
          Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun i _ => hMnn j i)
            (Finset.mem_univ p.1)
        have h3 : (∑ i, M p.2 i) ≤ ∑ j, ∑ i, M j i :=
          Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun i _ => hMnn j i)
            (Finset.mem_univ p.2)
        linarith
      filter_upwards [hD, eventually_ge_atTop 1] with x hDx hx1
      exact le_trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx1) hle) hDx
    exact theorem36_i_real hk H hHinj (f p.1) (f p.2)
      (fun i => hcs p.1 i) (fun i => hsm p.1 i) (fun i => hcs p.2 i) (fun i => hsm p.2 i)
      (fun i => max (M p.1 i) (M p.2 i))
      (fun i => le_trans (hMnn p.1 i) (le_max_left _ _))
      (fun i t ht => ⟨hsupp p.1 i t (lt_of_le_of_lt (le_max_left _ _) ht),
                      hsupp p.2 i t (lt_of_le_of_lt (le_max_right _ _) ht)⟩)
      hMps1 W hW w hw hsmall hlq D hDp b hbW
  choose x₀p εp hεp using hpair
  refine ⟨max 2 ((Finset.univ : Finset (Fin J × Fin J)).sup'
      ⟨(⟨0, hJ⟩, ⟨0, hJ⟩), Finset.mem_univ _⟩ x₀p),
    (fun x => ∑ p : Fin J × Fin J, |c p.1 * c p.2| * |εp p x|), ?_,
    fun x => Finset.sum_nonneg fun p _ => mul_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  · have hη : ∀ p : Fin J × Fin J, Tendsto (fun x => |εp p x|) atTop (𝓝 (0 : ℝ)) := by
      intro p
      have h := (hεp p).1.abs
      simpa using h
    have hsum_t : Tendsto (fun x => ∑ p ∈ (Finset.univ : Finset (Fin J × Fin J)),
        |c p.1 * c p.2| * |εp p x|) atTop
        (𝓝 (∑ p ∈ (Finset.univ : Finset (Fin J × Fin J)), |c p.1 * c p.2| * 0)) :=
      tendsto_finsetSum _ (fun p _ => tendsto_const_nhds.mul (hη p))
    simpa using hsum_t
  · intro x hx
    have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
    have hx0 : ∀ p : Fin J × Fin J, x₀p p ≤ x := fun p =>
      le_trans (Finset.le_sup' x₀p (Finset.mem_univ p)) (le_trans (le_max_right _ _) hx)
    have hMSpos : 0 < mainScale k (fun _ => W x) x := mainScale_pos (hW x) hx2 k
    have hMSnn : 0 ≤ mainScale k (fun _ => W x) x := le_of_lt hMSpos
    have hεnn_all : ∀ p : Fin J × Fin J, 0 ≤ εp p x := by
      intro p
      have h := (hεp p).2 x (hx0 p)
      have h0 : (0 : ℝ) ≤ εp p x * mainScale k (fun _ => W x) x :=
        le_trans (abs_nonneg _) h
      nlinarith [h0, hMSpos]
    have habsp : ∀ p : Fin J × Fin J,
        |windowDivisorProduct (f p.1) (f p.2) H (W x) (b x) (D x) x -
          mainTargetR (f p.1) (f p.2) (fun _ => W x) x| ≤
          |εp p x| * mainScale k (fun _ => W x) x := by
      intro p
      have h := (hεp p).2 x (hx0 p)
      rw [← abs_of_nonneg (hεnn_all p)] at h
      exact h
    rw [weightSum_tpWeight_sq]
    have hstep1 : (∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          windowDivisorProduct (f j) (f j') H (W x) (b x) (D x) x) ≤
        ∑ j : Fin J, ∑ j' : Fin J, (c j * c j' *
            mainTargetR (f j) (f j') (fun _ => W x) x +
          |c j * c j'| * (|εp (j, j') x| * mainScale k (fun _ => W x) x)) := by
      refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ => ?_
      have h2 : c j * c j' *
            (windowDivisorProduct (f j) (f j') H (W x) (b x) (D x) x -
              mainTargetR (f j) (f j') (fun _ => W x) x) ≤
          |c j * c j'| * (|εp (j, j') x| * mainScale k (fun _ => W x) x) := by
        calc c j * c j' *
              (windowDivisorProduct (f j) (f j') H (W x) (b x) (D x) x -
                mainTargetR (f j) (f j') (fun _ => W x) x)
            ≤ |c j * c j' * (windowDivisorProduct (f j) (f j') H (W x) (b x) (D x) x -
                mainTargetR (f j) (f j') (fun _ => W x) x)| := le_abs_self _
          _ = |c j * c j'| * |windowDivisorProduct (f j) (f j') H (W x) (b x) (D x) x -
                mainTargetR (f j) (f j') (fun _ => W x) x| := abs_mul _ _
          _ ≤ |c j * c j'| * (|εp (j, j') x| * mainScale k (fun _ => W x) x) :=
              mul_le_mul_of_nonneg_left (habsp (j, j')) (abs_nonneg _)
      linarith
    refine le_trans hstep1 ?_
    simp only [Finset.sum_add_distrib]
    have hfirst : (∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          mainTargetR (f j) (f j') (fun _ => W x) x) =
        mainScale k (fun _ => W x) x * tpAlpha c f := by
      rw [tpAlpha]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      rw [mainTargetR]
      ring
    have hsecond : (∑ j : Fin J, ∑ j' : Fin J, |c j * c j'| *
          (|εp (j, j') x| * mainScale k (fun _ => W x) x)) =
        (∑ j : Fin J, ∑ j' : Fin J, |c j * c j'| * |εp (j, j') x|) *
          mainScale k (fun _ => W x) x := by
      simp only [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      ring
    rw [hfirst, hsecond, ← prefOne_eq_mainScale, Fintype.sum_prod_type]
    exact le_of_eq (by ring)

/-- **The `S₁` bound for the tensor-product sieve weight** (Polymath8a (13)):
`Σ_{n ≡ b (W)} ν(n) ≤ (α + o(1))·B^{-k}·x/W` where `ν = (Σ_j c_j ∏ᵢ λ_{f_{j,i}}(·+Hᵢ))²`
and `α = tpAlpha c f`.  Assembled from `theorem36_i_real` applied to each of the
`J²` pairs `(j, j′)`; the errors of the pairs are combined into a single
`ε → 0`.

This is the special case of the pairwise form `weightSum_tpWeight_le_pairwise`
in which every component family satisfies the stronger per-`j` support bound
`∑ i, M j i < ϑ/2` for a fixed `ϑ < 1/2`. -/
theorem weightSum_tpWeight_le {k J : ℕ} (hk : 1 ≤ k) (hJ : 1 ≤ J)
    (c : Fin J → ℝ) (f : Fin J → Fin k → ℝ → ℝ) (H : Fin k → ℕ)
    (hHinj : Function.Injective H)
    (hcs : ∀ j i, HasCompactSupport (f j i)) (hsm : ∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j i))
    (M : Fin J → Fin k → ℝ) (hMnn : ∀ j i, 0 ≤ M j i)
    (hsupp : ∀ j i t, M j i < |t| → f j i t = 0)
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1 / 2) (hMsum : ∀ j, ∑ i, M j i < ϑ / 2)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ (2 * (∑ j, ∑ i, M j i)) ≤ (D x : ℝ))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ x, 0 ≤ ε x) ∧
      ∀ x : ℕ, x₀ ≤ x →
      weightSum (W x) (b x) x (fun m => (tpWeight c f x (D x) H m) ^ 2) ≤
        (tpAlpha c f + ε x) * prefOne x (W x) k := by
  refine weightSum_tpWeight_le_pairwise hk hJ c f H hHinj hcs hsm M hMnn hsupp ?_ W hW w hw
    hsmall hlq D hD b hbW
  intro j j'
  have hmax : (∑ i, max (M j i) (M j' i)) ≤ (∑ i, M j i) + (∑ i, M j' i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ =>
      max_le (le_add_of_nonneg_right (hMnn j' i)) (le_add_of_nonneg_left (hMnn j i))
  linarith [hMsum j, hMsum j', hϑ1]

/-! ## The bound (14) for the tensor-product weight -/

/-- `∑_{l ≠ i₀} g l = ∑_{a : Fin n} g (i₀.succAbove a)` on `Fin (n+1)`. -/
theorem sum_erase_eq_sum_succAbove {n : ℕ} (i₀ : Fin (n + 1))
    (g : Fin (n + 1) → ℝ) :
    (∑ l ∈ (Finset.univ.erase i₀), g l) = ∑ a : Fin n, g (i₀.succAbove a) := by
  have himg : (Finset.univ.erase i₀ : Finset (Fin (n + 1))) =
      (Finset.univ : Finset (Fin n)).image i₀.succAbove := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq (show x ≠ i₀ from hx.1)
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩
      exact ⟨Fin.succAbove_ne i₀ a, trivial⟩
  rw [himg, Finset.sum_image]
  intro x _ y _ hxy
  exact Fin.succAbove_right_injective hxy

/-- `∏_{l ≠ i₀} g l = ∏_{a : Fin n} g (i₀.succAbove a)` on `Fin (n+1)`. -/
theorem prod_erase_eq_prod_succAbove {n : ℕ} (i₀ : Fin (n + 1))
    (g : Fin (n + 1) → ℝ) :
    (∏ l ∈ (Finset.univ.erase i₀), g l) = ∏ a : Fin n, g (i₀.succAbove a) := by
  have himg : (Finset.univ.erase i₀ : Finset (Fin (n + 1))) =
      (Finset.univ : Finset (Fin n)).image i₀.succAbove := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq (show x ≠ i₀ from hx.1)
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩
      exact ⟨Fin.succAbove_ne i₀ a, trivial⟩
  rw [himg, Finset.prod_image]
  intro x _ y _ hxy
  exact Fin.succAbove_right_injective hxy

/-- `thetaMainScale` and `prefTwo` agree (both equal `(1/φ(W))·N·(B^{-1})^j`). -/
theorem thetaMainScale_eq_prefTwo (N W j : ℕ) :
    thetaMainScale (k := j) (fun _ => W) N = prefTwo N W j := by
  rw [thetaMainScale, prefTwo, prefactor]
  simp only [Nat.totient_one]
  ring

/-- `0 < (1/φ(W))·x·B^{-k}`. -/
theorem thetaMainScale_pos {k : ℕ} {Wf : ℕ → ℕ} {x : ℕ} (hW : Wf x ≠ 0) (hx : 2 ≤ x) :
    0 < thetaMainScale (k := k) Wf x := by
  rw [thetaMainScale, prefactor]
  have hφ : (0 : ℝ) < ((Wf x).totient : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW))
  have hWr : (0 : ℝ) < (Wf x : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hW)
  have hlog : (0 : ℝ) < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hxr : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.mpr (by omega)
  positivity

/-- **The `S₂` bound for the tensor-product sieve weight** (Polymath8a (14)),
**pairwise form**: `Σ_{n ≡ b (W)} ν(n)θ(n + H i) ≥ (β_i - o(1))·B^{1-k}·x/φ(W)`
where `ν = (Σ_j c_j ∏ᵢ λ_{f_{j,i}}(·+Hᵢ))²` and `β_i = tpBeta c f i`.  Assembled
from `theorem35_i` (applied, for each `i` and each pair `(j,j′)`, to the `(k-1)`-tuple
obtained by deleting `H i`) together with the prime collapse `lamDivSum_prime`.

The hypothesis is the *pairwise* condition
`∑_{i ≠ i₀} (M j i + M j′ i) < ϑ` (Polymath8a §5.3 (90): for the `ε`-enlarged
construction only pairs in which one member has `∑_{i≠i₀} S(f) < (1-ε)ϑ/2` are
controlled). -/
theorem thetaWeightSum_tpWeight_ge_pairwise {J n : ℕ} (hn : 1 ≤ n) (hJ : 1 ≤ J)
    (c : Fin J → ℝ) (f : Fin J → Fin (n + 1) → ℝ → ℝ) (H : Fin (n + 1) → ℕ)
    (hHinj : Function.Injective H)
    (hcs : ∀ j i, HasCompactSupport (f j i)) (hsm : ∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j i))
    (M : Fin J → Fin (n + 1) → ℝ) (hMnn : ∀ j i, 0 ≤ M j i)
    (hsupp : ∀ j i t, M j i < |t| → f j i t = 0)
    (hfb : ∀ j i t, 1 ≤ t → f j i t = 0)
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1 / 2)
    (hMpair : ∀ j j' (i₀ : Fin (n + 1)),
      ∑ i ∈ Finset.univ.erase i₀, (M j i + M j' i) < ϑ)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x))
    (hlev : levelOfDistribution ϑ)
    (hWlog : ∃ A₀ : ℕ, ∀ᶠ x : ℕ in atTop, (W x : ℝ) ≤ (Real.log (x : ℝ)) ^ A₀)
    (hsep : ∀ᶠ x : ℕ in atTop, ∀ i j : Fin (n + 1), i ≠ j → H j - H i < w x)
    (D : ℕ → ℕ) (hD1 : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (2 * (∑ j, ∑ i, M j i)) ≤ (D x : ℝ))
    (hD2 : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ ϑ ≤ (D x : ℝ)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ x, 0 ≤ ε x) ∧
      ∀ x : ℕ, x₀ ≤ x → ∀ i₀ : Fin (n + 1),
      (tpBeta c f i₀ - ε x) * prefTwo x (W x) n ≤
        thetaWeightSum (W x) (b x) x (fun m => (tpWeight c f x (D x) H m) ^ 2) (H i₀) := by
  classical
  have hBex : ∀ p : Fin J × Fin (n + 1), ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |f p.1 p.2 t| ≤ C :=
    fun p => exists_abs_bound_of_hasCompactSupport (f p.1 p.2) (hcs p.1 p.2)
      (hsm p.1 p.2).continuous
  choose Bc hBc0 hBc using hBex
  set BF : ℝ := ∑ p : Fin J × Fin (n + 1), Bc p with hBFdef
  have hBF0 : 0 ≤ BF := by rw [hBFdef]; exact Finset.sum_nonneg fun p _ => hBc0 p
  have hBFbd : ∀ (j : Fin J) (i : Fin (n + 1)) (t : ℝ), |f j i t| ≤ BF := by
    intro j i t
    rw [hBFdef]
    exact le_trans (hBc (j, i) t)
      (Finset.single_le_sum (fun p _ => hBc0 p) (Finset.mem_univ (j, i)))
  have hMtot : ∀ j i, M j i ≤ 2 * (∑ j, ∑ i, M j i) := by
    intro j i
    have h1 : M j i ≤ ∑ i, M j i :=
      Finset.single_le_sum (fun i _ => hMnn j i) (Finset.mem_univ i)
    have h2 : (∑ i, M j i) ≤ ∑ j, ∑ i, M j i :=
      Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun i _ => hMnn j i)
        (Finset.mem_univ j)
    have h3 : (0 : ℝ) ≤ ∑ j, ∑ i, M j i :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hMnn j i
    linarith
  have hpair : ∀ p : Fin J × Fin J × Fin (n + 1),
      ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ x : ℕ, x₀ ≤ x →
        |thetaWindowSum x (W x) (b x) (H p.2.2) (D x) (fun a => H (p.2.2.succAbove a))
            (fun a => lamDivWeight (f p.1 (p.2.2.succAbove a)) x)
            (fun a => lamDivWeight (f p.2.1 (p.2.2.succAbove a)) x) -
          thetaMainTerm (fun a => f p.1 (p.2.2.succAbove a))
            (fun a => f p.2.1 (p.2.2.succAbove a)) (fun _ => W x) x| ≤
          ε x * thetaMainScale (k := n) (fun _ => W x) x := by
    rintro ⟨j, j', i₀⟩
    have hMsum' : (∑ a : Fin n, (M j (i₀.succAbove a) + M j' (i₀.succAbove a))) < ϑ := by
      rw [← sum_erase_eq_sum_succAbove i₀ (fun l => M j l + M j' l)]
      exact hMpair j j' i₀
    have hsep' : ∀ᶠ x : ℕ in atTop,
        ∀ a b : Fin n, a ≠ b → H (i₀.succAbove b) - H (i₀.succAbove a) < w x := by
      filter_upwards [hsep] with x hx
      intro a b hab
      exact hx _ _ (fun h => hab (Fin.succAbove_right_injective h))
    have hseph' : ∀ᶠ x : ℕ in atTop, ∀ a : Fin n,
        H i₀ - H (i₀.succAbove a) < w x ∧ H (i₀.succAbove a) - H i₀ < w x := by
      filter_upwards [hsep] with x hx
      intro a
      exact ⟨hx (i₀.succAbove a) i₀ (Fin.succAbove_ne i₀ a),
        hx i₀ (i₀.succAbove a) (Ne.symm (Fin.succAbove_ne i₀ a))⟩
    have hHinj' : Function.Injective (fun a : Fin n => H (i₀.succAbove a)) :=
      fun a b hab => Fin.succAbove_right_injective (hHinj hab)
    have hhne' : ∀ a : Fin n, H i₀ ≠ H (i₀.succAbove a) :=
      fun a h => Ne.symm (Fin.succAbove_ne i₀ a) (hHinj h)
    exact theorem35_i (k := n) hn (fun a => f j (i₀.succAbove a))
      (fun a => f j' (i₀.succAbove a))
      (fun a => hcs j (i₀.succAbove a)) (fun a => hsm j (i₀.succAbove a))
      (fun a => hcs j' (i₀.succAbove a)) (fun a => hsm j' (i₀.succAbove a))
      W hW w hw hsmall hlq hBF0 hBF0
      (fun a t => hBFbd j (i₀.succAbove a) t) (fun a t => hBFbd j' (i₀.succAbove a) t)
      (fun a t ht => ⟨hsupp j (i₀.succAbove a) t (lt_of_le_of_lt (hMtot j _) ht),
        hsupp j' (i₀.succAbove a) t (lt_of_le_of_lt (hMtot j' _) ht)⟩)
      hϑ0 hϑ1 (fun a => hMnn j (i₀.succAbove a)) (fun a => hMnn j' (i₀.succAbove a))
      (fun a t ht => hsupp j (i₀.succAbove a) t ht)
      (fun a t ht => hsupp j' (i₀.succAbove a) t ht)
      hMsum' b (H i₀) (fun a => H (i₀.succAbove a)) hHinj'
      (Filter.Eventually.of_forall fun x a => hbW x (i₀.succAbove a))
      (Filter.Eventually.of_forall fun x => hbW x i₀) hhne'
      w (Filter.Eventually.of_forall fun x => le_rfl) hsep' hseph' hlev hWlog D hD1 hD2
  choose x₀p εp hεp using hpair
  have hsup_nu : (Finset.univ : Finset (Fin J × Fin J × Fin (n + 1))).Nonempty :=
    ⟨(⟨0, hJ⟩, ⟨0, hJ⟩, ⟨0, Nat.succ_pos n⟩), Finset.mem_univ _⟩
  have hEps_t : Tendsto (fun x : ℕ => ∑ j : Fin J, ∑ j' : Fin J, ∑ i : Fin (n + 1),
      |c j * c j' * f j i 0 * f j' i 0| * |εp (j, j', i) x|) atTop (𝓝 0) := by
    have hη : ∀ p : Fin J × Fin J × Fin (n + 1),
        Tendsto (fun x => |εp p x|) atTop (𝓝 (0 : ℝ)) := by
      intro p
      have h := (hεp p).1.abs
      simpa using h
    have hsum_t : Tendsto (fun x : ℕ => ∑ j ∈ (Finset.univ : Finset (Fin J)),
          ∑ j' ∈ (Finset.univ : Finset (Fin J)),
          ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))),
            |c j * c j' * f j i 0 * f j' i 0| * |εp (j, j', i) x|) atTop
        (𝓝 (∑ j ∈ (Finset.univ : Finset (Fin J)), ∑ j' ∈ (Finset.univ : Finset (Fin J)),
          ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))),
            |c j * c j' * f j i 0 * f j' i 0| * 0)) := by
      refine tendsto_finsetSum _ (fun j _ => ?_)
      refine tendsto_finsetSum _ (fun j' _ => ?_)
      refine tendsto_finsetSum _ (fun i _ => ?_)
      exact tendsto_const_nhds.mul (hη (j, j', i))
    simpa using hsum_t
  have hgoal : ∀ᶠ x : ℕ in atTop, ∀ i₀ : Fin (n + 1),
      (tpBeta c f i₀ - (∑ j : Fin J, ∑ j' : Fin J, ∑ i : Fin (n + 1),
        |c j * c j' * f j i 0 * f j' i 0| * |εp (j, j', i) x|)) * prefTwo x (W x) n ≤
      thetaWeightSum (W x) (b x) x (fun m => (tpWeight c f x (D x) H m) ^ 2) (H i₀) := by
    filter_upwards [hD1, hD2, eventually_ge_atTop (max 2 ((Finset.univ :
      Finset (Fin J × Fin J × Fin (n + 1))).sup' hsup_nu x₀p))] with x hD1x hD2x hxbig
    intro i₀
    have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hxbig
    have hx0 : ∀ p : Fin J × Fin J × Fin (n + 1), x₀p p ≤ x := fun p =>
      le_trans (Finset.le_sup' x₀p (Finset.mem_univ p)) (le_trans (le_max_right _ _) hxbig)
    have hDx1 : 1 ≤ D x := by
      have h0 : (1 : ℝ) ≤ (x : ℝ) ^ (2 * (∑ j, ∑ i, M j i)) :=
        Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ x)) (by
          have : (0 : ℝ) ≤ ∑ j, ∑ i, M j i :=
            Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hMnn j i
          linarith)
      have h1 : (1 : ℝ) ≤ (D x : ℝ) := le_trans h0 hD1x
      exact_mod_cast h1
    have hRx : 1 < x := by omega
    set sc : ℝ := thetaMainScale (k := n) (fun _ => W x) x with hscdef
    have hscpos : 0 < sc := by
      rw [hscdef]
      exact thetaMainScale_pos (k := n) (Wf := fun _ => W x) (by simpa using hW x) hx2
    have hεnn : ∀ p : Fin J × Fin J × Fin (n + 1), 0 ≤ εp p x := by
      intro p
      have h := (hεp p).2 x (hx0 p)
      have h0 : (0 : ℝ) ≤ εp p x * thetaMainScale (k := n) (fun _ => W x) x :=
        le_trans (abs_nonneg _) h
      nlinarith [h0, hscpos]
    have hexp : thetaWeightSum (W x) (b x) x (fun m => (tpWeight c f x (D x) H m) ^ 2) (H i₀) =
        ∑ j : Fin J, ∑ j' : Fin J, c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
          thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
            (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
            (fun a => lamDivWeight (f j' (i₀.succAbove a)) x) :=
      thetaWeightSum_tpWeight_sq c f H i₀ (W x) (b x) (D x) x hDx1 hRx hfb
    rw [hexp, ← thetaMainScale_eq_prefTwo x (W x) n]
    -- the main identity: the `MT`-part of the sum is `tpBeta · sc`
    have hmainid : (∑ j : Fin J, ∑ j' : Fin J, c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
          thetaMainTerm (fun a => f j (i₀.succAbove a)) (fun a => f j' (i₀.succAbove a))
            (fun _ => W x) x) = tpBeta c f i₀ * sc := by
      rw [tpBeta, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [thetaMainTerm, prod_erase_eq_prod_succAbove, ← hscdef]
      ring
    -- each pair satisfies the two-sided bound `|X - MT| ≤ |εp| · sc`
    have hlow : ∀ j j' : Fin J,
        c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
            thetaMainTerm (fun a => f j (i₀.succAbove a)) (fun a => f j' (i₀.succAbove a))
              (fun _ => W x) x -
          |c j * c j' * (f j i₀ 0) * (f j' i₀ 0)| * (|εp (j, j', i₀) x| * sc) ≤
          c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
            thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
              (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
              (fun a => lamDivWeight (f j' (i₀.succAbove a)) x) := by
      intro j j'
      have h := (hεp (j, j', i₀)).2 x (hx0 (j, j', i₀))
      dsimp only at h
      rw [← hscdef, ← abs_of_nonneg (hεnn (j, j', i₀))] at h
      have h1 : thetaMainTerm (fun a => f j (i₀.succAbove a))
            (fun a => f j' (i₀.succAbove a)) (fun _ => W x) x -
            |εp (j, j', i₀) x| * sc ≤
          thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
            (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
            (fun a => lamDivWeight (f j' (i₀.succAbove a)) x) := by
        linarith [(abs_le.mp h).1]
      have h2 : thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
            (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
            (fun a => lamDivWeight (f j' (i₀.succAbove a)) x) ≤
          thetaMainTerm (fun a => f j (i₀.succAbove a))
            (fun a => f j' (i₀.succAbove a)) (fun _ => W x) x +
            |εp (j, j', i₀) x| * sc := by
        linarith [(abs_le.mp h).2]
      set cf : ℝ := c j * c j' * (f j i₀ 0) * (f j' i₀ 0) with hcf
      by_cases hc : 0 ≤ cf
      · have := mul_le_mul_of_nonneg_left h1 hc
        rw [show |c j * c j' * (f j i₀ 0) * (f j' i₀ 0)| = cf from by
          rw [← hcf]; exact abs_of_nonneg hc] 
        rw [hcf] at this ⊢
        linarith [this]
      · have hc' : cf < 0 := lt_of_not_ge hc
        have := mul_le_mul_of_nonpos_left h2 (le_of_lt hc')
        rw [show |c j * c j' * (f j i₀ 0) * (f j' i₀ 0)| = -cf from by
          rw [hcf, abs_of_neg hc']]
        rw [hcf] at this ⊢
        nlinarith [this]
    -- the error term dominates the `j,j'`-restricted error
    have hEps_ge : (∑ j : Fin J, ∑ j' : Fin J,
          (|c j * c j' * (f j i₀ 0) * (f j' i₀ 0)| * (|εp (j, j', i₀) x| * sc))) ≤
        (∑ j : Fin J, ∑ j' : Fin J, ∑ i : Fin (n + 1),
          (|c j * c j' * f j i 0 * f j' i 0| * |εp (j, j', i) x|)) * sc := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j' _ => ?_
      have hsingle := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (n + 1))))
        (f := fun i : Fin (n + 1) =>
          (|c j * c j' * f j i 0 * f j' i 0| * |εp (j, j', i) x|))
        (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i₀)
      have heq : |c j * c j' * (f j i₀ 0) * (f j' i₀ 0)| * (|εp (j, j', i₀) x| * sc) =
          (|c j * c j' * (f j i₀ 0) * (f j' i₀ 0)| * |εp (j, j', i₀) x|) * sc := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hsingle (le_of_lt hscpos)
    -- assemble
    have hper : ∀ j j' : Fin J,
        c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
            thetaMainTerm (fun a => f j (i₀.succAbove a)) (fun a => f j' (i₀.succAbove a))
              (fun _ => W x) x ≤
          c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
              thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
                (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
                (fun a => lamDivWeight (f j' (i₀.succAbove a)) x) +
            |c j * c j' * (f j i₀ 0) * (f j' i₀ 0)| * (|εp (j, j', i₀) x| * sc) := by
      intro j j'
      have := hlow j j'
      linarith
    have hsum_a : (∑ j : Fin J, ∑ j' : Fin J, c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
            thetaMainTerm (fun a => f j (i₀.succAbove a)) (fun a => f j' (i₀.succAbove a))
              (fun _ => W x) x) ≤
        (∑ j : Fin J, ∑ j' : Fin J, c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
              thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
                (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
                (fun a => lamDivWeight (f j' (i₀.succAbove a)) x)) +
          (∑ j : Fin J, ∑ j' : Fin J,
            (|c j * c j' * (f j i₀ 0) * (f j' i₀ 0)| * (|εp (j, j', i₀) x| * sc))) := by
      calc (∑ j : Fin J, ∑ j' : Fin J, c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
              thetaMainTerm (fun a => f j (i₀.succAbove a)) (fun a => f j' (i₀.succAbove a))
                (fun _ => W x) x)
          ≤ ∑ j : Fin J, ∑ j' : Fin J,
              (c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
                  thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
                    (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
                    (fun a => lamDivWeight (f j' (i₀.succAbove a)) x) +
                |c j * c j' * (f j i₀ 0) * (f j' i₀ 0)| * (|εp (j, j', i₀) x| * sc)) :=
            Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ => hper j j'
        _ = _ := by simp only [Finset.sum_add_distrib]
    have hfin : (tpBeta c f i₀ - (∑ j : Fin J, ∑ j' : Fin J, ∑ i : Fin (n + 1),
          (|c j * c j' * f j i 0 * f j' i 0| * |εp (j, j', i) x|))) * sc ≤
        (∑ j : Fin J, ∑ j' : Fin J, c j * c j' * (f j i₀ 0) * (f j' i₀ 0) *
              thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
                (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
                (fun a => lamDivWeight (f j' (i₀.succAbove a)) x)) := by
      have h3 : (tpBeta c f i₀ - (∑ j : Fin J, ∑ j' : Fin J, ∑ i : Fin (n + 1),
            (|c j * c j' * f j i 0 * f j' i 0| * |εp (j, j', i) x|))) * sc =
          tpBeta c f i₀ * sc - (∑ j : Fin J, ∑ j' : Fin J, ∑ i : Fin (n + 1),
            (|c j * c j' * f j i 0 * f j' i 0| * |εp (j, j', i) x|)) * sc := by ring
      rw [h3]
      linarith [hmainid, hsum_a, hEps_ge]
    exact hfin
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hgoal
  exact ⟨x₀, (fun x => ∑ j : Fin J, ∑ j' : Fin J, ∑ i : Fin (n + 1),
      |c j * c j' * f j i 0 * f j' i 0| * |εp (j, j', i) x|), hEps_t,
    fun x => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun j' _ =>
      Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _),
    fun x hx i₀ => hx₀ x hx i₀⟩

/-- **The `S₂` bound for the tensor-product sieve weight** (Polymath8a (14)):
`Σ_{n ≡ b (W)} ν(n)θ(n + H i) ≥ (β_i - o(1))·B^{1-k}·x/φ(W)` where
`ν = (Σ_j c_j ∏ᵢ λ_{f_{j,i}}(·+Hᵢ))²` and `β_i = tpBeta c f i`.  Assembled from
`theorem35_i` (applied, for each `i` and each pair `(j,j′)`, to the `(k-1)`-tuple
obtained by deleting `H i`) together with the prime collapse `lamDivSum_prime`.
This is the per-`j` special case of `thetaWeightSum_tpWeight_ge_pairwise`. -/
theorem thetaWeightSum_tpWeight_ge {J n : ℕ} (hn : 1 ≤ n) (hJ : 1 ≤ J)
    (c : Fin J → ℝ) (f : Fin J → Fin (n + 1) → ℝ → ℝ) (H : Fin (n + 1) → ℕ)
    (hHinj : Function.Injective H)
    (hcs : ∀ j i, HasCompactSupport (f j i)) (hsm : ∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j i))
    (M : Fin J → Fin (n + 1) → ℝ) (hMnn : ∀ j i, 0 ≤ M j i)
    (hsupp : ∀ j i t, M j i < |t| → f j i t = 0)
    (hfb : ∀ j i t, 1 ≤ t → f j i t = 0)
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1 / 2) (hMsum : ∀ j, ∑ i, M j i < ϑ / 2)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x))
    (hlev : levelOfDistribution ϑ)
    (hWlog : ∃ A₀ : ℕ, ∀ᶠ x : ℕ in atTop, (W x : ℝ) ≤ (Real.log (x : ℝ)) ^ A₀)
    (hsep : ∀ᶠ x : ℕ in atTop, ∀ i j : Fin (n + 1), i ≠ j → H j - H i < w x)
    (D : ℕ → ℕ) (hD1 : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (2 * (∑ j, ∑ i, M j i)) ≤ (D x : ℝ))
    (hD2 : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ ϑ ≤ (D x : ℝ)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ x, 0 ≤ ε x) ∧
      ∀ x : ℕ, x₀ ≤ x → ∀ i₀ : Fin (n + 1),
      (tpBeta c f i₀ - ε x) * prefTwo x (W x) n ≤
        thetaWeightSum (W x) (b x) x (fun m => (tpWeight c f x (D x) H m) ^ 2) (H i₀) := by
  refine thetaWeightSum_tpWeight_ge_pairwise hn hJ c f H hHinj hcs hsm M hMnn hsupp hfb
    hϑ0 hϑ1 ?_ W hW w hw hsmall hlq b hbW hlev hWlog hsep D hD1 hD2
  intro j j' i₀
  rw [Finset.sum_add_distrib]
  have h2 : (∑ i ∈ Finset.univ.erase i₀, M j i) ≤ ∑ i, M j i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun l _ _ => hMnn j l)
  have h3 : (∑ i ∈ Finset.univ.erase i₀, M j' i) ≤ ∑ i, M j' i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun l _ _ => hMnn j' l)
  linarith [hMsum j, hMsum j']

/-! ## The sieve criterion for the tensor-product weight -/

/-- **Polymath8a Lemma 3.4 bounds for the tensor-product sieve weight.**
Combining the `S₁` bound (`weightSum_tpWeight_le`) and the `S₂` bound
(`thetaWeightSum_tpWeight_ge`) gives the hypotheses (13), (14) of
`SieveBounds` for `ν(n) = (Σ_j c_j ∏ᵢ λ_{f_{j,i}}(n+Hᵢ))²` with
`α = tpAlpha c f` and `β_i = tpBeta c f i`. -/
theorem sieveBounds_of_tpWeight {J n : ℕ} (hn : 1 ≤ n) (hJ : 1 ≤ J)
    (c : Fin J → ℝ) (f : Fin J → Fin (n + 1) → ℝ → ℝ) (H : Fin (n + 1) → ℕ)
    (hHinj : Function.Injective H)
    (hcs : ∀ j i, HasCompactSupport (f j i)) (hsm : ∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j i))
    (M : Fin J → Fin (n + 1) → ℝ) (hMnn : ∀ j i, 0 ≤ M j i)
    (hsupp : ∀ j i t, M j i < |t| → f j i t = 0)
    (hfb : ∀ j i t, 1 ≤ t → f j i t = 0)
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1 / 2) (hMsum : ∀ j, ∑ i, M j i < ϑ / 2)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x))
    (hlev : levelOfDistribution ϑ)
    (hWlog : ∃ A₀ : ℕ, ∀ᶠ x : ℕ in atTop, (W x : ℝ) ≤ (Real.log (x : ℝ)) ^ A₀)
    (hsep : ∀ᶠ x : ℕ in atTop, ∀ i j : Fin (n + 1), i ≠ j → H j - H i < w x)
    (D : ℕ → ℕ) (hD1 : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (2 * (∑ j, ∑ i, M j i)) ≤ (D x : ℝ))
    (hD2 : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ ϑ ≤ (D x : ℝ)) :
    ∃ ε : ℕ → ℝ, Tendsto (fun x => |ε x|) atTop (𝓝 0) ∧
      SieveBounds (k := n + 1) H (tpAlpha c f) (tpBeta c f) ε
        (fun x m => (tpWeight c f x (D x) H m) ^ 2) W b := by
  classical
  obtain ⟨x₁, ε13, hε13t, hε13nn, hb13⟩ :=
    weightSum_tpWeight_le (k := n + 1) (Nat.succ_le_succ (Nat.zero_le n)) hJ c f H hHinj
      hcs hsm M hMnn hsupp hϑ0 hϑ1 hMsum W hW w hw hsmall hlq D hD1 b hbW
  obtain ⟨x₂, ε14, hε14t, hε14nn, hb14⟩ :=
    thetaWeightSum_tpWeight_ge hn hJ c f H hHinj hcs hsm M hMnn hsupp hfb hϑ0 hϑ1 hMsum
      W hW w hw hsmall hlq b hbW hlev hWlog hsep D hD1 hD2
  refine ⟨fun x => ε13 x + ε14 x, ?_, ?_⟩
  · have hsum : Tendsto (fun x => ε13 x + ε14 x) atTop (𝓝 ((0 : ℝ) + 0)) :=
      hε13t.add hε14t
    have heq : (fun x => |ε13 x + ε14 x|) = fun x => ε13 x + ε14 x := by
      funext x
      exact abs_of_nonneg (add_nonneg (hε13nn x) (hε14nn x))
    rw [heq]
    simpa using hsum
  · rw [SieveBounds]
    have h13ev : ∀ᶠ x : ℕ in atTop,
        weightSum (W x) (b x) x (fun m => (tpWeight c f x (D x) H m) ^ 2) ≤
          (tpAlpha c f + ε13 x) * prefOne x (W x) (n + 1) :=
      (eventually_ge_atTop x₁).mono fun x hx => hb13 x hx
    have h14ev : ∀ᶠ x : ℕ in atTop, ∀ i₀ : Fin (n + 1),
        (tpBeta c f i₀ - ε14 x) * prefTwo x (W x) n ≤
          thetaWeightSum (W x) (b x) x (fun m => (tpWeight c f x (D x) H m) ^ 2) (H i₀) :=
      (eventually_ge_atTop x₂).mono fun x hx i₀ => hb14 x hx i₀
    have hW1ev : ∀ᶠ x : ℕ in atTop, 1 ≤ W x :=
      Filter.Eventually.of_forall fun x => Nat.one_le_iff_ne_zero.mpr (hW x)
    have hx2ev : ∀ᶠ x : ℕ in atTop, 2 ≤ x := eventually_ge_atTop 2
    filter_upwards [h13ev, h14ev, hW1ev, hx2ev] with x h13x h14x hW1x hx2
    have habs : |ε13 x + ε14 x| = ε13 x + ε14 x :=
      abs_of_nonneg (add_nonneg (hε13nn x) (hε14nn x))
    have hp1 : 0 ≤ prefOne x (W x) (n + 1) := by
      rw [prefOne_eq_mainScale]
      exact le_of_lt (mainScale_pos (hW x) hx2 (n + 1))
    have hp2 : 0 ≤ prefTwo x (W x) n := by
      rw [← thetaMainScale_eq_prefTwo x (W x) n]
      exact le_of_lt (thetaMainScale_pos (k := n) (Wf := fun _ => W x) (by simpa using hW x) hx2)
    refine ⟨hW1x, fun m => sq_nonneg _, ?_, ?_⟩
    · rw [habs]
      have h1 : tpAlpha c f + ε13 x ≤ tpAlpha c f + (ε13 x + ε14 x) := by linarith [hε14nn x]
      have h2 := mul_le_mul_of_nonneg_right h1 hp1
      linarith [h2, h13x]
    · intro i
      rw [habs, show n + 1 - 1 = n from by omega]
      have h1 : tpBeta c f i - (ε13 x + ε14 x) ≤ tpBeta c f i - ε14 x := by linarith [hε13nn x]
      have h2 := mul_le_mul_of_nonneg_right h1 hp2
      linarith [h2, h14x i]

/-- **`DHL[k,2]` from the tensor-product sieve** (Polymath8a Theorem 3.2, given the
sieve asymptotics and the level of distribution): if the variational ratio
`Σ_i β_i/α` of the tensor-product test function exceeds `1`, then every admissible
tuple `H` has arbitrarily large translates with at least two prime values. -/
theorem translate_two_primes_of_tpWeight {J n : ℕ} (hn : 1 ≤ n) (hJ : 1 ≤ J)
    (c : Fin J → ℝ) (f : Fin J → Fin (n + 1) → ℝ → ℝ) (H : Fin (n + 1) → ℕ)
    (hHmax : ∃ hmax : ℕ, ∀ i : Fin (n + 1), H i ≤ hmax)
    (hHinj : Function.Injective H)
    (hcs : ∀ j i, HasCompactSupport (f j i)) (hsm : ∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j i))
    (M : Fin J → Fin (n + 1) → ℝ) (hMnn : ∀ j i, 0 ≤ M j i)
    (hsupp : ∀ j i t, M j i < |t| → f j i t = 0)
    (hfb : ∀ j i t, 1 ≤ t → f j i t = 0)
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1 / 2) (hMsum : ∀ j, ∑ i, M j i < ϑ / 2)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x))
    (hlev : levelOfDistribution ϑ)
    (hWlog : ∃ A₀ : ℕ, ∀ᶠ x : ℕ in atTop, (W x : ℝ) ≤ (Real.log (x : ℝ)) ^ A₀)
    (hsep : ∀ᶠ x : ℕ in atTop, ∀ i j : Fin (n + 1), i ≠ j → H j - H i < w x)
    (D : ℕ → ℕ) (hD1 : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (2 * (∑ j, ∑ i, M j i)) ≤ (D x : ℝ))
    (hD2 : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ ϑ ≤ (D x : ℝ))
    (hα : 0 < tpAlpha c f)
    (hkey : tpAlpha c f < ∑ i : Fin (n + 1), tpBeta c f i) :
    ∀ N0 : ℕ, ∃ m : ℕ, N0 ≤ m ∧ 2 ≤ primeIndexCard H m := by
  obtain ⟨ε, hε, hB⟩ := sieveBounds_of_tpWeight hn hJ c f H hHinj hcs hsm M hMnn hsupp hfb
    hϑ0 hϑ1 hMsum W hW w hw hsmall hlq b hbW hlev hWlog hsep D hD1 hD2
  exact translate_two_primes_of_sieve_bounds (k := n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    hHmax hα hkey hε hB


end Commons.NumberTheory.MaynardSieve
