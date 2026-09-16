import Mathlib
import Submission.SieveWeight
import Submission.SieveWeightSep

open scoped BigOperators Topology
open Finset Filter

set_option maxHeartbeats 4000000

/-!
# The `J₁`/`J₂` split of the tensor-product sieve weight (Polymath8a §5.3)

Polymath8a §5.3 produces, from a variational lower bound `M_{k,ε} > 2m/ϑ`, a
sieve weight

  `ν(n) = (Σ_{j=1}^J c_j λ_{f_{1,j}}(n+h_1)···λ_{f_{k,j}}(n+h_k))²`

whose tensor-product components `f_{1,j} ⊗ ⋯ ⊗ f_{k,j}` are supported in
`{Σ_i max(t_i, δ) ≤ (1+ε)ϑ/2 - δ}`, i.e. only

  `Σ_i S(f_{i,j}) ≤ (1+ε)ϑ/2  -  δ      (87)`

— *not* the per-component bound `ϑ/2` needed by
`SieveWeight.thetaWeightSum_tpWeight_ge`.  In exchange, the `(1+ε)` factor buys
exactly the `ε`-enlargement of the variational problem, and the price is the
split of the index set `{1,…,J} = J₁ ⊔ J₂` according to

  `j ∈ J₁  ⟺  Σ_{i<k} S(f_{i,j}) < (1-ε)ϑ/2      (90)`

(Polymath8a (90)).  For `j ∈ J₁ ∪ J₂` and `j′ ∈ J₁` one then has
`Σ_{i<k}(S(f_{i,j}) + S(f_{i,j′})) < ϑ`, so Theorem 3.5(i) is available for the
*mixed* pairs, and the pointwise inequality

  `(x₁ + x₂)² ≥ (x₁ + 2x₂)·x₁      (x₁ = Σ_{J₁}, x₂ = Σ_{J₂})`

turns the `θ`-sum of the full square into the `θ`-sum of the *restricted*
double sum over `(J₁ ∪ J₂) × J₁` (Polymath8a (91)).

This module formalises that final combinatorial step:

* `thetaWeightSum_mul_tpWeight` — the bilinear expansion of the `θ`-weighted
  window sum of a product of two tensor-product weights;
* `thetaPair_asymptotic` — the per-pair asymptotic (Theorem 3.5(i) with the
  `(k-1)`-tuple obtained by deleting `H i₀`);
* `tpBetaSplit` — the restricted coefficient `β_i` of (91);
* `translate_two_primes_of_tpWeight_split` — the criterion: the *pairwise*
  support conditions (87) plus `tpAlpha c f < Σ_i tpBetaSplit c f S i` imply
  `DHL[k,2]`.
-/

namespace Commons.NumberTheory.MaynardSieve

attribute [local instance] Classical.propDecidable

/-! ## The bilinear expansion of the `θ`-weighted window sum -/

/-- **Bilinear expansion for `S₂`.**  For two coefficient families `A, B` and a
common family of component functions `f`, the `θ`-weighted window sum of the
product `tpWeight A f · tpWeight B f` expands into the `J²` pairwise window sums,
with the factor `λ_{f_{j,i₀}}` collapsing to `f_{j,i₀}(0)` (Polymath8a (20)). -/
theorem thetaWeightSum_mul_tpWeight {J n : ℕ} (A B : Fin J → ℝ)
    (f : Fin J → Fin (n + 1) → ℝ → ℝ) (H : Fin (n + 1) → ℕ) (i₀ : Fin (n + 1))
    (W b D N : ℕ) (hD : 1 ≤ D) (hR : 1 < N)
    (hfb : ∀ (j : Fin J) (l : Fin (n + 1)) (t : ℝ), 1 ≤ t → f j l t = 0) :
    thetaWeightSum W b N (fun m => tpWeight A f N D H m * tpWeight B f N D H m)
        (H i₀) =
      ∑ j : Fin J, ∑ j' : Fin J, A j * B j' * (f j i₀ 0) * (f j' i₀ 0) *
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
  have hexp : ∀ (m : ℕ), tpWeight A f N D H m * tpWeight B f N D H m =
      ∑ j : Fin J, ∑ j' : Fin J, A j * B j' *
        ((∏ i : Fin (n + 1), lamDivSum (f j i) N D (m + H i)) *
         (∏ i : Fin (n + 1), lamDivSum (f j' i) N D (m + H i))) := by
    intro m
    rw [tpWeight, tpWeight, Finset.sum_mul_sum]
    simp only [prodLamDivSum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    ring
  have hpt : ∀ m ∈ residueWindow N W b,
      tpWeight A f N D H m * tpWeight B f N D H m * thetaNat (m + H i₀) =
        (∑ j : Fin J, ∑ j' : Fin J, A j * B j' * (f j i₀ 0) * (f j' i₀ 0) *
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
        (∑ j : Fin J, ∑ j' : Fin J, A j * B j' * (f j i₀ 0) * (f j' i₀ 0) *
          ((∏ a : Fin n, lamDivSum (f j (i₀.succAbove a)) N D (m + H (i₀.succAbove a))) *
           (∏ a : Fin n, lamDivSum (f j' (i₀.succAbove a)) N D (m + H (i₀.succAbove a))))) *
        thetaNat (m + H i₀)) =
      ∑ m ∈ residueWindow N W b, ∑ j : Fin J, ∑ j' : Fin J,
        A j * B j' * (f j i₀ 0) * (f j' i₀ 0) *
          ((∏ a : Fin n, lamDivSum (f j (i₀.succAbove a)) N D (m + H (i₀.succAbove a))) *
           (∏ a : Fin n, lamDivSum (f j' (i₀.succAbove a)) N D (m + H (i₀.succAbove a)))) *
        thetaNat (m + H i₀) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Finset.sum_mul]
  rw [hL]
  have hstep1 : (∑ m ∈ residueWindow N W b, ∑ j : Fin J, ∑ j' : Fin J,
        A j * B j' * (f j i₀ 0) * (f j' i₀ 0) *
          ((∏ a : Fin n, lamDivSum (f j (i₀.succAbove a)) N D (m + H (i₀.succAbove a))) *
           (∏ a : Fin n, lamDivSum (f j' (i₀.succAbove a)) N D (m + H (i₀.succAbove a)))) *
        thetaNat (m + H i₀)) =
      ∑ j : Fin J, ∑ j' : Fin J, A j * B j' * (f j i₀ 0) * (f j' i₀ 0) *
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


/-! ## The per-pair `S₂` asymptotic -/

/-- **Per-pair `S₂` asymptotic.**  Polymath8a Theorem 3.5(i) applied to the
`(k-1)`-tuple obtained by deleting `H i₀`, for a single pair `(j, j′)` of
component families.  This is the per-pair content of
`SieveWeight.thetaWeightSum_tpWeight_ge_pairwise`. -/
theorem thetaPair_asymptotic {J n : ℕ} (hn : 1 ≤ n) (j j' : Fin J)
    (f : Fin J → Fin (n + 1) → ℝ → ℝ) (H : Fin (n + 1) → ℕ) (i₀ : Fin (n + 1))
    (hHinj : Function.Injective H)
    (hcs : ∀ l, HasCompactSupport (f j l)) (hsm : ∀ l, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j l))
    (hcs' : ∀ l, HasCompactSupport (f j' l)) (hsm' : ∀ l, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j' l))
    (hfb : ∀ l t, 1 ≤ t → f j l t = 0) (hfb' : ∀ l t, 1 ≤ t → f j' l t = 0)
    (M : Fin J → Fin (n + 1) → ℝ) (hMnn : ∀ l, 0 ≤ M j l) (hMnn' : ∀ l, 0 ≤ M j' l)
    (hsupp : ∀ l t, M j l < |t| → f j l t = 0)
    (hsupp' : ∀ l t, M j' l < |t| → f j' l t = 0)
    {BF : ℝ} (hBF0 : 0 ≤ BF) (hBFbd : ∀ l t, |f j l t| ≤ BF ∧ |f j' l t| ≤ BF)
    {Mtot : ℝ} (hMtot0 : 0 ≤ Mtot) (hMtot : ∀ l, M j l ≤ Mtot ∧ M j' l ≤ Mtot)
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1 / 2)
    (hpair : ∑ a : Fin n, (M j (i₀.succAbove a) + M j' (i₀.succAbove a)) < ϑ)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (b : ℕ → ℕ) (hbW : ∀ᶠ x : ℕ in atTop, ∀ l : Fin (n + 1), (b x + H l).Coprime (W x))
    (hlev : levelOfDistribution ϑ)
    (hWlog : ∃ A₀ : ℕ, ∀ᶠ x : ℕ in atTop, (W x : ℝ) ≤ (Real.log (x : ℝ)) ^ A₀)
    (hsep : ∀ᶠ x : ℕ in atTop, ∀ a c : Fin (n + 1), a ≠ c → H c - H a < w x)
    (D : ℕ → ℕ) (hDM : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ Mtot ≤ (D x : ℝ))
    (hDϑ : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ ϑ ≤ (D x : ℝ)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ x : ℕ, x₀ ≤ x →
      |thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
          (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
          (fun a => lamDivWeight (f j' (i₀.succAbove a)) x) -
        thetaMainTerm (fun a => f j (i₀.succAbove a)) (fun a => f j' (i₀.succAbove a))
          (fun _ => W x) x| ≤
        ε x * thetaMainScale (k := n) (fun _ => W x) x := by
  classical
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
    (fun a => hcs (i₀.succAbove a)) (fun a => hsm (i₀.succAbove a))
    (fun a => hcs' (i₀.succAbove a)) (fun a => hsm' (i₀.succAbove a))
    W hW w hw hsmall hlq hBF0 hBF0
    (fun a t => (hBFbd (i₀.succAbove a) t).1) (fun a t => (hBFbd (i₀.succAbove a) t).2)
    (fun a t ht => ⟨hsupp (i₀.succAbove a) t (lt_of_le_of_lt (hMtot _).1 ht),
      hsupp' (i₀.succAbove a) t (lt_of_le_of_lt (hMtot _).2 ht)⟩)
    hϑ0 hϑ1 (fun a => hMnn (i₀.succAbove a)) (fun a => hMnn' (i₀.succAbove a))
    (fun a t ht => hsupp (i₀.succAbove a) t ht)
    (fun a t ht => hsupp' (i₀.succAbove a) t ht)
    hpair b (H i₀) (fun a => H (i₀.succAbove a)) hHinj'
    (hbW.mono fun x hx a => hx (i₀.succAbove a))
    (hbW.mono fun x hx => hx i₀) hhne'
    w (Filter.Eventually.of_forall fun x => le_rfl) hsep' hseph' hlev hWlog D hDM hDϑ


/-! ## The restricted coefficients and the pointwise inequality -/

/-- The coefficient family of the `J₁`-part `x₁ + 2x₂` of the split. -/
noncomputable def splitA {J : ℕ} (S : Finset (Fin J)) (c : Fin J → ℝ) : Fin J → ℝ :=
  fun j => if j ∈ S then c j else 2 * c j

/-- The coefficient family of the `J₁`-part `x₁` of the split. -/
noncomputable def splitB {J : ℕ} (S : Finset (Fin J)) (c : Fin J → ℝ) : Fin J → ℝ :=
  fun j => if j ∈ S then c j else 0

/-- **The restricted `S₂` coefficient** `β_i` of Polymath8a (91). -/
noncomputable def tpBetaSplit {k J : ℕ} (S : Finset (Fin J)) (c : Fin J → ℝ)
    (f : Fin J → Fin k → ℝ → ℝ) (i : Fin k) : ℝ :=
  ∑ j : Fin J, ∑ j' ∈ S, (if j ∈ S then c j * c j' else 2 * (c j * c j')) *
    (f j i 0) * (f j' i 0) *
    ∏ l ∈ (Finset.univ.erase i),
      (∫ t : ℝ in Set.Ioi 0, deriv (f j l) t * deriv (f j' l) t)

/-- The double sum with the split coefficients equals the restricted double sum
over `(J₁ ∪ J₂) × J₁` with the weight `1` on `J₁ × J₁` and `2` on `J₂ × J₁`. -/
theorem sum_splitA_mul_splitB {J : ℕ} (S : Finset (Fin J)) (c : Fin J → ℝ)
    (X : Fin J → Fin J → ℝ) :
    (∑ j : Fin J, ∑ j' : Fin J, splitA S c j * splitB S c j' * X j j') =
      ∑ j : Fin J, ∑ j' ∈ S, (if j ∈ S then c j * c j' else 2 * (c j * c j')) * X j j' := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (∑ j' : Fin J, splitA S c j * splitB S c j' * X j j')
      = ∑ j' ∈ S, splitA S c j * splitB S c j' * X j j' from by
    symm
    exact Finset.sum_subset (Finset.subset_univ S) (fun j' _ hj' => by
      rw [splitB, if_neg hj', mul_zero, zero_mul])]
  refine Finset.sum_congr rfl fun j' hj' => ?_
  rw [splitA, splitB, if_pos hj']
  by_cases hj : j ∈ S
  · simp only [hj, if_true]
  · simp only [hj, if_false]; ring

/-- **The pointwise split inequality.**  With `x₁ = Σ_{j∈J₁}`, `x₂ = Σ_{j∈J₂}`,
`(x₁ + 2x₂)·x₁ ≤ (x₁ + x₂)²`. -/
theorem tpWeight_split_mul_le {k J : ℕ} (S : Finset (Fin J)) (c : Fin J → ℝ)
    (f : Fin J → Fin k → ℝ → ℝ) (N D : ℕ) (H : Fin k → ℕ) (n : ℕ) :
    tpWeight (splitA S c) f N D H n * tpWeight (splitB S c) f N D H n ≤
      (tpWeight c f N D H n) ^ 2 := by
  simp only [tpWeight]
  set P : Fin J → ℝ := fun j => prodLamDivSum (f j) N D H n with hP
  have hA : (∑ j : Fin J, splitA S c j * P j) =
      (∑ j ∈ S, c j * P j) + 2 * (∑ j ∈ (Finset.univ \ S), c j * P j) := by
    rw [show (∑ j : Fin J, splitA S c j * P j)
        = (∑ j ∈ S, splitA S c j * P j) + (∑ j ∈ (Finset.univ \ S), splitA S c j * P j) from by
      rw [← Finset.sum_sdiff (Finset.subset_univ S)]; ring]
    have hcomp : (∑ j ∈ (Finset.univ \ S), splitA S c j * P j) =
        2 * (∑ j ∈ (Finset.univ \ S), c j * P j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_sdiff] at hj
      rw [splitA, if_neg hj.2]; ring
    have hS : (∑ j ∈ S, splitA S c j * P j) = ∑ j ∈ S, c j * P j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [splitA, if_pos hj]
    rw [hS, hcomp]
  have hB : (∑ j : Fin J, splitB S c j * P j) = ∑ j ∈ S, c j * P j := by
    rw [show (∑ j : Fin J, splitB S c j * P j)
        = ∑ j ∈ S, splitB S c j * P j from by
      symm
      exact Finset.sum_subset (Finset.subset_univ S) (fun j' _ hj' => by
        rw [splitB, if_neg hj', zero_mul])]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [splitB, if_pos hj]
  have hC : (∑ j : Fin J, c j * P j) =
      (∑ j ∈ S, c j * P j) + (∑ j ∈ (Finset.univ \ S), c j * P j) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ S)]; ring
  rw [hA, hB, hC]
  nlinarith [sq_nonneg (∑ j ∈ (Finset.univ \ S), c j * P j)]

/-! ## The split criterion -/

/-- **`DHL[k,2]` from the split tensor-product sieve.**  This is the combinatorial
content of Polymath8a §5.3: with the *pairwise* support conditions (87), the
pointwise inequality `(x₁+x₂)² ≥ (x₁+2x₂)x₁` together with Theorem 3.5(i) applied
to the mixed pairs `(J₁ ∪ J₂) × J₁` gives the `S₂` lower bound with the restricted
coefficient `tpBetaSplit`, while the `S₁` upper bound still uses the full square
with `tpAlpha`. -/
theorem translate_two_primes_of_tpWeight_split_family {J n : ℕ} (hn : 1 ≤ n) (hJ : 1 ≤ J)
    (c : Fin J → ℝ) (f : Fin J → Fin (n + 1) → ℝ → ℝ) (H : Fin (n + 1) → ℕ)
    (Sf : Fin (n + 1) → Finset (Fin J))
    (hHmax : ∃ hmax : ℕ, ∀ i : Fin (n + 1), H i ≤ hmax)
    (hHinj : Function.Injective H)
    (hcs : ∀ j i, HasCompactSupport (f j i)) (hsm : ∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j i))
    (M : Fin J → Fin (n + 1) → ℝ) (hMnn : ∀ j i, 0 ≤ M j i)
    (hsupp : ∀ j i t, M j i < |t| → f j i t = 0)
    (hfb : ∀ j i t, 1 ≤ t → f j i t = 0)
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1 / 2)
    (hM1 : ∀ j j', (∑ i, (M j i + M j' i)) < 1)
    (Mtop : ℝ) (hMtop : ∀ j i, M j i ≤ Mtop)
    (hM2 : ∀ j j' (i₀ : Fin (n + 1)), j' ∈ Sf i₀ →
      ∑ i ∈ Finset.univ.erase i₀, (M j i + M j' i) < ϑ)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x))
    (hlev : levelOfDistribution ϑ)
    (hWlog : ∃ A₀ : ℕ, ∀ᶠ x : ℕ in atTop, (W x : ℝ) ≤ (Real.log (x : ℝ)) ^ A₀)
    (hsep : ∀ᶠ x : ℕ in atTop, ∀ i j : Fin (n + 1), i ≠ j → H j - H i < w x)
    (D : ℕ → ℕ) (hD1 : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ Mtop ≤ (D x : ℝ))
    (hD2 : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ ϑ ≤ (D x : ℝ))
    (hα : 0 < tpAlpha c f)
    (hkey : tpAlpha c f < ∑ i : Fin (n + 1), tpBetaSplit (Sf i) c f i) :
    ∀ N0 : ℕ, ∃ m : ℕ, N0 ≤ m ∧ 2 ≤ primeIndexCard H m := by
  classical
  -- §1  the `S₁` bound (full square, pairwise support condition)
  obtain ⟨x₁, ε₁, hε₁t, hε₁nn, hb₁⟩ :=
    weightSum_tpWeight_le_pairwise_sep (k := n + 1) (by omega) hJ c f H hHinj hcs hsm M hMnn
      hsupp hM1 (fun j i t ht => hsupp j i t (lt_of_le_of_lt (hMtop j i) ht))
      W hW w hw hsmall hlq D hD1 b hbW
  -- §2  a uniform bound for the components
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
  -- §3  a uniform bound for the support radii
  set Mtot : ℝ := Mtop with hMtotdef
  have hMtotnn : 0 ≤ Mtot := by
    rw [hMtotdef]
    exact le_trans (hMnn ⟨0, hJ⟩ ⟨0, Nat.succ_pos n⟩) (hMtop ⟨0, hJ⟩ ⟨0, Nat.succ_pos n⟩)
  have hMtot_le : ∀ j i, M j i ≤ Mtot := by
    intro j i
    rw [hMtotdef]
    exact hMtop j i
  -- §4  the per-pair `S₂` asymptotics (only the pairs with `j' ∈ Sf i₀` are needed)
  have hpairTot : ∀ p : Fin J × Fin J × Fin (n + 1),
      ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        (p.2.1 ∈ Sf p.2.2 → ∀ x : ℕ, x₀ ≤ x →
          |thetaWindowSum x (W x) (b x) (H p.2.2) (D x) (fun a => H (p.2.2.succAbove a))
              (fun a => lamDivWeight (f p.1 (p.2.2.succAbove a)) x)
              (fun a => lamDivWeight (f p.2.1 (p.2.2.succAbove a)) x) -
            thetaMainTerm (fun a => f p.1 (p.2.2.succAbove a))
              (fun a => f p.2.1 (p.2.2.succAbove a)) (fun _ => W x) x| ≤
            ε x * thetaMainScale (k := n) (fun _ => W x) x) := by
    rintro ⟨j, j', i₀⟩
    by_cases hj' : j' ∈ Sf i₀
    · have hsum' : (∑ a : Fin n, (M j (i₀.succAbove a) + M j' (i₀.succAbove a))) < ϑ := by
        rw [← sum_erase_eq_sum_succAbove i₀ (fun l => M j l + M j' l)]
        exact hM2 j j' i₀ hj'
      obtain ⟨x₀, ε, ht, hb⟩ :=
        thetaPair_asymptotic hn j j' f H i₀ hHinj (fun l => hcs j l) (fun l => hsm j l)
          (fun l => hcs j' l) (fun l => hsm j' l)
          (fun l t => hfb j l t) (fun l t => hfb j' l t)
          M (fun l => hMnn j l) (fun l => hMnn j' l)
          (fun l t => hsupp j l t) (fun l t => hsupp j' l t)
          hBF0 (fun l t => ⟨hBFbd j l t, hBFbd j' l t⟩) hMtotnn
          (fun l => ⟨hMtot_le j l, hMtot_le j' l⟩)
          hϑ0 hϑ1 hsum' W hW w hw hsmall hlq b (Filter.Eventually.of_forall hbW)
          hlev hWlog hsep D (by simpa [hMtotdef] using hD1) hD2
      exact ⟨x₀, ε, ht, fun _ x hx => hb x hx⟩
    · exact ⟨0, fun _ => 0, tendsto_const_nhds, fun hh => absurd hh hj'⟩
  choose x₀p εp hεpT hεpB using hpairTot
  -- §5  the combined error
  set ε₂ : ℕ → ℝ := fun x => ∑ j : Fin J, ∑ j' : Fin J, ∑ i : Fin (n + 1),
      |splitA (Sf i) c j * splitB (Sf i) c j' * f j i 0 * f j' i 0| * |εp (j, j', i) x|
    with hε₂def
  have hε₂nn : ∀ x, 0 ≤ ε₂ x := by
    intro x
    rw [hε₂def]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun j' _ =>
      Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hε₂t : Tendsto (fun x : ℕ => |ε₂ x|) atTop (𝓝 0) := by
    have hη : ∀ p : Fin J × Fin J × Fin (n + 1),
        Tendsto (fun x => |εp p x|) atTop (𝓝 (0 : ℝ)) := by
      intro p
      have h := (hεpT p).abs
      simpa using h
    have heq : (fun x : ℕ => |ε₂ x|) = fun x : ℕ => ∑ j : Fin J, ∑ j' : Fin J,
        ∑ i : Fin (n + 1),
        |splitA (Sf i) c j * splitB (Sf i) c j' * f j i 0 * f j' i 0| * |εp (j, j', i) x| := by
      funext x
      rw [hε₂def, abs_of_nonneg (hε₂nn x)]
    rw [heq]
    have hmain : Tendsto (fun x : ℕ => ∑ j : Fin J, ∑ j' : Fin J, ∑ i : Fin (n + 1),
        |splitA (Sf i) c j * splitB (Sf i) c j' * f j i 0 * f j' i 0| * |εp (j, j', i) x|) atTop
        (𝓝 (∑ j : Fin J, ∑ j' : Fin J, ∑ i : Fin (n + 1),
          |splitA (Sf i) c j * splitB (Sf i) c j' * f j i 0 * f j' i 0| * 0)) := by
      refine tendsto_finsetSum (Finset.univ : Finset (Fin J)) (fun j _ => ?_)
      refine tendsto_finsetSum (Finset.univ : Finset (Fin J)) (fun j' _ => ?_)
      refine tendsto_finsetSum (Finset.univ : Finset (Fin (n + 1))) (fun i _ => ?_)
      exact tendsto_const_nhds.mul (hη (j, j', i))
    simpa using hmain
  have hε₂t' : Tendsto ε₂ atTop (𝓝 0) := by
    have h : ε₂ = fun x : ℕ => |ε₂ x| := funext fun x => (abs_of_nonneg (hε₂nn x)).symm
    rw [h]; exact hε₂t
  -- §6  the sieve bounds
  refine translate_two_primes_of_sieve_bounds (k := n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    hHmax hα hkey (ε := fun x => ε₁ x + ε₂ x)
    (ν := fun x m => (tpWeight c f x (D x) H m) ^ 2) (W := W) (b := b) ?_ ?_
  · have hsum : Tendsto (fun x => ε₁ x + ε₂ x) atTop (𝓝 ((0 : ℝ) + 0)) := hε₁t.add hε₂t'
    have heq : (fun x => |ε₁ x + ε₂ x|) = fun x => ε₁ x + ε₂ x := by
      funext x
      exact abs_of_nonneg (add_nonneg (hε₁nn x) (hε₂nn x))
    rw [heq]
    simpa using hsum
  · rw [SieveBounds]
    have h13ev : ∀ᶠ x : ℕ in atTop,
        weightSum (W x) (b x) x (fun m => (tpWeight c f x (D x) H m) ^ 2) ≤
          (tpAlpha c f + ε₁ x) * prefOne x (W x) (n + 1) :=
      (eventually_ge_atTop x₁).mono fun x hx => hb₁ x hx
    have h14ev : ∀ᶠ x : ℕ in atTop, ∀ i₀ : Fin (n + 1),
        (tpBetaSplit (Sf i₀) c f i₀ - ε₂ x) * prefTwo x (W x) n ≤
          thetaWeightSum (W x) (b x) x (fun m => (tpWeight c f x (D x) H m) ^ 2) (H i₀) := by
      -- for all large `x`
      have hsup : (Finset.univ : Finset (Fin J × Fin J × Fin (n + 1))).Nonempty :=
        ⟨(⟨0, hJ⟩, ⟨0, hJ⟩, ⟨0, Nat.succ_pos n⟩), Finset.mem_univ _⟩
      filter_upwards [hD1, hD2, eventually_ge_atTop (max 2 ((Finset.univ :
        Finset (Fin J × Fin J × Fin (n + 1))).sup' hsup x₀p))] with x hD1x hD2x hxbig
      intro i₀
      have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hxbig
      have hx0 : ∀ p : Fin J × Fin J × Fin (n + 1), x₀p p ≤ x := fun p =>
        le_trans (Finset.le_sup' x₀p (Finset.mem_univ p)) (le_trans (le_max_right _ _) hxbig)
      have hDx1 : 1 ≤ D x := by
        have h0 : (1 : ℝ) ≤ (x : ℝ) ^ Mtot :=
          Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ x)) hMtotnn
        have h1 : (1 : ℝ) ≤ (D x : ℝ) := le_trans h0 (by simpa [hMtotdef] using hD1x)
        exact_mod_cast h1
      have hRx : 1 < x := by omega
      set sc : ℝ := thetaMainScale (k := n) (fun _ => W x) x with hscdef
      have hscpos : 0 < sc := by
        rw [hscdef]
        exact thetaMainScale_pos (k := n) (Wf := fun _ => W x) (by simpa using hW x) hx2
      -- §6.1  monotonicity: the `θ`-sum of `ν'` is below that of the full square
      have hmono : thetaWeightSum (W x) (b x) x
          (fun m => tpWeight (splitA (Sf i₀) c) f x (D x) H m *
            tpWeight (splitB (Sf i₀) c) f x (D x) H m) (H i₀) ≤
          thetaWeightSum (W x) (b x) x (fun m => (tpWeight c f x (D x) H m) ^ 2) (H i₀) := by
        rw [thetaWeightSum, thetaWeightSum]
        refine Finset.sum_le_sum fun m _ => ?_
        exact mul_le_mul_of_nonneg_right (tpWeight_split_mul_le (Sf i₀) c f x (D x) H m)
          (thetaNat_nonneg _)
      -- §6.2  the bilinear expansion of `θ`-sum of `ν'`
      have hexp : thetaWeightSum (W x) (b x) x
          (fun m => tpWeight (splitA (Sf i₀) c) f x (D x) H m *
            tpWeight (splitB (Sf i₀) c) f x (D x) H m) (H i₀) =
          ∑ j : Fin J, ∑ j' ∈ Sf i₀, (if j ∈ Sf i₀ then c j * c j' else 2 * (c j * c j')) *
            (f j i₀ 0) * (f j' i₀ 0) *
            thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
              (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
              (fun a => lamDivWeight (f j' (i₀.succAbove a)) x) := by
        have h1 : thetaWeightSum (W x) (b x) x
            (fun m => tpWeight (splitA (Sf i₀) c) f x (D x) H m *
              tpWeight (splitB (Sf i₀) c) f x (D x) H m) (H i₀) =
            ∑ j : Fin J, ∑ j' : Fin J, splitA (Sf i₀) c j * splitB (Sf i₀) c j' *
              ((f j i₀ 0) * (f j' i₀ 0) *
                thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
                  (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
                  (fun a => lamDivWeight (f j' (i₀.succAbove a)) x)) := by
          rw [thetaWeightSum_mul_tpWeight (splitA (Sf i₀) c) (splitB (Sf i₀) c) f H i₀ (W x) (b x) (D x) x
            hDx1 hRx (fun j l t ht => hfb j l t ht)]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          ring
        have h2 := sum_splitA_mul_splitB (Sf i₀) c (fun j j' => (f j i₀ 0) * (f j' i₀ 0) *
          thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
            (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
            (fun a => lamDivWeight (f j' (i₀.succAbove a)) x))
        rw [h1, h2]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
        ring
      -- §6.3  the main term of the restricted double sum
      have hmainid : (∑ j : Fin J, ∑ j' ∈ Sf i₀, (if j ∈ Sf i₀ then c j * c j' else 2 * (c j * c j')) *
            (f j i₀ 0) * (f j' i₀ 0) *
            thetaMainTerm (fun a => f j (i₀.succAbove a))
              (fun a => f j' (i₀.succAbove a)) (fun _ => W x) x) =
          tpBetaSplit (Sf i₀) c f i₀ * sc := by
        rw [tpBetaSplit, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [thetaMainTerm, prod_erase_eq_prod_succAbove, ← hscdef]
        ring
      -- §6.4  per-pair two-sided comparison
      have hper : ∀ j : Fin J, ∀ j' ∈ Sf i₀,
          (if j ∈ Sf i₀ then c j * c j' else 2 * (c j * c j')) * (f j i₀ 0) * (f j' i₀ 0) *
              thetaMainTerm (fun a => f j (i₀.succAbove a))
                (fun a => f j' (i₀.succAbove a)) (fun _ => W x) x ≤
            (if j ∈ Sf i₀ then c j * c j' else 2 * (c j * c j')) * (f j i₀ 0) * (f j' i₀ 0) *
              thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
                (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
                (fun a => lamDivWeight (f j' (i₀.succAbove a)) x) +
            |(if j ∈ Sf i₀ then c j * c j' else 2 * (c j * c j')) * (f j i₀ 0) * (f j' i₀ 0)| *
              (|εp (j, j', i₀) x| * sc) := by
        intro j j' hj'
        have h := hεpB (j, j', i₀) hj' x (hx0 (j, j', i₀))
        have hεpnn : 0 ≤ εp (j, j', i₀) x := by
          have h0 : (0 : ℝ) ≤ εp (j, j', i₀) x *
              thetaMainScale (k := n) (fun _ => W x) x := le_trans (abs_nonneg _) h
          nlinarith [h0, hscpos]
        dsimp only at h
        rw [← hscdef, ← abs_of_nonneg hεpnn] at h
        have h1 : thetaMainTerm (fun a => f j (i₀.succAbove a))
              (fun a => f j' (i₀.succAbove a)) (fun _ => W x) x -
              |εp (j, j', i₀) x| * sc ≤
            thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
              (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
              (fun a => lamDivWeight (f j' (i₀.succAbove a)) x) := by
          linarith [(abs_le.mp h).1]
        by_cases hc : 0 ≤ (if j ∈ Sf i₀ then c j * c j' else 2 * (c j * c j')) *
            (f j i₀ 0) * (f j' i₀ 0)
        · have hthis := mul_le_mul_of_nonneg_left h1 hc
          rw [abs_of_nonneg hc]
          linarith [hthis]
        · have hc' : (if j ∈ Sf i₀ then c j * c j' else 2 * (c j * c j')) *
              (f j i₀ 0) * (f j' i₀ 0) < 0 := lt_of_not_ge hc
          have h2 : thetaWindowSum x (W x) (b x) (H i₀) (D x)
                (fun a => H (i₀.succAbove a))
                (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
                (fun a => lamDivWeight (f j' (i₀.succAbove a)) x) ≤
              thetaMainTerm (fun a => f j (i₀.succAbove a))
                (fun a => f j' (i₀.succAbove a)) (fun _ => W x) x +
                |εp (j, j', i₀) x| * sc := by linarith [(abs_le.mp h).2]
          have hthis := mul_le_mul_of_nonpos_left h2 (le_of_lt hc')
          rw [abs_of_neg hc']
          nlinarith [hthis]
      -- §6.5  the error estimate
      have hEps_ge : (∑ j : Fin J, ∑ j' ∈ Sf i₀,
            |(if j ∈ Sf i₀ then c j * c j' else 2 * (c j * c j')) * (f j i₀ 0) * (f j' i₀ 0)| *
              (|εp (j, j', i₀) x| * sc)) ≤ ε₂ x * sc := by
        have hcoef : ∀ j : Fin J, ∀ j' ∈ Sf i₀,
            |(if j ∈ Sf i₀ then c j * c j' else 2 * (c j * c j')) * (f j i₀ 0) * (f j' i₀ 0)| *
                |εp (j, j', i₀) x| =
              |splitA (Sf i₀) c j * splitB (Sf i₀) c j' * f j i₀ 0 * f j' i₀ 0| * |εp (j, j', i₀) x| := by
          intro j j' hj'
          have heq : (if j ∈ Sf i₀ then c j * c j' else 2 * (c j * c j')) * (f j i₀ 0) * (f j' i₀ 0) =
              splitA (Sf i₀) c j * splitB (Sf i₀) c j' * f j i₀ 0 * f j' i₀ 0 := by
            rw [splitA, splitB, if_pos hj']
            by_cases hj : j ∈ Sf i₀
            · simp only [hj, if_true]
            · simp only [hj, if_false]; ring
          rw [heq]
        have hstep : (∑ j : Fin J, ∑ j' ∈ Sf i₀,
              |splitA (Sf i₀) c j * splitB (Sf i₀) c j' * f j i₀ 0 * f j' i₀ 0| * |εp (j, j', i₀) x|) ≤
            ε₂ x := by
          rw [hε₂def]
          have h1 : (∑ j : Fin J, ∑ j' ∈ Sf i₀,
                |splitA (Sf i₀) c j * splitB (Sf i₀) c j' * f j i₀ 0 * f j' i₀ 0| *
                  |εp (j, j', i₀) x|) =
              ∑ j : Fin J, ∑ j' : Fin J,
                |splitA (Sf i₀) c j * splitB (Sf i₀) c j' * f j i₀ 0 * f j' i₀ 0| *
                  |εp (j, j', i₀) x| := by
            refine Finset.sum_congr rfl fun j _ => ?_
            exact Finset.sum_subset (Finset.subset_univ (Sf i₀))
              (fun j' _ hj' => by rw [splitB, if_neg hj']; simp)
          rw [h1]
          refine Finset.sum_le_sum fun j _ => ?_
          refine Finset.sum_le_sum fun j' _ => ?_
          exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin (n + 1))))
            (f := fun i : Fin (n + 1) =>
              |splitA (Sf i) c j * splitB (Sf i) c j' * f j i 0 * f j' i 0| * |εp (j, j', i) x|)
            (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i₀)
        have hL : (∑ j : Fin J, ∑ j' ∈ Sf i₀,
              |(if j ∈ Sf i₀ then c j * c j' else 2 * (c j * c j')) * (f j i₀ 0) * (f j' i₀ 0)| *
                (|εp (j, j', i₀) x| * sc)) =
            (∑ j : Fin J, ∑ j' ∈ Sf i₀,
              |splitA (Sf i₀) c j * splitB (Sf i₀) c j' * f j i₀ 0 * f j' i₀ 0| * |εp (j, j', i₀) x|) * sc := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j' hj' => ?_
          rw [← mul_assoc, hcoef j j' hj']
        rw [hL]
        exact mul_le_mul_of_nonneg_right hstep (le_of_lt hscpos)
      -- §6.6  assemble the `θ`-lower bound
      have hsum_per : (∑ j : Fin J, ∑ j' ∈ Sf i₀, (if j ∈ Sf i₀ then c j * c j' else 2 * (c j * c j')) *
            (f j i₀ 0) * (f j' i₀ 0) *
            thetaMainTerm (fun a => f j (i₀.succAbove a))
              (fun a => f j' (i₀.succAbove a)) (fun _ => W x) x) ≤
          (∑ j : Fin J, ∑ j' ∈ Sf i₀, (if j ∈ Sf i₀ then c j * c j' else 2 * (c j * c j')) *
            (f j i₀ 0) * (f j' i₀ 0) *
            thetaWindowSum x (W x) (b x) (H i₀) (D x) (fun a => H (i₀.succAbove a))
              (fun a => lamDivWeight (f j (i₀.succAbove a)) x)
              (fun a => lamDivWeight (f j' (i₀.succAbove a)) x)) +
          (∑ j : Fin J, ∑ j' ∈ Sf i₀,
            |(if j ∈ Sf i₀ then c j * c j' else 2 * (c j * c j')) * (f j i₀ 0) * (f j' i₀ 0)| *
              (|εp (j, j', i₀) x| * sc)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j' hj' => hper j j' hj'
      have hsum_ge : (tpBetaSplit (Sf i₀) c f i₀ - ε₂ x) * sc ≤
          thetaWeightSum (W x) (b x) x (fun m => (tpWeight c f x (D x) H m) ^ 2) (H i₀) := by
        rw [hmainid] at hsum_per
        rw [hexp] at hmono
        linarith [hmono, hsum_per, hEps_ge]
      -- convert to the `prefTwo` normalisation and absorb the `S₁` error
      rw [← thetaMainScale_eq_prefTwo x (W x) n]
      have hrelax : tpBetaSplit (Sf i₀) c f i₀ - (ε₁ x + ε₂ x) ≤ tpBetaSplit (Sf i₀) c f i₀ - ε₂ x := by
        linarith [hε₁nn x]
      have := mul_le_mul_of_nonneg_right hrelax (le_of_lt hscpos)
      linarith [this, hsum_ge]
    have hW1ev : ∀ᶠ x : ℕ in atTop, 1 ≤ W x :=
      Filter.Eventually.of_forall fun x => Nat.one_le_iff_ne_zero.mpr (hW x)
    have hx2ev : ∀ᶠ x : ℕ in atTop, 2 ≤ x := eventually_ge_atTop 2
    filter_upwards [h13ev, h14ev, hW1ev, hx2ev] with x h13x h14x hW1x hx2
    have habs : |ε₁ x + ε₂ x| = ε₁ x + ε₂ x :=
      abs_of_nonneg (add_nonneg (hε₁nn x) (hε₂nn x))
    have hp1 : 0 ≤ prefOne x (W x) (n + 1) := by
      rw [prefOne_eq_mainScale]
      exact le_of_lt (mainScale_pos (hW x) hx2 (n + 1))
    have hp2 : 0 ≤ prefTwo x (W x) n := by
      rw [← thetaMainScale_eq_prefTwo x (W x) n]
      exact le_of_lt (thetaMainScale_pos (k := n) (Wf := fun _ => W x) (by simpa using hW x) hx2)
    refine ⟨hW1x, fun m => sq_nonneg _, ?_, ?_⟩
    · rw [habs]
      have h1 : tpAlpha c f + ε₁ x ≤ tpAlpha c f + (ε₁ x + ε₂ x) := by linarith [hε₂nn x]
      have h2 := mul_le_mul_of_nonneg_right h1 hp1
      linarith [h2, h13x]
    · intro i
      rw [habs, show n + 1 - 1 = n from by omega]
      have h1 : tpBetaSplit (Sf i) c f i - (ε₁ x + ε₂ x) ≤ tpBetaSplit (Sf i) c f i - ε₂ x := by
        linarith [hε₁nn x]
      have h2 := mul_le_mul_of_nonneg_right h1 hp2
      linarith [h2, h14x i]

/-- **`DHL[k,2]` from the split tensor-product sieve** (single index-set form).  This is the
case `Sf = fun _ ↦ S` of `translate_two_primes_of_tpWeight_split_family`; the per-coordinate
form is what the §5.3 construction of Polymath8a actually meets (the `J₁` set of (90) can be
chosen separately for each `θ`-coordinate). -/
theorem translate_two_primes_of_tpWeight_split {J n : ℕ} (hn : 1 ≤ n) (hJ : 1 ≤ J)
    (c : Fin J → ℝ) (f : Fin J → Fin (n + 1) → ℝ → ℝ) (H : Fin (n + 1) → ℕ)
    (S : Finset (Fin J))
    (hHmax : ∃ hmax : ℕ, ∀ i : Fin (n + 1), H i ≤ hmax)
    (hHinj : Function.Injective H)
    (hcs : ∀ j i, HasCompactSupport (f j i)) (hsm : ∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j i))
    (M : Fin J → Fin (n + 1) → ℝ) (hMnn : ∀ j i, 0 ≤ M j i)
    (hsupp : ∀ j i t, M j i < |t| → f j i t = 0)
    (hfb : ∀ j i t, 1 ≤ t → f j i t = 0)
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1 / 2)
    (hM1 : ∀ j j', (∑ i, (M j i + M j' i)) < 1)
    (Mtop : ℝ) (hMtop : ∀ j i, M j i ≤ Mtop)
    (hM2 : ∀ j j' (i₀ : Fin (n + 1)), j' ∈ S →
      ∑ i ∈ Finset.univ.erase i₀, (M j i + M j' i) < ϑ)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x))
    (hlev : levelOfDistribution ϑ)
    (hWlog : ∃ A₀ : ℕ, ∀ᶠ x : ℕ in atTop, (W x : ℝ) ≤ (Real.log (x : ℝ)) ^ A₀)
    (hsep : ∀ᶠ x : ℕ in atTop, ∀ i j : Fin (n + 1), i ≠ j → H j - H i < w x)
    (D : ℕ → ℕ) (hD1 : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ Mtop ≤ (D x : ℝ))
    (hD2 : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ ϑ ≤ (D x : ℝ))
    (hα : 0 < tpAlpha c f)
    (hkey : tpAlpha c f < ∑ i : Fin (n + 1), tpBetaSplit S c f i) :
    ∀ N0 : ℕ, ∃ m : ℕ, N0 ≤ m ∧ 2 ≤ primeIndexCard H m :=
  translate_two_primes_of_tpWeight_split_family (Sf := fun _ => S) hn hJ c f H hHmax hHinj
    hcs hsm M hMnn hsupp hfb hϑ0 hϑ1 hM1 Mtop hMtop (fun j j' i₀ hj' => hM2 j j' i₀ hj') W hW w hw
    hsmall hlq b hbW hlev hWlog hsep D hD1 hD2 hα hkey

end Commons.NumberTheory.MaynardSieve

