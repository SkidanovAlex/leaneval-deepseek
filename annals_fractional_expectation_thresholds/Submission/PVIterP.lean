import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Prob
import Submission.PVCore
import Submission.PVAPI
import Submission.PVCost
import Submission.PVIter
import Submission.TailBnd
import Submission.OrMass

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval ProbabilityTheory
open FractionalExpectationThresholds
open Submission.PVC
open Submission.PVAPI
open Submission.PVIter
open Submission.FET

attribute [local instance] Classical.propDecidable

/-!
# Probabilistic layer for the iteration (finite Bernoulli layers as lists)

All statements are about a finite `X`.  We realize `d` independent Bernoulli-`p` rounds as
lists `ws : List (Set X)` of length `d`, weighted by `Π bmass p w`.

The main goals:
1. `prodExpUnion`: the distribution of the union of `d` Bernoulli-`p` rounds is Bernoulli with
   parameter `1-(1-p)^d`, i.e. `prodExp d (fun ws => if sUnion ws ∈ A then 1 else 0)
   = mu (pD ... ) A` (this is the layer identity, proved by induction using the identity
   that a union of one Bernoulli-`r` round and an independent Bernoulli-`s` round is
   Bernoulli-`(1-(1-r)(1-s))`).
2. `iterCost_eq_prodExp`: `iterCost q0 L d H = prodExp d (fun ws => zRun q0 H ws)`.
3. `fail_le_cost`: failure probability ≤ expected removed cost / ccost  (Markov + fail_ge_cost).
4. `iterCost_le`: `iterCost q0 L d H ≤ mu (pD q0 L d) (Up H) * tailCost L d`.
5. `pvHit`: the final hitting statement.
-/

namespace Submission
namespace PVIterP

universe u
variable {X : Type u} [Fintype X]

/-- expected value of `f` over `d` independent Bernoulli-`p` rounds (as lists). -/
noncomputable def prodExp (p : ℝ) : ℕ → ((List (Set X)) → ℝ) → ℝ
  | 0, f => f []
  | d + 1, f => expW p (fun W => prodExp p d (fun ws => f (W :: ws)))


/-- Bernoulli-round parameter after `d` rounds. -/
noncomputable def pRounds (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (d : ℕ) : I :=
  ⟨1 - (1 - p) ^ d, by
     have hle : (1 - p) ^ d ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
     linarith, by
     have h : 0 ≤ (1 - p) ^ d := pow_nonneg (by linarith) _
     linarith⟩

/-! ### Bernoulli weights: basic API -/

lemma bmass_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Set X) : 0 ≤ PVIter.bmass p W := by
  unfold PVIter.bmass
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

lemma bmass_eq_Pmass {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Set X) :
    PVIter.bmass p W = Pmass (⟨p, hp0, hp1⟩ : I) W := by
  rfl

lemma mu_univ_eq_one (p : I) : mu p (univ : Set (Set X)) = 1 := by
  unfold mu
  simpa using (probReal_univ (μ := setBer(univ, p)))

/-- `mu` as an explicit sum over all subsets. -/
lemma mu_eq_sum_all (p : I) (A : Set (Set X)) :
    mu p A = ∑ S : Set X, if S ∈ A then Pmass p S else 0 := by
  classical
  rw [mu_eq_sum p A]
  have hset : A.toFinite.toFinset = (Finset.univ : Finset (Set X)).filter (fun S => S ∈ A) := by
    ext S
    by_cases hS : S ∈ A <;> simp [hS]
  rw [hset]
  rw [Finset.sum_filter]

/-- `mu` of a set of the form `{Y | W ∪ Y ∈ A}` as a sum over `Y`. -/
lemma mu_compose_sum {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {d : ℕ} (A : Set (Set X))
    (W : Set X) :
    mu (pRounds p hp0 hp1 d) {Y | W ∪ Y ∈ A}
      = ∑ Y : Set X, if W ∪ Y ∈ A then Pmass (pRounds p hp0 hp1 d) Y else 0 := by
  classical
  rw [mu_eq_sum_all]
  apply Finset.sum_congr rfl
  intro Y hY
  by_cases h : W ∪ Y ∈ A <;> simp [h]

lemma expW_indicator_eq_mu {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Set (Set X)) :
    expW p (fun W => if W ∈ A then 1 else 0) = mu (⟨p, hp0, hp1⟩ : I) A := by
  classical
  calc
    expW p (fun W => if W ∈ A then 1 else 0)
        = (∑ W : Set X, if W ∈ A then PVIter.bmass p W else 0) := by
          unfold expW
          apply Finset.sum_congr rfl
          intro W hW
          by_cases h : W ∈ A <;> simp [h]
    _ = (∑ W : Set X, if W ∈ A then Pmass (⟨p, hp0, hp1⟩ : I) W else 0) := by
          apply Finset.sum_congr rfl
          intro W hW
          by_cases h : W ∈ A <;> simp [h, bmass_eq_Pmass hp0 hp1 W]
    _ = mu (⟨p, hp0, hp1⟩ : I) A := by
          rw [← mu_eq_sum_all]

lemma sum_bmass_eq_one_all (p : ℝ) : (∑ W : Set X, PVIter.bmass p W) = 1 := by
  classical
  let n : ℕ := Fintype.card X
  have hsplit : (∑ W : Set X, PVIter.bmass p W)
      = ∑ k ∈ Finset.range (n + 1),
          (p ^ k * (1 - p) ^ (n - k)) * (∑ W : Set X, if W.ncard = k then 1 else 0) := by
    calc
      (∑ W : Set X, PVIter.bmass p W)
          = ∑ W : Set X, ∑ k ∈ Finset.range (n + 1),
              (if W.ncard = k then p ^ k * (1 - p) ^ (n - k) else 0) := by
            apply Finset.sum_congr rfl
            intro W hW
            have hkn : W.ncard ≤ n := by
              simpa [n] using (Set.ncard_le_ncard (s := W) (t := (Set.univ : Set X))
                (by intro x hx; simp) (by simp))
            have hmem : W.ncard ∈ Finset.range (n + 1) := by
              simpa using (Nat.lt_succ_of_le hkn)
            have hval : (∑ k ∈ Finset.range (n + 1),
                  (if W.ncard = k then p ^ k * (1 - p) ^ (n - k) else 0))
                = p ^ W.ncard * (1 - p) ^ (n - W.ncard) := by
              have hsum := Finset.sum_eq_single (s := Finset.range (n + 1)) (a := W.ncard)
                (f := fun k => if W.ncard = k then p ^ k * (1 - p) ^ (n - k) else 0)
                (by
                  intro b hb hbne
                  have hnot : ¬ W.ncard = b := fun h => hbne h.symm
                  simp [hnot])
                (by simpa [hmem])
              rw [hsum]
              simp
            rw [hval]
            rfl
      _ = ∑ k ∈ Finset.range (n + 1),
            (p ^ k * (1 - p) ^ (n - k)) * (∑ W : Set X, if W.ncard = k then 1 else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro W hW
          by_cases h : W.ncard = k
          · simp [h]
          · simp [h]
  have hcount : ∀ k : ℕ, (∑ W : Set X, if W.ncard = k then 1 else 0) = (n.choose k : ℝ) := by
    intro k
    have h1 := PVCost.subset_slice_count (s := (univ : Set X)) (j := k)
    have hsimp : ∀ T : Set X, (if T ⊆ (univ : Set X) ∧ T.ncard = k then (1 : ℝ) else 0)
                 = (if T.ncard = k then (1 : ℝ) else 0) := by
      intro T
      by_cases h : T.ncard = k <;> simp [h]
    calc
      (∑ W : Set X, if W.ncard = k then 1 else 0)
          = ∑ T : Set X, if T ⊆ (univ : Set X) ∧ T.ncard = k then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro T hT
            rw [← hsimp T]
      _ = ((univ : Set X).ncard.choose k : ℝ) := h1
      _ = (n.choose k : ℝ) := by rw [show (univ : Set X).ncard = n by simp [n]]
  calc
    (∑ W : Set X, PVIter.bmass p W)
        = ∑ k ∈ Finset.range (n + 1),
            (p ^ k * (1 - p) ^ (n - k)) * (∑ W : Set X, if W.ncard = k then 1 else 0) := hsplit
    _ = ∑ k ∈ Finset.range (n + 1), p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hcount k]
    _ = (p + (1 - p)) ^ n := by
          rw [add_pow]
    _ = 1 := by
          have hp : p + (1 - p) = 1 := by ring
          rw [hp]
          simp

/-- `expW` of a constant function is the constant (the weights sum to 1). -/
lemma expW_const_all (p : ℝ) (c : ℝ) : expW p (fun _ : Set X => c) = c := by
  unfold expW
  calc
    (∑ W : Set X, PVIter.bmass p W * c) = c * (∑ W : Set X, PVIter.bmass p W) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro W hW
      ring
    _ = c := by rw [sum_bmass_eq_one_all p]; ring

lemma expW_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f : Set X → ℝ}
    (hf : ∀ W, 0 ≤ f W) : 0 ≤ expW p f := by
  unfold expW
  exact Finset.sum_nonneg (fun W hW => mul_nonneg (bmass_nonneg hp0 hp1 W) (hf W))

lemma expW_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : Set X → ℝ}
    (h : ∀ W, f W ≤ g W) : expW p f ≤ expW p g := by
  unfold expW
  exact Finset.sum_le_sum (fun W hW => mul_le_mul_of_nonneg_left (h W) (bmass_nonneg hp0 hp1 W))

lemma expW_add {p : ℝ} (f g : Set X → ℝ) : expW p (fun W => f W + g W) = expW p f + expW p g := by
  unfold expW
  simp [mul_add, Finset.sum_add_distrib]

lemma expW_sub {p : ℝ} (f g : Set X → ℝ) : expW p (fun W => f W - g W) = expW p f - expW p g := by
  unfold expW
  simp [mul_sub, Finset.sum_sub_distrib]

lemma expW_mul_const {p : ℝ} (c : ℝ) (f : Set X → ℝ) :
    expW p (fun W => c * f W) = c * expW p f := by
  unfold expW
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro W hW
  ring

/-- `expW` equals the corresponding `mu`-weighted double sum against a function of the pair. -/
lemma expW_pair_mu {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {s : I} (A : Set (Set X)) :
    expW p (fun W => mu s {Y | W ∪ Y ∈ A}) =
      (∑ W : Set X, ∑ Y : Set X,
        if W ∪ Y ∈ A then PVIter.bmass p W * Pmass s Y else 0) := by
  classical
  calc
    expW p (fun W => mu s {Y | W ∪ Y ∈ A})
        = ∑ W : Set X, PVIter.bmass p W * mu s {Y | W ∪ Y ∈ A} := by rfl
    _ = ∑ W : Set X, ∑ Y : Set X,
          PVIter.bmass p W * (if W ∪ Y ∈ A then Pmass s Y else 0) := by
          apply Finset.sum_congr rfl
          intro W hW
          rw [mu_eq_sum_all]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro Y hY
          by_cases h : W ∪ Y ∈ A <;> simp [h, mul_comm, mul_left_comm, mul_assoc]
    _ = ∑ W : Set X, ∑ Y : Set X,
          if W ∪ Y ∈ A then PVIter.bmass p W * Pmass s Y else 0 := by
          apply Finset.sum_congr rfl
          intro W hW
          apply Finset.sum_congr rfl
          intro Y hY
          by_cases h : W ∪ Y ∈ A <;> simp [h]
/-- helper: the expectation of an indicator of an event is nonnegative for a Bernoulli parameter
`p ∈ [0,1]`.  (As originally drafted this lemma omitted the bounds on `p`; for `p ∉ [0,1]` the
statement is false -- e.g. `X = PUnit`, `p = 2`, `d = 1`, `A ws := ws = [∅]` gives value `-1`.) -/
lemma prodExp_indicator {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (d : ℕ)
    (A : List (Set X) → Prop) [DecidablePred A] :
    prodExp p d (fun ws => if A ws then 1 else 0) ≥ 0 := by
  classical
  induction d generalizing A with
  | zero =>
      simp [prodExp]
      by_cases h : A []
      · simp [h]
      · simp [h]
  | succ d ih =>
      simp [prodExp]
      apply expW_nonneg hp0 hp1
      intro W
      exact ih (fun ws => A (W :: ws))

/-- `prodExp` is monotone in the integrand. -/
lemma prodExp_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {d : ℕ} (f g : List (Set X) → ℝ)
    (hfg : ∀ ws, f ws ≤ g ws) : prodExp p d f ≤ prodExp p d g := by
  classical
  revert f g
  induction d with
  | zero =>
      intro f g hfg
      simp [prodExp, hfg]
  | succ d ih =>
      intro f g hfg
      simp [prodExp]
      apply expW_mono hp0 hp1
      intro W
      exact ih (fun ws => f (W :: ws)) (fun ws => g (W :: ws)) (fun ws => hfg (W :: ws))

/-- `prodExp` is additive in the integrand. -/
lemma prodExp_add {p : ℝ} (d : ℕ) (f g : List (Set X) → ℝ) :
    prodExp p d (fun ws => f ws + g ws) = prodExp p d f + prodExp p d g := by
  classical
  revert f g
  induction d with
  | zero =>
      intro f g
      simp [prodExp]
  | succ d ih =>
      intro f g
      simp [prodExp]
      have hfun : (fun W => prodExp p d (fun ws => f (W :: ws) + g (W :: ws)))
                = fun W => prodExp p d (fun ws => f (W :: ws)) +
                            prodExp p d (fun ws => g (W :: ws)) := by
        funext W
        exact ih (fun ws => f (W :: ws)) (fun ws => g (W :: ws))
      rw [hfun]
      rw [expW_add]

/-- `prodExp` of a constant function is the constant (weights sum to 1). -/
lemma prodExp_const (p : ℝ) (d : ℕ) (c : ℝ) :
    prodExp p d (fun _ : List (Set X) => c) = c := by
  induction d with
  | zero => simp [prodExp]
  | succ d ih =>
      simp [prodExp]
      rw [expW_const_all p]
      exact ih

lemma prodExp_mul_const {p : ℝ} (d : ℕ) (c : ℝ) (f : List (Set X) → ℝ) :
    prodExp p d (fun ws => c * f ws) = c * prodExp p d f := by
  classical
  revert c f
  induction d with
  | zero =>
      intro c f
      simp [prodExp]
  | succ d ih =>
      intro c f
      simp [prodExp]
      have hfun : (fun W => prodExp p d (fun ws => c * f (W :: ws)))
                = fun W => c * prodExp p d (fun ws => f (W :: ws)) := by
        funext W
        exact ih c (fun ws => f (W :: ws))
      rw [hfun]
      rw [expW_mul_const]

/-- `mOf ws = 2^d` when `ws` has length `d`. -/
lemma mOf_length {ws : List (Set X)} {d : ℕ} (h : ws.length = d) : mOf ws = (2 : ℕ) ^ d := by
  unfold mOf
  rw [h]

/-- `prodExp` depends only on the values on lists of the right length. -/
lemma prodExp_of_length {p : ℝ} {d : ℕ} {f g : List (Set X) → ℝ}
    (hfg : ∀ ws : List (Set X), ws.length = d → f ws = g ws) : prodExp p d f = prodExp p d g := by
  classical
  revert f g
  induction d with
  | zero =>
      intro f g hfg
      simp [prodExp]
      exact hfg [] (by simp)
  | succ d ih =>
      intro f g hfg
      simp [prodExp]
      apply congrArg (expW p)
      funext W
      apply ih
      intro ws hws
      exact hfg (W :: ws) (by simp [hws])

lemma expW_eq_sum_Pmass {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Set X → ℝ) :
    expW p f = ∑ W : Set X, Pmass (⟨p, hp0, hp1⟩ : I) W * f W := by
  unfold expW
  apply Finset.sum_congr rfl
  intro W hW
  rw [bmass_eq_Pmass hp0 hp1 W]

/-- at parameter 0 the mass is on the empty set. -/
private lemma mu_zero_mem {A : Set (Set X)} (h : (∅ : Set X) ∈ A) : mu (0 : I) A = 1 := by
  unfold mu
  have hd : (setBer(univ, (0 : I)) : Measure (Set X)) = Measure.dirac (∅ : Set X) := by
    simp [setBernoulli_zero]
  rw [hd]
  have h1 : (Measure.dirac (∅ : Set X)) A = (1 : ℝ≥0∞) := by simp [h]
  simp [measureReal_def, h1]

/-- `mu` respects I-elements with equal values. -/
private lemma mu_I_congr {A : Set (Set X)} {a b : I} (h : (a : ℝ) = (b : ℝ)) :
    mu a A = mu b A := by
  exact congrArg (fun t : I => mu t A) (Subtype.ext h)

/-- the layer identity, with the parameter bundled as `pRounds`. -/
private lemma union_law_pRounds {p : ℝ} {d : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (Set X)) :
    prodExp p d (fun ws : List (Set X) => if sUnion ws ∈ A then 1 else 0) =
      mu (pRounds p hp0 hp1 d) A := by
  classical
  induction d generalizing A with
  | zero =>
      simp [prodExp, pRounds, PVIter.sUnion]
      by_cases h : (∅ : Set X) ∈ A
      · have hm : mu (0 : I) A = 1 := mu_zero_mem h
        simp [h, hm]
      · have hm : mu (0 : I) A = 0 := by
          exact mu_zero (𝓕 := A) h
        simp [h, hm]
  | succ d ih =>
      change expW p (fun W => prodExp p d (fun ws =>
          if sUnion (W :: ws) ∈ A then 1 else 0))
        = mu (pRounds p hp0 hp1 (d + 1)) A
      have hinner : (fun W => prodExp p d (fun ws : List (Set X) =>
            if sUnion (W :: ws) ∈ A then 1 else 0))
          = fun W => prodExp p d (fun ws : List (Set X) =>
            if W ∪ sUnion ws ∈ A then 1 else 0) := by
        funext W
        apply congrArg (prodExp p d)
        funext ws
        rfl
      rw [hinner]
      have hIH : (fun W => prodExp p d (fun ws : List (Set X) =>
            if W ∪ sUnion ws ∈ A then 1 else 0))
          = fun W => mu (pRounds p hp0 hp1 d) {Y | W ∪ Y ∈ A} := by
        funext W
        have hB : prodExp p d (fun ws : List (Set X) => if W ∪ sUnion ws ∈ A then 1 else 0)
            = prodExp p d (fun ws : List (Set X) =>
                if sUnion ws ∈ ({Y | W ∪ Y ∈ A} : Set (Set X)) then 1 else 0) := by
          apply congrArg (prodExp p d)
          funext ws
          by_cases h : W ∪ sUnion ws ∈ A <;> simp [h]
        rw [hB]
        exact ih {Y | W ∪ Y ∈ A}
      rw [hIH]
      have hcomp := OrMass.compose_union (a := (⟨p, hp0, hp1⟩ : I)) (s := pRounds p hp0 hp1 d) A
      have hval : (1 - (1 - (p : ℝ)) * (1 - (pRounds p hp0 hp1 d : ℝ)))
          = (pRounds p hp0 hp1 (d + 1) : ℝ) := by
        dsimp [pRounds]
        rw [pow_succ]
        ring
      have hstep : expW p (fun W => mu (pRounds p hp0 hp1 d) {Y | W ∪ Y ∈ A})
          = mu (pRounds p hp0 hp1 (d + 1)) A := by
        calc
          expW p (fun W => mu (pRounds p hp0 hp1 d) {Y | W ∪ Y ∈ A})
              = (∑ W : Set X, Pmass (⟨p, hp0, hp1⟩ : I) W *
                  mu (pRounds p hp0 hp1 d) {Y | W ∪ Y ∈ A}) := by
                rw [expW_eq_sum_Pmass hp0 hp1]
          _ = mu (pRounds p hp0 hp1 (d + 1)) A := by
                rw [hcomp]
                apply mu_I_congr
                exact hval
      exact hstep

lemma union_law {p : ℝ} {d : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (Set X)) :
    prodExp p d (fun ws : List (Set X) => if sUnion ws ∈ A then 1 else 0) =
      mu (⟨1 - (1 - p) ^ d, by
             have hle : (1 - p) ^ d ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
             linarith, by
             have h : (1 - p) ^ d ≥ 0 := pow_nonneg (by linarith) _
             linarith⟩ : I) A := by
  classical
  rw [union_law_pRounds hp0 hp1 A]
  apply mu_I_congr
  dsimp [pRounds]

/-- `iterCost` is the expectation of the removed cost over the product of rounds. -/
lemma iterCost_eq_prodExp (q0 : ℝ) (L : ℕ) (d : ℕ) (H : Set (Set X)) :
    iterCost q0 L d H = prodExp (1 - (1 - q0) ^ L) d (fun ws => zRun q0 H ws) := by
  classical
  let p : ℝ := 1 - (1 - q0) ^ L
  change iterCost q0 L d H = prodExp p d (fun ws => zRun q0 H ws)
  revert H
  induction d with
  | zero =>
      intro H
      simp [iterCost, prodExp, zRun]
  | succ d ih =>
      intro H
      change expW p (fun W => ccost q0 (Lm H W ((2 : ℕ) ^ d)) + iterCost q0 L d (Sm H W ((2 : ℕ) ^ d)))
        = expW p (fun W => prodExp p d (fun ws => zRun q0 H (W :: ws)))
      apply congrArg (expW p)
      funext W
      rw [ih (Sm H W ((2 : ℕ) ^ d))]
      symm
      calc
        prodExp p d (fun ws => zRun q0 H (W :: ws))
            = prodExp p d (fun ws =>
                ccost q0 (Lm H W (mOf ws)) + zRun q0 (Sm H W (mOf ws)) ws) := by
              rfl
        _ = prodExp p d (fun ws =>
              ccost q0 (Lm H W ((2 : ℕ) ^ d)) + zRun q0 (Sm H W ((2 : ℕ) ^ d)) ws) := by
              apply prodExp_of_length
              intro ws hws
              rw [mOf_length hws]
        _ = ccost q0 (Lm H W ((2 : ℕ) ^ d)) + prodExp p d (fun ws => zRun q0 (Sm H W ((2 : ℕ) ^ d)) ws) := by
              rw [prodExp_add]
              have hconst : prodExp p d (fun ws : List (Set X) =>
                  ccost q0 (Lm H W ((2 : ℕ) ^ d)))
                  = ccost q0 (Lm H W ((2 : ℕ) ^ d)) := by
                simpa using (prodExp_const p d (ccost q0 (Lm H W ((2 : ℕ) ^ d))))
              rw [hconst]

/-- the minimal cover cost is nonnegative. -/
lemma ccost_nonneg {q0 : ℝ} (hq0 : 0 ≤ q0) (H : Set (Set X)) : 0 ≤ ccost q0 H := by
  classical
  unfold ccost
  let s : Set ℝ := {a | ∃ G : Set (Set X), Covers G H ∧ ecost q0 G = a}
  change 0 ≤ sInf s
  apply le_csInf
  · refine ⟨ecost q0 H, H, covers_self H, rfl⟩
  · intro a ha
    rcases ha with ⟨G, hC, rfl⟩
    exact ecost_nonneg hq0 G

/-- the removed cost is nonnegative. -/
lemma zRun_nonneg {q0 : ℝ} (hq0 : 0 ≤ q0) (H : Set (Set X)) (ws : List (Set X)) :
    0 ≤ zRun q0 H ws := by
  revert H
  induction ws with
  | nil => intro H; simp [zRun]
  | cons w ws ih =>
      intro H
      simp [zRun]
      exact add_nonneg (ccost_nonneg hq0 (Lm H w (mOf ws))) (ih (Sm H w (mOf ws)))

/-- failure probability is at most (expected removed cost)/ccost.  `fail ≤ prodExp(zRun)/c`. -/
lemma fail_le_cost {q0 : ℝ} (hq0 : 0 ≤ q0) {H : Set (Set X)} {d : ℕ}
    (hℓb : Bounded H ((2 : ℕ) ^ d - 1)) (hd : 1 ≤ d) (hc : 1 ≤ ccost q0 H) (L : ℕ)
    (hL1 : 1 ≤ L) (hq01 : q0 ≤ 1) :
    let p := 1 - (1 - q0) ^ L
    prodExp p d (fun ws : List (Set X) =>
      if sUnion ws ∈ Up H then 0 else 1) ≤
      iterCost q0 L d H / ccost q0 H := by
  classical
  let p : ℝ := 1 - (1 - q0) ^ L
  have hp0 : 0 ≤ p := by
    dsimp [p]
    have hle : (1 - q0) ^ L ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    linarith
  have hp1 : p ≤ 1 := by
    dsimp [p]
    have h : 0 ≤ (1 - q0) ^ L := pow_nonneg (by linarith) _
    linarith
  have hcpos : 0 < ccost q0 H := by linarith
  let f : List (Set X) → ℝ := fun ws => if sUnion ws ∈ Up H then 0 else 1
  let f' : List (Set X) → ℝ := fun ws => if ws = [] then 0 else f ws
  let g : List (Set X) → ℝ := fun ws => zRun q0 H ws / ccost q0 H
  have hf_eq : prodExp p d f = prodExp p d f' := by
    apply prodExp_of_length
    intro ws hws
    have hne : ws ≠ [] := by
      intro he
      rw [he] at hws
      simp at hws
      linarith
    simp [f', f, hne]
  have hpt : ∀ ws, ws ≠ [] → f ws ≤ g ws := by
    intro ws hws
    dsimp [f, g]
    by_cases hhit : sUnion ws ∈ Up H
    · have hz : 0 ≤ zRun q0 H ws := zRun_nonneg hq0 H ws
      have this0 : 0 ≤ zRun q0 H ws / ccost q0 H := div_nonneg hz (le_of_lt hcpos)
      simp [hhit, this0]
    · have hge := PVIter.fail_ge_cost (q0 := q0) (hq0 := hq0) H hws hhit
      have hle : (1 : ℝ) ≤ zRun q0 H ws / ccost q0 H := by
        rw [le_div_iff₀ hcpos]
        simpa using hge
      simp [hhit, hle]
  have hfg : ∀ ws, f' ws ≤ g ws := by
    intro ws
    by_cases hws : ws = []
    · have hz : 0 ≤ zRun q0 H ws / ccost q0 H := div_nonneg (zRun_nonneg hq0 H ws) (le_of_lt hcpos)
      rw [hws] at hz ⊢
      simp [f', g, hz]
    · simp [f', hws]
      exact hpt ws hws
  have h1 : prodExp p d f ≤ prodExp p d g := by
    calc
      prodExp p d f = prodExp p d f' := hf_eq
      _ ≤ prodExp p d g := prodExp_mono hp0 hp1 f' g hfg
  have hg : prodExp p d g = iterCost q0 L d H / ccost q0 H := by
    calc
      prodExp p d g
          = prodExp p d (fun ws => zRun q0 H ws * (ccost q0 H)⁻¹) := by
            apply congrArg (prodExp p d)
            funext ws
            dsimp [g]
            ring
      _ = prodExp p d (fun ws => (ccost q0 H)⁻¹ * zRun q0 H ws) := by
            apply congrArg (prodExp p d)
            funext ws
            ring
      _ = (ccost q0 H)⁻¹ * prodExp p d (fun ws => zRun q0 H ws) := by
            rw [prodExp_mul_const]
      _ = iterCost q0 L d H / ccost q0 H := by
            rw [iterCost_eq_prodExp]
            rw [div_eq_mul_inv]
            ring
  change prodExp p d f ≤ iterCost q0 L d H / ccost q0 H
  calc
    prodExp p d f ≤ prodExp p d g := h1
    _ = iterCost q0 L d H / ccost q0 H := hg

/-! ### parameter helpers -/

/-- `pD q0 L d` equals the iterated single-round parameter `pRounds (1-(1-q0)^L) d`. -/
lemma pD_eq_pRounds {q0 : ℝ} (hq0 : 0 ≤ q0) (hq01 : q0 ≤ 1) (L d : ℕ) :
    pD q0 hq0 hq01 L d = pRounds (1 - (1 - q0) ^ L)
        (by
          have hle : (1 - q0) ^ L ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
          linarith)
        (by
          have h : 0 ≤ (1 - q0) ^ L := pow_nonneg (by linarith) _
          linarith) d := by
  apply Subtype.ext
  dsimp [pD, pRounds]
  have hbase : (1 - (1 - (1 - q0) ^ L)) = (1 - q0) ^ L := by ring
  rw [hbase]
  congr 1
  rw [show (d * L) = L * d by exact Nat.mul_comm d L]
  exact (pow_mul (1 - q0) L d)

/-- the `d+1`-round parameter is at least the single-round parameter. -/
lemma p_le_pD {q0 : ℝ} (hq0 : 0 ≤ q0) (hq01 : q0 ≤ 1) (L d : ℕ) :
    (1 - (1 - q0) ^ L) ≤ (pD q0 hq0 hq01 L (d + 1) : ℝ) := by
  classical
  have h0 : 0 ≤ 1 - q0 := by linarith
  have h1 : 1 - q0 ≤ 1 := by linarith
  dsimp [pD]
  have hpow : (1 - q0) ^ ((d + 1) * L) ≤ (1 - q0) ^ L := by
    rw [show (d + 1) * L = L * (d + 1) by rw [Nat.mul_comm]]
    rw [pow_mul]
    have ha0 : 0 ≤ (1 - q0) ^ L := pow_nonneg h0 _
    have ha1 : (1 - q0) ^ L ≤ 1 := pow_le_one₀ h0 h1
    rw [pow_succ]
    have hstep : ((1 - q0) ^ L) ^ d * (1 - q0) ^ L ≤ (1 - q0) ^ L := by
      simpa using (mul_le_mul_of_nonneg_right (pow_le_one₀ ha0 ha1) ha0)
    exact hstep
  linarith

/-! ### measure-level helpers for the hitting theorem -/

/-- the measure of a family and its complement add up to 1. -/
lemma mu_add_compl (p : I) (A : Set (Set X)) : mu p A + mu p Aᶜ = 1 := by
  classical
  have hsum : (∑ S : Set X, if S ∈ A then Pmass p S else 0) +
        (∑ S : Set X, if S ∈ Aᶜ then Pmass p S else 0)
      = ∑ S : Set X, Pmass p S := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    by_cases h : S ∈ A <;> simp [h]
  calc
    mu p A + mu p Aᶜ
        = (∑ S : Set X, if S ∈ A then Pmass p S else 0) +
          (∑ S : Set X, if S ∈ Aᶜ then Pmass p S else 0) := by
          rw [mu_eq_sum_all]
          congr 1
          rw [mu_eq_sum_all]
          apply Finset.sum_congr rfl
          intro S hS
          by_cases h : S ∈ Aᶜ <;> simp [h]
    _ = (∑ S : Set X, Pmass p S) := hsum
    _ = mu p (univ : Set (Set X)) := by
          rw [mu_eq_sum_all]
          apply Finset.sum_congr rfl
          intro S hS
          simp
    _ = 1 := mu_univ_eq_one p

lemma Up_Sm_subset_union {H : Set (Set X)} {W : Set X} {m : ℕ} :
    Up (Sm H W m) ⊆ {Y | W ∪ Y ∈ Up H} := by
  intro Y hY
  rcases (mem_Up.mp hY) with ⟨F, hF, hFY⟩
  have hfrag : F ∈ Frag H W := Sm_mem_frag hF
  rcases (mem_Frag.mp hfrag) with ⟨S, hS, hF'⟩
  refine (mem_Up.mpr ⟨S, hS, ?_⟩)
  -- S ⊆ W ∪ Y
  intro x hxS
  by_cases hxW : x ∈ W
  · exact Or.inl hxW
  · have hxSdiff : x ∈ S \ W := ⟨hxS, hxW⟩
    have hxF : x ∈ F := by rw [hF']; exact hxSdiff
    exact Or.inr (hFY hxF)

/-- measure of fragments pointing at `Up H` is at most the measure of the union-composition. -/
lemma expW_Up_Sm_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {s : I} (H : Set (Set X)) (m : ℕ) :
    expW p (fun W => mu s (Up (Sm H W m)))
      ≤ expW p (fun W => mu s {Y | W ∪ Y ∈ Up H}) := by
  apply expW_mono hp0 hp1
  intro W
  exact mu_mono_family s (Up_Sm_subset_union (H := H) (W := W) (m := m))

/-- per-round binomial tail is tiny (≤ 2·(4/L)^m for m = 2^t). -/
lemma bOne_le (L : ℕ) (hL : 8 ≤ L) (t : ℕ) : bOne L t ≤ 2 * (4 / L) ^ ((2 : ℕ) ^ t) := by
  exact Submission.TailBnd.bOne_le L hL t

/-- total tail budget is at most `8/L`. -/
lemma tailCost_le {L : ℕ} (hL : 8 ≤ L) : ∀ d : ℕ, tailCost L d ≤ 8 / L := by
  intro d
  exact Submission.TailBnd.tailCost_le hL d

/-- `bOne L t ≥ 0`. -/
private lemma bOne_nonneg (L : ℕ) (t : ℕ) : 0 ≤ bOne L t := by
  classical
  dsimp [bOne]
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (by positivity) (pow_nonneg (by positivity) j)

/-- `tailCost L d ≥ 0`. -/
private lemma tailCost_nonneg (L : ℕ) (d : ℕ) : 0 ≤ tailCost L d := by
  classical
  induction d with
  | zero => simp [tailCost]
  | succ d ih =>
      dsimp [tailCost]
      exact add_nonneg (bOne_nonneg L d) ih

/-- one-round measure step used in the `iterCost_le` recursion. -/
private lemma expW_Up_next {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {q0 : ℝ} (hq00 : 0 ≤ q0) (hq01 : q0 ≤ 1) (L d : ℕ) (H : Set (Set X))
    (hp : p = 1 - (1 - q0) ^ L) :
    expW p (fun W => mu (pD q0 hq00 hq01 L d) (Up (Sm H W ((2 : ℕ) ^ d))))
      ≤ mu (pD q0 hq00 hq01 L (d + 1)) (Up H) := by
  classical
  calc
    expW p (fun W => mu (pD q0 hq00 hq01 L d) (Up (Sm H W ((2 : ℕ) ^ d))))
        ≤ expW p (fun W => mu (pD q0 hq00 hq01 L d) {Y | W ∪ Y ∈ Up H}) := by
          exact expW_Up_Sm_le hp0 hp1 (s := pD q0 hq00 hq01 L d) H ((2 : ℕ) ^ d)
    _ = mu (pD q0 hq00 hq01 L (d + 1)) (Up H) := by
          have hcomp := OrMass.compose_union (a := (⟨p, hp0, hp1⟩ : I))
            (s := pD q0 hq00 hq01 L d) (Up H)
          calc
            expW p (fun W => mu (pD q0 hq00 hq01 L d) {Y | W ∪ Y ∈ Up H})
                = (∑ W : Set X, Pmass (⟨p, hp0, hp1⟩ : I) W *
                    mu (pD q0 hq00 hq01 L d) {Y | W ∪ Y ∈ Up H}) := by
                  rw [expW_eq_sum_Pmass hp0 hp1]
            _ = mu (pD q0 hq00 hq01 L (d + 1)) (Up H) := by
                  rw [hcomp]
                  apply mu_I_congr
                  dsimp [pD]
                  rw [hp]
                  congr 1
                  congr 1
                  have hx1 : (1 - (1 - (1 - q0) ^ L)) = (1 - q0) ^ L := by ring
                  have hx2 : (1 - (1 - (1 - q0) ^ (d * L))) = (1 - q0) ^ (d * L) := by ring
                  rw [hx1, hx2]
                  rw [← pow_add]
                  exact congrArg (fun e : ℕ => (1 - q0) ^ e) (by ring : L + d * L = (d + 1) * L)

lemma iterCost_le (q0 : ℝ) (L : ℕ) (hL : 1 ≤ L) (hq0 : 0 < q0) (hq01 : q0 ≤ 1) :
    ∀ d (H : Set (Set X)), Bounded H ((2 : ℕ) ^ d - 1) →
      iterCost q0 L d H ≤ mu (pD q0 hq0.le hq01 L d) (Up H) * tailCost L d := by
  classical
  let p : ℝ := 1 - (1 - q0) ^ L
  have hp0 : 0 ≤ p := by
    dsimp [p]
    have hle : (1 - q0) ^ L ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    linarith
  have hp1 : p ≤ 1 := by
    dsimp [p]
    have h : 0 ≤ (1 - q0) ^ L := pow_nonneg (by linarith) _
    linarith
  have hpf : p = 1 - (1 - q0) ^ L := by rfl
  have hq00 : 0 ≤ q0 := hq0.le
  have htail : ∀ d : ℕ, 0 ≤ tailCost L d := tailCost_nonneg L
  have hbOne : ∀ t : ℕ, 0 ≤ bOne L t := bOne_nonneg L
  -- induction on the number of rounds
  have hmain : ∀ d (H : Set (Set X)), Bounded H ((2 : ℕ) ^ d - 1) →
      iterCost q0 L d H ≤ mu (pD q0 hq00 hq01 L d) (Up H) * tailCost L d := by
    intro d
    induction d with
    | zero =>
        intro H hb
        simp [iterCost, tailCost]
    | succ d ih =>
        intro H hb
        change expW p (fun W => ccost q0 (Lm H W ((2 : ℕ) ^ d)) + iterCost q0 L d (Sm H W ((2 : ℕ) ^ d)))
            ≤ mu (pD q0 hq00 hq01 L (d + 1)) (Up H) * tailCost L (d + 1)
        let m : ℕ := (2 : ℕ) ^ d
        let ℓ : ℕ := (2 : ℕ) ^ (d + 1) - 1
        have hm1 : 1 ≤ m := by
          dsimp [m]
          have h : (0 : ℕ) < (2 : ℕ) ^ d := pow_pos (by norm_num) d
          omega
        -- first-round cost via pvCostLemma
        have hb1 : (2 : ℕ) ^ d ≤ (2 : ℕ) ^ (d + 1) - 1 := by omega
        have hbℓ : Bounded H ℓ := by
          dsimp [ℓ]
          exact hb
        have hmℓ : m ≤ ℓ := by
          dsimp [m, ℓ]
          exact hb1
        have hfirst := PVCost.pvCostLemma (X := X) (H := H) (ℓ := ℓ) hbℓ
          (q0 := q0) hq0 hq01 L hL (m := m) hm1 hmℓ
        -- hfirst : (∑ W, bmass p W * ccost q0 (Lm H W m)) ≤
        --   (∑ W, bmass p W * (if W ∈ Up H then 1 else 0)) *
        --   (∑ j ∈ Icc m ℓ, ((ℓ.choose j : ℝ) * (1 / L) ^ j))
        have hbOned : (∑ j ∈ Finset.Icc m ℓ, ((ℓ.choose j : ℝ) * (1 / L : ℝ) ^ j)) = bOne L d := by
          dsimp [m, ℓ, bOne]
        have hpart1 : expW p (fun W => ccost q0 (Lm H W m))
            ≤ mu (pD q0 hq00 hq01 L (d + 1)) (Up H) * bOne L d := by
          have hfirst' :
              expW p (fun W => ccost q0 (Lm H W m))
                ≤ (∑ W : Set X, PVIter.bmass p W * (if W ∈ Up H then 1 else 0)) *
                  (∑ j ∈ Finset.Icc m ℓ, ((ℓ.choose j : ℝ) * (1 / L : ℝ) ^ j)) := by
            calc
              expW p (fun W => ccost q0 (Lm H W m))
                  = (∑ W : Set X, PVCost.bmass (1 - (1 - q0) ^ L) W * ccost q0 (Lm H W m)) := by
                    rfl
              _ ≤ (∑ W : Set X, PVCost.bmass (1 - (1 - q0) ^ L) W * (if W ∈ Up H then 1 else 0)) *
                  (∑ j ∈ Finset.Icc m ℓ, ((ℓ.choose j : ℝ) * (1 / L : ℝ) ^ j)) := by
                    exact hfirst
              _ = (∑ W : Set X, PVIter.bmass p W * (if W ∈ Up H then 1 else 0)) *
                  (∑ j ∈ Finset.Icc m ℓ, ((ℓ.choose j : ℝ) * (1 / L : ℝ) ^ j)) := by
                    rfl
          calc
            expW p (fun W => ccost q0 (Lm H W m))
                ≤ (∑ W : Set X, PVIter.bmass p W * (if W ∈ Up H then 1 else 0)) *
                  bOne L d := by
                  -- rewrite the second factor to bOne and combine
                  calc
                    expW p (fun W => ccost q0 (Lm H W m))
                        ≤ (∑ W : Set X, PVIter.bmass p W * (if W ∈ Up H then 1 else 0)) *
                          (∑ j ∈ Finset.Icc m ℓ, ((ℓ.choose j : ℝ) * (1 / L : ℝ) ^ j)) := hfirst'
                    _ = (∑ W : Set X, PVIter.bmass p W * (if W ∈ Up H then 1 else 0)) * bOne L d := by
                          rw [hbOned]
            _ = mu (⟨p, hp0, hp1⟩ : I) (Up H) * bOne L d := by
                  rw [show (∑ W : Set X, PVIter.bmass p W * (if W ∈ Up H then 1 else 0))
                        = expW p (fun W => if W ∈ Up H then 1 else 0) by
                          unfold expW
                          apply Finset.sum_congr rfl
                          intro W hW
                          by_cases h : W ∈ Up H <;> simp [h]]
                  rw [expW_indicator_eq_mu hp0 hp1 (A := Up H)]
            _ ≤ mu (pD q0 hq00 hq01 L (d + 1)) (Up H) * bOne L d := by
                  have hmm : mu (⟨p, hp0, hp1⟩ : I) (Up H)
                      ≤ mu (pD q0 hq00 hq01 L (d + 1)) (Up H) := by
                    exact mu_mono_p (Up_upper H) (⟨p, hp0, hp1⟩ : I)
                      (pD q0 hq00 hq01 L (d + 1)) (p_le_pD hq00 hq01 L d)
                  exact mul_le_mul_of_nonneg_right hmm (hbOne d)
        -- remaining rounds via the induction hypothesis
        -- remaining rounds via the induction hypothesis
        have hpart2 : expW p (fun W => iterCost q0 L d (Sm H W m))
            ≤ mu (pD q0 hq00 hq01 L (d + 1)) (Up H) * tailCost L d := by
          have hpt : ∀ W, iterCost q0 L d (Sm H W m) ≤
              mu (pD q0 hq00 hq01 L d) (Up (Sm H W m)) * tailCost L d := by
            intro W
            have hbW : Bounded (Sm H W m) ((2 : ℕ) ^ d - 1) := by
              intro F hF
              have hlt : F.ncard < m := Sm_small hF
              dsimp [m] at hlt
              omega
            exact ih (Sm H W m) hbW
          calc
            expW p (fun W => iterCost q0 L d (Sm H W m))
                ≤ expW p (fun W => mu (pD q0 hq00 hq01 L d) (Up (Sm H W m)) * tailCost L d) := by
                  apply expW_mono hp0 hp1
                  intro W
                  exact hpt W
            _ = expW p (fun W => tailCost L d * mu (pD q0 hq00 hq01 L d) (Up (Sm H W m))) := by
                  apply congrArg (expW p)
                  funext W
                  ring
            _ = tailCost L d * expW p (fun W => mu (pD q0 hq00 hq01 L d) (Up (Sm H W m))) := by
                  rw [expW_mul_const]
            _ ≤ tailCost L d * mu (pD q0 hq00 hq01 L (d + 1)) (Up H) := by
                  exact mul_le_mul_of_nonneg_left (expW_Up_next hp0 hp1 hq00 hq01 L d H hpf) (htail d)
            _ = mu (pD q0 hq00 hq01 L (d + 1)) (Up H) * tailCost L d := by ring
        -- assemble
        calc
          expW p (fun W => ccost q0 (Lm H W ((2 : ℕ) ^ d)) + iterCost q0 L d (Sm H W ((2 : ℕ) ^ d)))
              = expW p (fun W => ccost q0 (Lm H W m)) + expW p (fun W => iterCost q0 L d (Sm H W m)) := by
                rw [expW_add]
          _ ≤ mu (pD q0 hq00 hq01 L (d + 1)) (Up H) * bOne L d +
              mu (pD q0 hq00 hq01 L (d + 1)) (Up H) * tailCost L d := by
                exact add_le_add hpart1 hpart2
          _ = mu (pD q0 hq00 hq01 L (d + 1)) (Up H) * (bOne L d + tailCost L d) := by ring
          _ = mu (pD q0 hq00 hq01 L (d + 1)) (Up H) * tailCost L (d + 1) := by
                dsimp [tailCost]
  -- convert hq00 back to hq0.le
  have hfinal : ∀ d (H : Set (Set X)), Bounded H ((2 : ℕ) ^ d - 1) →
      iterCost q0 L d H ≤ mu (pD q0 hq0.le hq01 L d) (Up H) * tailCost L d := by
    intro d H hb
    exact hmain d H hb
  exact hfinal

private lemma pD_eq_pRounds_p {q0 : ℝ} (hq0 : 0 ≤ q0) (hq01 : q0 ≤ 1) (L d : ℕ)
    {p : ℝ} (hpf : p = 1 - (1 - q0) ^ L) :
    pD q0 hq0 hq01 L d = pRounds p
        (by
          rw [hpf]
          have hle : (1 - q0) ^ L ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
          linarith)
        (by
          rw [hpf]
          have h : 0 ≤ (1 - q0) ^ L := pow_nonneg (by linarith) _
          linarith) d := by
  rw [pD_eq_pRounds hq0 hq01 L d]
  apply Subtype.ext
  dsimp [pRounds]
  rw [hpf]

/-- the failure probability over `d` rounds is `mu (pD q0 L d) (Up H)ᶜ`. -/
theorem pvHit {H : Set (Set X)} {ℓ : ℕ} (hℓb : Bounded H ℓ) (hℓ1 : 1 ≤ ℓ)
    {q0 : ℝ} (hq0 : 0 < q0) (hq01 : q0 ≤ 1) (hc : 1 ≤ ccost q0 H)
    {L : ℕ} (hL : 8 ≤ L) :
    let d := Nat.log2 ℓ + 1
    (3 / 4 : ℝ) ≤ mu (pD q0 hq0.le hq01 L d) (Up H) := by
  classical
  let d : ℕ := Nat.log2 ℓ + 1
  let p : ℝ := 1 - (1 - q0) ^ L
  have hL1 : 1 ≤ L := by omega
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hℓd : ℓ ≤ (2 : ℕ) ^ d - 1 := by
    dsimp [d]
    have hlt : ℓ < (2 : ℕ) ^ (Nat.log2 ℓ + 1) := Nat.lt_log2_self (n := ℓ)
    omega
  have hb2 : Bounded H ((2 : ℕ) ^ d - 1) := by
    intro S hS
    have hSℓ : S.ncard ≤ ℓ := hℓb S hS
    omega
  have hp0 : 0 ≤ p := by
    dsimp [p]
    have hle : (1 - q0) ^ L ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    linarith
  have hp1 : p ≤ 1 := by
    dsimp [p]
    have h : 0 ≤ (1 - q0) ^ L := pow_nonneg (by linarith) _
    linarith
  have hq00 : 0 ≤ q0 := hq0.le
  let x : ℝ := mu (pD q0 hq0.le hq01 L d) (Up H)
  have hu := union_law (p := p) (d := d) (hp0 := hp0) (hp1 := hp1) (A := Up H)
  have hpr := pD_eq_pRounds_p hq00 hq01 L d (p := p) (by rfl)
  have hval2 : (pRounds p hp0 hp1 d : ℝ) = (pD q0 hq0.le hq01 L d : ℝ) := by
    have h1 : (pRounds p hp0 hp1 d : ℝ) = (pD q0 hq00 hq01 L d : ℝ) := by
      rw [← hpr]
    have h2 : (pD q0 hq00 hq01 L d : ℝ) = (pD q0 hq0.le hq01 L d : ℝ) := rfl
    exact h1.trans h2
  have hhit : prodExp p d (fun ws : List (Set X) => if sUnion ws ∈ Up H then 1 else 0) = x := by
    dsimp [x]
    calc
      prodExp p d (fun ws : List (Set X) => if sUnion ws ∈ Up H then 1 else 0)
          = mu (pRounds p hp0 hp1 d) (Up H) := by
            rw [hu]
            apply mu_I_congr
            rfl
      _ = mu (pD q0 hq0.le hq01 L d) (Up H) := by
            apply mu_I_congr
            exact hval2
  -- failure indicator + hit indicator = 1, so the failure probability is 1 - x
  let f : ℝ := prodExp p d (fun ws : List (Set X) => if sUnion ws ∈ Up H then 0 else 1)
  have hpt : ∀ ws : List (Set X),
      (if sUnion ws ∈ Up H then (0 : ℝ) else 1) + (if sUnion ws ∈ Up H then (1 : ℝ) else 0) = 1 := by
    intro ws
    by_cases h : sUnion ws ∈ Up H <;> simp [h]
  have htotal : f + x = 1 := by
    calc
      f + x = f + prodExp p d (fun ws : List (Set X) => if sUnion ws ∈ Up H then 1 else 0) := by
              rw [← hhit]
      _ = prodExp p d (fun ws : List (Set X) =>
            (if sUnion ws ∈ Up H then 0 else 1) + (if sUnion ws ∈ Up H then 1 else 0)) := by
            have hsplit : f + prodExp p d (fun ws : List (Set X) => if sUnion ws ∈ Up H then 1 else 0)
                = prodExp p d (fun ws : List (Set X) =>
                    (if sUnion ws ∈ Up H then 0 else 1) + (if sUnion ws ∈ Up H then 1 else 0)) := by
              dsimp [f]
              exact (prodExp_add (p := p) d (fun ws : List (Set X) => if sUnion ws ∈ Up H then 0 else 1)
                (fun ws : List (Set X) => if sUnion ws ∈ Up H then 1 else 0)).symm
            exact hsplit
      _ = prodExp p d (fun _ : List (Set X) => 1) := by
            apply congrArg (prodExp p d)
            funext ws
            exact hpt ws
      _ = 1 := prodExp_const p d 1
  -- failure probability is bounded by the expected removed cost over ccost
  have hfl := fail_le_cost (q0 := q0) (hq0 := hq00) (H := H) (d := d) hb2 hd hc L hL1 hq01
  have hic := iterCost_le q0 L hL1 hq0 hq01 d H hb2
  have htail : tailCost L d ≤ 1 / 3 := Submission.TailBnd.tailCost_le_thirds hL d
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact mu_nonneg _ _
  have htail0 : 0 ≤ tailCost L d := tailCost_nonneg L d
  have hxmu : mu (pD q0 hq0.le hq01 L d) (Up H) = x := rfl
  -- f ≤ x · tailCost
  have hfpt : f ≤ x * tailCost L d := by
    have hcpos : 0 < ccost q0 H := by linarith
    have hle1 : iterCost q0 L d H ≤ x * tailCost L d := by
      simpa [hxmu] using hic
    have hle2 : f ≤ x * tailCost L d := by
      calc
        f ≤ iterCost q0 L d H / ccost q0 H := by
              simpa [f] using hfl
        _ ≤ (x * tailCost L d) / ccost q0 H := by
              exact div_le_div_of_nonneg_right hle1 hcpos.le
        _ ≤ x * tailCost L d := by
              exact div_le_self (mul_nonneg hx0 htail0) hc
    exact hle2
  -- tail is at most 1/3, so f ≤ x/3
  have hfthird : f ≤ x / 3 := by
    have hxle : x * tailCost L d ≤ x * (1 / 3) := by
      exact mul_le_mul_of_nonneg_left htail hx0
    have hxdiv : x * (1 / 3) = x / 3 := by ring
    rw [hxdiv] at hxle
    exact le_trans hfpt hxle
  -- conclude: 1 - x = f ≤ x/3 ⟹ 3/4 ≤ x
  have h1mx : 1 - x = f := by linarith [htotal]
  nlinarith [h1mx, hfthird]

end PVIterP
end Submission
