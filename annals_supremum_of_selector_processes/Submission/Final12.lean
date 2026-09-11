import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ChallengeDeps
import Submission.SelCore
import Submission.Chain12
import Submission.Thm57p
import Submission.Bridge
import Submission.Binom

/-!
# Final bridge for Theorem 1.2 (selector processes).

Everything here is `classical` over a finite type `X`; `Λ : Set (X → ℝ≥0)` is an
arbitrary family of nonnegative functions; `μ` is the ENNReal expectation of the sup
process over the binomial set distribution.

MAIN RESULT of the file:
    `selector_p_small`: for a suitable huge constant `L2`, the collection
    {s : Set X | ⨆ f ∈ Λ, ∑ i ∈ s, (f i : ℝ≥0∞) ≥ L2 · μ}
    is p-small.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Classical
open MeasureTheory Measure ProbabilityTheory unitInterval Finset
open scoped ENNReal NNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Final12

open Frame
open Sel
open Sel.Deep
open Sel.Deep.Sys
open Chain12

variable {X : Type*} [Fintype X]

/-- constant L₂ = 10^45 : ℝ≥0 -/
noncomputable def L2 : ℝ≥0 := (10 : ℝ≥0) ^ 45

/-- the big sup-process value at s -/
noncomputable def bigSup (Λ : Set (X → ℝ≥0)) (s : Set X) : ℝ≥0∞ :=
  ⨆ f ∈ Λ, (∑ i ∈ s, (f i : ℝ≥0∞))

/-- real-valued sum of an NNReal function over a set -/
noncomputable def realSum (f : X → ℝ≥0) (s : Set X) : ℝ :=
  ∑ i ∈ s, (f i : ℝ)

/-- ENNReal set-sum equals the filtered full sum -/
lemma esum_eq_filter (f : X → ℝ≥0) (s : Set X) :
    (∑ i ∈ s, (f i : ℝ≥0∞)) = ∑ i : X, if i ∈ s then (f i : ℝ≥0∞) else 0 := by
  classical
  have hs : s.toFinset = Finset.univ.filter (fun i : X => i ∈ s) := by
    ext i
    simp [Set.mem_toFinset]
  rw [hs]
  rw [Finset.sum_filter]

/-- real set-sum equals the filtered full sum -/
lemma rsum_eq_filter (f : X → ℝ≥0) (s : Set X) :
    (∑ i ∈ s, (f i : ℝ)) = ∑ i : X, if i ∈ s then (f i : ℝ) else 0 := by
  classical
  have hs : s.toFinset = Finset.univ.filter (fun i : X => i ∈ s) := by
    ext i
    simp [Set.mem_toFinset]
  rw [hs]
  rw [Finset.sum_filter]

/-- ENNReal sum over a set of a subset is ≤ the sum over a superset -/
lemma esum_mono_set (f : X → ℝ≥0) {s t : Set X} (h : s ⊆ t) :
    (∑ i ∈ s, (f i : ℝ≥0∞)) ≤ (∑ i ∈ t, (f i : ℝ≥0∞)) := by
  classical
  rw [esum_eq_filter, esum_eq_filter]
  exact Finset.sum_le_sum (by
    intro i hi
    by_cases his : i ∈ s
    · have hit : i ∈ t := h his
      simp [his, hit]
    · by_cases hit : i ∈ t
      · simp [his, hit]
      · simp [his, hit])

/-- real sum over a set of a subset ≤ sum over superset (functions nonneg) -/
lemma rsum_le_set_of_subset (f : X → ℝ≥0) {s t : Set X} (h : s ⊆ t) :
    (∑ i ∈ s, (f i : ℝ)) ≤ (∑ i ∈ t, (f i : ℝ)) := by
  classical
  rw [rsum_eq_filter, rsum_eq_filter]
  exact Finset.sum_le_sum (by
    intro i hi
    by_cases his : i ∈ s
    · have hit : i ∈ t := h his
      simp [his, hit]
    · by_cases hit : i ∈ t
      · simp [his, hit]
      · simp [his, hit])

/-- realSum equals the real part of the ENNReal sum -/
lemma realSum_eq_toReal (f : X → ℝ≥0) (s : Set X) :
    realSum f s = ((∑ i ∈ s, (f i : ℝ≥0∞)).toReal) := by
  classical
  unfold realSum
  rw [rsum_eq_filter]
  rw [esum_eq_filter]
  rw [ENNReal.toReal_sum]
  · congr 1
    funext i
    by_cases his : i ∈ s <;> simp [his]
  · intro i hi
    by_cases his : i ∈ s <;> simp [his]

/-- the ENNReal sup is an upper bound on each member -/
lemma le_bigSup {Λ : Set (X → ℝ≥0)} {s : Set X} {f : X → ℝ≥0} (hf : f ∈ Λ) :
    (∑ i ∈ s, (f i : ℝ≥0∞)) ≤ bigSup Λ s := by
  classical
  unfold bigSup
  have h1 : (∑ i ∈ s, (f i : ℝ≥0∞)) ≤ ⨆ (h : f ∈ Λ), (∑ i ∈ s, (f i : ℝ≥0∞)) := by
    exact le_iSup (fun h : f ∈ Λ => (∑ i ∈ s, (f i : ℝ≥0∞))) hf
  have h2 : (⨆ (h : f ∈ Λ), (∑ i ∈ s, (f i : ℝ≥0∞))) ≤
      ⨆ f' : X → ℝ≥0, ⨆ (h : f' ∈ Λ), (∑ i ∈ s, (f' i : ℝ≥0∞)) := by
    exact le_iSup (fun f' : X → ℝ≥0 =>
      (⨆ (h : f' ∈ Λ), (∑ i ∈ s, (f' i : ℝ≥0∞)))) f
  exact le_trans h1 h2

/-- if every member is below c then the sup is below c -/
lemma bigSup_le_of_forall {Λ : Set (X → ℝ≥0)} {s : Set X} {c : ℝ≥0∞}
    (h : ∀ f ∈ Λ, (∑ i ∈ s, (f i : ℝ≥0∞)) ≤ c) : bigSup Λ s ≤ c := by
  classical
  unfold bigSup
  exact iSup_le (fun f => iSup_le (fun hf => h f hf))

/-- sup at least y > 0, y finite, gives a member at least y/2 (ENNReal). -/
lemma exists_member_ge_half {Λ : Set (X → ℝ≥0)} {s : Set X} {y : ℝ≥0∞}
    (hy : 0 < y) (hfin : y ≠ ∞) (hsup : y ≤ bigSup Λ s) :
    ∃ f ∈ Λ, y / 2 ≤ (∑ i ∈ s, (f i : ℝ≥0∞)) := by
  classical
  by_contra hne
  push_neg at hne
  -- every member is < y/2, hence ≤ y/2
  have hle : bigSup Λ s ≤ y / 2 := by
    refine bigSup_le_of_forall (fun f hf => ?_)
    exact le_of_lt (hne f hf)
  have hhalf : y / 2 < y := ENNReal.half_lt_self (ne_of_gt hy) hfin
  exact (not_le_of_gt (lt_of_le_of_lt hle hhalf)) hsup

/-- toReal of a finite ENNReal upper bound chain -/
lemma toReal_le_of_le {a b : ℝ≥0∞} (hb : b ≠ ∞) (h : a ≤ b) : a.toReal ≤ b.toReal :=
  ENNReal.toReal_mono hb h

/-- real value of a member is at most the real value of the sup (when sup finite) -/
lemma realSum_le_bigSup_toReal {Λ : Set (X → ℝ≥0)} {s : Set X} {f : X → ℝ≥0}
    (hf : f ∈ Λ) (hfin : bigSup Λ s ≠ ∞) :
    realSum f s ≤ (bigSup Λ s).toReal := by
  classical
  rw [realSum_eq_toReal]
  exact ENNReal.toReal_mono hfin (le_bigSup hf)


/-- ENNReal binomial mass of a single subset -/
noncomputable def massENN (p : I) (s : Set X) : ℝ≥0∞ :=
  (unitInterval.toNNReal p : ℝ≥0∞) ^ s.ncard *
    (unitInterval.toNNReal (σ p) : ℝ≥0∞) ^ (Set.univ \ s).ncard

/-- real binomial mass (for a real parameter) -/
noncomputable def rmass (p : ℝ) (s : Set X) : ℝ :=
  p ^ s.ncard * (1 - p) ^ (Fintype.card X - s.ncard)

/-- complement ncard identity -/
lemma ncard_compl_univ (s : Set X) : (Set.univ \ s).ncard = Fintype.card X - s.ncard := by
  classical
  rw [Set.ncard_diff (s := s) (t := Set.univ) (Set.subset_univ s)]
  rw [Set.ncard_univ, Nat.card_eq_fintype_card]

/-- toReal of the ENNReal mass is the real mass -/
lemma massENN_toReal (p : I) (s : Set X) : (massENN p s).toReal = rmass (p : ℝ) s := by
  classical
  unfold massENN rmass
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_pow, ENNReal.toReal_pow]
  rw [ENNReal.coe_toReal, ENNReal.coe_toReal]
  rw [unitInterval.coe_toNNReal, unitInterval.coe_toNNReal]
  rw [unitInterval.coe_symm_eq]
  rw [ncard_compl_univ]

/-- ENNReal mass is finite -/
lemma massENN_lt_top (p : I) (s : Set X) : massENN p s ≠ ∞ := by
  classical
  unfold massENN
  rw [← ENNReal.coe_pow, ← ENNReal.coe_pow]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top

/-- ENNReal mass is nonzero when p ∈ (0,1) -/
lemma massENN_ne_zero (p : I) (hp₀ : 0 < p) (hp₁ : p < 1) (s : Set X) :
    massENN p s ≠ 0 := by
  classical
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp₀
  have hqR : 0 < 1 - (p : ℝ) := by
    have hp1 : (p : ℝ) < 1 := by exact_mod_cast hp₁
    linarith
  have hR : 0 < (massENN p s).toReal := by
    rw [massENN_toReal p s]
    unfold rmass
    positivity
  intro hz
  have hzR : (massENN p s).toReal = 0 := by simp [hz]
  linarith

/-- The expectation μ is a finite sum over subsets (Bridge). -/
lemma lintegral_binomial_eq_sum' (p : I) (f : Set X → ℝ≥0∞) :
    ∫⁻ s : Set X, f s ∂(binomialSetDistribution X p) =
      ∑ s : Set X, f s * massENN p s := by
  classical
  simpa [massENN, mul_assoc] using (Bridge.lintegral_binomial_eq_sum p f)

/-- Set-sum over a coerced Finset equals the Finset sum -/
lemma set_sum_of_finset (𝓖 : Finset (Set X)) (f : Set X → ℝ) :
    (∑ s ∈ (𝓖 : Set (Set X)), f s) = ∑ s ∈ 𝓖, f s := by
  classical
  have hs : ((𝓖 : Set (Set X)).toFinset) = 𝓖 := by
    ext s
    exact (Set.mem_toFinset)
  rw [hs]

/-- Finset-sum over the toFinset of a Set equals the Set-sum -/
lemma finset_sum_of_set (𝓖s : Set (Set X)) (f : Set X → ℝ) :
    (∑ s ∈ 𝓖s.toFinset, f s) = ∑ s ∈ 𝓖s, f s := by
  classical
  have hs : ((𝓖s.toFinset : Finset (Set X)) : Set (Set X)) = 𝓖s := by
    ext s
    exact (Set.mem_toFinset)
  rw [← hs]

/-- real binomial sum decomposes with the real masses -/
lemma binomSum_eq_massSum (p : ℝ) (g : Set X → ℝ) :
    Binom.binomSum p g = ∑ T : Set X, rmass p T * g T := by
  classical
  unfold Binom.binomSum rmass
  apply Finset.sum_congr rfl
  intro T hT
  ring

/-- the ENNReal expectation of the sup-process -/
noncomputable def mu (p : I) (Λ : Set (X → ℝ≥0)) : ℝ≥0∞ :=
  ∫⁻ s : Set X, bigSup Λ s ∂(binomialSetDistribution X p)

/-- the expectation decomposes over subsets -/
lemma mu_eq_sum (p : I) (Λ : Set (X → ℝ≥0)) :
    mu p Λ = ∑ s : Set X, bigSup Λ s * massENN p s := by
  classical
  unfold mu
  simpa [bigSup, massENN, mul_assoc] using (Bridge.lintegral_binomial_eq_sum p (bigSup Λ))

/-- all sup-values are finite when the expectation is -/
lemma bigSup_lt_top (p : I) (hp₀ : 0 < p) (hp₁ : p < 1) (Λ : Set (X → ℝ≥0))
    (hE : mu p Λ < ∞) (s : Set X) : bigSup Λ s ≠ ∞ := by
  classical
  have hmu := mu_eq_sum p Λ
  have hterm : bigSup Λ s * massENN p s ≤ mu p Λ := by
    rw [hmu]
    exact Finset.single_le_sum (by
      intro t ht
      exact (bot_le : (0 : ℝ≥0∞) ≤ bigSup Λ t * massENN p t)) (Finset.mem_univ s)
  have hfin : bigSup Λ s * massENN p s ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt hterm hE)
  have hmass0 : massENN p s ≠ 0 := massENN_ne_zero p hp₀ hp₁ s
  intro hinf
  apply hfin
  exact ENNReal.mul_eq_top.mpr (Or.inr ⟨hinf, hmass0⟩)

/-- the real part of the expectation equals the real-mass weighted sum of the real sups -/
lemma mu_toReal_eq (p : I) (hp₀ : 0 < p) (hp₁ : p < 1) (Λ : Set (X → ℝ≥0))
    (hE : mu p Λ < ∞) :
    (mu p Λ).toReal = ∑ s : Set X, rmass (p : ℝ) s * (bigSup Λ s).toReal := by
  classical
  have hfin (s : Set X) : bigSup Λ s ≠ ∞ := bigSup_lt_top p hp₀ hp₁ Λ hE s
  have hterm (s : Set X) : bigSup Λ s * massENN p s ≠ ∞ :=
    ENNReal.mul_ne_top (hfin s) (massENN_lt_top p s)
  have hto := ENNReal.toReal_sum (s := (Finset.univ : Finset (Set X)))
    (f := fun s : Set X => bigSup Λ s * massENN p s) (by
      intro s hs
      exact hterm s)
  rw [mu_eq_sum p Λ]
  rw [hto]
  congr 1
  funext s
  rw [ENNReal.toReal_mul]
  rw [massENN_toReal p s]
  ring

/-- real-value upper bound membership: realSum(f)(s) ≤ r(s) for f ∈ Λ -/
lemma realSum_le_toReal {Λ : Set (X → ℝ≥0)} (p : I) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hE : mu p Λ < ∞) {s : Set X} {f : X → ℝ≥0} (hf : f ∈ Λ) :
    realSum f s ≤ (bigSup Λ s).toReal := by
  classical
  have hfin : bigSup Λ s ≠ ∞ := bigSup_lt_top p hp₀ hp₁ Λ hE s
  exact realSum_le_bigSup_toReal hf hfin

/-- μ > 0 implies its real part > 0 -/
lemma mu_toReal_pos (p : I) (Λ : Set (X → ℝ≥0)) (hE₀ : 0 < mu p Λ) (hE : mu p Λ < ∞) :
    0 < (mu p Λ).toReal := by
  exact ENNReal.toReal_pos (ne_of_gt hE₀) (ne_of_lt hE)

/-- L2 is positive -/
lemma L2_pos : 0 < (L2 : ℝ) := by
  unfold L2
  positivity

/-- finite sums of finite ENNReal values are finite -/
lemma finite_sum_finite {α : Type*} (s : Finset α) (f : α → ℝ≥0∞)
    (hf : ∀ a ∈ s, f a ≠ ∞) : (∑ a ∈ s, f a) ≠ ∞ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has]
      exact ENNReal.add_ne_top.mpr ⟨hf a (by simp), ih (by
        intro b hb
        exact hf b (by simp [hb]))⟩

/-- real mass is nonnegative for p ∈ [0,1] -/
lemma rmass_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : Set X) : 0 ≤ rmass p T := by
  unfold rmass
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

/-- MAIN THEOREM: if the expectation is finite and positive then the upper family is p-small. -/
theorem selector_p_small (p : I) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Λ : Set (X → ℝ≥0))
    (hE₀ : 0 < mu p Λ) (hE : mu p Λ < ∞) :
    pSmall (p : ℝ) {s : Set X | (L2 : ℝ≥0∞) * mu p Λ ≤ bigSup Λ s} := by
  classical
  set μ : ℝ≥0∞ := mu p Λ with hμ
  have hμ0 : μ ≠ 0 := ne_of_gt (by simpa [hμ] using hE₀)
  have hμfin : μ ≠ ∞ := ne_of_lt (by simpa [hμ] using hE)
  have hμRpos : 0 < μ.toReal := ENNReal.toReal_pos hμ0 hμfin
  have hL2e : (0 : ℝ≥0∞) < (L2 : ℝ≥0∞) := by
    -- L2 : ℝ≥0 positive
    have hL2nn : (0 : ℝ≥0) < L2 := by
      -- (L2 : ℝ) > 0 → NNReal positive
      have hR : 0 < (L2 : ℝ) := L2_pos
      exact_mod_cast hR
    exact ENNReal.coe_pos.mpr hL2nn
  have hL2e0 : (L2 : ℝ≥0∞) ≠ 0 := ne_of_gt hL2e
  let y : ℝ≥0∞ := (L2 : ℝ≥0∞) * μ
  have hy0 : 0 < y := by
    dsimp [y]
    exact ENNReal.mul_pos hL2e0 hμ0
  have hyfin : y ≠ ∞ := by
    dsimp [y]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hμfin
  let c : ℝ := 2 / ((L2 : ℝ) * μ.toReal)
  have hcpos : 0 < c := by
    dsimp [c]
    have hL2R : 0 < (L2 : ℝ) := L2_pos
    positivity
  -- the upper family and the witness family
  let F : Set (Set X) := {s | y ≤ bigSup Λ s}
  let F' : Set (Set X) := {s | ∃ f ∈ Λ, y / 2 ≤ (∑ i ∈ s, (f i : ℝ≥0∞))}
  have Fsub : F ⊆ F' := by
    intro s hs
    rcases exists_member_ge_half (Λ := Λ) (s := s) (y := y) hy0 hyfin (by simpa [F, y] using hs) with ⟨f, hfΛ, hhalf⟩
    exact ⟨f, hfΛ, hhalf⟩
  -- witnesses
  have hex (s : Set X) (hs : s ∈ F') : ∃ f ∈ Λ, y / 2 ≤ (∑ i ∈ s, (f i : ℝ≥0∞)) := hs
  let tau : Set X → X → ℝ≥0 := fun s i => if hs : s ∈ F' then Classical.choose (hex s hs) i else 0
  have tau_mem (s : Set X) (hs : s ∈ F') : tau s ∈ Λ := by
    have hspec := Classical.choose_spec (hex s hs)
    simpa [tau, hs] using hspec.1
  have tau_sum (s : Set X) (hs : s ∈ F') : y / 2 ≤ (∑ i ∈ s, ((tau s i) : ℝ≥0∞)) := by
    have hspec := Classical.choose_spec (hex s hs)
    simpa [tau, hs] using hspec.2
  let lam : Set X → X → ℝ := fun s i => c * (tau s i : ℝ)
  have hlam0 : ∀ S ∈ F', ∀ i ∈ S, 0 ≤ lam S i := by
    intro S hS i hi
    dsimp [lam]
    exact mul_nonneg (le_of_lt hcpos) (by positivity)
  -- real witness lower bound: realSum (tau s) s ≥ (L2·μR)/2
  have tau_real_lb (s : Set X) (hs : s ∈ F') :
      realSum (tau s) s ≥ (L2 : ℝ) * μ.toReal / 2 := by
    have htoY : (y / 2).toReal = (L2 : ℝ) * μ.toReal / 2 := by
      dsimp [y]
      -- ((L2 : ∞)·μ)/2: toReal
      have h1 : (((L2 : ℝ≥0∞) * μ) / 2).toReal = (((L2 : ℝ≥0∞) * μ).toReal) / 2 := by
        rw [ENNReal.div_eq_inv_mul]
        rw [ENNReal.toReal_mul]
        rw [ENNReal.toReal_inv]
        have htwo : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
        rw [htwo]
        ring
      rw [h1]
      rw [ENNReal.toReal_mul]
      rw [ENNReal.coe_toReal]
    have hfin2 : y / 2 ≠ ∞ := ne_of_lt (ENNReal.div_lt_top hyfin (by norm_num : (2 : ℝ≥0∞) ≠ 0))
    have hmain := tau_sum s hs
    have hconv : realSum (tau s) s = (∑ i ∈ s, ((tau s i) : ℝ≥0∞)).toReal := realSum_eq_toReal (tau s) s
    have hsumfin : (∑ i ∈ s, ((tau s i) : ℝ≥0∞)) ≠ ∞ := by
      rw [esum_eq_filter (tau s)]
      exact finite_sum_finite (Finset.univ : Finset X) (fun i : X =>
        if i ∈ s then ((tau s i) : ℝ≥0∞) else 0) (by
        intro i hi
        by_cases his : i ∈ s <;> simp [his])
    have hle := ENNReal.toReal_le_toReal hfin2 hsumfin
    rw [hconv]
    rw [← htoY]
    exact hle.mpr hmain
  -- total weight of each member ≥ 1
  have htot1 : ∀ S ∈ F', 1 ≤ Sys.wtot lam S := by
    intro S hS
    have hb := tau_real_lb S hS
    -- Sys.wtot lam S = c * realSum (tau S) S
    have hwt : Sys.wtot lam S = c * realSum (tau S) S := by
      unfold Sys.wtot lam realSum
      rw [← Finset.mul_sum]
    rw [hwt]
    -- c * realSum ≥ c * (L2·μR/2) = 1
    have hm : c * ((L2 : ℝ) * μ.toReal / 2) ≤ c * realSum (tau S) S := by
      exact mul_le_mul_of_nonneg_left hb (le_of_lt hcpos)
    have hc1 : 1 ≤ c * ((L2 : ℝ) * μ.toReal / 2) := by
      dsimp [c]
      have hL2R : 0 < (L2 : ℝ) := L2_pos
      have hL2ne : (L2 : ℝ) ≠ 0 := ne_of_gt hL2R
      have hμRne : μ.toReal ≠ 0 := ne_of_gt hμRpos
      field_simp [hL2ne, hμRne]
      norm_num
    exact le_trans hc1 hm
  -- not-p-small of F'
  by_contra hnotF
  have hnotF' : ¬ pSmall (p : ℝ) F' := by
    intro hpF'
    exact hnotF (pSmall.mono (𝓕 := F) (𝓖 := F') (by simpa [F, F'] using Fsub) hpF')
  -- apply 5.7'
  have hE' : mu p Λ < ∞ := by simpa [hμ] using hE
  have h57 := Thm57p.thm57p (p : ℝ) F' lam hp₀ hp₁ hlam0 htot1 hnotF'
  -- pointwise upper bound
  have hpt (T : Set X) : Chain12.supFW lam F' T ≤ c * (bigSup Λ T).toReal := by
    unfold Chain12.supFW
    refine Sel.famSup_le_of_forall (fun S hS => ?_) ?_
    · -- S ∈ F': sumW lam S T ≤ c * r(T)
      have hmem := tau_mem S hS
      have hsub : (T ∩ S).toFinset ⊆ T.toFinset := by
        intro i hi
        exact (Set.mem_toFinset).2 (by
          rcases (Set.mem_toFinset).1 hi with ⟨hT, hS⟩
          exact hT)
      have h1 : ((T ∩ S).toFinset).sum (fun i : X => (tau S i : ℝ)) ≤
          T.toFinset.sum (fun i : X => (tau S i : ℝ)) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
          intro i hi hin
          positivity)
      have hsum : Chain12.sumW lam S T ≤ c * realSum (tau S) T := by
        unfold Chain12.sumW lam realSum
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left h1 (le_of_lt hcpos)
      have hle2 : c * realSum (tau S) T ≤ c * (bigSup Λ T).toReal := by
        exact mul_le_mul_of_nonneg_left (realSum_le_toReal p hp₀ hp₁ (by simpa [hμ] using hE) hmem) (le_of_lt hcpos)
      exact le_trans hsum hle2
    · -- 0 ≤ c * r(T)
      exact mul_nonneg (le_of_lt hcpos) (ENNReal.toReal_nonneg)
  -- binomSum ≤ c·μR
  have hub : Binom.binomSum (p : ℝ) (Chain12.supFW lam F') ≤ 2 / (L2 : ℝ) := by
    rw [binomSum_eq_massSum (p : ℝ) (Chain12.supFW lam F')]
    have hstep : (∑ T : Set X, rmass (p : ℝ) T * Chain12.supFW lam F' T) ≤
        ∑ T : Set X, rmass (p : ℝ) T * (c * (bigSup Λ T).toReal) := by
      exact Finset.sum_le_sum (by
        intro T hT
        exact mul_le_mul_of_nonneg_left (hpt T) (rmass_nonneg (p : ℝ) (le_of_lt hp₀) (le_of_lt hp₁) T))
    have hcc : (∑ T : Set X, rmass (p : ℝ) T * (c * (bigSup Λ T).toReal)) =
        c * (∑ T : Set X, rmass (p : ℝ) T * (bigSup Λ T).toReal) := by
      rw [Finset.mul_sum]
      congr 1
      funext T
      ring
    have hmueq : (∑ T : Set X, rmass (p : ℝ) T * (bigSup Λ T).toReal) = μ.toReal := by
      rw [mu_toReal_eq p hp₀ hp₁ Λ hE']
    calc
      (∑ T : Set X, rmass (p : ℝ) T * Chain12.supFW lam F' T)
          ≤ ∑ T : Set X, rmass (p : ℝ) T * (c * (bigSup Λ T).toReal) := hstep
      _ = c * (∑ T : Set X, rmass (p : ℝ) T * (bigSup Λ T).toReal) := hcc
      _ = c * μ.toReal := by rw [hmueq]
      _ = 2 / (L2 : ℝ) := by
            dsimp [c]
            have hL2R : 0 < (L2 : ℝ) := L2_pos
            have hL2ne : (L2 : ℝ) ≠ 0 := ne_of_gt hL2R
            have hμRne : μ.toReal ≠ 0 := ne_of_gt hμRpos
            field_simp [hL2ne, hμRne]
  -- contradiction
  have hLbig : 2 / (L2 : ℝ) < Thm57p.c0 := by
    dsimp [Thm57p.c0, Thm57p.J0, L2]
    norm_num
  have hcontra : Thm57p.c0 ≤ 2 / (L2 : ℝ) := le_trans h57 hub
  exact (not_le_of_gt hLbig) hcontra

end Final12
