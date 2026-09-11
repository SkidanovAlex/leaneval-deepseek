import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.ObsT
import Submission.ObsTPrime
import Submission.Nice
import Submission.ML
import Submission.DeepThm
import Submission.Pre
import Submission.Binom
import Submission.Binom2

/-!
# 5.7''-general and 5.7' for sup-type processes (Chain12).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Chain12

open Frame
open Sel
open Sel.Deep
open Sel.Deep.Sys

variable {X : Type*} [Fintype X]

/-- the weight sum Σ_{i ∈ S ∩ W} lam S i -/
noncomputable def sumW (lam : Set X → X → ℝ) (S W : Set X) : ℝ := by
  classical
  exact (W ∩ S).toFinset.sum (fun i : X => lam S i)

/-- the sup-process value at W for a weighted family -/
noncomputable def supFW (lam : Set X → X → ℝ) (F : Set (Set X)) (W : Set X) : ℝ :=
  famSup (fun S : Set X => sumW lam S W) F

/-- sumW is nonnegative under nonnegative weights -/
lemma sumW_nonneg {lam : Set X → X → ℝ} {F : Set (Set X)}
    (hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i) {S : Set X} (hS : S ∈ F) (W : Set X) :
    0 ≤ sumW lam S W := by
  classical
  unfold sumW
  exact Finset.sum_nonneg (by
    intro i hi
    exact hnonneg S hS i (Set.mem_toFinset.mp hi).2)

/-- supFW is monotone in W (weights nonnegative). -/
lemma supFW_mono {lam : Set X → X → ℝ} {F : Set (Set X)}
    (hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i) {W W' : Set X} (hW : W ⊆ W') :
    supFW lam F W ≤ supFW lam F W' := by
  classical
  unfold supFW
  refine famSup_le_of_forall (fun S hS => ?_) ?_
  · have hle : sumW lam S W ≤ sumW lam S W' := by
      unfold sumW
      have hsub : (W ∩ S).toFinset ⊆ (W' ∩ S).toFinset := by
        intro i hi
        exact (Set.mem_toFinset).mpr (by
          rcases (Set.mem_toFinset).mp hi with ⟨hiW, hiS⟩
          exact ⟨hW hiW, hiS⟩)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro i hi hin
        exact hnonneg S hS i ((Set.mem_toFinset).mp hi).2)
    exact le_trans hle (le_famSup (v := fun T : Set X => sumW lam T W') hS)
  · exact famSup_nonneg (fun S hS => sumW_nonneg hnonneg hS W')

/-- supFW nonnegative -/
lemma supFW_nonneg {lam : Set X → X → ℝ} {F : Set (Set X)}
    (hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i) (W : Set X) : 0 ≤ supFW lam F W := by
  classical
  unfold supFW
  exact famSup_nonneg (fun S hS => sumW_nonneg hnonneg hS W)

/-- weight of W∩T equals the sum over its elements of wlev(lv): fiber decomposition. -/
lemma weight_sum_eq (N : Sys X) (T W : Set X) (hTlv : ∀ i ∈ W ∩ T, N.lv T i ≤ N.τ) :
    N.weight T (W ∩ T) = (W ∩ T).toFinset.sum (fun i : X => wlev (N.lv T i)) := by
  classical
  let A : Finset X := (W ∩ T).toFinset
  let G : ℕ → Finset X := fun j => A.filter (fun i : X => i ∈ N.levelSet T j)
  have hcard0 (j : ℕ) : ((W ∩ T) ∩ N.levelSet T j).ncard = (G j).card := by
    dsimp [G, A]
    rw [Set.ncard_eq_toFinset_card ((W ∩ T) ∩ N.levelSet T j) (Set.toFinite _)]
    congr 1
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have h1 := (Set.Finite.mem_toFinset (Set.toFinite ((W ∩ T) ∩ N.levelSet T j))).1 hx
      exact Finset.mem_filter.mpr ⟨(Set.mem_toFinset).2 h1.1, h1.2⟩
    · intro hx
      have h1 := (Finset.mem_filter.mp hx)
      exact (Set.Finite.mem_toFinset (Set.toFinite ((W ∩ T) ∩ N.levelSet T j))).2
        ⟨(Set.mem_toFinset).1 h1.1, h1.2⟩
  have hGmem (j : ℕ) {i : X} (hi : i ∈ G j) : N.lv T i = j := by
    have h := (Finset.mem_filter.mp hi).2
    exact h.2
  have hGsub (j : ℕ) : G j ⊆ A := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hdisj : ((Finset.range (N.τ + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint G := by
    intro j hj k hk hjk
    change Disjoint (G j) (G k)
    rw [Finset.disjoint_left]
    intro i hi hik
    apply hjk
    calc
      j = N.lv T i := (hGmem j hi).symm
      _ = k := hGmem k hik
  have hunion : (Finset.range (N.τ + 1)).biUnion G = A := by
    ext i
    constructor
    · intro hi
      rcases (Finset.mem_biUnion.mp hi) with ⟨j, hj, hij⟩
      exact hGsub j hij
    · intro hi
      have hi' : i ∈ W ∩ T := (Set.mem_toFinset).1 hi
      refine (Finset.mem_biUnion.mpr) ⟨N.lv T i, ?_, ?_⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hTlv i hi'))
      · exact Finset.mem_filter.mpr ⟨hi, ⟨hi'.2, rfl⟩⟩
  calc
    N.weight T (W ∩ T)
        = ∑ j ∈ Finset.range (N.τ + 1), ((G j).card : ℝ) * wlev j := by
          unfold Sys.weight
          apply Finset.sum_congr rfl
          intro j hj
          rw [hcard0 j]
    _ = ∑ j ∈ Finset.range (N.τ + 1), (G j).sum (fun _ : X => wlev j) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = ∑ j ∈ Finset.range (N.τ + 1), (G j).sum (fun i : X => wlev (N.lv T i)) := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro i hi
          rw [hGmem j hi]
    _ = ∑ i ∈ (Finset.range (N.τ + 1)).biUnion G, wlev (N.lv T i) := by
          rw [Finset.sum_biUnion hdisj]
    _ = ∑ i ∈ A, wlev (N.lv T i) := by rw [hunion]
    _ = (W ∩ T).toFinset.sum (fun i : X => wlev (N.lv T i)) := by rfl

/-- single-member domination: weight of W∩T ≤ Σ_{W∩S} lam -/
lemma weight_le_sumW (N : Sys X) (F : Set (Set X)) (lam : Set X → X → ℝ)
    (hB : N.LevelBounded) {T : Set X} (hT : T ∈ N.F) (W : Set X)
    {S : Set X} (hSF : S ∈ F) (hTS : T ⊆ S)
    (hdomi : ∀ i ∈ T, lam S i ≥ wlev (N.lv T i))
    (hlam : ∀ i ∈ S, 0 ≤ lam S i) :
    N.weight T (W ∩ T) ≤ sumW lam S W := by
  classical
  have hTlv : ∀ i ∈ W ∩ T, N.lv T i ≤ N.τ := by
    intro i hi
    exact hB T hT i hi.2
  have h1 : N.weight T (W ∩ T) = (W ∩ T).toFinset.sum (fun i : X => wlev (N.lv T i)) :=
    weight_sum_eq N T W hTlv
  have hsub : (W ∩ T).toFinset ⊆ (W ∩ S).toFinset := by
    intro i hi
    exact (Set.mem_toFinset).mpr (by
      rcases (Set.mem_toFinset).mp hi with ⟨hW, hT⟩
      exact ⟨hW, hTS hT⟩)
  calc
    N.weight T (W ∩ T) = (W ∩ T).toFinset.sum (fun i : X => wlev (N.lv T i)) := h1
    _ ≤ (W ∩ T).toFinset.sum (fun i : X => lam S i) := by
          exact Finset.sum_le_sum (by
            intro i hi
            exact hdomi i ((Set.mem_toFinset).mp hi).2)
    _ ≤ (W ∩ S).toFinset.sum (fun i : X => lam S i) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
            intro i hi hin
            exact hlam i ((Set.mem_toFinset).mp hi).2)
    _ = sumW lam S W := rfl

/-- processed value ≤ sup-type value, pointwise in W -/
lemma procVal_le_supFW (N : Sys X) (F : Set (Set X)) (lam : Set X → X → ℝ)
    (hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i)
    (hdom : ∀ T ∈ N.F, ∃ S ∈ F, T ⊆ S ∧ ∀ i ∈ T, lam S i ≥ wlev (N.lv T i))
    (hB : N.LevelBounded) (W : Set X) :
    N.procVal W ≤ supFW lam F W := by
  classical
  unfold Sys.procVal supFW
  refine famSup_le_of_forall (fun T hT => ?_) ?_
  · rcases hdom T hT with ⟨S, hSF, hTS, hdomi⟩
    have hle1 : N.weight T (W ∩ T) ≤ sumW lam S W :=
      weight_le_sumW N F lam hB hT W hSF hTS hdomi (fun i hi => hnonneg S hSF i hi)
    have hle2 : sumW lam S W ≤ famSup (fun S' : Set X => sumW lam S' W) F :=
      le_famSup (v := fun S' : Set X => sumW lam S' W) hSF
    exact le_trans hle1 hle2
  · exact famSup_nonneg (fun S hS => sumW_nonneg hnonneg hS W)

/-- monotonicity of uniform averages (same level) -/
lemma avgOver_mono (v u : Set X → ℝ) (w0 : ℕ) (hw0 : w0 ≤ Fintype.card X)
    (hvu : ∀ W ∈ Binom.levelFinset X w0, v W ≤ u W) :
    Sys.avgOver v w0 ≤ Sys.avgOver u w0 := by
  classical
  have hCpos : 0 < (Binom.levelFinset X w0).card := by
    rw [DeepThm.levelFinset_card w0 hw0]
    exact Nat.choose_pos hw0
  have hC : 0 ≤ ((Binom.levelFinset X w0).card : ℝ) := by exact_mod_cast (le_of_lt hCpos)
  rw [DeepThm.avgOver_eq v w0 hw0]
  rw [DeepThm.avgOver_eq u w0 hw0]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (by intro W hW; exact hvu W hW)) hC

/-- 5.7''-general: not p-small with total weight ≥ 1 gives the uniform expectation ≥ 10^{-11} -/
theorem thm57gen (p : ℝ) (J : ℕ) (F : Set (Set X)) (lam : Set X → X → ℝ)
    (hJ : 10 ^ 20 ≤ J) (hp0 : 0 < p) (hp1 : p < 1)
    (hnonneg : ∀ S ∈ F, ∀ i ∈ S, 0 ≤ lam S i)
    (htot1 : ∀ S ∈ F, 1 ≤ Sys.wtot lam S)
    (hnot : ¬ pSmall p F) :
    ((10 : ℝ) ^ 11)⁻¹ ≤ Sys.avgOver (supFW lam F) (Sys.wSize J (Fintype.card X) p) := by
  classical
  rcases Pre.theorem_preprocess F lam hnonneg htot1 with ⟨N, hFB, hTot, hLeg, htrim, hdom⟩
  have hnotN : ¬ pSmall p N.F := by
    intro hpN
    exact hnot (pSmall.superset_family (p := p) (𝓕 := F) (𝓕' := N.F) (by
      intro S hS
      rcases htrim S hS with ⟨S', hS'F, hS'S⟩
      exact ⟨S', hS'F, hS'S⟩) hpN)
  have hdeep := DeepThm.nice57 p J N hJ hp0 hp1 hFB hTot hLeg hnotN
  have hw0 : Sys.wSize J (Fintype.card X) p ≤ Fintype.card X := by
    unfold Sys.wSize
    exact min_le_left _ _
  have hdomw : ∀ W : Set X, N.procVal W ≤ supFW lam F W :=
    procVal_le_supFW N F lam hnonneg hdom hFB
  have hmono : Sys.avgOver (fun W : Set X => N.procVal W) (Sys.wSize J (Fintype.card X) p)
      ≤ Sys.avgOver (supFW lam F) (Sys.wSize J (Fintype.card X) p) := by
    exact avgOver_mono (fun W : Set X => N.procVal W) (supFW lam F)
      (Sys.wSize J (Fintype.card X) p) hw0 (by
        intro W hW
        exact hdomw W)
  exact le_trans hdeep hmono

end Chain12
end Submission
