import Submission.ZagierHoffmanProof.StepM3
import Submission.ZagierHoffmanProof.StepL35
import Submission.ZagierHoffmanProof.Basic

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L36: Prop 3.2 (H_k) — expansion infrastructure and the theorem-A tail

★ `AdmExp F w k s` is (H_k)'s conclusion at a tuple `s`: `ζ_A s` is a finite
`K`-linear combination of `ζ_A(c)`'s with every `c` `k`-admissible of weight `w`.
This module lays down the recursion architecture of the H_k proof and proves the
pure infrastructure it composes:
  • `admExp_self`: an admissible weight-`w` tuple is its own expansion (coefficient 1);
  • ★ `admExp_combine`: the SPLICE combinator — given an identity
    `ζ_A s = Σ_i (a i)·ζ_A(c i)` and an expansion of every `c i`, produce the
    expansion of `s` (index type `Σ i, ιᵢ`, coefficients `a i · a' i j`, by
    `Fintype.sum_sigma`).  This is what the Step-1 decomposition identity plus
    per-member expansions plug into at every recursion step;
  • `kAdmissible_mono`: `k`-adm ⟹ `(k−1)`-adm (outputs of level `k` are admissible
    at every lower level);
  • ★ `admissible_mem_𝒯`: the theorem-A tail — a weight-`w` `w`-admissible tuple `c`
    satisfies `ζ_A c ∈ 𝒯 F w` (from `wAdmissible_weight_conds`, StepM1).

ARCHITECTURE (from SESSION 183e/f; the β-choice is resolved inside this proof):
  H_k (all weight-w tuples) is obtained from:
    (LEM)  H_k on all tuples ⟸ H_{k−1} + H_k on all (k−1)-adm tuples
           [non-(k−1)-adm `t`: apply H_{k−1}(t) and splice with admExp_combine];
    (MAIN) H_k on (k−1)-adm weight-w tuples by well-founded induction on the measure
           M(t) := (prefix-k(t), −Init-rank(t)) [Route B: NO member (k−1)-adm, NO
           member entry bounds, NO member re-decomposition — per SESSION 183f the
           type-3 members provably carry entries > q, so neither Route A nor F3 is
           buildable]; the Step-1 members are dispatched by
             k-adm → admExp_self;
             type-1/type-2 → prefix-k STRICT < S (type1/2_psum_lt_k) ⟹ measure drop;
             type-3 → prefix-k ≤ S with Init strictly growing when = S
             (type3_psum_k_le_X + type3_Init_gt) ⟹ measure drop;
           the CASE-1/CASE-2 split on the (k−1)-adm ¬k-adm input uses
           `depth_ge_of_not_adm` (StepM3) + `prop212_step1` (StepL35) / Prop 2.13;
    The final theorem-A span part: H_w on weight-w tuples + `admissible_mem_𝒯`
    ⟹ every weight-w `ζ_A s ∈ span K (𝒯 F w)`.
  H_1's base (s₁ ≤ q: admissible or R1 for the depth-1 (q); s₁ > q: Lemma-2.9
  CW(R1) + well-founded induction on s₁) is independent of the k ≥ 2 machinery.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]
/-- ★ Prop-3.2's (H_k) conclusion at a concrete tuple: `ζ_A s` is a finite
`K`-linear combination of `ζ_A(c)`'s with `c` `k`-admissible of weight `w`. -/
def AdmExp (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]
    (w k : ℕ) {r : ℕ} (s : Fin r → ℕ+) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (dep : ι → ℕ) (hdep : ∀ i : ι, 0 < dep i)
    (c : ∀ i : ι, Fin (dep i) → ℕ+) (a : ι → RatFunc F),
    (∀ i : ι, weight (dep i) (c i) = w) ∧
    (∀ i : ι, kAdmissible (Nat.card F) (c i) k) ∧
    ζ_A F s = ∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (c i)


/-- A `k`-admissible weight-`w` tuple is trivially its own expansion (coefficient 1). -/
lemma admExp_self (w k : ℕ) {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hadm : kAdmissible (Nat.card F) s k) : AdmExp F w k s := by
  classical
  refine ⟨PUnit, inferInstance, fun _ => r, fun _ => hr, fun _ => s, fun _ => 1,
    ?_, ?_, ?_⟩
  · intro i
    exact hw
  · intro i
    exact hadm
  · simp [completion_coe_one]

/-- ★ Splice an expansion of every output into an identity: if `ζ_A s = Σ a_i ζ_A(c_i)`
and each `c_i` expands into admissible outputs, then `s` does.  (The recursion
combinator of Prop 3.2: the Step-1 decomposition identity + per-member expansions.) -/
lemma admExp_combine (w k : ℕ) {r : ℕ} (s : Fin r → ℕ+)
    {ι : Type} [Fintype ι] (dep : ι → ℕ) (hdep : ∀ i : ι, 0 < dep i)
    (c : ∀ i : ι, Fin (dep i) → ℕ+) (a : ι → RatFunc F)
    (hid : ζ_A F s = ∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (c i))
    (e : ∀ i : ι, AdmExp F w k (c i)) :
    AdmExp F w k s := by
  classical
  choose ι' fin' dep' hdep' c' a' hw' hadm' hid' using e
  let κ : ι → Type := ι'
  letI : ∀ i : ι, Fintype (κ i) := fun i => fin' i
  refine ⟨Σ i : ι, κ i, inferInstance,
    fun p => dep' p.1 p.2, fun p => hdep' p.1 p.2,
    fun p => c' p.1 p.2,
    fun p => a p.1 * a' p.1 p.2, ?_, ?_, ?_⟩
  · intro p
    exact hw' p.1 p.2
  · intro p
    exact hadm' p.1 p.2
  · calc
      ζ_A F s = ∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (c i) := hid
      _ = ∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) *
            (∑ j : κ i, ((a' i j : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (c' i j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            congr 1
            exact hid' i
      _ = ∑ i : ι, ∑ j : κ i,
            (((a i : RatFunc F) * a' i j : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (c' i j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            have hcast : (((a i : RatFunc F) * a' i j : RatFunc F) : RatFunc.CompletionAtInfty F) =
                ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) *
                  ((a' i j : RatFunc F) : RatFunc.CompletionAtInfty F) := by
              change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (a i * a' i j)) =
                (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (a i)) *
                  (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (a' i j))
              rw [map_mul]
            rw [hcast]
            ring
      _ = ∑ p : Σ i : ι, κ i,
            (((a p.1 : RatFunc F) * a' p.1 p.2 : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (c' p.1 p.2) := by
            exact (Fintype.sum_sigma (f := fun p : Σ i : ι, κ i =>
              (((a p.1 : RatFunc F) * a' p.1 p.2 : RatFunc F) : RatFunc.CompletionAtInfty F) *
                ζ_A F (c' p.1 p.2))).symm

/-- `k`-admissibility is monotone in `k`: `k`-admissible tuples are `(k−1)`-admissible. -/
lemma kAdmissible_mono (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) {k : ℕ} (hk : 1 ≤ k)
    (hadm : kAdmissible q s k) : kAdmissible q s (k - 1) := by
  constructor
  · intro x hx
    have hxk : x < k := by omega
    exact hadm.1 x hxk
  · intro hc2
    apply hadm.2
    rcases hc2 with ⟨hr1, hrk, hall, hlast⟩
    refine ⟨hr1, ?_, hall, hlast⟩
    omega

/-- ★ The theorem-A tail: a weight-`w` `w`-admissible tuple is a member of the set
`𝒯 F w` of admissible MZV values (so `ζ_A(c) ∈ 𝒯 F w ⊆ span K (𝒯 F w)`). -/
lemma admissible_mem_𝒯 (w : ℕ) {r : ℕ} (hr : 0 < r) (c : Fin r → ℕ+)
    (hw : weight r c = w) (hadm : kAdmissible (Nat.card F) c w) :
    ζ_A F c ∈ 𝒯 F w := by
  classical
  rw [mem_𝒯_iff F w]
  refine ⟨⟨r, hr⟩, ?_⟩
  rw [mem_𝒯_aux_iff F w ⟨r, hr⟩]
  refine ⟨c, ?_, ?_, ?_, rfl⟩
  · exact hw
  · intro i hi
    exact (wAdmissible_weight_conds (Nat.card F) c hr hw hadm).1 i hi
  · exact (wAdmissible_weight_conds (Nat.card F) c hr hw hadm).2

/-- A finite `K`-combination of elements of a submodule lies in it (coefficient form:
each summand is `((a i : RatFunc F) : K∞) * z i = (a i) • (z i)`). -/
lemma sum_mem_span {ι : Type} [Fintype ι] (a : ι → RatFunc F) (z : ι → RatFunc.CompletionAtInfty F)
    (T : Set (RatFunc.CompletionAtInfty F))
    (hz : ∀ i : ι, z i ∈ Submodule.span (RatFunc F) T) :
    (∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) * z i) ∈
      Submodule.span (RatFunc F) T := by
  classical
  apply Submodule.sum_mem
  intro i hi
  -- ((a i : RatFunc F) : K∞) * z i = (a i) • (z i)
  have hsmul : ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) * z i =
      (a i) • (z i) := by
    rw [Algebra.smul_def]
    rfl
  rw [hsmul]
  exact Submodule.smul_mem _ _ (hz i)

/-- An admissible expansion puts `ζ_A s` in the span of `𝒯 F w` (weights are `w`). -/
lemma mem_span_of_admExp (w : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w)
    (h : AdmExp F w w s) : ζ_A F s ∈ Submodule.span (RatFunc F) (𝒯 F w) := by
  classical
  rcases h with ⟨ι, fin, dep, hdep, c, a, hw', hadm', hid⟩
  letI : Fintype ι := fin
  rw [hid]
  apply sum_mem_span (a := a) (z := fun i => ζ_A F (c i)) (T := 𝒯 F w)
  intro i
  -- c i has weight w (hw' i) and depth dep i ≥ 1 (hdep i): admissible_mem_𝒯 needs 0 < dep i ✓
  have hi0 : 0 < dep i := hdep i
  exact Submodule.subset_span (admissible_mem_𝒯 F w hi0 (c i) (hw' i) (hadm' i))

/-- ★ G7 assembly (argument form): if H_w holds (every weight-w tuple expands into
weight-w `w`-admissible tuples — `hH`), then `𝒵 F w ≤ span K (𝒯 F w)`, i.e. the
spanning half of theorem A. -/
theorem theoremA_span_of_H (w : ℕ)
    (hH : ∀ ⦃r : ℕ⦄ (s : Fin r → ℕ+), weight r s = w → AdmExp F w w s) :
    𝒵 F w ≤ Submodule.span (RatFunc F) (𝒯 F w) := by
  classical
  -- 𝒵 w = span (⋃ r, ζ_A_weight w r); show that union-set ⊆ span(𝒯)
  rw [𝒵]
  rw [Submodule.span_le]
  intro x hx
  -- x ∈ ⋃ r, ζ_A_weight F w r
  rw [Set.mem_iUnion] at hx
  rcases hx with ⟨r, hrx⟩
  rw [ζ_A_weight_mem_iff F w r] at hrx
  rcases hrx with ⟨s, hsum, rfl⟩
  have hw : weight r s = w := hsum
  exact mem_span_of_admExp F w s hw (hH s hw)

/-- G7 corollary: the full span equality `𝒵 F w = span K (𝒯 F w)` from H_w. -/
theorem theoremA_span_eq_of_H (w : ℕ) (hw : 0 < w)
    (hH : ∀ ⦃r : ℕ⦄ (s : Fin r → ℕ+), weight r s = w → AdmExp F w w s) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w) := by
  classical
  apply le_antisymm
  · exact theoremA_span_of_H F w hH
  · -- 𝒯 F w ⊆ 𝒵 F w: each ζ_A(c), c ∈ 𝔖'_w-weight-w, lies in 𝒵 (ζ_A_weight_subset_span)
    rw [Submodule.span_le]
    intro x hx
    rw [mem_𝒯_iff F w] at hx
    rcases hx with ⟨r, hrx⟩
    rw [mem_𝒯_aux_iff F w r] at hrx
    rcases hrx with ⟨c, hset, hle, hlt, rfl⟩
    -- c ∈ 𝔖_w w r (weight w) and ζ_A c ∈ 𝒵 w via ζ_A_weight_subset_span
    have hw' : weight (r : ℕ) c = w := by
      exact (𝔖_w_mem_iff w (r : ℕ) c).mp hset
    have hmem : ζ_A F c ∈ ζ_A_weight F w (r : ℕ) := by
      rw [ζ_A_weight_mem_iff F w (r : ℕ)]
      refine ⟨c, hw', rfl⟩
    exact ζ_A_weight_subset_span F w (r : ℕ) hmem


end ZagierHoffmanPositiveChar
