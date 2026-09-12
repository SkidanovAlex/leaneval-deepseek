import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Prob
import Submission.Mono2
import Submission.PVCore
import Submission.PVAPI
import Submission.PVCost

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval ProbabilityTheory
open FractionalExpectationThresholds
open Submission.PVC
open Submission.PVAPI
open Submission.PVCost
open Submission.FET

attribute [local instance] Classical.propDecidable

namespace Submission
namespace PVIter

universe u
variable {X : Type u} [Fintype X]

/-- Bernoulli `p` probability mass. -/
noncomputable def bmass (p : ℝ) (W : Set X) : ℝ :=
  (p : ℝ) ^ W.ncard * (1 - p) ^ (Fintype.card X - W.ncard)

/-- expectation under Bernoulli-`p`. -/
noncomputable def expW (p : ℝ) (f : Set X → ℝ) : ℝ :=
  ∑ W : Set X, bmass p W * f W

/-- union of a list of sets. -/
def sUnion : List (Set X) → Set X
  | [] => ∅
  | w :: ws => w ∪ sUnion ws

/-- round parameter for the head of a list whose tail has `ws.length` elements:
`2^ws.length`. -/
noncomputable def mOf (ws : List (Set X)) : ℕ := (2 : ℕ) ^ ws.length

/-- family after processing rounds in `ws` (left-to-right). -/
def runFam (H : Set (Set X)) : List (Set X) → Set (Set X)
  | [] => H
  | w :: ws => runFam (Sm H w (mOf ws)) ws

/-- total removed cost when processing the rounds in `ws`. -/
noncomputable def zRun (q0 : ℝ) (H : Set (Set X)) : List (Set X) → ℝ
  | [] => 0
  | w :: ws => ccost q0 (Lm H w (mOf ws)) + zRun q0 (Sm H w (mOf ws)) ws

/-- binomial-tail budget of a single round with parameter `2^t`. -/
noncomputable def bOne (L : ℕ) (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc ((2 : ℕ) ^ t) ((2 : ℕ) ^ (t + 1) - 1),
    ((((2 : ℕ) ^ (t + 1) - 1).choose j : ℝ) * (1 / L) ^ j)

/-- total cost budget for `d` rounds. -/
noncomputable def tailCost (L : ℕ) : ℕ → ℝ
  | 0 => 0
  | d + 1 => bOne L d + tailCost L d

/-- expected removed cost over `d` independent Bernoulli-`(1-(1-q0)^L)` rounds. -/
noncomputable def iterCost (q0 : ℝ) (L : ℕ) : ℕ → Set (Set X) → ℝ
  | 0, _ => 0
  | d + 1, H => expW (1 - (1 - q0) ^ L)
      (fun W => ccost q0 (Lm H W ((2 : ℕ) ^ d)) + iterCost q0 L d (Sm H W ((2 : ℕ) ^ d)))

/-- per-vertex probability after `d` rounds of `L` copies: `1-(1-q0)^{dL}`, as an `I`. -/
noncomputable def pD (q0 : ℝ) (hq0 : 0 ≤ q0) (hq01 : q0 ≤ 1) (L d : ℕ) : I :=
  ⟨1 - (1 - q0) ^ (d * L), by
    have hle : (1 - q0) ^ (d * L) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    linarith, by
    have h : 0 ≤ (1 - q0) ^ (d * L) := pow_nonneg (by linarith) _
    linarith⟩

/-! ### deterministic lemmas -/

/-- a round with parameter `m ≥ 1` only keeps sets of size `< m`. -/
lemma Sm_small {H : Set (Set X)} {W : Set X} {m : ℕ} {F : Set X} (hF : F ∈ Sm H W m) :
    F.ncard < m := Sm_mem_ncard_lt hF

/-- processing a nonempty list yields a family contained in `{∅}`. -/
lemma runFam_small : ∀ (H : Set (Set X)) (ws : List (Set X)), ws ≠ [] → runFam H ws ⊆ {∅} := by
  intro H ws
  revert H
  induction ws with
  | nil => intro H h; simp at h
  | cons w ws ih =>
      intro H hnon
      by_cases hws : ws = []
      · subst ws
        intro F hF
        have hs : F.ncard < (1 : ℕ) := by
          simpa [runFam, mOf] using (Sm_small (H := H) (W := w) (m := 1) hF)
        have hz : F.ncard = 0 := by omega
        have hF0 : F = ∅ := (Set.ncard_eq_zero).mp hz
        simp [hF0]
      · intro F hF
        have htail : runFam (Sm H w (mOf ws)) ws ⊆ {∅} := ih (Sm H w (mOf ws)) hws
        have hF' : F ∈ runFam (Sm H w (mOf ws)) ws := by simpa [runFam] using hF
        exact htail hF'

/-- if the final family contains the empty set then the union of the rounds contains a member
of the original family. -/
lemma runFam_empty_hit : ∀ (H : Set (Set X)) (ws : List (Set X)),
    (∅ : Set X) ∈ runFam H ws → ∃ S ∈ H, S ⊆ sUnion ws := by
  intro H ws
  have gen : ∀ ws : List (Set X), ∀ H : Set (Set X),
      (∅ : Set X) ∈ runFam H ws → ∃ S ∈ H, S ⊆ sUnion ws := by
    intro ws
    refine List.recOn ws ?_ ?_
    · intro H h
      exact ⟨(∅ : Set X), by simpa [runFam] using h, by simp [sUnion]⟩
    · intro w ws' rec H h
      have hF : (∅ : Set X) ∈ runFam (Sm H w (mOf ws')) ws' := by simpa [runFam] using h
      rcases rec (Sm H w (mOf ws')) hF with ⟨T, hT, hTsub⟩
      have hFrag : T ∈ Frag H w := Sm_mem_frag hT
      rcases mem_Frag.mp hFrag with ⟨S, hS, hT⟩
      refine ⟨S, hS, ?_⟩
      intro x hxS
      by_cases hxw : x ∈ w
      · exact Or.inl hxw
      · have hxSdiff : x ∈ S \ w := by simpa [hxw] using hxS
        have hxT' : x ∈ T := by simpa [hT] using hxSdiff
        exact Or.inr (hTsub hxT')

  exact gen ws H

/-- one-round cost drop. -/
lemma costDrop {q0 : ℝ} (hq0 : 0 ≤ q0) {H : Set (Set X)} {W : Set X} {m : ℕ} :
    ccost q0 H ≤ ccost q0 (Sm H W m) + ccost q0 (Lm H W m) := by
  have h1 : ccost q0 H ≤ ccost q0 (FStar H W) := ccost_le_ccost_FStar
  have hF : FStar H W = Lm H W m ∪ Sm H W m := FStar_eq_union
  have h2 : ccost q0 (FStar H W) ≤ ccost q0 (Lm H W m) + ccost q0 (Sm H W m) := by
    rw [hF]
    exact ccost_subadd hq0 (Lm H W m) (Sm H W m)
  linarith

/-- cost of the processed family is at least the original minus the removed. -/
lemma runFam_cost_drop {q0 : ℝ} (hq0 : 0 ≤ q0) : ∀ (H : Set (Set X)) (ws : List (Set X)),
    ccost q0 H ≤ ccost q0 (runFam H ws) + zRun q0 H ws := by
  intro H ws
  revert H
  induction ws with
  | nil => intro H; simp [runFam, zRun]
  | cons w ws ih =>
      intro H
      have hstep : ccost q0 H ≤ ccost q0 (Sm H w (mOf ws)) + ccost q0 (Lm H w (mOf ws)) := by
        exact costDrop hq0
      have ih' : ccost q0 (Sm H w (mOf ws)) ≤
          ccost q0 (runFam (Sm H w (mOf ws)) ws) + zRun q0 (Sm H w (mOf ws)) ws :=
        ih (Sm H w (mOf ws))
      calc
        ccost q0 H ≤ ccost q0 (Sm H w (mOf ws)) + ccost q0 (Lm H w (mOf ws)) := hstep
        _ ≤ (ccost q0 (runFam (Sm H w (mOf ws)) ws) + zRun q0 (Sm H w (mOf ws)) ws)
            + ccost q0 (Lm H w (mOf ws)) := by linarith
        _ = ccost q0 (runFam H (w :: ws)) + zRun q0 H (w :: ws) := by
          simp [runFam, zRun]
          ring

/-- failure to hit means the removed cost is at least the original cost. -/
lemma fail_ge_cost {q0 : ℝ} (hq0 : 0 ≤ q0) (H : Set (Set X)) {ws : List (Set X)}
    (hws : ws ≠ []) (hfail : sUnion ws ∉ Up H) : ccost q0 H ≤ zRun q0 H ws := by
  have hsmall : runFam H ws ⊆ {∅} := runFam_small H ws hws
  have hdrop := runFam_cost_drop hq0 H ws
  have hnotempty : (∅ : Set X) ∉ runFam H ws := by
    intro he
    rcases runFam_empty_hit H ws he with ⟨S, hS, hSsub⟩
    exact hfail ⟨S, hS, hSsub⟩
  have hrun0 : ccost q0 (runFam H ws) = 0 := by
    have hEq : runFam H ws = ∅ := by
      apply Subset.antisymm
      · intro F hF
        have hF0 : F ∈ ({∅} : Set (Set X)) := hsmall hF
        have hFemp : F = ∅ := by simpa using hF0
        exfalso
        exact hnotempty (by simpa [hFemp] using hF)
      · intro F hF
        simp at hF
    rw [hEq]
    exact ccost_empty hq0
  linarith

/-! ### probabilistic bounds (statements) -/

/-- the per-round binomial tail is small. -/
lemma bOne_le (L : ℕ) (hL : 4 ≤ L) (t : ℕ) : bOne L t ≤ 2 * (4 / L) ^ ((2 : ℕ) ^ t) := by
  sorry

/-- the total budget over any number of rounds is at most `8/L`. -/
lemma tailCost_le {L : ℕ} (hL : 4 ≤ L) : ∀ d : ℕ, tailCost L d ≤ 8 / L := by
  sorry

/-- expected removed cost bound. -/
lemma iterCost_le (q0 : ℝ) (L : ℕ) (hL : 1 ≤ L) (hq0 : 0 < q0) (hq01 : q0 ≤ 1) :
    ∀ d (H : Set (Set X)), Bounded H ((2 : ℕ) ^ d - 1) →
      iterCost q0 L d H ≤ mu (pD q0 hq0.le hq01 L d) (Up H) * tailCost L d := by
  sorry

end PVIter
end Submission
