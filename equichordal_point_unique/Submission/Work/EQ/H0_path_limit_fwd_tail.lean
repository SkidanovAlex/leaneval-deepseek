import Mathlib
import Submission.Work.EQ.tailP_bdd_near_puncture
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.chainWord_eventually_true_pos
import Submission.Work.EQ.H0_fibre_defs
import Submission.Work.EQ.label_dichotomy_cont
import Submission.Work.EQ.path_slit_of_isChain
import Submission.Work.Topology.uniform_bound_Ici_of_tendsto

namespace Work.EQ

open Filter _root_.Topology
open Complex
open Classical

noncomputable section

/-- **The principal forward tail of a continuous path of chains is uniform.**

Let `γ : ℝ → ChainData` be a continuous path (on `Ici S`) of `EqRelC`-chains whose stable
linearising parameter converges, `ψ₁(γ s) → u ≠ 0`.  Then there is a uniform index `n₁` from which
*every* chain of the path is already the principal stable leaf for its own parameter:
`(γ s).1 n = germC a h (λⁿ ψ₁(γ s))` for all `n ≥ n₁` and all `s ≥ S`.

Only `IsChain` is needed (no `H0`-membership): every point of a chain above index `n₁` is a fan
value with parameter `λ^{n}ψ₁(γ s)` (`Work.EQ.chain_eq_fan'` applied to `Work.EQ.shiftZ`, which
needs only `IsChain`), hence its backward radicand lies in the slit plane uniformly
(`Work.EQ.fan_slitPlane`), so the branch labels above `n₁` are independent of `s`
(`Work.EQ.label_dichotomy` + preconnectedness of `Ici S`), and the principal label at a single
reference parameter forces the principal leaf (`Work.EQ.TailP_of_invBranch_true_ge`). -/
theorem H0_path_limit_fwd_tail {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {γ : ℝ → Work.EQ.ChainData} {S : ℝ}
    (hγ : ∀ s, S ≤ s → Work.EQ.IsChain a h (γ s)) (hcont : ContinuousOn γ (Set.Ici S))
    {u : ℂ} (hu : u ≠ 0) (h1 : Filter.Tendsto (fun s => (γ s).2.1) Filter.atTop (nhds u)) :
    ∃ n₁ : ℕ, ∀ s, S ≤ s → ∀ n : ℕ, n₁ ≤ n →
      (γ s).1 (n : ℤ) = Work.EQ.germC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ n * (γ s).2.1) := by
  -- the contraction ratio `λ = eqLam a = (1-a)/(1+a)`
  have hl0 : (0 : ℝ) < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hl1le : eqLam a ≤ 1 := le_of_lt hl1
  -- the stable germ in rectangular coordinates: analytic near `0`, and the principal backward
  -- branch inverts the stable step there
  obtain ⟨ρ, hρ, _hAnC, _hgerm0, hgermPr, _hinjY, _hderivY⟩ := germC_facts (h := h) ha0 ha1 hh
  -- the stable parameter is uniformly bounded along the path
  have hcont_psi : ContinuousOn (fun s : ℝ => (γ s).2.1) (Set.Ici S) :=
    (continuous_fst.comp continuous_snd).comp_continuousOn hcont
  obtain ⟨B, hB0, hB⟩ := Work.Topology.uniform_bound_Ici_of_tendsto hcont_psi h1
  -- above a uniform index the backward radicands lie in the slit plane
  obtain ⟨n₀, hn₀⟩ := path_slit_of_isChain (h := h) (r := r) ha0 ha1 hh hγ hB0 hB
  -- and above one more index the germ parameter `λ^m ψ₁` lies in the analyticity ball
  obtain ⟨nρ, hnρ⟩ : ∃ m : ℕ, (eqLam a) ^ m * B < ρ := by
    rcases eq_or_lt_of_le hB0 with hz | hp
    · exact ⟨0, by rw [← hz, mul_zero]; exact hρ⟩
    · obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hρ hp) hl1
      refine ⟨m, ?_⟩
      have h2 : (eqLam a) ^ m * B < (ρ / B) * B := mul_lt_mul_of_pos_right hm hp
      rwa [div_mul_cancel₀ _ (ne_of_gt hp)] at h2
  set M : ℕ := max n₀ nρ with hMdef
  have hM₀ : n₀ ≤ M := le_max_left _ _
  have hMρ : nρ ≤ M := le_max_right _ _
  have hslitM : ∀ s, S ≤ s → ∀ m : ℕ, M ≤ m →
      (((γ s).1 ((m : ℤ) + 1)).1 + ((a / 2 : ℝ) : ℂ)) ^ 2
        + ((γ s).1 ((m : ℤ) + 1)).2 ^ 2 ∈ Complex.slitPlane :=
    fun s hs m hm => hn₀ s hs m (le_trans hM₀ hm)
  have hballM : ∀ m : ℕ, M ≤ m → (eqLam a) ^ m * B < ρ := by
    intro m hm
    have h1' : (eqLam a) ^ m ≤ (eqLam a) ^ nρ :=
      pow_le_pow_of_le_one hl0.le hl1le (le_trans hMρ hm)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1' hB0) hnρ
  -- the coordinates are continuous along the path
  have hcoord : ∀ n : ℤ, ContinuousOn (fun s : ℝ => (γ s).1 n) (Set.Ici S) := fun n =>
    ((continuous_apply n).comp continuous_fst).comp_continuousOn hcont
  -- above `M` the branch label of a step does not depend on `s` (`Ici S` is preconnected)
  have hdich : ∀ m : ℕ, M ≤ m →
      (∀ s, S ≤ s → (γ s).1 (m : ℤ) = invBranch a true ((γ s).1 ((m : ℤ) + 1))) ∨
      (∀ s, S ≤ s → (γ s).1 (m : ℤ) = invBranch a false ((γ s).1 ((m : ℤ) + 1))) := by
    intro m hm
    exact label_dichotomy_cont (a := a) (D := Set.Ici S) (isPreconnected_Ici (a := S))
      (hcoord (m : ℤ)) (hcoord ((m : ℤ) + 1))
      (fun s hs => (hγ s hs).1 (m : ℤ) |>.1)
      (fun s hs => hslitM s hs m hm)
  -- at the reference parameter `s = S` the chain's own tail makes the labels `true`
  have hchainS : IsChain a h (γ S) := hγ S le_rfl
  obtain ⟨Nc, hNc⟩ := chainWord_eventually_true_pos (h := h) ha0 ha1 hh hchainS
  have htrueRef : ∀ m : ℤ, (Nc : ℤ) ≤ m →
      (γ S).1 m = invBranch a true ((γ S).1 (m + 1)) := by
    intro m hm
    rw [chainWord_spec hchainS m, hNc m hm]
  set R : ℕ := max M Nc with hRdef
  have hMR : M ≤ R := le_max_left _ _
  have hNR : Nc ≤ R := le_max_right _ _
  refine ⟨R, fun s hs n hn => ?_⟩
  -- from `R` on the labels are `true` for *every* `s ≥ S`
  have htrue : ∀ m : ℕ, R ≤ m →
      (γ s).1 (m : ℤ) = invBranch a true ((γ s).1 ((m : ℤ) + 1)) := by
    intro m hm
    have hMm : M ≤ m := le_trans hMR hm
    rcases hdich m hMm with hT | hF
    · exact hT s hs
    · -- a `false` label everywhere would be false at the reference parameter
      exfalso
      have hcast : (Nc : ℤ) ≤ (m : ℤ) := by exact_mod_cast le_trans hNR hm
      exact invBranch_true_ne_false_of_slit (hslitM S le_rfl m hMm)
        ((htrueRef (m : ℤ) hcast).symm.trans (hF S le_rfl))
  have hRle : (eqLam a) ^ R * B < ρ :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hl0.le hl1le hMR) hB0) (hballM M le_rfl)
  exact TailP_of_invBranch_true_ge (h := h) ha0 ha1 (hγ s hs) hB0 (hB s hs)
    (fun w hw => (hgermPr w hw).2) hRle htrue n hn

end

end Work.EQ
