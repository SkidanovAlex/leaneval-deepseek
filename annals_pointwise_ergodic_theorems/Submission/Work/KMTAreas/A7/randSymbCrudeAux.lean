/-
# Auxiliary facts for `Work.KMTAreas.A7.randSymb_Tle_crude`

The crude `ℓ^p` bound for the randomised symbol `randSymb (smallSymbF …) ε K` of the small-scale
tuple reduces, through Young's inequality for the `ℓ¹` kernel of the Ionescu–Wainger multiplier,
to two `L¹` bounds for the symbol itself: it is `C²` with compact support
(`randSymb_contDiff_hasCompactSupport`), and the integrals `∫‖σ‖`, `∫‖σ''‖` are bounded by
`2 · (sup over the finitely many active scales) · #active` (`bumpS`, `bumpS_spec`).  This module
collects the elementary pieces; the main file `randSymb_Tle_crude.lean` performs the assembly.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded
import Submission.Work.KMTAreas.A7.randSymb_schwartz

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-- The `L¹` bound of `varphiNt_bounds` with the support radius dropped: there is a constant `S`,
depending on `N, k` but not on `t ∈ [1/2,1]`, which bounds both `∫ ‖φ_{N,t}‖` and
`∫ ‖φ_{N,t}''‖`. -/
lemma exists_bumpS (N k : ℕ) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      ContDiff ℝ 2 (fun ξ => varphiNt N k t ξ) ∧
      HasCompactSupport (fun ξ => varphiNt N k t ξ) ∧
      (∫ y, ‖varphiNt N k t y‖) ≤ S ∧
      (∫ y, ‖iteratedDeriv 2 (fun ξ => varphiNt N k t ξ) y‖) ≤ S := by
  obtain ⟨R, S, hS, hspec⟩ := varphiNt_bounds N k
  exact ⟨S, hS, fun t ht => ⟨(hspec t ht).2.1, (hspec t ht).2.2.1,
    (hspec t ht).2.2.2.1, (hspec t ht).2.2.2.2⟩⟩

/-- The canonical uniform bump bound. -/
noncomputable def bumpS (N k : ℕ) : ℝ := Classical.choose (exists_bumpS N k)

lemma bumpS_nonneg (N k : ℕ) : 0 ≤ bumpS N k :=
  (Classical.choose_spec (exists_bumpS N k)).1

lemma bumpS_spec (N k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    (∫ y, ‖varphiNt N k t y‖) ≤ bumpS N k ∧
    (∫ y, ‖iteratedDeriv 2 (fun ξ => varphiNt N k t ξ) y‖) ≤ bumpS N k := by
  have h := (Classical.choose_spec (exists_bumpS N k)).2 t ht
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- A finite sum of compactly supported functions is compactly supported. -/
lemma hasCompactSupport_finsetSum {ι : Type*} :
    ∀ (s : Finset ι) (g : ι → ℝ → ℂ), (∀ m ∈ s, HasCompactSupport (g m)) →
      HasCompactSupport (fun ξ : ℝ => ∑ m ∈ s, g m ξ) := by
  classical
  intro s
  induction s using Finset.induction with
  | empty =>
      intro g _
      have hzero : (fun ξ : ℝ => ∑ m ∈ (∅ : Finset ι), g m ξ) = (0 : ℝ → ℂ) := by
        funext ξ; simp
      rw [hzero]
      exact HasCompactSupport.zero
  | insert a s ha ih =>
      intro g hg
      have h1 := ih g (fun m hm => hg m (Finset.mem_insert_of_mem hm))
      have h2 : HasCompactSupport (g a) := hg a (Finset.mem_insert_self a s)
      have heq : (fun ξ : ℝ => ∑ m ∈ insert a s, g m ξ)
          = g a + (fun ξ : ℝ => ∑ m ∈ s, g m ξ) := by
        funext ξ
        simp [Finset.sum_insert ha]
      rw [heq]
      exact h2.add h1

/-- The randomised symbol `randSymb (smallSymbF …) ε K` is `C²` with compact support. -/
lemma randSymb_contDiff_hasCompactSupport (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ε : ℕ → ℂ) (K : ℕ) :
    ContDiff ℝ 2 (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) ∧
      HasCompactSupport (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) := by
  have hcd : ∀ m : ℕ, ContDiff ℝ 2 (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t m) := by
    intro m
    rw [smallSymbF_apply]
    by_cases h : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
    · rw [if_pos h]; exact contDiff_varphiNt _ _ t
    · rw [if_neg h]
      exact contDiff_const
  have hcs : ∀ m : ℕ, HasCompactSupport (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t m) := by
    intro m
    rw [smallSymbF_apply]
    by_cases h : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
    · rw [if_pos h]; exact hasCompactSupport_varphiNt _ _ t
    · rw [if_neg h]
      exact HasCompactSupport.zero
  have hsymb : randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K
      = fun ξ : ℝ => ∑ n ∈ Finset.range K, ε n *
          (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t (n + 1) ξ - smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n ξ) :=
    rfl
  constructor
  · rw [hsymb]
    exact ContDiff.sum (fun n _ => (contDiff_const (c := ε n)).mul ((hcd (n + 1)).sub (hcd n)))
  · rw [hsymb]
    refine hasCompactSupport_finsetSum _ _ (fun n _ => ?_)
    exact ((hcs (n + 1)).sub (hcs n)).comp_left (g := fun z : ℂ => ε n * z) (by simp)

end

end Work.KMTAreas.A7
