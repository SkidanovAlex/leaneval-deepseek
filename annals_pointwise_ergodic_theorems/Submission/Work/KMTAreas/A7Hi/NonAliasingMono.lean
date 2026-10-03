import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Helper: monotonicity of `NonAliasing` in the scale

Needed to instantiate the crux `A7Hi/FiberRephaseNarrowBand` (which asks for the separation at
the packet scale `8δ`) and the band condition `A7Hi/FiberOpTexFixNarrow`: the tree provides
non-aliasing at the scale `-(2·uScale ρ L)` (`A7/fiberVarSamplingReduce.exists_nonAliasing_uScale`),
and the packet scale `-(2 d U₀)` (`d = P.natDegree`) is *narrower*, so the arcs are still disjoint.
-/

/-- `realArc` is monotone in the scale. -/
theorem realArc_mono_of_le {k k' : ℤ} (h : k' ≤ k) :
    Work.Analysis.IonescuWainger.realArc k' ⊆ Work.Analysis.IonescuWainger.realArc k := by
  have hpow : (2 : ℝ) ^ k' ≤ (2 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) h
  intro θ hθ
  simp only [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at hθ ⊢
  exact ⟨by linarith [hθ.1, hpow], by linarith [hθ.2, hpow]⟩

/-- **Non-aliasing is monotone in the scale**: if the arcs `α + ℝ_{≤k}` are pairwise disjoint then
so are the narrower arcs `α + ℝ_{≤k'}` for `k' ≤ k`. -/
theorem nonAliasing_mono_scale {k k' : ℤ} (h : k' ≤ k)
    {A : Finset Work.Analysis.IonescuWainger.Circle}
    (hA : Work.Analysis.IonescuWainger.NonAliasing k A) :
    Work.Analysis.IonescuWainger.NonAliasing k' A := by
  intro α hα β hβ θ hθ θ' hθ' heq
  exact hA α hα β hβ θ (realArc_mono_of_le h hθ) θ' (realArc_mono_of_le h hθ') heq

/-- **Non-aliasing at the scale `k` separates the frequencies by `2^{k+1}`.**

This is the quantitative shadow of `NonAliasing`: the arcs `α + ℝ_{≤k}` and `β + ℝ_{≤k}` are
disjoint as soon as `α ≠ β`, and their difference set is `ℝ_{≤k+1} = [-2^{k+1}, 2^{k+1}]`.  It is
what turns the tree's non-aliasing input (`A7/fiberVarSamplingReduce.exists_nonAliasing_uScale`)
into the `8δ`-separation hypothesis of the crux `A7Hi/FiberRephaseNarrowBand`. -/
theorem nonAliasing_separation {k : ℤ}
    {A : Finset Work.Analysis.IonescuWainger.Circle}
    (hA : Work.Analysis.IonescuWainger.NonAliasing k A)
    {α β : Work.Analysis.IonescuWainger.Circle} (hα : α ∈ A) (hβ : β ∈ A) (hne : α ≠ β) :
    (2 : ℝ) ^ (k + 1) < ‖α - β‖ := by
  by_contra hle
  push_neg at hle
  -- a real representative `v` of `α - β`, with `|v| ≤ 1/2`
  set v : ℝ := (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) (α - β)).val with hvdef
  have hvm : (v : Work.Analysis.IonescuWainger.Circle) = α - β := AddCircle.coe_equivIco
  have hvlo : -(1 / 2 : ℝ) ≤ v := by
    rw [hvdef]; simpa using (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) (α - β)).2.1
  have hvhi : v < (1 / 2 : ℝ) := by
    rw [hvdef]
    have h := (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) (α - β)).2.2
    linarith
  have hnorm : ‖α - β‖ = |v| := by
    rw [← hvm]
    refine (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr ?_
    rw [abs_one, abs_le]
    exact ⟨hvlo, hvhi.le⟩
  have hvabs : |v| ≤ (2 : ℝ) ^ (k + 1) := by rw [← hnorm]; exact hle
  -- build `θ, θ' ∈ realArc k` with `θ' - θ = v`
  have hkey : ∃ θ ∈ Work.Analysis.IonescuWainger.realArc k,
      ∃ θ' ∈ Work.Analysis.IonescuWainger.realArc k, θ' - θ = v := by
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
    have hsplit : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      ring
    have hmax : max v 0 ≤ (2 : ℝ) ^ (k + 1) :=
      max_le (le_trans (le_abs_self v) hvabs) (by positivity)
    have hmin : -((2 : ℝ) ^ (k + 1)) ≤ min v 0 :=
      le_min (by linarith [neg_abs_le v, hvabs])
        (by linarith [zpow_pos (by norm_num : (0 : ℝ) < 2) (k + 1)])
    refine ⟨(2 : ℝ) ^ k - max v 0, ?_, (2 : ℝ) ^ k + min v 0, ?_, ?_⟩
    · rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
      constructor
      · linarith [hmax, h2k, hsplit]
      · linarith [le_max_right v (0 : ℝ)]
    · rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
      constructor
      · linarith [hmin, h2k, hsplit]
      · linarith [min_le_right v (0 : ℝ)]
    · have : (2 : ℝ) ^ k + min v 0 - ((2 : ℝ) ^ k - max v 0) = min v 0 + max v 0 := by ring
      rw [this]
      linarith [min_add_max v (0 : ℝ)]
  obtain ⟨θ, hθ, θ', hθ', hsub⟩ := hkey
  have heq : α + (θ : Work.Analysis.IonescuWainger.Circle)
      = β + (θ' : Work.Analysis.IonescuWainger.Circle) := by
    have h2 : (θ' : Work.Analysis.IonescuWainger.Circle)
        - (θ : Work.Analysis.IonescuWainger.Circle) = α - β := by
      have h : (((θ' - θ : ℝ)) : Work.Analysis.IonescuWainger.Circle) = α - β := by
        rw [hsub]; exact hvm
      push_cast at h
      exact h
    refine sub_eq_zero.mp ?_
    calc α + (θ : Work.Analysis.IonescuWainger.Circle)
          - (β + (θ' : Work.Analysis.IonescuWainger.Circle))
        = (α - β) - ((θ' : Work.Analysis.IonescuWainger.Circle)
            - (θ : Work.Analysis.IonescuWainger.Circle)) := by abel
      _ = 0 := by rw [h2]; abel
  obtain ⟨hαβ, -⟩ := hA α hα β hβ θ hθ θ' hθ' heq
  exact hne hαβ

end

end Work.KMTAreas.A7Hi
