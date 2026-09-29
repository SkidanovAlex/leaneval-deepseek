import Mathlib
import Submission.Work.TMC14Core.Defs

/-!
# `uniform_small_scale`: the upper bound on the window is uniform near it

If the Lyapunov exponent `lyap α lam` vanishes on a nondegenerate window `[c,d]` of real
energies, then the locally uniform upper bound contained in `P_LEBasics` can be made
*uniform over the window*: there is a complex neighbourhood of `[c,d]` (together with an
index `n₀`) on which `log ‖A_n(x)‖_F ≤ n ε'` for all `n ≥ n₀` and all phases `x`.

The point is compactness of `[c,d]`: part (2) of `P_LEBasics` gives, for every `E ∈ [c,d]`,
a radius `r E > 0` and an index `N E` such that
`log (frob (iterC α lam z n x)) ≤ n (lyap α lam (E:ℂ) + ε') = n ε'` whenever
`‖z - E‖ < r E`, `n ≥ N E`; halving the radii gives an open cover of the compact interval,
a finite subcover `t`, and then `ρ = min_{i ∈ t} r i / 2 > 0`, `n₀ = max_{i ∈ t} N i` work.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace Work.TMC14Core

theorem uniform_small_scale (hLE : P_LEBasics) (α lam c d : ℝ) (hIrr : Irrational α)
    (hcd : c < d) (hzero : ∀ E ∈ Set.Icc c d, lyap α lam (E : ℂ) = 0) (ε' : ℝ) (hε' : 0 < ε') :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ n₀ : ℕ, ∀ z : ℂ, (∃ E ∈ Set.Icc c d, ‖z - E‖ < ρ) →
      ∀ n : ℕ, n₀ ≤ n → ∀ x : ℝ, Real.log (frob (iterC α lam z n x)) ≤ (n : ℝ) * ε' := by
  -- ## Local (in the energy `E`) bounds coming from `P_LEBasics`
  have hloc : ∀ E : Icc c d, ∃ r : ℝ, 0 < r ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ,
      ‖z - ((E : ℝ) : ℂ)‖ < r → ∀ x : ℝ, Real.log (frob (iterC α lam z n x)) ≤ (n : ℝ) * ε' := by
    intro E
    obtain ⟨r, hr, N, hN⟩ := hLE.2 α lam hIrr ((E : ℝ) : ℂ) ε' hε'
    refine ⟨r, hr, N, ?_⟩
    intro n hn z hz x
    have h1 := hN n hn z hz x
    have h0 : lyap α lam ((E : ℝ) : ℂ) = 0 := hzero (E : ℝ) E.2
    rw [h0, zero_add] at h1
    exact h1
  choose r hr N hN using hloc
  -- ## Compactness: a finite subcover of `[c,d]` by the halved balls
  have hcov : (Set.Icc c d) ⊆ ⋃ E : (Set.Icc c d : Set ℝ), Metric.ball (E : ℝ) (r E / 2) := by
    intro E hE
    refine Set.mem_iUnion.mpr ⟨⟨E, hE⟩, ?_⟩
    rw [Metric.mem_ball, Subtype.coe_mk, Real.dist_eq, sub_self, abs_zero]
    linarith [hr ⟨E, hE⟩]
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover
    (fun E : (Set.Icc c d : Set ℝ) => Metric.ball (E : ℝ) (r E / 2))
    (fun _ => Metric.isOpen_ball) hcov
  have htne : t.Nonempty := by
    have hc : c ∈ Set.Icc c d := ⟨le_rfl, hcd.le⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht hc)
    obtain ⟨hit, -⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hit⟩
  refine ⟨(t.image (fun E => r E / 2)).min' (htne.image _), ?_, t.sup N, ?_⟩
  · rw [Finset.lt_min'_iff]
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨E, -, rfl⟩ := hb
    linarith [hr E]
  · intro z hz n hn x
    obtain ⟨E, hE, hElt⟩ := hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (ht hE)
    obtain ⟨hjmemt, hjball⟩ := Set.mem_iUnion.mp hj
    -- real closeness of the two centres
    have hdist : |E - ((j : ℝ))| < r j / 2 := by
      have hb := Metric.mem_ball.mp hjball
      rw [Real.dist_eq] at hb
      exact hb
    have hρle : (t.image (fun E => r E / 2)).min' (htne.image _) ≤ r j / 2 :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem _ hjmemt)
    -- `z` is within `r j` of the centre `j`
    have hzclose : ‖z - ((j : ℝ) : ℂ)‖ < r j := by
      have hdecomp : z - ((j : ℝ) : ℂ) = (z - ((E : ℝ) : ℂ)) + (((E : ℝ) : ℂ) - ((j : ℝ) : ℂ)) := by
        ring
      rw [hdecomp]
      have h1 : ‖(z - ((E : ℝ) : ℂ)) + (((E : ℝ) : ℂ) - ((j : ℝ) : ℂ))‖
          ≤ ‖z - ((E : ℝ) : ℂ)‖ + ‖((E : ℝ) : ℂ) - ((j : ℝ) : ℂ)‖ := norm_add_le _ _
      have h2 : ‖((E : ℝ) : ℂ) - ((j : ℝ) : ℂ)‖ = |E - ((j : ℝ))| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have h3 : ‖z - ((E : ℝ) : ℂ)‖ < (t.image (fun E => r E / 2)).min' (htne.image _) := hElt
      linarith
    exact hN j n (le_trans (Finset.le_sup hjmemt) hn) z hzclose x

end Work.TMC14Core
