import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.thetaBoxAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

/-- Monotone convergence for a nonnegative function on the half-line `Iz = [0,∞)`:
if `g ≥ 0` is integrable on every box `[0, n+1]` and the box integrals are uniformly
bounded by `M`, then `g` is integrable on `Iz`, the box integrals converge to the
integral over `Iz`, and that integral is at most `M`. -/
theorem monotone_interval (g : ℝ → ℝ) (M : ℝ)
    (hmeas : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hnn : ∀ z, 0 ≤ g z)
    (hint : ∀ n : ℕ, MeasureTheory.IntegrableOn g (Set.Icc 0 ((n : ℝ) + 1)))
    (hbdd : ∀ n : ℕ, ∫ z in Set.Icc 0 ((n : ℝ) + 1), g z ≤ M) :
    MeasureTheory.IntegrableOn g Work.Spaces.Iz
      ∧ Filter.Tendsto (fun n : ℕ => ∫ z in Set.Icc 0 ((n : ℝ) + 1), g z) Filter.atTop (nhds (∫ z in Work.Spaces.Iz, g z))
      ∧ (∫ z in Work.Spaces.Iz, g z) ≤ M := by
  -- The boxes `[0, n+1]` are increasing and exhaust the half-line `Iz`.
  have hmono : Monotone (fun n : ℕ => Set.Icc 0 ((n:ℝ)+1)) := by
    intro i j hij
    refine Set.Icc_subset_Icc_right ?_
    have hij' : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
    linarith
  have hdir : Directed (· ⊆ ·) (fun n : ℕ => Set.Icc 0 ((n:ℝ)+1)) :=
    fun i j => ⟨max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩
  have hUnion : (⋃ n : ℕ, Set.Icc 0 ((n:ℝ)+1)) = Work.Spaces.Iz := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Icc, Work.Spaces.Iz, Set.mem_Ici]
    constructor
    · rintro ⟨n, h0, _⟩; exact h0
    · intro h0
      obtain ⟨n, hn⟩ := exists_nat_gt x
      exact ⟨n, h0, by linarith⟩
  -- Monotone convergence of the `lintegral` over the increasing directed union.
  have hsupé : ∫⁻ x in Work.Spaces.Iz, ENNReal.ofReal (g x)
      = ⨆ n : ℕ, ∫⁻ x in Set.Icc 0 ((n:ℝ)+1), ENNReal.ofReal (g x) := by
    rw [← hUnion]
    exact MeasureTheory.setLIntegral_iUnion_of_directed _ hdir
  -- On each box, the `lintegral` of `ofReal g` is the `ofReal` of the Bochner integral.
  have hterm : ∀ n : ℕ, ∫⁻ x in Set.Icc 0 ((n:ℝ)+1), ENNReal.ofReal (g x)
      = ENNReal.ofReal (∫ x in Set.Icc 0 ((n:ℝ)+1), g x) := by
    intro n
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Set.Icc 0 ((n:ℝ)+1)))
      (hint n) (Filter.Eventually.of_forall hnn)).symm
  have hbb : ∀ n : ℕ, ∫⁻ x in Set.Icc 0 ((n:ℝ)+1), ENNReal.ofReal (g x) ≤ ENNReal.ofReal M := by
    intro n
    rw [hterm n]
    exact ENNReal.ofReal_le_ofReal (hbdd n)
  have hle : ∫⁻ x in Work.Spaces.Iz, ENNReal.ofReal (g x) ≤ ENNReal.ofReal M := by
    rw [hsupé]
    exact iSup_le hbb
  -- Hence the `lintegral` over `Iz` is finite, which gives integrability.
  have hne : (∫⁻ x in Work.Spaces.Iz, ENNReal.ofReal (g x)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  have hintS : MeasureTheory.IntegrableOn g Work.Spaces.Iz :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas (Filter.Eventually.of_forall hnn)).mp hne
  -- With integrability available, the standard monotone set-integral limit applies.
  have hconv : Filter.Tendsto (fun n : ℕ => ∫ x in Set.Icc 0 ((n:ℝ)+1), g x) Filter.atTop (nhds (∫ x in Work.Spaces.Iz, g x)) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone (μ := volume) (f := g)
      (s := fun n : ℕ => Set.Icc 0 ((n:ℝ)+1)) (fun n => measurableSet_Icc) hmono (by rw [hUnion]; exact hintS)
    rwa [hUnion] at h
  have hfin : (∫ z in Work.Spaces.Iz, g z) ≤ M := le_of_tendsto' hconv hbdd
  exact ⟨hintS, hconv, hfin⟩

end Work.Coercivity
