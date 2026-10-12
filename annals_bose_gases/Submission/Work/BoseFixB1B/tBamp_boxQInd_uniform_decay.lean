import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.SliceVocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Uniform `(1+‖p‖)⁻³` decay of the FS box-projected windowed amplitude

The windowed amplitude

    `tBamp χ p Φ i x = ∫_z χ(z)e^{−i⟪p,z⟫}·Φ(x_{i←z}) dz`

is the `p`-convention Fourier transform of the compactly supported smooth fibre
`z ↦ χ(z)Φ(x_{i←z})`; `Work.SmallBoxTBWord.tBamp_decay` bounds it by `C(1+‖p‖)⁻³` uniformly on
the box, for every `C^∞` state `Φ`.

The FS-faithful box mean-free projection `Q_{B,i} = 1_A(x_i) − P_{B,i}` (`Work.UBBInputs8.boxQInd`)
is **not** smooth (it carries the box indicator), so `tBamp_decay` cannot be applied to it
directly.  The repair is the exact subtraction identity of `Work.BoseBox.tBamp_boxQInd_eq_sub`:
since the window is supported in the box, the indicator is invisible to the amplitude and

    `tBamp χ p (Q_{B,i}Ψ) i x = tBamp χ p Ψ i x − (P_{B,i}Ψ)(x)·tBamp χ p 1 i x`,

the difference of the amplitude of the smooth state `Ψ` and the (slot-independent) box mean times
the amplitude of the constant state `1`.  Both amplitudes decay like `(1+‖p‖)⁻³` by
`tBamp_decay`; the box mean is bounded on the box by `B·|A|/|volA|`, because a point of
`A ⊆ acube a` inserted into a configuration of `abox N a` stays in the box, where `|Ψ| ≤ B`.
(For `volA = 0` the Lean convention `1/0 = 0` makes the mean vanish.)

No hypothesis is needed on the sign of `volA`, and `Ψ` need not be compactly supported — only its
smoothness (for the Fourier decay) and its bound on the box enter.
-/

namespace Work.BoseFixB1B

open MeasureTheory
open scoped Real ENNReal Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

/-- The norm of a real number seen as a complex number. -/
private lemma norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

/-- Replacing one coordinate of a point of the ambient box by a point of a set `A ⊆ acube a` keeps
the configuration in the ambient box. -/
private lemma update_mem_abox_of_subset {N : ℕ} {a : ℝ} {A : Set E3}
    (hAc : A ⊆ Submission.BoseGases.acube a) {x : Submission.BoseGases.X N}
    (hx : x ∈ Submission.BoseGases.abox N a) {z : E3} (hz : z ∈ A) (i : Fin N) :
    Function.update x i z ∈ Submission.BoseGases.abox N a := by
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro j
  by_cases hj : j = i
  · subst hj; rw [Function.update_self]; exact hAc hz
  · rw [Function.update_of_ne hj]; exact hx j

theorem tBamp_boxQInd_uniform_decay {N : ℕ} {a volA B : ℝ} (ha : 0 < a) (hB : 0 ≤ B)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχs : HasCompactSupport χ) (hχA : Function.support χ ⊆ A)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N a, |Ψ x| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Submission.BoseGases.abox N a, ∀ (i : Fin N)
      (p : EuclideanSpace ℝ (Fin 3)),
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖
          ≤ C / (1 + ‖p‖) ^ 3 := by
  classical
  -- the window vanishes off the box
  have hχsupp : ∀ z : E3, z ∉ A → χ z = 0 := by
    intro z hz
    by_contra h
    exact hz (hχA h)
  -- the two Fourier-decay constants (state `Ψ` and the constant state `1`)
  obtain ⟨C₁, hC₁0, hC₁⟩ := Work.SmallBoxTBWord.tBamp_decay (N := N) ha hχ hχs hΨ
  obtain ⟨C₂, hC₂0, hC₂⟩ := Work.SmallBoxTBWord.tBamp_decay (N := N) ha hχ hχs
    (Φ := fun _ : Submission.BoseGases.X N => (1 : ℝ)) contDiff_const
  -- the box `A` has finite measure
  have hfinA : (MeasureTheory.volume : Measure E3) A < ⊤ :=
    lt_of_le_of_lt (measure_mono hAc) (Submission.BoseGases.acube_lt_top a ha.le)
  -- the box mean is bounded by `B·|A|`
  have hint : ∀ (i : Fin N) (x : Submission.BoseGases.X N),
      x ∈ Submission.BoseGases.abox N a →
      |∫ z in A, Ψ (Function.update x i z)| ≤ B * (MeasureTheory.volume : Measure E3).real A := by
    intro i x hx
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := MeasureTheory.volume) (s := A) (f := fun z : E3 => Ψ (Function.update x i z)) (C := B)
      hfinA (fun z hz => by
        rw [Real.norm_eq_abs]
        exact hΨb _ (update_mem_abox_of_subset hAc hx hz i))
    rwa [Real.norm_eq_abs] at h
  -- the resulting uniform bound on the box mean `P_{B,i}Ψ` on the box
  set M : ℝ := |1 / volA| * (B * (MeasureTheory.volume : Measure E3).real A) with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have hreal : 0 ≤ (MeasureTheory.volume : Measure E3).real A := measureReal_nonneg
    positivity
  have hboxP_le : ∀ (i : Fin N) (x : Submission.BoseGases.X N),
      x ∈ Submission.BoseGases.abox N a →
      |Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i 0)| ≤ M := by
    intro i x hx
    have hEq : Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i 0)
        = (1 / volA) * ∫ z in A, Ψ (Function.update x i z) := by
      rw [Work.SmallBoxTBWord.boxP]
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      rw [Function.update_idem]
    rw [hEq, abs_mul, hMdef]
    exact mul_le_mul_of_nonneg_left (hint i x hx) (abs_nonneg _)
  refine ⟨C₁ + M * C₂, add_nonneg hC₁0 (mul_nonneg hM0 hC₂0), ?_⟩
  intro x hx i p
  rw [Work.BoseBox.tBamp_boxQInd_eq_sub (volA := volA) (A := A) (χ := χ) (N := N)
    Ψ i p x 0 hχsupp hχ.continuous hχs hΨ.continuous]
  have h1 : ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖ ≤ C₁ / (1 + ‖p‖) ^ 3 := hC₁ x hx i p
  have h2 : ‖Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X N => (1 : ℝ)) i x‖
      ≤ C₂ / (1 + ‖p‖) ^ 3 := hC₂ x hx i p
  have h3 : |Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i 0)| ≤ M := hboxP_le i x hx
  have h4 : |Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i 0)|
      * ‖Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X N => (1 : ℝ)) i x‖
      ≤ M * (C₂ / (1 + ‖p‖) ^ 3) :=
    mul_le_mul h3 h2 (norm_nonneg _) hM0
  calc ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x
        - ((Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i 0) : ℝ) : ℂ)
          * Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X N => (1 : ℝ)) i x‖
      ≤ ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖
        + ‖((Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i 0) : ℝ) : ℂ)
          * Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X N => (1 : ℝ)) i x‖ :=
        norm_sub_le _ _
    _ = ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖
        + |Work.SmallBoxTBWord.boxP volA A i Ψ (Function.update x i 0)|
          * ‖Work.SmallBoxTBWord.tBamp χ p (fun _ : Submission.BoseGases.X N => (1 : ℝ)) i x‖ := by
        rw [norm_mul, norm_ofReal_eq_abs]
    _ ≤ C₁ / (1 + ‖p‖) ^ 3 + M * (C₂ / (1 + ‖p‖) ^ 3) := add_le_add h1 h4
    _ = (C₁ + M * C₂) / (1 + ‖p‖) ^ 3 := by
        rw [← mul_div_assoc, ← add_div]

end Work.BoseFixB1B
