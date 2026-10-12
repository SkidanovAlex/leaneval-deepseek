import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.continuous_bsOneBody
import Submission.Work.BSKinetic.bsOneBody_eq_dirichlet
import Submission.Work.BSKinetic.exists_fibre_bound
import Submission.Work.BoseKinLoc.Kinetic.fibre_lift_general
import Submission.Work.BoseKinLoc.Sector.fsT_bound_all
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.BsOneBodyBoxBound`

The anchored (`u = 0`) one-body big-box kinetic form `bsOneBody ℓ (fsKinCoeff c) 0`
of the slot-`i` fibre of a smooth `(m+1)`-particle state is **uniformly bounded on the box**
`abox m ℓ`:

    `∃ K ≥ 0, ∀ r ∈ abox m ℓ, bsOneBody ℓ [·−c]₊² 0 (genFibre i Φ r) ≤ K`.

## Proof

`ψ_r := genFibre i Φ r` is the slot-`i` fibre of `Φ` at the frozen configuration `r`.  Three
inputs, all in the corpus, give the bound:

* `Work.BSKinetic.Decomp.bsOneBody_eq_bsW_shift` — the transport of the moving box back to the
  origin: `bsOneBody ℓ F 0 ψ = (2π)⁻³ · bsW F (bsShift ℓ ψ 0)` with
  `bsShift ℓ ψ 0 = χ_ℓ·(ψ − ⨍ψ)`, whose support is the fixed box `acube ℓ`.
* `Work.BSKinetic.Decomp.bsW_le_const` — the weighted Plancherel bound
  `(2π)⁻³ bsW [·−c]₊² h ≤ 2c²·bsL2 h + 2·bsDir h`, so it suffices to bound the `L²` mass and the
  Dirichlet word of the shifted state.
* `Work.BSKinetic.Decomp.bsL2_le_of_bounded_support` / `bsDir_le_of_bounded_support` — a state
  supported in `acube ℓ`, bounded by `C` with derivatives bounded by `D`, satisfies
  `bsL2 h ≤ C²ℓ³` and `bsDir h ≤ 3D²ℓ³`.

The two sup-bounds on the (unshifted) fibre and its coordinate derivatives on the box come from
pure compactness, `Work.BSKinetic.exists_fibre_bound` (`Φ` is `C^∞`, `abox (m+1) ℓ` is compact
and `kcInsN m i (·, r)` maps `acube ℓ × abox m ℓ` into it).  The window `χ_ℓ` contributes the
uniform bounds `|χ_ℓ| ≤ chiSupAbs` (`Submission.BoseGases.chiScale_abs_le_sup`) and
`|∂_k χ_ℓ| ≤ √(G/ℓ²)` (`Work.BlockBound4.chiScale_grad_bound`), and the box mean of the fibre is
bounded by the on-box sup of the fibre (`abs_bsMean_zero_le` below).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixR

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- The box mean over the *anchored* box of a state that is bounded only **on the box** is
bounded by the same constant: `|(ℓ³)⁻¹∫_{acube ℓ}ψ| ≤ M` whenever `|ψ| ≤ M` on `acube ℓ`.

(`Work.BSKinetic.abs_bsMean_le` requires a *global* bound on `ψ`; the fibre
`z ↦ Φ (kcInsN m i (z,r))` of a merely smooth `Φ` is not globally bounded, so the on-box form is
the one needed here.) -/
lemma abs_bsMean_zero_le {ℓ M : ℝ} (hℓ : 0 < ℓ) {ψ : E3 → ℝ}
    (hψ : ∀ x ∈ Submission.BoseGases.acube ℓ, |ψ x| ≤ M) :
    |Work.BSKinetic.bsMean ℓ 0 ψ| ≤ M := by
  have hreal : (MeasureTheory.volume : MeasureTheory.Measure E3).real
      (Submission.BoseGases.acube ℓ) = ℓ ^ 3 := by
    rw [Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (pow_nonneg hℓ.le 3)]
  have hInt : |∫ z in Submission.BoseGases.acube ℓ, ψ z| ≤ M * ℓ ^ 3 := by
    rw [← Real.norm_eq_abs]
    have h1 := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := (MeasureTheory.volume : MeasureTheory.Measure E3))
      (s := Submission.BoseGases.acube ℓ) (f := ψ) (C := M) ?_ ?_
    · rwa [hreal] at h1
    · rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
      exact ENNReal.ofReal_lt_top
    · intro z hz
      simpa [Real.norm_eq_abs] using hψ z hz
  rw [Work.BSKinetic.bsMean]
  simp only [smul_zero, zero_add]
  rw [abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hℓ 3))]
  calc (ℓ ^ 3)⁻¹ * |∫ z in Submission.BoseGases.acube ℓ, ψ z|
      ≤ (ℓ ^ 3)⁻¹ * (M * ℓ ^ 3) :=
        mul_le_mul_of_nonneg_left hInt (inv_nonneg.mpr (pow_nonneg hℓ.le 3))
    _ = M := by field_simp

theorem BsOneBodyBoxBound {m : ℕ} {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 ≤ c)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin (m + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Submission.BoseGases.abox m ℓ,
      Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
        (Work.BoseKinLoc.Kinetic.genFibre i Φ r) ≤ K := by
  -- the compactness bounds on the fibre and its derivatives, uniform in `r ∈ abox m ℓ`
  obtain ⟨S, S1, hS0, hS10, hSb⟩ := Work.BSKinetic.exists_fibre_bound hℓ m hΦ
  -- the uniform bounds on the window and its coordinate derivatives
  obtain ⟨G, hG0, hG⟩ := Work.BlockBound4.chiScale_grad_bound
  -- the constants
  set X : ℝ := Submission.BoseGases.chiSupAbs with hXdef
  have hX0 : 0 ≤ X := by rw [hXdef]; exact Submission.BoseGases.chiSupAbs_nonneg
  set Gd : ℝ := Real.sqrt (G / ℓ ^ 2) with hGddef
  have hGd0 : 0 ≤ Gd := by rw [hGddef]; exact Real.sqrt_nonneg _
  set C : ℝ := X * (2 * S) with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; exact mul_nonneg hX0 (by linarith)
  set D : ℝ := X * S1 + (2 * S) * Gd with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    exact add_nonneg (mul_nonneg hX0 hS10) (mul_nonneg (by linarith) hGd0)
  set K₀ : ℝ := max (C ^ 2 * ℓ ^ 3) (3 * (D ^ 2 * ℓ ^ 3)) with hK0def
  have hK00 : 0 ≤ K₀ := by
    rw [hK0def]
    exact le_trans (mul_nonneg (sq_nonneg C) (pow_nonneg hℓ.le 3)) (le_max_left _ _)
  have hK : 0 ≤ 2 * c ^ 2 * K₀ + 2 * K₀ := by
    have h1 : 0 ≤ 2 * c ^ 2 * K₀ := mul_nonneg (by positivity) hK00
    have h2 : 0 ≤ 2 * K₀ := by linarith
    linarith
  refine ⟨2 * c ^ 2 * K₀ + 2 * K₀, hK, ?_⟩
  intro r hr
  obtain ⟨hSbd, hSder⟩ := hSb i r hr
  -- the slot-`i` fibre
  set ψ : E3 → ℝ := Work.BoseKinLoc.Kinetic.genFibre i Φ r with hψdef
  have hψeq : ∀ z : E3, ψ z = Φ (Submission.BoseGases.kcInsN m i (z, r)) := by
    intro z
    rw [hψdef]
    rfl
  have hψfd : fderiv ℝ ψ
      = fderiv ℝ (fun w : E3 => Φ (Submission.BoseGases.kcInsN m i (w, r))) := by
    rw [hψdef]
    rfl
  have hψd : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    rw [hψdef]
    exact Work.BoseKinLoc.Kinetic.genFibre_contDiff hΦ i r
  have hψbd : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ z| ≤ S := by
    intro z hz
    rw [hψeq z]
    exact hSbd z hz
  have hψder : ∀ z ∈ Submission.BoseGases.acube ℓ, ∀ k : Fin 3,
      |(fderiv ℝ ψ z) (Submission.BoseGases.kcStdBasis k)| ≤ S1 := by
    intro z hz k
    rw [hψfd]
    exact hSder z hz k
  have hmean : |Work.BSKinetic.bsMean ℓ 0 ψ| ≤ S := abs_bsMean_zero_le hℓ hψbd
  have hqbd : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |ψ z - Work.BSKinetic.bsMean ℓ 0 ψ| ≤ 2 * S := by
    intro z hz
    calc |ψ z - Work.BSKinetic.bsMean ℓ 0 ψ|
        ≤ |ψ z| + |Work.BSKinetic.bsMean ℓ 0 ψ| := abs_sub _ _
      _ ≤ S + S := add_le_add (hψbd z hz) hmean
      _ = 2 * S := by ring
  -- the shifted (origin-anchored) windowed mean-free state
  set hh : E3 → ℝ := Work.BSKinetic.Decomp.bsShift ℓ ψ 0 with hhdef
  have hhform : ∀ z : E3,
      hh z = Submission.BoseGases.chiScale ℓ z * (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) := by
    intro z
    rw [hhdef]
    simp only [Work.BSKinetic.Decomp.bsShift_apply, smul_zero, add_zero]
  have hhzero : ∀ z ∉ Submission.BoseGases.acube ℓ, hh z = 0 := by
    intro z hz
    rw [hhform z, Work.UBBInputs9.B.chiScale_eq_zero_of_not_mem_acube hℓ hz, zero_mul]
  have hhder0 : ∀ z ∉ Submission.BoseGases.acube ℓ, fderiv ℝ hh z = 0 := by
    intro z hz
    have hopen : IsOpen (Submission.BoseGases.acube ℓ)ᶜ :=
      (Submission.BoseGases.acube_isClosed ℓ).isOpen_compl
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen z hz
    have hev : hh =ᶠ[nhds z] Function.const E3 (0 : ℝ) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      exact ⟨Metric.ball z ε, Metric.ball_mem_nhds z hε, fun y hy => hhzero y (hsub hy)⟩
    have h1 : fderiv ℝ hh z = fderiv ℝ (Function.const E3 (0 : ℝ)) z :=
      Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hev
    have h0 : fderiv ℝ (Function.const E3 (0 : ℝ)) z = 0 := by
      rw [fderiv_const]
      rfl
    exact h1.trans h0
  -- the `L²` bound on the shifted state
  have hhbd : ∀ z : E3, |hh z| ≤ C := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · have hχb : |Submission.BoseGases.chiScale ℓ z| ≤ X := by
        rw [hXdef]
        exact Submission.BoseGases.chiScale_abs_le_sup ℓ z
      calc |hh z|
          = |Submission.BoseGases.chiScale ℓ z|
              * |ψ z - Work.BSKinetic.bsMean ℓ 0 ψ| := by rw [hhform z, abs_mul]
        _ ≤ X * (2 * S) := mul_le_mul hχb (hqbd z hz) (abs_nonneg _) hX0
        _ = C := by rw [hCdef]
    · rw [hhzero z hz, abs_zero]
      exact hC0
  -- the `H¹` bound on the shifted state
  have hhder : ∀ (k : Fin 3) (z : E3),
      |(fderiv ℝ hh z) (Submission.BoseGases.kcStdBasis k)| ≤ D := by
    intro k z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · have hleib := Work.BSKinetic.Decomp.Aux.fderiv_bsShift_apply (ℓ := ℓ) (ne_of_gt hℓ) hψd
        (0 : E3) z (Submission.BoseGases.kcStdBasis k)
      have hgoal : (fderiv ℝ hh z) (Submission.BoseGases.kcStdBasis k)
          = Submission.BoseGases.chiScale ℓ z * (fderiv ℝ ψ z) (Submission.BoseGases.kcStdBasis k)
            + (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ)
              * (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z)
                  (Submission.BoseGases.kcStdBasis k) := by
        rw [show fderiv ℝ hh z = fderiv ℝ (Work.BSKinetic.Decomp.bsShift ℓ ψ 0) z from by
          rw [hhdef]]
        rw [hleib]
        simp only [smul_zero, add_zero]
      rw [hgoal]
      have hχb : |Submission.BoseGases.chiScale ℓ z| ≤ X := by
        rw [hXdef]
        exact Submission.BoseGases.chiScale_abs_le_sup ℓ z
      have hdψ : |(fderiv ℝ ψ z) (Submission.BoseGases.kcStdBasis k)| ≤ S1 := hψder z hz k
      have hdχ : |(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z)
          (Submission.BoseGases.kcStdBasis k)| ≤ Gd := by
        have hsum : ((fderiv ℝ (Submission.BoseGases.chiScale ℓ) z)
            (Submission.BoseGases.kcStdBasis k)) ^ 2 ≤ G / ℓ ^ 2 :=
          le_trans (Finset.single_le_sum
            (f := fun j : Fin 3 =>
              ((fderiv ℝ (Submission.BoseGases.chiScale ℓ) z)
                (Submission.BoseGases.kcStdBasis j)) ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ k)) (hG ℓ hℓ z)
        have h2 : ((fderiv ℝ (Submission.BoseGases.chiScale ℓ) z)
            (Submission.BoseGases.kcStdBasis k)) ^ 2 ≤ Gd ^ 2 := by
          rw [hGddef, Real.sq_sqrt (div_nonneg hG0 (pow_nonneg hℓ.le 2))]
          exact hsum
        have h3 := sq_le_sq.mp h2
        rwa [abs_of_nonneg hGd0] at h3
      calc |Submission.BoseGases.chiScale ℓ z * (fderiv ℝ ψ z) (Submission.BoseGases.kcStdBasis k)
            + (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ)
              * (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z)
                  (Submission.BoseGases.kcStdBasis k)|
          ≤ |Submission.BoseGases.chiScale ℓ z
                * (fderiv ℝ ψ z) (Submission.BoseGases.kcStdBasis k)|
            + |(ψ z - Work.BSKinetic.bsMean ℓ 0 ψ)
                * (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z)
                    (Submission.BoseGases.kcStdBasis k)| := abs_add_le _ _
        _ = |Submission.BoseGases.chiScale ℓ z|
              * |(fderiv ℝ ψ z) (Submission.BoseGases.kcStdBasis k)|
            + |ψ z - Work.BSKinetic.bsMean ℓ 0 ψ|
              * |(fderiv ℝ (Submission.BoseGases.chiScale ℓ) z)
                  (Submission.BoseGases.kcStdBasis k)| := by rw [abs_mul, abs_mul]
        _ ≤ D := by
            rw [hDdef]
            exact add_le_add (mul_le_mul hχb hdψ (abs_nonneg _) hX0)
              (mul_le_mul (hqbd z hz) hdχ (abs_nonneg _) (by linarith))
    · rw [hhder0 z hz]
      simpa using hD0
  have hL2 : Work.BSKinetic.Decomp.bsL2 hh ≤ C ^ 2 * ℓ ^ 3 :=
    Work.BSKinetic.Decomp.bsL2_le_of_bounded_support hℓ hC0 hhbd hhzero
  have hDir : Work.BSKinetic.Decomp.bsDir hh ≤ 3 * (D ^ 2 * ℓ ^ 3) :=
    Work.BSKinetic.Decomp.bsDir_le_of_bounded_support hℓ hD0 hhder hhzero
  have hW : Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) hh
      ≤ (2 * Real.pi) ^ 3 * (2 * c ^ 2 * K₀ + 2 * K₀) := by
    refine Work.BSKinetic.Decomp.bsW_le_const (c := c) (K := K₀) ?_ ?_ ?_ ?_
    · rw [hhdef]
      exact Work.BSKinetic.Decomp.contDiff_bsShift hℓ hψd 0
    · rw [hhdef]
      exact Work.BSKinetic.Decomp.hasCompactSupport_bsShift (ne_of_gt hℓ) 0
    · rw [hK0def]
      exact le_trans hL2 (le_max_left _ _)
    · rw [hK0def]
      exact le_trans hDir (le_max_right _ _)
  rw [Work.BSKinetic.Decomp.bsOneBody_eq_bsW_shift hℓ (Submission.BoseGases.fsKinCoeff c) 0 ψ]
  rw [show Work.BSKinetic.Decomp.bsShift ℓ ψ 0 = hh from hhdef.symm]
  calc ((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) hh
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((2 * Real.pi) ^ 3 * (2 * c ^ 2 * K₀ + 2 * K₀)) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
    _ = 2 * c ^ 2 * K₀ + 2 * K₀ := by
        rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

end Work.BoseFixR
