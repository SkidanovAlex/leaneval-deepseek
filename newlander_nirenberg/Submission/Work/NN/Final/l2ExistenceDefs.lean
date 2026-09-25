/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# `Work.NN.Final.l2Solvability_core` — the flat-model uniform `L²`-solvability of `∂̄_{Jstd+A}`

The target is the statement of `Work.NN.Final.L2SolvabilityHyp n α ρ` (also
`Work.NN.Final.l2Solvability_uniform`, `l2Solvability_local`, `l2SolvabilityCore2`): for every
smooth field `A` of endomorphisms of `ℂⁿ` which is `C^{0,α}`-small on the polydisc `pd n ρ 4`,
such that `J = JstdCn n + A` is an almost complex structure (`J² = -1`) with vanishing Nijenhuis
tensor on `pd n ρ 4` (the *integrability* hypothesis, in the form
`proj02 J (dOne (dbarCn J w)) = 0` for every smooth `w`), and for every smooth `J`-antilinear
`J`-closed `(0,1)`-form-valued `f` on `pd n ρ 4`, there is a `C¹` function `u` on the inner
polydisc `pd n ρ 2` solving `∂̄_J u = f` there, with the uniform `L²`-bound

  `‖u‖_{L²(pd n ρ 2)} ≤ C · Σ_j ‖f·e_j‖_{C^{0,α}(pd n ρ 4)}`

with `C, ε₀` independent of `A`.

## Structure of this file

* §1 (`eLpNorm_le_of_holderNorm_zero`): the **endgame** — on a bounded polydisc the `L²`-norm is
  controlled by the `C^{0,α}`-norm (in fact by `iterDerivNorm 0`, the sup-norm), with the volume
  factor.  This is the last step of *every* route to the target: a `C^{1,α}`-bound for the
  solution immediately gives the required `L²`-bound.
* §2 (`C1aSolvability`): the *solvability with a `C^{1,α}` bound* on the same regions as the
  target — the form in which the two analytic routes to this theorem (the flat Schauder /
  Calderón–Zygmund route and the weighted `L²` (Hörmander/Kohn) route) deliver the result.
* §3 (`l2SolvabilityHyp_of_C1a`): the **reduction** of the target to `C1aSolvability`, proved
  here (via §1); the only remaining gap of the file is therefore the single statement
  `c1aSolvability_holds` (§4).

See `Submission/Work/NN/Final/NOTES_l2Solvability_obstruction.md` §43/§44 for the analysis of the
two routes and of the region/`∂A` obstructions.
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_neg
import Submission.Work.NN.Core.eLpNorm_le_iterDerivNorm_zero
import Submission.Work.NN.Final.dbarSolverSmall_of_l2unif
import Submission.Work.NN.Final.interiorC0
import Submission.Work.NN.Final.holderNormCongr

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory
open Work.NN.Core
open Work.CR.Flat

namespace Work.NN.Final

/-! ## §1  The `L²`-endgame

On a bounded polydisc the `L²`-norm of a measurable function is controlled by its `C^{0,α}`-norm
(the sup-norm part suffices), with the constant `(volume)^{1/2} + 1`. -/

theorem eLpNorm_le_of_holderNorm_zero {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (u : Cn n → ℂ), AEStronglyMeasurable u (volume.restrict (pd n ρ 2)) →
        ∀ (M : ℝ≥0∞), holderNorm 0 α u (pd n ρ 2) ≤ M →
          eLpNorm u 2 (volume.restrict (pd n ρ 2)) ≤ ENNReal.ofReal K * M := by
  obtain ⟨V, hVpos, hV⟩ :=
    Work.NN.Core.eLpNorm_le_iterDerivNorm_zero (n := n)
      (ρ := fun j => 2 * ρ j) (fun j => by linarith [hρ j])
  refine ⟨V, hVpos, fun u hu M hM => ?_⟩
  have hpd : pd n ρ 2 = Work.CR.Flat.polydisc 0 (fun j => 2 * ρ j) := rfl
  rw [hpd] at hu hM ⊢
  refine le_trans (hV u hu) ?_
  calc ENNReal.ofReal V
        * Work.CR.Flat.iterDerivNorm 0 u (Work.CR.Flat.polydisc 0 (fun j => 2 * ρ j))
      ≤ ENNReal.ofReal V
          * Work.CR.Flat.holderNorm 0 α u (Work.CR.Flat.polydisc 0 (fun j => 2 * ρ j)) := by
        gcongr
        exact Work.CR.Flat.iterDerivNorm_le_holderNorm 0 α u _ le_rfl
    _ ≤ ENNReal.ofReal V * M := by gcongr

/-! ## §2  The `C^{1,α}`-solvability statement

The target's conclusion upgraded by the (A-uniform) `C^{1,α}` estimate on the same region
`pd n ρ 2`, against the same data norms on `pd n ρ 4`. -/

def C1aSolvability (n : ℕ) (α : ℝ) (ρ : Fin n → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (A : Cn n → Cn n →L[ℝ] Cn n),
      (∀ m : ℕ, ContDiff ℝ m A) →
      ∀ {ε : ℝ}, ε ≤ ε₀ →
      (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
          (fun z => A z (Pi.single i 1) j) (pd n ρ 4) ≤ ENNReal.ofReal ε) →
      (∀ z, z ∈ pd n ρ 4 → ∀ v : Cn n,
        (JstdCn n + A) z ((JstdCn n + A) z v) = -v) →
      (∀ u : Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
        ∀ z, z ∈ pd n ρ 4 → ∀ V W : Cn n,
          proj02 (JstdCn n + A)
            (fun z' => dOne (fun z'' => dbarCn (JstdCn n + A) u z'') z') z V W = 0) →
      ∀ f : Cn n → Cn n →L[ℝ] ℂ,
        (∀ m : ℕ, ContDiff ℝ m f) →
        (∀ z, z ∈ pd n ρ 4 → ∀ V : Cn n,
          f z ((JstdCn n + A) z V) = -Complex.I * f z V) →
        (∀ z, z ∈ pd n ρ 4 → ∀ V W : Cn n,
          proj02 (JstdCn n + A) (fun z' => dOne f z') z V W = 0) →
        ∃ u : Cn n → ℂ,
          ContDiffOn ℝ 1 u (pd n ρ 2) ∧
          (∀ z, z ∈ pd n ρ 2 → ∀ V : Cn n,
            dbarCn (JstdCn n + A) u z V = f z V) ∧
          Work.CR.Flat.holderNorm 1 α u (pd n ρ 2)
            ≤ ENNReal.ofReal C * ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
                (fun z => f z (Pi.single j 1)) (pd n ρ 4)

/-! ## §3  The reduction of the target to the `C^{1,α}`-solvability -/

theorem l2SolvabilityHyp_of_C1a {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ}
    (h : C1aSolvability n α ρ) : L2SolvabilityHyp n α ρ := by
  classical
  obtain ⟨C, hC, ε₀, hε₀, hsolv⟩ := h
  by_cases hρ : ∀ j, 0 < ρ j
  · obtain ⟨K, hK, hL2⟩ := eLpNorm_le_of_holderNorm_zero (n := n) (α := α) (ρ := ρ) hρ
    refine ⟨K * C, mul_pos hK hC, ε₀, hε₀, ?_⟩
    intro A hA ε hε hsmall hJ hint f hf hanti hclosed
    obtain ⟨u, hu1, hueq, hubd⟩ := hsolv A hA hε hsmall hJ hint f hf hanti hclosed
    refine ⟨u, hu1, hueq, ?_⟩
    have hsm : AEStronglyMeasurable u (volume.restrict (pd n ρ 2)) :=
      hu1.continuousOn.aestronglyMeasurable (isOpen_pd ρ 2).measurableSet
    set S : ℝ≥0∞ := ∑ j : Fin n, holderNorm 0 α (fun z => f z (Pi.single j 1)) (pd n ρ 4)
      with hS
    have hM : holderNorm 0 α u (pd n ρ 2) ≤ ENNReal.ofReal C * S :=
      le_trans (Work.CR.Flat.holderNorm_mono_k (Nat.zero_le 1) α u (pd n ρ 2)) hubd
    calc eLpNorm u 2 (volume.restrict (pd n ρ 2))
        ≤ ENNReal.ofReal K * (ENNReal.ofReal C * S) := hL2 u hsm _ hM
      _ = ENNReal.ofReal (K * C) * S := by
          rw [ENNReal.ofReal_mul (le_of_lt hK), mul_assoc]
  · -- some radius is nonpositive: the polydisc `pd n ρ 2` is empty and `u = 0` solves everything
    push Not at hρ
    obtain ⟨j, hj⟩ := hρ
    have hemp : pd n ρ 2 = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      have h1 := (mem_pd.mp hz) j
      have h2 : (0 : ℝ) ≤ ‖z j‖ := norm_nonneg _
      have h3 : 2 * ρ j ≤ 0 := by linarith
      linarith
    refine ⟨1, one_pos, 1, one_pos, ?_⟩
    intro A hA ε hε hsmall hJ hint f hf hanti hclosed
    refine ⟨fun _ => 0, contDiffOn_const, ?_, ?_⟩
    · intro z hz
      rw [hemp] at hz
      exact absurd hz (Set.notMem_empty z)
    · rw [hemp, MeasureTheory.Measure.restrict_empty]
      simp


/-! ## §3b  A weaker sufficient condition: a `C¹` solution with an `L²` bound on `pd n ρ (21/10)`

Every *constructive* route to the target produces a `C¹` solution of `∂̄_{Jstd+A}u = f` together with
an `L²`-bound for it on a polydisc **slightly larger** than `pd n ρ 2` (for instance the local flat
solver `Work.NN.Final.flatOneLin` solves the `∂̄₀`-equation on `pd n ρ (21/8) ⊇ pd n ρ (21/10)`, and
the fixed-point contraction gives the `L²`-bound there).  The interior a priori estimate
`Work.NN.Final.perturbed_C1a_L2_interior_C0` (proved, and `A`-uniform under the target's
`C^{0,α}`-smallness hypothesis) then upgrades such a solution to the `C^{1,α}`-bound of
`C1aSolvability`, using the *nested* polydiscs `pd n ρ 2 ⊂⊂ pd n ρ (21/10)`.

Hence the target follows from the existence statement `C1aExistence` below, which is the shape in
which the constructive routes deliver their output: **no `C^{1,α}`-estimate is required of them**,
only a `C¹` solution with an `L²`-bound on the slightly larger polydisc `pd n ρ (21/10)`.  This is
a genuine weakening of the obligation `C1aSolvability` (which asks for the `C^{1,α}`-bound on
`pd n ρ 2`): `C1aExistence` implies `C1aSolvability` by `c1aSolvability_of_existence` below. -/

/-- **The `C¹`-existence with an `L²`-bound on the larger polydisc `pd n ρ (21/10)`.**  The target's
quantifier structure with the conclusion weakened exactly as explained above. -/
def C1aExistence (n : ℕ) (α : ℝ) (ρ : Fin n → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (A : Cn n → Cn n →L[ℝ] Cn n),
      (∀ m : ℕ, ContDiff ℝ m A) →
      ∀ {ε : ℝ}, ε ≤ ε₀ →
      (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
          (fun z => A z (Pi.single i 1) j) (pd n ρ 4) ≤ ENNReal.ofReal ε) →
      (∀ z, z ∈ pd n ρ 4 → ∀ v : Cn n,
        (JstdCn n + A) z ((JstdCn n + A) z v) = -v) →
      (∀ u : Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
        ∀ z, z ∈ pd n ρ 4 → ∀ V W : Cn n,
          proj02 (JstdCn n + A)
            (fun z' => dOne (fun z'' => dbarCn (JstdCn n + A) u z'') z') z V W = 0) →
      ∀ f : Cn n → Cn n →L[ℝ] ℂ,
        (∀ m : ℕ, ContDiff ℝ m f) →
        (∀ z, z ∈ pd n ρ 4 → ∀ V : Cn n,
          f z ((JstdCn n + A) z V) = -Complex.I * f z V) →
        (∀ z, z ∈ pd n ρ 4 → ∀ V W : Cn n,
          proj02 (JstdCn n + A) (fun z' => dOne f z') z V W = 0) →
        ∃ u : Cn n → ℂ,
          ContDiffOn ℝ 1 u (pd n ρ (21 / 10)) ∧
          (∀ z, z ∈ pd n ρ (21 / 10) → ∀ V : Cn n,
            dbarCn (JstdCn n + A) u z V = f z V) ∧
          MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict (pd n ρ (21 / 10)))
            ≤ ENNReal.ofReal C * ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
                (fun z => f z (Pi.single j 1)) (pd n ρ 4)

/-- Auxiliary `ℝ≥0∞`-arithmetic of the two-region a priori estimate. -/
private lemma ennreal_arith_C1a {S D L : ℝ≥0∞} {C₁ C : ℝ} (hC₁ : 0 ≤ C₁) (hC : 0 ≤ C)
    (hD : D ≤ S) (hL : L ≤ ENNReal.ofReal C * S) :
    ENNReal.ofReal C₁ * (D + L) ≤ ENNReal.ofReal (C₁ * (1 + C)) * S := by
  have h1 : D + L ≤ ENNReal.ofReal (1 + C) * S := by
    calc D + L ≤ S + ENNReal.ofReal C * S := add_le_add hD hL
      _ = ENNReal.ofReal (1 + C) * S := by
          rw [ENNReal.ofReal_add zero_le_one hC, ENNReal.ofReal_one]
          ring
  calc ENNReal.ofReal C₁ * (D + L)
      ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal (1 + C) * S) := mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal (C₁ * (1 + C)) * S := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC₁]

/-- **`C1aExistence` implies `C1aSolvability`**: the a priori estimate
`perturbed_C1a_L2_interior_C0` upgrades a `C¹` solution with an `L²`-bound on the outer polydisc
`pd n ρ (21/8)` to the `C^{1,α}`-bound on the inner polydisc `pd n ρ 2`. -/
theorem c1aSolvability_of_existence {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (h : C1aExistence n α ρ) : C1aSolvability n α ρ := by
  classical
  obtain ⟨C, hC, ε₀, hε₀, hex⟩ := h
  have hσ0 : ∀ j, 0 < 2 * ρ j := fun j => by linarith [hρ j]
  have hρ'0 : ∀ j, 0 < (21 / 10) * ρ j := fun j => by linarith [hρ j]
  have hσρ : ∀ j, 2 * ρ j < (21 / 10) * ρ j := fun j => by linarith [hρ j]
  obtain ⟨ε₁, hε₁, C₁, hC₁, hEst⟩ :=
    perturbed_C1a_L2_interior_C0 (n := n) hn hα0 hα1 hσ0 hρ'0 hσρ
  refine ⟨C₁ * (1 + C), by positivity, min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro A hA ε hε hsmall hJ hint f hf hanti hclosed
  have hε₀' : ε ≤ ε₀ := le_trans hε (min_le_left _ _)
  have hε₁' : ε ≤ ε₁ := le_trans hε (min_le_right _ _)
  obtain ⟨u, hu1, hueq, huL2⟩ := hex A hA hε₀' hsmall hJ hint f hf hanti hclosed
  have hsub : pd n ρ 2 ⊆ pd n ρ (21 / 10) := pd_mono hρ (by norm_num)
  have hsub4 : pd n ρ (21 / 10) ⊆ pd n ρ 4 := pd_mono hρ (by norm_num)
  refine ⟨u, hu1.mono hsub, ?_, ?_⟩
  · intro z hz V
    exact hueq z (hsub hz) V
  · have hsmall' : ∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
        (fun z => A z (Pi.single i 1) j) (pd n ρ (21 / 10)) ≤ ENNReal.ofReal ε :=
      fun i j => le_trans (Work.CR.Flat.holderNorm_mono_set (isOpen_pd ρ 4) (isOpen_pd ρ (21 / 10))
        hsub4 0 α _) (hsmall i j)
    have hJ' : ∀ z, z ∈ pd n ρ (21 / 10) → ∀ v : Cn n,
        (JstdCn n + A) z ((JstdCn n + A) z v) = -v := fun z hz => hJ z (hsub4 hz)
    have hest := hEst (A := A) (ε := ε) hA hε₁' hsmall' hJ' u hu1
    set S : ℝ≥0∞ := ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
        (fun z => f z (Pi.single j 1)) (pd n ρ 4) with hS
    have hdata : (∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
          (fun z => dbarCn (JstdCn n + A) u z (Pi.single j 1)) (pd n ρ (21 / 10))) ≤ S := by
      rw [hS]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [holderNorm_congr_of_eqOn (fun z hz => hueq z hz (Pi.single j 1)) 0 α]
      exact Work.CR.Flat.holderNorm_mono_set (isOpen_pd ρ 4) (isOpen_pd ρ (21 / 10)) hsub4 0 α _
    have hL2 : MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict (pd n ρ (21 / 10)))
        ≤ ENNReal.ofReal C * S := huL2
    exact le_trans hest (ennreal_arith_C1a hC₁.le hC.le hdata hL2)

