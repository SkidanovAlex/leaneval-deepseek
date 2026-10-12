import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.KinPSuperadd.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `KinPSuperadd` — the exact cross-group deficiency of the `modeP` word

The word `modePGen s g N Ψ = (s³)⁻¹ ∫_{abox N s} (boxOp s 1 g Ψ)²` is a
**square of a sum** over the particle slots,
`boxOp s 1 g Ψ x = Σ_i A_i(x)` with `A_i(x) = ∫_{acube s} g z Ψ(x_{i↦z})`, and
therefore does **not** satisfy the block decomposition `SlotSplit`
(`Work.KinPSuperadd.not_slotSplit_modePGen`).  This module computes the
deficiency *exactly*, for an arbitrary smooth state `Φ`:

    modePGen s g (N₁+N₂) Φ − (∫_{abox N₂ s} modePGen s g N₁ (slice_w Φ)
                              + ∫_{abox N₁ s} modePGen s g N₂ (slice'_u Φ))
      = 2 (s³)⁻¹ ∫_{abox (N₁+N₂) s}
          (Σ_{i∈G₁} A_i(x)) · (Σ_{j∈G₂} A_j(x)) ,

i.e. exactly the missing cross-group term of the square of the sum.  (At the
constant state `Φ ≡ c` the right-hand side reduces to the value computed in
`Work.KinPSuperadd.modePGen_const_deficiency`.)

## Proof skeleton

Write `A(x)` for the first-block amplitude sum `Σ_{i:Fin N₁} ∫ g z Φ(x_{i↦z})`
and `B(x)` for the second-block one.  Then

* `boxOp_split` — `boxOp s 1 g Φ x = A x + B x` (the sum over `Fin (N₁+N₂)` of
  the slot amplitudes splits along the two block embeddings `Fin.castAdd` /
  `Fin.natAdd`);
* `fstAmp_merge`, `sndAmp_merge` — along the block concatenation `mergeBlock`,
  `A (merge(u,w))` is the `boxOp` of the `w`-slice at `u` (and symmetrically),
  which is what makes the two slice integrals in the statement equal to
  `(s³)⁻¹ ∫ A²` and `(s³)⁻¹ ∫ B²` (`integral_modePGen_fst`,
  `integral_modePGen_snd`, via the measure-preserving block split Fubini
  `Submission.BoseGases.aboxFubini{,_swapped}`);
* the two amplitude sums are continuous in `x` for continuous `g, Φ`
  (`continuous_fstAmp`, `continuous_sndAmp`), hence square-integrable on the
  (compact) box — this is what legitimates the splitting of the integrated
  squares;
* `(A+B)² − A² − B² = 2AB` pointwise, and `∫` is additive.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.KinPSuperadd

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1  The two block amplitude sums -/

/-- The **first-block amplitude sum** of the mode operator `boxOp s 1 g Φ` at
the configuration `x : X (N₁+N₂)`: the sum of the slot amplitudes of the slots
belonging to the first block. -/
noncomputable def fstAmp (s : ℝ) (g : ℝ³ → ℝ) (N1 N2 : ℕ) (Φ : X (N1+N2) → ℝ) :
    X (N1+N2) → ℝ :=
  fun x => ∑ i : Fin N1, ∫ z in acube s, g z * Φ (Function.update x (Fin.castAdd N2 i) z)

/-- The **second-block amplitude sum** of `boxOp s 1 g Φ` at `x`. -/
noncomputable def sndAmp (s : ℝ) (g : ℝ³ → ℝ) (N1 N2 : ℕ) (Φ : X (N1+N2) → ℝ) :
    X (N1+N2) → ℝ :=
  fun x => ∑ j : Fin N2, ∫ z in acube s, g z * Φ (Function.update x (Fin.natAdd N1 j) z)

/-! ## 2  The block concatenation against a slot update -/

/-- Two configurations of `X (N₁+N₂)` with equal first and last blocks agree. -/
lemma eq_of_first_last {N1 N2 : ℕ} {x y : X (N1+N2)}
    (h1 : firstBlock N1 N2 x = firstBlock N1 N2 y)
    (h2 : lastBlock N1 N2 x = lastBlock N1 N2 y) : x = y := by
  rw [← mergeBlock_eq N1 N2 x, ← mergeBlock_eq N1 N2 y, h1, h2]

/-- Updating a first-block slot and then concatenating is the same as
concatenating and then updating the corresponding overall slot. -/
lemma mergeBlock_update_fst {N1 N2 : ℕ} (u : X N1) (w : X N2) (i : Fin N1) (z : ℝ³) :
    mergeBlock N1 N2 (Function.update u i z, w)
      = Function.update (mergeBlock N1 N2 (u, w)) (Fin.castAdd N2 i) z := by
  refine eq_of_first_last ?_ ?_
  · rw [mergeBlock_first, firstBlock_update, mergeBlock_first]
  · rw [mergeBlock_last, lastBlock_update_first, mergeBlock_last]

/-- Updating a second-block slot and then concatenating is the same as
concatenating and then updating the corresponding overall slot. -/
lemma mergeBlock_update_snd {N1 N2 : ℕ} (u : X N1) (w : X N2) (j : Fin N2) (z : ℝ³) :
    mergeBlock N1 N2 (u, Function.update w j z)
      = Function.update (mergeBlock N1 N2 (u, w)) (Fin.natAdd N1 j) z := by
  refine eq_of_first_last ?_ ?_
  · rw [mergeBlock_first, firstBlock_update_last, mergeBlock_first]
  · rw [mergeBlock_last, lastBlock_update_last, mergeBlock_last]

/-! ## 3  Splitting the `boxOp` sum over the two blocks -/

/-- **The pointwise block split of the mode operator**: the slot sum of
`boxOp s 1 g Φ` splits into the first-block and the second-block amplitude
sums. -/
lemma boxOp_split (s : ℝ) (g : ℝ³ → ℝ) (N1 N2 : ℕ) (Φ : X (N1+N2) → ℝ) (x : X (N1+N2)) :
    boxOp s (fun _ => (1 : ℝ)) g Φ x = fstAmp s g N1 N2 Φ x + sndAmp s g N1 N2 Φ x := by
  simp only [boxOp, one_mul, fstAmp, sndAmp]
  rw [show (∑ i : Fin (N1+N2), ∫ z in acube s, g z * Φ (Function.update x i z))
      = ∑ k : Fin N1 ⊕ Fin N2, (fun i : Fin (N1+N2) => ∫ z in acube s,
          g z * Φ (Function.update x i z)) (finSumFinEquiv k) from
    Fintype.sum_equiv finSumFinEquiv.symm _ _ (fun i => by simp)]
  rw [Fintype.sum_sum_type]
  congr 1

/-! ## 4  The amplitude sums along the block concatenation -/

/-- Along `mergeBlock`, the first-block amplitude sum at `merge(u,w)` is the
`boxOp` of the `w`-slice at `u`. -/
lemma fstAmp_merge (s : ℝ) (g : ℝ³ → ℝ) (N1 N2 : ℕ) (Φ : X (N1+N2) → ℝ)
    (u : X N1) (w : X N2) :
    fstAmp s g N1 N2 Φ (mergeBlock N1 N2 (u, w))
      = boxOp s (fun _ => (1 : ℝ)) g (fun u' => Φ (mergeBlock N1 N2 (u', w))) u := by
  simp only [fstAmp, boxOp, one_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [mergeBlock_update_fst])

/-- Along `mergeBlock`, the second-block amplitude sum at `merge(u,w)` is the
`boxOp` of the `u`-slice at `w`. -/
lemma sndAmp_merge (s : ℝ) (g : ℝ³ → ℝ) (N1 N2 : ℕ) (Φ : X (N1+N2) → ℝ)
    (u : X N1) (w : X N2) :
    sndAmp s g N1 N2 Φ (mergeBlock N1 N2 (u, w))
      = boxOp s (fun _ => (1 : ℝ)) g (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w := by
  simp only [sndAmp, boxOp, one_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [mergeBlock_update_snd])

/-! ## 5  Continuity and integrability of the amplitude sums -/

/-- The first-block amplitude sum is continuous in the configuration. -/
lemma continuous_fstAmp {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) {g : ℝ³ → ℝ} (hg : Continuous g)
    {Φ : X (N1+N2) → ℝ} (hΦ : Continuous Φ) : Continuous (fstAmp s g N1 N2 Φ) := by
  refine continuous_finsetSum _ (fun i _ => ?_)
  refine continuous_iff_continuousAt.mpr (fun x => ?_)
  exact (continuousOn_paramIntegral (s := s) hs (Fin.castAdd N2 i) hg hΦ x).continuousAt
    (Metric.closedBall_mem_nhds x one_pos)

/-- The second-block amplitude sum is continuous in the configuration. -/
lemma continuous_sndAmp {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) {g : ℝ³ → ℝ} (hg : Continuous g)
    {Φ : X (N1+N2) → ℝ} (hΦ : Continuous Φ) : Continuous (sndAmp s g N1 N2 Φ) := by
  refine continuous_finsetSum _ (fun j _ => ?_)
  refine continuous_iff_continuousAt.mpr (fun x => ?_)
  exact (continuousOn_paramIntegral (s := s) hs (Fin.natAdd N1 j) hg hΦ x).continuousAt
    (Metric.closedBall_mem_nhds x one_pos)

/-- The square of the first-block amplitude sum is integrable on the `(N₁+N₂)`-box. -/
lemma integrableOn_fstAmp_sq {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) {g : ℝ³ → ℝ}
    (hg : Continuous g) {Φ : X (N1+N2) → ℝ} (hΦ : Continuous Φ) :
    IntegrableOn (fun x => (fstAmp s g N1 N2 Φ x) ^ 2) (abox (N1+N2) s) volume :=
  ContinuousOn.integrableOn_compact (abox_compact (N1+N2) hs)
    ((continuous_fstAmp hs hg hΦ).pow 2).continuousOn

/-- The square of the second-block amplitude sum is integrable on the `(N₁+N₂)`-box. -/
lemma integrableOn_sndAmp_sq {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) {g : ℝ³ → ℝ}
    (hg : Continuous g) {Φ : X (N1+N2) → ℝ} (hΦ : Continuous Φ) :
    IntegrableOn (fun x => (sndAmp s g N1 N2 Φ x) ^ 2) (abox (N1+N2) s) volume :=
  ContinuousOn.integrableOn_compact (abox_compact (N1+N2) hs)
    ((continuous_sndAmp hs hg hΦ).pow 2).continuousOn

/-! ## 6  The two slice integrals -/

/-- **The first slice integral**: the `w`-integral of the `N₁`-particle word on
the `w`-slice is `(s³)⁻¹` times the full-box integral of `(fstAmp)²`. -/
lemma integral_modePGen_fst {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) {g : ℝ³ → ℝ}
    (hg : Continuous g) {Φ : X (N1+N2) → ℝ} (hΦ : Continuous Φ) :
    (∫ w in abox N2 s, modePGen s g N1 (fun u => Φ (mergeBlock N1 N2 (u, w))))
      = (s ^ 3)⁻¹ * ∫ x in abox (N1+N2) s, (fstAmp s g N1 N2 Φ x) ^ 2 := by
  rw [← aboxFubini_swapped (N1 := N1) (N2 := N2) s
    (fun x => (fstAmp s g N1 N2 Φ x) ^ 2) (integrableOn_fstAmp_sq hs hg hΦ)]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [modePGen]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => by simp only [fstAmp_merge])

/-- **The second slice integral**: the `u`-integral of the `N₂`-particle word on
the `u`-slice is `(s³)⁻¹` times the full-box integral of `(sndAmp)²`. -/
lemma integral_modePGen_snd {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) {g : ℝ³ → ℝ}
    (hg : Continuous g) {Φ : X (N1+N2) → ℝ} (hΦ : Continuous Φ) :
    (∫ u in abox N1 s, modePGen s g N2 (fun w => Φ (mergeBlock N1 N2 (u, w))))
      = (s ^ 3)⁻¹ * ∫ x in abox (N1+N2) s, (sndAmp s g N1 N2 Φ x) ^ 2 := by
  rw [← aboxFubini (N1 := N1) (N2 := N2) s
    (fun x => (sndAmp s g N1 N2 Φ x) ^ 2) (integrableOn_sndAmp_sq hs hg hΦ)]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [modePGen]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun w => by simp only [sndAmp_merge])

/-! ## 7  The main theorem -/

theorem modePGen_block_deficiency {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (hg : Continuous g)
    (Φ : Submission.BoseGases.X (N1 + N2) → ℝ) (hΦ : ContDiff ℝ ∞ Φ) :
    @Work.KinPSuperadd.modePGen s g (N1 + N2) Φ
      - ((∫ w in Submission.BoseGases.abox N2 s,
            @Work.KinPSuperadd.modePGen s g N1
              (fun u => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w))))
         + (∫ u in Submission.BoseGases.abox N1 s,
            @Work.KinPSuperadd.modePGen s g N2
              (fun w => Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w)))))
      = 2 * (s ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (N1 + N2) s,
          ((∑ i : Fin N1, ∫ z in Submission.BoseGases.acube s, g z *
              Φ (Function.update x (Fin.castAdd N2 i) z)) *
           (∑ j : Fin N2, ∫ z in Submission.BoseGases.acube s, g z *
              Φ (Function.update x (Fin.natAdd N1 j) z))) := by
  have hcΦ : Continuous Φ := hΦ.continuous
  have hIab : Integrable (fun x : X (N1+N2) =>
      (fstAmp s g N1 N2 Φ x + sndAmp s g N1 N2 Φ x)^2)
      (volume.restrict (abox (N1+N2) s)) :=
    ContinuousOn.integrableOn_compact (abox_compact (N1+N2) hs)
      (((continuous_fstAmp hs hg hcΦ).add (continuous_sndAmp hs hg hcΦ)).pow 2).continuousOn
  have hIA : Integrable (fun x : X (N1+N2) => (fstAmp s g N1 N2 Φ x)^2)
      (volume.restrict (abox (N1+N2) s)) := integrableOn_fstAmp_sq hs hg hcΦ
  have hIB : Integrable (fun x : X (N1+N2) => (sndAmp s g N1 N2 Φ x)^2)
      (volume.restrict (abox (N1+N2) s)) := integrableOn_sndAmp_sq hs hg hcΦ
  have hIsub : Integrable (fun x : X (N1+N2) =>
      (fstAmp s g N1 N2 Φ x + sndAmp s g N1 N2 Φ x)^2 - (fstAmp s g N1 N2 Φ x)^2)
      (volume.restrict (abox (N1+N2) s)) :=
    ContinuousOn.integrableOn_compact (abox_compact (N1+N2) hs)
      ((((continuous_fstAmp hs hg hcΦ).add (continuous_sndAmp hs hg hcΦ)).pow 2).sub
        ((continuous_fstAmp hs hg hcΦ).pow 2)).continuousOn
  have hmode : modePGen s g (N1+N2) Φ
      = (s^3)⁻¹ * ∫ x in abox (N1+N2) s,
          (fstAmp s g N1 N2 Φ x + sndAmp s g N1 N2 Φ x)^2 := by
    simp only [modePGen]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [boxOp_split])
  have hJ1 := integral_modePGen_fst (N1 := N1) (N2 := N2) hs hg hcΦ
  have hJ2 := integral_modePGen_snd (N1 := N1) (N2 := N2) hs hg hcΦ
  have hsub1 : (∫ x in abox (N1+N2) s, (fstAmp s g N1 N2 Φ x + sndAmp s g N1 N2 Φ x)^2)
      - (∫ x in abox (N1+N2) s, (fstAmp s g N1 N2 Φ x)^2)
      = ∫ x in abox (N1+N2) s,
          ((fstAmp s g N1 N2 Φ x + sndAmp s g N1 N2 Φ x)^2 - (fstAmp s g N1 N2 Φ x)^2) :=
    (integral_sub hIab hIA).symm
  have hsub2 : (∫ x in abox (N1+N2) s,
        ((fstAmp s g N1 N2 Φ x + sndAmp s g N1 N2 Φ x)^2 - (fstAmp s g N1 N2 Φ x)^2))
      - (∫ x in abox (N1+N2) s, (sndAmp s g N1 N2 Φ x)^2)
      = ∫ x in abox (N1+N2) s,
          (((fstAmp s g N1 N2 Φ x + sndAmp s g N1 N2 Φ x)^2 - (fstAmp s g N1 N2 Φ x)^2)
            - (sndAmp s g N1 N2 Φ x)^2) :=
    (integral_sub hIsub hIB).symm
  rw [hmode, hJ1, hJ2]
  calc (s ^ 3)⁻¹ * (∫ x in abox (N1+N2) s, (fstAmp s g N1 N2 Φ x + sndAmp s g N1 N2 Φ x)^2)
        - ((s ^ 3)⁻¹ * (∫ x in abox (N1+N2) s, (fstAmp s g N1 N2 Φ x)^2)
           + (s ^ 3)⁻¹ * (∫ x in abox (N1+N2) s, (sndAmp s g N1 N2 Φ x)^2))
      = (s ^ 3)⁻¹ * (((∫ x in abox (N1+N2) s, (fstAmp s g N1 N2 Φ x + sndAmp s g N1 N2 Φ x)^2)
           - (∫ x in abox (N1+N2) s, (fstAmp s g N1 N2 Φ x)^2))
           - (∫ x in abox (N1+N2) s, (sndAmp s g N1 N2 Φ x)^2)) := by ring
    _ = (s ^ 3)⁻¹ * ((∫ x in abox (N1+N2) s,
            ((fstAmp s g N1 N2 Φ x + sndAmp s g N1 N2 Φ x)^2 - (fstAmp s g N1 N2 Φ x)^2))
           - (∫ x in abox (N1+N2) s, (sndAmp s g N1 N2 Φ x)^2)) := by rw [hsub1]
    _ = (s ^ 3)⁻¹ * (∫ x in abox (N1+N2) s,
            (((fstAmp s g N1 N2 Φ x + sndAmp s g N1 N2 Φ x)^2 - (fstAmp s g N1 N2 Φ x)^2)
              - (sndAmp s g N1 N2 Φ x)^2)) := by rw [hsub2]
    _ = (s ^ 3)⁻¹ * (∫ x in abox (N1+N2) s,
            2 * (fstAmp s g N1 N2 Φ x * sndAmp s g N1 N2 Φ x)) := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = (s ^ 3)⁻¹ * (2 * ∫ x in abox (N1+N2) s,
            fstAmp s g N1 N2 Φ x * sndAmp s g N1 N2 Φ x) := by
          rw [integral_const_mul]
    _ = 2 * (s ^ 3)⁻¹ * ∫ x in abox (N1+N2) s,
            fstAmp s g N1 N2 Φ x * sndAmp s g N1 N2 Φ x := by ring

end Work.KinPSuperadd
