import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.StrongEps.BumpDefs
import Submission.Work.FTS.StrongEps.EpsSqTools.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The refutation of the `EpsMem` conjunct of `EpsSq_sub_smul_bump`

The obstruction is purely measure-theoretic.  `EpsMem α f` is (by definition)
`IntegrableOn (fun p ↦ (f p₁ p₂ · epsW α p₁ p₂)²) (Iz ×ˢ Iθ)`, and Mathlib's `Integrable` **by
definition** contains `AEStronglyMeasurable`.  So any datum whose *weighted square* is a fixed
measurable function `G > 0` on a box `B` but whose value distribution is that of an arbitrary
subset `E ⊆ B`, inherits the a.e. measurability of the indicator `1_E` from `EpsMem` — and a
non-`NullMeasurableSet` `E` therefore produces a datum with `EpsMem α h` but `¬ EpsMem α (h - 1·bump)`.

The datum used below is the `±bump` sign flip
`h z θ = bump z θ · (1 - 2·1_E(z,θ))`, whose weighted square is literally `(bump · epsW 1)²`
(so `EpsMem 1 h` follows from `EpsMem 1 bump`), while
`(h - 1·bump) · epsW 1 = -2·bump·1_E·epsW 1`, i.e. its weighted square is
`4 · (bump · epsW 1)² · 1_E`, which is a.e. strongly measurable only if `E` is null measurable.
-/

/-- The box `(5/8, 7/8) × (π/4, 3π/8)` of the statement: inside the positive box of `bump`, and
inside the quadrant. -/
private def refBox : Set (ℝ × ℝ) :=
  Set.Ioo (5 / 8) (7 / 8) ×ˢ Set.Ioo (Real.pi / 4) (3 * Real.pi / 8)

private theorem measurableSet_refBox : MeasurableSet refBox :=
  measurableSet_Ioo.prod measurableSet_Ioo

private theorem refBox_subset_quad : refBox ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
  rintro ⟨z, θ⟩ hp
  rw [refBox, Set.mem_prod] at hp
  refine ⟨?_, ?_⟩
  · rw [Work.Spaces.Iz, Set.mem_Ici]; linarith [hp.1.1]
  · rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨by linarith [hp.2.1, Real.pi_pos], by linarith [hp.2.2, Real.pi_pos]⟩

/-- The weight `epsW 1` is positive on the open quadrant. -/
private theorem epsW_one_pos {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ)
    (hθ2 : θ < Real.pi / 2) : 0 < epsW 1 z θ := by
  rw [epsW, Work.Spaces.w]
  refine div_pos (div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)) ?_
  exact Real.rpow_pos_of_pos
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])) _

/-- On `refBox` the weighted bump `bump · epsW 1` does not vanish, so its square is positive
there.  This is the only place where the geometry of `B` enters the refutation. -/
private theorem bump_epsW_one_sq_pos_of_mem_refBox {p : ℝ × ℝ} (hp : p ∈ refBox) :
    0 < (bump p.1 p.2 * epsW 1 p.1 p.2) ^ 2 := by
  rw [refBox, Set.mem_prod] at hp
  have hbump : 0 < bump p.1 p.2 :=
    bump_pos_iff.mpr ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2⟩
  have hw : 0 < epsW 1 p.1 p.2 :=
    epsW_one_pos (by linarith [hp.1.1]) (by linarith [hp.2.1, Real.pi_pos])
      (by linarith [hp.2.2, Real.pi_pos])
  exact pow_pos (mul_pos hbump hw) 2

/-- **The measure-theoretic transfer.**  A positive multiple of `G · 1_E` which is a.e. strongly
measurable on the quadrant, with `G > 0` on a box `B ⊇ E` lying inside the quadrant, forces `E` to
be `NullMeasurableSet` (the factor `G` is invertible on `B`, so `1_E` is a.e. equal to the
measurable set `{g ≠ 0} ∩ B`). -/
private theorem nullMeasurableSet_of_aesm_smul_indicator {E : Set (ℝ × ℝ)}
    {G : ℝ × ℝ → ℝ} {c : ℝ}
    (hc : c ≠ 0) (hEsub : E ⊆ refBox) (hGpos : ∀ p ∈ refBox, 0 < G p)
    (h : AEStronglyMeasurable
      (fun p : ℝ × ℝ => c * G p * E.indicator (fun _ => (1 : ℝ)) p)
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))) :
    MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
  classical
  have hQmeas : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [Work.Spaces.Iz, Work.Spaces.Iθ]
    exact measurableSet_Ici.prod measurableSet_Icc
  obtain ⟨g, hg_sm, hg_eq⟩ := h
  -- move the a.e. equality from the restricted measure to the full one
  have hg_eq' : ∀ᵐ p ∂(MeasureTheory.volume : Measure (ℝ × ℝ)),
      p ∈ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) →
        (fun p => c * G p * E.indicator (fun _ => (1 : ℝ)) p) p = g p :=
    (ae_restrict_iff' hQmeas).mp hg_eq
  refine ⟨{p : ℝ × ℝ | g p ≠ 0} ∩ refBox, ?_, ?_⟩
  · exact (hg_sm.measurable (measurableSet_singleton (0 : ℝ))).compl.inter measurableSet_refBox
  · filter_upwards [hg_eq'] with p hp
    apply propext
    constructor
    · intro hpE
      have heq := hp (refBox_subset_quad (hEsub hpE))
      rw [Set.indicator_of_mem hpE] at heq
      have hgp : g p = c * G p := by rw [← heq, mul_one]
      refine ⟨?_, hEsub hpE⟩
      show g p ≠ 0
      rw [hgp]
      exact mul_ne_zero hc (ne_of_gt (hGpos p (hEsub hpE)))
    · rintro ⟨hgp, hpB⟩
      by_contra hpE
      have heq := hp (refBox_subset_quad hpB)
      rw [Set.indicator_of_notMem hpE] at heq
      exact hgp (by rw [← heq]; ring)

/-- The `±bump` datum of the refutation: `bump` flipped in sign on `E`. -/
private def refDatum (E : Set (ℝ × ℝ)) : Work.FTS.Galerkin.Fn :=
  fun z θ => bump z θ * (1 - 2 * E.indicator (fun _ => (1 : ℝ)) (z, θ))

private theorem refDatum_eq (E : Set (ℝ × ℝ)) (z θ : ℝ) :
    refDatum E z θ = bump z θ * (1 - 2 * E.indicator (fun _ => (1 : ℝ)) (z, θ)) := rfl

/-- Refutation of the `EpsMem` conjunct of the requested lemma `EpsSq_sub_smul_bump`: the `±bump` datum
built from a non-Lebesgue-measurable set `E` inside the bump's positive box has `EpsMem 1 h` (its
weighted square is the measurable `(bump · epsW 1)²`) but `h - c · bump` (`c ≠ 0`) is not a.e.
strongly measurable, hence not `EpsMem`. -/
theorem EpsSq_sub_smul_bump_refute
    (hbump : Work.FTS.StrongEps.EpsMem 1 Work.FTS.StrongEps.bump)
    {E : Set (ℝ × ℝ)}
    (hEsub : E ⊆ Set.Ioo (5 / 8) (7 / 8) ×ˢ Set.Ioo (Real.pi / 4) (3 * Real.pi / 8))
    (hE : ¬ MeasureTheory.NullMeasurableSet E MeasureTheory.volume) :
    ∃ (h : Work.FTS.Galerkin.Fn) (c : ℝ), c ≠ 0 ∧
      Work.FTS.StrongEps.EpsMem 1 h ∧
      ¬ Work.FTS.StrongEps.EpsMem 1
        (fun z θ => h z θ - c * Work.FTS.StrongEps.bump z θ) := by
  classical
  refine ⟨refDatum E, 1, one_ne_zero, ?_, ?_⟩
  · -- `EpsMem 1 h`: the weighted square of the sign flip is the weighted square of `bump`
    have hsq : ∀ p : ℝ × ℝ,
        (refDatum E p.1 p.2 * epsW 1 p.1 p.2) ^ 2 = (bump p.1 p.2 * epsW 1 p.1 p.2) ^ 2 := by
      intro p
      rw [refDatum_eq]
      have hsgn : (1 - 2 * E.indicator (fun _ => (1 : ℝ)) (p.1, p.2)) ^ 2 = 1 := by
        by_cases hp : (p.1, p.2) ∈ E
        · rw [Set.indicator_of_mem hp]; norm_num
        · rw [Set.indicator_of_notMem hp]; norm_num
      calc ((bump p.1 p.2 * (1 - 2 * E.indicator (fun _ => (1 : ℝ)) (p.1, p.2)))
              * epsW 1 p.1 p.2) ^ 2
          = (bump p.1 p.2 * epsW 1 p.1 p.2) ^ 2
              * (1 - 2 * E.indicator (fun _ => (1 : ℝ)) (p.1, p.2)) ^ 2 := by ring
        _ = (bump p.1 p.2 * epsW 1 p.1 p.2) ^ 2 := by rw [hsgn, mul_one]
    exact hbump.congr_fun_ae (by filter_upwards with p; exact (hsq p).symm)
  · -- `¬ EpsMem 1 (h - 1 · bump)`: its weighted square is `4 · G · 1_E`
    intro hmem
    have hmem' : MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => ((refDatum E p.1 p.2 - 1 * bump p.1 p.2) * epsW 1 p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hmem
    have hA : AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          4 * (bump p.1 p.2 * epsW 1 p.1 p.2) ^ 2 * E.indicator (fun _ => (1 : ℝ)) p)
        (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
      refine hmem'.aestronglyMeasurable.congr ?_
      filter_upwards with p
      rw [refDatum_eq]
      have hind : (E.indicator (fun _ => (1 : ℝ)) p) ^ 2
          = E.indicator (fun _ => (1 : ℝ)) p := by
        by_cases hp : p ∈ E
        · rw [Set.indicator_of_mem hp]; norm_num
        · rw [Set.indicator_of_notMem hp]; norm_num
      calc (((bump p.1 p.2 * (1 - 2 * E.indicator (fun _ => (1 : ℝ)) (p.1, p.2)))
                - 1 * bump p.1 p.2) * epsW 1 p.1 p.2) ^ 2
          = 4 * (bump p.1 p.2 * epsW 1 p.1 p.2) ^ 2
              * (E.indicator (fun _ => (1 : ℝ)) p) ^ 2 := by ring
        _ = 4 * (bump p.1 p.2 * epsW 1 p.1 p.2) ^ 2
              * E.indicator (fun _ => (1 : ℝ)) p := by rw [hind]
    exact hE (nullMeasurableSet_of_aesm_smul_indicator (G := fun p : ℝ × ℝ =>
        (bump p.1 p.2 * epsW 1 p.1 p.2) ^ 2) (c := 4) (by norm_num) hEsub
      (fun p hp => bump_epsW_one_sq_pos_of_mem_refBox hp) hA)

end

end Work.FTS.StrongEps.EpsSqTools
