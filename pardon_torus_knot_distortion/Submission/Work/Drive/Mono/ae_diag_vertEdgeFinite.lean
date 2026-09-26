import Mathlib
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.ae_ae_cornerLocus_finite
import Submission.Work.Drive.Mono.finite_zeroSet_of_isInvertible_fderiv

/-!
# The vertical edge locus is finite for almost every diagonal shift of the box centre

`Work.Drive.Mono.VertEdgeFinite ψ c σ s` says that the surface `F = ψ(standard torus)` meets the
box *edge lines* of direction `e_{σ 2}` in finitely many points, i.e. that the set of points of `F`
whose `σ 0`- and `σ 1`-coordinates are `σ`-extremal for the box `PBox s c σ` (that is
`|z (σ i) - c (σ i)| = boxSide i * s` for `i = 0, 1`) is finite.  It is part of the junction
genericity `Work.Drive.Mono.BoxGenE`: the finitely many heights of those points can then be avoided
by the cutting level (`Mono/NOTES_LEAD_junctionGen.md` §2, and §0.5 of the same note).

The statement at a **fixed** centre is false (`Mono/NOTES_H381_edgeArc_OBSTRUCTION.md` §5): a
`C^∞` diffeomorphism can flatten a patch of the surface into a plane containing an edge line, and
then the edge locus contains an arc.  The dependence on the centre saves the day: the edge lines of
the family sweep the plane `c + s w + span (e_{σ 2})` as `(c, s)` varies, and a plane is contained in
the surface only along the at most one-dimensional family of its ruled pieces.

This file proves `Work.Drive.Mono.ae_diag_vertEdgeFinite`: for **almost every** shift `τ` of the
centre along the diagonal `Work.Drive.Mono.diagVec` and **almost every** level `s`, the vertical
edge locus of the shifted centre `c + τ • diagVec` is finite.  This is exactly the input (G3) that
the junction route needs, and it is the reason the *diagonal* direction is used: along it the pair
of box coordinates `(y (σ 0), y (σ 1))` of the shifted centre is an **invertible** affine function
of `(τ, s)`.

The proof is the pair-Sard argument of `Mono/NOTES_LEAD_junctionGen.md` §2 (G3), run in the
two-parameter family `(τ, s)`:

* the pair projection `Φ = (y (σ 0), y (σ 1)) ∘ par` of the surface has null critical values
  (`Work.Drive.Mono.cornerCritVals_null`) and at a regular value its fibre is finite
  (`Work.Drive.Mono.cornerFibre_infinite_subset_critVals`);
* at level `s` and shift `τ` with sign choices `εi, εj` the corresponding corner value of the
  shifted centre is `(c (σ 0), c (σ 1)) + L_ε (τ, s)`, where
  `L_ε (τ, s) = (τ + εi * boxSide 0 * s, τ + εj * boxSide 1 * s)` is the linear map `shiftLin`;
  since `boxSide 0 = 1` and `boxSide 1 = 2^{1/3}` differ, `L_ε` is invertible for all four sign
  choices, so the bad set of `(τ, s)` (the preimage of the null set of critical values, translated)
  is null (`MeasureTheory.ae_comp_linearMap_mem_iff` in the form of its proof via
  `MeasureTheory.measure_preimage_add`);
* Fubini (`MeasureTheory.Measure.ae_ae_of_ae_prod`) turns the joint a.e. statement into the iterated
  one;
* finally the sign split `abs_eq` exhibits the edge locus as a finite union of four such fibres, so
  that finiteness of the fibres gives finiteness of the locus (for `s ≤ 0` the locus is contained in
  a single fibre at level `0`).
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal

noncomputable section

/-! ## The linear map of the diagonal shift -/

/-- The linear map `(τ, s) ↦ (τ + a * s, τ + b * s)` of `ℝ²`.  It describes the pair of box
coordinates `(y (σ 0), y (σ 1))` of the point `c + τ • diagVec` at level `s` with the sign choices
encoded in `a` and `b`, and it is invertible as soon as `a ≠ b`. -/
def shiftLin (a b : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun w := (w.1 + a * w.2, w.1 + b * w.2)
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp <;> ring

@[simp] theorem shiftLin_apply (a b τ s : ℝ) :
    shiftLin a b (τ, s) = (τ + a * s, τ + b * s) := rfl

/-- `shiftLin a b` is surjective (even a linear equivalence) as soon as `a ≠ b`. -/
theorem shiftLin_surjective {a b : ℝ} (hab : a ≠ b) : Function.Surjective (shiftLin a b) := by
  intro v
  refine ⟨(v.1 - a * ((v.2 - v.1) / (b - a)), (v.2 - v.1) / (b - a)), ?_⟩
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  rw [shiftLin_apply, Prod.mk.injEq]
  constructor
  · ring
  · field_simp
    ring

/-- `boxSide 1 = 2^{1/3}` exceeds `1`. -/
theorem one_lt_boxSide_one : (1 : ℝ) < Submission.boxSide 1 := by
  rw [Submission.boxSide_one]
  simpa using (Real.rpow_lt_rpow_left_iff (x := (2 : ℝ)) (by norm_num)).mpr
    (by norm_num : (0 : ℝ) < 1 / 3)

/-- The sign of any of the four sign choices, times the corresponding side length, never coincides
between the two coordinates: `εi * boxSide 0 ≠ εj * boxSide 1`.  This is what makes `shiftLin`
invertible. -/
theorem sgn_mul_boxSide_ne (εi εj : Bool) :
    sgn εi * Submission.boxSide 0 ≠ sgn εj * Submission.boxSide 1 := by
  have h1 := one_lt_boxSide_one
  rw [Submission.boxSide_zero, mul_one]
  cases εi <;> cases εj <;> simp only [sgn_true, sgn_false, one_mul, neg_one_mul] <;>
    intro h <;> linarith

/-- The corner value of the shifted centre is the translate of the value of `shiftLin`: this is
where the coordinate of the diagonal vector enters, `diagVec (σ i) = 1`. -/
theorem shift_shiftLin_eq (c : R3) (σ : Equiv.Perm (Fin 3)) (εi εj : Bool) (u v : ℝ) :
    (c (σ 0), c (σ 1)) + shiftLin (sgn εi * Submission.boxSide 0)
        (sgn εj * Submission.boxSide 1) (u, v)
      = cornerLin σ 0 1 (sgn εi) (sgn εj) (c + u • diagVec, v) := by
  ext <;> simp [shiftLin_apply, cornerLin_apply, PiLp.add_apply, diagVec] <;> ring

/-! ## Almost every `(τ, s)` gives a regular corner value -/

/-- **The pair-corner value of the shifted centre is a regular value of the pair projection for
almost every `(τ, s)`.**  This is the two-parameter Sard input: the bad set of `(τ, s)` is the
preimage under the invertible affine map `(τ, s) ↦ (c (σ 0), c (σ 1)) + L_ε (τ, s)` of the null set
of critical values of the pair projection `(y (σ 0), y (σ 1)) ∘ par`. -/
theorem ae_shift_pair_notMem (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (εi εj : Bool) :
    ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)),
      cornerLin σ 0 1 (sgn εi) (sgn εj) (c + w.1 • diagVec, w.2) ∉
        cornerCritVals ψ σ 0 1 := by
  have hab := sgn_mul_boxSide_ne εi εj
  have hms : MeasurableSet {v : ℝ × ℝ | (c (σ 0), c (σ 1)) + v ∉ cornerCritVals ψ σ 0 1} :=
    (cornerCritVals_measurable ψ σ 0 1).compl.preimage (measurable_const.add measurable_id)
  have hiff := MeasureTheory.ae_comp_linearMap_mem_iff
    (shiftLin (sgn εi * Submission.boxSide 0) (sgn εj * Submission.boxSide 1))
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
    (shiftLin_surjective hab) hms
  have hgoal : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)),
      shiftLin (sgn εi * Submission.boxSide 0) (sgn εj * Submission.boxSide 1) w ∈
        {v : ℝ × ℝ | (c (σ 0), c (σ 1)) + v ∉ cornerCritVals ψ σ 0 1} := by
    refine hiff.mpr ?_
    rw [MeasureTheory.ae_iff]
    have hset : {y : ℝ × ℝ | ¬ y ∈ {v : ℝ × ℝ |
        (c (σ 0), c (σ 1)) + v ∉ cornerCritVals ψ σ 0 1}} =
        (fun h : ℝ × ℝ => (c (σ 0), c (σ 1)) + h) ⁻¹' cornerCritVals ψ σ 0 1 := by
      ext y
      simp
    rw [hset, MeasureTheory.measure_preimage_add]
    exact cornerCritVals_null ψ σ 0 1
  filter_upwards [hgoal] with w hw
  obtain ⟨u, v⟩ := w
  rw [shift_shiftLin_eq c σ εi εj u v] at hw
  exact hw

/-! ## Fubini -/

/-- **Almost every shift and almost every level: all four pair-fibres are finite.** -/
theorem ae_ae_diag_fibre_finite (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ τ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ ε : Bool × Bool,
          (cornerFibre ψ σ 0 1
            (cornerLin σ 0 1 (sgn ε.1) (sgn ε.2) (c + τ • diagVec, s))).Finite := by
  have hjoint : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)),
      ∀ ε : Bool × Bool,
        cornerLin σ 0 1 (sgn ε.1) (sgn ε.2) (c + w.1 • diagVec, w.2) ∉
          cornerCritVals ψ σ 0 1 :=
    Filter.eventually_all.mpr fun ε => ae_shift_pair_notMem ψ c σ ε.1 ε.2
  have hprod : ∀ᵐ w ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)),
      ∀ ε : Bool × Bool,
        cornerLin σ 0 1 (sgn ε.1) (sgn ε.2) (c + w.1 • diagVec, w.2) ∉
          cornerCritVals ψ σ 0 1 := by
    rw [← MeasureTheory.Measure.volume_eq_prod]
    exact hjoint
  have h2 := MeasureTheory.Measure.ae_ae_of_ae_prod hprod
  filter_upwards [h2] with τ hτ
  filter_upwards [hτ] with s hs
  intro ε
  rw [← Set.not_infinite]
  exact fun hinf => hs ε (cornerFibre_infinite_subset_critVals ψ σ 0 1 hinf)

/-! ## From the fibres to the locus -/

/-- **The vertical edge locus is contained in the union of the four corner fibres.**  For `s > 0`
this is the sign split of the absolute values; for `s ≤ 0` the level condition forces `s = 0` and
the locus is contained in the fibre at the centre itself. -/
theorem vertEdgeFinite_of_forall_fibre_finite (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (s : ℝ)
    (hs : ∀ ε : Bool × Bool,
      (cornerFibre ψ σ 0 1 (cornerLin σ 0 1 (sgn ε.1) (sgn ε.2) (c, s))).Finite) :
    VertEdgeFinite ψ c σ s := by
  have hfin : (⋃ ε : Bool × Bool, cornerFibre ψ σ 0 1
      (cornerLin σ 0 1 (sgn ε.1) (sgn ε.2) (c, s))).Finite :=
    Set.Finite.iUnion (t := Set.univ) Set.finite_univ (fun ε _ => hs ε)
      (fun ε h => absurd (Set.mem_univ ε) h)
  refine hfin.subset (fun z hz => ?_)
  simp only [Set.mem_ofPred_eq] at hz
  obtain ⟨hcar, h1, h2⟩ := hz
  by_cases hs0 : 0 < s
  · obtain ⟨εi, εj, hmem⟩ := cornerFibre_mem_of_abs_eq ψ σ hs0 hcar h1 h2
    exact Set.mem_iUnion.mpr ⟨(εi, εj), hmem⟩
  · -- `s ≤ 0`: then necessarily `s = 0` and the locus is contained in the fibre at the centre.
    have hsle : s ≤ 0 := le_of_not_gt hs0
    have hb0 : Submission.boxSide 0 * s = 0 :=
      le_antisymm (mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Submission.boxSide_pos 0)) hsle)
        (h1 ▸ abs_nonneg _)
    have hseq : s = 0 := by
      rcases mul_eq_zero.mp hb0 with h | h
      · exact absurd h (ne_of_gt (Submission.boxSide_pos 0))
      · exact h
    have hz0 : z (σ 0) = c (σ 0) := by
      have h : |z (σ 0) - c (σ 0)| = 0 := by rw [h1, hb0]
      linarith [abs_eq_zero.mp h]
    have hz1 : z (σ 1) = c (σ 1) := by
      have h : |z (σ 1) - c (σ 1)| = 0 := by rw [h2, hseq, mul_zero]
      linarith [abs_eq_zero.mp h]
    refine Set.mem_iUnion.mpr ⟨(true, true), ?_⟩
    have hv : cornerLin σ 0 1 (sgn true) (sgn true) (c, s) = (c (σ 0), c (σ 1)) := by
      rw [cornerLin_apply, sgn_true, hseq]
      simp
    rw [cornerFibre, Set.mem_ofPred_eq, hv]
    exact ⟨hcar, hz0, hz1⟩

/-- **`VertEdgeFinite` for the shifted centre, for almost every shift and almost every level.**
This is the statement that the junction route (G3 of `Mono/NOTES_LEAD_junctionGen.md` §2) needs: the
shift along the diagonal makes the vertical edge locus finite except on a null set of `(τ, s)`. -/
theorem ae_diag_vertEdgeFinite (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ τ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        Work.Drive.Mono.VertEdgeFinite ψ (c + τ • Work.Drive.Mono.diagVec) σ s := by
  filter_upwards [ae_ae_diag_fibre_finite ψ c σ] with τ hτ
  filter_upwards [hτ] with s hs
  exact vertEdgeFinite_of_forall_fibre_finite ψ (c + τ • diagVec) σ s hs

end

end Work.Drive.Mono
