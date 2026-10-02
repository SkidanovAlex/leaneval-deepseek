/-
# ELRig — side preservation of the shift (`Z1Nest.SP`, R-a1 core)

For `u` in the far-left half plane of the repelling coordinate, the *side* of the `α`-pair `P`
of `Ψ u` and of `Ψ (u + 1) = F c (Ψ u)` agree.  This is the core of the side preservation
`Z1Nest.SP` (`NOTES_LEAD_mandelbar_residuals.md` §3.2 (d)), which replaces the false
`NestData.band`.

## The reduction

Let `Λ = range γ₁ ∪ range γ₂` be the two lifts of `RayCylLift`.  By `TailId`
(`RayCylLift.preimage_pairCurve`) the `Ψ`-preimages of the pair curve inside the half plane
`{Re < -L.R}` are exactly `Λ`, and `Λ` is invariant under the shift `w ↦ w + 1` (`lift_shift`),
which realises `F c` on the dynamical plane (`Ψ_shift`).

* If `u ∈ Λ`, then also `u + 1 ∈ Λ`; both `Ψ u` and `Ψ (u+1)` lie on the pair curve, so both
  sides of the equivalence are false (`sidePreserve_core_of_mem_lift`).
* If the whole segment `[u, u+1]` avoids `Λ`, its `Ψ`-image is connected and avoids the pair
  curve, hence lies in one side (`sidePreserve_core_of_avoid`).
* If the segment meets `Λ`, one walks along the segment: the labelling
  `w ↦ [Ψ w ∈ pairSide P]` is locally constant off `Λ`, so the label changes only at the
  crossing times.  At a crossing the label changes exactly when the crossing is a *sign change*
  of the corresponding height function (`Work.ELRig.side_flip_at_crossing` and its second-lift
  analogue), i.e. the label change is governed by `Im ∘ γᵢ - Im u`.

## The far-end case (proved here)

The far ends of the half planes `{Re w < -R₀, |Im w| > R₀}` map into the attracting petal `Pa`
(`RayCylLift.hγtail`), which lies in the far side `pairSide P` (`hPa_far`), and `F` preserves the
far side there (`mapsTo_Pa`).  Hence, whenever `u` is joined to such a point inside the far-left
half plane minus `Λ`, both `Ψ u` and `Ψ (u+1)` lie in the far side: see
`side_of_preconnected_Pa`, `sidePreserve_core_of_Pa_components`.


## The crossing-parity core (delegated: `Work.ELRig.sidePreserve_core_of_crossing_parity`)

Let `c := Im u`, `a := Re u`, and suppose the level sets
`{s ∈ [0,1) : (γᵢ s).im = c}` are finite (`hfin₁`, `hfin₂`).  Then the crossing-parity core
proves the target *without* any further hypothesis.  The proof, in outline:

1. **Finiteness of the crossing parameters.**  For `i = 1, 2` put
   `Zᵢ := {s : (γᵢ s).im = c}`, a `1`-periodic set (from `perᵢ`).  If `s ∈ Zᵢ` and
   `(γᵢ s).re ∈ [a, a+1]`, then `|s| ≤ |(γᵢ s).re| + M ≤ |a| + 1 + M` for `M` from
   `RayCylLift.highBdd`/`re_sub_bounded` (`Submission/Work/ELRig/TailBand.lean`), so all crossing
   parameters lie in a fixed compact interval, which is covered by finitely many unit windows;
   by `1`-periodicity and `hfinᵢ` the crossing set is therefore **finite**.
   Hmm: also: `u ∉ Λ` and `u + 1 ∉ Λ` (the second by `lift_shift`) give `dist u Λ > 0`, hence the
   **endpoints** of the segment are off `Λ`.

2. **The bijection.**  For `s ∈ Zᵢ ∩ [0,1)` there is *exactly one* `k ∈ ℤ` with
   `(γᵢ s).re + k ∈ (a, a+1)` — because the numbers `(γᵢ s).re + k` are equally spaced by `1` and
   the two excluded boundary cases would put an endpoint of the segment on `Λ`.  This gives a
   bijection between `Zᵢ ∩ [0,1)` and the crossing times of the open segment with `γᵢ`, and the
   *sign-change status* is preserved because the height functions are `1`-periodic.

3. **Flips vs. sign changes.**  At the crossing time corresponding to `s`, the label flips iff
   `Im γᵢ - c` changes sign at `s` (`Work.ELRig.side_flip_at_crossing` for `i = 1`,
   `Work.ELRig.side_flip_at_crossing_gamma2` for `i = 2`); the isolating `δ` needed by those
   criteria exists by step 1 (the crossing set is finite).  Hence the number of *flip* times is
   `#{sign changes of Im γ₁ - c in [0,1)} + #{sign changes of Im γ₂ - c in [0,1)}`, and each summand
   is **even** by `Work.ELRig.even_sign_changes` (applied to the `1`-periodic continuous functions
   `Im γ₁` at level `c` and to `Im γ₁` at level `-c`, since `Im γ₂ = -Im γ₁`).

4. **Conclusion.**  Apply `Work.ELRig.same_side_of_even_flips` to the straight segment
   `σ t = u + t` on `[0,1]`, with `T` the finite set of crossing times and `F ⊆ T` the flip times
   (even cardinality by step 3).

## The generic-height reduction (proved here, `sidePreserve_core_of_generic_levels`)

`sidePreserve_core_of_crossing_parity` needs the finiteness hypotheses `hfinᵢ`.  If they fail at
the height `c = Im u` one moves vertically by a small generic amount:  `Work.ELRig.levelSet_im_finite_small`
produces `η ∈ (0, dist u Λ)` (with `dist u Λ > 0` from `Work.ELRig.range_lift_closed`, and using a
window `[N, N+1]` in which the pin holds, so that `γ₁ s = invFunOn Ψ (rayPt α₁ (τ s))` via
`Work.ELRig.pointwise_pin`) such that the level sets at height `c + η` are finite.  Then:

* the vertical segment from `u` to `u + iη` (and likewise from `u + 1 + iη` down to `u + 1`)
  avoids `Λ`, because all its points are within distance `η < dist u Λ` of `u` (resp. of `u + 1`);
* hence the labels of `Ψ u` and `Ψ (u + iη)` agree, and so do those of `Ψ (u + 1 + iη)` and
  `Ψ (u + 1)`;
* apply the core to `u + iη` (whose `Re` is `a < -R ≤ -L.R` and whose shift has `Re` `a + 1`),
  using the finiteness at height `c + η`.

## The remaining case and its parity bookkeeping

For the middle components one uses the crossing parity along the horizontal segment `[u, u+1]`:
both height functions `Im ∘ γ₁` and `Im ∘ γ₂ = -Im ∘ γ₁` are `1`-periodic and continuous, by
`Work.ELRig.even_sign_changes` the number of sign changes of a `1`-periodic continuous function at
a level *inside one period* is even (provided the level set in that period is finite), the
crossings of the segment with `γᵢ` correspond bijectively to the level set of `Im ∘ γᵢ - Im u` in
one period, and the sign-change condition is periodic in the parameter.  So the total number of
label changes is the sum of two even numbers and the labels at `u`, `u+1` agree.

The finiteness of the level set in a period is the content of `levelSet_finite_generic`; the
second-lift form of the flip criterion is `side_flip_at_crossing_γ₂`.
-/
import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.CylSides
import Submission.Work.ELRig.Defs
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.Flower
import Submission.Work.ELRig.rayPt_iterate
import Submission.Work.ELRig.cert
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.paramRay_subset_pairSideNear
import Submission.Work.ELRig.TailBand
import Submission.Work.ELRig.pointwise_pin
import Submission.Work.ELRig.levelSet_im_finite_small
import Submission.Work.ELRig.range_lift_closed
import Submission.Work.ELRig.sidePreserve_core_of_crossing_parity

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ} {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}

/-! ## The lifts under the shift -/

/-- The two lifts are invariant under the shift `w ↦ w + 1`, in both directions. -/
theorem lift_shift (L : RayCylLift d fl) (u : ℂ) :
    (u ∈ Set.range L.γ₁ ∪ Set.range L.γ₂) ↔
      (u + 1 ∈ Set.range L.γ₁ ∪ Set.range L.γ₂) := by
  constructor
  · rintro (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact Or.inl ⟨s + 1, L.per₁ s⟩
    · exact Or.inr ⟨s + 1, L.per₂ s⟩
  · rintro (⟨s, hs⟩ | ⟨s, hs⟩)
    · refine Or.inl ⟨s - 1, ?_⟩
      have h := L.per₁ (s - 1)
      rw [sub_add_cancel] at h
      rw [hs] at h
      exact (add_right_cancel h).symm
    · refine Or.inr ⟨s - 1, ?_⟩
      have h := L.per₂ (s - 1)
      rw [sub_add_cancel] at h
      rw [hs] at h
      exact (add_right_cancel h).symm

/-! ## The two easy cases -/

/-- **Case `u ∈ Λ`.**  Both `Ψ u` and `Ψ (u+1)` lie on the pair curve, hence in neither side. -/
theorem sidePreserve_core_of_mem_lift (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P) {u : ℂ} (hu : u.re < -L.R) (hu1 : u.re + 1 < -L.R)
    (huΛ : u ∈ Set.range L.γ₁ ∪ Set.range L.γ₂) :
    (fl.Ψ u ∈ Work.EL.pairSide P ↔ fl.Ψ (u + 1) ∈ Work.EL.pairSide P) := by
  have hu1Λ : u + 1 ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ := (lift_shift L u).mp huΛ
  have hu1' : (u + 1).re < -L.R := by
    have : (u + 1).re = u.re + 1 := by simp
    rw [this]; exact hu1
  have h1 : fl.Ψ u ∈ Work.EL.pairCurve P :=
    (RayCylLift.preimage_pairCurve L P hPa hPb hPy u hu).mpr huΛ
  have h2 : fl.Ψ (u + 1) ∈ Work.EL.pairCurve P :=
    (RayCylLift.preimage_pairCurve L P hPa hPb hPy (u + 1) hu1').mpr hu1Λ
  exact ⟨fun h => (hside.notMem_curve_of_mem_far h h1).elim,
    fun h => (hside.notMem_curve_of_mem_far h h2).elim⟩

/-- **Case: the `Ψ`-image of the segment is connected and avoids the pair curve.** -/
theorem sidePreserve_core_of_avoid (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P) {u : ℂ} (hu1 : u.re + 1 < -L.R)
    (havoid : ∀ t ∈ Set.Icc (0 : ℝ) 1, u + t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) :
    (fl.Ψ u ∈ Work.EL.pairSide P ↔ fl.Ψ (u + 1) ∈ Work.EL.pairSide P) := by
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, (u + t).re < -L.R := by
    intro t ht
    have hre : (u + t).re = u.re + t := by simp
    have ht1 : t ≤ 1 := ht.2
    rw [hre]; linarith
  set S : Set ℂ := (fun t : ℝ => u + t) '' Set.Icc (0 : ℝ) 1 with hS
  have hcont : Continuous fun t : ℝ => u + t := continuous_const.add Complex.continuous_ofReal
  have hpre : IsPreconnected S :=
    (isPreconnected_Icc (a := (0 : ℝ)) (b := 1)).image _ hcont.continuousOn
  set T : Set ℂ := fl.Ψ '' S with hT
  have hTpre : IsPreconnected T := hpre.image _ fl.Ψ_diff.continuous.continuousOn
  have hTsub : T ⊆ (Work.EL.pairCurve P)ᶜ := by
    rintro z ⟨w, ⟨t, ht, rfl⟩, rfl⟩
    rw [Set.mem_compl_iff]
    intro hcurve
    exact havoid t ht
      ((RayCylLift.preimage_pairCurve L P hPa hPb hPy (u + t) (hseg t ht)).mp hcurve)
  have h0 : u ∈ S := ⟨0, ⟨le_rfl, by norm_num⟩, by simp⟩
  have h1 : u + 1 ∈ S := ⟨1, ⟨by norm_num, le_rfl⟩, by simp⟩
  have h0T : fl.Ψ u ∈ T := ⟨u, h0, rfl⟩
  have h1T : fl.Ψ (u + 1) ∈ T := ⟨u + 1, h1, rfl⟩
  rcases hside.subset_of_preconnected hTpre hTsub with h | h
  · exact ⟨fun _ => h h1T, fun _ => h h0T⟩
  · exact ⟨fun hf => (Set.disjoint_left.mp hside.disjoint hf (h h0T)).elim,
      fun hf => (Set.disjoint_left.mp hside.disjoint hf (h h1T)).elim⟩

/-! ## The far-end case: the petal is in the far side -/

/-- **`F` preserves the far side at the points of the attracting petal**: `Ψ (u+1) = F (Ψ u)`. -/
theorem side_of_mem_Pa (P : Work.EL.CoPair d.hN) (hPa_far : fl.Pa ⊆ Work.EL.pairSide P) {u : ℂ}
    (hu : fl.Ψ u ∈ fl.Pa) :
    fl.Ψ u ∈ Work.EL.pairSide P ∧ fl.Ψ (u + 1) ∈ Work.EL.pairSide P :=
  ⟨hPa_far hu, by rw [fl.Ψ_shift u]; exact hPa_far (fl.mapsTo_Pa hu)⟩

/-- **The label of `Ψ` is constant on a preconnected set avoiding `Λ`**, and it is the far side if
the `Ψ`-image meets the petal. -/
theorem side_of_preconnected_Pa (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P) (hPa_far : fl.Pa ⊆ Work.EL.pairSide P)
    {S : Set ℂ} (hSsub : ∀ w ∈ S, w.re < -L.R)
    (hSavoid : ∀ w ∈ S, w ∉ Set.range L.γ₁ ∪ Set.range L.γ₂)
    (hSconn : IsPreconnected S) {w₀ : ℂ} (hw₀ : w₀ ∈ S) (hw₀Pa : fl.Ψ w₀ ∈ fl.Pa) :
    ∀ w ∈ S, fl.Ψ w ∈ Work.EL.pairSide P := by
  have himg : fl.Ψ '' S ⊆ (Work.EL.pairCurve P)ᶜ := by
    rintro z ⟨w, hw, rfl⟩
    rw [Set.mem_compl_iff]
    intro hcurve
    exact hSavoid w hw ((RayCylLift.preimage_pairCurve L P hPa hPb hPy w (hSsub w hw)).mp hcurve)
  have hpre : IsPreconnected (fl.Ψ '' S) := hSconn.image _ fl.Ψ_diff.continuous.continuousOn
  rcases hside.subset_of_preconnected hpre himg with h | h
  · exact fun w hw => h ⟨w, hw, rfl⟩
  · exfalso
    exact (Set.disjoint_left.mp hside.disjoint (hPa_far hw₀Pa)) (h ⟨w₀, hw₀, rfl⟩)

/-- **The far-end case of the target.**  If `u` and `u + 1` are each joined to a point of the
petal `Pa` inside the far-left half plane minus the two lifts, then the two sides agree. -/
theorem sidePreserve_core_of_Pa_components (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P) (hPa_far : fl.Pa ⊆ Work.EL.pairSide P)
    {u : ℂ} {S S' : Set ℂ}
    (hSsub : ∀ w ∈ S, w.re < -L.R) (hSavoid : ∀ w ∈ S, w ∉ Set.range L.γ₁ ∪ Set.range L.γ₂)
    (hSconn : IsPreconnected S) (hu : u ∈ S) {w₀ : ℂ} (hw₀ : w₀ ∈ S)
    (hw₀Pa : fl.Ψ w₀ ∈ fl.Pa)
    (hS'sub : ∀ w ∈ S', w.re < -L.R)
    (hS'avoid : ∀ w ∈ S', w ∉ Set.range L.γ₁ ∪ Set.range L.γ₂)
    (hS'conn : IsPreconnected S') (hu' : u + 1 ∈ S') {w₁ : ℂ} (hw₁ : w₁ ∈ S')
    (hw₁Pa : fl.Ψ w₁ ∈ fl.Pa) :
    (fl.Ψ u ∈ Work.EL.pairSide P ↔ fl.Ψ (u + 1) ∈ Work.EL.pairSide P) :=
  ⟨fun _ => side_of_preconnected_Pa L P hPa hPb hPy hside hPa_far hS'sub hS'avoid hS'conn
      hw₁ hw₁Pa (u + 1) hu',
    fun _ => side_of_preconnected_Pa L P hPa hPb hPy hside hPa_far hSsub hSavoid hSconn
      hw₀ hw₀Pa u hu⟩


/-! ## A general "same side" transfer along a preconnected set -/

/-- **The two sides agree along any preconnected set avoiding `Λ` inside the far-left half
plane.**  Indeed the `Ψ`-image is preconnected and avoids the pair curve, so it lies in one of the
two sides. -/
theorem side_eq_of_preconnected (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P) {S : Set ℂ}
    (hSsub : ∀ w ∈ S, w.re < -L.R)
    (hSavoid : ∀ w ∈ S, w ∉ Set.range L.γ₁ ∪ Set.range L.γ₂)
    (hSconn : IsPreconnected S) {w w' : ℂ} (hw : w ∈ S) (hw' : w' ∈ S) :
    (fl.Ψ w ∈ Work.EL.pairSide P ↔ fl.Ψ w' ∈ Work.EL.pairSide P) := by
  have himg : fl.Ψ '' S ⊆ (Work.EL.pairCurve P)ᶜ := by
    rintro z ⟨x, hx, rfl⟩
    rw [Set.mem_compl_iff]
    intro hcurve
    exact hSavoid x hx ((RayCylLift.preimage_pairCurve L P hPa hPb hPy x (hSsub x hx)).mp hcurve)
  have hpre : IsPreconnected (fl.Ψ '' S) := hSconn.image _ fl.Ψ_diff.continuous.continuousOn
  rcases hside.subset_of_preconnected hpre himg with h | h
  · exact ⟨fun _ => h ⟨w', hw', rfl⟩, fun _ => h ⟨w, hw, rfl⟩⟩
  · exact ⟨fun hf => (Set.disjoint_left.mp hside.disjoint hf (h ⟨w, hw, rfl⟩)).elim,
      fun hf => (Set.disjoint_left.mp hside.disjoint hf (h ⟨w', hw', rfl⟩)).elim⟩

/-- The vertical segment `{u + i t | t ∈ [0, η]}` is preconnected. -/
theorem vertical_segment_Icc_preconnected (u : ℂ) (η : ℝ) :
    IsPreconnected ((fun t : ℝ => u + (t : ℂ) * Complex.I) '' Set.Icc (0 : ℝ) η) :=
  (isPreconnected_Icc (a := (0 : ℝ)) (b := η)).image _
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn)


/-- **Finiteness in a unit window transfers to the period `[0,1)`**, for a `1`-periodic
function. -/
theorem finite_levelSet_Ico_one_of_window {h : ℝ → ℝ} (hper : ∀ s : ℝ, h (s + 1) = h s) {c N : ℝ}
    (hfin : ({s : ℝ | s ∈ Set.Ico N (N + 1) ∧ h s = c}).Finite) :
    ({s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ h s = c}).Finite := by
  -- the level set on two consecutive half-open windows
  have h2 : ({s : ℝ | s ∈ Set.Ico N (N + 2) ∧ h s = c}).Finite := by
    have hshift : {s : ℝ | s ∈ Set.Ico (N + 1) (N + 2) ∧ h s = c}
        = (fun s : ℝ => s + 1) '' {s : ℝ | s ∈ Set.Ico N (N + 1) ∧ h s = c} := by
      ext s
      constructor
      · rintro ⟨hs, hsc⟩
        refine ⟨s - 1, ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩, by ring⟩
        have h1' : h (s - 1) = h s := by
          have hh := hper (s - 1)
          rw [sub_add_cancel] at hh
          exact hh.symm
        rw [h1']; exact hsc
      · rintro ⟨t, ⟨ht, htc⟩, rfl⟩
        refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
        rw [hper t]; exact htc
    have hsplit : {s : ℝ | s ∈ Set.Ico N (N + 2) ∧ h s = c}
        = ({s : ℝ | s ∈ Set.Ico N (N + 1) ∧ h s = c})
          ∪ ({s : ℝ | s ∈ Set.Ico (N + 1) (N + 2) ∧ h s = c}) := by
      ext s
      constructor
      · rintro ⟨hs, hsc⟩
        rcases lt_or_ge s (N + 1) with h | h
        · exact Or.inl ⟨⟨hs.1, h⟩, hsc⟩
        · exact Or.inr ⟨⟨h, hs.2⟩, hsc⟩
      · rintro (⟨hs, hsc⟩ | ⟨hs, hsc⟩)
        · exact ⟨⟨hs.1, by linarith [hs.2]⟩, hsc⟩
        · exact ⟨⟨by linarith [hs.1], hs.2⟩, hsc⟩
    rw [hsplit]
    exact hfin.union (hshift ▸ hfin.image _)
  -- an integral shift putting `[0,1)` inside the two-window
  obtain ⟨k : ℤ, hk1 : N + (k : ℝ) ≤ 0, hk2 : -1 ≤ N + (k : ℝ)⟩ :
      ∃ k : ℤ, N + (k : ℝ) ≤ 0 ∧ -1 ≤ N + (k : ℝ) := by
    refine ⟨⌊-N⌋, ?_, ?_⟩
    · have := Int.floor_le (-N); push_cast at this ⊢; linarith
    · have := Int.lt_floor_add_one (-N); push_cast at this ⊢; linarith
  have hk : ∀ s : ℝ, h (s + (k : ℝ)) = h s := fun s => by
    simpa using (Function.Periodic.int_mul (c := (1 : ℝ)) hper k) s
  have h3 : ({s : ℝ | s ∈ Set.Ico (N + (k : ℝ)) (N + (k : ℝ) + 2) ∧ h s = c}).Finite := by
    have hshift : {s : ℝ | s ∈ Set.Ico (N + (k : ℝ)) (N + (k : ℝ) + 2) ∧ h s = c}
        = (fun s : ℝ => s + (k : ℝ)) '' {s : ℝ | s ∈ Set.Ico N (N + 2) ∧ h s = c} := by
      ext s
      constructor
      · rintro ⟨hs, hsc⟩
        refine ⟨s - (k : ℝ), ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩, by ring⟩
        have h1' : h (s - (k : ℝ)) = h s := by
          have hh := hk (s - (k : ℝ))
          rw [sub_add_cancel] at hh
          exact hh.symm
        rw [h1']; exact hsc
      · rintro ⟨t, ⟨ht, htc⟩, rfl⟩
        refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
        rw [hk t]; exact htc
    rw [hshift]
    exact h2.image _
  exact h3.subset (fun s hs =>
    ⟨⟨by linarith [hs.1.1, hk1], by linarith [hs.1.2, hk2]⟩, hs.2⟩)

/-- **The label is unchanged along a vertical segment that avoids `Λ`.** -/
theorem side_eq_of_vertical_avoid (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P)
    {u : ℂ} {η : ℝ} (hη : 0 < η) (hre : u.re < -L.R)
    (havoid : ∀ t ∈ Set.Icc (0 : ℝ) η, u + (t : ℂ) * Complex.I ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) :
    (fl.Ψ u ∈ Work.EL.pairSide P ↔ fl.Ψ (u + (η : ℂ) * Complex.I) ∈ Work.EL.pairSide P) := by
  refine side_eq_of_preconnected L P hPa hPb hPy hside ?_ ?_
    (vertical_segment_Icc_preconnected u η) ?_ ?_
  · rintro z ⟨t, _, rfl⟩
    simpa using hre
  · rintro z ⟨t, ht, rfl⟩
    exact havoid t ht
  · exact ⟨0, ⟨le_rfl, hη.le⟩, by simp⟩
  · exact ⟨η, ⟨hη.le, le_rfl⟩, by simp⟩


/-! ## The generic-height reduction -/

/-- **The generic-height step.**  If the level sets of the two lifts at the height of `u` are not
both finite, one moves vertically by a small amount `η` smaller than the distance of `u` (and of
`u + 1`) from the two lifts: the two vertical segments then avoid `Λ`, so the labels at their two
ends agree, while at the shifted height the level sets *are* finite (by
`Work.ELRig.levelSet_im_finite_small`) and the crossing-parity core applies. -/
theorem sidePreserve_core_of_generic_levels (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P)
    {u : ℂ} (huΛ : u ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) (hu : u.re < -L.R)
    (hu1 : u.re + 1 < -L.R)
    (hbad : ¬ (({s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im}).Finite ∧
      ({s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im}).Finite)) :
    (fl.Ψ u ∈ Work.EL.pairSide P ↔ fl.Ψ (u + 1) ∈ Work.EL.pairSide P) := by
  set Λ : Set ℂ := Set.range L.γ₁ ∪ Set.range L.γ₂ with hΛdef
  have hcl : IsClosed Λ := range_lift_closed d fl L
  have hne : Λ.Nonempty := ⟨L.γ₁ 0, Or.inl ⟨0, rfl⟩⟩
  have hd1 : 0 < Metric.infDist u Λ := (hcl.notMem_iff_infDist_pos hne).mp huΛ
  have hu1Λ : u + 1 ∉ Λ := fun h => huΛ ((lift_shift L u).mpr h)
  have hd2 : 0 < Metric.infDist (u + 1) Λ := (hcl.notMem_iff_infDist_pos hne).mp hu1Λ
  -- the window in which the pin holds
  obtain ⟨M, hM⟩ := re_sub_bounded L
  set N : ℝ := -L.R - M - 2 with hN
  have hwin : ∀ s ∈ Set.Icc N (N + 1), (L.γ₁ s).re < -L.R := by
    intro s hs
    have h := (abs_le.mp (hM s)).2
    have hs2 : s ≤ N + 1 := hs.2
    linarith [h, hs2, hN]
  have hpin : ∀ t : ℝ, t ∈ Set.Icc N (N + 1) → L.γ₁ t = Function.invFunOn fl.Ψ
      {w : ℂ | w.re < -L.R} (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ t)) :=
    fun t ht => pointwise_pin d fl L (hwin t ht)
  set ε : ℝ := min (Metric.infDist u Λ) (Metric.infDist (u + 1) Λ) with hεdef
  have hε : 0 < ε := lt_min hd1 hd2
  obtain ⟨η, hηpos, hηlt, hfinW₁, hfinW₂⟩ :=
    levelSet_im_finite_small d fl L N hpin u.im hε
  have hη1 : η < Metric.infDist u Λ := lt_of_lt_of_le hηlt (min_le_left _ _)
  have hη2 : η < Metric.infDist (u + 1) Λ := lt_of_lt_of_le hηlt (min_le_right _ _)
  -- finiteness in the period at the shifted height
  have hper₁ : ∀ s : ℝ, (L.γ₁ (s + 1)).im = (L.γ₁ s).im := by
    intro s; rw [L.per₁ s]; simp
  have hper₂ : ∀ s : ℝ, (L.γ₂ (s + 1)).im = (L.γ₂ s).im := by
    intro s; rw [L.per₂ s]; simp
  have hf₁ : ({s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im + η}).Finite :=
    finite_levelSet_Ico_one_of_window hper₁ hfinW₁
  have hf₂ : ({s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im + η}).Finite :=
    finite_levelSet_Ico_one_of_window hper₂ hfinW₂
  -- the shifted point and the avoidance of the jogs
  have havoid1 : ∀ t ∈ Set.Icc (0 : ℝ) η,
      u + (t : ℂ) * Complex.I ∉ Λ := by
    intro t ht hmem
    have h1 : Metric.infDist u Λ ≤ ‖(u + (t : ℂ) * Complex.I) - u‖ := by
      simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := u) hmem
    have h2 : ‖(u + (t : ℂ) * Complex.I) - u‖ = |t| := by
      rw [show (u + (t : ℂ) * Complex.I) - u = (t : ℂ) * Complex.I by ring, norm_mul,
        Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have ht' : |t| ≤ η := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    linarith
  have havoid2 : ∀ t ∈ Set.Icc (0 : ℝ) η,
      (u + 1) + (t : ℂ) * Complex.I ∉ Λ := by
    intro t ht hmem
    have h1 : Metric.infDist (u + 1) Λ ≤ ‖((u + 1) + (t : ℂ) * Complex.I) - (u + 1)‖ := by
      simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := u + 1) hmem
    have h2 : ‖((u + 1) + (t : ℂ) * Complex.I) - (u + 1)‖ = |t| := by
      rw [show ((u + 1) + (t : ℂ) * Complex.I) - (u + 1) = (t : ℂ) * Complex.I by ring,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have ht' : |t| ≤ η := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    linarith
  -- the core at the shifted point
  set w : ℂ := u + (η : ℂ) * Complex.I with hw
  have hwre : w.re = u.re := by simp [hw]
  have hwim : w.im = u.im + η := by simp [hw]
  have hw1re : (w + 1).re = u.re + 1 := by
    have h1 : (w + 1).re = w.re + 1 := by simp
    rw [h1, hwre]
  have hwΛ : w ∉ Λ := by
    have := havoid1 η ⟨hηpos.le, le_rfl⟩
    simpa [hw] using this
  have hcore : fl.Ψ w ∈ Work.EL.pairSide P ↔ fl.Ψ (w + 1) ∈ Work.EL.pairSide P :=
    sidePreserve_core_of_crossing_parity d fl L P hPa hPb hPy hside hwΛ (by rw [hwre]; exact hu)
      (by linarith [hw1re, hu1]) (by rw [hwim]; exact hf₁) (by rw [hwim]; exact hf₂)
  -- the two jogs
  have h1 : fl.Ψ u ∈ Work.EL.pairSide P ↔ fl.Ψ w ∈ Work.EL.pairSide P := by
    have := side_eq_of_vertical_avoid L P hPa hPb hPy hside hηpos hu havoid1
    simpa [hw] using this
  have h2 : fl.Ψ (w + 1) ∈ Work.EL.pairSide P ↔ fl.Ψ (u + 1) ∈ Work.EL.pairSide P := by
    have h' := side_eq_of_vertical_avoid L P hPa hPb hPy hside (u := u + 1) (η := η) hηpos
      (by rw [Complex.add_re, Complex.one_re]; exact hu1) havoid2
    have hw1 : (u + 1) + (η : ℂ) * Complex.I = w + 1 := by rw [hw]; ring
    rw [hw1] at h'
    exact h'.symm
  exact h1.trans (hcore.trans h2)

/-! ## The target statement -/

/-- **Side preservation of the shift** (`Z1Nest.SP`, `NOTES_LEAD_mandelbar_residuals.md` §3.2 (d),
the ELNest field replacing the false `NestData.band`).  For `u` in the far-left half plane of the
repelling coordinate, `Ψ u` and `Ψ (u + 1) = F c (Ψ u)` lie in the same side of the `α`-pair. -/
theorem sidePreserve_core {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl)
    (P : Work.EL.CoPair d.hN) (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2)
    (hPy : P.y = d.z₁) (hside : Work.EL.PairSides d.hN P)
    (hPa_far : fl.Pa ⊆ Work.EL.pairSide P)
    (R : ℝ) (hR : L.R + 1 ≤ R) :
    ∀ u : ℂ, u.re < -R - 1 →
      (fl.Ψ u ∈ Work.EL.pairSide P ↔ fl.Ψ (u + 1) ∈ Work.EL.pairSide P) := by
  intro u hu
  have huR : u.re < -L.R := by linarith
  have hu1R : u.re + 1 < -L.R := by linarith
  by_cases huΛ : u ∈ Set.range L.γ₁ ∪ Set.range L.γ₂
  · exact sidePreserve_core_of_mem_lift L P hPa hPb hPy hside huR hu1R huΛ
  · by_cases hfin : (({s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im}).Finite ∧
        ({s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im}).Finite)
    · exact sidePreserve_core_of_crossing_parity d fl L P hPa hPb hPy hside huΛ huR hu1R
        hfin.1 hfin.2
    · exact sidePreserve_core_of_generic_levels L P hPa hPb hPy hside huΛ huR hu1R hfin

end Work.ELRig
