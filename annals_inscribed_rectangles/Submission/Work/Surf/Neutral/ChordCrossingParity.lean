import Mathlib
import Submission.Work.Drive.Surf.Model
import Submission.Work.Surf.chordMeet_finite
import Submission.Work.Surf.chordMeet_straight_odd
import Submission.Work.Surf.ncard_chordMeet_straightChord
import Submission.Work.Surf.defs
import Submission.Work.Surf.Neutral.ExistsGoodRayBoundaryOdd
import Submission.Work.Surf.even_ncard_zeros_add_boundary_ray

/-!
# (Neutral copy) `ChordCrossingParity`

Verbatim copy of the module `Work.Surf.ChordN.chord_crossing_parity` in the namespace `Work.Surf.ChordN`, with:

* every import of a module whose closure contains the declaration `Work.Drive.toC` of
  `Submission/Work/Drive/winding_eq_crossing_sum.lean` redirected to the neutral copy of that module
  (the only such channel is the import of `Submission/Work/Drive/line_crossings_even.lean`, replaced
  by `Submission/Work/Drive/Neutral/HalfDir.lean`);
* every qualified reference to the declarations of the neutral half-direction file
  (`halfDir`, `continuous_halfDir`, `halfDir_apply`, `halfDir_add_self`, `rescaleAngle`,
  `twoPiNeZero`, `toC`) redirected to `Work.Drive.NH`.

Reason: `Work.Drive.toC` is declared both in `Submission/Work/Drive/winding_eq_crossing_sum.lean` (in
the chord-parity world) and in `Submission/Work/Drive/UmlaufSetup.lean` (in the capping world), so the
two worlds cannot be imported together.  With these copies,
`Work.Surf.ChordN.chord_crossing_parity` — the strict base case of the mod-2 intersection form of
`ℝP²` — is importable next to `Work.Drive.CappingSpace`; see
`Submission/Work/Drive/cutTransportStrict.lean`.
-/
/-!
# Two chords of the disk cross an odd number of times

This is the base case of the mod-2 intersection form of `ℝP²`, in the disk model
(`Submission/Work/Drive/Surf/Model.lean`): a *chord* is a curve `a` with `IsChord a`
(`a (t+1) = -a t`, `‖a t‖ ≤ 1`, `a 0` on the unit circle), and
`chordMeet a b = {(s,t) ∈ (0,1)² : a s = b t}` is the count of crossings of the two 1-chains, i.e. the
mod-2 intersection number of the two essential loops of `ℝP²` that the chords represent.

## What is proved here (sorry-free)

* `Work.Surf.chordMeet_finite` — under `hint` (no crossing of `a` and `b` in `[0,1]²` has a parameter
  on the boundary, and `‖a s‖ < 1` at the crossings) and `htrans` (transversality of `a` and `b` at
  every crossing), the crossing set is finite: each crossing is an isolated zero of the map
  `(s,t) ↦ a s - b t` (inverse function theorem), and `hint` keeps the crossing set closed in the
  compact box `[0,1]²`.
* `Work.Surf.chordMeet_straight_odd` — if the second chord is the straight chord through a unit
  vector `w`, the count is odd: the crossing set is in bijection with the zero set of
  `s ↦ det2 (a s) w`, a `C¹` function with `φ 1 = -φ 0 ≠ 0` and only sign-changing zeros, so an odd
  number of zeros (`Work.Drive.odd_ncard_zeros_of_opposite_signs`).

## How the target is proved

The target `Work.Surf.ChordN.chord_crossing_parity` is reduced to the **mod-2 degree theorem** for the
difference map `F (s,t) = a s - b t` of the two chords, in the *cut (ray) form*:

* `Work.Surf.even_ncard_zeros_add_boundary_ray` — for a `C¹` map `F` on the square, zero-free on the
  boundary, with regular zeros, and meeting a ray `{r • v : 0 < r}` finitely often, transversally and
  away from the corners of the square: `#(zeros) + #(boundary ray-meetings)` is even (`F/‖F‖` theory:
  the interior count is the mod-2 degree, and the boundary count is the preimage count of the regular
  value `v/‖v‖`);
* `Work.Surf.ChordN.exists_good_ray_boundary_odd` — for two chords satisfying `hint` and `htrans` there is
  such a good direction `v` for which the boundary ray-meeting count is **odd** (the mod-2 degree of
  the boundary curve is computed by the linear homotopy to the pair of straight chords, where it is
  `±1`).

Together: `#(zeros of F in the square)` is odd, and `#(zeros)` is the number of crossings
`(chordMeet a b).ncard` (the bijection `(s,t) ↦` the point with coordinates `s, t`, using `hint` to
promote the box conditions to strict inequalities) — which is the statement.

The auxiliary lemmas in this file (`hasFDerivAt_chordMap`, `fderiv_chordMap_single_zero/one`,
`surjective_fderiv_chordMap`, `contDiff_chordMap`, `chordMap_ne_zero_on_bdry`,
`ncard_zeros_eq_chordMeet`) supply exactly the hypotheses of the two theorems above: `hint` gives
`F ≠ 0` on `∂□` and the strict interior conditions; `htrans` gives `det2 (deriv a s) (deriv b t) ≠ 0`
at the crossings, which is surjectivity of `fderiv ℝ F` there.
-/

namespace Work.Surf.ChordN

open Work.Drive.NH

open scoped Topology
open Set

noncomputable section

open Work.Drive

/-- The crossing set of two chords, as a subset of the closed square. -/
def chordBox (a b : ℝ → EuclideanSpace ℝ (Fin 2)) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ a p.1 = b p.2}

/-- Under `hint` the crossing set of two chords is its own set of parameters in the open square. -/
lemma chordMeet_eq_chordBox {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0 : ℝ) 1 ∧ t ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖a s‖ < 1) :
    chordMeet a b = chordBox a b := by
  ext p
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨le_of_lt h1.1, le_of_lt h1.2⟩, ⟨le_of_lt h2.1, le_of_lt h2.2⟩, h3⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨h1', h2', -⟩ := hint p.1 p.2 ⟨h1.1, h1.2⟩ ⟨h2.1, h2.2⟩ h3
    exact ⟨h1', h2', h3⟩


/-! ## The difference map of two curves and its derivative

For the assembly of the target we need the elementary facts about the map
`x ↦ a (x 0) - b (x 1)` on the plane: its smoothness, its derivative (which is surjective exactly
when `det2 (deriv a s) (deriv b t) ≠ 0`), and that it is zero-free on the boundary of the square
under `hint`. -/

/-- The derivative of `x ↦ f (x i)`. -/
lemma hasFDerivAt_comp_coordProj {f : ℝ → EuclideanSpace ℝ (Fin 2)} {s : ℝ} (i : Fin 2)
    (hf : HasDerivAt f (deriv f s) s) (x : EuclideanSpace ℝ (Fin 2)) (hx : x i = s) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => f (y i))
      (((1 : ℝ →L[ℝ] ℝ).smulRight (deriv f s)).comp (EuclideanSpace.proj i)) x := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => y i)
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) x := by
    simpa using (ContinuousLinearMap.hasFDerivAt
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ))
  have h2 : HasFDerivAt f ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv f s)) (x i) := by
    rw [hx]
    exact hf.hasFDerivAt
  exact h2.comp x h1

/-- The derivative of the difference map `x ↦ a (x 0) - b (x 1)`. -/
lemma hasFDerivAt_chordMap {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) (x : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => a (y 0) - b (y 1))
      ((((1 : ℝ →L[ℝ] ℝ).smulRight (deriv a (x 0))).comp (EuclideanSpace.proj (0 : Fin 2))) -
        (((1 : ℝ →L[ℝ] ℝ).smulRight (deriv b (x 1))).comp
          (EuclideanSpace.proj (1 : Fin 2)))) x := by
  have hda : HasDerivAt a (deriv a (x 0)) (x 0) :=
    ((ha.differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hdb : HasDerivAt b (deriv b (x 1)) (x 1) :=
    ((hb.differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hA := hasFDerivAt_comp_coordProj (f := a) 0 hda x rfl
  have hB := hasFDerivAt_comp_coordProj (f := b) 1 hdb x rfl
  exact hA.sub hB

/-- **Cramer's rule** for two vectors of the plane: `det2 A B • v = det2 v B • A + det2 A v • B`. -/
lemma det2_smul_cramer (A B v : EuclideanSpace ℝ (Fin 2)) :
    det2 A B • v = det2 v B • A + det2 A v • B := by
  ext i
  fin_cases i <;> simp [det2] <;> ring

/-- If `det2 A B ≠ 0` then `A` and `B` span the plane. -/
lemma span_pair_eq_top_of_det2_ne_zero {A B : EuclideanSpace ℝ (Fin 2)} (h : det2 A B ≠ 0) :
    Submodule.span ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun v => ?_
  have h2 : det2 A B • v = det2 v B • A + det2 A v • B := det2_smul_cramer A B v
  have hv : v = (det2 A B)⁻¹ • (det2 v B • A + det2 A v • B) := by
    rw [← h2, smul_smul, inv_mul_cancel₀ h, one_smul]
  rw [hv]
  exact Submodule.smul_mem _ _
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))

/-- The derivative of the difference map is surjective where `det2` does not vanish. -/
lemma surjective_fderiv_chordMap {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) {x : EuclideanSpace ℝ (Fin 2)}
    (h : det2 (deriv a (x 0)) (deriv b (x 1)) ≠ 0) :
    Function.Surjective (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => a (y 0) - b (y 1)) x) := by
  have hf := hasFDerivAt_chordMap ha hb x
  have hderiv : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => a (y 0) - b (y 1)) x
      = ((((1 : ℝ →L[ℝ] ℝ).smulRight (deriv a (x 0))).comp (EuclideanSpace.proj (0 : Fin 2))) -
        (((1 : ℝ →L[ℝ] ℝ).smulRight (deriv b (x 1))).comp
          (EuclideanSpace.proj (1 : Fin 2)))) := hf.fderiv
  have hA : deriv a (x 0) ∈ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
      a (y 0) - b (y 1)) x).range := by
    refine ⟨EuclideanSpace.single 0 1, ?_⟩
    rw [hderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  have hB : deriv b (x 1) ∈ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
      a (y 0) - b (y 1)) x).range := by
    refine ⟨-(EuclideanSpace.single 1 1), ?_⟩
    rw [hderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  have hsub : Submodule.span ℝ ({deriv a (x 0), deriv b (x 1)} :
      Set (EuclideanSpace ℝ (Fin 2))) ≤
      (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => a (y 0) - b (y 1)) x).range := by
    refine Submodule.span_le.mpr ?_
    rintro v (rfl | rfl)
    · exact hA
    · exact hB
  rw [span_pair_eq_top_of_det2_ne_zero h] at hsub
  intro v
  exact hsub Submodule.mem_top

/-- The difference map of two curves is `C¹`. -/
lemma contDiff_chordMap {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) :
    ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 2) => a (x 0) - b (x 1)) := by
  have h0 : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 2) => x 0) := by fun_prop
  have h1 : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin 2) => x 1) := by fun_prop
  exact (ha.comp h0).sub (hb.comp h1)

/-- Under `hint` the difference map of two chords is zero-free on the boundary of the square. -/
lemma chordMap_ne_zero_on_bdry {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0 : ℝ) 1 ∧ t ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖a s‖ < 1)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ sqBdry) :
    a (x 0) - b (x 1) ≠ 0 := by
  intro hzero
  have hbox : x ∈ sqBox := hx.1
  have heq : a (x 0) = b (x 1) := sub_eq_zero.mp hzero
  obtain ⟨h0, h1, -⟩ := hint (x 0) (x 1) hbox.1 hbox.2 heq
  rcases hx.2 with h | h | h | h
  · exact absurd h (ne_of_gt h0.1)
  · exact absurd h (ne_of_lt h0.2)
  · exact absurd h (ne_of_gt h1.1)
  · exact absurd h (ne_of_lt h1.2)

/-- The coordinates of a point of the plane, as a map to `ℝ × ℝ`. -/
lemma toLp_pair_injective :
    Function.Injective (fun p : ℝ × ℝ =>
      (WithLp.toLp 2 ![p.1, p.2] : EuclideanSpace ℝ (Fin 2))) := by
  intro p q hpq
  have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hpq
  have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hpq
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
  exact Prod.ext h0 h1

/-- The zeros of the difference map in the square are the crossings of the two chords. -/
lemma ncard_zeros_eq_chordMeet {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0 : ℝ) 1 ∧ t ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖a s‖ < 1) :
    ({x : EuclideanSpace ℝ (Fin 2) | x ∈ sqBox ∧ a (x 0) - b (x 1) = 0} :
        Set (EuclideanSpace ℝ (Fin 2))).ncard = (chordMeet a b).ncard := by
  have himg : ({x : EuclideanSpace ℝ (Fin 2) | x ∈ sqBox ∧ a (x 0) - b (x 1) = 0} :
      Set (EuclideanSpace ℝ (Fin 2))) =
      (fun p : ℝ × ℝ => (WithLp.toLp 2 ![p.1, p.2] : EuclideanSpace ℝ (Fin 2))) ''
        chordBox a b := by
    ext x
    constructor
    · rintro ⟨hx, hz⟩
      refine ⟨(x 0, x 1), ⟨hx.1, hx.2, sub_eq_zero.mp hz⟩, ?_⟩
      ext i
      fin_cases i <;>
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨hp.1, hp.2.1⟩, by
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        exact sub_eq_zero.mpr hp.2.2⟩
  rw [himg, Set.ncard_image_of_injective _ toLp_pair_injective, chordMeet_eq_chordBox hint]

/-- The derivative of the difference map in the `x 0` direction is `deriv a (x 0)`. -/
lemma fderiv_chordMap_single_zero {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) (x : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => a (y 0) - b (y 1)) x
      (EuclideanSpace.single 0 1) = deriv a (x 0) := by
  rw [(hasFDerivAt_chordMap ha hb x).fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]

/-- The derivative of the difference map in the `x 1` direction is `-deriv b (x 1)`. -/
lemma fderiv_chordMap_single_one {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) (x : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => a (y 0) - b (y 1)) x
      (EuclideanSpace.single 1 1) = -deriv b (x 1) := by
  rw [(hasFDerivAt_chordMap ha hb x).fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]

/-- `det2 (-u) v = -det2 u v`. -/
lemma det2_neg_left' {u v : EuclideanSpace ℝ (Fin 2)} : det2 (-u) v = -det2 u v := by
  rw [show (-u : EuclideanSpace ℝ (Fin 2)) = (-1 : ℝ) • u from by simp, det2_smul_left]
  ring

/-- **Two chords of the disk cross an odd number of times** (the base case of the mod-2 intersection
form of `ℝP²`). -/
theorem chord_crossing_parity {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (ha : Work.Drive.IsChord a) (hb : Work.Drive.IsChord b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0 : ℝ) 1 ∧ t ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖a s‖ < 1)
    (htrans : ∀ s t : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 → t ∈ Set.Ioo (0 : ℝ) 1 → a s = b t →
      Work.Drive.det2 (deriv a s) (deriv b t) ≠ 0) :
    Odd (Work.Drive.chordMeet a b).ncard := by
  classical
  have hda : ContDiff ℝ 1 a := ha.contDiff
  have hdb : ContDiff ℝ 1 b := hb.contDiff
  -- the good ray direction, with the boundary count odd
  obtain ⟨v, hv, hbig, hfin, hcorner, htrans_bdry, hodd⟩ :=
    exists_good_ray_boundary_odd ha hb hint htrans
  -- regularity of the zeros of the difference map
  have hreg : ∀ x ∈ sqBox, a (x 0) - b (x 1) = 0 →
      Function.Surjective (fderiv ℝ
        (fun y : EuclideanSpace ℝ (Fin 2) => a (y 0) - b (y 1)) x) := by
    intro x hx hzero
    refine surjective_fderiv_chordMap hda hdb ?_
    have heq : a (x 0) = b (x 1) := sub_eq_zero.mp hzero
    obtain ⟨h0, h1, -⟩ := hint (x 0) (x 1) hx.1 hx.2 heq
    exact htrans (x 0) (x 1) h0 h1 heq
  -- the boundary transversality in the form the cut theorem wants
  have htb : ∀ x ∈ sqBdry, (∃ r : ℝ, 0 < r ∧ a (x 0) - b (x 1) = r • v) →
      ((x 1 = 0 ∨ x 1 = 1) →
        det2 (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => a (y 0) - b (y 1)) x
          (EuclideanSpace.single 0 1)) v ≠ 0) ∧
      ((x 0 = 0 ∨ x 0 = 1) →
        det2 (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => a (y 0) - b (y 1)) x
          (EuclideanSpace.single 1 1)) v ≠ 0) := by
    intro x hx hmem
    refine ⟨fun h1 => ?_, fun h0 => ?_⟩
    · rw [fderiv_chordMap_single_zero hda hdb x]
      exact (htrans_bdry x hx hmem).1 h1
    · rw [fderiv_chordMap_single_one hda hdb x, det2_neg_left']
      exact fun h => (htrans_bdry x hx hmem).2 h0 (neg_eq_zero.mp h)
  -- the cut theorem
  have hcut := even_ncard_zeros_add_boundary_ray
    (fun x : EuclideanSpace ℝ (Fin 2) => a (x 0) - b (x 1))
    (contDiff_chordMap hda hdb)
    (fun x hx => chordMap_ne_zero_on_bdry hint hx)
    hreg hv hbig hcorner htb hfin
  -- identify the zeros with the crossings
  rw [ncard_zeros_eq_chordMeet hint] at hcut
  -- and conclude from `Even (N + M)`, `Odd M`
  rw [← Nat.not_even_iff_odd]
  intro hN
  exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_add.mp hcut).mp hN)

end

end Work.Surf.ChordN
