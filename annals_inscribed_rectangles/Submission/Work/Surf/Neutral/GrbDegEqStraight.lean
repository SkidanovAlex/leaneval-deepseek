import Mathlib
import Submission.Work.Surf.Neutral.GrbLevel
import Submission.Work.Surf.chordFamily
import Submission.Work.Drive.winding_of_homotopy

/-!
# (Neutral copy) `GrbDegEqStraight`

Verbatim copy of the module `Work.Surf.ChordN.grbDeg_eq_straight` in the namespace `Work.Surf.ChordN`, with:

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
# The honest degree of the boundary curve is invariant under straightening the chords

`Work.Surf.ChordN.grbDeg a b` is the honest degree (cf. `Work.Surf.grbLevel`) of the boundary curve
`u ↦ grbCurve a b u = a (s u) - b (t u)` of the difference map of the two chords `a`, `b`.  The
statement is that straightening each of the two chords to the diameter through its own endpoint does
not change this degree:

`grbDeg a b = grbDeg (straightChord (a 0)) (straightChord (b 0))`.

The two straightenings are performed one after the other, each as the linear family
`chordHom a (a 0) τ` of `Work.Surf.chordFamily`.  The two ingredients are:

* the family of boundary curves, a continuous family of closed curves avoiding the origin — this is
  exactly the content of `Work.Surf.chordDiff_ne_zero_of_sface` / `_tface`, which say that the
  difference map of the family has no zeros on the `s`- and `t`-faces of the cube;
* homotopy invariance of the winding number, `Work.Drive.winding_of_homotopy`.

The honest degree is half of the (doubled) winding number about the origin
(`Work.Surf.ChordN.winding_eq_two_mul_degree_halfDir`), so the equality of the winding numbers gives the
equality of the degrees.

## The circle-lifting lemma

The family of curves is naturally a map on `[0,1] × ℝ`, periodic in the second coordinate; to obtain
a genuine homotopy of circle maps we descend it along the covering `ℝ → ℝ/ℤ`.  This is
`Work.Surf.ChordN.exists_continuous_lift_circle`, a general statement (the descent of a continuous
`1`-periodic family along a quotient map, `IsQuotientMap.continuous_lift_prod_right`).
-/

namespace Work.Surf.ChordN

open Work.Drive.NH

open Work.Surf Work.Surf.GRB Work.Drive

open scoped Topology

noncomputable section

/-! ## Descending a periodic family to the circle -/

/-- **A continuous family `F : X × ℝ → Z` of period `1` in the second variable descends to the
circle.**  There is a continuous `G : X × ℝ/ℤ → Z` with `G (x, s) = F (x, s)` for every real `s`.

This is the general form of the (noncomputable) map `AddCircle.liftIco 1 0`; the point here is the
*joint* continuity in `x`, which follows from the universal property of the quotient map
`ℝ → ℝ/ℤ` (`Topology.IsQuotientMap.continuous_lift_prod_right`). -/
lemma exists_continuous_lift_circle {X Z : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [TopologicalSpace Z] {F : X × ℝ → Z} (hF : Continuous F) (hper : ∀ x s, F (x, s + 1) = F (x, s)) :
    ∃ G : C(X × UnitAddCircle, Z), ∀ (x : X) (s : ℝ), G (x, (s : UnitAddCircle)) = F (x, s) := by
  have hq : Topology.IsQuotientMap ((↑) : ℝ → UnitAddCircle) :=
    (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1:ℝ))).isQuotientMap
  have hcoe : ∀ (x : X) (s : ℝ),
      AddCircle.liftIco 1 0 (fun y : ℝ => F (x, y)) (s : UnitAddCircle) = F (x, s) := by
    intro x s
    have hrI : s - (⌊s⌋ : ℝ) ∈ Set.Ico (0:ℝ) 1 :=
      ⟨sub_nonneg.mpr (Int.floor_le s), by linarith [Int.lt_floor_add_one s]⟩
    have hcoe_eq : ((s : ℝ) : UnitAddCircle) = ((s - (⌊s⌋ : ℝ) : ℝ) : UnitAddCircle) := by
      rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
      refine ⟨⌊s⌋, ?_⟩
      simp only [zsmul_eq_mul, mul_one]
      ring
    rw [hcoe_eq, AddCircle.liftIco_zero_coe_apply hrI]
    have hper' : Function.Periodic (fun y : ℝ => F (x, y)) (1:ℝ) := fun y => hper x y
    have h2 := (hper'.int_mul ⌊s⌋) (s - (⌊s⌋:ℝ))
    simp only [mul_one] at h2
    rw [show s - (⌊s⌋ : ℝ) + (⌊s⌋ : ℝ) = s by ring] at h2
    exact h2.symm
  refine ⟨⟨fun p => AddCircle.liftIco 1 0 (fun y : ℝ => F (p.1, y)) p.2, ?_⟩,
    fun x s => hcoe x s⟩
  refine hq.continuous_lift_prod_right (g := fun p : X × UnitAddCircle =>
    AddCircle.liftIco 1 0 (fun y : ℝ => F (p.1, y)) p.2) ?_
  have hfun : (fun p : X × ℝ => AddCircle.liftIco 1 0 (fun y : ℝ => F (p.1, y))
      (p.2 : UnitAddCircle)) = F := by
    funext p
    exact hcoe p.1 p.2
  rw [hfun]
  exact hF

/-! ## The degree and the winding number depend only on the function -/

/-- The degree of a circle map does not depend on the proof of continuity. -/
lemma degree_eq_of_eq_fun {f g : UnitAddCircle → UnitAddCircle} (h : f = g)
    (hf : Continuous f) (hg : Continuous g) : degree f hf = degree g hg := by
  subst h
  exact congrArg (fun p => degree f p) (Subsingleton.elim hf hg)

/-- The winding number of a plane curve depends only on the curve (and on the point). -/
lemma winding_eq_of_eq_fun {γ γ' : UnitAddCircle → ℝ × ℝ} (h : γ = γ') (hγ : Continuous γ)
    (hγ' : Continuous γ') {p : ℝ × ℝ} (hp : p ∉ Set.range γ) (hp' : p ∉ Set.range γ') :
    winding γ hγ hp = winding γ' hγ' hp' := by
  subst h
  have key : dirCurve γ hγ p hp = dirCurve γ hγ p hp' := by
    funext t
    exact congrArg dirP (Subtype.ext rfl)
  exact degree_eq_of_eq_fun key _ _

/-! ## The straightening families of the two chords -/

/-- The coordinates `(τ, s, t)` of the cube `[0,1]³` of the straightening family, as a point of
`Work.Drive.Amb 2 = 𝔼³`. -/
def tri3 (τ s t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![τ, s, t]

lemma tri3_apply_zero (τ s t : ℝ) : (tri3 τ s t).ofLp 0 = τ := by simp [tri3]

lemma tri3_apply_one (τ s t : ℝ) : (tri3 τ s t).ofLp 1 = s := by simp [tri3]

lemma tri3_apply_two (τ s t : ℝ) : (tri3 τ s t).ofLp 2 = t := by simp [tri3]

lemma chordDiff_tri3 (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (τ s t : ℝ) :
    chordDiff a c (tri3 τ s t) = chordHom a (a 0) τ s - c t := by
  rw [chordDiff_eq, tri3_apply_zero, tri3_apply_one, tri3_apply_two]

lemma grbDiff_eq_gEu_chordDiff (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (τ s t : ℝ) :
    grbDiff (chordHom a (a 0) τ) c (s, t) = gEu (chordDiff a c (tri3 τ s t)) := by
  rw [chordDiff_tri3, map_sub, grbDiff]

lemma mem_unitBox_tri3 (x : unitInterval) {p : ℝ × ℝ} (hp : p ∈ Work.Drive.sqBox) :
    tri3 (x : ℝ) p.1 p.2 ∈ Submission.Drive.unitBox 2 := by
  intro i
  fin_cases i
  · simp [tri3, x.2]
  · simp [tri3, hp.1]
  · simp [tri3, hp.2]

/-- The straightening family of the first chord: the curve `u ↦ chordHom a (a 0) τ (s u) − c (t u)`
of the difference map of the family member `chordHom a (a 0) τ` against the fixed chord `c`. -/
def straightFamA (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (z : unitInterval × ℝ) : ℝ × ℝ :=
  grbDiff (chordHom a (a 0) (z.1 : ℝ)) c (sqPar z.2)

lemma straightFamA_eq_gEu (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (x : unitInterval) (s : ℝ) :
    straightFamA a c (x, s) = gEu (chordDiff a c (tri3 (x : ℝ) (sqPar s).1 (sqPar s).2)) :=
  grbDiff_eq_gEu_chordDiff a c (x : ℝ) (sqPar s).1 (sqPar s).2

/-- The straightening family of the second chord: the curve
`u ↦ a (s u) − chordHom c (c 0) τ (t u)` of the difference map of the fixed chord `a` against the
family member `chordHom c (c 0) τ`. -/
def straightFamB (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (z : unitInterval × ℝ) : ℝ × ℝ :=
  grbDiff a (chordHom c (c 0) (z.1 : ℝ)) (sqPar z.2)

lemma straightFamA_period (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (x : unitInterval) (s : ℝ) :
    straightFamA a c (x, s + 1) = straightFamA a c (x, s) := by
  simp only [straightFamA, sqPar_add_one]

lemma straightFamB_period (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (x : unitInterval) (s : ℝ) :
    straightFamB a c (x, s + 1) = straightFamB a c (x, s) := by
  simp only [straightFamB, sqPar_add_one]

lemma continuous_straightFamA (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hc : ContDiff ℝ 1 c) : Continuous (straightFamA a c) := by
  have hsq : Continuous fun z : unitInterval × ℝ => sqPar z.2 :=
    contDiff_sqPar.continuous.comp continuous_snd
  have hτ : Continuous fun z : unitInterval × ℝ => (z.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have ha1 : Continuous fun z : unitInterval × ℝ => a (sqPar z.2).1 := ha.continuous.comp hsq.fst
  have hc1 : Continuous fun z : unitInterval × ℝ => c (sqPar z.2).2 := hc.continuous.comp hsq.snd
  have hcos : Continuous fun z : unitInterval × ℝ => Real.cos (Real.pi * (sqPar z.2).1) :=
    Real.continuous_cos.comp (continuous_const.mul hsq.fst)
  have h1 : Continuous fun z : unitInterval × ℝ =>
      gEu ((1 - (z.1:ℝ)) • a (sqPar z.2).1
        + (z.1:ℝ) • (Real.cos (Real.pi * (sqPar z.2).1) • a 0)) :=
    gEu.continuous.comp
      (((continuous_const.sub hτ).smul ha1).add (hτ.smul (hcos.smul continuous_const)))
  have h2 : Continuous fun z : unitInterval × ℝ => gEu (c (sqPar z.2).2) := gEu.continuous.comp hc1
  have hfun : (fun z : unitInterval × ℝ => gEu ((1 - (z.1:ℝ)) • a (sqPar z.2).1
        + (z.1:ℝ) • (Real.cos (Real.pi * (sqPar z.2).1) • a 0)) - gEu (c (sqPar z.2).2))
      = straightFamA a c := by
    funext z
    simp only [straightFamA, grbDiff, chordHom]
  rw [← hfun]
  exact h1.sub h2

lemma continuous_straightFamB (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hc : ContDiff ℝ 1 c) : Continuous (straightFamB a c) := by
  have hsq : Continuous fun z : unitInterval × ℝ => sqPar z.2 :=
    contDiff_sqPar.continuous.comp continuous_snd
  have hτ : Continuous fun z : unitInterval × ℝ => (z.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have ha1 : Continuous fun z : unitInterval × ℝ => a (sqPar z.2).1 := ha.continuous.comp hsq.fst
  have hc1 : Continuous fun z : unitInterval × ℝ => c (sqPar z.2).2 := hc.continuous.comp hsq.snd
  have hcos : Continuous fun z : unitInterval × ℝ => Real.cos (Real.pi * (sqPar z.2).2) :=
    Real.continuous_cos.comp (continuous_const.mul hsq.snd)
  have h2 : Continuous fun z : unitInterval × ℝ =>
      gEu ((1 - (z.1:ℝ)) • c (sqPar z.2).2
        + (z.1:ℝ) • (Real.cos (Real.pi * (sqPar z.2).2) • c 0)) :=
    gEu.continuous.comp
      (((continuous_const.sub hτ).smul hc1).add (hτ.smul (hcos.smul continuous_const)))
  have h1 : Continuous fun z : unitInterval × ℝ => gEu (a (sqPar z.2).1) := gEu.continuous.comp ha1
  have hfun : (fun z : unitInterval × ℝ => gEu (a (sqPar z.2).1) - gEu ((1 - (z.1:ℝ)) • c (sqPar z.2).2
        + (z.1:ℝ) • (Real.cos (Real.pi * (sqPar z.2).2) • c 0))) = straightFamB a c := by
    funext z
    simp only [straightFamB, grbDiff, chordHom]
  rw [← hfun]
  exact h1.sub h2

/-- The straightening family of the first chord, as a homotopy of circle curves. -/
noncomputable def straightLiftA (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hc : ContDiff ℝ 1 c) : C(unitInterval × UnitAddCircle, ℝ × ℝ) :=
  (exists_continuous_lift_circle (continuous_straightFamA a c ha hc) (straightFamA_period a c)).choose

lemma straightLiftA_apply (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hc : ContDiff ℝ 1 c) (x : unitInterval) (s : ℝ) :
    straightLiftA a c ha hc (x, (s : UnitAddCircle)) = straightFamA a c (x, s) :=
  (exists_continuous_lift_circle (continuous_straightFamA a c ha hc)
    (straightFamA_period a c)).choose_spec x s

/-- The straightening family of the second chord, as a homotopy of circle curves. -/
noncomputable def straightLiftB (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hc : ContDiff ℝ 1 c) : C(unitInterval × UnitAddCircle, ℝ × ℝ) :=
  (exists_continuous_lift_circle (continuous_straightFamB a c ha hc) (straightFamB_period a c)).choose

lemma straightLiftB_apply (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hc : ContDiff ℝ 1 c) (x : unitInterval) (s : ℝ) :
    straightLiftB a c ha hc (x, (s : UnitAddCircle)) = straightFamB a c (x, s) :=
  (exists_continuous_lift_circle (continuous_straightFamB a c ha hc)
    (straightFamB_period a c)).choose_spec x s

/-! ## The two end curves of each family -/

lemma straightFamA_zero (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (u : ℝ) :
    straightFamA a c (0, u) = grbCurve a c (u : UnitAddCircle) := by
  have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have hch : chordHom a (a 0) (0:ℝ) = a := by funext s; exact chordHom_zero a (a 0) s
  rw [straightFamA, h0, hch]
  exact (grbCurve_coe a c u).symm

lemma straightFamA_one (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (u : ℝ) :
    straightFamA a c (1, u) = grbCurve (straightChord (a 0)) c (u : UnitAddCircle) := by
  have h0 : ((1 : unitInterval) : ℝ) = 1 := rfl
  have hch : chordHom a (a 0) (1:ℝ) = straightChord (a 0) := by
    funext s; exact chordHom_one a (a 0) s
  rw [straightFamA, h0, hch]
  exact (grbCurve_coe (straightChord (a 0)) c u).symm

lemma straightFamB_zero (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (u : ℝ) :
    straightFamB a c (0, u) = grbCurve a c (u : UnitAddCircle) := by
  have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have hch : chordHom c (c 0) (0:ℝ) = c := by funext s; exact chordHom_zero c (c 0) s
  rw [straightFamB, h0, hch]
  exact (grbCurve_coe a c u).symm

lemma straightFamB_one (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (u : ℝ) :
    straightFamB a c (1, u) = grbCurve a (straightChord (c 0)) (u : UnitAddCircle) := by
  have h0 : ((1 : unitInterval) : ℝ) = 1 := rfl
  have hch : chordHom c (c 0) (1:ℝ) = straightChord (c 0) := by
    funext s; exact chordHom_one c (c 0) s
  rw [straightFamB, h0, hch]
  exact (grbCurve_coe a (straightChord (c 0)) u).symm

lemma straightLiftA_zero (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hc : ContDiff ℝ 1 c) (u : UnitAddCircle) :
    straightLiftA a c ha hc (0, u) = grbCurve a c u := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep u
  rw [← hs, straightLiftA_apply, straightFamA_zero]

lemma straightLiftA_one (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hc : ContDiff ℝ 1 c) (u : UnitAddCircle) :
    straightLiftA a c ha hc (1, u) = grbCurve (straightChord (a 0)) c u := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep u
  rw [← hs, straightLiftA_apply, straightFamA_one]

lemma straightLiftB_zero (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hc : ContDiff ℝ 1 c) (u : UnitAddCircle) :
    straightLiftB a c ha hc (0, u) = grbCurve a c u := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep u
  rw [← hs, straightLiftB_apply, straightFamB_zero]

lemma straightLiftB_one (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hc : ContDiff ℝ 1 c) (u : UnitAddCircle) :
    straightLiftB a c ha hc (1, u) = grbCurve a (straightChord (c 0)) u := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep u
  rw [← hs, straightLiftB_apply, straightFamB_one]

/-! ## The families avoid the origin on the square's boundary -/

/-- A chord's straightening family against another chord avoids the origin on the boundary of the
square, provided no intersection of the two chords lies on that boundary.  This is
`Work.Surf.chordDiff_ne_zero_of_sface` and `Work.Surf.chordDiff_ne_zero_of_tface` in the
coordinates `(τ, s, t) = (x 0, (sqPar u).1, (sqPar u).2)`. -/
lemma straightFamA_ne_zero (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : Work.Drive.IsChord a)
    (hc : Work.Drive.IsChord c)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = c t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1)
    (x : unitInterval) (u : ℝ) : straightFamA a c (x, u) ≠ 0 := by
  intro h0
  have hz : gEu (chordDiff a c (tri3 (x:ℝ) (sqPar u).1 (sqPar u).2))
      = gEu (0 : EuclideanSpace ℝ (Fin 2)) := by
    rw [map_zero]
    rwa [straightFamA_eq_gEu] at h0
  have hcd : chordDiff a c (tri3 (x:ℝ) (sqPar u).1 (sqPar u).2) = 0 := gEu_eq_iff.mp hz
  have hp := sqPar_mem_sqBoxBdry u
  have hx' : tri3 (x:ℝ) (sqPar u).1 (sqPar u).2 ∈ Submission.Drive.unitBox 2 :=
    mem_unitBox_tri3 x hp.1
  rcases hp.2 with h | h | h | h
  · exact chordDiff_ne_zero_of_sface a c ha hc hint hx'
      (Or.inl (by rw [tri3_apply_one]; exact h)) hcd
  · exact chordDiff_ne_zero_of_sface a c ha hc hint hx'
      (Or.inr (by rw [tri3_apply_one]; exact h)) hcd
  · exact chordDiff_ne_zero_of_tface a c ha hc hint hx'
      (Or.inl (by rw [tri3_apply_two]; exact h)) hcd
  · exact chordDiff_ne_zero_of_tface a c ha hc hint hx'
      (Or.inr (by rw [tri3_apply_two]; exact h)) hcd

lemma straightFamB_eq_neg_gEu (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (x : unitInterval) (s : ℝ) :
    straightFamB a c (x, s)
      = - gEu (chordDiff c a (tri3 (x : ℝ) (sqPar s).2 (sqPar s).1)) := by
  rw [straightFamB, chordDiff_tri3, map_sub, grbDiff]
  abel

/-- The same for the straightening of the *second* chord: the roles of `s` and `t` are exchanged,
which is why the `s`- and `t`-face statements are applied in the opposite order. -/
lemma straightFamB_ne_zero (a c : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : Work.Drive.IsChord a)
    (hc : Work.Drive.IsChord c)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → c s = a t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1)
    (x : unitInterval) (u : ℝ) : straightFamB a c (x, u) ≠ 0 := by
  intro h0
  have hcd : chordDiff c a (tri3 (x:ℝ) (sqPar u).2 (sqPar u).1) = 0 := by
    have h1 : - gEu (chordDiff c a (tri3 (x:ℝ) (sqPar u).2 (sqPar u).1)) = 0 := by
      rw [← straightFamB_eq_neg_gEu]; exact h0
    have h2 : gEu (chordDiff c a (tri3 (x:ℝ) (sqPar u).2 (sqPar u).1)) = 0 := neg_eq_zero.mp h1
    have h3 : gEu (chordDiff c a (tri3 (x:ℝ) (sqPar u).2 (sqPar u).1))
        = gEu (0 : EuclideanSpace ℝ (Fin 2)) := by rw [map_zero]; exact h2
    exact gEu_eq_iff.mp h3
  have hp := sqPar_mem_sqBoxBdry u
  have hx' : tri3 (x:ℝ) (sqPar u).2 (sqPar u).1 ∈ Submission.Drive.unitBox 2 :=
    mem_unitBox_tri3 x (p := ((sqPar u).2, (sqPar u).1)) ⟨hp.1.2, hp.1.1⟩
  rcases hp.2 with h | h | h | h
  · exact chordDiff_ne_zero_of_tface c a hc ha hint hx'
      (Or.inl (by rw [tri3_apply_two]; exact h)) hcd
  · exact chordDiff_ne_zero_of_tface c a hc ha hint hx'
      (Or.inr (by rw [tri3_apply_two]; exact h)) hcd
  · exact chordDiff_ne_zero_of_sface c a hc ha hint hx'
      (Or.inl (by rw [tri3_apply_one]; exact h)) hcd
  · exact chordDiff_ne_zero_of_sface c a hc ha hint hx'
      (Or.inr (by rw [tri3_apply_one]; exact h)) hcd

/-! ## The no-collision hypothesis of the intermediate pair -/

/-- `|cos (π t)| < 1` for `t ∈ (0,1)`, by strict antitonicity of the cosine on `[0, π]`. -/
lemma abs_cos_pi_mul_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    |Real.cos (Real.pi * t)| < 1 := by
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have ht0 : 0 < Real.pi * t := mul_pos hpi0 h0
  have htp : Real.pi * t < Real.pi := by nlinarith
  have hlt1 : Real.cos (Real.pi * t) < 1 := by
    have := Real.strictAntiOn_cos (show (0:ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_refl _, Real.pi_pos.le⟩)
      (show Real.pi * t ∈ Set.Icc 0 Real.pi from ⟨ht0.le, htp.le⟩) ht0
    rwa [Real.cos_zero] at this
  have hlt2 : -1 < Real.cos (Real.pi * t) := by
    have := Real.strictAntiOn_cos (show Real.pi * t ∈ Set.Icc 0 Real.pi from ⟨ht0.le, htp.le⟩)
      (show Real.pi ∈ Set.Icc 0 Real.pi from ⟨Real.pi_pos.le, le_refl _⟩) htp
    rwa [Real.cos_pi] at this
  rw [abs_lt]; exact ⟨hlt2, hlt1⟩

/-- **The collision hypothesis against the straightened second chord.**  If `a s = cos (π t) • b 0`
with `s, t ∈ [0,1]`, then `s` and `t` are interior and `a s` is strictly inside the disk: on the
faces `t ∈ {0,1}` the collision is forbidden by the hypothesis `hint` for the pair `(a, b)`, and on
the faces `s ∈ {0,1}` it is forbidden by the norm (`‖a 0‖ = ‖a 1‖ = 1` against
`‖cos (π t) • b 0‖ = |cos (π t)| < 1`). -/
lemma hint_straight (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : Work.Drive.IsChord a)
    (hb : Work.Drive.IsChord b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1)
    {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (heq : a s = Work.Drive.straightChord (b 0) t) :
    s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1 := by
  have hb0 : ‖b 0‖ = 1 := hb.start
  have hb1 : b 1 = - b 0 := by
    have h := hb.periodic 0
    rw [zero_add] at h
    rw [h, Work.Drive.antipode_apply]
  have hnorm_eq : ‖a s‖ = |Real.cos (Real.pi * t)| := by
    have h := congrArg Norm.norm heq
    rw [Work.Drive.straightChord, norm_smul, Real.norm_eq_abs, hb0, mul_one] at h
    exact h
  have ht0 : t ≠ 0 := by
    intro h
    have hb' : a s = b 0 := by rw [heq, h, Work.Drive.straightChord_zero]
    exact absurd (hint s 0 hs (by norm_num) hb').2.1.1 (lt_irrefl 0)
  have ht1 : t ≠ 1 := by
    intro h
    have hb' : a s = b 1 := by rw [heq, h, Work.Drive.straightChord_one, hb1]
    exact absurd (hint s 1 hs (by norm_num) hb').2.1.2 (lt_irrefl 1)
  have htI : t ∈ Set.Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  have hcos := abs_cos_pi_mul_lt_one htI.1 htI.2
  have hs0 : s ≠ 0 := by
    intro h
    have h2 : ‖a 0‖ = |Real.cos (Real.pi * t)| := by simpa [h] using hnorm_eq
    rw [ha.start] at h2
    exact absurd (h2 ▸ hcos) (lt_irrefl _)
  have hs1 : s ≠ 1 := by
    intro h
    have h2 : ‖a 1‖ = |Real.cos (Real.pi * t)| := by simpa [h] using hnorm_eq
    rw [ha.end] at h2
    exact absurd (h2 ▸ hcos) (lt_irrefl _)
  exact ⟨⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hs1⟩, htI,
    by rw [hnorm_eq]; exact hcos⟩

/-! ## The winding number of the boundary curve is twice the honest degree -/

lemma grbCurve_not_mem_zero {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1) :
    (0 : ℝ × ℝ) ∉ Set.range (grbCurve a b) := by
  rintro ⟨u, hu⟩
  obtain ⟨s, hs⟩ := Quotient.exists_rep u
  rw [← hs] at hu
  exact grbCurve_ne_zero hint hu

/-- **The doubling formula for the honest degree**: the winding number of the boundary curve is
twice `grbDeg`. -/
lemma two_mul_grbDeg_eq_winding {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1) :
    2 * grbDeg a b ha hb hint
      = winding (grbCurve a b) (continuous_grbCurve a b ha hb) (grbCurve_not_mem_zero hint) := by
  have key := winding_eq_two_mul_degree_halfDir (grbCurve a b) (continuous_grbCurve a b ha hb)
    (grbCurve_not_mem_zero hint)
  have hdeg : degree (halfDir (grbCurve a b) 0)
      (continuous_halfDir (grbCurve a b) (continuous_grbCurve a b ha hb) (grbCurve_not_mem_zero hint))
      = grbDeg a b ha hb hint := by
    rw [grbDeg]
    exact degree_eq_of_eq_fun rfl _ _
  rw [hdeg] at key
  exact key.symm

/-! ## The main theorem -/
/-- The workhorse form of `grbDeg_eq_straight`, with the two smoothness proofs of the chords
passed explicitly (so that the statement can be instantiated with the very terms appearing in the
target). -/
theorem grbDeg_eq_straight_aux (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (haC : ContDiff ℝ 1 a)
    (hbC : ContDiff ℝ 1 b) (ha : Work.Drive.IsChord a) (hb : Work.Drive.IsChord b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1)
    (hintS : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
      Work.Drive.straightChord (a 0) s = Work.Drive.straightChord (b 0) t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖Work.Drive.straightChord (a 0) s‖ < 1) :
    Work.Surf.ChordN.grbDeg a b haC hbC hint =
      Work.Surf.ChordN.grbDeg (Work.Drive.straightChord (a 0)) (Work.Drive.straightChord (b 0))
        (Work.Drive.straightChord_isChord ha.start).contDiff
        (Work.Drive.straightChord_isChord hb.start).contDiff hintS := by
  have ha'C : ContDiff ℝ 1 (straightChord (a 0)) := (straightChord_isChord ha.start).contDiff
  have hb'C : ContDiff ℝ 1 (straightChord (b 0)) := (straightChord_isChord hb.start).contDiff
  have ha' : Work.Drive.IsChord (straightChord (a 0)) := straightChord_isChord ha.start
  have hb' : Work.Drive.IsChord (straightChord (b 0)) := straightChord_isChord hb.start
  -- the two no-collision hypotheses needed for the intermediate curves
  have hint_ba : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → b s = a t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 :=
    fun s t hs ht h => ⟨(hint t s ht hs h.symm).2.1, (hint t s ht hs h.symm).1⟩
  have hint3 : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
      a s = straightChord (b 0) t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1 :=
    fun s t hs ht h => hint_straight a b ha hb hint hs ht h
  have hint2 : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
      a s = straightChord (b 0) t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 :=
    fun s t hs ht h => ⟨(hint3 s t hs ht h).1, (hint3 s t hs ht h).2.1⟩
  --##### step 1: straightening the second chord, the first one fixed
  have hp1 : ∀ x : unitInterval, (0 : ℝ × ℝ) ∉ Set.range
      (fun u : UnitAddCircle => straightLiftB a b haC hbC (x, u)) := by
    intro x
    rintro ⟨u, hu⟩
    obtain ⟨s, hs⟩ := Quotient.exists_rep u
    rw [← hs] at hu
    beta_reduce at hu
    rw [straightLiftB_apply] at hu
    exact straightFamB_ne_zero a b ha hb hint_ba x s hu
  have hstep1 : winding (grbCurve a b) (continuous_grbCurve a b haC hbC)
        (grbCurve_not_mem_zero hint)
      = winding (grbCurve a (straightChord (b 0)))
          (continuous_grbCurve a (straightChord (b 0)) haC hb'C)
          (grbCurve_not_mem_zero hint3) := by
    have hF0 : Continuous (fun u : UnitAddCircle => straightLiftB a b haC hbC (0, u)) := by
      rw [show (fun u : UnitAddCircle => straightLiftB a b haC hbC (0, u)) = grbCurve a b from
        funext (straightLiftB_zero a b haC hbC)]
      exact continuous_grbCurve a b haC hbC
    have hF1 : Continuous (fun u : UnitAddCircle => straightLiftB a b haC hbC (1, u)) := by
      rw [show (fun u : UnitAddCircle => straightLiftB a b haC hbC (1, u))
        = grbCurve a (straightChord (b 0)) from funext (straightLiftB_one a b haC hbC)]
      exact continuous_grbCurve a (straightChord (b 0)) haC hb'C
    have hhom := winding_of_homotopy_aux (Φ := straightLiftB a b haC hbC) hp1 hF0 hF1
    have e0 : winding (fun u : UnitAddCircle => straightLiftB a b haC hbC (0, u)) hF0 (hp1 0)
        = winding (grbCurve a b) (continuous_grbCurve a b haC hbC)
            (grbCurve_not_mem_zero hint) :=
      winding_eq_of_eq_fun (funext (straightLiftB_zero a b haC hbC)) hF0 _ (hp1 0) _
    have e1 : winding (fun u : UnitAddCircle => straightLiftB a b haC hbC (1, u)) hF1 (hp1 1)
        = winding (grbCurve a (straightChord (b 0)))
            (continuous_grbCurve a (straightChord (b 0)) haC hb'C)
            (grbCurve_not_mem_zero hint3) :=
      winding_eq_of_eq_fun (funext (straightLiftB_one a b haC hbC)) hF1 _ (hp1 1) _
    exact e0.symm.trans (hhom.trans e1)
  --##### step 2: straightening the first chord, the second one already straight
  have hp2 : ∀ x : unitInterval, (0 : ℝ × ℝ) ∉ Set.range
      (fun u : UnitAddCircle => straightLiftA a (straightChord (b 0)) haC hb'C (x, u)) := by
    intro x
    rintro ⟨u, hu⟩
    obtain ⟨s, hs⟩ := Quotient.exists_rep u
    rw [← hs] at hu
    beta_reduce at hu
    rw [straightLiftA_apply] at hu
    exact straightFamA_ne_zero a (straightChord (b 0)) ha hb' hint2 x s hu
  have hstep2 : winding (grbCurve a (straightChord (b 0)))
        (continuous_grbCurve a (straightChord (b 0)) haC hb'C)
        (grbCurve_not_mem_zero hint3)
      = winding (grbCurve (straightChord (a 0)) (straightChord (b 0)))
          (continuous_grbCurve (straightChord (a 0)) (straightChord (b 0)) ha'C hb'C)
          (grbCurve_not_mem_zero hintS) := by
    have hF0 : Continuous
        (fun u : UnitAddCircle => straightLiftA a (straightChord (b 0)) haC hb'C (0, u)) := by
      rw [show (fun u : UnitAddCircle =>
            straightLiftA a (straightChord (b 0)) haC hb'C (0, u))
          = grbCurve a (straightChord (b 0)) from
        funext (straightLiftA_zero a (straightChord (b 0)) haC hb'C)]
      exact continuous_grbCurve a (straightChord (b 0)) haC hb'C
    have hF1 : Continuous
        (fun u : UnitAddCircle => straightLiftA a (straightChord (b 0)) haC hb'C (1, u)) := by
      rw [show (fun u : UnitAddCircle =>
            straightLiftA a (straightChord (b 0)) haC hb'C (1, u))
          = grbCurve (straightChord (a 0)) (straightChord (b 0)) from
        funext (straightLiftA_one a (straightChord (b 0)) haC hb'C)]
      exact continuous_grbCurve (straightChord (a 0)) (straightChord (b 0)) ha'C hb'C
    have hhom := winding_of_homotopy_aux (Φ := straightLiftA a (straightChord (b 0)) haC hb'C)
      hp2 hF0 hF1
    have e0 : winding (fun u : UnitAddCircle =>
          straightLiftA a (straightChord (b 0)) haC hb'C (0, u)) hF0 (hp2 0)
        = winding (grbCurve a (straightChord (b 0)))
            (continuous_grbCurve a (straightChord (b 0)) haC hb'C)
            (grbCurve_not_mem_zero hint3) :=
      winding_eq_of_eq_fun (funext (straightLiftA_zero a (straightChord (b 0)) haC hb'C))
        hF0 _ (hp2 0) _
    have e1 : winding (fun u : UnitAddCircle =>
          straightLiftA a (straightChord (b 0)) haC hb'C (1, u)) hF1 (hp2 1)
        = winding (grbCurve (straightChord (a 0)) (straightChord (b 0)))
            (continuous_grbCurve (straightChord (a 0)) (straightChord (b 0)) ha'C hb'C)
            (grbCurve_not_mem_zero hintS) :=
      winding_eq_of_eq_fun (funext (straightLiftA_one a (straightChord (b 0)) haC hb'C))
        hF1 _ (hp2 1) _
    exact e0.symm.trans (hhom.trans e1)
  --##### putting the two steps together
  have hfirst : 2 * grbDeg a b haC hbC hint
      = winding (grbCurve a b) (continuous_grbCurve a b haC hbC)
          (grbCurve_not_mem_zero hint) :=
    two_mul_grbDeg_eq_winding haC hbC hint
  have hlast : 2 * grbDeg (straightChord (a 0)) (straightChord (b 0)) ha'C hb'C hintS
      = winding (grbCurve (straightChord (a 0)) (straightChord (b 0)))
          (continuous_grbCurve (straightChord (a 0)) (straightChord (b 0)) ha'C hb'C)
          (grbCurve_not_mem_zero hintS) :=
    two_mul_grbDeg_eq_winding ha'C hb'C hintS
  have hfinal : 2 * grbDeg a b haC hbC hint
      = 2 * grbDeg (straightChord (a 0)) (straightChord (b 0)) ha'C hb'C hintS :=
    hfirst.trans (hstep1.trans (hstep2.trans hlast.symm))
  omega

/-- **The honest degree of the boundary curve is unchanged by straightening the two chords.**
Along the linear straightening `a ↦ straightChord (a 0)` (the second chord fixed) and then
`b ↦ straightChord (b 0)` the boundary curve of the difference map never hits the origin
(`Work.Surf.chordDiff_ne_zero_of_sface`/`_tface`), so the winding numbers — and hence the honest
degrees of the honest direction maps, `Work.Surf.ChordN.grbDeg` — agree. -/
theorem grbDeg_eq_straight (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : Work.Drive.IsChord a)
    (hb : Work.Drive.IsChord b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1)
    (hintS : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
      Work.Drive.straightChord (a 0) s = Work.Drive.straightChord (b 0) t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖Work.Drive.straightChord (a 0) s‖ < 1) :
    Work.Surf.ChordN.grbDeg a b ha.contDiff hb.contDiff hint =
      Work.Surf.ChordN.grbDeg (Work.Drive.straightChord (a 0)) (Work.Drive.straightChord (b 0))
        (Work.Drive.straightChord_isChord ha.start).contDiff
        (Work.Drive.straightChord_isChord hb.start).contDiff hintS :=
  grbDeg_eq_straight_aux a b ha.contDiff hb.contDiff ha hb hint hintS

end

end Work.Surf.ChordN
