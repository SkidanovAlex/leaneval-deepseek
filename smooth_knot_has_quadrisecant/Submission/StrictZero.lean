import Mathlib
import ChallengeDeps
import Submission.TorusCollinearity
import Submission.Torus1Chart
import Submission.TrisecantClosed
import Submission.TrisecantLocus
import Submission.TrisecantCover
import Submission.SecantSpace

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology RealInnerProductSpace
set_option linter.style.haveILetI false

/-!
# Layer A (xxiii) — Milestone-2 step (ii), dependency 1: quantitative
chord betweenness & the openness of the strict trisecant data

The Milestone-2 global structure of the trisecant locus `O` over the
Möbius band of secants begins with the *strict data*: the collinear
off-diagonal triples `(a, b, m)` of knot parameters whose middle point
`knotMap m` lies strictly between the chord endpoints.  Before the
projection `strict data → O` can be shown to be an open / local
homeomorphism (the local 1-manifold structure of `O`), one needs a
*quantitative* version of "strictly between" — an affine coefficient
of the middle point along its chord that is continuous on the zero set
and whose unit interval characterises betweenness:

1. **`chordCoeff`** — the Gram coefficient `s(q)` of `knotMap m` along
   the chord from `knotMap a` to `knotMap b` (quotient of the inner
   product by the squared chord length);
2. **factorisation** — `middle_parallel_of_torusCollinearity`: at a
   collinear triple with distinct endpoints,
   `knotMap m − knotMap a = chordCoeff q • (knotMap b − knotMap a)`
   (the cross-product linear-dependence factorisation made explicit
   with the coefficient);
3. **betweenness criteria** — `strict_iff_chordCoeff_mem_Ioo` and
   `closed_iff_chordCoeff_mem_Icc`: with collinearity and distinct
   chord endpoints, strict (closed) betweenness is exactly the
   coefficient lying in the open (closed) unit interval;
4. **continuity** — `continuousAt_chordCoeff`, `zeroChordCoeff` and
   `continuous_zeroChordCoeff`: the coefficient is continuous on the
   whole trisecant zero set (its chord denominator never vanishes
   there, since the zero set is off-diagonal);
5. **openness of the strict data** — `isOpen_strictZero` and
   `isClosed_closedZero`: on the zero set, "the third point is strictly
   between the chord endpoints" is an *open* condition and "on the
   closed chord" is *closed* (both are coefficient-preimages of
   intervals);
6. **the `O`-side interface** — `strictZero`, `zeroChordClass`,
   `zeroChord_endpoints_ne`, `strict_hasMiddleOnClass`, and the fibre
   structure of the chord-class map: `strictZero_fiber` (two strict
   data over one class have equal or swapped chord endpoints) and
   `strictZero_fiber_middle` (under `QuadrisecantFree` the middle
   coordinate is constant on each fibre — the two-to-one double cover
   of `O` by the strict data, with the swap as the only
   identification);
7. **local injectivity on chart strict parts** — `tripleSwap`,
   `continuous_tripleSwap`, `tripleSwap_ne_self`,
   `exists_isOpen_disjoint_self_image` (generic displaced-neighbourhood
   lemma), `chartLift_injective`, and the milestone lemma
   **`zeroChordClass_injective_near_base`**: around the strict base
   parameter `x₀` of any 1-chart there is an open parameter
   neighbourhood `J` on which the chord-class map is injective among
   strict data (the injectivity half of the local-homeomorphism
   statement from which the 1-manifold charts of `O` are built).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant


def chordCoeff (r : ℝ → Space) (q : KnotParamTriple) : ℝ :=
  inner ℝ (knotMap r q.2.2 - knotMap r q.1) (knotMap r q.2.1 - knotMap r q.1) /
    ‖knotMap r q.2.1 - knotMap r q.1‖ ^ 2

lemma inner_sub_chordCoeff (r : ℝ → Space) (q : KnotParamTriple)
    (hd : knotMap r q.2.1 - knotMap r q.1 ≠ 0) :
    inner ℝ (knotMap r q.2.2 - knotMap r q.1) (knotMap r q.2.1 - knotMap r q.1) =
      chordCoeff r q * ‖knotMap r q.2.1 - knotMap r q.1‖ ^ 2 := by
  unfold chordCoeff
  rw [div_mul_cancel₀]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)

lemma middle_parallel_of_torusCollinearity {r : ℝ → Space} (h : IsSmoothKnot r) {q : KnotParamTriple}
    (hcol : torusCollinearity r q = 0) (hab : q.1 ≠ q.2.1) :
    knotMap r q.2.2 - knotMap r q.1 =
      chordCoeff r q • (knotMap r q.2.1 - knotMap r q.1) := by
  have hka_ne : knotMap r q.1 - knotMap r q.2.1 ≠ 0 := by
    exact sub_ne_zero.mpr ((knotMap_injective h).ne hab)
  rcases (cross3_eq_zero_iff_smul_local (u := knotMap r q.1 - knotMap r q.2.1)
    (v := knotMap r q.1 - knotMap r q.2.2)).mp hcol with hz | ⟨t, ht⟩
  · exact False.elim (hka_ne hz)
  · have hpar : knotMap r q.2.2 - knotMap r q.1 = t • (knotMap r q.2.1 - knotMap r q.1) := by
      calc
        knotMap r q.2.2 - knotMap r q.1 = -(knotMap r q.1 - knotMap r q.2.2) := by abel
        _ = -(t • (knotMap r q.1 - knotMap r q.2.1)) := by rw [ht]
        _ = t • (knotMap r q.2.1 - knotMap r q.1) := by
          rw [← smul_neg]
          congr 1
          abel
    have ht_eq : t = chordCoeff r q := by
      have hd : knotMap r q.2.1 - knotMap r q.1 ≠ 0 := by
        exact sub_ne_zero.mpr ((knotMap_injective h).ne hab.symm)
      have hgram := inner_sub_chordCoeff r q hd
      have hmain : inner ℝ (knotMap r q.2.2 - knotMap r q.1) (knotMap r q.2.1 - knotMap r q.1) =
          t * ‖knotMap r q.2.1 - knotMap r q.1‖ ^ 2 := by
        rw [hpar]
        simp [inner_smul_left]
      have hmul : chordCoeff r q * ‖knotMap r q.2.1 - knotMap r q.1‖ ^ 2 =
          t * ‖knotMap r q.2.1 - knotMap r q.1‖ ^ 2 := by
        rw [← hgram]
        exact hmain
      have hnorm : ‖knotMap r q.2.1 - knotMap r q.1‖ ^ 2 ≠ 0 :=
        pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
      have hct : chordCoeff r q = t := mul_right_cancel₀ hnorm hmul
      exact hct.symm
    rw [ht_eq] at hpar
    exact hpar

/-- **Strict betweenness ⟺ coefficient in the open unit interval** (for a
collinear triple with distinct chord endpoints): `knotMap m` lies strictly
between `knotMap a` and `knotMap b` exactly when the affine coefficient of
`knotMap m` along the chord lies in `(0,1)`. -/
lemma strict_iff_chordCoeff_mem_Ioo {r : ℝ → Space} (h : IsSmoothKnot r) {q : KnotParamTriple}
    (hcol : torusCollinearity r q = 0) (hab : q.1 ≠ q.2.1) :
    IsMiddleOnOpenChord r q.1 q.2.1 q.2.2 ↔
      0 < chordCoeff r q ∧ chordCoeff r q < 1 := by
  constructor
  · intro hm
    dsimp [IsMiddleOnOpenChord] at hm
    rcases hm with ⟨a, b, ha, hb, habc, hz⟩
    have hstep : knotMap r q.2.2 - knotMap r q.1 = b • (knotMap r q.2.1 - knotMap r q.1) := by
      calc
        knotMap r q.2.2 - knotMap r q.1 = (a • knotMap r q.1 + b • knotMap r q.2.1) - knotMap r q.1 := by rw [← hz]
        _ = b • (knotMap r q.2.1 - knotMap r q.1) := by
          have h1 := smul_add_smul_eq_add_smul_sub (E := Space) (A := knotMap r q.1) (B := knotMap r q.2.1)
            (s := a) (t := b) habc
          rw [h1]
          abel
    have hd : knotMap r q.2.1 - knotMap r q.1 ≠ 0 := by
      exact sub_ne_zero.mpr ((knotMap_injective h).ne hab.symm)
    have hnorm2 : ‖knotMap r q.2.1 - knotMap r q.1‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
    have hcoeff : chordCoeff r q = b := by
      unfold chordCoeff
      rw [hstep]
      simp [inner_smul_left]
      field_simp [hnorm2]
    constructor
    · rw [hcoeff]
      exact hb
    · rw [hcoeff]
      have hlt : a > 0 := ha
      linarith [habc]
  · intro hc
    have h0 : 0 < chordCoeff r q := hc.1
    have h1 : chordCoeff r q < 1 := hc.2
    have hpar := middle_parallel_of_torusCollinearity h hcol hab
    have hz : (1 - chordCoeff r q) • knotMap r q.1 + chordCoeff r q • knotMap r q.2.1 =
        knotMap r q.2.2 := by
      calc
        (1 - chordCoeff r q) • knotMap r q.1 + chordCoeff r q • knotMap r q.2.1
            = knotMap r q.1 + chordCoeff r q • (knotMap r q.2.1 - knotMap r q.1) := by
          have h1 := smul_add_smul_eq_add_smul_sub (E := Space) (A := knotMap r q.1) (B := knotMap r q.2.1)
            (s := 1 - chordCoeff r q) (t := chordCoeff r q) (by ring)
          rw [h1]
        _ = knotMap r q.2.2 := by
          rw [← hpar]
          abel
    dsimp [IsMiddleOnOpenChord]
    refine ⟨1 - chordCoeff r q, chordCoeff r q, ?_, h0, by ring, hz⟩
    linarith

/-- **Closed-segment betweenness ⟺ coefficient in the closed unit interval**
(collinear triple, distinct chord endpoints). -/
lemma closed_iff_chordCoeff_mem_Icc {r : ℝ → Space} (h : IsSmoothKnot r) {q : KnotParamTriple}
    (hcol : torusCollinearity r q = 0) (hab : q.1 ≠ q.2.1) :
    IsMiddleOnClosedChord r q.1 q.2.1 q.2.2 ↔
      0 ≤ chordCoeff r q ∧ chordCoeff r q ≤ 1 := by
  constructor
  · intro hm
    dsimp [IsMiddleOnClosedChord] at hm
    rcases hm with ⟨a, b, ha, hb, habc, hz⟩
    have hstep : knotMap r q.2.2 - knotMap r q.1 = b • (knotMap r q.2.1 - knotMap r q.1) := by
      calc
        knotMap r q.2.2 - knotMap r q.1 = (a • knotMap r q.1 + b • knotMap r q.2.1) - knotMap r q.1 := by rw [← hz]
        _ = b • (knotMap r q.2.1 - knotMap r q.1) := by
          have h1 := smul_add_smul_eq_add_smul_sub (E := Space) (A := knotMap r q.1) (B := knotMap r q.2.1)
            (s := a) (t := b) habc
          rw [h1]
          abel
    have hd : knotMap r q.2.1 - knotMap r q.1 ≠ 0 := by
      exact sub_ne_zero.mpr ((knotMap_injective h).ne hab.symm)
    have hnorm2 : ‖knotMap r q.2.1 - knotMap r q.1‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
    have hcoeff : chordCoeff r q = b := by
      unfold chordCoeff
      rw [hstep]
      simp [inner_smul_left]
      field_simp [hnorm2]
    constructor
    · rw [hcoeff]
      exact hb
    · rw [hcoeff]
      have hle : a ≥ 0 := ha
      linarith [habc]
  · intro hc
    have h0 : 0 ≤ chordCoeff r q := hc.1
    have h1 : chordCoeff r q ≤ 1 := hc.2
    have hpar := middle_parallel_of_torusCollinearity h hcol hab
    have hz : (1 - chordCoeff r q) • knotMap r q.1 + chordCoeff r q • knotMap r q.2.1 =
        knotMap r q.2.2 := by
      calc
        (1 - chordCoeff r q) • knotMap r q.1 + chordCoeff r q • knotMap r q.2.1
            = knotMap r q.1 + chordCoeff r q • (knotMap r q.2.1 - knotMap r q.1) := by
          have h1 := smul_add_smul_eq_add_smul_sub (E := Space) (A := knotMap r q.1) (B := knotMap r q.2.1)
            (s := 1 - chordCoeff r q) (t := chordCoeff r q) (by ring)
          rw [h1]
        _ = knotMap r q.2.2 := by
          rw [← hpar]
          abel
    dsimp [IsMiddleOnClosedChord]
    refine ⟨1 - chordCoeff r q, chordCoeff r q, ?_, h0, by ring, hz⟩
    linarith

/-- The chord coefficient is continuous at every triple with distinct chord
endpoints (the Gram denominator does not vanish there). -/
lemma continuousAt_chordCoeff {r : ℝ → Space} (h : IsSmoothKnot r) {q : KnotParamTriple}
    (hab : q.1 ≠ q.2.1) : ContinuousAt (chordCoeff r) q := by
  have hkm : Continuous (knotMap r) := h.knotMap_continuous
  let num : KnotParamTriple → ℝ := fun q => inner ℝ (knotMap r q.2.2 - knotMap r q.1) (knotMap r q.2.1 - knotMap r q.1)
  let den : KnotParamTriple → ℝ := fun q => ‖knotMap r q.2.1 - knotMap r q.1‖ ^ 2
  have hnum : Continuous num := by
    dsimp [num]
    refine Continuous.inner ?_ ?_
    · exact (hkm.comp (continuous_snd.comp continuous_snd)).sub (hkm.comp continuous_fst)
    · exact (hkm.comp (continuous_fst.comp continuous_snd)).sub (hkm.comp continuous_fst)
  have hden : Continuous den := by
    dsimp [den]
    exact (continuous_norm.comp ((hkm.comp (continuous_fst.comp continuous_snd)).sub (hkm.comp continuous_fst))).pow 2
  have hden0 : den q ≠ 0 := by
    dsimp [den]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr ((knotMap_injective h).ne hab.symm)))
  have hdiv : ContinuousAt (fun x : KnotParamTriple => num x / den x) q :=
    ContinuousAt.div hnum.continuousAt hden.continuousAt hden0
  exact hdiv

/-- The chord coefficient along the trisecant zero set (every zero-set point
has distinct chord endpoints, since the zero set is off-diagonal). -/
noncomputable def zeroChordCoeff {r : ℝ → Space} (_h : IsSmoothKnot r) :
    ZeroSetPoint r → ℝ :=
  fun z => chordCoeff r (z : KnotParamTriple)

/-- The chord coefficient is continuous along the whole trisecant zero set. -/
theorem continuous_zeroChordCoeff {r : ℝ → Space} (h : IsSmoothKnot r) :
    Continuous (zeroChordCoeff h) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hzoff : (z : KnotParamTriple) ∈ TorusOffDiag r :=
    (mem_trisecantZeroSet_iff (z : KnotParamTriple)).mp z.2 |>.2
  have hzab : (z : KnotParamTriple).1 ≠ (z : KnotParamTriple).2.1 :=
    (TorusOffDiag_iff_params h (z : KnotParamTriple)).mp hzoff |>.1
  have h1 : ContinuousAt (fun z : ZeroSetPoint r => (z : KnotParamTriple)) z :=
    continuous_subtype_val.continuousAt
  have h2 : ContinuousAt (chordCoeff r) (z : KnotParamTriple) := continuousAt_chordCoeff h hzab
  have hcomp : ContinuousAt (fun z : ZeroSetPoint r => chordCoeff r (z : KnotParamTriple)) z := h2.comp h1
  exact hcomp

/-- The (strict) middle condition is open along the trisecant zero set: near
a collinear off-diagonal triple whose third point is strictly between the
chord endpoints, the same holds for all nearby zero-set triples (the strict
data form an open subset of the zero set). -/
theorem isOpen_strictZero {r : ℝ → Space} (h : IsSmoothKnot r) :
    IsOpen {z : ZeroSetPoint r | IsMiddleOnOpenChord r z.1.1 z.1.2.1 z.1.2.2} := by
  have heq : {z : ZeroSetPoint r | IsMiddleOnOpenChord r z.1.1 z.1.2.1 z.1.2.2} =
      (zeroChordCoeff h) ⁻¹' (Set.Ioo (0 : ℝ) 1) := by
    ext z
    constructor
    · intro hs
      have hzoff : (z : KnotParamTriple) ∈ TorusOffDiag r :=
        (mem_trisecantZeroSet_iff (z : KnotParamTriple)).mp z.2 |>.2
      have hzab : (z : KnotParamTriple).1 ≠ (z : KnotParamTriple).2.1 :=
        (TorusOffDiag_iff_params h (z : KnotParamTriple)).mp hzoff |>.1
      have hiff := strict_iff_chordCoeff_mem_Ioo h (q := (z : KnotParamTriple))
        ((mem_trisecantZeroSet_iff (z : KnotParamTriple)).mp z.2 |>.1) hzab
      have : 0 < chordCoeff r (z : KnotParamTriple) ∧ chordCoeff r (z : KnotParamTriple) < 1 := hiff.mp hs
      simpa [zeroChordCoeff] using this
    · intro hc
      have hzoff : (z : KnotParamTriple) ∈ TorusOffDiag r :=
        (mem_trisecantZeroSet_iff (z : KnotParamTriple)).mp z.2 |>.2
      have hzab : (z : KnotParamTriple).1 ≠ (z : KnotParamTriple).2.1 :=
        (TorusOffDiag_iff_params h (z : KnotParamTriple)).mp hzoff |>.1
      have hiff := strict_iff_chordCoeff_mem_Ioo h (q := (z : KnotParamTriple))
        ((mem_trisecantZeroSet_iff (z : KnotParamTriple)).mp z.2 |>.1) hzab
      have : chordCoeff r (z : KnotParamTriple) ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa [zeroChordCoeff] using hc
      exact hiff.mpr (by simpa [zeroChordCoeff] using this)
  rw [heq]
  exact (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1)).preimage (continuous_zeroChordCoeff h)

/-- The (closed) middle condition is closed along the trisecant zero set. -/
theorem isClosed_closedZero {r : ℝ → Space} (h : IsSmoothKnot r) :
    IsClosed {z : ZeroSetPoint r | IsMiddleOnClosedChord r z.1.1 z.1.2.1 z.1.2.2} := by
  have heq : {z : ZeroSetPoint r | IsMiddleOnClosedChord r z.1.1 z.1.2.1 z.1.2.2} =
      (zeroChordCoeff h) ⁻¹' (Set.Icc (0 : ℝ) 1) := by
    ext z
    constructor
    · intro hs
      have hzoff : (z : KnotParamTriple) ∈ TorusOffDiag r :=
        (mem_trisecantZeroSet_iff (z : KnotParamTriple)).mp z.2 |>.2
      have hzab : (z : KnotParamTriple).1 ≠ (z : KnotParamTriple).2.1 :=
        (TorusOffDiag_iff_params h (z : KnotParamTriple)).mp hzoff |>.1
      have hiff := closed_iff_chordCoeff_mem_Icc h (q := (z : KnotParamTriple))
        ((mem_trisecantZeroSet_iff (z : KnotParamTriple)).mp z.2 |>.1) hzab
      have : 0 ≤ chordCoeff r (z : KnotParamTriple) ∧ chordCoeff r (z : KnotParamTriple) ≤ 1 := hiff.mp hs
      simpa [zeroChordCoeff] using this
    · intro hc
      have hzoff : (z : KnotParamTriple) ∈ TorusOffDiag r :=
        (mem_trisecantZeroSet_iff (z : KnotParamTriple)).mp z.2 |>.2
      have hzab : (z : KnotParamTriple).1 ≠ (z : KnotParamTriple).2.1 :=
        (TorusOffDiag_iff_params h (z : KnotParamTriple)).mp hzoff |>.1
      have hiff := closed_iff_chordCoeff_mem_Icc h (q := (z : KnotParamTriple))
        ((mem_trisecantZeroSet_iff (z : KnotParamTriple)).mp z.2 |>.1) hzab
      have : chordCoeff r (z : KnotParamTriple) ∈ Set.Icc (0 : ℝ) 1 := by simpa [zeroChordCoeff] using hc
      exact hiff.mpr (by simpa [zeroChordCoeff] using this)
  rw [heq]
  exact (isClosed_Icc : IsClosed (Set.Icc (0 : ℝ) 1)).preimage (continuous_zeroChordCoeff h)

noncomputable def zeroChordClass {r : ℝ → Space} (h : IsSmoothKnot r) (z : ZeroSetPoint r) : OpenMobius :=
  mobiusCover ⟨((z : KnotParamTriple).1, (z : KnotParamTriple).2.1),
    (TorusOffDiag_iff_params h (z : KnotParamTriple)).mp
      ((mem_trisecantZeroSet_iff (z : KnotParamTriple)).mp z.2 |>.2) |>.1⟩

def strictZero (r : ℝ → Space) (z : ZeroSetPoint r) : Prop :=
  IsMiddleOnOpenChord r (z : KnotParamTriple).1 (z : KnotParamTriple).2.1 (z : KnotParamTriple).2.2

/-- chord endpoints of a zero-set point are distinct (zero set is off-diagonal) -/
lemma zeroChord_endpoints_ne {r : ℝ → Space} (h : IsSmoothKnot r) (z : ZeroSetPoint r) :
    (z : KnotParamTriple).1 ≠ (z : KnotParamTriple).2.1 :=
  (TorusOffDiag_iff_params h (z : KnotParamTriple)).mp
    ((mem_trisecantZeroSet_iff (z : KnotParamTriple)).mp z.2 |>.2) |>.1

lemma strict_hasMiddleOnClass {r : ℝ → Space} (h : IsSmoothKnot r) (z : ZeroSetPoint r)
    (hz : strictZero r z) : HasMiddleOnClass r (zeroChordClass h z) := by
  let p : OrderedPairs := ⟨((z : KnotParamTriple).1, (z : KnotParamTriple).2.1), zeroChord_endpoints_ne h z⟩
  change HasMiddleOnClass r (mobiusCover p)
  rw [HasMiddleOnClass_iff r p]
  refine ⟨(z : KnotParamTriple).2.2, ?_⟩
  simpa [p, strictZero, IsMiddleOnChord, IsMiddleOnOpenChord] using hz

/-- **Fibre of the chord-class map over `O`.**  Two strict zero-set points
over the same chord class have equal or swapped chord endpoints: the
projection of the strict data onto the Möbius band is two-to-one and the
swap of the endpoints is the only identification at the chord level. -/
lemma strictZero_fiber {r : ℝ → Space} (h : IsSmoothKnot r)
    {z w : ZeroSetPoint r} (hcl : zeroChordClass h z = zeroChordClass h w) :
    (z.1.1 = w.1.1 ∧ z.1.2.1 = w.1.2.1) ∨
      (z.1.1 = w.1.2.1 ∧ z.1.2.1 = w.1.1) := by
  let pz : OrderedPairs := ⟨((z : KnotParamTriple).1, (z : KnotParamTriple).2.1), zeroChord_endpoints_ne h z⟩
  let pw : OrderedPairs := ⟨((w : KnotParamTriple).1, (w : KnotParamTriple).2.1), zeroChord_endpoints_ne h w⟩
  have hcl' : mobiusCover pz = mobiusCover pw := by
    dsimp [pz, pw, zeroChordClass]
    exact hcl
  have hfib := mobiusCover_fiber pz
  have hpw : pw ∈ ({pz, swapOrdered pz} : Set OrderedPairs) := by
    rw [← hfib]
    exact hcl'.symm
  simp [pw, pz] at hpw
  rcases hpw with hpair | hpair
  · left
    constructor
    · simpa using hpair.1.symm
    · simpa using hpair.2.symm
  · right
    have hq1 : ((w : KnotParamTriple).1, (w : KnotParamTriple).2.1) =
          ((z : KnotParamTriple).2.1, (z : KnotParamTriple).1) := by
      have hq := congrArg (fun q : OrderedPairs => q.1) hpair
      simpa [pz, pw, swapOrdered] using hq
    constructor
    · simpa using (congrArg Prod.snd hq1).symm
    · simpa using (congrArg Prod.fst hq1).symm

/-- **The middle coordinate is a function of the secant class over `O`
(no-quadrisecant case).**  Two strict zero-set points over the same chord
class have equal middle coordinates — together with `strictZero_fiber` this
is the two-to-one double cover structure of the strict data over `O` with
the middle constant on each fibre. -/
lemma strictZero_fiber_middle {r : ℝ → Space} (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    {z w : ZeroSetPoint r} (hz : strictZero r z) (hw : strictZero r w)
    (hcl : zeroChordClass h z = zeroChordClass h w) : z.1.2.2 = w.1.2.2 := by
  let a : KnotParam := (z : KnotParamTriple).1
  let b : KnotParam := (z : KnotParamTriple).2.1
  have hab : a ≠ b := by
    dsimp [a, b]
    exact zeroChord_endpoints_ne h z
  rcases strictZero_fiber h hcl with hpair | hpair
  · exact middle_unique_of_quadrisecantFree h hqf hab
      (by simpa [a, b, strictZero, IsMiddleOnChord, IsMiddleOnOpenChord] using hz)
      (by
        have hw' : IsMiddleOnOpenChord r (z : KnotParamTriple).1 (z : KnotParamTriple).2.1
            (w : KnotParamTriple).2.2 := by
          simpa [strictZero, ← hpair.1, ← hpair.2] using hw
        simpa [a, b, IsMiddleOnChord, IsMiddleOnOpenChord] using hw')
  · exact middle_unique_of_quadrisecantFree h hqf hab
      (by simpa [a, b, strictZero, IsMiddleOnChord, IsMiddleOnOpenChord] using hz)
      (by
        have hw' : IsMiddleOnOpenChord r (z : KnotParamTriple).2.1 (z : KnotParamTriple).1
            (w : KnotParamTriple).2.2 := by
          simpa [strictZero, ← hpair.2, ← hpair.1] using hw
        have hw'' : IsMiddleOnOpenChord r (z : KnotParamTriple).1 (z : KnotParamTriple).2.1
            (w : KnotParamTriple).2.2 := by
          change knotMap r (w : KnotParamTriple).2.2 ∈ openSegment ℝ
            (knotMap r (z : KnotParamTriple).2.1) (knotMap r (z : KnotParamTriple).1) at hw'
          rw [openSegment_symm] at hw'
          simpa [IsMiddleOnOpenChord] using hw'
        simpa [a, b, IsMiddleOnChord, IsMiddleOnOpenChord] using hw'')


/-! ## 7. Local injectivity of the class map on the strict part of a chart -/

/-- Swap of the two chord endpoints of a parameter triple:
`(a, (b, m)) ↦ (b, (a, m))`. -/
def tripleSwap (q : KnotParamTriple) : KnotParamTriple := (q.2.1, (q.1, q.2.2))

/-- The endpoint swap is continuous. -/
lemma continuous_tripleSwap : Continuous (tripleSwap : KnotParamTriple → KnotParamTriple) := by
  unfold tripleSwap
  exact (continuous_fst.comp continuous_snd).prodMk
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd))

/-- A triple with distinct chord endpoints is not fixed by the swap. -/
lemma tripleSwap_ne_self {q : KnotParamTriple} (h : q.1 ≠ q.2.1) : tripleSwap q ≠ q := by
  intro hq
  have hc := congrArg (fun t : KnotParamTriple => t.1) hq
  have : q.1 = q.2.1 := by simpa [tripleSwap] using hc.symm
  exact h this

/-- A point whose continuous image is distinct from it has an open
neighbourhood disjoint from its own image ("no fixed point ⇒ locally
displaced"). -/
lemma exists_isOpen_disjoint_self_image {X : Type*} [TopologicalSpace X] [T2Space X]
    {f : X → X} (hf : Continuous f) {p : X} (hp : f p ≠ p) :
    ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ Disjoint U (f '' U) := by
  rcases t2_separation (x := p) (y := f p) hp.symm with ⟨A, B, hAo, hBo, hpA, hfpB, hdis⟩
  let U : Set X := A ∩ f ⁻¹' B
  refine ⟨U, hAo.inter (hBo.preimage hf), ⟨hpA, hfpB⟩, ?_⟩
  have hsub1 : U ⊆ A := fun x hx => hx.1
  have hsub2 : f '' U ⊆ B := by
    rintro y ⟨x, hx, rfl⟩
    exact hx.2
  exact hdis.mono hsub1 hsub2

/-- The single-chart lift is injective (the chart homeomorphism is). -/
lemma chartLift_injective {r : ℝ → Space} {p : KnotParamTriple}
    (c : ZeroSet1Chart r p) : Function.Injective (chartLift c) := by
  intro x y hxy
  have hv : ((chartLift c x : ZeroSetPoint r) : KnotParamTriple) =
      ((chartLift c y : ZeroSetPoint r) : KnotParamTriple) :=
    congrArg (fun z : ZeroSetPoint r => (z : KnotParamTriple)) hxy
  apply c.homeo.injective
  apply Subtype.ext
  simpa [chartLift] using hv

/-- **Local injectivity of the chord-class map on the strict part of a
chart.**  Let `c` be a 1-chart at a point of the zero set whose base
parameter `x₀` is *strict* (the chart is centred at a strict data point,
i.e. at a point of `O`).  Under `QuadrisecantFree`, on a sufficiently small
strict parameter neighbourhood `J` of `x₀` (one avoiding the swapped-sheet
image under `tripleSwap`) the class map is injective: nearby strict data
points with the same secant class are equal.  This is the injectivity half
of the local-homeomorphism statement from which the 1-manifold charts of
`O` are built: the two-to-one fibre structure `strictZero_fiber` has no
room inside `J` — equal ordered chords would give equal data points
(contradicting chart injectivity) and swapped chords would put both points
of a fibre inside `J ⊆ U` while `U` is disjoint from its swap image. -/
theorem zeroChordClass_injective_near_base {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) {p : KnotParamTriple} (c : ZeroSet1Chart r p)
    (hz₀ : strictZero r (chartLift c ⟨c.x₀, c.x₀_mem⟩)) :
    ∃ J : Set (ChartInterval c.lo c.hi), ⟨c.x₀, c.x₀_mem⟩ ∈ J ∧ IsOpen J ∧
      ∀ ⦃x₁ x₂ : ChartInterval c.lo c.hi⦄, x₁ ∈ J → x₂ ∈ J →
        strictZero r (chartLift c x₁) → strictZero r (chartLift c x₂) →
        zeroChordClass h (chartLift c x₁) = zeroChordClass h (chartLift c x₂) → x₁ = x₂ := by
  let z₀ : ZeroSetPoint r := chartLift c ⟨c.x₀, c.x₀_mem⟩
  have hp₀ne : tripleSwap (z₀ : KnotParamTriple) ≠ (z₀ : KnotParamTriple) := by
    apply tripleSwap_ne_self
    exact zeroChord_endpoints_ne h z₀
  rcases exists_isOpen_disjoint_self_image (f := tripleSwap) continuous_tripleSwap hp₀ne with
    ⟨U, hUo, hz₀U, hUdis⟩
  let J : Set (ChartInterval c.lo c.hi) :=
    {x : ChartInterval c.lo c.hi | strictZero r (chartLift c x) ∧
      (chartLift c x : KnotParamTriple) ∈ U}
  have hJ_open : IsOpen J := by
    dsimp [J]
    exact (isOpen_strictZero h).preimage (continuous_chartLift c) |>.inter
      (hUo.preimage (continuous_subtype_val.comp (continuous_chartLift c)))
  have hJ₀ : ⟨c.x₀, c.x₀_mem⟩ ∈ J := by
    dsimp [J, z₀]
    exact ⟨hz₀, (by simpa using hz₀U)⟩
  refine ⟨J, hJ₀, hJ_open, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hs₁ hs₂ hcl
  let z₁ : ZeroSetPoint r := chartLift c x₁
  let z₂ : ZeroSetPoint r := chartLift c x₂
  have hz1J : (z₁ : KnotParamTriple) ∈ U := by
    exact (by simpa [z₁] using hx₁.2)
  have hz2J : (z₂ : KnotParamTriple) ∈ U := by
    exact (by simpa [z₂] using hx₂.2)
  have hcl' : zeroChordClass h z₁ = zeroChordClass h z₂ := by
    simpa [z₁, z₂] using hcl
  rcases strictZero_fiber h hcl' with hpair | hpair
  · have hmid : z₁.1.2.2 = z₂.1.2.2 := strictZero_fiber_middle h hqf
      (by simpa [z₁] using hs₁) (by simpa [z₂] using hs₂) hcl'
    have hval : (z₁ : KnotParamTriple) = (z₂ : KnotParamTriple) := by
      apply Prod.ext
      · simpa using hpair.1
      · apply Prod.ext
        · simpa using hpair.2
        · simpa using hmid
    have hz12 : chartLift c x₁ = chartLift c x₂ := by
      apply Subtype.ext
      simpa [z₁, z₂] using hval
    exact chartLift_injective c hz12
  · have hmid : z₁.1.2.2 = z₂.1.2.2 := strictZero_fiber_middle h hqf
      (by simpa [z₁] using hs₁) (by simpa [z₂] using hs₂) hcl'
    have hsw : (z₂ : KnotParamTriple) = tripleSwap (z₁ : KnotParamTriple) := by
      apply Prod.ext
      · simpa [tripleSwap] using hpair.2.symm
      · apply Prod.ext
        · simpa [tripleSwap] using hpair.1.symm
        · simpa [tripleSwap] using hmid.symm
    have hz2im : (z₂ : KnotParamTriple) ∈ tripleSwap '' U := by
      refine ⟨(z₁ : KnotParamTriple), hz1J, hsw.symm⟩
    exact False.elim ((Set.disjoint_left.mp hUdis) hz2J hz2im)

end LeanEval.KnotTheory.Quadrisecant
