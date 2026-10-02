import Mathlib
import Submission.Work.ThomBordism.KeyLocal.tubeSets
import Submission.Work.ThomBordism.nfGen_span

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

/-!
# The continuous normal-coordinate map of a chart piece of the tube

`Work.ThomBordism.KeyLocal.tubeNormCoord` is the coordinate reading of the normal vector in the
σ-corrected frame `Gauss.gframe` of the normal datum, as a *function* of the chart piece
`tubeBaseSet E C ND i` of the tube.  The consumer `Work.ThomBordism.KeyLocal.tubeNormReading` (the
normal reading (T2) of the last mile) asks for it as a *continuous map* `b`, together with the
pinning `b y = tubeNormCoord ... y` and the non-vanishing condition on the punctured part.

This file supplies that map, together with the characterisation of its zero set: the values of `b`
vanish exactly on the zero section of the tube, i.e. `b⁻¹{0} = tubeBaseSet E C ND i ∖
tubeBaseSetPunct E C ND i`.

The two ingredients are:

* `continuous_tubeNormCoord` — continuity.  The frame `Gauss.gframe E ND i` is continuous along
  `ND.D.baseSet i` (`Gauss.continuousOn_sigma` and `Work.Tubular.continuousOn_orthFrame` composed
  through `Gauss.gframe_apply`), the foot of the tube is continuous (`tubeFoot`) and so is the
  normal vector (`NormalTotal.continuous_vec`); `readFrame` is the continuous-linear composite
  `x ↦ (⟨f j, x⟩)_j`.
* `tubeNormCoord_eq_zero_iff` — the zero set.  `readFrame f` for an orthonormal frame `f` is
  injective on the span of `f` (it inverts the coordinate combination,
  `Work.ThomBordism.readFrame_sum_smul`), and `Gauss.gframe E ND i x` is an orthonormal frame of the
  normal space `ν_x` (`Gauss.orthonormal_gframe`, `span_gframe`), so it vanishes exactly on the
  zero vector — which is precisely the zero section `normalNonzero Eᶜ`.
-/

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.Grassmann

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## The reading map of an orthonormal frame -/

/-- **The reading map of an orthonormal frame inverts the coordinate combination** (restated here
for convenience, from `Work.ThomBordism.readFrame_sum_smul`): reading `∑ j, c j • f j` in the
orthonormal frame `f` returns the coordinates `c`. -/
theorem readFrame_sum_smul' {N k : ℕ} (f : Fin k → EuclideanSpace ℝ (Fin N))
    (hf : Orthonormal ℝ f) (c : Fin k → ℝ) :
    Work.ThomBordism.readFrame f (∑ j, c j • f j) = Work.Tubular.funToEuc k c := by
  have h2 := Work.ThomBordism.readFrame_sum_smul f hf (Work.Tubular.funToEuc k c)
  convert h2 using 2
  exact rfl

/-- **The reading map of an orthonormal frame is injective on the span of the frame.** -/
theorem readFrame_eq_zero_iff_of_mem_span {N k : ℕ} {f : Fin k → EuclideanSpace ℝ (Fin N)}
    (hf : Orthonormal ℝ f) {w : EuclideanSpace ℝ (Fin N)}
    (hw : w ∈ Submodule.span ℝ (Set.range f)) :
    Work.ThomBordism.readFrame f w = 0 ↔ w = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
  have h1 : (Work.ThomBordism.readFrame f) (∑ i, c i • f i) = Work.Tubular.funToEuc k c :=
    readFrame_sum_smul' f hf c
  rw [← hc, h1] at h
  have hc0 : c = 0 := by
    have h3 := congrArg (fun u : EuclideanSpace ℝ (Fin k) => u.ofLp) h
    simpa using h3
  rw [← hc, hc0]
  simp

/-- **The σ-corrected normal frame of the normal datum reads the normal space injectively**: on
`ν_x` (for `x` in the chart `i`) the coordinate reading in `Gauss.gframe E ND i x` vanishes only at
the zero vector. -/
theorem readFrame_gframe_eq_zero_iff
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ ND.D.baseSet i) {w : Work.Tubular.Euc (8 + k)} (hw : w ∈ normalSpace E x) :
    Work.ThomBordism.readFrame (Gauss.gframe E ND i x) w = 0 ↔ w = 0 :=
  readFrame_eq_zero_iff_of_mem_span (Gauss.orthonormal_gframe E ND i hx)
    (by rw [span_gframe E ND i hx]; exact hw)

/-! ## The normal coordinate of the tube vanishes exactly on the zero section -/

/-- **The normal coordinate reading of a point of the chart piece of the tube vanishes exactly when
the normal vector of the tube inverse does.** -/
theorem tubeNormCoord_eq_zero_iff
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) {ε : ℝ} (C : TubeChart E ε)
    (i : CoverIdx V k) (y : ↥(tubeBaseSet E C ND i)) :
    tubeNormCoord E C ND i y = 0 ↔
      NormalTotal.vec (C.inv ((y : ↥C.U) : Work.Tubular.Euc (8 + k))) = 0 := by
  have hx : tubeFoot E C (y : ↥C.U) ∈ ND.D.baseSet i := y.2
  have hw : NormalTotal.vec (C.inv ((y : ↥C.U) : Work.Tubular.Euc (8 + k)))
      ∈ normalSpace E (tubeFoot E C (y : ↥C.U)) := (C.inv _).2
  rw [show tubeNormCoord E C ND i y
      = Work.ThomBordism.readFrame (Gauss.gframe E ND i (tubeFoot E C (y : ↥C.U)))
          (NormalTotal.vec (C.inv ((y : ↥C.U) : Work.Tubular.Euc (8 + k)))) from rfl]
  exact readFrame_gframe_eq_zero_iff E ND i hx hw

/-! ## Continuity -/

/-- **The σ-corrected normal frame is continuous along the tube** (in the tube base set of the
chart `i`). -/
theorem continuous_gframe_tube
    (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) (ND : NormalData V k E.e)
    (i : CoverIdx V k) :
    Continuous (fun y : ↥(tubeBaseSet E C ND i) =>
      Gauss.gframe E ND i (tubeFoot E C (y : ↥C.U))) := by
  rw [continuous_pi_iff]
  intro a
  rw [show (fun y : ↥(tubeBaseSet E C ND i) =>
        Gauss.gframe E ND i (tubeFoot E C (y : ↥C.U)) a)
      = fun y : ↥(tubeBaseSet E C ND i) =>
          (if (a : ℕ) = 0 then Gauss.sigma E ND i (tubeFoot E C (y : ↥C.U)) else 1)
          • orthFrame E ND i (tubeFoot E C (y : ↥C.U)) a from
    funext fun y => Gauss.gframe_apply E ND i _ a]
  have hsig : Continuous (fun y : ↥(tubeBaseSet E C ND i) =>
      Gauss.sigma E ND i (tubeFoot E C (y : ↥C.U))) :=
    (Gauss.continuousOn_sigma E ND i).comp_continuous
      ((tubeFoot E C).continuous.comp continuous_subtype_val) (fun y => y.2)
  have horth : Continuous (fun y : ↥(tubeBaseSet E C ND i) =>
      orthFrame E ND i (tubeFoot E C (y : ↥C.U)) a) :=
    (Work.Tubular.continuousOn_orthFrame E ND i a).comp_continuous
      ((tubeFoot E C).continuous.comp continuous_subtype_val) (fun y => y.2)
  by_cases ha : (a : ℕ) = 0
  · rw [show (fun y : ↥(tubeBaseSet E C ND i) =>
          (if (a : ℕ) = 0 then Gauss.sigma E ND i (tubeFoot E C (y : ↥C.U)) else 1)
            • orthFrame E ND i (tubeFoot E C (y : ↥C.U)) a)
        = fun y : ↥(tubeBaseSet E C ND i) => Gauss.sigma E ND i (tubeFoot E C (y : ↥C.U))
            • orthFrame E ND i (tubeFoot E C (y : ↥C.U)) a from
      funext fun y => by rw [if_pos ha]]
    exact hsig.smul horth
  · rw [show (fun y : ↥(tubeBaseSet E C ND i) =>
          (if (a : ℕ) = 0 then Gauss.sigma E ND i (tubeFoot E C (y : ↥C.U)) else 1)
            • orthFrame E ND i (tubeFoot E C (y : ↥C.U)) a)
        = fun y : ↥(tubeBaseSet E C ND i) =>
            (1 : ℝ) • orthFrame E ND i (tubeFoot E C (y : ↥C.U)) a from
      funext fun y => by rw [if_neg ha]]
    exact horth.const_smul (1 : ℝ)

/-- **The normal-coordinate reading of the chart piece of the tube is continuous.** -/
theorem continuous_tubeNormCoord
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) {ε : ℝ} (C : TubeChart E ε)
    (i : CoverIdx V k) :
    Continuous (fun y : ↥(tubeBaseSet E C ND i) => tubeNormCoord E C ND i y) := by
  have hframe : Continuous (fun y : ↥(tubeBaseSet E C ND i) =>
      Gauss.gframe E ND i (tubeFoot E C (y : ↥C.U))) := continuous_gframe_tube E C ND i
  have hg : Continuous (fun y : ↥(tubeBaseSet E C ND i) => ((y : ↥C.U) : Work.Tubular.Euc (8 + k))) :=
    (continuous_subtype_val (p := fun z : Work.Tubular.Euc (8 + k) => z ∈ C.U)).comp
      (continuous_subtype_val (p := fun z : ↥C.U => z ∈ tubeBaseSet E C ND i))
  have hvec : Continuous (fun y : ↥(tubeBaseSet E C ND i) =>
      NormalTotal.vec (C.inv ((y : ↥C.U) : Work.Tubular.Euc (8 + k)))) :=
    (NormalTotal.continuous_vec E).comp
      ((C.continuousOn_inv).comp_continuous hg (fun y => (y : ↥C.U).2))
  rw [show (fun y : ↥(tubeBaseSet E C ND i) => tubeNormCoord E C ND i y)
      = fun y : ↥(tubeBaseSet E C ND i) => Work.Tubular.funToEuc k
          (fun j => inner ℝ (Gauss.gframe E ND i (tubeFoot E C (y : ↥C.U)) j)
            (NormalTotal.vec (C.inv ((y : ↥C.U) : Work.Tubular.Euc (8 + k))))) from
    funext fun y => Work.ThomBordism.readFrame_apply (Gauss.gframe E ND i
      (tubeFoot E C (y : ↥C.U))) (NormalTotal.vec (C.inv ((y : ↥C.U) : Work.Tubular.Euc (8 + k))))]
  refine Continuous.comp (Work.Tubular.funToEuc k).continuous ?_
  exact continuous_pi fun j => continuous_inner.comp
    (((continuous_apply j).comp hframe).prodMk hvec)

end

end Work.ThomBordism.KeyLocal

namespace Work.ThomBordism.KeyLocal

/-- **The continuous normal-coordinate map of the chart piece of the tube**, together with the
characterisation of its zero set. -/
theorem exists_tubeNormCoordMap {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    ∃ b : C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), Work.Tubular.Euc k),
      (∀ y, b y = Work.ThomBordism.KeyLocal.tubeNormCoord E C ND i y) ∧
      (∀ y, b y = 0 ↔ C.inv (y : ↥C.U).1 ∉ Work.Tubular.normalNonzero E) := by
  refine ⟨⟨fun y => tubeNormCoord E C ND i y, continuous_tubeNormCoord E ND C i⟩, fun y => rfl,
    fun y => ?_⟩
  show tubeNormCoord E C ND i y = 0 ↔ C.inv (y : ↥C.U).1 ∉ Work.Tubular.normalNonzero E
  rw [tubeNormCoord_eq_zero_iff]
  rw [Work.Tubular.mem_normalNonzero]
  constructor
  · intro h hne
    refine hne ?_
    rw [Work.Tubular.normalNorm]
    rw [show (C.inv ((y : ↥C.U) : Work.Tubular.Euc (8 + k))).1.2 = 0 from h]
    rw [norm_zero]
  · intro h
    have h0 : Work.Tubular.normalNorm E (C.inv ((y : ↥C.U) : Work.Tubular.Euc (8 + k))) = 0 := by
      by_contra hne
      exact h hne
    rw [Work.Tubular.normalNorm] at h0
    exact norm_eq_zero.mp h0

end Work.ThomBordism.KeyLocal
