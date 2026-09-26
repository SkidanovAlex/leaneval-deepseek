import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap
import Submission.TorusCollinearity
import Submission.SecantSpace
import Submission.TrisecantLocus
import Submission.TrisecantClosed
import Submission.StrictZero
import Submission.TrisecantTransverse
import Submission.MiddleConvergence
import Submission.SheetAssembly
import Submission.Torus1Chart

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 step (iii), assembly item (c) — strict data of converging
classes converge along the sheet and enter the chart

With (a) the sheet local section (`ClassSection.lean`) and (b) the middle
convergence (`MiddleConvergence.lean`) in hand, the chart-local open-map
lemma of the `TrisecantTransverse.lean` header is assembled as follows:
classes `yₙ ∈ O = trisecantSet r` converging to the class `c₀` of a strict
base data point `z₀` (of a `ZeroSet1Chart`) are lifted by the sheet to
ordered chords `Pₙ → p₀` (`SheetAssembly.exists_lift_of_tendsto`), and the
canonical strict middles converge to the middle of `z₀`
(`MiddleConvergence.middle_tendsto_of_class_tendsto` instanced at the
strict base); hence the strict data triples
`Dₙ = ((Pₙ.a, Pₙ.b), classMiddle yₙ)` converge to the base triple `z₀`
(step 1, `strictData_tendsto_of_class_tendsto`).  The strict data triples
are eventually strict zero-set points over their classes
(`strictZeroData_of_class_tendsto`), so — entering the open chart window —
every class sequence converging to `c₀` is eventually realised by chart
parameters converging to the base parameter (step 2,
`classes_eventually_enter_chart`).  From this, every neighbourhood-issue
of the open-map lemma reduces to the chart trace (`chartLift c '' J` with
`J` any open interval neighbourhood of the base parameter), the content of
step 3 (`classes_eventually_in_chart_trace`).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-! ## 0. The chord and the strict middle of a strict base data point -/

/-- The ordered chord of a zero-set point (its first two parameters). -/
def chordOfZeroSet {r : ℝ → Space} (h : IsSmoothKnot r) (z₀ : ZeroSetPoint r) : OrderedPairs :=
  ⟨((z₀ : KnotParamTriple).1, (z₀ : KnotParamTriple).2.1), zeroChord_endpoints_ne h z₀⟩

/-- The class of a zero-set point is the class of its chord. -/
lemma zeroChordClass_eq_mobiusCover_chordOfZeroSet {r : ℝ → Space} (h : IsSmoothKnot r)
    (z₀ : ZeroSetPoint r) : zeroChordClass h z₀ = mobiusCover (chordOfZeroSet h z₀) := by
  rfl

/-- The third coordinate of a *strict* zero-set point is a strict middle of
its chord. -/
lemma strict_middle_of_strictZero {r : ℝ → Space} (h : IsSmoothKnot r) {z₀ : ZeroSetPoint r}
    (hz₀ : strictZero r z₀) :
    IsMiddleOnChord r (chordOfZeroSet h z₀).1.1 (chordOfZeroSet h z₀).1.2
      (z₀ : KnotParamTriple).2.2 := by
  change IsMiddleOnOpenChord r (z₀ : KnotParamTriple).1 (z₀ : KnotParamTriple).2.1
    (z₀ : KnotParamTriple).2.2
  simpa [strictZero] using hz₀

/-- Real representatives of the chord of a strict zero-set point in
transverse general position: the torus-level hypothesis provides
fundamental-domain representatives of every collinear off-diagonal triple,
with the chord transverse at both endpoints. -/
lemma transverseReps_of_baseData {r : ℝ → Space} (h : IsSmoothKnot r) {z₀ : ZeroSetPoint r}
    (hgp : TorusGeneralPositionTransverse r) :
    ∃ A₀ B₀ : ℝ,
      (A₀ : AddCircle period) = (z₀ : KnotParamTriple).1 ∧
      (B₀ : AddCircle period) = (z₀ : KnotParamTriple).2.1 ∧
      r A₀ ≠ r B₀ ∧ ChordOffEndpointTangents r A₀ B₀ := by
  have hcol : torusCollinearity r (z₀ : KnotParamTriple) = 0 :=
    (mem_trisecantZeroSet_iff (z₀ : KnotParamTriple)).mp z₀.2 |>.1
  have hoff : (z₀ : KnotParamTriple) ∈ TorusOffDiag r :=
    (mem_trisecantZeroSet_iff (z₀ : KnotParamTriple)).mp z₀.2 |>.2
  rcases hgp (z₀ : KnotParamTriple) hcol hoff with ⟨A₀, B₀, M₀, hA0f, hB0f, hM0f,
    hA0c, hB0c, hM0c, hGP⟩
  refine ⟨A₀, B₀, hA0c, hB0c, ?_, ?_⟩
  · -- r A₀ ≠ r B₀ from distinct circle classes + knotMap injectivity
    have hcls : (A₀ : AddCircle period) ≠ (B₀ : AddCircle period) := by
      rw [hA0c, hB0c]
      exact (TorusOffDiag_iff_params h (z₀ : KnotParamTriple)).mp hoff |>.1
    have hk : knotMap r (A₀ : AddCircle period) ≠ knotMap r (B₀ : AddCircle period) :=
      (knotMap_injective h).ne hcls
    simpa [knotMap_eq_r h A₀, knotMap_eq_r h B₀] using hk
  · exact hGP.2.chord_off

/-! ## 1. Strict data of converging classes converge to the base data -/

/-- **Middle convergence at a strict base**: the canonical strict middles of
classes converging to the class of the strict base data point converge to
the middle parameter of the base point.  (Instantiation of
`MiddleConvergence.middle_tendsto_of_class_tendsto` at the base chord, with
the real representatives and endpoint transversality supplied by
`transverseReps_of_baseData`.) -/
theorem middle_tendsto_of_strictBase {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) {z₀ : ZeroSetPoint r} (hz₀ : strictZero r z₀)
    (hgp : TorusGeneralPositionTransverse r) {y : ℕ → OpenMobius}
    (hyO : ∀ n : ℕ, y n ∈ trisecantSet r)
    (hy : Tendsto y atTop (𝓝 (zeroChordClass h z₀))) :
    Tendsto (fun n : ℕ => classMiddle r (y n) (hyO n)) atTop
      (𝓝 ((z₀ : KnotParamTriple).2.2)) := by
  rcases transverseReps_of_baseData h hgp with ⟨A₀, B₀, hA0, hB0, hAne, hchord⟩
  have hmid := middle_tendsto_of_class_tendsto h hqf (p₀ := chordOfZeroSet h z₀)
    (m₀ := (z₀ : KnotParamTriple).2.2) (A₀ := A₀) (B₀ := B₀)
    hA0 hB0 hAne hchord
    (strict_middle_of_strictZero h hz₀) hyO
    (by simpa [zeroChordClass_eq_mobiusCover_chordOfZeroSet] using hy)
  simpa [chordOfZeroSet, zeroChordClass_eq_mobiusCover_chordOfZeroSet] using hmid

/-- **Strict data convergence over the sheet (assembly (c), step 1).**  A
class sequence `yₙ ∈ O` converging to the class of the strict base data
point `z₀` is lifted by the sheet at the base chord to ordered chords
`Pₙ → p₀` (`SheetAssembly.exists_lift_of_tendsto`, so `mobiusCover (Pₙ) =
yₙ` eventually), and the strict data triples
`Dₙ = (Pₙ.a, (Pₙ.b, classMiddle yₙ))` converge to the base triple `z₀`
(first two coordinates by chord convergence, middle by
`middle_tendsto_of_strictBase`). -/
theorem strictData_tendsto_of_class_tendsto {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) {z₀ : ZeroSetPoint r} (hz₀ : strictZero r z₀)
    (hgp : TorusGeneralPositionTransverse r) {y : ℕ → OpenMobius}
    (hyO : ∀ n : ℕ, y n ∈ trisecantSet r)
    (hy : Tendsto y atTop (𝓝 (zeroChordClass h z₀))) :
    ∃ P : ℕ → OrderedPairs,
      Tendsto P atTop (𝓝 (chordOfZeroSet h z₀)) ∧
      (∀ᶠ n in atTop, mobiusCover (P n) = y n) ∧
      Tendsto (fun n : ℕ =>
          ((P n).1.1, ((P n).1.2, classMiddle r (y n) (hyO n)))) atTop
        (𝓝 (z₀ : KnotParamTriple)) := by
  let p₀ : OrderedPairs := chordOfZeroSet h z₀
  let sh : MobiusSheet p₀ := Classical.choice (MobiusSheet.nonempty p₀)
  rcases MobiusSheet.exists_lift_of_tendsto sh hy with ⟨P, hP, hPc⟩
  have hmid := middle_tendsto_of_strictBase h hqf hz₀ hgp hyO hy
  have hP₁ : Tendsto (fun n : ℕ => (P n).1.1) atTop (𝓝 p₀.1.1) := by
    have hf : Continuous (fun pp : OrderedPairs => pp.1.1) :=
      continuous_fst.comp continuous_subtype_val
    simpa [Function.comp_def] using (hf.tendsto p₀).comp hP
  have hP₂ : Tendsto (fun n : ℕ => (P n).1.2) atTop (𝓝 p₀.1.2) := by
    have hf : Continuous (fun pp : OrderedPairs => pp.1.2) :=
      continuous_snd.comp continuous_subtype_val
    simpa [Function.comp_def] using (hf.tendsto p₀).comp hP
  have htri : Tendsto (fun n : ℕ =>
      ((P n).1.1, ((P n).1.2, classMiddle r (y n) (hyO n)))) atTop
      (𝓝 (p₀.1.1, (p₀.1.2, (z₀ : KnotParamTriple).2.2))) := by
    have hm2 : Tendsto (fun n : ℕ => ((P n).1.2, classMiddle r (y n) (hyO n))) atTop
        (𝓝 (p₀.1.2, (z₀ : KnotParamTriple).2.2)) := Filter.Tendsto.prodMk_nhds hP₂ hmid
    exact Filter.Tendsto.prodMk_nhds hP₁ hm2
  refine ⟨P, ?_, hPc, ?_⟩
  · simpa [p₀] using hP
  · have htarget : (p₀.1.1, (p₀.1.2, (z₀ : KnotParamTriple).2.2)) = (z₀ : KnotParamTriple) := by
      ext <;> simp [p₀, chordOfZeroSet]
    simpa [htarget] using htri

/-! ## 2. The strict data triples are eventually strict zero-set points -/

/-- The strict data triple of a class over its lifted chord is a collinear
off-diagonal (hence zero-set) triple: strict middle points are collinear
with the chord and lie off the endpoints. -/
lemma zeroSetPoint_of_classMiddle_on_rep {r : ℝ → Space} (h : IsSmoothKnot r)
    (c : OpenMobius) (hc : c ∈ trisecantSet r) (P : OrderedPairs)
    (hPc : mobiusCover P = c) :
    ((P.1.1, (P.1.2, classMiddle r c hc)) : KnotParamTriple) ∈ trisecantZeroSet r := by
  have hm : IsMiddleOnChord r P.1.1 P.1.2 (classMiddle r c hc) :=
    classMiddle_middle_on_rep c hc P hPc
  have hcol : torusCollinearity r (P.1.1, (P.1.2, classMiddle r c hc)) = 0 := by
    have hO : (P.1.1, (P.1.2, classMiddle r c hc)) ∈ openMiddleData r := by
      change IsMiddleOnOpenChord r P.1.1 P.1.2 (classMiddle r c hc)
      simpa [IsMiddleOnOpenChord, IsMiddleOnChord] using hm
    exact openMiddleData_subset_collinearity_zero r hO
  have hoff : (P.1.1, (P.1.2, classMiddle r c hc)) ∈ TorusOffDiag r := by
    have hab : knotMap r P.1.1 ≠ knotMap r P.1.2 := by
      exact (knotMap_injective h).ne P.2
    have hO : (P.1.1, (P.1.2, classMiddle r c hc)) ∈ openMiddleData r := by
      change IsMiddleOnOpenChord r P.1.1 P.1.2 (classMiddle r c hc)
      simpa [IsMiddleOnOpenChord, IsMiddleOnChord] using hm
    have hoff' := openMiddleData_offDiag_of_endpoints_ne r hO hab
    simpa [TorusOffDiag] using hoff'
  exact (mem_trisecantZeroSet_iff (P.1.1, (P.1.2, classMiddle r c hc))).mpr ⟨hcol, hoff⟩

/-- Along a lifted class sequence the strict data triples are zero-set
points eventually (they are the canonical strict data over the classes). -/
lemma strictData_in_zeroSet_of_class_tendsto {r : ℝ → Space} (h : IsSmoothKnot r)
    {y : ℕ → OpenMobius} (hyO : ∀ n : ℕ, y n ∈ trisecantSet r) {P : ℕ → OrderedPairs}
    (hPc : ∀ᶠ n in atTop, mobiusCover (P n) = y n) :
    ∀ᶠ n in atTop,
      ((P n).1.1, ((P n).1.2, classMiddle r (y n) (hyO n))) ∈ trisecantZeroSet r := by
  filter_upwards [hPc] with n hPn
  exact zeroSetPoint_of_classMiddle_on_rep h (y n) (hyO n) (P n) hPn

/-! ## 3. Chart entry of converging strict data -/

/-- The class map on a chart lift at the preimage of a zero-set point `q` in
the chart window is the class of the canonical chord of `q`. -/
lemma zeroChordClass_chartLift_of_window {r : ℝ → Space} (h : IsSmoothKnot r)
    {p : KnotParamTriple} (c : ZeroSet1Chart r p) (q : KnotParamTriple)
    (hq : q ∈ trisecantZeroSet r) (hV : q ∈ c.V) :
    zeroChordClass h (chartLift c (c.homeo.symm ⟨q, ⟨hq, hV⟩⟩)) = zeroChordClass h ⟨q, hq⟩ := by
  have hrt : c.homeo (c.homeo.symm ⟨q, ⟨hq, hV⟩⟩) = ⟨q, ⟨hq, hV⟩⟩ :=
    c.homeo.apply_symm_apply ⟨q, ⟨hq, hV⟩⟩
  have hval : (chartLift c (c.homeo.symm ⟨q, ⟨hq, hV⟩⟩) : KnotParamTriple) = q := by
    rw [chartLift_val]
    exact congrArg (fun z : {q0 : KnotParamTriple // q0 ∈ trisecantZeroSet r ∧ q0 ∈ c.V} =>
      (z : KnotParamTriple)) hrt
  apply congrArg (fun z : ZeroSetPoint r => zeroChordClass h z)
  apply Subtype.ext
  exact hval

/-- The class of a zero-set point is the class of the canonical ordered
chord of its underlying triple. -/
lemma zeroChordClass_eq_mobiusCover_of_triple {r : ℝ → Space} (h : IsSmoothKnot r)
    (q : KnotParamTriple) (hq : q ∈ trisecantZeroSet r) :
    zeroChordClass h ⟨q, hq⟩ =
      mobiusCover ⟨(q.1, q.2.1),
        ((TorusOffDiag_iff_params h q).mp ((mem_trisecantZeroSet_iff q).mp hq).2).1⟩ := by
  have hne : q.1 ≠ q.2.1 :=
    ((TorusOffDiag_iff_params h q).mp ((mem_trisecantZeroSet_iff q).mp hq).2).1
  change mobiusCover ⟨(q.1, q.2.1), zeroChord_endpoints_ne h ⟨q, hq⟩⟩ =
      mobiusCover ⟨(q.1, q.2.1), hne⟩
  have hchord : (⟨(q.1, q.2.1), zeroChord_endpoints_ne h ⟨q, hq⟩⟩ : OrderedPairs) =
      ⟨(q.1, q.2.1), hne⟩ := Subtype.ext rfl
  rw [hchord]

/-- **Classes converging to the base class enter the chart (assembly (c),
step 2).**  Let `yₙ ∈ O` converge to the class of the strict base point
`z₀`, in the window of the chart `c` at `(z₀ : KnotParamTriple)`.  The
strict data triples `Dₙ` converge to `z₀` (step 1) and lie in the zero
set eventually, hence — being eventually in the open window `c.V` — they
are chart points with parameters `xₙ` converging to the base parameter and
realising the classes: `zeroChordClass h (chartLift c (xₙ)) = yₙ`
eventually. -/
theorem classes_eventually_in_chart_image {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) {p : KnotParamTriple} {z₀ : ZeroSetPoint r}
    (hz₀ : strictZero r z₀) (hgp : TorusGeneralPositionTransverse r)
    {c : ZeroSet1Chart r p} (hzV : (z₀ : KnotParamTriple) ∈ c.V)
    {y : ℕ → OpenMobius} (hyO : ∀ n : ℕ, y n ∈ trisecantSet r)
    (hy : Tendsto y atTop (𝓝 (zeroChordClass h z₀))) :
    ∃ x : ℕ → ChartInterval c.lo c.hi,
      Tendsto x atTop (𝓝 (c.homeo.symm ⟨(z₀ : KnotParamTriple), ⟨z₀.2, hzV⟩⟩)) ∧
      ∀ᶠ n in atTop, zeroChordClass h (chartLift c (x n)) = y n := by
  classical
  rcases strictData_tendsto_of_class_tendsto h hqf hz₀ hgp hyO hy with ⟨P, hP, hPc, hD⟩
  let D : ℕ → KnotParamTriple := fun n =>
    ((P n).1.1, ((P n).1.2, classMiddle r (y n) (hyO n)))
  have hDZ : ∀ᶠ n in atTop, D n ∈ trisecantZeroSet r := by
    simpa [D] using (strictData_in_zeroSet_of_class_tendsto h hyO hPc)
  have hDV : ∀ᶠ n in atTop, D n ∈ c.V := hD.eventually (c.V_open.mem_nhds hzV)
  have hall : ∀ᶠ n in atTop, D n ∈ trisecantZeroSet r ∧ D n ∈ c.V := hDZ.and hDV
  rcases (eventually_atTop.mp hall) with ⟨N, hN⟩
  let Y : ℕ → OpenMobius := fun k => y (k + N)
  let Dt : ℕ → KnotParamTriple := fun k => D (k + N)
  have hYconv : Tendsto Y atTop (𝓝 (zeroChordClass h z₀)) := by
    change Tendsto (fun k : ℕ => y (k + N)) atTop (𝓝 (zeroChordClass h z₀))
    exact hy.comp (tendsto_nat_add_atTop N)
  have hDt : Tendsto Dt atTop (𝓝 (z₀ : KnotParamTriple)) := by
    change Tendsto (fun k : ℕ => D (k + N)) atTop (𝓝 (z₀ : KnotParamTriple))
    exact hD.comp (tendsto_nat_add_atTop N)
  let w : ℕ → {q : KnotParamTriple // q ∈ trisecantZeroSet r ∧ q ∈ c.V} := fun k =>
    ⟨Dt k, hN (k + N) (by omega)⟩
  let w₀ : {q : KnotParamTriple // q ∈ trisecantZeroSet r ∧ q ∈ c.V} :=
    ⟨(z₀ : KnotParamTriple), z₀.2, hzV⟩
  have hw : Tendsto w atTop (𝓝 w₀) := by
    apply tendsto_subtype_of_tendsto_val
      (s := {q : KnotParamTriple | q ∈ trisecantZeroSet r ∧ q ∈ c.V})
    simpa [w, w₀, Dt, D] using hDt
  let x' : ℕ → ChartInterval c.lo c.hi := fun k => c.homeo.symm (w k)
  have hx' : Tendsto x' atTop (𝓝 (c.homeo.symm w₀)) := by
    have hcont := (c.homeo.symm).continuous.tendsto w₀
    simpa [Function.comp_def, x'] using (hcont.comp hw)
  -- class equality eventually along the shifted sequence
  have hclsEv : ∀ᶠ k in atTop, zeroChordClass h (chartLift c (x' k)) = Y k := by
    rcases (eventually_atTop.mp hPc) with ⟨M, hM⟩
    filter_upwards [eventually_ge_atTop M] with k hk
    have hkn : N ≤ k + N := by omega
    have hkM : M ≤ k + N := by omega
    have hmem := hN (k + N) hkn
    have hoffk : (Dt k) ∈ TorusOffDiag r := ((mem_trisecantZeroSet_iff (Dt k)).mp hmem.1).2
    let pf : (Dt k).1 ≠ (Dt k).2.1 := ((TorusOffDiag_iff_params h (Dt k)).mp hoffk).1
    have hzcl : zeroChordClass h (chartLift c (c.homeo.symm ⟨Dt k, hmem⟩)) =
        mobiusCover ⟨((Dt k).1, (Dt k).2.1), pf⟩ := by
      rw [zeroChordClass_chartLift_of_window h c (Dt k) hmem.1 hmem.2]
      exact zeroChordClass_eq_mobiusCover_of_triple h (Dt k) hmem.1
    have hPc' : mobiusCover (P (k + N)) = y (k + N) := hM (k + N) hkM
    change zeroChordClass h (chartLift c (x' k)) = y (k + N)
    rw [hzcl]
    have hpair : (⟨((Dt k).1, (Dt k).2.1), pf⟩ : OrderedPairs) = P (k + N) := by
      apply Subtype.ext
      dsimp [Dt, D]
    rw [hpair]
    exact hPc'
  -- splice before the tail
  rcases (eventually_atTop.mp hclsEv) with ⟨M2, hM2⟩
  let x : ℕ → ChartInterval c.lo c.hi := fun n => if N ≤ n then x' (n - N) else ⟨c.x₀, c.x₀_mem⟩
  have hxt : Tendsto x atTop (𝓝 (c.homeo.symm w₀)) := by
    have hmain : Tendsto (fun n : ℕ => x' (n - N)) atTop (𝓝 (c.homeo.symm w₀)) :=
      hx'.comp (tendsto_nat_sub_atTop N)
    have heq : x =ᶠ[atTop] (fun n : ℕ => x' (n - N)) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      simp [x, hn]
    exact hmain.congr' heq.symm
  refine ⟨x, ?_, ?_⟩
  · simpa [w₀] using hxt
  · filter_upwards [eventually_ge_atTop (N + M2)] with n hn
    have hnN : N ≤ n := by omega
    have hxn : x n = x' (n - N) := by simp [x, hnN]
    rw [hxn]
    have hcl := hM2 (n - N) (by omega)
    have hyshift : y ((n - N) + N) = y n := by congr 1; omega
    simpa [Y] using (hyshift ▸ hcl)

/-- **Classes are eventually in the class image of any open interval
neighbourhood of the base preimage parameter (assembly (c), step 3).**  The
parameters realising the classes converge to the preimage of the strict
point `z₀` in the chart window, so they enter any open interval `J` around
it: `yₙ ∈ zeroChordClass h '' (chartLift c '' J)` eventually. -/
theorem classes_eventually_in_chart_trace {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) {p : KnotParamTriple} {z₀ : ZeroSetPoint r}
    (hz₀ : strictZero r z₀) (hgp : TorusGeneralPositionTransverse r)
    {c : ZeroSet1Chart r p} (hzV : (z₀ : KnotParamTriple) ∈ c.V)
    {y : ℕ → OpenMobius} (hyO : ∀ n : ℕ, y n ∈ trisecantSet r)
    (hy : Tendsto y atTop (𝓝 (zeroChordClass h z₀)))
    {J : Set (ChartInterval c.lo c.hi)} (hJ : IsOpen J)
    (hJx : c.homeo.symm ⟨(z₀ : KnotParamTriple), ⟨z₀.2, hzV⟩⟩ ∈ J) :
    ∀ᶠ n in atTop, y n ∈ zeroChordClass h '' (chartLift c '' J) := by
  rcases classes_eventually_in_chart_image h hqf hz₀ hgp hzV hyO hy with ⟨x, hx, hcls⟩
  have hJev : ∀ᶠ n in atTop, x n ∈ J := hx.eventually (hJ.mem_nhds hJx)
  filter_upwards [hcls, hJev] with n hcl hJm
  exact ⟨chartLift c (x n), ⟨x n, hJm, rfl⟩, hcl⟩

/-- **Base-point instance of the chart-entry theorem.**  When the strict
point is the chart base (`c : ZeroSet1Chart r (z₀ : KnotParamTriple)`), the
preimage parameter is the base parameter. -/
theorem classes_eventually_in_chart_image_base {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) {z₀ : ZeroSetPoint r} (hz₀ : strictZero r z₀)
    (hgp : TorusGeneralPositionTransverse r) {c : ZeroSet1Chart r (z₀ : KnotParamTriple)}
    {y : ℕ → OpenMobius} (hyO : ∀ n : ℕ, y n ∈ trisecantSet r)
    (hy : Tendsto y atTop (𝓝 (zeroChordClass h z₀))) :
    ∃ x : ℕ → ChartInterval c.lo c.hi,
      Tendsto x atTop (𝓝 ⟨c.x₀, c.x₀_mem⟩) ∧
      ∀ᶠ n in atTop, zeroChordClass h (chartLift c (x n)) = y n := by
  rcases classes_eventually_in_chart_image h hqf hz₀ hgp (c := c) c.p_mem hyO hy with ⟨x, hx, hcls⟩
  refine ⟨x, ?_, hcls⟩
  have hpre : c.homeo.symm ⟨(z₀ : KnotParamTriple), ⟨z₀.2, c.p_mem⟩⟩ = ⟨c.x₀, c.x₀_mem⟩ := by
    have hcw : c.homeo ⟨c.x₀, c.x₀_mem⟩ = ⟨(z₀ : KnotParamTriple), ⟨z₀.2, c.p_mem⟩⟩ := by
      apply Subtype.ext
      exact c.base
    rw [← hcw]
    exact c.homeo.symm_apply_apply ⟨c.x₀, c.x₀_mem⟩
  simpa [hpre] using hx

/-- **Base-point instance of the chart-trace theorem.** -/
theorem classes_eventually_in_chart_trace_base {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) {z₀ : ZeroSetPoint r} (hz₀ : strictZero r z₀)
    (hgp : TorusGeneralPositionTransverse r) {c : ZeroSet1Chart r (z₀ : KnotParamTriple)}
    {y : ℕ → OpenMobius} (hyO : ∀ n : ℕ, y n ∈ trisecantSet r)
    (hy : Tendsto y atTop (𝓝 (zeroChordClass h z₀)))
    {J : Set (ChartInterval c.lo c.hi)} (hJ : IsOpen J)
    (hJx : ⟨c.x₀, c.x₀_mem⟩ ∈ J) :
    ∀ᶠ n in atTop, y n ∈ zeroChordClass h '' (chartLift c '' J) := by
  rcases classes_eventually_in_chart_image_base h hqf hz₀ hgp hyO hy with ⟨x, hx, hcls⟩
  have hJev : ∀ᶠ n in atTop, x n ∈ J := hx.eventually (hJ.mem_nhds hJx)
  filter_upwards [hcls, hJev] with n hcl hJm
  exact ⟨chartLift c (x n), ⟨x n, hJm, rfl⟩, hcl⟩

end LeanEval.KnotTheory.Quadrisecant
