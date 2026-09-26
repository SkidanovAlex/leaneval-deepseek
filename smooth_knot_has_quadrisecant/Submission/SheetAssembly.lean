import Mathlib
import ChallengeDeps
import Submission.ClassSection

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# Milestone-2 step (iii), assembly items (b)–(c) — convergence along the
sheet and the class-level local section over the strict locus

The open-map half of the local 1-manifold structure of the trisecant locus
`O` (`TrisecantTransverse.lean` header) is assembled from (a) the sheet
local section (`ClassSection.lean`: `MobiusSheet` and `chordBoxHomeo`),
(b) the convergence of strict data over class sequences along the sheet,
and (c) the local-section/open-map statement for `zeroChordClass` over
strict data.  This module provides the *topological plumbing* of item (b):

1. **subtype convergence** (`tendsto_subtype_of_tendsto_val`): a
   `ℕ`-sequence valued in a subset converges to a point of the subset
   exactly when its value sequence converges to the point's value (the
   subspace topology is the pullback of the ambient one —
   `nhds_subtype_eq_comap`);
2. **class-sequence lift onto the sheet** (`MobiusSheet.exists_lift_of_tendsto`):
   a class sequence `yₙ` converging to the base class `mobiusCover p₀` of
   a sheet lies eventually in the sheet's target, so the continuous
   section `MobiusSheet.sec` lifts it (eventually, and through the
   subtype-valued sequence `zₙ = ⟨yₙ, ·⟩`) to ordered pairs
   `Xₙ → p₀` with `mobiusCover (Xₙ) = yₙ` eventually — the chord
   representatives of a converging class sequence converge along the
   sheet.
3. **the generic sheet lift and the circle-to-real lift**
   (`exists_lift_tendsto_of_localSheet`): for a map `q : X → Y` agreeing
   with an `OpenPartialHomeomorph` `e` on its source, any sequence in `Y`
   converging to `q x₀` (with `x₀ ∈ e.source`) lifts — eventually — to a
   sequence in `X` converging to `x₀` with the original `q`-values
   (`e.toHomeomorphSourceTarget.symm` as the sheet inverse, composed with
   the source inclusion); and its circle instance
   (`exists_real_lift_of_tendsto_circle`): a sequence of points of the
   parameter circle `AddCircle period` converging to `x₀` lifts to a real
   sequence converging to any chosen real lift `X₀` of `x₀` (Mathlib's
   `AddCircle.isCoveringMap_coe` is the covering certificate) — the
   bridge from circle-valued convergence (e.g. of strict middle
   parameters of trisecant classes) to the real-sequence convergence that
   the endpoint-escape lemmas `no_middle_to_endpoint` /
   `no_middle_to_endpoint_b` consume in the middle-cluster analysis.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-! ## 1. Subtype-valued sequence convergence -/

/-- A `ℕ`-sequence valued in a subset of a topological space converges to a
point of the subset when its value sequence converges to the point's value
(the subspace topology on the subset is the pullback of the ambient
topology along the inclusion). -/
lemma tendsto_subtype_of_tendsto_val {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    {a : s} {u : ℕ → s} (hu : Tendsto (fun n : ℕ => (u n : Y)) atTop (𝓝 (a : Y))) :
    Tendsto u atTop (𝓝 a) := by
  rw [nhds_subtype_eq_comap]
  exact (tendsto_comap_iff).mpr hu

/-- The value sequence of a convergent subset-valued sequence converges to
the value of the limit (the inclusion is continuous). -/
lemma tendsto_val_of_tendsto_subtype {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    {a : s} {u : ℕ → s} (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => (u n : Y)) atTop (𝓝 (a : Y)) :=
  (continuous_subtype_val.tendsto a).comp hu

/-! ## 2. Lifting convergent class sequences onto a sheet -/

/-- `n ↦ n + N` tends to infinity (for the shift of a convergent sequence). -/
lemma tendsto_nat_add_atTop (N : ℕ) : Tendsto (fun n : ℕ => n + N) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b, ?_⟩
  intro a ha
  omega

/-- `n ↦ n − N` tends to infinity (for unshifting a convergent tail). -/
lemma tendsto_nat_sub_atTop (N : ℕ) : Tendsto (fun n : ℕ => n - N) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b + N, ?_⟩
  intro a ha
  omega


namespace MobiusSheet

variable {p₀ : OrderedPairs}

/-- A class sequence that lies **everywhere** in the sheet target lifts onto
the sheet: the section produces ordered pairs `Xₙ → p₀` whose classes are
exactly `yₙ` for every `n`. -/
theorem exists_lift_of_mem (sh : MobiusSheet p₀) {y : ℕ → OpenMobius}
    (hymem : ∀ n : ℕ, y n ∈ sh.T) (hy : Tendsto y atTop (𝓝 (mobiusCover p₀))) :
    ∃ X : ℕ → OrderedPairs, Tendsto X atTop (𝓝 p₀) ∧ ∀ n : ℕ, mobiusCover (X n) = y n := by
  let z : ℕ → {c : OpenMobius // c ∈ sh.T} := fun n => ⟨y n, hymem n⟩
  let z₀ : {c : OpenMobius // c ∈ sh.T} := ⟨mobiusCover p₀, sh.class_mem⟩
  have hz : Tendsto z atTop (𝓝 z₀) := by
    apply tendsto_subtype_of_tendsto_val (s := sh.T)
    simpa [z, z₀] using hy
  have hg : Continuous (fun c : {c : OpenMobius // c ∈ sh.T} => sh.sec c.1 c.2) := sh.secContinuous
  let X : ℕ → OrderedPairs := fun n => sh.sec (y n) (hymem n)
  have hXcomp : X = fun n => (fun c : {c : OpenMobius // c ∈ sh.T} => sh.sec c.1 c.2) (z n) := by
    funext n
    rfl
  have htend : Tendsto X atTop (𝓝 p₀) := by
    have hmain : Tendsto (fun n => (fun c : {c : OpenMobius // c ∈ sh.T} => sh.sec c.1 c.2) (z n))
        atTop (𝓝 (sh.sec (mobiusCover p₀) sh.class_mem)) :=
      (hg.tendsto z₀).comp hz
    have hbase : sh.sec (mobiusCover p₀) sh.class_mem = p₀ := sh.sec_base
    rw [hXcomp]
    simpa [hbase] using hmain
  refine ⟨X, htend, ?_⟩
  intro n
  exact sh.sec_comp (y n) (hymem n)

/-- **A class sequence converging to the base class of the sheet lifts onto
the sheet.**  The target `T` of the sheet is an open neighbourhood of
`mobiusCover p₀`, so `yₙ` lies in `T` eventually; passing to the tail where
it does (`exists_lift_of_mem`) and splicing with arbitrary lifts before the
tail, the sheet section produces ordered pairs `Xₙ → p₀` whose classes are
exactly `yₙ` eventually.  This is how converging class sequences acquire
converging *ordered chord representatives* on the sheet. -/
theorem exists_lift_of_tendsto (sh : MobiusSheet p₀) {y : ℕ → OpenMobius}
    (hy : Tendsto y atTop (𝓝 (mobiusCover p₀))) :
    ∃ X : ℕ → OrderedPairs,
      Tendsto X atTop (𝓝 p₀) ∧ ∀ᶠ n in atTop, mobiusCover (X n) = y n := by
  classical
  have h_evenT : ∀ᶠ n in atTop, y n ∈ sh.T := hy.eventually (sh.T_open.mem_nhds sh.class_mem)
  rcases (eventually_atTop.mp h_evenT) with ⟨N, hN⟩
  let Y : ℕ → OpenMobius := fun k => y (k + N)
  have hYmem : ∀ k : ℕ, Y k ∈ sh.T := by
    intro k
    exact hN (k + N) (by omega)
  have hY : Tendsto Y atTop (𝓝 (mobiusCover p₀)) := by
    change Tendsto (fun k : ℕ => y (k + N)) atTop (𝓝 (mobiusCover p₀))
    exact hy.comp (tendsto_nat_add_atTop N)
  rcases exists_lift_of_mem sh hYmem hY with ⟨X', hX', hsec⟩
  let X : ℕ → OrderedPairs := fun n => if N ≤ n then X' (n - N) else
    Classical.choose (mobiusCover_surjective (y n))
  have hXtend : Tendsto X atTop (𝓝 p₀) := by
    have hmain : Tendsto (fun n : ℕ => X' (n - N)) atTop (𝓝 p₀) := hX'.comp (tendsto_nat_sub_atTop N)
    have heq : X =ᶠ[atTop] (fun n : ℕ => X' (n - N)) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      simp [X, hn]
    exact hmain.congr' heq.symm
  refine ⟨X, hXtend, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  have hXn : X n = X' (n - N) := by simp [X, hn]
  rw [hXn]
  have hsec' : mobiusCover (X' (n - N)) = y n := by
    have h0 := hsec (n - N)
    have hy_eq : y ((n - N) + N) = y n := by
      congr 1
      omega
    simpa [Y] using (hy_eq ▸ h0)
  exact hsec'

end MobiusSheet


/-! ## 3. Generic lift of convergent sequences along a local sheet, and the
circle-to-real lift -/

/-- **Generic sheet lift.**  For a map `q : X → Y` agreeing with an open
partial homeomorphism `e` on its source, a sequence in `Y` converging to
`q x₀` (with `x₀ ∈ e.source`) lies eventually in `e.target`, and the sheet
inverse (`e.toHomeomorphSourceTarget.symm`, composed with the source
inclusion) lifts it to a sequence in `X` converging to `x₀` whose `q`-values
are the original sequence eventually.  This abstracts the sheet-lift content
of `MobiusSheet.exists_lift_of_tendsto` to any local sheet (the covering of
the circle by the line, the double cover of the band, …). -/
lemma exists_lift_tendsto_of_localSheet {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (q : X → Y) {x₀ : X} (e : OpenPartialHomeomorph X Y)
    (he : q = e) (hx₀ : x₀ ∈ e.source) {y : ℕ → Y}
    (hy : Tendsto y atTop (𝓝 (q x₀))) :
    ∃ Xs : ℕ → X, Tendsto Xs atTop (𝓝 x₀) ∧ ∀ᶠ n in atTop, q (Xs n) = y n := by
  classical
  have hx₀T : q x₀ ∈ e.target := by
    have hstep : q x₀ = e x₀ := congr_fun he x₀
    rw [hstep]
    exact e.map_source hx₀
  have h_evenT : ∀ᶠ n in atTop, y n ∈ e.target := hy.eventually (e.open_target.mem_nhds hx₀T)
  rcases (eventually_atTop.mp h_evenT) with ⟨N, hN⟩
  let Ys : ℕ → Y := fun k => y (k + N)
  have hYmem : ∀ k : ℕ, Ys k ∈ e.target := by
    intro k
    exact hN (k + N) (by omega)
  have hYs : Tendsto Ys atTop (𝓝 (q x₀)) := by
    change Tendsto (fun k : ℕ => y (k + N)) atTop (𝓝 (q x₀))
    exact hy.comp (tendsto_nat_add_atTop N)
  -- the everywhere-lift on the tail: through the target subtype
  let z : ℕ → {c : Y // c ∈ e.target} := fun k => ⟨Ys k, hYmem k⟩
  let z₀ : {c : Y // c ∈ e.target} := ⟨q x₀, hx₀T⟩
  have hz : Tendsto z atTop (𝓝 z₀) := by
    apply tendsto_subtype_of_tendsto_val (s := e.target)
    simpa [z, z₀] using hYs
  have hgcont : Continuous (fun c : {c : Y // c ∈ e.target} =>
      (e.toHomeomorphSourceTarget.symm c : X)) := by
    have hφinv : Continuous (fun c : {c : Y // c ∈ e.target} =>
        (e.toHomeomorphSourceTarget.symm c : {p : X // p ∈ e.source})) :=
      (e.toHomeomorphSourceTarget.symm).continuous
    exact continuous_subtype_val.comp hφinv
  let Xs : ℕ → X := fun k => (e.toHomeomorphSourceTarget.symm (z k) : X)
  have hbase : (e.toHomeomorphSourceTarget.symm z₀ : X) = x₀ := by
    -- φ.symm ⟨q x₀, hx₀T⟩ = ⟨x₀, hx₀⟩ because (φ ⟨x₀,hx₀⟩ : Y) = e x₀ = q x₀
    have hφbase : e.toHomeomorphSourceTarget ⟨x₀, hx₀⟩ = ⟨q x₀, hx₀T⟩ := by
      apply Subtype.ext
      change (e.toHomeomorphSourceTarget ⟨x₀, hx₀⟩ : Y) = q x₀
      rw [OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe]
      exact (congr_fun he x₀).symm
    have hback : e.toHomeomorphSourceTarget.symm ⟨q x₀, hx₀T⟩ = ⟨x₀, hx₀⟩ := by
      rw [← hφbase]
      exact e.toHomeomorphSourceTarget.symm_apply_apply ⟨x₀, hx₀⟩
    change (e.toHomeomorphSourceTarget.symm z₀ : X) = x₀
    dsimp [z₀]
    exact congrArg Subtype.val hback
  have htend : Tendsto Xs atTop (𝓝 x₀) := by
    have hmain : Tendsto (fun k : ℕ =>
        (e.toHomeomorphSourceTarget.symm (z k) : X)) atTop
        (𝓝 (e.toHomeomorphSourceTarget.symm z₀ : X)) :=
      (hgcont.tendsto z₀).comp hz
    have hz₀eq : (e.toHomeomorphSourceTarget.symm z₀ : X) = x₀ := hbase
    simpa [Xs, hz₀eq] using hmain
  have hsec : ∀ k : ℕ, q (Xs k) = Ys k := by
    intro k
    dsimp [Xs, z]
    have hrinv : (e.toHomeomorphSourceTarget (e.toHomeomorphSourceTarget.symm ⟨Ys k, hYmem k⟩) : Y)
        = Ys k := by
      exact congrArg Subtype.val (e.toHomeomorphSourceTarget.apply_symm_apply ⟨Ys k, hYmem k⟩)
    calc
      q ((e.toHomeomorphSourceTarget.symm ⟨Ys k, hYmem k⟩ : {p : X // p ∈ e.source}) : X)
          = e ((e.toHomeomorphSourceTarget.symm ⟨Ys k, hYmem k⟩ : {p : X // p ∈ e.source}) : X) :=
            congr_fun he _
      _ = (e.toHomeomorphSourceTarget
          (e.toHomeomorphSourceTarget.symm ⟨Ys k, hYmem k⟩) : Y) := by
            rw [OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe]
      _ = Ys k := hrinv
  -- splice the tail lift with arbitrary lifts before N
  let Xt : ℕ → X := fun n => if N ≤ n then Xs (n - N) else x₀
  have hXtend : Tendsto Xt atTop (𝓝 x₀) := by
    have hmain : Tendsto (fun n : ℕ => Xs (n - N)) atTop (𝓝 x₀) := htend.comp (tendsto_nat_sub_atTop N)
    have heq : Xt =ᶠ[atTop] (fun n : ℕ => Xs (n - N)) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      simp [Xt, hn]
    exact hmain.congr' heq.symm
  refine ⟨Xt, hXtend, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  have hXt : Xt n = Xs (n - N) := by simp [Xt, hn]
  rw [hXt]
  have hsec' := hsec (n - N)
  have hy_eq : Ys (n - N) = y n := by
    dsimp [Ys]
    congr 1
    omega
  exact hy_eq ▸ hsec'

/-- **A convergent sequence of circle points lifts to a convergent real
sequence.**  Let `x₀ : AddCircle period` be a point of the parameter circle
and `X₀ : ℝ` a real lift of it (`(X₀ : AddCircle period) = x₀`).  A
sequence `xₙ → x₀` in the circle (which is the quotient of the line by the
period lattice, a covering map by Mathlib's
`AddCircle.isCoveringMap_coe`) lifts — eventually — to a real sequence
`Xₙ → X₀` with `(Xₙ : AddCircle period) = xₙ`.  This is how circle-valued
convergence (e.g. of strict middle parameters of trisecant classes) is
converted into the real-sequence convergence that the endpoint-escape
lemmas `no_middle_to_endpoint` / `no_middle_to_endpoint_b` consume. -/
theorem exists_real_lift_of_tendsto_circle {x₀ : AddCircle period} {X₀ : ℝ}
    (hX₀ : (X₀ : AddCircle period) = x₀) {x : ℕ → AddCircle period}
    (hx : Tendsto x atTop (𝓝 x₀)) :
    ∃ X : ℕ → ℝ, Tendsto X atTop (𝓝 X₀) ∧ ∀ᶠ n in atTop, (X n : AddCircle period) = x n := by
  let q : ℝ → AddCircle period := fun t => (t : AddCircle period)
  have hcv : IsCoveringMap q := by
    simpa [q] using (AddCircle.isCoveringMap_coe (𝕜 := ℝ) (p := period))
  rcases (hcv.isLocalHomeomorph X₀) with ⟨e, hX₀e, hfe⟩
  have hqX₀ : q X₀ = x₀ := by simpa [q] using hX₀
  rcases exists_lift_tendsto_of_localSheet q e hfe hX₀e (by simpa [hqX₀] using hx) with
    ⟨X, hXt, hev⟩
  refine ⟨X, ?_, ?_⟩
  · simpa [q] using hXt
  · filter_upwards [hev] with n hn
    simpa [q] using hn
end LeanEval.KnotTheory.Quadrisecant
