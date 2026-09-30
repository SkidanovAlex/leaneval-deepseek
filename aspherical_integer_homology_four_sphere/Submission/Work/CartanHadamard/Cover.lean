/-
# Cartan–Hadamard: the exponential map is a covering map

This file assembles the evenly-covered neighbourhood argument.  Fix `p ∈ M`, let `F = GExp p`, and
let `ρ > 0` be a uniform injectivity radius (`InjAllAtLeast hmet ρ`, which exists on a compact
manifold).  For `y ∈ M` put

* `B = {w ∈ T_yM | ‖w‖ < ρ}` and `V = GExp y '' B` (an open neighbourhood of `y`), and
* for `ṽ ∈ F ⁻¹' {y}`, the **sheet** `U ṽ = translate ṽ '' B ⊆ T_pM`.

The four set-theoretic properties of the sheets — they are pairwise disjoint, they cover `F ⁻¹' V`,
each maps injectively under `F`, and `F` maps each onto `V` — follow from the universal property of
the translate (`Work.CartanHadamard.translate_eq_of_lift`), from uniqueness of lifts
(`Work.CartanHadamard.lift_unique_GExp`) and from the covering property of the translates
(`Work.CartanHadamard.exists_translate_eq`).  The remaining two inputs are the continuity of the
translate in `w` (`Work.CartanHadamard.continuousOn_translate`) and the resulting openness of the
sheets (`Work.CartanHadamard.isOpen_translate_image`); they are hypotheses of the auxiliary theorem
`isCoveringMap_GExp_aux` and discharged in `isCoveringMap_GExp`.
-/
import Submission.Work.CartanHadamard.Basic
import Submission.Work.CartanHadamard.Translate
import Submission.Work.CartanHadamard.exists_lift_from_vector
import Submission.Work.CartanHadamard.isCoveringMap_of_sheets
import Submission.Work.CartanHadamard.continuousOn_translate
import Submission.Work.CartanHadamard.isOpen_translate_image
import Submission.Work.RiemLib.UniformInj

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open LeanEval.Geometry.SphereTheorem

namespace Work.CartanHadamard

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- The curve `τ ↦ GExp y (τ • w)` is `C¹`, in the form needed by the lifting theorem. -/
theorem contMDiffOn_curv (hmet : IsMetricCompatible cov) (y : M) (w : TangentSpace I y) :
    ContMDiffOn 𝓘(ℝ) I 1 (fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet y (τ • w))
      (Set.Icc (0 : ℝ) 1) :=
  contMDiffOn_GExp_ray (cov := cov) hmet y w

/-- **The evenly-covered-neighbourhood data of the exponential map.**  This is the mathematical
content of the Cartan–Hadamard covering theorem, with the two analytic inputs (continuity of the
translate and openness of the sheets) taken as hypotheses. -/
theorem isCoveringMap_GExp_aux (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) (p : M) (ρ : ℝ) (hρpos : 0 < ρ)
    (hρ : Submission.InjRadius.InjAllAtLeast hmet ρ)
    (hcont : ∀ (y : M) (vt : TangentSpace I p),
      Submission.GlobalExp.GExp (cov := cov) hmet p vt = y →
      ContinuousOn (fun w : TangentSpace I y => translate (cov := cov) hmet htor hK vt w)
        (Metric.ball (0 : TangentSpace I y) ρ))
    (hopen : ∀ (y : M) (vt : TangentSpace I p),
      Submission.GlobalExp.GExp (cov := cov) hmet p vt = y →
      IsOpen ((fun w : TangentSpace I y => translate (cov := cov) hmet htor hK vt w) ''
        Metric.ball (0 : TangentSpace I y) ρ)) :
    IsCoveringMap (fun v : TangentSpace I p => Submission.GlobalExp.GExp (cov := cov) hmet p v) := by
  refine isCoveringMap_of_sheets _ ?_ ?_
  · intro y
    exact discreteTopology_fiber_GExp (cov := cov) hmet htor hK p y
  · intro y
    set B : Set (TangentSpace I y) := Metric.ball (0 : TangentSpace I y) ρ with hBdef
    have hBopen : IsOpen B := Metric.isOpen_ball
    have hBmem : ∀ w : TangentSpace I y, w ∈ B ↔ ‖w‖ < ρ := by
      intro w
      rw [hBdef, Metric.mem_ball, dist_eq_norm, sub_zero]
    set V : Set M :=
      (fun w : TangentSpace I y => Submission.GlobalExp.GExp (cov := cov) hmet y w) '' B with hVdef
    have hVopen : IsOpen V :=
      isOpenMap_GExp (cov := cov) hmet htor hK y B hBopen
    have hyV : y ∈ V :=
      ⟨0, Metric.mem_ball_self hρpos, Submission.GlobalExp.GExp_zero hmet y⟩
    have hGinj : Set.InjOn
        (fun w : TangentSpace I y => Submission.GlobalExp.GExp (cov := cov) hmet y w) B :=
      fun a ha b hb hab => hρ y a b ((hBmem a).mp ha) ((hBmem b).mp hb) hab
    have hcont_f : Continuous (fun v : TangentSpace I p =>
        Submission.GlobalExp.GExp (cov := cov) hmet p v) :=
      (isLocalHomeomorph_GExp (cov := cov) hmet htor hK p).continuous
    refine ⟨V, hVopen, hyV, fun vt => (fun w : TangentSpace I y =>
      translate (cov := cov) hmet htor hK vt.1 w) '' B, ?_, ?_, ?_, ?_, ?_⟩
    · -- the open-set condition of `IsOpen.trivializationDiscrete`
      intro vt W hWV
      constructor
      · intro hW
        exact (hW.preimage hcont_f).inter (hopen y vt.1 vt.2)
      · intro hW
        have heq : (fun v : TangentSpace I p => Submission.GlobalExp.GExp (cov := cov) hmet p v) ''
            ((fun v : TangentSpace I p => Submission.GlobalExp.GExp (cov := cov) hmet p v) ⁻¹' W ∩
              (fun w : TangentSpace I y => translate (cov := cov) hmet htor hK vt.1 w) '' B) = W := by
          apply Set.Subset.antisymm
          · rintro z ⟨u, ⟨huW, -⟩, rfl⟩
            exact huW
          · intro z hz
            obtain ⟨w, hwB, hwG⟩ := hWV hz
            refine ⟨translate (cov := cov) hmet htor hK vt.1 w, ⟨?_, ⟨w, hwB, rfl⟩⟩, ?_⟩
            · rw [Set.mem_preimage, translate_apply (cov := cov) hmet htor hK vt.2 w]
              simp only [hwG]
              exact hz
            · exact (translate_apply (cov := cov) hmet htor hK vt.2 w).trans hwG
        rw [← heq]
        exact (isOpenMap_GExp (cov := cov) hmet htor hK p) _ hW
    · -- `SurjOn`
      intro vt z hz
      obtain ⟨w, hwB, hwG⟩ := hz
      exact ⟨translate (cov := cov) hmet htor hK vt.1 w, ⟨w, hwB, rfl⟩,
        (translate_apply (cov := cov) hmet htor hK vt.2 w).trans hwG⟩
    · -- `InjOn`
      intro vt
      rintro u ⟨w, hwB, rfl⟩ u' ⟨w', hw'B, rfl⟩ heq
      have h1 : Submission.GlobalExp.GExp (cov := cov) hmet y w
          = Submission.GlobalExp.GExp (cov := cov) hmet y w' := by
        rw [← translate_apply (cov := cov) hmet htor hK vt.2 w,
          ← translate_apply (cov := cov) hmet htor hK vt.2 w']
        exact heq
      rw [hGinj hwB hw'B h1]
    · -- pairwise disjointness of the sheets
      rw [Pairwise]
      intro vt vt' hne
      change Disjoint ((fun w : TangentSpace I y => translate (cov := cov) hmet htor hK vt.1 w) '' B)
        ((fun w : TangentSpace I y => translate (cov := cov) hmet htor hK vt'.1 w) '' B)
      rw [Set.disjoint_left]
      rintro u ⟨w, hwB, huw⟩ ⟨w', hw'B, hu'w⟩
      -- two continuous lifts of the same radial curve `τ ↦ GExp y (τ • w)`
      set c : ℝ → M := fun τ => Submission.GlobalExp.GExp (cov := cov) hmet y (τ • w) with hcdef
      have hc0 : c 0 = y := by
        rw [hcdef]
        show Submission.GlobalExp.GExp (cov := cov) hmet y ((0 : ℝ) • w) = y
        rw [zero_smul, Submission.GlobalExp.GExp_zero]
      have hcc1 : ContMDiffOn 𝓘(ℝ) I 1 c (Set.Icc (0 : ℝ) 1) := by
        rw [hcdef]
        exact contMDiffOn_curv (cov := cov) hmet y w
      have hww : w = w' := hGinj hwB hw'B (by
        show Submission.GlobalExp.GExp (cov := cov) hmet y w
          = Submission.GlobalExp.GExp (cov := cov) hmet y w'
        rw [← translate_apply (cov := cov) hmet htor hK vt.2 w,
          ← translate_apply (cov := cov) hmet htor hK vt'.2 w']
        exact congrArg (fun v : TangentSpace I p =>
          Submission.GlobalExp.GExp (cov := cov) hmet p v) (huw.trans hu'w.symm))
      have hu'w' : translate (cov := cov) hmet htor hK vt'.1 w = u := by
        rw [hww]
        exact hu'w
      obtain ⟨K, hKpos, hKlt⟩ := Work.RiemLib.exists_lt_pi_div_sqrt (max ‖vt.1‖ ‖vt'.1‖
        + Submission.Length.curveLength (I := I) c 0 1 + 1)
      have hlt₁ : ‖vt.1‖ + Submission.Length.curveLength (I := I) c 0 1
          < Real.pi / Real.sqrt K := by
        have h1 : ‖vt.1‖ ≤ max ‖vt.1‖ ‖vt'.1‖ := le_max_left _ _
        linarith
      have hlt₂ : ‖vt'.1‖ + Submission.Length.curveLength (I := I) c 0 1
          < Real.pi / Real.sqrt K := by
        have h1 : ‖vt'.1‖ ≤ max ‖vt.1‖ ‖vt'.1‖ := le_max_right _ _
        linarith
      obtain ⟨W₁, hW₁c, hW₁0, hW₁G, -⟩ :=
        exists_lift_from_vector (cov := cov) hmet htor hKpos (hK K hKpos) (p := p)
          (h := c) (S := 1) one_pos hcc1 (by rw [hc0]; exact vt.2) hlt₁
      obtain ⟨W₂, hW₂c, hW₂0, hW₂G, -⟩ :=
        exists_lift_from_vector (cov := cov) hmet htor hKpos (hK K hKpos) (p := p)
          (h := c) (S := 1) one_pos hcc1 (by rw [hc0]; exact vt'.2) hlt₂
      have he₁ : W₁ 1 = translate (cov := cov) hmet htor hK vt.1 w := by
        rw [hcdef] at hW₁G
        exact translate_eq_of_lift (cov := cov) hmet htor hK vt.2 w hW₁c hW₁0 hW₁G
      have he₂ : W₂ 1 = translate (cov := cov) hmet htor hK vt'.1 w := by
        rw [hcdef] at hW₂G
        exact translate_eq_of_lift (cov := cov) hmet htor hK vt'.2 w hW₂c hW₂0 hW₂G
      have hagree : W₁ 1 = W₂ 1 := by
        rw [he₁, he₂]
        exact huw.trans hu'w'.symm
      haveI : PreconnectedSpace ↥(Set.Icc (0 : ℝ) 1) :=
        Subtype.preconnectedSpace (isPreconnected_Icc (a := (0 : ℝ)) (b := 1))
      have hfun : (fun τ : ↥(Set.Icc (0 : ℝ) 1) => W₁ τ.1)
          = fun τ : ↥(Set.Icc (0 : ℝ) 1) => W₂ τ.1 :=
        lift_unique_GExp (cov := cov) hmet htor hK p hW₁c.domRestrict hW₂c.domRestrict
          (fun τ => by rw [hW₁G τ.1 τ.2, hW₂G τ.1 τ.2])
          (a₀ := ⟨1, ⟨zero_le_one, le_rfl⟩⟩) hagree
      have hsub : vt.1 = vt'.1 := by
        have h0 := congrFun hfun ⟨0, ⟨le_refl 0, zero_le_one⟩⟩
        simpa [hW₁0, hW₂0] using h0
      exact hne (Subtype.ext hsub)
    · -- exhaustiveness: every preimage of `V` lies in the sheet of its fibre index
      intro u hu
      obtain ⟨w, hwB, hwG⟩ := hu
      obtain ⟨vt, hvt, htr⟩ :=
        exists_translate_eq (cov := cov) hmet htor hK (hu := hwG.symm)
      refine Set.mem_iUnion.mpr ⟨⟨vt, hvt⟩, ?_⟩
      exact ⟨w, hwB, htr⟩

/-- **The exponential map `GExp p` is a covering map** (Cartan–Hadamard). -/
theorem isCoveringMap_GExp (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) (p : M) :
    IsCoveringMap (fun v : TangentSpace I p =>
      Submission.GlobalExp.GExp (cov := cov) hmet p v) := by
  obtain ⟨ρ, hρpos, hρ⟩ := Submission.UniformInj.exists_pos_injAllAtLeast (cov := cov) hmet
  refine isCoveringMap_GExp_aux (cov := cov) hmet htor hK p ρ hρpos hρ ?_ ?_
  · intro y vt hvt
    exact continuousOn_translate (cov := cov) hmet htor hK hvt hρpos
  · intro y vt hvt
    exact isOpen_translate_image (cov := cov) hmet htor hK hvt hρpos
      (Submission.InjRadius.injAtLeast_of_injAllAtLeast hmet hρ y)
      (continuousOn_translate (cov := cov) hmet htor hK hvt hρpos)

/-- **The exponential map at `p` is a covering map** (the statement in the form delivered to the
rest of the project: the domain is the model space `E`). -/
theorem isCoveringMap_gexp (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) (p : M) :
    IsCoveringMap (Submission.XuLift.gexpMap (cov := cov) hmet p) :=
  isCoveringMap_GExp (cov := cov) hmet htor hK p

end

end Work.CartanHadamard
