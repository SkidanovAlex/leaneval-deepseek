import Mathlib
import Submission.Work.ThomBordism.frameClassDefs
import Submission.Work.ThomBordism.thomClass_fibreGenerator
import Submission.Work.Tubular.modelClass_fibre_span_top
import Submission.Work.ThomBordism.nfGen_ne_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The frame reading of the tautological Thom class generates the standard pair

`Work.ThomBordism.frameClass k σ ∈ H^k(ℝ^k, ℝ^k∖0;ℤ)` is the pullback of the tautological Thom
class `τ` along the frame evaluation `frameEval σ`, a homeomorphism of pairs
`(ℝ^k, ℝ^k∖0) ≅ (γ_{ogMk σ}, γ_{ogMk σ}∖0)`.  Hence `frameClass k σ` is the fibrewise generator of
`τ` read in the frame `σ`: it generates the `ℤ`-module `H^k(ℝ^k, ℝ^k∖0;ℤ)`, and since it is
independent of `σ` (`Work.ThomBordism.frameClass_eq`) it is `± stdThomGen`.

The proof is "a generator survives a surjection":

* `Work.ThomBordism.thomClass_fibreGenerator` applied to the tautological bundle gives that the
  restriction of `τ` to the fibre over `P = ogMk σ` generates `H^k(γ_P, γ_P∖0;ℤ)`;
* the frame evaluation factors through the fibre inclusion as `frameEvalMap σ = fibreIncl ∘ Φ` with
  `Φ : ℝ^k → γ_P` the coordinate map, so `frameClass k σ = Φ^*(fibreRes …)` (functoriality);
* `Φ` has the right inverse `Ψ = readFrame σ ∘ evalVec`
  (`Work.ThomBordism.readFrame_sum_smul`), and `Ψ` is a map of pairs because its composite with `Φ`
  is the identity on the fibre
  (`Work.ThomBordism.sum_inner_smul_eq_self`, via the fact that the corrected frame spans the plane
  of `σ`).  Hence `Ψ^*` is a left inverse of `Φ^*`, so `Φ^*` is surjective, and a surjective
  `ℤ`-linear map carries a generator to a generator
  (`Work.Tubular.span_singleton_map_eq_top`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

open Work.ThomBordism.Grassmann

noncomputable section

/-- **A point of the tautological bundle is determined by its plane and its evaluated vector.** -/
theorem eq_of_proj_eq_of_evalVec_eq (k m : ℕ)
    {p p' : (tautologicalBundle k m).TotalSpace} (h1 : p.1 = p'.1)
    (h2 : evalVec p = evalVec p') : p = p' := by
  obtain ⟨x, v⟩ := p
  obtain ⟨x', v'⟩ := p'
  simp only at h1
  subst h1
  have hS : x ∈ (tautologicalBundle k m).baseSet ((tautologicalBundle k m).indexAt x) :=
    (tautologicalBundle k m).mem_baseSet_at x
  have h3 : (show Amb k from ((tautologicalBundle k m).localTriv
        ((tautologicalBundle k m).indexAt x) (⟨x, v⟩ : (tautologicalBundle k m).TotalSpace)).2)
      = (show Amb k from ((tautologicalBundle k m).localTriv
        ((tautologicalBundle k m).indexAt x) (⟨x, v'⟩ : (tautologicalBundle k m).TotalSpace)).2) := by
    have h4 := evalVec_apply_chart (⟨x, v⟩ : (tautologicalBundle k m).TotalSpace)
      ((tautologicalBundle k m).indexAt x) hS
    have h5 := evalVec_apply_chart (⟨x, v'⟩ : (tautologicalBundle k m).TotalSpace)
      ((tautologicalBundle k m).indexAt x) hS
    rw [h4, h5] at h2
    exact peEvalChartO_injective _ _ h2
  have h6 : (tautologicalBundle k m).localTriv ((tautologicalBundle k m).indexAt x)
        (⟨x, v⟩ : (tautologicalBundle k m).TotalSpace)
      = (tautologicalBundle k m).localTriv ((tautologicalBundle k m).indexAt x)
        (⟨x, v'⟩ : (tautologicalBundle k m).TotalSpace) := by
    refine Prod.ext ?_ ?_
    · rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply]
    · exact h3
  have hmem' : (⟨x, v'⟩ : (tautologicalBundle k m).TotalSpace) ∈
      ((tautologicalBundle k m).localTriv ((tautologicalBundle k m).indexAt x)).source := hS
  calc (⟨x, v⟩ : (tautologicalBundle k m).TotalSpace)
      = ((tautologicalBundle k m).localTriv
            ((tautologicalBundle k m).indexAt x)).toOpenPartialHomeomorph.symm
          (((tautologicalBundle k m).localTriv ((tautologicalBundle k m).indexAt x))
            ⟨x, v⟩) :=
        (((tautologicalBundle k m).localTriv ((tautologicalBundle k m).indexAt x)).left_inv' hS).symm
    _ = ((tautologicalBundle k m).localTriv
            ((tautologicalBundle k m).indexAt x)).toOpenPartialHomeomorph.symm
          (((tautologicalBundle k m).localTriv ((tautologicalBundle k m).indexAt x))
            ⟨x, v'⟩) := by rw [h6]
    _ = (⟨x, v'⟩ : (tautologicalBundle k m).TotalSpace) :=
        ((tautologicalBundle k m).localTriv ((tautologicalBundle k m).indexAt x)).left_inv' hmem'

/-- **Two frames representing the same oriented plane span the same subspace.** -/
theorem span_range_eq_of_ogMk_eq {k m : ℕ} {f g : Stiefel k m}
    (h : ogMk k m f = ogMk k m g) :
    Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m)))
      = Submodule.span ℝ (Set.range (g.1 : Fin k → Amb (k + m))) := by
  obtain ⟨A, hA⟩ := Quotient.exact h
  have hg : (g.1 : Fin k → Amb (k + m)) = soActFun A.1 f.1 := by rw [hA]; rfl
  have hf : (f.1 : Fin k → Amb (k + m)) = soActFun A.transpose.1 g.1 := by
    rw [hg]
    exact congrArg Subtype.val (SOk.act_transpose_act A f).symm
  have h1 : ∀ i, soActFun A.1 f.1 i ∈
      Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m))) := by
    intro i
    rw [soActFun]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  have h2 : ∀ i, soActFun A.transpose.1 g.1 i ∈
      Submodule.span ℝ (Set.range (g.1 : Fin k → Amb (k + m))) := by
    intro i
    rw [soActFun]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  have hle1 : Submodule.span ℝ (Set.range (g.1 : Fin k → Amb (k + m))) ≤
      Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m))) := by
    rw [hg]
    exact Submodule.span_le.mpr fun w hw => by obtain ⟨i, rfl⟩ := hw; exact h1 i
  have hle2 : Submodule.span ℝ (Set.range (f.1 : Fin k → Amb (k + m))) ≤
      Submodule.span ℝ (Set.range (g.1 : Fin k → Amb (k + m))) := by
    rw [hf]
    exact Submodule.span_le.mpr fun w hw => by obtain ⟨i, rfl⟩ := hw; exact h2 i
  exact le_antisymm hle2 hle1

/-- A vector of the plane of a frame lies in the span of the frame. -/
theorem mem_span_range_of_memPlane {k : ℕ} (σ : Stiefel k 10) {w : Amb (k + 10)}
    (hw : memPlane (k := k) (m := 10) (ogMk k 10 σ) w) :
    w ∈ Submodule.span ℝ (Set.range (σ.1 : Fin k → Amb (k + 10))) := by
  obtain ⟨f, hf, hwspan⟩ := hw
  have hfg : ogMk k 10 σ = ogMk k 10 f := by rw [← hf]; rfl
  rw [span_range_eq_of_ogMk_eq hfg]
  exact hwspan

theorem span_frameClass (k : ℕ) (hk : 1 ≤ k) (σ : Stiefel k 10) :
    Submodule.span ℤ ({frameClass k σ} : Set (Work.Thom.RelCoh ℤ k (Amb k)
      (framePunct k))) = ⊤ := by
  classical
  set γ : Work.TangentClasses.RealBundle (OG k 10) (Amb k) (ChartIdx k 10) :=
    tautologicalBundle k 10
  set P : OG k 10 := ogMk k 10 σ with hP
  set τ : Work.Thom.OpenThom γ k := (tautologicalThomClass k 10).τ
  have hn : k = Module.finrank ℝ (Amb k) := by simp [Amb]
  have hfib : Submodule.span ℤ ({Work.ThomBordism.fibreRes γ P k τ} : Set
      (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.fibre γ P)
        (Work.ThomBordism.fibrePunctSub γ P))) = ⊤ :=
    thomClass_fibreGenerator γ (tautologicalThomClass k 10) hn P
  -- the coordinate map into the fibre and the reading map back
  let Fib : C(Amb k, ↥(Work.ThomBordism.fibre γ P)) :=
    ⟨fun v => ⟨frameEval k σ v, frameEval_base k σ v⟩,
      (continuous_frameEval_snd k σ).subtype_mk _⟩
  let Ψ : C(↥(Work.ThomBordism.fibre γ P), Amb k) :=
    ⟨fun q => readFrame (fun j => σ.1 j) (evalVec (q : γ.TotalSpace)),
      (readFrame (fun j => σ.1 j)).continuous.comp
        (continuous_evalVec.comp continuous_subtype_val)⟩
  have hFib_app : ∀ v : Amb k, Fib v =
      (⟨frameEval k σ v, frameEval_base k σ v⟩ : ↥(Work.ThomBordism.fibre γ P)) := fun v => rfl
  have hΨ_app : ∀ q : ↥(Work.ThomBordism.fibre γ P),
      Ψ q = readFrame (fun j => σ.1 j) (evalVec (q : γ.TotalSpace)) := fun q => rfl
  have hFibmem : ∀ v ∈ framePunct k, Fib v ∈ Work.ThomBordism.fibrePunctSub γ P := by
    intro v hv
    show (Fib v).1 ∈ Work.ThomBordism.fibrePunct γ P
    refine ⟨?_, ?_⟩
    · show (frameEval k σ v).1 = P
      rw [frameEval_base k σ v, hP]
    · have h := (frameEval_ne_zero_iff k σ v).mpr hv
      rwa [Work.Thom.mem_zeroComplement] at h
  -- the two directions are inverse to each other
  have hΨFib : ∀ v : Amb k, Ψ (Fib v) = v := by
    intro v
    rw [hΨ_app, hFib_app]
    show readFrame (fun j => σ.1 j) (evalVec (frameEval k σ v)) = v
    rw [evalVec_frameEval]
    exact readFrame_sum_smul (fun j => σ.1 j) σ.2 v
  have hFibΨ : ∀ q : ↥(Work.ThomBordism.fibre γ P), Fib (Ψ q) = q := by
    intro q
    refine Subtype.ext (eq_of_proj_eq_of_evalVec_eq k 10 ?_ ?_)
    · show (frameEval k σ (Ψ q)).1 = (q : γ.TotalSpace).1
      rw [frameEval_base k σ (Ψ q)]
      exact (q.2).symm
    · show evalVec (frameEval k σ (Ψ q)) = evalVec (q : γ.TotalSpace)
      rw [evalVec_frameEval, hΨ_app]
      have hmem : evalVec (q : γ.TotalSpace) ∈
          Submodule.span ℝ (Set.range (σ.1 : Fin k → Amb (k + 10))) :=
        mem_span_range_of_memPlane σ (by
          have h := evalVec_memPlane (q : γ.TotalSpace)
          rwa [q.2] at h)
      have hkey := sum_inner_smul_eq_self k σ hmem
      have hread : ((readFrame (fun j => σ.1 j) (evalVec (q : γ.TotalSpace))).ofLp)
          = (fun j => inner ℝ (σ.1 j) (evalVec (q : γ.TotalSpace))) := by
        rw [readFrame_apply]
        rfl
      rw [frameLI_apply, frameLM_apply]
      refine (Finset.sum_congr rfl fun j _ => ?_).trans hkey
      rw [congrFun hread j]
  -- `Ψ` is a map of pairs
  have hΨmem : ∀ q ∈ Work.ThomBordism.fibrePunctSub γ P, Ψ q ∈ framePunct k := by
    intro q hq
    rw [mem_framePunct]
    intro h0
    have hmem : evalVec (q : γ.TotalSpace) ∈
        Submodule.span ℝ (Set.range (σ.1 : Fin k → Amb (k + 10))) :=
      mem_span_range_of_memPlane σ (by
        have h := evalVec_memPlane (q : γ.TotalSpace)
        rwa [q.2] at h)
    have hinner : ∀ j, inner ℝ (σ.1 j) (evalVec (q : γ.TotalSpace)) = 0 :=
      (readFrame_eq_zero_iff (fun j => σ.1 j) (evalVec (q : γ.TotalSpace))).mp h0
    have hzero : evalVec (q : γ.TotalSpace) = 0 := by
      rw [← sum_inner_smul_eq_self k σ hmem]
      simp only [hinner, zero_smul, Finset.sum_const_zero]
    rw [evalVec_eq_zero_iff] at hzero
    exact hq.2 hzero
  -- surjectivity of the pullback along `Fib`
  have hsurj : Function.Surjective
      (Work.Thom.relCohMap Fib (framePunct k) (Work.ThomBordism.fibrePunctSub γ P)
        hFibmem ℤ k).hom := by
    have hcomp_id : Ψ.comp Fib = ContinuousMap.id (Amb k) := ContinuousMap.ext hΨFib
    have hcompA : Work.Thom.relCohMap Ψ (Work.ThomBordism.fibrePunctSub γ P) (framePunct k)
          hΨmem ℤ k
        ≫ Work.Thom.relCohMap Fib (framePunct k) (Work.ThomBordism.fibrePunctSub γ P)
            hFibmem ℤ k
        = 𝟙 (Work.Thom.RelCoh ℤ k (Amb k) (framePunct k)) := by
      rw [Work.Thom.relCohMap_compA (A := framePunct k)
        (B := Work.ThomBordism.fibrePunctSub γ P) (C := framePunct k) Fib Ψ hFibmem
        hΨmem (fun v hv => hΨmem (Fib v) (hFibmem v hv)) ℤ k]
      exact (Work.Thom.relCohMap_congrA (A := framePunct k) (B := framePunct k) hcomp_id
        (fun v hv => hΨmem (Fib v) (hFibmem v hv)) (fun _ hv => hv) ℤ k).trans
        (Work.Thom.relCohMap_idA (framePunct k) ℤ k)
    have hlin : (Work.Thom.relCohMap Fib (framePunct k) (Work.ThomBordism.fibrePunctSub γ P)
          hFibmem ℤ k).hom.comp (Work.Thom.relCohMap Ψ (Work.ThomBordism.fibrePunctSub γ P)
          (framePunct k) hΨmem ℤ k).hom = LinearMap.id := by
      have h := congrArg ModuleCat.Hom.hom hcompA
      rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact fun y => ⟨(Work.Thom.relCohMap Ψ (Work.ThomBordism.fibrePunctSub γ P) (framePunct k)
      hΨmem ℤ k).hom y, LinearMap.congr_fun hlin y⟩
  -- `frameClass` is the pullback of the fibre restriction along `Fib`
  have hrel : (Work.Thom.relCohMap Fib (framePunct k) (Work.ThomBordism.fibrePunctSub γ P)
        hFibmem ℤ k).hom (Work.ThomBordism.fibreRes γ P k τ) = frameClass k σ := by
    have hcomp : frameEvalMap k σ = (Work.ThomBordism.fibreIncl γ P).comp Fib :=
      ContinuousMap.ext fun v => rfl
    have hmem2 : ∀ v ∈ framePunct k, (Work.ThomBordism.fibreIncl γ P (Fib v)) ∈
        Work.Thom.zeroComplement γ :=
      fun v hv => Work.ThomBordism.fibreIncl_mem γ P (Fib v) (hFibmem v hv)
    have hmorph : Work.Thom.relCohMap (frameEvalMap k σ) (framePunct k)
          (Work.Thom.zeroComplement γ) (frameEvalMap_mem k σ) ℤ k
        = Work.Thom.relCohMap ((Work.ThomBordism.fibreIncl γ P).comp Fib) (framePunct k)
          (Work.Thom.zeroComplement γ) hmem2 ℤ k :=
      Work.Thom.relCohMap_congrA (A := framePunct k) (B := Work.Thom.zeroComplement γ)
        hcomp (frameEvalMap_mem k σ) hmem2 ℤ k
    have hkey := Work.Thom.relCohMap_compA_apply (framePunct k)
      (Work.ThomBordism.fibrePunctSub γ P) (Work.Thom.zeroComplement γ) Fib
      (Work.ThomBordism.fibreIncl γ P) hFibmem (Work.ThomBordism.fibreIncl_mem γ P)
      hmem2 ℤ k τ
    change (Work.Thom.relCohMap Fib (framePunct k) (Work.ThomBordism.fibrePunctSub γ P)
        hFibmem ℤ k).hom ((Work.Thom.relCohMap (Work.ThomBordism.fibreIncl γ P)
          (Work.ThomBordism.fibrePunctSub γ P) (Work.Thom.zeroComplement γ)
          (Work.ThomBordism.fibreIncl_mem γ P) ℤ k).hom τ) = frameClass k σ
    rw [hkey]
    show (Work.Thom.relCohMap ((Work.ThomBordism.fibreIncl γ P).comp Fib) (framePunct k)
      (Work.Thom.zeroComplement γ) hmem2 ℤ k).hom (tautologicalThomClass k 10).τ = frameClass k σ
    rw [← hmorph]
    rfl
  rw [← hrel]
  exact Work.Tubular.span_singleton_map_eq_top
    ((Work.Thom.relCohMap Fib (framePunct k) (Work.ThomBordism.fibrePunctSub γ P) hFibmem
      ℤ k).hom) hsurj (Work.ThomBordism.fibreRes γ P k τ) hfib

end

end Work.ThomBordism
