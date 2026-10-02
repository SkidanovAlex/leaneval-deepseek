import Mathlib
import Submission.Work.ThomBordism._gtd.P5
import Submission.Work.ThomBordism._gtd.P7
import Submission.Work.ThomBordism.gtdGaussCandidate
import Submission.Work.Thom.ATools
import Submission.Work.ThomBordism.thomClassFibreDefs
import Submission.Work.ThomBordism.fibreGeneratorBundleComap
import Submission.Work.ThomBordism.fibreGenerator_bundleComap
import Submission.Work.ThomBordism.thomClass_fibreGenerator
import Submission.Work.ThomBordism.thomClass_of_fibreGenerator
import Submission.Work.ThomBordism.fibreRes_span_iff
import Submission.Work.Tubular.thomClass_span_top
import Submission.Work.Tubular.LocalDegreeAll

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

noncomputable section

open Work.TangentClasses

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## Toolbox -/

/-- **The fibre of a real bundle over `b` is its model fibre.** -/
noncomputable def fibreModelHomeomorph {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) (b : B) :
    ↥(Work.ThomBordism.fibre Z b) ≃ₜ F where
  toFun q := ((q : Z.TotalSpace).snd : F)
  invFun v := ⟨⟨b, v⟩, rfl⟩
  left_inv q := by
    refine Subtype.ext ?_
    show (⟨b, ((q : Z.TotalSpace).snd : F)⟩ : Z.TotalSpace) = (q : Z.TotalSpace)
    rw [← Bundle.TotalSpace.eta (q : Z.TotalSpace), q.2]
  right_inv v := rfl
  continuous_toFun := Work.ThomBordism.continuous_fibreSnd Z b
  continuous_invFun := by
    have h : Continuous fun v : F => (⟨b, v⟩ : Z.TotalSpace) :=
      FiberBundle.continuous_totalSpaceMk F Z.Fiber b
    exact h.subtype_mk (fun v => rfl)

@[simp] theorem fibreModelHomeomorph_apply {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) (b : B)
    (q : ↥(Work.ThomBordism.fibre Z b)) :
    fibreModelHomeomorph Z b q = ((q : Z.TotalSpace).snd : F) := rfl

@[simp] theorem fibreModelHomeomorph_symm_apply {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) (b : B)
    (v : F) :
    (fibreModelHomeomorph Z b).symm v = (⟨⟨b, v⟩, rfl⟩ : ↥(Work.ThomBordism.fibre Z b)) := rfl

/-- Membership in the punctured fibre, in terms of the model fibre's second coordinate. -/
theorem mem_fibrePunctSub {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) (b : B)
    (q : ↥(Work.ThomBordism.fibre Z b)) :
    q ∈ Work.ThomBordism.fibrePunctSub Z b ↔ (show F from (q : Z.TotalSpace).snd) ≠ 0 := by
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨q.2, h⟩

/-- **The evaluation of a point of the tautological bundle, over a prescribed plane.** -/
theorem evalVec_eq_evalChartO_snd {k m : ℕ}
    (q : (Work.ThomBordism.Grassmann.tautologicalBundle k m).TotalSpace)
    (P : Work.ThomBordism.Grassmann.OG k m) (hP : q.1 = P) :
    Work.ThomBordism.Grassmann.evalVec q =
      Work.ThomBordism.Grassmann.evalChartO
        ((Work.ThomBordism.Grassmann.tautologicalBundle k m).indexAt P)
        ⟨P, (Work.ThomBordism.Grassmann.tautologicalBundle k m).mem_baseSet_at P⟩
        (show Work.ThomBordism.Grassmann.Amb k from q.snd) := by
  rw [show q = Work.ThomBordism.Grassmann.mkTotal P
      (show Work.ThomBordism.Grassmann.Amb k from q.snd) from by
    rw [← Bundle.TotalSpace.eta q]
    show (⟨q.proj, (show Work.ThomBordism.Grassmann.Amb k from q.snd)⟩ :
      (Work.ThomBordism.Grassmann.tautologicalBundle k m).TotalSpace) = _
    exact Bundle.TotalSpace.ext hP (heq_of_eq rfl)]
  rw [Work.ThomBordism.Grassmann.evalVec_mkTotal]
  rfl

/-- If `f` is surjective and `a` generates, then `f a` generates. -/
theorem span_singleton_map_eq_top_of_surjective' {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) {a : M}
    (h : Submodule.span ℤ ({a} : Set M) = ⊤) : Submodule.span ℤ ({f a} : Set N) = ⊤ := by
  have h1 : Submodule.span ℤ ({f a} : Set N) = Submodule.map f (Submodule.span ℤ ({a} : Set M)) := by
    rw [Submodule.map_span, Set.image_singleton]
  rw [h1, h, Submodule.map_top, LinearMap.range_eq_top.mpr hf]

/-- **A generator survives a change of degrees** (the inverse of the degree cast used by
`Work.Tubular.thomClass_span_top`). -/
theorem span_cast_singleton_eq_top_inv' {M : ℕ → Type*} [∀ n, AddCommGroup (M n)]
    [∀ n, Module ℤ (M n)] {a b : ℕ} (h : a = b) (x : M a)
    (hx : Submodule.span ℤ ({(h ▸ x)} : Set (M b)) = ⊤) :
    Submodule.span ℤ ({x} : Set (M a)) = ⊤ := by
  cases h
  simpa using hx

/-- **A fibre generator at the rank degree generates the relative cohomology of the Thom pair.** -/
theorem fibreGenerator_span_top' {B : Type} [TopologicalSpace B] [PathConnectedSpace B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type} {n : ℕ} (Z : RealBundle B F ι) (σ : Work.Thom.OpenThom Z n)
    (hn : n = Z.rank) (h : IsFibreGenerator Z n σ) :
    Submodule.span ℤ ({σ} : Set (Work.Thom.OpenThom Z n)) = ⊤ := by
  have hn' : n = Module.finrank ℝ F := hn
  have hspan : Submodule.span ℤ
      ({((Nat.zero_add n).symm ▸ σ)} : Set (Work.Thom.OpenThom Z (0 + n))) = ⊤ :=
    Work.Tubular.thomClass_span_top Z n ⟨σ, thomClass_of_fibreGenerator Z σ hn' h⟩
  exact span_cast_singleton_eq_top_inv' (M := fun m => Work.Thom.OpenThom Z m)
    (Nat.zero_add n).symm σ hspan

/-- `Z.rank` of a bundle with fibre `ℝ^k` is `k`. -/
@[simp] theorem rank_euc {B : Type} [TopologicalSpace B] {ι : Type}
    (Z : RealBundle B (Work.Tubular.Euc k) ι) : Z.rank = k :=
  finrank_euclideanSpace_fin

/-! ## The model map `Θ` of the Gauss/tube data -/

/-- `toECoordAt` as a continuous linear map. -/
noncomputable def toECoordAtCLM' {k m : ℕ} (S : Work.ThomBordism.Grassmann.ChartIdx k m)
    (P : Work.ThomBordism.Grassmann.OG k m) :
    Work.ThomBordism.Grassmann.Amb (k + m) →L[ℝ] Work.ThomBordism.Grassmann.Amb k :=
  (Work.ThomBordism.Grassmann.matLin (Work.ThomBordism.Grassmann.orientMat S P)).comp
    ((LinearMap.toContinuousLinearMap
        ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm : (Fin k → ℝ) →ₗ[ℝ]
          Work.ThomBordism.Grassmann.Amb k)).comp
      ((LinearMap.toContinuousLinearMap (Work.ThomBordism.Grassmann.coordProj S)).comp
        (LinearMap.toContinuousLinearMap
          ((WithLp.linearEquiv 2 ℝ (Fin (k + m) → ℝ)) :
            Work.ThomBordism.Grassmann.Amb (k + m) →ₗ[ℝ] (Fin (k + m) → ℝ)))))

theorem toECoordAtCLM'_apply {k m : ℕ} (S : Work.ThomBordism.Grassmann.ChartIdx k m)
    (P : Work.ThomBordism.Grassmann.OG k m) (w : Work.ThomBordism.Grassmann.Amb (k + m)) :
    toECoordAtCLM' S P w = Work.ThomBordism.Grassmann.toECoordAt S P w := by
  rw [toECoordAtCLM']
  show (Work.ThomBordism.Grassmann.matLin (Work.ThomBordism.Grassmann.orientMat S P))
      (((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm)
        ((Work.ThomBordism.Grassmann.coordProj S)
          ((WithLp.linearEquiv 2 ℝ (Fin (k + m) → ℝ)) w))) = _
  rfl

/-- **The model map of the crux**: the fibre coordinate of the `padEuc`-image of the inserted
normal vector. -/
noncomputable def gtdThetaCLM (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    Work.Tubular.Euc k →L[ℝ] Work.ThomBordism.Grassmann.Amb k :=
  (toECoordAtCLM' ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).indexAt
      (Work.ThomBordism.Grassmann.padGaussFun E ND x))
    (Work.ThomBordism.Grassmann.padGaussFun E ND x)).comp
  ((Work.PTGeometric.padEuc k 10 (by norm_num)).comp
    (Work.Tubular.insCLM E ND (ND.D.indexAt x) x))

theorem gtdThetaCLM_apply (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt)
    (v : Work.Tubular.Euc k) :
    gtdThetaCLM E ND x v = Work.ThomBordism.Grassmann.toECoordAt
      ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).indexAt
        (Work.ThomBordism.Grassmann.padGaussFun E ND x))
      (Work.ThomBordism.Grassmann.padGaussFun E ND x)
      (Work.PTGeometric.padEuc k 10 (by norm_num)
        (Work.Tubular.insCLM E ND (ND.D.indexAt x) x v)) := by
  rw [gtdThetaCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    toECoordAtCLM'_apply]

/-- The `padEuc`-image of an inserted normal vector is a vector of the padded Gauss plane. -/
theorem gtdMemPlane_insCLM (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt)
    (v : Work.Tubular.Euc k) :
    Work.ThomBordism.Grassmann.memPlane (Work.ThomBordism.Grassmann.padGaussFun E ND x)
      (Work.PTGeometric.padEuc k 10 (by norm_num)
        (Work.Tubular.insCLM E ND (ND.D.indexAt x) x v)) :=
  gtdMemPlane_padGaussEval E ND ⟨x, v⟩

/-- **The crux: `Θ x` is bijective.**  It is an injective linear endomorphism of `ℝ^k`. -/
theorem gtdThetaCLM_bijective (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    Function.Bijective (gtdThetaCLM E ND x) := by
  have hinj : Function.Injective ⇑(gtdThetaCLM E ND x) := by
    intro a b hab
    rw [gtdThetaCLM_apply, gtdThetaCLM_apply] at hab
    set S := (Work.ThomBordism.Grassmann.tautologicalBundle k 10).indexAt
      (Work.ThomBordism.Grassmann.padGaussFun E ND x) with hS
    set P := Work.ThomBordism.Grassmann.padGaussFun E ND x with hP
    have hPS : P ∈ (Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S :=
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).mem_baseSet_at P
    have h1 := Work.ThomBordism.Grassmann.evalChartO_toECoordAt S P hPS
      (Work.PTGeometric.padEuc k 10 (by norm_num)
        (Work.Tubular.insCLM E ND (ND.D.indexAt x) x a)) (gtdMemPlane_insCLM E ND x a)
    have h2 := Work.ThomBordism.Grassmann.evalChartO_toECoordAt S P hPS
      (Work.PTGeometric.padEuc k 10 (by norm_num)
        (Work.Tubular.insCLM E ND (ND.D.indexAt x) x b)) (gtdMemPlane_insCLM E ND x b)
    have h3 : Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.insCLM E ND (ND.D.indexAt x) x a) =
        Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.insCLM E ND (ND.D.indexAt x) x b) := by
      rw [← h1, ← h2, hab]
    have h4 := Work.PTGeometric.padEuc_injective k 10 (by norm_num) h3
    rw [← Work.Tubular.readCLM_insCLM E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x) a,
      ← Work.Tubular.readCLM_insCLM E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x) b, h4]
  refine ⟨hinj, ?_⟩
  have hfin : Module.finrank ℝ (Work.Tubular.Euc k) =
      Module.finrank ℝ (Work.ThomBordism.Grassmann.Amb k) := rfl
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
    (f := (gtdThetaCLM E ND x).toLinearMap)).mp hinj

/-- **The homeomorphism of the model fibres of the crux.** -/
noncomputable def gtdThetaHomeomorph (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    Work.Tubular.Euc k ≃ₜ Work.ThomBordism.Grassmann.Amb k :=
  (LinearEquiv.ofBijective (gtdThetaCLM E ND x).toLinearMap
    (by simpa using gtdThetaCLM_bijective E ND x)).toContinuousLinearEquiv.toHomeomorph

theorem gtdThetaHomeomorph_apply (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt)
    (v : Work.Tubular.Euc k) :
    gtdThetaHomeomorph E ND x v = gtdThetaCLM E ND x v := by
  show gtdThetaCLM E ND x v = gtdThetaCLM E ND x v
  rfl

/-! ## The explicit form of the Gauss/classifying map `G` -/

/-- **`G` is the map `v ↦ toECoordAt (padEuc v)` over the padded Gauss map.**  The hypotheses
`hbp` (the base point of `G p`) and `hvec` (the vector of `G p`) determine `G p` completely. -/
theorem gtdG_apply {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e}
    {G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace)}
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.proj)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    (p : (Work.Tubular.normalBundle E ND).TotalSpace) :
    G p = Work.ThomBordism.Grassmann.mkTotal
      (Work.ThomBordism.Grassmann.padGaussFun E ND p.proj)
      (Work.ThomBordism.Grassmann.toECoordAt
        ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).indexAt
          (Work.ThomBordism.Grassmann.padGaussFun E ND p.proj))
        (Work.ThomBordism.Grassmann.padGaussFun E ND p.proj)
        (Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))) := by
  have hbp' : (G p).proj = Work.ThomBordism.Grassmann.padGaussFun E ND p.proj := hbp p
  have heta : G p = Work.ThomBordism.Grassmann.mkTotal
      (Work.ThomBordism.Grassmann.padGaussFun E ND p.proj)
      (show Work.ThomBordism.Grassmann.Amb k from (G p).snd) := by
    rw [← Bundle.TotalSpace.eta (G p)]
    show (⟨(G p).proj, (show Work.ThomBordism.Grassmann.Amb k from (G p).snd)⟩ :
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace) = _
    exact Bundle.TotalSpace.ext hbp' (heq_of_eq rfl)
  have hcoord : (show Work.ThomBordism.Grassmann.Amb k from (G p).snd)
      = Work.ThomBordism.Grassmann.toECoordAt
          ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).indexAt
            (Work.ThomBordism.Grassmann.padGaussFun E ND p.proj))
          (Work.ThomBordism.Grassmann.padGaussFun E ND p.proj)
          (Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p))) := by
    refine Work.ThomBordism.Grassmann.peEvalChartO_injective
      ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).indexAt
        (Work.ThomBordism.Grassmann.padGaussFun E ND p.proj))
      ⟨Work.ThomBordism.Grassmann.padGaussFun E ND p.proj,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).mem_baseSet_at _⟩ ?_
    rw [Work.ThomBordism.Grassmann.evalChartO_toECoordAt _ _
      ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).mem_baseSet_at _) _
      (gtdMemPlane_padGaussEval E ND p)]
    rw [← evalVec_eq_evalChartO_snd (G p) (Work.ThomBordism.Grassmann.padGaussFun E ND p.proj) hbp']
    exact hvec p
  rw [heta, hcoord]

/-- **The fibre-level form of `gtdG_apply`.** -/
theorem gtdG_fibre {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e}
    {G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace)}
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.proj)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    (x : V.pt) (v : Work.Tubular.Euc k) :
    G (⟨x, v⟩ : (Work.Tubular.normalBundle E ND).TotalSpace)
      = Work.ThomBordism.Grassmann.mkTotal (Work.ThomBordism.Grassmann.padGaussFun E ND x)
          (gtdThetaCLM E ND x v) := by
  rw [gtdG_apply hbp hvec ⟨x, v⟩, gtdThetaCLM_apply]
  rfl

/-- **The fibre action of `G`**, for an arbitrary point of the normal bundle over `x`. -/
theorem gtdG_snd {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e}
    {G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace)}
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.proj)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    (x : V.pt) (q : (Work.Tubular.normalBundle E ND).TotalSpace) (hq : q.proj = x) :
    (show Work.Tubular.Euc k from (G q).snd)
      = gtdThetaCLM E ND x (show Work.Tubular.Euc k from q.snd) := by
  have hG := gtdG_apply hbp hvec
  have hqv : q = (⟨x, (show Work.Tubular.Euc k from q.snd)⟩ :
      (Work.Tubular.normalBundle E ND).TotalSpace) := by
    rw [← Bundle.TotalSpace.eta q, hq]
  have h1 : (show Work.Tubular.Euc k from (G q).snd)
      = (show Work.Tubular.Euc k from
          (G (⟨x, (show Work.Tubular.Euc k from q.snd)⟩ :
            (Work.Tubular.normalBundle E ND).TotalSpace)).snd) :=
    congrArg (fun z : (Work.Tubular.normalBundle E ND).TotalSpace =>
      (show Work.Tubular.Euc k from (G z).snd)) hqv
  have h2 : (show Work.Tubular.Euc k from
        (G (⟨x, (show Work.Tubular.Euc k from q.snd)⟩ :
          (Work.Tubular.normalBundle E ND).TotalSpace)).snd)
      = Work.ThomBordism.Grassmann.toECoordAt
          ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).indexAt
            (Work.ThomBordism.Grassmann.padGaussFun E ND x))
          (Work.ThomBordism.Grassmann.padGaussFun E ND x)
          (Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.insCLM E ND (ND.D.indexAt x) x
              (show Work.Tubular.Euc k from q.snd))) := by
    rw [hG (⟨x, (show Work.Tubular.Euc k from q.snd)⟩ :
      (Work.Tubular.normalBundle E ND).TotalSpace)]
    rfl
  exact h1.trans (h2.trans (gtdThetaCLM_apply E ND x
    (show Work.Tubular.Euc k from q.snd)).symm)

/-! ## The main assembly -/

/-- **The pullback of the tautological Thom class along the Gauss/classifying map `G` generates
`H^k(ν, ν∖0)`.** -/
theorem gtdU_span_top_aux {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.proj)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) :
    Submodule.span ℤ ({((Work.Thom.relCohMap G
        (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
        (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgm ℤ k).hom
      (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ)} : Set _) = ⊤ := by
  classical
  haveI : PathConnectedSpace V.pt := Work.Tubular.pathConnectedSpace_of_man8 V
  set σ : Work.Thom.OpenThom (Work.Tubular.normalBundle E ND) k :=
    (Work.Thom.relCohMap G (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
      (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgm ℤ k).hom
      (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ with hσ
  have hgen : IsFibreGenerator (Work.Tubular.normalBundle E ND) k σ := by
    intro x
    let efib : ↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x) ≃ₜ
        ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
          (Work.ThomBordism.Grassmann.padGaussFun E ND x)) :=
      (fibreModelHomeomorph (Work.Tubular.normalBundle E ND) x).trans
        ((gtdThetaHomeomorph E ND x).trans
          (fibreModelHomeomorph (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.Grassmann.padGaussFun E ND x)).symm)
    have hval : ∀ p : ↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
        (show Work.ThomBordism.Grassmann.Amb k from
            ((efib p : ↥(Work.ThomBordism.fibre
              (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.Grassmann.padGaussFun E ND x))) :
              (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace).snd)
          = gtdThetaCLM E ND x (show Work.Tubular.Euc k from
              (p : (Work.Tubular.normalBundle E ND).TotalSpace).snd) := by
      intro p
      rfl
    have he : ∀ p, ((efib p : ↥(Work.ThomBordism.fibre
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
          (Work.ThomBordism.Grassmann.padGaussFun E ND x))) :
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace)
        = G (p : (Work.Tubular.normalBundle E ND).TotalSpace) := by
      intro p
      refine totalSpace_eq_of ?_ ?_
      · exact (((hbp (p : (Work.Tubular.normalBundle E ND).TotalSpace)).trans
          (congrArg (Work.ThomBordism.Grassmann.padGaussFun E ND) (p.2))).symm)
      · exact ((hval p).trans
          (gtdG_snd hbp hvec x (p : (Work.Tubular.normalBundle E ND).TotalSpace) p.2).symm)
    have hpe : ∀ p, p ∈ Work.ThomBordism.fibrePunctSub (Work.Tubular.normalBundle E ND) x ↔
        efib p ∈ Work.ThomBordism.fibrePunctSub
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
          (Work.ThomBordism.Grassmann.padGaussFun E ND x) := by
      intro p
      rw [mem_fibrePunctSub, mem_fibrePunctSub, hval p]
      constructor
      · intro h
        intro h0
        exact h ((gtdThetaCLM_bijective E ND x).1 (by rw [h0, map_zero]))
      · intro h h0
        exact h (by rw [h0, map_zero])
    -- the restriction of the pullback to the fibre
    have hres : Work.ThomBordism.fibreRes (Work.Tubular.normalBundle E ND) x k σ
        = (Work.Thom.relCohMap (efib : C(↥(Work.ThomBordism.fibre
              (Work.Tubular.normalBundle E ND) x),
            ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.Grassmann.padGaussFun E ND x))))
            (Work.ThomBordism.fibrePunctSub (Work.Tubular.normalBundle E ND) x)
            (Work.ThomBordism.fibrePunctSub (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.Grassmann.padGaussFun E ND x))
            (fun p hp => (hpe p).mp hp) ℤ k).hom
          (Work.ThomBordism.fibreRes (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.Grassmann.padGaussFun E ND x) k
            (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ) := by
      rw [hσ]
      set A := Work.ThomBordism.fibrePunctSub (Work.Tubular.normalBundle E ND) x with hA
      set Bs := Work.ThomBordism.fibrePunctSub
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        (Work.ThomBordism.Grassmann.padGaussFun E ND x) with hBs
      set zν := Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND) with hzν
      set zγ := Work.Thom.zeroComplement
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10) with hzγ
      show (Work.Thom.relCohMap (Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x)
            A zν (Work.ThomBordism.fibreIncl_mem _ x) ℤ k).hom
          ((Work.Thom.relCohMap G zν zγ hgm ℤ k).hom
            (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ)
        = (Work.Thom.relCohMap (efib : C(↥(Work.ThomBordism.fibre
              (Work.Tubular.normalBundle E ND) x),
            ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.Grassmann.padGaussFun E ND x)))) A Bs
            (fun p hp => (hpe p).mp hp) ℤ k).hom
          ((Work.Thom.relCohMap
              (Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x))
              Bs zγ (Work.ThomBordism.fibreIncl_mem _ _) ℤ k).hom
            (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ)
      have hcomp : ∀ y ∈ A, G ((Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x) y)
          ∈ zγ :=
        fun y hy => hgm _ (Work.ThomBordism.fibreIncl_mem _ x y hy)
      have hcomp' : ∀ y ∈ A,
          (Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.Grassmann.padGaussFun E ND x)) (efib y) ∈ zγ := by
        intro y hy
        rw [show (Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.Grassmann.padGaussFun E ND x)) (efib y)
            = G ((Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x) y) from he y]
        exact hcomp y hy
      have hmap : ((Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.Grassmann.padGaussFun E ND x)).comp
            (efib : C(↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
              ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)))))
          = (G.comp (Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x)) := by
        apply ContinuousMap.ext
        intro y
        exact he y
      have hAstep : CategoryTheory.CategoryStruct.comp
            (Work.Thom.relCohMap G zν zγ hgm ℤ k)
            (Work.Thom.relCohMap (Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x)
              A zν (Work.ThomBordism.fibreIncl_mem _ x) ℤ k)
          = Work.Thom.relCohMap
              ((Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)).comp
                (efib : C(↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
                  ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                    (Work.ThomBordism.Grassmann.padGaussFun E ND x))))) A zγ hcomp' ℤ k :=
        (Work.Thom.relCohMap_compA A zν zγ
          (Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x) G
          (Work.ThomBordism.fibreIncl_mem _ x) hgm hcomp ℤ k).trans
        (Work.Thom.relCohMap_congrA A zγ hmap.symm hcomp hcomp' ℤ k)
      have hBstep : CategoryTheory.CategoryStruct.comp
            (Work.Thom.relCohMap
              (Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)) Bs zγ
              (Work.ThomBordism.fibreIncl_mem _ _) ℤ k)
            (Work.Thom.relCohMap (efib : C(↥(Work.ThomBordism.fibre
                (Work.Tubular.normalBundle E ND) x),
              ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)))) A Bs
              (fun p hp => (hpe p).mp hp) ℤ k)
          = Work.Thom.relCohMap
              ((Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)).comp
                (efib : C(↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
                  ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                    (Work.ThomBordism.Grassmann.padGaussFun E ND x))))) A zγ hcomp' ℤ k :=
        Work.Thom.relCohMap_compA A Bs zγ
          (efib : C(↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
            ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.Grassmann.padGaussFun E ND x))))
          (Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.Grassmann.padGaussFun E ND x))
          (fun p hp => (hpe p).mp hp) (Work.ThomBordism.fibreIncl_mem _ _) hcomp' ℤ k
      have lhs_eq : (Work.Thom.relCohMap
              (Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x) A zν
              (Work.ThomBordism.fibreIncl_mem _ x) ℤ k).hom
            ((Work.Thom.relCohMap G zν zγ hgm ℤ k).hom
              (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ)
          = (Work.Thom.relCohMap
              ((Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)).comp
                (efib : C(↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
                  ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                    (Work.ThomBordism.Grassmann.padGaussFun E ND x))))) A zγ hcomp' ℤ k).hom
            (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ := by
        rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp
            (Work.Thom.relCohMap G zν zγ hgm ℤ k)
            (Work.Thom.relCohMap (Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x)
              A zν (Work.ThomBordism.fibreIncl_mem _ x) ℤ k), hAstep]
      have rhs_eq : (Work.Thom.relCohMap (efib : C(↥(Work.ThomBordism.fibre
                (Work.Tubular.normalBundle E ND) x),
              ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)))) A Bs
              (fun p hp => (hpe p).mp hp) ℤ k).hom
            ((Work.Thom.relCohMap
                (Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                  (Work.ThomBordism.Grassmann.padGaussFun E ND x)) Bs zγ
                (Work.ThomBordism.fibreIncl_mem _ _) ℤ k).hom
              (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ)
          = (Work.Thom.relCohMap
              ((Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)).comp
                (efib : C(↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
                  ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                    (Work.ThomBordism.Grassmann.padGaussFun E ND x))))) A zγ hcomp' ℤ k).hom
            (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ := by
        rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp
            (Work.Thom.relCohMap
              (Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)) Bs zγ
              (Work.ThomBordism.fibreIncl_mem _ _) ℤ k)
            (Work.Thom.relCohMap (efib : C(↥(Work.ThomBordism.fibre
                (Work.Tubular.normalBundle E ND) x),
              ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)))) A Bs
              (fun p hp => (hpe p).mp hp) ℤ k), hBstep]
      rw [lhs_eq, rhs_eq]
    -- the span
    rw [hres]
    have hbij := Work.Thom.bijective_relCohMap_of_homeomorphA
      (Work.ThomBordism.fibrePunctSub (Work.Tubular.normalBundle E ND) x)
      (Work.ThomBordism.fibrePunctSub (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        (Work.ThomBordism.Grassmann.padGaussFun E ND x))
      efib hpe ℤ k
    have hgenx : Submodule.span ℤ ({(Work.ThomBordism.fibreRes
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        (Work.ThomBordism.Grassmann.padGaussFun E ND x) k
        (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ)} : Set _) = ⊤ :=
      thomClass_fibreGenerator (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        (Work.ThomBordism.Grassmann.tautologicalThomClass k 10)
        (by simp) (Work.ThomBordism.Grassmann.padGaussFun E ND x)
    exact span_singleton_map_eq_top_of_surjective' _ hbij.2 hgenx
  have hrank : k = (Work.Tubular.normalBundle E ND).rank := (rank_euc _).symm
  exact fibreGenerator_span_top' (Work.Tubular.normalBundle E ND) σ hrank hgen

/-! ## The generating property of `gtdU` -/

/-- The ambient vector of `bundleToNormal p` is the insertion of the fibre coordinate of `p`. -/
theorem bundleToNormal_vec (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (p : (Work.Tubular.normalBundle E ND).TotalSpace) :
    Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)
      = Work.Tubular.insCLM E ND ((Work.Tubular.normalBundle E ND).indexAt p.proj) p.proj
          (show Work.Tubular.Euc k from p.snd) := rfl

/-- The fibrewise norm of the gluing-data normal bundle computed in the concrete model. -/
theorem normalNorm_bundleToNormal (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (p : (Work.Tubular.normalBundle E ND).TotalSpace) :
    Work.Tubular.normalNorm E (Work.Tubular.bundleToNormal E ND p)
      = ‖(show Work.Tubular.Euc k from p.snd)‖ := by
  show ‖Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)‖ = _
  rw [bundleToNormal_vec E ND p, Work.Tubular.norm_insCLM E ND _
    ((Work.Tubular.normalBundle E ND).mem_baseSet_at p.proj)]

/-- The normal total space is homeomorphic to the total space of the gluing-data normal bundle, in a
way compatible with the nonzero points, so the generating property transfers. -/
theorem gtd_mem_iff (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) :
    ∀ x : Work.Tubular.NormalTotal E, x ∈ Work.Tubular.normalNonzero E ↔
      (Work.Tubular.eucNormalHomeomorph E ND).symm x
        ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND) := by
  intro x
  have hsymm : (Work.Tubular.eucNormalHomeomorph E ND).symm x
      = Work.Tubular.normalToBundle E ND x :=
    gtdEucNormalHomeomorph_symm_apply (E := E) (ND := ND) x
  have hnorm : Work.Tubular.normalNorm E x
      = ‖(show Work.Tubular.Euc k from
          (Work.Tubular.normalToBundle E ND x).snd)‖ :=
    (congrArg (Work.Tubular.normalNorm E)
      (Work.Tubular.bundleToNormal_normalToBundle E ND x).symm).trans
      (normalNorm_bundleToNormal E ND (Work.Tubular.normalToBundle E ND x))
  rw [Work.Tubular.mem_normalNonzero, hsymm, Work.Thom.mem_zeroComplement, hnorm]
  constructor
  · intro h hv
    exact h (by rw [hv, norm_zero])
  · intro h hnorm0
    exact h (norm_eq_zero.mp hnorm0)

theorem gtdU_span_top {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) :
    Submodule.span ℤ ({Work.ThomBordism.gtdU E ND G hgm} : Set
      (Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E))) = ⊤ := by
  classical
  set σ : Work.Thom.OpenThom (Work.Tubular.normalBundle E ND) k :=
    (Work.Thom.relCohMap G (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
      (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgm ℤ k).hom
      (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ with hσ
  have hspan : Submodule.span ℤ ({σ} : Set (Work.Thom.OpenThom (Work.Tubular.normalBundle E ND) k))
      = ⊤ :=
    gtdU_span_top_aux E ND G hbp hvec hgm
  have he : ∀ x : Work.Tubular.NormalTotal E, x ∈ Work.Tubular.normalNonzero E ↔
      (Work.Tubular.eucNormalHomeomorph E ND).symm x
        ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND) :=
    gtd_mem_iff E ND
  have hbij := Work.Thom.bijective_relCohMap_of_homeomorphA (Work.Tubular.normalNonzero E)
    (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
    (Work.Tubular.eucNormalHomeomorph E ND).symm he ℤ k
  have hbij' : Function.Surjective (Work.Thom.relCohMap
      ((Work.Tubular.eucNormalHomeomorph E ND).symm : C(Work.Tubular.NormalTotal E,
        (Work.Tubular.normalBundle E ND).TotalSpace)) (Work.Tubular.normalNonzero E)
      (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND)) (gtd_mem E ND) ℤ k).hom := by
    rw [Work.Thom.relCohMap_congrA (Work.Tubular.normalNonzero E)
      (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND)) rfl (gtd_mem E ND)
      (fun x hx => (he x).mp hx) ℤ k]
    exact hbij.2
  have hgtdU : Work.ThomBordism.gtdU E ND G hgm = (Work.Thom.relCohMap
      ((Work.Tubular.eucNormalHomeomorph E ND).symm : C(Work.Tubular.NormalTotal E,
        (Work.Tubular.normalBundle E ND).TotalSpace)) (Work.Tubular.normalNonzero E)
      (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND)) (gtd_mem E ND) ℤ k).hom σ := rfl
  rw [hgtdU]
  refine span_singleton_map_eq_top_of_surjective' _ hbij' ?_
  exact hspan

end

end Work.ThomBordism
