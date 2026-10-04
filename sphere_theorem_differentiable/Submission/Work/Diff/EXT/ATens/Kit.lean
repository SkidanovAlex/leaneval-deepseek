import Mathlib
import Submission.Work.Diff.EXT.ATens.Defs
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.kato_smooth
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiffOn_cov_apply
import Submission.Geodesic
import Submission.Work.Diff.T.FrameExt
import Submission.Work.Diff.EXT.contDiffAt_chartMat_of_jointSmooth
import Submission.Work.Diff.GE.norms_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A local-smoothness kit for the `A`-tower

`Work.Diff.EXT.cktA G t k` is the field-level `k`-th iterated covariant derivative (with respect to
the fixed background connection `∇^{G 0}`) of the lowered connection difference `aOf G t`.  Its
recursion only uses the *germ* of its field arguments; the aim of this file is to make that
available in the form needed to compare `cktA` on the coordinate-frame fields `cFrame x₀ a` (which
are smooth only on the chart at `x₀`) with `cktA` on globally smooth fields.

To that end we introduce a notion of local smoothness on an *open* neighbourhood,
`SmLoc X x = ∃ u, IsOpen u ∧ x ∈ u ∧ CMDiff[u] ∞ (T% X)`, and record the closure properties of
`SmLoc` and of `dirFA g X Y = ∇_Y X` that the induction needs.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- A tangent field which is smooth on an open neighbourhood of `x`. -/
abbrev SmLoc (X : TfA (I := I) (M := M)) (x : M) : Prop :=
  ∃ u : Set M, IsOpen u ∧ x ∈ u ∧ CMDiff[u] ∞ (T% X)


/-! ## Notation-free wrappers for eventual equality (for statement elaboration) -/

/-- Eventual equality of two tangent fields near a point. -/
abbrev EvEqF (x : M) (X X' : TfA (I := I) (M := M)) : Prop := X =ᶠ[𝓝 x] X'

/-- Eventual equality of two real-valued functions near a point. -/
abbrev EvEqR (x : M) (f f' : M → ℝ) : Prop := f =ᶠ[𝓝 x] f'

/-- A smooth real-valued function on `M` (notation-free wrapper for `CMDiff ∞ ·`). -/
abbrev SmFunM (f : M → ℝ) : Prop := CMDiff ∞ f

/-! ## Basic closure properties -/

/-- A globally smooth field is locally smooth. -/
lemma smLoc_of_smA {X : TfA (I := I) (M := M)} (hX : SmA (I := I) (M := M) X) (x : M) :
    SmLoc (I := I) (M := M) X x :=
  ⟨univ, isOpen_univ, trivial, by rw [contMDiffOn_univ]; exact hX⟩

/-- Local smoothness is a germ condition. -/
lemma smLoc_congr {X X' : TfA (I := I) (M := M)} {x : M}
    (h : SmLoc (I := I) (M := M) X x) (heq : X =ᶠ[𝓝 x] X') :
    SmLoc (I := I) (M := M) X' x := by
  obtain ⟨u, hu, hxu, hXu⟩ := h
  obtain ⟨v, hv, hvsub⟩ := Filter.eventually_iff_exists_mem.mp heq
  refine ⟨u ∩ interior v, hu.inter isOpen_interior, ⟨hxu, mem_interior_iff_mem_nhds.mpr hv⟩, ?_⟩
  refine (hXu.mono Set.inter_subset_left).congr fun y hy => ?_
  exact congrArg (TotalSpace.mk' E y) (hvsub y (interior_subset hy.2)).symm

/-- `SmLoc` holds on a neighbourhood. -/
lemma smLoc_eventually {X : TfA (I := I) (M := M)} {x : M}
    (h : SmLoc (I := I) (M := M) X x) : ∀ᶠ y in 𝓝 x, SmLoc (I := I) (M := M) X y := by
  obtain ⟨u, hu, hxu, hXu⟩ := h
  filter_upwards [hu.mem_nhds hxu] with y hy
  exact ⟨u, hu, hy, hXu⟩

/-- A locally smooth field agrees, near the point, with a globally smooth one. -/
lemma exists_sma_of_smLoc {X : TfA (I := I) (M := M)} {x : M}
    (h : SmLoc (I := I) (M := M) X x) :
    ∃ X' : TfA (I := I) (M := M), SmA (I := I) (M := M) X' ∧ X =ᶠ[𝓝 x] X' := by
  obtain ⟨u, hu, hxu, hXu⟩ := h
  obtain ⟨ψ, -, hψsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) (c := x)).mem_iff.mp (hu.mem_nhds hxu)
  refine ⟨fun y => ψ y • X y, ?_, ?_⟩
  · exact ContMDiffOn.smul_section_of_tsupport (F := E) (V := TangentSpace I)
      ψ.contMDiff.contMDiffOn hu hψsupp hXu
  · filter_upwards [ψ.eventuallyEq_one] with y hy
    show X y = ψ y • X y
    rw [hy, Pi.one_apply, one_smul]

/-! ## Additivity and homogeneity of smooth fields -/

lemma SmA_add {X Y : TfA (I := I) (M := M)} (hX : SmA (I := I) (M := M) X)
    (hY : SmA (I := I) (M := M) Y) : SmA (I := I) (M := M) (X + Y) :=
  hX.add_section hY

lemma SmA_smul {f : M → ℝ} {X : TfA (I := I) (M := M)} (hf : CMDiff ∞ f)
    (hX : SmA (I := I) (M := M) X) : SmA (I := I) (M := M) (f • X) :=
  hf.smul_section hX

/-! ## `dirFA`: the covariant derivative as a field -/

/-- The Leibniz rule for `dirFA` in the *field* argument. -/
lemma dirFA_leibniz (g : SMet I M) {X₁ X₂ : TfA (I := I) (M := M)} {f₁ f₂ : M → ℝ}
    {v0 : TfA (I := I) (M := M)}
    (hX₁ : SmA (I := I) (M := M) X₁) (hX₂ : SmA (I := I) (M := M) X₂)
    (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    dirFA g (f₁ • X₁ + f₂ • X₂) v0
      = f₁ • dirFA g X₁ v0 + (fun y => (mvfderiv I f₁ y) (v0 y)) • X₁
        + f₂ • dirFA g X₂ v0 + (fun y => (mvfderiv I f₂ y) (v0 y)) • X₂ := by
  funext y
  have h1 : MDiffAt (T% (f₁ • X₁)) y := (hf₁.smul_section hX₁).mdifferentiableAt (by simp)
  have h2 : MDiffAt (T% (f₂ • X₂)) y := (hf₂.smul_section hX₂).mdifferentiableAt (by simp)
  have h3 : MDiffAt (T% X₁) y := hX₁.mdifferentiableAt (by simp)
  have h4 : MDiffAt (T% X₂) y := hX₂.mdifferentiableAt (by simp)
  have h5 : MDiffAt f₁ y := hf₁.mdifferentiableAt (by simp)
  have h6 : MDiffAt f₂ y := hf₂.mdifferentiableAt (by simp)
  have hadd := (lcOf g).isCovariantDerivativeOn.add (s := Set.univ)
    (σ := f₁ • X₁) (σ' := f₂ • X₂) h1 h2
  have hl1 := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := X₁) (g := f₁) h3 h5
  have hl2 := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := X₂) (g := f₂) h4 h6
  simp only [dirFA, Pi.add_apply, Pi.smul_apply']
  rw [hadd, hl1, hl2]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, Pi.add_apply,
    Pi.smul_apply']
  abel

/-- `dirFA g X Y = ∇_Y X` is locally smooth when `X` and `Y` are. -/
lemma smLoc_dirFA (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M)
    {X Y : TfA (I := I) (M := M)} {x : M}
    (hX : SmLoc (I := I) (M := M) X x) (hY : SmLoc (I := I) (M := M) Y x) :
    SmLoc (I := I) (M := M) (dirFA g X Y) x := by
  obtain ⟨u, hu, hxu, hXu⟩ := hX
  obtain ⟨v, hv, hxv, hYv⟩ := hY
  refine ⟨u ∩ v, hu.inter hv, ⟨hxu, hxv⟩, ?_⟩
  have hcov : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  have h1 : CMDiff[u ∩ v] ∞ (T% X) := hXu.mono Set.inter_subset_left
  have h2 : CMDiff[u ∩ v] ∞ (T% Y) := hYv.mono Set.inter_subset_right
  have h3 := Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiffOn_cov_apply
    (lcOf g) hcov (hu.inter hv) h1 h2
  simpa only [dirFA] using h3

/-- Local smoothness of both the field and the direction field is enough to identify the covariant
derivative up to a germ. -/
lemma dirFA_germEq (g : SMet I M) {X X' Y Y' : TfA (I := I) (M := M)} {x : M}
    (hX : SmLoc (I := I) (M := M) X x) (hX' : SmLoc (I := I) (M := M) X' x)
    (heqX : X =ᶠ[𝓝 x] X') (heqY : Y =ᶠ[𝓝 x] Y') :
    dirFA g X Y =ᶠ[𝓝 x] dirFA g X' Y' := by
  obtain ⟨u, hu, hxu, hXu⟩ := hX
  obtain ⟨v, hv, hxv, hX'v⟩ := hX'
  have h1 : ∀ᶠ y in 𝓝 x, X =ᶠ[𝓝 y] X' := eventuallyEq_nhds_eventuallyA heqX
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ u := hu.mem_nhds hxu
  have h3 : ∀ᶠ y in 𝓝 x, y ∈ v := hv.mem_nhds hxv
  have h4 : ∀ᶠ y in 𝓝 x, Y y = Y' y := heqY
  filter_upwards [h1, h2, h3, h4] with y hy1 hy2 hy3 hy4
  rw [dirFA, dirFA]
  have hd1 : MDiffAt (T% X) y :=
    (hXu.contMDiffAt (hu.mem_nhds hy2)).mdifferentiableAt (by simp)
  have hd2 : MDiffAt (T% X') y :=
    (hX'v.contMDiffAt (hv.mem_nhds hy3)).mdifferentiableAt (by simp)
  have hlc := Work.Diff.GE.Kato3.lcOf_congr_eventuallyEq g hd1 hd2 hy1
  rw [hlc, hy4]

/-- The coordinate frame of the chart at `x₀` is locally smooth at every point of that chart. -/
lemma smLoc_cFrame (x₀ : M) {x : M} (hx : x ∈ (chartAt H x₀).source)
    (a : Fin (Module.finrank ℝ E)) :
    SmLoc (I := I) (M := M) (Work.Diff.GE.cFrame (I := I) x₀ a) x :=
  ⟨(chartAt H x₀).source, (chartAt H x₀).open_source, hx, fun y hy =>
    ((contMDiffAt_frameVector (I := I) x₀
        (Work.Diff.GE.cBasis (E := E) a) hy).contMDiffWithinAt).mono (Set.subset_univ _)⟩


/-! ## Splitting lemmas for the packed tuples `mkT3` -/

section Pack

variable {k : ℕ}

lemma smA_mkT3 {w : Fin k → TfA (I := I) (M := M)} {B : Fin 3 → TfA (I := I) (M := M)}
    (hw : ∀ i, SmA (I := I) (M := M) (w i)) (hB : ∀ p, SmA (I := I) (M := M) (B p)) :
    ∀ q, SmA (I := I) (M := M) ((mkT3 w B) q) := by
  intro q
  refine Fin.addCases ?_ ?_ q
  · intro i; rw [mkT3_castAdd]; exact hw i
  · intro p; rw [mkT3_natAdd]; exact hB p

lemma smLoc_mkT3 {w : Fin k → TfA (I := I) (M := M)} {B : Fin 3 → TfA (I := I) (M := M)}
    {x : M} (hw : ∀ i, SmLoc (I := I) (M := M) (w i) x)
    (hB : ∀ p, SmLoc (I := I) (M := M) (B p) x) :
    ∀ q, SmLoc (I := I) (M := M) ((mkT3 w B) q) x := by
  intro q
  refine Fin.addCases ?_ ?_ q
  · intro i; rw [mkT3_castAdd]; exact hw i
  · intro p; rw [mkT3_natAdd]; exact hB p

lemma evEqF_mkT3 {w w' : Fin k → TfA (I := I) (M := M)} {B B' : Fin 3 → TfA (I := I) (M := M)}
    {x : M} (hw : ∀ i, EvEqF (I := I) (M := M) x (w i) (w' i))
    (hB : ∀ p, EvEqF (I := I) (M := M) x (B p) (B' p)) :
    ∀ q, EvEqF (I := I) (M := M) x ((mkT3 w B) q) ((mkT3 w' B') q) := by
  intro q
  refine Fin.addCases ?_ ?_ q
  · intro i; rw [mkT3_castAdd, mkT3_castAdd]; exact hw i
  · intro p; rw [mkT3_natAdd, mkT3_natAdd]; exact hB p

lemma val_mkT3 {w w' : Fin k → TfA (I := I) (M := M)} {B B' : Fin 3 → TfA (I := I) (M := M)}
    {x : M} (hw : ∀ i, w i x = w' i x) (hB : ∀ p, B p x = B' p x) :
    ∀ q, (mkT3 w B) q x = (mkT3 w' B') q x := by
  intro q
  refine Fin.addCases ?_ ?_ q
  · intro i; rw [mkT3_castAdd, mkT3_castAdd]; exact hw i
  · intro p; rw [mkT3_natAdd, mkT3_natAdd]; exact hB p

end Pack

end Work.Diff.EXT
