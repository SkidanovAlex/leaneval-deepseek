import Mathlib
import Submission.Work.Diff.EXT.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# T2-free smooth field of orthonormal frames (`Work.EXT.exists_smooth_ONFrame`)

For a smooth Riemannian metric `g` on a smooth manifold `M` and a point `x`, there is a family of
globally defined tangent fields `F i` (`i : Fin (finrank ℝ E)`) such that

* `F · y` is a `g`-orthonormal frame of `T_yM` for all `y` near `x`, and
* every total-space map `y ↦ ⟨y, F i y⟩` is `C^∞` at `x`.

The construction is Gram–Schmidt on the constant-coordinate frame of the chart at `x`
(`(trivializationAt E (TangentSpace I) x).symmL ℝ y (b i)` for a basis `b` of `E`), exactly as in
`Submission/Work/Diff/GE/smooth_onframe.lean`; the `[T2Space M]` hypothesis of that file is *not*
used, so it is dropped here (the caller has no `T2Space M`).  All the auxiliary lemmas are repeated
here, in namespace `Work.EXT.ONF`, without that hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.EXT

namespace ONF

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M]

/-- Metric pairing of two smooth sections. -/
theorem pairing (g : SMet I M) (x : M) {X Y : Π y : M, TangentSpace I y}
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x) :
    CMDiffAt ∞ (fun y : M => g.inner y (X y) (Y y)) x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  exact ContMDiffAt.inner_bundle (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hX hY

/-- Inverse of the square root of the squared length. -/
theorem norm_inv (g : SMet I M) (x : M) {X : Π y : M, TangentSpace I y}
    (hX : CMDiffAt ∞ (T% X) x) (hne : g.inner x (X x) (X x) ≠ 0) :
    CMDiffAt ∞ (fun y : M => (Real.sqrt (g.inner y (X y) (X y)))⁻¹) x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hS : CMDiffAt ∞ (fun y : M => g.inner y (X y) (X y)) x := pairing g x hX hX
  have hpos : 0 < g.inner x (X x) (X x) := by
    rcases eq_or_ne (X x) (0 : TangentSpace I x) with h0 | h0
    · exact absurd (by rw [h0]; simp) hne
    · exact g.pos x (X x) h0
  have h1 : CMDiffAt ∞ (fun y : M => Real.sqrt (g.inner y (X y) (X y))) x :=
    ContMDiffAt.comp x (contMDiffAt_iff_contDiffAt.mpr (Real.contDiffAt_sqrt hpos.ne')) hS
  exact ContMDiffAt.inv₀ h1 (Real.sqrt_pos.mpr hpos).ne'

/-- One Gram–Schmidt step. -/
theorem gs_step (g : SMet I M) (x : M) {ι : Type*} (s : Finset ι)
    {A : ι → Π y : M, TangentSpace I y} {X : Π y : M, TangentSpace I y}
    (hA : ∀ i ∈ s, CMDiffAt ∞ (T% (A i)) x)
    (hX : CMDiffAt ∞ (T% X) x)
    (hne : ∀ i ∈ s, g.inner x (A i x) (A i x) ≠ 0) :
    CMDiffAt ∞ (T% (fun y : M => X y - ∑ i ∈ s,
      ((g.inner y (A i y) (X y)) * (g.inner y (A i y) (A i y))⁻¹) • A i y)) x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hterm : ∀ i ∈ s, CMDiffAt ∞ (T% (fun y : M =>
      ((g.inner y (A i y) (X y)) * (g.inner y (A i y) (A i y))⁻¹) • A i y)) x := by
    intro i hi
    have h1 : CMDiffAt ∞ (fun y : M => g.inner y (A i y) (X y)) x := pairing g x (hA i hi) hX
    have h2 : CMDiffAt ∞ (fun y : M => g.inner y (A i y) (A i y)) x :=
      pairing g x (hA i hi) (hA i hi)
    have h3 : CMDiffAt ∞ (fun y : M => (g.inner y (A i y) (A i y))⁻¹) x :=
      h2.inv₀ (hne i hi)
    exact (h1.mul h3).smul_section (hA i hi)
  exact hX.sub_section (ContMDiffAt.sum_section (s := s) hterm)

/-- The coordinate frame on a chart is a basis. -/
theorem coordframe_li (x : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) {y : M}
    (hy : y ∈ (chartAt H x).source) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        (trivializationAt E (TangentSpace I) x).symmL ℝ y (b i)) := by
  have hb : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hy
  let A := (trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ y hb
  have hA : ⇑A.symm = ⇑((trivializationAt E (TangentSpace I) x).symmL ℝ y) :=
    Bundle.Trivialization.symm_continuousLinearEquivAt_eq (R := ℝ)
      (trivializationAt E (TangentSpace I) x) hb
  have h2 : LinearIndependent ℝ (fun i => A.symm (b i)) :=
    (b.map (A.symm : E ≃ₗ[ℝ] TangentSpace I y)).linearIndependent
  have heq : (fun i : Fin (Module.finrank ℝ E) =>
      (trivializationAt E (TangentSpace I) x).symmL ℝ y (b i)) = fun i => A.symm (b i) := by
    funext i
    rw [← hA]
  rw [heq]
  exact h2

noncomputable def coordFrame (x₀ : M) (v : E) : Π y : M, TangentSpace I y :=
  fun y => (trivializationAt E (TangentSpace I) x₀).symmL ℝ y v

lemma coordFrame_contMDiffAt (x₀ : M) (v : E) {x : M} (hx : x ∈ (chartAt H x₀).source) :
    CMDiffAt ∞ (T% (coordFrame (I := I) x₀ v)) x := by
  have hb : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx
  rw [Bundle.Trivialization.contMDiffAt_section_iff (trivializationAt E (TangentSpace I) x₀) hb]
  refine (contMDiffAt_const (c := v)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hb] with y hy
  rw [show coordFrame (I := I) x₀ v y
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ y v from rfl]
  rw [Bundle.Trivialization.symmL_apply (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hy v]
  exact congrArg Prod.snd ((trivializationAt E (TangentSpace I) x₀).apply_mk_symm hy v)

end ONF

/-- T2-free version of `Work.Diff.GE.smooth_onframe`: for a smooth Riemannian metric `g` on a smooth manifold and a point `x`, there is a family of globally defined tangent fields `F i` (`i : Fin (Module.finrank ℝ E)`) whose total-space maps `y ↦ ⟨y, F i y⟩` are `C^∞` at `x`, and which is an orthonormal frame of `T_yM` for all `y` near `x`. -/
theorem exists_smooth_ONFrame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x : M) :
    ∃ F : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y,
      Filter.Eventually (fun y : M => Submission.Diff.IsONFrame g y (F y)) (nhds x) ∧
      (∀ i : Fin (Module.finrank ℝ E),
        ContMDiffAt I I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M => Bundle.TotalSpace.mk' E y (F y i)) x) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  let n := Module.finrank ℝ E
  let b : Module.Basis (Fin n) ℝ E := Module.finBasis ℝ E
  let fr : Fin n → Π y : M, TangentSpace I y :=
    fun i y => (trivializationAt E (TangentSpace I) x).symmL ℝ y (b i)
  have hfr : ∀ i : Fin n, CMDiffAt ∞ (T% (fr i)) x :=
    fun i => ONF.coordFrame_contMDiffAt (I := I) x (b i) (mem_chart_source H x)
  have hfr_li : ∀ y ∈ (chartAt H x).source, LinearIndependent ℝ (fun i : Fin n => fr i y) :=
    fun y hy => ONF.coordframe_li (I := I) x b hy
  let GS : Fin n → Π y : M, TangentSpace I y :=
    fun i y => InnerProductSpace.gramSchmidt ℝ (fun j : Fin n => fr j y) i
  have hGSli : ∀ i : Fin n, GS i x ≠ 0 := fun i =>
    InnerProductSpace.gramSchmidt_ne_zero i (hfr_li x (mem_chart_source H x))
  let Fs : Fin n → Π y : M, TangentSpace I y :=
    fun i y => (Real.sqrt (g.inner y (GS i y) (GS i y)))⁻¹ • GS i y
  have hGS : ∀ i : Fin n, CMDiffAt ∞ (T% (GS i)) x := by
    suffices h : ∀ m : ℕ, ∀ hm : m < n, CMDiffAt ∞ (T% (GS ⟨m, hm⟩)) x by
      intro i; exact h i.val i.isLt
    intro m
    refine Nat.strong_induction_on m (fun m ih => ?_)
    intro hm
    have hpt : ∀ y : M, GS ⟨m, hm⟩ y = fr ⟨m, hm⟩ y -
        ∑ i ∈ Finset.Iio (⟨m, hm⟩ : Fin n),
          ((g.inner y (GS i y) (fr ⟨m, hm⟩ y)) *
            (g.inner y (GS i y) (GS i y))⁻¹) • GS i y := by
      intro y
      change InnerProductSpace.gramSchmidt ℝ (fun j : Fin n => fr j y) (⟨m, hm⟩ : Fin n) =
        fr ⟨m, hm⟩ y - ∑ i ∈ Finset.Iio (⟨m, hm⟩ : Fin n),
          ((g.inner y (GS i y) (fr ⟨m, hm⟩ y)) *
            (g.inner y (GS i y) (GS i y))⁻¹) • GS i y
      rw [InnerProductSpace.gramSchmidt_def]
      simp only [Submodule.starProjection_singleton]
      congr 1
      refine Finset.sum_congr rfl (fun i hi => ?_)
      congr 1
      rw [← real_inner_self_eq_norm_sq, div_eq_mul_inv]
      rfl
    have hA : ∀ i ∈ Finset.Iio (⟨m, hm⟩ : Fin n), CMDiffAt ∞ (T% (GS i)) x := by
      intro i hi
      have hi' : i < (⟨m, hm⟩ : Fin n) := Finset.mem_Iio.mp hi
      exact ih i.val hi' i.isLt
    have hne : ∀ i ∈ Finset.Iio (⟨m, hm⟩ : Fin n), g.inner x (GS i x) (GS i x) ≠ 0 := by
      intro i hi
      exact inner_self_ne_zero.mpr (hGSli i)
    have hstep := ONF.gs_step (I := I) g x (Finset.Iio (⟨m, hm⟩ : Fin n))
      (A := GS) (X := fr ⟨m, hm⟩) hA (hfr ⟨m, hm⟩) hne
    simpa only [hpt] using hstep
  have hFs : ∀ i : Fin n, CMDiffAt ∞ (T% (Fs i)) x := by
    intro i
    exact (ONF.norm_inv (I := I) g x (hGS i)
      (inner_self_ne_zero.mpr (hGSli i))).smul_section (hGS i)
  have hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => Fs i y) := by
    filter_upwards [(chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with y hy
    have hli := hfr_li y hy
    set GN : Fin n → TangentSpace I y :=
      InnerProductSpace.gramSchmidtNormed ℝ (fun j : Fin n => fr j y) with hGN
    have horth : Orthonormal ℝ GN :=
      hGN ▸ InnerProductSpace.gramSchmidtNormed_orthonormal (𝕜 := ℝ) hli
    have hFs_eq : ∀ i, Fs i y = GN i := by
      intro i
      rw [hGN]
      show (Real.sqrt (g.inner y (GS i y) (GS i y)))⁻¹ • GS i y =
        (‖GS i y‖ : ℝ)⁻¹ • GS i y
      rw [norm_eq_sqrt_real_inner]
      rfl
    rw [show (fun i => Fs i y) = GN from funext hFs_eq]
    intro i j
    have hif : Inner.inner ℝ (GN i) (GN j) = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl, real_inner_self_eq_norm_sq, horth.1 i, one_pow]
      · rw [ite_eq_right hij]
        exact horth.2 hij
    exact hif
  exact ⟨fun y i => Fs i y, hON, fun i => hFs i⟩

end Work.EXT
