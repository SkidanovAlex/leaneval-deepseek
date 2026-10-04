import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.T.lcOf_apply_inner_koszul
import Submission.Work.Diff.GE.smooth_onframe
import Submission.Work.Diff.C.mvfderiv_contMDiffAt
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
import Submission.Work.EXT.exists_smooth_ONFrame
import Submission.Work.EXT.sum_inner_smul_eq_self_of_isONFrame
import Submission.Work.EXT.contMDiffAt_of_apply_basis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the Levi-Civita connection of a smooth metric (T2-free)

`Work.EXT.contMDiffCovariantDerivative_lcOf`: for a smooth Riemannian metric `g` on a smooth
manifold `M` (no `T2Space M` hypothesis!), Mathlib's Levi-Civita connection `lcOf g` is a smooth
covariant derivative, i.e. for every `C^∞` section `σ` the section `x ↦ lcOf g σ x` of the bundle
of endomorphisms of `TM` is `C^∞`.

Route (local, no bump functions, hence no `T2Space`):

* `pairing_contMDiffAt`: the metric pairing of two fields smooth at a point is smooth there.
* `mlieBracket_contMDiffAt`: the Lie bracket of two fields smooth at a point is smooth there.
* `lcOf_apply_inner_koszul_at`: Mathlib's Koszul formula for the Levi-Civita connection, with the
  inner products transported from the instance to the explicit metric `g.inner`.
* `lcOf_pairing_contMDiffAt`: for `σ` globally smooth and `X`, `Z` smooth at `p`, the function
  `q ↦ ⟪∇_X σ q, Z q⟫` is smooth at `p`, by the Koszul formula on a neighbourhood where the fields
  are differentiable, at every finite order.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

/-! ## The metric pairing and the Lie bracket at a point -/

/-- The metric pairing `y ↦ g.inner y (X y) (Y y)` of two fields smooth at `x` is smooth at `x`. -/
theorem pairing_contMDiffAt (g : SMet I M) {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x) :
    CMDiffAt ∞ (fun y : M => g.inner y (X y) (Y y)) x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  exact ContMDiffAt.inner_bundle (F := E) (E := fun x : M ↦ TangentSpace I x)
    (b := (id : M → M)) (v := X) (w := Y) hX hY

/-- The Lie bracket of two fields smooth at `x` is smooth at `x`. -/
theorem mlieBracket_contMDiffAt {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x) :
    CMDiffAt ∞ (T% (mlieBracket I X Y)) x := by
  rw [contMDiffAt_infty]
  intro N
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I (((⊤ : ℕ∞) : ℕ∞ω) + 1) M := by
    have h : (((⊤ : ℕ∞) : ℕ∞ω) + 1) = ∞ := by simp
    rw [h]
    infer_instance
  exact ContMDiffAt.mlieBracket_vectorField (m := (N : ℕ∞)) (n := ⊤) hX hY (by simp)

/-- **Koszul formula for `lcOf g`** at a point, with differentiability hypotheses only.  This is
Mathlib's `leviCivitaConnection_apply_inner`, with the instance inner products rewritten as the
explicit `g.inner`. -/
theorem lcOf_apply_inner_koszul_at (g : SMet I M)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    g.inner x ((lcOf g) Y x (X x)) (Z x) =
      (mvfderiv I (fun y : M => g.inner y (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y : M => g.inner y (Z y) (X y)) x (Y x)
        - mvfderiv I (fun y : M => g.inner y (X y) (Y y)) x (Z x)
        - g.inner x (Y x) (mlieBracket I X Z x)
        - g.inner x (Z x) (mlieBracket I Y X x)
        + g.inner x (X x) (mlieBracket I Z Y x)) / 2 := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) := inferInstance
  exact CovariantDerivative.leviCivitaConnection_apply_inner (I := I) (X := X) (Y := Y) (Z := Z)
    hX hY hZ

/-! ## Smoothness of the Koszul pairing -/

/-- For `σ` smooth everywhere and `X`, `Z` smooth at `p`, the pairing `q ↦ ⟪∇_X σ q, Z q⟫` of the
Levi-Civita connection is smooth at `p`. -/
theorem lcOf_pairing_contMDiffAt (g : SMet I M)
    {σ X Z : Π x : M, TangentSpace I x} {p : M}
    (hσ : CMDiff ∞ (T% σ)) (hX : CMDiffAt ∞ (T% X) p) (hZ : CMDiffAt ∞ (T% Z) p) :
    CMDiffAt ∞ (fun q : M => g.inner q ((lcOf g) σ q (X q)) (Z q)) p := by
  rw [contMDiffAt_infty]
  intro N
  -- neighbourhoods of `p` on which `X`, `Z` are differentiable
  obtain ⟨u₁, hu₁, hXu₁⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (I := I) (n := (1 : ℕ∞ω)) (by simp)).mp (hX.of_le (by simp))
  obtain ⟨u₂, hu₂, hZu₂⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (I := I) (n := (1 : ℕ∞ω)) (by simp)).mp (hZ.of_le (by simp))
  obtain ⟨v, hvsub, hvopen, hpv⟩ := mem_nhds_iff.mp (Filter.inter_mem hu₁ hu₂)
  have hXv : CMDiff[v] (1 : ℕ∞ω) (T% X) := hXu₁.mono (hvsub.trans inter_subset_left)
  have hZv : CMDiff[v] (1 : ℕ∞ω) (T% Z) := hZu₂.mono (hvsub.trans inter_subset_right)
  -- the six terms of the Koszul expression, and the expression itself
  set A : M → ℝ := fun q => mvfderiv I (fun y : M => g.inner y (σ y) (Z y)) q (X q) with hA
  set B : M → ℝ := fun q => mvfderiv I (fun y : M => g.inner y (Z y) (X y)) q (σ q) with hB
  set C : M → ℝ := fun q => mvfderiv I (fun y : M => g.inner y (X y) (σ y)) q (Z q) with hC
  set D : M → ℝ := fun q => g.inner q (σ q) (mlieBracket I X Z q) with hD
  set F : M → ℝ := fun q => g.inner q (Z q) (mlieBracket I σ X q) with hF
  set G : M → ℝ := fun q => g.inner q (X q) (mlieBracket I Z σ q) with hG
  -- the identity holds in a neighbourhood of `p`
  have heq : (fun q : M => g.inner q ((lcOf g) σ q (X q)) (Z q))
      =ᶠ[𝓝 p] (fun q : M => (A q + B q - C q - D q - F q + G q) / 2) := by
    filter_upwards [hvopen.mem_nhds hpv] with q hqv
    have h1 : MDiffAt (T% X) q :=
      (ContMDiffWithinAt.contMDiffAt (hXv q hqv) (hvopen.mem_nhds hqv)).mdifferentiableAt (by simp)
    have h2 : MDiffAt (T% Z) q :=
      (ContMDiffWithinAt.contMDiffAt (hZv q hqv) (hvopen.mem_nhds hqv)).mdifferentiableAt (by simp)
    have h3 : MDiffAt (T% σ) q := hσ.contMDiffAt.mdifferentiableAt (by simp)
    exact lcOf_apply_inner_koszul_at g h1 h3 h2
  -- smoothness of the six terms
  have hpair1 : CMDiffAt ∞ (fun y : M => g.inner y (σ y) (Z y)) p :=
    pairing_contMDiffAt g hσ.contMDiffAt hZ
  have hpair2 : CMDiffAt ∞ (fun y : M => g.inner y (Z y) (X y)) p :=
    pairing_contMDiffAt g hZ hX
  have hpair3 : CMDiffAt ∞ (fun y : M => g.inner y (X y) (σ y)) p :=
    pairing_contMDiffAt g hX hσ.contMDiffAt
  have hbr1 : CMDiffAt ∞ (T% (mlieBracket I X Z)) p := mlieBracket_contMDiffAt hX hZ
  have hbr2 : CMDiffAt ∞ (T% (mlieBracket I σ X)) p := mlieBracket_contMDiffAt hσ.contMDiffAt hX
  have hbr3 : CMDiffAt ∞ (T% (mlieBracket I Z σ)) p := mlieBracket_contMDiffAt hZ hσ.contMDiffAt
  have hA' : CMDiffAt N A p :=
    (Work.Diff.C.mvfderiv_contMDiffAt hpair1 hX).of_le (by simp)
  have hB' : CMDiffAt N B p :=
    (Work.Diff.C.mvfderiv_contMDiffAt hpair2 hσ.contMDiffAt).of_le (by simp)
  have hC' : CMDiffAt N C p :=
    (Work.Diff.C.mvfderiv_contMDiffAt hpair3 hZ).of_le (by simp)
  have hD' : CMDiffAt N D p := (pairing_contMDiffAt g hσ.contMDiffAt hbr1).of_le (by simp)
  have hF' : CMDiffAt N F p := (pairing_contMDiffAt g hZ hbr2).of_le (by simp)
  have hG' : CMDiffAt N G p := (pairing_contMDiffAt g hX hbr3).of_le (by simp)
  have hsum : CMDiffAt N (fun q : M => (A q + B q - C q - D q - F q + G q) / 2) p :=
    ((((hA'.add hB').sub hC').sub hD').sub hF').add hG' |>.div_const 2
  exact hsum.congr_of_eventuallyEq heq

/-! ## The chart coordinate frame is smooth at every point of the chart -/

/-- The section `q ↦ (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v` (the tangent vector
whose coordinates in the chart at `x₀` are `v`) is smooth at every point of the chart source. -/
theorem symmL_contMDiffAt (x₀ : M) (v : E) {p : M} (hp : p ∈ (chartAt H x₀).source) :
    CMDiffAt ∞ (T% (fun q : M => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v)) p := by
  set triv := trivializationAt E (TangentSpace I) x₀ with htriv
  have hb : p ∈ triv.baseSet := by
    rw [htriv, TangentBundle.trivializationAt_baseSet]
    exact hp
  rw [Trivialization.contMDiffAt_section_iff triv hb]
  refine (contMDiffAt_const (c := v)).congr_of_eventuallyEq ?_
  filter_upwards [triv.open_baseSet.mem_nhds hb] with q hq
  rw [show triv.symmL ℝ q v = triv.symm q v from
    Trivialization.symmL_apply (e := triv) (R := ℝ) hq v]
  exact congrArg Prod.snd (triv.apply_mk_symm hq v)

/-! ## Applying the connection to a field smooth at a point -/

/-- For `σ` smooth everywhere and `X` smooth at `p`, the field `q ↦ lcOf g σ q (X q)` is smooth
at `p`.  This is where the Koszul pairing is used: expanding `X` in a local orthonormal frame, the
field is a combination of the pairings `q ↦ ⟪∇ σ q, F i q⟫` with the smooth frame fields. -/
theorem lcOf_apply_contMDiffAt (g : SMet I M) {σ X : Π x : M, TangentSpace I x} {p : M}
    (hσ : CMDiff ∞ (T% σ)) (hX : CMDiffAt ∞ (T% X) p) :
    CMDiffAt ∞ (T% (fun q : M => (lcOf g) σ q (X q))) p := by
  obtain ⟨F, hF_ON, hF⟩ := exists_smooth_ONFrame (I := I) g p
  have hexp : (fun q : M => (⟨q, (lcOf g) σ q (X q)⟩ : TangentBundle I M))
      =ᶠ[𝓝 p] (fun q : M =>
        (⟨q, ∑ i, g.inner q ((lcOf g) σ q (X q)) (F q i) • F q i⟩ : TangentBundle I M)) := by
    filter_upwards [hF_ON] with q hq
    exact congrArg (fun w : TangentSpace I q => (⟨q, w⟩ : TangentBundle I M))
      (sum_inner_smul_eq_self_of_isONFrame (I := I) g q (F q) hq
        ((lcOf g) σ q (X q))).symm
  have hterm : ∀ i : Fin (Module.finrank ℝ E), CMDiffAt ∞
      (T% (fun q : M => g.inner q ((lcOf g) σ q (X q)) (F q i) • F q i)) p :=
    fun i => (lcOf_pairing_contMDiffAt g hσ hX (hF i)).smul_section (hF i)
  have hsum := ContMDiffAt.sum_section (I := I) (s := Finset.univ)
    (t := fun i (q : M) => g.inner q ((lcOf g) σ q (X q)) (F q i) • F q i)
    (fun i _ => hterm i)
  have hgoal : CMDiffAt ∞ (T% (fun q : M =>
      ∑ i, g.inner q ((lcOf g) σ q (X q)) (F q i) • F q i)) p := by
    convert hsum using 1
  exact hgoal.congr_of_eventuallyEq hexp

/-! ## Smoothness of the endomorphism-bundle section -/

/-- If applying `A` to every field smooth at `p` gives a field smooth at `p`, then `q ↦ ⟨q, A q⟩`
is a smooth section of the bundle of endomorphisms of `TM` at `p`.  The coordinate representation
of the section in `hom_trivializationAt` is reconstructed from its values on a basis of the model
space. -/
theorem hom_section_contMDiffAt (g : SMet I M)
    {A : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x} {p : M}
    (hA : ∀ X : ((y : M) → TangentSpace I y), CMDiffAt ∞ (T% X) p →
        CMDiffAt ∞ (T% (fun q : M => A q (X q))) p) :
    CMDiffAt ∞ (fun q : M => (⟨q, A q⟩ : TotalSpace (E →L[ℝ] E)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))) p := by
  set triv := trivializationAt E (TangentSpace I) p with htriv
  have hp : p ∈ triv.baseSet := by
    rw [htriv, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H p
  have hb : p ∈ (trivializationAt (E →L[ℝ] E)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) p).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hp, hp⟩
  refine (Trivialization.contMDiffAt_section_iff (trivializationAt (E →L[ℝ] E)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) p) hb).mpr ?_
  simp only [hom_trivializationAt_apply]
  have hZi : ∀ i : Fin (Module.finrank ℝ E),
      CMDiffAt ∞ (T% (fun q : M => triv.symmL ℝ q ((Module.finBasis ℝ E) i))) p :=
    fun i => symmL_contMDiffAt (I := I) p ((Module.finBasis ℝ E) i) (mem_chart_source H p)
  have hcomp : ∀ i : Fin (Module.finrank ℝ E), ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun q : M => (ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
        p q p q (A q)) ((Module.finBasis ℝ E) i)) p := by
    intro i
    have hW : CMDiffAt ∞
        (T% (fun q : M => A q (triv.symmL ℝ q ((Module.finBasis ℝ E) i)))) p := hA _ (hZi i)
    have hcoord : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun q : M =>
        triv.continuousLinearMapAt ℝ q (A q (triv.symmL ℝ q ((Module.finBasis ℝ E) i)))) p := by
      refine ((Trivialization.contMDiffAt_section_iff triv hp).mp hW).congr_of_eventuallyEq ?_
      filter_upwards [triv.open_baseSet.mem_nhds hp] with q hq
      exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ triv hq _
    refine hcoord.congr_of_eventuallyEq ?_
    filter_upwards [triv.open_baseSet.mem_nhds hp] with q hq
    show (ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) p q p q
      (A q)) ((Module.finBasis ℝ E) i)
      = triv.continuousLinearMapAt ℝ q (A q (triv.symmL ℝ q ((Module.finBasis ℝ E) i)))
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply, ← htriv]
  exact contMDiffAt_of_apply_basis (I := I) (Module.finBasis ℝ E) hcomp

theorem contMDiffCovariantDerivative_lcOf
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) :
    CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g) (⊤ : ℕ∞) := by
  refine ⟨⟨?_⟩⟩
  intro σ hσ
  have hσ' : CMDiff ∞ (T% σ) := by
    rw [contMDiffOn_univ] at hσ
    simpa using hσ
  rw [contMDiffOn_univ]
  intro x
  exact hom_section_contMDiffAt (I := I) g
    (A := fun q : M => (Submission.Diff.lcOf g) σ q)
    (fun X hX => lcOf_apply_contMDiffAt (I := I) g hσ' hX)

end Work.EXT

