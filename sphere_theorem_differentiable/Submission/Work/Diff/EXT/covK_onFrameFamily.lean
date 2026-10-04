
import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.covK_metric_pairing_family

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A jointly smooth family of orthonormal frames

This file proves `Work.Diff.EXT.covK_onFrameFamily`: for a family of metrics `G` jointly smooth on
an open set `V ⊆ ℝ × M`, there are an open `W ∋ p₀`, `W ⊆ V`, and a family of frames
`F t y : Fin (finrank ℝ E) → T_yM` that is `(G t)`-orthonormal at every `p ∈ W` and jointly smooth.

The construction is Gram–Schmidt applied to the chart frame
`y ↦ (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (b i)` at `x₀ = p₀.2`, with respect to the
metric `G t`; the pointwise Gram–Schmidt process is Mathlib's `InnerProductSpace.gramSchmidt` run
in the inner product space structure on `T_yM` given by the metric `G t`.

The smoothness is proved in three steps.

* `jointField_iff_coords`: on a set contained in the chart source of `x₀`, joint smoothness of a
  section is *equivalent* to the smoothness of its chart coordinates (Mathlib's
  `Bundle.Trivialization.contMDiffOn_iff`).
* `jointField_smul`, `jointField_add`, `jointField_sub`, `jointField_sum`: the coordinate criterion
  turns these into the closure of `ContMDiffOn` under sums, scalar multiples and finite sums.
* `gsFrame_jointField`: the Gram–Schmidt family is jointly smooth, by strong induction on the
  index, using the recursion `gsFrame_rec` (from `gramSchmidt_rec_generic`, a restatement of
  `InnerProductSpace.gramSchmidt_def`) and `covK_metric_pairing_family` for the smoothness of the
  Gram–Schmidt coefficients.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The chart-coordinate criterion for `JointField` -/

/-- **Joint smoothness of a family of sections, read in the chart at `x₀`.**  For `W` contained in
the chart source of `x₀`, a family of tangent fields `X` is jointly smooth on `W` if and only if
the projection `p ↦ p.2` is smooth on `W` (automatic) and the chart coordinates
`p ↦ (trivializationAt E (TangentSpace I) x₀ ⟨p.2, X p.1 p.2⟩).2` are smooth on `W`. -/
theorem jointField_iff_coords {x₀ : M} {W : Set (ℝ × M)}
    (hW : W ⊆ univ ×ˢ (chartAt H x₀).source) (X : ℝ → TField (I := I) (M := M)) :
    JointField X W ↔
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) I ∞ (fun p : ℝ × M => p.2) W ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
        (fun p : ℝ × M => ((trivializationAt E (TangentSpace I) x₀) ⟨p.2, X p.1 p.2⟩).2) W := by
  have hmap : MapsTo (fun p : ℝ × M => (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) W
      (trivializationAt E (TangentSpace I) x₀).source := by
    intro p hp
    rw [Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact (hW hp).2
  exact Bundle.Trivialization.contMDiffOn_iff (e := trivializationAt E (TangentSpace I) x₀) hmap

/-- The chart frame field `y ↦ (trivializationAt E (TangentSpace I) x₀).symmL ℝ y v` is jointly
smooth (it is independent of `t`). -/
theorem jointField_chartFrame {x₀ : M} {W : Set (ℝ × M)}
    (hW : W ⊆ univ ×ˢ (chartAt H x₀).source) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (i : Fin (Module.finrank ℝ E)) :
    JointField (fun (_ : ℝ) (y : M) =>
      (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (b i)) W := by
  rw [jointField_iff_coords hW]
  refine ⟨contMDiffOn_snd, ?_⟩
  refine (contMDiffOn_const (c := b i)).congr ?_
  intro p hp
  have hb : p.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact (hW hp).2
  rw [Trivialization.symmL_apply (R := ℝ) (e := trivializationAt E (TangentSpace I) x₀) hb (b i)]
  exact congrArg Prod.snd
    (Trivialization.apply_mk_symm (trivializationAt E (TangentSpace I) x₀) hb (b i))

/-! ## Closure of `JointField` under the vector space operations -/

/-- A jointly smooth family of fields multiplied by a jointly smooth scalar function. -/
theorem jointField_smul {x₀ : M} {W : Set (ℝ × M)}
    (hW : W ⊆ univ ×ˢ (chartAt H x₀).source)
    {X : ℝ → TField (I := I) (M := M)} (hX : JointField X W) {c : ℝ × M → ℝ}
    (hc : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ c W) :
    JointField (fun t y => c (t, y) • X t y) W := by
  rw [jointField_iff_coords hW] at hX ⊢
  refine ⟨hX.1, ?_⟩
  refine (hc.smul hX.2).congr ?_
  intro p hp
  have hb : p.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact (hW hp).2
  have h1 := Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ
    (trivializationAt E (TangentSpace I) x₀) p.2 hb (c (p.1, p.2) • X p.1 p.2)
  have h2 := Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ
    (trivializationAt E (TangentSpace I) x₀) p.2 hb (X p.1 p.2)
  change ((trivializationAt E (TangentSpace I) x₀) ⟨p.2, c (p.1, p.2) • X p.1 p.2⟩).2 =
    c p • ((trivializationAt E (TangentSpace I) x₀) ⟨p.2, X p.1 p.2⟩).2
  rw [h1, h2]
  exact ContinuousLinearEquiv.map_smul _ _ _

/-- The sum of two jointly smooth families of fields. -/
theorem jointField_add {x₀ : M} {W : Set (ℝ × M)}
    (hW : W ⊆ univ ×ˢ (chartAt H x₀).source)
    {X Y : ℝ → TField (I := I) (M := M)} (hX : JointField X W) (hY : JointField Y W) :
    JointField (fun t y => X t y + Y t y) W := by
  rw [jointField_iff_coords hW] at hX hY ⊢
  refine ⟨hX.1, ?_⟩
  refine (hX.2.add hY.2).congr ?_
  intro p hp
  have hb : p.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact (hW hp).2
  have h1 := Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ
    (trivializationAt E (TangentSpace I) x₀) p.2 hb (X p.1 p.2 + Y p.1 p.2)
  have h2 := Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ
    (trivializationAt E (TangentSpace I) x₀) p.2 hb (X p.1 p.2)
  have h3 := Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ
    (trivializationAt E (TangentSpace I) x₀) p.2 hb (Y p.1 p.2)
  change ((trivializationAt E (TangentSpace I) x₀) ⟨p.2, X p.1 p.2 + Y p.1 p.2⟩).2 =
    ((trivializationAt E (TangentSpace I) x₀) ⟨p.2, X p.1 p.2⟩).2 +
    ((trivializationAt E (TangentSpace I) x₀) ⟨p.2, Y p.1 p.2⟩).2
  rw [h1, h2, h3]
  exact ContinuousLinearEquiv.map_add _ _ _

/-- The difference of two jointly smooth families of fields. -/
theorem jointField_sub {x₀ : M} {W : Set (ℝ × M)}
    (hW : W ⊆ univ ×ˢ (chartAt H x₀).source)
    {X Y : ℝ → TField (I := I) (M := M)} (hX : JointField X W) (hY : JointField Y W) :
    JointField (fun t y => X t y - Y t y) W := by
  rw [jointField_iff_coords hW] at hX hY ⊢
  refine ⟨hX.1, ?_⟩
  refine (hX.2.sub hY.2).congr ?_
  intro p hp
  have hb : p.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact (hW hp).2
  have h1 := Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ
    (trivializationAt E (TangentSpace I) x₀) p.2 hb (X p.1 p.2 - Y p.1 p.2)
  have h2 := Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ
    (trivializationAt E (TangentSpace I) x₀) p.2 hb (X p.1 p.2)
  have h3 := Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ
    (trivializationAt E (TangentSpace I) x₀) p.2 hb (Y p.1 p.2)
  change ((trivializationAt E (TangentSpace I) x₀) ⟨p.2, X p.1 p.2 - Y p.1 p.2⟩).2 =
    ((trivializationAt E (TangentSpace I) x₀) ⟨p.2, X p.1 p.2⟩).2 -
    ((trivializationAt E (TangentSpace I) x₀) ⟨p.2, Y p.1 p.2⟩).2
  rw [h1, h2, h3]
  exact ContinuousLinearEquiv.map_sub _ _ _

/-- A finite linear combination of jointly smooth families of fields, with jointly smooth
coefficients. -/
theorem jointField_sum {x₀ : M} {W : Set (ℝ × M)}
    (hW : W ⊆ univ ×ˢ (chartAt H x₀).source)
    {ι : Type*} (s : Finset ι) {X : ι → ℝ → TField (I := I) (M := M)}
    (hX : ∀ i ∈ s, JointField (X i) W) {c : ι → ℝ × M → ℝ}
    (hc : ∀ i ∈ s, ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ (c i) W) :
    JointField (fun t y => ∑ i ∈ s, c i (t, y) • X i t y) W := by
  classical
  revert hX hc
  refine Finset.induction_on s ?_ ?_
  · intro hX hc
    rw [jointField_iff_coords hW]
    refine ⟨contMDiffOn_snd, ?_⟩
    refine (contMDiffOn_const (c := (0 : E))).congr ?_
    intro p hp
    have hb : p.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact (hW hp).2
    rw [Finset.sum_empty]
    have h1 := Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ
      (trivializationAt E (TangentSpace I) x₀) p.2 hb (0 : TangentSpace I p.2)
    rw [h1]
    exact ContinuousLinearEquiv.map_zero _
  · intro a s ha ih hX hc
    have hterm : JointField (fun t y => c a (t, y) • X a t y) W :=
      jointField_smul hW (hX a (Finset.mem_insert_self a s)) (hc a (Finset.mem_insert_self a s))
    have hrest : JointField (fun t y => ∑ i ∈ s, c i (t, y) • X i t y) W :=
      ih (fun i hi => hX i (Finset.mem_insert_of_mem hi))
        (fun i hi => hc i (Finset.mem_insert_of_mem hi))
    refine (jointField_add hW hterm hrest).congr ?_
    intro p hp
    simp only [Finset.sum_insert ha]

/-! ## Linear independence of the chart frame -/

/-- The chart frame at `x₀` is linearly independent on the chart source. -/
theorem chartFrame_linearIndependent {x₀ : M} {y : M} (hy : y ∈ (chartAt H x₀).source)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ E) =>
      (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (b i)) := by
  have hb : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy
  let A := (trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ y hb
  have hA : ⇑A.symm = ⇑((trivializationAt E (TangentSpace I) x₀).symmL ℝ y) :=
    Bundle.Trivialization.symm_continuousLinearEquivAt_eq (R := ℝ)
      (trivializationAt E (TangentSpace I) x₀) hb
  have h2 : LinearIndependent ℝ (fun i => A.symm (b i)) :=
    (b.map (A.symm : E ≃ₗ[ℝ] TangentSpace I y)).linearIndependent
  have heq : (fun i : Fin (Module.finrank ℝ E) =>
      (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (b i)) = fun i => A.symm (b i) := by
    funext i
    rw [← hA]
  rw [heq]
  exact h2

end Helpers

/-- **The Gram–Schmidt recursion**, in the form used below: `gramSchmidt` is `f i` minus its
projections onto the previous vectors, the coefficient being the metric pairing divided by the
square of the norm. -/
theorem gramSchmidt_rec_generic {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {k : ℕ} (f : Fin k → V) (i : Fin k) :
    InnerProductSpace.gramSchmidt ℝ f i =
      f i - ∑ j ∈ Finset.Iio i,
        ((inner ℝ (InnerProductSpace.gramSchmidt ℝ f j) (f i)) *
          (inner ℝ (InnerProductSpace.gramSchmidt ℝ f j)
            (InnerProductSpace.gramSchmidt ℝ f j))⁻¹) •
        InnerProductSpace.gramSchmidt ℝ f j := by
  rw [InnerProductSpace.gramSchmidt_def]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Submodule.starProjection_singleton]
  congr 1
  simp only [div_eq_mul_inv, real_inner_self_eq_norm_sq]
  norm_cast

section Helpers2

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The Gram–Schmidt family -/

/-- The (unnormalised) Gram–Schmidt family attached to the chart frame at `x₀`, the metric `G t`
and a basis `b` of the model space. -/
noncomputable def gsFrame (G : ℝ → Submission.Diff.SMet I M) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (t : ℝ) (i : Fin (Module.finrank ℝ E)) :
    Π y : M, TangentSpace I y :=
  fun y =>
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
    InnerProductSpace.gramSchmidt ℝ
      (fun j : Fin (Module.finrank ℝ E) =>
        (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (b j)) i

/-- **The Gram–Schmidt recursion.**  Pointwise, `gsFrame G x₀ b t i y` is `frᵢ` minus its
projections onto the previous vectors, the coefficients being computed with the metric `G t`. -/
theorem gsFrame_rec (G : ℝ → Submission.Diff.SMet I M) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) (t : ℝ) (i : Fin (Module.finrank ℝ E))
    (y : M) :
    gsFrame G x₀ b t i y =
      (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (b i) -
        ∑ j ∈ Finset.Iio i,
          (((G t).inner y (gsFrame G x₀ b t j y)
              ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y (b i))) *
            (((G t).inner y (gsFrame G x₀ b t j y) (gsFrame G x₀ b t j y))⁻¹)) •
          gsFrame G x₀ b t j y := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  simp only [gsFrame]
  conv_lhs => rw [gramSchmidt_rec_generic]
  rfl

/-- The Gram–Schmidt vectors do not vanish on the chart source. -/
theorem gsFrame_ne_zero (G : ℝ → Submission.Diff.SMet I M) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (t : ℝ) (i : Fin (Module.finrank ℝ E)) :
    gsFrame G x₀ b t i y ≠ 0 := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  exact InnerProductSpace.gramSchmidt_ne_zero i (chartFrame_linearIndependent hy b)

/-- **Joint smoothness of the Gram–Schmidt family.**  For `W` contained in the chart source of
`x₀` and `G` jointly smooth on `W`, every member `t ↦ gsFrame G x₀ b t i` of the Gram–Schmidt
family is a jointly smooth family of tangent fields on `W`. -/
theorem gsFrame_jointField (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) {W : Set (ℝ × M)}
    (hW : W ⊆ univ ×ˢ (chartAt H x₀).source) (hG : JointMet G W)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    ∀ i : Fin (Module.finrank ℝ E), JointField (fun t => gsFrame G x₀ b t i) W := by
  have key : ∀ m, (hm : m < Module.finrank ℝ E) →
      JointField (fun t => gsFrame G x₀ b t (⟨m, hm⟩ : Fin (Module.finrank ℝ E))) W := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih hm
    set i : Fin (Module.finrank ℝ E) := ⟨m, hm⟩ with hi
    have hc : ∀ j ∈ Finset.Iio i, ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M =>
          ((G p.1).inner p.2 (gsFrame G x₀ b p.1 j p.2)
              ((trivializationAt E (TangentSpace I) x₀).symmL ℝ p.2 (b i))) *
            (((G p.1).inner p.2 (gsFrame G x₀ b p.1 j p.2)
              (gsFrame G x₀ b p.1 j p.2))⁻¹)) W := by
      intro j hj
      have hji : j < i := Finset.mem_Iio.mp hj
      have hjm : j.val < m := hji
      have hGSj : JointField (fun t => gsFrame G x₀ b t j) W := ih j.val hjm j.isLt
      have h1 := covK_metric_pairing_family hG hGSj (jointField_chartFrame hW b i)
      have h2 := covK_metric_pairing_family hG hGSj hGSj
      refine h1.mul (h2.inv₀ (fun p hp => ?_))
      exact ((G p.1).pos p.2 _ (gsFrame_ne_zero G x₀ b (hW hp).2 p.1 j)).ne'
    have hsum : JointField (fun t y => ∑ j ∈ Finset.Iio i,
        (((G t).inner y (gsFrame G x₀ b t j y)
            ((trivializationAt E (TangentSpace I) x₀).symmL ℝ y (b i))) *
          (((G t).inner y (gsFrame G x₀ b t j y) (gsFrame G x₀ b t j y))⁻¹)) •
        gsFrame G x₀ b t j y) W :=
      jointField_sum hW (Finset.Iio i)
        (fun j hj => ih j.val (Finset.mem_Iio.mp hj : j < i) j.isLt) (fun j hj => hc j hj)
    refine (jointField_sub hW (jointField_chartFrame hW b i) hsum).congr ?_
    intro p hp
    dsimp only
    rw [gsFrame_rec G x₀ b p.1 i p.2]
  intro i
  exact key i.val i.isLt

end Helpers2

/-- **A jointly smooth family of orthonormal frames.**  For a family of metrics `G` jointly smooth on
an open set `V ⊆ ℝ × M` containing `p₀`, there are an open `W` with `p₀ ∈ W ⊆ V` and a family of
frames `F t y : Fin (finrank ℝ E) → T_yM`, jointly smooth on `W`, such that `F t y` is
`(G t)`-orthonormal at every `p = (t,y) ∈ W` (`IsONFrame`).

PROOF: Gram–Schmidt applied to the chart frame
`y ↦ (trivializationAt E (TangentSpace I) p₀.2).symmL ℝ y (b i)` (smooth on the chart source), with
respect to the metric `G t`; all Gram–Schmidt coefficients are built from the pairings
`(t,y) ↦ (G t).inner y (A i y) (A k y)` (jointly smooth by `hG`), scalar products, sums, the square
root of a positive quantity and its inverse, hence jointly smooth.  The template is
`Work.Diff.GE.smooth_onframe` (module `Submission.Work.Diff.GE.smooth_onframe`) — do NOT import it or
`Submission.Work.Diff.GE.bianchi_kato_defs`, whose constants (`Work.Diff.GE.exists_isONFrame`) clash
with `Submission.Work.Diff.GE.curvbasic`, already in the import closure of `curvDefs`.  A clash-free
copy of the source material is `Submission.Work.EXT.exists_smooth_ONFrame` (fixed metric; also
unproved) and `Submission.Work.EXT.smooth_onframe_clean`; the relevant elementary lemmas are
`ContMDiffAt.inner_bundle` and the closure of `ContMDiffWithinAt` under sums, products and `inv₀`,
`Real.contDiffAt_sqrt`. -/
theorem covK_onFrameFamily
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V) (hG : JointMet G V)
    {p₀ : ℝ × M} (hp₀ : p₀ ∈ V) :
    ∃ W : Set (ℝ × M), IsOpen W ∧ p₀ ∈ W ∧ W ⊆ V ∧
      ∃ F : ℝ → (Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y),
        (∀ i : Fin (Module.finrank ℝ E), JointField (fun t ↦ fun y ↦ F t y i) W) ∧
        (∀ p ∈ W, IsONFrame (G p.1) p.2 (F p.1 p.2)) := by
  classical
  set x₀ : M := p₀.2 with hx₀
  have hWopen : IsOpen (V ∩ (univ ×ˢ (chartAt H x₀).source)) :=
    hV.inter (isOpen_univ.prod (chartAt H x₀).open_source)
  have hp₀W : p₀ ∈ V ∩ (univ ×ˢ (chartAt H x₀).source) := by
    refine ⟨hp₀, ?_⟩
    rw [Set.mem_prod]
    exact ⟨trivial, by rw [← hx₀]; exact mem_chart_source H p₀.2⟩
  refine ⟨V ∩ (univ ×ˢ (chartAt H x₀).source), hWopen, hp₀W, Set.inter_subset_left, ?_⟩
  set W : Set (ℝ × M) := V ∩ (univ ×ˢ (chartAt H x₀).source) with hWdef
  have hWsub : W ⊆ univ ×ˢ (chartAt H x₀).source := Set.inter_subset_right
  have hGW : JointMet G W := hG.mono Set.inter_subset_left
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  have hGS : ∀ i : Fin (Module.finrank ℝ E),
      JointField (fun t => gsFrame G x₀ b t i) W :=
    gsFrame_jointField G x₀ hWsub hGW b
  -- the normalising coefficient is jointly smooth
  have hcoef : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M =>
          (Real.sqrt ((G p.1).inner p.2 (gsFrame G x₀ b p.1 i p.2)
            (gsFrame G x₀ b p.1 i p.2)))⁻¹) W := by
    intro i
    have hq : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => (G p.1).inner p.2 (gsFrame G x₀ b p.1 i p.2)
          (gsFrame G x₀ b p.1 i p.2)) W :=
      covK_metric_pairing_family hGW (hGS i) (hGS i)
    have hpos : ∀ p ∈ W,
        0 < (G p.1).inner p.2 (gsFrame G x₀ b p.1 i p.2) (gsFrame G x₀ b p.1 i p.2) :=
      fun p hp => (G p.1).pos p.2 _ (gsFrame_ne_zero G x₀ b (hWsub hp).2 p.1 i)
    have hsq : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => Real.sqrt ((G p.1).inner p.2 (gsFrame G x₀ b p.1 i p.2)
          (gsFrame G x₀ b p.1 i p.2))) W := by
      intro p hp
      have hfp : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × M => (G q.1).inner q.2 (gsFrame G x₀ b q.1 i q.2)
            (gsFrame G x₀ b q.1 i q.2)) W p := hq p hp
      have hg : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.sqrt univ
          ((G p.1).inner p.2 (gsFrame G x₀ b p.1 i p.2)
            (gsFrame G x₀ b p.1 i p.2)) :=
        (Real.contDiffAt_sqrt (hpos p hp).ne').contMDiffAt.contMDiffWithinAt
      exact ContMDiffWithinAt.comp (s := W) (t := univ) p hg hfp (fun _ _ => trivial)
    exact hsq.inv₀ (fun p hp => (Real.sqrt_pos.mpr (hpos p hp)).ne')
  refine ⟨fun t y i =>
    (Real.sqrt ((G t).inner y (gsFrame G x₀ b t i y) (gsFrame G x₀ b t i y)))⁻¹ •
      gsFrame G x₀ b t i y, ?_, ?_⟩
  · intro i
    exact jointField_smul hWsub (hGS i) (hcoef i)
  · intro p hp
    have hpy : p.2 ∈ (chartAt H x₀).source := (hWsub hp).2
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G p.1).toRiemannianMetric⟩
    have hli : LinearIndependent ℝ (fun j : Fin (Module.finrank ℝ E) =>
        (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.2 (b j)) :=
      chartFrame_linearIndependent hpy b
    have horth := InnerProductSpace.gramSchmidtNormed_orthonormal (𝕜 := ℝ) hli
    have hF : ∀ i : Fin (Module.finrank ℝ E),
        (Real.sqrt ((G p.1).inner p.2 (gsFrame G x₀ b p.1 i p.2)
            (gsFrame G x₀ b p.1 i p.2)))⁻¹ • gsFrame G x₀ b p.1 i p.2 =
        InnerProductSpace.gramSchmidtNormed ℝ
          (fun j : Fin (Module.finrank ℝ E) =>
            (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.2 (b j)) i := by
      intro i
      show (Real.sqrt ((G p.1).inner p.2 (gsFrame G x₀ b p.1 i p.2)
            (gsFrame G x₀ b p.1 i p.2)))⁻¹ • gsFrame G x₀ b p.1 i p.2 =
          (‖InnerProductSpace.gramSchmidt ℝ
              (fun j : Fin (Module.finrank ℝ E) =>
                (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.2 (b j)) i‖ : ℝ)⁻¹ •
            InnerProductSpace.gramSchmidt ℝ
              (fun j : Fin (Module.finrank ℝ E) =>
                (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.2 (b j)) i
      rw [norm_eq_sqrt_real_inner]
      rfl
    intro i j
    dsimp only
    rw [hF i, hF j]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl]
      change inner ℝ (InnerProductSpace.gramSchmidtNormed ℝ
              (fun j : Fin (Module.finrank ℝ E) =>
                (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.2 (b j)) i)
            (InnerProductSpace.gramSchmidtNormed ℝ
              (fun j : Fin (Module.finrank ℝ E) =>
                (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.2 (b j)) i) = 1
      rw [real_inner_self_eq_norm_sq, horth.1 i, one_pow]
    · rw [ite_eq_right hij]
      change inner ℝ (InnerProductSpace.gramSchmidtNormed ℝ
              (fun j : Fin (Module.finrank ℝ E) =>
                (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.2 (b j)) i)
            (InnerProductSpace.gramSchmidtNormed ℝ
              (fun j : Fin (Module.finrank ℝ E) =>
                (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.2 (b j)) j) = 0
      exact horth.2 hij

end Work.Diff.EXT
