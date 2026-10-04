import Mathlib
import Submission.Work.Diff.GE.rmP_jointSmooth
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.gramInv_jointSmooth
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.EXT.eq_sum_frameVector_of_pairing
import Submission.Work.Diff.GE.metric_pairing_family_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Finset

/-! ## Multilinearity of `rmP` in its four slots, in finite-sum form

The frozen curvature form `rmP g x a b c d` is additive and `ℝ`-homogeneous in each of its four
arguments (`Work.Diff.GE.rmP_add_fst/…`, `rmP_smul_fst/…`), hence `ℝ`-multilinear; these elementary
lemmas record the resulting expansion of `rmP` applied to four finite sums. -/

private lemma rmP_sum_fst2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (a : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (b c d : TangentSpace I x) :
    rmP g x (∑ i, a i • f i) b c d = ∑ i, a i * rmP g x (f i) b c d := by
  let T : TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun v => rmP g x v b c d
      map_add' := fun v w => rmP_add_fst g hLC x v w b c d
      map_smul' := fun r v => by rw [rmP_smul_fst g hLC x r v b c d]; rfl }
  have h := map_sum T (fun i => a i • f i) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

private lemma rmP_sum_snd2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (b : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (a c d : TangentSpace I x) :
    rmP g x a (∑ i, b i • f i) c d = ∑ i, b i * rmP g x a (f i) c d := by
  let T : TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun v => rmP g x a v c d
      map_add' := fun v w => rmP_add_snd g hLC x a v w c d
      map_smul' := fun r v => by rw [rmP_smul_snd g hLC x r a v c d]; rfl }
  have h := map_sum T (fun i => b i • f i) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

private lemma rmP_sum_thd2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (c : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (a b d : TangentSpace I x) :
    rmP g x a b (∑ i, c i • f i) d = ∑ i, c i * rmP g x a b (f i) d := by
  let T : TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun v => rmP g x a b v d
      map_add' := fun v w => rmP_add_thd g hLC x a b v w d
      map_smul' := fun r v => by rw [rmP_smul_thd g hLC x r a b v d]; rfl }
  have h := map_sum T (fun i => c i • f i) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

private lemma rmP_sum_fth2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (d : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (a b c : TangentSpace I x) :
    rmP g x a b c (∑ i, d i • f i) = ∑ i, d i * rmP g x a b c (f i) := by
  let T : TangentSpace I x →ₗ[ℝ] ℝ :=
    { toFun := fun v => rmP g x a b c v
      map_add' := fun v w => rmP_add_fth g hLC x a b c v w
      map_smul' := fun r v => by rw [rmP_smul_fth g hLC x r a b c v]; rfl }
  have h := map_sum T (fun i => d i • f i) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

/-- Expansion of `rmP` applied to four finite sums in the same frame. -/
private lemma rmP_expand4''
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (a b c d : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    rmP g x (∑ p, a p • f p) (∑ q, b q • f q) (∑ r, c r • f r) (∑ u, d u • f u)
      = ∑ p, ∑ q, ∑ r, ∑ u,
          a p * (b q * (c r * (d u * rmP g x (f p) (f q) (f r) (f u)))) := by
  rw [rmP_sum_fst2 hLC g x a f (∑ q, b q • f q) (∑ r, c r • f r) (∑ u, d u • f u)]
  have hq : ∀ p, a p * rmP g x (f p) (∑ q, b q • f q) (∑ r, c r • f r) (∑ u, d u • f u)
      = ∑ q, ∑ r, ∑ u, a p * (b q * (c r * (d u * rmP g x (f p) (f q) (f r) (f u)))) := by
    intro p
    rw [rmP_sum_snd2 hLC g x b f (f p) (∑ r, c r • f r) (∑ u, d u • f u)]
    simp only [Finset.mul_sum]
    have hr : ∀ q, a p * (b q * rmP g x (f p) (f q) (∑ r, c r • f r) (∑ u, d u • f u))
        = ∑ r, ∑ u, a p * (b q * (c r * (d u * rmP g x (f p) (f q) (f r) (f u)))) := by
      intro q
      rw [rmP_sum_thd2 hLC g x c f (f p) (f q) (∑ u, d u • f u)]
      simp only [Finset.mul_sum]
      have hu : ∀ r, a p * (b q * (c r * rmP g x (f p) (f q) (f r) (∑ u, d u • f u)))
          = ∑ u, a p * (b q * (c r * (d u * rmP g x (f p) (f q) (f r) (f u)))) := by
        intro r
        rw [rmP_sum_fth2 hLC g x d f (f p) (f q) (f r)]
        simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun r _ => hu r)
    exact Finset.sum_congr rfl (fun q _ => hr q)
  exact Finset.sum_congr rfl (fun p _ => hq p)

/-- **Joint smoothness of the frozen curvature form along a family of fields.**  For a metric family
`G` jointly smooth on an open `J ∋ t` and jointly `C^∞` families of tangent fields `A B C D`, the map
`(s,y) ↦ rmP (G s) y (A s y) (B s y) (C s y) (D s y)` is jointly `C^∞` at `(t,x)`.

Proof route: expand each of `A s y, …, D s y` in the coordinate frame `σᵢ y = cFrame x i y` of the
chart at `x` (a basis on the chart source), using
`Work.Diff.EXT.eq_sum_frameVector_of_pairing`; the resulting coefficients
`∑ᵢ GramInv G x s y j i · (G s).inner y (A s y) (σᵢ y)` are jointly smooth by
`Work.Diff.GE.metric_pairing_family_jointSmooth` (pairing the family `A` with the fixed frame field)
and `Work.Diff.GE.gramInv_jointSmooth`; the frame components
`rmP (G s) y (σᵢ y) (σⱼ y) (σₖ y) (σₗ y)` are jointly smooth by `Work.Diff.GE.rmC4_jointSmooth`;
and `rmP` is `ℝ`-multilinear in its four slots (`Work.Diff.GE.rmP_add_*`, `Work.Diff.GE.rmP_smul_*`),
so the expansion is a finite sum of products. -/
theorem rmP_family_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t : ℝ} (ht : t ∈ J) {x : M}
    {A B C D : ℝ → Π y : M, TangentSpace I y}
    (hA : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, A p.1 p.2⟩ : TangentBundle I M)) (t, x))
    (hB : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, B p.1 p.2⟩ : TangentBundle I M)) (t, x))
    (hC : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, C p.1 p.2⟩ : TangentBundle I M)) (t, x))
    (hD : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, D p.1 p.2⟩ : TangentBundle I M)) (t, x)) :
    ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M ↦ Submission.Diff.rmP (G p.1) p.2 (A p.1 p.2) (B p.1 p.2)
        (C p.1 p.2) (D p.1 p.2)) (t, x) := by
  -- the metric `G t` as the Riemannian bundle instance, so that the frame lemmas apply
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun y : M ↦ TangentSpace I y) :=
    inferInstance
  have hsnd : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Prod.snd : ℝ × M → M) (t, x) := contMDiffAt_snd
  -- the constant-in-time families of coordinate frame vectors are jointly smooth
  have hframe : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, cFrame (I := I) x i p.2⟩ : TangentBundle I M)) (t, x) := by
    intro i
    have h := Work.Diff.EXT.contMDiffAt_frameVector (I := I) x (cBasis (E := E) i)
      (mem_chart_source H x)
    exact h.comp (t, x) hsnd
  -- the metric pairings of a jointly smooth family with the frame are jointly smooth
  have hpair : ∀ (V : ℝ → Π y : M, TangentSpace I y),
      ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, V p.1 p.2⟩ : TangentBundle I M)) (t, x) →
      ∀ j : Fin (Module.finrank ℝ E),
        Work.Diff.EXT.JointSmoothAt I M
          (fun p : ℝ × M ↦ (G p.1).inner p.2 (V p.1 p.2) (cFrame (I := I) x j p.2)) t x :=
    fun V hV j => Work.Diff.GE.metric_pairing_family_jointSmooth (I := I) (M := M) hJ hG ht
      (Z := fun s y ↦ cFrame (I := I) x j y) hV (hframe j)
  -- the coordinate coefficients `α^j(s,y) = ∑ᵢ (GramInv G x s y)^{ji} (G s).inner y (V s y) (σᵢ y)`
  let coef : (ℝ → Π y : M, TangentSpace I y) → ℝ × M → Fin (Module.finrank ℝ E) → ℝ :=
    fun V p i ↦ Matrix.mulVec (GramInv (I := I) G x p.1 p.2)
      (fun j ↦ (G p.1).inner p.2 (V p.1 p.2) (cFrame (I := I) x j p.2)) i
  have hcoef : ∀ (V : ℝ → Π y : M, TangentSpace I y),
      ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, V p.1 p.2⟩ : TangentBundle I M)) (t, x) →
      ∀ i : Fin (Module.finrank ℝ E),
        Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ coef V p i) t x := by
    intro V hV i
    have hsum : Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M ↦ ∑ j, GramInv (I := I) G x p.1 p.2 i j *
          ((G p.1).inner p.2 (V p.1 p.2) (cFrame (I := I) x j p.2))) t x :=
      ContMDiffAt.sum (fun j _ ↦
        (Work.Diff.GE.gramInv_jointSmooth (I := I) hJ hG ht x i j).mul (hpair V hV j))
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards with p
    dsimp only [coef]
    rw [Matrix.mulVec_apply_eq_sum]
  -- the frame expansion of a family of fields
  have hexp : ∀ (V : ℝ → Π y : M, TangentSpace I y) (s : ℝ) {y : M},
      y ∈ (chartAt H x).source →
      V s y = ∑ k, Matrix.mulVec (GramInv (I := I) G x s y)
        (fun j ↦ (G s).inner y (V s y) (cFrame (I := I) x j y)) k • cFrame (I := I) x k y := by
    intro V s y hy
    conv_lhs => rw [Work.Diff.EXT.eq_sum_frameVector_of_pairing (I := I) (g := G s) (x₀ := x)
      (p := y) hy (V s y)]
    rfl
  -- the expanded expression is jointly smooth
  have hmain : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M ↦ ∑ p' : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
        ∑ r : Fin (Module.finrank ℝ E), ∑ u : Fin (Module.finrank ℝ E),
        coef A p p' * (coef B p q * (coef C p r *
          (coef D p u * rmC4 (I := I) G x p.1 p.2 p' q r u)))) (t, x) := by
    refine ContMDiffAt.sum (fun p' _ ↦ ?_)
    refine ContMDiffAt.sum (fun q _ ↦ ?_)
    refine ContMDiffAt.sum (fun r _ ↦ ?_)
    refine ContMDiffAt.sum (fun u _ ↦ ?_)
    exact (hcoef A hA p').mul ((hcoef B hB q).mul ((hcoef C hC r).mul
      ((hcoef D hD u).mul (rmC4_jointSmooth (I := I) hLC hJ hG ht x p' q r u))))
  -- the expansion is valid on the chart source, hence near `(t, x)`
  refine hmain.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))] with p hp
  conv_lhs => rw [hexp A p.1 hp.2, hexp B p.1 hp.2, hexp C p.1 hp.2, hexp D p.1 hp.2]
  rw [rmP_expand4'' hLC (G p.1) p.2 (coef A p) (coef B p) (coef C p) (coef D p)
    (fun i ↦ cFrame (I := I) x i p.2)]
  rfl

end Work.Diff.GE
