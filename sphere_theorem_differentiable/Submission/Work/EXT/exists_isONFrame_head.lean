import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# An orthonormal frame with prescribed first vector

For a smooth Riemannian metric `g` on `M`, a point `x` and a `g`-unit vector `w ∈ TₓM`, there is a
`g`-orthonormal frame of `TₓM` whose zeroth vector is `w`.

The proof is purely pointwise linear algebra: installing the metric `g` as the `RiemannianBundle`
instance puts an inner product space structure on `TₓM` whose inner product is `g.inner x`
(definitionally), and Mathlib's `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` extends
the orthonormal singleton `{w}` to an orthonormal basis indexed by `Fin (finrank ℝ E)`.
-/

open Bundle
open scoped Manifold ContDiff Bundle Topology

namespace Work.EXT

theorem exists_isONFrame_head
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x : M) (hn : 0 < Module.finrank ℝ E)
    (w : TangentSpace I x) (hw : g.inner x w w = 1) :
    ∃ e : Fin (Module.finrank ℝ E) → TangentSpace I x,
      Submission.Diff.IsONFrame g x e ∧ e ⟨0, hn⟩ = w := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  -- the fiber inner product *is* the metric, definitionally
  have key : ∀ v z : TangentSpace I x, inner ℝ v z = g.inner x v z := fun v z => rfl
  have hw1 : inner ℝ w w = 1 := by rw [key w w]; exact hw
  -- a unit vector for the fiber norm
  have hwn : ‖w‖ = 1 := by
    have h2 : ‖w‖ ^ 2 = 1 ^ 2 := by
      rw [← real_inner_self_eq_norm_sq w, hw1]
      norm_num
    exact (sq_eq_sq₀ (norm_nonneg w) zero_le_one).mp h2
  have hcard : Module.finrank ℝ (TangentSpace I x) =
      Fintype.card (Fin (Module.finrank ℝ E)) := by
    rw [Fintype.card_fin]
    rfl
  -- the orthonormal family given by the single vector `w` at the index `⟨0, hn⟩`
  have hOrth : Orthonormal ℝ
      ((({⟨0, hn⟩} : Set (Fin (Module.finrank ℝ E)))).domRestrict
        (fun _ : Fin (Module.finrank ℝ E) => w)) := by
    constructor
    · intro i
      simp only [Set.domRestrict_apply]
      exact hwn
    · intro i j hij
      exact absurd (Subtype.ext (by
        have hi : i.1 = ⟨0, hn⟩ := Set.mem_singleton_iff.mp i.2
        have hj : j.1 = ⟨0, hn⟩ := Set.mem_singleton_iff.mp j.2
        rw [hi, hj])) hij
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (E := TangentSpace I x) (ι := Fin (Module.finrank ℝ E)) hcard hOrth
  refine ⟨fun i => b i, ?_, ?_⟩
  · intro i j
    rw [← key (b i) (b j)]
    exact orthonormal_iff_ite.mp b.orthonormal i j
  · exact hb ⟨0, hn⟩ (Set.mem_singleton _)

end Work.EXT
