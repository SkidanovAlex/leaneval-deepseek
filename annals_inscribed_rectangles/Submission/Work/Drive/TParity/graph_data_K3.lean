import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.LocalGraph
import Submission.Work.Drive.TParity.ChartDeriv

/-!
# The local graph structure of the triple intersection set (`K3 D`)

`Work.Drive.TParity.graph_data_K3`: at every point `x` of the triple intersection set `K3 D` of
three smooth chains `D 0, D 1, D 2 : ℝ³ → M` in a smooth `4`-manifold which meet transversally
(`transHyp`), there is a coordinate `i` of the nine-box and a neighbourhood `U` of `x` on which
`K3 D` is *exactly* the graph `y = (y i) • eᵢ + η (y i)` of a smooth map `η : ℝ → ℝ⁹` with
`η t i = 0`.

The point of the proof is that the charted difference map `chartDiff3 p D` at a triple intersection
point is a submersion `ℝ⁹ → ℝ⁸` (transversality, `chartDiff3_surj`), so its kernel is
one-dimensional and therefore not contained in any one coordinate hyperplane; picking a coordinate
`i` in which a non-zero kernel vector does not vanish makes the restriction of the derivative to
`{v | v i = 0}` surjective, which is exactly the hypothesis of the local graph theorem
`exists_local_graph3`.
-/

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **A surjective map `ℝ⁹ → ℝ⁸` is surjective on one of the coordinate hyperplanes.**  The kernel
of such a map is non-zero by rank–nullity, and a non-zero kernel vector has a non-zero coordinate
`i`; subtracting a multiple of it kills the `i`-th coordinate without changing the image. -/
lemma exists_coord_restrict_surjective (L : Amb 8 →L[ℝ] Tgt 8) (hL : Function.Surjective L) :
    ∃ i : Fin 9, Function.Surjective (fun v : {v : Amb 8 // v i = 0} => L v.1) := by
  have hne : LinearMap.ker (L : Amb 8 →ₗ[ℝ] Tgt 8) ≠ ⊥ := by
    intro hbot
    have h1 := LinearMap.finrank_range_add_finrank_ker (L : Amb 8 →ₗ[ℝ] Tgt 8)
    rw [LinearMap.range_eq_top.mpr hL, finrank_top, hbot, finrank_bot] at h1
    rw [finrank_euclideanSpace, finrank_euclideanSpace] at h1
    simp at h1
  obtain ⟨w, hwker, hwne⟩ := (Submodule.ne_bot_iff _).mp hne
  have hw0 : L w = 0 := hwker
  have hcoord : ∃ i : Fin 9, w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hwne (by ext j; exact h j)
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨i, fun u => ?_⟩
  obtain ⟨v, hv⟩ := hL u
  refine ⟨⟨v - (v i / w i) • w, ?_⟩, ?_⟩
  · show (v - (v i / w i) • w) i = 0
    have h1 : (v i / w i) * w i = v i := div_mul_cancel₀ _ hi
    rw [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, h1, sub_self]
  · show L (v - (v i / w i) • w) = u
    rw [map_sub, map_smul, hw0, smul_zero, sub_zero, hv]

theorem graph_data_K3 {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (htrans : Work.Drive.TParity.transHyp D) :
    ∀ x ∈ Work.Drive.TParity.K3 D,
      ∃ (i : Fin 9) (U : Set (Work.Drive.Amb 8)) (η : ℝ → Work.Drive.Amb 8),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t, η t i = 0) ∧
        (∀ y ∈ U, (Work.Drive.TParity.meet3 D y ↔
          y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) := by
  intro x hxK
  obtain ⟨hbox, hm⟩ := mem_K3.mp hxK
  have hreg : x ∈ region3 (D 0 (bPartC 0 x)) D := mem_region3_self D hm
  -- transversality makes the charted difference map a submersion at `x`
  have hsurj : Function.Surjective (fderiv ℝ (chartDiff3 (D 0 (bPartC 0 x)) D) x) :=
    chartDiff3_surj D hD hreg hm (htrans x hbox hm)
  -- hence some coordinate hyperplane is mapped onto the target
  obtain ⟨i, hsurj_i⟩ := exists_coord_restrict_surjective _ hsurj
  -- the local graph theorem
  obtain ⟨δ, ρ, η, hδ, hρ, hηcd, hηi, hηx, hchar⟩ :=
    exists_local_graph3 (D 0 (bPartC 0 x)) D hD hreg hm i hsurj_i
  have hηcont : Continuous η := hηcd.continuous
  refine ⟨i, {y : Amb 8 | |y i - x i| < δ ∧
    ‖y - (y i) • EuclideanSpace.single i (1:ℝ) - η (y i)‖ < ρ}, η, ?_, ?_, hηcd, hηi, ?_⟩
  · have h1 : Continuous (fun y : Amb 8 => |y i - x i|) := by fun_prop
    have h2 : Continuous (fun y : Amb 8 =>
        ‖y - (y i) • EuclideanSpace.single i (1:ℝ) - η (y i)‖) := by fun_prop
    exact (isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const)
  · refine ⟨by simpa using hδ, ?_⟩
    rw [hηx, sub_self, norm_zero]
    exact hρ
  · intro y hy
    exact (hchar y hy.1 hy.2).2

end

end Work.Drive.TParity
