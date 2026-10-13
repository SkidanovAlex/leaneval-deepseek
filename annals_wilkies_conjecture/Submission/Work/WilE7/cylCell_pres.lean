/-
  Area E7: cylindrical cell preservation.

  Given a semi-Pfaffian set `Z` in `ℝ^{p+M}` and a connected component `K` of `Z.set` at a point
  `u₀`, let `C = projFirst p M '' K` be the projection of that component onto `ℝ^p`.  The lemma
  `cylCell_pres` produces a semi-Pfaffian set `Z'` in `ℝ^{(p+1)+M'}` (here `M' = M`) together with
  a base point `u₀' ∈ Z'.set` such that the projection of the connected component of `Z'.set` at
  `u₀'` is exactly the cylinder `C × [-1,1]` over `C` in the new (last) coordinate, with a format
  bound `A = F + 1` and degree bound `D` (i.e. `Cb = X`).

  The construction is the cylindrical lift of a semi-Pfaffian set along the coordinate injection
  `Work.WilE8.skipInj p M`, which inserts the new free coordinate at position `p`:

  * `Work.WilE8.Star.connectedComponentIn_liftCyl` identifies the connected components of the
    lifted set with the cylinders over the connected components of the original one;
  * `Work.WilE8.Star.projFirst_cyl` computes the projection of such a cylinder;
  * `Work.WilE8.Extend.semipf_deg_extend` says the degree does not change.

  The only elementary point is that the closed cube on the first `p+1` coordinates may be replaced
  by the condition `|last coordinate| ≤ 1`, because membership in `C` already forces the first `p`
  coordinates into the cube.
-/
import Mathlib
import Submission.Work.WilE7.pad_component_proj
import Submission.Work.WilE8.Star.lift_right_cube
import Submission.Work.WilE8.Star.projFirst_cyl
import Submission.Work.WilE8.Extend.semipf_set_extend
import Submission.Work.WilE8.Extend.semipf_deg_extend

set_option autoImplicit false
noncomputable section

namespace Work.WilE7

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- Let `K ⊆ ℝ^{p+M}` be contained in the closed cube.  Cutting the cylinder
`{z : Fin (p+1) → ℝ | Fin.init z ∈ projFirst p M '' K}` by the closed cube `cubeC (p+1)` is the
same as intersecting it with the closed interval on the last coordinate: the first `p`
coordinates are automatically in the cube because they lie in `projFirst p M '' K ⊆ cubeC p`. -/
theorem projFirst_cube_cyl {p M : ℕ} (K : Set (Fin (p + M) → ℝ))
    (hK : K ⊆ cubeC (p + M)) :
    {z : Fin (p + 1) → ℝ | Fin.init z ∈ projFirst p M '' K} ∩ cubeC (p + 1) =
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ projFirst p M '' K ∧ |y (Fin.last p)| ≤ 1} := by
  ext y
  constructor
  · rintro ⟨hy1, hy2⟩
    exact ⟨hy1, hy2 (Fin.last p)⟩
  · rintro ⟨hy1, hy2⟩
    refine ⟨hy1, ?_⟩
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · obtain ⟨a, haK, ha⟩ := hy1
      have h2 : y j.castSucc = a (Fin.castAdd M j) := (congrFun ha j).symm
      rw [h2]
      exact hK haK (Fin.castAdd M j)
    · exact hy2

theorem cylCell_pres (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ), ∀ (p M : ℕ) (Z : WilkiesDesign.E.SemiPf (p + M))
      (u₀ : Fin (p + M) → ℝ) (hu₀ : u₀ ∈ Z.set) (C : Set (Fin p → ℝ))
      (hC : C = Set.image (WilkiesDesign.E.projFirst p M) (connectedComponentIn Z.set u₀)) (D : ℕ),
      Z.fmt ≤ F → Z.deg ≤ D →
      ∃ (M' : ℕ) (Z' : WilkiesDesign.E.SemiPf (p + 1 + M')) (u₀' : Fin (p + 1 + M') → ℝ),
        u₀' ∈ Z'.set ∧
        WilkiesDesign.E.projFirst (p + 1) M' '' (connectedComponentIn Z'.set u₀') =
          {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ |y (Fin.last p)| ≤ 1} ∧
        Z'.fmt ≤ A ∧ Z'.deg ≤ Cb.eval D := by
  refine ⟨F + 1, Polynomial.X, ?_⟩
  intro p M Z u₀ hu₀ C hC D hfmt hdeg
  have hKsub : connectedComponentIn Z.set u₀ ⊆ cubeC (p + M) :=
    fun x hx => Work.WilE8.SemiPf.set_subset_cube Z (connectedComponentIn_subset Z.set u₀ hx)
  have hq : ∀ i : Fin (p + M),
      Work.WilE8.Star.insCoord p M u₀ 0 (Work.WilE8.skipInj p M i) = u₀ i :=
    fun i => Work.WilE8.Star.insCoord_skipInj p M u₀ 0 i
  have hcube : u₀ ∈ Z.set → Work.WilE8.Star.insCoord p M u₀ 0 ∈ cubeC (p + 1 + M) :=
    fun hp => Work.WilE8.Star.insCoord_cube p M (Work.WilE8.SemiPf.set_subset_cube Z hp)
      (by norm_num)
  refine ⟨M, Work.WilE8.SemiPf.extend (Work.WilE8.skipInj p M) Z,
    Work.WilE8.Star.insCoord p M u₀ 0, ?_, ?_, ?_, ?_⟩
  · rw [Work.WilE8.Extend.semipf_set_extend (Work.WilE8.Star.skipInj_injective p M) Z]
    refine ⟨hcube hu₀, ?_⟩
    show (fun i => Work.WilE8.Star.insCoord p M u₀ 0 (Work.WilE8.skipInj p M i)) ∈ Z.set
    rw [funext hq]
    exact hu₀
  · rw [Work.WilE8.Star.connectedComponentIn_liftCyl (n := p) (m := M) Z u₀
        (Work.WilE8.Star.insCoord p M u₀ 0) hq hcube]
    rw [Work.WilE8.Star.projFirst_cyl (n := p) (m := M) hKsub]
    rw [hC]
    exact projFirst_cube_cyl (connectedComponentIn Z.set u₀) hKsub
  · have hfmt' : (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj p M) Z).fmt =
        (p + 1 + M) + Z.r := rfl
    have hfmtZ : Z.fmt = (p + M) + Z.r := rfl
    rw [hfmt']
    rw [hfmtZ] at hfmt
    omega
  · rw [Work.WilE8.Extend.semipf_deg_extend (Work.WilE8.Star.skipInj_injective p M) Z,
      Polynomial.eval_X]
    exact hdeg

end Work.WilE7
