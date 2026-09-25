import Mathlib

namespace Work.Tower.Shafarevich.Rank

/-- If `φ : F_d ↠ G` has kernel the normal closure of the relators `R`, and the normal subgroup
`N ≤ G` is the normal closure of the elements `g`, then the kernel of the composite
`F_d → G → G ⧸ N` is the normal closure of `r + k` relators: the `R` together with chosen
lifts of the `g`. -/
theorem ker_comp_mk_eq {G : Type} [Group G] {d r k : ℕ} (N : Subgroup G) [N.Normal]
    (φ : FreeGroup (Fin d) →* G) (hφ : Function.Surjective φ)
    (R : Fin r → FreeGroup (Fin d))
    (hR : φ.ker = Subgroup.normalClosure (Set.range R))
    (g : Fin k → G) (hN : N = Subgroup.normalClosure (Set.range g)) :
    ∃ R' : Fin (r + k) → FreeGroup (Fin d),
      ((QuotientGroup.mk' N).comp φ).ker = Subgroup.normalClosure (Set.range R') := by
  classical
  -- Choose lifts of the generators `g i` of `N` to the free group.
  obtain ⟨gl, hgl⟩ : ∃ gl : Fin k → FreeGroup (Fin d), ∀ i, φ (gl i) = g i :=
    ⟨fun i => (hφ (g i)).choose, fun i => (hφ (g i)).choose_spec⟩
  -- Membership in the kernel of the composite means the image lies in `N`.
  have mem_ker : ∀ x : FreeGroup (Fin d),
      x ∈ ((QuotientGroup.mk' N).comp φ).ker ↔ φ x ∈ N := by
    intro x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  have hcomp : (φ : FreeGroup (Fin d) → G) ∘ gl = g := funext hgl
  -- The image of the normal closure of the lifts is the normal closure of `range g`.
  have hmap : (Subgroup.normalClosure (Set.range gl)).map φ
      = Subgroup.normalClosure (Set.range g) := by
    rw [Subgroup.map_normalClosure (Set.range gl) φ hφ, ← Set.range_comp, hcomp]
  have hsubR : Set.range R ⊆ Set.range (Fin.append R gl) := by
    intro x hx
    obtain ⟨j, rfl⟩ := hx
    exact ⟨Fin.castAdd k j, Fin.append_left R gl j⟩
  have hsubgl : Set.range gl ⊆ Set.range (Fin.append R gl) := by
    intro x hx
    obtain ⟨j, rfl⟩ := hx
    exact ⟨Fin.natAdd r j, Fin.append_right R gl j⟩
  -- The candidate family of relators: `R` followed by the lifts.
  refine ⟨Fin.append R gl, le_antisymm ?_ ?_⟩
  · -- `ker (mk' N ∘ φ) ≤ normalClosure (range R')`
    intro x hx
    have hφx : φ x ∈ Subgroup.normalClosure (Set.range g) := hN ▸ (mem_ker x).mp hx
    rw [← hmap] at hφx
    -- So `φ x = φ y` for some `y` in the normal closure of the lifts.
    obtain ⟨y, hy, hφy⟩ := Subgroup.mem_map.mp hφx
    have hxy : x * y⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφy, mul_inv_cancel]
    rw [hR] at hxy
    have h1 : x * y⁻¹ ∈ Subgroup.normalClosure (Set.range (Fin.append R gl)) :=
      Subgroup.normalClosure_mono hsubR hxy
    have h2 : y ∈ Subgroup.normalClosure (Set.range (Fin.append R gl)) :=
      Subgroup.normalClosure_mono hsubgl hy
    have hxeq : x = (x * y⁻¹) * y := by group
    rw [hxeq]
    exact mul_mem h1 h2
  · -- `normalClosure (range R') ≤ ker (mk' N ∘ φ)`
    apply Subgroup.normalClosure_le_normal
    rw [Set.range_subset_iff]
    intro i
    rw [SetLike.mem_coe]
    induction i using Fin.addCases with
    | left j =>
      rw [Fin.append_left, mem_ker]
      have h1 : φ (R j) = 1 := by
        rw [← MonoidHom.mem_ker, hR]
        exact Subgroup.subset_normalClosure ⟨j, rfl⟩
      rw [h1]
      exact one_mem N
    | right j =>
      rw [Fin.append_right, mem_ker, hgl j, hN]
      exact Subgroup.subset_normalClosure ⟨j, rfl⟩

end Work.Tower.Shafarevich.Rank
