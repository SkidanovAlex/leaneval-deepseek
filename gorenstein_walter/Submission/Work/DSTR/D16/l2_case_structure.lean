import Mathlib

open scoped MatrixGroups

namespace Work.DSTR.D16

set_option linter.unusedVariables false

/-- Auxiliary structural lemma.

Let `L ≤ Q` be a subgroup isomorphic (via `e`) to a group `M`, and suppose the commutator
subgroup `N = ⁅M, M⁆` of `M` is isomorphic to a group `T` and has index at most two in `M`.
Then the commutator subgroup `⁅L, L⁆` of `L` — viewed as a subgroup of `Q` — is isomorphic to
`T` and has index at most two in `L`.

The point is that an isomorphism transports commutator subgroups
(`Subgroup.map_subtype_commutator` identifies `(commutator ↥L).map L.subtype` with `⁅L, L⁆`, and
`Subgroup.map_commutator` identifies the image of `commutator ↥L` under `e` with `commutator M`),
and that the index of a subgroup is preserved by an isomorphism
(`Subgroup.index_map_equiv`). -/
theorem l2_commutator_aux (Q : Type*) [Group Q] (L : Subgroup Q)
    {M : Type*} [Group M] (e : ↥L ≃* M) (N : Subgroup M) (hN : N = commutator M)
    (hNidx : N.index ≤ 2) {T : Type*} [Group T] (hNiso : Nonempty (N ≃* T)) :
    ∃ P : Subgroup Q, P ≤ L ∧ P = ⁅L, L⁆ ∧ Nonempty (P ≃* T) ∧
      (P.subgroupOf L).index ≤ 2 := by
  classical
  -- The commutator subgroup of `L`, viewed inside `↥L` as a subgroup, is `commutator ↥L`.
  have hPsub : (⁅L, L⁆ : Subgroup Q).subgroupOf L = _root_.commutator ↥L := by
    rw [← Subgroup.map_subtype_commutator L, ← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  -- Transporting the commutator subgroup of `↥L` along the isomorphism `e` gives `commutator M`.
  have hcomm : (_root_.commutator ↥L).map (e : ↥L →* M) = commutator M := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, MulEquiv.range_eq_top,
      commutator_def]
  refine ⟨⁅L, L⁆, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.commutator_le_self L
  · rfl
  · -- `⁅L, L⁆ ≃* (⁅L, L⁆).subgroupOf L ≃* commutator ↥L ≃* commutator M = N ≃* T`.
    refine ⟨(Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self L)).symm.trans ?_⟩
    refine (MulEquiv.subgroupCongr hPsub).trans ?_
    refine (MulEquiv.subgroupMap e (_root_.commutator ↥L)).trans ?_
    refine (MulEquiv.subgroupCongr hcomm).trans ?_
    exact (MulEquiv.subgroupCongr hN.symm).trans hNiso.some
  · -- The index is preserved by the isomorphism `e` and equals `N.index ≤ 2`.
    have hidx : ((⁅L, L⁆ : Subgroup Q).subgroupOf L).index = N.index := by
      have h1 : ((⁅L, L⁆ : Subgroup Q).subgroupOf L).index =
          (((⁅L, L⁆ : Subgroup Q).subgroupOf L).map (e : ↥L →* M)).index :=
        (Subgroup.index_map_equiv ((⁅L, L⁆ : Subgroup Q).subgroupOf L) e).symm
      have h2 : (((⁅L, L⁆ : Subgroup Q).subgroupOf L).map (e : ↥L →* M)) = commutator M := by
        rw [hPsub, hcomm]
      rw [h1, h2, ← hN]
    rw [hidx]; exact hNidx

theorem l2_case_structure (Q : Type) [Group Q] (L : Subgroup Q) (p k : ℕ) [Fact p.Prime] (hq : 5 ≤ p ^ k) (hPSLperf : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) (hPGL : ∃ P₀ : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)), P₀.Normal ∧ P₀.index = 2 ∧ Nonempty (P₀ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ∧ P₀ = ⁅(⊤ : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k))), ⊤⁆) (h : Nonempty (↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ∨ Nonempty (↥L ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k))) : ∃ P : Subgroup Q, P ≤ L ∧ P = ⁅L, L⁆ ∧ Nonempty (P ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ∧ (P.subgroupOf L).index ≤ 2 := by
  classical
  rcases h with h1 | h2
  · -- Case `L ≃* PSL(2, q)`: `PSL(2, q)` is perfect, so its commutator subgroup is everything.
    obtain ⟨e⟩ := h1
    exact l2_commutator_aux Q L e ⊤
      (@Group.IsPerfect.commutator_eq_top
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) _ hPSLperf).symm
      (by rw [Subgroup.index_top]; norm_num) ⟨Subgroup.topEquiv⟩
  · -- Case `L ≃* PGL(2, q)`: use the supplied normal subgroup of index two, which is the
    -- commutator subgroup of `PGL(2, q)` and is isomorphic to `PSL(2, q)`.
    obtain ⟨e⟩ := h2
    obtain ⟨P₀, _, hidx, hiso, hcommP⟩ := hPGL
    exact l2_commutator_aux Q L e P₀ hcommP (le_of_eq hidx) hiso

end Work.DSTR.D16
