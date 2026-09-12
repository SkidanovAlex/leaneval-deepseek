import Mathlib.RingTheory.Flat.TorsionFree
import Submission.Commons.Lattice.Module.basis_extension_pure

open Module Submodule
open scoped BigOperators

noncomputable section

namespace Commons.Lattice.Module

namespace basisExtensionPureRankHelpers

/-- Identity linear equivalence between the two `ℤ`-module structures on a submodule `p`:
the source is `p.module` (the module structure of the submodule), and the target is
`AddCommGroup.toIntModule p` (the canonical module derived from the additive group). -/
noncomputable def submoduleToIntModuleEquiv {M : Type*} [AddCommGroup M] [Module ℤ M]
    (p : Submodule ℤ M) :
    @LinearEquiv ℤ ℤ _ _ (RingHom.id ℤ) (RingHom.id ℤ) _ _ (↥p) (↥p) _ _ p.module
      (AddCommGroup.toIntModule (↥p)) := by
  let L : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) (↥p) (↥p) _ _ p.module (AddCommGroup.toIntModule (↥p)) :=
    @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) (↥p) (↥p) _ _ p.module (AddCommGroup.toIntModule (↥p))
      (AddMonoidHom.id (↥p)) (by
        intro c x
        apply Subtype.ext
        exact int_smul_eq_zsmul (inferInstance : Module ℤ M) c (x : M))
  exact @LinearEquiv.mk ℤ ℤ _ _ (RingHom.id ℤ) (RingHom.id ℤ) _ _ (↥p) (↥p) _ _ p.module
      (AddCommGroup.toIntModule (↥p)) L id (by intro x; rfl) (by intro x; rfl)

/-- The inclusion of a submodule into `M`, as a linear map from the canonical module
(`AddCommGroup.toIntModule p`) to `M` (with `M`'s given module structure). -/
def submoduleSubtypeInt {M : Type*} [AddCommGroup M] [Module ℤ M] (p : Submodule ℤ M) :
    @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) (↥p) M _ _ (AddCommGroup.toIntModule (↥p))
      (inferInstance : Module ℤ M) where
  toFun := fun x => (x : M)
  map_add' := by intro x y; rfl
  map_smul' := by
    intro c x
    exact (int_smul_eq_zsmul (inferInstance : Module ℤ M) c (x : M)).symm

@[simp]
lemma submoduleSubtypeInt_apply {M : Type*} [AddCommGroup M] [Module ℤ M] (p : Submodule ℤ M)
    (x : ↥p) : submoduleSubtypeInt p x = (x : M) := rfl

end basisExtensionPureRankHelpers

open basisExtensionPureRankHelpers

theorem basis_extension_pure_rank {m d : ℕ} (hd : d ≤ m)
    {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (N : Submodule ℤ M) [Module.Free ℤ N] [Module.Finite ℤ N]
    (bM : Module.Basis (Fin m) ℤ M) (bN : Module.Basis (Fin d) ℤ N)
    (hpure : ∀ x : M, (∃ a : ℤ, a ≠ 0 ∧ a • x ∈ N) → x ∈ N) :
    ∃ e : Module.Basis (Fin m) ℤ M,
      ∀ i : Fin d, (e (Fin.castLE hd i) : M) = ((bN i : N) : M) := by
  classical
  obtain ⟨n0, o, hno, bO, bN0, a, hsnf⟩ :=
    Submodule.exists_smith_normal_form_of_le bM N (⊤ : Submodule ℤ M) le_top
  let bM' : Basis (Fin o) ℤ M := by
    letI : Module ℤ (⊤ : Submodule ℤ M) := (⊤ : Submodule ℤ M).module
    exact bO.map (LinearEquiv.ofTop (⊤ : Submodule ℤ M) rfl)
  have hbM'_eq_bO : ∀ j : Fin o, (bM' j : M) = (bO j : M) := by
    intro j
    simp [bM', LinearEquiv.ofTop_apply]
  have hsnf' : ∀ i : Fin n0, ((bN0 i : N) : M) = a i • bM' (Fin.castLE hno i) := by
    intro i
    have hstep1 : ((bN0 i : N) : M) = a i • (bO (Fin.castLE hno i) : M) := by
      rw [← int_smul_eq_zsmul (inferInstance : Module ℤ M) (a i) ((bO (Fin.castLE hno i) : M))]
      exact hsnf i
    calc
      ((bN0 i : N) : M) = a i • (bO (Fin.castLE hno i) : M) := hstep1
      _ = a i • bM' (Fin.castLE hno i) := by rw [hbM'_eq_bO]
  have ho : o = m := by
    have hfinO : Module.finrank ℤ M = o := by
      simpa using (Module.finrank_eq_card_basis bM')
    have hfinM : Module.finrank ℤ M = m := by
      simpa using (Module.finrank_eq_card_basis bM)
    omega
  let bN0i : Basis (Fin n0) ℤ N :=
    @Basis.map (Fin n0) ℤ (↥N) (↥N) _ _ N.module _ (AddCommGroup.toIntModule (↥N)) bN0
      (submoduleToIntModuleEquiv N)
  have hn0 : n0 = d := by
    have h1 : Module.finrank ℤ N = n0 := by
      simpa using (Module.finrank_eq_card_basis bN0i)
    have h2 : Module.finrank ℤ N = d := by
      simpa using (Module.finrank_eq_card_basis bN)
    omega
  have hdo : d ≤ o := by omega
  have ha_ne : ∀ i : Fin n0, a i ≠ 0 := by
    intro i h0
    have hzero : ((bN0 i : N) : M) = 0 := by
      rw [hsnf i]
      rw [h0]
      simp
    apply (Basis.ne_zero bN0i i)
    apply Subtype.ext
    simpa [bN0i] using hzero
  have hbM_mem : ∀ i : Fin n0, bM' (Fin.castLE hno i) ∈ N := by
    intro i
    exact hpure (bM' (Fin.castLE hno i)) ⟨a i, ha_ne i, by
      rw [← hsnf' i]
      exact (bN0 i).2⟩
  have hNspan : N = span ℤ (Set.range fun i : Fin n0 => bM' (Fin.castLE hno i)) := by
    apply le_antisymm
    · intro x hx
      rcases (bN0.mem_submodule_iff'.mp hx) with ⟨c, hc⟩
      rw [hc]
      refine Submodule.sum_mem _ ?_
      intro i _
      have hb : ((bN0 i : N) : M) ∈
          span ℤ (Set.range fun i : Fin n0 => bM' (Fin.castLE hno i)) := by
        rw [hsnf' i]
        rw [← int_smul_eq_zsmul (inferInstance : Module ℤ M) (a i) (bM' (Fin.castLE hno i))]
        exact (span ℤ (Set.range fun i : Fin n0 => bM' (Fin.castLE hno i))).smul_mem
          (a i) (subset_span ⟨i, rfl⟩)
      exact (span ℤ (Set.range fun i : Fin n0 => bM' (Fin.castLE hno i))).smul_mem (c i) hb
    · exact span_le.mpr (by
        intro y hy
        rcases hy with ⟨i, rfl⟩
        exact hbM_mem i)
  have hspan_d : span ℤ (Set.range fun j : Fin d => bM' (Fin.castLE hdo j)) =
      span ℤ (Set.range fun i0 : Fin n0 => bM' (Fin.castLE hno i0)) := by
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      have hj0 : j.val < n0 := by omega
      refine ⟨⟨j.val, hj0⟩, ?_⟩
      change bM' (Fin.castLE hno ⟨j.val, hj0⟩) = bM' (Fin.castLE hdo j)
      congr
    · rintro ⟨i0, rfl⟩
      have hi0d : i0.val < d := by omega
      refine ⟨⟨i0.val, hi0d⟩, ?_⟩
      change bM' (Fin.castLE hdo ⟨i0.val, hi0d⟩) = bM' (Fin.castLE hno i0)
      congr
  have hNblock : LinearMap.range (submoduleSubtypeInt N) =
      span ℤ (Set.range fun j : Fin d => bM' (Fin.castLE hdo j)) := by
    have hran : LinearMap.range (submoduleSubtypeInt N) = N := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact x.2
      · intro hz
        exact ⟨⟨z, hz⟩, rfl⟩
    rw [hran, hNspan, ← hspan_d]
  obtain ⟨e0, he0⟩ :=
    BasisExtensionPure.exists_basis_extend_of_range_block (M := M) (N := N)
      (o := o) (n0 := d) hdo (submoduleSubtypeInt N)
      (by
        rw [LinearMap.ker_eq_bot]
        intro x y h
        apply Subtype.ext
        exact h)
      bM' bN hNblock
  let e : Basis (Fin m) ℤ M := e0.reindex (finCongr ho)
  refine ⟨e, ?_⟩
  intro u
  have hs : (finCongr ho).symm (Fin.castLE hd u) = Fin.castLE hdo u := by
    apply Fin.ext
    rfl
  have hm : (e (Fin.castLE hd u) : M) = ((bN u : N) : M) := by
    dsimp [e]
    rw [Basis.reindex_apply, hs]
    simpa using he0 u
  exact hm

end Commons.Lattice.Module