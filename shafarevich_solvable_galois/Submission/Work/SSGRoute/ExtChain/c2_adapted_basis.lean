import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- The involution hypothesis `ht` is not needed: purity of `ker (t + 1)` only uses that `V` is
-- torsion-free.  (Keeping the statement as requested.)
set_option linter.unusedVariables false

namespace Work.SSGRoute.ExtChain

-- Make the `ℤ`-module structure (rather than the derived `zsmul`) the canonical `ℤ`-scalar action
-- for the duration of the proof, and likewise the restricted module structure on submodules: this
-- keeps the `ℤ`-module instance diamonds on `Submodule`s from producing non-definitionally-equal
-- instances.
attribute [-instance] AddCommGroup.toIntModule in
attribute [-instance] ZSMul.toSMul in
/-- An integral basis adapted to an involution. For a finite free `ℤ`-module `V` with an involution `t` (so `t (t v) = v`), there is a `ℤ`-basis `B` indexed by `Fin a ⊕ Fin b` whose `Fin a`-part is a basis of the `(-1)`-eigenspace `ker (t + 1)`: `t (B (Sum.inl i)) = - B (Sum.inl i)`, and the span of that part is exactly `LinearMap.ker (t + LinearMap.id)`. Reason: `ker (t + 1)` is pure in the torsion-free `V`, hence a direct summand, and so has a `ℤ`-basis which extends to one of `V`. -/
theorem c2_adapted_basis {V : Type} [AddCommGroup V] [Module ℤ V] [Module.Finite ℤ V]
    [Module.Free ℤ V] (t : V →ₗ[ℤ] V) (ht : ∀ v, t (t v) = v) :
    ∃ (a b : ℕ) (B : Module.Basis (Fin a ⊕ Fin b) ℤ V),
      (∀ i : Fin a, t (B (Sum.inl i)) = -B (Sum.inl i)) ∧
      Submodule.span ℤ (Set.range fun i : Fin a => B (Sum.inl i)) =
        LinearMap.ker (t + LinearMap.id) := by
  classical
  set W : Submodule ℤ V := LinearMap.ker (t + LinearMap.id) with hW
  -- `W` is pure in the torsion-free `V`: `n v ∈ W`, `n ≠ 0` imply `v ∈ W`.
  have hpure : ∀ (k : ℤ) (v : V), k ≠ 0 → k • v ∈ W → v ∈ W := by
    intro k v hk hv
    rw [hW, LinearMap.mem_ker] at hv ⊢
    have h1 : k • ((t + LinearMap.id : V →ₗ[ℤ] V) v) = 0 := by
      have hz := map_smul (f := (t + LinearMap.id : V →ₗ[ℤ] V)) k v
      rw [← hz]
      exact hv
    exact (smul_eq_zero_iff_right hk).mp h1
  -- Smith normal form of the pure submodule `W` of the free module `V`.
  obtain ⟨n, o, hno, bO, bN, a, hsnf⟩ :=
    Submodule.exists_smith_normal_form_of_le (Module.finBasis ℤ V) W ⊤ le_top
  let bV : Module.Basis (Fin o) ℤ V := bO.map Submodule.topEquiv
  have hbV : ∀ j : Fin o, bV j = (bO j : V) := by
    intro j
    simp [bV, Module.Basis.map_apply, Submodule.topEquiv_apply]
  have hsnf' : ∀ i : Fin n, (bN i : V) = a i • bV (Fin.castLE hno i) := by
    intro i
    have h := hsnf i
    rw [← hbV (Fin.castLE hno i)] at h
    exact h
  -- The Smith coefficients are non-zero.
  have ha_ne : ∀ i : Fin n, a i ≠ 0 := by
    intro i
    have hbne : (bN i : V) ≠ 0 :=
      fun h => (LinearIndependent.ne_zero i bN.linearIndependent) (Subtype.ext h)
    have hne : a i • bV (Fin.castLE hno i) ≠ 0 := by rw [← hsnf' i]; exact hbne
    exact (smul_ne_zero_iff.mp hne).1
  -- Purity kills the coefficients: the adapted part of the `V`-basis lies in `W`.
  have hmem : ∀ i : Fin n, bV (Fin.castLE hno i) ∈ W := by
    intro i
    refine hpure (a i) (bV (Fin.castLE hno i)) (ha_ne i) ?_
    rw [← hsnf' i]
    exact (bN i).2
  -- The adapted part consists of `(-1)`-eigenvectors.
  have heig : ∀ i : Fin n, t (bV (Fin.castLE hno i)) = -bV (Fin.castLE hno i) := by
    intro i
    have h := hmem i
    rw [hW, LinearMap.mem_ker] at h
    have h2 : t (bV (Fin.castLE hno i)) + bV (Fin.castLE hno i) = 0 := by
      simpa only [LinearMap.add_apply, LinearMap.id_apply] using h
    exact eq_neg_iff_add_eq_zero.mpr h2
  -- The `W`-basis spans `W` inside `V`.
  have hspanN : Submodule.span ℤ (Set.range fun i : Fin n => ((bN i : W) : V)) = W :=
    (Submodule.span_range_subtype_eq_top_iff (p := W) (s := fun i => ((bN i : W) : V))
      (fun i => (bN i).2)).mp bN.span_eq
  -- The adapted part of `bV` spans exactly `W`.
  have hspan_eq :
      Submodule.span ℤ (Set.range fun i : Fin n => bV (Fin.castLE hno i)) = W := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact hmem i
    · rw [← hspanN, Submodule.span_le]
      rintro x ⟨i, rfl⟩
      change (bN i : V) ∈ Submodule.span ℤ (Set.range fun j : Fin n => bV (Fin.castLE hno j))
      rw [hsnf' i]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsum : n + (o - n) = o := Nat.add_sub_cancel' hno
  let e : Fin n ⊕ Fin (o - n) ≃ Fin o := finSumFinEquiv.trans (finCongr hsum)
  have hB : ∀ i : Fin n, (bV.reindex e.symm) (Sum.inl i) = bV (Fin.castLE hno i) := by
    intro i
    rw [Module.Basis.reindex_apply, Equiv.symm_symm]
    congr 1
  refine ⟨n, o - n, bV.reindex e.symm, ?_, ?_⟩
  · intro i
    rw [hB i]
    exact heig i
  · have hr : (Set.range fun i : Fin n => (bV.reindex e.symm) (Sum.inl i))
        = Set.range fun i : Fin n => bV (Fin.castLE hno i) := by
      congr 1
      funext i
      exact hB i
    rw [hr]
    exact hspan_eq

end Work.SSGRoute.ExtChain
