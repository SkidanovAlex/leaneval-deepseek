import Mathlib
import Submission.NK.Reconstruct.Transport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

/-- **Normality transports through base-field-mapping isomorphisms.**  If `L / K₂` is a finite
normal extension and `σ : K₂' ≃+* K₁'` maps the embedded copy of `K₂` onto the embedded copy of
`K₁`, then the transported level `σ(L) ⊆ K₁'` is normal over `K₁`.

The proof conjugates the `K₁`-algebra endomorphisms of `K₁'` into `K₂`-algebra endomorphisms of
`K₂'` via `σ` (`Submission.NeukirchUchida.conj`); the characterisation of normality by stability
under endomorphisms (`IntermediateField.normal_iff_forall_map_le'`) then transports the stability
of `L` to stability of `σ(L)`. -/
theorem normal_sigmaLevel {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁']
    [IsSepClosure K₂ K₂'] (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (L : IntermediateField K₂ K₂') [FiniteDimensional K₂ L] [Normal K₂ L] :
    Normal K₁ (NK.Reconstruct.sigmaLevel σ hσ L) := by
  rw [IntermediateField.normal_iff_forall_map_le' (F := K₁) (L := K₁')
        (K := NK.Reconstruct.sigmaLevel σ hσ L)]
  intro s x hx
  rw [IntermediateField.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [NK.Reconstruct.mem_sigmaLevel] at hy ⊢
  have hs' : σ.symm ((s : K₁' →ₐ[K₁] K₁') y) =
      (Submission.NeukirchUchida.conj hσ s : K₂' →ₐ[K₂] K₂') (σ.symm y) := by
    simp [Submission.NeukirchUchida.conj_apply]
  rw [hs']
  have hL : L.map (Submission.NeukirchUchida.conj hσ s : K₂' →ₐ[K₂] K₂') ≤ L :=
    (IntermediateField.normal_iff_forall_map_le' (F := K₂) (L := K₂') (K := L)).mp
      (inferInstance : Normal K₂ L) (Submission.NeukirchUchida.conj hσ s)
  refine hL ?_
  rw [IntermediateField.mem_map]
  exact ⟨σ.symm y, hy, rfl⟩

end NK.Reconstruct
