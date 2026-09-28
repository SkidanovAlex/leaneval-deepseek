import Mathlib
import Submission.Work.Stems.RankOne.exists_sphMap_piMapN_injective
import Submission.Work.Stems.RankOneClauses

/-!
# `πₙ(Sⁿ) ≅ ℤ`: the sphere is a cyclic homotopy group

For `n ≥ 2` the Hurewicz map `πₙ(Sⁿ, x₀) → Hₙ(Sⁿ;ℤ)` is an isomorphism onto `Hₙ(Sⁿ;ℤ) ≅ ℤ`:

* it is injective — Hurewicz injectivity in the first non-vanishing degree
  (`Work.Serre.hurewiczMap_sphere_injective`), since `Sⁿ` is `(n-1)`-connected;
* it is surjective — Hurewicz surjectivity in the first non-vanishing degree
  (`Work.Stems.hurewiczMapN_surjective`), with the same connectivity
  (`Work.Stems.sphereConnectivity`).

Composing with a chosen identification `Hₙ(Sⁿ;ℤ) ≅ ℤ`
(`Work.Cohomology.sphereHomologyTop`) therefore gives a group isomorphism
`πₙ(Sⁿ, x₀) ≅ ℤ`.  A generator is the preimage of `1`; it has infinite order and every element of
`πₙ(Sⁿ, x₀)` is one of its integral powers.  No path-connectedness of the base point is needed:
both Hurewicz facts are available at an arbitrary base point `x₀`.
-/

namespace Work.Stems.RankOne

open CategoryTheory

noncomputable section

/-- The fork-neutral Hurewicz map and the Hurewicz map agree, with independently given proofs of
`1 ≤ n` (the `(by omega)` proofs inside the library statements differ from ours). -/
private theorem hurewiczMapN_eq_hurewiczMap' (n : ℕ) (h1 h2 : 1 ≤ n) {X : Type}
    [TopologicalSpace X] (x₀ : X) :
    Work.Stems.hurewiczMapN n h1 x₀ = Work.Stems.hurewiczMap n h2 x₀ := by
  rw [← Work.Stems.hurewiczMap_proof_congr n h1 h2 x₀]
  exact Work.Stems.hurewiczMapN_eq_hurewiczMap n h1 x₀

theorem sphere_pi_generator (n : ℕ) [Nonempty (Fin n)] (hn : 2 ≤ n) (s₀ : Work.Serre.Sph n) :
    ∃ γ₀ : HomotopyGroup (Fin n) (Work.Serre.Sph n) s₀,
      (∀ m : ℕ, 0 < m → γ₀ ^ m ≠ 1) ∧
      (∀ a : HomotopyGroup (Fin n) (Work.Serre.Sph n) s₀, ∃ k : ℤ, a = γ₀ ^ k) := by
  -- write `n = m + 1`; then `n ≥ 2` means `m ≥ 1`
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel (by omega)).symm⟩
  have hm : 1 ≤ m := by omega
  have h1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  -- `Sⁿ` is `(n-1)`-connected
  have hconn : ∀ i : ℕ, i < m + 1 →
      Subsingleton (HomotopyGroup (Fin i) (Work.Serre.Sph (m+1)) s₀) :=
    fun i hi => Work.Stems.sphereConnectivity (m + 1) i hi s₀
  -- the Hurewicz map `πₙ(Sⁿ,s₀) → Hₙ(Sⁿ;ℤ)` is surjective ...
  have hsurj : Function.Surjective (Work.Stems.hurewiczMap (m+1) h1 s₀) := by
    have h := Work.Stems.hurewiczMapN_surjective (m+1) (by omega : 2 ≤ m+1) s₀ hconn
    rw [hurewiczMapN_eq_hurewiczMap' (m+1) _ h1 s₀] at h
    exact h
  -- ... and injective.
  have hinj : Function.Injective (Work.Stems.hurewiczMap (m+1) h1 s₀) := by
    have h := Work.Serre.hurewiczMap_sphere_injective (m+1) (by omega : 2 ≤ m+1) s₀
    rw [← Work.Stems.hurewiczMap_proof_congr (m+1) _ h1 s₀] at h
    exact h
  -- the chosen identification `Hₙ(Sⁿ;ℤ) ≅ ℤ`
  obtain ⟨e⟩ := Work.Cohomology.sphereHomologyTop (m+1) h1
  have hinje : Function.Injective (ModuleCat.Hom.hom e.hom) :=
    (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  have hsurje : Function.Surjective (ModuleCat.Hom.hom e.hom) :=
    (ModuleCat.epi_iff_surjective e.hom).mp inferInstance
  -- the additive homomorphism `πₙ(Sⁿ,s₀) → ℤ` obtained from the Hurewicz map
  set G : Additive (HomotopyGroup (Fin (m+1)) (Work.Serre.Sph (m+1)) s₀) →+ ℤ :=
    (LinearMap.toAddMonoidHom (ModuleCat.Hom.hom e.hom)).comp (Work.Stems.hurewiczHom m s₀)
    with hGdef
  have hHom : Function.Bijective (Work.Stems.hurewiczHom m s₀) := by
    constructor
    · intro a b hab
      have hab' : Work.Stems.hurewiczMap (m+1) h1 s₀ (Additive.toMul a) =
          Work.Stems.hurewiczMap (m+1) h1 s₀ (Additive.toMul b) := by
        simpa [Work.Stems.hurewiczHom_apply] using hab
      exact Additive.toMul.injective (hinj hab')
    · intro y
      obtain ⟨a, ha⟩ := hsurj y
      exact ⟨Additive.ofMul a, by simpa [Work.Stems.hurewiczHom_apply] using ha⟩
  have hLin : Function.Bijective (LinearMap.toAddMonoidHom (ModuleCat.Hom.hom e.hom)) :=
    ⟨hinje, hsurje⟩
  have hG : Function.Bijective G := by
    rw [hGdef]
    exact hLin.comp hHom
  -- the resulting additive equivalence `πₙ(Sⁿ,s₀) ≅ ℤ`
  set eG : Additive (HomotopyGroup (Fin (m+1)) (Work.Serre.Sph (m+1)) s₀) ≃+ ℤ :=
    AddEquiv.ofBijective G hG with heGdef
  refine ⟨Additive.toMul (eG.symm (1 : ℤ)), ?_, ?_⟩
  · -- the generator has infinite order
    intro k hk hpow
    have h2 : eG (Additive.ofMul (Additive.toMul (eG.symm (1:ℤ)) ^ k)) = (k : ℤ) := by
      calc eG (Additive.ofMul (Additive.toMul (eG.symm (1:ℤ)) ^ k))
          = eG (Additive.ofMul (Additive.toMul (eG.symm (1:ℤ)) ^ (k : ℤ))) := by
            rw [zpow_natCast]
        _ = eG ((k : ℤ) • Additive.ofMul (Additive.toMul (eG.symm (1:ℤ)))) := by rw [ofMul_zpow]
        _ = (k : ℤ) • eG (Additive.ofMul (Additive.toMul (eG.symm (1:ℤ)))) := map_zsmul _ _ _
        _ = (k : ℤ) • (1 : ℤ) := by rw [ofMul_toMul, AddEquiv.apply_symm_apply]
        _ = (k : ℤ) := by simp
    have hzero : eG (Additive.ofMul (Additive.toMul (eG.symm (1:ℤ)) ^ k)) = 0 := by
      rw [hpow, ofMul_one, map_zero]
    have hk0 : (k : ℤ) = 0 := by rw [← h2, hzero]
    have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
    omega
  · -- every class is an integral power of the generator
    intro a
    refine ⟨G (Additive.ofMul a), ?_⟩
    have hk : eG.symm (G (Additive.ofMul a)) = Additive.ofMul a := by
      rw [show G (Additive.ofMul a) = eG (Additive.ofMul a) from rfl]
      exact eG.symm_apply_apply _
    have h2 : Additive.ofMul (Additive.toMul (eG.symm (1:ℤ)) ^ (G (Additive.ofMul a)))
        = eG.symm (G (Additive.ofMul a)) := by
      calc Additive.ofMul (Additive.toMul (eG.symm (1:ℤ)) ^ (G (Additive.ofMul a)))
          = (G (Additive.ofMul a)) • Additive.ofMul (Additive.toMul (eG.symm (1:ℤ))) :=
            ofMul_zpow _ _
        _ = (G (Additive.ofMul a)) • eG.symm (1:ℤ) := by rw [ofMul_toMul]
        _ = eG.symm ((G (Additive.ofMul a)) • (1:ℤ)) := (map_zsmul eG.symm _ _).symm
        _ = eG.symm (G (Additive.ofMul a)) := by simp
    exact (Additive.ofMul.injective (by rw [h2, hk])).symm

end

end Work.Stems.RankOne
