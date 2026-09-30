/-
# `BridgeSquare/hsurj_of_cuspPairSurj.lean` — the surjectivity transfer `(c)`

This file discharges the first of the two residual hypotheses of the bridge: given

* the identifications `eM k : ModelM k ≅ mhatLES.H (k,0)` and `eN k : ModelN k ≅ mhatLES.H (k,1)`
  of the two first slots of the Mayer–Vietoris sequence with the free models of `Work.HomologyMV`,
* and the surjectivity of the **cusp pair** `F_k = cuspPair k` in the three degrees `k = 1, 2, 3`
  in which the models are non-trivial,

the Mayer–Vietoris differential `mhatLES.d (k,0) : H_k(A ∩ B) → H_k(A) ⊞ H_k(B)` is surjective in
every degree `k ≥ 1`.

The argument has two halves.

* **Low degrees `k = 1, 2, 3`.**  By `mhatLES_d_zero` the differential is the Mayer–Vietoris map
  `mvFhat k` up to the `eqToHom`s of the identifications of its source and target; and by
  `mvFhat_conj_cuspPair` the map `mvFhat k` is conjugate to the cusp pair `F_k`.  Since
  conjugation by isomorphisms preserves surjectivity, `F_k` surjective gives `mvFhat k` surjective.
* **High degrees `k ≥ 4`.**  There `rankM k = rankN k = 0`, so both `ModelM k` and `ModelN k` are
  the zero module; through `eN k` the target `mhatLES.H (k,1)` of the differential is a
  subsingleton, so the differential is surjective for trivial reasons.

Nothing else about the space enters.
-/
import Mathlib
import Submission.Work.BridgeSquare.Data
import Submission.Work.BridgeSquare.mvFhat_conj_cuspPair

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.BridgeSquare

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## §1  Three elementary lemmas on `Function.Surjective` of morphisms of `ℤ`-modules -/

/-- A morphism of `ℤ`-modules whose target is a subsingleton is surjective. -/
lemma surjective_of_subsingleton_codomain {M N : ModuleCat ℤ} [Subsingleton ↥N] (f : M ⟶ N) :
    Function.Surjective f.hom :=
  fun y => ⟨0, Subsingleton.elim (f.hom 0) y⟩

/-- If `f ≫ g` is surjective and `g` is injective, then `f` is surjective. -/
lemma surjective_of_comp_injective {M N P : ModuleCat ℤ} {f : M ⟶ N} {g : N ⟶ P}
    (hg : Function.Injective ⇑g.hom) (h : Function.Surjective ⇑(f ≫ g).hom) :
    Function.Surjective ⇑f.hom := by
  intro y
  obtain ⟨x, hx⟩ := h (g.hom y)
  refine ⟨x, hg ?_⟩
  rw [ModuleCat.comp_apply] at hx
  exact hx

/-- Surjectivity is stable under bracketing a morphism with isomorphisms. -/
lemma surjective_comp_of_iso {M N P Q : ModuleCat ℤ} (e₁ : M ≅ N) (f : N ⟶ P) (e₂ : P ≅ Q)
    (hf : Function.Surjective ⇑f.hom) : Function.Surjective ⇑(e₁.hom ≫ f ≫ e₂.hom).hom := by
  have h₁ : Function.Surjective ⇑e₁.hom := Work.Final.function_surjective_of_iso e₁
  have h₂ : Function.Surjective ⇑e₂.hom := Work.Final.function_surjective_of_iso e₂
  have hfun : ⇑(e₁.hom ≫ f ≫ e₂.hom).hom = ⇑e₂.hom ∘ (⇑f.hom ∘ ⇑e₁.hom) := by
    funext x
    simp only [ModuleCat.comp_apply, Function.comp_apply]
  rw [hfun]
  exact h₂.comp (hf.comp h₁)

/-- A `ℤ`-module isomorphic to the zero free module `freeMod 0` is a subsingleton. -/
lemma subsingleton_of_iso_freeMod_zero {M : ModuleCat ℤ} (e : Work.HomologyMV.freeMod 0 ≅ M) :
    Subsingleton ↥M := by
  haveI : Subsingleton ↥(Work.HomologyMV.freeMod 0) :=
    ModuleCat.isZero_iff_subsingleton.mp Work.HomologyMV.isZero_freeMod_zero
  exact Function.Surjective.subsingleton (Work.Final.function_surjective_of_iso e)

/-! ## §2  The transfer -/

theorem hsurj_of_cuspPairSurj
    (eM : ∀ k : ℤ, Nonempty (Work.HomologyMV.ModelM k ≅ Work.HomologyIso.mhatLES.H (k, 0)))
    (eN : ∀ k : ℤ, Nonempty (Work.HomologyMV.ModelN k ≅ Work.HomologyIso.mhatLES.H (k, 1)))
    (hF : ∀ k : ℕ, 1 ≤ k → k ≤ 3 →
      Function.Surjective (Work.BridgeSquare.cuspPair (rt := Work.RTOwed.rtData) k).hom) :
    ∀ k : ℤ, 1 ≤ k → Function.Surjective (Work.HomologyIso.mhatLES.d (k, 0)).hom := by
  intro k hk1
  have _ := eM k
  by_cases hk3 : k ≤ 3
  · -- The low degrees `k = 1, 2, 3`: conjugation with the cusp pair.
    have hk0 : (0 : ℤ) ≤ k := by omega
    have hkn1 : 1 ≤ k.toNat := by omega
    have hkn3 : k.toNat ≤ 3 := by omega
    -- the cusp pair is surjective in this degree
    have hcusp : Function.Surjective
        (Work.BridgeSquare.cuspPair (rt := Work.RTOwed.rtData) k.toNat).hom :=
      hF k.toNat hkn1 hkn3
    -- `mvFhat k` is conjugate to the cusp pair
    obtain ⟨α, β, hβ⟩ :=
      Work.BridgeSquare.mvFhat_conj_cuspPair (rt := Work.RTOwed.rtData) k.toNat
    have hα : Function.Surjective ⇑α.hom := Work.Final.function_surjective_of_iso α
    have hβinj : Function.Injective ⇑β.hom := Work.Final.function_injective_of_iso β
    have hmvF : Function.Surjective
        (Work.HomologyIso.mvFhat (rt := Work.RTOwed.rtData) k.toNat).hom := by
      refine surjective_of_comp_injective hβinj ?_
      rw [hβ]
      have hfun : ⇑(α.hom ≫
            Work.BridgeSquare.cuspPair (rt := Work.RTOwed.rtData) k.toNat).hom
          = ⇑(Work.BridgeSquare.cuspPair (rt := Work.RTOwed.rtData) k.toNat).hom ∘ ⇑α.hom := by
        funext x
        simp only [ModuleCat.comp_apply, Function.comp_apply]
      rw [hfun]
      exact hcusp.comp hα
    -- the differential is `mvFhat` bracketed by the `eqToHom`s of the two slots
    rw [Work.HomologyIso.mhatLES_d_zero (rt := Work.RTOwed.rtData) k hk0]
    exact surjective_comp_of_iso
      (eqToIso (Work.HomologyIso.mhatLES_H_zero (rt := Work.RTOwed.rtData) k hk0))
      (Work.HomologyIso.mvFhat (rt := Work.RTOwed.rtData) k.toNat)
      (eqToIso (Work.HomologyIso.mhatLES_H_one (rt := Work.RTOwed.rtData) k hk0)).symm
      hmvF
  · -- The high degrees `k ≥ 4`: both models vanish.
    have hk4' : 4 ≤ k := by omega
    have hN0 : Work.HomologyMV.rankN k = 0 :=
      Work.HomologyMV.rankN_eq_zero k (by omega) (by omega) (by omega) (by omega)
    obtain ⟨e⟩ := eN k
    haveI : Subsingleton ↥(Work.HomologyMV.ModelN k) := by
      have hmod : Work.HomologyMV.ModelN k = Work.HomologyMV.freeMod 0 := by
        unfold Work.HomologyMV.ModelN
        rw [hN0]
      rw [hmod]
      exact ModuleCat.isZero_iff_subsingleton.mp Work.HomologyMV.isZero_freeMod_zero
    have hsub : Subsingleton ↥(Work.HomologyIso.mhatLES.H (k, 1)) :=
      Function.Surjective.subsingleton (Work.Final.function_surjective_of_iso e)
    haveI : Subsingleton ↥(Work.HomologyIso.mhatLES.H (Work.HomologyMV.mvSucc (k, 0))) := hsub
    exact surjective_of_subsingleton_codomain (Work.HomologyIso.mhatLES.d (k, 0))

end

end Work.BridgeSquare
