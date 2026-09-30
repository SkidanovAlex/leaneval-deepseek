/-
# `BridgeSquare/hker_of_cuspPairSurj.lean` — the kernel of the first Mayer–Vietoris map

This file proves `Work.BridgeSquare.hker_of_cuspPairSurj`: **surjectivity of the cusp pair
`F_k = cuspPair k` in degrees `1, 2, 3`, together with the (merely existential) identifications
`eM`, `eN` of the two first Mayer–Vietoris slots with the free models, determines the kernel of the
first Mayer–Vietoris map `L.d (k, 0)` in every degree `k ≥ 0`**: it is `ℤ` in degree `3` and `0` in
every other degree `k ≥ 0`, i.e. exactly `Work.HomologyMV.kerModel k`.

## The mechanism

* **§1–§2, the kernel transfer.**  By `Work.HomologyIso.mhatLES_d_zero` the map `L.d (k,0)` is
  `mvFhat k.toNat` up to the `eqToHom`s that transport the library terms `HInter`, `HBiprod` to the
  terms of the sequence, and by `Work.BridgeSquare.mvFhat_conj_cuspPair` the Mayer–Vietoris map
  `mvFhat k` is conjugate to the cusp pair `cuspPair k` by the explicit isomorphisms of the cusp
  picture.  Conjugating by isomorphisms changes the kernel only up to linear equivalence
  (`kerCompIsoLeft`, `kerCompIsoRight`), so `ker (L.d (k,0)) ≃ ker (cuspPair k.toNat)`.
* **§3, the rank bookkeeping.**  The hypotheses `eM k`, `eN k` give the ranks of the source and the
  target of `cuspPair k.toNat` (`exists_rankM`, `exists_rankN`): the source is `H_k(A ∩ B)`, which
  the cusp picture identifies with the source `H_k(⊔_v ∂[-1,1]² × T²_v)` of the cusp pair, and the
  target is the biproduct `H_k(M̄) ⊞ H_k(⊔_v T²_v)`.
* **§4–§5, the cases.**
  * `k = 0`: `cuspPair 0` is injective — `Work.BridgeSquare.cuspPair_injective_zero`, whose two
    inputs are the rank of `H_0(⊔_v ∂[-1,1]² × T²_v)` (from `eM 0` and `isoInter`) and the rank of
    `H_0(⊔_v T²_v)` (from the path connectedness of the five tori, `eTopZero`).  The kernel is
    trivial.
  * `k = 1, 2`: `cuspPair k` is surjective (`hF`) between free modules of rank `15 = 15`, hence
    injective (Hopfian: `injective_of_surjective_of_rank`), so the kernel is trivial again.
  * `k = 3`: `cuspPair 3` is surjective (`hF`) from rank `5` onto rank `4`, so its kernel is `ℤ`
    (`ker_equiv_int_of_surjective`).
  * `k ≥ 4`: the source of `cuspPair k` is the zero module (`rankM k = 0`), so the kernel is
    trivial, and `kerModel k = ℤ^0` there.

`kerModel k` is `ℤ^0` except in degree `3`, where it is `ℤ`; the trivial-module cases are handled by
`linEquivOfSubsingleton`, the degree-`3` case by `ker_equiv_int_of_surjective`.
-/
import Mathlib
import Submission.Work.BridgeSquare.Data
import Submission.Work.BridgeSquare.mvFhat_conj_cuspPair
import Submission.Work.BridgeSquare.cuspPair_injective_zero
import Submission.Work.BridgeSquare.injective_of_surjective_of_rank
import Submission.Work.BridgeSquare.ker_equiv_int_of_surjective
import Submission.Work.BridgeSquare.pathConnected_torus_concrete

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.Topology CategoryTheory CategoryTheory.Limits

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  Kernels under composition with isomorphisms

Composing a linear map with an isomorphism, on either side, does not change its kernel up to linear
equivalence.  These two lemmas are the only algebraic input of the kernel transfer of §2. -/

/-- **The kernel of `e ≫ f` is the kernel of `f`**, for an isomorphism `e`. -/
def kerCompIsoLeft {A A' B : ModuleCat ℤ} (e : A ≅ A') (f : A' ⟶ B) :
    (e.hom ≫ f).hom.ker ≃ₗ[ℤ] f.hom.ker where
  toFun x := ⟨e.hom x.1, x.2⟩
  invFun y := ⟨e.inv.hom y.1, by
    have hy : f.hom y.1 = 0 := y.2
    change f.hom (e.hom (e.inv.hom y.1)) = 0
    rw [show e.hom (e.inv.hom y.1) = y.1 from ConcreteCategory.congr_hom e.inv_hom_id y.1, hy]⟩
  left_inv x := by
    apply Subtype.ext
    exact ConcreteCategory.congr_hom e.hom_inv_id x.1
  right_inv y := by
    apply Subtype.ext
    exact ConcreteCategory.congr_hom e.inv_hom_id y.1
  map_add' x y := by
    apply Subtype.ext
    simp [map_add]
  map_smul' c x := by
    apply Subtype.ext
    simp

/-- **The kernel of `f ≫ e` is the kernel of `f`**, for an isomorphism `e`. -/
def kerCompIsoRight {A B B' : ModuleCat ℤ} (f : A ⟶ B) (e : B ≅ B') :
    (f ≫ e.hom).hom.ker ≃ₗ[ℤ] f.hom.ker := by
  have h : (f ≫ e.hom).hom.ker = f.hom.ker := by
    ext x
    simp only [LinearMap.mem_ker, ModuleCat.comp_apply]
    constructor
    · intro hx
      exact e.toLinearEquiv.injective (by simpa using hx)
    · intro hx
      rw [hx, map_zero]
  exact LinearEquiv.ofEq _ _ h

/-- A kernel is a subsingleton as soon as the map is injective. -/
lemma subsingleton_ker_of_injective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (h : Function.Injective f) :
    Subsingleton ↥f.ker :=
  ⟨fun a b => Subtype.ext (h (by rw [a.2, b.2]))⟩

/-- A surjective map between free modules of the same finite rank has trivial kernel (the Hopfian
property of finite free `ℤ`-modules, `injective_of_surjective_of_rank`). -/
lemma subsingleton_ker_of_surj_of_rank {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] {n : ℕ} (eM : M ≃ₗ[ℤ] (Fin n → ℤ))
    (eN : N ≃ₗ[ℤ] (Fin n → ℤ)) (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) :
    Subsingleton ↥f.ker :=
  subsingleton_ker_of_injective f (injective_of_surjective_of_rank eM eN f hf)

/-- `LinearEquiv.ofSubsingleton` with the two `Subsingleton` hypotheses passed explicitly, so that
the equivalence is built in the ambient instance normalisation of the goal. -/
def linEquivOfSubsingleton (M N : Type*) [AddCommMonoid M] [Module ℤ M] [AddCommMonoid N]
    [Module ℤ N] (hM : Subsingleton M) (hN : Subsingleton N) : M ≃ₗ[ℤ] N :=
  @LinearEquiv.ofSubsingleton ℤ M N _ _ _ _ _ hM hN

/-! ## §2  The kernel of the first Mayer–Vietoris map is the kernel of the cusp pair -/

/-- **The kernel of `L.d (k,0)` is the kernel of `mvFhat k.toNat`**: the map of the sequence is the
library Mayer–Vietoris map `mvFhat` conjugated by the `eqToHom`s that transport the library terms
`HInter`, `HBiprod` to the terms of the sequence (`Work.HomologyIso.mhatLES_d_zero`). -/
lemma ker_d_zero_mvFhat (k : ℤ) (hk : 0 ≤ k) :
    Nonempty (((Work.HomologyIso.mhatLES (rt := Work.RTOwed.rtData)).d (k, 0)).hom.ker ≃ₗ[ℤ]
      (Work.HomologyIso.mvFhat (rt := Work.RTOwed.rtData) k.toNat).hom.ker) := by
  rw [Work.HomologyIso.mhatLES_d_zero (rt := Work.RTOwed.rtData) k hk]
  exact ⟨(kerCompIsoLeft
        (eqToIso (Work.HomologyIso.mhatLES_H_zero (rt := Work.RTOwed.rtData) k hk))
        (Work.HomologyIso.mvFhat (rt := Work.RTOwed.rtData) k.toNat ≫
          eqToHom (Work.HomologyIso.mhatLES_H_one (rt := Work.RTOwed.rtData) k hk).symm)).trans
    (kerCompIsoRight (Work.HomologyIso.mvFhat (rt := Work.RTOwed.rtData) k.toNat)
      ((eqToIso (Work.HomologyIso.mhatLES_H_one (rt := Work.RTOwed.rtData) k hk)).symm))⟩

/-- **The kernel of `mvFhat n` is the kernel of the cusp pair in degree `n`**: the conjugation
`mvFhat n ≫ β = α ≫ cuspPair n` of `Work.BridgeSquare.mvFhat_conj_cuspPair`, read on kernels. -/
lemma ker_mvFhat_cuspPair (n : ℕ) :
    Nonempty (((Work.HomologyIso.mvFhat (rt := Work.RTOwed.rtData) n).hom.ker ≃ₗ[ℤ]
      (cuspPair (rt := Work.RTOwed.rtData) n).hom.ker)) := by
  obtain ⟨α, β, hαβ⟩ := mvFhat_conj_cuspPair (rt := Work.RTOwed.rtData) n
  exact ⟨(kerCompIsoRight (Work.HomologyIso.mvFhat (rt := Work.RTOwed.rtData) n) β).symm.trans
    (by rw [hαβ]; exact kerCompIsoLeft α (cuspPair (rt := Work.RTOwed.rtData) n))⟩

/-- **The kernel of `L.d (k,0)` is the kernel of the cusp pair `cuspPair k.toNat`**, for `k ≥ 0`. -/
lemma ker_d_zero_cuspPair (k : ℤ) (hk : 0 ≤ k) :
    Nonempty (((Work.HomologyIso.mhatLES (rt := Work.RTOwed.rtData)).d (k, 0)).hom.ker ≃ₗ[ℤ]
      (cuspPair (rt := Work.RTOwed.rtData) k.toNat).hom.ker) := by
  obtain ⟨e1⟩ := ker_d_zero_mvFhat k hk
  obtain ⟨e2⟩ := ker_mvFhat_cuspPair k.toNat
  exact ⟨e1.trans e2⟩

/-- The same statement, with the degree given as a natural number (so that the types of the small
degrees can be used in their literal form). -/
lemma ker_d_zero_cuspPair_nat (n : ℕ) :
    Nonempty (((Work.HomologyIso.mhatLES (rt := Work.RTOwed.rtData)).d ((n : ℤ), 0)).hom.ker ≃ₗ[ℤ]
      (cuspPair (rt := Work.RTOwed.rtData) n).hom.ker) := by
  obtain ⟨e⟩ := ker_d_zero_cuspPair (n : ℤ) (Int.natCast_nonneg n)
  rw [Int.toNat_natCast] at e
  exact ⟨e⟩

/-! ## §3  The ranks of the source and the target of the cusp pair

The two slots of the Mayer–Vietoris sequence are the free models `ModelM k`, `ModelN k` by the
hypotheses `eM`, `eN`, and the cusp picture identifies them with the source and the target of
`cuspPair` (`isoInter` on the source; the additivity of homology over the binary biproduct followed
by `isoA` and `isoB` on the target).  This is the rank information used in §5. -/

/-- **The rank of the source of the cusp pair** in degree `k ≥ 0`:
`H_{k.toNat}(A ∩ B) ≃ ℤ^{rankM k}`, in the identification supplied by `eM`. -/
lemma exists_rankM (eM : ∀ k : ℤ, Nonempty (Work.HomologyMV.ModelM k ≅
    (Work.HomologyIso.mhatLES (rt := Work.RTOwed.rtData)).H (k, 0)))
    (k : ℤ) (hk : 0 ≤ k) :
    Nonempty (↥(intHomology k.toNat (Cop (rt := Work.RTOwed.rtData))) ≃ₗ[ℤ]
      (Fin (Work.HomologyMV.rankM k) → ℤ)) := by
  obtain ⟨e⟩ := eM k
  obtain ⟨α, β, h⟩ := mvFhat_conj_cuspPair (rt := Work.RTOwed.rtData) k.toNat
  exact ⟨(e ≪≫ eqToIso (Work.HomologyIso.mhatLES_H_zero (rt := Work.RTOwed.rtData) k hk)
    ≪≫ α).symm.toLinearEquiv⟩

/-- **The rank of the target of the cusp pair** in degree `k ≥ 0`:
`H_{k.toNat}(M̄) ⊞ H_{k.toNat}(⊔_v T²_v) ≃ ℤ^{rankN k}`, in the identification supplied by `eN`. -/
lemma exists_rankN (eN : ∀ k : ℤ, Nonempty (Work.HomologyMV.ModelN k ≅
    (Work.HomologyIso.mhatLES (rt := Work.RTOwed.rtData)).H (k, 1)))
    (k : ℤ) (hk : 0 ≤ k) :
    Nonempty (↥(intHomology k.toNat (Mop (rt := Work.RTOwed.rtData)) ⊞
        intHomology k.toNat (Top (rt := Work.RTOwed.rtData))) ≃ₗ[ℤ]
      (Fin (Work.HomologyMV.rankN k) → ℤ)) := by
  obtain ⟨e⟩ := eN k
  obtain ⟨α, β, h⟩ := mvFhat_conj_cuspPair (rt := Work.RTOwed.rtData) k.toNat
  exact ⟨(e ≪≫ eqToIso (Work.HomologyIso.mhatLES_H_one (rt := Work.RTOwed.rtData) k hk)
    ≪≫ β).symm.toLinearEquiv⟩

/-- The rank of the source of the cusp pair, degree given as a natural number. -/
lemma exists_rankM_nat (eM : ∀ k : ℤ, Nonempty (Work.HomologyMV.ModelM k ≅
    (Work.HomologyIso.mhatLES (rt := Work.RTOwed.rtData)).H (k, 0))) (n : ℕ) :
    Nonempty (↥(intHomology n (Cop (rt := Work.RTOwed.rtData))) ≃ₗ[ℤ]
      (Fin (Work.HomologyMV.rankM (n : ℤ)) → ℤ)) := by
  obtain ⟨e⟩ := exists_rankM eM (n : ℤ) (Int.natCast_nonneg n)
  rw [Int.toNat_natCast] at e
  exact ⟨e⟩

/-- The rank of the target of the cusp pair, degree given as a natural number. -/
lemma exists_rankN_nat (eN : ∀ k : ℤ, Nonempty (Work.HomologyMV.ModelN k ≅
    (Work.HomologyIso.mhatLES (rt := Work.RTOwed.rtData)).H (k, 1))) (n : ℕ) :
    Nonempty (↥(intHomology n (Mop (rt := Work.RTOwed.rtData)) ⊞
        intHomology n (Top (rt := Work.RTOwed.rtData))) ≃ₗ[ℤ]
      (Fin (Work.HomologyMV.rankN (n : ℤ)) → ℤ)) := by
  obtain ⟨e⟩ := exists_rankN eN (n : ℤ) (Int.natCast_nonneg n)
  rw [Int.toNat_natCast] at e
  exact ⟨e⟩

/-! ## §4  The degree-`0` rank of the cusp tori

To know that `H_0(π)` — hence `cuspPair 0` — is injective, one needs the rank of `H_0(⊔_v T²_v)`:
the five filling tori are path connected (`pathConnected_torus_concrete`), so additivity over the
finite disjoint union (`intHomologySigma`) identifies `H_0(⊔_v T²_v)` with `(ℤ^1)^5 = ℤ^5`
(`biproductIsoPi`). -/

/-- **`H_0(⊔_v T²_v) ≃ ℤ^5`.** -/
def eTopZero : ↥(intHomology 0 (Top (rt := Work.RTOwed.rtData))) ≃ₗ[ℤ] (Fin 5 → ℤ) := by
  haveI (v : Fin 5) : PathConnectedSpace ((Work.RTOwed.rtData).core.Torus v) :=
    pathConnected_torus_concrete v
  exact ((intHomologySigma 0 (fun v : Fin 5 => (Work.RTOwed.rtData).core.Torus v)) ≪≫
    (biproduct.mapIso (fun v : Fin 5 =>
      (Work.Homology.singHomologyZeroIsoOfPathConnected Work.Homology.ZMod
        (TopCat.of ((Work.RTOwed.rtData).core.Torus v))))) ≪≫
    (ModuleCat.biproductIsoPi (fun _ : Fin 5 => Work.Homology.ZMod))).toLinearEquiv

/-! ## §5  The kernel certificate -/

theorem hker_of_cuspPairSurj
    (eM : ∀ k : ℤ, Nonempty (Work.HomologyMV.ModelM k ≅ Work.HomologyIso.mhatLES.H (k, 0)))
    (eN : ∀ k : ℤ, Nonempty (Work.HomologyMV.ModelN k ≅ Work.HomologyIso.mhatLES.H (k, 1)))
    (hF : ∀ k : ℕ, 1 ≤ k → k ≤ 3 →
      Function.Surjective (Work.BridgeSquare.cuspPair (rt := Work.RTOwed.rtData) k).hom) :
    ∀ k : ℤ, 0 ≤ k →
      Nonempty ((Work.HomologyIso.mhatLES.d (k, 0)).hom.ker ≃ₗ[ℤ]
        ↥(Work.HomologyMV.kerModel k)) := by
  intro k hk
  rcases lt_or_ge k 4 with hk4 | hk4
  · -- the low degrees `0, 1, 2, 3`
    have hlow : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hlow with rfl | rfl | rfl | rfl
    · -- degree `0`: the cusp pair is injective
      obtain ⟨e0⟩ := ker_d_zero_cuspPair_nat 0
      obtain ⟨eC⟩ := exists_rankM_nat eM 0
      have hinj : Function.Injective (cuspPair (rt := Work.RTOwed.rtData) 0).hom :=
        cuspPair_injective_zero (rt := Work.RTOwed.rtData) eC eTopZero
      have hsub : Subsingleton ↥((cuspPair (rt := Work.RTOwed.rtData) 0).hom.ker) :=
        subsingleton_ker_of_injective _ hinj
      have hsub2 : Subsingleton ↥(Work.HomologyMV.kerModel 0) := by
        rw [Work.HomologyMV.kerModel_eq_zero 0 (by norm_num)]
        exact Work.HomologyMV.subsingleton_freeMod_zero
      exact ⟨e0.trans (linEquivOfSubsingleton _ _ hsub hsub2)⟩
    · -- degree `1`: surjective between free modules of rank `15`
      obtain ⟨e0⟩ := ker_d_zero_cuspPair_nat 1
      obtain ⟨eC⟩ := exists_rankM_nat eM 1
      obtain ⟨eT⟩ := exists_rankN_nat eN 1
      have hsub : Subsingleton ↥((cuspPair (rt := Work.RTOwed.rtData) 1).hom.ker) :=
        subsingleton_ker_of_surj_of_rank eC eT _
          (hF 1 (by norm_num) (by norm_num))
      have hsub2 : Subsingleton ↥(Work.HomologyMV.kerModel 1) := by
        rw [Work.HomologyMV.kerModel_eq_zero 1 (by norm_num)]
        exact Work.HomologyMV.subsingleton_freeMod_zero
      exact ⟨e0.trans (linEquivOfSubsingleton _ _ hsub hsub2)⟩
    · -- degree `2`: surjective between free modules of rank `15`
      obtain ⟨e0⟩ := ker_d_zero_cuspPair_nat 2
      obtain ⟨eC⟩ := exists_rankM_nat eM 2
      obtain ⟨eT⟩ := exists_rankN_nat eN 2
      have hsub : Subsingleton ↥((cuspPair (rt := Work.RTOwed.rtData) 2).hom.ker) :=
        subsingleton_ker_of_surj_of_rank eC eT _
          (hF 2 (by norm_num) (by norm_num))
      have hsub2 : Subsingleton ↥(Work.HomologyMV.kerModel 2) := by
        rw [Work.HomologyMV.kerModel_eq_zero 2 (by norm_num)]
        exact Work.HomologyMV.subsingleton_freeMod_zero
      exact ⟨e0.trans (linEquivOfSubsingleton _ _ hsub hsub2)⟩
    · -- degree `3`: surjective from rank `5` onto rank `4`, so the kernel is `ℤ`
      obtain ⟨e0⟩ := ker_d_zero_cuspPair_nat 3
      obtain ⟨eC⟩ := exists_rankM_nat eM 3
      obtain ⟨eT⟩ := exists_rankN_nat eN 3
      obtain ⟨e3⟩ := ker_equiv_int_of_surjective eC eT
        ((cuspPair (rt := Work.RTOwed.rtData) 3).hom)
        (hF 3 (by norm_num) (by norm_num))
      -- `e3` is built with the generic `ℤ`-module structures; transport it to the ambient ones
      have h1 : (AddCommGroup.toIntModule
            ↥((cuspPair (rt := Work.RTOwed.rtData) 3).hom.ker)) =
          (Submodule.module ((cuspPair (rt := Work.RTOwed.rtData) 3).hom.ker) :
            Module ℤ ↥((cuspPair (rt := Work.RTOwed.rtData) 3).hom.ker)) :=
        Subsingleton.elim _ _
      have h2 : (Semiring.toModule : Module ℤ ↥(Work.HomologyMV.kerModel 3)) =
          (Work.HomologyMV.kerModel 3).isModule := Subsingleton.elim _ _
      exact ⟨e0.trans (h2 ▸ h1 ▸ e3)⟩
  · -- degrees `≥ 4`: the source of the cusp pair is the zero module
    obtain ⟨e0⟩ := ker_d_zero_cuspPair k hk
    obtain ⟨eC⟩ := exists_rankM eM k hk
    haveI hM : Subsingleton (Fin (Work.HomologyMV.rankM k) → ℤ) :=
      Work.HomologyMV.subsingleton_modelM_of_ge k hk4
    have hsub : Subsingleton ↥(intHomology k.toNat (Cop (rt := Work.RTOwed.rtData))) :=
      ⟨fun a b => eC.injective (Subsingleton.elim (eC a) (eC b))⟩
    have hsubK : Subsingleton ↥((cuspPair (rt := Work.RTOwed.rtData) k.toNat).hom.ker) := by
      haveI := hsub
      exact subsingleton_ker_of_injective _ (fun a b _ => Subsingleton.elim a b)
    have hsub2 : Subsingleton ↥(Work.HomologyMV.kerModel k) := by
      rw [Work.HomologyMV.kerModel_eq_zero k (by omega)]
      exact Work.HomologyMV.subsingleton_freeMod_zero
    exact ⟨e0.trans (linEquivOfSubsingleton _ _ hsubK hsub2)⟩

end

end Work.BridgeSquare
