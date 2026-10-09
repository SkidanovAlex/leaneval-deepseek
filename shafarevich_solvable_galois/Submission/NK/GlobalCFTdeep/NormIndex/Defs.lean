/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.Norm.NormTransAux
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The vocabulary of the elementary proof of the finiteness of the norm index

For a finite extension `L / K` of number fields the quotient `C[K] ⧸ N_{L/K} C[L]` is finite.
The proof (no class field theory) exhibits a finite-index subgroup of `𝕀 K` contained in the
idèlic norm subgroup and contained in `Kˣ · 𝕀_{K,S}` for a finite set `S` of places.

This file contains the shared vocabulary:

* `NK.GlobalCFTdeep.constrainedE`: the idèles subject to a finite family of local conditions
  (`A v ≤ K_vˣ` for `v ∈ S`, local units outside `S`);
* `NK.GlobalCFTdeep.finiteIndex_sup_of_sup_eq_top`: the abstract group-theoretic step
  `⊤ = P ⊔ B`, `B ∩ E` finite index in `B` ⟹ `P ⊔ E` finite index in `G`;
* `NK.GlobalCFTdeep.localNormAt` (with its computation rule `localNormAt_spec`): the local norm
  `L_wˣ → K_vˣ` at a chosen place `w = g v` of `L` above `v`, regarded as a homomorphism — the
  bridge between the local norm groups and the idèlic norm formula at a single place.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-- **The idèles of `K` subject to a finite family of local conditions.**  For a finite set `S` of
places and subgroups `A v ≤ K_vˣ` (`v ∈ S`), this is the subgroup of `𝕀 K` consisting of the
idèles which lie in `A v` for `v ∈ S` and are local units outside `S`. -/
def constrainedE {K : Type} [Field K] [NumberField K] (S : Finset (Place K))
    (A : (v : S) → Subgroup ((Place.localField K v)ˣ)) : Subgroup (Idele K) where
  carrier := {x | (∀ v : S, (x : Idele K) v ∈ A v) ∧
    ∀ v : Place K, v ∉ S → x v ∈ Place.localUnits K v}
  one_mem' := ⟨fun v => Subgroup.one_mem _, fun v _ => Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨fun v => by rw [Idele.mul_apply]; exact Subgroup.mul_mem _ (hx1 v) (hy1 v),
      fun v hv => by rw [Idele.mul_apply]; exact Subgroup.mul_mem _ (hx2 v hv) (hy2 v hv)⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨fun v => by rw [Idele.inv_apply]; exact Subgroup.inv_mem _ (hx1 v),
      fun v hv => by rw [Idele.inv_apply]; exact Subgroup.inv_mem _ (hx2 v hv)⟩

@[simp] theorem mem_constrainedE {K : Type} [Field K] [NumberField K] {S : Finset (Place K)}
    {A : (v : S) → Subgroup ((Place.localField K v)ˣ)} {x : Idele K} :
    x ∈ constrainedE S A ↔ (∀ v : S, x v ∈ A v) ∧
      ∀ v : Place K, v ∉ S → x v ∈ Place.localUnits K v := Iff.rfl

/-- **The abstract group-theoretic step.**  If `P ⊔ B = ⊤` and `B ∩ E` has finite index in `B`,
then `P ⊔ E` has finite index in `G`: indeed `G ⧸ (P ⊔ B)` is a quotient of `B ⧸ (B ∩ E)`
because `G ⧸ (P ⊔ E) ≅ B ⧸ (B ∩ (P ⊔ E))` and `B ∩ E ≤ B ∩ (P ⊔ E)`. -/
theorem finiteIndex_sup_of_sup_eq_top {G : Type*} [CommGroup G] {P B E : Subgroup G}
    (hPB : P ⊔ B = ⊤) (hE : ((B ⊓ E).subgroupOf B).FiniteIndex) : (P ⊔ E).FiniteIndex := by
  have hle : (B ⊓ E).subgroupOf B ≤ (B ⊓ (P ⊔ E)).subgroupOf B := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hx.1, Subgroup.mem_sup_right hx.2⟩
  haveI := hE
  have hfin : ((B ⊓ (P ⊔ E)).subgroupOf B).FiniteIndex := Subgroup.finiteIndex_of_le hle
  let f : B →* G ⧸ (P ⊔ E) := (QuotientGroup.mk' (P ⊔ E)).comp B.subtype
  have hker : f.ker = (B ⊓ (P ⊔ E)).subgroupOf B := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hx : (x : G) ∈ P ⊔ E :=
        (QuotientGroup.eq_one_iff (N := P ⊔ E) (x : G)).mp (by simpa [f] using h)
      exact ⟨x.2, hx⟩
    · rintro ⟨-, hx⟩
      simp only [f, MonoidHom.comp_apply, Subgroup.subtype_apply]
      exact (QuotientGroup.eq_one_iff (N := P ⊔ E) (x : G)).mpr hx
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (P ⊔ E) y
    have hg : g ∈ P ⊔ B := by rw [hPB]; trivial
    rw [Subgroup.mem_sup] at hg
    obtain ⟨p, hp, b, hb, rfl⟩ := hg
    refine ⟨⟨b, hb⟩, ?_⟩
    show QuotientGroup.mk' (P ⊔ E) b = QuotientGroup.mk' (P ⊔ E) (p * b)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      show b⁻¹ * (p * b) = p from by rw [mul_comm p b, ← mul_assoc, inv_mul_cancel, one_mul]]
    exact Subgroup.mem_sup_left hp
  haveI : Finite (B ⧸ f.ker) := by
    rw [hker]
    exact (Nat.card_ne_zero.mp (Subgroup.finiteIndex_iff.mp hfin)).2
  exact Subgroup.FiniteIndex.mk (by
    rw [Subgroup.index_eq_card]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, Finite.of_surjective _
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj).surjective⟩)

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- **The local norm at a chosen place above `v`, as a homomorphism.**  For a choice `g` of a
place of `L` above each place `v` of `K`, the local norm `N_{L_{g v}/K_v}` is a homomorphism
`L_{g v}ˣ → K_vˣ` matching the idèlic norm formula at the single place `v`
(`localNormAt_spec`).  It is the identity on `L_{g v}ˣ` only in the degenerate case `L = K`. -/
theorem exists_normHom (g : Place K → Place L) (hg : ∀ v, Place.LiesOver (g v) v) (v : Place K) :
    ∃ Φ : (Place.localField L (g v))ˣ →* (Place.localField K v)ˣ,
      (∀ u, Idele.normIdeleFun K L
        (SecondInequality.KummerCase.singleIdele (g v) u) v = Φ u) := by
  rcases hg v with ⟨w, v', h1, h2, h3⟩ | ⟨q, Q, h1, h2, h3⟩
  · obtain rfl := h2
    haveI : w.LiesOver v' := h3
    rw [h1]
    refine ⟨Place.localNormInfinite w v', fun u => ?_⟩
    exact SecondInequality.KummerCase.normIdeleFun_singleIdele_ofInfinite v' w u
  · obtain rfl := h2
    rw [h1]
    refine ⟨Place.localNormFinite q Q h3, fun u => ?_⟩
    exact SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite Q q h3 u

/-- The local norm `N_{L_{g v}/K_v}`, chosen uniformly in `v`. -/
noncomputable def localNormAt (g : Place K → Place L) (hg : ∀ v, Place.LiesOver (g v) v) :
    ∀ v : Place K, (Place.localField L (g v))ˣ →* (Place.localField K v)ˣ :=
  fun v => Classical.choose (exists_normHom g hg v)

/-- **The computation rule of `localNormAt`**: at the single place `v`, the idèlic norm of the
idèle of `L` concentrated at `g v` with value `u` is the local norm of `u`. -/
theorem localNormAt_spec (g : Place K → Place L) (hg : ∀ v, Place.LiesOver (g v) v)
    (v : Place K) (u : (Place.localField L (g v))ˣ) :
    Idele.normIdeleFun K L (SecondInequality.KummerCase.singleIdele (g v) u) v =
      localNormAt g hg v u :=
  Classical.choose_spec (exists_normHom g hg v) u

end NK.GlobalCFTdeep
