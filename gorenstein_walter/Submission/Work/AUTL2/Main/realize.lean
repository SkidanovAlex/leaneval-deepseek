/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Work.AUTL2.Main.realize`

For `q = p ^ k`, `p` odd, `q ≥ 5`, every automorphism `α` of `PSL(2,q)` is realized by
conjugation with a permutation `π` of the projective line lying in `PΓL(2,F)`.

The proof is the geometric reconstruction of `α`:

* the root subgroups (`Upt x`, `Work.AUTL2.Aut.geometry`) are the subgroups of `pslImage F`
  of order `p ^ k`; each has a unique fixed point on `ℙ¹(F)`, and the map
  `x ↦ Upt x` is a bijection from `ℙ¹(F)` onto the set of these subgroups
  (`UXEquiv` below);
* an automorphism `β` of `pslImage F` permutes them, hence induces a permutation `π` of
  `ℙ¹(F)` (`piPerm`);
* the equivariance `Upt (γ • x) = β γ • Upt x` turns into `π * γ * π⁻¹ = β γ`, so `π`
  normalizes `pslImage F`, i.e. lies in `PΓL(2,F)`
  (`Work.AUTL2.Normalizer.le_pgammaL`).
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Mobius
import Submission.Work.AUTL2.Stabilizer
import Submission.Work.AUTL2.Normalizer.le_pgammaL
import Submission.Work.AUTL2.Normalizer.eq
import Submission.Work.AUTL2.Galois.decomposition
import Submission.Work.AUTL2.Aut.centralizer
import Submission.Work.AUTL2.Aut.pglHomInjective
import Submission.Work.AUTL2.Aut.geometry
import Submission.Work.AUTL2.A5.basic
import Submission.Work.AUTL2.A5.mat

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint Subgroup

set_option maxHeartbeats 1000000

namespace Work.AUTL2.Main

open Work.AUTL2
open Work.AUTL2.Aut

/-! ## Subgroup bookkeeping -/

/-- Membership in the conjugate `H.map (MulAut.conj δ)`. -/
theorem mem_map_conj_iff (F : Type*) [Field F] [DecidableEq F]
    (H : Subgroup (Equiv.Perm (P1 F))) (δ : Equiv.Perm (P1 F)) (g : Equiv.Perm (P1 F)) :
    g ∈ H.map (MulAut.conj δ) ↔ δ⁻¹ * g * δ ∈ H := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨t, ht, hteq⟩
    have : δ⁻¹ * g * δ = t := by
      rw [← hteq]
      show δ⁻¹ * MulAut.conj δ t * δ = t
      rw [MulAut.conj_apply]; group
    rw [this]; exact ht
  · intro hmem
    refine ⟨δ⁻¹ * g * δ, hmem, ?_⟩
    show MulAut.conj δ (δ⁻¹ * g * δ) = g
    rw [MulAut.conj_apply]; group

/-- Cardinality of a conjugate subgroup. -/
theorem card_map_conj (F : Type*) [Field F] [DecidableEq F]
    (H : Subgroup (Equiv.Perm (P1 F))) (δ : Equiv.Perm (P1 F)) :
    Nat.card (H.map (MulAut.conj δ : Equiv.Perm (P1 F) →* Equiv.Perm (P1 F))) =
      Nat.card H :=
  Subgroup.card_map_of_injective (f := (MulAut.conj δ : Equiv.Perm (P1 F) →* Equiv.Perm (P1 F)))
    (fun a b h => (MulAut.conj δ).injective h)

/-- Conjugating twice by `δ` and `δ⁻¹` gives back the subgroup. -/
theorem map_conj_mul_inv (F : Type*) [Field F] [DecidableEq F]
    (H : Subgroup (Equiv.Perm (P1 F))) (δ : Equiv.Perm (P1 F)) :
    ((H.map (MulAut.conj δ : Equiv.Perm (P1 F) →* Equiv.Perm (P1 F))).map
        (MulAut.conj δ⁻¹ : Equiv.Perm (P1 F) →* Equiv.Perm (P1 F))) = H := by
  rw [Subgroup.map_map]
  have hcomp : ((MulAut.conj δ⁻¹ : Equiv.Perm (P1 F) →* Equiv.Perm (P1 F)).comp
      (MulAut.conj δ : Equiv.Perm (P1 F) →* Equiv.Perm (P1 F))) =
      MonoidHom.id (Equiv.Perm (P1 F)) := by
    apply MonoidHom.ext
    intro z
    show MulAut.conj δ⁻¹ (MulAut.conj δ z) = z
    rw [MulAut.conj_apply, MulAut.conj_apply]
    simp only [inv_inv]
    group
  rw [hcomp, Subgroup.map_id]

/-- Conjugation by an element of `pslImage F` fixing `∞` preserves the translation subgroup:
the point stabilizer of `∞` lies in the normalizer of `U = {x ↦ x + b}`. -/
theorem mapConjTranslSub (F : Type*) [Field F] [DecidableEq F]
    (γ : Equiv.Perm (P1 F)) (hγ : γ ∈ pslImage F) (hfix : γ (∞ : P1 F) = ∞) :
    (Normalizer.translSub F).map (MulAut.conj γ) = Normalizer.translSub F := by
  have hfixinv : γ⁻¹ (∞ : P1 F) = ∞ := by
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]; exact hfix.symm
  have hle : (Normalizer.translSub F).map (MulAut.conj γ) ≤ Normalizer.translSub F := by
    rintro x ⟨t, ht, hteq⟩
    rw [← hteq]
    show MulAut.conj γ t ∈ Normalizer.translSub F
    rw [MulAut.conj_apply]
    exact Normalizer.conj_mem_translSub F (Subgroup.le_normalizer hγ) hfix ht
  have hle' : (Normalizer.translSub F).map (MulAut.conj γ⁻¹) ≤ Normalizer.translSub F := by
    rintro x ⟨t, ht, hteq⟩
    rw [← hteq]
    show MulAut.conj γ⁻¹ t ∈ Normalizer.translSub F
    rw [MulAut.conj_apply]
    exact Normalizer.conj_mem_translSub F (Subgroup.le_normalizer (inv_mem hγ)) hfixinv ht
  refine le_antisymm hle ?_
  intro g hg
  refine ⟨γ⁻¹ * g * γ, ?_, ?_⟩
  · exact hle' ⟨g, hg, by
      show MulAut.conj γ⁻¹ g = γ⁻¹ * g * γ
      rw [MulAut.conj_apply, inv_inv]⟩
  · show MulAut.conj γ (γ⁻¹ * g * γ) = g
    rw [MulAut.conj_apply]; group

/-- `(H.subgroupOf K).map K.subtype = H` when `H ≤ K`. -/
theorem subgroupOf_map_subtype_eq {M : Type*} [Group M] (K : Subgroup M) (H : Subgroup M)
    (hH : H ≤ K) : (H.subgroupOf K).map K.subtype = H := by
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
  exact hH

/-- For `K : Subgroup M` and `L : Subgroup ↥K`, mapping along `K.subtype` and pulling back
is the identity. -/
theorem subgroupOf_map_subtype_self {M : Type*} [Group M] (K : Subgroup M)
    (L : Subgroup ↥K) : (L.map K.subtype).subgroupOf K = L := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h : y = x := Subtype.ext hyx
    rwa [h] at hy
  · intro hx; exact ⟨x, hx, rfl⟩

/-- Cardinality of `H.subgroupOf K` when `H ≤ K`. -/
theorem card_subgroupOf {M : Type*} [Group M] {H K : Subgroup M} (hHK : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr
    { toFun := fun x => ⟨(x.1 : M), x.2⟩
      invFun := fun y => ⟨⟨(y.1 : M), hHK y.2⟩, y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

/-- Conjugating a subgroup commutes with `subgroupOf`. -/
theorem subgroupOf_map_conj {M : Type*} [Group M] (K : Subgroup M) (H : Subgroup M)
    (hH : H ≤ K) (g : ↥K) :
    (H.map (MulAut.conj (g : M))).subgroupOf K = (H.subgroupOf K).map (MulAut.conj g) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hhx⟩
    exact ⟨⟨h, hH hh⟩, Subgroup.mem_subgroupOf.mpr hh,
      Subtype.ext (by simpa [MulAut.conj_apply] using hhx)⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨(y : M), Subgroup.mem_subgroupOf.mp hy, ?_⟩
    exact (by simpa [MulAut.conj_apply] using congrArg Subtype.val hyx)

/-- Cardinality of the image of a subgroup under a multiplicative equivalence. -/
theorem card_map_mulEquiv {A : Type*} [Group A] (β : A ≃* A) (K : Subgroup A) :
    Nat.card (K.map β.toMonoidHom) = Nat.card K :=
  Subgroup.card_map_of_injective (f := β.toMonoidHom) (fun a b h => β.injective h)

/-- Conjugating a subgroup and then applying an automorphism: the two actions commute. -/
theorem map_conj_comp {A : Type*} [Group A] (β : A ≃* A) (H : Subgroup A) (g : A) :
    (H.map (MulAut.conj g).toMonoidHom).map β.toMonoidHom =
      (H.map β.toMonoidHom).map (MulAut.conj (β g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  apply congrArg (fun f => Subgroup.map f H)
  ext z
  simp only [MonoidHom.comp_apply]
  show β (MulAut.conj g z) = MulAut.conj (β g) (β z)
  rw [MulAut.conj_apply, MulAut.conj_apply]
  simp only [map_mul, map_inv]

section Galois

variable (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)] [DecidableEq (GaloisField p k)]

/-! ## The root subgroups -/

/-- Membership in `Upt x`, tested with any element of `pslImage F` moving `x` to `∞`. -/
theorem mem_Upt_iff (x : P1 (GaloisField p k)) (γ : Equiv.Perm (P1 (GaloisField p k)))
    (hγ : γ ∈ pslImage (GaloisField p k)) (hγx : γ x = ∞)
    (g : Equiv.Perm (P1 (GaloisField p k))) :
    g ∈ Upt p k x ↔ γ * g * γ⁻¹ ∈ Normalizer.translSub (GaloisField p k) := by
  have hδmem : gammaPt p k x * γ⁻¹ ∈ pslImage (GaloisField p k) :=
    mul_mem (gammaPt_mem p k x) (inv_mem hγ)
  have hδfix : (gammaPt p k x * γ⁻¹) (∞ : P1 (GaloisField p k)) = ∞ := by
    have h1 : γ⁻¹ (∞ : P1 (GaloisField p k)) = x := by
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]; exact hγx.symm
    rw [Equiv.Perm.mul_apply, h1]; exact gammaPt_apply p k x
  have hN : gammaPt p k x * γ⁻¹ ∈
      Subgroup.normalizer (Normalizer.translSub (GaloisField p k) :
        Set (Equiv.Perm (P1 (GaloisField p k)))) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (mapConjTranslSub (GaloisField p k) (gammaPt p k x * γ⁻¹) hδmem hδfix)
  rw [Upt_def, mem_map_conj_iff]
  simp only [inv_inv]
  rw [Subgroup.mem_normalizer_iff.mp hN (γ * g * γ⁻¹)]
  rw [show (gammaPt p k x * γ⁻¹) * (γ * g * γ⁻¹) * (gammaPt p k x * γ⁻¹)⁻¹ =
      gammaPt p k x * g * (gammaPt p k x)⁻¹ from by group]

/-- `Upt x` does not depend on the chosen element moving `x` to `∞`. -/
theorem Upt_eq_of (x : P1 (GaloisField p k)) (γ : Equiv.Perm (P1 (GaloisField p k)))
    (hγ : γ ∈ pslImage (GaloisField p k)) (hγx : γ x = ∞) :
    Upt p k x = (Normalizer.translSub (GaloisField p k)).map (MulAut.conj γ⁻¹) := by
  ext g
  rw [mem_map_conj_iff]
  simp only [inv_inv]
  exact mem_Upt_iff p k x γ hγ hγx g

/-- `Upt` is equivariant: conjugation by `γ ∈ pslImage F` sends the point `x` to `γ x`. -/
theorem Upt_conj (x : P1 (GaloisField p k)) (γ : Equiv.Perm (P1 (GaloisField p k)))
    (hγ : γ ∈ pslImage (GaloisField p k)) :
    Upt p k (γ x) = (Upt p k x).map (MulAut.conj γ) := by
  have hδmem : gammaPt p k x * γ⁻¹ ∈ pslImage (GaloisField p k) :=
    mul_mem (gammaPt_mem p k x) (inv_mem hγ)
  have hδx : (gammaPt p k x * γ⁻¹) (γ x) = ∞ := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    exact gammaPt_apply p k x
  ext g
  rw [mem_Upt_iff p k (γ x) (gammaPt p k x * γ⁻¹) hδmem hδx g]
  rw [mem_map_conj_iff,
    mem_Upt_iff p k x (gammaPt p k x) (gammaPt_mem p k x) (gammaPt_apply p k x)]
  rw [show (gammaPt p k x * γ⁻¹) * g * (gammaPt p k x * γ⁻¹)⁻¹ =
      gammaPt p k x * (γ⁻¹ * g * γ) * (gammaPt p k x)⁻¹ from by group]

/-- The only point fixed by all of `Upt x` is `x`. -/
theorem eq_of_forall_mem_Upt_fixes (x y : P1 (GaloisField p k))
    (h : ∀ g ∈ Upt p k x, g y = y) : y = x := by
  have hmem : (gammaPt p k x)⁻¹ * transl (GaloisField p k) 1 * gammaPt p k x ∈ Upt p k x := by
    rw [Upt_def, Subgroup.mem_map]
    refine ⟨transl (GaloisField p k) 1, Normalizer.transl_mem_translSub _ 1, ?_⟩
    show MulAut.conj (gammaPt p k x)⁻¹ (transl (GaloisField p k) 1) =
      (gammaPt p k x)⁻¹ * transl (GaloisField p k) 1 * gammaPt p k x
    rw [MulAut.conj_apply, inv_inv]
  have h1 := h _ hmem
  have h2 : transl (GaloisField p k) 1 (gammaPt p k x y) = gammaPt p k x y := by
    have h4 : gammaPt p k x
        (((gammaPt p k x)⁻¹ * transl (GaloisField p k) 1 * gammaPt p k x) y)
        = gammaPt p k x y := by rw [h1]
    simpa [Equiv.Perm.mul_apply] using h4
  have h3 : gammaPt p k x y = ∞ := transl_fixed (GaloisField p k) 1 one_ne_zero _ h2
  have h4 : gammaPt p k x y = gammaPt p k x x := by rw [h3, gammaPt_apply]
  exact (gammaPt p k x).injective h4

/-- `Upt` is injective: a root subgroup remembers its fixed point. -/
theorem uptInjective : Function.Injective (Upt p k) := by
  intro x y hxy
  have h : ∀ g ∈ Upt p k x, g y = y := by
    intro g hg; rw [hxy] at hg; exact Upt_fixes p k y g hg
  exact (eq_of_forall_mem_Upt_fixes p k x y h).symm

/-- The only subgroup of `pslImage F` of order `p ^ k` fixing `x` is `Upt x`. -/
theorem uptUnique (hp : Odd p) (hq : 5 ≤ p ^ k)
    (H : Subgroup (Equiv.Perm (P1 (GaloisField p k))))
    (hH : H ≤ pslImage (GaloisField p k)) (hcard : Nat.card H = p ^ k)
    (x : P1 (GaloisField p k)) (hfix : ∀ h ∈ H, h x = x) : H = Upt p k x := by
  set H' : Subgroup (Equiv.Perm (P1 (GaloisField p k))) :=
    H.map (MulAut.conj (gammaPt p k x)) with hH'def
  have hle' : H' ≤ pslImage (GaloisField p k) := by
    intro g hg
    rw [hH'def, Subgroup.mem_map] at hg
    obtain ⟨h, hh, hteq⟩ := hg
    rw [← hteq]
    show MulAut.conj (gammaPt p k x) h ∈ pslImage (GaloisField p k)
    rw [MulAut.conj_apply]
    exact mul_mem (mul_mem (gammaPt_mem p k x) (hH hh)) (inv_mem (gammaPt_mem p k x))
  have hcard' : Nat.card H' = p ^ k := by
    rw [hH'def, card_map_conj, hcard]
  have hfix' : ∀ g ∈ H', g ∞ = ∞ := by
    intro g hg
    rw [hH'def, Subgroup.mem_map] at hg
    obtain ⟨h, hh, hteq⟩ := hg
    rw [← hteq]
    show MulAut.conj (gammaPt p k x) h (∞ : P1 (GaloisField p k)) = ∞
    rw [MulAut.conj_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    have h1 : (gammaPt p k x)⁻¹ (∞ : P1 (GaloisField p k)) = x := by
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]; exact (gammaPt_apply p k x).symm
    rw [h1, hfix h hh, gammaPt_apply]
  have hEq : H' = Normalizer.translSub (GaloisField p k) :=
    eqTranslSub p k hp hq H' hle' hcard' hfix'
  rw [Upt_def]
  rw [← map_conj_mul_inv (GaloisField p k) H (gammaPt p k x), ← hH'def, hEq]

/-- Every subgroup of `pslImage F` of order `p ^ k` is a root subgroup. -/
theorem uptExists (hp : Odd p) (hq : 5 ≤ p ^ k)
    (H : Subgroup (Equiv.Perm (P1 (GaloisField p k))))
    (hH : H ≤ pslImage (GaloisField p k)) (hcard : Nat.card H = p ^ k) :
    ∃ x, H = Upt p k x := by
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  have hdvd : ¬ p ∣ Nat.card (P1 (GaloisField p k)) := by
    rw [card_P1 p k hq]
    intro h
    have hpk : p ∣ p ^ k := dvd_pow_self p hk
    have h1 : p ∣ (p ^ k + 1) - p ^ k := Nat.dvd_sub h hpk
    rw [Nat.add_sub_cancel_left] at h1
    exact (Fact.out : p.Prime).not_dvd_one h1
  obtain ⟨x, hx⟩ := exists_fixed_point_of_card_prime_pow H p k Fact.out hcard hdvd
  exact ⟨x, uptUnique p k hp hq H hH hcard x hx⟩

/-! ## The root subgroups of `pslImage`, as subgroups of the abstract group -/

/-- `Upt x` viewed as a subgroup of `↥(pslImage F)`. -/
noncomputable def UX (x : P1 (GaloisField p k)) : Subgroup ↥(pslImage (GaloisField p k)) :=
  (Upt p k x).subgroupOf (pslImage (GaloisField p k))

theorem UX_card (hq : 5 ≤ p ^ k) (x : P1 (GaloisField p k)) :
    Nat.card (UX p k x) = p ^ k := by
  rw [UX, card_subgroupOf (Upt_le_pslImage p k x), Upt_card p k hq x]

theorem UX_injective : Function.Injective (UX p k) := by
  intro x y hxy
  apply uptInjective p k
  have h1 : (UX p k x).map (pslImage (GaloisField p k)).subtype = Upt p k x :=
    subgroupOf_map_subtype_eq _ _ (Upt_le_pslImage p k x)
  have h2 : (UX p k y).map (pslImage (GaloisField p k)).subtype = Upt p k y :=
    subgroupOf_map_subtype_eq _ _ (Upt_le_pslImage p k y)
  rw [← h1, ← h2, hxy]

theorem UX_exists (hp : Odd p) (hq : 5 ≤ p ^ k) (K : Subgroup ↥(pslImage (GaloisField p k)))
    (hcard : Nat.card K = p ^ k) : ∃ x, K = UX p k x := by
  have hle : K.map (pslImage (GaloisField p k)).subtype ≤ pslImage (GaloisField p k) :=
    Subgroup.map_subtype_le K
  have hcard' : Nat.card (K.map (pslImage (GaloisField p k)).subtype) = p ^ k := by
    rw [Subgroup.card_map_of_injective (f := (pslImage (GaloisField p k)).subtype)
      Subtype.coe_injective, hcard]
  obtain ⟨x, hx⟩ := uptExists p k hp hq _ hle hcard'
  refine ⟨x, ?_⟩
  have h3 : K = (Upt p k x).subgroupOf (pslImage (GaloisField p k)) := by
    rw [← hx, subgroupOf_map_subtype_self]
  rw [h3, UX]

theorem UX_conj (g : ↥(pslImage (GaloisField p k))) (x : P1 (GaloisField p k)) :
    (UX p k x).map (MulAut.conj g) = UX p k (g • x) := by
  rw [UX, UX]
  rw [← subgroupOf_map_conj (pslImage (GaloisField p k)) (Upt p k x)
    (Upt_le_pslImage p k x) g]
  rw [show g • x = (g : Equiv.Perm (P1 (GaloisField p k))) x from rfl,
    Upt_conj p k x (g : Equiv.Perm (P1 (GaloisField p k))) g.2]

/-! ## The bijection `ℙ¹(F) ≃ {root subgroups}` -/

/-- The points of `ℙ¹(F)` are the root subgroups of `pslImage F`. -/
noncomputable def UXEquiv (hp : Odd p) (hq : 5 ≤ p ^ k) :
    P1 (GaloisField p k) ≃
      {K : Subgroup ↥(pslImage (GaloisField p k)) // Nat.card K = p ^ k} where
  toFun x := ⟨UX p k x, UX_card p k hq x⟩
  invFun K := Classical.choose (UX_exists p k hp hq K.1 K.2)
  left_inv x := by
    apply UX_injective p k
    exact (Classical.choose_spec (UX_exists p k hp hq (UX p k x) (UX_card p k hq x))).symm
  right_inv K := by
    apply Subtype.ext
    exact (Classical.choose_spec (UX_exists p k hp hq K.1 K.2)).symm

/-- An automorphism of `↥(pslImage F)` permutes the root subgroups. -/
noncomputable def autSubtypeEquiv
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k))) :
    {K : Subgroup ↥(pslImage (GaloisField p k)) // Nat.card K = p ^ k} ≃
      {K : Subgroup ↥(pslImage (GaloisField p k)) // Nat.card K = p ^ k} where
  toFun K := ⟨K.1.map β.toMonoidHom, by rw [card_map_mulEquiv β K.1, K.2]⟩
  invFun K := ⟨K.1.map β.symm.toMonoidHom, by rw [card_map_mulEquiv β.symm K.1, K.2]⟩
  left_inv K := by
    apply Subtype.ext
    show (K.1.map β.toMonoidHom).map β.symm.toMonoidHom = K.1
    rw [Subgroup.map_map]
    have hcomp : (β.symm.toMonoidHom).comp β.toMonoidHom = MonoidHom.id _ := by
      ext z; simp
    rw [hcomp, Subgroup.map_id]
  right_inv K := by
    apply Subtype.ext
    show (K.1.map β.symm.toMonoidHom).map β.toMonoidHom = K.1
    rw [Subgroup.map_map]
    have hcomp : (β.toMonoidHom).comp β.symm.toMonoidHom = MonoidHom.id _ := by
      ext z; simp
    rw [hcomp, Subgroup.map_id]

/-- The permutation of `ℙ¹(F)` induced by an automorphism of `pslImage F`. -/
noncomputable def piPerm (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k))) :
    Equiv.Perm (P1 (GaloisField p k)) :=
  (UXEquiv p k hp hq).trans ((autSubtypeEquiv p k β).trans (UXEquiv p k hp hq).symm)

theorem UX_pi (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k)))
    (x : P1 (GaloisField p k)) :
    UX p k (piPerm p k hp hq β x) = (UX p k x).map β.toMonoidHom := by
  have h1 : UXEquiv p k hp hq (piPerm p k hp hq β x) =
      autSubtypeEquiv p k β (UXEquiv p k hp hq x) := by
    simp only [piPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  have h2 := congrArg Subtype.val h1
  change UX p k (piPerm p k hp hq β x) = (UX p k x).map β.toMonoidHom at h2
  exact h2

/-- The equivariance of `piPerm`. -/
theorem pi_conj (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k)))
    (g : ↥(pslImage (GaloisField p k))) (x : P1 (GaloisField p k)) :
    piPerm p k hp hq β (g • x) = (β g) • (piPerm p k hp hq β x) := by
  apply UX_injective p k
  rw [UX_pi p k hp hq β (g • x), ← UX_conj p k g x,
      ← UX_conj p k (β g) (piPerm p k hp hq β x), UX_pi p k hp hq β x]
  exact map_conj_comp β (UX p k x) g

/-- `piPerm` intertwines the actions: `π * g = β g * π`. -/
theorem pi_mul_eq (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k)))
    (g : ↥(pslImage (GaloisField p k))) :
    piPerm p k hp hq β * (g : Equiv.Perm (P1 (GaloisField p k))) =
      ((β g : ↥(pslImage (GaloisField p k))) : Equiv.Perm (P1 (GaloisField p k))) *
        piPerm p k hp hq β := by
  apply Equiv.ext
  intro y
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  show piPerm p k hp hq β (g • y) = (β g) • (piPerm p k hp hq β y)
  exact pi_conj p k hp hq β g y

/-- `piPerm` conjugates `g` to `β g`. -/
theorem pi_mul_conj (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k)))
    (g : ↥(pslImage (GaloisField p k))) :
    piPerm p k hp hq β * (g : Equiv.Perm (P1 (GaloisField p k))) *
        (piPerm p k hp hq β)⁻¹ =
      ((β g : ↥(pslImage (GaloisField p k))) : Equiv.Perm (P1 (GaloisField p k))) := by
  rw [pi_mul_eq p k hp hq β g]
  group

/-- `piPerm` normalizes `pslImage F`, hence lies in `PΓL(2,F)`. -/
theorem pi_mem_pgammaL (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k))) :
    piPerm p k hp hq β ∈ pgammaL (GaloisField p k) := by
  refine Normalizer.le_pgammaL p k hp hq (piPerm p k hp hq β) ?_
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro y ⟨g, hg, rfl⟩
    show MulAut.conj (piPerm p k hp hq β) g ∈ pslImage (GaloisField p k)
    rw [MulAut.conj_apply, pi_mul_conj p k hp hq β ⟨g, hg⟩]
    exact (β ⟨g, hg⟩).2
  · intro y hy
    refine Subgroup.mem_map.mpr
      ⟨(β.symm ⟨y, hy⟩ : ↥(pslImage (GaloisField p k))), (β.symm ⟨y, hy⟩).2, ?_⟩
    show MulAut.conj (piPerm p k hp hq β)
      ((β.symm ⟨y, hy⟩ : ↥(pslImage (GaloisField p k))) :
        Equiv.Perm (P1 (GaloisField p k))) = y
    rw [MulAut.conj_apply, pi_mul_conj p k hp hq β (β.symm ⟨y, hy⟩)]
    simp

end Galois

/-! ## The deliverable -/

theorem realize (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    [DecidableEq (GaloisField p k)] (hp : Odd p) (hq : 5 ≤ p ^ k)
    (α : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :
    ∃ π : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)),
      π ∈ Work.AUTL2.pgammaL (GaloisField p k) ∧
        ∀ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k),
          π * Work.AUTL2.pslHom (GaloisField p k) x * π⁻¹ =
            Work.AUTL2.pslHom (GaloisField p k) (α x) := by
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k) ≃*
      ↥(pslImage (GaloisField p k)) :=
    MonoidHom.ofInjective (Work.AUTL2.Aut.pslHomInjective (GaloisField p k))
  let β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k)) :=
    e.symm.trans (α.trans e)
  have hco : ∀ z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k),
      ((e z : ↥(pslImage (GaloisField p k))) : Equiv.Perm (P1 (GaloisField p k))) =
        pslHom (GaloisField p k) z := fun _ => rfl
  refine ⟨piPerm p k hp hq β, pi_mem_pgammaL p k hp hq β, ?_⟩
  intro x
  have hβ : β (e x) = e (α x) := by
    show (e.symm.trans (α.trans e)) (e x) = e (α x)
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
  rw [← hco x, pi_mul_conj p k hp hq β (e x), hβ, hco (α x)]

end Work.AUTL2.Main
