/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 / Aut : every automorphism of `PSL(2,q)` is realized inside `PΓL(2,q)`

Step A6 (transfer) of the AUTL2 design.  For `q = p ^ k`, `p` odd, `q ≥ 5`, every group
automorphism `α` of `PSL(2,q)` is induced by conjugation with a permutation `π` of the
projective line lying in `PΓL(2,F)`:

* `Work.AUTL2.Aut.realize` (the deliverable).

The proof is the classical geometric reconstruction of `α`:

* the root subgroups (the Sylow `p`-subgroups of `pslImage F`, i.e. the unipotent radicals of the
  point stabilizers) are parametrized by the points of `ℙ¹(F)`: for `x` let `Upt p k x` be the
  conjugate of the translation group `U = {x ↦ x + b}` by an element of `pslImage F` moving `x`
  to `∞`; these are exactly the subgroups of `pslImage F` of cardinality `p^k`
  (`Work.AUTL2.Aut.geometry` and `Work.AUTL2.Aut.pointGroup` here), each with `x` as its unique
  fixed point;
* an automorphism `β` of `pslImage F` permutes them, hence induces a permutation `π` of
  `ℙ¹(F)` by `Upt (π x) = β (Upt x)` (`piPerm`);
* the equivariance `Upt (g • x) = β g • Upt x` (`piPerm_conj`) turns into
  `π * g * π⁻¹ = β g` for all `g ∈ pslImage F`, i.e. `π` normalizes `pslImage F`, and
  `Work.AUTL2.Normalizer.le_pgammaL` gives `π ∈ pgammaL F`.
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Mobius
import Submission.Work.AUTL2.Stabilizer
import Submission.Work.AUTL2.Normalizer.Defs
import Submission.Work.AUTL2.Normalizer.le_pgammaL
import Submission.Work.AUTL2.Aut.images
import Submission.Work.AUTL2.Aut.geometry

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint Subgroup

namespace Work.AUTL2.Aut

open Work.AUTL2

/-! ## Conjugation bookkeeping -/

section Conj

variable {F : Type*} [Field F] [DecidableEq F]

/-- Conjugation, as a monoid homomorphism. -/
noncomputable def conjH (δ : Equiv.Perm (P1 F)) : Equiv.Perm (P1 F) →* Equiv.Perm (P1 F) :=
  (MulAut.conj δ).toMonoidHom

@[simp] lemma conjH_apply (δ g : Equiv.Perm (P1 F)) : conjH δ g = δ * g * δ⁻¹ := by
  show MulAut.conj δ g = δ * g * δ⁻¹
  rw [MulAut.conj_apply]

@[simp] lemma conjH_one : conjH (1 : Equiv.Perm (P1 F)) = MonoidHom.id _ := by
  ext z
  simp [conjH_apply]

@[simp] lemma conjH_comp (δ ε : Equiv.Perm (P1 F)) :
    (conjH δ).comp (conjH ε) = conjH (δ * ε) := by
  ext z
  simp [conjH_apply, mul_assoc]

@[simp] lemma conjH_mul_inv (δ : Equiv.Perm (P1 F)) : (conjH δ).comp (conjH δ⁻¹) = MonoidHom.id _ := by
  rw [conjH_comp, mul_inv_cancel, conjH_one]

@[simp] lemma conjH_inv_mul (δ : Equiv.Perm (P1 F)) : (conjH δ⁻¹).comp (conjH δ) = MonoidHom.id _ := by
  rw [conjH_comp, inv_mul_cancel, conjH_one]

/-- Membership in the conjugate `H.map (conjH δ)`. -/
lemma mem_map_conj_iff {H : Subgroup (Equiv.Perm (P1 F))} {δ g : Equiv.Perm (P1 F)} :
    g ∈ H.map (conjH δ) ↔ δ⁻¹ * g * δ ∈ H := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨t, ht, hteq⟩
    have h : δ⁻¹ * g * δ = t := by
      rw [← hteq]
      simp only [conjH_apply]
      group
    rwa [h]
  · intro hmem
    exact ⟨δ⁻¹ * g * δ, hmem, by
      simp only [conjH_apply]
      group⟩

/-- Cardinality of a conjugate subgroup. -/
lemma card_map_conj {H : Subgroup (Equiv.Perm (P1 F))} {δ : Equiv.Perm (P1 F)} :
    Nat.card (H.map (conjH δ)) = Nat.card H :=
  Subgroup.card_map_of_injective (f := conjH δ) (MulAut.conj δ).injective

/-- Conjugating a subgroup by `δ` and then by `δ⁻¹` gives it back. -/
lemma map_conj_inv_map_conj {H : Subgroup (Equiv.Perm (P1 F))} {δ : Equiv.Perm (P1 F)} :
    (H.map (conjH δ)).map (conjH δ⁻¹) = H := by
  rw [Subgroup.map_map, conjH_inv_mul, Subgroup.map_id]

/-- Conjugating a subgroup by `δ⁻¹` and then by `δ` gives it back. -/
lemma map_conj_inv_map_conj' {H : Subgroup (Equiv.Perm (P1 F))} {δ : Equiv.Perm (P1 F)} :
    (H.map (conjH δ⁻¹)).map (conjH δ) = H := by
  rw [Subgroup.map_map, conjH_mul_inv, Subgroup.map_id]

end Conj

/-! ## The point groups are the only subgroups of order `p ^ k` fixing a given point -/

section GF

variable (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)] [DecidableEq (GaloisField p k)]

/-- The point group of `x`, in the explicit form given by the definition. -/
lemma Upt_eq_conj (x : P1 (GaloisField p k)) :
    Upt p k x = (Normalizer.translSub (GaloisField p k)).map (conjH (gammaPt p k x)⁻¹) :=
  Upt_def p k x

/-- `g ∈ Upt p k x` iff conjugating `g` into the `∞`-chart by `gammaPt p k x` gives a
translation. -/
lemma mem_Upt_iff {x : P1 (GaloisField p k)} {g : Equiv.Perm (P1 (GaloisField p k))} :
    g ∈ Upt p k x ↔
      gammaPt p k x * g * (gammaPt p k x)⁻¹ ∈ Normalizer.translSub (GaloisField p k) := by
  rw [Upt_eq_conj, mem_map_conj_iff]
  simp only [inv_inv]

/-- **Uniqueness of the point group.**  A subgroup of `pslImage F` of cardinality `p ^ k` all of
whose elements fix `x` is `Upt p k x`.  (Conjugate by an element of `pslImage F` moving `x` to
`∞`, then apply `eqTranslSub`.) -/
theorem pointGroup (hp : Odd p) (hq : 5 ≤ p ^ k)
    (H : Subgroup (Equiv.Perm (P1 (GaloisField p k)))) (x : P1 (GaloisField p k))
    (hH : H ≤ pslImage (GaloisField p k)) (hcard : Nat.card H = p ^ k)
    (hfix : ∀ h ∈ H, h x = x) :
    H = Upt p k x := by
  have hγ : gammaPt p k x ∈ pslImage (GaloisField p k) := gammaPt_mem p k x
  have hγx : gammaPt p k x x = ∞ := gammaPt_apply p k x
  -- conjugate `H` by `gammaPt p k x`, so that it fixes `∞`
  have hle : (H.map (conjH (gammaPt p k x))) ≤ pslImage (GaloisField p k) := by
    rintro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨h, hh, hgh⟩ := hg
    rw [← hgh]
    simp only [conjH_apply]
    exact mul_mem (mul_mem hγ (hH hh)) (inv_mem hγ)
  have hcard' : Nat.card (H.map (conjH (gammaPt p k x))) = p ^ k := by
    rw [card_map_conj, hcard]
  have hfix' : ∀ g ∈ H.map (conjH (gammaPt p k x)), g ∞ = ∞ := by
    intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨h, hh, hgh⟩ := hg
    rw [← hgh]
    simp only [conjH_apply, Equiv.Perm.mul_apply]
    have h1 : (gammaPt p k x)⁻¹ ∞ = x := by
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
      exact hγx.symm
    rw [h1, hfix h hh, hγx]
  have hEq : H.map (conjH (gammaPt p k x)) = Normalizer.translSub (GaloisField p k) :=
    eqTranslSub p k hp hq _ hle hcard' hfix'
  rw [Upt_eq_conj, ← map_conj_inv_map_conj (H := H) (δ := gammaPt p k x), hEq]

/-- `Upt` is equivariant under the action of `pslImage F` on `ℙ¹(F)`. -/
theorem Upt_conj (hp : Odd p) (hq : 5 ≤ p ^ k) (x : P1 (GaloisField p k))
    (g : Equiv.Perm (P1 (GaloisField p k))) (hg : g ∈ pslImage (GaloisField p k)) :
    Upt p k (g x) = (Upt p k x).map (conjH g) := by
  refine (pointGroup p k hp hq _ (g x) ?_ ?_ ?_).symm
  · rintro y ⟨t, ht, rfl⟩
    simp only [conjH_apply]
    exact mul_mem (mul_mem hg (Upt_le_pslImage p k x ht)) (inv_mem hg)
  · rw [card_map_conj, Upt_card p k hq x]
  · rintro y ⟨t, ht, rfl⟩
    simp only [conjH_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rw [Upt_fixes p k x t ht]

/-- The only point fixed by all of `Upt p k x` is `x`. -/
theorem eq_of_forall_mem_Upt_fixes (x y : P1 (GaloisField p k))
    (h : ∀ g ∈ Upt p k x, g y = y) : y = x := by
  have hmem : (gammaPt p k x)⁻¹ * transl (GaloisField p k) 1 * gammaPt p k x ∈ Upt p k x := by
    rw [mem_Upt_iff]
    have h1 : gammaPt p k x *
        ((gammaPt p k x)⁻¹ * transl (GaloisField p k) 1 * gammaPt p k x) *
        (gammaPt p k x)⁻¹ = transl (GaloisField p k) 1 := by group
    rw [h1]
    exact Normalizer.transl_mem_translSub _ 1
  have h2 := congrArg (gammaPt p k x) (h _ hmem)
  have h1 : transl (GaloisField p k) 1 (gammaPt p k x y) = gammaPt p k x y := by
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h2
  have h3 : gammaPt p k x y = ∞ := transl_fixed (GaloisField p k) 1 one_ne_zero _ h1
  have h4 : gammaPt p k x y = gammaPt p k x x := by rw [h3, gammaPt_apply]
  exact (gammaPt p k x).injective h4

/-- `Upt` is injective. -/
theorem uptInjective : Function.Injective (Upt p k) := by
  intro x y hxy
  have h : ∀ g ∈ Upt p k x, g y = y := by
    intro g hg
    rw [hxy] at hg
    exact Upt_fixes p k y g hg
  exact (eq_of_forall_mem_Upt_fixes p k x y h).symm

/-- Every subgroup of `pslImage F` of cardinality `p ^ k` is a point group. -/
theorem exists_eq_Upt (hp : Odd p) (hq : 5 ≤ p ^ k)
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
  exact ⟨x, pointGroup p k hp hq H x hH hcard hx⟩

end GF

/-! ## The point groups inside the abstract group `↥(pslImage F)` -/

section Abstract

variable (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)] [DecidableEq (GaloisField p k)]

/-- `Upt p k x`, viewed as a subgroup of the abstract group `↥(pslImage F)`. -/
noncomputable def KU (x : P1 (GaloisField p k)) : Subgroup ↥(pslImage (GaloisField p k)) :=
  (Upt p k x).comap (Subgroup.subtype (pslImage (GaloisField p k)))

lemma mem_KU_iff {x : P1 (GaloisField p k)} {g : ↥(pslImage (GaloisField p k))} :
    g ∈ KU p k x ↔ (g : Equiv.Perm (P1 (GaloisField p k))) ∈ Upt p k x := Iff.rfl

/-- Cardinality of `H.subgroupOf K` for `H ≤ K`. -/
theorem card_comap_subtype_of_le {H : Subgroup (Equiv.Perm (P1 (GaloisField p k)))}
    (hH : H ≤ pslImage (GaloisField p k)) :
    Nat.card (H.comap (Subgroup.subtype (pslImage (GaloisField p k)))) = Nat.card H :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, hH y.2⟩, y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

lemma KU_card (hq : 5 ≤ p ^ k) (x : P1 (GaloisField p k)) :
    Nat.card (KU p k x) = p ^ k := by
  rw [KU, card_comap_subtype_of_le p k (Upt_le_pslImage p k x), Upt_card p k hq x]

/-- `(H.subgroupOf K).map K.subtype = H` for `H ≤ K`. -/
theorem map_subtype_comap_self {H : Subgroup (Equiv.Perm (P1 (GaloisField p k)))}
    (hH : H ≤ pslImage (GaloisField p k)) :
    (H.comap (Subgroup.subtype (pslImage (GaloisField p k)))).map
      (Subgroup.subtype (pslImage (GaloisField p k))) = H := by
  rw [Subgroup.map_comap_eq_self]
  rwa [Subgroup.range_subtype]

/-- Pulling back after mapping along `K.subtype` is the identity. -/
theorem comap_subtype_map_subtype (K : Subgroup ↥(pslImage (GaloisField p k))) :
    (K.map (Subgroup.subtype (pslImage (GaloisField p k)))).comap
      (Subgroup.subtype (pslImage (GaloisField p k))) = K := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h : y = x := Subtype.ext hyx
    rwa [h] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma KU_injective : Function.Injective (KU p k) := by
  intro x y hxy
  refine uptInjective p k ?_
  have h2 := congrArg (fun K : Subgroup ↥(pslImage (GaloisField p k)) =>
    K.map (Subgroup.subtype (pslImage (GaloisField p k)))) hxy
  simp only [KU] at h2
  rwa [map_subtype_comap_self p k (Upt_le_pslImage p k x),
    map_subtype_comap_self p k (Upt_le_pslImage p k y)] at h2

lemma KU_exists (hp : Odd p) (hq : 5 ≤ p ^ k)
    (K : Subgroup ↥(pslImage (GaloisField p k))) (hK : Nat.card K = p ^ k) :
    ∃ x, K = KU p k x := by
  have hle : K.map (Subgroup.subtype (pslImage (GaloisField p k))) ≤ pslImage (GaloisField p k) :=
    Subgroup.map_subtype_le K
  have hcard : Nat.card (K.map (Subgroup.subtype (pslImage (GaloisField p k)))) = p ^ k := by
    rw [Subgroup.card_map_of_injective (f := Subgroup.subtype (pslImage (GaloisField p k)))
      Subtype.coe_injective, hK]
  obtain ⟨x, hx⟩ := exists_eq_Upt p k hp hq _ hle hcard
  refine ⟨x, ?_⟩
  have h3 : K = (Upt p k x).comap (Subgroup.subtype (pslImage (GaloisField p k))) := by
    rw [← hx, comap_subtype_map_subtype]
  rw [h3, KU]

/-- Conjugation in the abstract group, transported to the ambient permutation group. -/
lemma subtype_conj_coe (g t : ↥(pslImage (GaloisField p k))) :
    (((MulAut.conj g).toMonoidHom t : ↥(pslImage (GaloisField p k))) :
      Equiv.Perm (P1 (GaloisField p k))) =
      conjH (g : Equiv.Perm (P1 (GaloisField p k)))
        (t : Equiv.Perm (P1 (GaloisField p k))) := by
  have h1 : ((MulAut.conj g).toMonoidHom t : ↥(pslImage (GaloisField p k))) = g * t * g⁻¹ := by
    show MulAut.conj g t = g * t * g⁻¹
    rw [MulAut.conj_apply]
  rw [h1, conjH_apply]
  simp

lemma KU_conj (hp : Odd p) (hq : 5 ≤ p ^ k) (g : ↥(pslImage (GaloisField p k)))
    (x : P1 (GaloisField p k)) :
    (KU p k x).map (MulAut.conj g).toMonoidHom =
      KU p k ((g : Equiv.Perm (P1 (GaloisField p k))) x) := by
  ext z
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨t, ht, htz⟩
    rw [← htz]
    change ((MulAut.conj g).toMonoidHom t : Equiv.Perm (P1 (GaloisField p k))) ∈
      Upt p k ((g : Equiv.Perm (P1 (GaloisField p k))) x)
    rw [Upt_conj p k hp hq x (g : Equiv.Perm (P1 (GaloisField p k))) g.2]
    refine Subgroup.mem_map.mpr ⟨(t : Equiv.Perm (P1 (GaloisField p k))),
      (Subgroup.mem_comap.mp ht), ?_⟩
    exact (subtype_conj_coe p k g t).symm
  · intro hz
    have hz' : (z : Equiv.Perm (P1 (GaloisField p k))) ∈
        (Upt p k x).map (conjH (g : Equiv.Perm (P1 (GaloisField p k)))) := by
      rw [← Upt_conj p k hp hq x (g : Equiv.Perm (P1 (GaloisField p k))) g.2]
      exact hz
    obtain ⟨t, ht, htz⟩ := Subgroup.mem_map.mp hz'
    refine ⟨⟨t, Upt_le_pslImage p k x ht⟩, Subgroup.mem_comap.mpr ht, ?_⟩
    apply Subtype.ext
    show conjH (g : Equiv.Perm (P1 (GaloisField p k))) t = (z : Equiv.Perm (P1 (GaloisField p k)))
    rw [conjH_apply]
    exact htz

end Abstract

/-! ## The permutation of `ℙ¹(F)` induced by an automorphism of `↥(pslImage F)` -/

section Pi

variable (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)] [DecidableEq (GaloisField p k)]

/-- Cardinality of the image of a subgroup under an automorphism. -/
lemma card_map_mulEquiv {A : Type*} [Group A] (β : A ≃* A) (K : Subgroup A) :
    Nat.card (K.map β.toMonoidHom) = Nat.card K :=
  Subgroup.card_map_of_injective (f := β.toMonoidHom) β.injective

/-- Round trip: mapping along `β` and back along `β⁻¹`. -/
lemma map_map_mulEquiv_symm {A : Type*} [Group A] (β : A ≃* A) (K : Subgroup A) :
    (K.map β.toMonoidHom).map β.symm.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have h : (β.symm.toMonoidHom).comp β.toMonoidHom = MonoidHom.id A := by
    ext z
    simp
  rw [h, Subgroup.map_id]

/-- Round trip: mapping along `β⁻¹` and back along `β`. -/
lemma map_map_mulEquiv_symm' {A : Type*} [Group A] (β : A ≃* A) (K : Subgroup A) :
    (K.map β.symm.toMonoidHom).map β.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have h : (β.toMonoidHom).comp β.symm.toMonoidHom = MonoidHom.id A := by
    ext z
    simp
  rw [h, Subgroup.map_id]

/-- Conjugating a subgroup and applying an automorphism: the two operations commute. -/
lemma map_conj_comp {A : Type*} [Group A] (β : A ≃* A) (K : Subgroup A) (g : A) :
    (K.map (MulAut.conj g).toMonoidHom).map β.toMonoidHom =
      (K.map β.toMonoidHom).map (MulAut.conj (β g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext z
  simp only [MonoidHom.comp_apply]
  show β (MulAut.conj g z) = MulAut.conj (β g) (β z)
  simp only [MulAut.conj_apply, map_mul, map_inv]

/-- The point whose root subgroup is `K`. -/
noncomputable def ptOf (hp : Odd p) (hq : 5 ≤ p ^ k)
    (K : Subgroup ↥(pslImage (GaloisField p k))) (hK : Nat.card K = p ^ k) :
    P1 (GaloisField p k) :=
  Classical.choose (KU_exists p k hp hq K hK)

lemma ptOf_spec (hp : Odd p) (hq : 5 ≤ p ^ k)
    (K : Subgroup ↥(pslImage (GaloisField p k))) (hK : Nat.card K = p ^ k) :
    KU p k (ptOf p k hp hq K hK) = K :=
  (Classical.choose_spec (KU_exists p k hp hq K hK)).symm

lemma ptOf_KU (hp : Odd p) (hq : 5 ≤ p ^ k) (x : P1 (GaloisField p k))
    (hK : Nat.card (KU p k x) = p ^ k) :
    ptOf p k hp hq (KU p k x) hK = x :=
  KU_injective p k (by rw [ptOf_spec])

/-- Conjugation by `g` moves the point of `K` to `g` applied to it. -/
lemma ptOf_conj (hp : Odd p) (hq : 5 ≤ p ^ k)
    (K : Subgroup ↥(pslImage (GaloisField p k))) (hK : Nat.card K = p ^ k)
    (g : ↥(pslImage (GaloisField p k))) :
    ptOf p k hp hq (K.map (MulAut.conj g).toMonoidHom)
        (by rw [card_map_mulEquiv, hK]) =
      (g : Equiv.Perm (P1 (GaloisField p k))) (ptOf p k hp hq K hK) := by
  apply KU_injective p k
  rw [ptOf_spec, ← KU_conj p k hp hq g (ptOf p k hp hq K hK), ptOf_spec]

/-- The permutation of `ℙ¹(F)` induced by the automorphism `β` of `↥(pslImage F)`: it sends the
point of `K` to the point of `β K`. -/
noncomputable def piFun (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k)))
    (x : P1 (GaloisField p k)) : P1 (GaloisField p k) :=
  ptOf p k hp hq ((KU p k x).map β.toMonoidHom)
    (by rw [card_map_mulEquiv, KU_card p k hq])

lemma piFun_spec (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k)))
    (x : P1 (GaloisField p k)) :
    KU p k (piFun p k hp hq β x) = (KU p k x).map β.toMonoidHom :=
  ptOf_spec p k hp hq _ _

lemma piFun_injective (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k))) :
    Function.Injective (piFun p k hp hq β) := by
  intro x y hxy
  apply KU_injective p k
  have h : (KU p k x).map β.toMonoidHom = (KU p k y).map β.toMonoidHom := by
    rw [← piFun_spec p k hp hq β x, ← piFun_spec p k hp hq β y, hxy]
  have h2 : ((KU p k x).map β.toMonoidHom).map β.symm.toMonoidHom =
      ((KU p k y).map β.toMonoidHom).map β.symm.toMonoidHom := by rw [h]
  rwa [map_map_mulEquiv_symm, map_map_mulEquiv_symm] at h2

lemma piFun_surjective (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k))) :
    Function.Surjective (piFun p k hp hq β) := by
  intro y
  refine ⟨ptOf p k hp hq ((KU p k y).map β.symm.toMonoidHom)
    (by rw [card_map_mulEquiv, KU_card p k hq]), ?_⟩
  apply KU_injective p k
  rw [piFun_spec, ptOf_spec, map_map_mulEquiv_symm']

/-- The permutation of `ℙ¹(F)` induced by the automorphism `β` of `↥(pslImage F)`. -/
noncomputable def piPerm (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k))) :
    Equiv.Perm (P1 (GaloisField p k)) :=
  Equiv.ofBijective (piFun p k hp hq β)
    ⟨piFun_injective p k hp hq β, piFun_surjective p k hp hq β⟩

lemma piPerm_apply (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k)))
    (x : P1 (GaloisField p k)) :
    piPerm p k hp hq β x = piFun p k hp hq β x := rfl

/-- The equivariance of `piPerm`. -/
lemma piPerm_conj (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k)))
    (g : ↥(pslImage (GaloisField p k))) (x : P1 (GaloisField p k)) :
    piPerm p k hp hq β ((g : Equiv.Perm (P1 (GaloisField p k))) x) =
      ((β g : ↥(pslImage (GaloisField p k))) : Equiv.Perm (P1 (GaloisField p k)))
        (piPerm p k hp hq β x) := by
  rw [piPerm_apply, piPerm_apply]
  apply KU_injective p k
  rw [piFun_spec, ← KU_conj p k hp hq g x, map_conj_comp, ← piFun_spec,
    ← KU_conj p k hp hq (β g) (piFun p k hp hq β x)]

/-- `piPerm` intertwines the two actions. -/
lemma piPerm_mul_eq (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k)))
    (g : ↥(pslImage (GaloisField p k))) :
    piPerm p k hp hq β * (g : Equiv.Perm (P1 (GaloisField p k))) =
      ((β g : ↥(pslImage (GaloisField p k))) : Equiv.Perm (P1 (GaloisField p k))) *
        piPerm p k hp hq β := by
  apply Equiv.ext
  intro y
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  exact piPerm_conj p k hp hq β g y

/-- `piPerm` conjugates `g` into `β g`. -/
lemma piPerm_mul_conj (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k)))
    (g : ↥(pslImage (GaloisField p k))) :
    piPerm p k hp hq β * (g : Equiv.Perm (P1 (GaloisField p k))) *
        (piPerm p k hp hq β)⁻¹ =
      ((β g : ↥(pslImage (GaloisField p k))) : Equiv.Perm (P1 (GaloisField p k))) := by
  rw [piPerm_mul_eq p k hp hq β g]
  group

/-- `piPerm` lies in `PΓL(2,F)`. -/
theorem piPerm_mem_pgammaL (hp : Odd p) (hq : 5 ≤ p ^ k)
    (β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k))) :
    piPerm p k hp hq β ∈ pgammaL (GaloisField p k) := by
  refine Normalizer.le_pgammaL p k hp hq _ ?_
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro y ⟨g, hg, rfl⟩
    show MulAut.conj (piPerm p k hp hq β) g ∈ pslImage (GaloisField p k)
    rw [MulAut.conj_apply, piPerm_mul_conj p k hp hq β ⟨g, hg⟩]
    exact (β ⟨g, hg⟩).2
  · intro y hy
    refine Subgroup.mem_map.mpr
      ⟨((β.symm ⟨y, hy⟩ : ↥(pslImage (GaloisField p k))) :
        Equiv.Perm (P1 (GaloisField p k))), (β.symm ⟨y, hy⟩).2, ?_⟩
    show MulAut.conj (piPerm p k hp hq β)
      ((β.symm ⟨y, hy⟩ : ↥(pslImage (GaloisField p k))) :
        Equiv.Perm (P1 (GaloisField p k))) = y
    rw [MulAut.conj_apply, piPerm_mul_conj p k hp hq β (β.symm ⟨y, hy⟩)]
    simp

end Pi

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
  classical
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k) ≃*
      ↥(pslImage (GaloisField p k)) :=
    MonoidHom.ofInjective (pslHomInjective (GaloisField p k))
  let β : ↥(pslImage (GaloisField p k)) ≃* ↥(pslImage (GaloisField p k)) :=
    e.symm.trans (α.trans e)
  have he : ∀ z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k),
      ((e z : ↥(pslImage (GaloisField p k))) : Equiv.Perm (P1 (GaloisField p k))) =
        pslHom (GaloisField p k) z := fun _ => rfl
  have hβ : ∀ z, β (e z) = e (α z) := by
    intro z
    show (e.symm.trans (α.trans e)) (e z) = e (α z)
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
  refine ⟨piPerm p k hp hq β, piPerm_mem_pgammaL p k hp hq β, ?_⟩
  intro x
  rw [← he x, piPerm_mul_conj p k hp hq β (e x), hβ x, he (α x)]

end Work.AUTL2.Aut
