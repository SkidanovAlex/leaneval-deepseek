/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The number of `dil`-conjugates of `smulHom a * galHom σ`

Split case of DS10a.  For `F = GF(p^k)` (`p` odd) and `σ` a field automorphism of `F` of odd
prime order `r`, the conjugates

  `dil u * (smulHom a * galHom σ) * (dil u)⁻¹`,   `u ∈ Fˣ`,

of `smulHom a * galHom σ` under the square torus `dil u = smulHom (u²)` are the elements

  `smulHom (a · (phiHom σ u)²) * galHom σ`,   `phiHom σ u = u / σu`,

and there are exactly `(p^k - 1) / (p^(k/r) - 1)` of them.

The two ingredients are

* `card_ker_phiHom`: the kernel of `phiHom σ` is the unit group of the fixed field of `σ`, of
  order `p^(k/r) - 1`; since `phiHom σ` is onto its range this gives
  `|range (phiHom σ)| = (p^k - 1)/(p^(k/r) - 1)`, and
* `sq_injOn_range_phi` (with `phi_ne_neg_one`): squaring is injective on the range of `phiHom σ`
  because `-1` is not in it, so multiplying by `a` and squaring does not change the number of
  values.
-/
import Mathlib
import Submission.Work.DSTR.M110.SplitCase.Basic
import Submission.Work.DSTR.M110.SplitCase.GaloisPart
import Submission.Work.DSTR.M110.SplitCase.TorusConj
import Submission.Work.DSTR.M110.SplitCase.FixedField
import Submission.Work.DSTR.M110.SplitCase.CardRangeDefs
import Submission.Work.DSTR.M110.SplitCase.phi_ne_neg_one
import Submission.Work.DSTR.M110.SplitCase.sq_injOn_range_phi
import Submission.Work.DSTR.M110.SplitCase.card_ker_phiHom

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110.SplitCase

open Work.AUTL2 Work.DSTR.M110.SplitAux

/-! ## The conjugation formula -/

/-- `dil a` is the permutation `x ↦ a²x`, i.e. `smulHom (a²)`. -/
lemma dil_eq_smulHom (F : Type*) [Field F] [DecidableEq F] (a : Fˣ) :
    dil F a = smulHom F (a ^ 2) := by
  rw [Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun x => ?_⟩
  · rw [dil_infty, smulHom_apply_infty]
  · rw [dil_formula, smulHom_apply_some, Units.val_pow_eq_pow_val]

/-- `galHom σ` conjugates the diagonal torus, in the "commuting" form: `galHom σ` moves past
`smulHom b` at the cost of applying `σ` to `b`. -/
lemma galHom_mul_smulHom (F : Type*) [Field F] [DecidableEq F] (σ : F ≃+* F) (b : Fˣ) :
    galHom F σ * smulHom F b = smulHom F (unitMap F σ b) * galHom F σ := by
  calc galHom F σ * smulHom F b
      = galHom F σ * smulHom F b * (galHom F σ)⁻¹ * galHom F σ := by group
    _ = smulHom F (unitMap F σ b) * galHom F σ := by rw [galHom_conj_smulHom]

/-- **The conjugation formula**: conjugating `smulHom a * galHom σ` by `dil u` produces
`smulHom (a · (u/σu)²) * galHom σ`. -/
lemma dil_conj (F : Type*) [Field F] [DecidableEq F] (σ : F ≃+* F) (a u : Fˣ) :
    dil F u * (smulHom F a * galHom F σ) * (dil F u)⁻¹
      = smulHom F (a * (phiHom F σ u) ^ 2) * galHom F σ := by
  rw [dil_eq_smulHom F u]
  calc smulHom F (u ^ 2) * (smulHom F a * galHom F σ) * (smulHom F (u ^ 2))⁻¹
      = smulHom F (u ^ 2 * a) * (galHom F σ * smulHom F ((u ^ 2)⁻¹)) := by
          rw [map_mul, map_inv]; group
    _ = smulHom F (u ^ 2 * a) * (smulHom F (unitMap F σ ((u ^ 2)⁻¹)) * galHom F σ) := by
          rw [galHom_mul_smulHom]
    _ = smulHom F (u ^ 2 * a * unitMap F σ ((u ^ 2)⁻¹)) * galHom F σ := by
          rw [← mul_assoc, ← map_mul]
    _ = smulHom F (a * (phiHom F σ u) ^ 2) * galHom F σ := by
          congr 2
          rw [unitMap_inv, unitMap_pow, phiHom_apply, ← inv_pow, pow_two, pow_two, pow_two]
          ac_rfl

/-! ## Counting the range -/

/-- Multiplying by `a` and squaring is injective on the range of `phiHom σ` (as `-1` is not in
that range), hence it does not change the number of values. -/
theorem card_range_mul_sq (F : Type*) [Field F] (σ : F ≃+* F)
    (hneg : ∀ u : Fˣ, phiHom F σ u ≠ -1) (a : Fˣ) :
    Nat.card ↥(Set.range fun u : Fˣ => a * (phiHom F σ u) ^ 2)
      = Nat.card ↥(phiHom F σ).range := by
  have hinj : Function.Injective
      (fun c : ↥(phiHom F σ).range => a * (c : Fˣ) ^ 2) := by
    intro c d hcd
    apply Subtype.ext
    have h2 : (c : Fˣ) ^ 2 = (d : Fˣ) ^ 2 := mul_left_cancel hcd
    exact sq_injOn_range_phi F σ hneg c.2 d.2 h2
  have hset : Set.range (fun u : Fˣ => a * (phiHom F σ u) ^ 2)
      = Set.range (fun c : ↥(phiHom F σ).range => a * (c : Fˣ) ^ 2) := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨⟨phiHom F σ u, MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩, ?_⟩
      simp
    · rintro ⟨c, rfl⟩
      obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp c.2
      refine ⟨u, ?_⟩
      simp only [hu]
  rw [hset]
  have h := Nat.card_image_of_injective hinj (Set.univ : Set ↥(phiHom F σ).range)
  rw [Set.image_univ] at h
  rw [h, Nat.card_coe_set_eq, Set.ncard_univ]

/-- The range of `phiHom σ` has `(p^k - 1)/(p^(k/r) - 1)` elements: it is the quotient of `Fˣ`
(cyclic of order `p^k - 1`) by the kernel, which is the unit group of the fixed field of `σ`
and so has `p^(k/r) - 1` elements. -/
theorem card_range_phi (p k r : ℕ) [Fact p.Prime] (hk : 1 ≤ k) (hr : r.Prime)
    (σ : GaloisField p k ≃+* GaloisField p k) (hσ : orderOf σ = r) :
    Nat.card ↥(phiHom (GaloisField p k) σ).range = (p ^ k - 1) / (p ^ (k / r) - 1) := by
  classical
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hcardF : Nat.card (GaloisField p k)ˣ = p ^ k - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
      GaloisField.card p k (by omega)]
  have hker : Nat.card ↥(phiHom (GaloisField p k) σ).ker = p ^ (k / r) - 1 :=
    card_ker_phiHom p k r hk hr σ hσ
  have hmul : Nat.card ↥(phiHom (GaloisField p k) σ).ker *
      Nat.card ↥(phiHom (GaloisField p k) σ).range = Nat.card (GaloisField p k)ˣ :=
    Subgroup.card_ker_mul_card_range _
  have hpos : 0 < Nat.card ↥(phiHom (GaloisField p k) σ).ker := by
    haveI : Nonempty ↥(phiHom (GaloisField p k) σ).ker :=
      ⟨1, (phiHom (GaloisField p k) σ).ker.one_mem⟩
    exact Nat.card_pos
  rw [hcardF, hker] at hmul
  rw [← hmul]
  exact (Nat.mul_div_cancel_left (Nat.card ↥(phiHom (GaloisField p k) σ).range)
    (by rw [← hker]; exact hpos)).symm

/-- **The number of conjugates.**  The `dil(Fˣ)`-conjugates of `smulHom a * galHom σ` number
`(p^k - 1)/(p^(k/r) - 1)`. -/
theorem card_range_dil_conj (p k r : ℕ) [Fact p.Prime] (hp : Odd p) (hk : 1 ≤ k)
    (hr : r.Prime) (hro : Odd r) [DecidableEq (GaloisField p k)]
    (σ : GaloisField p k ≃+* GaloisField p k) (hσ : orderOf σ = r)
    (a : (GaloisField p k)ˣ) :
    Nat.card ↥(Set.range fun u : (GaloisField p k)ˣ =>
        Work.AUTL2.dil (GaloisField p k) u *
          (Work.DSTR.M110.SplitAux.smulHom (GaloisField p k) a *
            Work.AUTL2.galHom (GaloisField p k) σ) *
          (Work.AUTL2.dil (GaloisField p k) u)⁻¹)
      = (p ^ k - 1) / (p ^ (k / r) - 1) := by
  have hneg : ∀ u : (GaloisField p k)ˣ, phiHom (GaloisField p k) σ u ≠ -1 :=
    fun u => phi_ne_neg_one p k r hp hk hr hro σ hσ u
  have hfun : (fun u : (GaloisField p k)ˣ =>
        dil (GaloisField p k) u * (smulHom (GaloisField p k) a * galHom (GaloisField p k) σ) *
          (dil (GaloisField p k) u)⁻¹)
      = (fun u : (GaloisField p k)ˣ =>
        smulHom (GaloisField p k) (a * (phiHom (GaloisField p k) σ u) ^ 2) *
          galHom (GaloisField p k) σ) := by
    funext u
    exact dil_conj (GaloisField p k) σ a u
  rw [hfun]
  have hinj : Function.Injective
      (fun c : (GaloisField p k)ˣ =>
        smulHom (GaloisField p k) c * galHom (GaloisField p k) σ) := by
    intro c d h
    apply smulHom_injective (GaloisField p k)
    have h' := congrArg (fun z : Equiv.Perm (P1 (GaloisField p k)) =>
      z * (galHom (GaloisField p k) σ)⁻¹) h
    simpa [mul_assoc] using h'
  have hset : Set.range (fun u : (GaloisField p k)ˣ =>
        smulHom (GaloisField p k) (a * (phiHom (GaloisField p k) σ u) ^ 2) *
          galHom (GaloisField p k) σ)
      = (fun c : (GaloisField p k)ˣ =>
          smulHom (GaloisField p k) c * galHom (GaloisField p k) σ) ''
        Set.range (fun u : (GaloisField p k)ˣ => a * (phiHom (GaloisField p k) σ u) ^ 2) := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨_, ⟨u, rfl⟩, rfl⟩
    · rintro ⟨c, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
  rw [hset]
  rw [Nat.card_image_of_injective hinj]
  rw [card_range_mul_sq (GaloisField p k) σ hneg a, card_range_phi p k r hk hr σ hσ]

end Work.DSTR.M110.SplitCase
