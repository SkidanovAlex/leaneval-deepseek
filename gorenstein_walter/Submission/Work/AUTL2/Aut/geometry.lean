/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 / Aut : the point groups of `PSL(2,q)`

Foundations for the reconstruction of an automorphism of `PSL(2,q)` from its action on `ℙ¹(F)`.

For `F = GF(p^k)` (`p` odd, `q = p^k ≥ 5`):

* `Work.AUTL2.Aut.exists_fixed_point_of_card_prime_pow`: a `p`-subgroup of `Equiv.Perm X` has a
  fixed point on any finite set whose cardinality is prime to `p`;
* `Work.AUTL2.Aut.card_P1`, `Work.AUTL2.Aut.card_translSub`: the cardinalities of the projective
  line and of the translation group;
* `Work.AUTL2.Aut.eqTranslSub`: a subgroup of `pslImage F` of cardinality `p ^ k` all of whose
  elements fix `∞` is the translation group;
* `Work.AUTL2.Aut.Upt x`: the subgroup of `pslImage F` of cardinality `p ^ k` whose unique fixed
  point is `x`, obtained as the conjugate of the translation group by any element of `pslImage F`
  sending `x` to `∞` (`Work.AUTL2.Aut.gammaPt`).

The deeper properties of the family `Upt` are `Work.AUTL2.Aut.pointGroup`
(uniqueness of the point group of a point), `Work.AUTL2.Aut.uptConj` (equivariance) and
`Work.AUTL2.Aut.uptFixUnique` (an order `p^k` subgroup of `pslImage F` has at most one fixed
point).
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Mobius
import Submission.Work.AUTL2.Stabilizer
import Submission.Work.AUTL2.Normalizer.Defs
import Submission.Work.AUTL2.Normalizer.le_pgammaL
import Submission.Work.AUTL2.Aut.images

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint Subgroup

namespace Work.AUTL2.Aut

open Work.AUTL2

/-! ## `p`-subgroups of a permutation group have a fixed point on a set of prime-to-`p` size -/

/-- A subgroup of `Equiv.Perm X` of cardinality `p ^ k` (`p` prime) has a fixed point on any
finite set `X` whose cardinality is not divisible by `p`. -/
theorem exists_fixed_point_of_card_prime_pow {X : Type*} [Fintype X]
    (H : Subgroup (Equiv.Perm X)) (p k : ℕ) (hp : p.Prime) (hcard : Nat.card H = p ^ k)
    (hdvd : ¬ p ∣ Nat.card X) : ∃ x : X, ∀ g ∈ H, g x = x := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := (IsPGroup.of_card hcard).nonempty_fixed_point_of_prime_not_dvd_card X hdvd
  exact ⟨x, fun g hg => (MulAction.mem_fixedPoints.mp hx) ⟨g, hg⟩⟩

/-! ## Cardinalities of `ℙ¹(F)` and of the translation group -/

/-- The projective line over `GF(p^k)` has `p ^ k + 1` points. -/
theorem card_P1 (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)] (hq : 5 ≤ p ^ k) :
    Nat.card (P1 (GaloisField p k)) = p ^ k + 1 := by
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  have h1 : Nat.card (P1 (GaloisField p k)) = Fintype.card (P1 (GaloisField p k)) :=
    Nat.card_eq_fintype_card
  have h2 : Fintype.card (P1 (GaloisField p k)) = Fintype.card (GaloisField p k) + 1 :=
    Fintype.card_option
  have h3 : (Fintype.card (GaloisField p k) : ℕ) = p ^ k := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p k hk
  omega

/-- The translation group `{x ↦ x + b}` has `p ^ k` elements. -/
theorem card_translSub (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    [DecidableEq (GaloisField p k)] (hq : 5 ≤ p ^ k) :
    Nat.card (Normalizer.translSub (GaloisField p k)) = p ^ k := by
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  have hinj : Function.Injective (Normalizer.translHom (GaloisField p k)) := by
    intro a b hab
    exact Multiplicative.toAdd.injective (Normalizer.transl_injective _ hab)
  have h1 : Nat.card (Normalizer.translSub (GaloisField p k)) =
      Nat.card (Multiplicative (GaloisField p k)) :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  rw [h1, Nat.card_congr (Multiplicative.ofAdd (α := GaloisField p k)).symm,
    GaloisField.card p k hk]

/-! ## The key structural lemma -/

/-- **Key structural lemma.**  A subgroup of `pslImage F` of cardinality `p ^ k` (where
`F = GF(p^k)`, `p` odd) all of whose elements fix `∞` is the translation group
`{x ↦ x + b}`.

Indeed an element of `pslImage F` fixing `∞` is affine, `x ↦ a²x + b` (`element_fixing_infty`);
if `a² ≠ 1` it has exactly two fixed points on `ℙ¹(F)`, namely `∞` and `-b/(a²-1)`.  As `H` is a
`p`-group, any `g ∈ H` has `p`-power order, so the cyclic group `⟨g⟩` acting on the `p ^ k + 1`
points of `ℙ¹(F)` has a number of fixed points congruent to `p ^ k + 1 ≡ 1` modulo `p`
(`IsPGroup.card_modEq_card_fixedPoints`); but that number is `2`, forcing `p ∣ 1`, a
contradiction.  Hence `a² = 1` for every `g ∈ H`, i.e. `H ≤ translSub`, and since both have
cardinality `p ^ k` the two are equal. -/
theorem eqTranslSub (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    [DecidableEq (GaloisField p k)] (hp : Odd p) (hq : 5 ≤ p ^ k)
    (H : Subgroup (Equiv.Perm (P1 (GaloisField p k))))
    (hH : H ≤ pslImage (GaloisField p k)) (hcard : Nat.card H = p ^ k)
    (hfix : ∀ g ∈ H, g OnePoint.infty = OnePoint.infty) :
    H = Normalizer.translSub (GaloisField p k) := by
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  have hle : H ≤ Normalizer.translSub (GaloisField p k) := by
    intro g hg
    obtain ⟨a, b, hab⟩ := element_fixing_infty (GaloisField p k) g (hH hg) (hfix g hg)
    by_cases ha : (↑a : GaloisField p k) ^ 2 = 1
    · have hg_eq : g = transl (GaloisField p k) b := by
        ext x
        rcases x with _ | x
        · change g ∞ = transl (GaloisField p k) b ∞
          rw [hfix g hg, transl_infty]
        · change g ((x : GaloisField p k) : P1 (GaloisField p k)) =
            transl (GaloisField p k) b ((x : GaloisField p k) : P1 (GaloisField p k))
          rw [hab x, transl_formula, ha, one_mul]
      rw [hg_eq]
      exact Normalizer.transl_mem_translSub (GaloisField p k) b
    · exfalso
      have hden : (↑a : GaloisField p k) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr ha
      set x0 : GaloisField p k := -b / ((↑a : GaloisField p k) ^ 2 - 1) with hx0def
      have hx0fix : g ((x0 : GaloisField p k) : P1 (GaloisField p k)) =
          (x0 : GaloisField p k) := by
        rw [hab x0, hx0def]
        congr 1
        field_simp
        ring
      -- powers of `g` fix every point that `g` fixes
      have hpow : ∀ (y : P1 (GaloisField p k)), g y = y → ∀ n : ℤ, (g ^ n) y = y := by
        intro y hy n
        have hmem : g ∈ MulAction.stabilizer (Equiv.Perm (P1 (GaloisField p k))) y :=
          MulAction.mem_stabilizer_iff.mpr hy
        exact MulAction.mem_stabilizer_iff.mp
          (Subgroup.zpow_mem (MulAction.stabilizer (Equiv.Perm (P1 (GaloisField p k))) y)
            hmem n)
      -- the fixed points of the cyclic group `⟨g⟩` are exactly `∞` and `x₀`
      have hfixset : MulAction.fixedPoints ↥(Subgroup.zpowers g) (P1 (GaloisField p k)) =
          ({(∞ : P1 (GaloisField p k)), ((x0 : GaloisField p k) : P1 (GaloisField p k))} :
            Set (P1 (GaloisField p k))) := by
        ext y
        rw [MulAction.mem_fixedPoints, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro hy
          have hgy : g y = y := hy ⟨g, Subgroup.mem_zpowers g⟩
          rcases y with _ | x
          · exact Or.inl rfl
          · refine Or.inr ?_
            suffices h : x = x0 by
              show ((x : GaloisField p k) : P1 (GaloisField p k)) =
                ((x0 : GaloisField p k) : P1 (GaloisField p k))
              rw [h]
            have hx : (↑a : GaloisField p k) ^ 2 * x + b = x := by
              have h2 : g ((x : GaloisField p k) : P1 (GaloisField p k)) =
                  ((x : GaloisField p k) : P1 (GaloisField p k)) := hgy
              rw [hab x] at h2
              exact OnePoint.coe_eq_coe.mp h2
            rw [hx0def, eq_div_iff hden]
            linear_combination hx
        · rintro (rfl | rfl)
          · intro u
            obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp u.2
            calc u • (∞ : P1 (GaloisField p k)) =
                (u : Equiv.Perm (P1 (GaloisField p k))) ∞ := rfl
              _ = (g ^ m) ∞ := by rw [← hm]
              _ = ∞ := hpow ∞ (hfix g hg) m
          · intro u
            obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp u.2
            calc u • ((x0 : GaloisField p k) : P1 (GaloisField p k)) =
                (u : Equiv.Perm (P1 (GaloisField p k)))
                  ((x0 : GaloisField p k) : P1 (GaloisField p k)) := rfl
              _ = (g ^ m) ((x0 : GaloisField p k) : P1 (GaloisField p k)) := by rw [← hm]
              _ = ((x0 : GaloisField p k) : P1 (GaloisField p k)) :=
                  hpow ((x0 : GaloisField p k) : P1 (GaloisField p k)) hx0fix m
      have hgcard : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers g)
          (P1 (GaloisField p k))) = 2 := by
        rw [Nat.card_coe_set_eq, hfixset]
        exact Set.ncard_pair (OnePoint.infty_ne_coe x0)
      -- `⟨g⟩` is a `p`-group
      have horder : orderOf g ∣ p ^ k := by
        rw [← hcard]
        exact Subgroup.orderOf_dvd_natCard H hg
      obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp horder
      have hpgroup : IsPGroup p ↥(Subgroup.zpowers g) :=
        IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
      -- the congruence counting fixed points contradicts `|ℙ¹(F)| = p ^ k + 1`
      have hcong := hpgroup.card_modEq_card_fixedPoints (P1 (GaloisField p k))
      rw [card_P1 p k hq, hgcard] at hcong
      have h1 : p ^ k ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self p hk)
      have h2 : p ^ k + 1 ≡ 1 [MOD p] := by simpa using h1.add_right 1
      have h12 : (1 : ℕ) ≡ 2 [MOD p] := h2.symm.trans hcong
      have hdvd : p ∣ 1 := (Nat.modEq_iff_dvd' (by norm_num)).mp h12
      have hle1 : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      omega
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_translSub p k hq, hcard]

/-! ## The point groups -/

variable (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)] [DecidableEq (GaloisField p k)]

/-- An element of `pslImage F` moving a given point `x` to `∞`. -/
noncomputable def gammaPt (x : P1 (GaloisField p k)) : Equiv.Perm (P1 (GaloisField p k)) :=
  Classical.choose (exists_pslImage_map_to_infty (GaloisField p k) x)

lemma gammaPt_mem (x : P1 (GaloisField p k)) : gammaPt p k x ∈ pslImage (GaloisField p k) :=
  (Classical.choose_spec (exists_pslImage_map_to_infty (GaloisField p k) x)).1

lemma gammaPt_apply (x : P1 (GaloisField p k)) : gammaPt p k x x = ∞ :=
  (Classical.choose_spec (exists_pslImage_map_to_infty (GaloisField p k) x)).2

/-- The point group of `x : ℙ¹(F)`: the conjugate of the translation group by `gammaPt p k x`.
Its unique fixed point is `x`. -/
noncomputable def Upt (x : P1 (GaloisField p k)) :
    Subgroup (Equiv.Perm (P1 (GaloisField p k))) :=
  (Normalizer.translSub (GaloisField p k)).map (MulAut.conj (gammaPt p k x)⁻¹)

lemma Upt_def (x : P1 (GaloisField p k)) : Upt p k x =
    (Normalizer.translSub (GaloisField p k)).map (MulAut.conj (gammaPt p k x)⁻¹) := rfl

lemma Upt_le_pslImage (x : P1 (GaloisField p k)) :
    Upt p k x ≤ pslImage (GaloisField p k) := by
  rintro g ⟨t, ht, rfl⟩
  show MulAut.conj (gammaPt p k x)⁻¹ t ∈ pslImage (GaloisField p k)
  rw [MulAut.conj_apply, inv_inv]
  exact mul_mem (mul_mem (inv_mem (gammaPt_mem p k x))
    (Normalizer.translSub_le_pslImage (GaloisField p k) ht)) (gammaPt_mem p k x)

lemma Upt_card (hq : 5 ≤ p ^ k) (x : P1 (GaloisField p k)) :
    Nat.card (Upt p k x) = p ^ k := by
  have h : Upt p k x = (Normalizer.translSub (GaloisField p k)).map
      (↑(MulAut.conj (gammaPt p k x)⁻¹) : Equiv.Perm (P1 (GaloisField p k)) →*
        Equiv.Perm (P1 (GaloisField p k))) := Upt_def p k x
  rw [h, Subgroup.card_map_of_injective (f := (↑(MulAut.conj (gammaPt p k x)⁻¹) :
      Equiv.Perm (P1 (GaloisField p k)) →* Equiv.Perm (P1 (GaloisField p k))))
    (MulAut.conj (gammaPt p k x)⁻¹).injective, card_translSub p k hq]

lemma Upt_fixes (x : P1 (GaloisField p k)) : ∀ g ∈ Upt p k x, g x = x := by
  rintro g ⟨t, ht, rfl⟩
  show MulAut.conj (gammaPt p k x)⁻¹ t x = x
  rw [MulAut.conj_apply, inv_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    gammaPt_apply p k x, Normalizer.mem_translSub_fixes_infty (GaloisField p k) ht]
  rw [show (∞ : P1 (GaloisField p k)) = gammaPt p k x x from (gammaPt_apply p k x).symm,
    Equiv.Perm.inv_def, Equiv.symm_apply_apply]

end Work.AUTL2.Aut
