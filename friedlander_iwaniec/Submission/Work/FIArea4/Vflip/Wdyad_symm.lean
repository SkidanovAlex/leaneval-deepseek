/-
# The `r ↔ s` symmetry of the dyadic dual variance `Wdyad`

Friedlander–Iwaniec (11.14)–(11.24): the dyadic dual variance

`W(D) = ∑_{R<r≤2R} ∑_{S<s≤2S} |∑_{D<d≤2D} ∑_{a<d} γ_{a d} M((d,a),(r,s))|²`

(with `M((d,a),(r,s))` the indicator of `(r,d)=1`, `s ≡ r a (mod d)` times the Jacobi symbol
`(r | d')`, `d' = oddPart d`) is invariant under exchanging the roles of `r` and `s`, provided the
coefficients `γ_{a d}` are supported on the classes `(a,d)=1`: one has

`Wdyad D R S γ = Wdyad D S R γ'`,  `γ'_{b d} = [ (b,d)=1 ] γ_{b⁻¹ mod d, d} · (b | d')`.

The proof is the classical change of summation variable `a ↔ a⁻¹ (mod d)` together with Jacobi
reciprocity `(a⁻¹ | d') (s | d') = (r | d')`, valid because `s ≡ r a (mod d)` and `d' ∣ d`.
-/
import Mathlib
import Submission.Work.FIArea4.prop_11_1_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The `r ↔ s` transformation of the coefficient matrix:
`γ'_{b d} = [ (b,d)=1 ] γ_{b⁻¹ mod d, d} · (b | d')`. -/
def gammaF (γ : ℕ → ℕ → ℂ) (b d : ℕ) : ℂ :=
  if Nat.Coprime b d then γ (((b : ZMod d)⁻¹).val) d
      * (jacobiSym (b : ℤ) (Work.FIPlan.oddPart d) : ℂ) else 0

/-- The class sum over the dyadic `d`-range defining `Wdyad`:
`TZ D γ r s = ∑_{D<d≤2D} ∑_{a<d} γ_{a d} M((d,a),(r,s))`. -/
def TZ (D : ℕ) (γ : ℕ → ℕ → ℂ) (r s : ℕ) : ℂ :=
  ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
    γ a d * Work.FIArea4.Mentry d a r s

/-! ### Elementary helpers -/

/-- `(if P then x else 0) * (if Q then y else 0) = if Q then (if P then x*y else 0) else 0`. -/
lemma ite_mul_ite_zero (P Q : Prop) [Decidable P] [Decidable Q] (x y : ℂ) :
    (if P then x else 0) * (if Q then y else 0) = if Q then (if P then x * y else 0) else 0 := by
  by_cases hq : Q
  · simp only [hq, if_true]; by_cases hp : P <;> simp [hp]
  · simp only [hq, if_false, mul_zero]

/-- Collapsing a sum over `range d` against the condition `(a : ZMod d) = x`. -/
lemma sum_range_ite_zmod {d : ℕ} [NeZero d] (x : ZMod d) (F : ℕ → ℂ) :
    (∑ a ∈ Finset.range d, if (a : ZMod d) = x then F a else 0) = F x.val := by
  rw [Finset.sum_eq_single x.val]
  · rw [if_pos (ZMod.natCast_zmod_val x)]
  · intro a ha hne
    rw [if_neg]
    intro h
    apply hne
    have h1 : (a : ZMod d).val = x.val := by rw [h]
    rwa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)] at h1
  · intro h
    exact absurd (Finset.mem_range.mpr (ZMod.val_lt x)) h

/-- The odd part of `d` divides `d`. -/
lemma oddPart_dvd_local (d : ℕ) : Work.FIPlan.oddPart d ∣ d := Nat.ordCompl_dvd d 2

/-! ### Collapsing the two class sums -/

/-- The class sum over `a` collapses to the single class `a ≡ r⁻¹ s (mod d)`. -/
lemma Mentry_sum_rhs {d : ℕ} [NeZero d] (γ : ℕ → ℕ → ℂ) (r s : ℕ) :
    (∑ a ∈ Finset.range d, γ a d * Work.FIArea4.Mentry d a r s) =
      (if Nat.Coprime r d then γ (((r : ZMod d)⁻¹ * (s : ZMod d)).val) d
        * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ) else 0) := by
  by_cases hr : Nat.Coprime r d
  · have hRunit : IsUnit (r : ZMod d) := (ZMod.isUnit_iff_coprime r d).mpr hr
    have hiff : ∀ a : ℕ, ((s : ZMod d) = (r : ZMod d) * (a : ZMod d)) ↔
        ((a : ZMod d) = (r : ZMod d)⁻¹ * (s : ZMod d)) := by
      intro a
      constructor
      · intro h
        calc (a : ZMod d) = 1 * (a : ZMod d) := (one_mul _).symm
          _ = ((r : ZMod d)⁻¹ * (r : ZMod d)) * (a : ZMod d) := by
                rw [ZMod.inv_mul_of_unit _ hRunit]
          _ = (r : ZMod d)⁻¹ * ((r : ZMod d) * (a : ZMod d)) := by ring
          _ = (r : ZMod d)⁻¹ * (s : ZMod d) := by rw [← h]
      · intro h
        calc (s : ZMod d) = (r : ZMod d) * ((r : ZMod d)⁻¹ * (s : ZMod d)) := by
                rw [← mul_assoc, ZMod.mul_inv_of_unit _ hRunit, one_mul]
          _ = (r : ZMod d) * (a : ZMod d) := by rw [← h]
    rw [if_pos hr]
    rw [show (∑ a ∈ Finset.range d, γ a d * Work.FIArea4.Mentry d a r s)
        = ∑ a ∈ Finset.range d,
            (if (a : ZMod d) = (r : ZMod d)⁻¹ * (s : ZMod d) then
              γ a d * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ) else 0) from ?_]
    · exact sum_range_ite_zmod _ _
    · apply Finset.sum_congr rfl; intro a _
      have hcond : (Nat.Coprime r d ∧ (s : ZMod d) = (r : ZMod d) * (a : ZMod d)) ↔
          ((a : ZMod d) = (r : ZMod d)⁻¹ * (s : ZMod d)) := by
        rw [show (Nat.Coprime r d) = True from propext (iff_true_intro hr), true_and]
        exact hiff a
      rw [Work.FIArea4.Mentry, mul_ite, mul_zero, if_congr hcond rfl rfl]
  · rw [if_neg hr]
    apply Finset.sum_eq_zero; intro a _
    rw [Work.FIArea4.Mentry, if_neg (fun h => hr h.1), mul_zero]

/-- The class sum over `b` of the transformed coefficients collapses to
`b ≡ s⁻¹ r (mod d)`. -/
lemma Mentry_sum_lhs {d : ℕ} [NeZero d] (γ : ℕ → ℕ → ℂ) (r s : ℕ) :
    (∑ b ∈ Finset.range d, gammaF γ b d * Work.FIArea4.Mentry d b s r) =
      (if Nat.Coprime s d then gammaF γ (((s : ZMod d)⁻¹ * (r : ZMod d)).val) d
        * (jacobiSym (s : ℤ) (Work.FIPlan.oddPart d) : ℂ) else 0) := by
  by_cases hs : Nat.Coprime s d
  · have hSunit : IsUnit (s : ZMod d) := (ZMod.isUnit_iff_coprime s d).mpr hs
    rw [if_pos hs]
    rw [show (∑ b ∈ Finset.range d, gammaF γ b d * Work.FIArea4.Mentry d b s r)
        = ∑ b ∈ Finset.range d,
            (if (b : ZMod d) = (s : ZMod d)⁻¹ * (r : ZMod d) then
              (if Nat.Coprime b d then γ (((b : ZMod d)⁻¹).val) d
                * (jacobiSym (b : ℤ) (Work.FIPlan.oddPart d) : ℂ)
                * (jacobiSym (s : ℤ) (Work.FIPlan.oddPart d) : ℂ) else 0) else 0) from ?_]
    · rw [sum_range_ite_zmod]
      rw [gammaF, ite_mul, zero_mul]
    · apply Finset.sum_congr rfl; intro b _
      have hcond : (Nat.Coprime s d ∧ (r : ZMod d) = (s : ZMod d) * (b : ZMod d)) ↔
          ((b : ZMod d) = (s : ZMod d)⁻¹ * (r : ZMod d)) := by
        rw [show (Nat.Coprime s d) = True from propext (iff_true_intro hs), true_and]
        constructor
        · intro h
          calc (b : ZMod d) = 1 * (b : ZMod d) := (one_mul _).symm
            _ = ((s : ZMod d)⁻¹ * (s : ZMod d)) * (b : ZMod d) := by
                  rw [ZMod.inv_mul_of_unit _ hSunit]
            _ = (s : ZMod d)⁻¹ * ((s : ZMod d) * (b : ZMod d)) := by ring
            _ = (s : ZMod d)⁻¹ * (r : ZMod d) := by rw [← h]
        · intro h
          calc (r : ZMod d) = (s : ZMod d) * ((s : ZMod d)⁻¹ * (r : ZMod d)) := by
                  rw [← mul_assoc, ZMod.mul_inv_of_unit _ hSunit, one_mul]
            _ = (s : ZMod d) * (b : ZMod d) := by rw [← h]
      rw [gammaF, Work.FIArea4.Mentry, ite_mul_ite_zero, if_congr hcond rfl rfl]
  · rw [if_neg hs]
    apply Finset.sum_eq_zero; intro b _
    rw [Work.FIArea4.Mentry, if_neg (fun h => hs h.1), mul_zero]

/-- **The per-modulus identity.**  The two class sums (over `a` with `Mentry d a r s`, and over `b`
with the transformed coefficients times `Mentry d b s r`) are equal, given the support hypothesis
`γ_{a d} ≠ 0 → (a,d)=1`. -/
lemma Mentry_sum_eq (d : ℕ) [NeZero d] (γ : ℕ → ℕ → ℂ)
    (hγ : ∀ a d, γ a d ≠ 0 → Nat.Coprime a d) (r s : ℕ) :
    (∑ a ∈ Finset.range d, γ a d * Work.FIArea4.Mentry d a r s)
      = (∑ b ∈ Finset.range d, gammaF γ b d * Work.FIArea4.Mentry d b s r) := by
  rw [Mentry_sum_rhs γ r s, Mentry_sum_lhs γ r s]
  by_cases hs : Nat.Coprime s d
  · have hSunit : IsUnit (s : ZMod d) := (ZMod.isUnit_iff_coprime s d).mpr hs
    rw [if_pos hs]
    set b0 : ℕ := ((s : ZMod d)⁻¹ * (r : ZMod d)).val with hb0def
    have hb0val : (b0 : ZMod d) = (s : ZMod d)⁻¹ * (r : ZMod d) := by
      rw [hb0def]; exact ZMod.natCast_zmod_val _
    have hb0cop : Nat.Coprime b0 d ↔ Nat.Coprime r d := by
      rw [← ZMod.isUnit_iff_coprime b0 d, ← ZMod.isUnit_iff_coprime r d, hb0val]
      have hSinv : IsUnit ((s : ZMod d)⁻¹) := by
        have h1 : IsUnit ((s : ZMod d)⁻¹ * (s : ZMod d)) := by
          rw [ZMod.inv_mul_of_unit _ hSunit]; exact isUnit_one
        exact (IsUnit.mul_iff.mp h1).1
      constructor
      · intro h
        have h2 : IsUnit ((s : ZMod d) * ((s : ZMod d)⁻¹ * (r : ZMod d))) := hSunit.mul h
        rw [← mul_assoc, ZMod.mul_inv_of_unit _ hSunit, one_mul] at h2
        exact h2
      · intro h; exact hSinv.mul h
    rw [gammaF, ite_mul, zero_mul]
    by_cases hc : Nat.Coprime b0 d
    · have hcr : Nat.Coprime r d := hb0cop.mp hc
      have hRunit : IsUnit (r : ZMod d) := (ZMod.isUnit_iff_coprime r d).mpr hcr
      rw [if_pos hc, if_pos hcr]
      have hinv : (b0 : ZMod d)⁻¹ = (r : ZMod d)⁻¹ * (s : ZMod d) := by
        rw [hb0val]
        refine ZMod.inv_eq_of_mul_eq_one d _ _ ?_
        rw [show (s : ZMod d)⁻¹ * (r : ZMod d) * ((r : ZMod d)⁻¹ * (s : ZMod d))
            = ((s : ZMod d)⁻¹ * (s : ZMod d)) * ((r : ZMod d) * (r : ZMod d)⁻¹) from by ring,
          ZMod.inv_mul_of_unit _ hSunit, ZMod.mul_inv_of_unit _ hRunit, one_mul]
      have hval : ((b0 : ZMod d)⁻¹).val = (((r : ZMod d)⁻¹ * (s : ZMod d)).val) := by
        rw [hinv]
      have hbs : (b0 : ZMod d) * (s : ZMod d) = (r : ZMod d) := by
        rw [hb0val]
        rw [show (s : ZMod d)⁻¹ * (r : ZMod d) * (s : ZMod d)
            = ((s : ZMod d)⁻¹ * (s : ZMod d)) * (r : ZMod d) from by ring,
          ZMod.inv_mul_of_unit _ hSunit, one_mul]
      have hmodd : (b0 * s) ≡ r [MOD d] := by
        rw [← Nat.cast_mul] at hbs
        exact (ZMod.natCast_eq_natCast_iff (b0 * s) r d).mp hbs
      have hMeq : (b0 * s) ≡ r [MOD Work.FIPlan.oddPart d] :=
        Nat.ModEq.of_dvd (oddPart_dvd_local d) hmodd
      have hne : ((b0 * s : ℕ) : ℤ) % ((Work.FIPlan.oddPart d : ℕ) : ℤ)
          = ((r : ℕ) : ℤ) % ((Work.FIPlan.oddPart d : ℕ) : ℤ) := by
        rw [← Int.natCast_emod, ← Int.natCast_emod]
        exact congrArg (fun k : ℕ => (k : ℤ)) hMeq
      have hJ_int : jacobiSym (b0 : ℤ) (Work.FIPlan.oddPart d)
            * jacobiSym (s : ℤ) (Work.FIPlan.oddPart d)
          = jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) := by
        rw [← jacobiSym.mul_left, ← Nat.cast_mul]
        exact jacobiSym.mod_left' hne
      have hJac : (jacobiSym (b0 : ℤ) (Work.FIPlan.oddPart d) : ℂ)
            * (jacobiSym (s : ℤ) (Work.FIPlan.oddPart d) : ℂ)
          = (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℂ) := by
        rw [← Int.cast_mul, hJ_int]
      rw [hval, mul_assoc, hJac]
    · have hcr : ¬ Nat.Coprime r d := fun h => hc (hb0cop.mpr h)
      rw [if_neg hc, if_neg hcr]
  · rw [if_neg hs]
    by_cases hr : Nat.Coprime r d
    · have hRunit : IsUnit (r : ZMod d) := (ZMod.isUnit_iff_coprime r d).mpr hr
      rw [if_pos hr]
      have hna0 : ¬ Nat.Coprime (((r : ZMod d)⁻¹ * (s : ZMod d)).val) d := by
        rw [← ZMod.isUnit_iff_coprime]
        intro hunit
        rw [ZMod.natCast_zmod_val ((r : ZMod d)⁻¹ * (s : ZMod d))] at hunit
        have h3 : IsUnit ((r : ZMod d) * ((r : ZMod d)⁻¹ * (s : ZMod d))) := hRunit.mul hunit
        rw [← mul_assoc, ZMod.mul_inv_of_unit _ hRunit, one_mul] at h3
        exact hs ((ZMod.isUnit_iff_coprime s d).mp h3)
      have hz : γ (((r : ZMod d)⁻¹ * (s : ZMod d)).val) d = 0 := by
        by_contra hne
        exact hna0 (hγ _ _ hne)
      rw [hz, zero_mul]
    · rw [if_neg hr]

/-! ### The symmetry -/

/-- The pointwise symmetry of the class sums: `TZ D γ' s r = TZ D γ r s`. -/
lemma TZ_flip (D : ℕ) (γ : ℕ → ℕ → ℂ)
    (hγ : ∀ a d, γ a d ≠ 0 → Nat.Coprime a d) (r s : ℕ) :
    TZ D (gammaF γ) s r = TZ D γ r s := by
  simp only [TZ]
  apply Finset.sum_congr rfl; intro d hd
  have hdmem : D < d ∧ d ≤ 2 * D := Finset.mem_Ioc.mp hd
  exact (@Mentry_sum_eq d ⟨by omega⟩ γ hγ r s).symm

/-- **Friedlander–Iwaniec, the `r ↔ s` symmetry of the dyadic dual variance.**  For coefficients
supported on the classes `(a,d) = 1`, exchanging `R` and `S` amounts to transforming
`γ_{a d} ↦ [ (a,d)=1 ] γ_{a⁻¹ mod d, d} (a | d')`. -/
theorem Wdyad_symm (D R S : ℕ) (γ : ℕ → ℕ → ℂ)
    (hγ : ∀ a d, γ a d ≠ 0 → Nat.Coprime a d) :
    Work.FIArea4.Wdyad D R S γ = Work.FIArea4.Wdyad D S R (fun b d =>
      if Nat.Coprime b d then γ (((b : ZMod d)⁻¹).val) d * (jacobiSym (b : ℤ) (Work.FIPlan.oddPart d) : ℂ) else 0) := by
  change Work.FIArea4.Wdyad D R S γ = Work.FIArea4.Wdyad D S R (gammaF γ)
  calc Work.FIArea4.Wdyad D R S γ
      = ∑ r ∈ Finset.Ioc R (2 * R), ∑ s ∈ Finset.Ioc S (2 * S),
          Complex.normSq (TZ D γ r s) := rfl
    _ = ∑ s ∈ Finset.Ioc S (2 * S), ∑ r ∈ Finset.Ioc R (2 * R),
          Complex.normSq (TZ D γ r s) := Finset.sum_comm
    _ = ∑ s ∈ Finset.Ioc S (2 * S), ∑ r ∈ Finset.Ioc R (2 * R),
          Complex.normSq (TZ D (gammaF γ) s r) := by
        apply Finset.sum_congr rfl; intro s _
        apply Finset.sum_congr rfl; intro r _
        rw [TZ_flip D γ hγ r s]
    _ = Work.FIArea4.Wdyad D S R (gammaF γ) := rfl

end

end Work.FIArea4.Vflip
