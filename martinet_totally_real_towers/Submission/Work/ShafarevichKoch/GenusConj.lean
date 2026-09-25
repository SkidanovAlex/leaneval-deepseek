import Mathlib
import Submission.Work.ShafarevichKoch.Defs
import Submission.Work.ClassFieldTower.WitnessField
import Submission.Work.ClassFieldTower.int_coords_and_norm
import Submission.Work.ClassFieldTower.span_pair_sq
import Submission.Commons.FieldTheory.Galois.isGalois_of_finrank_eq_two

/-!
# The conjugation of `Kc = ℚ(√-30030)` and of its ring of integers

The genus-theory chapter of `Work.ShafarevichKoch` needs the nontrivial automorphism `σ` of the
imaginary quadratic field `Kc` (complex conjugation) and its action on the ring of integers
`𝓞 Kc = ℤ[√-30030]`.  Since `sc = √-30030` generates `Kc` over `ℚ` (`adjoin_sc_eq_top`) and
`sc² = -30030 ∉ ℚ²`, any `σ ≠ 1` in `Gal(Kc/ℚ)` sends `sc` to `-sc`, so

`σ (a + b·sc) = a - b·sc` and `conjR (a + b·scR) = a - b·scR`.

The main new notion is `IsConjInv J` (`J` is stable under `conjR`), the hypothesis of the
structure theorem for ambiguous ideals (`conjInv_ideal_structure`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower


open Work.ClassFieldTower

instance : IsGalois ℚ Kc :=
  Commons.FieldTheory.Galois.isGalois_of_finrank_eq_two finrank_eq_two (by norm_num)

theorem card_algEquiv_Kc : Nat.card (Kc ≃ₐ[ℚ] Kc) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, finrank_eq_two]

theorem exists_algEquiv_ne_one : ∃ σ : Kc ≃ₐ[ℚ] Kc, σ ≠ 1 := by
  have hcard : Nat.card (Kc ≃ₐ[ℚ] Kc) = 2 := card_algEquiv_Kc
  haveI : Fintype (Kc ≃ₐ[ℚ] Kc) := Fintype.ofFinite _
  have h1 : 1 < Fintype.card (Kc ≃ₐ[ℚ] Kc) := by
    rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  obtain ⟨σ, hσ⟩ := Fintype.exists_ne_of_one_lt_card h1 1
  exact ⟨σ, hσ⟩

noncomputable def conjK : Kc ≃ₐ[ℚ] Kc := Classical.choose exists_algEquiv_ne_one

theorem conjK_ne_one : conjK ≠ 1 := Classical.choose_spec exists_algEquiv_ne_one

theorem eq_one_of_fixes_sc (σ : Kc ≃ₐ[ℚ] Kc) (h : σ sc = sc) : σ = 1 := by
  apply AlgEquiv.ext
  intro z
  have hz : z ∈ Algebra.adjoin ℚ ({sc} : Set Kc) := by
    rw [adjoin_sc_eq_top]; trivial
  induction hz using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff] at hx; subst hx; simpa using h
  | algebraMap r => simp
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]; rfl
  | mul x y hx hy ihx ihy => rw [map_mul, ihx, ihy]; rfl

theorem algEquiv_apply_sc_eq_or (σ : Kc ≃ₐ[ℚ] Kc) : σ sc = sc ∨ σ sc = -sc := by
  have h1 : σ sc * σ sc = sc * sc := by rw [← map_mul, sc_sq_num, map_neg, map_ofNat]
  have h2 : (σ sc - sc) * (σ sc + sc) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (add_eq_zero_iff_eq_neg.mp h)

theorem conjK_apply_sc : conjK sc = -sc := by
  rcases algEquiv_apply_sc_eq_or conjK with h | h
  · exact absurd (eq_one_of_fixes_sc conjK h) conjK_ne_one
  · exact h

theorem conjK_invol (z : Kc) : conjK (conjK z) = z := by
  have hfix : (conjK * conjK) sc = sc := by
    show conjK (conjK sc) = sc
    rw [conjK_apply_sc, map_neg, conjK_apply_sc, neg_neg]
  have hone : conjK * conjK = 1 := eq_one_of_fixes_sc (conjK * conjK) hfix
  have := congrArg (fun e : Kc ≃ₐ[ℚ] Kc => e z) hone
  simpa using this

theorem conjK_apply (a b : ℚ) :
    conjK (algebraMap ℚ Kc a + algebraMap ℚ Kc b * sc)
      = algebraMap ℚ Kc a - algebraMap ℚ Kc b * sc := by
  rw [map_add, map_mul, conjK_apply_sc, AlgEquiv.commutes, AlgEquiv.commutes]
  ring

noncomputable def conjR : 𝓞 Kc ≃+* 𝓞 Kc :=
  RingOfIntegers.mapRingEquiv conjK.toRingEquiv

theorem conjR_apply_coe (z : 𝓞 Kc) : ((conjR z : 𝓞 Kc) : Kc) = conjK z :=
  RingOfIntegers.mapRingEquiv_apply conjK.toRingEquiv z

theorem conjR_apply_scR : conjR scR = -scR := by
  apply Subtype.ext
  show ((conjR scR : 𝓞 Kc) : Kc) = ((-scR : 𝓞 Kc) : Kc)
  rw [conjR_apply_coe]
  push_cast
  exact conjK_apply_sc

theorem conjR_invol (z : 𝓞 Kc) : conjR (conjR z) = z := by
  apply Subtype.ext
  show ((conjR (conjR z) : 𝓞 Kc) : Kc) = (z : Kc)
  rw [conjR_apply_coe, conjR_apply_coe]
  exact conjK_invol z

theorem conjK_mul_self (z : Kc) : z * conjK z = algebraMap ℚ Kc (Algebra.norm ℚ z) := by
  obtain ⟨a, b, rfl⟩ := exists_coords z
  rw [conjK_apply, basisPair_norm]
  push_cast
  have hsq : sc ^ 2 = -algebraMap ℚ Kc (30030 : ℚ) := by
    rw [pow_two, sc_sq_num]; norm_num
  linear_combination (-((algebraMap ℚ Kc) b) ^ 2) * hsq

theorem conjR_apply (a b : ℤ) :
    conjR ((a : 𝓞 Kc) + (b : 𝓞 Kc) * scR) = (a : 𝓞 Kc) - (b : 𝓞 Kc) * scR := by
  rw [map_add, map_mul, conjR_apply_scR]
  rw [show conjR ((a : ℤ) : 𝓞 Kc) = ((a : ℤ) : 𝓞 Kc) from map_intCast conjR a,
    show conjR ((b : ℤ) : 𝓞 Kc) = ((b : ℤ) : 𝓞 Kc) from map_intCast conjR b]
  ring

theorem exists_int_coords (z : 𝓞 Kc) :
    ∃ a b : ℤ, z = (a : 𝓞 Kc) + (b : 𝓞 Kc) * scR := by
  obtain ⟨a, b, hab, -⟩ := int_coords_and_norm z
  refine ⟨a, b, ?_⟩
  have h2 : (((a : 𝓞 Kc) + (b : 𝓞 Kc) * scR : 𝓞 Kc) : Kc)
      = (a : Kc) + (b : Kc) * sc := by
    push_cast
    rfl
  exact Subtype.ext (hab.trans h2.symm)

theorem int_coords_unique {a b a' b' : ℤ}
    (h : (a : 𝓞 Kc) + (b : 𝓞 Kc) * scR = (a' : 𝓞 Kc) + (b' : 𝓞 Kc) * scR) :
    a = a' ∧ b = b' := by
  have hK : algebraMap ℚ Kc (a : ℚ) + algebraMap ℚ Kc (b : ℚ) * sc
      = algebraMap ℚ Kc (a' : ℚ) + algebraMap ℚ Kc (b' : ℚ) * sc := by
    have := congrArg (fun z : 𝓞 Kc => (z : Kc)) h
    push_cast at this
    simpa using this
  by_cases hb : b = b'
  · subst hb
    have ha : (algebraMap ℚ Kc (a : ℚ)) = algebraMap ℚ Kc (a' : ℚ) := by
      linear_combination hK
    exact ⟨by exact_mod_cast (algebraMap ℚ Kc).injective ha, rfl⟩
  · exfalso
    have hne : ((b : ℚ) - b') ≠ 0 := by
      intro h0
      exact hb (by exact_mod_cast (sub_eq_zero.mp h0))
    have hsc : sc = algebraMap ℚ Kc (((a' : ℚ) - a) / ((b : ℚ) - b')) := by
      rw [map_div₀]
      rw [eq_div_iff]
      · push_cast
        linear_combination hK
      · intro hz
        apply hne
        have h2 : algebraMap ℚ Kc ((b : ℚ) - b') = 0 := by simpa using hz
        exact (algebraMap ℚ Kc).injective (by rw [h2, map_zero])
    exact sc_not_rat _ hsc

def IsConjInv (J : Ideal (𝓞 Kc)) : Prop := ∀ z ∈ J, conjR z ∈ J

theorem isConjInv_iff_map_le (J : Ideal (𝓞 Kc)) :
    IsConjInv J ↔ Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) J ≤ J := by
  constructor
  · intro h z hz
    obtain ⟨y, hy, hyz⟩ :=
      (Ideal.mem_map_iff_of_surjective (conjR : 𝓞 Kc →+* 𝓞 Kc) conjR.surjective).mp hz
    rw [← hyz]
    exact h y hy
  · intro h z hz
    exact h (Ideal.mem_map_of_mem (conjR : 𝓞 Kc →+* 𝓞 Kc) hz)

theorem map_conjR_eq_self (J : Ideal (𝓞 Kc)) (h : IsConjInv J) :
    Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) J = J := by
  refine le_antisymm ((isConjInv_iff_map_le J).mp h) ?_
  intro z hz
  have hz1 : conjR z ∈ J := h z hz
  have hmem : conjR (conjR z) ∈ Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) J :=
    Ideal.mem_map_of_mem (conjR : 𝓞 Kc →+* 𝓞 Kc) hz1
  rwa [conjR_invol] at hmem


end Work.ShafarevichKoch
