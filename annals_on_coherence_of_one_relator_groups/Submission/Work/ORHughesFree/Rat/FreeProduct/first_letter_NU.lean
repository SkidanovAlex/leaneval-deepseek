import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.NUMonoid

namespace Work.ORHughesFree.Rat.FreeProduct

open Work.ORHughesFree

variable {U : Type} [Group U]

/-- Purely algebraic manipulation in `Rat(U)`: from `actR u a = actR w a'` one recovers
`a'` from `a` using `v = u * w⁻¹`. -/
theorem actR_eq_actR_imp {u w : U} {a a' : RatU U} (h : actR u a = actR w a') :
    a' = actR (u * w⁻¹) a := by
  rw [actR, actR] at h
  rw [actR, mul_inv_rev, inv_inv, RatU.ofGroup_mul, mul_assoc]
  rw [h, ← mul_assoc, ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, one_mul]

/-- An `X`-word of length one cannot be equal (in `XPart`) to an `X`-word of length `≥ 2`. -/
theorem length_eq_of_mk_eq {L L' : NEL (U := U)}
    (h : (Quotient.mk _ L : XPart U) = Quotient.mk _ L') : L.1.length = L'.1.length :=
  relNE_len (Quotient.exact h)

theorem first_letter_NU {U : Type} [Group U] (a a' : Work.ORHughesFree.RatU U)
    (p q : Work.ORHughesFree.Rat.FreeProduct.NU U)
    (h : Work.ORHughesFree.Rat.FreeProduct.NU.Xgen a * p
        = Work.ORHughesFree.Rat.FreeProduct.NU.Xgen a' * q) :
    ∃ v : U, Work.ORHughesFree.Rat.FreeProduct.NU.Xgen a'
        = Work.ORHughesFree.Rat.FreeProduct.NU.Xgen a
          * Work.ORHughesFree.Rat.FreeProduct.NU.Ugen v
      ∧ p = Work.ORHughesFree.Rat.FreeProduct.NU.Ugen v * q := by
  rcases p with u | P
  · rcases q with w | Q
    · -- `p = Ugen u`, `q = Ugen w`
      simp only [NU.Xgen_mul_Ugen] at h
      have h1 : actR u a = actR w a' := NU.Xgen_injective h
      refine ⟨u * w⁻¹, ?_, ?_⟩
      · rw [NU.Xgen_mul_Ugen, NU.Xgen_injective.eq_iff]
        exact actR_eq_actR_imp h1
      · simp
    · -- `p = Ugen u`, `q` in the `X`-part: lengths `1` vs `≥ 2`
      exfalso
      induction Q using Quotient.inductionOn with
      | h M =>
        simp only [NU.Xgen_mul_Ugen, NU.Xgen_mul_mk] at h
        have h' : (Quotient.mk _ (⟨[actR u a], by simp⟩ : NEL (U := U)) : XPart U)
            = Quotient.mk _ (⟨a' :: M.1, by simp⟩ : NEL (U := U)) := Sum.inr.inj h
        have hlen := length_eq_of_mk_eq h'
        simp only [List.length_cons, List.length_nil] at hlen
        have : M.1.length = 0 := by omega
        exact M.2 (List.length_eq_zero_iff.mp this)
  · rcases q with w | Q
    · -- `p` in the `X`-part, `q = Ugen w`: lengths `≥ 2` vs `1`
      exfalso
      induction P using Quotient.inductionOn with
      | h L =>
        simp only [NU.Xgen_mul_Ugen, NU.Xgen_mul_mk] at h
        have h' : (Quotient.mk _ (⟨a :: L.1, by simp⟩ : NEL (U := U)) : XPart U)
            = Quotient.mk _ (⟨[actR w a'], by simp⟩ : NEL (U := U)) := Sum.inr.inj h
        have hlen := length_eq_of_mk_eq h'
        simp only [List.length_cons, List.length_nil] at hlen
        have : L.1.length = 0 := by omega
        exact L.2 (List.length_eq_zero_iff.mp this)
    · -- both in the `X`-part: compare first letters
      induction P using Quotient.inductionOn with
      | h L =>
        induction Q using Quotient.inductionOn with
        | h M =>
          simp only [NU.Xgen_mul_mk] at h
          have h' : (Quotient.mk _ (⟨a :: L.1, by simp⟩ : NEL (U := U)) : XPart U)
              = Quotient.mk _ (⟨a' :: M.1, by simp⟩ : NEL (U := U)) := Sum.inr.inj h
          obtain ⟨v, ha', hL⟩ :=
            relNE_first_letter a a' ⟨L.1, L.2⟩ ⟨M.1, M.2⟩ (Quotient.exact h')
          refine ⟨v, ?_, ?_⟩
          · rw [NU.Xgen_mul_Ugen, NU.Xgen_injective.eq_iff]
            exact ha'
          · rw [NU.Ugen_mul_mk]
            exact congrArg Sum.inr (Quotient.sound hL)

end Work.ORHughesFree.Rat.FreeProduct
