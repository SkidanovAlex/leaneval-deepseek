/-
  Area C2 (WilC2): the (ring-)first-order sentence "every element is a square or minus a square",
  its realisation, its truth in `ℝ`, and its transfer to every model of `TR`.  This is what makes
  the definable order of a model of `TR` agree with the order of the language of rings.
-/
import Submission.Work.WilC2.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

/-- A `ring`-formula with free variables `(Empty ⊕ Fin 1) ⊕ Fin 1`: the middle block is `x`
and the last block is `z`; the formula is `z * z = x ∨ z * z = -x`. -/
def sqOrNegSqBody : Language.ring.Formula ((Empty ⊕ Fin 1) ⊕ Fin 1) :=
  (Term.equal (Term.var (Sum.inr (0 : Fin 1)) * Term.var (Sum.inr (0 : Fin 1)))
      (Term.var (Sum.inl (Sum.inr (0 : Fin 1))))) ⊔
    (Term.equal (Term.var (Sum.inr (0 : Fin 1)) * Term.var (Sum.inr (0 : Fin 1)))
      (-Term.var (Sum.inl (Sum.inr (0 : Fin 1)))))

/-- `∀ x, ∃ z, z * z = x ∨ z * z = -x`, i.e. every element is a square up to sign. -/
def sqOrNegSq : Language.ring.Sentence := (sqOrNegSqBody.iExs (Fin 1)).iAlls (Fin 1)

theorem sqOrNegSq_realize {M : Type} [Add M] [Mul M] [Neg M] [One M] [Zero M]
    [Ring.CompatibleRing M] :
    M ⊨ sqOrNegSq ↔ ∀ x : M, ∃ z : M, z * z = x ∨ z * z = -x := by
  simp only [Sentence.Realize, sqOrNegSq, sqOrNegSqBody, Formula.realize_iAlls,
    Formula.realize_iExs, Formula.realize_sup, Formula.realize_equal, Ring.realize_mul,
    Ring.realize_neg, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h x
    obtain ⟨z, hz⟩ := h (fun _ => x)
    exact ⟨z 0, hz⟩
  · intro h i
    obtain ⟨z, hz⟩ := h (i 0)
    exact ⟨fun _ => z, hz⟩

/-- `ℝ` satisfies the sentence: use square roots, with a sign. -/
theorem real_realize_sqOrNegSq : ℝ ⊨ sqOrNegSq := by
  rw [sqOrNegSq_realize]
  intro x
  rcases lt_or_ge x 0 with h | h
  · exact ⟨Real.sqrt (-x), Or.inr (by rw [← sq, Real.sq_sqrt (by linarith)])⟩
  · exact ⟨Real.sqrt x, Or.inl (by rw [← sq, Real.sq_sqrt h])⟩

/-- Every nonnegative real is a square. -/
theorem real_exists_sq (x : ℝ) (hx : 0 ≤ x) : ∃ z : ℝ, x = z * z :=
  ⟨Real.sqrt x, by rw [← sq, Real.sq_sqrt hx]⟩

/-- In a model of `TR`, every nonnegative element is a square (the `ring`-sentence transfers). -/
theorem model_exists_sq {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hM : M ⊨ TR) : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z := by
  haveI hMT : M ⊨ LRc.completeTheory ℝ := hM
  haveI hExp : ringToLRc.IsExpansionOn M := instRingToLRcIsExpansionOn M
  have hℝ : ℝ ⊨ ringToLRc.onSentence sqOrNegSq :=
    (LHom.realize_onSentence (M := ℝ) ringToLRc sqOrNegSq).mpr real_realize_sqOrNegSq
  have h1 : M ⊨ ringToLRc.onSentence sqOrNegSq :=
    Theory.realize_sentence_of_mem (M := M) (T := LRc.completeTheory ℝ)
      (mem_completeTheory.mpr hℝ)
  have h2 : M ⊨ sqOrNegSq := (LHom.realize_onSentence (M := M) ringToLRc sqOrNegSq).mp h1
  intro x hx
  obtain ⟨z, hz | hz⟩ := (sqOrNegSq_realize.mp h2) x
  · exact ⟨z, hz.symm⟩
  · have hz0 : z * z = 0 := by
      have : 0 ≤ z * z := mul_self_nonneg z
      linarith
    have hx0 : x = 0 := by linarith
    exact ⟨0, by rw [mul_zero, hx0]⟩

end Work.WilC2
