import Mathlib
import Submission.Work.LT.relT_defs

namespace Work.LT

/-- The standard additive character of `ZMod p`, `ω = ZMod.stdAddChar`, is inverted by complex
conjugation: `star (ω ^ x) = ω ^ (-x)`. -/
lemma star_zmodStdAddChar (p : ℕ) [NeZero p] (c : ZMod p) :
    star (ZMod.stdAddChar c) = ZMod.stdAddChar (-c) := by
  have h := Circle.coe_inv_eq_conj (ZMod.toCircle c)
  simp [← h, AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]

/-- Elementary algebra of the additive character `chi p uv st = ω^{uv.1*st.1 + uv.2*st.2}` of
`(ℤ/p)²`: it is `1` at the zero character index, multiplicative in each argument,
complex conjugation negates the character index, it never vanishes, and the two
"dual transvection" identities `chi p uv (s + k·t, t) = chi p (Mab p k uv) st` and
`chi p uv (s, t + k·s) = chi p (Mba p k uv) st`. -/
theorem chi_basic (p : ℕ) [NeZero p] :
    (∀ st : ZMod p × ZMod p, chi p 0 st = 1)
  ∧ (∀ uv uv' st : ZMod p × ZMod p, chi p (uv + uv') st = chi p uv st * chi p uv' st)
  ∧ (∀ uv st st' : ZMod p × ZMod p, chi p uv (st + st') = chi p uv st * chi p uv st')
  ∧ (∀ uv st : ZMod p × ZMod p, star (chi p uv st) = chi p (-uv) st)
  ∧ (∀ uv st : ZMod p × ZMod p, chi p uv st ≠ 0)
  ∧ (∀ (k : ZMod p) (uv st : ZMod p × ZMod p),
        chi p uv (st.1 + k * st.2, st.2) = chi p (Mab p k uv) st)
  ∧ (∀ (k : ZMod p) (uv st : ZMod p × ZMod p),
        chi p uv (st.1, st.2 + k * st.1) = chi p (Mba p k uv) st) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro st
    simp [chi]
  · intro uv uv' st
    simp only [chi, Prod.fst_add, Prod.snd_add]
    rw [show (uv.1 + uv'.1) * st.1 + (uv.2 + uv'.2) * st.2
          = (uv.1 * st.1 + uv.2 * st.2) + (uv'.1 * st.1 + uv'.2 * st.2) by ring,
      AddChar.map_add_eq_mul]
  · intro uv st st'
    simp only [chi, Prod.fst_add, Prod.snd_add]
    rw [show uv.1 * (st.1 + st'.1) + uv.2 * (st.2 + st'.2)
          = (uv.1 * st.1 + uv.2 * st.2) + (uv.1 * st'.1 + uv.2 * st'.2) by ring,
      AddChar.map_add_eq_mul]
  · intro uv st
    simp only [chi, Prod.fst_neg, Prod.snd_neg]
    rw [show -uv.1 * st.1 + -uv.2 * st.2 = -(uv.1 * st.1 + uv.2 * st.2) by ring,
      star_zmodStdAddChar]
  · intro uv st
    simp only [chi, ZMod.stdAddChar_apply]
    exact Circle.coe_ne_zero _
  · intro k uv st
    simp only [chi, Mab]
    congr 1
    ring
  · intro k uv st
    simp only [chi, Mba]
    congr 1
    ring

end Work.LT
