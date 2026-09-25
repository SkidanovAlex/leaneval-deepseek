import Mathlib
import Submission.Work.LT.relT_defs

namespace Work.LT

/-! # Orthogonality of the additive characters of `(ℤ/p)²`

We prove the four orthogonality sums for the character
`chi p uv st = ZMod.stdAddChar (uv.1 * st.1 + uv.2 * st.2)` of `ZMod p × ZMod p`.

The pairing `(uv, st) ↦ uv.1 * st.1 + uv.2 * st.2` is a non-degenerate `ℤ/p`-bilinear form,
so it identifies `(ℤ/p)²` with its own dual group; the character `chi p · w` is trivial exactly
when `w = 0`.  The orthogonality then follows from the general character orthogonality
`AddChar.sum_eq_ite`, and the complex-conjugate statements follow by taking `star` through the
(finite) sum. -/

/-- The additive character `uv ↦ chi p uv w` of `(ZMod p × ZMod p)`, as a bundled
`AddChar`. -/
private noncomputable def chiChar (p : ℕ) [NeZero p] (w : ZMod p × ZMod p) :
    AddChar (ZMod p × ZMod p) ℂ where
  toFun uv := ZMod.stdAddChar (uv.1 * w.1 + uv.2 * w.2)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro a b
    have h : ((a + b).1 * w.1 + (a + b).2 * w.2)
        = (a.1 * w.1 + a.2 * w.2) + (b.1 * w.1 + b.2 * w.2) := by
      simp only [Prod.fst_add, Prod.snd_add]; ring
    rw [h, AddChar.map_add_eq_mul]

private lemma chiChar_apply (p : ℕ) [NeZero p] (w uv : ZMod p × ZMod p) :
    chiChar p w uv = chi p uv w := rfl

/-- The character `chi p · w` is trivial (equivalently, `chi p uv w = 1` for every `uv`) if and
only if `w = 0`; i.e. `uv ↦ chi p uv ·` is injective. -/
private lemma chiChar_eq_zero_iff (p : ℕ) [NeZero p] (w : ZMod p × ZMod p) :
    chiChar p w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have h1 : ZMod.stdAddChar w.1 = 1 := by
      have := congr_fun (congrArg DFunLike.coe h) ((1 : ZMod p), (0 : ZMod p))
      simpa [chiChar] using this
    have h2 : ZMod.stdAddChar w.2 = 1 := by
      have := congr_fun (congrArg DFunLike.coe h) ((0 : ZMod p), (1 : ZMod p))
      simpa [chiChar] using this
    have e1 : w.1 = 0 := ZMod.injective_stdAddChar (by rw [h1, AddChar.map_zero_eq_one])
    have e2 : w.2 = 0 := ZMod.injective_stdAddChar (by rw [h2, AddChar.map_zero_eq_one])
    exact Prod.ext e1 e2
  · intro h
    subst h
    ext uv
    simp [chiChar]

/-- The character sum over the group: `∑_uv chi p uv w` vanishes unless `w = 0`. -/
private lemma chi_sum (p : ℕ) [NeZero p] (w : ZMod p × ZMod p) :
    ∑ uv : ZMod p × ZMod p, chi p uv w = if w = 0 then (p : ℂ) ^ 2 else 0 := by
  classical
  have h1 : (∑ uv : ZMod p × ZMod p, chi p uv w) = ∑ uv, chiChar p w uv :=
    Finset.sum_congr rfl fun uv _ => (chiChar_apply p w uv).symm
  rw [h1, AddChar.sum_eq_ite]
  simp only [chiChar_eq_zero_iff p w]
  split_ifs with h
  · rw [Fintype.card_prod, ZMod.card]
    push_cast
    ring
  · rfl

/-- The character pairing is symmetric in its two arguments. -/
private lemma chi_comm (p : ℕ) [NeZero p] (uv st : ZMod p × ZMod p) :
    chi p uv st = chi p st uv := by
  simp only [chi]
  congr 1
  ring

/-- The four orthogonality sums for the additive character
`chi p uv st = ZMod.stdAddChar (uv.1 * st.1 + uv.2 * st.2)` of `(ℤ/p)²`: summing over the
character index kills all non-zero group elements (and conversely, summing over the group
kills all non-zero character indices), together with the complex-conjugate variants. -/
theorem chi_orth (p : ℕ) [NeZero p] :
    (∀ w : ZMod p × ZMod p,
        ∑ uv : ZMod p × ZMod p, chi p uv w = if w = 0 then (p : ℂ) ^ 2 else 0)
  ∧ (∀ uv : ZMod p × ZMod p,
        ∑ st : ZMod p × ZMod p, chi p uv st = if uv = 0 then (p : ℂ) ^ 2 else 0)
  ∧ (∀ w : ZMod p × ZMod p,
        ∑ uv : ZMod p × ZMod p, star (chi p uv w) = if w = 0 then (p : ℂ) ^ 2 else 0)
  ∧ (∀ uv : ZMod p × ZMod p,
        ∑ st : ZMod p × ZMod p, star (chi p uv st) = if uv = 0 then (p : ℂ) ^ 2 else 0) := by
  refine ⟨chi_sum p, ?_, ?_, ?_⟩
  · intro uv
    rw [show (∑ st : ZMod p × ZMod p, chi p uv st)
          = ∑ st : ZMod p × ZMod p, chi p st uv from
        Finset.sum_congr rfl fun st _ => chi_comm p uv st]
    exact chi_sum p uv
  · intro w
    have hs : (∑ uv : ZMod p × ZMod p, star (chi p uv w)) = star (∑ uv, chi p uv w) :=
      (star_sum Finset.univ _).symm
    rw [hs, chi_sum p w]
    split_ifs <;> simp
  · intro uv
    have hs : (∑ st : ZMod p × ZMod p, star (chi p uv st)) = star (∑ st, chi p uv st) :=
      (star_sum Finset.univ _).symm
    rw [hs, show (∑ st : ZMod p × ZMod p, chi p uv st)
          = ∑ st : ZMod p × ZMod p, chi p st uv from
        Finset.sum_congr rfl fun st _ => chi_comm p uv st]
    rw [chi_sum p uv]
    split_ifs <;> simp

end Work.LT
