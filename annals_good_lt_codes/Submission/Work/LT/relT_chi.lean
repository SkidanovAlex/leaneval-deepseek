import Mathlib
import Submission.Work.LT.relT_defs
import Submission.Work.LT.chi_basic
import Submission.Work.LT.chi_orth

namespace Work.LT

/-- Complex conjugation inverts the additive character: `star (chi p uv st) = chi p uv (-st)`. -/
lemma chi_neg_star (p : ℕ) [NeZero p] (uv st : ZMod p × ZMod p) :
    star (chi p uv st) = chi p uv (-st) := by
  simp only [chi, Prod.fst_neg, Prod.snd_neg]
  rw [Complex.star_def, AddChar.starComp_apply (φ := ZMod.stdAddChar)
      (by rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_ne_zero (NeZero.ne p))
      (uv.1 * st.1 + uv.2 * st.2)]
  rw [AddChar.inv_apply', ← AddChar.map_neg_eq_inv]
  congr 1
  ring

/-- Parseval/orthogonality of the character table of `(ℤ/p)²`:
`∑_uv conj (χ_uv a) · χ_uv b = p²·[a = b]`. -/
lemma chi_parseval (p : ℕ) [NeZero p] (a b : ZMod p × ZMod p) :
    ∑ uv : ZMod p × ZMod p, star (chi p uv a) * chi p uv b =
      if a = b then (p : ℂ) ^ 2 else 0 := by
  have hC := (chi_basic p).2.2.1
  have hterm : ∀ uv : ZMod p × ZMod p,
      star (chi p uv a) * chi p uv b = chi p uv (b - a) := by
    intro uv
    rw [chi_neg_star p uv a, ← hC uv (-a) b]
    congr 1
    rw [sub_eq_add_neg, add_comm]
  simp only [hterm]
  rw [(chi_orth p).1 (b - a)]
  by_cases hab : a = b
  · subst hab; simp
  · have hne : b - a ≠ 0 := fun h => hab (sub_eq_zero.mp h).symm
    simp [hne, hab]

/-- Basic theory of the additive characters `chi p uv st = ω^{uv.1 * st.1 + uv.2 * st.2}` of
`(ℤ/p)²` (here `ω = ZMod.stdAddChar`, so `chi p uv (-)` is an additive character of `(ℤ/p)²`
and `chi p (-) st` is an additive character of the dual group, identified with `(ℤ/p)²`):
multiplicativity in each argument, `chi p 0 st = 1`, non-vanishing, complex conjugation inverts
the character index, the two orthogonality sums (a sum over the character index vanishes unless
the group element is `0`, and vice versa), the Parseval sum
`∑_uv conj(χ_uv(a)) χ_uv(b) = p²·[a=b]`, and the two "dual transvection" identities
`chi p uv (s + k·t, t) = chi p (Mab p k uv) st`, `chi p uv (s, t + k·s) = chi p (Mba p k uv) st`. -/
theorem relT_chi :
    (∀ (p : ℕ) [NeZero p] (st : ZMod p × ZMod p), chi p 0 st = 1)
  ∧ (∀ (p : ℕ) [NeZero p] (uv uv' st : ZMod p × ZMod p),
        chi p (uv + uv') st = chi p uv st * chi p uv' st)
  ∧ (∀ (p : ℕ) [NeZero p] (uv st st' : ZMod p × ZMod p),
        chi p uv (st + st') = chi p uv st * chi p uv st')
  ∧ (∀ (p : ℕ) [NeZero p] (uv st : ZMod p × ZMod p), star (chi p uv st) = chi p (-uv) st)
  ∧ (∀ (p : ℕ) [NeZero p] (uv st : ZMod p × ZMod p), chi p uv st ≠ 0)
  ∧ (∀ (p : ℕ) [NeZero p] (w : ZMod p × ZMod p),
        ∑ uv : ZMod p × ZMod p, chi p uv w = if w = 0 then (p : ℂ) ^ 2 else 0)
  ∧ (∀ (p : ℕ) [NeZero p] (uv : ZMod p × ZMod p),
        ∑ st : ZMod p × ZMod p, chi p uv st = if uv = 0 then (p : ℂ) ^ 2 else 0)
  ∧ (∀ (p : ℕ) [NeZero p] (w : ZMod p × ZMod p),
        ∑ uv : ZMod p × ZMod p, star (chi p uv w) = if w = 0 then (p : ℂ) ^ 2 else 0)
  ∧ (∀ (p : ℕ) [NeZero p] (uv : ZMod p × ZMod p),
        ∑ st : ZMod p × ZMod p, star (chi p uv st) = if uv = 0 then (p : ℂ) ^ 2 else 0)
  ∧ (∀ (p : ℕ) [NeZero p] (a b : ZMod p × ZMod p),
        ∑ uv : ZMod p × ZMod p, star (chi p uv a) * chi p uv b =
          if a = b then (p : ℂ) ^ 2 else 0)
  ∧ (∀ (p : ℕ) [NeZero p] (k : ZMod p) (uv st : ZMod p × ZMod p),
        chi p uv (st.1 + k * st.2, st.2) = chi p (Mab p k uv) st)
  ∧ (∀ (p : ℕ) [NeZero p] (k : ZMod p) (uv st : ZMod p × ZMod p),
        chi p uv (st.1, st.2 + k * st.1) = chi p (Mba p k uv) st) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p _ st
    exact (chi_basic p).1 st
  · intro p _ uv uv' st
    exact (chi_basic p).2.1 uv uv' st
  · intro p _ uv st st'
    exact (chi_basic p).2.2.1 uv st st'
  · intro p _ uv st
    exact (chi_basic p).2.2.2.1 uv st
  · intro p _ uv st
    exact (chi_basic p).2.2.2.2.1 uv st
  · intro p _ w
    exact (chi_orth p).1 w
  · intro p _ uv
    exact (chi_orth p).2.1 uv
  · intro p _ w
    exact (chi_orth p).2.2.1 w
  · intro p _ uv
    exact (chi_orth p).2.2.2 uv
  · intro p _ a b
    exact chi_parseval p a b
  · intro p _ k uv st
    exact (chi_basic p).2.2.2.2.2.1 k uv st
  · intro p _ k uv st
    exact (chi_basic p).2.2.2.2.2.2 k uv st

end Work.LT
