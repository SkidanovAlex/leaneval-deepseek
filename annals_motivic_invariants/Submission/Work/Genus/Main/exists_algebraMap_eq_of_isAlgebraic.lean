import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.ord_aeval_of_neg
import Submission.Work.Genus.OrderInf.ordInf_aeval_of_neg
import Submission.Work.Genus.Main.exists_ord_neg_or_ordInf_neg

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Main

/-- The order of vanishing at infinity of the zero rational function is `0` (`ordInf f = -f.intDegree`
and `intDegree 0 = 0`).  The same statement is proved privately in
`Submission/Work/Genus/OrderInf/ordInf_aeval_of_neg.lean`; it is reproduced here so that this file
does not depend on a private lemma. -/
private lemma ordInf_zero {F : Type*} [Field F] : Work.Genus.ordInf (0 : RatFunc F) = 0 := by
  simp [Work.Genus.ordInf, RatFunc.intDegree_zero]

/-- **`F` is algebraically closed in `F(t)`**: an element of `F(t)` algebraic over `F` is a
constant.

Route: `IsAlgebraic F f` unfolds to `∃ p ≠ 0, Polynomial.aeval f p = 0`.  If `f` is not a constant
then by `Work.Genus.Main.exists_ord_neg_or_ordInf_neg` it has a pole at some place, and
`Work.Genus.Order.ord_aeval_of_neg` (resp. `Work.Genus.OrderInf.ordInf_aeval_of_neg`) computes the
order of `aeval f p` there as `p.natDegree * ord f < 0` (note `0 < p.natDegree` because `p` is
non-constant: a non-zero constant `p` would give `aeval f p = p ≠ 0`), contradicting
`aeval f p = 0`. -/
theorem exists_algebraMap_eq_of_isAlgebraic {F : Type*} [Field F] {f : RatFunc F}
    (hf : IsAlgebraic F f) : ∃ c : F, f = algebraMap F (RatFunc F) c := by
  by_contra h
  obtain ⟨p, hpne, hp0⟩ := hf
  -- A non-zero polynomial killing `f` must be non-constant: a non-zero constant `p = C a`
  -- would give `aeval f p = algebraMap F (RatFunc F) a = 0`, hence `a = 0`, hence `p = 0`.
  have hdeg : 0 < p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
    · exfalso
      have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
      have hc0 : p.coeff 0 = 0 := by
        have h1 : Polynomial.aeval f (Polynomial.C (p.coeff 0)) = 0 := by
          rw [← hpC]; exact hp0
        rw [Polynomial.aeval_C] at h1
        exact (algebraMap F (RatFunc F)).injective (by rw [h1, map_zero])
      rw [hpC, hc0, Polynomial.C_0] at hpne
      exact hpne rfl
    · exact hpos
  -- Since `f` is not a constant it has a pole, at a finite place or at infinity.
  rcases Work.Genus.Main.exists_ord_neg_or_ordInf_neg h with ⟨π, hπ, hπf⟩ | hinf
  · -- A pole at the place of an irreducible `π`.
    have hf0 : f ≠ 0 := by
      intro h0
      rw [h0, Work.Genus.Order.ord_zero] at hπf
      exact absurd hπf (lt_irrefl 0)
    have hkey := Work.Genus.Order.ord_aeval_of_neg (π := π) (A := p) (x := f) hπ hdeg hf0 hπf
    rw [hp0, Work.Genus.Order.ord_zero] at hkey
    -- `hkey : 0 = p.natDegree * ord π f`, but the right hand side is strictly negative.
    have hneg : (p.natDegree : ℤ) * Work.Genus.ord π f < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast hdeg) hπf
    exact absurd (hkey.symm ▸ hneg) (lt_irrefl 0)
  · -- A pole at infinity.
    have hf0 : f ≠ 0 := by
      intro h0
      rw [h0, ordInf_zero] at hinf
      exact absurd hinf (lt_irrefl 0)
    have hkey := Work.Genus.OrderInf.ordInf_aeval_of_neg (A := p) (x := f) hdeg hf0 hinf
    rw [hp0, ordInf_zero] at hkey
    have hneg : (p.natDegree : ℤ) * Work.Genus.ordInf f < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast hdeg) hinf
    exact absurd (hkey.symm ▸ hneg) (lt_irrefl 0)

end Work.Genus.Main
