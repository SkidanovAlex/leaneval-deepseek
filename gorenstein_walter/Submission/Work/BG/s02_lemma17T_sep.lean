import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.Lambda

/-!
# BG §2, Lemma 1.7 ("separation" form): some `λ ∈ Λ` does not fix the value at `g`

`Λ` is the dual group of `H₀/U`, and `lambdaSum P = ∑_{β} lamCF C β` is the regular
character `r(Λ)` of `H₀/U` inflated to `H₀` (`Lambda.lean`).  If `r(Λ)(g) = 0`, then
`g ∉ U`, and therefore some `λ_β ∈ Λ` must satisfy `λ_β(g) ≠ 1` — otherwise every summand
would be `1` and `r(Λ)(g) = |Λ| = |Fintype (H₀/U →* ℂˣ)| ≠ 0`, contradiction.

The statement is the "one coordinate is non-trivial" separation step extracted from
Lemma 1.7 and used when the character-theoretic arguments of §2 pick a constituent off
`T = H₀ ∖ U`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

theorem s02_lemma17T_sep {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G)
    [Fintype (Work.BG.quotGroup C.P →* ℂˣ)] {g : ↥C.P.H0}
    (hg : Work.BG.lambdaSum C.P g = 0) :
    ∃ β : Work.BG.quotGroup C.P →* ℂˣ, Work.BG.lamCF C β g ≠ 1 := by
  by_contra h
  simp only [not_exists, not_not] at h
  -- Every summand of `r(Λ)(g)` equals `1`, hence `r(Λ)(g) = |Λ|`.
  have hcard : (Fintype.card (Work.BG.quotGroup C.P →* ℂˣ) : ℂ) = 0 := by
    have hsum : Work.BG.lambdaSum C.P g =
        ∑ β : Work.BG.quotGroup C.P →* ℂˣ, Work.BG.lamCF C β g := by
      rw [Work.BG.lambdaSum, ClassFunction.sum_apply]
      rfl
    rw [hsum, Finset.sum_congr rfl (fun β _ => h β), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one] at hg
    exact hg
  -- But `|Λ| ≥ 1`.
  have hne : (Fintype.card (Work.BG.quotGroup C.P →* ℂˣ) : ℂ) ≠ 0 := by
    have : 0 < Fintype.card (Work.BG.quotGroup C.P →* ℂˣ) :=
      Fintype.card_pos_iff.mpr ⟨(1 : Work.BG.quotGroup C.P →* ℂˣ)⟩
    exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
  exact hne hcard

end Work.BG
