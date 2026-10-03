import Mathlib
import Submission.Work.Peluse.UControl.peluseFamily

/-!
# The PET chapter of Peluse's Proposition 3.4, in the nested-family vocabulary

`Work.Peluse.UControl.Prop34` (Peluse's Proposition 3.4 for the embedded configuration
`(x, x+y, …, x+y^{d-1}, x+P(y))`) splits, exactly as in the source, into

* **`PetChapter`** (this file): the *PET chapter*, Peluse's Lemma 4.9, i.e. her Lemma 4.7 once
  followed by Lemma 4.8 `(d-2)` times — from the multilinear average
  `ΛMD N M P F` one obtains a lower bound for the average, over the parameter box `D.parBox d H`,
  of the multilinear correlation along the *linear* configuration whose direction family is the
  datum's own level-`(d-1)` family `w ↦ dir D d c (d-1) w (pad d a)`; and
* the *last step* of her proof of Proposition 3.4 (Lemma 4.2 once, Lemma 4.10 per fibre, the
  box-norm peel, and the identification of the direction family with the datum's family), which is
  proved in `Submission/Work/Peluse/UControl/peluseProp34.lean`.

The hypotheses of `PetChapter` are the *data* of the PET induction, and the conclusion displays
exactly the three things the last step consumes:

* the *base* function of the linear configuration is the last function `F_d` of the multilinear
  average (so that the box norm `famNorm` at the end is taken of `F_d` itself);
* every *slot* function is `F_d` or its conjugate, evaluated at
  `x + dir(a)·y + β(a)` (the constant term `β` is the paper's `p'_i(a)`, absorbed into the slot
  function by translation invariance of the box norm);
* the shift bound `|dir(a)·y + β(a)| ≤ Cne·N` (the paper's (4.11)/`(C')` bound, needed to apply
  Peluse's Lemma 4.2 and Lemma 4.10 along the chain).
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- The datum's level-`(l-1)` direction attached to the `i`-th element of `D.I (l-1)` (in the fixed
enumeration `Fintype.equivFin`), evaluated at the parameter family `a`.  This is the leading
coefficient `p_i(a) ∈ A_{ℓ-1}` of Peluse's Lemma 4.9. -/
def petDir (D : IdxDatum) (l : ℕ) (c : ℤ) (a : D.Idx l)
    (i : Fin (Fintype.card (D.I (l - 1)))) : ℤ :=
  D.dir l c (l - 1) ((Fintype.equivFin (D.I (l - 1))).symm i) (D.pad l a)

/-- The multilinear correlation along the *linear* configuration with direction family the datum's
directions: the quantity produced by Peluse's Lemma 4.9 and consumed by the last step of the proof
of Proposition 3.4.  `b i` chooses whether the `i`-th slot carries `f` or its conjugate, and
`β a i` is the (parameter-dependent) constant term `p'_i(a)`. -/
def linFamAvg (D : IdxDatum) (l : ℕ) (c : ℤ) (N M H : ℕ) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) : ℝ :=
  (((D.parBox l H).card : ℕ) : ℝ)⁻¹ *
    ∑ a ∈ D.parBox l H,
      ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f x *
        ∑ y ∈ Finset.Icc 1 M,
          ∏ i : Fin (Fintype.card (D.I (l - 1))),
            (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
              else f (x + (petDir D l c a i * (y : ℤ) + β a i)))‖

/-- **The PET chapter** (Peluse's Lemma 4.9 for the configuration
`(x, x+y, …, x+y^{d-1}, x+P(y))`, `d = deg P`): there is a level datum `D` — the multiplicities
`k_i ≪_d 1` of her §3, with the last level nonempty and `|I_{d-1}| ≥ 2` — and a constant `Cne₀ ≥ 1`
such that for every scale constant `A ≥ 1` there are an exponent `K ≥ 2` and a shift-bound constant
`Cne ≥ 1` with `Cne ≤ Cne₀·A`, such that a large multilinear average along the polynomial
progression (with the scale imbalances measured by `A`) forces the average, over the parameter box
`D.parBox d ⌊δ'M⌋`, of the multilinear correlation along the linear configuration with the datum's
directions to be at least `(γ/A)^K`, the constant terms `β` being bounded by `Cne·N`.

The quantifier order is the paper's (`D` and the polynomial dependent shift-bound constant `Cne₀`
are fixed by `P`; `K` and `Cne` are produced after the scale parameter `A`), the diagonalisation
`δ' ≤ γ^K/A` carries her `δ' ≪_{C,d} δ^{O_d(1)}`, the scale hypotheses are those of `Prop34`, and
`K ≥ 2` is a harmless normalisation (a larger exponent weakens the conclusion and strengthens the
window hypothesis).  The bound `Cne ≤ Cne₀·A` records that the shift bound (the paper's (4.11)) is,
in the normalisation of `Prop34`, polynomial in the scale imbalance: it is what lets the consumer
choose `A` to absorb all the constants of the last step of the proof of Proposition 3.4. -/
def PetChapter (P : Polynomial ℤ) : Prop :=
  ∃ D : IdxDatum, 2 ≤ Fintype.card (D.I (P.natDegree - 1)) ∧
  ∃ Cne₀ : ℕ, 1 ≤ Cne₀ ∧
  ∀ A : ℝ, 1 ≤ A → ∃ K : ℕ, 2 ≤ K ∧ ∃ Cne : ℕ, 1 ≤ Cne ∧ (Cne : ℝ) ≤ (Cne₀ : ℝ) * A ∧
    ∀ (N M : ℕ) (F : Fin (P.natDegree + 1) → ℤ → ℂ) (γ δ' : ℝ),
      2 ≤ P.natDegree → 1 ≤ N → 1 ≤ M →
      (N : ℝ) ≤ A * (M : ℝ) ^ P.natDegree →
      (M : ℝ) ^ P.natDegree ≤ A * γ⁻¹ * (N : ℝ) →
      0 < γ → γ ≤ 1 → 0 < δ' → A * δ' ≤ γ ^ K →
      2 ≤ (⌊δ' * (M : ℝ)⌋).toNat →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, SupportIn (F i) N) →
      γ ≤ ‖LambdaMD N M P F‖ →
      ∃ (b : Fin (Fintype.card (D.I (P.natDegree - 1))) → Bool)
        (β : D.Idx P.natDegree → Fin (Fintype.card (D.I (P.natDegree - 1))) → ℤ),
        (∀ a ∈ D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat,
            ∀ i : Fin (Fintype.card (D.I (P.natDegree - 1))), ∀ y ∈ Finset.Icc 1 M,
              |petDir D P.natDegree P.leadingCoeff a i * (y : ℤ) + β a i|
                ≤ (Cne : ℤ) * (N : ℤ)) ∧
        (γ / A) ^ K ≤ linFamAvg D P.natDegree P.leadingCoeff N M (⌊δ' * (M : ℝ)⌋).toNat
          (F ⟨P.natDegree, Nat.lt_succ_self _⟩) b β

end

end Work.Peluse.UControl
