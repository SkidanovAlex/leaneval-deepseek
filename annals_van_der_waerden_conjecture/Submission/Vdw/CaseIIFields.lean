import Mathlib
import Submission.Vdw.FinalAssembly
import Submission.Vdw.SubcaseIStructure
import Submission.Vdw.FourierDequi
import Submission.Vdw.ImprimitiveInput
import Submission.Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow

open Polynomial Filter Asymptotics
open scoped BigOperators
open Function
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Case II from field counting (Schmidt + Lemke Oliver–Thorne)

Bhargava's Case II is the region `D_f ≤ H^{2+2δ}` of `SubcaseI`.  The paper
bounds it by number-field counting:

* **Schmidt**: the number of degree-`n` number fields of absolute discriminant
  `≤ Y` is `≪ Y^{(n+2)/4}`;
* **Lemke Oliver–Thorne** (Prop. 2.2 of *[LOT]*): a degree-`n` field `K` whose
  Galois group is primitive is cut out by `≪ H log^{n-1}H/|Disc K|^{1/(n(n-1))}`
  monic degree-`n` polynomials of height `≤ H`.

Multiplying the two and summing over the fields by Abel summation (the
per-field weights `|Disc K|^{-1/(n(n-1))}` against the cumulative field count)
gives the *Abel-refined* estimate behind Case II, which is what this module
isolates as the input `CaseIICountBound n β`:

    `#{f ∈ SubcaseI_P2 n H : |Disc K_f| ≤ X} ≤ C·H·(log H)^{n-1}·X^{β-α}`,
    `α = 1/(n(n-1))`,

uniform in `X` (the input of Schmidt's exponent `β`; Schmidt gives
`β = (n+2)/4`, and the case-`n = 4, 5` exact counts give `β = 1`).

**Main result.**  Whenever `1 + (2+2δ)(β-α) < n-1` (with the project's
`δ = 1/(2n)`), Case II is `O(H^{n-1})`:

    `subcaseI_P2_isBigO_of_countBound`.

For `β = (n+2)/4` this exponent condition holds exactly for `n ≥ 7`
(`n = 7`: `1 + (15/7)(9/4 - 1/42) = 5.770 < 6`); for `n = 6` it fails
(`5.261 > 5`) at `δ = 1/(2n)`, which is why the paper's "say `δ = 1/(2n)`" is
loose at `n = 6` (an absolute small `δ ≤ 1/60` repairs it): see the Roadmap
Session-139 block.  The challenge-theorem endpoints therefore keep the
*region* form `SubcaseI_P2 = O(H^{n-1})` as the Case-II input, and this module
supplies the faithful route (`SubcaseI_P2_isBigO_of_schmidt`) for `n ≥ 7`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **The field discriminant of a member of the Case-II region** (closing the
existential witness of `SubcaseI_P2`; the value is independent of the witness
by proof irrelevance). -/
noncomputable def subcaseI_P2_disc (n H : ℕ) (f : ↥(SubcaseI_P2 n H)) : ℕ :=
  fieldDiscExp (f : ℤ[X]) (Classical.choose f.2.2)

/-- The defining bound of a Case-II member: its field discriminant is at most
`H^{2+2δ} = H^{2+1/n}`. -/
theorem subcaseI_P2_disc_le (n H : ℕ) (f : ↥(SubcaseI_P2 n H)) :
    (subcaseI_P2_disc n H f : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) :=
  Classical.choose_spec f.2.2

/-- **The Case-II input in Abel-refined form** (Schmidt + Lemke
Oliver–Thorne; see the module docstring). -/
def CaseIICountBound (n : ℕ) (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H X : ℕ, 1 ≤ X →
    ((Nat.card {f : ↥(SubcaseI_P2 n H) //
        (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} : ℕ) : ℝ)
      ≤ C * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
          * (X : ℝ) ^ (β - 1 / ((n : ℝ) * ((n : ℝ) - 1)))

/-- **Case II is `O(H^{n-1})` from the Abel-refined count bound**, whenever the
resulting exponent `1 + (2+2δ)(β-α)` stays strictly below `n-1` (the
logarithmic factor `(log H)^{n-1}` is then absorbed by the power saving). -/
theorem subcaseI_P2_isBigO_of_countBound (n : ℕ) (hn : 3 ≤ n) (β : ℝ)
    (hβ : 1 / ((n : ℝ) * ((n : ℝ) - 1)) < β)
    (hexp : 1 + (2 + 1 / (n : ℝ)) * (β - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
      < (n : ℝ) - 1)
    (h : CaseIICountBound n β) :
    (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  obtain ⟨C, hC, hCb⟩ := h
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hnpos hn1pos
  -- the two abbreviations of the proof
  set γ : ℝ := β - 1 / ((n : ℝ) * ((n : ℝ) - 1)) with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  set κ : ℝ := 1 + (2 + 1 / (n : ℝ)) * γ with hκdef
  have hκ : κ < (n : ℝ) - 1 := by rw [hκdef, hγdef]; exact hexp
  set δ : ℝ := ((n : ℝ) - 1 - κ) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hlog : ∀ᶠ H : ℕ in atTop,
      (1 + Real.log (H : ℝ)) ^ (n - 1) ≤ (H : ℝ) ^ δ := by
    have h1 := Commons.Analysis.ExpLog.eventually_one_add_log_pow_le_rpow
      (n - 1) 1 δ hδ
    filter_upwards [h1] with H hH
    simpa using hH
  have hXpow : ∀ (H X : ℕ), 1 ≤ H → (X : ℝ) ≤ 2 * (H : ℝ) ^ (2 + 1 / (n : ℝ)) →
      (X : ℝ) ^ γ ≤ 2 ^ γ * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * γ) := by
    intro H X hH1 hXle
    have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
    have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le one_pos hH1R
    calc (X : ℝ) ^ γ ≤ (2 * (H : ℝ) ^ (2 + 1 / (n : ℝ))) ^ γ :=
          Real.rpow_le_rpow (by positivity) hXle hγ.le
      _ = 2 ^ γ * ((H : ℝ) ^ (2 + 1 / (n : ℝ))) ^ γ :=
          Real.mul_rpow (by norm_num) (by positivity)
      _ = 2 ^ γ * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * γ) := by
          rw [Real.rpow_mul hHpos.le]
  have hbound : ∀ᶠ H : ℕ in atTop,
      ((SubcaseI_P2 n H).ncard : ℝ) ≤ C * 2 ^ γ * (H : ℝ) ^ ((n : ℝ) - 1) := by
    filter_upwards [hlog, eventually_ge_atTop (1 : ℕ)] with H hlogH hH1
    have hH1R : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
    have hHpos : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le one_pos hH1R
    -- the chosen modulus `X = ⌈H^(2+1/n)⌉`
    set X : ℕ := Nat.ceil ((H : ℝ) ^ (2 + 1 / (n : ℝ))) with hX
    have hX1 : 1 ≤ X := by
      rw [hX]
      have h2 : (1 : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) :=
        Real.one_le_rpow hH1R (by positivity)
      have h3 : (1 : ℝ) ≤ ((Nat.ceil ((H : ℝ) ^ (2 + 1 / (n : ℝ)))) : ℕ) :=
        le_trans h2 (Nat.le_ceil _)
      exact_mod_cast h3
    have hdisc : ∀ f : ↥(SubcaseI_P2 n H), (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ) := by
      intro f
      refine le_trans (subcaseI_P2_disc_le n H f) ?_
      rw [hX]
      exact Nat.le_ceil _
    have hcard : Nat.card {f : ↥(SubcaseI_P2 n H) //
          (subcaseI_P2_disc n H f : ℝ) ≤ (X : ℝ)} = Nat.card ↥(SubcaseI_P2 n H) :=
      Nat.card_congr
        { toFun := fun x => x.1
          invFun := fun y => ⟨y, hdisc y⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun y => rfl }
    have happly := hCb H X hX1
    rw [hcard] at happly
    -- `X ≤ 2·H^(2+1/n)`
    have hXle : (X : ℝ) ≤ 2 * (H : ℝ) ^ (2 + 1 / (n : ℝ)) := by
      have h1 : (X : ℝ) < (H : ℝ) ^ (2 + 1 / (n : ℝ)) + 1 := by
        rw [hX]; exact Nat.ceil_lt_add_one (by positivity)
      have h2 : (1 : ℝ) ≤ (H : ℝ) ^ (2 + 1 / (n : ℝ)) :=
        Real.one_le_rpow hH1R (by positivity)
      linarith
    have hXp := hXpow H X hH1 hXle
    have hlogle : (Real.log (H : ℝ)) ^ (n - 1) ≤ (1 + Real.log (H : ℝ)) ^ (n - 1) :=
      pow_le_pow_left₀ (Real.log_nonneg hH1R) (by linarith) (n - 1)
    -- `(1 + eγ) + δ ≤ n - 1`
    have hκδ : κ + δ ≤ (n : ℝ) - 1 := by rw [hδdef]; linarith
    calc ((SubcaseI_P2 n H).ncard : ℝ)
        ≤ C * (H : ℝ) * (Real.log (H : ℝ)) ^ (n - 1)
            * (X : ℝ) ^ γ := happly
      _ ≤ C * (H : ℝ) * (1 + Real.log (H : ℝ)) ^ (n - 1) * (X : ℝ) ^ γ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogle (by positivity))
            (by positivity)
      _ ≤ C * (H : ℝ) * (1 + Real.log (H : ℝ)) ^ (n - 1)
            * (2 ^ γ * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * γ)) :=
          mul_le_mul_of_nonneg_left hXp (by positivity)
      _ = C * 2 ^ γ * ((H : ℝ) ^ κ * (1 + Real.log (H : ℝ)) ^ (n - 1)) := by
          have hrw1 : (H : ℝ) * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * γ) = (H : ℝ) ^ κ := by
            have h1 : (H : ℝ) * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * γ)
                = (H : ℝ) ^ (1 : ℝ) * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * γ) := by
              rw [Real.rpow_one]
            rw [h1, (Real.rpow_add hHpos 1 _).symm]
          have hstep : C * (H : ℝ) * (1 + Real.log (H : ℝ)) ^ (n - 1)
                * (2 ^ γ * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * γ))
              = C * 2 ^ γ * ((H : ℝ) * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * γ))
                * (1 + Real.log (H : ℝ)) ^ (n - 1) := by ring
          calc C * (H : ℝ) * (1 + Real.log (H : ℝ)) ^ (n - 1)
                * (2 ^ γ * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * γ))
              = C * 2 ^ γ * ((H : ℝ) * (H : ℝ) ^ ((2 + 1 / (n : ℝ)) * γ))
                * (1 + Real.log (H : ℝ)) ^ (n - 1) := hstep
            _ = C * 2 ^ γ * ((H : ℝ) ^ κ * (1 + Real.log (H : ℝ)) ^ (n - 1)) := by
                rw [hrw1]; ring
      _ ≤ C * 2 ^ γ * ((H : ℝ) ^ κ * (H : ℝ) ^ δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hlogH (by positivity)
      _ = C * 2 ^ γ * (H : ℝ) ^ (κ + δ) := by rw [← Real.rpow_add hHpos]
      _ ≤ C * 2 ^ γ * (H : ℝ) ^ ((n : ℝ) - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hH1R hκδ
  refine IsBigO.of_bound (C * 2 ^ γ) ?_
  filter_upwards [hbound] with H hH
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  rw [← Real.rpow_natCast (H : ℝ) (n - 1)]
  have hcast : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hcast]
  exact hH

/-- **Case II for `n ≥ 7` from Schmidt + Lemke Oliver–Thorne** (Schmidt's
exponent `β = (n+2)/4`). -/
theorem subcaseI_P2_isBigO_of_schmidt (n : ℕ) (hn : 7 ≤ n)
    (h : CaseIICountBound n (((n : ℝ) + 2) / 4)) :
    (fun H : ℕ => ((SubcaseI_P2 n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  refine subcaseI_P2_isBigO_of_countBound n (by omega) (((n : ℝ) + 2) / 4) ?_ ?_ h
  · -- `β > α`
    have hnR : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : (0 : ℝ) < (n : ℝ) := by linarith
    have h2 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    rw [div_lt_iff₀ h2]
    nlinarith
  · -- the exponent margin `1 + (2+1/n)(β - α) < n - 1`
    have hnR : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : (0 : ℝ) < (n : ℝ) := by linarith
    have h2 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hfac : 2 * (n : ℝ) ^ 4 - 15 * (n : ℝ) ^ 3 + 11 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 4
        = ((n : ℝ) - 7) * (2 * (n : ℝ) ^ 3 - (n : ℝ) ^ 2 + 4 * (n : ℝ) + 38) + 270 := by
      ring
    have hpos : 0 < 2 * (n : ℝ) ^ 4 - 15 * (n : ℝ) ^ 3 + 11 * (n : ℝ) ^ 2
        + 10 * (n : ℝ) + 4 := by
      rw [hfac]
      have h4 : 0 ≤ (n : ℝ) - 7 := by linarith
      have h5 : 0 < 2 * (n : ℝ) ^ 3 - (n : ℝ) ^ 2 + 4 * (n : ℝ) + 38 := by
        nlinarith [sq_nonneg (n : ℝ), hnR]
      nlinarith [h4, h5]
    have hgoal : 4 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) ^ 2
        = 4 * (n : ℝ) ^ 2 * ((n : ℝ) - 1)
          + (2 * (n : ℝ) + 1) * ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) + 2) - 4)
          + (2 * (n : ℝ) ^ 4 - 15 * (n : ℝ) ^ 3 + 11 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 4) := by
      ring
    have hA : 1 + (2 + 1 / (n : ℝ)) * (((n : ℝ) + 2) / 4 - 1 / ((n : ℝ) * ((n : ℝ) - 1)))
        = (4 * (n : ℝ) ^ 2 * ((n : ℝ) - 1)
            + (2 * (n : ℝ) + 1) * ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) + 2) - 4))
          / (4 * (n : ℝ) ^ 2 * ((n : ℝ) - 1)) := by
      field_simp
    rw [hA, div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * (n : ℝ) ^ 2 * ((n : ℝ) - 1))]
    have hrew : ((n : ℝ) - 1) * (4 * (n : ℝ) ^ 2 * ((n : ℝ) - 1))
        = 4 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) ^ 2 := by ring
    rw [hrew, hgoal]
    linarith [hpos]

/-! ## Challenge-theorem endpoints

Using Schmidt's exponent `β = (n+2)/4` (valid for `n ≥ 7`), the paper's three
inputs are the §4 Fourier bound (`DequiBound`), Case II
(`CaseIICountBound n ((n+2)/4)`) and Widmer's imprimitive bound. -/

/-- **The challenge theorem for `n ≥ 7` from the paper's three inputs.** -/
theorem theorem_1_of_dequi_caseII (n : ℕ) (hn : 7 ≤ n) (h : DequiBound n)
    (h2 : CaseIICountBound n (((n : ℝ) + 2) / 4))
    (hw : (fun H : ℕ => ((ImprimitiveBad n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => (H : ℝ) ^ ((n : ℝ) / 2 + 2))) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_dequi_three n (by omega) h (subcaseI_P2_isBigO_of_schmidt n hn h2)
    (ImprimitiveBad_isBigO_of_widmer n (by omega) hw)

/-- **The challenge theorem in prime degree `n ≥ 7`**: the imprimitive input is
vacuous, leaving the §4 Fourier bound and Case II. -/
theorem theorem_1_of_dequi_caseII_prime (n : ℕ) (hn : 7 ≤ n) (hp : Nat.Prime n)
    (h : DequiBound n) (h2 : CaseIICountBound n (((n : ℝ) + 2) / 4)) :
    (fun H : ℕ => (E n H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) :=
  theorem_1_of_dequi_one_prime n (by omega) hp h (subcaseI_P2_isBigO_of_schmidt n hn h2)

end

end Submission.Vdw
