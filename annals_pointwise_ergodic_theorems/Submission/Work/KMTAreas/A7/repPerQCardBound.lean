import Mathlib
import Submission.Work.KMTAreas.A7.addOrderOf_le_sharp
import Submission.Work.KMTAreas.A7.exp_dominates_poly_half
import Submission.Work.KMTPlan.A6.LowSmallSymDefs

namespace Work.KMTAreas.A7

open Work.Analysis.IonescuWainger

/-- **Absorption of the sharp sub-exponential exponent into the prescribed scale.**

For `ρ ∈ (0,1]`, `A ≥ 0` and `ε > 0` there is `C > 0` with

`2 ^ (A · (1 + l·2^{ρl/2} + l)) ≤ C · 2 ^ (ε · 2^{ρl})`  for all `l : ℕ`.

This is the clean replacement of `Work.KMTAreas.A7.rpow_sharp_absorb` (which rests on a `sorry`).
It is reduced to `exp_dominates_poly_half`: the polynomial-ish expression
`(1 + l·2^{ρl/2} + l)` is bounded by `C'·2^{ρl}` (with an *additive* constant), and scaling the
coefficient `A` down by `ε/2` keeps the inequality valid, after which `2^{K + (ε/2)2^{ρl}}` is
bounded by `2^K · 2^{ε 2^{ρl}}`. -/
private lemma rpow_sharp_absorb_e (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ l : ℕ,
      (2 : ℝ) ^ (A * (1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ)))
        ≤ C * (2 : ℝ) ^ (ε * (2 : ℝ) ^ (ρ * (l : ℝ))) := by
  obtain ⟨K, hK0, hK⟩ :=
    exp_dominates_poly_half ρ hρ hρ1 (2 * A / ε) 0 0 (by positivity) le_rfl le_rfl
  refine ⟨(2 : ℝ) ^ ((ε / 2) * K), Real.rpow_pos_of_pos (by norm_num) _, fun l => ?_⟩
  set E : ℝ := 1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ) with hE
  have hfrac : (ε / 2) * (2 * A / ε) = A := by
    field_simp
  -- the additive domination of `E` by `2^{ρl}`
  have hK' : (2 * A / ε) * E ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) + K := by
    have h' : (2 * A / ε) * (1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ))
        ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) + K := by
      simpa using hK l
    rwa [hE]
  have hAbs : A * E ≤ (ε / 2) * (2 : ℝ) ^ (ρ * (l : ℝ)) + (ε / 2) * K := by
    have h2 : (ε / 2) * ((2 * A / ε) * E) ≤ (ε / 2) * ((2 : ℝ) ^ (ρ * (l : ℝ)) + K) :=
      mul_le_mul_of_nonneg_left hK' (by positivity)
    calc A * E = (ε / 2) * ((2 * A / ε) * E) := by rw [← mul_assoc, hfrac]
      _ ≤ (ε / 2) * ((2 : ℝ) ^ (ρ * (l : ℝ)) + K) := h2
      _ = (ε / 2) * (2 : ℝ) ^ (ρ * (l : ℝ)) + (ε / 2) * K := by ring
  calc (2 : ℝ) ^ (A * E)
      ≤ (2 : ℝ) ^ ((ε / 2) * (2 : ℝ) ^ (ρ * (l : ℝ)) + (ε / 2) * K) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hAbs
    _ = (2 : ℝ) ^ ((ε / 2) * K) * (2 : ℝ) ^ ((ε / 2) * (2 : ℝ) ^ (ρ * (l : ℝ))) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        ring
    _ ≤ (2 : ℝ) ^ ((ε / 2) * K) * (2 : ℝ) ^ (ε * (2 : ℝ) ^ (ρ * (l : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) :=
          le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
        exact mul_le_mul_of_nonneg_right (by linarith : ε / 2 ≤ ε) hp

/-- **The counting and period bounds for the exact-height Ionescu–Wainger frequency sets.**

This is the *clean* (sorry-free) replacement of `Work.KMTAreas.A7.perQ_card_bound`
(`Submission/Work/KMTAreas/A7/perQ_card_bound.lean`), whose proof rests on the two `sorry`
stubs `Work.KMTAreas.A7.card_iwArithFreqs_le_sharp` and `Work.KMTAreas.A7.rpow_sharp_absorb`
and therefore cannot be used in a sorry-free development.  It is needed to sum the §6 fibre
mass bound over the fibres `(ℚ/ℤ)_{≤l₁} × (ℚ/ℤ)_{≤l₂}`.

For `ρ ∈ (0,1]` and any `ε > 0` there is `C > 0` such that, for all levels `l₁, l₂`:

* every pair of arithmetic frequencies `α ∈ (ℚ/ℤ)_{≤l₁}`, `β ∈ (ℚ/ℤ)_{≤l₂}` has fibre period
  `perQ α β = lcm (addOrderOf α) (addOrderOf β) ≤ C·2^{ε(2^{ρl₁} + 2^{ρl₂})}`, and
* the Ionescu–Wainger frequency set has cardinality `#(ℚ/ℤ)_{≤l} ≤ C·2^{2·2^{ρl}}`
  (the weaker, `ε`-free form of the cardinality estimate; the sharp
  `2^{O(l·2^{ρl/2})}` form is not needed here).

Resources for the two proofs (read, do not import the two `sorry` stubs, nor `perQ_card_bound`):

* `Work.KMTAreas.A7.addOrderOf_le_sharp` (sorry-free, public) states
  `∃ C K > 0, ∀ l α ∈ iwArithFreqs ρ l, addOrderOf α ≤ C·2^{K(1 + l·2^{ρl/2} + l)}`;
  the first clause follows with `perQ α β ≤ addOrderOf α * addOrderOf β`
  (`spikeToolbox`: `perQ = lcm`, `Nat.lcm_le_mul`) once the exponent
  `K(1 + l₁2^{ρl₁/2} + l₁) + K(1 + l₂2^{ρl₂/2} + l₂)` is absorbed into `ε(2^{ρl₁}+2^{ρl₂})`.
  That absorption is `Work.KMTAreas.A7.rpow_sharp_absorb`'s content and must be re-proved here:
  `l·2^{ρl/2} ≤ 2^{ρl}` holds for `l ≥ L(ρ)` (because `2^{ρl/2}/l → ∞`; a short proof uses
  `Real.quadratic_le_exp` or `Real.add_one_le_exp` with `2^{ρl} = exp(ρl·log 2)`), and for the
  finitely many `l < L` the exponential `C·2^{ε2^{ρl}}` with a large enough constant absorbs
  everything.
* `Work.Analysis.IonescuWainger.iw_height_card_le` (sorry-free, public) states
  `∃ C > 0, ∀ l, #(iwArithFreqs ρ l) ≤ C * 2^{2^{ρl}}` — the second clause after
  `2^{2^{ρl}} ≤ 2^{2·2^{ρl}}`.
* If a smaller `ε` is more convenient for the second clause, any exponent of the form
  `2^{(2:ℝ)·2^{ρl}}` (or `2^{c·2^{ρl}}` for a fixed `c > 0` independent of `l`) is acceptable —
  in that case state the second clause with that exponent. -/
theorem repPerQCardBound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (l₁ l₂ : ℕ) (α : Work.Analysis.IonescuWainger.Circle),
          α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ →
        ∀ (β : Work.Analysis.IonescuWainger.Circle),
          β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ →
        ((Work.KMTPlan.A6.perQ α β : ℕ) : ℝ)
          ≤ C * (2 : ℝ) ^ (ε * ((2 : ℝ) ^ (ρ * (l₁ : ℝ)) + (2 : ℝ) ^ (ρ * (l₂ : ℝ))))) ∧
      (∀ l : ℕ, ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ)
          ≤ C * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (l : ℝ)))) := by
  obtain ⟨Ca, Ka, hCapos, hKapos, hord⟩ := addOrderOf_le_sharp ρ hρ hρ1
  obtain ⟨Cabs, hCabspos, habs⟩ := rpow_sharp_absorb_e ρ hρ hρ1 Ka hKapos.le ε hε
  obtain ⟨Ccard, hCcardpos, hcard⟩ := iw_height_card_le hρ
  refine ⟨max 1 (max (Ca ^ 2 * Cabs ^ 2) Ccard), lt_of_lt_of_le one_pos (le_max_left _ _),
    ?_, ?_⟩
  · intro l₁ l₂ α hα β hβ
    obtain ⟨q₁, hq₁, hq₁α⟩ := mem_iwArithFreqs.mp hα
    obtain ⟨q₂, hq₂, hq₂β⟩ := mem_iwArithFreqs.mp hβ
    have ho1 : 0 < addOrderOf α := addOrderOf_pos_iff.mpr
      (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨q₁, pos_of_mem_iwP hq₁, hq₁α⟩)
    have ho2 : 0 < addOrderOf β := addOrderOf_pos_iff.mpr
      (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨q₂, pos_of_mem_iwP hq₂, hq₂β⟩)
    -- `perQ` is the lcm of the two additive orders, hence is at most their product
    have hper : ((Work.KMTPlan.A6.perQ α β : ℕ) : ℝ)
        ≤ (addOrderOf α : ℝ) * (addOrderOf β : ℝ) := by
      have h : Work.KMTPlan.A6.perQ α β ≤ addOrderOf α * addOrderOf β := by
        rw [Work.KMTPlan.A6.perQ]
        exact Nat.lcm_le_mul ho1 ho2
      exact_mod_cast h
    -- the sharp order bounds at the two levels, and the absorption of their exponents
    have ho₁ := hord l₁ α hα
    have ho₂ := hord l₂ β hβ
    have hb₁ := habs l₁
    have hb₂ := habs l₂
    have hchain : (addOrderOf α : ℝ) * (addOrderOf β : ℝ)
        ≤ (Ca ^ 2 * Cabs ^ 2)
          * ((2 : ℝ) ^ (ε * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))
              * (2 : ℝ) ^ (ε * (2 : ℝ) ^ (ρ * (l₂ : ℝ)))) := by
      calc (addOrderOf α : ℝ) * (addOrderOf β : ℝ)
          ≤ (Ca * (2 : ℝ) ^ (Ka * (1 + (l₁ : ℝ) * (2 : ℝ) ^ (ρ * (l₁ : ℝ) / 2) + (l₁ : ℝ))))
              * (Ca * (2 : ℝ) ^ (Ka * (1 + (l₂ : ℝ) * (2 : ℝ) ^ (ρ * (l₂ : ℝ) / 2) + (l₂ : ℝ)))) :=
            mul_le_mul ho₁ ho₂ (by positivity) (by positivity)
        _ = Ca ^ 2
              * ((2 : ℝ) ^ (Ka * (1 + (l₁ : ℝ) * (2 : ℝ) ^ (ρ * (l₁ : ℝ) / 2) + (l₁ : ℝ)))
                * (2 : ℝ) ^ (Ka * (1 + (l₂ : ℝ) * (2 : ℝ) ^ (ρ * (l₂ : ℝ) / 2) + (l₂ : ℝ)))) := by
            ring
        _ ≤ Ca ^ 2
              * ((Cabs * (2 : ℝ) ^ (ε * (2 : ℝ) ^ (ρ * (l₁ : ℝ))))
                * (Cabs * (2 : ℝ) ^ (ε * (2 : ℝ) ^ (ρ * (l₂ : ℝ))))) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg Ca)
            exact mul_le_mul hb₁ hb₂ (by positivity) (by positivity)
        _ = (Ca ^ 2 * Cabs ^ 2)
              * ((2 : ℝ) ^ (ε * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))
                * (2 : ℝ) ^ (ε * (2 : ℝ) ^ (ρ * (l₂ : ℝ)))) := by
            ring
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hchain
    have hexp : ε * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) + ε * (2 : ℝ) ^ (ρ * (l₂ : ℝ))
        = ε * ((2 : ℝ) ^ (ρ * (l₁ : ℝ)) + (2 : ℝ) ^ (ρ * (l₂ : ℝ))) := by ring
    rw [hexp] at hchain
    calc ((Work.KMTPlan.A6.perQ α β : ℕ) : ℝ)
        ≤ (addOrderOf α : ℝ) * (addOrderOf β : ℝ) := hper
      _ ≤ (Ca ^ 2 * Cabs ^ 2)
            * (2 : ℝ) ^ (ε * ((2 : ℝ) ^ (ρ * (l₁ : ℝ)) + (2 : ℝ) ^ (ρ * (l₂ : ℝ)))) := hchain
      _ ≤ max 1 (max (Ca ^ 2 * Cabs ^ 2) Ccard)
            * (2 : ℝ) ^ (ε * ((2 : ℝ) ^ (ρ * (l₁ : ℝ)) + (2 : ℝ) ^ (ρ * (l₂ : ℝ)))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact le_trans (le_max_left _ _) (le_max_right _ _)
  · intro l
    have h2 : (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))) ≤ (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (l : ℝ))) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hp : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
      linarith
    calc ((iwArithFreqs ρ l).card : ℝ)
        ≤ Ccard * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))) := hcard l
      _ ≤ Ccard * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (l : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 hCcardpos.le
      _ ≤ max 1 (max (Ca ^ 2 * Cabs ^ 2) Ccard) * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (l : ℝ))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact le_trans (le_max_right _ _) (le_max_right _ _)

end Work.KMTAreas.A7
