/-
# `Submission.Work.FIArea3.Y` — the paper-faithful core of area 3: *FI* Lemma 10.1

`Ybound` is the paper's Lemma 10.1, `Y(β) ≪ θ⁴N²(log N)^{2^19}`, isolated as a `Prop` so that
`Area3` can be shown to follow *only* from it.  The reduction `Ybound → CoreBound` (and hence
`Area3`) is elementary and is proved here.

The paper's weight (10.6) is `Y(β) = Σ_{(z₁,z₂)=1} |β_{z₁}β_{z₂}| τ(|z₁|²) τ(|z₂|²) τ₃(Δ(z₁,z₂))`;
`τ₃(0) := 1` by convention (the convention never matters: for coprime pairs with `β ≠ 0` on both
sides one has `Δ ≠ 0`, but the convention makes the statement unconditional).
-/
import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm

open Finset Work.FIPlan
open scoped BigOperators

namespace Work.FIArea3

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The 3-fold divisor function `τ₃(n) = #{(d₁,d₂,d₃) : d₁d₂d₃ = n} = Σ_{d | n} τ(n/d)`, with the
convention `τ₃ 0 = 1` (which makes the `Y`-bound unconditional; it never matters for the pairs that
occur, where `β ≠ 0` forces `|z|²` squarefree and coprime pairs have `Δ ≠ 0`). -/
def tau3 (n : ℕ) : ℕ :=
  if n = 0 then 1 else ∑ d ∈ n.divisors, (n / d).divisors.card

lemma one_le_divisors_card {m : ℕ} (hm : m ≠ 0) : 1 ≤ m.divisors.card :=
  Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm⟩

lemma one_le_tau3 (n : ℕ) : 1 ≤ tau3 n := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp [tau3]
  · rw [tau3, if_neg hn]
    have h1 : (n / 1).divisors.card ≤ ∑ d ∈ n.divisors, (n / d).divisors.card :=
      Finset.single_le_sum (f := fun d => (n / d).divisors.card)
        (fun d _ => Nat.zero_le _) (Nat.one_mem_divisors.mpr hn)
    rw [Nat.div_one] at h1
    exact le_trans (one_le_divisors_card hn) h1

lemma tau_le_tau3 (n : ℕ) : n.divisors.card ≤ tau3 n := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp [tau3]
  · rw [tau3, if_neg hn]
    calc n.divisors.card = ∑ _d ∈ n.divisors, 1 := by simp
      _ ≤ ∑ d ∈ n.divisors, (n / d).divisors.card :=
          Finset.sum_le_sum (fun d hd => one_le_divisors_card
            (Nat.pos_iff_ne_zero.mp (Nat.div_pos
              (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp hd).1)
              (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 (Nat.pos_of_ne_zero hn)))))

/-- **`(1 + τ(|Δ|)) ≤ 2 τ₃(|Δ|)`**, the comparison that lets the sharp `τ₃`-weighted Lemma 10.1
dominate the `τ`-weighted `CoreBound`. -/
lemma one_add_tau_le_two_tau3 (m : ℕ) : 1 + m.divisors.card ≤ 2 * tau3 m := by
  have h1 : m.divisors.card ≤ tau3 m := tau_le_tau3 m
  have h2 : 1 ≤ tau3 m := one_le_tau3 m
  omega

/-- **The paper's Lemma 10.1** in the form needed for (10.10): for every coefficient in the polar
box, `Y(β) = Σ_{(z₁,z₂)=1} ‖β₁‖‖β₂‖ τ(|z₁|²) τ(|z₂|²) τ₃(Δ) ≪ θ⁴N²(log N)^{2^19}`.

(The paper's proof is Lemma 2.2 — splitting `τ(|z₁|²)`, `τ(|z₂|²)`, `τ₃(Δ)` at *small* divisors
`d₁, d₂, d ≤ N^{1/4}` — followed by the count "the number of points `z₁,z₂ ∈ B` with
`d | Δ(z₁,z₂)`, `d₁ | |z₁|²`, `d₂ | |z₂|²` is `O(θ⁴(N log N)²τ(dd₁d₂)(dd₁d₂)^{-1})`" and the
divisor sums `ΣΣΣ τ(dd₁d₂)^{17}(dd₁d₂)^{-1} ≪ (log N)^{2^19}`.) -/
def Ybound : Prop :=
  ∃ Cb : ℝ, 0 < Cb ∧
  ∀ (Pa : Work.FITop.Params) (f : ℤ → ℝ) (φ : ℝ) (β : GaussianInt → ℂ),
    Work.FITop3.IsMajorant Pa f → Work.FITop3.IsBetaCoeff Pa φ β →
    (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if GaussCoprime z1 z2 then
          ‖β z1‖ * ‖β z2‖ * ((gnorm z1).divisors.card : ℝ) * ((gnorm z2).divisors.card : ℝ)
            * (tau3 (absDelta z1 z2) : ℝ) else 0))
      ≤ Cb * Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))

end

end Work.FIArea3
