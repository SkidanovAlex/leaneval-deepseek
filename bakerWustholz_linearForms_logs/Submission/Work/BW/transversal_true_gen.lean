import Mathlib
import Submission.Work.BW.multiplicity_engine
import Submission.Work.BW.transversal_gen_defs
import Submission.Work.BW.ze_cancel_true_gen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The transversal exclusion in the `ε = true`, `ρ ≥ 2` case, for a general cyclic point

`Work.BW.ze_bad_true` proves the transversal exclusion for the full `ZEData` package, whose
cyclic point is `exp ∘ ℓ`. Downstream (`Work.BW.transversal_exclusion_spec` and the paper's
assembly) one needs the same exclusion with the cyclic point an *arbitrary* family
`θ : Fin N → ℂ`, and under only the hypotheses the proof consumes.

We restate the exclusion for the reduced package `ZEDataG` (`Work.BW.transversal_gen_defs`),
whose `ℓ` field plays the role of `θ`, and then specialise it to `transversal_true_gen`.

The proof is the proof of `ze_bad_true`: cancel all the positive factors in the zero estimate's
inequality (`Work.BW.ze_cancel_true_gen`) to obtain
`(Sq (ρ-1) + 1) · C(Tq (ρ-1) + ρ, ρ) · |Δ_J| ≤ (N+1).descFactorial ρ · ∏_{i∈J} ⌊δ_{i+1}⌋₊`,
then use `|Δ_J| ≥ 1` and `⌊δ_{i+1}⌋₊ ≤ δ_{i+1}`, `(N+1).descFactorial ρ ≤ (r+1).descFactorial ρ`,
and finally contradict (E1) at `m = ρ - 1` with `e` the indicator of `J`.
-/

namespace Work.BW

open scoped BigOperators

/-- **Transversal exclusion (`ε = true`, `ρ ≥ 2`), reduced hypotheses.** If the zero estimate
returns `L = ρ ≥ 2` for a primitive system `M` at a step `m` with `m + 1 ≤ ρ`, and if the
degree bounds `δ`, the step sequences `Sq`, `Tq` and the exclusion condition (E1) hold, then the
resulting inequality is contradictory. The cyclic point is an arbitrary `ℓ : Fin N → ℂ`. -/
lemma ze_bad_true_gen {N r : ℕ} (D : ZEDataG N r) (ρ : ℕ) (M : Fin ρ → Fin N → ℤ) (m L : ℕ)
    (hρN : ρ ≤ N) (hM : PrimSys M) (hm : m + 1 ≤ ρ) (hρ2 : 2 ≤ ρ) (hL : L = ρ)
    (hcard : D.Sq m + 1 ≤ cardMod true M D.ℓ (D.Sq m))
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
      (((D.Tq m + L).choose L : ℕ) : ℝ) *
          (cardMod true M D.ℓ (D.Sq m) : ℝ) *
        ((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        ((⌊D.δ 0⌋₊ : ℕ) : ℝ) * ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ)) : False := by
  classical
  have hNr' : N ≤ r := D.hNr
  have hρ1 : 1 ≤ ρ := by omega
  obtain ⟨J, hJ, hΔ⟩ := exists_minorJ_ne_zero M hM.1
  have hred := ze_cancel_true_gen D ρ (ρ - 1) ρ M m L hL (by omega) (by omega) hρN hcard hineq
    J hJ hΔ
  have hΔ1 := one_le_abs_minorJ hΔ
  have hA : (0 : ℝ) ≤ ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ) := by
    positivity
  have hle : ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ) ≤
      ((N + 1).descFactorial ρ : ℝ) * ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by
    calc ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ)
        = (((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ)) * 1 := by ring
      _ ≤ (((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ)) *
            |(minorJ M J hJ : ℝ)| := mul_le_mul_of_nonneg_leftℝ hΔ1 hA
      _ ≤ ((N + 1).descFactorial ρ : ℝ) *
            ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := hred
  have hdesc : ((N + 1).descFactorial ρ : ℝ) ≤ ((r + 1).descFactorial ρ : ℝ) :=
    by exact_mod_cast Nat.descFactorial_le ρ (by omega : N + 1 ≤ r + 1)
  have hprodle : ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤ ∏ i ∈ J, D.δ i.succ :=
    Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => Nat.floor_le (D.hδnn i.succ))
  have hE1 : ((r + 1).descFactorial ρ : ℝ) * ∏ i ∈ J, D.δ i.succ <
      ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ) := by
    have h := D.hE1 (ρ - 1) (by omega) (indT J) (indT_le_one J) (by rw [sum_indT]; omega)
    have hT : (D.Tq (ρ - 1) + (ρ - 1) + 1) = (D.Tq (ρ - 1) + ρ) := by omega
    have hρ1' : ρ - 1 + 1 = ρ := by omega
    rw [prod_delta_indT, hT, hρ1'] at h
    exact h
  have hlt : ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ) <
      ((D.Sq (ρ - 1) : ℝ) + 1) * ((D.Tq (ρ - 1) + ρ).choose ρ : ℝ) :=
    calc _ ≤ ((N + 1).descFactorial ρ : ℝ) *
          ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := hle
      _ ≤ ((r + 1).descFactorial ρ : ℝ) * ∏ i ∈ J, D.δ i.succ :=
          le_trans (mul_le_mul_of_nonneg_rightℝ hdesc
              (Finset.prod_nonneg fun i _ => by positivity))
            (mul_le_mul_of_nonneg_leftℝ hprodle (by positivity))
      _ < _ := hE1
  exact absurd hlt (lt_irrefl _)

lemma transversal_true_gen {N r : ℕ} (hNr : N < r)
    (δ : Fin (N + 1) → ℝ) (hδnn : ∀ i, 0 ≤ δ i) (hδ1 : ∀ i, 1 ≤ ⌊δ i⌋₊)
    (Sq Tq : ℕ → ℕ) (hSa : ∀ m, m < N → Sq (m + 1) ≤ Sq m)
    (hTa : ∀ m, m < N → Tq (m + 1) ≤ Tq m)
    (hE1 : ∀ m, m < r → ∀ e : Fin (N + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, δ i ^ e i <
        ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ))
    (θ : Fin N → ℂ) (ρ : ℕ) (M : Fin ρ → Fin N → ℤ) (m : ℕ)
    (hρN : ρ ≤ N) (hM : PrimSys M) (hρ2 : 2 ≤ ρ) (hm : m + 1 ≤ ρ)
    (hcard : Sq m + 1 ≤ cardMod true M θ (Sq m))
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
      (((Tq m + ρ).choose ρ : ℕ) : ℝ) * (cardMod true M θ (Sq m) : ℝ) *
        ((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        ((⌊δ 0⌋₊ : ℕ) : ℝ) * ∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊δ i⌋₊ : ℕ) : ℝ)) :
    False := by
  let D : ZEDataG N r :=
    { hNr := le_of_lt hNr, δ := δ, hδnn := hδnn, hδ1 := hδ1,
      Sq := Sq, Tq := Tq, hSa := hSa, hTa := hTa, hE1 := hE1, ℓ := θ }
  exact ze_bad_true_gen D ρ M m ρ hρN hM hm hρ2 rfl hcard hineq

end Work.BW
