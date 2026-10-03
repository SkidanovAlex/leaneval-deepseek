/-
# The support of the Littlewood--Paley shell symbol `DiSym`

The frequency piece of §5 of Krause--Mirek--Tao is the Littlewood--Paley *shell*
`η_{≤k} − η_{≤k−1}` spread over the arithmetic frequencies `(ℚ/ℤ)_l` of height exactly `l`;
its symbol is `DiSym ρ l k : ℝ/ℤ → ℂ` of `BesselDefs.lean`.

A non-zero value of that symbol at `ξ` exhibits `ξ = α + θ` with `α ∈ (ℚ/ℤ)_l` an arithmetic
frequency and `θ` a *real* frequency in the shell `2^{k−2} < |θ| < 2^k`.  This is the
form in which the §5 paraproduct analysis consumes the symbol: the shells of different scale
do not overlap, and the value is a genuine function of the frequency `θ` (not merely of its
class modulo `1`).

The proof is a two-step reduction, both steps formalised below.

* `etaCut_sub_ne_zero`: the *scalar* support statement.  If the difference
  `η_{≤k}(u) − η_{≤k−1}(u)` of the two rescaled cutoffs is non-zero, then
  `2^{k−2} < |u| < 2^k`.  Indeed, for `|u| ≤ 2^{k−2}` both cutoffs equal `1` (since
  `|u/2^k| ≤ 1/4 ≤ 1/2` and `|u/2^{k−1}| ≤ 1/2`), while for `|u| ≥ 2^k` both vanish
  (since `|u/2^k| ≥ 1` and `|u/2^{k−1}| ≥ 2 ≥ 1`).
* `exists_shell_of_periodize_sub`: the *periodisation* step.  If the periodisations of two
  functions `φ, ψ` differ at a point `x` of the circle, then the pointwise difference
  `φ − ψ` does not vanish at some translate `t + j` of the canonical representative `t` of
  `x`; this translate is the real frequency `θ` (which represents `x` on the circle, since
  `j ∈ ℤ`).

Combining the two with `DiSym_apply` gives `DiSym_support`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.BesselDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory Finset
open Work.Analysis.IonescuWainger

noncomputable section

/-- **The scalar support of the Littlewood--Paley shell.**  If the difference
`η_{≤k}(u) − η_{≤k−1}(u)` of the two rescaled cutoffs is non-zero, then `u` lies in the shell
`2^{k−2} < |u| < 2^k`. -/
lemma etaCut_sub_ne_zero {k : ℤ} {u : ℝ}
    (h : etaCut Work.KMTContract.kmtEta k u - etaCut Work.KMTContract.kmtEta (k-1) u ≠ 0) :
    (2:ℝ)^(k-2) < |u| ∧ |u| < (2:ℝ)^k := by
  have hk : (0:ℝ) < (2:ℝ)^k := zpow_pos (by norm_num) _
  have hk1 : (0:ℝ) < (2:ℝ)^(k-1) := zpow_pos (by norm_num) _
  have t2 : (1/2:ℝ) * (2:ℝ)^k = (2:ℝ)^(k-1) := by
    rw [zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0) k 1, zpow_one]; ring
  have t3 : (1/2:ℝ) * (2:ℝ)^(k-1) = (2:ℝ)^(k-2) := by
    rw [show ((2:ℝ)^(k-2)) = (2:ℝ)^k / 4 by
      rw [zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0) k 2]; norm_num]
    rw [show (2:ℝ)^(k-1) = (2:ℝ)^k / 2 by
      rw [zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0) k 1, zpow_one]]
    ring
  constructor
  · -- `|u| ≤ 2^{k-2}` makes both cutoffs equal to `1`
    by_contra hle
    rw [not_lt] at hle
    apply h
    have e1 : etaCut Work.KMTContract.kmtEta k u = 1 := by
      rw [etaCut]
      refine Work.KMTContract.kmtEta_one ?_
      rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
      calc |u| ≤ (2:ℝ)^(k-2) := hle
        _ ≤ (1/2) * (2:ℝ)^k := by
            rw [t2]
            exact zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
    have e2 : etaCut Work.KMTContract.kmtEta (k-1) u = 1 := by
      rw [etaCut]
      refine Work.KMTContract.kmtEta_one ?_
      rw [abs_div, abs_of_pos hk1, div_le_iff₀ hk1]
      calc |u| ≤ (2:ℝ)^(k-2) := hle
        _ = (1/2) * (2:ℝ)^(k-1) := (t3).symm
    rw [e1, e2, sub_self]
  · -- `|u| ≥ 2^k` makes both cutoffs vanish
    by_contra hge
    rw [not_lt] at hge
    apply h
    have e1 : etaCut Work.KMTContract.kmtEta k u = 0 := by
      rw [etaCut]
      refine Work.KMTContract.kmtEta_zero ?_
      rw [abs_div, abs_of_pos hk, one_le_div hk]
      exact hge
    have e2 : etaCut Work.KMTContract.kmtEta (k-1) u = 0 := by
      rw [etaCut]
      refine Work.KMTContract.kmtEta_zero ?_
      rw [abs_div, abs_of_pos hk1, one_le_div hk1]
      exact le_trans (zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)) hge
    rw [e1, e2, sub_self]

/-- **The periodisation step.**  If the periodisations of `φ` and `ψ` differ at a point `x` of
the circle, and the pointwise difference `φ − ψ` is supported in the shell
`2^{k−2} < |·| < 2^k`, then there is a real frequency `θ` in that shell representing `x`. -/
lemma exists_shell_of_periodize_sub {k : ℤ} {φ ψ : ℝ → ℂ}
    (hg : ∀ u, φ u - ψ u ≠ 0 → (2:ℝ)^(k-2) < |u| ∧ |u| < (2:ℝ)^k)
    {x : Work.Analysis.IonescuWainger.Circle} (h : periodize φ x - periodize ψ x ≠ 0) :
    ∃ θ : ℝ, (θ : Work.Analysis.IonescuWainger.Circle) = x ∧
      (2:ℝ)^(k-2) < |θ| ∧ |θ| < (2:ℝ)^k := by
  have per : ∀ φ : ℝ → ℂ, periodize φ x
      = ∑' j : ℤ, φ ((AddCircle.equivIco (1:ℝ) 0 x).val + j) := fun φ => rfl
  -- some translate of the canonical representative has non-zero difference
  have hex : ∃ j : ℤ, φ ((AddCircle.equivIco (1:ℝ) 0 x).val + j)
      - ψ ((AddCircle.equivIco (1:ℝ) 0 x).val + j) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply h
    rw [per φ, per ψ, sub_eq_zero]
    exact tsum_congr (fun j => sub_eq_zero.mp (hcon j))
  obtain ⟨j, hj⟩ := hex
  refine ⟨((AddCircle.equivIco (1:ℝ) 0 x).val : ℝ) + (j : ℝ), ?_, hg _ hj⟩
  have hxc : (((AddCircle.equivIco (1 : ℝ) 0 x).val : ℝ) :
      Work.Analysis.IonescuWainger.Circle) = x := AddCircle.coe_equivIco
  have hjc : ((j : ℝ) : Work.Analysis.IonescuWainger.Circle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨j, by simp⟩
  rw [AddCircle.coe_add, hxc, hjc, add_zero]

/-- **The support of the shell symbol `DiSym`.**  A non-zero value of `DiSym ρ l k` at `ξ`
comes from an arithmetic frequency `α ∈ kmtSet ρ l = (ℚ/ℤ)_l` and a real frequency `θ` in the
shell `2^{k−2} < |θ| < 2^k` with `ξ = α + θ`. -/
theorem DiSym_support (ρ : ℝ) (l : ℕ) (k : ℤ) (h2 : (2:ℝ)^(k+1) < 1) {ξ : Work.Analysis.IonescuWainger.Circle}
    (h : Work.KMTPlan.A6.DiSym ρ l k ξ ≠ 0) :
    ∃ α ∈ Work.KMTPlan.A6.kmtSet ρ l, ∃ θ : ℝ,
      (θ : Work.Analysis.IonescuWainger.Circle) = ξ - α ∧
      (2:ℝ)^(k-2) < |θ| ∧ |θ| < (2:ℝ)^k := by
  rw [DiSym_apply] at h
  obtain ⟨α, hα, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨α, hα, exists_shell_of_periodize_sub (fun u hu => etaCut_sub_ne_zero hu) hne⟩

end

end Work.KMTPlan.A6
