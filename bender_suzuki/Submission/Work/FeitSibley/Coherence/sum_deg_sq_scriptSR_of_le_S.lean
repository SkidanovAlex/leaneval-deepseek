import Mathlib
import Submission.Work.FeitSibley.Coherence.sum_deg_sq_scriptSR
import Submission.Work.FeitSibley.Coherence.scriptSR_deg_Qcomm

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The sum of squared degrees over `𝒮(R)` for `R ≤ S`

Peterfalvi II, Appendice XII: for the Feit–Sibley data `h : FSData G` and a subgroup
`R ≤ S` normalised by `H`, the characters of `𝒮(R) = scriptSR h.H h.Q₁ R` satisfy

`∑_{χ ∈ 𝒮(R)} χ(1)² = |D| · [S : R] · (|Q₁| - 1)`.

`Work.FeitSibley.Coherence.sum_deg_sq_scriptSR` evaluates the same sum as the difference of
indices `[H : R] - [H : R·Q₁]`; the content here is the arithmetic evaluation of that
difference, which uses `R ≤ S` (so that `R` and `Q₁` meet trivially and commute) and the
factorisation `H = Q ⋊ D`.

## Proof

Since `R ≤ S`, the subgroup `R` commutes elementwise with `Q₁` and `R ⊓ Q₁ ≤ S ⊓ Q₁ = ⊥`, so
`|R ⊔ Q₁| = |R| · |Q₁|`; likewise `|Q| = |S| · |Q₁|` and `|H| = |D| · |Q|`.  Writing
`r = |R|`, `i_S = [S : R]`, `q = |Q₁|`, `d = |D|`, Lagrange's identity
`H.index * Nat.card H = Nat.card G` (applied to `H = R`, to `H = R ⊔ Q₁` and to `S`) gives

* `r · [H : R] = |H| = d·(r·i_S)·q`, hence `[H : R] = d·i_S·q`;
* `(r·q) · [H : R·Q₁] = |H| = d·(r·i_S)·q`, hence `[H : R·Q₁] = d·i_S`.

Their difference is `d·i_S·(q - 1)`, the right-hand side.
-/

set_option linter.style.haveILetI false

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

theorem sum_deg_sq_scriptSR_of_le_S {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (R : Subgroup G) (hR : R ≤ h.S) (hRn : h.H ≤ Subgroup.normalizer (R : Set G)) :
    ∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 R, ((Work.CharCore.irrDeg χ : ℝ)) ^ 2 =
      (Nat.card h.D : ℝ) * (((R.subgroupOf h.S).index : ℕ) : ℝ) * ((Nat.card h.Q1 : ℝ) - 1) := by
  classical
  -- `R ≤ S ≤ Q`, so the index-counting lemma for `R ≤ Q` applies
  have hRQ : R ≤ h.Q := hR.trans h.S_le_Q
  rw [sum_deg_sq_scriptSR h R hRQ hRn]
  -- positivity, used for the cancellations below
  have hr : 0 < Nat.card R := Nat.card_pos
  have hq : 0 < Nat.card h.Q1 := Nat.card_pos
  -- the cardinalities of the three subgroups of `G` viewed inside their containers
  have hcardR_H : Nat.card ↥(R.subgroupOf h.H) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hR.trans h.S_le_H)).toEquiv
  have hcardR_S : Nat.card ↥(R.subgroupOf h.S) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv
  have hcardA_H : Nat.card ↥((R ⊔ h.Q1).subgroupOf h.H) = Nat.card ↥(R ⊔ h.Q1) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le (hR.trans h.S_le_H) h.Q1_le_H)).toEquiv
  -- `|R ⊔ Q₁| = |R| · |Q₁|`: `R` and `Q₁` commute elementwise and meet trivially
  have hA : Nat.card ↥(R ⊔ h.Q1) = Nat.card R * Nat.card h.Q1 := by
    have hcomm : ∀ a ∈ R, ∀ b ∈ h.Q1, a * b = b * a :=
      fun a ha b hb => h.commute a (hR ha) b hb
    have hsup := Work.PGroup.card_sup_mul_card_inf R h.Q1 hcomm
    have hinf : R ⊓ h.Q1 = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro x hx
      obtain ⟨hxR, hxQ1⟩ := Subgroup.mem_inf.mp hx
      have hx' : x ∈ h.S ⊓ h.Q1 := Subgroup.mem_inf.mpr ⟨hR hxR, hxQ1⟩
      rw [h.S_inf_Q1] at hx'
      simpa using hx'
    rw [hinf] at hsup
    simpa using hsup
  -- `|Q| = |S| · |Q₁|`
  have hQcard : Nat.card ↥h.Q = Nat.card h.S * Nat.card h.Q1 := by
    have hsup := Work.PGroup.card_sup_mul_card_inf h.S h.Q1 h.commute
    rw [h.S_sup_Q1, h.S_inf_Q1] at hsup
    simpa using hsup
  -- `|H| = |D| · |Q|`, from `[H : Q] = |D|` and Lagrange
  have hHcard : Nat.card ↥h.H = Nat.card h.D * Nat.card h.Q := by
    have h1 := Subgroup.card_mul_index (h.Q.subgroupOf h.H)
    have hc : Nat.card ↥(h.Q.subgroupOf h.H) = Nat.card h.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Q_le_H).toEquiv
    rw [hc, index_subgroupOf_Q h] at h1
    exact h1.symm.trans (Nat.mul_comm _ _)
  -- Lagrange for the three subgroups: `|·| · [H : ·] = |H|`, resp. `|R| · [S : R] = |S|`
  have h7 : Nat.card R * (R.subgroupOf h.H).index = Nat.card ↥h.H := by
    rw [← hcardR_H]; exact Subgroup.card_mul_index _
  have h8 : Nat.card R * (R.subgroupOf h.S).index = Nat.card h.S := by
    rw [← hcardR_S]; exact Subgroup.card_mul_index _
  have h9 : (Nat.card R * Nat.card h.Q1) * ((R ⊔ h.Q1).subgroupOf h.H).index
      = Nat.card ↥h.H := by
    rw [← hA, ← hcardA_H]; exact Subgroup.card_mul_index _
  -- `[H : R] = d · [S : R] · q`
  have hIR : (R.subgroupOf h.H).index
      = (R.subgroupOf h.S).index * Nat.card h.Q1 * Nat.card h.D := by
    have key : Nat.card R * (R.subgroupOf h.H).index
        = Nat.card R * ((R.subgroupOf h.S).index * Nat.card h.Q1 * Nat.card h.D) := by
      rw [h7, hHcard, hQcard, ← h8]
      ring
    exact Nat.eq_of_mul_eq_mul_left hr key
  -- `[H : R ⊔ Q₁] = d · [S : R]`
  have hIA : ((R ⊔ h.Q1).subgroupOf h.H).index
      = (R.subgroupOf h.S).index * Nat.card h.D := by
    have key : (Nat.card R * Nat.card h.Q1) * ((R ⊔ h.Q1).subgroupOf h.H).index
        = (Nat.card R * Nat.card h.Q1) * ((R.subgroupOf h.S).index * Nat.card h.D) := by
      rw [h9, hHcard, hQcard, ← h8]
      ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hr hq) key
  -- the difference of the two indices, in additive form
  have hadd : (R.subgroupOf h.H).index
      = ((R ⊔ h.Q1).subgroupOf h.H).index
        + Nat.card h.D * (R.subgroupOf h.S).index * (Nat.card h.Q1 - 1) := by
    have hqm : Nat.card h.Q1 - 1 + 1 = Nat.card h.Q1 := Nat.sub_add_cancel hq
    calc (R.subgroupOf h.H).index
        = (R.subgroupOf h.S).index * Nat.card h.Q1 * Nat.card h.D := hIR
      _ = (R.subgroupOf h.S).index * (Nat.card h.Q1 - 1 + 1) * Nat.card h.D := by rw [hqm]
      _ = (R.subgroupOf h.S).index * Nat.card h.D
            + Nat.card h.D * (R.subgroupOf h.S).index * (Nat.card h.Q1 - 1) := by ring
      _ = ((R ⊔ h.Q1).subgroupOf h.H).index
            + Nat.card h.D * (R.subgroupOf h.S).index * (Nat.card h.Q1 - 1) := by rw [hIA]
  -- the right-hand side, with the `ℕ`-subtraction cast to `ℝ`
  have hZ : (((Nat.card h.D * (R.subgroupOf h.S).index * (Nat.card h.Q1 - 1)) : ℕ) : ℝ)
      = (Nat.card h.D : ℝ) * ((R.subgroupOf h.S).index : ℝ) * ((Nat.card h.Q1 : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq, Nat.cast_one]
  have hcast : ((R.subgroupOf h.H).index : ℝ)
      = (((R ⊔ h.Q1).subgroupOf h.H).index : ℝ)
        + ((Nat.card h.D * (R.subgroupOf h.S).index * (Nat.card h.Q1 - 1) : ℕ) : ℝ) := by
    rw [← Nat.cast_add, hadd]
  rw [hcast, hZ]
  ring

end Work.FeitSibley.Coherence
