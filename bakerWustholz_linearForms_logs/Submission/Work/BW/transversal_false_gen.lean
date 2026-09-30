import Mathlib
import Submission.Work.BW.multiplicity_engine
import Submission.Work.BW.ze_cancel_false_gen
import Submission.Work.BW.descFactorial_floor_mul_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped BigOperators

/-! # The transversal exclusion in the partially degenerate case (`N < r`, `ε = false`)

This is the `ε = false` transversal exclusion of the multiplicity engine, stated without the
`ZEData` bundle and for an arbitrary point sequence `θ` (the engine only ever uses the *number*
`cardMod false M θ (Sq m)`):

the zero-estimate inequality (`hineq`) at the transversal value `L = 1 + ρ` transfers to
`(Sq ρ + 1) * C(Tq ρ + 1 + ρ, 1 + ρ) * |Δ_J| ≤ (N+1).descFactorial (ρ+1) * ⌊δ 0⌋ * ∏_{J} ⌊δ i.succ⌋`,
which contradicts the interpolation inequality (E1) at step `ρ` with `e = indT0 J`. -/

lemma transversal_false_gen {N r : ℕ} (hNr : N < r)
    (δ : Fin (N + 1) → ℝ) (hδnn : ∀ i, 0 ≤ δ i) (hδ0 : 1 ≤ δ 0) (hδ1 : ∀ i, 1 ≤ ⌊δ i⌋₊)
    (Sq Tq : ℕ → ℕ) (hSa : ∀ m, m < N → Sq (m + 1) ≤ Sq m)
    (hTa : ∀ m, m < N → Tq (m + 1) ≤ Tq m)
    (hE1 : ∀ m, m < r → ∀ e : Fin (N + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, δ i ^ e i <
        ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ))
    (θ : Fin N → ℂ) (ρ : ℕ) (M : Fin ρ → Fin N → ℤ) (m : ℕ)
    (hρN : ρ ≤ N) (hM : PrimSys M) (hm : m + 1 ≤ 1 + ρ)
    (hcard : Sq m + 1 ≤ cardMod false M θ (Sq m))
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
      (((Tq m + (1 + ρ)).choose (1 + ρ) : ℕ) : ℝ) * (cardMod false M θ (Sq m) : ℝ) *
        ((N + 1 - (1 + ρ)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * 1 *
        ∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊δ i⌋₊ : ℕ) : ℝ)) :
    False := by
  classical
  have hρr : ρ < r := lt_of_le_of_lt hρN hNr
  have hmρ : m ≤ ρ := by omega
  obtain ⟨J, hJ, hΔ⟩ := exists_minorJ_ne_zero M hM.1
  -- put `hineq` in the form consumed by the transfer (`ρ + 1` instead of `1 + ρ`)
  have hineq' : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
      (((Tq m + (ρ + 1)).choose (ρ + 1) : ℕ) : ℝ) * (cardMod false M θ (Sq m) : ℝ) *
        ((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * 1 *
        ∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊δ i⌋₊ : ℕ) : ℝ) := by
    intro J hJ hΔ
    have h := hineq J hJ hΔ
    simpa only [Nat.add_comm 1 ρ] using h
  -- the transfer: cancel `cardMod`, the complement product and the factorial
  have hred := ze_cancel_false_gen (N := N) (δ := δ) (hδ1 := hδ1) (Sq := Sq) (Tq := Tq)
    (hSa := hSa) (hTa := hTa) (θ := θ) (ρ := ρ) (i := ρ) (j := ρ + 1) (M := M)
    (m := m) (L := ρ + 1) (hL := rfl) (hmi := hmρ) (hiN := hρN) (hρN := hρN)
    (hcard := hcard) (hineq := hineq') (J := J) (hJ := hJ) (hΔ := hΔ)
  have hΔ1 : (1 : ℝ) ≤ |(minorJ M J hJ : ℝ)| := one_le_abs_minorJ hΔ
  have hCnn : (0 : ℝ) ≤ ((Sq ρ : ℝ) + 1) * ((Tq ρ + (ρ + 1)).choose (ρ + 1) : ℝ) := by
    positivity
  have hle1 : ((Sq ρ : ℝ) + 1) * ((Tq ρ + (ρ + 1)).choose (ρ + 1) : ℝ) ≤
      ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊δ 0⌋₊ : ℕ) : ℝ) *
        ∏ i ∈ J, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) := by
    calc ((Sq ρ : ℝ) + 1) * ((Tq ρ + (ρ + 1)).choose (ρ + 1) : ℝ)
        = (((Sq ρ : ℝ) + 1) * ((Tq ρ + (ρ + 1)).choose (ρ + 1) : ℝ)) * 1 := by ring
      _ ≤ (((Sq ρ : ℝ) + 1) * ((Tq ρ + (ρ + 1)).choose (ρ + 1) : ℝ)) *
            |(minorJ M J hJ : ℝ)| := mul_le_mul_of_nonneg_leftℝ hΔ1 hCnn
      _ ≤ ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊δ 0⌋₊ : ℕ) : ℝ) *
            ∏ i ∈ J, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) := hred
  -- replace floors by reals and `N + 1` by the ambient dimension `r + 1`
  have hle2 := descFactorial_floor_mul_le (N := N) (r := r) hNr ρ δ hδnn J
  -- (E1) at step `ρ` with `e = indT0 J`
  have hE1ρ := hE1 ρ hρr (indT0 J) (indT0_le_one J) (by rw [sum_indT0]; omega)
  rw [prod_delta_indT0] at hE1ρ
  have hlt : ((Sq ρ : ℝ) + 1) * ((Tq ρ + (ρ + 1)).choose (ρ + 1) : ℝ) <
      ((Sq ρ : ℝ) + 1) * ((Tq ρ + (ρ + 1)).choose (ρ + 1) : ℝ) := by
    calc ((Sq ρ : ℝ) + 1) * ((Tq ρ + (ρ + 1)).choose (ρ + 1) : ℝ)
        ≤ ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊δ 0⌋₊ : ℕ) : ℝ) *
            ∏ i ∈ J, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) := hle1
      _ ≤ ((r + 1).descFactorial (ρ + 1) : ℝ) * δ 0 * ∏ i ∈ J, δ i.succ := hle2
      _ < ((Sq ρ : ℝ) + 1) * ((Tq ρ + (ρ + 1)).choose (ρ + 1) : ℝ) := by
            have h := hE1ρ
            rw [show ((r + 1).descFactorial (ρ + 1) : ℝ) * (δ 0 * ∏ i ∈ J, δ i.succ)
                = ((r + 1).descFactorial (ρ + 1) : ℝ) * δ 0 * ∏ i ∈ J, δ i.succ
                from by ring] at h
            exact h
  exact absurd hlt (lt_irrefl _)

end Work.BW
