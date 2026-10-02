import Submission.Work.Deep.Nibble.exists_assemblyData
import Submission.Work.Deep.Nibble.Blocks
import Submission.Work.Deep.Nibble.AbsorbImport

/-!
# The absorption margins from the assembly parameters

The §7 assembly (`nibbleConclusion_of_assembly`) consumes the §7.2 absorption at
pseudorandomness parameter `γp` in the form of the cone's margin bundles
`InternalMargins n ρ ε γp κ ξ` (`Submission/EFL/InternalAbsorption.lean`) and
`CrossingMargins n ρ ε γp κ ξ` (`Submission/EFL/CrossingAbsorption.lean`).

This module derives both bundles from the numeric conditions that the assembly
itself supplies about its parameters (`AssemblyParams`), so that the final glue
never has to mention the absorption margins again.

The only field that is *not* a consequence of `AssemblyParams` is the crossing
absorption's `1000 ξ ≤ γp ρ²`: `AssemblyParams` only gives `4000 ξ ≤ γp ρ`.  With
`γp = γ/4` (the assembly's choice) the missing field follows from
`4000 ξ ≤ γ ρ²` — the repair (D8 of `HANDOFF.md`, "SESSION 5") of the seeded
margin bundle, which the callers of this chapter supply.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

/-- **`InternalMargins` from `AssemblyParams`.** -/
theorem internalMargins_of_assemblyParams {n : ℕ} {D β γ ε ρ ξ κ γp δ βp : ℝ} {K : ℕ}
    (h : AssemblyParams n D β γ ε ρ ξ κ γp δ βp K)
    (hρ1 : ρ ≤ 1) (hε4 : 4000 * ε ≤ 1) (hξ0 : 0 < ξ) :
    InternalMargins n ρ ε γp κ ξ := by
  have hγp0 : 0 < γp := h.hγp0
  have hρ0 : 0 < ρ := by
    have h1 := h.hγpρ
    linarith [h1, hγp0]
  have hε0 : 0 < ε := by
    have h1 := h.hγpε
    have h2 : 0 < γp * ρ := mul_pos hγp0 hρ0
    by_contra hcon
    push Not at hcon
    nlinarith [h1, h2, hcon]
  have hγphalf : 2 * γp ≤ 1 := by
    have h1 := h.hγpρ
    linarith [h1, hρ1, hγp0]
  have hε8 : 2 * ε ≤ 1 / 8 := by linarith
  exact
    { hρ := hρ0
      hρ1 := hρ1
      hε := hε0
      hγ := hγp0
      hκ := h.hκ0
      hξ := hξ0
      hε4 := hε4
      hγρ := h.hγpρ
      hκγ := h.hκγ
      hκγρ := h.hκγρ
      hnbig := h.hγpbig
      hξγρ := h.hγpξε
      hγε := h.hγpε
      hκγε := h.hκγε
      hκγ2 := h.hκγ2
      hεhalf := hε8
      hγhalf := hγphalf
      hγn := h.hγpn }

/-- **`CrossingMargins` from `AssemblyParams`**, using the crossing absorption's
extra `4000 ξ ≤ γ ρ²` (defect D8 of the seeded margin bundle). -/
theorem crossingMargins_of_assemblyParams {n : ℕ} {D β γ ε ρ ξ κ γp δ βp : ℝ} {K : ℕ}
    (h : AssemblyParams n D β γ ε ρ ξ κ γp δ βp K)
    (hρ1 : ρ ≤ 1) (hε4 : 4000 * ε ≤ 1) (hξ0 : 0 < ξ) (hD8 : 4000 * ξ ≤ γ * ρ ^ 2) :
    CrossingMargins n ρ ε γp κ ξ := by
  have hγp0 : 0 < γp := h.hγp0
  have hρ0 : 0 < ρ := by
    have h1 := h.hγpρ
    linarith [h1, hγp0]
  have hε0 : 0 < ε := by
    have h1 := h.hγpε
    have h2 : 0 < γp * ρ := mul_pos hγp0 hρ0
    by_contra hcon
    push Not at hcon
    nlinarith [h1, h2, hcon]
  -- `1 ≤ n`
  have hgp1 : γp ≤ 1 := by
    have h1 := h.hγpρ
    linarith [h1, hρ1]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have h1 := h.hγpbig
    have h2 : γp * ρ ≤ 1 := by nlinarith [hgp1, hρ1, hγp0, hρ0]
    by_contra hcon
    push Not at hcon
    have h3 : (n : ℝ) < 1 := hcon
    have h4 : γp * ρ * (n : ℝ) ≤ γp * ρ * 1 :=
      mul_le_mul_of_nonneg_left (le_of_lt h3) (by positivity)
    linarith
  have hξρ : ξ ≤ ρ := by
    have h1 := h.hγpξε
    have h3 : γp * ρ ≤ ρ := by nlinarith [hgp1, hρ0]
    linarith [h1, h3]
  have hξγρ : 1000 * ξ ≤ γp * ρ ^ 2 := by
    have h1 := h.hγpξε
    have hρ2 : 0 < ρ ^ 2 := by positivity
    have h3 : γ * ρ ^ 2 ≤ 4 * γp * ρ ^ 2 := by nlinarith [h.hγpγ, hρ2]
    linarith [h1, h3, hD8]
  exact
    { hn := by exact_mod_cast hn1
      hρ := hρ0
      hε := hε0
      hγ := hγp0
      hκ := h.hκ0
      hξ := hξ0
      hε2 := by linarith
      hρ2 := hρ1
      hκγ := by linarith [h.hκγρ, h.hκ0]
      hγρ := by linarith [h.hγpρ, hγp0]
      hξρ := hξρ
      hξγρ := hξγρ }

end

end Work.Deep.Nibble
