import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseK15.Derive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.count_PL_le` — the support count of `f_L` (FS `count_PL`)

FS's cutoff `f_L` vanishes outside the low-momentum region `P_L` (`fL_supp`),
so the modes on which `f_L ≠ 0` all have `‖kmom s‖ ≤ K_L√(μa)`.  The mode labels
are dual-lattice points `ℓ⁻¹ • vec n` with `vec n = 2πn` (`OnDualLattice`), and
`ℓ K_L√(μa) = K_ℓ K_L` (`hell`), so the supported modes inject into the lattice
ball of radius `K_ℓ K_L`; the lattice ball of radius `ρ ≥ 1` has at most
`Ccard(ρ+1)³ ≤ Ccard·8ρ³ ≤ K₀ρ³` points (`card_le`, `K₀_card`).

This is the K2 field `count_PL` of `Work.BoseB7A.Q3Kernel` (`Defs.lean` §4),
needed by the `Est1` chapter to bound the number of summands of the low-momentum
part of `Q3`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseK15

/-- **The support count of `f_L`.**  The number of excited modes on which FS's
cutoff `f_L` does not vanish is at most `K₀(K_ℓK_L)³`. -/
theorem count_PL_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    {K₀ : ℝ} (h : Work.BoseK15.K15Input K₀ F T E)
    (hell : h.ell * E.KL * Real.sqrt (E.mu * E.aScat) = E.Kl * E.KL)
    (hKL : 1 ≤ E.Kl * E.KL) :
    (((Work.BoseB7.excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) ≤ K₀ * (E.Kl * E.KL) ^ 3 := by
  -- The supported modes sit in the lattice ball of radius `K_ℓK_L`.
  set S : Finset Mode := (Work.BoseB7.excited Mode).filter (fun s => E.fL s ≠ 0) with hSdef
  have hTnorm : ∀ n ∈ S.image h.hlat.lift, ‖Work.BoseB4.vec n‖ ≤ E.Kl * E.KL := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨s, hsS, rfl⟩ := hn
    rw [hSdef, Finset.mem_filter] at hsS
    obtain ⟨-, hsfL⟩ := hsS
    -- `s` is supported by `f_L`, hence `‖kmom s‖ ≤ K_L√(μa)`
    have hsupp : ‖F.kmom s‖ ≤ E.KL * Real.sqrt (E.mu * E.aScat) := by
      have h1 : h.fLf (h.kmom s) ≠ 0 := by rwa [← h.fL_eq s]
      have h2 := h.fL_supp (h.kmom s) h1
      rwa [← h.kmom_eq s] at h2
    -- `vec (lift s) = ℓ • kmom s`
    have hkey : Work.BoseB4.vec (h.hlat.lift s) = h.ell • F.kmom s := by
      have hsp := h.hlat.lift_spec s
      rw [← h.kmom_eq s] at hsp
      rw [hsp, smul_smul, mul_inv_cancel₀ (ne_of_gt h.ell_pos), one_smul]
    rw [hkey, norm_smul, Real.norm_eq_abs, abs_of_pos h.ell_pos]
    calc h.ell * ‖F.kmom s‖ ≤ h.ell * (E.KL * Real.sqrt (E.mu * E.aScat)) :=
          mul_le_mul_of_nonneg_left hsupp (le_of_lt h.ell_pos)
      _ = E.Kl * E.KL := by rw [← mul_assoc]; exact hell
  -- The lattice ball count at radius `ρ = K_ℓK_L ≥ 1`.
  have hcard : (S.card : ℝ) ≤ h.Ccard * (E.Kl * E.KL + 1) ^ 3 := by
    have hc := h.card_le (S.image h.hlat.lift) (E.Kl * E.KL) (by linarith) hTnorm
    rwa [Finset.card_image_of_injective _ h.hlat.lift_injective] at hc
  have hC : h.Ccard ≤ K₀ / 8 := by linarith [h.K₀_card]
  have hpow : (E.Kl * E.KL + 1) ^ 3 ≤ 8 * (E.Kl * E.KL) ^ 3 := by
    have h2 : E.Kl * E.KL + 1 ≤ 2 * (E.Kl * E.KL) := by linarith
    calc (E.Kl * E.KL + 1) ^ 3 ≤ (2 * (E.Kl * E.KL)) ^ 3 :=
          pow_le_pow_left₀ (by linarith) h2 3
      _ = 8 * (E.Kl * E.KL) ^ 3 := by ring
  calc (S.card : ℝ) ≤ h.Ccard * (E.Kl * E.KL + 1) ^ 3 := hcard
    _ ≤ (K₀ / 8) * (8 * (E.Kl * E.KL) ^ 3) := by
        refine mul_le_mul hC hpow (by positivity) (by linarith [h.K₀_one])
    _ = K₀ * (E.Kl * E.KL) ^ 3 := by ring

end Work.BoseK15
