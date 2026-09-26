import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.K24FDefs
import Submission.Work.Asymptotics.K24FBase
import Submission.Work.Asymptotics.K24F_sm_sum_bound
import Submission.Work.Asymptotics.DeltaFun_imagAxis_lower_sharp
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.E_jdiff_large
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.tile_Bdd_atoms
import Submission.Work.Asymptotics.Tile.HalfDev24Defs
import Submission.Work.Asymptotics.Tile.HalfDev24Aux
import Submission.Work.Asymptotics.Tile.HalfDev24TileFacts

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane
open Work.Kernels

noncomputable section

set_option maxHeartbeats 2000000

/-! ## Positivity of the constant `c` of the cleared identity -/

lemma norm_K24Fc_pos : 0 < ‖K24F.c‖ := by
  rw [norm_pos_iff, K24F.c]
  refine inv_ne_zero ?_
  have h1 : ((Real.pi : ℂ)) ^ (-2 : ℤ) ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num)) h1)
    Complex.I_ne_zero


/-- **Far-region deviation of `K_+^{(24)}` on the cusp-`±1` tiles, `3 ≤ t`.**

For `w ∈ E = KEpsilon`, `n = ±1` and `z = i t` with `3 ≤ t ≤ Im (S • w) − 1`, the deviation
of `K_+^{(24)}` from `𝒢_+^{(24)}` is polynomially bounded in `scale w` and `t`.

Unlike `d = 8`, *both halves* are exponentially large here
(`‖KPlus 24 (n+ᵥw) (it)‖ ≍ e^{2πt}` and likewise for `Gplus 24`), so the content is the
cancellation between them.  The clean way to organise it is the exact cleared identity
`Work.Asymptotics.K24F.KPlus24_diff` (proved, in `Submission/Work/Asymptotics/K24FDefs.lean`):
`Δ(z)·(j τ − j z)·(KPlus 24 τ z − Gplus 24 τ z) = c z² (Sm1 τ z + … + Sm5 τ z)`
(valid for `j τ ≠ j z` and `E₄(z) ≠ 0`; for `z = i t` with `t ≥ 3` use
`Work.Asymptotics.K24F.E4_ne_zero_three`, and note `j τ = j w ≠ j(i t)` since `Im w ≤ 1/2`).
It therefore suffices to show
`‖Sm1 + … + Sm5‖ ≤ C (scale w)^N e^{2π(Im(S•w) − t)} t^M` (for the `4 ≤ Im(S•w)` needed) and
to combine with the sharp divisor bound `c e^{2π(Im(S•w)−t)} ≤ ‖Δ(i t)(j τ − j(i t))‖`
(which follows from `Work.Asymptotics.DeltaFun_imagAxis_lower_sharp` and
`Work.Asymptotics.E_jdiff_large`, the latter's exponential factor being
`e^{2π Im(S•w)}`; `‖1 − e^{2πi((S•w) − it)}‖ ≥ 1/2` because `t ≤ Im(S•w) − 1`).

The individual `Sm i` are bounded as follows (each is a sum of products
`τ-atom × z-dev`), using:
* the `τ`-atom bounds at `n + ᵥ w` (`r0 = τE₁₄(τ)`, `r1 = φ₀(τ)Δ(τ)`, `R0 = r1·j(τ) = φ₀(τ)E₄(τ)³`,
  `r2 = φ₂(τ)E₁₀(τ)`, `j(τ)`) via the `Work.Asymptotics.EtailE.Bdd` calculus
  (`Submission/Work/Asymptotics/tile_Bdd_atoms.lean`, `Bdd.exists_bound_zero`,
  `Bdd.shift`, `Bdd.mul_zero`): all are `O((scale w)^N)`, while `j(τ)` is
  `O((scale w)^N e^{2π Im(S•w)})` (`EtailE.E_bdd_j` shifted);
* the expansions in `Submission/Work/Asymptotics/K24FBase.lean`
  (`Phi_sub_Phiref_expanded`, `Phi_sub_Phiref_sub_expanded`, `Sm3_bracket`, `Sm4_split`,
  `Sm5_split`, and the `j`-free rewrites `K24Fsm.phiref_jfree`, `K24Fsm.q1_jfree`), which
  write `Φ − Φref`, `Φ − Φref − q Q1`, `Sm3`, `Sm4`, `Sm5` as *linear* combinations of the
  `τ`-atoms against the `z`-deviations `E₄(z)−1`, `E₂S(z)²−S0(z)²`, `E₆(z)E₂S(z)/E₄(z)−S0(z)`,
  `E₄(z)−1−240q`, `B2 z`, `S0(z)(E₄(z)³−1)`, `q/Δ(z)−1`, `1/Δ(z)−1/q−24`, `1−Δ(z)/q`,
  `U − Uref`;
* the `z`-side bounds `Work.Asymptotics.K24Fsm.zdev` (needs `3 ≤ z.im`; a pure `z`-statement:
  each of the above deviations is `≤ A‖qParamFun z‖` resp. `≤ A‖qParamFun z‖²`, plus
  `‖1/Δ(z)‖ ≤ A/‖q(z)‖`, `‖1/E₄(z)‖ ≤ 2`, `‖E₄(z)‖ ≤ 3/2`, `‖S0(z)‖ ≤ 3`,
  `‖q(z)‖/2 ≤ ‖Δ(z)‖`), with `‖qParamFun (i t)‖ = e^{−2πt}`
  (`Work.Asymptotics.norm_qParamFun`) and `K24Fsm.S0_eq_S0c`;
* hence for `Sm1`, `Sm2`, `Sm5` (which carry one factor `j(τ)` resp. `Δ(z)j(τ)`) one gets
  `O((scale w)^N e^{2π(Im(S•w)−t)} t^M)` (using `‖Δ(z)‖ ≤ 2e^{−2πt}` from
  `Work.Asymptotics.DeltaFun_upper_sharp`), while `Sm3`, `Sm4` are even smaller
  (`O((scale w)^N t^M e^{−2πt})`).

There is no need to prove anything at the funnels: `K24F_sm_sum_bound` is stated for
`Funnel τ` and does not apply at `τ = n + ᵥ w`. -/
theorem halfDevFar24High :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) (t : ℝ),
        (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        (z : ℂ) = (t : ℂ) * Complex.I → 3 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Kernels.KPlus 24 ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gplus 24 ((n : ℝ) +ᵥ w) z‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M := by
    obtain ⟨KA, NA, hKAp, hNA, hAtoms⟩ := H24.tileAtoms24_axis
    obtain ⟨Ks, Ns, hKsp, hNsp, hSmsum⟩ := sm_sum_le_atoms
    obtain ⟨cD, hcDp, hDlow⟩ := H24.divisor_lower_sharp
    refine ⟨‖K24F.c‖ * (4 * Ks * (KA + 1) ^ 2 * 4 ^ Ns) / cD, 2 * NA + Ns, 2, ?_, ?_, ?_, ?_⟩
    · exact div_pos (mul_pos norm_K24Fc_pos (by positivity)) hcDp
    · linarith
    · norm_num
    · intro w n z t hn hw hz ht3 htle
      have ht0 : (0 : ℝ) < t := by linarith
      set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
      have hzs : z.im = t := K24F.im_of_coe_eq_axis hz
      have hz3 : (3 : ℝ) ≤ z.im := by rw [hzs]; exact ht3
      have hs1 : (1 : ℝ) ≤ scale w := one_le_scale w
      have hs0 : (0 : ℝ) < scale w := scale_pos w
      set E : ℝ := Real.exp (2 * Real.pi * (ModularGroup.S • w).im) with hEdef
      have hE1 : (1 : ℝ) ≤ E := by
        rw [hEdef, ← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by positivity)
      set O : ℝ := Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t)) with hOdef
      have hOpos : 0 < O := by rw [hOdef]; exact Real.exp_pos _
      set D : ℝ := (KA + 1) * (scale w) ^ NA with hDdef
      set Dj : ℝ := (KA + 1) * (scale w) ^ NA * E with hDjdef
      have hD0 : 0 ≤ D := by rw [hDdef]; positivity
      have hDj0 : 0 ≤ Dj := by rw [hDjdef]; positivity
      have hsNA : (1 : ℝ) ≤ (scale w) ^ NA := Real.one_le_rpow hs1 hNA
      have hsNA0 : (0 : ℝ) ≤ (scale w) ^ NA := Real.rpow_nonneg hs0.le NA
      have hD1 : (1 : ℝ) ≤ D := by
        rw [hDdef]
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (KA + 1) * (scale w) ^ NA :=
              mul_le_mul (by linarith) hsNA (by norm_num) (by linarith)
      have hDj1 : (1 : ℝ) ≤ Dj := by
        rw [hDjdef]
        calc (1 : ℝ) = 1 * 1 * 1 := by ring
          _ ≤ (KA + 1) * (scale w) ^ NA * E :=
              mul_le_mul (mul_le_mul (by linarith) hsNA (by norm_num) (by linarith)) hE1
                (by norm_num) (by positivity)
      have hAt : TileAtoms24 τ D Dj := by
        have h0 := hAtoms w n hn hw
        have h1 : KA * (scale w) ^ NA ≤ (KA + 1) * (scale w) ^ NA :=
          mul_le_mul_of_nonneg_right (show KA ≤ KA + 1 by linarith) hsNA0
        have h2 : KA * (scale w) ^ NA * E ≤ (KA + 1) * (scale w) ^ NA * E :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
        exact h0.mono (by rw [hDdef]; exact h1) (by rw [hDjdef]; exact h2)
      have hSmb := hSmsum τ z D Dj hD0 hDj0 hAt hz3
      have hscaleτ : scale τ ≤ 4 * scale w := by
        have hcoe : ((τ : ℍ) : ℂ) = ((n : ℝ) : ℂ) + (w : ℂ) := by
          rw [hτdef]; exact UpperHalfPlane.coe_vadd _ _
        have hτim : τ.im = w.im := by
          have h := congrArg Complex.im hcoe
          simpa [UpperHalfPlane.coe_im] using h
        have hn1 : ‖((n : ℝ) : ℂ)‖ = 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          rcases hn with h | h <;> rw [h] <;> norm_num
        have hnorm : ‖(τ : ℂ)‖ ≤ ‖(w : ℂ)‖ + 1 := by
          rw [hcoe]
          calc ‖((n : ℝ) : ℂ) + (w : ℂ)‖ ≤ ‖((n : ℝ) : ℂ)‖ + ‖(w : ℂ)‖ := norm_add_le _ _
            _ = ‖(w : ℂ)‖ + 1 := by rw [hn1]; ring
        have h1 : (w.im)⁻¹ ≤ scale w := by
          rw [Work.Kernels.scale]; linarith [norm_nonneg ((w : ℂ))]
        have h2 : ‖(w : ℂ)‖ ≤ scale w := by
          rw [Work.Kernels.scale]; linarith [inv_nonneg.mpr w.im_pos.le]
        rw [Work.Kernels.scale, hτim]
        nlinarith [h1, h2, hs1, hnorm]
      have hpowτ : (scale τ) ^ Ns ≤ 4 ^ Ns * (scale w) ^ Ns := by
        have h1 : (scale τ) ^ Ns ≤ (4 * scale w) ^ Ns :=
          Real.rpow_le_rpow (scale_pos τ).le hscaleτ hNsp
        rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hs0.le] at h1
      have hprod : (1 + D) * (1 + Dj) ≤ 4 * (KA + 1) ^ 2 * (scale w) ^ (2 * NA) * E := by
        have h1 : 1 + D ≤ 2 * D := by linarith
        have h2 : 1 + Dj ≤ 2 * Dj := by linarith
        have h3 : (1 + D) * (1 + Dj) ≤ (2 * D) * (2 * Dj) :=
          mul_le_mul h1 h2 (by linarith) (by linarith)
        have hs2 : (scale w) ^ NA * (scale w) ^ NA = (scale w) ^ (2 * NA) := by
          rw [← Real.rpow_add hs0]; congr 1; ring
        calc (1 + D) * (1 + Dj) ≤ (2 * D) * (2 * Dj) := h3
          _ = 4 * ((KA + 1) ^ 2 * ((scale w) ^ NA * (scale w) ^ NA) * E) := by
              rw [hDdef, hDjdef]; ring
          _ = 4 * (KA + 1) ^ 2 * (scale w) ^ (2 * NA) * E := by rw [hs2]; ring
      have hexp : E * Real.exp (-(2 * Real.pi * t)) = O := by
        rw [hEdef, hOdef, ← Real.exp_add]
        congr 1; ring
      have hqnorm : ‖qParamFun z‖ = Real.exp (-(2 * Real.pi * t)) := by
        rw [norm_qParamFun, hzs]
      have hkey : ‖K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z + K24F.Sm4 τ z
            + K24F.Sm5 τ z‖
          ≤ 4 * Ks * (KA + 1) ^ 2 * 4 ^ Ns * (scale w) ^ (2 * NA + Ns) * O := by
        refine le_trans hSmb ?_
        calc Ks * (1 + D) * (1 + Dj) * (scale τ) ^ Ns * ‖qParamFun z‖
            = Ks * ((1 + D) * (1 + Dj)) * (scale τ) ^ Ns * ‖qParamFun z‖ := by ring
          _ ≤ Ks * (4 * (KA + 1) ^ 2 * (scale w) ^ (2 * NA) * E) * (4 ^ Ns * (scale w) ^ Ns)
                * ‖qParamFun z‖ := by
              have h1 : Ks * ((1 + D) * (1 + Dj))
                  ≤ Ks * (4 * (KA + 1) ^ 2 * (scale w) ^ (2 * NA) * E) :=
                mul_le_mul_of_nonneg_left hprod hKsp.le
              exact mul_le_mul (mul_le_mul h1 hpowτ (Real.rpow_nonneg (scale_pos τ).le Ns)
                (by positivity)) le_rfl (norm_nonneg _) (by positivity)
          _ = 4 * Ks * (KA + 1) ^ 2 * 4 ^ Ns * (scale w) ^ (2 * NA + Ns) * O := by
              have hstep : Ks * (4 * (KA + 1) ^ 2 * (scale w) ^ (2 * NA) * E)
                    * (4 ^ Ns * (scale w) ^ Ns) * ‖qParamFun z‖
                  = (4 * Ks * (KA + 1) ^ 2 * 4 ^ Ns)
                    * ((scale w) ^ (2 * NA) * (scale w) ^ Ns)
                    * (E * ‖qParamFun z‖) := by ring
              rw [hstep, hqnorm, ← hexp, ← Real.rpow_add hs0]
      have hnum : ‖K24F.c * (z : ℂ) ^ 2 * (K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z
            + K24F.Sm4 τ z + K24F.Sm5 τ z)‖
          ≤ ‖K24F.c‖ * t ^ 2
            * (4 * Ks * (KA + 1) ^ 2 * 4 ^ Ns * (scale w) ^ (2 * NA + Ns) * O) := by
        have hznorm : ‖(z : ℂ)‖ = t := by
          rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos ht0]
        calc ‖K24F.c * (z : ℂ) ^ 2 * (K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z
              + K24F.Sm4 τ z + K24F.Sm5 τ z)‖
            = ‖K24F.c‖ * ‖(z : ℂ) ^ 2‖
              * ‖K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z + K24F.Sm4 τ z
                + K24F.Sm5 τ z‖ := by rw [norm_mul, norm_mul]
          _ = ‖K24F.c‖ * t ^ 2
              * ‖K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z + K24F.Sm4 τ z
                + K24F.Sm5 τ z‖ := by rw [norm_pow, hznorm]
          _ ≤ ‖K24F.c‖ * t ^ 2
              * (4 * Ks * (KA + 1) ^ 2 * 4 ^ Ns * (scale w) ^ (2 * NA + Ns) * O) :=
              mul_le_mul_of_nonneg_left hkey (by positivity)
      have hzt : z = Work.Kernels.imagAxis t ht0 := by
        apply UpperHalfPlane.ext
        rw [hz]
        simp [Work.Kernels.imagAxis]
      have hjτ : jInvariantFun τ = jInvariantFun w := by
        rw [hτdef]
        exact vadd_int_eq_self _ (fun σ => KernelFacts.jInvariantFun_vadd_one σ) n hn w
      have hDv : cD * O ≤ ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := by
        have h := hDlow w t ht0 hw (by linarith : (1 : ℝ) ≤ t) htle
        rw [← hzt, ← hjτ] at h
        rwa [hOdef]
      have hDvpos : 0 < ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
        lt_of_lt_of_le (by positivity : 0 < cD * O) hDv
      have hDvne : DeltaFun z * (jInvariantFun τ - jInvariantFun z) ≠ 0 :=
        norm_pos_iff.mp hDvpos
      have hJne : jInvariantFun τ - jInvariantFun z ≠ 0 := fun h0 => hDvne (by rw [h0, mul_zero])
      have hE4ne : E4Fun z ≠ 0 := K24F.E4_ne_zero_three z hz3
      have hclear := K24F.KPlus24_diff τ z hJne hE4ne
      have hKG : Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z
          = K24F.c * (z : ℂ) ^ 2 * (K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z
              + K24F.Sm4 τ z + K24F.Sm5 τ z)
            / (DeltaFun z * (jInvariantFun τ - jInvariantFun z)) := by
        rw [eq_div_iff hDvne, mul_comm]
        exact hclear
      have hfinal :
          (‖K24F.c‖ * t ^ 2
              * (4 * Ks * (KA + 1) ^ 2 * 4 ^ Ns * (scale w) ^ (2 * NA + Ns) * O))
            / (cD * O)
          = (‖K24F.c‖ * (4 * Ks * (KA + 1) ^ 2 * 4 ^ Ns) / cD)
            * (scale w) ^ (2 * NA + Ns) * t ^ 2 := by
        have hO0 : O ≠ 0 := ne_of_gt hOpos
        have hcD0 : cD ≠ 0 := ne_of_gt hcDp
        field_simp
      have h1 : ‖K24F.c * (z : ℂ) ^ 2 * (K24F.Sm1 τ z + K24F.Sm2 τ z + K24F.Sm3 τ z
            + K24F.Sm4 τ z + K24F.Sm5 τ z)‖
          / ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖
          ≤ (‖K24F.c‖ * t ^ 2
              * (4 * Ks * (KA + 1) ^ 2 * 4 ^ Ns * (scale w) ^ (2 * NA + Ns) * O))
            / (cD * O) := div_le_div₀ (by positivity) hnum (by positivity) hDv
      rw [hKG, norm_div]
      rw [hfinal] at h1
      rw [Real.rpow_two]
      exact h1

end

end Work.Asymptotics.Tile
