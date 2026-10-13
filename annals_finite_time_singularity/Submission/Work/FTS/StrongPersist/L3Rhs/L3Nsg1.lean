/-
# `Work.FTS.StrongPersist.L3Rhs.L3Nsg1` — the `ℋ³` bound for the single summand `N₁^{sg}`

The row-10 `sg`-summand of the level-three right-hand side of the modulated `g`-equation:

`N₁^{sg} = 2 ℛ(Φ̃_*) · f`,  `ℛ(Φ̃_*) = Rop α (PhiTs α Φs)`,

with the elliptic residual `Φ̃_*` priced by the star package `StarPkgo2 α Cs Φs` and the
modulation `f` by `H6Adm α f` and `Xn α f ≤ M`.

## Route

Write `H := StarH α Φs = ((z+1)/z)·ℛ(Φ̃_*)` (the weighted star coefficient, `WlInfMem α 4 H`
and `|H|_{𝒲^{4,∞}} ≤ Cs·α` by the `RW` field of `StarPkgo2`), and `φ(z) = z/(1+z)`, so that

`N₁^{sg} = 2 · H · (φ·f)`  on the open quadrant (the only place `HkIntegrand` sees).

* the radial factor costs nothing: `HkMem α 4 (φ·f)` and `Xn α (φ·f) ≤ Cφ·Xn α f`
  (`NRow10aux.mul_phi_Hk`, from `HQo α 4 f`);
* the level-four `𝒲^{4,∞}`-product rule `OpenPkg.wprod_field_winf` gives
  `HkMem α 4 (H·(φf))` and `Xn α (H·(φf)) ≤ Cw α^{-1/2} |H|_{𝒲^{4,∞}} Xn α (φf)`;
* `ℋ³ ⊂ ℋ⁴` (`StrongLWP.HkNorm_mono_of_mem`, `StrongPersist.HkMem_of_le_of_smoothOpen`),
  `HkNorm_smul` for the factor `2`, and `HkSq_congr_open`/`HkMem_congr_Q0` to transfer from
  the product to the literal `N₁^{sg}`;
* the final arithmetic collects `α^{-1/2}·α = α^{1/2} ≤ 1`, `max Cs 0 ≤ 1 + |Cs|`, `M ≤ 1 + M`
  and `1 ≤ α^{-1}`.

-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.OpenPkg.wprod_field_winf
import Submission.Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
import Submission.Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen
import Submission.Work.FTS.NonlinRows.NRow10
import Submission.Work.FTS.NonlinRows.NRow10T2
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.EggBound
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.ScaleAPI
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.FieldRegularity
import Submission.Work.FTS.StrongLWP.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1600000

namespace Work.FTS.StrongPersist.L3Rhs

theorem L3Nsg1 : ∃ C : ℝ, 0 < C ∧
    ∀ (α Cs M : ℝ) (Φs f : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.StrongPersist.H6Adm α f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      Work.Spaces.HkMem α 3 (Work.FTS.Nonlin.N1sg α Φs f) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f)
        ≤ C * (1 + |Cs|) * α ^ (-(1 : ℝ)) * (1 + M) := by
  obtain ⟨Cw, hCw, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨Cp, hCp, hphib⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  refine ⟨2 * Cw * Cp + 1, by positivity, ?_⟩
  intro α Cs M Φs f hα hα1 hs hadm hM
  -- the weighted star coefficient `H` and its `𝒲^{4,∞}`-bounds
  obtain ⟨hHmem, hHle⟩ := Work.FTS.NonlinRows.starH_mem_of_StarPkgo2 hs
  have hHsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.NonlinRows.StarH α Φs) :=
    Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen hα hα1 hs.toStarPkgo
  -- the modulation factors through the bounded radial factor `φ(z) = z/(1+z)`
  have hf4 : Work.FTS.VocabO.HQo α 4 f :=
    ⟨hadm.reg.1, Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hadm.reg.1
      hadm.reg.2⟩
  obtain ⟨hGmem, hGbnd⟩ := hphib (g := f) hα hα1 hf4
  have hGsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * f z θ) := by
    have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) := by
      simpa only [Work.FTS.NonlinRows.NRow10aux.phiF] using
        Work.FTS.NonlinRows.NRow10aux.phiSelf_smoothOpen
    exact Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul h1 hadm.reg.1
  -- the level-four `𝒲^{4,∞}`-priced product rule
  obtain ⟨hPmem4, hPbd4⟩ := hwprod α hα hα1 (Work.FTS.NonlinRows.StarH α Φs)
      (fun z θ => z / (1 + z) * f z θ) hHsm hHmem ⟨hGsm, hGmem⟩
  have hPsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ)) :=
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul hHsm hGsm
  -- the row is `2` times the product on the open quadrant
  have hagree : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      2 * (Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ))
        = Work.FTS.Nonlin.N1sg α Φs f z θ := by
    intro z θ hz _ _
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := by positivity
    simp only [Work.FTS.Nonlin.N1sg, Work.FTS.NonlinRows.StarH]
    field_simp
    ring
  -- elementary facts about the data
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Real.sqrt_nonneg _
  have hM0 : 0 ≤ M := le_trans hXn0 hM
  have hHle' : Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.StarH α Φs) ≤ max Cs 0 * α :=
    le_trans hHle (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
  have hGbnd' : Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * f z θ) ≤ Cp * M :=
    le_trans hGbnd (mul_le_mul_of_nonneg_left hM hCp.le)
  have hXG0 : 0 ≤ Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * f z θ) := Real.sqrt_nonneg _
  have hq0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hCsα : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right Cs 0) hα.le
  -- the level-four estimate, priced by `max Cs 0 * α` and `Cp * M`
  have hstep : Work.Spaces.HkNorm α 4
      (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ))
      ≤ Cw * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α) * (Cp * M) := by
    refine le_trans hPbd4 ?_
    calc Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.StarH α Φs)
            * Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * f z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α)
            * Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * f z θ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hHle' (mul_nonneg hCw.le hq0)) hXG0
      _ ≤ Cw * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α) * (Cp * M) :=
          mul_le_mul_of_nonneg_left hGbnd' (mul_nonneg (mul_nonneg hCw.le hq0) hCsα)
  constructor
  · -- `ℋ³`-membership: descend from level four, scale by `2`, transfer along `Q0`
    have hPmem3 : Work.Spaces.HkMem α 3
        (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ)) :=
      Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hPsm hPmem4
    have h2P : Work.Spaces.HkMem α 3
        (fun z θ => 2 * (Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ))) :=
      Work.FTS.Nonlinear.Pieces.Rl1.HkMem_const_mul_of 2 hPmem3
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 3 h2P ?_
    intro z hz θ hθ
    exact hagree z θ hz hθ.1 hθ.2
  · -- the norm bound
    have hPbd3 : Work.Spaces.HkNorm α 3
        (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ))
        ≤ Work.Spaces.HkNorm α 4
        (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ)) :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 4) (k' := 3) (by norm_num) hPmem4
    have hSeq : Work.Spaces.HkSq α 3 (Work.FTS.Nonlin.N1sg α Φs f)
        = Work.Spaces.HkSq α 3
          (fun z θ => 2 * (Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ))) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 3
        (fun z θ hz hθ0 hθ1 => (hagree z θ hz hθ0 hθ1).symm)
    have hnorm_eq : Work.Spaces.HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f)
        = 2 * Work.Spaces.HkNorm α 3
          (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ)) := by
      rw [show Work.Spaces.HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f)
            = Work.Spaces.HkNorm α 3
              (fun z θ => 2 * (Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ)))
            from by simp only [Work.Spaces.HkNorm, hSeq],
        show (fun z θ => 2 * (Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ)))
            = (2 : ℝ) • (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ))
            from by funext z θ; simp,
        Work.FTS.EllipticEst.HkNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have harith : 2 * (Cw * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α) * (Cp * M))
        ≤ (2 * Cw * Cp + 1) * (1 + |Cs|) * α ^ (-(1 : ℝ)) * (1 + M) := by
      have hqα : α ^ (-(1 / 2 : ℝ)) * α ≤ 1 := by
        have h1 : α ^ (-(1 / 2 : ℝ)) * α ^ (1 : ℝ) ≤ 1 := by
          rw [← Real.rpow_add hα (-(1 / 2 : ℝ)) 1, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
          exact Real.rpow_le_one hα.le hα1 (by norm_num)
        rwa [Real.rpow_one] at h1
      have hR1 : max Cs 0 ≤ 1 + |Cs| :=
        max_le (le_trans (le_abs_self Cs) (by linarith [abs_nonneg Cs])) (by positivity)
      have hRM : max Cs 0 * M ≤ (1 + |Cs|) * (1 + M) :=
        mul_le_mul hR1 (by linarith) hM0 (by positivity)
      have hα1' : (1 : ℝ) ≤ α ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg_one]
        exact (one_le_inv₀ hα).mpr hα1
      have hnn : (0 : ℝ) ≤ 2 * Cw * Cp * (max Cs 0) * M := by positivity
      calc 2 * (Cw * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α) * (Cp * M))
          = 2 * Cw * Cp * (max Cs 0) * M * (α ^ (-(1 / 2 : ℝ)) * α) := by ring
        _ ≤ 2 * Cw * Cp * (max Cs 0) * M * 1 := mul_le_mul_of_nonneg_left hqα hnn
        _ = 2 * Cw * Cp * ((max Cs 0) * M) := by ring
        _ ≤ 2 * Cw * Cp * ((1 + |Cs|) * (1 + M)) :=
            mul_le_mul_of_nonneg_left hRM (by positivity)
        _ = 2 * Cw * Cp * (1 + |Cs|) * (1 + M) := by ring
        _ ≤ (2 * Cw * Cp + 1) * (1 + |Cs|) * (1 + M) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
        _ ≤ (2 * Cw * Cp + 1) * (1 + |Cs|) * (1 + M) * α ^ (-(1 : ℝ)) :=
            le_mul_of_one_le_right (by positivity) hα1'
        _ = (2 * Cw * Cp + 1) * (1 + |Cs|) * α ^ (-(1 : ℝ)) * (1 + M) := by ring
    calc Work.Spaces.HkNorm α 3 (Work.FTS.Nonlin.N1sg α Φs f)
        = 2 * Work.Spaces.HkNorm α 3
            (fun z θ => Work.FTS.NonlinRows.StarH α Φs z θ * (z / (1 + z) * f z θ)) := hnorm_eq
      _ ≤ 2 * (Cw * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α) * (Cp * M)) :=
          mul_le_mul_of_nonneg_left (le_trans hPbd3 hstep) (by norm_num)
      _ ≤ (2 * Cw * Cp + 1) * (1 + |Cs|) * α ^ (-(1 : ℝ)) * (1 + M) := harith

end Work.FTS.StrongPersist.L3Rhs
