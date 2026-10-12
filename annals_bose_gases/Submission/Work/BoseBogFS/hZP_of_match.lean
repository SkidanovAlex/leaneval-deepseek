import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseBogFS.BogFSData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.hZP_of_match` — the zero-point estimate on the abstract
mode group

`Work.BoseB6Est.fsZeroPoint_le` bounds FS's zero-point sum `zpSum` at FS's parameters
in terms of the *mode-lattice* quantities (`meshD`, `latticeSum`, `zpRiemErr`,
`fsMass`, `lhyEps`).  `Work.BoseBogFS.sum_zp_eq` identifies the abstract-group sum
`Σ_k bogZeroPoint (bogA E ρ k) (bogB E ρ k)` with `zpSum` under the mode identification
`FsMatch`, and `Work.BoseB6.lattice_sum_upper` (the one-sided sharp lattice Riemann
bound, `lattice_sum_value`) then replaces the lattice sum by the model value
`-lhyValue (8π)`.

The constant bookkeeping is `half_lhyValue_eight_pi`:
`½·(2π)⁻³·lhyValue (8π) = 4π·lhyC`, which is what turns the model value into FS's
leading LHY term `-4π lhyC ρ²a√(ρa³)ℓ³`.  Everything is linear after that, so the
assembly is the one-line arithmetic core `hZP_arith` below, applied to
`hz` (the `zpSum` bound), `hmesh` (the lattice bound) and `hCV` (the constant identity).
-/

open scoped Real

namespace Work.BoseBogFS

/-- **Arithmetic core of the transfer.**  If `A ≤ C·M·L + A₂ + e + C·r` (`hz`),
`M·L ≤ -V + E` (`hmesh`), `½·C·V = m` (`hCV`) and `0 ≤ C`, then
`½·A ≤ -m + ½·A₂ + ½·(C·(E+r) + e)`.  Halving the chain is what produces the
factor `½` on FS's error bracket. -/
lemma hZP_arith {A Cc ML A2 e Ec Vv Em mc : ℝ} (hCc : 0 ≤ Cc)
    (h1 : A ≤ Cc * ML + A2 + e + Cc * Ec)
    (h2 : ML ≤ -Vv + Em)
    (h3 : (1 / 2) * (Cc * Vv) = mc) :
    (1 / 2) * A ≤ -mc + (1 / 2) * A2 + (1 / 2) * (Cc * (Em + Ec) + e) := by
  have h4 : Cc * ML ≤ Cc * (-Vv + Em) := mul_le_mul_of_nonneg_left h2 hCc
  have h5 : Cc * (-Vv + Em) = Cc * (-Vv) + Cc * Em := by ring
  have h6 : A ≤ Cc * (-Vv) + Cc * Em + A2 + e + Cc * Ec := by linarith
  have h7 := mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h8 : (1 / 2) * (Cc * (-Vv) + Cc * Em + A2 + e + Cc * Ec)
      = -((1 / 2) * (Cc * Vv)) + (1 / 2) * (A2 + (Cc * (Em + Ec) + e)) := by ring
  rw [h8] at h7
  rw [h3] at h7
  have h9 : (1 / 2) * (A2 + (Cc * (Em + Ec) + e))
      = (1 / 2) * A2 + (1 / 2) * (Cc * (Em + Ec) + e) := by ring
  linarith

/-- **FS `eq:BogIntegral`'s zero-point term on the abstract mode group.**  Under the
mode identification `FsMatch` and FS's parameter regime `FsZeroRegime`, the
Bogoliubov zero-point sum is bounded by FS's display: the sharp LHY term
`-4π·lhyC·ρ²a√(ρa³)ℓ³`, the mass term `½ρ²ℓ³Ŵ₁ω(0)` and `½` times the error
bracket (lattice mesh error, discretisation error `zpRiemErr` and FS's
`10¹⁰ε(μ,ρ_z)`). -/
theorem hZP_of_match {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ gHat0 : ℝ)
    (M : Work.BoseBogFS.FsMatch F E ρ gHat0)
    (hreg : Work.BoseB6Est.FsZeroRegime M.n M.D.K M.D.a M.D.R M.D.ρz M.D.ℓ M.D.μ M.D.z
      M.D.chiM M.D.δ M.D.εT M.D.c1 M.D.c2 M.D.Kl M.D.s M.D.d) :
    (∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (Work.BoseBogFS.bogA E ρ k)
        (Work.BoseBogFS.bogB E ρ k))
      ≤ -(4 * π * Work.UBB.lhyC * ρ ^ 2 * E.aScat * E.ell ^ 3
            * Real.sqrt (ρ * E.aScat ^ 3))
        + (1 / 2) * E.ell ^ 3 * ρ ^ 2 * E.W1omega0
        + (1 / 2) * (((2 * π) ^ 3)⁻¹ * E.ell ^ 3
              * (ρ ^ 2 * E.aScat * Real.sqrt (ρ * E.aScat ^ 3))
              * (Work.BoseB6.latticeMeshErr (8 * π) M.n
                  + Work.BoseB6Est.zpRiemErr M.n M.D.K M.D.c2)
            + 10 ^ 10 * Work.BoseB6.lhyEps M.D.a M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ
                * ρ ^ 2 * M.D.a * Real.sqrt (ρ * M.D.a ^ 3) * E.ell ^ 3) := by
  -- `fsZeroPoint_le` at the datum's parameters
  have hz := Work.BoseB6Est.fsZeroPoint_le hreg
  -- the one-sided sharp lattice Riemann bound
  have hmesh := Work.BoseB6.lattice_sum_upper (c := 8 * π) (by positivity) hreg.hn
  -- the prefactor `C = (2π)⁻³ℓ³ρ_z²a√(ρ_z a³)` is nonnegative
  have hCc : 0 ≤ ((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3
      * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3)) := by
    have hρz : 0 < M.D.ρz := hreg.hi1.hρz
    have ha : 0 < M.D.a := hreg.hi1.ha
    have hℓ : 0 < M.D.ℓ := hreg.hℓ
    positivity
  -- `½·C·lhyValue(8π) = 4π·lhyC·ρ_z²aℓ³√(ρ_z a³)`, by `half_lhyValue_eight_pi`
  have hCV : (1 / 2) * ((((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3
          * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3)))
        * Work.BoseB6.lhyValue (8 * π))
      = 4 * π * Work.UBB.lhyC * M.D.ρz ^ 2 * M.D.a * M.D.ℓ ^ 3
        * Real.sqrt (M.D.ρz * M.D.a ^ 3) := by
    have key := Work.BoseBogFS.half_lhyValue_eight_pi
    calc (1 / 2) * ((((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3
            * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3)))
          * Work.BoseB6.lhyValue (8 * π))
        = (M.D.ℓ ^ 3 * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3)))
            * ((1 / 2) * ((2 * π) ^ 3)⁻¹ * Work.BoseB6.lhyValue (8 * π)) := by ring
      _ = (M.D.ℓ ^ 3 * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3)))
            * (4 * π * Work.UBB.lhyC) := by rw [key]
      _ = 4 * π * Work.UBB.lhyC * M.D.ρz ^ 2 * M.D.a * M.D.ℓ ^ 3
            * Real.sqrt (M.D.ρz * M.D.a ^ 3) := by ring
  -- the arithmetic core, at the four concrete slots
  have hmain := hZP_arith
    (A := Work.BoseB6Est.zpSum M.n M.D.ρz M.D.a M.D.K M.D.εT M.D.c1 M.D.c2)
    (Cc := ((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3 * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3)))
    (ML := Work.BoseB6.meshD M.n ^ 3 * Work.BoseB6.latticeSum (8 * π) M.n)
    (A2 := Work.BoseB6Est.fsMass M.D.ρz M.D.a M.D.ℓ M.D.K)
    (e := 10 ^ 10 * Work.BoseB6.lhyEps M.D.a M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ
      * M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3) * M.D.ℓ ^ 3)
    (Ec := Work.BoseB6Est.zpRiemErr M.n M.D.K M.D.c2)
    (Vv := Work.BoseB6.lhyValue (8 * π))
    (Em := Work.BoseB6.latticeMeshErr (8 * π) M.n)
    (mc := 4 * π * Work.UBB.lhyC * M.D.ρz ^ 2 * M.D.a * M.D.ℓ ^ 3
      * Real.sqrt (M.D.ρz * M.D.a ^ 3))
    hCc hz hmesh hCV
  -- the datum's parameters are the envelope's (`FsMatch`)
  have hRHS : -(4 * π * Work.UBB.lhyC * M.D.ρz ^ 2 * M.D.a * M.D.ℓ ^ 3
          * Real.sqrt (M.D.ρz * M.D.a ^ 3))
        + (1 / 2) * Work.BoseB6Est.fsMass M.D.ρz M.D.a M.D.ℓ M.D.K
        + (1 / 2) * ((((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3
                * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3)))
              * (Work.BoseB6.latticeMeshErr (8 * π) M.n
                + Work.BoseB6Est.zpRiemErr M.n M.D.K M.D.c2)
            + 10 ^ 10 * Work.BoseB6.lhyEps M.D.a M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ
                * M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3) * M.D.ℓ ^ 3)
      = -(4 * π * Work.UBB.lhyC * ρ ^ 2 * E.aScat * E.ell ^ 3 * Real.sqrt (ρ * E.aScat ^ 3))
        + (1 / 2) * E.ell ^ 3 * ρ ^ 2 * E.W1omega0
        + (1 / 2) * (((2 * π) ^ 3)⁻¹ * E.ell ^ 3
              * (ρ ^ 2 * E.aScat * Real.sqrt (ρ * E.aScat ^ 3))
              * (Work.BoseB6.latticeMeshErr (8 * π) M.n
                  + Work.BoseB6Est.zpRiemErr M.n M.D.K M.D.c2)
            + 10 ^ 10 * Work.BoseB6.lhyEps M.D.a M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ
                * ρ ^ 2 * M.D.a * Real.sqrt (ρ * M.D.a ^ 3) * E.ell ^ 3) := by
    rw [Work.BoseB6Est.fsMass, ← M.hGw, M.hρ, M.ha, M.hℓ]
    ring
  -- identify the abstract sum with `zpSum` (`sum_zp_eq`) and halve
  rw [← Finset.mul_sum, Work.BoseBogFS.sum_zp_eq F E ρ gHat0 M]
  rw [← hRHS]
  exact hmain

end Work.BoseBogFS
