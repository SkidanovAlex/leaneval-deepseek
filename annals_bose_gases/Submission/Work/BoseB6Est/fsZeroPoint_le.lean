import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB6Est.Zero.fsI1_lattice
import Submission.Work.BoseB6Est.Zero.fsScaleId
import Submission.Work.BoseB6Est.Zero.integrableBetaDiv
import Submission.Work.BoseB6Est.Zero.integrableCleanBracket
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — the zero-point comparison `hzero` of FS `thm:BogHamDiag`

This is deliverable item 2 of the chapter: the zero-point sum of FS's
`thm:BogHamDiag` against the lattice model of `eq:BogIntegral`, at FS's
parameters.

## The argument

Write `P = ρ_z a`, `δ = meshD n = 2π/((n:ℝ)+1)`, `S = Σ_k cleanBracket(t_k)` (the
mode-lattice sum of the scaled zero-point bracket), `L = latticeSum (8π) n` (the
same sum for the *model* bracket `lhyR3 (8π)`), `I = ∫ cleanBracket` and
`C = (2π)⁻³ℓ³ρ_z²a√(ρ_z a³)`.

1. `zpSum = P·S` (`zpSum_eq`).
2. **Scaling**: the mesh relation `(n:ℝ)+1 = ℓ√(ρ_z a)` of `FsZeroRegime.hrel`
   gives `C·δ³ = P` (`Zero.fsScaleId`), so the FS prefactor `C` is exactly
   `P·δ^{-3}`: `C` converts a lattice sum into an FS-normalised integral.
3. **Riemann**: `δ³S ≤ I + zpRiemErr n K c₂` (`zpRiem`); multiplying by
   `C = P δ^{-3}` turns this into `P·S ≤ C·I + C·zpRiemErr`.
4. **The integral** splits as `I = fsI1 + fsI2` (`Integrable` of the two pieces
   is `Zero.integrableCleanBracket`/`Zero.integrableBetaDiv`), and the mass term
   is exactly `C·fsI2`: `fsMass ρz a ℓ K = C·fsI2 K` (the `(2π)⁻³` of `fsGω0`
   and the `√(ρ_z a³) = a√(ρ_z a)` of `C` cancel).
5. **The `I₁` estimate against the lattice**: `fsI1 ≤ δ³L + 10¹⁰(2π)³ε`
   (`Zero.fsI1_lattice`, which combines `fsI1_le`, `lattice_sum_lower` and the
   explicit bound on `latticeMeshErr`).  Multiplying by `C`, the term
   `10¹⁰(2π)³ε·C` is exactly the `10¹⁰ε·ρ_z²a√(ρ_z a³)ℓ³` of the statement.

Everything is linear after step 3, so the assembly is an explicit `calc`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB6Est

theorem fsZeroPoint_le {n : ℕ} {K : FsKernel} {a R ρz ℓ μ z chiM δ εT c1 c2 Kl s d : ℝ}
    (h : FsZeroRegime n K a R ρz ℓ μ z chiM δ εT c1 c2 Kl s d) :
    zpSum n ρz a K εT c1 c2
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3))
          * ((Work.BoseB6.meshD n) ^ 3 * Work.BoseB6.latticeSum (8 * Real.pi) n)
        + fsMass ρz a ℓ K
        + 10 ^ 10 * Work.BoseB6.lhyEps a R εT Kl s d μ * ρz ^ 2 * a
            * Real.sqrt (ρz * a ^ 3) * ℓ ^ 3
        + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3))
            * zpRiemErr n K c2 := by
  have hreg := h.hi1
  have hρz : 0 < ρz := hreg.hρz
  have ha : 0 < a := hreg.ha
  have hℓ : 0 < ℓ := h.hℓ
  have hPpos : 0 < ρz * a := mul_pos hρz ha
  have hε0 : 0 ≤ εT := hreg.hε0
  have hε1 : εT ≤ 1 := by linarith [hreg.hε1]
  -- abbreviations of the compound expressions of the statement
  set Cc : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3))
    with hCdef
  set eps : ℝ := Work.BoseB6.lhyEps a R εT Kl s d μ with hEpsdef
  set Mc : ℝ := (Work.BoseB6.meshD n) ^ 3 with hMdef
  set Lc : ℝ := Work.BoseB6.latticeSum (8 * Real.pi) n with hLdef
  set Ec : ℝ := zpRiemErr n K c2 with hEdef
  set Sc : ℝ := ∑ k : modeIdx n, cleanBracket K εT c1 c2 (modePos n k) with hSdef
  set Ic : ℝ := ∫ t : Fin 3 → ℝ, cleanBracket K εT c1 c2 t with hIdef
  -- 1. the zero-point sum is `ρ_z a` times the lattice sum
  have hzp : zpSum n ρz a K εT c1 c2 = ρz * a * Sc := by
    rw [hSdef]
    exact zpSum_eq n K hPpos.le hε0 hε1
  -- the kernel's support is inside the mode range
  have hT' : K.T ≤ Real.sqrt 3 * Real.pi * ((n : ℝ) + 1) := by
    rw [h.hrel]
    exact h.hTlat
  -- 3. the lattice Riemann comparison
  have hriem : Mc * Sc ≤ Ic + Ec := by
    rw [hMdef, hSdef, hIdef, hEdef]
    have h2 := zpRiem hreg h.hn hT'
    simp only [zpRiemErr] at h2 ⊢
    linarith [h2]
  -- 2. the scaling identity `C δ³ = P`
  have hscale : Cc * Mc = ρz * a := by
    rw [hCdef, hMdef]
    exact Zero.fsScaleId hρz ha hℓ h.hrel
  have hCnn : 0 ≤ Cc := by
    rw [hCdef]; positivity
  -- 5. the `I₁` estimate against the lattice
  have hI1l : fsI1 K εT c1 c2 ≤ Mc * Lc + 10 ^ 10 * (2 * Real.pi) ^ 3 * eps := by
    rw [hMdef, hLdef, hEpsdef]
    exact Zero.fsI1_lattice hreg h.hn h.hEpsLatt
  -- 4. the integral decomposition `∫ cleanBracket = fsI1 + fsI2`
  have hsplit : Ic = fsI1 K εT c1 c2 + fsI2 K := by
    rw [hIdef, fsI1, fsI2]
    have h1 : Integrable (fun t : Fin 3 → ℝ => cleanBracket K εT c1 c2 t) :=
      Zero.integrableCleanBracket hreg
    have h2 : Integrable (fun t : Fin 3 → ℝ => (K.β (nrm t)) ^ 2 / (2 * (nrm t) ^ 2)) :=
      Zero.integrableBetaDiv K
    have hunfold : (fun t : Fin 3 → ℝ => cleanBracket K εT c1 c2 t)
        = fun t => fsI1Integrand K εT c1 c2 t + (K.β (nrm t)) ^ 2 / (2 * (nrm t) ^ 2) := by
      funext t; rw [fsI1Integrand]; ring
    rw [hunfold, integral_add (f := fsI1Integrand K εT c1 c2)
      (g := fun t => (K.β (nrm t)) ^ 2 / (2 * (nrm t) ^ 2))]
    · exact h1.sub h2
    · exact h2
  -- `C·(2π)³ = ℓ³ρ_z²a√(ρ_z a³)`
  have hCcPi : Cc * (2 * Real.pi) ^ 3 = ℓ ^ 3 * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) := by
    rw [hCdef]
    have hπ : (2 * Real.pi) ^ 3 ≠ 0 := by positivity
    field_simp
  -- the mass term is exactly `C·fsI2`
  have hfsMass : fsMass ρz a ℓ K = Cc * fsI2 K := by
    have hsq : Real.sqrt (ρz * a ^ 3) = a * Real.sqrt (ρz * a) := by
      have h1 : ρz * a ^ 3 = (ρz * a) * a ^ 2 := by ring
      rw [h1, Real.sqrt_mul hPpos.le, Real.sqrt_sq ha.le]; ring
    rw [fsMass, fsGω0, hCdef, hsq]
    have hπ : (2 * Real.pi) ^ 3 ≠ 0 := by positivity
    field_simp
  -- the assembly
  have hgoal : zpSum n ρz a K εT c1 c2
      ≤ Cc * (Mc * Lc) + fsMass ρz a ℓ K
        + 10 ^ 10 * eps * ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3) * ℓ ^ 3 + Cc * Ec := by
    rw [hzp]
    calc ρz * a * Sc = Cc * (Mc * Sc) := by rw [← hscale]; ring
      _ ≤ Cc * (Ic + Ec) := mul_le_mul_of_nonneg_left hriem hCnn
      _ = Cc * (fsI1 K εT c1 c2 + fsI2 K) + Cc * Ec := by rw [hsplit]; ring
      _ = Cc * fsI1 K εT c1 c2 + Cc * fsI2 K + Cc * Ec := by ring
      _ ≤ Cc * (Mc * Lc + 10 ^ 10 * (2 * Real.pi) ^ 3 * eps) + Cc * fsI2 K + Cc * Ec := by
            have hh := mul_le_mul_of_nonneg_left hI1l hCnn
            linarith
      _ = Cc * (Mc * Lc) + fsMass ρz a ℓ K
            + 10 ^ 10 * eps * ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3) * ℓ ^ 3 + Cc * Ec := by
            rw [hfsMass]
            rw [show Cc * (Mc * Lc + 10 ^ 10 * (2 * Real.pi) ^ 3 * eps) + Cc * fsI2 K + Cc * Ec
                  = Cc * (Mc * Lc) + 10 ^ 10 * eps * (Cc * (2 * Real.pi) ^ 3)
                    + Cc * fsI2 K + Cc * Ec by ring,
                hCcPi]
            ring
  simpa only [hCdef, hEpsdef, hMdef, hLdef, hEdef] using hgoal

end Work.BoseB6Est
