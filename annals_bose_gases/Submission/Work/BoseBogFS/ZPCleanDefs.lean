import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.ZPLatticeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.ZPCleanDefs` — the scaled honest clean bracket

The target `Work.BoseBogFS.ZPCleanDeficitRow` bounds the lattice sum of FS's *clean*
part `cleanTerm = 𝒵(τ+c,c) − c²/(2‖k‖²)` at the honest datum.  This module collects the
*scaled* objects in which that row is proved, together with the elementary algebraic
layer.

## The scaling

With `P := ρ·(a v)` the squared momentum unit and `t := k/√P` the scaled momentum,

* `tSca v ρ μ n = (√P)⁻¹ • kAt v μ n` — the scaled lattice point of the label `n`;
* `tauSc v ρ μ t = τ(√P • t)/P` — the scaled kinetic symbol (`τ = tauAt`);
* `betaSc v h ρ μ t = c(√P • t)/P` — the scaled pairing coefficient
  (`c = ρ·Ŵ₁`, so `betaSc t = Ŵ₁(√P·t)/(a v)`);
* `psiSc v h ρ μ t = 𝒵(τ_s+β,β) − β²/(2‖t‖²)` — the scaled clean bracket.

The key identity (`cleanTerm_eq_scale`) is `cleanTerm n = P·psiSc (tSca n)`, which holds
as soon as the square root is in its honest range, i.e. `0 ≤ τ(k) + 2c(k)` (then
`(τ+c)² − c² = τ(τ+2c) ≥ 0`); the row `cleanTerm_eq_scale_of_nonneg` records the
sufficient sign condition `0 ≤ c`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The scaled objects -/

/-- The momentum unit `P = ρ·(a v)`. -/
def Psc (v : E3 → ℝ) (ρ : ℝ) : ℝ := ρ * a v

/-- The scaled lattice point of the label `n`: `t_n = k_n/√(ρ·a v)`. -/
def tSca (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) : E3 :=
  (Real.sqrt (ρ * a v))⁻¹ • kAt v μ n

/-- The scaled kinetic symbol `τ_s(t) = τ(√P·t)/P`. -/
def tauSc (v : E3 → ℝ) (ρ μ : ℝ) (t : E3) : ℝ :=
  (ρ * a v)⁻¹ * tauAt v μ (Real.sqrt (ρ * a v) • t)

/-- The scaled pairing coefficient `β(t) = Ŵ₁(√P·t)/(a v)`. -/
def betaSc (v : E3 → ℝ) (h : ScatSol v) (ρ μ : ℝ) (t : E3) : ℝ :=
  (ρ * a v)⁻¹ * cAt v h ρ μ (Real.sqrt (ρ * a v) • t)

/-- The scaled clean bracket `𝒵(τ_s+β,β) − β²/(2‖t‖²)`. -/
def psiSc (v : E3 → ℝ) (h : ScatSol v) (ρ μ : ℝ) (t : E3) : ℝ :=
  Work.BoseB6.bogZeroPoint (tauSc v ρ μ t + betaSc v h ρ μ t) (betaSc v h ρ μ t)
    - (betaSc v h ρ μ t) ^ 2 / (2 * ‖t‖ ^ 2)

/-! ## 2. Elementary identities -/

/-- `√P • tSca n = kAt n`: the scaling is inverted by `√P`. -/
lemma sqrt_smul_tSca {v : E3 → ℝ} {ρ μ : ℝ} (hP : 0 < ρ * a v) (n : Fin 3 → ℤ) :
    Real.sqrt (ρ * a v) • tSca v ρ μ n = kAt v μ n := by
  rw [tSca, smul_smul, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hP)), one_smul]

/-- The norm rescaling `‖√P • t‖² = P ‖t‖²`. -/
lemma norm_smul_sqrt_sq {v : E3 → ℝ} {ρ : ℝ} (hP : 0 < ρ * a v) (t : E3) :
    ‖Real.sqrt (ρ * a v) • t‖ ^ 2 = (ρ * a v) * ‖t‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hP.le]

/-- The division identity behind the mass part of the scaling:
`c²/(2·(P·T)) = P·((P⁻¹c)²/(2·T))` (the junk case `T = 0` is compatible). -/
lemma div_norm_scaling {P c T : ℝ} (hP : 0 < P) :
    c ^ 2 / (2 * (P * T)) = P * ((P⁻¹ * c) ^ 2 / (2 * T)) := by
  by_cases hT : T = 0
  · subst hT; simp
  · have hPT : P * T ≠ 0 := mul_ne_zero (ne_of_gt hP) hT
    field_simp
    try ring

/-- **The scaling identity for the Bogoliubov zero point**: for `P > 0` and `B² ≤ A²`,
`𝒵(A,B) = P·𝒵(A/P,B/P)`. -/
lemma bogZeroPoint_smul {P A B : ℝ} (hP : 0 < P) (hAB : B ^ 2 ≤ A ^ 2) :
    Work.BoseB6.bogZeroPoint A B = P * Work.BoseB6.bogZeroPoint (P⁻¹ * A) (P⁻¹ * B) := by
  have h1 : (P⁻¹ * A) ^ 2 - (P⁻¹ * B) ^ 2 = P⁻¹ ^ 2 * (A ^ 2 - B ^ 2) := by ring
  have hPP : P * P⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hP)
  have h2 : A ^ 2 - B ^ 2 = P ^ 2 * ((P⁻¹ * A) ^ 2 - (P⁻¹ * B) ^ 2) := by
    rw [h1, ← mul_assoc, ← mul_pow, hPP, one_pow, one_mul]
  have hX : Real.sqrt (P ^ 2 * ((P⁻¹ * A) ^ 2 - (P⁻¹ * B) ^ 2))
      = P * Real.sqrt ((P⁻¹ * A) ^ 2 - (P⁻¹ * B) ^ 2) := by
    rw [Real.sqrt_mul (sq_nonneg P), Real.sqrt_sq hP.le]
  rw [Work.BoseB6.bogZeroPoint, Work.BoseB6.bogZeroPoint, h2, hX, mul_sub, ← mul_assoc, hPP,
    one_mul]

/-- The hypothesis `0 ≤ τ + 2c` makes the square root honest: `c² ≤ (τ+c)²`. -/
lemma sq_le_sq_of_two_mul {τ c : ℝ} (hτ : 0 ≤ τ) (h : 0 ≤ τ + 2 * c) :
    c ^ 2 ≤ (τ + c) ^ 2 := by
  nlinarith [hτ, h, sq_nonneg c]

/-- **The core scaling identity**: `cleanTerm n = P·psiSc (tSca n)`. -/
theorem cleanTerm_eq_scale {v : E3 → ℝ} {h : ScatSol v} {ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hP : 0 < ρ * a v) (hτ : 0 ≤ tauAt v μ (kAt v μ n))
    (h2 : 0 ≤ tauAt v μ (kAt v μ n) + 2 * cAt v h ρ μ (kAt v μ n)) :
    cleanTerm v h ρ μ n = Psc v ρ * psiSc v h ρ μ (tSca v ρ μ n) := by
  have hsc := sqrt_smul_tSca (v := v) (ρ := ρ) (μ := μ) hP n
  have hAB : (cAt v h ρ μ (kAt v μ n)) ^ 2
      ≤ (tauAt v μ (kAt v μ n) + cAt v h ρ μ (kAt v μ n)) ^ 2 :=
    sq_le_sq_of_two_mul hτ h2
  have hτs : tauSc v ρ μ (tSca v ρ μ n) = (ρ * a v)⁻¹ * tauAt v μ (kAt v μ n) := by
    rw [tauSc, hsc]
  have hβs : betaSc v h ρ μ (tSca v ρ μ n) = (ρ * a v)⁻¹ * cAt v h ρ μ (kAt v μ n) := by
    rw [betaSc, hsc]
  have hnk : ‖kAt v μ n‖ ^ 2 = (ρ * a v) * ‖tSca v ρ μ n‖ ^ 2 := by
    have h1 := norm_smul_sqrt_sq (v := v) (ρ := ρ) hP (tSca v ρ μ n)
    rwa [hsc] at h1
  have hZ : Work.BoseB6.bogZeroPoint
        (tauAt v μ (kAt v μ n) + cAt v h ρ μ (kAt v μ n)) (cAt v h ρ μ (kAt v μ n))
      = Psc v ρ * Work.BoseB6.bogZeroPoint
          (tauSc v ρ μ (tSca v ρ μ n) + betaSc v h ρ μ (tSca v ρ μ n))
          (betaSc v h ρ μ (tSca v ρ μ n)) := by
    rw [hτs, hβs, ← mul_add, bogZeroPoint_smul hP hAB, Psc]
  have hM : (cAt v h ρ μ (kAt v μ n)) ^ 2 / (2 * ‖kAt v μ n‖ ^ 2)
      = Psc v ρ * ((betaSc v h ρ μ (tSca v ρ μ n)) ^ 2 / (2 * ‖tSca v ρ μ n‖ ^ 2)) := by
    rw [hβs, hnk, Psc]
    exact div_norm_scaling hP
  rw [cleanTerm, psiSc, hZ, hM]
  ring

/-- **The sign-sufficient form**: if `0 ≤ τ` and `0 ≤ c`, the identity holds. -/
theorem cleanTerm_eq_scale_of_nonneg {v : E3 → ℝ} {h : ScatSol v} {ρ μ : ℝ} {n : Fin 3 → ℤ}
    (hP : 0 < ρ * a v) (hτ : 0 ≤ tauAt v μ (kAt v μ n))
    (hc : 0 ≤ cAt v h ρ μ (kAt v μ n)) :
    cleanTerm v h ρ μ n = Psc v ρ * psiSc v h ρ μ (tSca v ρ μ n) :=
  cleanTerm_eq_scale hP hτ (by linarith)

/-! ## 3. The arithmetic identities of the target's right-hand side -/

/-- The Lee–Huang–Yang term, in the form used by the assembly:
`4π·lhyC·ρ²a·ℓ³·√(ρa³) = 4π·lhyC·(ρa)·K_ℓ³` with `K_ℓ = ℓ√(ρa)`. -/
theorem lhyTerm_scaled {aa ρ ℓ : ℝ} (ha : 0 < aa) (hρ : 0 < ρ) :
    4 * Real.pi * lhyC * ρ ^ 2 * aa * ℓ ^ 3 * Real.sqrt (ρ * aa ^ 3)
      = 4 * Real.pi * lhyC * (ρ * aa) * (ℓ * Real.sqrt (ρ * aa)) ^ 3 := by
  have hρaa : 0 < ρ * aa := mul_pos hρ ha
  have hsq : Real.sqrt (ρ * aa ^ 3) = aa * Real.sqrt (ρ * aa) := by
    rw [show ρ * aa ^ 3 = (ρ * aa) * aa ^ 2 by ring, Real.sqrt_mul hρaa.le,
      Real.sqrt_sq ha.le]
    ring
  have hcube : (ℓ * Real.sqrt (ρ * aa)) ^ 3 = ℓ ^ 3 * ((ρ * aa) * Real.sqrt (ρ * aa)) := by
    have h3 : (Real.sqrt (ρ * aa)) ^ 3 = (ρ * aa) * Real.sqrt (ρ * aa) := by
      rw [show (Real.sqrt (ρ * aa)) ^ 3
            = (Real.sqrt (ρ * aa)) ^ 2 * Real.sqrt (ρ * aa) by ring,
          Real.sq_sqrt hρaa.le]
    rw [mul_pow, h3]
  have key : 4 * Real.pi * lhyC * ρ ^ 2 * aa * ℓ ^ 3 * (aa * Real.sqrt (ρ * aa))
      = 4 * Real.pi * lhyC * (ρ * aa) * (ℓ ^ 3 * ((ρ * aa) * Real.sqrt (ρ * aa))) := by ring
  rw [hsq, hcube]
  exact key

/-- `errBracket` in the factored form `μ²·a·ℓ³·√(dil)·errSlot`. -/
theorem errBracket_factor (v : E3 → ℝ) (R μ : ℝ) :
    errBracket v R μ = μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ) * errSlot v R μ := rfl

end Work.BoseBogFS
