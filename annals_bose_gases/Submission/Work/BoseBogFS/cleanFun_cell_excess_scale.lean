import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBogFS.CleanRiem
import Submission.Work.BoseBogFS.integrand_reduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.cleanFun_cell_excess_scale` — the cell excess scales exactly

The clean Riemann row (`Work.BoseBogFS.cleanFun_tsum_le_integral`) controls the *per-cell excess*

`cleanFun (k_n) − (h³)⁻¹ ∫_{cell h n} cleanFun`

of the honest clean integrand on the honest momentum lattice `k_n = kAt v μ n` of mesh
`h = 2π/ℓ(μ)`.  The *scaled* objects of `ZPCleanDefs` (`psiSc`, the scaled clean bracket, whose
mesh is `h/√P` with `P = ρ·(a v)`) enter the assembly through the same excess, and this module
proves that the two excesses are proportional, with the *same* constant `P` that relates the
integrands:

`cleanFun (k_n) − (h³)⁻¹ ∫_{cell h n} cleanFun
   = P · ( psiSc (t_n) − ((h/√P)³)⁻¹ ∫_{cell (h/√P) n} psiSc )`.

## The proof

Everything is the pointwise scaling `cleanFun (√P • t) = P·psiSc t`
(`Work.BoseBogFS.cleanFun_scaled_eq`, itself unconditional: the zero point `𝒵` and the mass term
`c²/(2‖k‖²)` both rescale, junk branches included) plus the Haar change of variables, which is
exact because *the scaling maps the coarse cell onto the fine one*:
`√P • cell (h/√P) n = cell h n` (both the centre and the half-width rescale).

Two lattice bookkeepings connect the abstract statement to the corpus vocabulary:
`kAt v μ n = lpt (2π/ℓ) n` and `tSca v ρ μ n = lpt ((2π/ℓ)/√(ρ·a v)) n`.

No integrability hypothesis is needed: `MeasureTheory.Measure.setIntegral_comp_smul_of_pos` is
valid for arbitrary functions (the junk convention `∫ = 0` is compatible on both sides), and the
remaining algebra is exact.  Consequently the integrability hypotheses of the target are not used.
-/

noncomputable section

open scoped Real Topology BigOperators Pointwise

open MeasureTheory

namespace Work.BoseBogFS

open _root_.BoseGases Work.UBB Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The dilation of a lattice cell -/

/-- Membership in the dilated cell: `c • cell (m/c) n = cell m n` at the level of points. -/
private lemma mem_smul_cell {c m : ℝ} (hc : 0 < c) (n : Fin 3 → ℤ) (x : E3) :
    x ∈ c • cell (m / c) n ↔ x ∈ cell m n := by
  have hcne : c ≠ 0 := ne_of_gt hc
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hcne, mem_cell, mem_cell]
  constructor
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at h1 h2
    refine ⟨?_, ?_⟩
    · have key : m * (n i : ℝ) - m / 2 = c * (m / c * (n i) - m / c / 2) := by
        field_simp
      calc m * (n i : ℝ) - m / 2 = c * (m / c * (n i) - m / c / 2) := key
        _ ≤ c * (c⁻¹ * x.ofLp i) := mul_le_mul_of_nonneg_left h1 hc.le
        _ = x.ofLp i := by field_simp
    · have key : m * (n i : ℝ) + m / 2 = c * (m / c * (n i) + m / c / 2) := by
        field_simp
      calc x.ofLp i = c * (c⁻¹ * x.ofLp i) := by field_simp
        _ < c * (m / c * (n i) + m / c / 2) := mul_lt_mul_of_pos_left h2 hc
        _ = m * (n i : ℝ) + m / 2 := key.symm
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    refine ⟨?_, ?_⟩
    · have key : m / c * (n i : ℝ) - m / c / 2 = c⁻¹ * (m * (n i) - m / 2) := by
        field_simp
      calc m / c * (n i : ℝ) - m / c / 2 = c⁻¹ * (m * (n i) - m / 2) := key
        _ ≤ c⁻¹ * x.ofLp i := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hc.le)
    · have key : m / c * (n i : ℝ) + m / c / 2 = c⁻¹ * (m * (n i) + m / 2) := by
        field_simp
      calc c⁻¹ * x.ofLp i = c⁻¹ * x.ofLp i := rfl
        _ < c⁻¹ * (m * (n i) + m / 2) := mul_lt_mul_of_pos_left h2 (inv_pos.mpr hc)
        _ = m / c * (n i : ℝ) + m / c / 2 := key.symm

/-- **The dilation of a lattice cell**: for `c > 0`, `c • cell (m/c) n = cell m n`. -/
private lemma smul_cell_eq {c m : ℝ} (hc : 0 < c) (n : Fin 3 → ℤ) :
    c • cell (m / c) n = cell m n :=
  Set.ext (mem_smul_cell hc n)

/-- The lattice point scales with the mesh: `lpt m n = √P • lpt (m/√P) n`. -/
private lemma lpt_smul_div {P m : ℝ} (hP : 0 < P) (n : Fin 3 → ℤ) :
    lpt m n = Real.sqrt P • lpt (m / Real.sqrt P) n := by
  ext i
  simp only [WithLp.ofLp_smul, Pi.smul_apply, lpt_ofLp, smul_eq_mul]
  field_simp

/-! ## 2. The scaling of the per-cell excess -/

/-- **The cell excess scales like the integrand.**  If `f (√P • t) = P·g t` pointwise and
`P > 0`, then the excess of `f` at `lpt m n` over the cell of the mesh `m` equals `P` times the
excess of `g` at `lpt (m/√P) n` over the cell of the mesh `m/√P`. -/
private lemma cell_excess_scale {P m : ℝ} (hP : 0 < P) {f g : E3 → ℝ}
    (hfg : ∀ t : E3, f (Real.sqrt P • t) = P * g t) (n : Fin 3 → ℤ) :
    f (lpt m n) - (m ^ 3)⁻¹ * (∫ k in cell m n, f k)
      = P * (g (lpt (m / Real.sqrt P) n)
          - ((m / Real.sqrt P) ^ 3)⁻¹ * (∫ t in cell (m / Real.sqrt P) n, g t)) := by
  set c := Real.sqrt P with hc_def
  have hc : 0 < c := by rw [hc_def]; exact Real.sqrt_pos.mpr hP
  have hfg' : ∀ t : E3, f (c • t) = P * g t := by intro t; rw [hc_def]; exact hfg t
  have hlpt : lpt m n = c • lpt (m / c) n := by rw [hc_def]; exact lpt_smul_div hP n
  have hcell : c • cell (m / c) n = cell m n := smul_cell_eq hc n
  have hval : f (lpt m n) = P * g (lpt (m / c) n) := by rw [hlpt, hfg']
  have hint : ∫ k in cell m n, f k = c ^ 3 * (P * ∫ t in cell (m / c) n, g t) := by
    have hcv := MeasureTheory.Measure.setIntegral_comp_smul_of_pos (μ := volume) (f := f)
      (s := cell (m / c) n) hc
    rw [hcell, finrank_euclideanSpace, Fintype.card_fin] at hcv
    rw [setIntegral_congr_fun (measurableSet_cell _ _) (fun x _ => hfg' x),
      MeasureTheory.integral_const_mul, smul_eq_mul] at hcv
    calc ∫ k in cell m n, f k = c ^ 3 * ((c ^ 3)⁻¹ * ∫ k in cell m n, f k) := by
          rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 (ne_of_gt hc)), one_mul]
      _ = c ^ 3 * (P * ∫ t in cell (m / c) n, g t) := by rw [hcv]
  rw [hval, hint]
  have hkey : ((m / c) ^ 3)⁻¹ = c ^ 3 / m ^ 3 := by rw [div_pow, inv_div]
  rw [hkey, div_eq_mul_inv]
  ring

/-! ## 3. The lattice bookkeeping -/

/-- The honest lattice point `kAt v μ n` is the lattice point of the mesh `2π/ℓ(μ)`. -/
private lemma kAt_eq_lpt_mesh (v : E3 → ℝ) (μ : ℝ) (n : Fin 3 → ℤ) :
    kAt v μ n = lpt (2 * Real.pi / ell v μ) n := by
  rw [kAt, Work.BoseB4.vec, lpt]
  ext i
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The scaled lattice point `tSca v ρ μ n` is the lattice point of the mesh `(2π/ℓ)/√(ρ·a v)`. -/
private lemma tSca_eq_lpt_mesh (v : E3 → ℝ) (ρ μ : ℝ) (n : Fin 3 → ℤ) :
    tSca v ρ μ n = lpt ((2 * Real.pi / ell v μ) / Real.sqrt (ρ * a v)) n := by
  rw [tSca, kAt_eq_lpt_mesh]
  ext i
  simp only [WithLp.ofLp_smul, Pi.smul_apply, lpt_ofLp, smul_eq_mul]
  ring

/-! ## 4. The target -/

theorem cleanFun_cell_excess_scale {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {ρ μ : ℝ} (hρ : 0 < ρ * _root_.BoseGases.a v) (n : Fin 3 → ℤ)
    (hInt : MeasureTheory.IntegrableOn (Work.BoseBogFS.cleanFun v h ρ μ)
      (Work.BoseBogFS.cell (2 * Real.pi / Work.BoseFixR.ell v μ) n))
    (hIntS : MeasureTheory.IntegrableOn (Work.BoseBogFS.psiSc v h ρ μ)
      (Work.BoseBogFS.cell ((2 * Real.pi / Work.BoseFixR.ell v μ)
        / Real.sqrt (ρ * _root_.BoseGases.a v)) n)) :
    Work.BoseBogFS.cleanFun v h ρ μ (Work.BoseBogFS.kAt v μ n)
        - ((2 * Real.pi / Work.BoseFixR.ell v μ) ^ 3)⁻¹
          * (∫ k in Work.BoseBogFS.cell (2 * Real.pi / Work.BoseFixR.ell v μ) n,
              Work.BoseBogFS.cleanFun v h ρ μ k)
      = Work.BoseBogFS.Psc v ρ
          * (Work.BoseBogFS.psiSc v h ρ μ (Work.BoseBogFS.tSca v ρ μ n)
              - (((2 * Real.pi / Work.BoseFixR.ell v μ) / Real.sqrt (ρ * _root_.BoseGases.a v)) ^ 3)⁻¹
                * (∫ t in Work.BoseBogFS.cell ((2 * Real.pi / Work.BoseFixR.ell v μ)
                    / Real.sqrt (ρ * _root_.BoseGases.a v)) n,
                    Work.BoseBogFS.psiSc v h ρ μ t)) := by
  have hfg : ∀ t : E3, cleanFun v h ρ μ (Real.sqrt (ρ * _root_.BoseGases.a v) • t)
      = (ρ * _root_.BoseGases.a v) * psiSc v h ρ μ t := fun t => cleanFun_scaled_eq hρ t
  have key := cell_excess_scale (P := ρ * _root_.BoseGases.a v)
    (m := 2 * Real.pi / Work.BoseFixR.ell v μ)
    (f := cleanFun v h ρ μ) (g := psiSc v h ρ μ) hρ hfg n
  rw [kAt_eq_lpt_mesh, tSca_eq_lpt_mesh]
  exact key

end Work.BoseBogFS
