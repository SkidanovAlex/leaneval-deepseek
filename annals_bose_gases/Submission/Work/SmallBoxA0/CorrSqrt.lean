import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxA0.corrWord_sqrt_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Corr` residue in `√`-shape, and its AM–GM reduction
(Work.SmallBoxA0, SESSION-286c)

The SESSION-286 bundle carried the `Corr` residue in the LINEAR form

    hCorrF : 2·s⁻³·CorrWord ≤ n₊/(72s²) + 36π(av)μ .

`CorrWord = Σᵢ∫(PᵢΦ)·f₁(xᵢ)·(Σ_k Q_kQ_iΦ)` is BILINEAR in the condensate and
the excited parts, so the only shape that comes out of the corpus's
quadratic-form framework is `√`-shaped:

    hCorrF : 2·s⁻³·CorrWord ≤ CorrC·(av)·√(cS1 s Φ)·√(cnPlus s Φ)   (`hbound`)

with `CorrC` a data scalar (it absorbs the fibre sup `fsqC1 = 16π(av)χSup²`
and the `N`-factor of the `Σ_k`-Cauchy–Schwarz).  This module proves the AM–GM
reduction `corr_linear_of_sqrt` turning that `√`-shape into the LINEAR form
used by the assembly, under the (data-only) regime

    hcorrreg : 4·(CorrC·(av))²·N̂·s² ≤ π·(av)·μ ,

i.e. the AM–GM's constant term `144·s²·CorrC²(av)²·cS1` fits the `(av)μ`
budget (`cS1 ≤ N̂` by `cS1_le_norm_sq`).

So the assembly sees the same linear `hCorr`, but it is now a THEOREM from the
provable `√`-shape plus the regime — exactly the reviewer's requested item (3).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxA0

open Submission BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Arithmetic core of the AM–GM: for `p, q ≥ 0` and `K, s > 0`,

    `K·√p·√q ≤ q/(576s²) + 144·s²·K²·p` .

Proof: `K·√p·√q = 2·(√q/(24s))·(12s·K·√p)` and `2xy ≤ x² + y²`. -/
lemma amgm_sqrt {p q K s : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hK : 0 ≤ K) (hs : 0 < s) :
    K * Real.sqrt p * Real.sqrt q ≤ q / (576 * s ^ 2) + 144 * s ^ 2 * K ^ 2 * p := by
  have h2 : K * Real.sqrt p * Real.sqrt q
      = 2 * (Real.sqrt q / (24 * s)) * (12 * s * K * Real.sqrt p) := by
    field_simp
    ring
  have hx2 : (Real.sqrt q / (24 * s)) ^ 2 = q / (576 * s ^ 2) := by
    rw [div_pow, div_eq_mul_inv, div_eq_mul_inv]
    have h1 : (Real.sqrt q) ^ 2 = q := by rw [sq]; exact Real.mul_self_sqrt hq
    rw [h1]
    ring
  have hy2 : (12 * s * K * Real.sqrt p) ^ 2 = 144 * s ^ 2 * K ^ 2 * p := by
    have h1 : (Real.sqrt p) ^ 2 = p := by rw [sq]; exact Real.mul_self_sqrt hp
    ring_nf
    rw [h1]
  have hprod : 2 * (Real.sqrt q / (24 * s)) * (12 * s * K * Real.sqrt p)
      ≤ q / (576 * s ^ 2) + 144 * s ^ 2 * K ^ 2 * p := by
    have h0 : (0 : ℝ) ≤ (Real.sqrt q / (24 * s) - 12 * s * K * Real.sqrt p) ^ 2 :=
      sq_nonneg _
    nlinarith [h0, hx2, hy2]
  linarith [h2, hprod]

/-- **The AM–GM reduction of the `√`-shaped `Corr` bound to the linear form used by the
assembly.**

From `2·CorrWord ≤ CorrC·(av)·√(cS1)·√(n₊)` (the only shape the corpus's
quadratic-form framework yields) and the scale-invariant regime
`4·(CorrC(av))²·N̂ ≤ π·(av)μ·s⁴` (which absorbs the AM–GM constant via
`cS1 ≤ N̂`), the assembly's linear form

    `2·s⁻³·CorrWord ≤ n₊/(72s²) + 36π(av)μ`

follows.  (Both shapes are invariant under the physical rescaling
`s ↦ εs, v ↦ ε⁻²v(·/ε), μ ↦ μ/ε³`; note the `s⁻³` sits on the `2·s⁻³·CorrWord`
side, NOT on the `√`-bound.) -/
theorem corr_linear_of_sqrt {N : ℕ} {s μ CorrC : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hav : 0 ≤ a v) (hC : 0 ≤ CorrC)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1)
    (hreg : 4 * (CorrC * (a v)) ^ 2 * ((N : ℝ)) ≤ π * (a v) * μ * s ^ 4)
    (hbound : 2 * CorrWord s h Φ
        ≤ CorrC * (a v) * Real.sqrt (cS1 s Φ) * Real.sqrt (cnPlus s Φ)) :
    2 * (s ^ 3)⁻¹ * CorrWord s h Φ
      ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ := by
  have hSc1nn : (0 : ℝ) ≤ cS1 s Φ := cS1_nonneg
  have hcnnn : (0 : ℝ) ≤ cnPlus s Φ := cnPlus_nonneg
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  have hK : (0 : ℝ) ≤ CorrC * (a v) * (s ^ 3)⁻¹ :=
    mul_nonneg (mul_nonneg hC hav) (by positivity)
  -- the `√`-bound with the `s⁻³` moved inside
  have hbound' : 2 * (s ^ 3)⁻¹ * CorrWord s h Φ
      ≤ (CorrC * (a v) * (s ^ 3)⁻¹) * Real.sqrt (cS1 s Φ) * Real.sqrt (cnPlus s Φ) := by
    have h0 : (0 : ℝ) ≤ (s ^ 3)⁻¹ := by positivity
    calc 2 * (s ^ 3)⁻¹ * CorrWord s h Φ = (s ^ 3)⁻¹ * (2 * CorrWord s h Φ) := by ring
      _ ≤ (s ^ 3)⁻¹ * (CorrC * (a v) * Real.sqrt (cS1 s Φ) * Real.sqrt (cnPlus s Φ)) :=
            mul_le_mul_of_nonneg_left hbound h0
      _ = (CorrC * (a v) * (s ^ 3)⁻¹) * Real.sqrt (cS1 s Φ) * Real.sqrt (cnPlus s Φ) := by ring
  have ham := amgm_sqrt (p := cS1 s Φ) (q := cnPlus s Φ) (K := CorrC * (a v) * (s ^ 3)⁻¹)
    hSc1nn hcnnn hK hs
  -- `cS1 ≤ N̂`
  have hSle : cS1 s Φ ≤ (N : ℝ) := by
    have h1 := cS1_le_norm_sq (N := N) (ℓ := s) hs hΦc
    rw [hnorm, mul_one] at h1
    exact h1
  -- the AM–GM constant fits the `(av)μ` budget
  have hconst : 144 * s ^ 2 * (CorrC * (a v) * (s ^ 3)⁻¹) ^ 2 * cS1 s Φ
      ≤ 36 * π * (a v) * μ := by
    have h1 : 144 * s ^ 2 * (CorrC * (a v) * (s ^ 3)⁻¹) ^ 2 * cS1 s Φ
        = 4 * (CorrC * (a v)) ^ 2 * cS1 s Φ / s ^ 4 * 36 := by
      field_simp
      ring
    rw [h1]
    have h2 : 4 * (CorrC * (a v)) ^ 2 * cS1 s Φ ≤ 4 * (CorrC * (a v)) ^ 2 * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hSle (by positivity)
    have h5 : 4 * (CorrC * (a v)) ^ 2 * cS1 s Φ / s ^ 4 ≤ π * (a v) * μ := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < s ^ 4)]
      nlinarith [h2, hreg]
    nlinarith [h5]
  have hq : cnPlus s Φ / (576 * s ^ 2) ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ := by
    have h6 : (1 / 576 : ℝ) ≤ 1 / 72 := by norm_num
    have h7 : (0 : ℝ) ≤ cnPlus s Φ / s ^ 2 := div_nonneg hcnnn (by positivity)
    calc cnPlus s Φ / (576 * s ^ 2) = (1 / 576) * (cnPlus s Φ / s ^ 2) := by ring
      _ ≤ (1 / 72) * (cnPlus s Φ / s ^ 2) := mul_le_mul_of_nonneg_right h6 h7
      _ = (1 / (72 * s ^ 2)) * cnPlus s Φ := by ring
  linarith [hbound', ham, hconst, hq]

/-- **The `√`-shaped `Corr` bound for every particle number** (the form the bundles use):
`N = 0` is trivial (`CorrWord`, `cS1` and `cnPlus` all vanish) and `N = m+1` is the
delegated theorem `Work.SmallBoxA0.corrWord_sqrt_bound` at `n := m`. -/
theorem corr_sqrt_bound_all {N : ℕ} {s R : ℝ} {v : ℝ³ → ℝ}
    (hs : 0 < s) (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (hRs : R ≤ s * chiR0)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1) :
    2 * CorrWord s h Φ
      ≤ (32 * π * chiSup ^ 2 * ((N : ℝ) + 1)) * (a v)
          * Real.sqrt (cS1 s Φ) * Real.sqrt (cnPlus s Φ) := by
  cases N with
  | zero =>
    have hC0 : CorrWord s h Φ = 0 := by
      simp [CorrWord]
    have hS0 : cS1 s Φ = 0 := by simp [cS1]
    have hn0 : cnPlus s Φ = 0 := by simp [cnPlus]
    rw [hC0, hS0, hn0, Real.sqrt_zero]
    ring_nf
    positivity
  | succ m =>
    have hbound := corrWord_sqrt_bound (n := m) (s := s) (R := R) (v := v) hs hR hv_nonneg
      hvrad hv_supp h hRs hΦc hnorm
    have hcast : (((m + 1 : ℕ)) : ℝ) + 1 = (m : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    exact hbound

end Work.SmallBoxA0
