import Mathlib
import Submission.Work.OddCurve.LowSlope.RadialLogConstruction
import Submission.Work.OddRadon.radialSystem_determined
import Submission.Work.OddRadon.RadialDefs

namespace Work.OddVolterra.Free

open Work.OddCurve.LowSlope

/-!
# The normalised solution reproduces the anchor profile, low-`cos` region

Same content as `solR_eq_anchor_cap`, but phrased for the complementary cap condition
`Real.cos α ≤ 4 / 5`.  The pointwise algebraic identification of the solution does not use the
size of `Real.cos α` at all: given the data equalities

  `A α = ρ (cos α) ^ (2n+2) + ρ (-cos α) ^ (2n+2) - 2`,
  `B α = ρ (cos α) ^ (2n+1) - ρ (-cos α) ^ (2n+1)`,

the pair `(ρ (cos α), ρ (-cos α))` is an explicit positive solution of the two-power system, and
the normalised construction inverts `radH` on `(0,1)` uniquely.
-/

/-! ## Elementary `rpow` bookkeeping for the exponent `θ = (2n+1)/(2n+2)` -/

/-- `(a ^ (2n+2)) ^ θ = a ^ (2n+1)` for `a ≥ 0`. -/
private lemma rpow_th_pow (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (a ^ (2 * n + 2)) ^ (radTh n) = a ^ (2 * n + 1) := by
  rw [← Real.rpow_natCast a (2 * n + 2), ← Real.rpow_mul ha]
  have hExp : ((2 * n + 2 : ℕ) : ℝ) * (radTh n) = ((2 * n + 1 : ℕ) : ℝ) := by
    simp only [radTh]
    have h : ((2 * n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hExp, Real.rpow_natCast]

/-- `(a ^ (2n+2) / u) ^ θ = a ^ (2n+1) / u ^ θ` for `a ≥ 0 < u`. -/
private lemma div_pow_rpow_th (n : ℕ) {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u) :
    (a ^ (2 * n + 2) / u) ^ (radTh n) = a ^ (2 * n + 1) / u ^ (radTh n) := by
  rw [Real.div_rpow (pow_nonneg ha _) hu.le (radTh n), rpow_th_pow n ha]

/-- The two-power system with data `(2 + A α, B α)` has at most one positive solution, and the
explicit one attached to a positive profile `ρ` beats the normalised construction.

Concretely: if `A α = R ^ (2n+2) + r ^ (2n+2) - 2` and `B α = R ^ (2n+1) - r ^ (2n+1)` for
positive `R, r`, then `solR n A B α = R` and `solr n A B α = r`.  The normalising coordinate is
`x = R ^ (2n+2) / u` with `u = R ^ (2n+2) + r ^ (2n+2)`; it lies in `(0,1)` and
`radH n x = B α / u ^ θ`, so it is `solX n A B α` by uniqueness of the inverse `radInv n`. -/
private lemma anchor_pair_of_cap_lt (n : ℕ) {A B : ℝ → ℝ} {α R r : ℝ}
    (hR : 0 < R) (hr : 0 < r)
    (hA : A α = R ^ (2 * n + 2) + r ^ (2 * n + 2) - 2)
    (hB : B α = R ^ (2 * n + 1) - r ^ (2 * n + 1)) :
    solR n A B α = R ∧ solr n A B α = r := by
  have hRm : 0 < R ^ (2 * n + 2) := pow_pos hR _
  have hrm : 0 < r ^ (2 * n + 2) := pow_pos hr _
  set u : ℝ := R ^ (2 * n + 2) + r ^ (2 * n + 2) with hu_def
  have hu : 0 < u := by rw [hu_def]; linarith
  have hsolU : solU A α = u := by
    rw [solU_apply, hA, hu_def]; ring
  have h2A : (2 : ℝ) + A α = u := by rw [← hsolU, solU_apply]
  have hsolW : solW n A B α = (R ^ (2 * n + 1) - r ^ (2 * n + 1)) / u ^ (radTh n) := by
    rw [solW_apply, hB, h2A]
  set x0 : ℝ := R ^ (2 * n + 2) / u with hx0_def
  have hx0pos : 0 < x0 := by rw [hx0_def]; exact div_pos hRm hu
  have hx0lt : x0 < 1 := by
    rw [hx0_def, div_lt_one hu]
    rw [hu_def]; linarith
  have h1mx0 : 1 - x0 = r ^ (2 * n + 2) / u := by
    rw [hx0_def]; field_simp; rw [hu_def]; ring
  have hH : radH n x0 = (R ^ (2 * n + 1) - r ^ (2 * n + 1)) / u ^ (radTh n) := by
    rw [radH_apply, hx0_def, h1mx0, div_pow_rpow_th n hR.le hu, div_pow_rpow_th n hr.le hu]
    ring
  -- the normalised second datum is the `radH`-value of `x0` and lies in `(-1,1)`
  have habsW : |solW n A B α| < 1 := by
    rw [hsolW, abs_div, abs_of_pos (Real.rpow_pos_of_pos hu _),
      div_lt_one (Real.rpow_pos_of_pos hu _)]
    rcases le_total r R with hle | hle
    · have hRk : r ^ (2 * n + 1) ≤ R ^ (2 * n + 1) :=
        pow_le_pow_left₀ hr.le hle (2 * n + 1)
      have habs : |R ^ (2 * n + 1) - r ^ (2 * n + 1)|
          = R ^ (2 * n + 1) - r ^ (2 * n + 1) := abs_of_nonneg (by linarith)
      have hlt1 : R ^ (2 * n + 1) - r ^ (2 * n + 1) < R ^ (2 * n + 1) := by
        have := pow_pos hr (2 * n + 1); linarith
      have hlt2 : R ^ (2 * n + 1) < u ^ (radTh n) := by
        rw [hu_def, ← rpow_th_pow n hR.le]
        exact Real.rpow_lt_rpow (pow_nonneg hR.le (2 * n + 2))
          (by have := pow_pos hr (2 * n + 2); linarith) (radTh_pos n)
      rw [habs]
      linarith
    · have hrk : R ^ (2 * n + 1) ≤ r ^ (2 * n + 1) :=
        pow_le_pow_left₀ hR.le hle (2 * n + 1)
      have habs : |R ^ (2 * n + 1) - r ^ (2 * n + 1)|
          = r ^ (2 * n + 1) - R ^ (2 * n + 1) := by
        rw [abs_of_nonpos (by linarith)]
        ring
      have hlt1 : r ^ (2 * n + 1) - R ^ (2 * n + 1) < r ^ (2 * n + 1) := by
        have := pow_pos hR (2 * n + 1); linarith
      have hlt2 : r ^ (2 * n + 1) < u ^ (radTh n) := by
        rw [hu_def, ← rpow_th_pow n hr.le]
        exact Real.rpow_lt_rpow (pow_nonneg hr.le (2 * n + 2))
          (by have := pow_pos hR (2 * n + 2); linarith) (radTh_pos n)
      rw [habs]
      linarith
  have hX : solX n A B α = x0 := by
    rw [solX_apply]
    exact (radInv_eq_of habsW ⟨hx0pos, hx0lt⟩ (hH.trans hsolW.symm)).symm
  have hRu : x0 * u = R ^ (2 * n + 2) := by
    rw [hx0_def]; field_simp
  have hr1u : (1 - x0) * u = r ^ (2 * n + 2) := by
    rw [h1mx0]; field_simp
  have hexp : ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ)⁻¹ = 1 := by
    rw [mul_inv_cancel₀ (by positivity : ((2 * n + 2 : ℕ) : ℝ) ≠ 0)]
  constructor
  · rw [solR_apply, hX, hsolU, hRu, ← Real.rpow_natCast R (2 * n + 2), ← Real.rpow_mul hR.le,
      hexp, Real.rpow_one]
  · rw [solr_apply, hX, hsolU, hr1u, ← Real.rpow_natCast r (2 * n + 2), ← Real.rpow_mul hr.le,
      hexp, Real.rpow_one]

theorem solR_eq_anchor_cap_lt (n : ℕ) (hn : 1 ≤ n) {A B ρ : ℝ → ℝ}
    (hAcap : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), Real.cos α ≤ 4 / 5 →
      A α = ρ (Real.cos α) ^ (2 * n + 2) + ρ (-(Real.cos α)) ^ (2 * n + 2) - 2)
    (hBcap : ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2), Real.cos α ≤ 4 / 5 →
      B α = ρ (Real.cos α) ^ (2 * n + 1) - ρ (-(Real.cos α)) ^ (2 * n + 1))
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u) :
    ∀ α ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos α ≤ 4 / 5 →
      Work.OddCurve.LowSlope.solR n A B α = ρ (Real.cos α) ∧
        Work.OddCurve.LowSlope.solr n A B α = ρ (-(Real.cos α)) := by
  intro α hα hcos
  have hαIcc : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_of_lt hα.1, le_of_lt hα.2⟩
  have hcpos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
  have hclt1 : Real.cos α < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (le_refl (0 : ℝ)) (le_of_lt hα.2) hα.1
    simpa using h
  have hR : 0 < ρ (Real.cos α) := hρpos _ ⟨by linarith, hclt1⟩
  have hr : 0 < ρ (-(Real.cos α)) := hρpos _ ⟨by linarith, by linarith⟩
  exact anchor_pair_of_cap_lt n hR hr (hAcap α hαIcc hcos) (hBcap α hαIcc hcos)

end Work.OddVolterra.Free
