import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.Word
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The box side `ℓ = sideAt μ a` blows up as `μ → 0⁺`

`sideAt μ a = boxSide (paramsAt μ a) μ a = K_ℓ (μa)^{-1/2}` with
`K_ℓ = (μa³)^{-3/646}` (FS `eq:def_ell` at the diluteness-correct parameters).
Both factors tend to `+∞` as `μ → 0⁺`, so for every fixed radius `R` and every
fixed positive `r₀` the box side eventually dominates the support-radius
condition `R ≤ ℓ·r₀` that the comparison statement of the `C`-node needs
(`perStateBox_of_LHYBox_compareBox`): the condition holds for all sufficiently
small diluteness, with no constraint on how small.

We record the closed form

  `sideAt μ a = a · (μ a³)^{-(163/323)}`   (`sideAt_eq_rpow`),

whose exponent is negative, so the growth is immediate; the proof of the main
statement only needs the two separate factors, each compared at a threshold
chosen from `max (R/r₀) 1`.
-/

namespace Work.BoseBox

/-- **Closed form of the box side**: `ℓ = a (μa³)^{-163/323}`.  The exponent is
`3/646 + 1/2` (from `K_ℓ = (μa³)^{-3/646}` and `(μa)^{-1/2} = a (μa³)^{-1/2}`),
so `ℓ → ∞` as `μ → 0⁺`. -/
lemma sideAt_eq_rpow {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ) :
    Work.BoseBox.sideAt μ a = a * (μ * a ^ 3) ^ (-(163 / 323 : ℝ)) := by
  have hμa3 : 0 < μ * a ^ 3 := by positivity
  -- `(μa)^{-1/2} = a (μa³)^{-1/2}`
  have hsec : (μ * a) ^ (-(1 / 2 : ℝ)) = a * (μ * a ^ 3) ^ (-(1 / 2 : ℝ)) := by
    have h : μ * a = (μ * a ^ 3) / a ^ 2 := by field_simp
    rw [h, Real.div_rpow hμa3.le (by positivity : (0 : ℝ) ≤ a ^ 2)]
    rw [show (a ^ 2 : ℝ) ^ (-(1 / 2 : ℝ)) = a⁻¹ by
      rw [show (a ^ 2 : ℝ) = a ^ (2 : ℕ) by ring, ← Real.rpow_natCast a 2,
        ← Real.rpow_mul ha.le]
      norm_num
      rw [Real.rpow_neg_one]]
    rw [div_eq_mul_inv, inv_inv]
    ring
  -- unfold `sideAt` at the parameters `fsParams (μa³)`
  rw [show Work.BoseBox.sideAt μ a
      = (μ * a ^ 3) ^ (-(3 / 646 : ℝ)) * (μ * a) ^ (-(1 / 2 : ℝ)) by
    simp only [Work.BoseBox.sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt,
      Work.BoseBox.fsParams, Work.BoseBox.fsXp]
    norm_num]
  rw [hsec,
    show (μ * a ^ 3) ^ (-(3 / 646 : ℝ)) * (a * (μ * a ^ 3) ^ (-(1 / 2 : ℝ)))
      = a * ((μ * a ^ 3) ^ (-(3 / 646 : ℝ)) * (μ * a ^ 3) ^ (-(1 / 2 : ℝ))) by ring,
    ← Real.rpow_add hμa3]
  congr 1
  norm_num

/-- **The support-radius condition at small diluteness**: for every radius `R`
and every `r₀ > 0`, the box side `ℓ = sideAt μ a` satisfies `R ≤ ℓ·r₀` for all
sufficiently small `μ > 0`.  (The `C`-node of the comparison argument needs
this at each fixed `v`; here it is recorded for a bare real `a = a v`.) -/
theorem sideAt_large {a : ℝ} (ha : 0 < a) (R r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∀ᶠ μ in nhdsWithin (0 : ℝ) (Set.Ioi 0), R ≤ Work.BoseBox.sideAt μ a * r₀ := by
  -- Work at the threshold `c := max (R/r₀) 1 ≥ 1` on the box side; `c` is
  -- chosen so that `c ≥ R/r₀` (the radius condition) while `c ≥ 1` keeps it
  -- positive, which is all the arithmetic below needs.
  set c : ℝ := max (R / r₀) 1 with hcdef
  have hc1 : (1 : ℝ) ≤ c := le_max_right _ _
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc1
  have hRc : R / r₀ ≤ c := le_max_left _ _
  -- `μ` below the explicit threshold `δ`
  set δ : ℝ := min (1 / (2 * a ^ 3)) (1 / (2 * c ^ 2 * a)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Ioo_mem_nhds (show -(δ) < (0 : ℝ) by linarith) hδpos]
    with μ hμmem hμpos
  have hμpos' : 0 < μ := hμpos
  have hμlt : μ < δ := hμmem.2
  have hμa3 : 0 < μ * a ^ 3 := by positivity
  have hμa : 0 < μ * a := by positivity
  -- threshold 1: `μa³ ≤ 1`, so `K_ℓ = (μa³)^{-3/646} ≥ 1`
  have hμa3le : μ * a ^ 3 ≤ 1 := by
    have h : μ < 1 / (2 * a ^ 3) := lt_of_lt_of_le hμlt (min_le_left _ _)
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * a ^ 3)] at h
    nlinarith
  -- threshold 2: `μa ≤ c^{-2}`, so `(μa)^{-1/2} ≥ c`
  have hμale : μ * a ≤ c ^ (-(2 : ℝ)) := by
    have h : μ < 1 / (2 * c ^ 2 * a) := lt_of_lt_of_le hμlt (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * c ^ 2 * a)] at h
    have h4 : μ * a < 1 / (2 * c ^ 2) := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * c ^ 2)]
      nlinarith
    have h5 : (1 : ℝ) / (2 * c ^ 2) ≤ 1 / c ^ 2 := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * c ^ 2)
        (by positivity : (0 : ℝ) < c ^ 2)]
      nlinarith
    have h6 : (1 : ℝ) / c ^ 2 = c ^ (-(2 : ℝ)) := by
      rw [show c ^ (-(2 : ℝ)) = (c ^ 2)⁻¹ by
        rw [Real.rpow_neg (le_of_lt hcpos)]; norm_num]
      simp [one_div]
    linarith [le_of_lt h4, h5, h6 ▸ h5]
  have h1 : (1 : ℝ) ≤ (μ * a ^ 3) ^ (-(3 / 646 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hμa3 hμa3le (by norm_num)
  have h2 : c ≤ (μ * a) ^ (-(1 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos hμa hμale (show (-(1 / 2 : ℝ)) ≤ 0 by norm_num)
    have hcl : (c ^ (-(2 : ℝ))) ^ (-(1 / 2 : ℝ)) = c := by
      rw [← Real.rpow_mul hcpos.le]
      norm_num
    rwa [hcl] at h
  have hkey : c ≤ Work.BoseBox.sideAt μ a := by
    calc c ≤ (μ * a) ^ (-(1 / 2 : ℝ)) := h2
      _ = 1 * (μ * a) ^ (-(1 / 2 : ℝ)) := (one_mul _).symm
      _ ≤ (μ * a ^ 3) ^ (-(3 / 646 : ℝ)) * (μ * a) ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hμa.le _)
      _ = Work.BoseBox.sideAt μ a := by
            simp only [Work.BoseBox.sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt,
              Work.BoseBox.fsParams, Work.BoseBox.fsXp]
            norm_num
  have hfin : R / r₀ * r₀ ≤ Work.BoseBox.sideAt μ a * r₀ :=
    mul_le_mul_of_nonneg_right (le_trans hRc hkey) hr₀.le
  have hRe : R / r₀ * r₀ = R := by field_simp
  rwa [hRe] at hfin

end Work.BoseBox
