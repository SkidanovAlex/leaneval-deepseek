import Mathlib
import Submission.Work.EKLC6Core.cell_relthin_cover2

namespace Work.EKLC6Core

/-!
# `Work.EKLC6Core.bad_inCol_shell`

**Inside collar.** A point `z` of the cell ball of radius `cellRad μ y j` around `y j` that is
pushed *out* of that ball by a displacement `v ∈ V (ε * injCap z)` must lie in the two-sided
shell of relative width `deltac * ε` (where `deltac = 2^60`, `epsZero = 1/deltac`).

Equivalently: the part of the ball at relative depth `< deltac * ε` is not moved out of the ball
by a displacement of size `ε * injCap z`.  The quantitative content is that for
`z = u • y j` with `u ∈ V (cellRad μ y j * (1 - deltac * ε))` one has
`injCap z ≤ 2^19 * injCap (y j) ≤ 2^19 * 4096 * cellRad μ y j`, so that
`ε * injCap z` is small compared with `cellRad μ y j * (deltac * ε)`; hence `v * u ∈ V (cellRad μ y j)`
and `v • z = (v * u) • y j` is still in the ball — a contradiction.
-/

/-- Arithmetic of the inside collar: the product `ε * injCap z` times the amplification factor
`1 + 3 * (r * (1 - de))` is at most `r * de`. -/
theorem badInCol_arith_k {r ink0 inkz ε de : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 2)
    (hε : 0 < ε) (hde : 0 ≤ de) (hde1 : de ≤ 1)
    (hβ : ink0 ≤ 4096 * r) (hK : inkz ≤ 2 ^ 19 * ink0)
    (hde_eq : de = deltac * ε) :
    ε * inkz * (1 + 3 * (r * (1 - de))) ≤ r * de := by
  have h1 : (1 + 3 * (r * (1 - de))) ≤ 3 := by nlinarith [hr, hr1, hde, hde1]
  have h2 : ε * inkz ≤ ε * (2 ^ 19 * ink0) := mul_le_mul_of_nonneg_left hK (le_of_lt hε)
  have h3 : ε * (2 ^ 19 * ink0) ≤ ε * (2 ^ 19 * (4096 * r)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hβ (by norm_num)) (le_of_lt hε)
  have h4 : ε * inkz ≤ ε * (2 ^ 19 * (4096 * r)) := le_trans h2 h3
  have h5 : ε * inkz * (1 + 3 * (r * (1 - de))) ≤ ε * (2 ^ 19 * (4096 * r)) * 3 := by
    have h6 : 0 ≤ 1 + 3 * (r * (1 - de)) := by nlinarith [hde, hde1, hr]
    have h7 : 0 ≤ ε * (2 ^ 19 * (4096 * r)) := by positivity
    exact mul_le_mul h4 h1 h6 h7
  have h8 : ε * (2 ^ 19 * (4096 * r)) * 3 = 3 * 2^19 * 4096 * (ε * r) := by ring
  have h9 : 3 * 2^19 * 4096 * (ε * r) ≤ deltac * (ε * r) := by
    have hm : 3 * 2^19 * 4096 ≤ deltac := by norm_num [deltac]
    exact mul_le_mul_of_nonneg_right hm (by positivity)
  have h10 : deltac * (ε * r) = r * de := by rw [hde_eq]; ring
  linarith [h5, h8, h9, h10]

/-- Rewriting step of the inside collar: the exponent of the product displacement
`V_mul_subset_V` is bounded by `r`. -/
theorem badInCol_arith_sum {r inkz ε de : ℝ}
    (hk : ε * inkz * (1 + 3 * (r * (1 - de))) ≤ r * de) :
    ε * inkz + r * (1 - de) + 3 * (ε * inkz) * (r * (1 - de)) ≤ r := by
  nlinarith [hk]

theorem bad_inCol_shell {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsFiniteMeasure μ] {y : ℕ → Work.EKLContract.X3} {j : ℕ}
    (hj : j ∈ Work.EKLC6Core.sel y) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ Work.EKLC6Core.epsZero) {z : Work.EKLContract.X3} {v : Work.EKLContract.SL3}
    (hzB : z ∈ Work.EKLComp.Vball (Work.EKLC6Core.cellRad μ y j) (y j))
    (hv : v ∈ Work.EKLContract.V (ε * Work.EKLC6Core.injCap z))
    (hvz : v • z ∉ Work.EKLComp.Vball (Work.EKLC6Core.cellRad μ y j) (y j)) :
    z ∈ Work.EKLC6Core.shell μ y (Work.EKLC6Core.deltac * ε) j := by
  have hspec := Work.EKLC6Core.cellRad_spec (μ := μ) hj
  have hrpos : 0 < Work.EKLC6Core.cellRad μ y j := Work.EKLC6Core.cellRad_pos (μ := μ) hj
  have hrhi : Work.EKLC6Core.cellRad μ y j ≤ Work.EKLC6Core.cellHi (y j) := hspec.2.1
  have hr1 : Work.EKLC6Core.cellRad μ y j ≤ 1 / 2 :=
    le_trans (le_trans hrhi (Work.EKLC6Core.cellHi_le _)) (by norm_num)
  have hlo : Work.EKLC6Core.cellLo (y j) ≤ Work.EKLC6Core.cellRad μ y j := hspec.1
  -- `cellLo (y j) = injCap (y j)/4096 ≤ cellRad μ y j`, i.e. `injCap (y j) ≤ 4096 * cellRad`.
  have hβ : Work.EKLC6Core.injCap (y j) ≤ 4096 * Work.EKLC6Core.cellRad μ y j := by
    have h := hlo
    rw [Work.EKLC6Core.cellLo, div_le_iff₀ (by norm_num : (0:ℝ) < 4096)] at h
    linarith
  have hde : 0 ≤ Work.EKLC6Core.deltac * ε :=
    mul_nonneg (le_of_lt Work.EKLC6Core.deltac_pos) (le_of_lt hε0)
  have hde1 : Work.EKLC6Core.deltac * ε ≤ 1 := Work.EKLC6Core.deltac_eps_le_one hε1
  -- the shallow ball is well inside the injectivity threshold of `y j`.
  have hr8 : Work.EKLC6Core.cellRad μ y j * (1 - Work.EKLC6Core.deltac * ε)
      ≤ Work.EKLC6Core.injCap (y j) / 8 := by
    have h1 : Work.EKLC6Core.cellRad μ y j * (1 - Work.EKLC6Core.deltac * ε)
        ≤ Work.EKLC6Core.cellRad μ y j := by nlinarith [hde, hrpos]
    have h2 : Work.EKLC6Core.cellRad μ y j ≤ Work.EKLC6Core.injCap (y j) / 8 :=
      le_trans hrhi (by
        rw [Work.EKLC6Core.cellHi]
        exact div_le_div_of_nonneg_left (le_of_lt (Work.EKLC6Core.injCap_pos _))
          (by norm_num) (by norm_num))
    linarith
  have hmon : Work.EKLC6Core.cellRad μ y j
      ≤ Work.EKLC6Core.cellRad μ y j * (1 + Work.EKLC6Core.deltac * ε) := by
    nlinarith [hde, hrpos]
  rw [Work.EKLC6Core.shell]
  refine ⟨Work.Misiurewicz.Vball_mono (y j) hmon hzB, ?_⟩
  -- suppose `z = u • y j` lies deep inside the ball.
  intro hzdeep
  obtain ⟨u, hu, rfl⟩ := Work.EKLComp.mem_Vball.mp hzdeep
  have hcap : Work.EKLC6Core.injCap (u • y j) ≤ 2 ^ 19 * Work.EKLC6Core.injCap (y j) :=
    Work.EKLC6Core.injCap_le_mul_of_mem_Vball (z := u • y j) (y := y j)
      (r := Work.EKLC6Core.cellRad μ y j * (1 - Work.EKLC6Core.deltac * ε))
      (by nlinarith [hde, hde1, hrpos]) hr8 ⟨u, hu, rfl⟩
  have hkey := badInCol_arith_k (r := Work.EKLC6Core.cellRad μ y j)
    (ink0 := Work.EKLC6Core.injCap (y j)) (inkz := Work.EKLC6Core.injCap (u • y j))
    (ε := ε) (de := Work.EKLC6Core.deltac * ε)
    hrpos hr1 hε0 hde hde1 hβ hcap rfl
  have hsum := badInCol_arith_sum (r := Work.EKLC6Core.cellRad μ y j)
    (inkz := Work.EKLC6Core.injCap (u • y j)) (ε := ε)
    (de := Work.EKLC6Core.deltac * ε) hkey
  have hmem : v • (u • y j) ∈ Work.EKLComp.Vball (Work.EKLC6Core.cellRad μ y j) (y j) := by
    refine ⟨v * u, ?_, ?_⟩
    · refine Work.Misiurewicz.V_mono ?_ (Work.EKLC6Core.V_mul_subset_V
        (s := ε * Work.EKLC6Core.injCap (u • y j))
        (t := Work.EKLC6Core.cellRad μ y j * (1 - Work.EKLC6Core.deltac * ε))
        (mul_nonneg (le_of_lt hε0) (le_of_lt (Work.EKLC6Core.injCap_pos _)))
        (by nlinarith [hde, hde1, hrpos]) hv hu)
      linarith [hsum]
    · exact mul_smul v u (y j)
  exact hvz hmem

end Work.EKLC6Core
