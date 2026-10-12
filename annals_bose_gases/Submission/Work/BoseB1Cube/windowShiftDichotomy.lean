import ChallengeDeps
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Submission.Work.BoseB1Cube.chiSmallB_shift_sq_le
import Submission.Work.BoseB1Cube.w1MassB_le_sharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.windowShiftDichotomy`

The **window/shift dichotomy** of the sliding-box analysis: for every prescribed `C ≥ 1`
there is a diluteness threshold `ε₀ > 0` such that for every admissible `μ`, every
`u ∈ goodSet`,

    μ · ∬ w_{1,B(u)}  ≤  C · (a v)

*or* the `χ_{B(u)}`-autocorrelation at every lag `‖z‖ ≤ R` is at least
`(1 - 2 Γ)`-times the `χ_{B(u)}`-mass, where `Γ = PBΓ v μ = K_B³(μa³)^{1/2} → 0`.

## Proof

Write `t = μ (a v)³`, `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`,
`χ_B = chiSmallB 48 ℓ d u`, `χ = chiMass 48 ℓ d u = ∫ χ_B²` and `Γ = PBΓ v μ`.

* **Branch 1** is the sharp mass law `w1MassB_le_sharp`: for every `δ > 0`,
  `PBW ≤ (1+δ)·8π(a v)·χ` for small diluteness; with `δ = 1` the bound
  `μ PBW ≤ C(a v)` follows as soon as `μ χ ≤ C/(16π)`.

* **Branch 2** uses the exact identity (`chiSmallB_sub_sq_eq`, the expansion of the
  square plus translation invariance)

      ∫ (χ_B(x) - χ_B(x-z))² = 2χ - 2∫ χ_B(x) χ_B(x-z) ,

  the global `L²`-shift bound `chiSmallB_shift_sq_le`

      ∫ (χ_B(x+z) - χ_B(x))² ≤ Cs ‖z‖² (ℓd + L²(ℓd)³/ℓ²)

  (whose Lipschitz input is supplied by `exists_chi_lipschitz`, from
  `ContDiff.lipschitzWith_of_hasCompactSupport` applied to the bump `chiBase`), and the
  *negation* of branch 1, which via the sharp mass law forces `χ ≥ C/(16πμ)`.

  Since `μ (a v)² (ℓd) = fsXp t 166`, `μ (a v)² ((ℓd)³/ℓ²) = fsXp t 178` while
  `Γ = fsXp t (287/2)`, the two thresholds close: the margin is
  `Γ/(μ ℓ d) = (a v)^{-2} t^{-45/646} → ∞`.  Branch 1 therefore holds whenever the
  `χ`-mass is below `C/(16πμ)`, branch 2 whenever it is above, and the `u ∈ goodSet`
  hypothesis is not needed by either estimate (both are uniform in `u`).
-/

namespace Work.BoseB1Cube

open MeasureTheory
open scoped Real

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## 1. A global Lipschitz constant for the corpus bump `χ` -/

/-- The corpus bump `Submission.BoseGases.chi` is globally Lipschitz.  Proof: `chi` is
`chiBase` up to the constant `1/√chiNormSq`, and `chiBase` is a `C^∞` function with
compact support, hence Lipschitz (`ContDiff.lipschitzWith_of_hasCompactSupport`). -/
theorem exists_chi_lipschitz : ∃ L : ℝ, 0 ≤ L ∧ ∀ x v : E3,
    |Submission.BoseGases.chi (x + v) - Submission.BoseGases.chi x| ≤ L * ‖v‖ := by
  obtain ⟨Cb, hCb⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    Submission.BoseGases.chiBase_hasCompactSupport Submission.BoseGases.chiBase_contDiff
    (by simp)
  set s := Real.sqrt Submission.BoseGases.chiNormSq with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos
  refine ⟨(Cb : ℝ) / s, by positivity, ?_⟩
  intro x v
  have hb : |Submission.BoseGases.chiBase (x + v) - Submission.BoseGases.chiBase x|
      ≤ (Cb : ℝ) * ‖v‖ := by
    have h := hCb.dist_le_mul (x + v) x
    have h2 : dist (x + v) x = ‖v‖ := by rw [dist_eq_norm, add_sub_cancel_left]
    rw [h2] at h
    exact h
  have hchi : ∀ y : E3, Submission.BoseGases.chi y = Submission.BoseGases.chiBase y / s :=
    fun y => rfl
  rw [hchi (x + v), hchi x, div_sub_div_same, abs_div, abs_of_pos hs0]
  calc |Submission.BoseGases.chiBase (x + v) - Submission.BoseGases.chiBase x| / s
      ≤ ((Cb : ℝ) * ‖v‖) / s := div_le_div_of_nonneg_right hb (le_of_lt hs0)
    _ = (Cb : ℝ) / s * ‖v‖ := by ring

/-! ## 2. `fsXp` arithmetic -/

/-- `fsXp · e` is nondecreasing in the diluteness for `e > 0`. -/
theorem fsXp_mono_le {s t e : ℝ} (hs : 0 < s) (hst : s ≤ t) (he : 0 < e) :
    Work.BoseBox.fsXp s e ≤ Work.BoseBox.fsXp t e := by
  rw [Work.BoseBox.fsXp]
  exact Real.rpow_le_rpow hs.le hst (div_nonneg he.le (by norm_num))

/-- For every `C ≥ 0`, `c > 0` and exponent `e > 0` there is `ε > 0` with
`C · fsXp ε e ≤ c`. -/
theorem exists_fsXp_mul_le {C c e : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (he : 0 < e) :
    ∃ ε : ℝ, 0 < ε ∧ C * Work.BoseBox.fsXp ε e ≤ c := by
  have hden : 0 < C + 1 := by linarith
  have hbase : 0 < c / (C + 1) := by positivity
  refine ⟨(c / (C + 1)) ^ (323 / e), Real.rpow_pos_of_pos hbase _, ?_⟩
  have hfe : Work.BoseBox.fsXp ((c / (C + 1)) ^ (323 / e)) e = c / (C + 1) := by
    rw [Work.BoseBox.fsXp, ← Real.rpow_mul hbase.le]
    rw [show 323 / e * (e / 323) = 1 by field_simp]
    rw [Real.rpow_one]
  rw [hfe]
  have hle1 : C / (C + 1) ≤ 1 := by rw [div_le_one hden]; linarith
  calc C * (c / (C + 1)) = c * (C / (C + 1)) := by ring
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left hle1 hc.le
    _ = c := by ring

/-- `μ (a v)² (d ℓ) = fsXp t 166`, `t = μ(a v)³` (`d ℓ = a·fsXp t (-157)`). -/
theorem mu_mul_sq_mul_l_d {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    μ * A^2 * (Work.BoseBox.sideAt μ A * (Work.BoseBox.paramsAt μ A).d)
      = Work.BoseBox.fsXp (μ * A^3) 166 := by
  have ht : (0:ℝ) < μ * A^3 := by positivity
  rw [mul_comm (Work.BoseBox.sideAt μ A) ((Work.BoseBox.paramsAt μ A).d),
    Work.BoseFixB1.d_mul_sideAt_eq hA hμ]
  calc μ * A^2 * (A * Work.BoseBox.fsXp (μ*A^3) (-157))
      = (μ * A^3) * Work.BoseBox.fsXp (μ*A^3) (-157) := by ring
    _ = Work.BoseBox.fsXp (μ*A^3) 323 * Work.BoseBox.fsXp (μ*A^3) (-157) := by
          rw [Work.BoseFixB1.fsXp_323]
    _ = Work.BoseBox.fsXp (μ*A^3) 166 := by rw [Work.BoseBox.fsXp_mul ht]; norm_num

/-- `μ (a v)² ((d ℓ)³/ℓ²) = fsXp t 178`, `t = μ(a v)³`. -/
theorem mu_mul_sq_mul_l_d_cube {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    μ * A^2 * ((Work.BoseBox.sideAt μ A * (Work.BoseBox.paramsAt μ A).d)^3
        / (Work.BoseBox.sideAt μ A)^2)
      = Work.BoseBox.fsXp (μ * A^3) 178 := by
  have ht : (0:ℝ) < μ * A^3 := by positivity
  have hsplit : (Work.BoseBox.sideAt μ A * (Work.BoseBox.paramsAt μ A).d)^3
      / (Work.BoseBox.sideAt μ A)^2
      = Work.BoseBox.sideAt μ A * (Work.BoseBox.paramsAt μ A).d^3 := by field_simp
  rw [hsplit, Work.BoseFixB1.sideAt_eq_fsXp hA hμ, Work.BoseFixB1.d_cube_eq hA hμ]
  calc μ * A^2 * (A * Work.BoseBox.fsXp (μ*A^3) (-163) * Work.BoseBox.fsXp (μ*A^3) 18)
      = (μ * A^3) * (Work.BoseBox.fsXp (μ*A^3) (-163) * Work.BoseBox.fsXp (μ*A^3) 18) := by
        ring
    _ = (μ * A^3) * Work.BoseBox.fsXp (μ*A^3) (-145) := by
        rw [Work.BoseBox.fsXp_mul ht]; norm_num
    _ = Work.BoseBox.fsXp (μ*A^3) 323 * Work.BoseBox.fsXp (μ*A^3) (-145) := by
        rw [Work.BoseFixB1.fsXp_323]
    _ = Work.BoseBox.fsXp (μ*A^3) 178 := by rw [Work.BoseBox.fsXp_mul ht]; norm_num

/-! ## 3. The exact shift identity for the sliding cutoff -/

/-- **The `L²`-shift identity**: `∫(χ_B(x) - χ_B(x-z))² = 2·chiMass - 2·autocorr`,
the expansion of the square together with the translation invariance of `∫ χ_B²`. -/
theorem chiSmallB_sub_sq_eq {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : E3) :
    (∫ x : E3, (Submission.BoseGases.chiSmallB M ℓ d u x
        - Submission.BoseGases.chiSmallB M ℓ d u (x - z)) ^ 2)
      = 2 * Work.SmallBoxSliding.chiMass M ℓ d u
        - 2 * ∫ x : E3, Submission.BoseGases.chiSmallB M ℓ d u x
            * Submission.BoseGases.chiSmallB M ℓ d u (x - z) := by
  set f : E3 → ℝ := fun x => Submission.BoseGases.chiSmallB M ℓ d u x
  have hcont : Continuous f := Submission.BoseGases.chiSmallB_continuous hM hℓ hd u
  have hcs : HasCompactSupport f := Submission.BoseGases.chiSmallB_hasCompactSupport hM hℓ u
  have hS : Integrable (fun x : E3 => (f x) ^ 2) := by
    have h2 : HasCompactSupport (fun x : E3 => (f x) ^ 2) :=
      hcs.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
    exact (hcont.pow 2).integrable_of_hasCompactSupport h2
  have hS2 : Integrable (fun x : E3 => (f (x - z)) ^ 2) := by
    have h := hS.comp_sub_right z
    simpa [Function.comp_def] using h
  have hS12 : Integrable (fun x : E3 => f x * f (x - z)) := by
    refine Integrable.mono' ((hS.add hS2).const_mul (1 / 2)) ?_ ?_
    · exact (hcont.mul (hcont.comp (continuous_id.sub continuous_const))).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul]
      simp only [Pi.add_apply]
      have h1 : |f x| ^ 2 = (f x)^2 := by rw [sq_abs]
      have h2 : |f (x - z)| ^ 2 = (f (x - z))^2 := by rw [sq_abs]
      nlinarith [sq_nonneg (|f x| - |f (x - z)|)]
  have htr : (∫ x : E3, (f (x - z)) ^ 2) = ∫ x : E3, (f x) ^ 2 :=
    MeasureTheory.integral_sub_right_eq_self (μ := (volume : Measure E3))
      (fun x : E3 => (f x) ^ 2) z
  have hexp : (∫ x : E3, (f x - f (x - z)) ^ 2)
      = (∫ x : E3, (f x) ^ 2) - 2 * (∫ x : E3, f x * f (x - z))
        + (∫ x : E3, (f (x - z)) ^ 2) := by
    have hI1 : Integrable (fun x : E3 => (f x) ^ 2 - 2 * (f x * f (x - z))) :=
      hS.sub (hS12.const_mul 2)
    have h1 : (∫ x : E3, (f x - f (x - z)) ^ 2)
        = ∫ x : E3, ((f x) ^ 2 - 2 * (f x * f (x - z))) + (f (x - z)) ^ 2 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      ring
    rw [h1, MeasureTheory.integral_add (f := fun x : E3 => (f x) ^ 2 - 2 * (f x * f (x - z)))
        (g := fun x : E3 => (f (x - z)) ^ 2) hI1 hS2]
    rw [MeasureTheory.integral_sub (f := fun x : E3 => (f x) ^ 2)
        (g := fun x : E3 => 2 * (f x * f (x - z))) hS (hS12.const_mul 2)]
    rw [MeasureTheory.integral_const_mul (f := fun x : E3 => f x * f (x - z))]
  simp only [Work.SmallBoxSliding.chiMass_def]
  rw [hexp, htr]
  ring

/-! ## 4. The target -/

theorem windowShiftDichotomy {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (C : ℝ) (hC : 1 ≤ C) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
        (Work.BoseFixB1B.PBW h μ u ≤ C * (_root_.BoseGases.a v) / μ) ∨
          (∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
            (1 - 2 * Work.BoseFixB1B.PBΓ v μ) *
                Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
                  (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u
              ≤ ∫ x : EuclideanSpace ℝ (Fin 3),
                  Submission.BoseGases.chiSmallB (Work.BoseFixB1B.PBM v μ)
                    (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u x
                  * Submission.BoseGases.chiSmallB (Work.BoseFixB1B.PBM v μ)
                    (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u (x - z)) := by
  obtain ⟨L, hL0, hLip⟩ := exists_chi_lipschitz
  obtain ⟨Cs, hCs0, hCs⟩ := chiSmallB_shift_sq_le
  obtain ⟨εw, hεw0, hwle⟩ := w1MassB_le_sharp h hv hv1 hvrad hR hv_supp hav (δ := 1) (by norm_num)
  obtain ⟨εa, hεa0, hεa⟩ := exists_fsXp_mul_le (C := 4 * Real.pi * Cs * R^2 * (1 + L^2))
      (c := C * (BoseGases.a v)^2) (by positivity) (by positivity) (e := (45/2 : ℝ)) (by norm_num)
  refine ⟨min εw (min 1 εa), lt_min hεw0 (lt_min one_pos hεa0), ?_⟩
  intro μ hAdm u hu
  have hμ0 : 0 < μ := hAdm.1
  have hdle : μ * (BoseGases.a v)^3 ≤ min εw (min 1 εa) := hAdm.2.1
  have hpar := hAdm.2.2
  have htw : μ * (BoseGases.a v)^3 ≤ εw := le_trans hdle (min_le_left _ _)
  have ht1 : μ * (BoseGases.a v)^3 ≤ 1 :=
    le_trans hdle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hta : μ * (BoseGases.a v)^3 ≤ εa :=
    le_trans hdle (le_trans (min_le_right _ _) (min_le_right _ _))
  have ht0 : 0 < μ * (BoseGases.a v)^3 := by positivity
  by_cases h1 : Work.BoseFixB1B.PBW h μ u ≤ C * (BoseGases.a v) / μ
  · exact Or.inl h1
  · refine Or.inr ?_
    have hgt : C * (BoseGases.a v) / μ < Work.BoseFixB1B.PBW h μ u := lt_of_not_ge h1
    set chiM : ℝ := Work.SmallBoxSliding.chiMass (Work.BoseFixB1B.PBM v μ)
      (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u with hchiM
    set Gam : ℝ := Work.BoseFixB1B.PBΓ v μ with hGam
    set f : E3 → ℝ := fun y => Submission.BoseGases.chiSmallB (Work.BoseFixB1B.PBM v μ)
      (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u y with hf
    have hℓ0 : 0 < Work.BoseFixB1B.PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
    have hd0 : 0 < Work.BoseFixB1B.PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
    have hM48 : 1 ≤ Work.BoseFixB1B.PBM v μ := by
      rw [Work.BoseFixB1B.PBM_eq]; norm_num [Work.BoseBox.mValue]
    -- the sharp mass law
    have hgw : Work.BoseFixB1B.PBW h μ u ≤ 16 * Real.pi * (BoseGases.a v) * chiM := by
      have hw := hwle μ (show Work.BoseBoxFix.Adm v εw μ from ⟨hμ0, htw, hpar⟩) u
      have hw' : Work.BoseFixB1B.PBW h μ u ≤ (1 + 1) * (8 * Real.pi * (BoseGases.a v)) * chiM := by
        simpa only [Work.BoseFixB1B.PBW, Work.BoseFixB1B.PBM, Work.BoseFixB1B.PBℓ,
          Work.BoseFixB1B.PBd, Work.BoseFixB1.pM, Work.BoseFixB1.pL, Work.BoseFixB1.pD,
          hchiM] using hw
      have h2 : (1 + 1) * (8 * Real.pi * (BoseGases.a v)) = 16 * Real.pi * (BoseGases.a v) := by
        ring
      rw [h2] at hw'
      exact hw'
    -- the forced lower bound on the χ-mass
    have hχ : C / (16 * Real.pi * μ) ≤ chiM := by
      have h2 : C * (BoseGases.a v) / μ < 16 * Real.pi * (BoseGases.a v) * chiM :=
        lt_of_lt_of_le hgt hgw
      rw [div_lt_iff₀ hμ0] at h2
      have h3 : C * (BoseGases.a v) < (chiM * (16 * Real.pi * μ)) * (BoseGases.a v) := by
        calc C * (BoseGases.a v) < (16 * Real.pi * (BoseGases.a v) * chiM) * μ := h2
          _ = (chiM * (16 * Real.pi * μ)) * (BoseGases.a v) := by ring
      have h4 : C < chiM * (16 * Real.pi * μ) := lt_of_mul_lt_mul_right h3 (le_of_lt hav)
      rw [div_le_iff₀ (by positivity : 0 < 16 * Real.pi * μ)]
      linarith
    have chiM0 : 0 ≤ chiM := by rw [hchiM]; exact Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
    have hGam0 : 0 ≤ Gam := by
      rw [hGam]
      rw [show Work.BoseFixB1B.PBΓ v μ = (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3
          * (μ * (BoseGases.a v) ^ 3) ^ (1/2:ℝ) from rfl, Work.BoseFixB1.KB3_half_eq hav hμ0]
      exact le_of_lt (Work.BoseBox.fsXp_pos (c := (287/2)) ht0)
    have hGamEq : Work.BoseFixB1B.PBΓ v μ
        = Work.BoseBox.fsXp (μ * (BoseGases.a v)^3) (287/2) := by
      rw [show Work.BoseFixB1B.PBΓ v μ = (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3
          * (μ * (BoseGases.a v) ^ 3) ^ (1/2:ℝ) from rfl, Work.BoseFixB1.KB3_half_eq hav hμ0]
    intro z hz
    set X : ℝ := Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ
        + L^2 * ((Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ)^3
            / (Work.BoseFixB1B.PBℓ v μ)^2) with hX
    have hX0 : 0 ≤ X := by
      rw [hX]
      have h1 : 0 ≤ Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ :=
        le_of_lt (mul_pos hℓ0 hd0)
      have h2 : 0 ≤ (Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ)^3
          / (Work.BoseFixB1B.PBℓ v μ)^2 := by positivity
      nlinarith [h1, h2, sq_nonneg L]
    -- the `L²`-shift bound
    have hD : (∫ x : E3, (f x - f (x - z))^2) ≤ Cs * R^2 * X := by
      have hz0 := hCs L (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u z
        hL0 hℓ0 hd0 hLip
      have hraw : (∫ x : E3, (Submission.BoseGases.chiSmallB (Work.BoseFixB1B.PBM v μ)
            (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u (x + z)
          - Submission.BoseGases.chiSmallB (Work.BoseFixB1B.PBM v μ)
            (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u x)^2) ≤ Cs * ‖z‖^2 * X := by
        rw [hX]
        simpa only [Work.BoseFixB1B.PBM_eq, Work.BoseBox.mValue, mul_div_assoc] using hz0
      have hraw' : (∫ x : E3, (f (x + z) - f x)^2) ≤ Cs * ‖z‖^2 * X := by
        simpa only [hf] using hraw
      have htrans : (∫ x : E3, (f (x + z) - f x)^2) = ∫ y : E3, (f y - f (y - z))^2 := by
        have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure E3))
          (fun y : E3 => (f y - f (y - z))^2) z
        simpa only [add_sub_cancel_right] using h
      rw [← htrans]
      calc (∫ x : E3, (f (x + z) - f x)^2) ≤ Cs * ‖z‖^2 * X := hraw'
        _ ≤ Cs * R^2 * X := by
            refine mul_le_mul_of_nonneg_right ?_ hX0
            exact mul_le_mul_of_nonneg_left (by nlinarith [hz, hR.le, norm_nonneg z]) hCs0
    -- the arithmetic: `Cs R² X ≤ 4 Γ χ`
    have hstep1 : Cs * R^2 * X ≤ Gam * C / (4 * Real.pi * μ) := by
      have hA2 : 0 < (BoseGases.a v)^2 := by positivity
      have hK1 : μ * (BoseGases.a v)^2 * (Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ)
          = Work.BoseBox.fsXp (μ * (BoseGases.a v)^3) 166 :=
        mu_mul_sq_mul_l_d (A := BoseGases.a v) (μ := μ) hav hμ0
      have hK2 : μ * (BoseGases.a v)^2
            * ((Work.BoseFixB1B.PBℓ v μ * Work.BoseFixB1B.PBd v μ)^3
              / (Work.BoseFixB1B.PBℓ v μ)^2)
          = Work.BoseBox.fsXp (μ * (BoseGases.a v)^3) 178 :=
        mu_mul_sq_mul_l_d_cube (A := BoseGases.a v) (μ := μ) hav hμ0
      have hE1 : 4 * Real.pi * μ * (BoseGases.a v)^2 * (Cs * R^2 * X)
          = 4 * Real.pi * Cs * R^2 * (Work.BoseBox.fsXp (μ * (BoseGases.a v)^3) 166
              + L^2 * Work.BoseBox.fsXp (μ * (BoseGases.a v)^3) 178) := by
        rw [hX, ← hK1, ← hK2]
        ring
      have hE2 : 4 * Real.pi * Cs * R^2 * (Work.BoseBox.fsXp (μ * (BoseGases.a v)^3) 166
            + L^2 * Work.BoseBox.fsXp (μ * (BoseGases.a v)^3) 178)
          ≤ C * (BoseGases.a v)^2 * Work.BoseBox.fsXp (μ * (BoseGases.a v)^3) (287/2) := by
        have h166 : Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (287/2)
              * Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (45/2)
            = Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) 166 := by
          rw [Work.BoseBox.fsXp_mul ht0]; norm_num
        have h178 : Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (287/2)
              * Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (69/2)
            = Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) 178 := by
          rw [Work.BoseBox.fsXp_mul ht0]; norm_num
        rw [← h166, ← h178]
        have h69 : Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (69/2)
            ≤ Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (45/2) :=
          Work.BoseBox.fsXp_le_fsXp ht0 ht1 (by norm_num)
        have h45 : Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (45/2)
            ≤ Work.BoseBox.fsXp εa (45/2) := fsXp_mono_le ht0 hta (by norm_num)
        have hkey : 4 * Real.pi * Cs * R^2 *
              (Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (45/2)
                + L^2 * Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (69/2))
            ≤ C * (BoseGases.a v)^2 := by
          have hb : Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (45/2)
                + L^2 * Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (69/2)
              ≤ (1 + L^2) * Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (45/2) := by
            nlinarith [h69, sq_nonneg L,
              (Work.BoseBox.fsXp_pos (c := (69/2)) ht0).le]
          calc 4 * Real.pi * Cs * R^2 *
                (Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (45/2)
                  + L^2 * Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (69/2))
              ≤ 4 * Real.pi * Cs * R^2 *
                  ((1 + L^2) * Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (45/2)) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
            _ ≤ 4 * Real.pi * Cs * R^2 * ((1 + L^2) * Work.BoseBox.fsXp εa (45/2)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_left h45 (by positivity)
            _ = (4 * Real.pi * Cs * R^2 * (1 + L^2)) * Work.BoseBox.fsXp εa (45/2) := by ring
            _ ≤ C * (BoseGases.a v)^2 := hεa
        have h287 : 0 ≤ Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (287/2) :=
          le_of_lt (Work.BoseBox.fsXp_pos (c := (287/2)) ht0)
        calc 4 * Real.pi * Cs * R^2 *
              (Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (287/2)
                * Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (45/2)
              + L^2 * (Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (287/2)
                * Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (69/2)))
            = Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (287/2) *
              (4 * Real.pi * Cs * R^2 *
                (Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (45/2)
                  + L^2 * Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (69/2))) := by ring
            _ ≤ Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (287/2) * (C * (BoseGases.a v)^2) :=
                mul_le_mul_of_nonneg_left hkey h287
            _ = C * (BoseGases.a v)^2 * Work.BoseBox.fsXp (μ*(BoseGases.a v)^3) (287/2) := by
                ring
      have hcomb : 4 * Real.pi * μ * (BoseGases.a v)^2 * (Cs * R^2 * X)
          ≤ Gam * C * (BoseGases.a v)^2 := by
        rw [hE1, hGam, hGamEq]
        linarith [hE2]
      have hmain' : (4 * Real.pi * μ * (Cs * R^2 * X)) * (BoseGases.a v)^2
          ≤ (Gam * C) * (BoseGases.a v)^2 := by
        calc (4 * Real.pi * μ * (Cs * R^2 * X)) * (BoseGases.a v)^2
            = 4 * Real.pi * μ * (BoseGases.a v)^2 * (Cs * R^2 * X) := by ring
          _ ≤ Gam * C * (BoseGases.a v)^2 := hcomb
          _ = (Gam * C) * (BoseGases.a v)^2 := by ring
      have hmain : 4 * Real.pi * μ * (Cs * R^2 * X) ≤ Gam * C :=
        le_of_mul_le_mul_right hmain' hA2
      rw [le_div_iff₀ (by positivity : 0 < 4 * Real.pi * μ)]
      linarith [hmain]
    have hstep2 : Gam * C / (4 * Real.pi * μ) ≤ 4 * Gam * chiM := by
      have h2 : Gam * C / (4 * Real.pi * μ) = 4 * Gam * (C / (16 * Real.pi * μ)) := by ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left hχ (by linarith [hGam0])
    have hDle : (∫ x : E3, (f x - f (x - z))^2) ≤ 4 * Gam * chiM :=
      le_trans hD (le_trans hstep1 hstep2)
    have hid : (∫ x : E3, (f x - f (x - z))^2) = 2 * chiM - 2 * ∫ x : E3, f x * f (x - z) := by
      have hh := chiSmallB_sub_sq_eq hM48 hℓ0 hd0 u z
      simpa only [hf, hchiM] using hh
    linarith

end Work.BoseB1Cube
