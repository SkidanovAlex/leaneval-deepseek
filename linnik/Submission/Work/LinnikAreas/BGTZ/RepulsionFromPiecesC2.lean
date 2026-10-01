import Mathlib
import Submission.Work.LinnikAreas.BGTZZFR
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.BGTZ.DetectorLowerAux
import Submission.Work.LinnikAreas.BGTZ.LFunctionZeroFromZeroMult
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.LinnikAreas.OtherCharRepel.otherCharRepelConst
import Submission.Work.LinnikAreas.BGTZ.SharedZeroLower
import Submission.Work.LinnikAreas.BGTZ.DetectorChain
import Submission.Work.LinnikAreas.BGTZArith.RepulsionSizesReal
import Submission.Work.LinnikAreas.BGTZArith.RepulsionSizesC
import Submission.Work.LinnikAreas.BGTZArith.RepulsionSizesD
import Submission.Work.LinnikAreas.BGTZ.PrincipalNoRealZero
import Submission.Work.LinnikAreas.BGTZ.DetectorEDefs
import Submission.Work.LinnikAreas.BGTZ.E.RepulsionSizesE
import Submission.Work.LinnikAreas.BGTZ.E.caseC_bound_far
import Submission.Work.LinnikAreas.BGTZ.DetectorETarget
import Submission.Work.LinnikAreas.BGTZArith.caseB_bound
import Submission.Work.LinnikAreas.BGTZArith.caseC_bound
import Submission.Work.LinnikAreas.BGTZArith.detector_step
import Submission.Work.LinnikAreas.BGTZArith.phi_bound

namespace Work.LinnikAreas.BGTZ

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
open Work.LinnikContract

set_option maxHeartbeats 4000000

/-! **Auxiliary lemmas.**

The conclusion `(log (1/lam1) - log (C0*U))/U <= lam` of `RepulsionGenC` is equivalent (for the
positive quantities at hand) to `1 <= lam1*C0*U*exp (lam*U)`; `C0_times_min` is the arithmetic that
makes `C0 = max (1000/cZ) 1000` the right additive constant. -/

lemma repulsionGoal_of_exp {lam1 lam U C0 : ℝ} (h1 : 0 < lam1) (hU : 0 < U) (hC0 : 0 < C0)
    (h : 1 ≤ lam1 * C0 * U * Real.exp (lam * U)) :
    (Real.log (1 / lam1) - Real.log (C0 * U)) / U ≤ lam := by
  have hCU : 0 < C0 * U := mul_pos hC0 hU
  have hq : 0 < (1 : ℝ) / lam1 := one_div_pos.mpr h1
  have hpos : 0 < lam1 * C0 * U := mul_pos (mul_pos h1 hC0) hU
  rw [div_le_iff₀ hU]
  have hlog : Real.log (1 / lam1) - Real.log (C0 * U)
      = Real.log ((1 / lam1) / (C0 * U)) := (Real.log_div hq.ne' hCU.ne').symm
  rw [hlog, Real.log_le_iff_le_exp (div_pos hq hCU)]
  have key : (1 / lam1) / (C0 * U) = 1 / (lam1 * C0 * U) := by field_simp
  rw [key, div_le_iff₀ hpos]
  linarith [h]

lemma lamOf_ofReal (q : ℕ) (beta : ℝ) :
    lamOf q (beta : ℂ) = (1 - beta) * Real.log q := by
  simp [lamOf]

lemma zeroMult_re_lt_one_of {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    {rho : ℂ} (h : zeroMult chi rho ≠ 0) : rho.re < 1 :=
  Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one chi h

lemma C0_times_min {cZ : ℝ} (hcZ : 0 < cZ) :
    1000 ≤ max (1000 / cZ) 1000 * min cZ 1 := by
  rcases le_total cZ 1 with h | h
  · have h2 : min cZ 1 = cZ := min_eq_left h
    have h1 : (1000 : ℝ) / cZ * cZ = 1000 := by field_simp
    rw [h2]
    calc (1000 : ℝ) = (1000 / cZ) * cZ := h1.symm
      _ ≤ max (1000 / cZ) 1000 * cZ := mul_le_mul_of_nonneg_right (le_max_left _ _) hcZ.le
  · have h2 : min cZ 1 = 1 := min_eq_right h
    rw [h2, mul_one]
    exact le_max_right _ _

/-- `1 ≤ x` and `0 ≤ y` give `1 ≤ x * exp y`. -/
lemma one_le_mul_exp_of {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) : 1 ≤ x * Real.exp y := by
  have h1 : 1 ≤ Real.exp y := Real.one_le_exp hy
  have h2 : 0 ≤ x := le_trans zero_le_one hx
  have h3 := mul_le_mul hx h1 zero_le_one h2
  simpa using h3

/-! **The theorem** (statement frozen).  Route: reduce to `1 <= lam1*C0*U*exp (lam*U)` via
`repulsionGoal_of_exp`; Case I is immediate; in Case II split into (a) `rho = beta1` (the shared
exceptional zero, `SharedZeroLower` + `C0_times_min`), (b) `rho.re = beta1`, `rho.im != 0` (the
zero-free region alone, `caseB_bound`), (c) `rho.re < 1/2 + 1/100` (`caseC_bound`) and (d) the
detector case `1/2 + 1/100 <= rho.re < beta1` (`RepulsionSizes` + `SieveWeightsProp` +
`DetectorMainProp` + `DetectorChain` + `phi_bound` + `detector_step`). -/
/-- **The detector interface with its constant pinned (the usable form).**

`Work.LinnikAreas.BGTZ.DetectorMainProp` was repaired (2026-09-28) by asking, for the sifting level
`R`, both `C·A²q^{2θ}e^{2(log q)^{3/4}}(1-β₁)^{-2} ≤ R` and `R ≤ 2·sieveR A θ q β₁`, where
`sieveR A θ q β₁ = 256·A²q^{2θ}e^{2(log q)^{3/4}}(1-β₁)^{-2}`; the two conditions can hold together
*only* when the existential constant `C` of the interface satisfies `C ≤ 512`.  That constant is not
pinned, so the interface is provable with the vacuous witness `C = 1000` (see
`Work.LinnikAreas.BGTZArith.detectorMainProp_vacuous`) and carries no detector bound that a consumer
who must *exhibit* `R` can use.  This definition is the usable form, with the constant pinned:
`C ≤ 510` is the *largest* pin for which a consumer can exhibit the sifting level at all (with
`R := ⌈C·A²·X⌉ + 1 ≤ C·A²·X + 2 ≤ 512·A²·X = 2·sieveR`, using `A²X ≥ 1`); BGTZ's own choice
`R = sieveR` forces the sharper `C ≤ 256`, and any pin in between is fine.  The size conditions for
the consumer are `Work.LinnikAreas.BGTZArith.RepulsionSizesD` (which subsumes the `C ≤ 256` version
`RepulsionSizesC`). -/
def DetectorMainPropPinned (Cmax : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ C ≤ Cmax ∧ ∀ (q : ℕ) [NeZero q], 400000 < q → ∀ (χ₁ : DirichletCharacter ℂ q),
    χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ∀ {β₁ : ℝ}, β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    1 - 1 / (10 * Real.log q) < β₁ →
    ∀ {A θ B ε Cz : ℝ}, HypA A θ → HypB B ε → HypZeta Cz →
    ∀ {R : ℕ}, 200 ≤ R →
    C * A ^ 2 * (q : ℝ) ^ (2 * θ) * Real.exp (2 * (Real.log q) ^ (3 / 4 : ℝ))
        * (1 - β₁) ^ (-2 : ℝ) ≤ (R : ℝ) →
    (R : ℝ) ≤ 2 * sieveR A θ q β₁ →
    ∀ {θw : ℕ → ℝ}, IsSieveWeight R θw →
    sieveGre χ₁ R θw 1 (1 : DirichletCharacter ℂ q)
        ≤ (q : ℝ) / (q.totient : ℝ)
          * (∑ n ∈ Finset.Icc 1 R, aCoeff χ₁ n / (n : ℝ))⁻¹ →
    ∀ (χ : DirichletCharacter ℂ q) (T : ℝ), 4 ≤ T → ∀ {ρ : ℂ},
      (DirichletCharacter.LFunction χ ρ = 0 ∨ DirichletCharacter.LFunction (χ * χ₁) ρ = 0) →
      1 / 2 < ρ.re → |ρ.im| ≤ T →
    ∀ (N : ℕ), C * A ^ 8 * Real.exp (8 * (Real.log q) ^ (3 / 4 : ℝ))
          * (Real.log (2 + A ^ 2 * (q : ℝ) ^ 3)) ^ 24 * (q : ℝ) ^ (8 * θ) * T ^ (4 * θ)
          * (1 - β₁) ^ (-2 : ℝ) ≤ (N : ℝ) →
      ‖detector χ₁ χ N θw ρ‖
        ≤ ((2 - β₁) / (1 - ρ.re) + 1 / (ρ.re - 1 / 2)) * (1 - β₁)
          * ((N : ℝ) ^ (1 - ρ.re))

/-- The pinned interface implies the unpinned one (forget the bound). -/
theorem DetectorMainPropPinned.toProp {Cmax : ℝ} (h : DetectorMainPropPinned Cmax) :
    Work.LinnikAreas.BGTZ.DetectorMainProp := by
  obtain ⟨C, hCpos, _, h⟩ := h
  exact ⟨C, hCpos, h⟩

/-- A pinning at a smaller constant implies a pinning at a larger one. -/
theorem DetectorMainPropPinned.mono {c c' : ℝ} (h : DetectorMainPropPinned c) (hle : c ≤ c') :
    DetectorMainPropPinned c' := by
  obtain ⟨C, hCpos, hC, h⟩ := h
  exact ⟨C, hCpos, le_trans hC hle, h⟩

theorem RepulsionFromPiecesC2_aux (cZ : ℝ) (hcZ : 0 < cZ)
    (hA : ∃ A : ℝ, Work.LinnikAreas.BGTZ.HypA A (1 / 4 + 1 / 100))
    (hB : ∃ B : ℝ, Work.LinnikAreas.BGTZ.HypB B (1 / 100))
    (hZ : ∃ Cz : ℝ, Work.LinnikAreas.BGTZ.HypZeta Cz)
    (hSW : Work.LinnikAreas.BGTZ.SieveWeightsProp)
    (hS2 : Work.LinnikAreas.BGTZ.SelbergSieveMainProp)
    (hR : Work.LinnikAreas.BGTZ.RatioLoneProp)
    (hDet : DetectorMainPropPinned 510)
    (hzfr : Work.LinnikAreas.BGTZ.ZFRInputL cZ) :
    Work.LinnikAreas.BGTZ.RepulsionGenC (11 / 5) (11 / 10) (max (1000 / cZ) 1000) := by
  obtain ⟨A₀, hA₀⟩ := hA
  obtain ⟨B₀, hB₀⟩ := hB
  obtain ⟨Cz, hZ₀⟩ := hZ
  obtain ⟨Cd, hCdpos, hCd510, hDet₀⟩ := hDet
  obtain ⟨q₀Z, hZFR₀⟩ := hzfr
  obtain ⟨q₀R, hRep₀⟩ := Work.LinnikAreas.OtherCharRepel.otherCharRepelConst
  set A : ℝ := max A₀ 1 with hAdef
  set B : ℝ := max B₀ 1 with hBdef
  have hA1 : 1 ≤ A := by rw [hAdef]; exact le_max_right _ _
  have hB1 : 1 ≤ B := by rw [hBdef]; exact le_max_right _ _
  have hA₀A : A₀ ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hB₀B : B₀ ≤ B := by rw [hBdef]; exact le_max_left _ _
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA1
  set L0 : ℝ :=
    1000000000 + 1000 * (|Real.log A| + |Real.log B| + |Real.log Cd| + |Real.log cZ| + 1)
    with hL0def
  refine ⟨max (max q₀Z q₀R) (max 400001 (⌈Real.exp L0⌉₊ + 1)), ?_⟩
  intro q hq hqne χ₁ β₁ hχ₁ hsq hβ₁lt hz₁ hlamlow hlamup χ ρ hzρ hne hle
  have hqZ : q₀Z ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqR : q₀R ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq400 : 400001 ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hceil : ⌈Real.exp L0⌉₊ + 1 ≤ q :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have hq400' : 400000 < q := by omega
  have hq3 : 3 ≤ q := by omega
  have hq1R : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have h𝓛pos : 0 < Real.log (q : ℝ) := Real.log_pos hq1R
  have hL0le : L0 ≤ Real.log (q : ℝ) := by
    have h1 : Real.exp L0 ≤ ((⌈Real.exp L0⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp L0⌉₊ : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hceil
    have h3 : Real.exp L0 < (q : ℝ) := by linarith
    have h4 : Real.log (Real.exp L0) < Real.log (q : ℝ) :=
      Real.log_lt_log (Real.exp_pos L0) h3
    rw [Real.log_exp] at h4
    linarith
  have hL0big : (1000000000 : ℝ) ≤ L0 := by
    rw [hL0def]
    have h1 : 0 ≤ |Real.log A| := abs_nonneg _
    have h2 : 0 ≤ |Real.log B| := abs_nonneg _
    have h3 : 0 ≤ |Real.log Cd| := abs_nonneg _
    have h4 : 0 ≤ |Real.log cZ| := abs_nonneg _
    linarith
  have h𝓛8 : (100000000 : ℝ) ≤ Real.log (q : ℝ) := by linarith
  have h𝓛big : (1000 : ℝ) ≤ Real.log (q : ℝ) := by linarith
  have h𝓛big2 : (2000 : ℝ) ≤ Real.log (q : ℝ) := by linarith
  have hlogA : Real.log A ≤ Real.log (q : ℝ) / 1000 := by
    have h1 : 1000 * |Real.log A| ≤ L0 := by
      rw [hL0def]
      have h2 : 0 ≤ |Real.log B| := abs_nonneg _
      have h3 : 0 ≤ |Real.log Cd| := abs_nonneg _
      have h4 : 0 ≤ |Real.log cZ| := abs_nonneg _
      linarith
    have h2 : Real.log A ≤ |Real.log A| := le_abs_self _
    linarith
  have hlogB : Real.log B ≤ Real.log (q : ℝ) / 1000 := by
    have h1 : 1000 * |Real.log B| ≤ L0 := by
      rw [hL0def]
      have h2 : 0 ≤ |Real.log A| := abs_nonneg _
      have h3 : 0 ≤ |Real.log Cd| := abs_nonneg _
      have h4 : 0 ≤ |Real.log cZ| := abs_nonneg _
      linarith
    have h2 : Real.log B ≤ |Real.log B| := le_abs_self _
    linarith
  have hlogCd : Real.log Cd ≤ Real.log (q : ℝ) / 1000 := by
    have h1 : 1000 * |Real.log Cd| ≤ L0 := by
      rw [hL0def]
      have h2 : 0 ≤ |Real.log A| := abs_nonneg _
      have h3 : 0 ≤ |Real.log B| := abs_nonneg _
      have h4 : 0 ≤ |Real.log cZ| := abs_nonneg _
      linarith
    have h2 : Real.log Cd ≤ |Real.log Cd| := le_abs_self _
    linarith
  have hAinst : Work.LinnikAreas.BGTZ.HypA A (1 / 4 + 1 / 100) := by
    refine ⟨hApos, by norm_num, le_rfl, ?_⟩
    intro N _ ψ hψprim hψ1 t
    have h1 := hA₀.2.2.2 ψ hψprim hψ1 t
    refine le_trans h1 ?_
    refine mul_le_mul_of_nonneg_right hA₀A ?_
    exact Real.rpow_nonneg (by positivity) _
  set 𝓛 : ℝ := Real.log (q : ℝ) with h𝓛def
  set P : ℝ := Work.LinnikContract.lamOf q (β₁ : ℂ) with hPdef
  set L : ℝ := Work.LinnikContract.lamOf q ρ with hLdef
  set U : ℝ := 11 / 5 + (11 / 10) * (Real.log (5 + |ρ.im|) / 𝓛) with hUdef
  set C₀ : ℝ := max (1000 / cZ) 1000 with hC₀def
  have hPreal : P = (1 - β₁) * 𝓛 := by
    rw [hPdef, h𝓛def]; exact lamOf_ofReal q β₁
  have hLreal : L = (1 - ρ.re) * 𝓛 := by
    rw [hLdef, h𝓛def]; rfl
  have hC₀pos : 0 < C₀ := by
    rw [hC₀def]
    exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1000) (le_max_right _ _)
  have hC₀1000 : 1000 ≤ C₀ := by rw [hC₀def]; exact le_max_right _ _
  have hU1 : 11 / 5 ≤ U := by
    rw [hUdef]
    have h1 : 0 ≤ (11 / 10) * (Real.log (5 + |ρ.im|) / 𝓛) := by
      refine mul_nonneg (by norm_num) ?_
      refine div_nonneg ?_ h𝓛pos.le
      exact Real.log_nonneg (by linarith [abs_nonneg ρ.im])
    linarith
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num : (0:ℝ) < 11 / 5) hU1
  have hPpos : 0 < P := by
    have h1 : 0 < 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * 𝓛) := by
      refine one_div_pos.mpr ?_
      exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) h𝓛pos
    exact lt_trans h1 hlamlow
  have hPleL : P ≤ L := hle
  have hLpos : 0 < L := lt_of_lt_of_le hPpos hPleL
  have hkey : 1 ≤ P * C₀ * U * Real.exp (L * U) := by
    by_cases hI : 1 ≤ P * C₀ * U
    · exact one_le_mul_exp_of hI (mul_nonneg hLpos.le hUpos.le)
    · push_neg at hI
      have hCU2200 : 2200 ≤ C₀ * U := by
        have h := mul_le_mul hC₀1000 hU1 (by norm_num : (0:ℝ) ≤ 11 / 5) hC₀pos.le
        norm_num at h
        linarith
      have hCUpos : 0 < C₀ * U := mul_pos hC₀pos hUpos
      have hP2200 : P < 1 / 2200 := by
        have h1 : P < 1 / (C₀ * U) := by
          rw [lt_div_iff₀ hCUpos]
          nlinarith [hI]
        have h2 : 1 / (C₀ * U) ≤ 1 / 2200 :=
          one_div_le_one_div_of_le (by norm_num) hCU2200
        linarith
      have hδlt : 1 - β₁ < 1 / (2200 * 𝓛) := by
        have h1 : (1 - β₁) * 𝓛 < 1 / 2200 := by
          rw [← hPreal]; exact hP2200
        have h2 : 1 - β₁ < (1 / 2200) / 𝓛 := by
          rw [lt_div_iff₀ h𝓛pos]
          linarith [h1]
        have h3 : (1 / 2200 : ℝ) / 𝓛 = 1 / (2200 * 𝓛) := by field_simp
        linarith [h2, h3.le, h3.ge]
      have hβ1big : 1 - 1 / (10 * 𝓛) < β₁ := by
        have ha : 0 < 10 * 𝓛 := by linarith
        have h1 : 1 / (2200 * 𝓛) ≤ 1 / (10 * 𝓛) := by
          refine one_div_le_one_div_of_le ha ?_
          linarith
        linarith
      have h1β1pos : 0 < 1 - β₁ := by
        have h1 : 0 < 1 / (2200 * 𝓛) := by positivity
        linarith
      have hβ1half : (1 / 2 : ℝ) < β₁ := by
        have h1 : 1 / (10 * 𝓛) ≤ 1 / 10000 := by
          refine one_div_le_one_div_of_le (by norm_num) ?_
          linarith
        linarith
      by_cases hρβ : ρ = (β₁ : ℂ)
      · -- (a) the shared exceptional zero
        have hχne₁ : χ ≠ χ₁ := by
          intro h; exact hne ⟨h, hρβ⟩
        have hsz : min cZ 1 / 2200 ≤ P := by
          have h1 := Work.LinnikAreas.BGTZ.SharedZeroLower (q := q) cZ hcZ
            (fun χa βa h1 h2 h3 h4 h5 χb ρb hL hre hne' =>
              hZFR₀ q hqZ χa βa h1 h2 h3 h4 h5 χb ρb hL hre hne')
            (fun χ₀ ρ₀ hmin hsq0 him0 hlam0 χb ρb h1 h2 h3 h4 h5 =>
              hRep₀ q hqR χ₀ ρ₀ hmin hsq0 him0 hlam0 χb ρb h1 h2 h3 h4 h5)
            hχ₁ hsq hβ₁lt hz₁ (by rw [← hPdef]; exact hlamup) h𝓛big hχne₁ ?_
          · rw [hPdef]; exact h1
          · rw [← hρβ]; exact hzρ
        have h1 : 1 ≤ P * C₀ * U := by
          have hC0min : 1000 ≤ C₀ * min cZ 1 := by
            rw [hC₀def]; exact C0_times_min hcZ
          have h2 : (min cZ 1 / 2200) * (11 / 5) ≤ P * U :=
            mul_le_mul hsz hU1 (by norm_num) hPpos.le
          have h3 : ((min cZ 1 / 2200) * (11 / 5)) * C₀ ≤ (P * U) * C₀ :=
            mul_le_mul_of_nonneg_right h2 hC₀pos.le
          have h4 : ((min cZ 1 / 2200) * (11 / 5)) * C₀ = (C₀ * min cZ 1) / 1000 := by ring
          have h5 : (1 : ℝ) ≤ (C₀ * min cZ 1) / 1000 := by linarith
          have h6 : (P * U) * C₀ = P * C₀ * U := by ring
          linarith [h3, h4, h5, h6]
        exact one_le_mul_exp_of h1 (mul_nonneg hLpos.le hUpos.le)
      · by_cases hρre : ρ.re = β₁
        · -- (b) same real part, nonzero imaginary part
          have hre_half : (1 / 2 : ℝ) < ρ.re := by rw [hρre]; exact hβ1half
          have hρre_le1 : ρ.re ≤ 1 := by rw [hρre]; linarith [hβ₁lt]
          have hLz : DirichletCharacter.LFunction χ ρ = 0 :=
            LFunction_eq_zero_of_zeroMult_complex χ (le_of_lt hre_half) hρre_le1 hzρ
          have hzfr_ρ := hZFR₀ q hqZ χ₁ β₁ hχ₁ hsq hβ₁lt hz₁ hβ1big χ ρ (Or.inl hLz)
            hre_half hρβ
          have hlogmpos : 0 < Real.log ((q : ℝ) * max 4 |ρ.im|) := by
            refine Real.log_pos ?_
            have hm : (1 : ℝ) < max 4 |ρ.im| :=
              lt_of_lt_of_le (by norm_num) (le_max_left _ _)
            nlinarith
          have hzfr2 : cZ ≤ (P / 𝓛) * Real.log ((q : ℝ) * max 4 |ρ.im|) := by
            have h1 : 1 - ρ.re = P / 𝓛 := by
              rw [hρre, hPreal]
              field_simp
            rw [h1, div_le_iff₀ hlogmpos] at hzfr_ρ
            exact hzfr_ρ
          have hU_b : 11 / 5 + (11 / 10) * ((Real.log (max 4 |ρ.im|) - Real.log 4) / 𝓛) ≤ U := by
            rw [hUdef]
            have hTle : Real.log (max 4 |ρ.im|) ≤ Real.log 4 + Real.log (5 + |ρ.im|) := by
              have h1 : max 4 |ρ.im| ≤ 4 * (5 + |ρ.im|) := by
                refine max_le ?_ ?_ <;> nlinarith [abs_nonneg ρ.im]
              have h4 : 0 < max 4 |ρ.im| :=
                lt_of_lt_of_le (by norm_num) (le_max_left _ _)
              calc Real.log (max 4 |ρ.im|) ≤ Real.log (4 * (5 + |ρ.im|)) :=
                    Real.log_le_log h4 h1
                _ = Real.log 4 + Real.log (5 + |ρ.im|) :=
                    Real.log_mul (by norm_num) (by positivity)
            have h3 : (Real.log (max 4 |ρ.im|) - Real.log 4) / 𝓛
                ≤ Real.log (5 + |ρ.im|) / 𝓛 := by
              refine div_le_div_of_nonneg_right ?_ h𝓛pos.le
              linarith
            have h4 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 11 / 10)
            linarith [h4]
          have h1 : 1 ≤ P * max (1000 / cZ) 1000 * U := by
            have hb := Work.LinnikAreas.BGTZArith.caseB_bound (cZ := cZ) (Lq := 𝓛)
              (T := max 4 |ρ.im|) (U := U) (P := P) (q := (q : ℝ))
              hcZ hq1R h𝓛def h𝓛big (le_max_left _ _) hU_b hzfr2
            exact hb
          exact one_le_mul_exp_of h1 (mul_nonneg hLpos.le hUpos.le)
        · by_cases hc : ρ.re < 1 / 2 + 1 / 100
          · -- (c) far to the left
            have hL49 : (49 / 100) * 𝓛 ≤ L := by
              rw [hLreal]
              have h1 : (49 / 100 : ℝ) ≤ 1 - ρ.re := by linarith
              nlinarith [h𝓛pos, h1]
            have hc1 := Work.LinnikAreas.BGTZArith.caseC_bound (q := q) (cZ := cZ)
              (Lq := 𝓛) (U := U) (P := P) (L := L) hq1R h𝓛def h𝓛big hU1 hlamlow hL49
            rw [hC₀def]
            exact hc1
          · -- (d) the detector
            push_neg at hc
            have hρre_le_β₁ : ρ.re ≤ β₁ := by
              have h1 : (1 - β₁) * 𝓛 ≤ (1 - ρ.re) * 𝓛 := by
                rw [← hPreal, ← hLreal]; exact hle
              nlinarith [h𝓛pos, h1]
            have hρβ1lt : ρ.re < β₁ := lt_of_le_of_ne hρre_le_β₁ hρre
            have hT4 : (4 : ℝ) ≤ 5 + |ρ.im| := by linarith [abs_nonneg ρ.im]
            have hγT : |ρ.im| ≤ 5 + |ρ.im| := by linarith
            have hSiegel : B / ((q : ℝ) ^ (1 / 100 : ℝ) * (Real.log (q : ℝ)) ^ 2) < 1 - β₁ := by
              have hden : 0 < (q : ℝ) ^ (1 / 100 : ℝ) * (Real.log (q : ℝ)) ^ 2 :=
                mul_pos (Real.rpow_pos_of_pos (by linarith) _) (pow_pos h𝓛pos 2)
              rcases lt_or_ge B₀ 1 with hB0lt | hB0ge
              · have hB0 : B = 1 := by rw [hBdef]; exact max_eq_right (le_of_lt hB0lt)
                have hqpow : 0 < (q : ℝ) ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
                have hlt : 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * 𝓛) < (1 - β₁) * 𝓛 := by
                  rw [← hPreal]; exact hlamlow
                have hstep := (div_lt_iff₀ (mul_pos hqpow h𝓛pos)).mp hlt
                have hgoal : 1 < (1 - β₁) * ((q : ℝ) ^ (1 / 100 : ℝ) * 𝓛 ^ 2) := by
                  have heq : ((1 - β₁) * 𝓛) * ((q : ℝ) ^ (1 / 100 : ℝ) * 𝓛)
                      = (1 - β₁) * ((q : ℝ) ^ (1 / 100 : ℝ) * 𝓛 ^ 2) := by ring
                  rw [heq] at hstep
                  exact hstep
                rw [hB0, div_lt_iff₀ hden]
                exact hgoal
              · have hB0 : B = B₀ := by rw [hBdef]; exact max_eq_left hB0ge
                rw [hB0]
                exact hB₀.2.2.2 q hq3 χ₁ β₁ hχ₁ hsq hβ₁lt hz₁ (by linarith [hβ1big])
            obtain ⟨R, N, hR200, hN2, hNδ, hRlo, hRhi, hNsize, hlogNmax⟩ :=
              Work.LinnikAreas.BGTZArith.RepulsionSizesD (q := q) (A := A) (B := B) (C := Cd)
                (cZ := cZ) (T := 5 + |ρ.im|) (β₁ := β₁) (γ := ρ.im)
                hA1 hB1 hCdpos hCd510 hcZ hT4 hγT le_rfl hβ₁lt hβ1big hSiegel h𝓛8 hlogA hlogB
            obtain ⟨θw, hθwsw, hθwgre⟩ := hSW (q := q) hq400' χ₁ hsq hR200
            have hLzρ : DirichletCharacter.LFunction χ ρ = 0 :=
              LFunction_eq_zero_of_zeroMult_complex χ (by linarith)
                (by linarith [hρβ1lt, hβ₁lt]) hzρ
            have hLzβ : DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 :=
              LFunction_eq_zero_of_zeroMult_complex χ₁ (by rw [Complex.ofReal_re]; linarith [hβ1half]) (le_of_lt hβ₁lt) hz₁
            have hupρ := hDet₀ q hq400' χ₁ hsq hχ₁ hβ₁lt hz₁ hβ1big
              (A := A) (θ := 1 / 4 + 1 / 100) (B := B₀) (ε := 1 / 100) (Cz := Cz)
              hAinst hB₀ hZ₀ hR200 hRlo hRhi hθwsw hθwgre χ (5 + |ρ.im|) hT4
              (Or.inl hLzρ) (by linarith) hγT N hNsize
            have hupβ₀ := hDet₀ q hq400' χ₁ hsq hχ₁ hβ₁lt hz₁ hβ1big
              (A := A) (θ := 1 / 4 + 1 / 100) (B := B₀) (ε := 1 / 100) (Cz := Cz)
              hAinst hB₀ hZ₀ hR200 hRlo hRhi hθwsw hθwgre
              (1 : DirichletCharacter ℂ q) (5 + |ρ.im|) hT4
              (Or.inr (by rw [one_mul]; exact hLzβ)) (by simpa using hβ1half)
              (by rw [Complex.ofReal_im, abs_zero]; linarith [abs_nonneg ρ.im]) N hNsize
            have hupβ : (detector χ₁ 1 N θw (β₁ : ℂ)).re ≤
                ((2 - β₁) / (1 - β₁) + 1 / (β₁ - 1 / 2)) * (1 - β₁) * ((N : ℝ) ^ (1 - β₁)) :=
              le_trans (Complex.re_le_norm _) hupβ₀
            have hmpos : 0 < max 4 |ρ.im| := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
            have hX1 : (1 : ℝ) ≤ Real.log ((q : ℝ) * max 4 |ρ.im|) := by
              rw [Real.log_mul (by linarith) (ne_of_gt hmpos)]
              have h2 : 0 ≤ Real.log (max 4 |ρ.im|) :=
                Real.log_nonneg (le_trans (by norm_num : (1 : ℝ) ≤ 4) (le_max_left _ _))
              linarith
            have hX0 : 0 ≤ Real.log ((q : ℝ) * max 4 |ρ.im|) := le_trans zero_le_one hX1
            have hZFRρ : cZ / Real.log ((q : ℝ) * max 4 |ρ.im|) ≤ 1 - ρ.re :=
              hZFR₀ q hqZ χ₁ β₁ hχ₁ hsq hβ₁lt hz₁ hβ1big χ ρ (Or.inl hLzρ)
                (by linarith) hρβ
            have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
            have hchain := Work.LinnikAreas.BGTZ.DetectorChain (q := q) (χ₁ := χ₁) (χ := χ)
              (θw := θw) (N := N) (β₁ := β₁) (ρ := ρ) (cZ := cZ) (Lmax := 𝓛 * U)
              hcZ hsq hθwsw.1 hN2 hβ₁lt h1β1pos hβ1big h𝓛big hρre_le_β₁ hc hX1 hZFRρ
              hNδ hlogNmax hupρ hupβ
            have hhU : 𝓛 * U = (11 / 5) * 𝓛 + (11 / 10) * Real.log (5 + |ρ.im|) := by
              rw [hUdef]; field_simp
            have hXbound : Real.log ((q : ℝ) * max 4 |ρ.im|)
                ≤ 𝓛 + Real.log 4 + Real.log (5 + |ρ.im|) := by
              rw [Real.log_mul (by linarith) (ne_of_gt hmpos)]
              have h1 : Real.log (max 4 |ρ.im|) ≤ Real.log 4 + Real.log (5 + |ρ.im|) := by
                have h2 : max 4 |ρ.im| ≤ 4 * (5 + |ρ.im|) := by
                  refine max_le ?_ ?_ <;> nlinarith [abs_nonneg ρ.im]
                calc Real.log (max 4 |ρ.im|) ≤ Real.log (4 * (5 + |ρ.im|)) :=
                      Real.log_le_log hmpos h2
                  _ = Real.log 4 + Real.log (5 + |ρ.im|) :=
                      Real.log_mul (by norm_num) (by positivity)
              linarith [h1]
            set Φ : ℝ := 1.01 * (Real.log ((q : ℝ) * max 4 |ρ.im|) / cZ) + 𝓛 * U + 106 with hΦdef
            have hΦb : Φ * Real.exp 1 ≤ C₀ * U * 𝓛 := by
              rw [hΦdef, hC₀def]
              exact Work.LinnikAreas.BGTZArith.phi_bound (cZ := cZ) (Lq := 𝓛) (U := U)
                (X := Real.log ((q : ℝ) * max 4 |ρ.im|))
                (Φ := 1.01 * (Real.log ((q : ℝ) * max 4 |ρ.im|) / cZ) + 𝓛 * U + 106)
                (γ := ρ.im) hcZ h𝓛big2 hX0 hhU hXbound rfl
            have hΦpos : 0 < Φ := by
              rw [hΦdef]
              have h2 : 0 < 𝓛 * U := mul_pos h𝓛pos hUpos
              have h3 : 0 ≤ 1.01 * (Real.log ((q : ℝ) * max 4 |ρ.im|) / cZ) :=
                mul_nonneg (by norm_num) (div_nonneg hX0 hcZ.le)
              linarith
            have hstep := Work.LinnikAreas.BGTZArith.detector_step (Lq := 𝓛) (σ := ρ.re)
              (β₁ := β₁) (U := U) (P := P) (L := L) (N := (N : ℝ)) (Φ := Φ) (C₀ := C₀)
              h𝓛pos hUpos hΦpos hLpos hLreal hPreal hβ₁lt hN2R hlogNmax hchain hΦb
            have hkey' : Real.log (1 / P) - Real.log (C₀ * U) ≤ L * U := by
              have h2 := hstep
              rwa [div_le_iff₀ hUpos] at h2
            have hCUne : C₀ * U ≠ 0 := mul_ne_zero hC₀pos.ne' hUpos.ne'
            have h2 : Real.log (1 / (P * C₀ * U)) = Real.log (1 / P) - Real.log (C₀ * U) := by
              have h1 : (1 : ℝ) / (P * C₀ * U) = (1 / P) / (C₀ * U) := by field_simp
              rw [h1, Real.log_div (one_div_ne_zero hPpos.ne') hCUne]
            have h3 : Real.log (1 / (P * C₀ * U)) ≤ L * U := by rw [h2]; exact hkey'
            have h4 : (1 / (P * C₀ * U)) ≤ Real.exp (L * U) := by
              have h5 := Real.exp_le_exp.mpr h3
              rwa [Real.exp_log (by positivity)] at h5
            have h6 : 0 < P * C₀ * U := by positivity
            rw [div_le_iff₀ h6] at h4
            calc (1 : ℝ) ≤ Real.exp (L * U) * (P * C₀ * U) := h4
              _ = P * C₀ * U * Real.exp (L * U) := by ring
  exact repulsionGoal_of_exp hPpos hUpos hC₀pos hkey



/-! **The assembly against the corrected (non-vacuous) detector interface.**

`RepulsionFromPiecesC2_aux` is the same assembly against `DetectorMainPropPinned`; that interface
is *retired* (`BGTZ/NOTE_detector_interface_2026-09-28.md`), so the live route takes the detector as
`Work.LinnikAreas.BGTZ.DetectorPropE`, which is *non-vacuous* (`CR >= 1` with the window
`[CR.sieveX, 2.CR.sieveX]` never empty, and an independent `CN > 0`).  Three edits with respect to
`RepulsionFromPiecesC2_aux`:

* the sizes come from `Work.LinnikAreas.BGTZ.E.RepulsionSizesE` (`CR`, `CN`, and the scale
  `detNE` with `(1-b1)^{-6}` and `(1+log R)^{18}`), and `L0` is chosen to dominate `log CR`, `log CN`;
* case (c) is `Re rho < 3/4` (the detector interface only covers `Re rho >= 3/4`), so it uses
  `E.caseC_bound_far` with `L >= Lq/4 >= Lq/200`;
* the detector hypotheses: `3/4 <= Re rho` in place of `1/2 < Re rho`, and `1 + |Im rho| <= T`.

`HypB`, `SelbergSieveMainProp` and `RatioLoneProp` are *not* used. -/
theorem RepulsionFromPiecesC2E_aux (cZ : ℝ) (hcZ : 0 < cZ)
    (hA : ∃ A : ℝ, Work.LinnikAreas.BGTZ.HypA A (1 / 4 + 1 / 100))
    (hZ : ∃ Cz : ℝ, Work.LinnikAreas.BGTZ.HypZeta Cz)
    (hSW : Work.LinnikAreas.BGTZ.SieveWeightsProp)
    (hDetE : Work.LinnikAreas.BGTZ.DetectorPropE)
    (hzfr : Work.LinnikAreas.BGTZ.ZFRInputL cZ) :
    Work.LinnikAreas.BGTZ.RepulsionGenC (11 / 5) (11 / 10) (max (1000 / cZ) 1000) := by
  obtain ⟨A₀, hA₀⟩ := hA
  obtain ⟨Cz, hZ₀⟩ := hZ
  obtain ⟨CR, hCR1, CN, hCNpos, hDet₀⟩ := hDetE
  obtain ⟨q₀Z, hZFR₀⟩ := hzfr
  obtain ⟨q₀R, hRep₀⟩ := Work.LinnikAreas.OtherCharRepel.otherCharRepelConst
  set A : ℝ := max A₀ 1 with hAdef
  have hA1 : 1 ≤ A := by rw [hAdef]; exact le_max_right _ _
  have hA₀A : A₀ ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA1
  set L0 : ℝ := (10 : ℝ) ^ 12
      + 10000 * (|Real.log A| + |Real.log CR| + |Real.log CN| + |Real.log cZ| + 1) with hL0def
  refine ⟨max (max q₀Z q₀R) (max 400001 (⌈Real.exp L0⌉₊ + 1)), ?_⟩
  intro q hq hqne χ₁ β₁ hχ₁ hsq hβ₁lt hz₁ hlamlow hlamup χ ρ hzρ hne hle
  have hqZ : q₀Z ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqR : q₀R ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq400 : 400001 ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hceil : ⌈Real.exp L0⌉₊ + 1 ≤ q :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have hq4002 : 400000 < q := by omega
  have hq3 : 3 ≤ q := by omega
  have hq1R : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hLqpos : 0 < Real.log (q : ℝ) := Real.log_pos hq1R
  have hL0le : L0 ≤ Real.log (q : ℝ) := by
    have h1 : Real.exp L0 ≤ ((⌈Real.exp L0⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp L0⌉₊ : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hceil
    have h3 : Real.exp L0 < (q : ℝ) := by linarith
    have h4 : Real.log (Real.exp L0) < Real.log (q : ℝ) :=
      Real.log_lt_log (Real.exp_pos L0) h3
    rw [Real.log_exp] at h4
    linarith
  have hL0big : ((10 : ℝ) ^ 12) ≤ L0 := by
    rw [hL0def]
    have h1 : 0 ≤ |Real.log A| := abs_nonneg _
    have h2 : 0 ≤ |Real.log CR| := abs_nonneg _
    have h3 : 0 ≤ |Real.log CN| := abs_nonneg _
    have h4 : 0 ≤ |Real.log cZ| := abs_nonneg _
    linarith
  have hL12 : (10 : ℝ) ^ 12 ≤ Real.log (q : ℝ) := le_trans hL0big hL0le
  have hL8 : (100000000 : ℝ) ≤ Real.log (q : ℝ) := le_trans (by norm_num) hL12
  have hLbig : (1000 : ℝ) ≤ Real.log (q : ℝ) := le_trans (by norm_num) hL12
  have hLbig2 : (2000 : ℝ) ≤ Real.log (q : ℝ) := le_trans (by norm_num) hL12
  have hlogA : Real.log A ≤ Real.log (q : ℝ) / 10000 := by
    have h1 : 10000 * |Real.log A| ≤ L0 := by
      rw [hL0def]
      have h2 : 0 ≤ |Real.log CR| := abs_nonneg _
      have h3 : 0 ≤ |Real.log CN| := abs_nonneg _
      have h4 : 0 ≤ |Real.log cZ| := abs_nonneg _
      linarith
    have h2 : Real.log A ≤ |Real.log A| := le_abs_self _
    linarith
  have hlogCR : Real.log CR ≤ Real.log (q : ℝ) / 10000 := by
    have h1 : 10000 * |Real.log CR| ≤ L0 := by
      rw [hL0def]
      have h2 : 0 ≤ |Real.log A| := abs_nonneg _
      have h3 : 0 ≤ |Real.log CN| := abs_nonneg _
      have h4 : 0 ≤ |Real.log cZ| := abs_nonneg _
      linarith
    have h2 : Real.log CR ≤ |Real.log CR| := le_abs_self _
    linarith
  have hlogCN : Real.log CN ≤ Real.log (q : ℝ) / 10000 := by
    have h1 : 10000 * |Real.log CN| ≤ L0 := by
      rw [hL0def]
      have h2 : 0 ≤ |Real.log A| := abs_nonneg _
      have h3 : 0 ≤ |Real.log CR| := abs_nonneg _
      have h4 : 0 ≤ |Real.log cZ| := abs_nonneg _
      linarith
    have h2 : Real.log CN ≤ |Real.log CN| := le_abs_self _
    linarith
  have hAinst : Work.LinnikAreas.BGTZ.HypA A (1 / 4 + 1 / 100) := by
    refine ⟨hApos, by norm_num, le_rfl, ?_⟩
    intro N _ ψ hψprim hψ1 t
    have h1 := hA₀.2.2.2 ψ hψprim hψ1 t
    refine le_trans h1 ?_
    refine mul_le_mul_of_nonneg_right hA₀A ?_
    exact Real.rpow_nonneg (by positivity) _
  set Lq : ℝ := Real.log (q : ℝ) with hLqdef
  set P : ℝ := Work.LinnikContract.lamOf q (β₁ : ℂ) with hPdef
  set L : ℝ := Work.LinnikContract.lamOf q ρ with hLdef
  set U : ℝ := 11 / 5 + (11 / 10) * (Real.log (5 + |ρ.im|) / Lq) with hUdef
  set C₀ : ℝ := max (1000 / cZ) 1000 with hC₀def
  have hPreal : P = (1 - β₁) * Lq := by
    rw [hPdef, hLqdef]; exact lamOf_ofReal q β₁
  have hLreal : L = (1 - ρ.re) * Lq := by
    rw [hLdef, hLqdef]; rfl

  have hC₀pos : 0 < C₀ := by
    rw [hC₀def]
    exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1000) (le_max_right _ _)
  have hC₀1000 : 1000 ≤ C₀ := by rw [hC₀def]; exact le_max_right _ _
  have hU1 : 11 / 5 ≤ U := by
    rw [hUdef]
    have h1 : 0 ≤ (11 / 10) * (Real.log (5 + |ρ.im|) / Lq) := by
      refine mul_nonneg (by norm_num) ?_
      refine div_nonneg ?_ hLqpos.le
      exact Real.log_nonneg (by linarith [abs_nonneg ρ.im])
    linarith
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num : (0:ℝ) < 11 / 5) hU1
  have hPpos : 0 < P := by
    have h1 : 0 < 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Lq) := by
      refine one_div_pos.mpr ?_
      exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) hLqpos
    exact lt_trans h1 hlamlow
  have hPleL : P ≤ L := hle
  have hLpos : 0 < L := lt_of_lt_of_le hPpos hPleL
  have hkey : 1 ≤ P * C₀ * U * Real.exp (L * U) := by
    by_cases hI : 1 ≤ P * C₀ * U
    · exact one_le_mul_exp_of hI (mul_nonneg hLpos.le hUpos.le)
    · push_neg at hI
      have hCU2200 : 2200 ≤ C₀ * U := by
        have h := mul_le_mul hC₀1000 hU1 (by norm_num : (0:ℝ) ≤ 11 / 5) hC₀pos.le
        norm_num at h
        linarith
      have hCUpos : 0 < C₀ * U := mul_pos hC₀pos hUpos
      have hP2200 : P < 1 / 2200 := by
        have h1 : P < 1 / (C₀ * U) := by
          rw [lt_div_iff₀ hCUpos]
          nlinarith [hI]
        have h2 : 1 / (C₀ * U) ≤ 1 / 2200 :=
          one_div_le_one_div_of_le (by norm_num) hCU2200
        linarith
      have hb1dlt : 1 - β₁ < 1 / (2200 * Lq) := by
        have h1 : (1 - β₁) * Lq < 1 / 2200 := by
          rw [← hPreal]; exact hP2200
        have h2 : 1 - β₁ < (1 / 2200) / Lq := by
          rw [lt_div_iff₀ hLqpos]
          linarith [h1]
        have h3 : (1 / 2200 : ℝ) / Lq = 1 / (2200 * Lq) := by field_simp
        linarith [h2, h3.le, h3.ge]
      have hb1big : 1 - 1 / (10 * Lq) < β₁ := by
        have ha : 0 < 10 * Lq := by linarith
        have h1 : 1 / (2200 * Lq) ≤ 1 / (10 * Lq) := by
          refine one_div_le_one_div_of_le ha ?_
          linarith
        linarith
      have h1b1pos : 0 < 1 - β₁ := by
        have h1 : 0 < 1 / (2200 * Lq) := by positivity
        linarith
      have hb1half : (1 / 2 : ℝ) < β₁ := by
        have h1 : 1 / (10 * Lq) ≤ 1 / 10000 := by
          refine one_div_le_one_div_of_le (by norm_num) ?_
          linarith
        linarith
      by_cases hrb : ρ = (β₁ : ℂ)
      · -- (a) the shared exceptional zero
        have hχne₁ : χ ≠ χ₁ := by
          intro h; exact hne ⟨h, hrb⟩
        have hsz : min cZ 1 / 2200 ≤ P := by
          have h1 := Work.LinnikAreas.BGTZ.SharedZeroLower (q := q) cZ hcZ
            (fun χa βa h1 h2 h3 h4 h5 χb ρb hL hre hne2 =>
              hZFR₀ q hqZ χa βa h1 h2 h3 h4 h5 χb ρb hL hre hne2)
            (fun χ0 ρ0 hmin hsq0 him0 hlam0 χb ρb h1 h2 h3 h4 h5 =>
              hRep₀ q hqR χ0 ρ0 hmin hsq0 him0 hlam0 χb ρb h1 h2 h3 h4 h5)
            hχ₁ hsq hβ₁lt hz₁ (by rw [← hPdef]; exact hlamup) hLbig hχne₁ ?_
          · rw [hPdef]; exact h1
          · rw [← hrb]; exact hzρ
        have h1 : 1 ≤ P * C₀ * U := by
          have hC0min : 1000 ≤ C₀ * min cZ 1 := by
            rw [hC₀def]; exact C0_times_min hcZ
          have h2 : (min cZ 1 / 2200) * (11 / 5) ≤ P * U :=
            mul_le_mul hsz hU1 (by norm_num) hPpos.le
          have h3 : ((min cZ 1 / 2200) * (11 / 5)) * C₀ ≤ (P * U) * C₀ :=
            mul_le_mul_of_nonneg_right h2 hC₀pos.le
          have h4 : ((min cZ 1 / 2200) * (11 / 5)) * C₀ = (C₀ * min cZ 1) / 1000 := by ring
          have h5 : (1 : ℝ) ≤ (C₀ * min cZ 1) / 1000 := by linarith
          have h6 : (P * U) * C₀ = P * C₀ * U := by ring
          linarith [h3, h4, h5, h6]
        exact one_le_mul_exp_of h1 (mul_nonneg hLpos.le hUpos.le)

      · by_cases hρre : ρ.re = β₁
        · -- (b) same real part, nonzero imaginary part
          have hre_half : (1 / 2 : ℝ) < ρ.re := by rw [hρre]; exact hb1half
          have hρre_le1 : ρ.re ≤ 1 := by rw [hρre]; linarith [hβ₁lt]
          have hLz : DirichletCharacter.LFunction χ ρ = 0 :=
            LFunction_eq_zero_of_zeroMult_complex χ (le_of_lt hre_half) hρre_le1 hzρ
          have hzfr_r := hZFR₀ q hqZ χ₁ β₁ hχ₁ hsq hβ₁lt hz₁ hb1big χ ρ (Or.inl hLz)
            hre_half hrb
          have hlogmpos : 0 < Real.log ((q : ℝ) * max 4 |ρ.im|) := by
            refine Real.log_pos ?_
            have hm : (1 : ℝ) < max 4 |ρ.im| :=
              lt_of_lt_of_le (by norm_num) (le_max_left _ _)
            nlinarith
          have hzfr2 : cZ ≤ (P / Lq) * Real.log ((q : ℝ) * max 4 |ρ.im|) := by
            have h1 : 1 - ρ.re = P / Lq := by
              rw [hρre, hPreal]
              field_simp
            rw [h1, div_le_iff₀ hlogmpos] at hzfr_r
            exact hzfr_r
          have hU_b : 11 / 5 + (11 / 10) * ((Real.log (max 4 |ρ.im|) - Real.log 4) / Lq) ≤ U := by
            rw [hUdef]
            have hTle : Real.log (max 4 |ρ.im|) ≤ Real.log 4 + Real.log (5 + |ρ.im|) := by
              have h1 : max 4 |ρ.im| ≤ 4 * (5 + |ρ.im|) := by
                refine max_le ?_ ?_ <;> nlinarith [abs_nonneg ρ.im]
              have h4 : 0 < max 4 |ρ.im| :=
                lt_of_lt_of_le (by norm_num) (le_max_left _ _)
              calc Real.log (max 4 |ρ.im|) ≤ Real.log (4 * (5 + |ρ.im|)) :=
                    Real.log_le_log h4 h1
                _ = Real.log 4 + Real.log (5 + |ρ.im|) :=
                    Real.log_mul (by norm_num) (by positivity)
            have h3 : (Real.log (max 4 |ρ.im|) - Real.log 4) / Lq
                ≤ Real.log (5 + |ρ.im|) / Lq := by
              refine div_le_div_of_nonneg_right ?_ hLqpos.le
              linarith
            have h4 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 11 / 10)
            linarith [h4]
          have h1 : 1 ≤ P * max (1000 / cZ) 1000 * U := by
            have hb := Work.LinnikAreas.BGTZArith.caseB_bound (cZ := cZ) (Lq := Lq)
              (T := max 4 |ρ.im|) (U := U) (P := P) (q := (q : ℝ))
              hcZ hq1R hLqdef hLbig (le_max_left _ _) hU_b hzfr2
            exact hb
          exact one_le_mul_exp_of h1 (mul_nonneg hLpos.le hUpos.le)
        · by_cases hc : ρ.re < 3 / 4
          · -- (c) far to the left of the detector range
            have hL200 : Lq / 200 ≤ L := by
              rw [hLreal]
              have h1 : (1 / 200 : ℝ) ≤ 1 - ρ.re := by linarith
              nlinarith [hLqpos, h1]
            have hc1 := Work.LinnikAreas.BGTZ.E.caseC_bound_far (q := q) (cZ := cZ)
              (Lq := Lq) (U := U) (P := P) (L := L) hq1R hLqdef hLbig hU1 hlamlow hL200
            rw [hC₀def]
            exact hc1

          · -- (d) the detector
            push_neg at hc
            have hρre_le_β₁ : ρ.re ≤ β₁ := by
              have h1 : (1 - β₁) * Lq ≤ (1 - ρ.re) * Lq := by
                rw [← hPreal, ← hLreal]; exact hle
              nlinarith [hLqpos, h1]
            have hρβ1lt : ρ.re < β₁ := lt_of_le_of_ne hρre_le_β₁ hρre
            have hT4 : (4 : ℝ) ≤ 5 + |ρ.im| := by linarith [abs_nonneg ρ.im]
            have h1γ : 1 + |ρ.im| ≤ 5 + |ρ.im| := by linarith
            have hb34 : (3 / 4 : ℝ) ≤ β₁ := by
              have h1 : 1 / (10 * Lq) ≤ 1 / 4 := by
                refine one_div_le_one_div_of_le (by norm_num) ?_
                linarith
              linarith
            obtain ⟨R, N, hR200, hN2, hNδ, hRlo, hRhi, hNsize, hlogNmax⟩ :=
              Work.LinnikAreas.BGTZ.E.RepulsionSizesE (q := q) (A := A) (CR := CR) (CN := CN)
                (β₁ := β₁) (γ := ρ.im) hA1 hCR1 hCNpos hβ₁lt hb1big hlamlow hL12 hlogA hlogCR
                hlogCN
            obtain ⟨θw, hθwsw, hθwgre⟩ := hSW (q := q) hq4002 χ₁ hsq hR200
            have hLzρ : DirichletCharacter.LFunction χ ρ = 0 :=
              LFunction_eq_zero_of_zeroMult_complex χ (by linarith)
                (by linarith [hρβ1lt, hβ₁lt]) hzρ
            have hLzβ : DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 :=
              LFunction_eq_zero_of_zeroMult_complex χ₁
                (by rw [Complex.ofReal_re]; linarith [hb1half]) (le_of_lt hβ₁lt) hz₁
            have hupρ := hDet₀ q hq4002 χ₁ hsq hχ₁ hβ₁lt hz₁ hb1big
              (A := A) (Cz := Cz) hA1 hAinst hZ₀ hR200 hRlo hRhi hθwsw hθwgre
              χ (5 + |ρ.im|) hT4 (Or.inl hLzρ) hc h1γ N hNsize
            have hupβ₀ := hDet₀ q hq4002 χ₁ hsq hχ₁ hβ₁lt hz₁ hb1big
              (A := A) (Cz := Cz) hA1 hAinst hZ₀ hR200 hRlo hRhi hθwsw hθwgre
              (1 : DirichletCharacter ℂ q) (5 + |ρ.im|) hT4
              (Or.inr (by rw [one_mul]; exact hLzβ)) (by simpa using hb34)
              (by rw [Complex.ofReal_im, abs_zero]; linarith [abs_nonneg ρ.im]) N hNsize
            have hupβ : (detector χ₁ 1 N θw (β₁ : ℂ)).re ≤
                ((2 - β₁) / (1 - β₁) + 1 / (β₁ - 1 / 2)) * (1 - β₁) * ((N : ℝ) ^ (1 - β₁)) :=
              le_trans (Complex.re_le_norm _) hupβ₀
            have hmpos : 0 < max 4 |ρ.im| := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
            have hX1 : (1 : ℝ) ≤ Real.log ((q : ℝ) * max 4 |ρ.im|) := by
              rw [Real.log_mul (by linarith) (ne_of_gt hmpos)]
              have h2 : 0 ≤ Real.log (max 4 |ρ.im|) :=
                Real.log_nonneg (le_trans (by norm_num : (1 : ℝ) ≤ 4) (le_max_left _ _))
              linarith
            have hX0 : 0 ≤ Real.log ((q : ℝ) * max 4 |ρ.im|) := le_trans zero_le_one hX1
            have hZFRr : cZ / Real.log ((q : ℝ) * max 4 |ρ.im|) ≤ 1 - ρ.re :=
              hZFR₀ q hqZ χ₁ β₁ hχ₁ hsq hβ₁lt hz₁ hb1big χ ρ (Or.inl hLzρ)
                (by linarith) hrb
            have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
            have hrege : (1 / 2 + 1 / 100 : ℝ) ≤ ρ.re := by linarith
            have hchain := Work.LinnikAreas.BGTZ.DetectorChain (q := q) (χ₁ := χ₁) (χ := χ)
              (θw := θw) (N := N) (β₁ := β₁) (ρ := ρ) (cZ := cZ) (Lmax := Lq * U)
              hcZ hsq hθwsw.1 hN2 hβ₁lt h1b1pos hb1big hLbig hρre_le_β₁ hrege hX1 hZFRr
              hNδ hlogNmax hupρ hupβ
            have hhU : Lq * U = (11 / 5) * Lq + (11 / 10) * Real.log (5 + |ρ.im|) := by
              rw [hUdef]; field_simp
            have hXbound : Real.log ((q : ℝ) * max 4 |ρ.im|)
                ≤ Lq + Real.log 4 + Real.log (5 + |ρ.im|) := by
              rw [Real.log_mul (by linarith) (ne_of_gt hmpos)]
              have h1 : Real.log (max 4 |ρ.im|) ≤ Real.log 4 + Real.log (5 + |ρ.im|) := by
                have h2 : max 4 |ρ.im| ≤ 4 * (5 + |ρ.im|) := by
                  refine max_le ?_ ?_ <;> nlinarith [abs_nonneg ρ.im]
                calc Real.log (max 4 |ρ.im|) ≤ Real.log (4 * (5 + |ρ.im|)) :=
                      Real.log_le_log hmpos h2
                  _ = Real.log 4 + Real.log (5 + |ρ.im|) :=
                      Real.log_mul (by norm_num) (by positivity)
              linarith [h1]
            set Φ : ℝ := 1.01 * (Real.log ((q : ℝ) * max 4 |ρ.im|) / cZ) + Lq * U + 106 with hΦdef
            have hΦb : Φ * Real.exp 1 ≤ C₀ * U * Lq := by
              rw [hΦdef, hC₀def]
              exact Work.LinnikAreas.BGTZArith.phi_bound (cZ := cZ) (Lq := Lq) (U := U)
                (X := Real.log ((q : ℝ) * max 4 |ρ.im|))
                (Φ := 1.01 * (Real.log ((q : ℝ) * max 4 |ρ.im|) / cZ) + Lq * U + 106)
                (γ := ρ.im) hcZ hLbig2 hX0 hhU hXbound rfl
            have hΦpos : 0 < Φ := by
              rw [hΦdef]
              have h2 : 0 < Lq * U := mul_pos hLqpos hUpos
              have h3 : 0 ≤ 1.01 * (Real.log ((q : ℝ) * max 4 |ρ.im|) / cZ) :=
                mul_nonneg (by norm_num) (div_nonneg hX0 hcZ.le)
              linarith
            have hstep := Work.LinnikAreas.BGTZArith.detector_step (Lq := Lq) (σ := ρ.re)
              (β₁ := β₁) (U := U) (P := P) (L := L) (N := (N : ℝ)) (Φ := Φ) (C₀ := C₀)
              hLqpos hUpos hΦpos hLpos hLreal hPreal hβ₁lt hN2R hlogNmax hchain hΦb
            have hkey2 : Real.log (1 / P) - Real.log (C₀ * U) ≤ L * U := by
              have h2 := hstep
              rwa [div_le_iff₀ hUpos] at h2
            have hCUne : C₀ * U ≠ 0 := mul_ne_zero (ne_of_gt hC₀pos) (ne_of_gt hUpos)
            have h2 : Real.log (1 / (P * C₀ * U)) = Real.log (1 / P) - Real.log (C₀ * U) := by
              have h1 : (1 : ℝ) / (P * C₀ * U) = (1 / P) / (C₀ * U) := by field_simp
              rw [h1, Real.log_div (one_div_ne_zero (ne_of_gt hPpos)) hCUne]
            have h3 : Real.log (1 / (P * C₀ * U)) ≤ L * U := by rw [h2]; exact hkey2
            have h4 : (1 / (P * C₀ * U)) ≤ Real.exp (L * U) := by
              have h5 := Real.exp_le_exp.mpr h3
              rwa [Real.exp_log (by positivity)] at h5
            have h6 : 0 < P * C₀ * U := by positivity
            rw [div_le_iff₀ h6] at h4
            calc (1 : ℝ) ≤ Real.exp (L * U) * (P * C₀ * U) := h4
              _ = P * C₀ * U * Real.exp (L * U) := by ring
  exact repulsionGoal_of_exp hPpos hUpos hC₀pos hkey


/-- **The requested statement (frozen).**

Its hypothesis `hDet` is the *retired* `Work.LinnikAreas.BGTZ.DetectorMainProp`, whose own `Exists`
does not pin its constant, so that it is provable with the vacuous witness `C = 1000`
(`Work.LinnikAreas.BGTZArith.detectorMainProp_vacuous`); it is used nowhere below
(`BGTZ/NOTE_detector_interface_2026-09-28.md` records the diagnosis).  The genuine detector is the
theorem `Work.LinnikAreas.BGTZ.DetectorE : DetectorPropE` of the corrected interface, and the
assembly against it is `RepulsionFromPiecesC2E_aux` above; the two lines below are the whole
discrepancy. -/
theorem RepulsionFromPiecesC2 (cZ : ℝ) (hcZ : 0 < cZ)
    (hA : ∃ A : ℝ, Work.LinnikAreas.BGTZ.HypA A (1 / 4 + 1 / 100))
    (hB : ∃ B : ℝ, Work.LinnikAreas.BGTZ.HypB B (1 / 100))
    (hZ : ∃ Cz : ℝ, Work.LinnikAreas.BGTZ.HypZeta Cz)
    (hSW : Work.LinnikAreas.BGTZ.SieveWeightsProp)
    (hS2 : Work.LinnikAreas.BGTZ.SelbergSieveMainProp)
    (hR : Work.LinnikAreas.BGTZ.RatioLoneProp)
    (hDet : Work.LinnikAreas.BGTZ.DetectorMainProp)
    (hzfr : Work.LinnikAreas.BGTZ.ZFRInputL cZ) :
    Work.LinnikAreas.BGTZ.RepulsionGenC (11 / 5) (11 / 10) (max (1000 / cZ) 1000) := by
  have hDetE : Work.LinnikAreas.BGTZ.DetectorPropE :=
    Work.LinnikAreas.BGTZ.DetectorPropE_of_workspace
  exact RepulsionFromPiecesC2E_aux cZ hcZ hA hZ hSW hDetE hzfr

end
end Work.LinnikAreas.BGTZ
