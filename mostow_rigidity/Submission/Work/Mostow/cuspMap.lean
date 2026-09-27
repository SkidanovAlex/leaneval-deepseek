import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.cuspPsiDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOfLevelYc
import Submission.Work.Mostow.hptOf_hdist
import Submission.Work.Mostow.horoSpec
import Submission.Work.Mostow.flatActBasic

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

variable {n : ℕ}

/-- The normalised flat coordinate `yc ξ u` of a point lies in `ξ^⊥`. -/
lemma yc_orth {ξ u : E n} (hξ : ξ ∈ Sph n) : inner ℝ (yc ξ u) ξ = 0 := by
  have hξξ : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have h : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
    rw [h, one_pow]
  rw [yc, real_inner_smul_left, wc, inner_sub_left, real_inner_smul_left, hξξ, mul_one, sub_self,
    mul_zero]

/-- The horospherical law of cosines for two points of prescribed level and flat coordinate at a
boundary point `ξ`: `hdist (hptOf ξ y D) (hptOf ξ y' D')` only depends on `log (D/D')` and on the
Euclidean distance of the flat coordinates, weighted by the product of the levels. -/
lemma hdist_hptOf_gen {ξ : E n} (hξ : ξ ∈ Sph n) (hI : HypIsoData n)
    (y y' : E n) (D D' : ℝ) (hy : inner ℝ y ξ = 0) (hy' : inner ℝ y' ξ = 0)
    (hD : 0 < D) (hD' : 0 < D') :
    hdist (hptOf ξ y D) (hptOf ξ y' D') =
      Real.arcosh (Real.cosh (Real.log (D / D')) + (D * D' / 2) * ‖y - y'‖ ^ 2) := by
  have h := levYcFormula hξ (hptOf ξ y D) (hptOf ξ y' D')
  rw [(hptOfLevelYc ξ hξ hy hD).1, (hptOfLevelYc ξ hξ hy hD).2.1,
      (hptOfLevelYc ξ hξ hy' hD').1, (hptOfLevelYc ξ hξ hy' hD').2.1] at h
  calc hdist (hptOf ξ y D) (hptOf ξ y' D')
      = Real.arcosh (Real.cosh (hdist (hptOf ξ y D) (hptOf ξ y' D'))) :=
        (Real.arcosh_cosh (hI.nonneg _ _)).symm
    _ = Real.arcosh (Real.cosh (Real.log (D / D')) + (D * D' / 2) * ‖y - y'‖ ^ 2) := by rw [h]

/-- An isometry fixing a boundary point `ξ` and preserving the levels acts on the horosphere of
`ξ` at *every* level by the same flat isometry: the flat coordinate of `g • hptOf ξ y D` is
independent of `D` and equals `flatAct ξ g y`. -/
theorem hptOf_smul_level (hA : POBasic n) (hI : HypIsoData n)
    {ξ : E n} (hξ : ξ ∈ Sph n) {g : PO n 1}
    (hg : bd g ξ = ξ) (h0 : lev ξ (g • (0 : E n)) = 1)
    {y : E n} (hy : inner ℝ y ξ = 0) {D : ℝ} (hD : 0 < D) :
    g • hptOf ξ y D = hptOf ξ (flatAct ξ g y) D := by
  have hz : inner ℝ (flatAct ξ g y) ξ = 0 := flatAct_mem hξ g y
  have hlevg : lev ξ (g • hptOf ξ y D) = D := by
    rw [lev_smul_self hI hA ξ hξ g (hptOf ξ y D) hg, (hptOfLevelYc ξ hξ hy hD).1, h0, mul_one]
  -- the point `g • hptOf ξ y D` is at distance `|log D|` from the level-one point `hptOf ξ z 1`
  have hd : hdist (hptOf ξ (flatAct ξ g y) 1) (g • hptOf ξ y D) = |Real.log D| := by
    have e1 : hdist (hptOf ξ (flatAct ξ g y) 1) (g • hptOf ξ y D)
        = hdist (g • horoPt ξ y) (g • hptOf ξ y D) := by
      rw [flatAct_horoPt hξ hA hI hg h0 hy, horoPt_eq_hptOf]
    rw [e1, hI.isom_smul, horoPt_eq_hptOf, hI.symm (hptOf ξ y 1) (hptOf ξ y D),
      hdist_hptOf_gen hξ hI y y D 1 hy hy hD one_pos]
    have ey : ‖y - y‖ ^ 2 = (0 : ℝ) := by simp
    rw [ey, mul_zero, add_zero]
    rw [Real.log_div (ne_of_gt hD) one_ne_zero, Real.log_one, sub_zero]
    rw [← Real.cosh_abs (Real.log D), Real.arcosh_cosh (abs_nonneg _)]
  -- hence the flat coordinate of `g • hptOf ξ y D` is forced
  have hpt_eq : hptOf ξ (yc ξ (g • hptOf ξ y D)) D = g • hptOf ξ y D := by
    have hh := hptOf_yc_lev hξ (g • hptOf ξ y D)
    rw [hlevg] at hh
    exact hh
  have hkey := hdist_hptOf_gen hξ hI (flatAct ξ g y) (yc ξ (g • hptOf ξ y D)) 1 D hz (yc_orth hξ)
    one_pos hD
  rw [hpt_eq] at hkey
  rw [hd] at hkey
  -- `|log D| = arccosh (cosh (log (1/D)) + (D/2) ‖z - yc ξ (g•hptOf ξ y D)‖²)`
  have h1X : (1 : ℝ) ≤ Real.cosh (Real.log (1 / D))
      + (1 * D / 2) * ‖flatAct ξ g y - yc ξ (g • hptOf ξ y D)‖ ^ 2 := by
    have hc := Real.one_le_cosh (Real.log (1 / D))
    have hs := sq_nonneg ‖flatAct ξ g y - yc ξ (g • hptOf ξ y D)‖
    nlinarith [hc, hs]
  have hc := congrArg Real.cosh hkey
  rw [Real.cosh_arcosh h1X] at hc
  have hlog : Real.log (1 / D) = -Real.log D := by
    rw [Real.log_div one_ne_zero (ne_of_gt hD), Real.log_one, zero_sub]
  have hcL : Real.cosh |Real.log D| = Real.cosh (Real.log D) := Real.cosh_abs _
  have hcR : Real.cosh (Real.log (1 / D)) = Real.cosh (Real.log D) := by
    rw [hlog, ← Real.cosh_abs (-Real.log D), abs_neg, Real.cosh_abs]
  rw [hcL, hcR] at hc
  have hzero : (1 * D / 2) * ‖flatAct ξ g y - yc ξ (g • hptOf ξ y D)‖ ^ 2 = 0 := by linarith
  have hpos2 : (0 : ℝ) < 1 * D / 2 := by linarith
  have hnorm : ‖flatAct ξ g y - yc ξ (g • hptOf ξ y D)‖ = 0 := by
    have h2 : ‖flatAct ξ g y - yc ξ (g • hptOf ξ y D)‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h (ne_of_gt hpos2)
      · exact h
    calc ‖flatAct ξ g y - yc ξ (g • hptOf ξ y D)‖
        = Real.sqrt (‖flatAct ξ g y - yc ξ (g • hptOf ξ y D)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = 0 := by rw [h2, Real.sqrt_zero]
  have hyc : yc ξ (g • hptOf ξ y D) = flatAct ξ g y := by
    have := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    exact this.symm
  calc g • hptOf ξ y D = hptOf ξ (yc ξ (g • hptOf ξ y D)) (lev ξ (g • hptOf ξ y D)) :=
        (hptOf_yc_lev hξ (g • hptOf ξ y D)).symm
    _ = hptOf ξ (flatAct ξ g y) D := by rw [hyc, hlevg]

theorem cuspMap {n : ℕ} (hA : Work.Mostow.POBasic n) (hI : Work.Mostow.HypIsoData n)
    {Γ Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)} (f : Γ ≃* Λ)
    {ξ η : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hη : η ∈ Submission.Mostow.Sph n) (tΓ tΛ : ℝ)
    (ψ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hpsiperp : ∀ x : Submission.Mostow.E n, inner ℝ x ξ = 0 → inner ℝ (ψ x) η = 0)
    (hpsiQI : ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧
      (∀ x y : Submission.Mostow.E n, inner ℝ x ξ = 0 → inner ℝ y ξ = 0 →
        ‖ψ x - ψ y‖ ≤ L * ‖x - y‖ + C) ∧
      (∀ x y : Submission.Mostow.E n, inner ℝ x ξ = 0 → inner ℝ y ξ = 0 →
        ‖x - y‖ ≤ L * ‖ψ x - ψ y‖ + C))
    (hpsisurj : ∃ C : ℝ, ∀ z : Submission.Mostow.E n, inner ℝ z η = 0 →
      ∃ x : Submission.Mostow.E n, inner ℝ x ξ = 0 ∧ ‖ψ x - z‖ ≤ C)
    (hstab : ∀ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Submission.Mostow.bd ((f γ : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) η = η)
    (hstab' : ∀ m : Λ, Submission.Mostow.bd ((m : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      ∃ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧ f γ = m)
    (hlevξ : ∀ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.lev ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • (0 : Submission.Mostow.E n)) = 1)
    (hlevη : ∀ m : Λ, Submission.Mostow.bd ((m : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      Work.Mostow.lev η (((m : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) • (0 : Submission.Mostow.E n)) = 1)
    (hpsieq : ∀ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      ∃ C : ℝ, ∀ x : Submission.Mostow.E n, inner ℝ x ξ = 0 →
        ‖ψ (Work.Mostow.flatAct ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)) x)
          - Work.Mostow.flatAct η (((f γ : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1)) (ψ x)‖ ≤ C)
    (hcpt : ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ u = 1 → ∃ γ : Γ,
        Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
        ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K) :
    ∃ Ψ : Submission.Mostow.E n → Submission.Mostow.E n,
      (∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Submission.Mostow.E n, Work.Mostow.lev ξ u ≤ Real.exp tΓ →
        Work.Mostow.lev ξ v ≤ Real.exp tΓ → Submission.Mostow.hdist u v ≤ 1 →
        Submission.Mostow.hdist (Ψ u) (Ψ v) ≤ C) ∧
      (∀ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
        ∃ C : ℝ, ∀ u : Submission.Mostow.E n, Work.Mostow.lev ξ u ≤ Real.exp tΓ →
          Submission.Mostow.hdist
            (Ψ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • u))
            (((f γ : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) • Ψ u) ≤ C) ∧
      (∃ C : ℝ, ∀ w : Submission.Mostow.E n, Work.Mostow.lev η w ≤ Real.exp tΛ →
        ∃ u : Submission.Mostow.E n, Work.Mostow.lev ξ u ≤ Real.exp tΓ ∧
          Submission.Mostow.hdist (Ψ u) w ≤ C) := by
  refine ⟨cuspPsi ψ ξ η, ?_, ?_, ?_⟩
  · -- (a) the cusp map is coarsely Lipschitz on the sublevel set
    obtain ⟨Lq, Cq, hLq1, hCq0, hfwd, _hbwd⟩ := hpsiQI
    set Ka : ℝ := Real.cosh 1
      + (Lq * Real.sqrt (2 * (Real.cosh 1 - 1)) + Cq * Real.exp tΓ) ^ 2 / 2 with hKa
    have hKa_ge : (1 : ℝ) ≤ Ka := by
      rw [hKa]
      have hc1 := Real.one_le_cosh 1
      have hsq : 0 ≤ (Lq * Real.sqrt (2 * (Real.cosh 1 - 1)) + Cq * Real.exp tΓ) ^ 2 / 2 :=
        div_nonneg (sq_nonneg _) (by norm_num)
      linarith
    refine ⟨Real.arcosh Ka, ?_, ?_⟩
    · exact Real.arcosh_nonneg hKa_ge
    · intro u v hu hv hd
      have hKey := levYcFormula hξ u v
      have hcosh1 : Real.cosh (hdist u v) ≤ Real.cosh 1 := by
        refine Real.cosh_le_cosh.mpr ?_
        rw [abs_of_nonneg (hI.nonneg u v), abs_one]
        exact hd
      have hlog1 : (1 : ℝ) ≤ Real.cosh (Real.log (lev ξ u / lev ξ v)) := Real.one_le_cosh _
      have hAZ : (lev ξ u * lev ξ v / 2) * ‖yc ξ u - yc ξ v‖ ^ 2 ≤ Real.cosh 1 - 1 := by
        linarith [hKey, hcosh1, hlog1]
      have hZ : lev ξ u * lev ξ v * ‖yc ξ u - yc ξ v‖ ^ 2 ≤ 2 * (Real.cosh 1 - 1) := by
        linarith [hAZ]
      have hA0 : 0 ≤ lev ξ u * lev ξ v :=
        mul_nonneg (le_of_lt (lev_pos ξ hξ u)) (le_of_lt (lev_pos ξ hξ v))
      have hM0 : 0 ≤ 2 * (Real.cosh 1 - 1) := by
        have h := Real.one_le_cosh 1
        linarith
      have hsA : Real.sqrt (lev ξ u * lev ξ v) * ‖yc ξ u - yc ξ v‖
          ≤ Real.sqrt (2 * (Real.cosh 1 - 1)) := by
        have hs : (Real.sqrt (lev ξ u * lev ξ v) * ‖yc ξ u - yc ξ v‖) ^ 2
            ≤ (Real.sqrt (2 * (Real.cosh 1 - 1))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hM0]
          exact hZ
        have hs' : Real.sqrt ((Real.sqrt (lev ξ u * lev ξ v) * ‖yc ξ u - yc ξ v‖) ^ 2)
            ≤ Real.sqrt ((Real.sqrt (2 * (Real.cosh 1 - 1))) ^ 2) := Real.sqrt_le_sqrt hs
        rwa [Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)),
          Real.sqrt_sq (Real.sqrt_nonneg _)] at hs'
      have hpsi_le : ‖ψ (yc ξ u) - ψ (yc ξ v)‖ ≤ Lq * ‖yc ξ u - yc ξ v‖ + Cq :=
        hfwd (yc ξ u) (yc ξ v) (yc_orth hξ) (yc_orth hξ)
      have hLq0 : 0 ≤ Lq := le_trans zero_le_one hLq1
      have hsAexp : Real.sqrt (lev ξ u * lev ξ v) ≤ Real.exp tΓ := by
        have hAexp : lev ξ u * lev ξ v ≤ Real.exp tΓ * Real.exp tΓ :=
          mul_le_mul hu hv (le_of_lt (lev_pos ξ hξ v)) (le_of_lt (Real.exp_pos tΓ))
        have h2 : Real.exp tΓ * Real.exp tΓ = Real.exp (2 * tΓ) := by
          rw [← Real.exp_add]; ring_nf
        rw [h2] at hAexp
        have h3 : Real.exp (2 * tΓ) = (Real.exp tΓ) ^ 2 := by
          rw [two_mul, Real.exp_add]; ring
        calc Real.sqrt (lev ξ u * lev ξ v) ≤ Real.sqrt (Real.exp (2 * tΓ)) :=
              Real.sqrt_le_sqrt hAexp
          _ = Real.exp tΓ := by
              rw [h3, Real.sqrt_sq (le_of_lt (Real.exp_pos tΓ))]
      have hprod : Real.sqrt (lev ξ u * lev ξ v) * ‖ψ (yc ξ u) - ψ (yc ξ v)‖
          ≤ Lq * Real.sqrt (2 * (Real.cosh 1 - 1)) + Cq * Real.exp tΓ := by
        have h1 : Real.sqrt (lev ξ u * lev ξ v) * ‖ψ (yc ξ u) - ψ (yc ξ v)‖
            ≤ Real.sqrt (lev ξ u * lev ξ v) * (Lq * ‖yc ξ u - yc ξ v‖ + Cq) :=
          mul_le_mul_of_nonneg_left hpsi_le (Real.sqrt_nonneg _)
        have h2 : Real.sqrt (lev ξ u * lev ξ v) * (Lq * ‖yc ξ u - yc ξ v‖ + Cq)
            = Lq * (Real.sqrt (lev ξ u * lev ξ v) * ‖yc ξ u - yc ξ v‖)
              + Cq * Real.sqrt (lev ξ u * lev ξ v) := by ring
        have h3 : Lq * (Real.sqrt (lev ξ u * lev ξ v) * ‖yc ξ u - yc ξ v‖)
            ≤ Lq * Real.sqrt (2 * (Real.cosh 1 - 1)) :=
          mul_le_mul_of_nonneg_left hsA hLq0
        have h4 : Cq * Real.sqrt (lev ξ u * lev ξ v) ≤ Cq * Real.exp tΓ :=
          mul_le_mul_of_nonneg_left hsAexp hCq0
        linarith [h1, h2, h3, h4]
      have hB : (lev ξ u * lev ξ v / 2) * ‖ψ (yc ξ u) - ψ (yc ξ v)‖ ^ 2
          ≤ (Lq * Real.sqrt (2 * (Real.cosh 1 - 1)) + Cq * Real.exp tΓ) ^ 2 / 2 := by
        have h1 : (lev ξ u * lev ξ v / 2) * ‖ψ (yc ξ u) - ψ (yc ξ v)‖ ^ 2
            = (Real.sqrt (lev ξ u * lev ξ v) * ‖ψ (yc ξ u) - ψ (yc ξ v)‖) ^ 2 / 2 := by
          rw [mul_pow, Real.sq_sqrt hA0]; ring
        rw [h1]
        have h2 := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hprod 2
        linarith
      have hlevu : lev η (cuspPsi ψ ξ η u) = lev ξ u :=
        (hptOfLevelYc η hη (hpsiperp (yc ξ u) (yc_orth hξ)) (lev_pos ξ hξ u)).1
      have hycu : yc η (cuspPsi ψ ξ η u) = ψ (yc ξ u) :=
        (hptOfLevelYc η hη (hpsiperp (yc ξ u) (yc_orth hξ)) (lev_pos ξ hξ u)).2.1
      have hlevv : lev η (cuspPsi ψ ξ η v) = lev ξ v :=
        (hptOfLevelYc η hη (hpsiperp (yc ξ v) (yc_orth hξ)) (lev_pos ξ hξ v)).1
      have hycv : yc η (cuspPsi ψ ξ η v) = ψ (yc ξ v) :=
        (hptOfLevelYc η hη (hpsiperp (yc ξ v) (yc_orth hξ)) (lev_pos ξ hξ v)).2.1
      have hK1 := levYcFormula hη (cuspPsi ψ ξ η u) (cuspPsi ψ ξ η v)
      rw [hlevu, hlevv, hycu, hycv] at hK1
      have hlogle : Real.cosh (Real.log (lev ξ u / lev ξ v)) ≤ Real.cosh 1 := by
        have h0 : 0 ≤ (lev ξ u * lev ξ v / 2) * ‖yc ξ u - yc ξ v‖ ^ 2 :=
          mul_nonneg (div_nonneg hA0 (by norm_num)) (sq_nonneg _)
        linarith [hKey, hcosh1, h0]
      have hmain : Real.cosh (hdist (cuspPsi ψ ξ η u) (cuspPsi ψ ξ η v)) ≤ Ka := by
        rw [hKa]
        exact hK1.le.trans (add_le_add hlogle hB)
      calc hdist (cuspPsi ψ ξ η u) (cuspPsi ψ ξ η v)
          = Real.arcosh (Real.cosh (hdist (cuspPsi ψ ξ η u) (cuspPsi ψ ξ η v))) :=
            (Real.arcosh_cosh (hI.nonneg _ _)).symm
        _ ≤ Real.arcosh Ka :=
            (Real.arcosh_le_arcosh (Real.cosh_pos _) (lt_of_lt_of_le zero_lt_one hKa_ge)).mpr hmain
  · -- (b) equivariance up to bounded error for the stabiliser of `ξ`
    intro γ hγ
    obtain ⟨Cψ, hCψ⟩ := hpsieq γ hγ
    refine ⟨Real.arcosh (1 + (Real.exp tΓ * Cψ) ^ 2 / 2), ?_⟩
    intro u hu
    have hγ0 : lev ξ (((γ : Γ) : PO n 1) • (0 : E n)) = 1 := hlevξ γ hγ
    have hm : bd (((f γ : Λ) : PO n 1)) η = η := hstab γ hγ
    have hm0 : lev η ((((f γ : Λ) : PO n 1)) • (0 : E n)) = 1 := hlevη (f γ) hm
    have hycu : inner ℝ (yc ξ u) ξ = 0 := yc_orth hξ
    have hu' : ((γ : Γ) : PO n 1) • u
        = hptOf ξ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u)) (lev ξ u) := by
      conv_lhs => rw [← hptOf_yc_lev hξ u]
      exact hptOf_smul_level hA hI hξ hγ hγ0 hycu (lev_pos ξ hξ u)
    have hlevγu : lev ξ (((γ : Γ) : PO n 1) • u) = lev ξ u := by
      rw [hu', (hptOfLevelYc ξ hξ (flatAct_mem hξ (((γ : Γ) : PO n 1)) (yc ξ u))
        (lev_pos ξ hξ u)).1]
    have hycγu : yc ξ (((γ : Γ) : PO n 1) • u)
        = flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u) := by
      rw [hu', (hptOfLevelYc ξ hξ (flatAct_mem hξ (((γ : Γ) : PO n 1)) (yc ξ u))
        (lev_pos ξ hξ u)).2.1]
    have hΨγu : cuspPsi ψ ξ η (((γ : Γ) : PO n 1) • u)
        = hptOf η (ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))) (lev ξ u) := by
      simp only [cuspPsi, hycγu, hlevγu]
    have hΨu : cuspPsi ψ ξ η u = hptOf η (ψ (yc ξ u)) (lev ξ u) := by simp only [cuspPsi]
    have hmΨ : (((f γ : Λ) : PO n 1)) • cuspPsi ψ ξ η u
        = hptOf η (flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))) (lev ξ u) := by
      rw [hΨu]
      exact hptOf_smul_level hA hI hη hm hm0 (hpsiperp (yc ξ u) hycu) (lev_pos ξ hξ u)
    have horth1 : inner ℝ (ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))) η = 0 :=
      hpsiperp _ (flatAct_mem hξ (((γ : Γ) : PO n 1)) (yc ξ u))
    have horth2 : inner ℝ (flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))) η = 0 :=
      flatAct_mem hη (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))
    have hb := hptOf_hdist η hη (lev ξ u) (lev_pos ξ hξ u)
      (ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u)))
      (flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))) horth1 horth2
    have hle : ‖ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))
        - flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))‖ ≤ Cψ := hCψ (yc ξ u) hycu
    have harg : 1 + (lev ξ u * ‖ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))
          - flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))‖) ^ 2 / 2
        ≤ 1 + (Real.exp tΓ * Cψ) ^ 2 / 2 := by
      have h1 : lev ξ u * ‖ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))
            - flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))‖ ≤ Real.exp tΓ * Cψ :=
        mul_le_mul hu hle (norm_nonneg _) (le_of_lt (Real.exp_pos tΓ))
      have h2 : 0 ≤ lev ξ u * ‖ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))
            - flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))‖ :=
        mul_nonneg (le_of_lt (lev_pos ξ hξ u)) (norm_nonneg _)
      have h3 := pow_le_pow_left₀ h2 h1 2
      linarith [h3]
    rw [hΨγu, hmΨ]
    calc hdist (hptOf η (ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))) (lev ξ u))
          (hptOf η (flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))) (lev ξ u))
        = Real.arcosh (1 + (lev ξ u * ‖ψ (flatAct ξ (((γ : Γ) : PO n 1)) (yc ξ u))
            - flatAct η (((f γ : Λ) : PO n 1)) (ψ (yc ξ u))‖) ^ 2 / 2) := hb
      _ ≤ Real.arcosh (1 + (Real.exp tΓ * Cψ) ^ 2 / 2) :=
          (Real.arcosh_le_arcosh (by positivity) (by positivity)).mpr harg
  · -- (c) coarse surjectivity onto the sublevel set of `η`
    obtain ⟨Cψ, hCψ⟩ := hpsisurj
    refine ⟨Real.arcosh (Real.cosh (|tΓ| + |tΛ|) + Real.exp (tΓ + tΛ) * Cψ ^ 2 / 2), ?_⟩
    intro w hw
    obtain ⟨y, hy, hyC⟩ := hCψ (yc η w) (yc_orth hη)
    set L' : ℝ := min (lev η w) (Real.exp tΓ) with hL'
    have hL'pos : 0 < L' := by
      rw [hL']
      exact lt_min (lev_pos η hη w) (Real.exp_pos tΓ)
    have hL'le : L' ≤ Real.exp tΓ := by
      rw [hL']; exact min_le_right _ _
    refine ⟨hptOf ξ y L', ?_, ?_⟩
    · rw [(hptOfLevelYc ξ hξ hy hL'pos).1]
      exact hL'le
    · have hψorth : inner ℝ (ψ y) η = 0 := hpsiperp y hy
      have hgen := hdist_hptOf_gen (ξ := η) hη hI (ψ y) (yc η w) L' (lev η w) hψorth (yc_orth hη)
        hL'pos (lev_pos η hη w)
      rw [hptOf_yc_lev hη w] at hgen
      have h1 : cuspPsi ψ ξ η (hptOf ξ y L') = hptOf η (ψ y) L' := by
        simp only [cuspPsi, (hptOfLevelYc ξ hξ hy hL'pos).1, (hptOfLevelYc ξ hξ hy hL'pos).2.1]
      rw [h1, hgen]
      have hLpos : 0 < lev η w := lev_pos η hη w
      have hlogb : |Real.log (L' / lev η w)| ≤ |tΓ| + |tΛ| := by
        rcases le_total (lev η w) (Real.exp tΓ) with hcase | hcase
        · have hLeq : L' = lev η w := by rw [hL']; exact min_eq_left hcase
          rw [hLeq, div_self (ne_of_gt hLpos), Real.log_one, abs_zero]
          linarith [abs_nonneg tΓ, abs_nonneg tΛ]
        · have hLeq : L' = Real.exp tΓ := by rw [hL']; exact min_eq_right hcase
          rw [hLeq, Real.log_div (ne_of_gt (Real.exp_pos tΓ)) (ne_of_gt hLpos), Real.log_exp]
          have h1' : tΓ ≤ Real.log (lev η w) := by
            rw [← Real.log_exp tΓ]
            exact Real.log_le_log (Real.exp_pos tΓ) hcase
          have h2' : Real.log (lev η w) ≤ tΛ := by
            rw [← Real.log_exp tΛ]
            exact Real.log_le_log hLpos hw
          have h3' : tΓ - Real.log (lev η w) ≤ 0 := by linarith
          rw [abs_of_nonpos h3']
          linarith [le_abs_self tΛ, neg_le_abs tΓ]
      have hcoshlog : Real.cosh (Real.log (L' / lev η w)) ≤ Real.cosh (|tΓ| + |tΛ|) := by
        refine Real.cosh_le_cosh.mpr ?_
        have h2 : |(|tΓ| + |tΛ|)| = |tΓ| + |tΛ| := abs_of_nonneg (by positivity)
        rw [h2]
        exact hlogb
      have hflat : (L' * lev η w / 2) * ‖ψ y - yc η w‖ ^ 2
          ≤ Real.exp (tΓ + tΛ) * Cψ ^ 2 / 2 := by
        have hL'L : L' * lev η w ≤ Real.exp tΓ * Real.exp tΛ :=
          mul_le_mul hL'le hw (le_of_lt hLpos) (le_of_lt (Real.exp_pos tΓ))
        have hψ2 : ‖ψ y - yc η w‖ ^ 2 ≤ Cψ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hyC 2
        have hb2 : 0 ≤ Real.exp tΓ * Real.exp tΛ / 2 :=
          div_nonneg (mul_nonneg (le_of_lt (Real.exp_pos tΓ)) (le_of_lt (Real.exp_pos tΛ)))
            (by norm_num)
        calc (L' * lev η w / 2) * ‖ψ y - yc η w‖ ^ 2
            ≤ (Real.exp tΓ * Real.exp tΛ / 2) * Cψ ^ 2 :=
              mul_le_mul (by linarith) hψ2 (sq_nonneg _)
                (div_nonneg (mul_nonneg (le_of_lt (Real.exp_pos tΓ)) (le_of_lt (Real.exp_pos tΛ)))
                  (by norm_num))
          _ = Real.exp (tΓ + tΛ) * Cψ ^ 2 / 2 := by rw [Real.exp_add]; ring
      refine (Real.arcosh_le_arcosh (by positivity) (by positivity)).mpr ?_
      linarith [hcoshlog, hflat]

end Work.Mostow
