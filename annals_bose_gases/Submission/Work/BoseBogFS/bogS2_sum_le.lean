import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.bogS2_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bogS2_sum_le` — the region-B lattice sum of the clean row

This is the second of the three regional sum bounds of
`Work.BoseBogFS.cleanFun_tsum_le_integral` (see
`Submission/Work/BoseBogFS/FINDING_cleanFun_tsum_session21.md`): the gated region-B majorant
`bogS2 v h R ρ μ` (`= max 0 (bogMajB …)` on the cells with `r_hi ≤ 16√Vs`) is summable with
`∑' bogS2 ≤ 2000·X^{-43/10}`, `X = fsX v μ`, on the diluteness window `dil v μ ≤ ε₂`.

## The proof

* **The gate confines the sum to a cube.**  `r_hi ≤ 16√Vs ≤ 16√C` (`C = bogS2Cst`), and
  `r_hi = δ(‖n‖+√3/2)`, so the summand is supported in `cube ⌈16√C/δ⌉`; hence `bogS2` is
  finitely supported (`Summable`), and it suffices to bound the sum over that cube.
* **The pointwise majorant** (`bogS2Maj`): the six rows of `bogMajB` are bounded by
  `4Δ·16√C + 9c₁²`, `√(2A1)(√3δ(m+1)+C)`, `2CX³`, `2√C X^{3/2}√3δ(m+1)`,
  `512C²X³/(δ²(m+1)²)` and `1024ΔC²/(δ³(m+1)³)`; the key inputs are the sharp two-kink
  oscillation bound `tauScRad_sub_le`, `bogOm ≤ 2·bogOscM`, and the two inverse-radius
  estimates `bogS2_inv_rlo_sq_le`, `bogS2_inv_rlo_sq_sub_le`.
* **The shell sums** (`cubeMomSums`) plus the parameter identities `δ = 2πX^{3/2}√(μ/ρ)`,
  `c₁ = ½X^{1/2}√(μ/ρ)`, `Δ = 2π√3Xc₁` convert everything into `bogS2KB v R · X^{-4}`.
* **The threshold** `X^{3/10}·bogS2KB v R ≤ 2000` turns that into `2000·X^{-43/10}`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Work.UBB Work.BoseFixR Work.BoseBox

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The diluteness threshold of the region-B sum. -/
def bogS2Thr (v : E3 → ℝ) (R : ℝ) : ℝ :=
min (1 / 10 ^ 12)
    (min (1 / 50)
      (min ((2000 / bogS2KB v R) ^ ((10 : ℝ) / 3))
        (min ((a v / (2 * Real.pi * Real.sqrt 3)) ^ ((1 : ℝ) / 163))
          ((1 / (50 * Real.sqrt (bogS2Cst v R))) ^ ((2 : ℝ) / 11)))))

lemma bogS2Thr_le_twelve {v : E3 → ℝ} {R : ℝ} : bogS2Thr v R ≤ 1 / 10 ^ 12 := by
  change min (1 / 10 ^ 12)
    (min (1 / 50)
      (min ((2000 / bogS2KB v R) ^ ((10 : ℝ) / 3))
        (min ((a v / (2 * Real.pi * Real.sqrt 3)) ^ ((1 : ℝ) / 163))
          ((1 / (50 * Real.sqrt (bogS2Cst v R))) ^ ((2 : ℝ) / 11))))) ≤ 1 / 10 ^ 12
  exact min_le_left _ _

lemma bogS2Thr_le_fifty {v : E3 → ℝ} {R : ℝ} : bogS2Thr v R ≤ 1 / 50 := by
  change min (1 / 10 ^ 12)
    (min (1 / 50)
      (min ((2000 / bogS2KB v R) ^ ((10 : ℝ) / 3))
        (min ((a v / (2 * Real.pi * Real.sqrt 3)) ^ ((1 : ℝ) / 163))
          ((1 / (50 * Real.sqrt (bogS2Cst v R))) ^ ((2 : ℝ) / 11))))) ≤ 1 / 50
  exact le_trans (min_le_right _ _) (min_le_left _ _)

lemma bogS2Thr_le_KB {v : E3 → ℝ} {R : ℝ} :
    bogS2Thr v R ≤ (2000 / bogS2KB v R) ^ ((10 : ℝ) / 3) := by
  change min (1 / 10 ^ 12)
    (min (1 / 50)
      (min ((2000 / bogS2KB v R) ^ ((10 : ℝ) / 3))
        (min ((a v / (2 * Real.pi * Real.sqrt 3)) ^ ((1 : ℝ) / 163))
          ((1 / (50 * Real.sqrt (bogS2Cst v R))) ^ ((2 : ℝ) / 11))))) ≤ (2000 / bogS2KB v R) ^ ((10 : ℝ) / 3)
  exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))

lemma bogS2Thr_le_ell {v : E3 → ℝ} {R : ℝ} :
    bogS2Thr v R ≤ (a v / (2 * Real.pi * Real.sqrt 3)) ^ ((1 : ℝ) / 163) := by
  change min (1 / 10 ^ 12)
    (min (1 / 50)
      (min ((2000 / bogS2KB v R) ^ ((10 : ℝ) / 3))
        (min ((a v / (2 * Real.pi * Real.sqrt 3)) ^ ((1 : ℝ) / 163))
          ((1 / (50 * Real.sqrt (bogS2Cst v R))) ^ ((2 : ℝ) / 11))))) ≤ (a v / (2 * Real.pi * Real.sqrt 3)) ^ ((1 : ℝ) / 163)
  exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _)))

lemma bogS2Thr_le_c2 {v : E3 → ℝ} {R : ℝ} :
    bogS2Thr v R ≤ (1 / (50 * Real.sqrt (bogS2Cst v R))) ^ ((2 : ℝ) / 11) := by
  change min (1 / 10 ^ 12)
    (min (1 / 50)
      (min ((2000 / bogS2KB v R) ^ ((10 : ℝ) / 3))
        (min ((a v / (2 * Real.pi * Real.sqrt 3)) ^ ((1 : ℝ) / 163))
          ((1 / (50 * Real.sqrt (bogS2Cst v R))) ^ ((2 : ℝ) / 11))))) ≤ (1 / (50 * Real.sqrt (bogS2Cst v R))) ^ ((2 : ℝ) / 11)
  exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _)))

lemma bogS2Thr_pos {v : E3 → ℝ} {R : ℝ} (hR : 0 < R) (hav : 0 < a v) :
    0 < bogS2Thr v R := by
  have hC : 0 < bogS2Cst v R := bogS2Cst_pos hR hav
  have hK : 0 < bogS2KB v R := bogS2KB_pos hR hav
  have h1 : 0 < (2000 / bogS2KB v R) ^ ((10 : ℝ) / 3) :=
    Real.rpow_pos_of_pos (div_pos (by norm_num) hK) _
  have h2 : 0 < (a v / (2 * Real.pi * Real.sqrt 3)) ^ ((1 : ℝ) / 163) :=
    Real.rpow_pos_of_pos (by positivity) _
  have h4 : 0 < (1 / (50 * Real.sqrt (bogS2Cst v R))) ^ ((2 : ℝ) / 11) :=
    Real.rpow_pos_of_pos (by positivity) _
  change 0 < min (1 / 10 ^ 12)
    (min (1 / 50)
      (min ((2000 / bogS2KB v R) ^ ((10 : ℝ) / 3))
        (min ((a v / (2 * Real.pi * Real.sqrt 3)) ^ ((1 : ℝ) / 163))
          ((1 / (50 * Real.sqrt (bogS2Cst v R))) ^ ((2 : ℝ) / 11)))))
  exact lt_min (by norm_num) (lt_min (by norm_num) (lt_min h1 (lt_min h2 h4)))

/-- The main bound: summability and the `2000·X^{-43/10}` estimate at the threshold. -/
theorem bogS2_tsum_le {v : E3 → ℝ} {h : ScatSol v} {R : ℝ}
    (hR : 0 < R) (hav : 0 < a v) (hv : ∀ x, 0 ≤ v x) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    {ρ μ : ℝ} (hC : Core v R μ ρ) (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0)
    (hX : fsX v μ ≤ bogS2Thr v R) :
    Summable (bogS2 v h R ρ μ) ∧
      (∑' n : Fin 3 → ℤ, bogS2 v h R ρ μ n)
        ≤ 2000 * (fsX v μ) ^ (-(43 / 10 : ℝ)) := by
  set C := bogS2Cst v R with hCdef
  set X := fsX v μ with hXdef
  have hC1 : 1 ≤ C := one_le_bogS2Cst hR hav
  have hX0 : 0 < X := bogS2_fsX_pos hC hav
  have hXnn : 0 ≤ X := hX0.le
  have hδ : 0 < bogMesh v ρ μ := bogMesh_pos_of hC.hρ0 hav (sb_ell_pos hav hC)
  -- the threshold rows
  have hX12 : X ≤ 1 / 10 ^ 12 := le_trans hX (bogS2Thr_le_twelve (v := v) (R := R))
  have hX50 : X ≤ 1 / 50 := le_trans hX (bogS2Thr_le_fifty (v := v) (R := R))
  have hXKB : X ≤ (2000 / bogS2KB v R) ^ ((10 : ℝ) / 3) :=
    le_trans hX (bogS2Thr_le_KB (v := v) (R := R))
  have hXell : X ≤ (a v / (2 * Real.pi * Real.sqrt 3)) ^ ((1 : ℝ) / 163) :=
    le_trans hX (bogS2Thr_le_ell (v := v) (R := R))
  have hXc2 : X ≤ (1 / (50 * Real.sqrt C)) ^ ((2 : ℝ) / 11) := by
    rw [hCdef]
    exact le_trans hX (bogS2Thr_le_c2 (v := v) (R := R))
  have hell : 2 * Real.pi * Real.sqrt 3 ≤ ell v μ := bogS2_ell_ge hC hav hXell
  -- the oscillation rows
  have hBnn : (0 : ℝ) ≤ bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3
      / (a v) ^ 2 := by
    refine div_nonneg ?_ (sq_nonneg _)
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg bogKOs_nonneg
      (pow_nonneg (by positivity) 3)) (Real.sqrt_nonneg _)) Real.pi_pos.le) (Real.sqrt_nonneg _)
  have hOsc2 : bogOscM v R ρ μ
      ≤ 2 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3
        / (a v) ^ 2) :=
    bogS2_oscM_le_eleven (v := v) (R := R) (μ := μ) (ρ := ρ) hav hR.le hC
  have hOsc1 : bogOscM v R ρ μ ≤ C * (fsX v μ) ^ (3 : ℝ) := by
    have h1 := bogS2_oscM_le (v := v) (R := R) (μ := μ) (ρ := ρ) hC hav hR hX50
    have h2 : 2 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3
        / (a v) ^ 2) ≤ C := by
      rw [hCdef, bogS2Cst]
      have hKnn : (0 : ℝ) ≤ bogKB * (1 + R) ^ 3 / a v :=
        div_nonneg (mul_nonneg bogKB_nonneg (pow_nonneg (by positivity) 3)) hav.le
      linarith [hBnn, hKnn]
    have h3 : 0 ≤ X ^ (3 : ℝ) := Real.rpow_nonneg hXnn _
    calc bogOscM v R ρ μ
        ≤ 2 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3
            / (a v) ^ 2) * (fsX v μ) ^ (3 : ℝ) := h1
      _ ≤ C * (fsX v μ) ^ (3 : ℝ) := mul_le_mul_of_nonneg_right h2 h3
  -- the `Vs` row
  have hVs : bogVs v R ρ μ ≤ C := by
    rw [bogVs, hCdef, bogS2Cst]
    have h1 : bogBs v R ≤ 1 + bogKB * (1 + R) ^ 3 / a v := by
      rw [bogBs]
      have h2 : (0 : ℝ) ≤ bogKB * (1 + R) ^ 3 / a v :=
        div_nonneg (mul_nonneg bogKB_nonneg (pow_nonneg (by positivity) 3)) hav.le
      exact max_le (by linarith) (by linarith)
    have h5 : max 0 (bogOscM v R ρ μ)
        ≤ 16 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3
          / (a v) ^ 2) := by
      have h6 : max 0 (bogOscM v R ρ μ)
          ≤ 2 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3
            / (a v) ^ 2) := max_le (by linarith [hBnn]) hOsc2
      have h7 : 2 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3
            / (a v) ^ 2)
          ≤ 16 * (bogKOs * (1 + R) ^ 3 * Real.sqrt (11 / 10) * Real.pi * Real.sqrt 3
            / (a v) ^ 2) := by
        have h8 := mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 16) hBnn
        exact h8
      linarith [h6, h7]
    linarith [h1, h5]
  -- the `c₂` row
  have hc2big : bogS2RB v R ≤ bogC2 v ρ μ := by
    have h1 : (X ^ (-(11 / 2 : ℝ))) / 3 ≤ bogC2 v ρ μ := by
      have h := bogS2_c2_ge (v := v) (R := R) (ρ := ρ) (μ := μ) hC hav
      rw [← hXdef] at h
      exact h
    have h50 : (0 : ℝ) ≤ 50 * Real.sqrt C :=
      mul_nonneg (by norm_num) (Real.sqrt_nonneg C)
    have h2 : (1 / (50 * Real.sqrt C)) ^ ((2 : ℝ) / 11)
        = (50 * Real.sqrt C) ^ (-((2 : ℝ) / 11)) := by
      rw [one_div, Real.inv_rpow h50, ← Real.rpow_neg h50]
    rw [h2] at hXc2
    have h3 : X ^ ((11 : ℝ) / 2) ≤ 1 / (50 * Real.sqrt C) := by
      have h4 := Real.rpow_le_rpow hXnn hXc2 (by norm_num : (0 : ℝ) ≤ 11 / 2)
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 50 * Real.sqrt C),
        show (-((2 : ℝ) / 11)) * (11 / 2) = -1 by norm_num, Real.rpow_neg_one,
        ← one_div] at h4
      exact h4
    have h5 : X ^ (-(11 / 2 : ℝ)) = (X ^ ((11 : ℝ) / 2))⁻¹ := Real.rpow_neg hXnn _
    have h6 : (50 * Real.sqrt C) ≤ X ^ (-(11 / 2 : ℝ)) := by
      have h7 : X ^ ((11 : ℝ) / 2) * (50 * Real.sqrt C) ≤ 1 := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 50 * Real.sqrt C)] at h3
        exact h3
      have h8 : (50 * Real.sqrt C) ≤ 1 / X ^ ((11 : ℝ) / 2) := by
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hX0 _),
          show (50 * Real.sqrt C) * X ^ ((11 : ℝ) / 2)
            = X ^ ((11 : ℝ) / 2) * (50 * Real.sqrt C) by ring]
        exact h7
      rw [one_div, ← h5] at h8
      exact h8
    have h9 : 16 * Real.sqrt C ≤ X ^ (-(11 / 2 : ℝ)) / 3 := by
      have h10 : (16 / 50 : ℝ) * (50 * Real.sqrt C)
          ≤ (16 / 50 : ℝ) * X ^ (-(11 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h6 (by norm_num)
      have h11 : (16 / 50 : ℝ) * (50 * Real.sqrt C) = 16 * Real.sqrt C := by ring
      have h12 : (16 / 50 : ℝ) * X ^ (-(11 / 2 : ℝ)) ≤ X ^ (-(11 / 2 : ℝ)) / 3 := by
        calc (16 / 50 : ℝ) * X ^ (-(11 / 2 : ℝ))
            ≤ (1 / 3 : ℝ) * X ^ (-(11 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hXnn _)
          _ = X ^ (-(11 / 2 : ℝ)) / 3 := by ring
      exact le_trans h11.ge (le_trans h10 h12)
    rw [bogS2RB, ← hCdef]
    linarith [h1, h9]
  -- the cube
  set J : ℕ := ⌈bogBigThr v R ρ μ / bogMesh v ρ μ⌉₊ with hJdef
  have hδ1 : bogMesh v ρ μ ≤ 1 := bogS2_mesh_le_one hC hav hX12
  have hJ : (J : ℝ) + 1 ≤ (16 * Real.sqrt C + 2) / bogMesh v ρ μ := by
    have hb0 : (0 : ℝ) ≤ bogBigThr v R ρ μ := by
      rw [bogBigThr]; positivity
    have hce2 : (J : ℝ) < bogBigThr v R ρ μ / bogMesh v ρ μ + 1 :=
      Nat.ceil_lt_add_one (div_nonneg hb0 hδ.le)
    have h2 : bogBigThr v R ρ μ ≤ 16 * Real.sqrt C := by
      rw [bogBigThr]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by rw [hCdef]; exact hVs))
        (by norm_num)
    have h3 : bogBigThr v R ρ μ / bogMesh v ρ μ ≤ 16 * Real.sqrt C / bogMesh v ρ μ :=
      div_le_div_of_nonneg_right h2 hδ.le
    have h4 : (2 : ℝ) ≤ 2 / bogMesh v ρ μ := by
      rw [le_div_iff₀ hδ]; linarith [hδ1]
    have h5 : 16 * Real.sqrt C / bogMesh v ρ μ + 2 / bogMesh v ρ μ
        = (16 * Real.sqrt C + 2) / bogMesh v ρ μ := by ring
    linarith [hce2, h3, h4, h5.le, h5.ge]
  -- the pointwise bound and the support
  have hmaj : ∀ n : Fin 3 → ℤ, bogS2 v h R ρ μ n ≤ bogS2Maj v R ρ μ n := fun n =>
    bogS2_le_maj (n := n) hR hav hC hX50 hX12 hOsc1 hVs hc2big hell
      (bogS2_vmaxt_le (n := n) hR hav hv hvrad hv_supp hC hRℓ hVs hOsc2 hell)
  have hzero : ∀ n ∉ cube J, bogS2Maj v R ρ μ n = 0 := by
    intro n hn
    rw [bogS2Maj]
    by_cases hgate : bogRHit v ρ μ n ≤ bogBigThr v R ρ μ
    · rw [if_pos hgate]
      exfalso
      apply hn
      rw [mem_cube]
      have h1 : bogRHit v ρ μ n = bogMesh v ρ μ * (‖lpt (1 : ℝ) n‖ + Real.sqrt 3 / 2) :=
        bogRHit_eq v ρ μ n hδ.le
      rw [h1] at hgate
      have h2 : bogMesh v ρ μ * ‖lpt (1 : ℝ) n‖ ≤ bogBigThr v R ρ μ := by
        have h3 : (0 : ℝ) ≤ bogMesh v ρ μ * (Real.sqrt 3 / 2) := by positivity
        linarith [hgate]
      have h3 : ‖lpt (1 : ℝ) n‖ ≤ bogBigThr v R ρ μ / bogMesh v ρ μ := by
        rw [le_div_iff₀ hδ]; linarith [h2]
      have h4 : (mn n : ℝ) ≤ ‖lpt (1 : ℝ) n‖ := mn_cast_le_norm n
      have h5 : (mn n : ℝ) ≤ (J : ℝ) := le_trans h4 (le_trans h3 (Nat.le_ceil _))
      exact_mod_cast h5
    · rw [if_neg hgate]
  -- partial sums
  have hstep : ∀ s : Finset (Fin 3 → ℤ),
      ∑ n ∈ s, bogS2 v h R ρ μ n ≤ ∑ n ∈ cube J, bogS2MajE v R ρ μ n := by
    intro s
    have h1 : ∑ n ∈ s, bogS2 v h R ρ μ n ≤ ∑ n ∈ s, bogS2Maj v R ρ μ n :=
      Finset.sum_le_sum fun n _ => hmaj n
    have h2 : ∑ n ∈ s ∩ cube J, bogS2Maj v R ρ μ n = ∑ n ∈ s, bogS2Maj v R ρ μ n :=
      Finset.sum_subset Finset.inter_subset_left (fun n hn hn2 => hzero n (by
        intro hc
        exact hn2 (Finset.mem_inter.mpr ⟨hn, hc⟩)))
    have h3 : ∑ n ∈ s ∩ cube J, bogS2Maj v R ρ μ n ≤ ∑ n ∈ cube J, bogS2MajE v R ρ μ n :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun n _ _ => bogS2Maj_nonneg (v := v) (R := R) (ρ := ρ) (μ := μ) hR hav hC.hρ0
          hC.hμ (sb_ell_pos hav hC)))
        (Finset.sum_le_sum fun n _ => bogS2Maj_le_majE (v := v) (R := R) (ρ := ρ) (μ := μ)
          hR hav hC.hρ0 hC.hμ (sb_ell_pos hav hC))
    exact le_trans h1 (le_trans h2.ge h3)
  have hsum : ∑ n ∈ cube J, bogS2MajE v R ρ μ n ≤ bogS2KB v R * X ^ (-(4 : ℝ)) := by
    rw [hXdef]
    exact bogS2_cube_sum_le (h := h) (J := J) hR hav hC hX50 hJ
  have hsumm : Summable (bogS2 v h R ρ μ) :=
    summable_of_ne_finset_zero (s := cube J) (fun n hn =>
      le_antisymm (le_trans (hmaj n) (le_of_eq (hzero n hn)))
        (bogS2_nonneg v h R ρ μ n))
  have htsum : (∑' n : Fin 3 → ℤ, bogS2 v h R ρ μ n) ≤ bogS2KB v R * X ^ (-(4 : ℝ)) :=
    le_trans (Real.tsum_le_of_sum_le (fun n => bogS2_nonneg v h R ρ μ n) hstep) hsum
  -- the final comparison
  have hKB0 : 0 < bogS2KB v R := bogS2KB_pos hR hav
  have hXKB' : X ^ ((3 : ℝ) / 10) ≤ 2000 / bogS2KB v R := by
    have h := Real.rpow_le_rpow hXnn hXKB (by norm_num : (0 : ℝ) ≤ 3 / 10)
    rw [← Real.rpow_mul (div_nonneg (by norm_num) hKB0.le),
      show ((10 : ℝ) / 3) * (3 / 10) = 1 by norm_num, Real.rpow_one] at h
    exact h
  refine ⟨hsumm, ?_⟩
  calc (∑' n : Fin 3 → ℤ, bogS2 v h R ρ μ n)
      ≤ bogS2KB v R * X ^ (-(4 : ℝ)) := htsum
    _ = bogS2KB v R * X ^ ((3 : ℝ) / 10) * X ^ (-(43 / 10 : ℝ)) := by
        rw [show (-(4 : ℝ)) = (3 : ℝ) / 10 + (-(43 / 10 : ℝ)) by norm_num,
          Real.rpow_add hX0]
        ring
    _ ≤ bogS2KB v R * (2000 / bogS2KB v R) * X ^ (-(43 / 10 : ℝ)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXKB' hKB0.le)
          (Real.rpow_nonneg hXnn _)
    _ = 2000 * X ^ (-(43 / 10 : ℝ)) := by
        field_simp

theorem bogS2_sum_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) (hv : ∀ x, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ {ρ μ : ℝ}, Work.BoseBogFS.Core v R μ ρ →
      Work.BoseFixR.dil v μ ≤ ε₂ →
      R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 →
      Summable (fun n : Fin 3 → ℤ => Work.BoseBogFS.bogS2 v h R ρ μ n) ∧
      (∑' n : Fin 3 → ℤ, Work.BoseBogFS.bogS2 v h R ρ μ n)
        ≤ 2000 * (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ) := by
  refine ⟨(Work.BoseBogFS.bogS2Thr v R) ^ 323,
    pow_pos (Work.BoseBogFS.bogS2Thr_pos hR hav) 323, ?_⟩
  intro ρ μ hC hdil hRℓ
  have hX : Work.BoseFixR.fsX v μ ≤ Work.BoseBogFS.bogS2Thr v R := by
    rw [Work.BoseBogFS.bogS2_fsX_rpow]
    calc (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 323)
        ≤ ((Work.BoseBogFS.bogS2Thr v R) ^ 323) ^ ((1 : ℝ) / 323) :=
          Real.rpow_le_rpow hC.hD0.le hdil (by norm_num)
      _ = Work.BoseBogFS.bogS2Thr v R := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul
            (le_of_lt (Work.BoseBogFS.bogS2Thr_pos hR hav))]
          norm_num
  exact Work.BoseBogFS.bogS2_tsum_le hR hav hv hvrad hv_supp hC hRℓ hX

end Work.BoseBogFS
