import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.bogSumAux
import Submission.Work.BoseBogFS.latticeSumBounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bogS1_sum_le` — the region-A lattice sum of the clean row

`bogS1` is the gated region-A piece of `bogMaj`, the per-cell majorant of the clean Riemann row
(`FINDING_cleanFun_tsum_session20.md` §2): on the cells with `bogRHit ≤ bogC1` (the ball of
lattice radius `c₁/δ = (4πX)^{-1}`, `X = fsX v μ`)

    `bogMajA = bogOscM + (bogBs v R)² / (2 · bogRLot²)` ,

which is summable because `bogRLot = δ(‖n‖ − √3/2)` decays like `δ‖n‖` and the lattice sum of
`1/‖n‖²` over a ball of lattice radius `N` is `O(N)`.  The result is

    `Σ'ₙ bogS1 v h R ρ μ n ≤ 2000 · X^{-43/10}`

for `dil v μ ≤ ε₁`, with `ε₁` a fixed (but small) constant depending only on `v` and `R`.

The proof is: (i) the pointwise bound `bogS1 n ≤ A + C/(max ‖n‖ 1)²` on the ball of radius
`N = c₁/δ` (lemmas `bogS1_le_profile` and `bogS1_oscM_le`), (ii) the shell decomposition of the
lattice sum (`sum_le_profile` + `bogS1_shell_le`), giving
`Σ' ≤ 810·A₀·X^{-3} + K₂·X^{-4}` with `A₀ = √3π·bogKOs·(1+R)³/(a v)²` and
`K₂ = 2746·(bogBs v R)²/π²`, and (iii) the small-`X` absorption `bogS1_arith`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Work.UBB Work.BoseFixR Work.BoseBox

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The generic lattice/shell reduction -/

/-- A function of lattice points dominated by a decaying profile `g` of the lattice norm, cut off
at `‖n‖ ≤ N`, has its sum over any finite set bounded by the shell sum `∑ prof j · g j`. -/
lemma sum_le_profile {f : (Fin 3 → ℤ) → ℝ} {g : ℝ → ℝ} {N : ℝ}
    (hg0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ g r)
    (hdec : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → g b ≤ g a) (hN : 0 ≤ N)
    (hfg : ∀ n, f n ≤ if ‖lpt 1 n‖ ≤ N then g (‖lpt 1 n‖) else 0)
    (s : Finset (Fin 3 → ℤ)) :
    ∑ n ∈ s, f n ≤ ∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j * g (j : ℝ) := by
  calc ∑ n ∈ s, f n
      ≤ ∑ n ∈ s, (if ‖lpt 1 n‖ ≤ N then g (‖lpt 1 n‖) else 0) :=
        Finset.sum_le_sum (fun n _ => hfg n)
    _ = ∑ n ∈ s.filter (fun n => ‖lpt 1 n‖ ≤ N), g (‖lpt 1 n‖) := by
        rw [← Finset.sum_filter]
    _ ≤ ∑ n ∈ cube ⌈N⌉₊, g (‖lpt 1 n‖) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro n hn
          exact mem_cube.mpr (mn_le_ceil_of_norm_le (Finset.mem_filter.mp hn).2)
        · intro n _ _
          exact hg0 _ (norm_nonneg _)
    _ ≤ ∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j * g (j : ℝ) := sum_cube_le hg0 hdec _

/-! ## 2. The scaled mesh, and the small-`X` arithmetic -/

/-- `1/(bogMesh v ρ μ)² = X^{-3}·ρ/(4π²μ) ≤ (11/(40π²))·X^{-3}`. -/
lemma bogS1_mesh_inv_sq_le {v : E3 → ℝ} {R μ ρ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hC : Core v R μ ρ) :
    1 / (bogMesh v ρ μ) ^ 2
      ≤ (11 / (40 * Real.pi ^ 2)) * (fsX v μ) ^ (-(3 : ℝ)) := by
  have ha : 0 < _root_.BoseGases.a v := hav
  have hμ : 0 < μ := hC.hμ
  have hρ : 0 < ρ := hC.hρ0
  have hD0 : 0 < dil v μ := hC.hD0
  have hKl : 0 < (paramsAt μ (a v)).Kl := fsXp_pos hD0
  have hμa : 0 < μ * _root_.BoseGases.a v := mul_pos hμ ha
  have hρa : 0 < ρ * _root_.BoseGases.a v := mul_pos hρ ha
  have hfar : ((paramsAt μ (a v)).Kl) ^ 2 = (fsX v μ) ^ (-(3 : ℝ)) := by
    have h1 : ((paramsAt μ (a v)).Kl) ^ 2 = fsXp (dil v μ) (-(3 : ℝ)) := by
      show (fsXp (dil v μ) (-(3 / 2))) ^ 2 = _
      rw [fsXp_pow hD0.le]
      norm_num
    have h2 : (fsX v μ) ^ (-(3 : ℝ)) = fsXp (dil v μ) (-(3 : ℝ)) := by
      show (fsXp (dil v μ) 1) ^ (-(3 : ℝ)) = _
      rw [fsXp_rpow hD0.le]
      norm_num
    rw [h1, h2]
  have hell2 : (ell v μ) ^ 2 = ((paramsAt μ (a v)).Kl) ^ 2 * (μ * _root_.BoseGases.a v)⁻¹ := by
    rw [hC.hℓ, mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ))) 2,
        ← Real.rpow_mul hμa.le]
    rw [show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg_one]
  have hsq : (Real.sqrt (ρ * _root_.BoseGases.a v)) ^ 2 = ρ * _root_.BoseGases.a v :=
    Real.sq_sqrt hρa.le
  have hδ2 : (bogMesh v ρ μ) ^ 2
      = 4 * Real.pi ^ 2 * μ / (((paramsAt μ (a v)).Kl) ^ 2 * ρ) := by
    rw [bogMesh, div_pow, div_pow, hell2, hsq]
    field_simp
    norm_num
  have hδinv : 1 / (bogMesh v ρ μ) ^ 2
      = ((paramsAt μ (a v)).Kl) ^ 2 * (ρ / (4 * Real.pi ^ 2 * μ)) := by
    rw [hδ2]
    field_simp
  have hratio : ρ / (4 * Real.pi ^ 2 * μ) ≤ 11 / (40 * Real.pi ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hC.hρhi, Real.pi_pos]
  calc 1 / (bogMesh v ρ μ) ^ 2
      = ((paramsAt μ (a v)).Kl) ^ 2 * (ρ / (4 * Real.pi ^ 2 * μ)) := hδinv
    _ ≤ ((paramsAt μ (a v)).Kl) ^ 2 * (11 / (40 * Real.pi ^ 2)) :=
        mul_le_mul_of_nonneg_left hratio (sq_nonneg _)
    _ = (11 / (40 * Real.pi ^ 2)) * ((paramsAt μ (a v)).Kl) ^ 2 := by ring
    _ = (11 / (40 * Real.pi ^ 2)) * (fsX v μ) ^ (-(3 : ℝ)) := by rw [hfar]

/-- **The small-`X` absorption.**  For `A0, K2 ≥ 0` there is `x₀ ∈ (0,1]` such that for every
`0 < X ≤ x₀`, `810·A0·X^{-3} + K2·X^{-4} ≤ 2000·X^{-43/10}`. -/
theorem bogS1_arith (A0 K2 : ℝ) (hA0 : 0 ≤ A0) (hK2 : 0 ≤ K2) :
    ∃ x0 : ℝ, 0 < x0 ∧ x0 ≤ 1 ∧ ∀ X : ℝ, 0 < X → X ≤ x0 →
      810 * A0 * X ^ (-(3 : ℝ)) + K2 * X ^ (-(4 : ℝ))
        ≤ 2000 * X ^ (-(43 / 10 : ℝ)) := by
  set C : ℝ := 810 * A0 + K2 with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; nlinarith [hA0, hK2]
  have hC1pos : 0 < C + 1 := by linarith
  have hbase_pos : 0 < 2000 / (C + 1) := div_pos (by norm_num) hC1pos
  refine ⟨min 1 ((2000 / (C + 1)) ^ (10 / 3 : ℝ)),
    lt_min one_pos (Real.rpow_pos_of_pos hbase_pos _), min_le_left _ _, ?_⟩
  intro X hXpos hXle
  have hX1 : X ≤ 1 := le_trans hXle (min_le_left _ _)
  have hXto : X ≤ (2000 / (C + 1)) ^ (10 / 3 : ℝ) := le_trans hXle (min_le_right _ _)
  have h310 : X ^ (3 / 10 : ℝ) ≤ 2000 / (C + 1) := by
    have h1 : X ^ (3 / 10 : ℝ) ≤ ((2000 / (C + 1)) ^ (10 / 3 : ℝ)) ^ (3 / 10 : ℝ) :=
      Real.rpow_le_rpow hXpos.le hXto (by norm_num)
    have h2 : ((2000 / (C + 1)) ^ (10 / 3 : ℝ)) ^ (3 / 10 : ℝ) = 2000 / (C + 1) := by
      rw [← Real.rpow_mul hbase_pos.le, show (10 / 3 : ℝ) * (3 / 10 : ℝ) = 1 by norm_num,
        Real.rpow_one]
    linarith [h1, h2.le, h2.ge]
  have hmain : 810 * A0 * X ^ (13 / 10 : ℝ) + K2 * X ^ (3 / 10 : ℝ) ≤ 2000 := by
    have hmono : X ^ (13 / 10 : ℝ) ≤ X ^ (3 / 10 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hXpos hX1 (by norm_num)
    have step1 : 810 * A0 * X ^ (13 / 10 : ℝ) ≤ 810 * A0 * X ^ (3 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_left hmono (by nlinarith)
    have step2 : 810 * A0 * X ^ (3 / 10 : ℝ) + K2 * X ^ (3 / 10 : ℝ)
        = C * X ^ (3 / 10 : ℝ) := by
      rw [hCdef]; ring
    have step3 : C * X ^ (3 / 10 : ℝ) ≤ C * (2000 / (C + 1)) :=
      mul_le_mul_of_nonneg_left h310 hCnn
    have step4 : C * (2000 / (C + 1)) ≤ 2000 := by
      have h : C / (C + 1) ≤ 1 := by
        rw [div_le_one hC1pos]; linarith
      have he : C * (2000 / (C + 1)) = 2000 * (C / (C + 1)) := by ring
      rw [he]
      nlinarith [h]
    linarith [step1, step3, step4]
  have e1 : X ^ (43 / 10 : ℝ) * X ^ (-(3 : ℝ)) = X ^ (13 / 10 : ℝ) := by
    rw [← Real.rpow_add hXpos]; norm_num
  have e2 : X ^ (43 / 10 : ℝ) * X ^ (-(4 : ℝ)) = X ^ (3 / 10 : ℝ) := by
    rw [← Real.rpow_add hXpos]; norm_num
  have e3 : X ^ (43 / 10 : ℝ) * X ^ (-(43 / 10 : ℝ)) = 1 := by
    rw [← Real.rpow_add hXpos, show (43 / 10 : ℝ) + (-(43 / 10 : ℝ)) = 0 by norm_num,
      Real.rpow_zero]
  have hL : X ^ (43 / 10 : ℝ) * (810 * A0 * X ^ (-(3 : ℝ)) + K2 * X ^ (-(4 : ℝ)))
      = 810 * A0 * X ^ (13 / 10 : ℝ) + K2 * X ^ (3 / 10 : ℝ) := by
    rw [show X ^ (43 / 10 : ℝ) * (810 * A0 * X ^ (-(3 : ℝ)) + K2 * X ^ (-(4 : ℝ)))
        = 810 * A0 * (X ^ (43 / 10 : ℝ) * X ^ (-(3 : ℝ)))
          + K2 * (X ^ (43 / 10 : ℝ) * X ^ (-(4 : ℝ))) by ring]
    rw [e1, e2]
  have hR : X ^ (43 / 10 : ℝ) * (2000 * X ^ (-(43 / 10 : ℝ))) = 2000 := by
    rw [show X ^ (43 / 10 : ℝ) * (2000 * X ^ (-(43 / 10 : ℝ)))
        = 2000 * (X ^ (43 / 10 : ℝ) * X ^ (-(43 / 10 : ℝ))) by ring]
    rw [e3, mul_one]
  have h43 : 0 < X ^ (43 / 10 : ℝ) := Real.rpow_pos_of_pos hXpos _
  refine le_of_mul_le_mul_left ?_ h43
  rw [hL, hR]
  exact hmain

/-! ## 3. The profile bounds of `bogS1` -/

/-- `bogOscM v R ρ μ ≤ √3π·bogKOs·(1+R)³/(a v)²` under `Core` (and `dil v μ ≤ 1`). -/
lemma bogS1_oscM_le {v : E3 → ℝ} {R μ ρ : ℝ} (hav : 0 < a v) (_hR : 0 ≤ R)
    (hC : Core v R μ ρ) :
    bogOscM v R ρ μ ≤ Real.sqrt 3 * Real.pi * bogKOs * (1 + R) ^ 3 / (a v) ^ 2 := by
  have hμ : 0 < μ := hC.hμ
  have hρ : 0 < ρ := hC.hρ0
  have hP : 0 < ρ * a v := mul_pos hρ hav
  have hℓ : 0 < ell v μ := by
    rw [ell_eq_boxSide]
    exact mul_pos (by rw [paramsAt_Kl]; exact Real.rpow_pos_of_pos hC.hD0 _)
      (Real.rpow_pos_of_pos (mul_pos hμ hav) _)
  -- `a v ≤ ell v μ`
  have haℓ : a v ≤ ell v μ := by
    have h1 : (1 : ℝ) ≤ (dil v μ) ^ (-(3 / 646 : ℝ)) := by
      rw [Real.rpow_neg hC.hD0.le]
      exact (one_le_inv₀ (Real.rpow_pos_of_pos hC.hD0 _)).mpr
        (Real.rpow_le_one hC.hD0.le hC.hD1 (by norm_num))
    have h2 : a v ≤ (μ * a v) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, inv_eq_one_div]
      rw [le_div_iff₀ (Real.sqrt_pos.mpr (mul_pos hμ hav))]
      have hsq : (a v * Real.sqrt (μ * a v)) ^ 2 = dil v μ := by
        rw [mul_pow, Real.sq_sqrt (mul_pos hμ hav).le, dil]
        ring
      have h0 : 0 ≤ a v * Real.sqrt (μ * a v) := by positivity
      nlinarith [hsq, h0, hC.hD1]
    calc a v = 1 * a v := (one_mul _).symm
      _ ≤ (dil v μ) ^ (-(3 / 646 : ℝ)) * (μ * a v) ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul h1 h2 hav.le (le_of_lt (Real.rpow_pos_of_pos hC.hD0 _))
      _ = (paramsAt μ (a v)).Kl * (μ * a v) ^ (-(1 / 2 : ℝ)) := by rw [paramsAt_Kl]
      _ = ell v μ := (ell_eq_boxSide v μ).symm
  -- the `√(ρ/a)·bogHalf` bound
  have hstep : Real.sqrt (ρ / a v) * bogHalf v ρ μ ≤ Real.sqrt 3 * Real.pi / (a v) ^ 2 := by
    have hsqrt : Real.sqrt (ρ / a v) / Real.sqrt (ρ * a v) = 1 / a v := by
      have h2 : (Real.sqrt (ρ / a v) / Real.sqrt (ρ * a v)) ^ 2 = (1 / a v) ^ 2 := by
        rw [div_pow, div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ρ / a v),
          Real.sq_sqrt hP.le, one_pow]
        field_simp
      exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp h2
    have he : Real.sqrt (ρ / a v) * bogHalf v ρ μ
        = Real.sqrt 3 * Real.pi * (Real.sqrt (ρ / a v) / Real.sqrt (ρ * a v)) / ell v μ := by
      rw [bogHalf, bogMesh]
      field_simp
    rw [he, hsqrt]
    rw [show Real.sqrt 3 * Real.pi * (1 / a v) / ell v μ
        = Real.sqrt 3 * Real.pi / (a v * ell v μ) by field_simp]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith [haℓ, hav]
  have hK : 0 ≤ bogKOs * (1 + R) ^ 3 :=
    mul_nonneg bogKOs_nonneg (pow_nonneg (by linarith) 3)
  calc bogOscM v R ρ μ
      = (bogKOs * (1 + R) ^ 3) * (Real.sqrt (ρ / a v) * bogHalf v ρ μ) := by
        rw [bogOscM]; ring
    _ ≤ (bogKOs * (1 + R) ^ 3) * (Real.sqrt 3 * Real.pi / (a v) ^ 2) :=
        mul_le_mul_of_nonneg_left hstep hK
    _ = Real.sqrt 3 * Real.pi * bogKOs * (1 + R) ^ 3 / (a v) ^ 2 := by ring

/-- **The pointwise bound of `bogS1`.**  On the ball `‖n‖ ≤ c₁/δ` the gated region-A majorant is
bounded by `bogOscM + (128(bogBs)²/δ²)/(max ‖n‖ 1)²`, and it vanishes outside. -/
lemma bogS1_le_profile {v : E3 → ℝ} {h : ScatSol v} {R μ ρ : ℝ}
    (hR : 0 < R) (hav : 0 < a v) (hC : Core v R μ ρ) :
    ∀ n : Fin 3 → ℤ, bogS1 v h R ρ μ n ≤
      if ‖lpt 1 n‖ ≤ bogC1 v ρ μ / bogMesh v ρ μ then
        bogOscM v R ρ μ + ((128 * (bogBs v R) ^ 2) / (bogMesh v ρ μ) ^ 2)
          * (1 / (max ‖lpt 1 n‖ 1) ^ 2)
      else 0 := by
  have hμ : 0 < μ := hC.hμ
  have hρ : 0 < ρ := hC.hρ0
  have hℓ : 0 < ell v μ := by
    rw [ell_eq_boxSide]
    exact mul_pos (by rw [paramsAt_Kl]; exact Real.rpow_pos_of_pos hC.hD0 _)
      (Real.rpow_pos_of_pos (mul_pos hμ hav) _)
  have hδ : 0 < bogMesh v ρ μ := bogMesh_pos_of hρ hav hℓ
  have hOsc0 : 0 ≤ bogOscM v R ρ μ := bogOscM_nonneg hR.le hav hρ hδ
  have hBs : 0 ≤ (bogBs v R) ^ 2 := sq_nonneg _
  have hΔ : 0 ≤ bogHalf v ρ μ := (bogHalf_pos hδ).le
  have hcore : ∀ n : Fin 3 → ℤ,
      (bogBs v R) ^ 2 / (2 * (bogRLot v ρ μ n) ^ 2)
        ≤ ((128 * (bogBs v R) ^ 2) / (bogMesh v ρ μ) ^ 2)
          * (1 / (max ‖lpt 1 n‖ 1) ^ 2) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have h0rlo : bogRLot v ρ μ 0 = -bogHalf v ρ μ := by
        rw [bogRLot, norm_tSca, norm_lpt_eq (bogMesh v ρ μ) hδ.le 0, norm_lpt_zero]
        ring
      have h0m : max ‖lpt 1 (0 : Fin 3 → ℤ)‖ 1 = 1 := by
        rw [norm_lpt_zero, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      have hrlo2 : (bogRLot v ρ μ 0) ^ 2 = 3 * (bogMesh v ρ μ) ^ 2 / 4 := by
        rw [h0rlo, bogHalf,
          show (-(bogMesh v ρ μ * Real.sqrt 3 / 2)) ^ 2
              = (bogMesh v ρ μ) ^ 2 * (Real.sqrt 3) ^ 2 / 4 by ring,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        ring
      rw [hrlo2, h0m]
      simp only [one_pow, div_one, mul_one]
      have hδ2 : 0 < (bogMesh v ρ μ) ^ 2 := pow_pos hδ 2
      rw [div_le_div_iff₀ (by positivity) hδ2]
      nlinarith [hBs, hδ2]
    · have hm1 : 1 ≤ ‖lpt 1 n‖ := one_le_norm_lpt_one hn
      have hmpos : 0 < ‖lpt 1 n‖ := lt_of_lt_of_le one_pos hm1
      have hmax : max ‖lpt 1 n‖ 1 = ‖lpt 1 n‖ := max_eq_left hm1
      have hrlo : bogMesh v ρ μ * ‖lpt 1 n‖ / 16 ≤ bogRLot v ρ μ n := by
        rw [bogRLot, norm_tSca, norm_lpt_eq (bogMesh v ρ μ) hδ.le n, bogHalf]
        have hs3 : Real.sqrt 3 / 2 ≤ 15 / 16 := by
          have hs : Real.sqrt 3 ≤ 15 / 8 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
          linarith
        nlinarith [hδ, hm1, hs3]
      have hrlo0 : 0 < bogMesh v ρ μ * ‖lpt 1 n‖ / 16 := by positivity
      have hrlopos : 0 < bogRLot v ρ μ n := lt_of_lt_of_le hrlo0 hrlo
      have hsq' : (bogMesh v ρ μ) ^ 2 * ‖lpt 1 n‖ ^ 2 / 256 ≤ (bogRLot v ρ μ n) ^ 2 := by
        have hsq : (bogMesh v ρ μ * ‖lpt 1 n‖ / 16) ^ 2 ≤ (bogRLot v ρ μ n) ^ 2 :=
          pow_le_pow_left₀ hrlo0.le hrlo 2
        have he : (bogMesh v ρ μ * ‖lpt 1 n‖ / 16) ^ 2
            = (bogMesh v ρ μ) ^ 2 * ‖lpt 1 n‖ ^ 2 / 256 := by ring
        rwa [he] at hsq
      rw [hmax, div_mul_div_comm, mul_one]
      have hδ2 : 0 < (bogMesh v ρ μ) ^ 2 := pow_pos hδ 2
      have hm2 : 0 < ‖lpt 1 n‖ ^ 2 := pow_pos hmpos 2
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hsq', hBs, hδ2, hm2]
  intro n
  have hMA : 0 ≤ bogMajA v h R ρ μ n := by
    rw [bogMajA]
    have : 0 ≤ (bogBs v R) ^ 2 / (2 * (bogRLot v ρ μ n) ^ 2) := by positivity
    linarith
  have hRHS : 0 ≤ bogOscM v R ρ μ
      + ((128 * (bogBs v R) ^ 2) / (bogMesh v ρ μ) ^ 2) * (1 / (max ‖lpt 1 n‖ 1) ^ 2) := by
    have h1 : 0 ≤ ((128 * (bogBs v R) ^ 2) / (bogMesh v ρ μ) ^ 2)
        * (1 / (max ‖lpt 1 n‖ 1) ^ 2) := by positivity
    linarith
  by_cases hgate : bogRHit v ρ μ n ≤ bogC1 v ρ μ
  · have hnr : ‖lpt 1 n‖ ≤ bogC1 v ρ μ / bogMesh v ρ μ := by
      rw [le_div_iff₀ hδ]
      rw [bogRHit, norm_tSca, norm_lpt_eq (bogMesh v ρ μ) hδ.le n] at hgate
      linarith
    rw [bogS1, if_pos hgate, if_pos hnr, max_eq_right hMA, bogMajA]
    linarith [hcore n]
  · rw [bogS1, if_neg hgate]
    by_cases hc : ‖lpt 1 n‖ ≤ bogC1 v ρ μ / bogMesh v ρ μ
    · rw [if_pos hc]
      exact hRHS
    · rw [if_neg hc]

/-! ## 4. The shell sum -/

/-- The one-dimensional shell sum of the profile `A + C/(max j 1)²`. -/
lemma bogS1_shell_le {A A0 C K2 X N : ℝ}
    (hA0 : 0 ≤ A) (hAA0 : A ≤ A0) (hC0 : 0 ≤ C) (hX0 : 0 < X) (hX1 : X ≤ 1)
    (_hN0 : 0 ≤ N) (hNJ : (⌈N⌉₊ : ℝ) + 1 ≤ 3 * X ^ (-(1 : ℝ)))
    (hCK : C * (78 * X ^ (-(1 : ℝ))) ≤ K2 * X ^ (-(4 : ℝ))) :
    (∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j * (A + C * (1 / (max (j : ℝ) 1) ^ 2)))
      ≤ 810 * A0 * X ^ (-(3 : ℝ)) + K2 * X ^ (-(4 : ℝ)) := by
  have hcube : (X ^ (-(1 : ℝ))) ^ 3 = X ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_natCast (X ^ (-(1 : ℝ))) 3, ← Real.rpow_mul hX0.le]
    norm_num
  have h13 : ((⌈N⌉₊ : ℝ) + 1) ^ 3 ≤ 27 * X ^ (-(3 : ℝ)) := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (⌈N⌉₊ : ℝ) + 1) hNJ 3
    rwa [mul_pow, hcube, show (3 : ℝ) ^ 3 = 27 by norm_num] at h
  have hsum1 : (∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j) ≤ 810 * X ^ (-(3 : ℝ)) := by
    have h' : (∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j) ≤ 30 * ((⌈N⌉₊ : ℝ) + 1) ^ 3 :=
      latSumOneDCount_quad ⌈N⌉₊
    calc (∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j) ≤ 30 * ((⌈N⌉₊ : ℝ) + 1) ^ 3 := h'
      _ ≤ 30 * (27 * X ^ (-(3 : ℝ))) := mul_le_mul_of_nonneg_left h13 (by norm_num)
      _ = 810 * X ^ (-(3 : ℝ)) := by ring
  have hterm : ∀ j : ℕ, prof j * (1 / (max (j : ℝ) 1) ^ 2) ≤ 26 := by
    intro j
    rcases Nat.eq_zero_or_pos j with h0 | hp
    · subst h0
      have hm : max (((0 : ℕ)) : ℝ) 1 = 1 := by norm_num
      rw [hm, prof]
      norm_num
    · have hj : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hp
      have hm : max (j : ℝ) 1 = (j : ℝ) := max_eq_left hj
      have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
      rw [hm, prof, mul_one_div, div_le_iff₀ (pow_pos hjpos 2)]
      nlinarith
  have hsum2 : (∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j * (1 / (max (j : ℝ) 1) ^ 2))
      ≤ 78 * X ^ (-(1 : ℝ)) := by
    calc (∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j * (1 / (max (j : ℝ) 1) ^ 2))
        ≤ ∑ _j ∈ Finset.range (⌈N⌉₊ + 1), (26 : ℝ) := Finset.sum_le_sum (fun j _ => hterm j)
      _ = 26 * ((⌈N⌉₊ : ℝ) + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ 26 * (3 * X ^ (-(1 : ℝ))) := mul_le_mul_of_nonneg_left hNJ (by norm_num)
      _ = 78 * X ^ (-(1 : ℝ)) := by ring
  have hsplit : (∑ j ∈ Finset.range (⌈N⌉₊ + 1),
        prof j * (A + C * (1 / (max (j : ℝ) 1) ^ 2)))
      = A * (∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j)
        + C * (∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j * (1 / (max (j : ℝ) 1) ^ 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hsplit]
  have hs1 : 0 ≤ ∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j :=
    Finset.sum_nonneg (fun j _ => by simp only [prof]; positivity)
  have hb1 : A * (∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j) ≤ 810 * A0 * X ^ (-(3 : ℝ)) := by
    calc A * (∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j) ≤ A0 * (810 * X ^ (-(3 : ℝ))) :=
          mul_le_mul hAA0 hsum1 hs1 (le_trans hA0 hAA0)
      _ = 810 * A0 * X ^ (-(3 : ℝ)) := by ring
  have hb2 : C * (∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j * (1 / (max (j : ℝ) 1) ^ 2))
      ≤ K2 * X ^ (-(4 : ℝ)) :=
    calc C * (∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j * (1 / (max (j : ℝ) 1) ^ 2))
        ≤ C * (78 * X ^ (-(1 : ℝ))) := mul_le_mul_of_nonneg_left hsum2 hC0
      _ ≤ K2 * X ^ (-(4 : ℝ)) := hCK
  linarith

/-! ## 5. The theorem -/

theorem bogS1_sum_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) (hv : ∀ x, 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ {ρ μ : ℝ}, Work.BoseBogFS.Core v R μ ρ →
      Work.BoseFixR.dil v μ ≤ ε₁ →
      R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 →
      Summable (fun n : Fin 3 → ℤ => Work.BoseBogFS.bogS1 v h R ρ μ n) ∧
      (∑' n : Fin 3 → ℤ, Work.BoseBogFS.bogS1 v h R ρ μ n)
        ≤ 2000 * (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ) := by
  have hA0nn : (0 : ℝ) ≤ Real.sqrt 3 * Real.pi * bogKOs * (1 + R) ^ 3 / (a v) ^ 2 := by
    have h1 : 0 ≤ bogKOs := bogKOs_nonneg
    have h2 : 0 ≤ (1 + R) ^ 3 := pow_nonneg (by linarith) 3
    positivity
  have hK2nn : (0 : ℝ) ≤ 2746 * (bogBs v R) ^ 2 / Real.pi ^ 2 := by positivity
  obtain ⟨x₀, hx₀0, hx₀1, hx₀⟩ :=
    bogS1_arith (Real.sqrt 3 * Real.pi * bogKOs * (1 + R) ^ 3 / (a v) ^ 2)
      (2746 * (bogBs v R) ^ 2 / Real.pi ^ 2) hA0nn hK2nn
  refine ⟨x₀ ^ (323 : ℝ), Real.rpow_pos_of_pos hx₀0 323, ?_⟩
  intro ρ μ hC hdil hRℓ
  have hμ : 0 < μ := hC.hμ
  have hρ : 0 < ρ := hC.hρ0
  have hℓ : 0 < ell v μ := by
    rw [ell_eq_boxSide]
    exact mul_pos (by rw [paramsAt_Kl]; exact Real.rpow_pos_of_pos hC.hD0 _)
      (Real.rpow_pos_of_pos (mul_pos hμ hav) _)
  set X : ℝ := fsX v μ with hXdef
  have hX0 : 0 < X := by
    rw [hXdef, Work.BoseFixR.fsX, Work.BoseBox.fsXp]
    exact Real.rpow_pos_of_pos hC.hD0 _
  have hXle1 : X ≤ 1 := by
    rw [hXdef, Work.BoseFixR.fsX, Work.BoseBox.fsXp]
    calc (dil v μ) ^ ((1 : ℝ) / 323) ≤ (1 : ℝ) ^ ((1 : ℝ) / 323) :=
          Real.rpow_le_rpow hC.hD0.le hC.hD1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hXx₀ : X ≤ x₀ := by
    rw [hXdef, Work.BoseFixR.fsX, Work.BoseBox.fsXp]
    calc (dil v μ) ^ ((1 : ℝ) / 323) ≤ (x₀ ^ (323 : ℝ)) ^ ((1 : ℝ) / 323) :=
          Real.rpow_le_rpow hC.hD0.le hdil (by norm_num)
      _ = x₀ := by
          have h : (x₀ ^ (323 : ℝ)) ^ ((1 : ℝ) / 323)
              = x₀ ^ ((323 : ℝ) * ((1 : ℝ) / 323)) :=
            (Real.rpow_mul hx₀0.le 323 ((1 : ℝ) / 323)).symm
          rw [h, show (323 : ℝ) * ((1 : ℝ) / 323) = 1 by norm_num, Real.rpow_one]
  set A : ℝ := bogOscM v R ρ μ with hAdef
  set Bsq : ℝ := (bogBs v R) ^ 2 with hBsqdef
  set N : ℝ := bogC1 v ρ μ / bogMesh v ρ μ with hNdef
  set C : ℝ := 128 * Bsq / (bogMesh v ρ μ) ^ 2 with hCdef
  set K2 : ℝ := 2746 * Bsq / Real.pi ^ 2 with hK2def
  set A0 : ℝ := Real.sqrt 3 * Real.pi * bogKOs * (1 + R) ^ 3 / (a v) ^ 2 with hA0def
  set g : ℝ → ℝ := fun r => A + C * (1 / (max r 1) ^ 2) with hgdef
  have hδ0 : 0 < bogMesh v ρ μ := bogMesh_pos_of hρ hav hℓ
  have hA0' : 0 ≤ A := by
    rw [hAdef]
    exact bogOscM_nonneg hR.le hav hρ hδ0
  have hBsq0 : 0 ≤ Bsq := by rw [hBsqdef]; positivity
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hN0 : 0 ≤ N := by
    rw [hNdef]
    have hc1 : 0 < bogC1 v ρ μ := by
      rw [bogC1]
      have hs0 : 0 < (paramsAt μ (a v)).s := by
        rw [paramsAt_s]; exact Real.rpow_pos_of_pos hC.hD0 _
      positivity
    exact div_nonneg hc1.le hδ0.le
  have hpoint : ∀ n : Fin 3 → ℤ,
      bogS1 v h R ρ μ n ≤ if ‖lpt 1 n‖ ≤ N then g (‖lpt 1 n‖) else 0 := by
    intro n
    have h := bogS1_le_profile (h := h) hR hav hC n
    simpa only [hNdef, hgdef, hAdef, hCdef, hBsqdef] using h
  have hg0' : ∀ r : ℝ, 0 ≤ g r := by
    intro r
    rw [hgdef]
    have h1 : 0 ≤ 1 / (max r 1) ^ 2 := by positivity
    nlinarith [hA0', mul_nonneg hC0 h1]
  have hg0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ g r := fun r _ => hg0' r
  have hdec : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → g b ≤ g a := by
    intro a b ha hab
    rw [hgdef]
    have hm : max a 1 ≤ max b 1 := max_le_max hab le_rfl
    have h1 : (0 : ℝ) < max a 1 := lt_of_lt_of_le one_pos (le_max_right a 1)
    have h2 : 1 / (max b 1) ^ 2 ≤ 1 / (max a 1) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ h1.le hm 2)
    have h3 : C * (1 / (max b 1) ^ 2) ≤ C * (1 / (max a 1) ^ 2) :=
      mul_le_mul_of_nonneg_left h2 hC0
    linarith
  have hNval : N = (4 * Real.pi * X) ^ (-(1 : ℝ)) := by
    have hs : (paramsAt μ (a v)).s = X := by rw [hXdef]; exact paramsAt_s v μ
    have hspos : 0 < (paramsAt μ (a v)).s := by rw [hs]; exact hX0
    rw [hNdef, bogC1_div_mesh hρ hav hℓ hspos, hs, Real.rpow_neg_one]
  have hNle : N ≤ X ^ (-(1 : ℝ)) := by
    rw [hNval, Real.rpow_neg_one, mul_inv, Real.rpow_neg_one]
    have h1 : (4 * Real.pi)⁻¹ ≤ 1 := by
      rw [inv_eq_one_div, div_le_one (by positivity)]
      linarith [Real.pi_gt_three]
    have h2 : (0 : ℝ) ≤ X⁻¹ := inv_nonneg.mpr hX0.le
    have h3 : (4 * Real.pi)⁻¹ * X⁻¹ ≤ 1 * X⁻¹ := mul_le_mul_of_nonneg_right h1 h2
    simpa using h3
  have hNJ : (⌈N⌉₊ : ℝ) + 1 ≤ 3 * X ^ (-(1 : ℝ)) := by
    have hc := Nat.ceil_lt_add_one hN0
    have h1 : (1 : ℝ) ≤ X ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one]
      exact (one_le_inv₀ hX0).mpr hXle1
    linarith
  have hCK : C * (78 * X ^ (-(1 : ℝ))) ≤ K2 * X ^ (-(4 : ℝ)) := by
    have hinv := bogS1_mesh_inv_sq_le (v := v) (R := R) (μ := μ) (ρ := ρ) hav hC
    have hX4 : X ^ (-(3 : ℝ)) * X ^ (-(1 : ℝ)) = X ^ (-(4 : ℝ)) := by
      rw [← Real.rpow_add hX0]
      norm_num
    have hcoef : (128 : ℝ) * Bsq * (11 / (40 * Real.pi ^ 2)) * 78
        ≤ 2746 * Bsq / Real.pi ^ 2 := by
      have h1 : (128 : ℝ) * 11 * 78 / 40 ≤ 2746 := by norm_num
      calc (128 : ℝ) * Bsq * (11 / (40 * Real.pi ^ 2)) * 78
          = (128 * 11 * 78 / 40) * (Bsq / Real.pi ^ 2) := by ring
        _ ≤ 2746 * (Bsq / Real.pi ^ 2) := by
            apply mul_le_mul_of_nonneg_right h1
            exact div_nonneg hBsq0 (by positivity)
        _ = 2746 * Bsq / Real.pi ^ 2 := by ring
    calc C * (78 * X ^ (-(1 : ℝ)))
        = (128 * Bsq * (1 / (bogMesh v ρ μ) ^ 2)) * (78 * X ^ (-(1 : ℝ))) := by
          rw [hCdef]; ring
      _ ≤ (128 * Bsq * ((11 / (40 * Real.pi ^ 2)) * X ^ (-(3 : ℝ))))
            * (78 * X ^ (-(1 : ℝ))) := by
          gcongr
      _ = (128 * Bsq * (11 / (40 * Real.pi ^ 2)) * 78)
            * (X ^ (-(3 : ℝ)) * X ^ (-(1 : ℝ))) := by ring
      _ = (128 * Bsq * (11 / (40 * Real.pi ^ 2)) * 78) * X ^ (-(4 : ℝ)) := by rw [hX4]
      _ ≤ (2746 * Bsq / Real.pi ^ 2) * X ^ (-(4 : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hX0.le _)
      _ = K2 * X ^ (-(4 : ℝ)) := by rw [hK2def]
  have hpart : ∀ s : Finset (Fin 3 → ℤ),
      ∑ n ∈ s, bogS1 v h R ρ μ n ≤ 810 * A0 * X ^ (-(3 : ℝ)) + K2 * X ^ (-(4 : ℝ)) := by
    intro s
    have h1 := sum_le_profile hg0 hdec hN0 hpoint s
    have h2 : (∑ j ∈ Finset.range (⌈N⌉₊ + 1), prof j * g (j : ℝ))
        ≤ 810 * A0 * X ^ (-(3 : ℝ)) + K2 * X ^ (-(4 : ℝ)) := by
      have hAA0 : A ≤ A0 := by
        rw [hAdef, hA0def]
        exact bogS1_oscM_le hav hR.le hC
      simpa only [hgdef] using
        (bogS1_shell_le (A := A) (A0 := A0) (C := C) (K2 := K2) (X := X) (N := N)
          hA0' hAA0 hC0 hX0 hXle1 hN0 hNJ hCK)
    linarith
  refine ⟨?_, ?_⟩
  · exact summable_of_sum_le (fun n => bogS1_nonneg v h R ρ μ n) hpart
  · refine le_trans (Real.tsum_le_of_sum_le (fun n => bogS1_nonneg v h R ρ μ n) hpart) ?_
    have hx := hx₀ X hX0 hXx₀
    simpa only [← hXdef, hA0def, hK2def] using hx

end Work.BoseBogFS
