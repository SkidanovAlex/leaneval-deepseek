import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB1S.chiSmallB_eq_zero_of_volume_dlBox_eq_zero
import Submission.Work.BoseFixB1S.corrPlanchMarg
import Submission.Work.BoseFixB1S.fsXpLogSmall
import Submission.Work.BoseFixB1S.kineticCruxParsed
import Submission.Work.BoseFixB1S.weightedPlancherelKinFT
import Submission.Work.BoseFixB1S.win.chiSmallB_kinFT_decay
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
import Submission.Work.LocRepoint.chiSmallB_sq_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S.CubeWindow

open Work.BoseBox

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Auxiliary bookkeeping for `cubeArithN`

The target `cubeArithN` is a pure-real asymptotic statement about FS's parameters
at diluteness `t = μa³`: `s = t^{1/323}`, `d = t^{6/323}`, `ℓ = sideAt μ a =
a·t^{-163/323}`, `L = 1 + (ℓd)⁻¹ + |log d|`.  It is proved here by

* **exact power cancellation** (`cubeArith_prodRed`, `cubeArith_sqrtRed`): after
  multiplying by `ℓ²`, `(ℓd)·((ℓd)³)⁻¹·s^{2N-5} = (ℓ⁻¹)²·s^{2N-17}` and the
  square root reduces to `ℓ⁻²·2√(Ceγζ(2π)³L³s^{2N-31})` (uses `d = s⁶`), and
* **the logarithmic/counting estimate** (`cubeArith_asymProd`, `cubeArith_asymSqrt`):
  `L³ ≤ 8(1+|log t|)³` once `(ℓd)⁻¹ ≤ 1`, and `s^{2N-17} ≤ fsXp t 17`,
  `s^{2N-31} ≤ fsXp t 3` — a positive power of `t` beats any power of `log`.
-/

/-- **Smallness of `K · t^{c/323} · (1+|log t|)^M`**: a positive power of `t`
beats every power of `|log t|`, uniformly in the prefactor `K`
(cf. `Work.BoseFixB1S.fsXp_mul_log_le_one`). -/
lemma cubeFsXp_mul_log_le_one {K c M : ℝ} (hK : 0 < K) (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      K * fsXp t c * (1 + |Real.log t|) ^ M ≤ 1 := by
  obtain ⟨ε, hε, h⟩ := Work.BoseFixB1S.fsXpLogSmall (c := c) (M := M) (K := K⁻¹)
    (inv_pos.mpr hK) hc hM
  refine ⟨ε, hε, fun t ht htle => ?_⟩
  have h1 := h t ht htle
  have h2 : K * (fsXp t c * (1 + |Real.log t|) ^ M) ≤ K * K⁻¹ :=
    mul_le_mul_of_nonneg_left h1 hK.le
  rw [mul_inv_cancel₀ hK.ne'] at h2
  calc K * fsXp t c * (1 + |Real.log t|) ^ M
      = K * (fsXp t c * (1 + |Real.log t|) ^ M) := by ring
    _ ≤ 1 := h2

/-- The localisation quantity `L = 1 + (ℓd)⁻¹ + |log d|` is at most
`2(1 + |log (μa³)|)` as soon as `(ℓd)⁻¹ = a⁻¹(μa³)^{157/323} ≤ 1`. -/
lemma cubeArith_L_le_two {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a)
    (hu : a⁻¹ * fsXp (μ * a ^ 3) 157 ≤ 1) :
    1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|
      ≤ 2 * (1 + |Real.log (μ * a ^ 3)|) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  have hmul : sideAt μ a * (paramsAt μ a).d = a * fsXp (μ * a ^ 3) (-157) := by
    rw [mul_comm (sideAt μ a), Work.BoseFixB1.d_mul_sideAt_eq ha hμ]
  have hinv : (sideAt μ a * (paramsAt μ a).d)⁻¹ = a⁻¹ * fsXp (μ * a ^ 3) 157 := by
    rw [hmul, mul_inv, fsXp_inv ht]
    norm_num
  have hlog : |Real.log ((paramsAt μ a).d)| ≤ |Real.log (μ * a ^ 3)| := by
    have hd : (paramsAt μ a).d = fsXp (μ * a ^ 3) 6 := rfl
    rw [hd, fsXp, Real.log_rpow ht, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 323)]
    nlinarith [abs_nonneg (Real.log (μ * a ^ 3))]
  rw [hinv]
  have := abs_nonneg (Real.log (μ * a ^ 3))
  linarith

/-- **The product term, exact cancellation**: with `d = s⁶` the product
`(ℓd)·((ℓd)³)⁻¹·s^{2N-5}` equals `(ℓ⁻¹)²·s^{2N-17}`. -/
lemma cubeArith_prodRed {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (N : ℕ) (hN : 17 ≤ N)
    (Cq γ : ℝ) :
    Cq * (sideAt μ a * (paramsAt μ a).d) * (paramsAt μ a).s ^ (2 * N - 5) * γ
        * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|) ^ 3
        * ((sideAt μ a * (paramsAt μ a).d) ^ 3)⁻¹
      = (sideAt μ a)⁻¹ ^ 2
        * (Cq * γ * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹
            + |Real.log ((paramsAt μ a).d)|) ^ 3 * (paramsAt μ a).s ^ (2 * N - 17)) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  set Z : ℝ := fsXp (μ * a ^ 3) (-157) with hZ
  set W : ℝ := fsXp (μ * a ^ 3) (-163) with hW
  set V : ℝ := fsXp (μ * a ^ 3) 1 with hV
  set L : ℝ := 1 + (sideAt μ a * (paramsAt μ a).d)⁻¹
    + |Real.log ((paramsAt μ a).d)| with hL
  have hZy : sideAt μ a * (paramsAt μ a).d = a * Z := by
    rw [mul_comm (sideAt μ a), Work.BoseFixB1.d_mul_sideAt_eq ha hμ, hZ]
  have hWy : sideAt μ a = a * W := by
    rw [Work.BoseFixB1.sideAt_eq_fsXp ha hμ, hW]
  have hVy : (paramsAt μ a).s = V := by
    rw [hV]
    rfl
  have hZinv : (a * Z)⁻¹ = a⁻¹ * fsXp (μ * a ^ 3) 157 := by
    rw [mul_inv, hZ, fsXp_inv ht]
    norm_num
  have hWinv : (a * W)⁻¹ = a⁻¹ * fsXp (μ * a ^ 3) 163 := by
    rw [mul_inv, hW, fsXp_inv ht]
    norm_num
  have hZne : a * Z ≠ 0 := by
    refine mul_ne_zero ha.ne' ?_
    rw [hZ]
    exact (fsXp_pos ht).ne'
  have hkey : a * Z * ((a * Z) ^ 3)⁻¹ = (a * Z)⁻¹ ^ 2 := by
    rw [inv_pow]
    field_simp
  have hsqZ : (a * Z)⁻¹ ^ 2 = a⁻¹ ^ 2 * fsXp (μ * a ^ 3) 314 := by
    rw [hZinv, mul_pow, fsXp_pow ht.le]
    norm_num
  have hsqW : (a * W)⁻¹ ^ 2 = a⁻¹ ^ 2 * fsXp (μ * a ^ 3) 326 := by
    rw [hWinv, mul_pow, fsXp_pow ht.le]
    norm_num
  have hV5 : V ^ (2 * N - 5) = fsXp (μ * a ^ 3) (((2 * N - 5 : ℕ)) : ℝ) := by
    rw [hV, fsXp_pow ht.le]
    norm_num
  have hV17 : V ^ (2 * N - 17) = fsXp (μ * a ^ 3) (((2 * N - 17 : ℕ)) : ℝ) := by
    rw [hV, fsXp_pow ht.le]
    norm_num
  have hcast : (((2 * N - 5 : ℕ)) : ℝ) = (((2 * N - 17 : ℕ)) : ℝ) + 12 := by
    rw [Nat.cast_sub (by omega : 5 ≤ 2 * N), Nat.cast_sub (by omega : 17 ≤ 2 * N)]
    push_cast
    ring
  have hfs : fsXp (μ * a ^ 3) 314 * fsXp (μ * a ^ 3) (((2 * N - 5 : ℕ)) : ℝ)
      = fsXp (μ * a ^ 3) 326 * fsXp (μ * a ^ 3) (((2 * N - 17 : ℕ)) : ℝ) := by
    rw [fsXp_mul ht, fsXp_mul ht]
    congr 1
    linarith [hcast]
  rw [hZy, hWy, hVy]
  calc Cq * (a * Z) * V ^ (2 * N - 5) * γ * L ^ 3 * ((a * Z) ^ 3)⁻¹
      = Cq * γ * L ^ 3 * ((a * Z) * ((a * Z) ^ 3)⁻¹) * V ^ (2 * N - 5) := by ring
    _ = Cq * γ * L ^ 3 * (a * Z)⁻¹ ^ 2 * V ^ (2 * N - 5) := by rw [hkey]
    _ = Cq * γ * L ^ 3 * (a⁻¹ ^ 2 * fsXp (μ * a ^ 3) 314) * V ^ (2 * N - 5) := by
          rw [hsqZ]
    _ = Cq * γ * L ^ 3 * a⁻¹ ^ 2 * (fsXp (μ * a ^ 3) 314
          * fsXp (μ * a ^ 3) (((2 * N - 5 : ℕ)) : ℝ)) := by rw [hV5]; ring
    _ = Cq * γ * L ^ 3 * a⁻¹ ^ 2 * (fsXp (μ * a ^ 3) 326
          * fsXp (μ * a ^ 3) (((2 * N - 17 : ℕ)) : ℝ)) := by rw [hfs]
    _ = Cq * γ * L ^ 3 * (a⁻¹ ^ 2 * fsXp (μ * a ^ 3) 326) * V ^ (2 * N - 17) := by
          rw [hV17]; ring
    _ = (a * W)⁻¹ ^ 2 * (Cq * γ * L ^ 3 * V ^ (2 * N - 17)) := by rw [hsqW]; ring

/-- **The square-root term, exact cancellation**: with `d = s⁶` the two square
roots differ by the exact factor `ℓ⁻²`. -/
lemma cubeArith_sqrtRed {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (N : ℕ) (hN : 17 ≤ N)
    (Ce γ ζ : ℝ) (hCe : 0 ≤ Ce) (hγ : 0 ≤ γ) (hζ : 0 ≤ ζ) :
    2 * Real.sqrt (Ce * (sideAt μ a * (paramsAt μ a).d)⁻¹ * (paramsAt μ a).s ^ (2 * N - 7)
          * γ * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|) ^ 3
          * ((sideAt μ a * (paramsAt μ a).d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * ζ)
      ≤ (sideAt μ a)⁻¹ ^ 2
        * (2 * Real.sqrt (Ce * γ * ζ * (2 * Real.pi) ^ 3
            * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|) ^ 3
            * (paramsAt μ a).s ^ (2 * N - 31))) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  set Z : ℝ := fsXp (μ * a ^ 3) (-157) with hZ
  set W : ℝ := fsXp (μ * a ^ 3) (-163) with hW
  set V : ℝ := fsXp (μ * a ^ 3) 1 with hV
  set L : ℝ := 1 + (sideAt μ a * (paramsAt μ a).d)⁻¹
    + |Real.log ((paramsAt μ a).d)| with hL
  have hZy : sideAt μ a * (paramsAt μ a).d = a * Z := by
    rw [mul_comm (sideAt μ a), Work.BoseFixB1.d_mul_sideAt_eq ha hμ, hZ]
  have hWy : sideAt μ a = a * W := by
    rw [Work.BoseFixB1.sideAt_eq_fsXp ha hμ, hW]
  have hVy : (paramsAt μ a).s = V := by
    rw [hV]
    rfl
  have hZinv : (a * Z)⁻¹ = a⁻¹ * fsXp (μ * a ^ 3) 157 := by
    rw [mul_inv, hZ, fsXp_inv ht]
    norm_num
  have hWinv : (a * W)⁻¹ = a⁻¹ * fsXp (μ * a ^ 3) 163 := by
    rw [mul_inv, hW, fsXp_inv ht]
    norm_num
  have hinv4Z : (a * Z)⁻¹ * ((a * Z) ^ 3)⁻¹ = (a * Z)⁻¹ ^ 4 := by
    rw [inv_pow]; ring
  have hZ4 : (a * Z)⁻¹ ^ 4 = a⁻¹ ^ 4 * fsXp (μ * a ^ 3) 628 := by
    rw [show (a * Z)⁻¹ ^ 4 = ((a * Z)⁻¹) ^ 4 from rfl, hZinv, mul_pow, fsXp_pow ht.le]
    norm_num
  have hW4 : (a * W)⁻¹ ^ 4 = a⁻¹ ^ 4 * fsXp (μ * a ^ 3) 652 := by
    rw [show (a * W)⁻¹ ^ 4 = ((a * W)⁻¹) ^ 4 from rfl, hWinv, mul_pow, fsXp_pow ht.le]
    norm_num
  have hsq4W : ((a * W)⁻¹ ^ 2) ^ 2 = a⁻¹ ^ 4 * fsXp (μ * a ^ 3) 652 := by
    rw [show ((a * W)⁻¹ ^ 2) ^ 2 = (a * W)⁻¹ ^ 4 by ring, hW4]
  have hV7 : V ^ (2 * N - 7) = fsXp (μ * a ^ 3) (((2 * N - 7 : ℕ)) : ℝ) := by
    rw [hV, fsXp_pow ht.le]
    norm_num
  have hV31 : V ^ (2 * N - 31) = fsXp (μ * a ^ 3) (((2 * N - 31 : ℕ)) : ℝ) := by
    rw [hV, fsXp_pow ht.le]
    norm_num
  have hcast : (((2 * N - 7 : ℕ)) : ℝ) = (((2 * N - 31 : ℕ)) : ℝ) + 24 := by
    rw [Nat.cast_sub (by omega : 7 ≤ 2 * N), Nat.cast_sub (by omega : 31 ≤ 2 * N)]
    push_cast
    ring
  have hfs : fsXp (μ * a ^ 3) 628 * fsXp (μ * a ^ 3) (((2 * N - 7 : ℕ)) : ℝ)
      = fsXp (μ * a ^ 3) 652 * fsXp (μ * a ^ 3) (((2 * N - 31 : ℕ)) : ℝ) := by
    rw [fsXp_mul ht, fsXp_mul ht]
    congr 1
    linarith [hcast]
  have harg : Ce * (a * Z)⁻¹ * V ^ (2 * N - 7) * γ * L ^ 3 * ((a * Z) ^ 3)⁻¹
        * (2 * Real.pi) ^ 3 * ζ
      = ((a * W)⁻¹ ^ 2) ^ 2
        * (Ce * γ * ζ * (2 * Real.pi) ^ 3 * L ^ 3 * V ^ (2 * N - 31)) := by
    calc Ce * (a * Z)⁻¹ * V ^ (2 * N - 7) * γ * L ^ 3 * ((a * Z) ^ 3)⁻¹
            * (2 * Real.pi) ^ 3 * ζ
        = Ce * γ * ζ * (2 * Real.pi) ^ 3 * L ^ 3
            * ((a * Z)⁻¹ * ((a * Z) ^ 3)⁻¹) * V ^ (2 * N - 7) := by ring
      _ = Ce * γ * ζ * (2 * Real.pi) ^ 3 * L ^ 3
            * (a⁻¹ ^ 4 * fsXp (μ * a ^ 3) 628) * V ^ (2 * N - 7) := by rw [hinv4Z, hZ4]
      _ = Ce * γ * ζ * (2 * Real.pi) ^ 3 * L ^ 3
            * (a⁻¹ ^ 4 * (fsXp (μ * a ^ 3) 628
              * fsXp (μ * a ^ 3) (((2 * N - 7 : ℕ)) : ℝ))) := by rw [hV7]; ring
      _ = Ce * γ * ζ * (2 * Real.pi) ^ 3 * L ^ 3
            * (a⁻¹ ^ 4 * (fsXp (μ * a ^ 3) 652
              * fsXp (μ * a ^ 3) (((2 * N - 31 : ℕ)) : ℝ))) := by rw [hfs]
      _ = ((a * W)⁻¹ ^ 2) ^ 2
            * (Ce * γ * ζ * (2 * Real.pi) ^ 3 * L ^ 3 * V ^ (2 * N - 31)) := by
          rw [hsq4W, hV31]; ring
  rw [hZy, hWy, hVy]
  rw [harg]
  have hs : Real.sqrt (((a * W)⁻¹ ^ 2) ^ 2
        * (Ce * γ * ζ * (2 * Real.pi) ^ 3 * L ^ 3 * V ^ (2 * N - 31)))
      = (a * W)⁻¹ ^ 2 * Real.sqrt (Ce * γ * ζ * (2 * Real.pi) ^ 3 * L ^ 3 * V ^ (2 * N - 31)) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((a * W)⁻¹ ^ 2) ^ 2),
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (a * W)⁻¹ ^ 2)]
  rw [hs]
  exact le_of_eq (by ring)

/-- **The product half of the reduced asymptotic**: `(2π)⁻³CqγL³s^{2N-17} ≤ 1/128`
for small diluteness. -/
lemma cubeArith_asymProd {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 17 ≤ N) (Cq γ : ℝ)
    (hCq : 0 ≤ Cq) (hγ : 0 ≤ γ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * a ^ 3 ≤ ε₀ →
      ((2 * Real.pi) ^ 3)⁻¹ * (Cq * γ
          * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|) ^ 3
          * (paramsAt μ a).s ^ (2 * N - 17)) ≤ 1 / 128 := by
  have hpair : 0 ≤ Cq * γ := mul_nonneg hCq hγ
  set KA : ℝ := 128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (Cq * γ)) + 1 with hKA
  have hKApos : 0 < KA := by
    rw [hKA]
    have hp : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
    have hX : 0 ≤ 128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (Cq * γ)) := by positivity
    linarith
  obtain ⟨δ, hδpos, hδ⟩ :=
    cubeFsXp_mul_log_le_one (K := KA) (c := 17) (M := 3) hKApos (by norm_num) (by norm_num)
  refine ⟨min 1 (min (a ^ (323 / 157 : ℝ)) δ),
    lt_min one_pos (lt_min (Real.rpow_pos_of_pos ha _) hδpos), ?_⟩
  intro μ hμ hμle
  set t : ℝ := μ * a ^ 3 with ht_def
  have ht : 0 < t := by rw [ht_def]; positivity
  have hspos : 0 < (paramsAt μ a).s := fsXp_pos ht
  have ht1 : t ≤ 1 := hμle.trans (min_le_left _ _)
  have htm : t ≤ min (a ^ (323 / 157 : ℝ)) δ := hμle.trans (min_le_right _ _)
  have hta : t ≤ a ^ (323 / 157 : ℝ) := htm.trans (min_le_left _ _)
  have htδ : t ≤ δ := htm.trans (min_le_right _ _)
  have hu : a⁻¹ * fsXp t 157 ≤ 1 := by
    have h1 : fsXp t 157 ≤ a := by
      have h2 := Real.rpow_le_rpow ht.le hta (by norm_num : (0 : ℝ) ≤ (157 : ℝ) / 323)
      have h3 : (a ^ (323 / 157 : ℝ)) ^ ((157 : ℝ) / 323) = a := by
        rw [← Real.rpow_mul ha.le]; norm_num
      rw [h3] at h2
      simpa [fsXp] using h2
    calc a⁻¹ * fsXp t 157 ≤ a⁻¹ * a := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by rw [inv_mul_cancel₀ ha.ne']
  have hLb : 1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|
      ≤ 2 * (1 + |Real.log t|) := by
    have h := cubeArith_L_le_two hμ ha hu
    simpa only [ht_def] using h
  have hLnn : 0 ≤ 1 + (sideAt μ a * (paramsAt μ a).d)⁻¹
      + |Real.log ((paramsAt μ a).d)| := by
    have hℓ : 0 < sideAt μ a := by
      rw [Work.BoseFixB1.sideAt_eq_fsXp ha hμ]; exact mul_pos ha (fsXp_pos ht)
    have hd : 0 < (paramsAt μ a).d := fsXp_pos ht
    have hinv : 0 < (sideAt μ a * (paramsAt μ a).d)⁻¹ := inv_pos.mpr (mul_pos hℓ hd)
    have := abs_nonneg (Real.log ((paramsAt μ a).d)); linarith
  have hL3 : (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|) ^ 3
      ≤ 8 * (1 + |Real.log t|) ^ 3 := by
    calc (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|) ^ 3
        ≤ (2 * (1 + |Real.log t|)) ^ 3 := pow_le_pow_left₀ hLnn hLb 3
      _ = 8 * (1 + |Real.log t|) ^ 3 := by ring
  have hs17 : (paramsAt μ a).s ^ (2 * N - 17) ≤ fsXp t 17 := by
    have hs : (paramsAt μ a).s = fsXp t 1 := by rw [ht_def]; rfl
    rw [hs, fsXp_pow ht.le]
    refine fsXp_le_fsXp ht ht1 ?_
    have hNR : (17 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [Nat.cast_sub (by omega : 17 ≤ 2 * N)]
    push_cast
    linarith
  have hmono : Cq * γ * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹
        + |Real.log ((paramsAt μ a).d)|) ^ 3 * (paramsAt μ a).s ^ (2 * N - 17)
      ≤ 8 * (Cq * γ) * (1 + |Real.log t|) ^ 3 * fsXp t 17 := by
    have h1 : Cq * γ * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹
          + |Real.log ((paramsAt μ a).d)|) ^ 3
        ≤ Cq * γ * (8 * (1 + |Real.log t|) ^ 3) :=
      mul_le_mul_of_nonneg_left hL3 hpair
    calc Cq * γ * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹
            + |Real.log ((paramsAt μ a).d)|) ^ 3 * (paramsAt μ a).s ^ (2 * N - 17)
        = (Cq * γ * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹
            + |Real.log ((paramsAt μ a).d)|) ^ 3) * (paramsAt μ a).s ^ (2 * N - 17) := by ring
      _ ≤ (Cq * γ * (8 * (1 + |Real.log t|) ^ 3)) * fsXp t 17 :=
          mul_le_mul h1 hs17 (pow_nonneg hspos.le (2 * N - 17)) (by positivity)
      _ = 8 * (Cq * γ) * (1 + |Real.log t|) ^ 3 * fsXp t 17 := by ring
  have hKAle : 128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (Cq * γ)) ≤ KA := by
    rw [hKA]; linarith
  have hKA2 : 128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (Cq * γ))
      * (fsXp t 17 * (1 + |Real.log t|) ^ 3) ≤ 1 := by
    have hh := hδ t ht htδ
    have hconv : (1 + |Real.log t|) ^ (3 : ℝ) = (1 + |Real.log t|) ^ 3 :=
      Real.rpow_natCast _ 3
    rw [hconv] at hh
    rw [mul_assoc] at hh
    calc 128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (Cq * γ))
          * (fsXp t 17 * (1 + |Real.log t|) ^ 3)
        ≤ KA * (fsXp t 17 * (1 + |Real.log t|) ^ 3) :=
          mul_le_mul_of_nonneg_right hKAle
            (mul_nonneg (fsXp_pos ht).le (pow_nonneg (by positivity) 3))
      _ ≤ 1 := hh
  have hfinal : ((2 * Real.pi) ^ 3)⁻¹ * (8 * (Cq * γ) * (1 + |Real.log t|) ^ 3
      * fsXp t 17) ≤ 1 / 128 := by
    have h1 : 128 * (((2 * Real.pi) ^ 3)⁻¹ * (8 * (Cq * γ) * (1 + |Real.log t|) ^ 3
        * fsXp t 17)) ≤ 1 := by
      rw [show 128 * (((2 * Real.pi) ^ 3)⁻¹ * (8 * (Cq * γ) * (1 + |Real.log t|) ^ 3
            * fsXp t 17))
          = 128 * (((2 * Real.pi) ^ 3)⁻¹) * (8 * (Cq * γ))
            * (fsXp t 17 * (1 + |Real.log t|) ^ 3) by ring]
      exact hKA2
    linarith
  calc ((2 * Real.pi) ^ 3)⁻¹ * (Cq * γ * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹
        + |Real.log ((paramsAt μ a).d)|) ^ 3 * (paramsAt μ a).s ^ (2 * N - 17))
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (8 * (Cq * γ) * (1 + |Real.log t|) ^ 3 * fsXp t 17) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ 1 / 128 := hfinal

/-- **The square-root half of the reduced asymptotic**:
`(2π)⁻³·2√(Ceγζ(2π)³L³s^{2N-31}) ≤ 1/128` for small diluteness. -/
lemma cubeArith_asymSqrt {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 17 ≤ N) (Ce γ ζ : ℝ)
    (hCe : 0 ≤ Ce) (hγ : 0 ≤ γ) (hζ : 0 ≤ ζ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * a ^ 3 ≤ ε₀ →
      ((2 * Real.pi) ^ 3)⁻¹ * (2 * Real.sqrt (Ce * γ * ζ * (2 * Real.pi) ^ 3
          * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|) ^ 3
          * (paramsAt μ a).s ^ (2 * N - 31))) ≤ 1 / 128 := by
  set KB : ℝ := 128 * (((2 * Real.pi) ^ 3)⁻¹)
    * (2 * Real.sqrt (8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3))) + 1 with hKB
  have hKBpos : 0 < KB := by
    rw [hKB]
    have hp : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
    have hs : 0 ≤ Real.sqrt (8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3)) := Real.sqrt_nonneg _
    have hX : 0 ≤ 128 * (((2 * Real.pi) ^ 3)⁻¹)
        * (2 * Real.sqrt (8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3))) := by positivity
    linarith
  obtain ⟨δ, hδpos, hδ⟩ :=
    cubeFsXp_mul_log_le_one (K := KB) (c := 3 / 2) (M := 3 / 2) hKBpos
      (by norm_num) (by norm_num)
  refine ⟨min 1 (min (a ^ (323 / 157 : ℝ)) δ),
    lt_min one_pos (lt_min (Real.rpow_pos_of_pos ha _) hδpos), ?_⟩
  intro μ hμ hμle
  set t : ℝ := μ * a ^ 3 with ht_def
  have ht : 0 < t := by rw [ht_def]; positivity
  have hspos : 0 < (paramsAt μ a).s := fsXp_pos ht
  have ht1 : t ≤ 1 := hμle.trans (min_le_left _ _)
  have htm : t ≤ min (a ^ (323 / 157 : ℝ)) δ := hμle.trans (min_le_right _ _)
  have hta : t ≤ a ^ (323 / 157 : ℝ) := htm.trans (min_le_left _ _)
  have htδ : t ≤ δ := htm.trans (min_le_right _ _)
  have hu : a⁻¹ * fsXp t 157 ≤ 1 := by
    have h1 : fsXp t 157 ≤ a := by
      have h2 := Real.rpow_le_rpow ht.le hta (by norm_num : (0 : ℝ) ≤ (157 : ℝ) / 323)
      have h3 : (a ^ (323 / 157 : ℝ)) ^ ((157 : ℝ) / 323) = a := by
        rw [← Real.rpow_mul ha.le]; norm_num
      rw [h3] at h2
      simpa [fsXp] using h2
    calc a⁻¹ * fsXp t 157 ≤ a⁻¹ * a := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by rw [inv_mul_cancel₀ ha.ne']
  have hLb : 1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|
      ≤ 2 * (1 + |Real.log t|) := by
    have h := cubeArith_L_le_two hμ ha hu
    simpa only [ht_def] using h
  have hLnn : 0 ≤ 1 + (sideAt μ a * (paramsAt μ a).d)⁻¹
      + |Real.log ((paramsAt μ a).d)| := by
    have hℓ : 0 < sideAt μ a := by
      rw [Work.BoseFixB1.sideAt_eq_fsXp ha hμ]; exact mul_pos ha (fsXp_pos ht)
    have hd : 0 < (paramsAt μ a).d := fsXp_pos ht
    have hinv : 0 < (sideAt μ a * (paramsAt μ a).d)⁻¹ := inv_pos.mpr (mul_pos hℓ hd)
    have := abs_nonneg (Real.log ((paramsAt μ a).d)); linarith
  have hL3 : (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|) ^ 3
      ≤ 8 * (1 + |Real.log t|) ^ 3 := by
    calc (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|) ^ 3
        ≤ (2 * (1 + |Real.log t|)) ^ 3 := pow_le_pow_left₀ hLnn hLb 3
      _ = 8 * (1 + |Real.log t|) ^ 3 := by ring
  have hs3 : (paramsAt μ a).s ^ (2 * N - 31) ≤ fsXp t 3 := by
    have hs : (paramsAt μ a).s = fsXp t 1 := by rw [ht_def]; rfl
    rw [hs, fsXp_pow ht.le]
    refine fsXp_le_fsXp ht ht1 ?_
    have hNR : (17 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [Nat.cast_sub (by omega : 31 ≤ 2 * N)]
    push_cast
    linarith
  have hCe0 : 0 ≤ Ce * γ * ζ * (2 * Real.pi) ^ 3 := by positivity
  have harg : Ce * γ * ζ * (2 * Real.pi) ^ 3
        * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|) ^ 3
        * (paramsAt μ a).s ^ (2 * N - 31)
      ≤ 8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3) * (1 + |Real.log t|) ^ 3 * fsXp t 3 := by
    have h1 : Ce * γ * ζ * (2 * Real.pi) ^ 3
          * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|) ^ 3
        ≤ Ce * γ * ζ * (2 * Real.pi) ^ 3 * (8 * (1 + |Real.log t|) ^ 3) :=
      mul_le_mul_of_nonneg_left hL3 hCe0
    calc Ce * γ * ζ * (2 * Real.pi) ^ 3
            * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|) ^ 3
            * (paramsAt μ a).s ^ (2 * N - 31)
        = (Ce * γ * ζ * (2 * Real.pi) ^ 3
            * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹
              + |Real.log ((paramsAt μ a).d)|) ^ 3) * (paramsAt μ a).s ^ (2 * N - 31) := by ring
      _ ≤ (Ce * γ * ζ * (2 * Real.pi) ^ 3 * (8 * (1 + |Real.log t|) ^ 3)) * fsXp t 3 :=
          mul_le_mul h1 hs3 (pow_nonneg hspos.le (2 * N - 31)) (by positivity)
      _ = 8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3) * (1 + |Real.log t|) ^ 3 * fsXp t 3 := by ring
  have hsqrt : Real.sqrt (Ce * γ * ζ * (2 * Real.pi) ^ 3
        * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|) ^ 3
        * (paramsAt μ a).s ^ (2 * N - 31))
      ≤ Real.sqrt (8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3) * (1 + |Real.log t|) ^ 3
        * fsXp t 3) := Real.sqrt_le_sqrt harg
  have hfac : Real.sqrt (8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3) * (1 + |Real.log t|) ^ 3
        * fsXp t 3)
      = Real.sqrt (8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3)) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)
        * fsXp t (3 / 2) := by
    have hA0 : 0 ≤ 8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3) := by positivity
    have hM0 : 0 ≤ 1 + |Real.log t| := by positivity
    rw [show 8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3) * (1 + |Real.log t|) ^ 3 * fsXp t 3
        = 8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3) * ((1 + |Real.log t|) ^ 3
          * (fsXp t 1) ^ 3) by rw [fsXp_pow ht.le]; norm_num; ring]
    rw [Real.sqrt_mul hA0, Real.sqrt_mul (pow_nonneg hM0 3)]
    rw [show Real.sqrt ((1 + |Real.log t|) ^ 3) = (1 + |Real.log t|) ^ (3 / 2 : ℝ) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (1 + |Real.log t|) 3, ← Real.rpow_mul hM0]; norm_num]
    rw [show Real.sqrt ((fsXp t 1) ^ 3) = fsXp t (3 / 2) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (fsXp t 1) 3,
        ← Real.rpow_mul (fsXp_nonneg ht.le), fsXp_rpow ht.le]
      norm_num]
    ring
  have hKBle : 128 * (((2 * Real.pi) ^ 3)⁻¹)
      * (2 * Real.sqrt (8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3))) ≤ KB := by
    rw [hKB]; linarith
  have hKB2 : 128 * (((2 * Real.pi) ^ 3)⁻¹)
      * (2 * Real.sqrt (8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3)))
      * (fsXp t (3 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) ≤ 1 := by
    have hh := hδ t ht htδ
    rw [mul_assoc] at hh
    calc 128 * (((2 * Real.pi) ^ 3)⁻¹)
          * (2 * Real.sqrt (8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3)))
          * (fsXp t (3 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ))
        ≤ KB * (fsXp t (3 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hKBle
            (mul_nonneg (fsXp_pos ht).le
              (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + |Real.log t|) (3 / 2)))
      _ ≤ 1 := hh
  have hfinal : ((2 * Real.pi) ^ 3)⁻¹
      * (2 * (Real.sqrt (8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3))
          * (1 + |Real.log t|) ^ (3 / 2 : ℝ) * fsXp t (3 / 2))) ≤ 1 / 128 := by
    have h1 : 128 * (((2 * Real.pi) ^ 3)⁻¹
        * (2 * (Real.sqrt (8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3))
            * (1 + |Real.log t|) ^ (3 / 2 : ℝ) * fsXp t (3 / 2)))) ≤ 1 := by
      rw [show 128 * (((2 * Real.pi) ^ 3)⁻¹
            * (2 * (Real.sqrt (8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3))
                * (1 + |Real.log t|) ^ (3 / 2 : ℝ) * fsXp t (3 / 2))))
          = 128 * (((2 * Real.pi) ^ 3)⁻¹)
            * (2 * Real.sqrt (8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3)))
            * (fsXp t (3 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) by ring]
      exact hKB2
    linarith
  calc ((2 * Real.pi) ^ 3)⁻¹ * (2 * Real.sqrt (Ce * γ * ζ * (2 * Real.pi) ^ 3
        * (1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)|) ^ 3
        * (paramsAt μ a).s ^ (2 * N - 31)))
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (2 * (Real.sqrt (8 * (Ce * γ * ζ * (2 * Real.pi) ^ 3))
          * (1 + |Real.log t|) ^ (3 / 2 : ℝ) * fsXp t (3 / 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hfac]
        exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ ≤ 1 / 128 := hfinal

/-- **The arithmetic of the cube mean-mismatch** (at decay order `N`): with `ℓ = K_ℓ(μa)^{-1/2}`,
`d, s` the FS parameters at diluteness `t = μa³` and `L = 1+(ℓd)^{-1}+|log d|`, the two cut-word
terms `(2π)⁻³·Cq(ℓd)s^{2N-5}·γL³((ℓd)³)⁻¹` and `(2π)⁻³·2√(Ce(ℓd)⁻¹s^{2N-7}·γL³((ℓd)³)⁻¹(2π)³ζ)`
fit inside the flat payment `bValue/(4ℓ²)` for all sufficiently small diluteness, for every decay
order `N ≥ 17`.  Proof route: `t = μa³`, `s = t^{1/323}`, `d = s⁶`, `ℓ = a t^{-163/323}`, so after
multiplying by `ℓ²` the two ratios are `≍ s^{2N-17}L³` and `≍ s^{N-31/2}L^{3/2}`, and `L` is
controlled by `|log t|` (the proved `Work.BoseFixB1.fsXpLogSmall` bookkeeping). -/
theorem cubeArithN (N : ℕ) (hN : 17 ≤ N) (Cq Ce γ ζ : ℝ) (hCq : 0 ≤ Cq) (hCe : 0 ≤ Ce)
    (hγ : 0 ≤ γ) (hζ : 0 ≤ ζ) {a : ℝ} (ha : 0 < a) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * a ^ 3 ≤ ε₀ →
      (let ℓ : ℝ := Work.BoseBox.sideAt μ a
       let d : ℝ := (Work.BoseBox.paramsAt μ a).d
       let s : ℝ := (Work.BoseBox.paramsAt μ a).s
       let L : ℝ := 1 + (ℓ * d)⁻¹ + |Real.log d|
       ((2 * Real.pi) ^ 3)⁻¹ * (Cq * (ℓ * d) * s ^ (2 * N - 5) * γ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹
          + 2 * Real.sqrt (Ce * (ℓ * d)⁻¹ * s ^ (2 * N - 7) * γ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹
              * (2 * Real.pi) ^ 3 * ζ))
        ≤ Work.BoseBox.bValue / (4 * ℓ ^ 2)) := by
  obtain ⟨εP, hεPpos, hP⟩ := cubeArith_asymProd ha N hN Cq γ hCq hγ
  obtain ⟨εQ, hεQpos, hQ⟩ := cubeArith_asymSqrt ha N hN Ce γ ζ hCe hγ hζ
  refine ⟨min εP εQ, lt_min hεPpos hεQpos, fun μ hμ hμle => ?_⟩
  have hP' := hP μ hμ (hμle.trans (min_le_left _ _))
  have hQ' := hQ μ hμ (hμle.trans (min_le_right _ _))
  have hC := cubeArith_prodRed hμ ha N hN Cq γ
  have hD := cubeArith_sqrtRed hμ ha N hN Ce γ ζ hCe hγ hζ
  dsimp only
  set L : ℝ := 1 + (sideAt μ a * (paramsAt μ a).d)⁻¹ + |Real.log ((paramsAt μ a).d)| with hLs
  set P : ℝ := Cq * γ * L ^ 3 * (paramsAt μ a).s ^ (2 * N - 17) with hPs
  set Q : ℝ := 2 * Real.sqrt (Ce * γ * ζ * (2 * Real.pi) ^ 3 * L ^ 3
    * (paramsAt μ a).s ^ (2 * N - 31)) with hQs
  have hPQ : ((2 * Real.pi) ^ 3)⁻¹ * (P + Q) ≤ 1 / 64 := by
    have h1 : ((2 * Real.pi) ^ 3)⁻¹ * P ≤ 1 / 128 := hP'
    have h2 : ((2 * Real.pi) ^ 3)⁻¹ * Q ≤ 1 / 128 := hQ'
    have h3 : ((2 * Real.pi) ^ 3)⁻¹ * (P + Q)
        = ((2 * Real.pi) ^ 3)⁻¹ * P + ((2 * Real.pi) ^ 3)⁻¹ * Q := by ring
    rw [h3]; linarith
  have hb : Work.BoseBox.bValue / (4 * (sideAt μ a) ^ 2)
      = (1 / 64) * (sideAt μ a)⁻¹ ^ 2 := by
    rw [Work.BoseBox.bValue, inv_pow, div_eq_mul_inv, mul_inv]
    norm_num
    ring
  rw [hb]
  have hsum : Cq * (sideAt μ a * (paramsAt μ a).d) * (paramsAt μ a).s ^ (2 * N - 5)
        * γ * L ^ 3 * ((sideAt μ a * (paramsAt μ a).d) ^ 3)⁻¹
      + 2 * Real.sqrt (Ce * (sideAt μ a * (paramsAt μ a).d)⁻¹ * (paramsAt μ a).s ^ (2 * N - 7)
          * γ * L ^ 3 * ((sideAt μ a * (paramsAt μ a).d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * ζ)
      ≤ (sideAt μ a)⁻¹ ^ 2 * P + (sideAt μ a)⁻¹ ^ 2 * Q := by
    refine add_le_add (le_of_eq hC) ?_
    exact hD
  have hstep : ((2 * Real.pi) ^ 3)⁻¹ * (Cq * (sideAt μ a * (paramsAt μ a).d)
        * (paramsAt μ a).s ^ (2 * N - 5) * γ * L ^ 3
        * ((sideAt μ a * (paramsAt μ a).d) ^ 3)⁻¹
      + 2 * Real.sqrt (Ce * (sideAt μ a * (paramsAt μ a).d)⁻¹ * (paramsAt μ a).s ^ (2 * N - 7)
          * γ * L ^ 3 * ((sideAt μ a * (paramsAt μ a).d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * ζ))
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((sideAt μ a)⁻¹ ^ 2 * (P + Q)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ (sideAt μ a)⁻¹ ^ 2 * P + (sideAt μ a)⁻¹ ^ 2 * Q := hsum
      _ = (sideAt μ a)⁻¹ ^ 2 * (P + Q) := by ring
  calc ((2 * Real.pi) ^ 3)⁻¹ * (Cq * (sideAt μ a * (paramsAt μ a).d)
        * (paramsAt μ a).s ^ (2 * N - 5) * γ * L ^ 3
        * ((sideAt μ a * (paramsAt μ a).d) ^ 3)⁻¹
      + 2 * Real.sqrt (Ce * (sideAt μ a * (paramsAt μ a).d)⁻¹ * (paramsAt μ a).s ^ (2 * N - 7)
          * γ * L ^ 3 * ((sideAt μ a * (paramsAt μ a).d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * ζ))
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((sideAt μ a)⁻¹ ^ 2 * (P + Q)) := hstep
    _ = (sideAt μ a)⁻¹ ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * (P + Q)) := by ring
    _ ≤ (sideAt μ a)⁻¹ ^ 2 * (1 / 64) := mul_le_mul_of_nonneg_left hPQ (by positivity)
    _ = (1 / 64) * (sideAt μ a)⁻¹ ^ 2 := by ring

end Work.BoseFixB1S.CubeWindow
