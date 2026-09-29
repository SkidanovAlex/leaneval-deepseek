import Mathlib
import ChallengeDeps
import Submission.Work.TMContract.Defs

/-!
# Component C2 (`P_Perfect`): shared definitions

This module fixes the vocabulary for the proof of `Work.TMComp.prove_Perfect`
(the component `Work.TMContract.P_Perfect` of the Ten Martini formalisation).

* `sh k` -- the shift `(sh k f) n = f (n + k)` on `l^2(Z)`, as a linear isometry equivalence.
* `diag c K hK` -- the diagonal operator `(diag c f) n = c n * f n` (bounded by `K`).
* `amoOp α lam θ` -- the canonical almost Mathieu operator, defined by its coordinate formula
  `(amoOp f) n = f (n+1) + f (n-1) + 2λ cos 2π(θ+nα) f n`.
* `projFun E δ` / `proj α lam θ E δ` -- the canonical spectral projection `cfc (projFun E δ)`
  at an energy `E` isolated in the spectrum by a margin `δ`.
-/

open LeanEval.Analysis.TenMartini
open Work.TMContract
open scoped ENNReal

noncomputable section

namespace Work.TMComp.Perfect

/-! ## 1. The shift operator -/

theorem memℓp_shift {f : ℤ → ℂ} (hf : Memℓp f 2) (k : ℤ) : Memℓp (fun n : ℤ => f (n + k)) 2 := by
  apply memℓp_gen
  have h : Summable (fun n : ℤ => ‖f n‖ ^ ((2 : ℝ≥0∞).toReal)) := hf.summable (by norm_num)
  have h2 := (Equiv.summable_iff (Equiv.addRight k)).mpr h
  simpa [Function.comp_def] using h2

/-- Reindexing `n ↦ n + k` of a sequence in `l^2(Z)`. -/
def shiftFn (k : ℤ) (f : EllTwo) : EllTwo :=
  ⟨fun n : ℤ => f (n + k), memℓp_shift (lp.memℓp f) k⟩

@[simp] theorem shiftFn_apply (k : ℤ) (f : EllTwo) (n : ℤ) : shiftFn k f n = f (n + k) := rfl

theorem ellTwo_ext {f g : EllTwo} (h : ∀ n : ℤ, f n = g n) : f = g := lp.ext (funext h)

/-- The shift as a linear isometry equivalence of `l^2(Z)`. -/
def shE (k : ℤ) : EllTwo ≃ₗᵢ[ℂ] EllTwo where
  toFun := shiftFn k
  invFun := shiftFn (-k)
  left_inv f := by apply ellTwo_ext; intro n; simp [shiftFn_apply]
  right_inv f := by apply ellTwo_ext; intro n; simp [shiftFn_apply]
  map_add' f g := by apply ellTwo_ext; intro n; simp [shiftFn_apply]
  map_smul' c f := by apply ellTwo_ext; intro n; simp [shiftFn_apply]
  norm_map' f := by
    have h1 := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℤ => ℂ)
      (show (0:ℝ) < (2:ℝ≥0∞).toReal by norm_num) (shiftFn k f)
    have h2 := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℤ => ℂ)
      (show (0:ℝ) < (2:ℝ≥0∞).toReal by norm_num) f
    have h3 : (∑' n : ℤ, ‖shiftFn k f n‖ ^ ((2 : ℝ≥0∞).toReal))
        = ∑' n : ℤ, ‖f n‖ ^ ((2 : ℝ≥0∞).toReal) := by
      rw [← Equiv.tsum_eq (Equiv.addRight k) (fun i => ‖f i‖ ^ ((2:ℝ≥0∞).toReal))]
      exact tsum_congr (fun n => by simp [shiftFn_apply])
    have h4 : ‖shiftFn k f‖ ^ ((2:ℝ≥0∞).toReal) = ‖f‖ ^ ((2:ℝ≥0∞).toReal) := by
      rw [h1, h3, ← h2]
    have h5 : ‖shiftFn k f‖ ^ (2:ℕ) = ‖f‖ ^ (2:ℕ) := by simpa using h4
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h5

/-- The shift `(sh k f) n = f (n + k)` as a continuous linear map. -/
def sh (k : ℤ) : EllTwo →L[ℂ] EllTwo := (shE k).toLinearIsometry.toContinuousLinearMap

@[simp] theorem sh_apply (k : ℤ) (f : EllTwo) (n : ℤ) : sh k f n = f (n + k) := rfl

theorem sh_isometry (k : ℤ) (f : EllTwo) : ‖sh k f‖ = ‖f‖ := (shE k).norm_map f

theorem sh_zero : sh 0 = 1 := by
  refine ContinuousLinearMap.ext (fun f => ellTwo_ext (fun n => ?_))
  simp [sh_apply]

theorem sh_comp (k l : ℤ) : sh k * sh l = sh (k + l) := by
  refine ContinuousLinearMap.ext (fun f => ellTwo_ext (fun n => ?_))
  simp only [ContinuousLinearMap.mul_apply, sh_apply]
  ring

theorem sh_injective (k : ℤ) : Function.Injective (sh k) := by
  intro f g hfg
  have h := congrArg (sh (-k)) hfg
  simpa [← ContinuousLinearMap.mul_apply, sh_comp, sh_zero] using h

/-! ## 2. The diagonal operator -/

theorem memℓp_diag {c : ℤ → ℂ} {K : ℝ} (hK : ∀ n : ℤ, ‖c n‖ ≤ K) {f : ℤ → ℂ}
    (hf : Memℓp f 2) : Memℓp (fun n : ℤ => c n * f n) 2 := by
  refine Memℓp.mono (hf.norm.const_mul K) (fun n => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hK n) (norm_nonneg _)

/-- The underlying linear map of the diagonal operator `(c . f) n = c n * f n`. -/
def diagL (c : ℤ → ℂ) (K : ℝ) (hK : ∀ n : ℤ, ‖c n‖ ≤ K) : EllTwo →ₗ[ℂ] EllTwo where
  toFun f := ⟨fun n : ℤ => c n * f n, memℓp_diag hK (lp.memℓp f)⟩
  map_add' f g := by
    apply ellTwo_ext; intro n
    simp only [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' a f := by
    apply ellTwo_ext; intro n
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem diagL_apply (c : ℤ → ℂ) (K : ℝ) (hK : ∀ n : ℤ, ‖c n‖ ≤ K) (f : EllTwo) (n : ℤ) :
    diagL c K hK f n = c n * f n := rfl

theorem diagL_bound (c : ℤ → ℂ) (K : ℝ) (hK : ∀ n : ℤ, ‖c n‖ ≤ K) (f : EllTwo) :
    ‖diagL c K hK f‖ ≤ K * ‖f‖ := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  have hnorm : ‖f‖ ^ ((2 : ℝ≥0∞).toReal) = ∑' n : ℤ, ‖f n‖ ^ ((2 : ℝ≥0∞).toReal) :=
    lp.norm_rpow_eq_tsum (show (0:ℝ) < (2:ℝ≥0∞).toReal by norm_num) f
  have hpt : ∀ n : ℤ, ‖c n * f n‖ ^ ((2 : ℝ≥0∞).toReal)
      ≤ K ^ ((2 : ℝ≥0∞).toReal) * ‖f n‖ ^ ((2 : ℝ≥0∞).toReal) := by
    intro n
    calc ‖c n * f n‖ ^ ((2 : ℝ≥0∞).toReal)
        ≤ (K * ‖f n‖) ^ ((2 : ℝ≥0∞).toReal) :=
          Real.rpow_le_rpow (norm_nonneg _)
            (by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hK n) (norm_nonneg _))
            (by norm_num)
      _ = K ^ ((2 : ℝ≥0∞).toReal) * ‖f n‖ ^ ((2 : ℝ≥0∞).toReal) :=
          Real.mul_rpow hK0 (norm_nonneg _)
  have hS2 : Summable (fun n : ℤ => K ^ ((2 : ℝ≥0∞).toReal) * ‖f n‖ ^ ((2 : ℝ≥0∞).toReal)) :=
    Summable.mul_left _ ((lp.memℓp f).summable (by norm_num))
  have hS1 : Summable (fun n : ℤ => ‖c n * f n‖ ^ ((2 : ℝ≥0∞).toReal)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hpt hS2
  have hmain : ∑' n : ℤ, ‖c n * f n‖ ^ ((2 : ℝ≥0∞).toReal)
      ≤ (K * ‖f‖) ^ ((2 : ℝ≥0∞).toReal) := by
    calc ∑' n : ℤ, ‖c n * f n‖ ^ ((2 : ℝ≥0∞).toReal)
        ≤ ∑' n : ℤ, K ^ ((2 : ℝ≥0∞).toReal) * ‖f n‖ ^ ((2 : ℝ≥0∞).toReal) :=
          Summable.tsum_le_tsum hpt hS1 hS2
      _ = K ^ ((2 : ℝ≥0∞).toReal) * ∑' n : ℤ, ‖f n‖ ^ ((2 : ℝ≥0∞).toReal) :=
          tsum_mul_left
      _ = K ^ ((2 : ℝ≥0∞).toReal) * ‖f‖ ^ ((2 : ℝ≥0∞).toReal) := by rw [hnorm]
      _ = (K * ‖f‖) ^ ((2 : ℝ≥0∞).toReal) := (Real.mul_rpow hK0 (norm_nonneg f)).symm
  exact lp.norm_le_of_tsum_le (by norm_num) (mul_nonneg hK0 (norm_nonneg f)) hmain

/-- The diagonal operator `(diag c f) n = c n * f n`, bounded by `K ≥ sup_n ‖c n‖`. -/
def diag (c : ℤ → ℂ) (K : ℝ) (hK : ∀ n : ℤ, ‖c n‖ ≤ K) : EllTwo →L[ℂ] EllTwo :=
  (diagL c K hK).mkContinuous K (diagL_bound c K hK)

@[simp] theorem diag_apply (c : ℤ → ℂ) (K : ℝ) (hK : ∀ n : ℤ, ‖c n‖ ≤ K) (f : EllTwo) (n : ℤ) :
    diag c K hK f n = c n * f n := by
  rw [show diag c K hK = (diagL c K hK).mkContinuous K (diagL_bound c K hK) from rfl,
    LinearMap.mkContinuous_apply]
  rfl

theorem diag_norm_le (c : ℤ → ℂ) (K : ℝ) (hK : ∀ n : ℤ, ‖c n‖ ≤ K) (f : EllTwo) :
    ‖diag c K hK f‖ ≤ K * ‖f‖ := by
  rw [show diag c K hK = (diagL c K hK).mkContinuous K (diagL_bound c K hK) from rfl,
    LinearMap.mkContinuous_apply]
  exact diagL_bound c K hK f

theorem diag_congr {c c' : ℤ → ℂ} {K : ℝ} (hK : ∀ n, ‖c n‖ ≤ K) (hK' : ∀ n, ‖c' n‖ ≤ K)
    (h : ∀ n, c n = c' n) : diag c K hK = diag c' K hK' := by
  refine ContinuousLinearMap.ext (fun f => ellTwo_ext (fun n => ?_))
  simp only [diag_apply, h]

theorem diag_sub {c c' : ℤ → ℂ} {K K' : ℝ} (hK : ∀ n, ‖c n‖ ≤ K) (hK' : ∀ n, ‖c' n‖ ≤ K')
    {K'' : ℝ} (hK'' : ∀ n, ‖c n - c' n‖ ≤ K'') :
    diag c K hK - diag c' K' hK' = diag (fun n => c n - c' n) K'' hK'' := by
  refine ContinuousLinearMap.ext (fun f => ellTwo_ext (fun n => ?_))
  simp only [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply, diag_apply]
  ring

/-! ## 3. The canonical almost Mathieu operator -/

/-- The complex weight `2λ cos 2π(θ + nα)` of the almost Mathieu potential. -/
def potC (α lam θ : ℝ) (n : ℤ) : ℂ := ((amoPot α lam θ n : ℝ) : ℂ)

@[simp] theorem potC_apply (α lam θ : ℝ) (n : ℤ) : potC α lam θ n = ((amoPot α lam θ n : ℝ) : ℂ) :=
  rfl

theorem potC_bound (α lam θ : ℝ) : ∀ n : ℤ, ‖potC α lam θ n‖ ≤ 2 * |lam| := by
  intro n
  rw [potC_apply, Complex.norm_real, Real.norm_eq_abs, amoPot, abs_mul, abs_mul]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  have h3 := Real.abs_cos_le_one (2 * Real.pi * (θ + (n : ℝ) * α))
  have h4 : (0:ℝ) ≤ |lam| := abs_nonneg lam
  nlinarith [h3, h4]

/-- The canonical almost Mathieu operator with frequency `α`, coupling `λ` and phase `θ`:
`H u n = u(n+1) + u(n-1) + 2λ cos 2π(θ+nα) u n`. -/
def amoOp (α lam θ : ℝ) : EllTwo →L[ℂ] EllTwo :=
  sh 1 + sh (-1) + diag (potC α lam θ) (2 * |lam|) (potC_bound α lam θ)

@[simp] theorem amoOp_coord (α lam θ : ℝ) (f : EllTwo) (n : ℤ) :
    amoOp α lam θ f n = f (n + 1) + f (n - 1) + ((amoPot α lam θ n : ℝ) : ℂ) * f n := by
  show (sh 1 + sh (-1) + diag (potC α lam θ) (2 * |lam|) (potC_bound α lam θ)) f n = _
  simp only [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply, sh_apply, diag_apply,
    potC_apply]
  ring

theorem amoOp_isAMO (α lam θ : ℝ) : IsAlmostMathieuOperator α lam θ (amoOp α lam θ) := by
  rw [isAMO_iff]
  intro f n
  rw [amoOp_coord]
  rfl

theorem amoOp_unique {α lam θ : ℝ} {H : EllTwo →L[ℂ] EllTwo}
    (hH : IsAlmostMathieuOperator α lam θ H) : H = amoOp α lam θ := by
  rw [isAMO_iff] at hH
  refine ContinuousLinearMap.ext (fun f => ellTwo_ext (fun n => ?_))
  rw [amoOp_coord, hH f n]
  rfl

theorem amoOp_periodic (α lam θ : ℝ) : amoOp α lam (θ + 1) = amoOp α lam θ := by
  have h : ∀ n : ℤ, potC α lam (θ + 1) n = potC α lam θ n := by
    intro n
    rw [potC_apply, potC_apply, amoPot, amoPot]
    have harg : 2 * Real.pi * (θ + 1 + (n : ℝ) * α) = 2 * Real.pi * (θ + (n : ℝ) * α) + 2 * Real.pi := by
      ring
    rw [harg, Real.cos_add_two_pi]
  simp only [amoOp]
  rw [diag_congr (potC_bound α lam (θ + 1)) (potC_bound α lam θ) h]

/-! ## 4. The canonical spectral projection at an isolated energy -/

/-- The "tent" function `z ↦ max 0 (1 - ‖z - E‖/δ)`; it equals `1` at `E` and vanishes for
`‖z - E‖ ≥ δ`, so on a spectrum whose only point within distance `δ` of `E` is `E` it is the
indicator of `{E}`. -/
def projFun (E δ : ℝ) : ℂ → ℂ := fun z => ((max 0 (1 - ‖z - (E : ℂ)‖ / δ) : ℝ) : ℂ)

theorem projFun_continuous (E δ : ℝ) : Continuous (projFun E δ) := by
  unfold projFun
  fun_prop

theorem projFun_apply_self (E δ : ℝ) : projFun E δ (E : ℂ) = 1 := by
  unfold projFun
  simp

theorem projFun_star (E δ : ℝ) (z : ℂ) : star (projFun E δ z) = projFun E δ z := by
  unfold projFun
  exact Complex.conj_ofReal _

theorem projFun_vanishes {E δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : δ ≤ ‖z - (E : ℂ)‖) :
    projFun E δ z = 0 := by
  unfold projFun
  have h : 1 - ‖z - (E : ℂ)‖ / δ ≤ 0 := by
    rw [sub_nonpos, one_le_div hδ]
    exact hz
  rw [max_eq_left h]
  simp

/-- The canonical spectral projection of `amoOp α lam θ` at the energy `E` (with isolation
margin `δ`): the functional calculus of the tent function `projFun E δ`. -/
def proj (α lam θ : ℝ) (E δ : ℝ) : EllTwo →L[ℂ] EllTwo :=
  cfc (projFun E δ) (amoOp α lam θ)

end Work.TMComp.Perfect
