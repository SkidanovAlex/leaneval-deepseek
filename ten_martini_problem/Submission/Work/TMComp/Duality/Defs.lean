import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMC7Core.Scale.spectral_continuity

/-!
# Aubry duality (component C3): infrastructure

This file defines the operators and vectors used in the proof of `P_Duality`
(`Σ_λ = λ Σ_{1/λ}`, Avila--Jitomirskaya §1.1).
-/

open LeanEval.Analysis.TenMartini

open scoped ENNReal

noncomputable section

namespace Work.TMComp.Duality

/-! ## 1. Bounded operators with prescribed coordinates -/

section General

variable {ι : Type*} [DecidableEq ι]

/-- Reindexing a `ℓ²` sequence along a bijection preserves `Memℓp`. -/
theorem memℓp_comp_equiv {f : ι → ℂ} (e : ι ≃ ι) (hf : Memℓp f 2) :
    Memℓp (fun i => f (e i)) 2 := by
  refine memℓp_gen ?_
  have h : Summable (fun i : ι => ‖f i‖ ^ ((2 : ℝ≥0∞).toReal)) := hf.summable (by norm_num)
  have h2 : Summable ((fun i : ι => ‖f i‖ ^ ((2 : ℝ≥0∞).toReal)) ∘ e) :=
    (Equiv.summable_iff e).2 h
  simpa only [Function.comp_def] using h2

/-- The operator `f ↦ (i ↦ b i * f (e i))` on `ℓ²(ι)` is bounded with norm `≤ K`, whenever
`e` is a bijection of the index type and `‖b i‖ ≤ K` for all `i`. -/
theorem exists_coord_op (b : ι → ℂ) (e : ι ≃ ι) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ i, ‖b i‖ ≤ K) :
    ∃ T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2,
      (∀ (f : lp (fun _ : ι => ℂ) 2) (i : ι), T f i = b i * f (e i)) ∧ ‖T‖ ≤ K := by
  have hmem : ∀ f : lp (fun _ : ι => ℂ) 2, Memℓp (fun i => b i * f (e i)) 2 := by
    intro f
    have hKshift : Memℓp (fun i => K * ‖f (e i)‖) 2 :=
      (memℓp_comp_equiv e (lp.memℓp f)).norm.const_mul K
    refine Memℓp.mono hKshift (fun i => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hK i) (norm_nonneg _)
  let L : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 :=
    { toFun := fun f => ⟨fun i => b i * f (e i), hmem f⟩
      map_add' := fun f g => by
        apply lp.ext; funext i
        simp only [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun a f => by
        apply lp.ext; funext i
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hbound : ∀ f : lp (fun _ : ι => ℂ) 2, ‖L f‖ ≤ K * ‖f‖ := by
    intro f
    have hs : Summable (fun i : ι => ‖f (e i)‖ ^ ((2 : ℝ≥0∞).toReal)) :=
      (memℓp_comp_equiv e (lp.memℓp f)).summable (by norm_num)
    have hshiftnorm :
        ∑' i : ι, ‖f (e i)‖ ^ ((2 : ℝ≥0∞).toReal) = ‖f‖ ^ ((2 : ℝ≥0∞).toReal) := by
      rw [show (∑' i : ι, ‖f (e i)‖ ^ ((2 : ℝ≥0∞).toReal))
            = ∑' i : ι, ‖f i‖ ^ ((2 : ℝ≥0∞).toReal) from by
            simpa only [Function.comp_def] using
              (Equiv.tsum_eq e (fun i : ι => ‖f i‖ ^ ((2 : ℝ≥0∞).toReal)))]
      exact (lp.norm_rpow_eq_tsum (by norm_num) f).symm
    have hpt : ∀ i : ι, ‖b i * f (e i)‖ ^ ((2 : ℝ≥0∞).toReal)
        ≤ K ^ ((2 : ℝ≥0∞).toReal) * ‖f (e i)‖ ^ ((2 : ℝ≥0∞).toReal) := by
      intro i
      have hle : ‖b i * f (e i)‖ ≤ K * ‖f (e i)‖ := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hK i) (norm_nonneg _)
      calc ‖b i * f (e i)‖ ^ ((2 : ℝ≥0∞).toReal)
          ≤ (K * ‖f (e i)‖) ^ ((2 : ℝ≥0∞).toReal) :=
            Real.rpow_le_rpow (by positivity) hle (by norm_num)
        _ = K ^ ((2 : ℝ≥0∞).toReal) * ‖f (e i)‖ ^ ((2 : ℝ≥0∞).toReal) :=
            Real.mul_rpow hK0 (norm_nonneg _)
    have hS2 : Summable
        (fun i : ι => K ^ ((2 : ℝ≥0∞).toReal) * ‖f (e i)‖ ^ ((2 : ℝ≥0∞).toReal)) :=
      hs.mul_left _
    have hS1 : Summable (fun i : ι => ‖b i * f (e i)‖ ^ ((2 : ℝ≥0∞).toReal)) :=
      Summable.of_nonneg_of_le (fun i => by positivity) hpt hS2
    have hmain : ∑' i : ι, ‖b i * f (e i)‖ ^ ((2 : ℝ≥0∞).toReal)
        ≤ (K * ‖f‖) ^ ((2 : ℝ≥0∞).toReal) := by
      calc ∑' i : ι, ‖b i * f (e i)‖ ^ ((2 : ℝ≥0∞).toReal)
          ≤ ∑' i : ι, K ^ ((2 : ℝ≥0∞).toReal) * ‖f (e i)‖ ^ ((2 : ℝ≥0∞).toReal) :=
            Summable.tsum_le_tsum hpt hS1 hS2
        _ = K ^ ((2 : ℝ≥0∞).toReal) * ∑' i : ι, ‖f (e i)‖ ^ ((2 : ℝ≥0∞).toReal) :=
            tsum_mul_left
        _ = K ^ ((2 : ℝ≥0∞).toReal) * ‖f‖ ^ ((2 : ℝ≥0∞).toReal) := by rw [hshiftnorm]
        _ = (K * ‖f‖) ^ ((2 : ℝ≥0∞).toReal) := (Real.mul_rpow hK0 (norm_nonneg f)).symm
    exact lp.norm_le_of_tsum_le (by norm_num) (mul_nonneg hK0 (norm_nonneg _)) hmain
  refine ⟨L.mkContinuous K hbound, ?_, ?_⟩
  · intro f i
    rw [LinearMap.mkContinuous_apply]
    rfl
  · exact LinearMap.mkContinuous_norm_le L hK0 hbound

/-- The bounded operator on `ℓ²` with coordinates `f ↦ (i ↦ b i * f (e i))`. -/
def coordOp (b : ι → ℂ) (e : ι ≃ ι) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ i, ‖b i‖ ≤ K) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  (exists_coord_op b e hK0 hK).choose

theorem coordOp_coord (b : ι → ℂ) (e : ι ≃ ι) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ i, ‖b i‖ ≤ K)
    (f : lp (fun _ : ι => ℂ) 2) (i : ι) : coordOp b e K hK0 hK f i = b i * f (e i) :=
  (exists_coord_op b e hK0 hK).choose_spec.1 f i

theorem coordOp_norm_le (b : ι → ℂ) (e : ι ≃ ι) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ i, ‖b i‖ ≤ K) : ‖coordOp b e K hK0 hK‖ ≤ K :=
  (exists_coord_op b e hK0 hK).choose_spec.2

/-- A bounded operator on `ℓ²` is determined by its coordinates. -/
theorem coord_ext {T U : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2}
    (h : ∀ (f : lp (fun _ : ι => ℂ) 2) (i : ι), T f i = U f i) : T = U :=
  ContinuousLinearMap.ext fun f => lp.ext (funext fun i => h f i)

/-- Finitely supported vectors are dense in `ℓ²`. -/
theorem exists_finsupp_close_lp (x : lp (fun _ : ι => ℂ) 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ι, ‖(∑ i ∈ s, lp.single 2 i (x i)) - x‖ < ε := by
  have h := lp.hasSum_single (E := fun _ : ι => ℂ) (p := 2) (by norm_num) x
  rw [HasSum] at h
  have h2 : ∀ᶠ s in Filter.atTop, dist (∑ i ∈ s, lp.single 2 i (x i)) x < ε :=
    Metric.tendsto_nhds.mp h ε hε
  rw [Filter.eventually_atTop] at h2
  obtain ⟨s₀, hs₀⟩ := h2
  exact ⟨s₀, by simpa [dist_eq_norm] using hs₀ s₀ (le_refl s₀)⟩

end General

/-! ## 2. The phase characters -/

/-- `e^{2πi x}`. -/
def phR (x : ℝ) : ℂ := Complex.exp (↑(2 * Real.pi * x) * Complex.I)

theorem phR_norm (x : ℝ) : ‖phR x‖ = 1 := by
  rw [phR, Complex.norm_exp]
  simp

theorem phR_add (x y : ℝ) : phR (x + y) = phR x * phR y := by
  rw [phR, phR, phR, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phR_zero : phR 0 = 1 := by simp [phR]

theorem phR_neg (x : ℝ) : phR (-x) = (phR x)⁻¹ := by
  have h : phR x * phR (-x) = 1 := by
    rw [← phR_add, add_neg_cancel, phR_zero]
  exact (inv_eq_of_mul_eq_one_right h).symm

/-- `e^{2πi n α}`. -/
def ph (α : ℝ) (n : ℤ) : ℂ := phR ((n : ℝ) * α)

theorem ph_norm (α : ℝ) (n : ℤ) : ‖ph α n‖ = 1 := phR_norm _

theorem ph_add (α : ℝ) (m n : ℤ) : ph α (m + n) = ph α m * ph α n := by
  rw [ph, ph, ph, ← phR_add]
  congr 1
  push_cast
  ring

theorem ph_zero (α : ℝ) : ph α 0 = 1 := by simp [ph, phR_zero]

theorem ph_neg (α : ℝ) (n : ℤ) : ph α (-n) = (ph α n)⁻¹ := by
  rw [ph, ph, ← phR_neg]
  congr 1
  push_cast
  ring

/-! ## 3. The almost Mathieu operator on `ℓ²(ℤ)` -/

/-- The shift `(S f) n = f (n + k)` on `ℓ²(ℤ)`. -/
def shiftZ (k : ℤ) : EllTwo →L[ℂ] EllTwo :=
  coordOp (fun _ => (1 : ℂ)) (Equiv.addRight k) 1 zero_le_one (by intro i; simp)

theorem shiftZ_coord (k : ℤ) (f : EllTwo) (n : ℤ) : shiftZ k f n = f (n + k) := by
  rw [shiftZ, coordOp_coord]
  simp

/-- Diagonal multiplication on `ℓ²(ℤ)`. -/
def diagZ (b : ℤ → ℂ) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ n, ‖b n‖ ≤ K) : EllTwo →L[ℂ] EllTwo :=
  coordOp b (Equiv.refl ℤ) K hK0 hK

theorem diagZ_coord (b : ℤ → ℂ) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ n, ‖b n‖ ≤ K)
    (f : EllTwo) (n : ℤ) : diagZ b K hK0 hK f n = b n * f n := by
  rw [diagZ, coordOp_coord]
  rfl

theorem diagZ_norm_le (b : ℤ → ℂ) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ n, ‖b n‖ ≤ K) :
    ‖diagZ b K hK0 hK‖ ≤ K := coordOp_norm_le _ _ _ _ _

/-- The almost Mathieu potential, as a diagonal operator. -/
def amoPotOp (α lam θ : ℝ) : EllTwo →L[ℂ] EllTwo :=
  diagZ (fun n => ((2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α)) : ℝ) : ℂ))
    (2 * |lam|) (by positivity) (by
      intro n
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc |2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))|
          = |2 * lam| * |Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))| := abs_mul _ _
        _ ≤ |2 * lam| * 1 := by
            gcongr
            exact Real.abs_cos_le_one _
        _ = 2 * |lam| := by rw [abs_mul]; norm_num)

theorem amoPotOp_coord (α lam θ : ℝ) (f : EllTwo) (n : ℤ) :
    amoPotOp α lam θ f n
      = ((2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α)) : ℝ) : ℂ) * f n := by
  rw [amoPotOp, diagZ_coord]

/-- The almost Mathieu operator `(H u) n = u (n+1) + u (n-1) + 2 λ cos 2π(θ + nα) u n`. -/
def amoOp (α lam θ : ℝ) : EllTwo →L[ℂ] EllTwo :=
  shiftZ 1 + shiftZ (-1) + amoPotOp α lam θ

theorem amoOp_coord (α lam θ : ℝ) (f : EllTwo) (n : ℤ) :
    amoOp α lam θ f n = f (n + 1) + f (n - 1)
      + ((2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α)) : ℝ) : ℂ) * f n := by
  have h1 : (shiftZ 1 + shiftZ (-1) + amoPotOp α lam θ) f n
      = shiftZ 1 f n + shiftZ (-1) f n + amoPotOp α lam θ f n := by
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, lp.coeFn_add, lp.coeFn_add]
    rfl
  rw [amoOp, h1, shiftZ_coord, shiftZ_coord, amoPotOp_coord]
  simp only [sub_eq_add_neg]

/-- `amoOp` satisfies the challenge's almost Mathieu coordinate formula. -/
theorem amoOp_isAMO (α lam θ : ℝ) : IsAlmostMathieuOperator α lam θ (amoOp α lam θ) := by
  intro u n
  rw [amoOp_coord]
  norm_num

/-- Uniqueness of the operator with the almost Mathieu coordinate formula. -/
theorem amoOp_unique {α lam θ : ℝ} {H : EllTwo →L[ℂ] EllTwo}
    (hH : IsAlmostMathieuOperator α lam θ H) : H = amoOp α lam θ := by
  refine coord_ext fun f n => ?_
  rw [hH f n, amoOp_coord]
  norm_num

/-- Coordinates of the difference of two almost Mathieu operators. -/
theorem amoOp_sub_coord (α lam θ θ' : ℝ) (f : EllTwo) (n : ℤ) :
    (amoOp α lam θ - amoOp α lam θ') f n =
      ((2 * lam * (Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))
        - Real.cos (2 * Real.pi * (θ' + (n : ℝ) * α))) : ℝ) : ℂ) * f n := by
  rw [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply, amoOp_coord, amoOp_coord]
  push_cast
  ring

/-- The almost Mathieu operator is Lipschitz in the phase. -/
theorem amoOp_norm_sub_le (α lam θ θ' : ℝ) :
    ‖amoOp α lam θ - amoOp α lam θ'‖ ≤ 4 * Real.pi * |lam| * |θ - θ'| := by
  set K : ℝ := 4 * Real.pi * |lam| * |θ - θ'| with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hb : ∀ n : ℤ, ‖((2 * lam * (Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))
      - Real.cos (2 * Real.pi * (θ' + (n : ℝ) * α))) : ℝ) : ℂ)‖ ≤ K := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hcos : |Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))
        - Real.cos (2 * Real.pi * (θ' + (n : ℝ) * α))| ≤ 2 * Real.pi * |θ - θ'| := by
      have h := Real.abs_cos_sub_cos_le (2 * Real.pi * (θ + (n : ℝ) * α))
        (2 * Real.pi * (θ' + (n : ℝ) * α))
      have harg : 2 * Real.pi * (θ + (n : ℝ) * α) - 2 * Real.pi * (θ' + (n : ℝ) * α)
          = 2 * Real.pi * (θ - θ') := by ring
      rwa [harg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)] at h
    calc |2 * lam * (Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))
          - Real.cos (2 * Real.pi * (θ' + (n : ℝ) * α)))|
        = |2 * lam| * |Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))
          - Real.cos (2 * Real.pi * (θ' + (n : ℝ) * α))| := abs_mul _ _
      _ ≤ |2 * lam| * (2 * Real.pi * |θ - θ'|) := by gcongr
      _ = K := by rw [hK, abs_mul]; norm_num; ring
  have hEq : amoOp α lam θ - amoOp α lam θ'
      = coordOp (fun n : ℤ => ((2 * lam * (Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))
          - Real.cos (2 * Real.pi * (θ' + (n : ℝ) * α))) : ℝ) : ℂ)) (Equiv.refl ℤ) K hK0 hb := by
    refine coord_ext fun f n => ?_
    rw [amoOp_sub_coord, coordOp_coord]
    rfl
  rw [hEq]
  exact coordOp_norm_le _ _ _ _ _

/-! ## 4. The suspension operator on `ℓ²(ℤ × ℤ)` and the twist -/

/-- `ℓ²(ℤ × ℤ)`: the first index is the phase (Fourier) mode, the second the site. -/
abbrev EllTwo2 : Type := lp (fun _ : ℤ × ℤ => ℂ) 2

/-- `(m, n) ↦ (m, n + k)`. -/
def shiftSnd (k : ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1, p.2 + k)
  invFun p := (p.1, p.2 - k)
  left_inv p := by simp
  right_inv p := by simp

/-- `(m, n) ↦ (m + k, n)`. -/
def shiftFst (k : ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 + k, p.2)
  invFun p := (p.1 - k, p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- The coordinate swap `(m, n) ↦ (n, -m)` implementing the Aubry twist. -/
def twistEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.2, -p.1)
  invFun p := (-p.2, p.1)
  left_inv p := by simp
  right_inv p := by simp

@[simp] theorem twistEquiv_apply (p : ℤ × ℤ) : twistEquiv p = (p.2, -p.1) := rfl
@[simp] theorem twistEquiv_symm_apply (p : ℤ × ℤ) : twistEquiv.symm p = (-p.2, p.1) := rfl
@[simp] theorem shiftSnd_apply (k : ℤ) (p : ℤ × ℤ) : shiftSnd k p = (p.1, p.2 + k) := rfl
@[simp] theorem shiftFst_apply (k : ℤ) (p : ℤ × ℤ) : shiftFst k p = (p.1 + k, p.2) := rfl

/-- Shift in the site index: `(T f) (m,n) = f (m, n+1)`. -/
def s2Sh : EllTwo2 →L[ℂ] EllTwo2 :=
  coordOp (fun _ => (1 : ℂ)) (shiftSnd 1) 1 zero_le_one (by intro p; simp)

theorem s2Sh_coord (f : EllTwo2) (m n : ℤ) : s2Sh f (m, n) = f (m, n + 1) := by
  rw [s2Sh, coordOp_coord]
  simp only [shiftSnd_apply, one_mul]

/-- Backward site shift. -/
def s2Sh' : EllTwo2 →L[ℂ] EllTwo2 :=
  coordOp (fun _ => (1 : ℂ)) (shiftSnd (-1)) 1 zero_le_one (by intro p; simp)

theorem s2Sh'_coord (f : EllTwo2) (m n : ℤ) : s2Sh' f (m, n) = f (m, n - 1) := by
  rw [s2Sh', coordOp_coord]
  simp only [shiftSnd_apply, sub_eq_add_neg, one_mul]

/-- The potential term `λ e^{2πiαn} f (m-1, n)`. -/
def s2P (α lam : ℝ) : EllTwo2 →L[ℂ] EllTwo2 :=
  coordOp (fun p => (lam : ℂ) * ph α p.2) (shiftFst (-1)) |lam| (abs_nonneg _) (by
    intro p
    rw [norm_mul, ph_norm, mul_one, Complex.norm_real, Real.norm_eq_abs])

theorem s2P_coord (α lam : ℝ) (f : EllTwo2) (m n : ℤ) :
    s2P α lam f (m, n) = (lam : ℂ) * ph α n * f (m - 1, n) := by
  rw [s2P, coordOp_coord]
  simp only [shiftFst_apply, sub_eq_add_neg]

/-- The potential term `λ e^{-2πiαn} f (m+1, n)`. -/
def s2M (α lam : ℝ) : EllTwo2 →L[ℂ] EllTwo2 :=
  coordOp (fun p => (lam : ℂ) * ph α (-(p.2))) (shiftFst 1) |lam| (abs_nonneg _) (by
    intro p
    rw [norm_mul, ph_norm, mul_one, Complex.norm_real, Real.norm_eq_abs])

theorem s2M_coord (α lam : ℝ) (f : EllTwo2) (m n : ℤ) :
    s2M α lam f (m, n) = (lam : ℂ) * ph α (-n) * f (m + 1, n) := by
  rw [s2M, coordOp_coord]
  simp only [shiftFst_apply]

/-- The suspension of the almost Mathieu cocycle: the operator on `ℓ²(ℤ × ℤ)` whose
"fibrations" are the almost Mathieu operators at all phases. -/
def suspA (α lam : ℝ) : EllTwo2 →L[ℂ] EllTwo2 :=
  s2Sh + s2Sh' + s2P α lam + s2M α lam

theorem suspA_coord (α lam : ℝ) (f : EllTwo2) (m n : ℤ) :
    suspA α lam f (m, n) = f (m, n + 1) + f (m, n - 1)
      + (lam : ℂ) * ph α n * f (m - 1, n) + (lam : ℂ) * ph α (-n) * f (m + 1, n) := by
  have h1 : (s2Sh + s2Sh' + s2P α lam + s2M α lam) f (m, n)
      = s2Sh f (m, n) + s2Sh' f (m, n) + s2P α lam f (m, n) + s2M α lam f (m, n) := by
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.add_apply, lp.coeFn_add, lp.coeFn_add, lp.coeFn_add]
    rfl
  rw [suspA, h1, s2Sh_coord, s2Sh'_coord, s2P_coord, s2M_coord]

/-- The suspension preserves the site-localised support: a vector supported in the
`m`-interval `[a, a + N - 1]` is mapped into `[a - 1, a + N]`. -/
theorem suspA_support (α lam : ℝ) (f : EllTwo2) (a : ℤ) (N : ℕ) (hN : 0 < N)
    (hf : ∀ p : ℤ × ℤ, f p ≠ 0 → p.1 ∈ Set.Icc a (a + (N : ℤ) - 1)) :
    ∀ p : ℤ × ℤ, suspA α lam f p ≠ 0 → p.1 ∈ Set.Icc (a - 1) (a + (N : ℤ)) := by
  intro p hp
  obtain ⟨m, n⟩ := p
  rw [suspA_coord] at hp
  have h1 : f (m, n + 1) ≠ 0 ∨ f (m, n - 1) ≠ 0 ∨ f (m - 1, n) ≠ 0 ∨ f (m + 1, n) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hp (by rw [h.1, h.2.1, h.2.2.1, h.2.2.2]; ring)
  rcases h1 with h | h | h | h
  · have hh := hf _ h; simp only [Set.mem_Icc] at hh ⊢; omega
  · have hh := hf _ h; simp only [Set.mem_Icc] at hh ⊢; omega
  · have hh := hf _ h; simp only [Set.mem_Icc] at hh ⊢; omega
  · have hh := hf _ h; simp only [Set.mem_Icc] at hh ⊢; omega

/-- The Aubry twist `(U f) (m,n) = e^{2πiαmn} f (n, -m)`. -/
def twistU (α : ℝ) : EllTwo2 →L[ℂ] EllTwo2 :=
  coordOp (fun p => ph α (p.1 * p.2)) twistEquiv 1 zero_le_one (by intro p; rw [ph_norm])

theorem twistU_coord (α : ℝ) (f : EllTwo2) (m n : ℤ) :
    twistU α f (m, n) = ph α (m * n) * f (n, -m) := by
  rw [twistU, coordOp_coord]
  simp only [twistEquiv_apply]

/-- The inverse twist. -/
def twistUinv (α : ℝ) : EllTwo2 →L[ℂ] EllTwo2 :=
  coordOp (fun p => ph α (p.1 * p.2)) twistEquiv.symm 1 zero_le_one (by intro p; rw [ph_norm])

theorem twistUinv_coord (α : ℝ) (f : EllTwo2) (m n : ℤ) :
    twistUinv α f (m, n) = ph α (m * n) * f (-n, m) := by
  rw [twistUinv, coordOp_coord]
  simp only [twistEquiv_symm_apply]

/-! ## 5. The twisted partial Fourier sums and block vectors -/

/-- The twisted partial Fourier sum of a vector, computed over the finset `s` (which is meant
to contain the support of `v`): coordinates `Σ_m e^{2πi m ϑ} v (m,n)`. -/
def fibVec (ϑ : ℝ) (v : ℤ × ℤ → ℂ) (s : Finset (ℤ × ℤ)) : EllTwo :=
  ⟨fun n => ∑ p ∈ s.filter (fun p => p.2 = n), phR ((p.1 : ℝ) * ϑ) * v p, by
    refine memℓp_gen ?_
    refine summable_of_ne_finset_zero (s := s.image (fun p => p.2)) ?_
    intro n hn
    have hz : (∑ p ∈ s.filter (fun p => p.2 = n), phR ((p.1 : ℝ) * ϑ) * v p) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_filter] at hp
      exact absurd (hp.2 ▸ Finset.mem_image_of_mem (fun p : ℤ × ℤ => p.2) hp.1) hn
    rw [hz]
    simp⟩

theorem fibVec_coord (ϑ : ℝ) (v : ℤ × ℤ → ℂ) (s : Finset (ℤ × ℤ)) (n : ℤ) :
    fibVec ϑ v s n = ∑ p ∈ s.filter (fun p => p.2 = n), phR ((p.1 : ℝ) * ϑ) * v p := rfl

/-- `fibVec` only depends on the values of `v` on `s`. -/
theorem fibVec_congr (ϑ : ℝ) (v w : ℤ × ℤ → ℂ) (s : Finset (ℤ × ℤ))
    (hvw : ∀ p ∈ s, v p = w p) : fibVec ϑ v s = fibVec ϑ w s := by
  refine lp.ext ?_
  funext n
  rw [fibVec_coord, fibVec_coord]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hvw p (Finset.mem_filter.mp hp).1]

/-- The "block" vector: `u` repeated on `m ∈ [0, N)`, scaled by `1/N`. -/
def blockVec (u : ℤ → ℂ) (s : Finset ℤ) (N : ℕ) : EllTwo2 :=
  ⟨fun p => if 0 ≤ p.1 ∧ p.1 < (N : ℤ) ∧ p.2 ∈ s then u p.2 / (N : ℂ) else 0, by
    refine memℓp_gen ?_
    refine summable_of_ne_finset_zero (s := (Finset.Ico 0 (N : ℤ)) ×ˢ s) ?_
    intro p hp
    have hp' : ¬ (0 ≤ p.1 ∧ p.1 < (N : ℤ) ∧ p.2 ∈ s) := by
      intro h
      exact hp (Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩)
    rw [if_neg hp']
    simp⟩

theorem blockVec_coord (u : ℤ → ℂ) (s : Finset ℤ) (N : ℕ) (m n : ℤ) :
    blockVec u s N (m, n) = if 0 ≤ m ∧ m < (N : ℤ) ∧ n ∈ s then u n / (N : ℂ) else 0 := rfl

end Work.TMComp.Duality
