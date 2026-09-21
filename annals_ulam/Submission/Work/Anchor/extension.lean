import Mathlib
import Submission.Work.OddEnvelope.Defs
import Submission.Work.Anchor.flat_glue
import Submission.Work.Anchor.borel_series

namespace Work.Anchor

open Set Filter
open scoped Topology ContDiff Pointwise

noncomputable section

/-- The scaling of `η₁`. -/
def T1 : ℝ := 11 / 20
/-- The scale of the oscillation in `η₂`. -/
def e2 : ℝ := 1 / 10

lemma T1_pos : 0 < T1 := by norm_num [T1]
lemma e2_pos : 0 < e2 := by norm_num [e2]

def i1 : ℝ → ℝ := fun x => x / T1
def i2 : ℝ → ℝ := Real.sinh ∘ i1
def i3 : ℝ → ℝ := Real.arctan ∘ i2

def eta0 : ℝ → ℝ := fun _ => 1
def eta1 : ℝ → ℝ := fun u => T1 * i3 u
def eta2 : ℝ → ℝ := fun u => e2 ^ 2 * (1 - Real.cos (u / e2))

@[simp] lemma i1_apply (u : ℝ) : i1 u = u / T1 := rfl
@[simp] lemma i2_apply (u : ℝ) : i2 u = Real.sinh (u / T1) := rfl
@[simp] lemma i3_apply (u : ℝ) : i3 u = Real.arctan (Real.sinh (u / T1)) := rfl
@[simp] lemma eta0_apply (u : ℝ) : eta0 u = 1 := rfl

lemma i1_eq : i1 = fun x : ℝ => x / T1 := rfl
lemma i2_eq : i2 = Real.sinh ∘ i1 := rfl
lemma i3_eq : i3 = Real.arctan ∘ i2 := rfl
lemma eta1_eq : eta1 = fun u : ℝ => T1 * i3 u := rfl

lemma diff_i1 (u : ℝ) : DifferentiableAt ℝ i1 u := by
  rw [i1_eq]; fun_prop
lemma diff_i2 (u : ℝ) : DifferentiableAt ℝ i2 u := by
  rw [i2_eq]; exact (Real.differentiable_sinh.differentiableAt).comp u (diff_i1 u)
lemma diff_i3 (u : ℝ) : DifferentiableAt ℝ i3 u := by
  rw [i3_eq]; exact (Real.differentiable_arctan.differentiableAt).comp u (diff_i2 u)

lemma deriv_i1 (u : ℝ) : deriv i1 u = 1 / T1 := by
  rw [i1_eq, deriv_div_const]; simp
lemma deriv_i2 (u : ℝ) : deriv i2 u = Real.cosh (u / T1) * (1 / T1) := by
  rw [i2_eq, deriv_comp (𝕜 := ℝ) (𝕜' := ℝ) (h₂ := Real.sinh) (h := i1)
    (hh₂ := Real.differentiable_sinh.differentiableAt) (hh := diff_i1 u)]
  rw [Real.deriv_sinh, deriv_i1]
  simp [i1]
lemma deriv_i3 (u : ℝ) :
    deriv i3 u = 1 / (1 + (Real.sinh (u / T1)) ^ 2) * (Real.cosh (u / T1) * (1 / T1)) := by
  rw [i3_eq, deriv_comp (𝕜 := ℝ) (𝕜' := ℝ) (h₂ := Real.arctan) (h := i2)
    (hh₂ := Real.differentiable_arctan.differentiableAt) (hh := diff_i2 u)]
  rw [Real.deriv_arctan, deriv_i2]
  simp [i2]

lemma cosh_sq_eq (u : ℝ) : 1 + (Real.sinh (u / T1)) ^ 2 = (Real.cosh (u / T1)) ^ 2 := by
  have := Real.cosh_sq_sub_sinh_sq (u / T1)
  linarith

lemma deriv_eta1 (u : ℝ) : deriv eta1 u = 1 / Real.cosh (u / T1) := by
  have h : deriv eta1 u =
      T1 * (1 / (1 + (Real.sinh (u / T1)) ^ 2) * (Real.cosh (u / T1) * (1 / T1))) := by
    rw [eta1_eq, deriv_const_mul _ (diff_i3 u), deriv_i3]
  rw [h, cosh_sq_eq]
  have hc : Real.cosh (u / T1) ≠ 0 := (Real.cosh_pos _).ne'
  field_simp
  exact div_self T1_pos.ne'

lemma cosh_pos' (u : ℝ) : 0 < Real.cosh (u / T1) := Real.cosh_pos _

lemma abs_deriv_eta1_le (u : ℝ) : |deriv eta1 u| ≤ 1 := by
  rw [deriv_eta1, abs_div, abs_one, abs_of_pos (cosh_pos' u)]
  rw [div_le_one (cosh_pos' u)]
  exact Real.one_le_cosh _

/-! ### The second derivative of `η₁` -/

def iv : ℝ → ℝ := fun x => x⁻¹
def csh : ℝ → ℝ := Real.cosh ∘ i1
def dEta1 : ℝ → ℝ := iv ∘ csh

lemma iv_eq : iv = fun x : ℝ => x⁻¹ := rfl
lemma csh_eq : csh = Real.cosh ∘ i1 := rfl
lemma dEta1_eq : dEta1 = iv ∘ csh := rfl

lemma diff_iv (x : ℝ) (hx : x ≠ 0) : DifferentiableAt ℝ iv x := by
  rw [iv_eq]; exact differentiableAt_inv hx
lemma diff_csh (u : ℝ) : DifferentiableAt ℝ csh u := by
  rw [csh_eq]; exact (Real.differentiable_cosh.differentiableAt).comp u (diff_i1 u)

lemma csh_ne (u : ℝ) : csh u ≠ 0 := by
  rw [csh_eq]; simp only [Function.comp_apply, i1_apply]; exact (Real.cosh_pos _).ne'

lemma deriv_csh (u : ℝ) : deriv csh u = Real.sinh (u / T1) * (1 / T1) := by
  rw [csh_eq, deriv_comp (𝕜 := ℝ) (𝕜' := ℝ) (h₂ := Real.cosh) (h := i1)
    (hh₂ := Real.differentiable_cosh.differentiableAt) (hh := diff_i1 u)]
  rw [Real.deriv_cosh, deriv_i1]
  simp [i1]

lemma deriv_dEta1 (u : ℝ) :
    deriv dEta1 u = -((Real.cosh (u / T1)) ^ 2)⁻¹ * (Real.sinh (u / T1) * (1 / T1)) := by
  rw [dEta1_eq, deriv_comp (𝕜 := ℝ) (𝕜' := ℝ) (h₂ := iv) (h := csh)
    (hh₂ := diff_iv _ (csh_ne u)) (hh := diff_csh u)]
  rw [iv_eq, deriv_inv, deriv_csh]
  simp [csh, i1]

lemma deriv_deriv_eta1 (u : ℝ) :
    deriv (deriv eta1) u = -((Real.cosh (u / T1)) ^ 2)⁻¹ * (Real.sinh (u / T1) * (1 / T1)) := by
  have h : deriv eta1 = dEta1 := by
    funext v
    rw [deriv_eta1]
    simp [dEta1, iv, csh, i1]
  rw [h, deriv_dEta1]

lemma iteratedDeriv_two_eta1 : iteratedDeriv 2 eta1 0 = 0 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_deriv_eta1]
  simp

lemma abs_deriv_deriv_eta1_le (u : ℝ) : |deriv (deriv eta1) u| ≤ 1 / (2 * T1) := by
  rw [deriv_deriv_eta1]
  set c := Real.cosh (u / T1) with hc
  set s := Real.sinh (u / T1) with hs
  have hc0 : 0 < c := Real.cosh_pos _
  have hsq : 1 + s ^ 2 = c ^ 2 := cosh_sq_eq u
  have h1 : |s| / c ^ 2 ≤ 1/2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg s, sq_abs s, sq_nonneg (|s| - 1)]
  have h2 : |c ^ 2|⁻¹ * (|s| * |1/T1|) ≤ 1/(2*T1) := by
    have hc2 : (0:ℝ) < c^2 := by positivity
    have hT : (0:ℝ) < T1 := T1_pos
    have hTinv : (0:ℝ) < 1/T1 := by positivity
    rw [abs_of_pos hc2, abs_of_pos hTinv]
    have step : (c^2)⁻¹ * (|s| * (1/T1)) = (|s| / c^2) * (1/T1) := by field_simp
    rw [step]
    calc (|s| / c^2) * (1/T1) ≤ (1/2) * (1/T1) :=
          mul_le_mul_of_nonneg_right h1 hTinv.le
      _ = 1/(2*T1) := by ring
  calc |-(c^2)⁻¹ * (s * (1/T1))| = |c^2|⁻¹ * (|s| * |1/T1|) := by
        rw [abs_mul, abs_mul, abs_neg, abs_inv, abs_pow]
    _ ≤ 1/(2*T1) := h2

/-! ### `η₂` -/

def co2 : ℝ → ℝ := Real.cos ∘ (fun x : ℝ => x / e2)
def si2 : ℝ → ℝ := Real.sin ∘ (fun x : ℝ => x / e2)
def co2' : ℝ → ℝ := fun u => e2 ^ 2 * (1 - co2 u)

lemma co2_eq : co2 = Real.cos ∘ (fun x : ℝ => x / e2) := rfl

lemma diff_co2 (u : ℝ) : DifferentiableAt ℝ co2 u := by
  rw [co2_eq]; exact (Real.differentiable_cos.differentiableAt).comp u (by fun_prop)

lemma deriv_co2 (u : ℝ) : deriv co2 u = -Real.sin (u / e2) * (1 / e2) := by
  rw [co2_eq, deriv_comp (𝕜 := ℝ) (𝕜' := ℝ) (h₂ := Real.cos) (h := fun x : ℝ => x / e2)
    (hh₂ := Real.differentiable_cos.differentiableAt) (hh := by fun_prop)]
  rw [Real.deriv_cos, deriv_div_const]
  simp

lemma eta2_eq' : eta2 = co2' := rfl

lemma deriv_eta2 (u : ℝ) : deriv eta2 u = e2 * Real.sin (u / e2) := by
  have h : eta2 = co2' := rfl
  rw [h]
  unfold co2'
  rw [deriv_const_mul]
  · rw [deriv_const_sub (1 : ℝ), deriv_co2]; field_simp
  · exact (differentiableAt_const _).sub (diff_co2 u)

lemma deriv_deriv_eta2 (u : ℝ) : deriv (deriv eta2) u = Real.cos (u / e2) := by
  have h : deriv eta2 = fun u => e2 * si2 u := by
    funext v; rw [deriv_eta2]; simp [si2]
  rw [h]
  rw [deriv_const_mul]
  · rw [show si2 = Real.sin ∘ (fun x : ℝ => x / e2) from rfl,
      deriv_comp (𝕜 := ℝ) (𝕜' := ℝ) (h₂ := Real.sin) (h := fun x : ℝ => x / e2)
      (hh₂ := Real.differentiable_sin.differentiableAt) (hh := by fun_prop)]
    rw [Real.deriv_sin, deriv_div_const]
    simp only [deriv_id'']
    field_simp [e2_pos.ne']
  · rw [show si2 = Real.sin ∘ (fun x : ℝ => x / e2) from rfl]
    exact (Real.differentiable_sin.differentiableAt).comp u (by fun_prop)

lemma eta2_zero : eta2 0 = 0 := by simp [eta2]
lemma deriv_eta2_zero : deriv eta2 0 = 0 := by rw [deriv_eta2]; simp
lemma iteratedDeriv_two_eta2 : iteratedDeriv 2 eta2 0 = 1 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_deriv_eta2]; simp

lemma abs_eta2_le (u : ℝ) : |eta2 u| ≤ 2 * e2 ^ 2 := by
  have h : eta2 u = e2 ^ 2 * (1 - Real.cos (u / e2)) := rfl
  rw [h, abs_mul]
  have h2 : |1 - Real.cos (u / e2)| ≤ 2 := by
    rw [abs_le]
    constructor
    · linarith [Real.cos_le_one (u / e2)]
    · linarith [Real.neg_one_le_cos (u / e2)]
  have h3 : |e2 ^ 2| = e2 ^ 2 := abs_of_nonneg (by positivity)
  rw [h3]
  nlinarith [h2, sq_nonneg e2, e2_pos]
lemma abs_deriv_eta2_le (u : ℝ) : |deriv eta2 u| ≤ e2 := by
  rw [deriv_eta2, abs_mul, abs_of_nonneg e2_pos.le]
  nlinarith [Real.abs_sin_le_one (u / e2), e2_pos]
lemma abs_deriv_deriv_eta2_le (u : ℝ) : |deriv (deriv eta2) u| ≤ 1 := by
  rw [deriv_deriv_eta2]; simpa using Real.abs_cos_le_one (u / e2)

/-! ### `η₀` -/

lemma iteratedDeriv_eta0 : iteratedDeriv 0 eta0 0 = 1 ∧ iteratedDeriv 1 eta0 0 = 0 ∧
    iteratedDeriv 2 eta0 0 = 0 := by
  have hd : deriv eta0 = fun _ => 0 := by
    funext v
    show deriv (fun _ : ℝ => (1:ℝ)) v = (fun _ : ℝ => (0:ℝ)) v
    rw [deriv_const]
  refine ⟨?_, ?_, ?_⟩
  · rw [iteratedDeriv_zero, eta0]
  · rw [iteratedDeriv_one, hd]
  · rw [iteratedDeriv_succ, iteratedDeriv_one, hd]; simp

lemma abs_eta0_le (u : ℝ) : |eta0 u| ≤ 1 := by simp [eta0]
lemma deriv_eta0_eq : deriv eta0 = fun _ => 0 := by
  funext v
  show deriv (fun _ : ℝ => (1:ℝ)) v = (fun _ : ℝ => (0:ℝ)) v
  rw [deriv_const]
lemma abs_deriv_eta0_le (u : ℝ) : |deriv eta0 u| ≤ 0 := by
  rw [deriv_eta0_eq]; simp
lemma abs_deriv_deriv_eta0_le (u : ℝ) : |deriv (deriv eta0) u| ≤ 0 := by
  rw [deriv_eta0_eq]
  show |deriv (fun _ : ℝ => (0:ℝ)) u| ≤ 0
  rw [deriv_const]; simp

lemma eta1_zero : eta1 0 = 0 := by simp [eta1, i3, i2, i1]
lemma deriv_eta1_zero : deriv eta1 0 = 1 := by rw [deriv_eta1]; simp
/-! ## Smoothness of `profileX`, and the `η`-bounds used by the assembly -/

lemma contDiff_profileX : ContDiff ℝ (⊤ : ℕ∞) Work.OddEnvelope.profileX := by
  unfold Work.OddEnvelope.profileX
  refine ContDiff.div contDiff_const (ContDiff.sqrt (contDiff_const.add (contDiff_id.pow 2)) ?_) ?_
  · intro x
    positivity
  · intro x
    exact (Real.sqrt_pos.mpr (by positivity)).ne'

/-- `|i₃ u| ≤ π/2`. -/
lemma abs_i3_le (u : ℝ) : |i3 u| ≤ Real.pi / 2 := by
  rw [i3_apply, abs_le]
  exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _), le_of_lt (Real.arctan_lt_pi_div_two _)⟩

/-- `|η₁ u| ≤ T₁ · π/2`. -/
lemma abs_eta1_le (u : ℝ) : |eta1 u| ≤ T1 * (Real.pi / 2) := by
  rw [eta1_eq]
  rw [abs_mul, abs_of_nonneg T1_pos.le]
  exact mul_le_mul_of_nonneg_left (abs_i3_le u) T1_pos.le

/-- The numerical bound `T₁ · π/2 ≤ 87/100`. -/
lemma T1_mul_pi_div_two_le : T1 * (Real.pi / 2) ≤ 87 / 100 := by
  have h2 : T1 * (Real.pi / 2) < T1 * (3.1416 / 2) := by
    refine mul_lt_mul_of_pos_left ?_ T1_pos
    linarith [Real.pi_lt_d4]
  have h3 : T1 * (3.1416 / 2) ≤ 87 / 100 := by norm_num [T1]
  linarith

/-! ## General analytic tools -/

/-- `iteratedDeriv 2 g = deriv (deriv g)`, as a function. -/
lemma iteratedDeriv_two_eq (g : ℝ → ℝ) : iteratedDeriv 2 g = deriv (deriv g) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- `iteratedDerivWithin 2 g s = derivWithin (derivWithin g s) s`, as a function. -/
lemma iteratedDerivWithin_two_eq (g : ℝ → ℝ) (s : Set ℝ) :
    iteratedDerivWithin 2 g s = derivWithin (derivWithin g s) s := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ', iteratedDerivWithin_one]

/-- The derivative of a `C^∞` function is differentiable. -/
lemma differentiable_deriv_of_contDiff {g : ℝ → ℝ} (h : ContDiff ℝ (⊤ : ℕ∞) g) :
    Differentiable ℝ (deriv g) := by
  rw [← iteratedDeriv_one]
  exact h.differentiable_iteratedDeriv 1 (natCast_lt_topE 1)

/-- Smoothness of `x ↦ g (x - a)`. -/
lemma contDiff_comp_sub_const {g : ℝ → ℝ} (a : ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => g (x - a)) :=
  hg.comp (contDiff_id.sub contDiff_const)

/-- The chain rule for a translation. -/
lemma deriv_comp_sub_const (g : ℝ → ℝ) (x a : ℝ) (hg : DifferentiableAt ℝ g (x - a)) :
    deriv (fun y : ℝ => g (y - a)) x = deriv g (x - a) := by
  have h1 : HasDerivAt (fun y : ℝ => y - a) 1 x := (hasDerivAt_id x).sub_const a
  have h2 : HasDerivAt (g ∘ fun y : ℝ => y - a) (deriv g (x - a) * 1) x :=
    hg.hasDerivAt.comp x h1
  have h3 : deriv (g ∘ fun y : ℝ => y - a) x = deriv g (x - a) * 1 := h2.deriv
  show deriv (g ∘ fun y : ℝ => y - a) x = deriv g (x - a)
  rw [h3]; ring

/-- The chain rule for a translation, applied to the derivative. -/
lemma deriv_deriv_comp_sub_const (g : ℝ → ℝ) (x a : ℝ)
    (hdg : Differentiable ℝ (deriv g)) :
    deriv (fun y : ℝ => deriv g (y - a)) x = deriv (deriv g) (x - a) :=
  deriv_comp_sub_const (deriv g) x a (hdg.differentiableAt)

/-- The translate of the derivative is differentiable. -/
lemma differentiableAt_deriv_shift {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x a : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => deriv g (y - a)) x :=
  ((differentiable_deriv_of_contDiff hg).differentiableAt).comp x
    ((differentiableAt_id (x := x)).sub_const a)

/-- A `C^∞` function is differentiable. -/
lemma differentiable_of_contDiff {g : ℝ → ℝ} (h : ContDiff ℝ (⊤ : ℕ∞) g) :
    Differentiable ℝ g := h.differentiable (by simp)

/-- A `C^∞` function is differentiable at every point. -/
lemma differentiableAt_of_contDiff {g : ℝ → ℝ} (h : ContDiff ℝ (⊤ : ℕ∞) g) (x : ℝ) :
    DifferentiableAt ℝ g x := (differentiable_of_contDiff h).differentiableAt

/-- Smoothness of `x ↦ D (x - a)`, in the form of a `ContDiffOn` statement. -/
lemma contDiffOn_comp_sub_const {g : ℝ → ℝ} (a : ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => g (x - a)) (Set.Ici a) :=
  (contDiff_comp_sub_const a hg).contDiffOn

/-- On `[a,∞)` the derivative of a `C^∞` function agreeing with `f` there is the one-sided
derivative of `f`. -/
lemma deriv_eq_derivWithin_of_contDiff_eqOn {F f : ℝ → ℝ} (a : ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (heq : Set.EqOn F f (Set.Ici a)) :
    ∀ x : ℝ, a ≤ x → deriv F x = derivWithin f (Set.Ici a) x := by
  intro x hx
  have h1 : iteratedDerivWithin 1 F (Set.Ici a) x = iteratedDeriv 1 F x :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici a)
      (hF.contDiffAt.of_le (natCast_le_topE 1)) hx
  have h2 : iteratedDerivWithin 1 F (Set.Ici a) x = iteratedDerivWithin 1 f (Set.Ici a) x :=
    iteratedDerivWithin_congr (n := 1) heq hx
  calc deriv F x = iteratedDeriv 1 F x := by rw [iteratedDeriv_one]
    _ = iteratedDerivWithin 1 F (Set.Ici a) x := h1.symm
    _ = iteratedDerivWithin 1 f (Set.Ici a) x := h2
    _ = derivWithin f (Set.Ici a) x := by rw [iteratedDerivWithin_one]

/-- The same statement one order higher. -/
lemma deriv_deriv_eq_derivWithin_of_contDiff_eqOn {F f : ℝ → ℝ} (a : ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (heq : Set.EqOn F f (Set.Ici a)) :
    ∀ x : ℝ, a ≤ x → deriv (deriv F) x
      = derivWithin (derivWithin f (Set.Ici a)) (Set.Ici a) x := by
  intro x hx
  have h1 : iteratedDerivWithin 2 F (Set.Ici a) x = iteratedDeriv 2 F x :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici a)
      (hF.contDiffAt.of_le (natCast_le_topE 2)) hx
  have h2 : iteratedDerivWithin 2 F (Set.Ici a) x = iteratedDerivWithin 2 f (Set.Ici a) x :=
    iteratedDerivWithin_congr (n := 2) heq hx
  calc deriv (deriv F) x = iteratedDeriv 2 F x := by rw [iteratedDeriv_two_eq]
    _ = iteratedDerivWithin 2 F (Set.Ici a) x := h1.symm
    _ = iteratedDerivWithin 2 f (Set.Ici a) x := h2
    _ = derivWithin (derivWithin f (Set.Ici a)) (Set.Ici a) x := by
        rw [iteratedDerivWithin_two_eq]

/-- `a +ᵥ [0,∞) = [a,∞)`. -/
lemma vadd_Ici_zero (a : ℝ) : a +ᵥ Set.Ici (0 : ℝ) = Set.Ici a := by
  ext x
  rw [Set.mem_vadd_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Set.mem_Ici] at hy ⊢
    rw [vadd_eq_add]
    linarith
  · intro hx
    refine ⟨x - a, ?_, ?_⟩
    · rw [Set.mem_Ici] at hx
      rw [Set.mem_Ici]
      linarith
    · rw [vadd_eq_add]; ring

/-- One-sided derivatives are invariant under a translation. -/
lemma iteratedDerivWithin_translate (g : ℝ → ℝ) (a : ℝ) (k : ℕ) :
    iteratedDerivWithin k (fun u : ℝ => g (a + u)) (Set.Ici 0) 0
      = iteratedDerivWithin k g (Set.Ici a) a := by
  have h := congrFun (iteratedDerivWithin_comp_const_add (𝕜 := ℝ) (F := ℝ) (f := g)
    (s := Set.Ici (0 : ℝ)) (n := k) a) 0
  rw [vadd_Ici_zero, add_zero] at h
  exact h

/-- The one-sided jets of `x ↦ D (x - a)` at `a` are the jets of `D` at `0`. -/
lemma iteratedDerivWithin_sub_const {D : ℝ → ℝ} (a : ℝ) (k : ℕ)
    (hD : ContDiff ℝ (⊤ : ℕ∞) D) :
    iteratedDerivWithin k (fun x : ℝ => D (x - a)) (Set.Ici a) a = iteratedDeriv k D 0 := by
  have h := iteratedDerivWithin_translate (fun x : ℝ => D (x - a)) a k
  have hfun : (fun u : ℝ => (fun x : ℝ => D (x - a)) (a + u)) = D := by
    funext u
    show D (a + u - a) = D u
    rw [show a + u - a = u from by ring]
  rw [hfun] at h
  have h2 : iteratedDerivWithin k D (Set.Ici 0) 0 = iteratedDeriv k D 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0)
      (hD.contDiffAt.of_le (natCast_le_topE k)) (by simp)
  rw [← h, h2]

/-! ## The right jets of `f - profileX` at `a` -/

/-- The `k`-th right jet of `f - profileX` at `a`. -/
def bJet (f : ℝ → ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  iteratedDerivWithin k f (Set.Ici a) a - iteratedDeriv k Work.OddEnvelope.profileX a

lemma abs_bJet_zero_le (f : ℝ → ℝ) (a : ℝ)
    (h0 : ∀ s : ℝ, a ≤ s → |f s - Work.OddEnvelope.profileX s| ≤ 1 / 200) :
    |bJet f a 0| ≤ 1 / 200 := by
  have h := h0 a le_rfl
  simpa only [bJet, iteratedDerivWithin_zero, iteratedDeriv_zero] using h

lemma abs_bJet_one_le (f : ℝ → ℝ) (a : ℝ)
    (h1 : ∀ s : ℝ, a ≤ s →
      |derivWithin f (Set.Ici a) s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 200) :
    |bJet f a 1| ≤ 1 / 200 := by
  have h := h1 a le_rfl
  simpa only [bJet, iteratedDerivWithin_one, iteratedDeriv_one] using h

lemma abs_bJet_two_le (f : ℝ → ℝ) (a : ℝ)
    (h2 : ∀ s : ℝ, a ≤ s → |derivWithin (derivWithin f (Set.Ici a)) (Set.Ici a) s
        - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 200) :
    |bJet f a 2| ≤ 1 / 200 := by
  have h := h2 a le_rfl
  rw [show bJet f a 2 = derivWithin (derivWithin f (Set.Ici a)) (Set.Ici a) a
        - deriv (deriv Work.OddEnvelope.profileX) a from by
      rw [bJet, iteratedDerivWithin_two_eq, iteratedDeriv_two_eq]]
  exact h

/-! ## The finite jet-matching part `Dlow` -/

/-- The polynomial-type part of the extension: a combination of the three model functions
`η₀, η₁, η₂` whose jets at `0` are `(1,0,0)`, `(0,1,0)`, `(0,0,1)`. -/
def Dlow (b0 b1 b2 : ℝ) : ℝ → ℝ :=
  fun u => b0 * eta0 u + b1 * eta1 u + b2 * eta2 u

@[simp] lemma Dlow_apply (b0 b1 b2 u : ℝ) :
    Dlow b0 b1 b2 u = b0 * eta0 u + b1 * eta1 u + b2 * eta2 u := rfl

lemma contDiff_i1 : ContDiff ℝ (⊤ : ℕ∞) i1 := by
  rw [i1_eq]
  exact contDiff_id.div_const T1

lemma contDiff_i2 : ContDiff ℝ (⊤ : ℕ∞) i2 := by
  rw [i2_eq]
  exact Real.contDiff_sinh.comp contDiff_i1

lemma contDiff_i3 : ContDiff ℝ (⊤ : ℕ∞) i3 := by
  rw [i3_eq]
  exact Real.contDiff_arctan.comp contDiff_i2

lemma contDiff_eta0 : ContDiff ℝ (⊤ : ℕ∞) eta0 := contDiff_const

lemma contDiff_eta1 : ContDiff ℝ (⊤ : ℕ∞) eta1 := by
  rw [eta1_eq]
  exact (contDiff_const (c := T1)).mul contDiff_i3

lemma contDiff_eta2 : ContDiff ℝ (⊤ : ℕ∞) eta2 := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => u / e2) := contDiff_id.div_const e2
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Real.cos (u / e2)) := Real.contDiff_cos.comp h1
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => 1 - Real.cos (u / e2)) :=
    (contDiff_const (c := (1 : ℝ))).sub h2
  have h4 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => e2 ^ 2 * (1 - Real.cos (u / e2))) :=
    (contDiff_const (c := e2 ^ 2)).mul h3
  exact h4

lemma contDiff_Dlow (b0 b1 b2 : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Dlow b0 b1 b2) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => b0 * eta0 u) :=
    (contDiff_const (c := b0)).mul contDiff_eta0
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => b1 * eta1 u) :=
    (contDiff_const (c := b1)).mul contDiff_eta1
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => b2 * eta2 u) :=
    (contDiff_const (c := b2)).mul contDiff_eta2
  exact (h1.add h2).add h3

/-- Linearity of the iterated derivatives of `Dlow`. -/
lemma iteratedDeriv_Dlow_apply (b0 b1 b2 : ℝ) (k : ℕ) (u : ℝ) :
    iteratedDeriv k (Dlow b0 b1 b2) u =
      b0 * iteratedDeriv k eta0 u + b1 * iteratedDeriv k eta1 u + b2 * iteratedDeriv k eta2 u := by
  have hA : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (fun u : ℝ => b0 * eta0 u) u :=
    ((contDiff_const (c := b0)).mul contDiff_eta0).contDiffAt.of_le (natCast_le_topE k)
  have hB : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (fun u : ℝ => b1 * eta1 u) u :=
    ((contDiff_const (c := b1)).mul contDiff_eta1).contDiffAt.of_le (natCast_le_topE k)
  have hC : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (fun u : ℝ => b2 * eta2 u) u :=
    ((contDiff_const (c := b2)).mul contDiff_eta2).contDiffAt.of_le (natCast_le_topE k)
  have hAB : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞)
      ((fun u : ℝ => b0 * eta0 u) + (fun u : ℝ => b1 * eta1 u)) u := hA.add hB
  rw [show Dlow b0 b1 b2
      = ((fun u : ℝ => b0 * eta0 u) + (fun u : ℝ => b1 * eta1 u))
        + (fun u : ℝ => b2 * eta2 u) from rfl]
  rw [iteratedDeriv_add hAB hC, iteratedDeriv_add hA hB,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]

lemma iteratedDeriv_eta0_0 : iteratedDeriv 0 eta0 0 = 1 := by
  rw [iteratedDeriv_zero]; rfl

lemma iteratedDeriv_eta0_1 : iteratedDeriv 1 eta0 0 = 0 := by
  rw [iteratedDeriv_one, deriv_eta0_eq]

lemma iteratedDeriv_eta0_2 : iteratedDeriv 2 eta0 0 = 0 := by
  rw [iteratedDeriv_two_eq, deriv_eta0_eq]
  show deriv (fun _ : ℝ => (0 : ℝ)) 0 = 0
  rw [deriv_const]

lemma iteratedDeriv_eta1_0 : iteratedDeriv 0 eta1 0 = 0 := by
  rw [iteratedDeriv_zero]; exact eta1_zero

lemma iteratedDeriv_eta1_1 : iteratedDeriv 1 eta1 0 = 1 := by
  rw [iteratedDeriv_one]; exact deriv_eta1_zero

lemma iteratedDeriv_eta1_2 : iteratedDeriv 2 eta1 0 = 0 := iteratedDeriv_two_eta1

lemma iteratedDeriv_eta2_0 : iteratedDeriv 0 eta2 0 = 0 := by
  rw [iteratedDeriv_zero]; exact eta2_zero

lemma iteratedDeriv_eta2_1 : iteratedDeriv 1 eta2 0 = 0 := by
  rw [iteratedDeriv_one]; exact deriv_eta2_zero

lemma iteratedDeriv_eta2_2 : iteratedDeriv 2 eta2 0 = 1 := iteratedDeriv_two_eta2

/-- The jets of `Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2)` at `0` reproduce the first three
jets of `f - profileX` at `a`. -/
lemma iteratedDeriv_Dlow_le_two (f : ℝ → ℝ) (a : ℝ) (k : ℕ) (hk : k ≤ 2) :
    iteratedDeriv k (Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2)) 0 = bJet f a k := by
  rw [iteratedDeriv_Dlow_apply]
  interval_cases k <;>
    simp only [iteratedDeriv_eta0_0, iteratedDeriv_eta0_1, iteratedDeriv_eta0_2,
      iteratedDeriv_eta1_0, iteratedDeriv_eta1_1, iteratedDeriv_eta1_2,
      iteratedDeriv_eta2_0, iteratedDeriv_eta2_1, iteratedDeriv_eta2_2, mul_one, mul_zero,
      add_zero] <;> ring

/-- First derivative of `Dlow`, in closed form. -/
lemma deriv_Dlow_apply (b0 b1 b2 u : ℝ) :
    deriv (Dlow b0 b1 b2) u
      = b0 * deriv eta0 u + b1 * deriv eta1 u + b2 * deriv eta2 u := by
  rw [← iteratedDeriv_one, iteratedDeriv_Dlow_apply]
  simp only [iteratedDeriv_one]

/-- Second derivative of `Dlow`, in closed form. -/
lemma deriv_deriv_Dlow_apply (b0 b1 b2 u : ℝ) :
    deriv (deriv (Dlow b0 b1 b2)) u
      = b0 * deriv (deriv eta0) u + b1 * deriv (deriv eta1) u + b2 * deriv (deriv eta2) u := by
  rw [← iteratedDeriv_two_eq, iteratedDeriv_Dlow_apply]
  simp only [iteratedDeriv_two_eq]

lemma abs_Dlow_le (f : ℝ → ℝ) (a : ℝ)
    (h0 : ∀ s : ℝ, a ≤ s → |f s - Work.OddEnvelope.profileX s| ≤ 1 / 200)
    (h1 : ∀ s : ℝ, a ≤ s →
      |derivWithin f (Set.Ici a) s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 200)
    (h2 : ∀ s : ℝ, a ≤ s → |derivWithin (derivWithin f (Set.Ici a)) (Set.Ici a) s
        - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 200)
    (u : ℝ) :
    |Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2) u| ≤ 189 / 20000 := by
  rw [Dlow_apply]
  have hb0 := abs_bJet_zero_le f a h0
  have hb1 := abs_bJet_one_le f a h1
  have hb2 := abs_bJet_two_le f a h2
  have e0 : |bJet f a 0 * eta0 u| ≤ (1 / 200) * 1 := by
    rw [abs_mul]
    exact mul_le_mul hb0 (abs_eta0_le u) (abs_nonneg _) (by norm_num)
  have e1 : |bJet f a 1 * eta1 u| ≤ (1 / 200) * (87 / 100) := by
    rw [abs_mul]
    exact mul_le_mul hb1 (le_trans (abs_eta1_le u) T1_mul_pi_div_two_le) (abs_nonneg _)
      (by norm_num)
  have e2' : |bJet f a 2 * eta2 u| ≤ (1 / 200) * (1 / 50) := by
    rw [abs_mul]
    exact mul_le_mul hb2 (le_trans (abs_eta2_le u) (by norm_num [e2])) (abs_nonneg _)
      (by norm_num)
  have htri : |bJet f a 0 * eta0 u + bJet f a 1 * eta1 u + bJet f a 2 * eta2 u|
      ≤ |bJet f a 0 * eta0 u| + |bJet f a 1 * eta1 u| + |bJet f a 2 * eta2 u| := by
    have hA := abs_add_le (bJet f a 0 * eta0 u + bJet f a 1 * eta1 u) (bJet f a 2 * eta2 u)
    have hB := abs_add_le (bJet f a 0 * eta0 u) (bJet f a 1 * eta1 u)
    linarith [abs_nonneg (bJet f a 0 * eta0 u), abs_nonneg (bJet f a 1 * eta1 u),
      abs_nonneg (bJet f a 2 * eta2 u)]
  calc |bJet f a 0 * eta0 u + bJet f a 1 * eta1 u + bJet f a 2 * eta2 u|
      ≤ |bJet f a 0 * eta0 u| + |bJet f a 1 * eta1 u| + |bJet f a 2 * eta2 u| := htri
    _ ≤ (1 / 200) * 1 + (1 / 200) * (87 / 100) + (1 / 200) * (1 / 50) := by
        linarith
    _ = 189 / 20000 := by norm_num

lemma abs_deriv_Dlow_le (f : ℝ → ℝ) (a : ℝ)
    (h0 : ∀ s : ℝ, a ≤ s → |f s - Work.OddEnvelope.profileX s| ≤ 1 / 200)
    (h1 : ∀ s : ℝ, a ≤ s →
      |derivWithin f (Set.Ici a) s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 200)
    (h2 : ∀ s : ℝ, a ≤ s → |derivWithin (derivWithin f (Set.Ici a)) (Set.Ici a) s
        - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 200)
    (u : ℝ) :
    |deriv (Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2)) u| ≤ 11 / 2000 := by
  rw [deriv_Dlow_apply]
  have hb0 := abs_bJet_zero_le f a h0
  have hb1 := abs_bJet_one_le f a h1
  have hb2 := abs_bJet_two_le f a h2
  have e0 : |bJet f a 0 * deriv eta0 u| ≤ (1 / 200) * 0 := by
    rw [abs_mul]
    have hz : |deriv eta0 u| = 0 := le_antisymm (abs_deriv_eta0_le u) (abs_nonneg _)
    rw [hz, mul_zero, mul_zero]
  have e1 : |bJet f a 1 * deriv eta1 u| ≤ (1 / 200) * 1 := by
    rw [abs_mul]
    exact mul_le_mul hb1 (abs_deriv_eta1_le u) (abs_nonneg _) (by norm_num)
  have e2' : |bJet f a 2 * deriv eta2 u| ≤ (1 / 200) * e2 := by
    rw [abs_mul]
    exact mul_le_mul hb2 (abs_deriv_eta2_le u) (abs_nonneg _) (by norm_num)
  have htri : |bJet f a 0 * deriv eta0 u + bJet f a 1 * deriv eta1 u
        + bJet f a 2 * deriv eta2 u|
      ≤ |bJet f a 0 * deriv eta0 u| + |bJet f a 1 * deriv eta1 u|
        + |bJet f a 2 * deriv eta2 u| := by
    have hA := abs_add_le (bJet f a 0 * deriv eta0 u + bJet f a 1 * deriv eta1 u)
      (bJet f a 2 * deriv eta2 u)
    have hB := abs_add_le (bJet f a 0 * deriv eta0 u) (bJet f a 1 * deriv eta1 u)
    linarith [abs_nonneg (bJet f a 0 * deriv eta0 u), abs_nonneg (bJet f a 1 * deriv eta1 u),
      abs_nonneg (bJet f a 2 * deriv eta2 u)]
  calc |bJet f a 0 * deriv eta0 u + bJet f a 1 * deriv eta1 u + bJet f a 2 * deriv eta2 u|
      ≤ |bJet f a 0 * deriv eta0 u| + |bJet f a 1 * deriv eta1 u|
        + |bJet f a 2 * deriv eta2 u| := htri
    _ ≤ (1 / 200) * 0 + (1 / 200) * 1 + (1 / 200) * e2 := by linarith
    _ = 11 / 2000 := by norm_num [e2]

lemma abs_deriv_deriv_Dlow_le (f : ℝ → ℝ) (a : ℝ)
    (h0 : ∀ s : ℝ, a ≤ s → |f s - Work.OddEnvelope.profileX s| ≤ 1 / 200)
    (h1 : ∀ s : ℝ, a ≤ s →
      |derivWithin f (Set.Ici a) s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 200)
    (h2 : ∀ s : ℝ, a ≤ s → |derivWithin (derivWithin f (Set.Ici a)) (Set.Ici a) s
        - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 200)
    (u : ℝ) :
    |deriv (deriv (Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2))) u| ≤ 21 / 2200 := by
  rw [deriv_deriv_Dlow_apply]
  have hb0 := abs_bJet_zero_le f a h0
  have hb1 := abs_bJet_one_le f a h1
  have hb2 := abs_bJet_two_le f a h2
  have e0 : |bJet f a 0 * deriv (deriv eta0) u| ≤ (1 / 200) * 0 := by
    rw [abs_mul]
    have hz : |deriv (deriv eta0) u| = 0 := le_antisymm (abs_deriv_deriv_eta0_le u) (abs_nonneg _)
    rw [hz, mul_zero, mul_zero]
  have e1 : |bJet f a 1 * deriv (deriv eta1) u| ≤ (1 / 200) * (1 / (2 * T1)) := by
    rw [abs_mul]
    exact mul_le_mul hb1 (abs_deriv_deriv_eta1_le u) (abs_nonneg _) (by norm_num)
  have e2' : |bJet f a 2 * deriv (deriv eta2) u| ≤ (1 / 200) * 1 := by
    rw [abs_mul]
    exact mul_le_mul hb2 (abs_deriv_deriv_eta2_le u) (abs_nonneg _) (by norm_num)
  have htri : |bJet f a 0 * deriv (deriv eta0) u + bJet f a 1 * deriv (deriv eta1) u
        + bJet f a 2 * deriv (deriv eta2) u|
      ≤ |bJet f a 0 * deriv (deriv eta0) u| + |bJet f a 1 * deriv (deriv eta1) u|
        + |bJet f a 2 * deriv (deriv eta2) u| := by
    have hA := abs_add_le (bJet f a 0 * deriv (deriv eta0) u + bJet f a 1 * deriv (deriv eta1) u)
      (bJet f a 2 * deriv (deriv eta2) u)
    have hB := abs_add_le (bJet f a 0 * deriv (deriv eta0) u) (bJet f a 1 * deriv (deriv eta1) u)
    linarith [abs_nonneg (bJet f a 0 * deriv (deriv eta0) u),
      abs_nonneg (bJet f a 1 * deriv (deriv eta1) u),
      abs_nonneg (bJet f a 2 * deriv (deriv eta2) u)]
  calc |bJet f a 0 * deriv (deriv eta0) u + bJet f a 1 * deriv (deriv eta1) u
        + bJet f a 2 * deriv (deriv eta2) u|
      ≤ |bJet f a 0 * deriv (deriv eta0) u| + |bJet f a 1 * deriv (deriv eta1) u|
        + |bJet f a 2 * deriv (deriv eta2) u| := htri
    _ ≤ (1 / 200) * 0 + (1 / 200) * (1 / (2 * T1)) + (1 / 200) * 1 := by linarith
    _ = 21 / 2200 := by norm_num [T1]

/-! ## The series correction -/

/-- The discrepancy between the right jets of `f - profileX` and the jets of `Dlow`. -/
def eSeq (f : ℝ → ℝ) (a : ℝ) : ℕ → ℝ :=
  fun k => bJet f a k - iteratedDeriv k (Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2)) 0

lemma eSeq_zero (f : ℝ → ℝ) (a : ℝ) : ∀ k : ℕ, k ≤ 2 → eSeq f a k = 0 := by
  intro k hk
  rw [eSeq, iteratedDeriv_Dlow_le_two f a k hk, sub_self]

/-- A `C^∞` correction matching the remaining jets, with small first two derivatives. -/
lemma exists_series_correction (f : ℝ → ℝ) (a : ℝ) :
    ∃ S : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) S ∧ (∀ k : ℕ, iteratedDeriv k S 0 = eSeq f a k) ∧
      (∀ u : ℝ, u ≤ 0 → |S u| ≤ 1 / 10000) ∧
      (∀ u : ℝ, u ≤ 0 → |deriv S u| ≤ 1 / 10000) ∧
      (∀ u : ℝ, u ≤ 0 → |deriv (deriv S) u| ≤ 1 / 10000) :=
  borel_series (eSeq f a) (eSeq_zero f a) (1 / 10000) (by norm_num)

/-- The function used on the left of `a`. -/
def bigD (f : ℝ → ℝ) (a : ℝ) (S : ℝ → ℝ) : ℝ → ℝ :=
  fun u => Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2) u + S u

lemma contDiff_bigD {f : ℝ → ℝ} {a : ℝ} {S : ℝ → ℝ} (hS : ContDiff ℝ (⊤ : ℕ∞) S) :
    ContDiff ℝ (⊤ : ℕ∞) (bigD f a S) :=
  (contDiff_Dlow _ _ _).add hS

lemma iteratedDeriv_bigD {f : ℝ → ℝ} {a : ℝ} {S : ℝ → ℝ} (hS : ContDiff ℝ (⊤ : ℕ∞) S)
    (hSj : ∀ k : ℕ, iteratedDeriv k S 0 = eSeq f a k) (k : ℕ) :
    iteratedDeriv k (bigD f a S) 0 = bJet f a k := by
  have hA : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞)
      (Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2)) 0 :=
    (contDiff_Dlow _ _ _).contDiffAt.of_le (natCast_le_topE k)
  have hB : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) S 0 :=
    hS.contDiffAt.of_le (natCast_le_topE k)
  rw [show bigD f a S = Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2) + S from rfl,
    iteratedDeriv_add hA hB, hSj k, eSeq]
  ring

lemma deriv_bigD_apply (f : ℝ → ℝ) (a : ℝ) (S : ℝ → ℝ) (hS : ContDiff ℝ (⊤ : ℕ∞) S) (u : ℝ) :
    deriv (bigD f a S) u
      = deriv (Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2)) u + deriv S u := by
  have hA : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2)) u :=
    (contDiff_Dlow _ _ _).contDiffAt.of_le (natCast_le_topE 1)
  have hB : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) S u := hS.contDiffAt.of_le (natCast_le_topE 1)
  rw [← iteratedDeriv_one,
    show bigD f a S = Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2) + S from rfl,
    iteratedDeriv_add hA hB]
  simp only [iteratedDeriv_one]

lemma deriv_deriv_bigD_apply (f : ℝ → ℝ) (a : ℝ) (S : ℝ → ℝ) (hS : ContDiff ℝ (⊤ : ℕ∞) S)
    (u : ℝ) :
    deriv (deriv (bigD f a S)) u
      = deriv (deriv (Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2))) u
        + deriv (deriv S) u := by
  have hA : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞)
      (Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2)) u :=
    (contDiff_Dlow _ _ _).contDiffAt.of_le (natCast_le_topE 2)
  have hB : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) S u := hS.contDiffAt.of_le (natCast_le_topE 2)
  rw [← iteratedDeriv_two_eq,
    show bigD f a S = Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2) + S from rfl,
    iteratedDeriv_add hA hB]
  simp only [iteratedDeriv_two_eq]

lemma abs_bigD_le (f : ℝ → ℝ) (a : ℝ) (S : ℝ → ℝ)
    (h0 : ∀ s : ℝ, a ≤ s → |f s - Work.OddEnvelope.profileX s| ≤ 1 / 200)
    (h1 : ∀ s : ℝ, a ≤ s →
      |derivWithin f (Set.Ici a) s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 200)
    (h2 : ∀ s : ℝ, a ≤ s → |derivWithin (derivWithin f (Set.Ici a)) (Set.Ici a) s
        - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 200)
    (hS0 : ∀ u : ℝ, u ≤ 0 → |S u| ≤ 1 / 10000)
    (u : ℝ) (hu : u ≤ 0) : |bigD f a S u| ≤ 1 / 100 := by
  have h1' : |bigD f a S u| ≤ 189 / 20000 + 1 / 10000 := by
    rw [show bigD f a S u = Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2) u + S u from rfl]
    calc |Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2) u + S u|
        ≤ |Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2) u| + |S u| := abs_add_le _ _
      _ ≤ 189 / 20000 + 1 / 10000 :=
          add_le_add (abs_Dlow_le f a h0 h1 h2 u) (hS0 u hu)
  linarith

lemma abs_deriv_bigD_le (f : ℝ → ℝ) (a : ℝ) (S : ℝ → ℝ) (hS : ContDiff ℝ (⊤ : ℕ∞) S)
    (h0 : ∀ s : ℝ, a ≤ s → |f s - Work.OddEnvelope.profileX s| ≤ 1 / 200)
    (h1 : ∀ s : ℝ, a ≤ s →
      |derivWithin f (Set.Ici a) s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 200)
    (h2 : ∀ s : ℝ, a ≤ s → |derivWithin (derivWithin f (Set.Ici a)) (Set.Ici a) s
        - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 200)
    (hS1 : ∀ u : ℝ, u ≤ 0 → |deriv S u| ≤ 1 / 10000)
    (u : ℝ) (hu : u ≤ 0) : |deriv (bigD f a S) u| ≤ 1 / 100 := by
  rw [deriv_bigD_apply f a S hS u]
  have h1' : |deriv (Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2)) u + deriv S u| ≤
      11 / 2000 + 1 / 10000 :=
    (abs_add_le _ _).trans (add_le_add (abs_deriv_Dlow_le f a h0 h1 h2 u) (hS1 u hu))
  linarith

lemma abs_deriv_deriv_bigD_le (f : ℝ → ℝ) (a : ℝ) (S : ℝ → ℝ) (hS : ContDiff ℝ (⊤ : ℕ∞) S)
    (h0 : ∀ s : ℝ, a ≤ s → |f s - Work.OddEnvelope.profileX s| ≤ 1 / 200)
    (h1 : ∀ s : ℝ, a ≤ s →
      |derivWithin f (Set.Ici a) s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 200)
    (h2 : ∀ s : ℝ, a ≤ s → |derivWithin (derivWithin f (Set.Ici a)) (Set.Ici a) s
        - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 200)
    (hS2 : ∀ u : ℝ, u ≤ 0 → |deriv (deriv S) u| ≤ 1 / 10000)
    (u : ℝ) (hu : u ≤ 0) : |deriv (deriv (bigD f a S)) u| ≤ 1 / 100 := by
  rw [deriv_deriv_bigD_apply f a S hS u]
  have h1' : |deriv (deriv (Dlow (bJet f a 0) (bJet f a 1) (bJet f a 2))) u
        + deriv (deriv S) u| ≤ 21 / 2200 + 1 / 10000 :=
    (abs_add_le _ _).trans (add_le_add (abs_deriv_deriv_Dlow_le f a h0 h1 h2 u) (hS2 u hu))
  linarith

/-! ## Vanishing of the one-sided jets of `φ = f - profileX - D (· - a)` -/

lemma iteratedDerivWithin_phi_jets_zero (f : ℝ → ℝ) (a : ℝ)
    (hf : ContDiffWithinAt ℝ (⊤ : ℕ∞) f (Set.Ici a) a)
    (D : ℝ → ℝ) (hD : ContDiff ℝ (⊤ : ℕ∞) D)
    (hDjet : ∀ k : ℕ, iteratedDeriv k D 0 = bJet f a k) :
    ∀ k : ℕ,
      iteratedDerivWithin k (fun x : ℝ => f x - Work.OddEnvelope.profileX x - D (x - a))
        (Set.Ici a) a = 0 := by
  intro k
  have hf' : ContDiffWithinAt ℝ (k : ℕ∞) f (Set.Ici a) a := hf.of_le (natCast_le_topE k)
  have hp' : ContDiffWithinAt ℝ (k : ℕ∞) Work.OddEnvelope.profileX (Set.Ici a) a :=
    (contDiff_profileX.contDiffAt.contDiffWithinAt).of_le (natCast_le_topE k)
  have hd' : ContDiffWithinAt ℝ (k : ℕ∞) (fun x : ℝ => D (x - a)) (Set.Ici a) a :=
    ((contDiff_comp_sub_const a hD).contDiffAt.contDiffWithinAt).of_le (natCast_le_topE k)
  have hfg' : ContDiffWithinAt ℝ (k : ℕ∞)
      ((fun x : ℝ => f x) - (fun x : ℝ => Work.OddEnvelope.profileX x)) (Set.Ici a) a :=
    hf'.sub hp'
  have hsub : iteratedDerivWithin k
      (fun x : ℝ => f x - Work.OddEnvelope.profileX x - D (x - a)) (Set.Ici a) a
      = iteratedDerivWithin k
          ((fun x : ℝ => f x) - (fun x : ℝ => Work.OddEnvelope.profileX x)) (Set.Ici a) a
        - iteratedDerivWithin k (fun x : ℝ => D (x - a)) (Set.Ici a) a := by
    rw [show (fun x : ℝ => f x - Work.OddEnvelope.profileX x - D (x - a))
        = ((fun x : ℝ => f x) - (fun x : ℝ => Work.OddEnvelope.profileX x))
          - (fun x : ℝ => D (x - a)) from rfl]
    rw [iteratedDerivWithin_sub (by simp) (uniqueDiffOn_Ici a) hfg' hd']
  have hsub2 : iteratedDerivWithin k
      ((fun x : ℝ => f x) - (fun x : ℝ => Work.OddEnvelope.profileX x)) (Set.Ici a) a
      = iteratedDerivWithin k f (Set.Ici a) a
        - iteratedDerivWithin k Work.OddEnvelope.profileX (Set.Ici a) a :=
    iteratedDerivWithin_sub (by simp) (uniqueDiffOn_Ici a) hf' hp'
  rw [hsub, hsub2]
  have hp2 : iteratedDerivWithin k Work.OddEnvelope.profileX (Set.Ici a) a
      = iteratedDeriv k Work.OddEnvelope.profileX a :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici a)
      (contDiff_profileX.contDiffAt.of_le (natCast_le_topE k)) (by simp)
  rw [hp2, iteratedDerivWithin_sub_const a k hD, hDjet k]
  rw [bJet]
  ring


/-! ## The extension theorem -/

/-- Smooth extension of a function known on the half-line `[a,∞)` to all of `ℝ`, matching all
one-sided derivatives at `a` and staying `C²`-close to `Work.OddEnvelope.profileX`.
Route (Seeley/Borel, nothing like it in Mathlib): let `β` be a smooth bump with `β = 1` near `0`
and support in `[-1,0]`, and `b k` the `k`-th right derivative of `f - profileX` at `a` (via
`iteratedDerivWithin`, from `ContDiffOn ℝ ⊤ f (Ici a)`).  Put
`D x := Σ k, b k * (x - a)^k / k! * β (λ k * (x - a))` with `λ k` growing fast enough that the
series converges in `C^∞` (`contDiff_tsum` in `Mathlib/Analysis/Calculus/SmoothSeries.lean`);
`D` is `C^∞`, its left derivatives at `a` are the `b k`, it vanishes for `x ≤ a - 1/λ 0`, and
with `λ` large its first two derivatives are `≤ 1/200` everywhere.  Then `F := f` for `a ≤ x` and
`F := Work.OddEnvelope.profileX + D` for `x ≤ a` is `C^∞`, and the closeness bounds follow. -/
theorem extension (f : ℝ → ℝ) (a : ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ici a))
    (hcl0 : ∀ s : ℝ, a ≤ s → |f s - Work.OddEnvelope.profileX s| ≤ 1 / 200)
    (hcl1 : ∀ s : ℝ, a ≤ s →
      |derivWithin f (Set.Ici a) s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 200)
    (hcl2 : ∀ s : ℝ, a ≤ s →
      |derivWithin (derivWithin f (Set.Ici a)) (Set.Ici a) s
        - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 200) :
    ∃ F : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧ (∀ s : ℝ, a ≤ s → F s = f s) ∧
      (∀ s : ℝ, |F s - Work.OddEnvelope.profileX s| ≤ 1 / 100) ∧
      (∀ s : ℝ, |deriv F s - deriv Work.OddEnvelope.profileX s| ≤ 1 / 100) ∧
      (∀ s : ℝ, |deriv (deriv F) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 / 100) := by
  obtain ⟨S, hSc, hSj, hS0, hS1, hS2⟩ := exists_series_correction f a
  let D : ℝ → ℝ := bigD f a S
  have hDc : ContDiff ℝ (⊤ : ℕ∞) D := contDiff_bigD hSc
  have hDj : ∀ k : ℕ, iteratedDeriv k D 0 = bJet f a k := fun k => iteratedDeriv_bigD hSc hSj k
  have hphi : ∀ k : ℕ, iteratedDerivWithin k
      (fun x : ℝ => f x - Work.OddEnvelope.profileX x - D (x - a)) (Set.Ici a) a = 0 :=
    iteratedDerivWithin_phi_jets_zero f a (hf.contDiffWithinAt (by simp)) D hDc hDj
  have hφc : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : ℝ => f x - Work.OddEnvelope.profileX x - D (x - a)) (Set.Ici a) :=
    (hf.sub contDiff_profileX.contDiffOn).sub (contDiffOn_comp_sub_const a hDc)
  have hΨc : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ => if a ≤ x then f x - Work.OddEnvelope.profileX x - D (x - a) else 0) :=
    (flat_glue a (fun x : ℝ => f x - Work.OddEnvelope.profileX x - D (x - a)) hφc hphi).1
  have hΦc : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ => Work.OddEnvelope.profileX x + D (x - a)) :=
    contDiff_profileX.add (contDiff_comp_sub_const a hDc)
  let F : ℝ → ℝ := fun x => (Work.OddEnvelope.profileX x + D (x - a)) +
      (if a ≤ x then f x - Work.OddEnvelope.profileX x - D (x - a) else 0)
  have hFc : ContDiff ℝ (⊤ : ℕ∞) F := hΦc.add hΨc
  have hFf : ∀ s : ℝ, a ≤ s → F s = f s := by
    intro s hs
    show (Work.OddEnvelope.profileX s + D (s - a)) +
      (if a ≤ s then f s - Work.OddEnvelope.profileX s - D (s - a) else 0) = f s
    rw [if_pos hs]; ring
  have hleft : ∀ x : ℝ, x < a → F x = Work.OddEnvelope.profileX x + D (x - a) := by
    intro x hx
    show (Work.OddEnvelope.profileX x + D (x - a)) +
      (if a ≤ x then f x - Work.OddEnvelope.profileX x - D (x - a) else 0)
      = Work.OddEnvelope.profileX x + D (x - a)
    rw [if_neg (not_le.mpr hx), add_zero]
  refine ⟨F, hFc, hFf, ?_, ?_, ?_⟩
  · intro s
    by_cases hs : a ≤ s
    · rw [hFf s hs]; linarith [hcl0 s hs]
    · have hs' : s < a := not_le.mp hs
      have hval : F s - Work.OddEnvelope.profileX s = D (s - a) := by
        rw [hleft s hs']; ring
      rw [hval]
      exact abs_bigD_le f a S hcl0 hcl1 hcl2 hS0 (s - a) (by linarith)
  · intro s
    by_cases hs : a ≤ s
    · rw [deriv_eq_derivWithin_of_contDiff_eqOn a hFc hFf s hs]
      linarith [hcl1 s hs]
    · have hs' : s < a := not_le.mp hs
      have heq : F =ᶠ[𝓝 s] (fun y : ℝ => Work.OddEnvelope.profileX y + D (y - a)) := by
        filter_upwards [IsOpen.mem_nhds isOpen_Iio hs'] with y hy
        exact hleft y hy
      have hder : deriv F s
          = deriv (fun y : ℝ => Work.OddEnvelope.profileX y + D (y - a)) s :=
        Filter.EventuallyEq.deriv_eq heq
      have hval : deriv F s - deriv Work.OddEnvelope.profileX s = deriv D (s - a) := by
        rw [hder]
        rw [show (fun y : ℝ => Work.OddEnvelope.profileX y + D (y - a))
            = Work.OddEnvelope.profileX + (fun y : ℝ => D (y - a)) from rfl]
        rw [deriv_add (differentiableAt_of_contDiff contDiff_profileX s)
          (differentiableAt_of_contDiff (contDiff_comp_sub_const a hDc) s)]
        rw [deriv_comp_sub_const D s a (differentiableAt_of_contDiff hDc (s - a))]
        ring
      rw [hval]
      exact abs_deriv_bigD_le f a S hSc hcl0 hcl1 hcl2 hS1 (s - a) (by linarith)
  · intro s
    by_cases hs : a ≤ s
    · rw [deriv_deriv_eq_derivWithin_of_contDiff_eqOn a hFc hFf s hs]
      linarith [hcl2 s hs]
    · have hs' : s < a := not_le.mp hs
      have hdeq : deriv F =ᶠ[𝓝 s]
          deriv (fun y : ℝ => Work.OddEnvelope.profileX y + D (y - a)) := by
        filter_upwards [IsOpen.mem_nhds isOpen_Iio hs'] with y hy
        have h1 : F =ᶠ[𝓝 y] (fun z : ℝ => Work.OddEnvelope.profileX z + D (z - a)) := by
          filter_upwards [IsOpen.mem_nhds isOpen_Iio hy] with z hz
          exact hleft z hz
        exact Filter.EventuallyEq.deriv_eq h1
      have hder : deriv (deriv F) s
          = deriv (deriv (fun y : ℝ => Work.OddEnvelope.profileX y + D (y - a))) s :=
        Filter.EventuallyEq.deriv_eq hdeq
      have h2 : deriv (fun y : ℝ => Work.OddEnvelope.profileX y + D (y - a))
          = fun y : ℝ => deriv Work.OddEnvelope.profileX y + deriv D (y - a) := by
        funext y
        rw [show (fun z : ℝ => Work.OddEnvelope.profileX z + D (z - a))
            = Work.OddEnvelope.profileX + (fun z : ℝ => D (z - a)) from rfl]
        rw [deriv_add (differentiableAt_of_contDiff contDiff_profileX y)
          (differentiableAt_of_contDiff (contDiff_comp_sub_const a hDc) y)]
        rw [deriv_comp_sub_const D y a (differentiableAt_of_contDiff hDc (y - a))]
      have hval : deriv (deriv F) s - deriv (deriv Work.OddEnvelope.profileX) s
          = deriv (deriv D) (s - a) := by
        rw [hder, h2]
        rw [show (fun y : ℝ => deriv Work.OddEnvelope.profileX y + deriv D (y - a))
            = deriv Work.OddEnvelope.profileX + (fun y : ℝ => deriv D (y - a)) from rfl]
        rw [deriv_add ((differentiable_deriv_of_contDiff contDiff_profileX).differentiableAt)
          (differentiableAt_deriv_shift hDc s a)]
        rw [deriv_deriv_comp_sub_const D s a (differentiable_deriv_of_contDiff hDc)]
        ring
      rw [hval]
      exact abs_deriv_deriv_bigD_le f a S hSc hcl0 hcl1 hcl2 hS2 (s - a) (by linarith)

end

end Work.Anchor
