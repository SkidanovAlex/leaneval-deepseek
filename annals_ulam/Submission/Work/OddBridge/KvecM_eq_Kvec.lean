import Mathlib
import Submission.Work.OddBridge.KernelDefs
import Submission.Work.OddBridge.J1M_eq_J1

/-!
# The manifest kernel `KvecM` agrees with the paper's `Kvec`

`Work.OddBridge.KvecM` replaces the two Abel numerators `J₁`, `J₂` of `Work.OddVolterra.Kvec`
by their manifest (polynomial) representatives `J1M`, `J2M` built from the Bell recursion `RR`.

The two agree at every point of the triangle `s ≤ σ` at which the paper's positivity hypothesis
`0 < (t + H(s,σ)) · (L(σ,t) + L(s,t))` holds at the two endpoints `t = y`, `t = -x`:

* off the diagonal `s < σ` the radicand `Z(s,σ,t) = (σ-s)(t+H)(L_σ+L_s)` is positive and
  `RR` computes `∂_s^m[Z^ν · init]·Z^{m-ν}`, which is the paper's differentiated numerator;
* on the diagonal `σ = s` the recursion collapses to the explicit limit values of `J₁`, `J₂`.

Everything is done at the `C^∞` level `⊤ : ℕ∞`; the `KernelExt` version of these statements was
formulated at the analytic level `⊤ : ℕ∞ω`, which is a strictly stronger hypothesis and hence not
applicable here.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddBridge

open Work.OddVolterra

noncomputable section

/-! ## The positivity of the radicand -/

/-- The difference of the two chord values is `(σ-s)` times the paper's quotient `H`:
`L(σ,t) - L(s,t) = (σ-s)(t + H(s,σ))`. -/
lemma line_sub_line (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s σ t : ℝ) :
    line h σ t - line h s t = (σ - s) * (t + hquot h s σ) := by
  have h2 := sub_mul_hquot (h := h) (hh.of_le (by simp)) s σ
  unfold line
  linear_combination h2

/-- The paper's positivity hypothesis makes the radicand positive off the diagonal. -/
lemma Zrad_pos_of_hR {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s σ t : ℝ} (hsσ : s < σ)
    (hR : 0 < (t + hquot h s σ) * (line h σ t + line h s t)) :
    0 < Zrad h s σ t := by
  have hfac : Zrad h s σ t = (line h σ t - line h s t) * (line h σ t + line h s t) := by
    unfold Zrad; ring
  rw [hfac, line_sub_line h hh s σ t, mul_assoc]
  exact mul_pos (by linarith) hR

/-! ## The diagonal value of `∂_s Z` -/

/-- On the diagonal `σ = s`, `∂_s Z(s,σ,t) = -2 L(s,t) ∂_sL(s,t)`. -/
lemma Zs_diag (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s t : ℝ) :
    Zs h s s t = -2 * (line h s t * lineSlope h s t) := by
  have hd : DifferentiableAt ℝ h s := (hh.differentiable (by simp)).differentiableAt
  have h1 : HasDerivAt (fun u : ℝ => u * t) t s := hasDerivAt_mul_const t
  have h2 : HasDerivAt (fun u : ℝ => h u) (deriv h s) s := hd.hasDerivAt
  have hl : HasDerivAt (fun u : ℝ => line h u t) (t + deriv h s) s := h1.add h2
  have hsub := (hasDerivAt_const s (line h s t ^ 2)).sub (hl.pow 2)
  have hfun : ((fun _ : ℝ => line h s t ^ 2) - (fun u : ℝ => line h u t) ^ 2)
      = (fun u : ℝ => Zrad h u s t) := by
    funext u
    simp [Zrad]
  rw [Zs, ← hfun, hsub.deriv]
  unfold lineSlope
  ring

/-! ## The recursion at a zero of the radicand -/

/-- On the zero set of `Zrad` the recursion `R_{m+1} = Z ∂_sR_m + (ν-m)(∂_sZ) R_m` solves
explicitly, because the term containing `∂_s R_m` drops out. -/
lemma RR_of_Zrad_eq_zero (ν : ℝ) (h : ℝ → ℝ) (init : ℝ → ℝ → ℝ → ℝ) :
    ∀ (m : ℕ) (s σ t : ℝ), Zrad h s σ t = 0 →
      RR ν h init m s σ t =
        (∏ i ∈ Finset.range m, (ν - (i : ℝ))) * Zs h s σ t ^ m * init s σ t := by
  intro m
  induction m with
  | zero => intro s σ t _; simp [RR]
  | succ k ih =>
    intro s σ t hz
    have hstep : RR ν h init (k + 1) s σ t =
        Zrad h s σ t * deriv (fun u : ℝ => RR ν h init k u σ t) s
          + (ν - (k : ℝ)) * Zs h s σ t * RR ν h init k s σ t := rfl
    rw [hstep, hz, zero_mul, zero_add, ih s σ t hz, Finset.prod_range_succ, pow_succ]
    ring

/-! ## The double-factorial arithmetic -/

/-- `(2n+1)!! = (2n+1) (2n-1)!!`, valid also for `n = 0`. -/
lemma doubleFactorial_odd_succ (n : ℕ) :
    Nat.doubleFactorial (2 * n + 1) = (2 * n + 1) * Nat.doubleFactorial (2 * n - 1) := by
  cases n with
  | zero => simp [Nat.doubleFactorial]
  | succ k =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
        Nat.doubleFactorial_add_two,
        show 2 * (k + 1) - 1 = 2 * k + 1 by omega]

/-- The falling factorial `(n+1/2)(n-1/2)···(1/2)` equals `(2n+1)!!/2^{n+1}`. -/
lemma prod_half_succ (n : ℕ) :
    (∏ i ∈ Finset.range (n + 1), ((n : ℝ) + 1 / 2 - (i : ℝ))) * 2 ^ (n + 1) =
      (Nat.doubleFactorial (2 * n + 1) : ℝ) := by
  induction n with
  | zero => norm_num [Nat.doubleFactorial]
  | succ k ih =>
    rw [Finset.prod_range_succ']
    have hcongr : (∏ i ∈ Finset.range (k + 1), ((↑(k+1) : ℝ) + 1 / 2 - (↑(i+1) : ℝ)))
        = (∏ i ∈ Finset.range (k + 1), ((k : ℝ) + 1 / 2 - (i : ℝ))) := by
      apply Finset.prod_congr rfl
      intro i _
      push_cast
      ring
    rw [hcongr, Nat.cast_zero, sub_zero]
    have expand : (∏ i ∈ Finset.range (k + 1), ((k : ℝ) + 1 / 2 - (i : ℝ))) *
          (↑(k+1) + 1 / 2) * 2 ^ (k + 1 + 1)
        = ((∏ i ∈ Finset.range (k + 1), ((k : ℝ) + 1 / 2 - (i : ℝ))) * 2 ^ (k + 1)) *
          ((↑(k+1) + 1 / 2) * 2) := by
      rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ]
      ring
    rw [expand, ih]
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, Nat.doubleFactorial_add_two]
    push_cast
    ring

/-- The falling factorial `(n-1/2)(n-3/2)···(1/2)` equals `(2n-1)!!/2^n`. -/
lemma prod_half (n : ℕ) :
    (∏ i ∈ Finset.range n, ((n : ℝ) - 1 / 2 - (i : ℝ))) * 2 ^ n =
      (Nat.doubleFactorial (2 * n - 1) : ℝ) := by
  induction n with
  | zero => norm_num [Nat.doubleFactorial]
  | succ k ih =>
    rw [Finset.prod_range_succ']
    have hcongr : (∏ i ∈ Finset.range k, ((↑(k+1) : ℝ) - 1 / 2 - (↑(i+1) : ℝ)))
        = (∏ i ∈ Finset.range k, ((k : ℝ) - 1 / 2 - (i : ℝ))) := by
      apply Finset.prod_congr rfl
      intro i _
      push_cast
      ring
    rw [hcongr, Nat.cast_zero, sub_zero]
    have expand : (∏ i ∈ Finset.range k, ((k : ℝ) - 1 / 2 - (i : ℝ))) *
          ((↑(k+1) : ℝ) - 1 / 2) * 2 ^ (k + 1)
        = ((∏ i ∈ Finset.range k, ((k : ℝ) - 1 / 2 - (i : ℝ))) * 2 ^ k) *
          ((↑(k+1) - 1 / 2) * 2) := by
      rw [pow_succ]
      ring
    rw [expand, ih]
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, doubleFactorial_odd_succ k]
    push_cast
    ring

/-! ## The diagonal values of the manifest numerators -/

lemma J1M_diag (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s t : ℝ) :
    Work.OddBridge.J1M n h s s t = Work.OddVolterra.J1 n h s s t := by
  rw [Work.OddVolterra.J1, if_pos rfl, Work.OddBridge.J1M]
  rw [RR_of_Zrad_eq_zero ((n : ℝ) + 1 / 2) h (fun _ _ _ => (1 : ℝ)) (n + 1) s s t
        (by unfold Zrad line; ring)]
  simp only [mul_one]
  rw [Zs_diag h hh s t]
  have h2d : (-2 : ℝ) * (line h s t * lineSlope h s t)
      = 2 * (-(line h s t * lineSlope h s t)) := by ring
  rw [h2d, mul_pow]
  rw [show (∏ i ∈ Finset.range (n + 1), ((n : ℝ) + 1 / 2 - (i : ℝ))) *
        (2 ^ (n + 1) * (-(line h s t * lineSlope h s t)) ^ (n + 1))
      = ((∏ i ∈ Finset.range (n + 1), ((n : ℝ) + 1 / 2 - (i : ℝ))) * 2 ^ (n + 1)) *
        (-(line h s t * lineSlope h s t)) ^ (n + 1) by ring]
  rw [prod_half_succ n]

lemma J2M_diag (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s t : ℝ) :
    Work.OddBridge.J2M n h s s t = Work.OddVolterra.J2 n h s s t := by
  rw [Work.OddVolterra.J2, if_pos rfl, Work.OddBridge.J2M]
  rw [RR_of_Zrad_eq_zero ((n : ℝ) - 1 / 2) h (fun u _ t => lineSlope h u t) n s s t
        (by unfold Zrad line; ring)]
  rw [Zs_diag h hh s t]
  have h2d : (-2 : ℝ) * (line h s t * lineSlope h s t)
      = 2 * (-(line h s t * lineSlope h s t)) := by ring
  rw [h2d, mul_pow]
  rw [show (∏ i ∈ Finset.range n, ((n : ℝ) - 1 / 2 - (i : ℝ))) *
        (2 ^ n * (-(line h s t * lineSlope h s t)) ^ n) * lineSlope h s t
      = ((∏ i ∈ Finset.range n, ((n : ℝ) - 1 / 2 - (i : ℝ))) * 2 ^ n) *
        (-(line h s t * lineSlope h s t)) ^ n * lineSlope h s t by ring]
  rw [prod_half n]

/-! ## The off-diagonal identity for the second numerator -/

lemma psi_line_eq_Zrad (h : ℝ → ℝ) (σ u t : ℝ) :
    psi h (fun t' => line h σ t') u t = Zrad h u σ t := rfl

lemma rpow_sub_half_nat (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    x ^ ((n : ℝ) - 1 / 2) = x ^ (n - 1) * Real.sqrt x := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; norm_num
  rw [show (n : ℝ) - 1 / 2 = ((n - 1 : ℕ) : ℝ) + 1 / 2 by rw [hcast]; ring]
  rw [Real.rpow_add hx, Real.rpow_natCast, ← Real.sqrt_eq_rpow]

/-- Off the diagonal, where the radicand is positive, the manifest second numerator `J2M`
(`ν = n-1/2`, `m = n`) is the paper's `J2`. -/
theorem J2M_eq_J2 (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {s σ t : ℝ} (hsσ : s < σ) (hZ : 0 < Zrad h s σ t) :
    Work.OddBridge.J2M n h s σ t = Work.OddVolterra.J2 n h s σ t := by
  have hcontZ : Continuous (fun u : ℝ => Zrad h u σ t) := by unfold Zrad line; fun_prop
  have hopen : IsOpen {u : ℝ | 0 < Zrad h u σ t} := isOpen_lt continuous_const hcontZ
  have hinit : ContDiff ℝ (⊤ : ℕ∞) (RRinit (fun u _ t => lineSlope h u t)) := by
    unfold RRinit lineSlope
    fun_prop
  rw [Work.OddVolterra.J2, if_neg (ne_of_gt hsσ), Work.OddBridge.J2M,
    RR_spec' ((n : ℝ) - 1 / 2) n hh (init := fun u _ t => lineSlope h u t) hinit hZ]
  have heq : (fun u : ℝ => Zrad h u σ t ^ ((n : ℝ) - 1 / 2) * lineSlope h u t)
      =ᶠ[𝓝 s] (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ (n - 1) *
        Real.sqrt (psi h (fun t' => line h σ t') u t) * lineSlope h u t) := by
    filter_upwards [hopen.mem_nhds hZ] with u hu
    rw [psi_line_eq_Zrad, rpow_sub_half_nat n hn hu]
  rw [Filter.EventuallyEq.iteratedDeriv_eq n heq]
  have hexp : (↑n : ℝ) - ((n : ℝ) - 1 / 2) = 1 / 2 := by ring
  rw [hexp, ← Real.sqrt_eq_rpow, psi_line_eq_Zrad]

/-! ## Assembling the two kernels -/

lemma J1M_eq_J1_of_le (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s σ t : ℝ}
    (hsσ : s ≤ σ) (hR : 0 < (t + hquot h s σ) * (line h σ t + line h s t)) :
    Work.OddBridge.J1M n h s σ t = Work.OddVolterra.J1 n h s σ t := by
  rcases eq_or_lt_of_le hsσ with heq | hlt
  · subst heq
    exact J1M_diag n hh s t
  · exact Work.OddBridge.J1M_eq_J1 n hh hlt (Zrad_pos_of_hR hh hlt hR)

lemma J2M_eq_J2_of_le (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {s σ t : ℝ} (hsσ : s ≤ σ) (hR : 0 < (t + hquot h s σ) * (line h σ t + line h s t)) :
    Work.OddBridge.J2M n h s σ t = Work.OddVolterra.J2 n h s σ t := by
  rcases eq_or_lt_of_le hsσ with heq | hlt
  · subst heq
    exact J2M_diag n hh s t
  · exact J2M_eq_J2 n hn hh hlt (Zrad_pos_of_hR hh hlt hR)

lemma K1M_eq_K1_of_le (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s σ t : ℝ}
    (hsσ : s ≤ σ) (hR : 0 < (t + hquot h s σ) * (line h σ t + line h s t)) :
    Work.OddBridge.K1M n h s σ t = Work.OddVolterra.K1 n h s σ t := by
  rw [Work.OddBridge.K1M, Work.OddVolterra.K1, J1M_eq_J1_of_le n hh hsσ hR]

lemma K2M_eq_K2_of_le (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {s σ t : ℝ} (hsσ : s ≤ σ) (hR : 0 < (t + hquot h s σ) * (line h σ t + line h s t)) :
    Work.OddBridge.K2M n h s σ t = Work.OddVolterra.K2 n h s σ t := by
  rw [Work.OddBridge.K2M, Work.OddVolterra.K2, J2M_eq_J2_of_le n hn hh hsσ hR]

theorem KvecM_eq_Kvec (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s σ : ℝ}
    (hsσ : s ≤ σ) (x y x' y' : ℝ)
    (hRy : 0 < (y + Work.OddVolterra.hquot h s σ) * (Work.OddVolterra.line h σ y + Work.OddVolterra.line h s y))
    (hRx : 0 < (-x + Work.OddVolterra.hquot h s σ) * (Work.OddVolterra.line h σ (-x) + Work.OddVolterra.line h s (-x))) :
    Work.OddBridge.KvecM n h s σ x y x' y' = Work.OddVolterra.Kvec n h s σ x y x' y' := by
  have h1y : Work.OddBridge.K1M n h s σ y = Work.OddVolterra.K1 n h s σ y :=
    K1M_eq_K1_of_le n hh hsσ hRy
  have h1x : Work.OddBridge.K1M n h s σ (-x) = Work.OddVolterra.K1 n h s σ (-x) :=
    K1M_eq_K1_of_le n hh hsσ hRx
  have h2y : Work.OddBridge.K2M n h s σ y = Work.OddVolterra.K2 n h s σ y :=
    K2M_eq_K2_of_le n hn hh hsσ hRy
  have h2x : Work.OddBridge.K2M n h s σ (-x) = Work.OddVolterra.K2 n h s σ (-x) :=
    K2M_eq_K2_of_le n hn hh hsσ hRx
  simp only [Work.OddBridge.KvecM, Work.OddVolterra.Kvec, h1y, h1x, h2y, h2x]

end

end Work.OddBridge
