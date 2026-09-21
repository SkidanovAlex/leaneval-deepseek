import Mathlib
import Submission.Work.OddBridge.KernelDefs
import Submission.Work.OddVolterra.KernelExt.JM_eq_J

/-!
# The manifest numerator `J1M` agrees with the paper's `J1` off the diagonal

`Work.OddBridge.J1M` is the manifest (polynomial) representative of the numerator of the first
Abel kernel, produced by the recursion `RR` of `Work.OddBridge.KernelDefs`
(`R_{m+1} = Z ∂_s R_m + (ν - m)(∂_s Z) R_m`, `Z = Zrad`), while `Work.OddVolterra.J1` is the
paper's numerator, defined with a case split at `σ = s`.  Off the diagonal, where the radicand
`Z(s,σ,t) = L(σ,t)² - L(s,t)²` is positive, the two agree.

The engine is the classical identity defining the recursion,

`RR ν h init m s σ t = ∂_s^m [Z^ν · init] (s) · Z(s,σ,t)^{m-ν}`,

proved below as `RR_spec'` by transporting `RR` to the `KernelExt` recursion `Rnu`
(`Work.OddVolterra.KernelExt.Rnu`, whose defining property `Rnu_spec` is already proved in the
workspace) and then copying that proof at the smoothness level `⊤ : ℕ∞` used by this statement
(the `KernelExt` version is stated for the analytic level `⊤ : ℕ∞ω`, which is a *stronger*
hypothesis and therefore not directly applicable here).
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddBridge

open Work.OddVolterra (line psi lineSlope hquot)

noncomputable section

/-- Uncurrying of the `init` slot of `RR`, to match the `KernelExt` recursion `Rnu`. -/
def RRinit (init : ℝ → ℝ → ℝ → ℝ) : ℝ × ℝ × ℝ → ℝ := fun p => init p.1 p.2.1 p.2.2

/-- The `KernelExt` radicand is `C^∞` when `h` is (at the `⊤ : ℕ∞` level). -/
lemma Zrad_contDiff_inf {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.OddVolterra.KernelExt.Zrad h) := by
  unfold Work.OddVolterra.KernelExt.Zrad Work.OddVolterra.line
  fun_prop

/-- Differentiation in the first coordinate preserves `C^∞`-ness, as a function of the
base point. -/
lemma contDiff_fderiv_fst_inf {F : ℝ × ℝ × ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => (fderiv ℝ F p) (1, 0, 0)) :=
  (hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

/-- The `KernelExt` Bell numerator `Rnu` is `C^∞` when `h` and `init` are. -/
lemma Rnu_contDiff_inf (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.OddVolterra.KernelExt.Rnu ν h init m) := by
  induction m with
  | zero => simpa [Work.OddVolterra.KernelExt.Rnu] using hinit
  | succ m ih =>
    rw [Work.OddVolterra.KernelExt.Rnu]
    have hZ := Zrad_contDiff_inf hh
    have hdZ := contDiff_fderiv_fst_inf hZ
    have hdR := contDiff_fderiv_fst_inf ih
    fun_prop

/-- **The defining property of the Bell numerator `Rnu`, at the `⊤ : ℕ∞` level.**
This is `Work.KernelExt.Rnu_spec` restated with the smoothness hypothesis `ContDiff ℝ ⊤ h`
understood at the `ℕ∞` level (i.e. `⊤ : ℕ∞`), which is the hypothesis carried by
`Work.OddBridge.J1M_eq_J1`; the `KernelExt` version uses the analytic level `⊤ : ℕ∞ω`, which
is stronger. -/
theorem Rnu_spec_inf (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m : ℕ) (s σ t : ℝ)
    (hz : 0 < Work.OddVolterra.KernelExt.Zrad h (s, σ, t)) :
    Work.OddVolterra.KernelExt.Rnu ν h init m (s, σ, t) =
      iteratedDeriv m
          (fun u : ℝ => (Work.OddVolterra.KernelExt.Zrad h (u, σ, t)) ^ ν * init (u, σ, t)) s
        * (Work.OddVolterra.KernelExt.Zrad h (s, σ, t)) ^ ((m : ℝ) - ν) := by
  have hcontZ : Continuous (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t)) := by
    unfold Work.OddVolterra.KernelExt.Zrad Work.OddVolterra.line; fun_prop
  have key : ∀ m : ℕ, ∀ u : ℝ, 0 < Work.OddVolterra.KernelExt.Zrad h (u, σ, t) →
      iteratedDeriv m (fun u : ℝ =>
          (Work.OddVolterra.KernelExt.Zrad h (u, σ, t)) ^ ν * init (u, σ, t)) u =
        Work.OddVolterra.KernelExt.Rnu ν h init m (u, σ, t) *
          (Work.OddVolterra.KernelExt.Zrad h (u, σ, t)) ^ (ν - (m : ℝ)) := by
    intro m
    induction m with
    | zero =>
      intro u _
      simp only [iteratedDeriv_zero, Work.OddVolterra.KernelExt.Rnu, Nat.cast_zero, sub_zero]
      rw [mul_comm]
    | succ m ih =>
      intro u hu
      rw [iteratedDeriv_succ]
      have hopen : IsOpen {v : ℝ | 0 < Work.OddVolterra.KernelExt.Zrad h (v, σ, t)} :=
        isOpen_lt continuous_const hcontZ
      have hmem : {v : ℝ | 0 < Work.OddVolterra.KernelExt.Zrad h (v, σ, t)} ∈ 𝓝 u :=
        hopen.mem_nhds hu
      have heq : iteratedDeriv m (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.Zrad h (u, σ, t)) ^ ν * init (u, σ, t))
          =ᶠ[𝓝 u] (fun v : ℝ => Work.OddVolterra.KernelExt.Rnu ν h init m (v, σ, t) *
            (Work.OddVolterra.KernelExt.Zrad h (v, σ, t)) ^ (ν - (m : ℝ))) := by
        filter_upwards [hmem] with v hv
        exact ih v hv
      rw [Filter.EventuallyEq.deriv_eq heq]
      have hRmd : DifferentiableAt ℝ (Work.OddVolterra.KernelExt.Rnu ν h init m) (u, σ, t) :=
        ((Rnu_contDiff_inf ν hh hinit m).contDiffAt).differentiableAt (by simp)
      have hZd : DifferentiableAt ℝ (Work.OddVolterra.KernelExt.Zrad h) (u, σ, t) :=
        ((Zrad_contDiff_inf hh).contDiffAt).differentiableAt (by simp)
      have h1 : HasDerivAt (fun v : ℝ => Work.OddVolterra.KernelExt.Rnu ν h init m (v, σ, t))
          ((fderiv ℝ (Work.OddVolterra.KernelExt.Rnu ν h init m) (u, σ, t)) (1, 0, 0)) u :=
        Work.OddVolterra.KernelExt.hasDerivAt_section _ hRmd
      have h2 : HasDerivAt (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t))
          ((fderiv ℝ (Work.OddVolterra.KernelExt.Zrad h) (u, σ, t)) (1, 0, 0)) u :=
        Work.OddVolterra.KernelExt.hasDerivAt_section _ hZd
      have h3 : HasDerivAt
          (fun v : ℝ => (Work.OddVolterra.KernelExt.Zrad h (v, σ, t)) ^ (ν - (m : ℝ)))
          (((fderiv ℝ (Work.OddVolterra.KernelExt.Zrad h) (u, σ, t)) (1, 0, 0)) * (ν - (m : ℝ)) *
            (Work.OddVolterra.KernelExt.Zrad h (u, σ, t)) ^ (ν - (m : ℝ) - 1)) u :=
        h2.rpow_const (Or.inl (ne_of_gt hu))
      have hfun : (fun v : ℝ => Work.OddVolterra.KernelExt.Rnu ν h init m (v, σ, t) *
            Work.OddVolterra.KernelExt.Zrad h (v, σ, t) ^ (ν - (m : ℝ)))
          = ((fun v : ℝ => Work.OddVolterra.KernelExt.Rnu ν h init m (v, σ, t)) *
              (fun v : ℝ => Work.OddVolterra.KernelExt.Zrad h (v, σ, t) ^ (ν - (m : ℝ)))) := rfl
      rw [hfun, (h1.mul h3).deriv, Work.OddVolterra.KernelExt.Rnu]
      have hexp : ν - ((m + 1 : ℕ) : ℝ) = ν - (m : ℝ) - 1 := by push_cast; ring
      rw [hexp]
      have hAw : (Work.OddVolterra.KernelExt.Zrad h (u, σ, t)) ^ (ν - (m : ℝ)) =
          Work.OddVolterra.KernelExt.Zrad h (u, σ, t) *
            (Work.OddVolterra.KernelExt.Zrad h (u, σ, t)) ^ (ν - (m : ℝ) - 1) := by
        conv_lhs => rw [show ν - (m : ℝ) = (ν - (m : ℝ) - 1) + 1 from by ring]
        rw [Real.rpow_add hu, Real.rpow_one]
        ring
      rw [hAw]
      ring
  have hmain := key m s hz
  rw [hmain, mul_assoc, ← Real.rpow_add hz]
  have hexp : (ν - (m : ℝ)) + ((m : ℝ) - ν) = 0 := by ring
  rw [hexp, Real.rpow_zero, mul_one]

/-- The curried recursion `RR` of `OddBridge` is the `KernelExt` recursion `Rnu` applied to
the uncurried `init`. -/
theorem RR_eq_Rnu (ν : ℝ) (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (init : ℝ → ℝ → ℝ → ℝ)
    (hinit : ContDiff ℝ (⊤ : ℕ∞) (RRinit init)) (m : ℕ) :
    ∀ p : ℝ × ℝ × ℝ,
      RR ν h init m p.1 p.2.1 p.2.2 =
        Work.OddVolterra.KernelExt.Rnu ν h (RRinit init) m p := by
  induction m with
  | zero => intro p; rfl
  | succ m ih =>
    intro p
    have hdR : DifferentiableAt ℝ (Work.OddVolterra.KernelExt.Rnu ν h (RRinit init) m) p :=
      ((Rnu_contDiff_inf ν hh hinit m).contDiffAt).differentiableAt (by simp)
    have hderiv : deriv (fun u : ℝ => RR ν h init m u p.2.1 p.2.2) p.1 =
        (fderiv ℝ (Work.OddVolterra.KernelExt.Rnu ν h (RRinit init) m) p) (1, 0, 0) := by
      have hcongr : (fun u : ℝ => RR ν h init m u p.2.1 p.2.2) =
          (fun u : ℝ =>
            Work.OddVolterra.KernelExt.Rnu ν h (RRinit init) m (u, p.2.1, p.2.2)) := by
        funext u; exact ih (u, p.2.1, p.2.2)
      rw [hcongr]
      exact (Work.OddVolterra.KernelExt.hasDerivAt_section p hdR).deriv
    have hZs : Zs h p.1 p.2.1 p.2.2 =
        (fderiv ℝ (Work.OddVolterra.KernelExt.Zrad h) p) (1, 0, 0) := by
      have hd : DifferentiableAt ℝ (Work.OddVolterra.KernelExt.Zrad h) p :=
        ((Zrad_contDiff_inf hh).contDiffAt).differentiableAt (by simp)
      unfold Zs
      exact (Work.OddVolterra.KernelExt.hasDerivAt_section p hd).deriv
    rw [RR, Work.OddVolterra.KernelExt.Rnu]
    dsimp only []
    rw [hderiv, ih p, hZs]
    rfl

/-- **The defining property of the `OddBridge` Bell numerator `RR`.**  At every point where the
radicand is positive, `RR ν h init m` is the `m`-th `s`-derivative of `Z^ν · init` multiplied
by `Z^{m-ν}`. -/
theorem RR_spec' (ν : ℝ) (m : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ → ℝ → ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) (RRinit init))
    {s σ t : ℝ} (hZ : 0 < Zrad h s σ t) :
    RR ν h init m s σ t =
      iteratedDeriv m (fun u : ℝ => Zrad h u σ t ^ ν * init u σ t) s
        * Zrad h s σ t ^ ((m : ℝ) - ν) := by
  rw [RR_eq_Rnu ν h hh init hinit m (s, σ, t)]
  rw [Rnu_spec_inf ν hh hinit m s σ t hZ]
  rfl

theorem J1M_eq_J1 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s σ t : ℝ} (hsσ : s < σ)
    (hZ : 0 < Work.OddBridge.Zrad h s σ t) :
    Work.OddBridge.J1M n h s σ t = Work.OddVolterra.J1 n h s σ t := by
  have hne : σ ≠ s := ne_of_gt hsσ
  have hcontZ : Continuous (fun u : ℝ => Zrad h u σ t) := by unfold Zrad line; fun_prop
  have hopen : IsOpen {u : ℝ | 0 < Zrad h u σ t} := isOpen_lt continuous_const hcontZ
  rw [Work.OddVolterra.J1, if_neg hne, Work.OddBridge.J1M,
    RR_spec' ((n : ℝ) + 1 / 2) (n + 1) hh (init := fun _ _ _ => (1 : ℝ)) contDiff_const hZ]
  have heq : (fun u : ℝ => Zrad h u σ t ^ ((n : ℝ) + 1 / 2) * 1) =ᶠ[𝓝 s]
      (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ n *
        Real.sqrt (psi h (fun t' => line h σ t') u t)) := by
    filter_upwards [hopen.mem_nhds hZ] with u hu
    rw [mul_one, Work.OddVolterra.KernelExt.rpow_add_half_nat n hu]
    rfl
  rw [Filter.EventuallyEq.iteratedDeriv_eq (n + 1) heq]
  have hexp : ((n + 1 : ℕ) : ℝ) - ((n : ℝ) + 1 / 2) = 1 / 2 := by push_cast; ring
  rw [hexp, ← Real.sqrt_eq_rpow]
  rfl

end

end Work.OddBridge
