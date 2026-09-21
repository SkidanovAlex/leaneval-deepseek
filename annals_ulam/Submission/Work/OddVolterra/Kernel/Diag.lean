import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.hquot_contDiff
import Submission.Commons.Analysis.Calculus.contDiff_parametric_iteratedDeriv_gen
import Submission.Commons.Analysis.Calculus.contDiffOn_parametric_iteratedDeriv
import Submission.Work.Geometry.Ulam.ulam_faa_j

/-!
# The Abel kernel of the odd transition-slope system across the diagonal

This file collects the structural facts about the Abel kernel
`K₁ = J₁ / √R` (and `K₂ = J₂ / √R`) of `Work.OddVolterra` that are needed to see that
the diagonal singularity cancels.  Writing

* `R(a,σ,t) = (t + H(a,σ)) (L_σ(t) + L_a(t))`  (`krad`, the radicand of `Kden`),
* `ψ(v) = L_σ(t)² - L_v(t)² = (σ - v) R(v)`   (`psi_eq_mul_krad`),

one has, for `a < σ` and `R(a) > 0`,

  `K₁(a,σ,t) = √(σ - a) · ∂^{n+1} ((σ - ·) R(·))^{n+1/2} (a)`,
  `K₂(a,σ,t) = √(σ - a) · ∂^{n}   (((σ - ·) R(·))^{n-1/2} ∂L(·)) (a)`.

Both right-hand sides are restrictions of explicit smooth functions whose
`a`-derivatives stay bounded on the compact region `s ≤ a ≤ σ ≤ 1` — this is what
makes the Abel kernel Lipschitz across the diagonal, and it is the analytic input
behind the interval integrability of the `Θ` integrand.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

set_option maxHeartbeats 2000000

namespace Work.OddVolterra

noncomputable section

/-- The radicand `(t + H(a,σ)) (L_σ(t) + L_a(t))` of the Abel denominator `Kden h a σ t`,
displayed as a function of the first slot `a`. -/
def krad (h : ℝ → ℝ) (σ t a : ℝ) : ℝ :=
  (t + hquot h a σ) * (line h σ t + line h a t)

@[simp] lemma krad_apply (h : ℝ → ℝ) (σ t a : ℝ) :
    krad h σ t a = (t + hquot h a σ) * (line h σ t + line h a t) := rfl

lemma Kden_eq_sqrt_krad (h : ℝ → ℝ) (a σ t : ℝ) :
    Kden h a σ t = Real.sqrt (krad h σ t a) := rfl

/-- The `ψ` radicand factorises as `(σ - a) · krad`. -/
lemma psi_eq_mul_krad {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (σ t a : ℝ) :
    psi h (fun t' => line h σ t') a t = (σ - a) * krad h σ t a := by
  have h1 : h σ - h a = (σ - a) * hquot h a σ := sub_mul_hquot hh a σ
  unfold psi krad line
  rw [show (σ * t + h σ) ^ 2 - (a * t + h a) ^ 2
      = ((σ * t + h σ) - (a * t + h a)) * ((σ * t + h σ) + (a * t + h a)) by ring]
  rw [show (σ * t + h σ) - (a * t + h a) = (σ - a) * t + (h σ - h a) by ring, h1]
  ring

/-- The elementary `rpow` identity behind the structural form of `K₁`. -/
lemma pow_mul_sqrt_eq_rpow (n : ℕ) {x : ℝ} (hx : 0 < x) :
    x ^ n * Real.sqrt x = x ^ ((n : ℝ) + 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hx]

/-- The elementary `rpow` identity behind the structural form of `K₂` (`n ≥ 1`). -/
lemma pow_pred_mul_sqrt_eq_rpow (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    x ^ (n - 1) * Real.sqrt x = x ^ ((n : ℝ) - 1 / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hx]
  have : (((n - 1 : ℕ)) : ℝ) + 1 / 2 = (n : ℝ) - 1 / 2 := by
    rw [Nat.cast_sub hn]; ring
  rw [this]

section Continuity

variable {h : ℝ → ℝ}

lemma continuous_hquot_snd (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) :
    Continuous (fun a : ℝ => hquot h a σ) :=
  (Work.OddVolterra.Existence.hquot_contDiff hh).continuous.comp
    (f := fun a : ℝ => (a, σ)) (by fun_prop)

lemma continuous_krad (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    Continuous (fun a : ℝ => krad h σ t a) := by
  unfold krad line
  exact (continuous_const.add (continuous_hquot_snd hh σ)).mul
    (continuous_const.add ((continuous_id.mul continuous_const).add hh.continuous))

end Continuity

/-- **Structural form of the first Abel kernel.**  Off the diagonal, and where the
denominator radicand is positive, `K₁` is `√(σ - a)` times an explicit smooth expression. -/
theorem K1_eq_sqrt_mul {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (n : ℕ)
    {a σ t : ℝ} (ha : a < σ) (hR : 0 < krad h σ t a) :
    K1 n h a σ t =
      Real.sqrt (σ - a) * iteratedDeriv (n + 1)
        (fun v : ℝ => ((σ - v) * krad h σ t v) ^ ((n : ℝ) + 1 / 2)) a := by
  have h1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have haσ : ¬ (σ = a) := ne_of_gt ha
  have hsub : 0 < σ - a := sub_pos.mpr ha
  have hJ1 : J1 n h a σ t =
      iteratedDeriv (n + 1) (fun u : ℝ =>
          psi h (fun t' => line h σ t') u t ^ n *
            Real.sqrt (psi h (fun t' => line h σ t') u t)) a *
        Real.sqrt (psi h (fun t' => line h σ t') a t) := by
    unfold J1
    rw [if_neg haσ]
  have hcont : ContinuousAt (fun v : ℝ => (σ - v) * krad h σ t v) a :=
    ((continuous_const.sub continuous_id).mul (continuous_krad hh σ t)).continuousAt
  have hpos : 0 < (σ - a) * krad h σ t a := mul_pos hsub hR
  have hpt : ∀ᶠ v in 𝓝 a,
      psi h (fun t' => line h σ t') v t ^ n *
          Real.sqrt (psi h (fun t' => line h σ t') v t)
        = ((σ - v) * krad h σ t v) ^ ((n : ℝ) + 1 / 2) := by
    filter_upwards [hcont.eventually (isOpen_Ioi.mem_nhds hpos)] with v hv
    rw [psi_eq_mul_krad h1, pow_mul_sqrt_eq_rpow n hv]
  have hiter := Filter.EventuallyEq.iteratedDeriv_eq (n + 1) hpt
  have hpsi_a : psi h (fun t' => line h σ t') a t = (σ - a) * krad h σ t a :=
    psi_eq_mul_krad h1 σ t a
  have hsqrt : Real.sqrt (psi h (fun t' => line h σ t') a t)
      = Real.sqrt (σ - a) * Real.sqrt (krad h σ t a) := by
    rw [hpsi_a, Real.sqrt_mul (le_of_lt hsub)]
  have hkR : Real.sqrt (krad h σ t a) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hR)
  show J1 n h a σ t / Kden h a σ t = _
  rw [hJ1, Kden_eq_sqrt_krad, hiter, hsqrt]
  field_simp

/-- **Structural form of the second Abel kernel.**  Off the diagonal, and where the
denominator radicand is positive, `K₂` is `√(σ - a)` times an explicit smooth expression. -/
theorem K2_eq_sqrt_mul {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (n : ℕ) (hn : 1 ≤ n)
    {a σ t : ℝ} (ha : a < σ) (hR : 0 < krad h σ t a) :
    K2 n h a σ t =
      Real.sqrt (σ - a) * iteratedDeriv n
        (fun v : ℝ => ((σ - v) * krad h σ t v) ^ ((n : ℝ) - 1 / 2) * lineSlope h v t) a := by
  have h1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have haσ : ¬ (σ = a) := ne_of_gt ha
  have hsub : 0 < σ - a := sub_pos.mpr ha
  have hJ2 : J2 n h a σ t =
      iteratedDeriv n (fun u : ℝ =>
          psi h (fun t' => line h σ t') u t ^ (n - 1) *
            Real.sqrt (psi h (fun t' => line h σ t') u t) * lineSlope h u t) a *
        Real.sqrt (psi h (fun t' => line h σ t') a t) := by
    unfold J2
    rw [if_neg haσ]
  have hcont : ContinuousAt (fun v : ℝ => (σ - v) * krad h σ t v) a :=
    ((continuous_const.sub continuous_id).mul (continuous_krad hh σ t)).continuousAt
  have hpos : 0 < (σ - a) * krad h σ t a := mul_pos hsub hR
  have hpt : ∀ᶠ v in 𝓝 a,
      psi h (fun t' => line h σ t') v t ^ (n - 1) *
          Real.sqrt (psi h (fun t' => line h σ t') v t) * lineSlope h v t
        = ((σ - v) * krad h σ t v) ^ ((n : ℝ) - 1 / 2) * lineSlope h v t := by
    filter_upwards [hcont.eventually (isOpen_Ioi.mem_nhds hpos)] with v hv
    rw [psi_eq_mul_krad h1, pow_pred_mul_sqrt_eq_rpow n hn hv]
  have hiter := Filter.EventuallyEq.iteratedDeriv_eq n hpt
  have hpsi_a : psi h (fun t' => line h σ t') a t = (σ - a) * krad h σ t a :=
    psi_eq_mul_krad h1 σ t a
  have hsqrt : Real.sqrt (psi h (fun t' => line h σ t') a t)
      = Real.sqrt (σ - a) * Real.sqrt (krad h σ t a) := by
    rw [hpsi_a, Real.sqrt_mul (le_of_lt hsub)]
  have hkR : Real.sqrt (krad h σ t a) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hR)
  show J2 n h a σ t / Kden h a σ t = _
  rw [hJ2, Kden_eq_sqrt_krad, hiter, hsqrt]
  field_simp

/-! ## The diagonal extension of the two Abel kernels

Write `H(v) = (σ - v) krad(v)`, so that `ψ(v) = H(v)`.  Faà-di-Bruno (`faaDiBrunoJ_spec`)
turns `∂^{n+1} H^{n+1/2}` into a *polynomial in the jet of `H`*, and the factor `√(σ-a)` of
`K1_eq_sqrt_mul` exactly cancels the `H(a)^{-1/2}` produced by that formula.  The result is an
expression that is smooth in `(a,σ,t)` **wherever `krad > 0`**, with no restriction at `a = σ`:
this is the extension of the kernel across the diagonal.
-/

/-- The jet of the function `v ↦ (σ - v) * krad h σ t v` at the point `a`. -/
def kjet (h : ℝ → ℝ) (σ t a : ℝ) (i : ℕ) : ℝ :=
  iteratedDeriv i (fun v : ℝ => (σ - v) * krad h σ t v) a

/-- The diagonal extension of the first Abel kernel. -/
def k1ext (n : ℕ) (h : ℝ → ℝ) (σ t a : ℝ) : ℝ :=
  Commons.Geometry.Ulam.faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) a
      (fun i : Fin (n + 2) => kjet h σ t a i.1) / Real.sqrt (krad h σ t a)

/-- The diagonal extension of the second Abel kernel. -/
def k2ext (n : ℕ) (h : ℝ → ℝ) (σ t a : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    ((n.choose i : ℕ) : ℝ) *
      Commons.Geometry.Ulam.faaDiBrunoJ i ((n : ℝ) - 1 / 2) a
        (fun j : Fin (i + 1) => kjet h σ t a j.1) *
      (σ - a) ^ (n - i) * (krad h σ t a) ^ ((n : ℝ) - 1 / 2 - (i : ℝ)) *
      iteratedDeriv (n - i) (fun v : ℝ => lineSlope h v t) a

lemma kjet_zero (h : ℝ → ℝ) (σ t a : ℝ) : kjet h σ t a 0 = (σ - a) * krad h σ t a := by
  simp [kjet]

lemma kjet_succ (h : ℝ → ℝ) (σ t a : ℝ) (i : ℕ) :
    kjet h σ t a (i + 1) = deriv (fun v : ℝ => kjet h σ t v i) a := by
  simp only [kjet, iteratedDeriv_succ]

section Smoothness

variable {h : ℝ → ℝ}

/-- `krad` is smooth as a function of `((σ,t),a)`. -/
lemma contDiff_krad_full (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => krad h q.1.1 q.1.2 q.2) := by
  unfold krad line
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => hquot h q.2 q.1.1) :=
    (Work.OddVolterra.Existence.hquot_contDiff hh).comp
      (f := fun q : (ℝ × ℝ) × ℝ => (q.2, q.1.1)) (by fun_prop)
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => q.1.2) := by fun_prop
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => h q.1.1) :=
    hh.comp (f := fun q : (ℝ × ℝ) × ℝ => q.1.1) (by fun_prop)
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => q.1.1 * q.1.2) := by fun_prop
  have h4 : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => h q.2) :=
    hh.comp (f := fun q : (ℝ × ℝ) × ℝ => q.2) (by fun_prop)
  have h5 : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => q.2 * q.1.2) := by fun_prop
  exact (h1.add hq).mul ((h3.add h2).add (h5.add h4))

/-- `krad` is smooth in the point variable. -/
lemma contDiff_krad (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => krad h σ t a) :=
  (contDiff_krad_full hh).comp (f := fun a : ℝ => ((σ, t), a)) (by fun_prop)

/-- The jet of `H` depends smoothly on `(a,σ,t)`. -/
lemma contDiff_kjet (hh : ContDiff ℝ (⊤ : ℕ∞) h) (i : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => kjet h q.1.1 q.1.2 q.2 i) := by
  have hU : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ =>
      (q.1.1 - q.2) * krad h q.1.1 q.1.2 q.2) :=
    ((by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : (ℝ × ℝ) × ℝ => q.1.1 - q.2))).mul (contDiff_krad_full hh)
  have hpar := Commons.Analysis.Calculus.contDiff_parametric_iteratedDeriv_gen
    (P := ℝ × ℝ) (G := fun p : ℝ × ℝ => fun v : ℝ => (p.1 - v) * krad h p.1 p.2 v) (k := i)
    (by simpa only [Function.comp_apply] using hU)
  simpa only [kjet, Function.comp_apply] using hpar

/-- Faà-di-Bruno `J` is a polynomial in the jet variable, hence smooth everywhere. -/
lemma faaDiBrunoJ_contDiff_poly (m : ℕ) (α s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : Fin (m + 1) → ℝ =>
      Commons.Geometry.Ulam.faaDiBrunoJ m α s v) := by
  unfold Commons.Geometry.Ulam.faaDiBrunoJ
  refine ContDiff.sum (fun c _ => ?_)
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun v : Fin (m + 1) → ℝ =>
      ∏ j : Fin c.length, v ⟨c.partSize j, Nat.lt_succ_of_le (c.partSize_le j)⟩) := by
    refine contDiff_prod (t := Finset.univ)
      (f := fun j : Fin c.length => fun v : Fin (m + 1) → ℝ =>
        v ⟨c.partSize j, Nat.lt_succ_of_le (c.partSize_le j)⟩) (fun j _ => ?_)
    exact contDiff_apply ℝ ℝ _
  exact (contDiff_const.mul h1).mul ((contDiff_apply ℝ ℝ _).pow _)

/-- A positive smooth function has a smooth `rpow`. -/
lemma contDiff_rpow_const {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {s : Set X} (hs : IsOpen s) {u : X → ℝ} (h : ContDiffOn ℝ (⊤ : ℕ∞) u s)
    (hne : ∀ x ∈ s, u x ≠ 0) (p : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => u x ^ p) s := by
  intro x hx
  have hx' : s ∈ 𝓝 x := hs.mem_nhds hx
  exact (((Real.contDiffAt_rpow_const_of_ne (p := p) (hne x hx)).comp x
    (h.contDiffAt hx'))).contDiffWithinAt

end Smoothness

/-- **Structural form of the first Abel kernel, valid across the diagonal.**  Off the
diagonal and where `krad > 0` the kernel equals its explicit smooth extension. -/
theorem K1_eq_k1ext {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (n : ℕ)
    {a σ t : ℝ} (ha : a < σ) (hR : 0 < krad h σ t a) :
    K1 n h a σ t = k1ext n h σ t a := by
  have hsub : 0 < σ - a := sub_pos.mpr ha
  have hHpos : 0 < (σ - a) * krad h σ t a := mul_pos hsub hR
  have hHcont : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => (σ - v) * krad h σ t v) :=
    (contDiff_const.sub contDiff_id).mul (contDiff_krad hh σ t)
  rw [K1_eq_sqrt_mul hh n ha hR]
  unfold k1ext
  rw [Commons.Geometry.Ulam.faaDiBrunoJ_spec (n + 1) ((n : ℝ) + 1 / 2)
        (fun v : ℝ => (σ - v) * krad h σ t v) a hHcont hHpos]
  have hpow : ((n : ℝ) + 1 / 2) - (((n + 1 : ℕ)) : ℝ) = -(1 / 2) := by push_cast; ring
  rw [hpow]
  have hfac : ((σ - a) * krad h σ t a) ^ (-(1 / 2) : ℝ)
      = (σ - a) ^ (-(1 / 2) : ℝ) * (krad h σ t a) ^ (-(1 / 2) : ℝ) :=
    Real.mul_rpow (le_of_lt hsub) (le_of_lt hR)
  have hsqrt_cancel : Real.sqrt (σ - a) * (σ - a) ^ (-(1 / 2) : ℝ) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hsub]
    norm_num
  have hinv_sqrt : (krad h σ t a) ^ (-(1 / 2) : ℝ) = (Real.sqrt (krad h σ t a))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (le_of_lt hR)]
  rw [hfac, hinv_sqrt]
  simp only [kjet]
  have hnum : Real.sqrt (σ - a) * (σ - a) ^ (-(1 / 2) : ℝ) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hsub]
    norm_num
  have hmul : ∀ F G : ℝ, Real.sqrt (σ - a) * (F * ((σ - a) ^ (-(1 / 2) : ℝ) * G))
      = F * (Real.sqrt (σ - a) * (σ - a) ^ (-(1 / 2) : ℝ)) * G := fun F G => by ring
  rw [hmul, hnum, mul_one]
  simp only [div_eq_mul_inv]


/-- The region on which the two kernels coincide with their smooth diagonal extensions:
`a` lies strictly below `σ` and both denominator radicands (at the two section endpoints
carried by the state `z`) are positive. -/
def Kgood (h : ℝ → ℝ) (σ : ℝ) (z : St) : Set ℝ :=
  {a : ℝ | a < σ ∧ 0 < krad h σ (-(z 0)) a ∧ 0 < krad h σ (z 1) a}

/-- For `m ≥ 1` the `m`-th derivative of `v ↦ lineSlope h v t` is the `(m+1)`-st
derivative of `h` (for `m = 0` the value is `t + h'` instead). -/
lemma iteratedDeriv_succ_add_const (m : ℕ) (c : ℝ) (g : ℝ → ℝ) (a : ℝ) :
    iteratedDeriv (m + 1) (fun v : ℝ => c + g v) a = iteratedDeriv (m + 1) g a := by
  have hfun : deriv (fun v : ℝ => c + g v) = deriv g := by
    funext v
    exact deriv_const_add (𝕜 := ℝ) (F := ℝ) (f := g) (x := v) c
  rw [iteratedDeriv_succ', iteratedDeriv_succ', hfun]

theorem K2_eq_k2ext {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (n : ℕ) (hn : 1 ≤ n)
    {a σ t : ℝ} (ha : a < σ) (hR : 0 < krad h σ t a) :
    K2 n h a σ t = k2ext n h σ t a := by
  have hsub : 0 < σ - a := sub_pos.mpr ha
  have hHpos : 0 < (σ - a) * krad h σ t a := mul_pos hsub hR
  have hHcont : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => (σ - v) * krad h σ t v) :=
    (contDiff_const.sub contDiff_id).mul (contDiff_krad hh σ t)
  have hLcont : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => lineSlope h v t) := by
    have : (fun v : ℝ => lineSlope h v t) = fun v : ℝ => t + deriv h v := by funext v; rfl
    rw [this]
    exact contDiff_const.add hh.deriv'
  rw [K2_eq_sqrt_mul hh n hn ha hR]
  have hfd : ContDiffAt ℝ (n : ℕ∞)
      (fun v : ℝ => ((σ - v) * krad h σ t v) ^ ((n : ℝ) - 1 / 2)) a :=
    (Real.contDiffAt_rpow_const_of_ne (p := (n : ℝ) - 1 / 2) (ne_of_gt hHpos)).comp a
      (hHcont.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  have hgd : ContDiffAt ℝ (n : ℕ∞) (fun v : ℝ => lineSlope h v t) a :=
    (hLcont.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hprod : (fun v : ℝ => ((σ - v) * krad h σ t v) ^ ((n : ℝ) - 1 / 2) * lineSlope h v t)
      = (fun v : ℝ => ((σ - v) * krad h σ t v) ^ ((n : ℝ) - 1 / 2)) *
        (fun v : ℝ => lineSlope h v t) := rfl
  rw [hprod, iteratedDeriv_mul hfd hgd]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  have hile : i ≤ n := Nat.lt_succ_iff.mp hi
  rw [Commons.Geometry.Ulam.faaDiBrunoJ_spec i ((n : ℝ) - 1 / 2)
        (fun v : ℝ => (σ - v) * krad h σ t v) a hHcont hHpos]
  -- now a pure `rpow` computation
  have hΨ : ((σ - a) * krad h σ t a) ^ (((n : ℝ) - 1 / 2) - (i : ℝ))
      = ((σ - a) ^ (((n : ℝ) - 1 / 2) - (i : ℝ))) *
        ((krad h σ t a) ^ (((n : ℝ) - 1 / 2) - (i : ℝ))) :=
    Real.mul_rpow (le_of_lt hsub) (le_of_lt hR)
  have hsqrt : Real.sqrt (σ - a) * (σ - a) ^ (((n : ℝ) - 1 / 2) - (i : ℝ))
      = (σ - a) ^ (n - i) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hsub]
    rw [show (1 / 2 : ℝ) + (((n : ℝ) - 1 / 2) - (i : ℝ)) = ((n - i : ℕ) : ℝ) from by
      rw [Nat.cast_sub hile]; ring]
    exact Real.rpow_natCast (σ - a) (n - i)
  rw [hΨ]
  simp only [kjet]
  calc Real.sqrt (σ - a) *
        (((n.choose i : ℕ) : ℝ) *
          (Commons.Geometry.Ulam.faaDiBrunoJ i ((n : ℝ) - 1 / 2) a
              (fun j : Fin (i + 1) =>
                iteratedDeriv (j : ℕ) (fun v : ℝ => (σ - v) * krad h σ t v) a) *
            ((σ - a) ^ (((n : ℝ) - 1 / 2) - (i : ℝ)) *
              (krad h σ t a) ^ (((n : ℝ) - 1 / 2) - (i : ℝ)))) *
          iteratedDeriv (n - i) (fun v : ℝ => lineSlope h v t) a)
      = ((n.choose i : ℕ) : ℝ) *
          Commons.Geometry.Ulam.faaDiBrunoJ i ((n : ℝ) - 1 / 2) a
            (fun j : Fin (i + 1) =>
              iteratedDeriv (j : ℕ) (fun v : ℝ => (σ - v) * krad h σ t v) a) *
          (Real.sqrt (σ - a) * (σ - a) ^ (((n : ℝ) - 1 / 2) - (i : ℝ))) *
          (krad h σ t a) ^ (((n : ℝ) - 1 / 2) - (i : ℝ)) *
          iteratedDeriv (n - i) (fun v : ℝ => lineSlope h v t) a := by ring
    _ = ((n.choose i : ℕ) : ℝ) *
          Commons.Geometry.Ulam.faaDiBrunoJ i ((n : ℝ) - 1 / 2) a
            (fun j : Fin (i + 1) =>
              iteratedDeriv (j : ℕ) (fun v : ℝ => (σ - v) * krad h σ t v) a) *
          (σ - a) ^ (n - i) *
          (krad h σ t a) ^ (((n : ℝ) - 1 / 2) - (i : ℝ)) *
          iteratedDeriv (n - i) (fun v : ℝ => lineSlope h v t) a := by rw [hsqrt]

/-! ## Smoothness and bounds of the diagonal extensions -/

section ExtSmooth

variable {h : ℝ → ℝ}

/-- The partial derivative in the second variable of a jointly smooth function is jointly
smooth (general parameter space). -/
theorem contDiffOn_deriv_snd_gen {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set (P × ℝ)} (hU : IsOpen U) {F : P × ℝ → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : P × ℝ => deriv (fun v : ℝ => F (q.1, v)) q.2) U := by
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : P × ℝ => fderiv ℝ F q ((0 : P), (1 : ℝ))) U :=
    ((hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const)
  refine hH.congr ?_
  intro q hq
  have hq_nhds : U ∈ 𝓝 q := hU.mem_nhds hq
  have hdiff : DifferentiableAt ℝ F q :=
    (hF.differentiableOn (by simp)).differentiableAt hq_nhds
  have hlin : HasFDerivAt (fun v : ℝ => (q.1, v)) (ContinuousLinearMap.inr ℝ P ℝ) q.2 :=
    hasFDerivAt_prodMk_right q.1 q.2
  have hcomp := hdiff.hasFDerivAt.comp q.2 hlin
  have hder := hcomp.hasDerivAt
  have hfun : (fun v : ℝ => F (q.1, v)) = F ∘ fun v : ℝ => (q.1, v) := rfl
  rw [hfun, hder.deriv]
  simp [ContinuousLinearMap.comp_apply]

/-- The first diagonal extension is smooth (jointly in `(σ,t,a)`) wherever `krad > 0`. -/
theorem contDiffOn_k1ext (n : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => k1ext n h q.1.1 q.1.2 q.2)
      {q : (ℝ × ℝ) × ℝ | 0 < krad h q.1.1 q.1.2 q.2} := by
  have hjet : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ =>
      (fun i : Fin (n + 2) => kjet h q.1.1 q.1.2 q.2 i.1)) := by
    rw [contDiff_pi]
    intro i
    exact contDiff_kjet hh i.1
  have hpoly : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin (n + 2) → ℝ) =>
      Commons.Geometry.Ulam.faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) p.1 p.2) := by
    have h0 := faaDiBrunoJ_contDiff_poly (n + 1) ((n : ℝ) + 1 / 2) 0
    have heq : (fun p : ℝ × (Fin (n + 2) → ℝ) =>
        Commons.Geometry.Ulam.faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) p.1 p.2)
        = fun p : ℝ × (Fin (n + 2) → ℝ) =>
          Commons.Geometry.Ulam.faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) 0 p.2 := by
      funext p; rfl
    rw [heq]
    exact h0.comp (by fun_prop)
  have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ =>
      (q.2, (fun i : Fin (n + 2) => kjet h q.1.1 q.1.2 q.2 i.1))) :=
    (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => q.2)).prodMk hjet
  have hnum : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ =>
      Commons.Geometry.Ulam.faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) q.2
        (fun i : Fin (n + 2) => kjet h q.1.1 q.1.2 q.2 i.1)) :=
    hpoly.comp hpair
  unfold k1ext
  refine ContDiffOn.div hnum.contDiffOn ?_ ?_
  · refine ContDiffOn.sqrt ((contDiff_krad_full hh).contDiffOn) ?_
    intro q hq
    exact ne_of_gt hq
  · intro q hq
    exact ne_of_gt (Real.sqrt_pos_of_pos hq)

/-- The second diagonal extension is smooth (jointly in `(σ,t,a)`) wherever `krad > 0`. -/
theorem contDiffOn_k2ext (n : ℕ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => k2ext n h q.1.1 q.1.2 q.2)
      {q : (ℝ × ℝ) × ℝ | 0 < krad h q.1.1 q.1.2 q.2} := by
  unfold k2ext
  refine ContDiffOn.sum (fun i hi => ?_)
  refine ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul
    contDiffOn_const ?_) ?_) ?_) ?_
  · -- Faà-di-Bruno factor, smooth in the jet
    have hjet : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ =>
        (fun j : Fin (i + 1) => kjet h q.1.1 q.1.2 q.2 j.1)) := by
      rw [contDiff_pi]
      intro j
      exact contDiff_kjet hh j.1
    have hpoly : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin (i + 1) → ℝ) =>
        Commons.Geometry.Ulam.faaDiBrunoJ i ((n : ℝ) - 1 / 2) p.1 p.2) := by
      have h0 := faaDiBrunoJ_contDiff_poly i ((n : ℝ) - 1 / 2) 0
      have heq : (fun p : ℝ × (Fin (i + 1) → ℝ) =>
          Commons.Geometry.Ulam.faaDiBrunoJ i ((n : ℝ) - 1 / 2) p.1 p.2)
          = fun p : ℝ × (Fin (i + 1) → ℝ) =>
            Commons.Geometry.Ulam.faaDiBrunoJ i ((n : ℝ) - 1 / 2) 0 p.2 := by
        funext p; rfl
      rw [heq]
      exact h0.comp (by fun_prop)
    have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ =>
        (q.2, (fun j : Fin (i + 1) => kjet h q.1.1 q.1.2 q.2 j.1))) :=
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => q.2)).prodMk hjet
    exact (hpoly.comp hpair).contDiffOn
  · -- `(σ - a) ^ (n - i)`
    have : (fun q : (ℝ × ℝ) × ℝ => (q.1.1 - q.2) ^ (n - i))
        = fun q : (ℝ × ℝ) × ℝ => (fun q : (ℝ × ℝ) × ℝ => q.1.1 - q.2) q ^ (n - i) := rfl
    rw [this]
    exact ContDiffOn.pow (by fun_prop) _
  · -- `krad ^ (…)`
    refine contDiff_rpow_const
      (isOpen_lt continuous_const (contDiff_krad_full hh).continuous) ?_ ?_ _
    · exact (contDiff_krad_full hh).contDiffOn
    · intro q hq; exact ne_of_gt hq
  · -- the derivative of `lineSlope`
    have hG : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => lineSlope h p.2 p.1) := by
      have heq : (fun p : ℝ × ℝ => lineSlope h p.2 p.1) = fun p : ℝ × ℝ => p.1 + deriv h p.2 := by
        funext p; rfl
      rw [heq]
      exact (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => p.1)).add
        ((hh.deriv').comp (by fun_prop))
    have hpar := Commons.Analysis.Calculus.contDiff_parametric_iteratedDeriv_gen
      (P := ℝ) (G := fun p : ℝ => fun v : ℝ => lineSlope h v p) (k := n - i)
      (by simpa using hG)
    exact (hpar.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × ℝ) × ℝ => (q.1.2, q.2)))).contDiffOn

end ExtSmooth


end

section Bounds

variable {h : ℝ → ℝ}

/-- The `(σ,a)`-trapezium `s - δ ≤ a ≤ σ ≤ 1`. -/
def triLo (s δ : ℝ) : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ∈ Set.Icc s 1 ∧ p.2 ∈ Set.Icc (s - δ) p.1}

/-- The graph of `t` over the trapezium, in the `((σ,t),a)`-coordinates of the extensions. -/
def graphSet (t : ℝ → ℝ) (s δ : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  (fun p : ℝ × ℝ => ((p.1, t p.1), p.2)) '' triLo s δ

/-- The positivity region of the kernel extensions. -/
def extGood (h : ℝ → ℝ) : Set ((ℝ × ℝ) × ℝ) := {q : (ℝ × ℝ) × ℝ | 0 < krad h q.1.1 q.1.2 q.2}

lemma triLo_eq (s δ : ℝ) :
    triLo s δ = (Set.Icc s 1 ×ˢ Set.Icc (s - δ) 1) ∩ {p : ℝ × ℝ | p.2 ≤ p.1} := by
  ext p
  simp only [triLo, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3, le_trans h4 h2⟩, h4⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3, _⟩, h4⟩
    exact ⟨⟨h1, h2⟩, h3, h4⟩

lemma isCompact_triLo (s δ : ℝ) : IsCompact (triLo s δ) := by
  rw [triLo_eq]
  exact (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_snd continuous_fst)

lemma isCompact_graphSet {t : ℝ → ℝ} {s δ : ℝ} (ht : ContinuousOn t (Set.Icc s 1)) :
    IsCompact (graphSet t s δ) := by
  refine (isCompact_triLo s δ).image_of_continuousOn ?_
  exact ((continuous_fst.continuousOn).prodMk
      (ht.comp continuous_fst.continuousOn (fun p hp => hp.1))).prodMk
    continuous_snd.continuousOn

lemma isOpen_extGood (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) : IsOpen (extGood h) :=
  isOpen_lt continuous_const (contDiff_krad_full hh).continuous

/-- **Uniform bound on the two Abel kernels and their first-argument derivatives.**

On the trapezium `s - δ ≤ a ≤ σ ≤ 1`, with the denominator radicands positive along the graph
`σ ↦ t σ` of a continuous function `t`, the kernels `K₁`, `K₂` and their derivatives in the
first slot are bounded by a single constant.  This is what makes the diagonal singularity
harmless in the dominated-convergence argument for `G₂`. -/
theorem K1_K2_deriv_bound (n : ℕ) (hn : 1 ≤ n) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {s δ : ℝ} (hδ : 0 < δ) {t : ℝ → ℝ} (ht : ContinuousOn t (Set.Icc s 1))
    (hpos : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Icc (s - δ) σ, 0 < krad h σ (t σ) a) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Ico (s - δ) σ,
      ‖K1 n h a σ (t σ)‖ ≤ C ∧ ‖K2 n h a σ (t σ)‖ ≤ C ∧
      ‖deriv (fun u : ℝ => K1 n h u σ (t σ)) a‖ ≤ C ∧
      ‖deriv (fun u : ℝ => K2 n h u σ (t σ)) a‖ ≤ C := by
  have hP : IsCompact (graphSet t s δ) := isCompact_graphSet ht
  have hDsub : graphSet t s δ ⊆ extGood h := by
    rintro q ⟨p, hp, rfl⟩
    show 0 < krad h p.1 (t p.1) p.2
    exact hpos p.1 hp.1 p.2 hp.2
  have hUopen : IsOpen (extGood h) := isOpen_extGood h hh
  have hc1 : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => k1ext n h q.1.1 q.1.2 q.2) (extGood h) :=
    (contDiffOn_k1ext n hh).continuousOn
  have hc2 : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => k2ext n h q.1.1 q.1.2 q.2) (extGood h) :=
    (contDiffOn_k2ext n hh).continuousOn
  have hd1 : ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
      deriv (fun a : ℝ => k1ext n h q.1.1 q.1.2 a) q.2) (extGood h) :=
    (contDiffOn_deriv_snd_gen hUopen (contDiffOn_k1ext n hh)).continuousOn
  have hd2 : ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
      deriv (fun a : ℝ => k2ext n h q.1.1 q.1.2 a) q.2) (extGood h) :=
    (contDiffOn_deriv_snd_gen hUopen (contDiffOn_k2ext n hh)).continuousOn
  obtain ⟨C1, hC1⟩ := hP.exists_bound_of_continuousOn (hc1.mono hDsub)
  obtain ⟨C2, hC2⟩ := hP.exists_bound_of_continuousOn (hc2.mono hDsub)
  obtain ⟨C3, hC3⟩ := hP.exists_bound_of_continuousOn (hd1.mono hDsub)
  obtain ⟨C4, hC4⟩ := hP.exists_bound_of_continuousOn (hd2.mono hDsub)
  refine ⟨max 1 (max (max C1 C2) (max C3 C4)), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro σ hσ a ha
  have ha' : a ∈ Set.Icc (s - δ) σ := ⟨ha.1, le_of_lt ha.2⟩
  have hpS : (σ, a) ∈ triLo s δ := ⟨hσ, ha'⟩
  have hqP : ((σ, t σ), a) ∈ graphSet t s δ := ⟨(σ, a), hpS, rfl⟩
  have hkrad : 0 < krad h σ (t σ) a := hpos σ hσ a ha'
  have hK1 : K1 n h a σ (t σ) = k1ext n h σ (t σ) a := K1_eq_k1ext hh n (lt_of_lt_of_le ha.2 le_rfl) hkrad
  have hK2 : K2 n h a σ (t σ) = k2ext n h σ (t σ) a :=
    K2_eq_k2ext hh n hn (lt_of_lt_of_le ha.2 le_rfl) hkrad
  have hnhds : {u : ℝ | u < σ ∧ 0 < krad h σ (t σ) u} ∈ 𝓝 a :=
    ((isOpen_lt continuous_id continuous_const).inter
      (isOpen_lt continuous_const (continuous_krad hh σ (t σ)))).mem_nhds
        ⟨lt_of_lt_of_le ha.2 le_rfl, hkrad⟩
  have heq1 : (fun u : ℝ => K1 n h u σ (t σ)) =ᶠ[𝓝 a]
      (fun u : ℝ => k1ext n h σ (t σ) u) := by
    filter_upwards [hnhds] with u hu
    exact K1_eq_k1ext hh n hu.1 hu.2
  have heq2 : (fun u : ℝ => K2 n h u σ (t σ)) =ᶠ[𝓝 a]
      (fun u : ℝ => k2ext n h σ (t σ) u) := by
    filter_upwards [hnhds] with u hu
    exact K2_eq_k2ext hh n hn hu.1 hu.2
  have hle1 : C1 ≤ max 1 (max (max C1 C2) (max C3 C4)) :=
    le_trans (le_trans (le_max_left C1 C2) (le_max_left _ _)) (le_max_right _ _)
  have hle2 : C2 ≤ max 1 (max (max C1 C2) (max C3 C4)) :=
    le_trans (le_trans (le_max_right C1 C2) (le_max_left _ _)) (le_max_right _ _)
  have hle3 : C3 ≤ max 1 (max (max C1 C2) (max C3 C4)) :=
    le_trans (le_trans (le_max_left C3 C4) (le_max_right _ _)) (le_max_right _ _)
  have hle4 : C4 ≤ max 1 (max (max C1 C2) (max C3 C4)) :=
    le_trans (le_trans (le_max_right C3 C4) (le_max_right _ _)) (le_max_right _ _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hK1]
    have hpt : k1ext n h σ (t σ) a = (fun q : (ℝ × ℝ) × ℝ => k1ext n h q.1.1 q.1.2 q.2) ((σ, t σ), a) := rfl
    rw [hpt]
    exact le_trans (hC1 _ hqP) hle1
  · rw [hK2]
    have hpt : k2ext n h σ (t σ) a = (fun q : (ℝ × ℝ) × ℝ => k2ext n h q.1.1 q.1.2 q.2) ((σ, t σ), a) := rfl
    rw [hpt]
    exact le_trans (hC2 _ hqP) hle2
  · rw [heq1.deriv_eq]
    have hpt : deriv (fun u : ℝ => k1ext n h σ (t σ) u) a
        = (fun q : (ℝ × ℝ) × ℝ => deriv (fun u : ℝ => k1ext n h q.1.1 q.1.2 u) q.2) ((σ, t σ), a) := rfl
    rw [hpt]
    exact le_trans (hC3 _ hqP) hle3
  · rw [heq2.deriv_eq]
    have hpt : deriv (fun u : ℝ => k2ext n h σ (t σ) u) a
        = (fun q : (ℝ × ℝ) × ℝ => deriv (fun u : ℝ => k2ext n h q.1.1 q.1.2 u) q.2) ((σ, t σ), a) := rfl
    rw [hpt]
    exact le_trans (hC4 _ hqP) hle4

end Bounds


section Margin

variable {h : ℝ → ℝ}

/-- Extension of a function continuous on `[s,1]` to a globally continuous function. -/
def tExt (t : ℝ → ℝ) (s : ℝ) (σ : ℝ) : ℝ := t (max (min σ 1) s)

lemma tExt_continuous {t : ℝ → ℝ} {s : ℝ} (hs1 : s ≤ 1)
    (ht : ContinuousOn t (Set.Icc s 1)) : Continuous (tExt t s) := by
  have h1 : Continuous (fun σ : ℝ => max (min σ 1) s) := by fun_prop
  have h2 : ∀ σ : ℝ, max (min σ 1) s ∈ Set.Icc s 1 := by
    intro σ
    exact ⟨le_max_right _ _, max_le (min_le_right _ _) (by simpa using hs1)⟩
  exact ht.comp_continuous h1 h2

lemma tExt_eq {t : ℝ → ℝ} {s : ℝ} {σ : ℝ} (hσ : σ ∈ Set.Icc s 1) :
    tExt t s σ = t σ := by
  have h1 : min σ 1 = σ := min_eq_left hσ.2
  have h2 : max σ s = σ := max_eq_left hσ.1
  simp only [tExt, h1, h2]

/-- **Positivity margin.**  If the denominator radicand `krad h σ (t σ) a` is positive on the
triangle `s ≤ a ≤ σ ≤ 1` (for a continuous `t`), then it stays positive on a slightly larger
trapezium `s - δ ≤ a ≤ σ ≤ 1`.  This is what lets the parameter `x` in the differentiation
lemma run over a full two-sided neighbourhood of `s`. -/
theorem exists_pos_margin (hh : ContDiff ℝ (⊤ : ℕ∞) h) {t : ℝ → ℝ} {s : ℝ} (hs1 : s ≤ 1)
    (ht : ContinuousOn t (Set.Icc s 1))
    (hpos : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Icc s σ, 0 < krad h σ (t σ) a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Icc (s - δ) σ, 0 < krad h σ (t σ) a := by
  have hte : Continuous (tExt t s) := tExt_continuous hs1 ht
  have hF : Continuous (fun p : ℝ × ℝ => krad h p.1 (tExt t s p.1) p.2) := by
    have hfun : (fun p : ℝ × ℝ => krad h p.1 (tExt t s p.1) p.2)
        = fun p : ℝ × ℝ =>
            ((tExt t s p.1) + hquot h p.2 p.1) *
              (((p.1 * (tExt t s p.1) + h p.1) + (p.2 * (tExt t s p.1) + h p.2))) := by
      funext p
      simp only [krad, line]
    rw [hfun]
    exact ((hte.comp continuous_fst).add
        ((Work.OddVolterra.Existence.hquot_contDiff hh).continuous.comp
          (continuous_snd.prodMk continuous_fst))).mul
      (((continuous_fst.mul (hte.comp continuous_fst)).add (hh.continuous.comp continuous_fst)).add
        ((continuous_snd.mul (hte.comp continuous_fst)).add (hh.continuous.comp continuous_snd)))
  set E : Set (ℝ × ℝ) := ((Set.Icc s 1 ×ˢ Set.Icc (s - 1) 1) ∩ {p : ℝ × ℝ | p.2 ≤ p.1}) ∩
      {p : ℝ × ℝ | krad h p.1 (tExt t s p.1) p.2 ≤ 0} with hEdef
  have hEclosed : IsClosed E := by
    rw [hEdef]
    exact ((isClosed_Icc.prod isClosed_Icc).inter
      (isClosed_le continuous_snd continuous_fst)).inter
      (isClosed_le hF continuous_const)
  have hEcomp : IsCompact E :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hEclosed
      (fun p hp => hp.1.1)
  have hEmem : ∀ {p : ℝ × ℝ}, p ∈ E ↔ p.1 ∈ Set.Icc s 1 ∧ p.2 ∈ Set.Icc (s - 1) 1 ∧
      p.2 ≤ p.1 ∧ krad h p.1 (tExt t s p.1) p.2 ≤ 0 := by
    intro p
    rw [hEdef]
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc, Set.mem_setOf_eq]
    tauto
  have hEsub : ∀ p ∈ E, krad h p.1 (t p.1) p.2 ≤ 0 := by
    intro p hp
    have h1 : krad h p.1 (tExt t s p.1) p.2 ≤ 0 := (hEmem.mp hp).2.2.2
    rw [tExt_eq (hEmem.mp hp).1] at h1
    exact h1
  by_cases hne : E.Nonempty
  · obtain ⟨p₀, hp₀, hmax⟩ := hEcomp.exists_isMaxOn hne continuous_snd.continuousOn
    have hp₀le : p₀.2 ≤ p₀.1 := (hEmem.mp hp₀).2.2.1
    have hp₀F : krad h p₀.1 (t p₀.1) p₀.2 ≤ 0 := hEsub p₀ hp₀
    have hp₀lt : p₀.2 < s := by
      by_contra hge
      have hmem : p₀.2 ∈ Set.Icc s p₀.1 := ⟨le_of_not_gt hge, hp₀le⟩
      exact absurd (hpos p₀.1 (hEmem.mp hp₀).1 p₀.2 hmem) (not_lt.mpr hp₀F)
    refine ⟨min ((s - p₀.2) / 2) 1, lt_min (half_pos (sub_pos.mpr hp₀lt)) one_pos, ?_⟩
    intro σ hσ a ha
    by_contra hcon
    have haE : (σ, a) ∈ E := by
      refine hEmem.mpr ⟨hσ, ⟨?_, le_trans ha.2 hσ.2⟩, ha.2, ?_⟩
      · linarith [min_le_right ((s - p₀.2) / 2) 1, ha.1]
      · rw [tExt_eq hσ]
        exact le_of_not_gt hcon
    have ha₂ : a ≤ p₀.2 := isMaxOn_iff.mp hmax (σ, a) haE
    have hge : (s + p₀.2) / 2 ≤ a := by
      have h1 : min ((s - p₀.2) / 2) 1 ≤ (s - p₀.2) / 2 := min_le_left _ _
      linarith [ha.1]
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro σ hσ a ha
    by_contra hcon
    refine hne ⟨(σ, a), ?_⟩
    refine hEmem.mpr ⟨hσ, ⟨by linarith [ha.1], le_trans ha.2 hσ.2⟩, ha.2, ?_⟩
    rw [tExt_eq hσ]
    exact le_of_not_gt hcon

end Margin

end Work.OddVolterra
