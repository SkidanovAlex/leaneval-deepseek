import Mathlib
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.Rnu_spec

/-!
# The manifest Abel numerators agree with the paper's off the diagonal

`Work.OddVolterra.J1` and `J2` are the paper's numerators of the two Abel kernels `K₁`, `K₂`.
They are defined with a case split: off the diagonal `σ ≠ s` they are the differentiated moment
integrands, on the diagonal they are the explicit limit values (handled in
`Work.OddVolterra.KernelExt.JM_diag`).

`Work.OddVolterra.KernelExt.J1M` and `J2M` are the manifest polynomial representatives obtained
from the recursion `R_{m+1} = Z ∂_s R_m + (ν - m)(∂_s Z) R_m`, where `Z = Zrad` is the radicand
`L(σ,t)² - L(s,t)²`.

This file proves that the two agree at every *off-diagonal* point where the radicand is positive,
which is exactly the hypothesis `hR` of the paper (the product `(t + H)(L_σ + L_s)` is positive,
and `Z = (σ-s)·(t+H)·(L_σ + L_s)`).  The engine is `Work.OddVolterra.KernelExt.Rnu_spec`, which identifies
`Rnu` with `∂_s^m[Z^ν · init]·Z^{m-ν}`; the remaining work is the pointwise identity
`Z^{n+1/2} = Z^n √Z` (resp. `Z^{n-1/2} = Z^{n-1} √Z`, which is where `1 ≤ n` is needed) on the
open set `{Z > 0}`, together with the exponent bookkeeping `Z^{m-ν} = √Z`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.KernelExt

open Work.OddVolterra

noncomputable section

/-! ## The radicand -/

/-- The difference of the two chord values is `(σ-s)` times the paper's quotient `H`: this is
the identity `L(σ,t) - L(s,t) = (σ-s)(t + H(s,σ))`, i.e. `h σ - h s = (σ-s)H(s,σ)` plus `(σ-s)t`. -/
lemma line_sub_line {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s σ t : ℝ) :
    line h σ t - line h s t = (σ - s) * (t + hquot h s σ) := by
  have h2 := sub_mul_hquot (h := h) (hh.of_le (by norm_num)) s σ
  unfold line
  linear_combination h2

/-- `ψ` for the profile `L(σ,·)` is exactly the radicand `Zrad` at the triple `(u,σ,t)`. -/
lemma psi_line_eq_Zrad (h : ℝ → ℝ) (σ u t : ℝ) :
    psi h (fun t' => line h σ t') u t = Zrad h (u, σ, t) := rfl

/-- **Positivity of the radicand** at an off-diagonal point, from the paper's hypothesis that
the two factors `t + H(s,σ)` and `L(σ,t) + L(s,t)` have positive product. -/
lemma Zrad_pos_of_hR {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s σ t : ℝ} (hsσ : s < σ)
    (hR : 0 < (t + hquot h s σ) * (line h σ t + line h s t)) :
    0 < Zrad h (s, σ, t) := by
  have hfac : Zrad h (s, σ, t) = (line h σ t - line h s t) * (line h σ t + line h s t) := by
    unfold Zrad; ring
  rw [hfac, line_sub_line hh s σ t, mul_assoc]
  exact mul_pos (by linarith) hR

/-! ## Half-integer powers versus the square root -/

/-- On the positive half-line, `Z^{n+1/2} = Z^n √Z`. -/
lemma rpow_add_half_nat (n : ℕ) {x : ℝ} (hx : 0 < x) :
    x ^ ((n : ℝ) + 1 / 2) = x ^ n * Real.sqrt x := by
  rw [Real.rpow_add hx, Real.rpow_natCast, ← Real.sqrt_eq_rpow]

/-- On the positive half-line, `Z^{n-1/2} = Z^{n-1} √Z` (for `1 ≤ n`). -/
lemma rpow_sub_half_nat (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    x ^ ((n : ℝ) - 1 / 2) = x ^ (n - 1) * Real.sqrt x := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; norm_num
  rw [show (n : ℝ) - 1 / 2 = ((n - 1 : ℕ) : ℝ) + 1 / 2 by rw [hcast]; ring]
  rw [Real.rpow_add hx, Real.rpow_natCast, ← Real.sqrt_eq_rpow]

/-! ## The two off-diagonal identities -/

/-- Off the diagonal, where the radicand is positive, the manifest first numerator `J1M`
(ν = n+1/2, m = n+1) is the paper's `J1`. -/
theorem J1M_eq_J1 (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s σ t : ℝ} (hsσ : s < σ)
    (hR : 0 < (t + hquot h s σ) * (line h σ t + line h s t)) :
    J1M n h s σ t = J1 n h s σ t := by
  have hz : 0 < Zrad h (s, σ, t) := Zrad_pos_of_hR hh hsσ hR
  have hcontZ : Continuous (fun u : ℝ => Zrad h (u, σ, t)) := by unfold Zrad line; fun_prop
  have hopen : IsOpen {u : ℝ | 0 < Zrad h (u, σ, t)} := isOpen_lt continuous_const hcontZ
  rw [J1, if_neg (ne_of_gt hsσ), J1M,
    Work.OddVolterra.KernelExt.Rnu_spec ((n : ℝ) + 1 / 2) hh (init := fun _ : ℝ × ℝ × ℝ => (1 : ℝ))
      contDiff_const (n + 1) s σ t hz]
  have heq : (fun u : ℝ => Zrad h (u, σ, t) ^ ((n : ℝ) + 1 / 2) * 1)
      =ᶠ[𝓝 s] (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ n *
        Real.sqrt (psi h (fun t' => line h σ t') u t)) := by
    filter_upwards [hopen.mem_nhds hz] with u hu
    rw [mul_one, psi_line_eq_Zrad, rpow_add_half_nat n hu]
  rw [Filter.EventuallyEq.iteratedDeriv_eq (n + 1) heq]
  have hexp : (↑(n + 1) : ℝ) - ((n : ℝ) + 1 / 2) = 1 / 2 := by push_cast; ring
  rw [hexp, ← Real.sqrt_eq_rpow, psi_line_eq_Zrad]

/-- Off the diagonal, where the radicand is positive, the manifest second numerator `J2M`
(ν = n-1/2, m = n) is the paper's `J2`.  The hypothesis `1 ≤ n` is needed: the paper's `J2`
uses `ψ^{n-1}√ψ`, which for `n = 0` is not `ψ^{-1/2}`. -/
theorem J2M_eq_J2 (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s σ t : ℝ}
    (hsσ : s < σ) (hR : 0 < (t + hquot h s σ) * (line h σ t + line h s t)) :
    J2M n h s σ t = J2 n h s σ t := by
  have hz : 0 < Zrad h (s, σ, t) := Zrad_pos_of_hR hh hsσ hR
  have hcontZ : Continuous (fun u : ℝ => Zrad h (u, σ, t)) := by unfold Zrad line; fun_prop
  have hopen : IsOpen {u : ℝ | 0 < Zrad h (u, σ, t)} := isOpen_lt continuous_const hcontZ
  have hinit : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) := by
    unfold lineSlope; fun_prop
  rw [J2, if_neg (ne_of_gt hsσ), J2M,
    Work.OddVolterra.KernelExt.Rnu_spec ((n : ℝ) - 1 / 2) hh hinit n s σ t hz]
  have heq : (fun u : ℝ => Zrad h (u, σ, t) ^ ((n : ℝ) - 1 / 2) * lineSlope h u t)
      =ᶠ[𝓝 s] (fun u : ℝ => psi h (fun t' => line h σ t') u t ^ (n - 1) *
        Real.sqrt (psi h (fun t' => line h σ t') u t) * lineSlope h u t) := by
    filter_upwards [hopen.mem_nhds hz] with u hu
    rw [psi_line_eq_Zrad, rpow_sub_half_nat n hn hu]
  rw [Filter.EventuallyEq.iteratedDeriv_eq n heq]
  have hexp : (↑n : ℝ) - ((n : ℝ) - 1 / 2) = 1 / 2 := by ring
  rw [hexp, ← Real.sqrt_eq_rpow, psi_line_eq_Zrad]

/-! ## The requested conjunction -/

theorem JM_eq_J (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {s σ t : ℝ}
    (hsσ : s < σ)
    (hR : 0 < (t + Work.OddVolterra.hquot h s σ) *
      (Work.OddVolterra.line h σ t + Work.OddVolterra.line h s t)) :
    Work.OddVolterra.KernelExt.J1M n h s σ t = Work.OddVolterra.J1 n h s σ t ∧
    Work.OddVolterra.KernelExt.J2M n h s σ t = Work.OddVolterra.J2 n h s σ t :=
  ⟨J1M_eq_J1 n hh hsσ hR, J2M_eq_J2 n hn hh hsσ hR⟩

end

end Work.OddVolterra.KernelExt
