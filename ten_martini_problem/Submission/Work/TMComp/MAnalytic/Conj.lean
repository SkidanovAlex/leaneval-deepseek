import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.MAnalytic.Basic

/-!
# C9 (`P_mAnalytic`): the conjugacy to rotations built from the invariant section

Given the invariant section `m : (a,b) × ℝ → ℍ` of the almost Mathieu cocycle (AJ §2.3), this
file constructs AJ's conjugating matrix (AJ (4.11)–(4.13))

`C_E(x) = [[1/√σ, −β/√σ], [0, √σ]]`,  where `m(E,x) = β + iσ`,

which satisfies `C_E(x+α) S_E(x) = R_{φ(E,x)} C_E(x)` for a real-analytic angle `φ`, together
with `det C_E = 1`, periodicity in `x` and `deg C_E = 0`.

The identity `C_E(x+α) S_E(x) C_E(x)⁻¹ ∈ SO(2)` is equivalent to `C_E(x)⁻¹ · i = m(E,x)`:
indeed `C(x)⁻¹·i = m(x)` and the section equation `S(x)·m(x) = m(x+α)` give
`(C(x+α)S(x)C(x)⁻¹)·i = C(x+α)·m(x+α) = i`.

In terms of `β, σ, β', σ'` (`m(·+α) = β' + iσ'`) the section equation gives the two scalar
relations

* `σ' (β² + σ²) = σ`   (`sec_sigma`),
* `(a − β') (β² + σ²) = β`   (`sec_beta`),   `a = coeff λ E x`,

and the four matrix identities follow from these with `c = β/N`, `s = σ/N`, `N = |m|`:

`√σ' = s/√σ`, `(a − β')/√σ' = c/√σ`, `1/√σ' = cβ/√σ + s√σ`, `sβ/√σ = c√σ`.
-/

open LeanEval.Analysis.TenMartini
open Work.TMContract Set Filter Topology
open scoped Topology

noncomputable section

namespace Work.TMComp.MAnalytic

/-! ## Analyticity helpers -/

/-- `Real.sqrt` is real-analytic away from `0`. -/
theorem analyticAt_sqrt {y : ℝ} (hy : y ≠ 0) : AnalyticAt ℝ Real.sqrt y := by
  have h : Real.sqrt =ᶠ[𝓝 y] fun t : ℝ => t ^ (1 / 2 : ℝ) :=
    Filter.EventuallyEq.of_eq (funext fun t => Real.sqrt_eq_rpow t)
  exact AnalyticAt.congr ((ContDiffAt.rpow_const_of_ne (p := (1/2 : ℝ)) (n := (⊤ : WithTop ℕ∞)) contDiffAt_id hy).analyticAt)
    h.symm

/-- The real part of a jointly real-analytic `ℂ`-valued function of two real variables. -/
theorem AnalyticAt.re_comp {p : ℝ × ℝ} {M : ℝ → ℝ → ℂ}
    (hM : AnalyticAt ℝ (fun q : ℝ × ℝ => M q.1 q.2) p) :
    AnalyticAt ℝ (fun q : ℝ × ℝ => (M q.1 q.2).re) p :=
  AnalyticAt.comp (g := fun z : ℂ => z.re) (f := fun q : ℝ × ℝ => M q.1 q.2) (x := p)
    (Complex.reCLM.analyticAt (M p.1 p.2)) hM

/-- The imaginary part of a jointly real-analytic `ℂ`-valued function of two real variables. -/
theorem AnalyticAt.im_comp {p : ℝ × ℝ} {M : ℝ → ℝ → ℂ}
    (hM : AnalyticAt ℝ (fun q : ℝ × ℝ => M q.1 q.2) p) :
    AnalyticAt ℝ (fun q : ℝ × ℝ => (M q.1 q.2).im) p :=
  AnalyticAt.comp (g := fun z : ℂ => z.im) (f := fun q : ℝ × ℝ => M q.1 q.2) (x := p)
    (Complex.imCLM.analyticAt (M p.1 p.2)) hM

/-- The squared modulus of a jointly real-analytic `ℂ`-valued function of two real variables. -/
theorem AnalyticAt.normSq_comp {p : ℝ × ℝ} {M : ℝ → ℝ → ℂ}
    (hM : AnalyticAt ℝ (fun q : ℝ × ℝ => M q.1 q.2) p) :
    AnalyticAt ℝ (fun q : ℝ × ℝ => (M q.1 q.2).normSq) p := by
  have hre := re_comp hM
  have him := im_comp hM
  have h : (fun q : ℝ × ℝ => (M q.1 q.2).normSq) =
      (fun q : ℝ × ℝ => (M q.1 q.2).re * (M q.1 q.2).re + (M q.1 q.2).im * (M q.1 q.2).im) := by
    funext q
    exact Complex.normSq_apply (M q.1 q.2)
  rw [h]
  exact (hre.mul hre).add (him.mul him)

/-- `fun_prop`-friendly form: `p ↦ √(normSq (M p))` is analytic where the norm is nonzero. -/
theorem AnalyticAt.sqrt_normSq_comp {p : ℝ × ℝ} {M : ℝ → ℝ → ℂ}
    (hM : AnalyticAt ℝ (fun q : ℝ × ℝ => M q.1 q.2) p) (hp : M p.1 p.2 ≠ 0) :
    AnalyticAt ℝ (fun q : ℝ × ℝ => Real.sqrt (M q.1 q.2).normSq) p :=
  AnalyticAt.comp (g := Real.sqrt) (f := fun q : ℝ × ℝ => (M q.1 q.2).normSq) (x := p)
    (analyticAt_sqrt (ne_of_gt (Complex.normSq_pos.mpr hp))) (normSq_comp hM)

/-! ## The conjugating matrix and the angle, from the section `m` -/

/-- `β = Re m`. -/
def bbeta (m : ℝ → ℝ → ℂ) (E x : ℝ) : ℝ := (m E x).re
/-- `σ = Im m > 0`. -/
def ssigma (m : ℝ → ℝ → ℂ) (E x : ℝ) : ℝ := (m E x).im
/-- `N = |m| = √(β²+σ²) > 0`. -/
def nnrm (m : ℝ → ℝ → ℂ) (E x : ℝ) : ℝ := Real.sqrt (m E x).normSq
/-- `cos(2πφ) = β/|m|`. -/
def ccos (m : ℝ → ℝ → ℂ) (E x : ℝ) : ℝ := bbeta m E x / nnrm m E x
/-- `sin(2πφ) = σ/|m| > 0`. -/
def ssin (m : ℝ → ℝ → ℂ) (E x : ℝ) : ℝ := ssigma m E x / nnrm m E x
/-- `1/√σ`. -/
def isq (m : ℝ → ℝ → ℂ) (E x : ℝ) : ℝ := 1 / Real.sqrt (ssigma m E x)
/-- `√σ`. -/
def rsq (m : ℝ → ℝ → ℂ) (E x : ℝ) : ℝ := Real.sqrt (ssigma m E x)

/-- AJ's conjugating matrix (4.11): `C = [[1/√σ, −β/√σ],[0, √σ]]`. -/
def matC (m : ℝ → ℝ → ℂ) (E x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![isq m E x, -(bbeta m E x * isq m E x); 0, rsq m E x]

/-- The angle: `φ = arg(m)/2π`, computed from `c + i s = m/|m| ∈ ℍ` via the complex logarithm. -/
def phi (m : ℝ → ℝ → ℂ) (E x : ℝ) : ℝ :=
  (Complex.log ((ccos m E x : ℂ) + (ssin m E x : ℂ) * Complex.I)).im / (2 * Real.pi)

/-- The complex number `c + i·s = m/|m|`, whose argument is `2πφ`. -/
def cs (m : ℝ → ℝ → ℂ) (E x : ℝ) : ℂ := (ccos m E x : ℂ) + (ssin m E x : ℂ) * Complex.I

/-! ## Basic facts about the section on `(a,b) × ℝ` -/

variable {α lam a b : ℝ} {m : ℝ → ℝ → ℂ}

section BasicFacts

variable {E x : ℝ}

theorem ssigma_pos (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    0 < ssigma m E x := h.im_pos E hE x

theorem nnrm_pos (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) : 0 < nnrm m E x := by
  have hσ : 0 < ssigma m E x := h.im_pos E hE x
  have hne : m E x ≠ 0 := by
    intro h0
    have hσ' : 0 < (m E x).im := h.im_pos E hE x
    rw [h0] at hσ'
    simp at hσ'
  rw [nnrm, Real.sqrt_pos]
  exact Complex.normSq_pos.mpr hne

theorem nnrm_sq (m : ℝ → ℝ → ℂ) (E x : ℝ) :
    nnrm m E x ^ 2 = bbeta m E x ^ 2 + ssigma m E x ^ 2 := by
  rw [nnrm, Real.sq_sqrt (Complex.normSq_nonneg _)]
  simp [bbeta, ssigma, Complex.normSq_apply, pow_two]

theorem rsq_mul_isq (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    rsq m E x * isq m E x = 1 := by
  have hpos : 0 < rsq m E x := by
    rw [rsq, Real.sqrt_pos]
    exact h.im_pos E hE x
  rw [isq, rsq, one_div]
  exact mul_inv_cancel₀ (ne_of_gt hpos)

/-- The scalar content of the section equation: `σ' (β²+σ²) = σ` and
`(a − β')(β²+σ²) = β`, where `m(·+α) = β' + iσ'`. -/
theorem sec_rel (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    ssigma m E (x + α) * nnrm m E x ^ 2 = ssigma m E x ∧
      (coeff lam E x - bbeta m E (x + α)) * nnrm m E x ^ 2 = bbeta m E x := by
  have hs := h.sec E hE x
  constructor
  · rw [nnrm_sq]
    simpa [ssigma, bbeta, pow_two] using sec_sigma hs
  · rw [nnrm_sq]
    simpa [ssigma, bbeta, pow_two] using sec_beta hs

theorem nnrm_sq_ne (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    nnrm m E x ^ 2 ≠ 0 := by
  have := nnrm_pos (E := E) (x := x) h hE
  positivity

/-- `σ' = σ/N²`. -/
theorem ssigma_shift (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    ssigma m E (x + α) = ssigma m E x / nnrm m E x ^ 2 := by
  have hrel := (sec_rel (x := x) h hE).1
  rw [eq_div_iff (nnrm_sq_ne h hE)]
  exact hrel

/-- `a − β' = β/N²`. -/
theorem coeff_sub_bbeta (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    coeff lam E x - bbeta m E (x + α) = bbeta m E x / nnrm m E x ^ 2 := by
  have hrel := (sec_rel (x := x) h hE).2
  rw [eq_div_iff (nnrm_sq_ne h hE)]
  exact hrel

/-- `√σ' = √σ/N`. -/
theorem rsq_shift (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    rsq m E (x + α) = rsq m E x / nnrm m E x := by
  have hN := nnrm_pos (E := E) (x := x) h hE
  have hσ : 0 ≤ ssigma m E x := le_of_lt (h.im_pos E hE x)
  rw [rsq, ssigma_shift h hE, rsq, Real.sqrt_div hσ, Real.sqrt_sq (le_of_lt hN)]


/-- `σ' = σ/N²` in the direction needed below: `N² σ' = σ`. -/
theorem isq_shift (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    isq m E (x + α) = nnrm m E x / rsq m E x := by
  have hN := nnrm_pos (E := E) (x := x) h hE
  have hσ : 0 ≤ ssigma m E x := le_of_lt (h.im_pos E hE x)
  rw [isq, rsq, ssigma_shift h hE, Real.sqrt_div hσ, Real.sqrt_sq (le_of_lt hN), one_div, inv_div]

/-- `√σ · √σ = σ`. -/
theorem rsq_mul_rsq (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    rsq m E x * rsq m E x = ssigma m E x := by
  have hσ : 0 ≤ ssigma m E x := le_of_lt (h.im_pos E hE x)
  rw [rsq, Real.mul_self_sqrt hσ]

theorem rsq_pos (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) : 0 < rsq m E x := by
  rw [rsq, Real.sqrt_pos]
  exact h.im_pos E hE x

theorem rsq_ne (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) : rsq m E x ≠ 0 :=
  ne_of_gt (rsq_pos h hE)

/-- The complex number `c + i·s` attached to `m(E,x)` has modulus one and positive imaginary
part. -/
theorem cs_spec (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    ‖cs m E x‖ = 1 ∧ 0 < (cs m E x).im := by
  have hσ : 0 < ssigma m E x := h.im_pos E hE x
  have hN := nnrm_pos (E := E) (x := x) h hE
  have hN2 := nnrm_sq m E x
  have hns : Complex.normSq (cs m E x) = ccos m E x ^ 2 + ssin m E x ^ 2 := by
    simp only [Complex.normSq_apply, cs, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, mul_one, zero_mul, add_zero, zero_add, sub_zero]
    ring
  have hnormSq : Complex.normSq (cs m E x) = 1 := by
    rw [hns, ccos, ssin, div_pow, div_pow, ← add_div, ← hN2]
    exact div_self (ne_of_gt (pow_pos hN 2))
  refine ⟨?_, ?_⟩
  · have h : ‖cs m E x‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hnormSq
    nlinarith [norm_nonneg (cs m E x)]
  · simp only [cs, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_one, mul_zero, add_zero]
    simpa [ssin] using div_pos hσ hN

/-- The defining property of the angle `φ`: `cos 2πφ = c`, `sin 2πφ = s`. -/
theorem phi_cos_sin (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    Real.cos (2 * Real.pi * phi m E x) = ccos m E x ∧
      Real.sin (2 * Real.pi * phi m E x) = ssin m E x := by
  have hspec := cs_spec (x := x) h hE
  have hne : cs m E x ≠ 0 := by
    intro h0
    have := hspec.2
    rw [h0] at this
    simp at this
  have harg : 2 * Real.pi * phi m E x = Complex.arg (cs m E x) := by
    simp only [phi, cs, ccos, ssin, Complex.log_im]
    field_simp
  constructor
  · rw [harg, Complex.cos_arg hne, hspec.1, div_one]
    simp [cs, ccos]
  · rw [harg, Complex.sin_arg (cs m E x), hspec.1, div_one]
    simp [cs, ssin]

end BasicFacts


/-! ## The conjugacy identities -/

variable {α lam a b : ℝ} {m : ℝ → ℝ → ℂ}
variable {E x : ℝ}

theorem matC_periodic (h : AnalyticSection α lam a b m) : ∀ E x, matC m E (x + 1) = matC m E x := by
  intro E x
  unfold matC isq rsq bbeta ssigma
  rw [h.periodic E x]

theorem phi_periodic (h : AnalyticSection α lam a b m) : ∀ E x, phi m E (x + 1) = phi m E x := by
  intro E x
  unfold phi ccos ssin bbeta ssigma nnrm
  rw [h.periodic E x]

theorem matC_det (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    (matC m E x).det = 1 := by
  have hval : matC m E x 0 0 = isq m E x ∧ matC m E x 0 1 = -(bbeta m E x * isq m E x) ∧
      matC m E x 1 0 = 0 ∧ matC m E x 1 1 = rsq m E x := by
    simp [matC]
  obtain ⟨h00, h01, h10, h11⟩ := hval
  have hr : 0 < Real.sqrt (ssigma m E x) := rsq_pos (x := x) h hE
  rw [Matrix.det_fin_two, h00, h01, h10, h11, isq, rsq]
  simp only [mul_zero, sub_zero, one_div]
  exact inv_mul_cancel₀ (ne_of_gt hr)

/-! ### The four scalar identities behind `C(x+α) S(x) = R_φ C(x)` -/

theorem conj_entry00 (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    coeff lam E x * isq m E (x + α) - bbeta m E (x + α) * isq m E (x + α)
      = ccos m E x * isq m E x := by
  have h1 : coeff lam E x - bbeta m E (x + α) = bbeta m E x / nnrm m E x ^ 2 :=
    coeff_sub_bbeta (x := x) h hE
  have h2 : isq m E (x + α) = nnrm m E x / Real.sqrt (ssigma m E x) := isq_shift (x := x) h hE
  have hN : nnrm m E x ≠ 0 := (nnrm_pos (E := E) (x := x) h hE).ne'
  have hs : 0 < ssigma m E x := h.im_pos E hE x
  rw [← sub_mul, h1, h2, ccos, isq]
  field_simp
  try ring

theorem conj_entry10 (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    rsq m E (x + α) = ssin m E x * isq m E x := by
  have h2 : rsq m E (x + α) = Real.sqrt (ssigma m E x) / nnrm m E x := rsq_shift (x := x) h hE
  have hN : nnrm m E x ≠ 0 := (nnrm_pos (E := E) (x := x) h hE).ne'
  have hs : 0 < ssigma m E x := h.im_pos E hE x
  rw [h2, ssin, isq]
  field_simp
  rw [Real.sq_sqrt hs.le]
  try ring

theorem conj_entry01 (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    -(isq m E (x + α))
      = -(ccos m E x * (bbeta m E x * isq m E x)) - ssin m E x * rsq m E x := by
  have h2 : isq m E (x + α) = nnrm m E x / Real.sqrt (ssigma m E x) := isq_shift (x := x) h hE
  have hN : nnrm m E x ≠ 0 := (nnrm_pos (E := E) (x := x) h hE).ne'
  have hs : 0 < ssigma m E x := h.im_pos E hE x
  have hN2 : nnrm m E x ^ 2 = bbeta m E x ^ 2 + ssigma m E x ^ 2 := nnrm_sq m E x
  rw [h2, ccos, ssin, isq, rsq]
  field_simp
  rw [Real.sq_sqrt hs.le, hN2]
  ring

theorem conj_entry11 (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    (0 : ℝ)
      = -(ssin m E x * (bbeta m E x * isq m E x)) + ccos m E x * rsq m E x := by
  have hN : nnrm m E x ≠ 0 := (nnrm_pos (E := E) (x := x) h hE).ne'
  have hs : 0 < ssigma m E x := h.im_pos E hE x
  rw [ssin, ccos, isq, rsq]
  field_simp
  rw [Real.sq_sqrt hs.le]
  ring

/-- **The conjugacy identity (AJ (4.12))**: `C_E(x+α) S_{λ,E}(x) = R_{φ(E,x)} C_E(x)`. -/
theorem matC_conj (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    matC m E (x + α) * tmR lam E x = rot (phi m E x) * matC m E x := by
  have hcs := phi_cos_sin (x := x) h hE
  have h000 : matC m E (x + α) 0 0 = isq m E (x + α) := by simp [matC]
  have h001 : matC m E (x + α) 0 1 = -(bbeta m E (x + α) * isq m E (x + α)) := by simp [matC]
  have h010 : matC m E (x + α) 1 0 = 0 := by simp [matC]
  have h011 : matC m E (x + α) 1 1 = rsq m E (x + α) := by simp [matC]
  have hc00 : matC m E x 0 0 = isq m E x := by simp [matC]
  have hc01 : matC m E x 0 1 = -(bbeta m E x * isq m E x) := by simp [matC]
  have hc10 : matC m E x 1 0 = 0 := by simp [matC]
  have hc11 : matC m E x 1 1 = rsq m E x := by simp [matC]
  have ht00 : tmR lam E x 0 0 = coeff lam E x := by simp [tmR, coeff]
  have ht01 : tmR lam E x 0 1 = -1 := by simp [tmR]
  have ht10 : tmR lam E x 1 0 = 1 := by simp [tmR]
  have ht11 : tmR lam E x 1 1 = 0 := by simp [tmR]
  have hr00 : rot (phi m E x) 0 0 = ccos m E x := by
    have hh : rot (phi m E x) 0 0 = Real.cos (2 * Real.pi * phi m E x) := by simp [rot]
    rw [hh, hcs.1]
  have hr01 : rot (phi m E x) 0 1 = -ssin m E x := by
    have hh : rot (phi m E x) 0 1 = -Real.sin (2 * Real.pi * phi m E x) := by simp [rot]
    rw [hh, hcs.2]
  have hr10 : rot (phi m E x) 1 0 = ssin m E x := by
    have hh : rot (phi m E x) 1 0 = Real.sin (2 * Real.pi * phi m E x) := by simp [rot]
    rw [hh, hcs.2]
  have hr11 : rot (phi m E x) 1 1 = ccos m E x := by
    have hh : rot (phi m E x) 1 1 = Real.cos (2 * Real.pi * phi m E x) := by simp [rot]
    rw [hh, hcs.1]
  ext i j
  fin_cases i
  · fin_cases j
    · simp only [matC, rot, tmR, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [hcs.1, hcs.2]
      have h' := conj_entry00 (x := x) h hE
      try simp only [coeff] at h'
      ring_nf at h' ⊢
      exact h'
    · simp only [matC, rot, tmR, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [hcs.1, hcs.2]
      have h' := conj_entry01 (x := x) h hE
      try simp only [coeff] at h'
      ring_nf at h' ⊢
      exact h'
  · fin_cases j
    · simp only [matC, rot, tmR, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [hcs.1, hcs.2]
      have h' := conj_entry10 (x := x) h hE
      try simp only [coeff] at h'
      ring_nf at h' ⊢
      exact h'
    · simp only [matC, rot, tmR, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [hcs.1, hcs.2]
      have h' := conj_entry11 (x := x) h hE
      try simp only [coeff] at h'
      ring_nf at h' ⊢
      exact h'


/-! ## Analyticity of `C` and `φ` -/

theorem analyticAt_bbeta (h : AnalyticSection α lam a b m) {p : ℝ × ℝ}
    (hp : p ∈ Ioo a b ×ˢ univ) : AnalyticAt ℝ (fun q : ℝ × ℝ => bbeta m q.1 q.2) p :=
  Work.TMComp.MAnalytic.AnalyticAt.re_comp (h.analytic p hp)

theorem analyticAt_ssigma (h : AnalyticSection α lam a b m) {p : ℝ × ℝ}
    (hp : p ∈ Ioo a b ×ˢ univ) : AnalyticAt ℝ (fun q : ℝ × ℝ => ssigma m q.1 q.2) p :=
  Work.TMComp.MAnalytic.AnalyticAt.im_comp (h.analytic p hp)

theorem analyticAt_nnrm (h : AnalyticSection α lam a b m) {p : ℝ × ℝ}
    (hp : p ∈ Ioo a b ×ˢ univ) : AnalyticAt ℝ (fun q : ℝ × ℝ => nnrm m q.1 q.2) p := by
  have hne : m p.1 p.2 ≠ 0 := by
    intro h0
    have : (m p.1 p.2).im = 0 := by rw [h0]; simp
    have hpos := h.im_pos p.1 hp.1 p.2
    rw [this] at hpos
    exact lt_irrefl 0 hpos
  exact Work.TMComp.MAnalytic.AnalyticAt.sqrt_normSq_comp (h.analytic p hp) hne

theorem analyticAt_rsq (h : AnalyticSection α lam a b m) {p : ℝ × ℝ}
    (hp : p ∈ Ioo a b ×ˢ univ) : AnalyticAt ℝ (fun q : ℝ × ℝ => rsq m q.1 q.2) p := by
  have hσ := analyticAt_ssigma h hp
  have hne : ssigma m p.1 p.2 ≠ 0 := ne_of_gt (h.im_pos p.1 hp.1 p.2)
  exact AnalyticAt.comp (g := Real.sqrt) (f := fun q : ℝ × ℝ => ssigma m q.1 q.2) (x := p)
    (analyticAt_sqrt hne) hσ

theorem analyticAt_isq (h : AnalyticSection α lam a b m) {p : ℝ × ℝ}
    (hp : p ∈ Ioo a b ×ˢ univ) : AnalyticAt ℝ (fun q : ℝ × ℝ => isq m q.1 q.2) p := by
  have hσ := analyticAt_ssigma h hp
  have hne : ssigma m p.1 p.2 ≠ 0 := ne_of_gt (h.im_pos p.1 hp.1 p.2)
  have hg : AnalyticAt ℝ (fun y : ℝ => 1 / Real.sqrt y) (ssigma m p.1 p.2) := by
    exact analyticAt_const.div (analyticAt_sqrt hne)
      (ne_of_gt (Real.sqrt_pos.mpr (h.im_pos p.1 hp.1 p.2)))
  exact AnalyticAt.comp (g := fun y : ℝ => 1 / Real.sqrt y)
    (f := fun q : ℝ × ℝ => ssigma m q.1 q.2) (x := p) hg hσ

theorem analyticAt_ccos (h : AnalyticSection α lam a b m) {p : ℝ × ℝ}
    (hp : p ∈ Ioo a b ×ˢ univ) : AnalyticAt ℝ (fun q : ℝ × ℝ => ccos m q.1 q.2) p := by
  have hb := analyticAt_bbeta h hp
  have hn := analyticAt_nnrm h hp
  have hne : nnrm m p.1 p.2 ≠ 0 := ne_of_gt (nnrm_pos (E := p.1) (x := p.2) h hp.1)
  exact hb.div hn hne

theorem analyticAt_ssin (h : AnalyticSection α lam a b m) {p : ℝ × ℝ}
    (hp : p ∈ Ioo a b ×ˢ univ) : AnalyticAt ℝ (fun q : ℝ × ℝ => ssin m q.1 q.2) p := by
  have hσ := analyticAt_ssigma h hp
  have hn := analyticAt_nnrm h hp
  have hne : nnrm m p.1 p.2 ≠ 0 := ne_of_gt (nnrm_pos (E := p.1) (x := p.2) h hp.1)
  exact hσ.div hn hne

theorem analyticAt_cs (h : AnalyticSection α lam a b m) {p : ℝ × ℝ}
    (hp : p ∈ Ioo a b ×ˢ univ) : AnalyticAt ℝ (fun q : ℝ × ℝ => cs m q.1 q.2) p := by
  have hc := analyticAt_ccos h hp
  have hs := analyticAt_ssin h hp
  have h1 : AnalyticAt ℝ (fun q : ℝ × ℝ => ((ccos m q.1 q.2 : ℝ) : ℂ)) p :=
    AnalyticAt.comp (g := fun y : ℝ => (y : ℂ)) (f := fun q : ℝ × ℝ => ccos m q.1 q.2)
      (x := p) (Complex.ofRealCLM.analyticAt _) hc
  have h2 : AnalyticAt ℝ (fun q : ℝ × ℝ => ((ssin m q.1 q.2 : ℝ) : ℂ) * Complex.I) p :=
    (AnalyticAt.comp (g := fun y : ℝ => (y : ℂ)) (f := fun q : ℝ × ℝ => ssin m q.1 q.2)
      (x := p) (Complex.ofRealCLM.analyticAt _) hs).mul analyticAt_const
  exact h1.add h2

theorem analyticAt_phi (h : AnalyticSection α lam a b m) {p : ℝ × ℝ}
    (hp : p ∈ Ioo a b ×ˢ univ) : AnalyticAt ℝ (fun q : ℝ × ℝ => phi m q.1 q.2) p := by
  have hcs := analyticAt_cs h hp
  have hspos : 0 < (cs m p.1 p.2).im := by
    simp only [cs, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_one, mul_zero, add_zero, zero_add]
    exact div_pos (h.im_pos p.1 hp.1 p.2) (nnrm_pos (E := p.1) (x := p.2) h hp.1)
  have hslit : cs m p.1 p.2 ∈ Complex.slitPlane := Or.inr (ne_of_gt hspos)
  have hlog : AnalyticAt ℝ (fun q : ℝ × ℝ => Complex.log (cs m q.1 q.2)) p :=
    AnalyticAt.comp (g := Complex.log) (f := fun q : ℝ × ℝ => cs m q.1 q.2) (x := p)
      (analyticAt_clog hslit).restrictScalars hcs
  have him : AnalyticAt ℝ (fun q : ℝ × ℝ => (Complex.log (cs m q.1 q.2)).im) p :=
    AnalyticAt.comp (g := fun z : ℂ => z.im) (f := fun q : ℝ × ℝ => Complex.log (cs m q.1 q.2))
      (x := p) (Complex.imCLM.analyticAt _) hlog
  exact him.div analyticAt_const (by positivity)

theorem matC_analytic (h : AnalyticSection α lam a b m) (i j : Fin 2) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ => matC m p.1 p.2 i j) (Ioo a b ×ˢ univ) := by
  intro p hp
  have hb := analyticAt_bbeta h hp
  have hi := analyticAt_isq h hp
  have hr := analyticAt_rsq h hp
  fin_cases i <;> fin_cases j <;>
    simp only [matC, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one]
  · exact hi
  · exact (hb.mul hi).neg
  · exact analyticAt_const
  · exact hr

theorem phi_analytic (h : AnalyticSection α lam a b m) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ => phi m p.1 p.2) (Ioo a b ×ˢ univ) :=
  fun p hp => analyticAt_phi h hp

theorem matC_continuous (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    Continuous (matC m E) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hp : (E, x) ∈ Ioo a b ×ˢ univ := ⟨hE, mem_univ x⟩
  exact continuousAt_pi' fun i => continuousAt_pi' fun j =>
    (AnalyticAt.curry_right (matC_analytic h i j (E, x) hp)).continuousAt

theorem matC_hasDegree (h : AnalyticSection α lam a b m) (hE : E ∈ Ioo a b) :
    HasDegree (matC m E) 0 := by
  refine ⟨matC_continuous h hE, fun _ => 0, continuous_const, ?_, ?_⟩
  · intro x; simp
  · intro x
    have hpos : 0 < isq m E x := by
      rw [isq]
      exact one_div_pos.mpr (rsq_pos (x := x) h hE)
    refine ⟨isq m E x, hpos, ?_, ?_⟩
    · have hval : matC m E x 0 0 = isq m E x := by simp [matC]
      rw [hval]
      simp
    · have hval : matC m E x 1 0 = 0 := by simp [matC]
      rw [hval]
      simp

/-- **C9 from the invariant section**: the conjugacy to rotations, with all the properties
required by `Work.TMContract.P_mAnalytic`. -/
theorem exists_conj_of_analyticSection {α lam a b : ℝ} {m : ℝ → ℝ → ℂ}
    (h : AnalyticSection α lam a b m) :
    ∃ (C : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ → ℝ → ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun p : ℝ × ℝ => C p.1 p.2 i j) (Ioo a b ×ˢ univ)) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (Ioo a b ×ˢ univ) ∧
      (∀ E x, C E (x + 1) = C E x) ∧ (∀ E x, φ E (x + 1) = φ E x) ∧
      (∀ E ∈ Ioo a b, ∀ x, (C E x).det = 1) ∧
      (∀ E ∈ Ioo a b, HasDegree (C E) 0) ∧
      (∀ E ∈ Ioo a b, ∀ x, C E (x + α) * tmR lam E x = rot (φ E x) * C E x) :=
  ⟨matC m, phi m, fun i j => matC_analytic h i j, phi_analytic h, matC_periodic h,
    phi_periodic h, fun E hE x => matC_det h hE, fun E hE => matC_hasDegree h hE,
    fun E hE x => matC_conj h hE⟩

end Work.TMComp.MAnalytic
