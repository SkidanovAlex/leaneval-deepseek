import Submission.Work.RPV.Defs

/-!
# Rectangular peg: elementary API of the vocabulary (`Work.RPV`)

Lemmas about `Work.RPV`'s definitions that are pure algebra/manipulation of the coordinates:
the `2π`-periodicity `Tk`, the `K₀`-flow `tau` and its invariants `K0`, `uproj`, the two charts
`chordPS` and `levelPt`, and the symplectic form `symp` (`= dp₁∧dq₁ + dp₂∧dq₂`).

Notation in comments: a point of `PS` is written `((q₁,q₂),(p₁,p₂))`.

The harder analytic V-lemmas live in their own modules, proved by colleagues:
`Work.RPV.dchord_symplectic`, `Work.RPV.levelPt_omega`, `Work.RPV.rect_of_tau_chord`,
`Work.RPV.chordPS_circle`, `Work.RPV.chordPS_levelPt`, `Work.RPV.exists_two_points`,
`Work.RPV.theorem_1_of_main`.  The aggregator `Submission.Work.RPV.V` re-exports everything.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPV

/-! ## `symp` -/

theorem symp_skew (a b : PS) : symp a b = - symp b a := by
  simp only [symp]; ring

theorem symp_self (a : PS) : symp a a = 0 := by
  simp only [symp]; ring

/-- `symp` is nondegenerate: a vector pairing to zero with everything is zero. -/
theorem symp_ext_eq_zero {a : PS} (h : ∀ b : PS, symp a b = 0) : a = 0 := by
  have h1 : a.1.1 = 0 := by have := h ((0, 0), (1, 0)); simpa [symp] using this
  have h2 : a.1.2 = 0 := by have := h ((0, 0), (0, 1)); simpa [symp] using this
  have h3 : a.2.1 = 0 := by have := h ((1, 0), (0, 0)); simpa [symp] using this
  have h4 : a.2.2 = 0 := by have := h ((0, 1), (0, 0)); simpa [symp] using this
  have ha : a = (((0 : ℝ), (0 : ℝ)), ((0 : ℝ), (0 : ℝ))) := by
    refine Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)
  simpa only [Prod.zero_eq_mk] using ha

theorem symp_eq_zero_iff (a : PS) : (∀ b : PS, symp a b = 0) ↔ a = 0 :=
  ⟨symp_ext_eq_zero, by rintro rfl b; simp [symp]⟩

theorem symp_add_add (a b c d : PS) :
    symp (a + b) (c + d) = symp a c + symp a d + symp b c + symp b d := by
  simp only [symp, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add]; ring

theorem symp_smul_left (r : ℝ) (a b : PS) : symp (r • a) b = r * symp a b := by
  obtain ⟨⟨a₁, a₂⟩, ⟨a₃, a₄⟩⟩ := a
  obtain ⟨⟨b₁, b₂⟩, ⟨b₃, b₄⟩⟩ := b
  simp only [symp, Prod.smul_mk, smul_eq_mul]
  ring

theorem symp_smul_right (r : ℝ) (a b : PS) : symp a (r • b) = r * symp a b := by
  obtain ⟨⟨a₁, a₂⟩, ⟨a₃, a₄⟩⟩ := a
  obtain ⟨⟨b₁, b₂⟩, ⟨b₃, b₄⟩⟩ := b
  simp only [symp, Prod.smul_mk, smul_eq_mul]
  ring

/-- `stdZ` is injective. -/
theorem stdZ_inj_iff {x x' t t' : ℝ} : stdZ x t = stdZ x' t' ↔ x = x' ∧ t = t' := by
  constructor
  · intro h
    exact ⟨congrArg (fun y : PS => y.1.1) h, congrArg (fun y : PS => y.1.2) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Every point of the zero section is `stdZ x t` for its own coordinates. -/
theorem eq_stdZ_of_mem_Zsec {z : PS} (hz : z ∈ Zsec) : z = stdZ z.1.1 z.1.2 := by
  have h2 : z.2 = 0 := hz
  refine Prod.ext (Prod.ext rfl rfl) ?_
  simpa only [stdZ, Prod.zero_eq_mk] using h2

/-! ## The challenge hypothesis -/

theorem IsSmoothJordan.contMDiff {γ : Circle → ℂ} (h : IsSmoothJordan γ) :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ γ :=
  Manifold.IsSmoothEmbedding.contMDiff h

theorem IsSmoothJordan.injective {γ : Circle → ℂ} (h : IsSmoothJordan γ) :
    Function.Injective γ :=
  h.isEmbedding.injective

/-! ## `Tk`: the `2π`-periodic direction -/

theorem Tk_zero (x : PS) : Tk 0 x = x := by
  simp [Tk]

theorem Tk_add (k l : ℤ) (x : PS) : Tk k (Tk l x) = Tk (k + l) x := by
  ext <;> simp only [Tk] <;> push_cast <;> ring

theorem Tk_neg (k : ℤ) (x : PS) : Tk (-k) (Tk k x) = x := by
  rw [Tk_add]; simp [Tk]

theorem K0_Tk (k : ℤ) (x : PS) : K0 (Tk k x) = K0 x := by
  simp [K0, Tk]

/-- `uproj` is invariant under the `2π`-shift of the angle. -/
theorem uproj_Tk (k : ℤ) (x : PS) : uproj (Tk k x) = uproj x := by
  have h1 : Complex.exp (((x.1.2 + 2 * π * ↑k : ℝ) : ℂ) * I) =
      Complex.exp ((x.1.2 : ℂ) * I) * Complex.exp ((k : ℂ) * (2 * π * I)) := by
    rw [show ((x.1.2 + 2 * π * ↑k : ℝ) : ℂ) * I
        = (x.1.2 : ℂ) * I + (k : ℂ) * (2 * π * I) by push_cast; ring, Complex.exp_add]
  simp only [uproj, Tk]
  rw [h1, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem Tk_tau (k : ℤ) (θ : ℝ) (x : PS) : Tk k (tau θ x) = tau θ (Tk k x) := by
  ext <;> simp only [Tk, tau] <;> ring

/-! ## `Zsec` and `stdZ` -/

theorem mem_Zsec_iff (x : PS) : x ∈ Zsec ↔ x.2 = 0 := Iff.rfl

theorem stdZ_mem_Zsec (x t : ℝ) : stdZ x t ∈ Zsec := rfl

theorem K0_stdZ (x t : ℝ) : K0 (stdZ x t) = - (x ^ 2) / 2 := by
  simp only [K0, stdZ]; ring

theorem uproj_stdZ (x t : ℝ) : uproj (stdZ x t) = Complex.exp (t * I) * ((x : ℂ) * I) := by
  simp [uproj, stdZ]

/-! ## `tau`: the flow of `K₀` -/

theorem tau_zero (x : PS) : tau 0 x = x := by
  simp [tau]

theorem tau_add (θ₁ θ₂ : ℝ) (x : PS) : tau θ₁ (tau θ₂ x) = tau (θ₁ + θ₂) x := by
  ext <;> simp only [tau]
  all_goals first | (rw [Real.cos_add, Real.sin_add]; ring) | ring

theorem tau_neg (θ : ℝ) (x : PS) : tau (-θ) (tau θ x) = x := by
  rw [tau_add]; simp [tau]

theorem tau_pi (x : PS) : tau π x = ((-x.1.1, x.1.2 + π), (-x.2.1, x.2.2)) := by
  simp [tau]

theorem K0_tau (θ : ℝ) (x : PS) : K0 (tau θ x) = K0 x := by
  simp only [K0, tau]
  have h := Real.sin_sq_add_cos_sq θ
  linear_combination (-(x.1.1 ^ 2 + x.2.1 ^ 2) / 2) * h

theorem uproj_tau (θ : ℝ) (x : PS) : uproj (tau θ x) = uproj x := by
  have hexp : Complex.exp (-(θ : ℂ) * I) = ↑(Real.cos θ) - ↑(Real.sin θ) * I := by
    have h : -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
    rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg, Complex.ofReal_neg]
    ring
  have hrot : (↑(x.1.1 * Real.sin θ + x.2.1 * Real.cos θ) : ℂ) +
      ↑(x.1.1 * Real.cos θ - x.2.1 * Real.sin θ) * I =
      ((x.2.1 : ℂ) + (x.1.1 : ℂ) * I) * Complex.exp (-(θ : ℂ) * I) := by
    rw [hexp]
    refine Complex.ext ?_ ?_ <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hq : Complex.exp (((x.1.2 + θ : ℝ)) * I) * Complex.exp (-(θ : ℂ) * I) =
      Complex.exp (x.1.2 * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [uproj, tau]
  rw [hrot]
  calc Complex.exp (((x.1.2 + θ : ℝ)) * I) *
        (((x.2.1 : ℂ) + (x.1.1 : ℂ) * I) * Complex.exp (-(θ : ℂ) * I))
      = (Complex.exp (((x.1.2 + θ : ℝ)) * I) * Complex.exp (-(θ : ℂ) * I)) *
        ((x.2.1 : ℂ) + (x.1.1 : ℂ) * I) := by ring
    _ = Complex.exp (x.1.2 * I) * ((x.2.1 : ℂ) + (x.1.1 : ℂ) * I) := by rw [hq]

/-! ## `levelPt` and `chordPS`: coordinates -/

theorem K0_levelPt (u : ℂ) (σ a : ℝ) : K0 (levelPt u σ a) = -1 - σ := by
  simp only [K0, levelPt]
  have h1 : ‖Complex.exp (-(a : ℂ) * I) * u‖ = ‖u‖ := by
    rw [norm_mul, Complex.norm_exp]; simp
  have h2 := Complex.sq_norm (Complex.exp (-(a : ℂ) * I) * u)
  rw [Complex.normSq_apply, h1] at h2
  nlinarith [h2]

theorem uproj_levelPt (u : ℂ) (σ a : ℝ) : uproj (levelPt u σ a) = u := by
  simp only [uproj, levelPt]
  rw [Complex.re_add_im, ← mul_assoc, ← Complex.exp_add]
  have h : (a : ℂ) * I + -(a : ℂ) * I = 0 := by ring
  rw [h, Complex.exp_zero, one_mul]

theorem uproj_chordPS (z w : ℂ) (a : ℝ) :
    uproj (chordPS z w a) = (z + w) / (Real.sqrt 2 : ℂ) := by
  simp only [uproj, chordPS]
  rw [Complex.re_add_im, ← mul_assoc, ← Complex.exp_add]
  have h : (a : ℂ) * I + -(a : ℂ) * I = 0 := by ring
  rw [h, Complex.exp_zero, one_mul]

/-- `levelPt` is injective in `(u, σ, a)`: a point of `PS` determines its reduced coordinate,
its level and its phase.  This is the "no spurious coincidences" fact for level-curve data. -/
theorem levelPt_inj {u u' : ℂ} {σ σ' a a' : ℝ} (h : levelPt u σ a = levelPt u' σ' a') :
    u = u' ∧ σ = σ' ∧ a = a' := by
  have ha : a = a' := by
    have h1 := congrArg (fun x : PS => x.1.2) h
    simpa [levelPt] using h1
  have hu : u = u' := by
    have h1 := congrArg uproj h
    rwa [uproj_levelPt, uproj_levelPt] at h1
  have hs : σ = σ' := by
    have h1 := congrArg K0 h
    rw [K0_levelPt, K0_levelPt] at h1
    linarith
  exact ⟨hu, hs, ha⟩

/-- swapping the chord is `τ_π`. -/
theorem chordPS_swap (z w : ℂ) (a : ℝ) : chordPS w z (a + π) = tau π (chordPS z w a) := by
  have hexp : Complex.exp (-((a + π : ℝ) : ℂ) * I) = - Complex.exp (-(a : ℂ) * I) := by
    rw [show -((a + π : ℝ) : ℂ) * I = -(a : ℂ) * I + -(π : ℂ) * I by push_cast; ring,
      Complex.exp_add,
      show Complex.exp (-(π : ℂ) * I) = -1 by
        rw [show -(π : ℂ) * I = -(π * I) by ring, Complex.exp_neg_pi_mul_I]]
    ring
  have hquot : (w + z) / (Real.sqrt 2 : ℂ) = (z + w) / (Real.sqrt 2 : ℂ) := by ring
  have hnorm : (‖w‖ ^ 2 + ‖z‖ ^ 2) = (‖z‖ ^ 2 + ‖w‖ ^ 2) := by ring
  have harg : Complex.exp (-((a + π : ℝ) : ℂ) * I) * ((z + w) / (Real.sqrt 2 : ℂ)) =
      - (Complex.exp (-(a : ℂ) * I) * ((z + w) / (Real.sqrt 2 : ℂ))) := by
    rw [hexp]; ring
  simp only [chordPS, tau_pi]
  rw [hquot, harg, Complex.neg_re, Complex.neg_im, hnorm]

/-! ## `ωC` on `ℂ` -/

theorem ωC_skew (a b : ℂ) : ωC a b = - ωC b a := by
  have h := Complex.conj_im ((starRingEnd ℂ) a * b)
  have h2 : (starRingEnd ℂ) ((starRingEnd ℂ) a * b) = (starRingEnd ℂ) b * a := by
    simp [mul_comm]
  rw [h2] at h
  simp only [ωC]
  linarith

theorem ωC_self (a : ℂ) : ωC a a = 0 := by
  have h := Complex.conj_mul' a
  rw [ωC, h]
  simp [pow_two]

theorem ωC_mul_I (z : ℂ) : ωC z (z * I) = ‖z‖ ^ 2 := by
  have h : (starRingEnd ℂ) z * (z * I) = (((‖z‖ : ℂ)) ^ 2) * I := by
    rw [← mul_assoc, Complex.conj_mul']
  rw [ωC, h]
  simp [pow_two]

end Work.RPV
