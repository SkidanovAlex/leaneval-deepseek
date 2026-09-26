import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.DDefs
import Submission.Work.CKFinal.LineDecay.j_eq_tau_of_lines
import Submission.Work.Residues.KernelPoleLocation

/-!
# Growth of `K̂` along the three rays and in the far half-strip

For `τ` on one of the two critical lines `Re τ = ±1/2` with `Im τ ≥ 12`, the hatted kernel
`K̂ = (K₊ - K₋)/2` satisfies the two growth bounds that the contour shift of `shift_identity_khat`
needs:

* **on the three rays** `Re ∈ {-1,0,1}`, `t ≥ 1`: `‖K̂(τ, x+it)‖ ≤ C(1+t)^M e^{2πt}`.  The rays
  carry no orbit point of `τ` (the orbit points above height `1` are `τ, τ±1`, of real part
  `±1/2, ±3/2`), so `K̂` is continuous there and the only content is the behaviour at infinity,
  which is the cusp expansion below.
* **in the far half-strip** `|Re| ≤ 1`, `t ≥ T`: the same bound.  Here `K̂` differs from its cusp
  model `AexpZ Ĝ` by `O(cuspW^M e^{-πt})` (`strip_dev_ghat`) while the explicit model is
  `O((1+t)e^{2πt})`.

The upshot `Khat_ray_far_bound` is the interface used by the contour shifts: the ray bound gives
integrability of the tail integrands, the far bound gives decay of the top edges.
-/

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

noncomputable section

/-! ## The rays carry no orbit point -/

/-- On the three rays `Re w ∈ {-1,0,1}` above height `1`, the point `x + i t` is not in the
`SL(2,ℤ)`-orbit of `τ` (`Re τ = ±1/2`, `Im τ ≥ 12`): the orbit points with `Im ≥ 1` are
`τ, τ±1`, of real part `±1/2, ±3/2`. -/
lemma not_jInvariantFun_of_ray (τ : UpperHalfPlane) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2)
    (him : 12 ≤ τ.im) {x t : ℝ} (hx : x = -1 ∨ x = 0 ∨ x = 1) (ht : 1 ≤ t) :
    Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))
      ≠ Work.Kernels.jInvariantFun τ := by
  intro h
  have himw : 0 < (((x : ℂ) + (t : ℂ) * Complex.I)).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one]
    linarith
  set ζ : UpperHalfPlane := UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I) with hζdef
  have hcoe : (ζ : ℂ) = (x : ℂ) + (t : ℂ) * Complex.I := by
    rw [hζdef, UpperHalfPlane.ofComplex_apply_of_im_pos himw]
  have hζim : ζ.im = t := by rw [← UpperHalfPlane.coe_im, hcoe]; simp
  have hζre : ζ.re = x := by rw [← UpperHalfPlane.coe_re, hcoe]; simp
  have hjc := j_eq_tau_of_lines τ ζ hre (by linarith)
    (by rw [hζre]; rcases hx with h | h | h <;> linarith)
    (by rw [hζre]; rcases hx with h | h | h <;> linarith) (by rw [hζim]; exact ht) h
  rcases hjc with h1 | h1 | h1
  · have : x = τ.re := by rw [← hζre, h1]
    rcases hre with hre | hre <;> rw [hre] at this <;> (rcases hx with h | h | h <;> linarith)
  · have : x = τ.re - 1 := by
      rw [← hζre, h1]; simp only [UpperHalfPlane.vadd_re]; ring_nf
    rcases hre with hre | hre <;> rw [hre] at this <;> (rcases hx with h | h | h <;> linarith)
  · have : x = τ.re + 1 := by
      rw [← hζre, h1]; simp only [UpperHalfPlane.vadd_re]; ring_nf
    rcases hre with hre | hre <;> rw [hre] at this <;> (rcases hx with h | h | h <;> linarith)

/-- `K̂(τ, ·)` is continuous along the ray `x + i t`, `t ≥ 1`, for `x ∈ {-1,0,1}`: the ray
carries no orbit point of `τ`. -/
lemma continuousOn_khat_ray (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (him : 12 ≤ τ.im)
    {x : ℝ} (hx : x = -1 ∨ x = 0 ∨ x = 1) :
    ContinuousOn (fun t : ℝ => Work.Kernels.Khat ℓ d τ
      (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))) (Set.Ici 1) := by
  intro t ht
  have ht1 : (1 : ℝ) ≤ t := ht
  have htw : 0 < (((x : ℂ) + (t : ℂ) * Complex.I)).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one]
    linarith
  have hj := not_jInvariantFun_of_ray τ hre him hx ht1
  have hK := (Work.Residues.mdifferentiableAt_Khat_snd ℓ d hd τ
      (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I)) hj).continuousAt
  have hcont_of : ContinuousAt (fun z : ℂ => UpperHalfPlane.ofComplex z)
      ((x : ℂ) + (t : ℂ) * Complex.I) :=
    Work.Asymptotics.continuousOn_ofComplex_of_im_pos.continuousAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds htw)
  have hinner : ContinuousAt (fun u : ℝ => ((x : ℂ) + (u : ℂ) * Complex.I)) t := by fun_prop
  have hof : ContinuousAt (fun u : ℝ => UpperHalfPlane.ofComplex ((x : ℂ) + (u : ℂ) * Complex.I)) t :=
    ContinuousAt.comp (g := fun z : ℂ => UpperHalfPlane.ofComplex z)
      (f := fun u : ℝ => ((x : ℂ) + (u : ℂ) * Complex.I)) hcont_of hinner
  exact (ContinuousAt.comp (g := fun ζ : UpperHalfPlane => Work.Kernels.Khat ℓ d τ ζ)
    (f := fun u : ℝ => UpperHalfPlane.ofComplex ((x : ℂ) + (u : ℂ) * Complex.I)) hK hof).continuousWithinAt

/-! ## The cusp model and its size -/

/-- `‖(q z)⁻¹‖ = e^{2π Im z}`. -/
lemma norm_mq_inv (z : UpperHalfPlane) :
    ‖(Work.Asymptotics.mq z)⁻¹‖ = Real.exp (2 * Real.pi * z.im) := by
  have hmq : Work.Asymptotics.mq z = Work.Kernels.qParamFun z := rfl
  rw [hmq, norm_inv, Work.Asymptotics.norm_qParamFun, inv_eq_one_div, one_div, ← Real.exp_neg]
  congr 1
  ring

/-- The cusp model `𝒢(τ,z) = G₀₀ + zG₀₁ + q⁻¹(G₁₀ + zG₁₁)` is `O((1+Im z)e^{2π Im z})` for
`|Re z| ≤ 1`, `Im z ≥ 1`. -/
lemma AexpZ_norm_le (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im → |z.re| ≤ 1 →
      ‖Work.Asymptotics.AexpZ G τ z‖
        ≤ K * (1 + z.im) * Real.exp (2 * Real.pi * z.im) := by
  set A : ℝ := ‖G 0 0 τ‖ + ‖G 0 1 τ‖ + ‖G 1 0 τ‖ + ‖G 1 1 τ‖ + 1 with hAdef
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  have hA0 : ‖G 0 0 τ‖ ≤ A := by
    rw [hAdef]; linarith [norm_nonneg (G 0 1 τ), norm_nonneg (G 1 0 τ), norm_nonneg (G 1 1 τ)]
  have hA1 : ‖G 0 1 τ‖ ≤ A := by
    rw [hAdef]; linarith [norm_nonneg (G 0 0 τ), norm_nonneg (G 1 0 τ), norm_nonneg (G 1 1 τ)]
  have hA2 : ‖G 1 0 τ‖ ≤ A := by
    rw [hAdef]; linarith [norm_nonneg (G 0 0 τ), norm_nonneg (G 0 1 τ), norm_nonneg (G 1 1 τ)]
  have hA3 : ‖G 1 1 τ‖ ≤ A := by
    rw [hAdef]; linarith [norm_nonneg (G 0 0 τ), norm_nonneg (G 0 1 τ), norm_nonneg (G 1 0 τ)]
  refine ⟨4 * A, by positivity, ?_⟩
  intro z hz hzre
  have hzn : ‖(z : ℂ)‖ ≤ 1 + z.im := by
    have h := Complex.norm_le_abs_re_add_abs_im (z : ℂ)
    have h1 : |(z : ℂ).re| ≤ 1 := by rw [UpperHalfPlane.coe_re]; exact hzre
    have h2 : |(z : ℂ).im| = z.im := by
      rw [UpperHalfPlane.coe_im]
      exact abs_of_pos (by linarith)
    linarith [h, h1, h2]
  have hE : (1 : ℝ) ≤ Real.exp (2 * Real.pi * z.im) := by
    rw [Real.one_le_exp_iff]; positivity
  have hs1 : (1 : ℝ) ≤ 1 + z.im := by linarith
  have hqinv : ‖(Work.Asymptotics.mq z)⁻¹‖ = Real.exp (2 * Real.pi * z.im) := norm_mq_inv z
  have hmain : ‖Work.Asymptotics.AexpZ G τ z‖
      ≤ ‖G 0 0 τ‖ + ‖(z : ℂ)‖ * ‖G 0 1 τ‖
        + ‖(Work.Asymptotics.mq z)⁻¹‖ * (‖G 1 0 τ‖ + ‖(z : ℂ)‖ * ‖G 1 1 τ‖) := by
    rw [Work.Asymptotics.AexpZ]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
    · rw [norm_mul]
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add le_rfl ?_))
        (norm_nonneg _)
      rw [norm_mul]
  rw [hqinv] at hmain
  have hE1 : ‖G 0 0 τ‖ ≤ A * (1 + z.im) * Real.exp (2 * Real.pi * z.im) := by
    calc ‖G 0 0 τ‖ ≤ A := hA0
      _ ≤ A * (1 + z.im) := le_mul_of_one_le_right hA hs1
      _ ≤ A * (1 + z.im) * Real.exp (2 * Real.pi * z.im) :=
          le_mul_of_one_le_right (by positivity) hE
  have hE2 : ‖(z : ℂ)‖ * ‖G 0 1 τ‖ ≤ A * (1 + z.im) * Real.exp (2 * Real.pi * z.im) := by
    calc ‖(z : ℂ)‖ * ‖G 0 1 τ‖ ≤ (1 + z.im) * ‖G 0 1 τ‖ :=
          mul_le_mul_of_nonneg_right hzn (norm_nonneg _)
      _ ≤ (1 + z.im) * A := mul_le_mul_of_nonneg_left hA1 (by linarith)
      _ = A * (1 + z.im) := by ring
      _ ≤ A * (1 + z.im) * Real.exp (2 * Real.pi * z.im) :=
          le_mul_of_one_le_right (by positivity) hE
  have hE3 : Real.exp (2 * Real.pi * z.im) * ‖G 1 0 τ‖
      ≤ A * (1 + z.im) * Real.exp (2 * Real.pi * z.im) := by
    have hE0 : 0 ≤ Real.exp (2 * Real.pi * z.im) := Real.exp_nonneg _
    calc Real.exp (2 * Real.pi * z.im) * ‖G 1 0 τ‖
        ≤ Real.exp (2 * Real.pi * z.im) * A := mul_le_mul_of_nonneg_left hA2 hE0
      _ ≤ Real.exp (2 * Real.pi * z.im) * (A * (1 + z.im)) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hA hs1) hE0
      _ = A * (1 + z.im) * Real.exp (2 * Real.pi * z.im) := by ring
  have hE4 : Real.exp (2 * Real.pi * z.im) * (‖(z : ℂ)‖ * ‖G 1 1 τ‖)
      ≤ A * (1 + z.im) * Real.exp (2 * Real.pi * z.im) := by
    have hE0 : 0 ≤ Real.exp (2 * Real.pi * z.im) := Real.exp_nonneg _
    calc Real.exp (2 * Real.pi * z.im) * (‖(z : ℂ)‖ * ‖G 1 1 τ‖)
        ≤ Real.exp (2 * Real.pi * z.im) * ((1 + z.im) * ‖G 1 1 τ‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hzn (norm_nonneg _)) hE0
      _ ≤ Real.exp (2 * Real.pi * z.im) * ((1 + z.im) * A) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA3 (by linarith)) hE0
      _ = A * (1 + z.im) * Real.exp (2 * Real.pi * z.im) := by ring
  calc ‖Work.Asymptotics.AexpZ G τ z‖
      ≤ ‖G 0 0 τ‖ + ‖(z : ℂ)‖ * ‖G 0 1 τ‖
        + Real.exp (2 * Real.pi * z.im) * (‖G 1 0 τ‖ + ‖(z : ℂ)‖ * ‖G 1 1 τ‖) := hmain
    _ = ‖G 0 0 τ‖ + ‖(z : ℂ)‖ * ‖G 0 1 τ‖
        + (Real.exp (2 * Real.pi * z.im) * ‖G 1 0 τ‖
          + Real.exp (2 * Real.pi * z.im) * (‖(z : ℂ)‖ * ‖G 1 1 τ‖)) := by ring
    _ ≤ (4 * A) * (1 + z.im) * Real.exp (2 * Real.pi * z.im) := by
        nlinarith [hE1, hE2, hE3, hE4]

/-- **The far bound for `K̂`**: for `|Re z| ≤ 1` and `Im z ≥ T` (the threshold of the cusp
expansion), `‖K̂(τ,z)‖ ≤ C(1+Im z)^M e^{2π Im z}`. -/
theorem Khat_far_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ, ∃ T : ℝ, 0 < T ∧
      ∀ (x t : ℝ), -1 ≤ x → x ≤ 1 → T ≤ t →
        ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t) := by
  obtain ⟨C₀, M₀, T₀, hC₀, hM₀, hT₀, hdev⟩ := strip_dev_ghat ℓ d hd τ
  obtain ⟨K, hK, hmod⟩ := AexpZ_norm_le (Ghat ℓ d) τ
  refine ⟨C₀ * 3 ^ (max (Nat.ceil M₀) 1) + K, by positivity, max (Nat.ceil M₀) 1, max T₀ 1,
    lt_max_of_lt_left hT₀, ?_⟩
  intro x t hx1 hx2 ht
  have hT₀t : T₀ ≤ t := le_trans (le_max_left _ _) ht
  have h1t : (1 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  set z : UpperHalfPlane := UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I) with hz
  have himpos : 0 < (((x : ℂ) + (t : ℂ) * Complex.I)).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one]
    linarith
  have hcoe : (z : ℂ) = (x : ℂ) + (t : ℂ) * Complex.I := by
    rw [hz, UpperHalfPlane.ofComplex_apply_of_im_pos himpos]
  have hzim : z.im = t := by rw [← UpperHalfPlane.coe_im, hcoe]; simp
  have hzre : z.re = x := by rw [← UpperHalfPlane.coe_re, hcoe]; simp
  have hzre_abs : |z.re| ≤ 1 := by rw [hzre, abs_le]; constructor <;> linarith
  -- the deviation
  have hdev' : ‖Work.Kernels.Khat ℓ d τ z - Work.Asymptotics.AexpZ (Ghat ℓ d) τ z‖
      ≤ C₀ * (Work.Asymptotics.cuspW z) ^ M₀ * ‖Work.Residues.Ept z‖ :=
    hdev z (by rw [hzim]; exact hT₀t)
  -- the model
  have hmod' : ‖Work.Asymptotics.AexpZ (Ghat ℓ d) τ z‖
      ≤ K * (1 + t) * Real.exp (2 * Real.pi * t) := by
    have := hmod z (by rw [hzim]; linarith) hzre_abs
    rwa [hzim] at this
  -- combine
  have hsplit : ‖Work.Kernels.Khat ℓ d τ z‖
      ≤ ‖Work.Kernels.Khat ℓ d τ z - Work.Asymptotics.AexpZ (Ghat ℓ d) τ z‖
        + ‖Work.Asymptotics.AexpZ (Ghat ℓ d) τ z‖ := by
    have := norm_add_le (Work.Kernels.Khat ℓ d τ z - Work.Asymptotics.AexpZ (Ghat ℓ d) τ z)
      (Work.Asymptotics.AexpZ (Ghat ℓ d) τ z)
    simpa using this
  -- bounds on the two pieces
  have hnormEpt : ‖Work.Residues.Ept z‖ = Real.exp (-(Real.pi * t)) := by
    rw [Work.Residues.norm_Ept, hzim]
  have hcuspW : Work.Asymptotics.cuspW z ≤ 3 * (1 + t) := by
    rw [Work.Asymptotics.cuspW, hzim]
    have hre' : |(z : ℂ).re| ≤ 1 := by rw [UpperHalfPlane.coe_re]; exact hzre_abs
    linarith
  have hMle : M₀ ≤ ((max (Nat.ceil M₀) 1 : ℕ) : ℝ) :=
    le_trans (Nat.le_ceil M₀) (by exact_mod_cast le_max_left (Nat.ceil M₀) 1)
  have hMnn : (0 : ℝ) ≤ ((max (Nat.ceil M₀) 1 : ℕ) : ℝ) := by positivity
  have hdev2 : C₀ * (Work.Asymptotics.cuspW z) ^ M₀ * ‖Work.Residues.Ept z‖
      ≤ C₀ * 3 ^ (max (Nat.ceil M₀) 1) * (1 + t) ^ (max (Nat.ceil M₀) 1) := by
    have hcw : (0 : ℝ) ≤ Work.Asymptotics.cuspW z := by rw [Work.Asymptotics.cuspW]; positivity
    have h3e : (0 : ℝ) ≤ 3 * (1 + t) := by linarith
    have h1 : (Work.Asymptotics.cuspW z) ^ M₀ ≤ (3 * (1 + t)) ^ M₀ :=
      Real.rpow_le_rpow hcw hcuspW hM₀
    have h2 : (3 * (1 + t)) ^ M₀ = 3 ^ M₀ * (1 + t) ^ M₀ :=
      Real.mul_rpow (by norm_num) (by linarith)
    have h3le : (3 : ℝ) ^ M₀ ≤ (3 : ℝ) ^ ((max (Nat.ceil M₀) 1 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hMle
    have h4le : (1 + t) ^ M₀ ≤ (1 + t) ^ ((max (Nat.ceil M₀) 1 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ 1 + t) hMle
    have h5 : (3 : ℝ) ^ ((max (Nat.ceil M₀) 1 : ℕ) : ℝ) = 3 ^ (max (Nat.ceil M₀) 1) :=
      Real.rpow_natCast 3 _
    have h6 : (1 + t) ^ ((max (Nat.ceil M₀) 1 : ℕ) : ℝ) = (1 + t) ^ (max (Nat.ceil M₀) 1) :=
      Real.rpow_natCast (1 + t) _
    have he : ‖Work.Residues.Ept z‖ ≤ 1 := by
      rw [hnormEpt]
      exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    have h5nn : (0 : ℝ) ≤ 3 ^ (max (Nat.ceil M₀) 1) := by positivity
    have h6nn : (0 : ℝ) ≤ (1 + t) ^ (max (Nat.ceil M₀) 1) := by positivity
    calc C₀ * (Work.Asymptotics.cuspW z) ^ M₀ * ‖Work.Residues.Ept z‖
        ≤ C₀ * (3 ^ M₀ * (1 + t) ^ M₀) * 1 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ hC₀.le) he (norm_nonneg _) (by positivity)
          rw [← h2]; exact h1
      _ = C₀ * (3 ^ M₀ * (1 + t) ^ M₀) := by ring
      _ ≤ C₀ * (3 ^ (max (Nat.ceil M₀) 1) * (1 + t) ^ (max (Nat.ceil M₀) 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC₀.le
          rw [← h5, ← h6]
          exact mul_le_mul h3le h4le (by positivity) (by positivity)
      _ = C₀ * 3 ^ (max (Nat.ceil M₀) 1) * (1 + t) ^ (max (Nat.ceil M₀) 1) := by ring
  have hmod2 : K * (1 + t) * Real.exp (2 * Real.pi * t)
      ≤ K * (1 + t) ^ max (Nat.ceil M₀) 1 * Real.exp (2 * Real.pi * t) := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hK) (Real.exp_nonneg _)
    calc (1 + t) = (1 + t) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ (1 + t) ^ max (Nat.ceil M₀) 1 :=
          pow_le_pow_right₀ (by linarith) (le_max_right (Nat.ceil M₀) 1)
  have he1 : (1 : ℝ) ≤ Real.exp (2 * Real.pi * t) := by
    rw [Real.one_le_exp_iff]; positivity
  have hsum : C₀ * 3 ^ (max (Nat.ceil M₀) 1) * (1 + t) ^ max (Nat.ceil M₀) 1
      + K * (1 + t) ^ max (Nat.ceil M₀) 1 * Real.exp (2 * Real.pi * t)
      ≤ (C₀ * 3 ^ (max (Nat.ceil M₀) 1) + K) * (1 + t) ^ max (Nat.ceil M₀) 1
        * Real.exp (2 * Real.pi * t) := by
    have hpnn : (0 : ℝ) ≤ (1 + t) ^ max (Nat.ceil M₀) 1 := by positivity
    have key : C₀ * 3 ^ (max (Nat.ceil M₀) 1) * (1 + t) ^ max (Nat.ceil M₀) 1
        ≤ C₀ * 3 ^ (max (Nat.ceil M₀) 1) * (1 + t) ^ max (Nat.ceil M₀) 1
          * Real.exp (2 * Real.pi * t) := le_mul_of_one_le_right (by positivity) he1
    calc C₀ * 3 ^ (max (Nat.ceil M₀) 1) * (1 + t) ^ max (Nat.ceil M₀) 1
          + K * (1 + t) ^ max (Nat.ceil M₀) 1 * Real.exp (2 * Real.pi * t)
        ≤ C₀ * 3 ^ (max (Nat.ceil M₀) 1) * (1 + t) ^ max (Nat.ceil M₀) 1
            * Real.exp (2 * Real.pi * t)
          + K * (1 + t) ^ max (Nat.ceil M₀) 1 * Real.exp (2 * Real.pi * t) := by linarith
      _ = (C₀ * 3 ^ (max (Nat.ceil M₀) 1) + K) * (1 + t) ^ max (Nat.ceil M₀) 1
            * Real.exp (2 * Real.pi * t) := by ring
  calc ‖Work.Kernels.Khat ℓ d τ
        (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
      = ‖Work.Kernels.Khat ℓ d τ z‖ := by rw [hz]
    _ ≤ ‖Work.Kernels.Khat ℓ d τ z - Work.Asymptotics.AexpZ (Ghat ℓ d) τ z‖
        + ‖Work.Asymptotics.AexpZ (Ghat ℓ d) τ z‖ := hsplit
    _ ≤ C₀ * 3 ^ (max (Nat.ceil M₀) 1) * (1 + t) ^ max (Nat.ceil M₀) 1
        + K * (1 + t) * Real.exp (2 * Real.pi * t) :=
        add_le_add (le_trans hdev' hdev2) hmod'
    _ ≤ C₀ * 3 ^ (max (Nat.ceil M₀) 1) * (1 + t) ^ max (Nat.ceil M₀) 1
        + K * (1 + t) ^ max (Nat.ceil M₀) 1 * Real.exp (2 * Real.pi * t) := by
        linarith [hmod2]
    _ ≤ (C₀ * 3 ^ (max (Nat.ceil M₀) 1) + K) * (1 + t) ^ max (Nat.ceil M₀) 1
          * Real.exp (2 * Real.pi * t) := hsum

/-! ## The ray bound -/

/-- **The growth of `K̂` along the rays `Re ∈ {-1,0,1}`** for `t ≥ 1`. -/
theorem Khat_ray_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (him : 12 ≤ τ.im)
    {x : ℝ} (hx : x = -1 ∨ x = 0 ∨ x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ, ∀ t : ℝ, 1 ≤ t →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t) := by
  obtain ⟨C, hC, M, T, hT, hfar⟩ := Khat_far_bound ℓ d hd τ
  have hTne : (1 : ℝ) ≤ max T 1 := le_max_right _ _
  have hcont : ContinuousOn (fun t : ℝ => ‖Work.Kernels.Khat ℓ d τ
      (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖) (Set.Icc 1 (max T 1)) :=
    (continuousOn_khat_ray ℓ d hd τ hre him hx).norm.mono Set.Icc_subset_Ici_self
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hKnn : 0 ≤ K := le_trans (norm_nonneg _) (hK 1 ⟨le_rfl, hTne⟩)
  refine ⟨C + K, by positivity, M, fun t ht => ?_⟩
  have h2 : (1 : ℝ) ≤ (1 + t) ^ M := one_le_pow₀ (by linarith)
  have h3 : (1 : ℝ) ≤ Real.exp (2 * Real.pi * t) := by
    rw [Real.one_le_exp_iff]; positivity
  have hmono : ∀ {a : ℝ}, a ≤ K → a ≤ (C + K) * (1 + t) ^ M * Real.exp (2 * Real.pi * t) := by
    intro a ha
    have hb : a ≤ C + K := le_trans ha (le_add_of_nonneg_left hC)
    have hc : C + K ≤ (C + K) * (1 + t) ^ M := le_mul_of_one_le_right (by positivity) h2
    have hd : (C + K) * (1 + t) ^ M ≤ (C + K) * (1 + t) ^ M * Real.exp (2 * Real.pi * t) :=
      le_mul_of_one_le_right (by positivity) h3
    linarith
  by_cases hle : t ≤ max T 1
  · exact hmono (by simpa using hK t ⟨ht, hle⟩)
  · have hlt : max T 1 < t := lt_of_not_ge hle
    have hTt : T ≤ t := le_trans (le_max_left _ _) hlt.le
    have h1 := hfar x t (by rcases hx with h | h | h <;> linarith)
      (by rcases hx with h | h | h <;> linarith) hTt
    refine le_trans h1 ?_
    have h2' : C ≤ C + K := le_add_of_nonneg_right hKnn
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2' (by positivity))
      (Real.exp_nonneg _)

/-- **The two growth bounds of `K̂` on the contour**, in the form used by the shifts: the rays
`Re ∈ {-1,0,1}` for all `t ≥ 1`, and the far half-strip `|Re| ≤ 1`, `t ≥ T`. -/
theorem Khat_ray_far_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (him : 12 ≤ τ.im) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ, ∃ T : ℝ, 0 < T ∧
      (∀ (x t : ℝ), (x = -1 ∨ x = 0 ∨ x = 1) → 1 ≤ t →
        ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t))
      ∧ (∀ (x t : ℝ), -1 ≤ x → x ≤ 1 → T ≤ t →
        ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t)) := by
  obtain ⟨C, hC, M, T, hT, hfar⟩ := Khat_far_bound ℓ d hd τ
  obtain ⟨Cm, hCm, Mm, hm⟩ := Khat_ray_bound ℓ d hd τ hre him (Or.inl rfl)
  obtain ⟨C0, hC0, M0, h0⟩ := Khat_ray_bound ℓ d hd τ hre him (Or.inr (Or.inl rfl))
  obtain ⟨Cp, hCp, Mp, hp⟩ := Khat_ray_bound ℓ d hd τ hre him (Or.inr (Or.inr rfl))
  refine ⟨C + Cm + C0 + Cp, by positivity, M + Mm + M0 + Mp, T, hT, ?_, ?_⟩
  · intro x t hx ht
    have h1t : (1 : ℝ) ≤ 1 + t := by linarith
    have hbase : ∀ {Cx : ℝ} {Mx : ℕ},
        ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ Cx * (1 + t) ^ Mx * Real.exp (2 * Real.pi * t) →
        Cx ≤ C + Cm + C0 + Cp → Mx ≤ M + Mm + M0 + Mp →
        ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ (C + Cm + C0 + Cp) * (1 + t) ^ (M + Mm + M0 + Mp)
            * Real.exp (2 * Real.pi * t) := by
      intro Cx Mx hh hCn hMn
      refine le_trans hh ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hCn (pow_le_pow_right₀ h1t hMn) (by positivity) (by positivity))
        (Real.exp_nonneg _)
    rcases hx with h | h | h
    · subst h
      exact hbase (hm t ht) (by linarith) (by omega)
    · subst h
      exact hbase (h0 t ht) (by linarith) (by omega)
    · subst h
      exact hbase (hp t ht) (by linarith) (by omega)
  · intro x t hx1 hx2 ht
    have h1t : (1 : ℝ) ≤ 1 + t := by linarith
    refine le_trans (hfar x t hx1 hx2 ht) ?_
    refine mul_le_mul_of_nonneg_right
      (mul_le_mul (by linarith [hCm, hC0, hCp]) (pow_le_pow_right₀ h1t (by omega))
        (by positivity) (by positivity))
      (Real.exp_nonneg _)

/-! ## Integrability of the ray integrands -/

/-- `t ↦ t ^ k · e^{-ct}` is integrable on `[1,∞)` for `c > 0`. -/
private lemma integrableOn_pow_exp_neg_Ici_one {c : ℝ} (hc : 0 < c) (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(c * t))) (Set.Ici 1) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := c)
    (by have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith) (by norm_num) hc
  refine (h.congr_fun (fun x hx => ?_) measurableSet_Ioi).mono_set ?_
  · simp only [Real.rpow_natCast, Real.rpow_one, neg_mul]
  · intro x hx
    simp only [Set.mem_Ioi, Set.mem_Ici] at hx ⊢
    linarith

/-- `t ↦ e^{-ct}` is integrable on `[1,∞)` for `c > 0`. -/
private lemma integrableOn_exp_neg_Ici_one {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-(c * t))) (Set.Ici 1) := by
  refine (integrableOn_pow_exp_neg_Ici_one hc 0).congr_fun (fun x hx => ?_) measurableSet_Ici
  simp

/-- **The ray integrands are integrable** for `2 < r²`: the ray bound gives the dominating
function `C·2^M·(1+t^M)·e^{-(πr²-2π)t}`. -/
lemma integrableOn_Kax_gauss_ray (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r C : ℝ} {M : ℕ} (hr : 2 < r ^ 2)
    (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (him : 12 ≤ τ.im) (hC : 0 ≤ C)
    (hray : ∀ (x t : ℝ), (x = -1 ∨ x = 0 ∨ x = 1) → 1 ≤ t →
      ‖Work.Kernels.Khat ℓ d τ (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ C * (1 + t) ^ M * Real.exp (2 * Real.pi * t))
    {x : ℝ} (hx : x = -1 ∨ x = 0 ∨ x = 1) :
    IntegrableOn (fun t : ℝ => Work.CKFinal.Kax (Work.Kernels.Khat ℓ d) τ x t
      * Work.Asymptotics.gaussWeight r t) (Set.Ici 1) := by
  have hx1 : -1 ≤ x := by rcases hx with h | h | h <;> linarith
  have hx2 : x ≤ 1 := by rcases hx with h | h | h <;> linarith
  have hc : 0 < Real.pi * r ^ 2 - 2 * Real.pi := by nlinarith [Real.pi_pos, hr]
  set c : ℝ := Real.pi * r ^ 2 - 2 * Real.pi with hcdef
  have hdom : IntegrableOn (fun t : ℝ => C * 2 ^ M * (1 + t ^ M) * Real.exp (-(c * t)))
      (Set.Ici 1) := by
    have h2 : IntegrableOn (fun t : ℝ => C * 2 ^ M * (t ^ M * Real.exp (-(c * t))))
        (Set.Ici 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_pow_exp_neg_Ici_one hc M) (C * 2 ^ M)
    have h1 : IntegrableOn (fun t : ℝ => C * 2 ^ M * Real.exp (-(c * t))) (Set.Ici 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_exp_neg_Ici_one hc) (C * 2 ^ M)
    exact MeasureTheory.IntegrableOn.congr_fun (MeasureTheory.IntegrableOn.add h2 h1)
      (fun t ht => by simp only [Pi.add_apply]; ring) measurableSet_Ici
  have hker_meas : AEStronglyMeasurable (fun t : ℝ => Work.Kernels.Khat ℓ d τ
      (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I)))
      (volume.restrict (Set.Ici 1)) :=
    (continuousOn_khat_ray ℓ d hd τ hre him hx).aestronglyMeasurable measurableSet_Ici
  have hgw_cont : Continuous (fun t : ℝ => Work.Asymptotics.gaussWeight r t) := by
    simp only [Work.Asymptotics.gaussWeight]
    fun_prop
  have hae : AEStronglyMeasurable (fun t : ℝ => Work.CKFinal.Kax (Work.Kernels.Khat ℓ d) τ x t
      * Work.Asymptotics.gaussWeight r t) (volume.restrict (Set.Ici 1)) := by
    refine (hker_meas.mul hgw_cont.aestronglyMeasurable.restrict).congr ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr ?_
    filter_upwards with t ht
    rw [Set.mem_Ici] at ht
    simp only [Pi.mul_apply]
    rw [Work.CKFinal.LineDecay.Kax_eq_K_ofComplex _ τ x t (by linarith : (0 : ℝ) < t)]
  have hpt : ∀ t ∈ Set.Ici (1 : ℝ), ‖Work.CKFinal.Kax (Work.Kernels.Khat ℓ d) τ x t
      * Work.Asymptotics.gaussWeight r t‖
        ≤ C * 2 ^ M * (1 + t ^ M) * Real.exp (-(c * t)) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht
    rw [Work.CKFinal.LineDecay.Kax_eq_K_ofComplex _ τ x t (by linarith : (0 : ℝ) < t), norm_mul,
      Work.Asymptotics.norm_gaussWeight]
    have hb := hray x t hx ht1
    have hexpadd : Real.exp (2 * Real.pi * t) * Real.exp (-(Real.pi * r ^ 2 * t))
        = Real.exp (-(c * t)) := by
      rw [hcdef, ← Real.exp_add]; congr 1; ring
    have h1t : 1 + t ≤ 2 * t := by linarith
    have hpow_le : (1 + t) ^ M ≤ 2 ^ M * (1 + t ^ M) := by
      have h2 : (1 + t) ^ M ≤ (2 * t) ^ M := pow_le_pow_left₀ (by linarith) h1t M
      have h3 : t ^ M ≤ 1 + t ^ M := by
        have := pow_nonneg (by linarith : (0 : ℝ) ≤ t) M; linarith
      calc (1 + t) ^ M ≤ (2 * t) ^ M := h2
        _ = 2 ^ M * t ^ M := by rw [mul_pow]
        _ ≤ 2 ^ M * (1 + t ^ M) := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hA : ‖Work.Kernels.Khat ℓ d τ
          (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
          * Real.exp (-(Real.pi * r ^ 2 * t))
        ≤ (C * (1 + t) ^ M * Real.exp (2 * Real.pi * t))
          * Real.exp (-(Real.pi * r ^ 2 * t)) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
    have hB : (C * (1 + t) ^ M * Real.exp (2 * Real.pi * t))
          * Real.exp (-(Real.pi * r ^ 2 * t)) = C * (1 + t) ^ M * Real.exp (-(c * t)) := by
      rw [← hexpadd]; ring
    have hD : C * (1 + t) ^ M * Real.exp (-(c * t))
        ≤ C * (2 ^ M * (1 + t ^ M)) * Real.exp (-(c * t)) := by
      have hCnn : 0 ≤ C * Real.exp (-(c * t)) := by positivity
      have e1 : C * (1 + t) ^ M * Real.exp (-(c * t))
          = (C * Real.exp (-(c * t))) * (1 + t) ^ M := by ring
      have e2 : C * (2 ^ M * (1 + t ^ M)) * Real.exp (-(c * t))
          = (C * Real.exp (-(c * t))) * (2 ^ M * (1 + t ^ M)) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hpow_le hCnn
    have hstep1 : ‖Work.Kernels.Khat ℓ d τ
          (UpperHalfPlane.ofComplex ((x : ℂ) + (t : ℂ) * Complex.I))‖
          * Real.exp (-(Real.pi * r ^ 2 * t))
        ≤ C * (2 ^ M * (1 + t ^ M)) * Real.exp (-(c * t)) :=
      le_trans hA (le_trans hB.le hD)
    have e3 : C * 2 ^ M * (1 + t ^ M) * Real.exp (-(c * t))
        = C * (2 ^ M * (1 + t ^ M)) * Real.exp (-(c * t)) := by ring
    rw [e3]
    exact hstep1
  exact hdom.mono' hae ((MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr
    (Filter.Eventually.of_forall fun t ht => hpt t (by rwa [Set.mem_Ici] at ht)))


end

end Work.CKFinal.LineDecay
