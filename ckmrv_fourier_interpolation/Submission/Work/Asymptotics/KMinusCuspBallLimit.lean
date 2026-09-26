import Mathlib
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.cuspAtomLimits
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.E6FunSecondOrder

namespace Work.Asymptotics

open Filter Topology UpperHalfPlane

noncomputable section

/-! ## A calculus of cusp estimates in the `z`-variable at `i∞`

For a fixed `τ` the function `z ↦ Ncusp ℓ d τ z` is a combination of the cusp atoms
`E_k`, `Δ`, `j`, `U`, `V`, `W`, `𝓛_S` evaluated at `z`.  The estimates below record the
two first orders of their cusp expansions, with `E = Ept z` and `t = tpar z = ‖E‖ ≤ 1`.

`CuspEst f k` is a bound `‖f z‖ ≤ C t^k` valid for all large `z.im`, with a *constant*
`C` (no growth in `z`): this is the form the final assembly consumes, and it is closed
under sums, products and multiplication by constants. -/

/-- `CuspEst f k`: `‖f z‖ ≤ C * tpar z ^ k` for all large `Im z`, with `C > 0`. -/
def CuspEst (f : ℍ → ℂ) (k : ℕ) : Prop :=
  ∃ H C : ℝ, 0 < C ∧ ∀ z : ℍ, H ≤ z.im → ‖f z‖ ≤ C * Work.Residues.tpar z ^ k

/-- `t^k ≤ t^j` for `j ≤ k`, since `0 < t ≤ 1`. -/
lemma tpar_pow_le_pow {j k : ℕ} (hjk : j ≤ k) (z : ℍ) :
    Work.Residues.tpar z ^ k ≤ Work.Residues.tpar z ^ j :=
  pow_le_pow_of_le_one (Work.Residues.tpar_nonneg z) (Work.Residues.tpar_le_one z) hjk

lemma CuspEst.mono {f : ℍ → ℂ} {k k' : ℕ} (h : CuspEst f k) (hk : k' ≤ k) : CuspEst f k' := by
  obtain ⟨H, C, hC, hb⟩ := h
  refine ⟨H, C, hC, fun z hz => ?_⟩
  exact le_trans (hb z hz) (mul_le_mul_of_nonneg_left (tpar_pow_le_pow hk z) hC.le)

lemma CuspEst.congr {f g : ℍ → ℂ} {k : ℕ} (h : ∀ z, f z = g z) (hf : CuspEst f k) :
    CuspEst g k := by
  obtain ⟨H, C, hC, hb⟩ := hf
  exact ⟨H, C, hC, fun z hz => by rw [← h z]; exact hb z hz⟩

lemma CuspEst.add {f g : ℍ → ℂ} {k : ℕ} (hf : CuspEst f k) (hg : CuspEst g k) :
    CuspEst (fun z => f z + g z) k := by
  obtain ⟨H1, C1, hC1, h1⟩ := hf
  obtain ⟨H2, C2, hC2, h2⟩ := hg
  refine ⟨max H1 H2, C1 + C2, by linarith, fun z hz => ?_⟩
  have hz1 : H1 ≤ z.im := le_trans (le_max_left _ _) hz
  have hz2 : H2 ≤ z.im := le_trans (le_max_right _ _) hz
  have ht : (0 : ℝ) ≤ Work.Residues.tpar z ^ k := pow_nonneg (Work.Residues.tpar_nonneg z) k
  calc ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ C1 * Work.Residues.tpar z ^ k + C2 * Work.Residues.tpar z ^ k :=
        add_le_add (h1 z hz1) (h2 z hz2)
    _ = (C1 + C2) * Work.Residues.tpar z ^ k := by ring

lemma CuspEst.neg {f : ℍ → ℂ} {k : ℕ} (hf : CuspEst f k) : CuspEst (fun z => -f z) k := by
  obtain ⟨H, C, hC, h⟩ := hf
  refine ⟨H, C, hC, fun z hz => ?_⟩
  rw [norm_neg]; exact h z hz

lemma CuspEst.sub {f g : ℍ → ℂ} {k : ℕ} (hf : CuspEst f k) (hg : CuspEst g k) :
    CuspEst (fun z => f z - g z) k := by
  have h := hf.add hg.neg
  exact h.congr (fun z => by ring)

lemma CuspEst.mul {f g : ℍ → ℂ} {k₁ k₂ : ℕ} (hf : CuspEst f k₁) (hg : CuspEst g k₂) :
    CuspEst (fun z => f z * g z) (k₁ + k₂) := by
  obtain ⟨H1, C1, hC1, h1⟩ := hf
  obtain ⟨H2, C2, hC2, h2⟩ := hg
  refine ⟨max H1 H2, C1 * C2, mul_pos hC1 hC2, fun z hz => ?_⟩
  have hz1 : H1 ≤ z.im := le_trans (le_max_left _ _) hz
  have hz2 : H2 ≤ z.im := le_trans (le_max_right _ _) hz
  have ht1 : (0 : ℝ) ≤ Work.Residues.tpar z ^ k₁ :=
    pow_nonneg (Work.Residues.tpar_nonneg z) k₁
  calc ‖f z * g z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ (C1 * Work.Residues.tpar z ^ k₁) * (C2 * Work.Residues.tpar z ^ k₂) :=
        mul_le_mul (h1 z hz1) (h2 z hz2) (norm_nonneg _) (mul_nonneg hC1.le ht1)
    _ = (C1 * C2) * Work.Residues.tpar z ^ (k₁ + k₂) := by ring

lemma CuspEst.const_mul (c : ℂ) {f : ℍ → ℂ} {k : ℕ} (hf : CuspEst f k) :
    CuspEst (fun z => c * f z) k := by
  obtain ⟨H, C, hC, h⟩ := hf
  refine ⟨H, (‖c‖ + 1) * C, by positivity, fun z hz => ?_⟩
  rw [norm_mul]
  have ht : (0 : ℝ) ≤ Work.Residues.tpar z ^ k := pow_nonneg (Work.Residues.tpar_nonneg z) k
  calc ‖c‖ * ‖f z‖ ≤ ‖c‖ * (C * Work.Residues.tpar z ^ k) :=
        mul_le_mul_of_nonneg_left (h z hz) (norm_nonneg c)
    _ ≤ (‖c‖ + 1) * C * Work.Residues.tpar z ^ k := by nlinarith [ht, hC.le, norm_nonneg c]

lemma CuspEst.of_norm_le {f : ℍ → ℂ} {C : ℝ} (hC : 0 < C) (h : ∀ z : ℍ, ‖f z‖ ≤ C) :
    CuspEst f 0 := by
  refine ⟨0, C, hC, fun z _ => ?_⟩
  simpa using h z

lemma CuspEst.const (c : ℂ) : CuspEst (fun _ : ℍ => c) 0 :=
  CuspEst.of_norm_le (C := ‖c‖ + 1) (by positivity) fun _ => by simp

/-- Division by a function that does not vanish faster than `t^k` lowers the exponent by `k`. -/
lemma CuspEst.div_of_lower {f g : ℍ → ℂ} {m k : ℕ} (hmk : k ≤ m) {c : ℝ} (hc : 0 < c)
    (hg : ∃ H₀ : ℝ, ∀ z : ℍ, H₀ ≤ z.im → c * Work.Residues.tpar z ^ k ≤ ‖g z‖)
    (hf : CuspEst f m) : CuspEst (fun z => f z / g z) (m - k) := by
  obtain ⟨Hf, Cf, hCf, hbf⟩ := hf
  obtain ⟨H₀, hb0⟩ := hg
  refine ⟨max Hf H₀, Cf * c⁻¹, by positivity, fun z hz => ?_⟩
  have hzf : Hf ≤ z.im := le_trans (le_max_left _ _) hz
  have hz0 : H₀ ≤ z.im := le_trans (le_max_right _ _) hz
  set t := Work.Residues.tpar z with ht
  have ht0 : 0 < t := Work.Residues.tpar_pos z
  have hden : 0 < c * t ^ k := mul_pos hc (pow_pos ht0 k)
  have hgpos : 0 < ‖g z‖ := lt_of_lt_of_le hden (hb0 z hz0)
  rw [norm_div, div_eq_mul_inv]
  have hinv : (‖g z‖)⁻¹ ≤ (c * t ^ k)⁻¹ := by
    simpa using one_div_le_one_div_of_le hden (hb0 z hz0)
  have hstep : ‖f z‖ * (‖g z‖)⁻¹ ≤ (Cf * t ^ m) * (c * t ^ k)⁻¹ :=
    mul_le_mul (hbf z hzf) hinv (inv_nonneg.mpr (norm_nonneg _))
      (mul_nonneg hCf.le (pow_nonneg ht0.le m))
  refine le_trans hstep ?_
  have hsplit : (Cf * t ^ m) * (c * t ^ k)⁻¹ = (Cf * c⁻¹) * t ^ (m - k) := by
    have htne : t ≠ 0 := ne_of_gt ht0
    have hpk : t ^ m = t ^ (m - k) * t ^ k := by rw [← pow_add, Nat.sub_add_cancel hmk]
    rw [hpk]
    field_simp
  rw [hsplit]

/-! ## The cusp expansions of the individual atoms -/

lemma qParamFun_eq_Ept_sq (z : ℍ) : Work.Kernels.qParamFun z = Work.Residues.Ept z ^ 2 := by
  rw [Work.Residues.Ept, Work.Kernels.qParamFun, sq, ← Complex.exp_add]
  congr 1
  ring

private lemma norm_qParamFun (z : ℍ) :
    ‖Work.Kernels.qParamFun z‖ = Work.Residues.tpar z ^ 2 := by
  rw [qParamFun_eq_Ept_sq, norm_pow, ← Work.Residues.tpar_eq_norm_Ept]

lemma cuspEst_Ept : CuspEst (fun z : ℍ => Work.Residues.Ept z) 1 := by
  refine ⟨0, 1, by norm_num, fun z _ => ?_⟩
  rw [Work.Residues.norm_Ept]
  simp [Work.Residues.tpar]

lemma cuspEst_Ept_pow (n : ℕ) : CuspEst (fun z : ℍ => Work.Residues.Ept z ^ n) n := by
  induction n with
  | zero => simpa using (CuspEst.const (1 : ℂ))
  | succ m ih =>
      have h := ih.mul cuspEst_Ept
      refine h.congr (fun z => ?_)
      rw [pow_succ]

lemma cuspEst_qParamFun : CuspEst (fun z : ℍ => Work.Kernels.qParamFun z) 2 := by
  refine ⟨0, 1, by norm_num, fun z _ => ?_⟩
  rw [norm_qParamFun]
  simp

/-- A two-term second order estimate: `f - 1 = (f - 1 - c q) + c q` with `q = E²`. -/
lemma cuspEst_sub_one_of_q (f : ℍ → ℂ) (c : ℝ) {A : ℝ} (hA : 0 < A)
    (h : ∀ z : ℍ, 1 ≤ z.im →
      ‖f z - 1 - (c : ℂ) * Work.Kernels.qParamFun z‖ ≤ A * ‖Work.Kernels.qParamFun z‖ ^ 2) :
    CuspEst (fun z : ℍ => f z - 1) 2 := by
  have h2 : CuspEst (fun z : ℍ => f z - 1 - (c : ℂ) * Work.Kernels.qParamFun z) 4 := by
    refine ⟨1, A, hA, fun z hz => ?_⟩
    have hz1 : 1 ≤ z.im := le_trans (by norm_num) hz
    have h' := h z hz1
    rw [norm_qParamFun z] at h'
    have : (Work.Residues.tpar z ^ 2) ^ 2 = Work.Residues.tpar z ^ 4 := by ring
    rwa [this] at h'
  have h3 : CuspEst (fun z : ℍ => (c : ℂ) * Work.Kernels.qParamFun z) 2 :=
    cuspEst_qParamFun.const_mul (c : ℂ)
  refine ((h2.mono (k' := 2) (by norm_num)).add h3).congr (fun z => ?_)
  ring

lemma cuspEst_E4_sub_one : CuspEst (fun z : ℍ => Work.Kernels.E4Fun z - 1) 2 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.E4FunSecondOrder
  exact cuspEst_sub_one_of_q _ 240 hC h

lemma cuspEst_E6_sub_one : CuspEst (fun z : ℍ => Work.Kernels.E6Fun z - 1) 2 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.E6FunSecondOrder
  refine cuspEst_sub_one_of_q _ (-504) hC fun z hz => ?_
  have h' := h z hz
  rw [show Work.Kernels.E6Fun z - 1 - ((-504 : ℝ) : ℂ) * Work.Kernels.qParamFun z
      = Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z by push_cast; ring]
  exact h'

lemma cuspEst_E4Fun : CuspEst (fun z : ℍ => Work.Kernels.E4Fun z) 0 := by
  have h := (cuspEst_E4_sub_one.mono (Nat.zero_le 2)).add (CuspEst.const 1)
  exact h.congr (fun z => by ring)

lemma cuspEst_E6Fun : CuspEst (fun z : ℍ => Work.Kernels.E6Fun z) 0 := by
  have h := (cuspEst_E6_sub_one.mono (Nat.zero_le 2)).add (CuspEst.const 1)
  exact h.congr (fun z => by ring)

lemma cuspEst_E8_sub_one : CuspEst (fun z : ℍ => Work.Kernels.E8Fun z - 1) 2 := by
  have h := cuspEst_E4_sub_one.mul (cuspEst_E4Fun.add (CuspEst.const 1))
  refine (h.mono (k' := 2) (by norm_num)).congr (fun z => ?_)
  rw [Work.Kernels.E8Fun]
  ring

lemma cuspEst_E10_sub_one : CuspEst (fun z : ℍ => Work.Kernels.E10Fun z - 1) 2 := by
  have h1 := cuspEst_E4_sub_one.mul cuspEst_E6Fun
  have h := h1.add cuspEst_E6_sub_one
  refine (h.mono (k' := 2) (by norm_num)).congr (fun z => ?_)
  rw [Work.Kernels.E10Fun]
  ring

lemma cuspEst_E14_sub_one : CuspEst (fun z : ℍ => Work.Kernels.E14Fun z - 1) 2 := by
  have h1 : CuspEst (fun z : ℍ => Work.Kernels.E4Fun z ^ 2 - 1) 2 := by
    have h := cuspEst_E4_sub_one.mul (cuspEst_E4Fun.add (CuspEst.const 1))
    refine (h.mono (k' := 2) (by norm_num)).congr (fun z => ?_)
    ring
  have h := h1.mul cuspEst_E6Fun
  refine ((h.add cuspEst_E6_sub_one).mono (k' := 2) (by norm_num)).congr (fun z => ?_)
  rw [Work.Kernels.E14Fun]
  ring

lemma cuspEst_E8Fun : CuspEst (fun z : ℍ => Work.Kernels.E8Fun z) 0 :=
  ((cuspEst_E8_sub_one.mono (Nat.zero_le 2)).add (CuspEst.const 1)).congr
    (fun z => by ring)

lemma cuspEst_E10Fun : CuspEst (fun z : ℍ => Work.Kernels.E10Fun z) 0 :=
  ((cuspEst_E10_sub_one.mono (Nat.zero_le 2)).add (CuspEst.const 1)).congr
    (fun z => by ring)

lemma cuspEst_E14Fun : CuspEst (fun z : ℍ => Work.Kernels.E14Fun z) 0 :=
  ((cuspEst_E14_sub_one.mono (Nat.zero_le 2)).add (CuspEst.const 1)).congr
    (fun z => by ring)

lemma cuspEst_UFun_sub_one : CuspEst (fun z : ℍ => Work.Kernels.UFun z - 1) 1 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.UFun_decay
  refine ⟨1, C, hC, fun z hz => ?_⟩
  have hz1 : 1 ≤ z.im := le_trans (by norm_num) hz
  have h' := h z hz1
  simpa [Work.Residues.tpar] using h'

lemma cuspEst_WFun_sub_one : CuspEst (fun z : ℍ => Work.Kernels.WFun z - 1) 1 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.WFun_decay
  refine ⟨1, C, hC, fun z hz => ?_⟩
  have hz1 : 1 ≤ z.im := le_trans (by norm_num) hz
  have h' := h z hz1
  simpa [Work.Residues.tpar] using h'

lemma cuspEst_VFun : CuspEst (fun z : ℍ => Work.Kernels.VFun z) 1 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.VFun_decay
  refine ⟨1, C, hC, fun z hz => ?_⟩
  have hz1 : 1 ≤ z.im := le_trans (by norm_num) hz
  have h' := h z hz1
  simpa [Work.Residues.tpar] using h'

lemma cuspEst_UFun : CuspEst (fun z : ℍ => Work.Kernels.UFun z) 0 :=
  ((cuspEst_UFun_sub_one.mono (Nat.zero_le 1)).add (CuspEst.const 1)).congr
    (fun z => by ring)

lemma cuspEst_WFun : CuspEst (fun z : ℍ => Work.Kernels.WFun z) 0 :=
  ((cuspEst_WFun_sub_one.mono (Nat.zero_le 1)).add (CuspEst.const 1)).congr
    (fun z => by ring)

/-- `Δ = E² + O(t⁴)`. -/
lemma cuspEst_Delta_sub_Ept_sq :
    CuspEst (fun z : ℍ => Work.Kernels.DeltaFun z - Work.Residues.Ept z ^ 2) 4 := by
  obtain ⟨H, C, hC, h⟩ := Work.Residues.Deltafun_expansion
  refine ⟨H, C, hC, fun z hz => ?_⟩
  have h' := h z hz
  rwa [Work.Residues.Epar_eq_Ept] at h'

/-- `𝓛_S = -16E + O(t³)`. -/
lemma cuspEst_LS_add_16E (ℓ : Work.Kernels.LogLambdaData) :
    CuspEst (fun z : ℍ => ℓ.L_S z + 16 * Work.Residues.Ept z) 3 := by
  obtain ⟨H, C, hC, h⟩ := Work.Residues.LS_expansion ℓ
  refine ⟨H, C, hC, fun z hz => ?_⟩
  have h' := h z hz
  rwa [Work.Residues.Epar_eq_Ept] at h'

/-- `U = 1 + 8E + O(t²)`. -/
lemma cuspEst_UFun_sub_one_sub_8E :
    CuspEst (fun z : ℍ => Work.Kernels.UFun z - 1 - 8 * Work.Residues.Ept z) 2 := by
  obtain ⟨H, C, hC, h⟩ := Work.Residues.acusp_expansion
  refine ⟨H, C, hC, fun z hz => ?_⟩
  have h' := h z hz
  rwa [Work.Residues.Epar_eq_Ept, Work.Residues.acusp] at h'

/-- `V = 16E + O(t³)`. -/
lemma cuspEst_VFun_sub_16E :
    CuspEst (fun z : ℍ => Work.Kernels.VFun z - 16 * Work.Residues.Ept z) 3 := by
  obtain ⟨H, C, hC, h⟩ := Work.Residues.bcusp_expansion
  refine ⟨H, C, hC, fun z hz => ?_⟩
  have h' := h z hz
  rwa [Work.Residues.Epar_eq_Ept, Work.Residues.bcusp] at h'

/-- `𝓛_S = O(t)`. -/
lemma cuspEst_LS (ℓ : Work.Kernels.LogLambdaData) : CuspEst (fun z : ℍ => ℓ.L_S z) 1 := by
  have h := (cuspEst_LS_add_16E ℓ).mono (k' := 1) (by norm_num)
  have h2 : CuspEst (fun z : ℍ => -(16 * Work.Residues.Ept z)) 1 :=
    (cuspEst_Ept.const_mul 16).neg
  exact (h.add h2).congr (fun z => by ring)

/-- `U + W = 2 + O(t²)` (from Jacobi's quartic identity `U = W + V`). -/
lemma cuspEst_UFun_add_WFun_sub_two :
    CuspEst (fun z : ℍ => Work.Kernels.UFun z + Work.Kernels.WFun z - 2) 2 := by
  have hq : ∀ z : ℍ, Work.Kernels.UFun z = Work.Kernels.WFun z + Work.Kernels.VFun z :=
    fun z => Work.Kernels.TildeFacts.theta_quartic z
  have h1 : CuspEst (fun z : ℍ => 2 * (Work.Kernels.UFun z - 1 - 8 * Work.Residues.Ept z)) 2 :=
    (cuspEst_UFun_sub_one_sub_8E.const_mul 2)
  have h2 : CuspEst (fun z : ℍ => -(Work.Kernels.VFun z - 16 * Work.Residues.Ept z)) 2 :=
    (cuspEst_VFun_sub_16E.neg).mono (k' := 2) (by norm_num)
  refine (h1.add h2).congr (fun z => ?_)
  rw [hq z]
  ring

/-- `U² - W² = 32E + O(t³)`. -/
lemma cuspEst_UFun_sq_sub_WFun_sq_sub_32E :
    CuspEst (fun z : ℍ => Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2
      - 32 * Work.Residues.Ept z) 3 := by
  have hq : ∀ z : ℍ, Work.Kernels.UFun z = Work.Kernels.WFun z + Work.Kernels.VFun z :=
    fun z => Work.Kernels.TildeFacts.theta_quartic z
  have h1 : CuspEst (fun z : ℍ => 2 * (Work.Kernels.VFun z - 16 * Work.Residues.Ept z)) 3 :=
    cuspEst_VFun_sub_16E.const_mul 2
  have h2 : CuspEst (fun z : ℍ => 16 * (Work.Residues.Ept z
      * (Work.Kernels.UFun z + Work.Kernels.WFun z - 2))) 3 := by
    have h := (cuspEst_Ept.mul (cuspEst_UFun_add_WFun_sub_two.mono (k' := 2) (by norm_num)))
    have h' : CuspEst (fun z : ℍ => Work.Residues.Ept z
        * (Work.Kernels.UFun z + Work.Kernels.WFun z - 2)) 3 := by
      simpa using h
    exact h'.const_mul 16
  have h3 : CuspEst (fun z : ℍ => (Work.Kernels.VFun z - 16 * Work.Residues.Ept z)
      * (Work.Kernels.UFun z + Work.Kernels.WFun z - 2)) 5 :=
    cuspEst_VFun_sub_16E.mul cuspEst_UFun_add_WFun_sub_two
  have h4 := (h1.add h2).add (h3.mono (k' := 3) (by norm_num))
  refine (h4.mono (k' := 3) (by norm_num)).congr (fun z => ?_)
  rw [hq z]
  ring

/-- `U² - W² = O(t)`. -/
lemma cuspEst_UFun_sq_sub_WFun_sq :
    CuspEst (fun z : ℍ => Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2) 1 := by
  have hq : ∀ z : ℍ, Work.Kernels.UFun z = Work.Kernels.WFun z + Work.Kernels.VFun z :=
    fun z => Work.Kernels.TildeFacts.theta_quartic z
  have h2 : CuspEst (fun z : ℍ => Work.Kernels.UFun z + Work.Kernels.WFun z) 0 :=
    ((cuspEst_UFun_add_WFun_sub_two.mono (Nat.zero_le 2)).add (CuspEst.const 2)).congr
      (fun z => by ring)
  refine (cuspEst_VFun.mul h2).congr (fun z => ?_)
  rw [hq z]
  ring

/-- `Δ` does not vanish faster than `t²`. -/
lemma cuspEst_Delta_lower :
    ∃ H c : ℝ, 0 < c ∧ ∀ z : ℍ, H ≤ z.im →
      c * Work.Residues.tpar z ^ 2 ≤ ‖Work.Kernels.DeltaFun z‖ :=
  Work.Residues.DeltaFun_lower

/-- `Δ z ≠ 0`. -/
lemma DeltaFun_ne_zero (z : ℍ) : Work.Kernels.DeltaFun z ≠ 0 :=
  Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z

/-- `A / D * E - 1 = (A * E - D) / D`. -/
lemma div_mul_sub_one (A D E : ℂ) (hD : D ≠ 0) : A / D * E - 1 = (A * E - D) / D := by
  field_simp

/-- `E * (A / D) - 1 = (E * A - D) / D`. -/
lemma mul_div_sub_one (A D E : ℂ) (hD : D ≠ 0) : E * (A / D) - 1 = (E * A - D) / D := by
  field_simp

/-- `fk 2 · E² = 1 + O(t²)`, i.e. `E₁₄/Δ = E^{-2} + O(1)`. -/
lemma cuspEst_fk_two_mul_Ept_sq :
    CuspEst (fun z : ℍ => Work.Kernels.fk 2 z * Work.Residues.Ept z ^ 2 - 1) 2 := by
  have hnum : CuspEst (fun z : ℍ => Work.Kernels.E14Fun z * Work.Residues.Ept z ^ 2
      - Work.Kernels.DeltaFun z) 4 := by
    have h := (cuspEst_Ept_pow 2).mul (cuspEst_E14_sub_one)
    have h2 : CuspEst (fun z : ℍ => -(Work.Kernels.DeltaFun z - Work.Residues.Ept z ^ 2)) 4 :=
      cuspEst_Delta_sub_Ept_sq.neg
    have h3 := h.add h2
    refine h3.congr (fun z => ?_)
    ring
  obtain ⟨H, c, hc, hlow⟩ := cuspEst_Delta_lower
  have hdiv := CuspEst.div_of_lower (f := fun z : ℍ => Work.Kernels.E14Fun z
      * Work.Residues.Ept z ^ 2 - Work.Kernels.DeltaFun z)
    (g := fun z : ℍ => Work.Kernels.DeltaFun z) (m := 4) (k := 2) (by norm_num) hc
    ⟨H, hlow⟩ hnum
  refine hdiv.congr (fun z => ?_)
  have hfk : Work.Kernels.fk 2 z = Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z := by
    simp only [Work.Kernels.fk]; norm_num
  rw [hfk, div_mul_sub_one _ _ _ (DeltaFun_ne_zero z)]

/-- `fk (-2) · E² = 1 + O(t²)`, i.e. `E₁₀/Δ = E^{-2} + O(1)`. -/
lemma cuspEst_fk_neg_two_mul_Ept_sq :
    CuspEst (fun z : ℍ => Work.Kernels.fk (-2) z * Work.Residues.Ept z ^ 2 - 1) 2 := by
  have hnum : CuspEst (fun z : ℍ => Work.Kernels.E10Fun z * Work.Residues.Ept z ^ 2
      - Work.Kernels.DeltaFun z) 4 := by
    have h := (cuspEst_Ept_pow 2).mul (cuspEst_E10_sub_one)
    have h2 : CuspEst (fun z : ℍ => -(Work.Kernels.DeltaFun z - Work.Residues.Ept z ^ 2)) 4 :=
      cuspEst_Delta_sub_Ept_sq.neg
    have h3 := h.add h2
    refine h3.congr (fun z => ?_)
    ring
  obtain ⟨H, c, hc, hlow⟩ := cuspEst_Delta_lower
  have hdiv := CuspEst.div_of_lower (f := fun z : ℍ => Work.Kernels.E10Fun z
      * Work.Residues.Ept z ^ 2 - Work.Kernels.DeltaFun z)
    (g := fun z : ℍ => Work.Kernels.DeltaFun z) (m := 4) (k := 2) (by norm_num) hc
    ⟨H, hlow⟩ hnum
  refine hdiv.congr (fun z => ?_)
  have hfk : Work.Kernels.fk (-2) z = Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z := by
    simp only [Work.Kernels.fk]; norm_num
  rw [hfk, div_mul_sub_one _ _ _ (DeltaFun_ne_zero z)]

/-- `E² j = 1 + O(t²)`, i.e. `j = E^{-2} + O(1)`. -/
lemma cuspEst_Ept_sq_mul_jInvariantFun_sub_one :
    CuspEst (fun z : ℍ => Work.Residues.Ept z ^ 2
      * Work.Kernels.jInvariantFun z - 1) 2 := by
  have hnum : CuspEst (fun z : ℍ => Work.Residues.Ept z ^ 2 * Work.Kernels.E4Fun z ^ 3
      - Work.Kernels.DeltaFun z) 4 := by
    have hE4 : CuspEst (fun z : ℍ => Work.Kernels.E4Fun z ^ 3 - 1) 2 := by
      have hA : CuspEst (fun z : ℍ => Work.Kernels.E4Fun z * Work.Kernels.E4Fun z
          + Work.Kernels.E4Fun z + 1) 0 :=
        ((cuspEst_E4Fun.mul cuspEst_E4Fun).add cuspEst_E4Fun).add (CuspEst.const 1)
      have h := cuspEst_E4_sub_one.mul hA
      refine (h.mono (k' := 2) (by norm_num)).congr (fun z => ?_)
      ring
    have h := (cuspEst_Ept_pow 2).mul hE4
    have h2 : CuspEst (fun z : ℍ => -(Work.Kernels.DeltaFun z - Work.Residues.Ept z ^ 2)) 4 :=
      cuspEst_Delta_sub_Ept_sq.neg
    have h3 := h.add h2
    refine h3.congr (fun z => ?_)
    ring
  obtain ⟨H, c, hc, hlow⟩ := cuspEst_Delta_lower
  have hdiv := CuspEst.div_of_lower (f := fun z : ℍ => Work.Residues.Ept z ^ 2
      * Work.Kernels.E4Fun z ^ 3 - Work.Kernels.DeltaFun z)
    (g := fun z : ℍ => Work.Kernels.DeltaFun z) (m := 4) (k := 2) (by norm_num) hc
    ⟨H, hlow⟩ hnum
  refine hdiv.congr (fun z => ?_)
  rw [Work.Kernels.jInvariantFun, mul_div_sub_one _ _ _ (DeltaFun_ne_zero z)]

/-! ## The matrix entries `Mcusp d τ z i m`

Only the entries of `Mcusp` are needed, and they are evaluated by reducing the matrix literal
`!![...]` at a *concrete* pair of indices. -/

lemma Mcusp8_00 (τ z : ℍ) :
    Mcusp 8 τ z (0 : Fin 3) (0 : Fin 3) = -3456 := by
  rw [Mcusp, if_pos (by norm_num : ((8:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp8_01 (τ z : ℍ) :
    Mcusp 8 τ z (0 : Fin 3) (1 : Fin 3) = 0 := by
  rw [Mcusp, if_pos (by norm_num : ((8:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp8_02 (τ z : ℍ) :
    Mcusp 8 τ z (0 : Fin 3) (2 : Fin 3) = 0 := by
  rw [Mcusp, if_pos (by norm_num : ((8:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp8_10 (τ z : ℍ) :
    Mcusp 8 τ z (1 : Fin 3) (0 : Fin 3) = 0 := by
  rw [Mcusp, if_pos (by norm_num : ((8:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp8_11 (τ z : ℍ) :
    Mcusp 8 τ z (1 : Fin 3) (1 : Fin 3) = 1 := by
  rw [Mcusp, if_pos (by norm_num : ((8:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp8_12 (τ z : ℍ) :
    Mcusp 8 τ z (1 : Fin 3) (2 : Fin 3) = -1 := by
  rw [Mcusp, if_pos (by norm_num : ((8:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp8_20 (τ z : ℍ) :
    Mcusp 8 τ z (2 : Fin 3) (0 : Fin 3) = 0 := by
  rw [Mcusp, if_pos (by norm_num : ((8:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp8_21 (τ z : ℍ) :
    Mcusp 8 τ z (2 : Fin 3) (1 : Fin 3) = 1728 - Work.Kernels.jInvariantFun τ := by
  rw [Mcusp, if_pos (by norm_num : ((8:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp8_22 (τ z : ℍ) :
    Mcusp 8 τ z (2 : Fin 3) (2 : Fin 3) = Work.Kernels.jInvariantFun τ := by
  rw [Mcusp, if_pos (by norm_num : ((8:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]

lemma Mcusp24_00 (τ z : ℍ) :
    Mcusp 24 τ z (0 : Fin 3) (0 : Fin 3) = -3456 := by
  rw [Mcusp, if_neg (by norm_num : ¬ ((24:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp24_01 (τ z : ℍ) :
    Mcusp 24 τ z (0 : Fin 3) (1 : Fin 3) = -3456 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) := by
  rw [Mcusp, if_neg (by norm_num : ¬ ((24:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp24_02 (τ z : ℍ) :
    Mcusp 24 τ z (0 : Fin 3) (2 : Fin 3) = 0 := by
  rw [Mcusp, if_neg (by norm_num : ¬ ((24:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp24_10 (τ z : ℍ) :
    Mcusp 24 τ z (1 : Fin 3) (0 : Fin 3) = 0 := by
  rw [Mcusp, if_neg (by norm_num : ¬ ((24:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp24_11 (τ z : ℍ) :
    Mcusp 24 τ z (1 : Fin 3) (1 : Fin 3) = Work.Kernels.jInvariantFun τ + 2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) := by
  rw [Mcusp, if_neg (by norm_num : ¬ ((24:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp24_12 (τ z : ℍ) :
    Mcusp 24 τ z (1 : Fin 3) (2 : Fin 3) = -1 := by
  rw [Mcusp, if_neg (by norm_num : ¬ ((24:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp24_20 (τ z : ℍ) :
    Mcusp 24 τ z (2 : Fin 3) (0 : Fin 3) = 0 := by
  rw [Mcusp, if_neg (by norm_num : ¬ ((24:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp24_21 (τ z : ℍ) :
    Mcusp 24 τ z (2 : Fin 3) (1 : Fin 3) = 1728 - 2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) - Work.Kernels.jInvariantFun τ := by
  rw [Mcusp, if_neg (by norm_num : ¬ ((24:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
lemma Mcusp24_22 (τ z : ℍ) :
    Mcusp 24 τ z (2 : Fin 3) (2 : Fin 3) = 1 := by
  rw [Mcusp, if_neg (by norm_num : ¬ ((24:ℕ) = 8))]
  norm_num [Work.Kernels.c1728, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]

/-! ## The values of `fk` at the weights occurring in `Ncusp` -/

lemma fk_two_eq (z : ℍ) :
    Work.Kernels.fk 2 z = Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z := by
  simp only [Work.Kernels.fk]; norm_num

lemma fk_neg_two_eq (z : ℍ) :
    Work.Kernels.fk (-2) z = Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z := by
  simp only [Work.Kernels.fk]; norm_num

lemma fk_zero_eq (z : ℍ) : Work.Kernels.fk 0 z = 1 := by
  simp only [Work.Kernels.fk]; norm_num

lemma fk_six_eq (z : ℍ) : Work.Kernels.fk 6 z = Work.Kernels.E6Fun z := by
  simp only [Work.Kernels.fk]; norm_num

lemma fk_eight_eq (z : ℍ) : Work.Kernels.fk 8 z = Work.Kernels.E8Fun z := by
  simp only [Work.Kernels.fk]; norm_num

lemma fk_ten_eq (z : ℍ) : Work.Kernels.fk 10 z = Work.Kernels.E10Fun z := by
  simp only [Work.Kernels.fk]; norm_num

lemma ulen8_zero : ulen 8 (0 : Fin 3) = 10 := rfl
lemma ulen8_one : ulen 8 (1 : Fin 3) = 8 := rfl
lemma ulen8_two : ulen 8 (2 : Fin 3) = 6 := rfl
lemma ulen24_zero : ulen 24 (0 : Fin 3) = 2 := rfl
lemma ulen24_one : ulen 24 (1 : Fin 3) = 0 := rfl
lemma ulen24_two : ulen 24 (2 : Fin 3) = -2 := rfl

/-! ## The `z`-factors `T₈`, `T₂₄` of the cusp numerator -/

/-- `α_i = ψ_i(τ)·f_{v_i}(τ)`: the `τ`-coefficients of `Ncusp`. -/
def Alpha (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (i : Fin 3) (τ : ℍ) : ℂ :=
  Work.Kernels.psiVec ℓ τ i * Work.Kernels.fk (vlen d i) τ

/-- `αᵢ = Alpha ℓ d i τ`: the three `τ`-coefficients of `Ncusp`. -/
def Alpha0 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) : ℂ := Alpha ℓ d 0 τ
def Alpha1 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) : ℂ := Alpha ℓ d 1 τ
def Alpha2 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) : ℂ := Alpha ℓ d 2 τ

/-- The `z`-dependent factor of `Ncusp` for `d = 8`. -/
def T8 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -3456 * Alpha ℓ 8 0 τ * Work.Kernels.fk (ulen 8 0) z * ℓ.L_S z
    + (Alpha ℓ 8 1 τ + Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ))
      * Work.Kernels.fk (ulen 8 1) z * (-(Work.Kernels.VFun z))
    + (-(Alpha ℓ 8 1 τ) + Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ)
      * Work.Kernels.fk (ulen 8 2) z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)

/-- The `z`-dependent factor of `Ncusp` for `d = 24`, with the `m = 1` coefficient split as
`c·(jτ - jz) + m₀` (the form in which the leading order cancels against `m = 0, 2`). -/
def T24 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  -3456 * Alpha ℓ 24 0 τ * Work.Kernels.fk 2 z * ℓ.L_S z
    - (((-3456 * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))
        + ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
            + 1728 * Alpha ℓ 24 2 τ))
      * Work.Kernels.VFun z
    + (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * Work.Kernels.fk (-2) z
      * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)

theorem Ncusp_eight_expansion (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Ncusp ℓ 8 τ z = (2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ * T8 ℓ τ z := by
  simp only [Ncusp, T8, Alpha]
  congr 1
  simp only [Fin.sum_univ_three]
  rw [Mcusp8_00, Mcusp8_10, Mcusp8_20, Mcusp8_01, Mcusp8_11, Mcusp8_21, Mcusp8_02,
    Mcusp8_12, Mcusp8_22]
  rw [ulen8_zero, ulen8_one, ulen8_two]
  rw [fk_ten_eq, fk_eight_eq, fk_six_eq]
  rw [Pcusp_zero, Pcusp_one, Pcusp_two]
  simp only [Work.Kernels.E10Fun, Work.Kernels.E8Fun, Work.Kernels.E6Fun, Work.Kernels.VFun,
    Work.Kernels.UFun, Work.Kernels.WFun, Work.Kernels.jInvariantFun, Work.Kernels.theta00Fun,
    Work.Kernels.theta01Fun, Work.Kernels.theta10Fun]
  ring

theorem Ncusp_twentyfour_expansion (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Ncusp ℓ 24 τ z = (2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ * T24 ℓ τ z := by
  simp only [Ncusp, T24, Alpha]
  congr 1
  simp only [Fin.sum_univ_three]
  rw [Mcusp24_00, Mcusp24_10, Mcusp24_20, Mcusp24_01, Mcusp24_11, Mcusp24_21, Mcusp24_02,
    Mcusp24_12, Mcusp24_22]
  rw [ulen24_zero, ulen24_one, ulen24_two]
  rw [fk_zero_eq]
  rw [Pcusp_zero, Pcusp_one, Pcusp_two]
  simp only [Work.Kernels.VFun, Work.Kernels.UFun, Work.Kernels.WFun,
    Work.Kernels.jInvariantFun, Work.Kernels.theta00Fun, Work.Kernels.theta01Fun,
    Work.Kernels.theta10Fun]
  ring

/-- `Alpha0`, `Alpha1`, `Alpha2` are the three coefficients `Alpha ℓ d i τ`. -/
lemma Alpha0_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) :
    Alpha0 ℓ d τ = Alpha ℓ d 0 τ := rfl
lemma Alpha1_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) :
    Alpha1 ℓ d τ = Alpha ℓ d 1 τ := rfl
lemma Alpha2_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) :
    Alpha2 ℓ d τ = Alpha ℓ d 2 τ := rfl

/-! ## The error functions of the cleared expansion -/

/-- `E₁₄/Δ · E² - 1 = O(t²)`. -/
def eA (τ z : ℍ) : ℂ := Work.Kernels.fk 2 z * Work.Residues.Ept z ^ 2 - 1

/-- `(jτ - jz)E² + 1 = O(t²)`. -/
def eB (τ z : ℍ) : ℂ :=
  (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) * Work.Residues.Ept z ^ 2 + 1

/-- `E₁₀/Δ · E² - 1 = O(t²)`. -/
def eE (τ z : ℍ) : ℂ := Work.Kernels.fk (-2) z * Work.Residues.Ept z ^ 2 - 1

/-- `𝓛_S + 16E = O(t³)`. -/
def eU (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) : ℂ := ℓ.L_S z + 16 * Work.Residues.Ept z

/-- `V - 16E = O(t³)`. -/
def eV (z : ℍ) : ℂ := Work.Kernels.VFun z - 16 * Work.Residues.Ept z

/-- `U² - W² - 32E = O(t³)`. -/
def eW (z : ℍ) : ℂ :=
  Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2 - 32 * Work.Residues.Ept z

lemma cuspEst_eA (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : CuspEst (eA τ) 2 :=
  cuspEst_fk_two_mul_Ept_sq

lemma cuspEst_eB (τ : ℍ) : CuspEst (eB τ) 2 := by
  have h1 : CuspEst (fun z : ℍ => Work.Kernels.jInvariantFun τ * Work.Residues.Ept z ^ 2) 2 :=
    (cuspEst_Ept_pow 2).const_mul (Work.Kernels.jInvariantFun τ)
  have h2 : CuspEst (fun z : ℍ => -(Work.Residues.Ept z ^ 2 * Work.Kernels.jInvariantFun z - 1)) 2 :=
    cuspEst_Ept_sq_mul_jInvariantFun_sub_one.neg
  exact (h1.add h2).congr (fun z => by simp only [eB]; ring)

lemma cuspEst_eE (τ : ℍ) : CuspEst (eE τ) 2 := cuspEst_fk_neg_two_mul_Ept_sq

lemma cuspEst_eU (ℓ : Work.Kernels.LogLambdaData) : CuspEst (eU ℓ) 3 := cuspEst_LS_add_16E ℓ

lemma cuspEst_eV : CuspEst eV 3 := cuspEst_VFun_sub_16E

lemma cuspEst_eW : CuspEst eW 3 := cuspEst_UFun_sq_sub_WFun_sq_sub_32E

/-! ## The exact cancellation behind `T₂₄ · E² = O(t³)` -/

/-- The leading `E^{-1}` order of `T₂₄ · E²` cancels: writing the cleared combination in terms
of the errors `a = E₁₄/Δ·E² - 1`, `b = (jτ-jz)E² + 1`, `e = E₁₀/Δ·E² - 1`, `u = 𝓛_S + 16E`,
`v₀ = V - 16E`, `w₀ = U²-W²-32E`, the terms of order `E` drop out and only `O(t³)` remains. -/
lemma T24_cancellation (a0 a1 a2 jτ E a b e u v0 w0 : ℂ) :
    -(3456 * a0) * (1 + a) * (-16 * E + u)
        - (-3456 * a0 + 2 * a1 - 2 * a2) * (-1 + b) * (16 * E + v0)
        - ((a1 - a2) * jτ + 1728 * a2) * (16 * E ^ 3 + v0 * E ^ 2)
        + (a2 - a1) * (1 + e) * (32 * E + w0)
      = (55296 * a0 * a - 16 * (-3456 * a0 + 2 * a1 - 2 * a2) * b
            + 32 * (a2 - a1) * e) * E
        - 3456 * a0 * u * (1 + a)
        + (-3456 * a0 + 2 * a1 - 2 * a2) * v0 * (1 - b)
        - 16 * ((a1 - a2) * jτ + 1728 * a2) * E ^ 3
        - ((a1 - a2) * jτ + 1728 * a2) * v0 * E ^ 2
        + (a2 - a1) * w0 * (1 + e) := by ring

/-- **The `d = 24` estimate.**  `T₂₄ · E² = O(t³)`. -/
theorem cuspEst_T24_mul_Ept_sq (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    CuspEst (fun z => T24 ℓ τ z * Work.Residues.Ept z ^ 2) 3 := by
  have ha := cuspEst_eA ℓ τ
  have hb := cuspEst_eB τ
  have he := cuspEst_eE τ
  have hu := cuspEst_eU ℓ
  have hv := cuspEst_eV
  have hw := cuspEst_eW
  have hone_a : CuspEst (fun z : ℍ => 1 + eA τ z) 0 :=
    (CuspEst.const 1).add (ha.mono (Nat.zero_le 2))
  have hone_b : CuspEst (fun z : ℍ => 1 - eB τ z) 0 :=
    (CuspEst.const 1).sub (hb.mono (Nat.zero_le 2))
  have hone_e : CuspEst (fun z : ℍ => 1 + eE τ z) 0 :=
    (CuspEst.const 1).add (he.mono (Nat.zero_le 2))
  have h1 : CuspEst (fun z : ℍ =>
      (55296 * Alpha ℓ 24 0 τ * eA τ z
        - 16 * (-3456 * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ) * eB τ z
        + 32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z) * Work.Residues.Ept z) 3 :=
    (((ha.const_mul (55296 * Alpha ℓ 24 0 τ)).sub
        (hb.const_mul (16 * (-3456 * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)))).add
      (he.const_mul (32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ)))).mul cuspEst_Ept
  have h2 : CuspEst (fun z : ℍ =>
      3456 * Alpha ℓ 24 0 τ * eU ℓ z * (1 + eA τ z)) 3 :=
    (hu.const_mul (3456 * Alpha ℓ 24 0 τ)).mul hone_a
  have h3 : CuspEst (fun z : ℍ =>
      (-3456 * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ) * eV z
        * (1 - eB τ z)) 3 :=
    (hv.const_mul (-3456 * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)).mul hone_b
  have h4 : CuspEst (fun z : ℍ => 16 * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)
      * Work.Kernels.jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Work.Residues.Ept z ^ 3) 3 :=
    (cuspEst_Ept_pow 3).const_mul (16 * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)
      * Work.Kernels.jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ))
  have h5 : CuspEst (fun z : ℍ => ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)
      * Work.Kernels.jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z
      * Work.Residues.Ept z ^ 2) 5 :=
    (hv.const_mul ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)
      * Work.Kernels.jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ)).mul (cuspEst_Ept_pow 2)
  have h6 : CuspEst (fun z : ℍ =>
      (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * (1 + eE τ z)) 3 :=
    (hw.const_mul (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ)).mul hone_e
  have h7 : CuspEst (fun z : ℍ => ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)
      * Work.Kernels.jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z
      * Work.Residues.Ept z ^ 2) 3 :=
    h5.mono (k' := 3) (by norm_num)
  have hRHS : CuspEst (fun z : ℍ =>
      (55296 * Alpha ℓ 24 0 τ * eA τ z
          - 16 * (-3456 * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ) * eB τ z
          + 32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z) * Work.Residues.Ept z
        - 3456 * Alpha ℓ 24 0 τ * eU ℓ z * (1 + eA τ z)
        + (-3456 * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ) * eV z * (1 - eB τ z)
        - 16 * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
              + 1728 * Alpha ℓ 24 2 τ) * Work.Residues.Ept z ^ 3
        - ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
              + 1728 * Alpha ℓ 24 2 τ) * eV z * Work.Residues.Ept z ^ 2
        + (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * (1 + eE τ z)) 3 :=
    ((((h1.sub h2).add h3).sub h4).sub h7).add h6
  refine hRHS.congr (fun z => ?_)
  refine Eq.symm ?_
  have h := T24_cancellation (Alpha ℓ 24 0 τ) (Alpha ℓ 24 1 τ) (Alpha ℓ 24 2 τ)
    (Work.Kernels.jInvariantFun τ) (Work.Residues.Ept z) (eA τ z) (eB τ z) (eE τ z)
    (eU ℓ z) (eV z) (eW z)
  rw [← h]
  simp only [T24, eA, eB, eE, eU, eV, eW]
  ring

/-! ## The `d = 8` estimate -/

/-- **The `d = 8` estimate.**  `T₈ = O(t)`. -/
theorem cuspEst_T8 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    CuspEst (fun z => T8 ℓ τ z) 1 := by
  have h1 : CuspEst (fun z : ℍ => Work.Kernels.E10Fun z * ℓ.L_S z) 1 :=
    cuspEst_E10Fun.mul (cuspEst_LS ℓ)
  have h2 : CuspEst (fun z : ℍ => Work.Kernels.E8Fun z * Work.Kernels.VFun z) 1 :=
    cuspEst_E8Fun.mul cuspEst_VFun
  have h3 : CuspEst (fun z : ℍ => Work.Kernels.E6Fun z
      * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)) 1 :=
    cuspEst_E6Fun.mul cuspEst_UFun_sq_sub_WFun_sq
  have h1' : CuspEst (fun z : ℍ => (-3456 * Alpha ℓ 8 0 τ)
      * (Work.Kernels.E10Fun z * ℓ.L_S z)) 1 := h1.const_mul _
  have h2' : CuspEst (fun z : ℍ =>
      (-(Alpha ℓ 8 1 τ + Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ)))
        * (Work.Kernels.E8Fun z * Work.Kernels.VFun z)) 1 := h2.const_mul _
  have h3' : CuspEst (fun z : ℍ =>
      (-(Alpha ℓ 8 1 τ) + Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ)
        * (Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))) 1 :=
    h3.const_mul _
  have h4 : CuspEst (fun z : ℍ => (-3456 * Alpha ℓ 8 0 τ)
      * (Work.Kernels.E10Fun z * ℓ.L_S z)
      + (-(Alpha ℓ 8 1 τ + Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ)))
        * (Work.Kernels.E8Fun z * Work.Kernels.VFun z)
      + (-(Alpha ℓ 8 1 τ) + Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ)
        * (Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))) 1 :=
    (h1'.add h2').add h3'
  refine h4.congr (fun z => ?_)
  simp only [T8, Alpha]
  rw [ulen8_zero, ulen8_one, ulen8_two, fk_ten_eq, fk_eight_eq, fk_six_eq]
  simp only [Work.Kernels.E10Fun, Work.Kernels.E8Fun, Work.Kernels.E6Fun, Work.Kernels.VFun,
    Work.Kernels.UFun, Work.Kernels.WFun, Work.Kernels.jInvariantFun, Work.Kernels.theta00Fun,
    Work.Kernels.theta01Fun, Work.Kernels.theta10Fun]
  ring

/-! ## The limit -/

/-- `‖Ncusp ℓ d τ z‖ ≤ C t` for `d ∈ {8, 24}`, i.e. the cusp numerator is bounded at `i∞`. -/
theorem cuspEst_Ncusp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) : CuspEst (fun z => Ncusp ℓ d τ z) 1 := by
  rcases hd with rfl | rfl
  · obtain ⟨H, C, hC, h⟩ := cuspEst_T8 ℓ τ
    refine ⟨H, ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * C + 1, by positivity, fun z hz => ?_⟩
    simp only []
    rw [Ncusp_eight_expansion ℓ τ z, norm_mul]
    have h' := h z hz
    simp only [] at h'
    have ht : (0 : ℝ) ≤ Work.Residues.tpar z ^ 1 :=
      pow_nonneg (Work.Residues.tpar_nonneg z) 1
    calc ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * ‖T8 ℓ τ z‖
        ≤ ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (C * Work.Residues.tpar z ^ 1) :=
          mul_le_mul_of_nonneg_left h' (norm_nonneg _)
      _ ≤ (‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * C + 1) * Work.Residues.tpar z ^ 1 := by
          nlinarith [ht, norm_nonneg ((2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹), hC.le]
  · obtain ⟨H, C, hC, h⟩ := cuspEst_T24_mul_Ept_sq ℓ τ
    refine ⟨H, ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * C + 1, by positivity, fun z hz => ?_⟩
    have ht : 0 < Work.Residues.tpar z := Work.Residues.tpar_pos z
    have hE : ‖Work.Residues.Ept z ^ 2‖ = Work.Residues.tpar z ^ 2 := by
      rw [norm_pow, ← Work.Residues.tpar_eq_norm_Ept]
    have h' := h z hz
    simp only [] at h'
    have hT : ‖T24 ℓ τ z‖ * Work.Residues.tpar z ^ 2 ≤ C * Work.Residues.tpar z ^ 3 := by
      rw [← hE, ← norm_mul]
      exact h'
    have hT' : ‖T24 ℓ τ z‖ ≤ C * Work.Residues.tpar z := by
      have h2 : (0 : ℝ) < Work.Residues.tpar z ^ 2 := pow_pos ht 2
      refine le_of_mul_le_mul_right ?_ h2
      rw [show C * Work.Residues.tpar z * Work.Residues.tpar z ^ 2
          = C * Work.Residues.tpar z ^ 3 by ring]
      exact hT
    simp only []
    rw [Ncusp_twentyfour_expansion ℓ τ z, norm_mul]
    have hCnn : (0 : ℝ) ≤ ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * C + 1 := by positivity
    calc ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * ‖T24 ℓ τ z‖
        ≤ ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (C * Work.Residues.tpar z) :=
          mul_le_mul_of_nonneg_left hT' (norm_nonneg _)
      _ ≤ (‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * C + 1) * Work.Residues.tpar z ^ 1 := by
          rw [pow_one]
          nlinarith [Work.Residues.tpar_nonneg z, norm_nonneg ((2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹),
            hC.le]

/-- `Ecusp z = Ept z`. -/
lemma Ecusp_eq_Ept (z : ℍ) : Ecusp z = Work.Residues.Ept z := rfl

lemma norm_Ecusp_tpar (z : ℍ) : ‖Ecusp z‖ = Work.Residues.tpar z := by
  rw [Ecusp_eq_Ept, ← Work.Residues.tpar_eq_norm_Ept]

theorem KMinusCuspBallLimit (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) : Filter.Tendsto (fun z : UpperHalfPlane => Work.Asymptotics.Ecusp z * Work.Asymptotics.Ncusp ℓ d τ z) UpperHalfPlane.atImInfty (nhds 0) := by
  obtain ⟨H, C, hC, h⟩ := cuspEst_Ncusp ℓ d hd τ
  refine tendsto_of_norm_sub_le (k := 1) (C := C) (by norm_num) ?_
  refine eventually_of_forall_im_ge (A := H) fun z hz => ?_
  rw [sub_zero]
  have ht1 : Work.Residues.tpar z ≤ 1 := Work.Residues.tpar_le_one z
  have ht0 : (0 : ℝ) ≤ Work.Residues.tpar z := Work.Residues.tpar_nonneg z
  have hb := h z hz
  simp only [] at hb
  have hb' : ‖Ncusp ℓ d τ z‖ ≤ C * Work.Residues.tpar z := by
    simpa using hb
  calc ‖Ecusp z * Ncusp ℓ d τ z‖ = ‖Ecusp z‖ * ‖Ncusp ℓ d τ z‖ := norm_mul _ _
    _ ≤ Work.Residues.tpar z * (C * Work.Residues.tpar z) := by
        refine mul_le_mul ?_ hb' (norm_nonneg _) (Work.Residues.tpar_nonneg z)
        rw [norm_Ecusp_tpar]
    _ = C * Work.Residues.tpar z ^ 2 := by ring
    _ ≤ C * ‖Work.Residues.Ept z‖ ^ 1 := by
        have hsq : Work.Residues.tpar z ^ 2 ≤ Work.Residues.tpar z ^ 1 := by
          rw [pow_one]
          have := mul_le_mul_of_nonneg_left ht1 ht0
          simpa [pow_two] using this
        have hfin := mul_le_mul_of_nonneg_left hsq hC.le
        simpa [Work.Residues.tpar_eq_norm_Ept] using hfin

end

end Work.Asymptotics
