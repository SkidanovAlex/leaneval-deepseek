import Mathlib
import Submission.Work.Asymptotics.Tile.tileTB
import Submission.Work.Asymptotics.EtailE.EtailE_KMinus24
import Submission.Work.Asymptotics.KMFDDefs
import Submission.Work.Asymptotics.tile_Bdd_atoms

/-!
# The `K_-` cusp-`i∞` tail on the cusp-`±1` tiles

For `w ∈ E = KEpsilon`, `n = ±1` and `t ≥ 2 Im (S • w) + 1` the kernel `K_-^{(d)}` differs from
its cusp model `𝒢_-^{(d)}` by `O((scale w)^N (1+t)^M e^{π Im(Sw) - π t})`:

`Work.Asymptotics.Tile.KMinusTileTail`.

The proof uses the exact identity

`3456π(K_- - 𝒢_-)(τ,z) = -(Sh τ z)⁻¹ (br + Sh · br0)`

of `Work.Asymptotics.Compact.tail_identity`, the bound `‖(Sh τ z)⁻¹‖ ≤ 16`, and the explicit
decompositions of `br + Sh · br0` for `d = 8` (`bracket8e`) resp. `d = 24`
(`Work.Asymptotics.kmfd_bracket_decomp`), in which the leading (non-decaying) part is written as a
sum of `(τ-atom) × (z-atom)` products whose `τ`-atoms on the tiles are controlled by
`Work.Asymptotics.Tile.tile_tau_atoms` and `Work.Asymptotics.Tile.psi_combo_small`.
-/

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold
open Work.Kernels

noncomputable section

/-! ## The contour `z = i t` -/

/-- `z = i t` has imaginary part `t`. -/
lemma ktl_im_of_contour {z : ℍ} {t : ℝ} (hz : (z : ℂ) = (t : ℂ) * Complex.I) : z.im = t :=
  Work.Asymptotics.kmfd_im_of_contour hz

/-- On the contour, `‖z‖ = t`. -/
lemma ktl_norm_coe {z : ℍ} {t : ℝ} (ht : 1 ≤ t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) : ‖(z : ℂ)‖ = t := by
  rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]

/-- On the contour, `‖Ept z‖ = e^{-πt}`. -/
lemma ktl_norm_Ept {z : ℍ} {t : ℝ} (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    ‖Work.Residues.Ept z‖ = Real.exp (-(Real.pi * t)) := by
  rw [Work.Residues.norm_Ept, ktl_im_of_contour hz]

/-- `IsBigOq f n` implies the corresponding decaying `z`-atom bound. -/
lemma ZC.of_isBigOq {f : ℍ → ℂ} {n : ℕ} (h : Work.Asymptotics.IsBigOq f n) :
    ZC 0 (2 * (n : ℝ)) f := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  have hzim : z.im = t := ktl_im_of_contour hz
  have h1 := hf z (by rw [hzim]; exact ht)
  have hq : ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * t)) := by
    rw [Work.Asymptotics.norm_qParamFun, hzim]
  have h2 : ‖Work.Kernels.qParamFun z‖ ^ n = Real.exp (-((2 * (n : ℝ)) * Real.pi * t)) := by
    rw [hq, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [h2] at h1
  simpa using h1

/-- From a `∃ C, ∀ z, 1 ≤ z.im → ‖f z‖ ≤ C ‖Ept z‖^n` bound to a decaying `z`-atom. -/
lemma ZC.of_Eptpow {f : ℍ → ℂ} {n : ℕ} {C : ℝ} (hC : 0 < C)
    (h : ∀ z : ℍ, 1 ≤ z.im → ‖f z‖ ≤ C * ‖Work.Residues.Ept z‖ ^ n) :
    ZC 0 (n : ℝ) f := by
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  have hzim : z.im = t := ktl_im_of_contour hz
  have h1 := h z (by rw [hzim]; exact ht)
  have h2 : ‖Work.Residues.Ept z‖ ^ n = Real.exp (-((n : ℝ) * Real.pi * t)) := by
    rw [ktl_norm_Ept hz, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [h2] at h1
  simpa using h1

/-- From a `∃ C, ∀ z, 1 ≤ z.im → ‖f z‖ ≤ C (‖Ept z‖²)⁻¹` bound to a growing `z`-atom. -/
lemma ZCg.of_Eptinv2 {f : ℍ → ℂ} {C : ℝ} (hC : 0 < C)
    (h : ∀ z : ℍ, 1 ≤ z.im → ‖f z‖ ≤ C * (‖Work.Residues.Ept z‖ ^ 2)⁻¹) :
    ZCg 0 2 f := by
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  have hzim : z.im = t := ktl_im_of_contour hz
  have h1 := h z (by rw [hzim]; exact ht)
  have h2 : (‖Work.Residues.Ept z‖ ^ 2)⁻¹ = Real.exp (2 * Real.pi * t) := by
    rw [ktl_norm_Ept hz, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  rw [h2] at h1
  simpa using h1

/-- `E₈ - 1 = O(q)`. -/
lemma ktl_E8_sub_one_isBigOq : Work.Asymptotics.IsBigOq (fun z : ℍ => E8Fun z - 1) 1 := by
  have h1 : Work.Asymptotics.IsBigOq (fun z : ℍ => E4Fun z - 1) 1 :=
    Work.Asymptotics.E4_minus_one
  have h2 : Work.Asymptotics.IsBigOq (fun z : ℍ => E4Fun z + 1) 0 :=
    Work.Asymptotics.E4Fun_bdd.add
      (Work.Asymptotics.IsBigOq.bounded (f := fun _ : ℍ => (1 : ℂ)) 1 one_pos
        (fun _ _ => by simp))
  refine (h1.mul h2).congr (fun z => ?_)
  simp only [E8Fun]
  ring

/-! ## The `z`-atoms as `ZC`/`ZCg` -/

/-- `Xc = π i z + c` is `O(1+t)` on the contour. -/
lemma ZC.ktl_Xc (ℓ : Work.Kernels.LogLambdaData) :
    ZC 1 0 (fun z : ℍ => Compact.Xc ℓ z) := by
  refine ⟨Real.pi + ‖Compact.cuspC ℓ‖ + 1, by positivity, fun z t ht hz => ?_⟩
  have hzt : ‖(z : ℂ)‖ = t := ktl_norm_coe ht hz
  have h1 : ‖Compact.Xc ℓ z‖ ≤ Real.pi * ‖(z : ℂ)‖ + ‖Compact.cuspC ℓ‖ := by
    rw [Compact.Xc]
    refine le_trans (norm_add_le _ _) (le_of_eq ?_)
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Work.Asymptotics.EtailE.norm_pi]
  have h2 : Real.pi * ‖(z : ℂ)‖ + ‖Compact.cuspC ℓ‖
      ≤ (Real.pi + ‖Compact.cuspC ℓ‖ + 1) * (1 + t) := by
    rw [hzt]
    nlinarith [Real.pi_pos, norm_nonneg (Compact.cuspC ℓ)]
  simp only [Real.rpow_one, zero_mul, neg_zero, Real.exp_zero, mul_one]
  exact le_trans h1 h2

/-- `dDelta = Δ⁻¹ - Dref` is `O(e^{-2πt})`. -/
lemma ZC.ktl_dDelta (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 2 (fun z : ℍ => Compact.dDelta z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  exact ZC.of_Eptpow hC (fun z hz => (h z hz).1)

/-- `dW` is `O(e^{-3πt})`. -/
lemma ZC.ktl_dW (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 3 (fun z : ℍ => Compact.dW z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  exact ZC.of_Eptpow hC (fun z hz => (h z hz).2.1)

/-- `dD2` is `O(e^{-3πt})`. -/
lemma ZC.ktl_dD2 (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 3 (fun z : ℍ => Compact.dD2 z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  exact ZC.of_Eptpow hC (fun z hz => (h z hz).2.2.1)

/-- `dL` is `O(e^{-3πt})`. -/
lemma ZC.ktl_dL (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 3 (fun z : ℍ => Compact.dL ℓ z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  exact ZC.of_Eptpow hC (fun z hz => (h z hz).2.2.2.1)

/-- `dE14` is `O(e^{-4πt})`. -/
lemma ZC.ktl_dE14 (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 4 (fun z : ℍ => Compact.dE14 z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  exact ZC.of_Eptpow hC (fun z hz => (h z hz).2.2.2.2.1)

/-- `dE10` is `O(e^{-4πt})`. -/
lemma ZC.ktl_dE10 (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 4 (fun z : ℍ => Compact.dE10 z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  exact ZC.of_Eptpow hC (fun z hz => (h z hz).2.2.2.2.2.1)

/-- `E₄³ - E4refc` is `O(e^{-4πt})`. -/
lemma ZC.ktl_E4cref_dev (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 4 (fun z : ℍ => E4Fun z ^ 3 - Work.Asymptotics.kmfd_E4refc z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  exact ZC.of_Eptpow hC (fun z hz => (h z hz).2.2.2.2.2.2.1)

/-- `Δ - Ept²` is `O(e^{-4πt})`. -/
lemma ZC.ktl_Delta_dev (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 4 (fun z : ℍ => DeltaFun z - Work.Residues.Ept z ^ 2) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  exact ZC.of_Eptpow hC (fun z hz => (h z hz).2.2.2.2.2.2.2.1)

/-- `j - jref` is `O(e^{-2πt})`. -/
lemma ZC.ktl_jdev (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 2 (fun z : ℍ => jInvariantFun z - Work.Asymptotics.kmfd_jref z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  exact ZC.of_Eptpow hC (fun z hz => (h z hz).2.2.2.2.2.2.2.2.1)

/-- `L` is `O(1+t)` on the contour. -/
lemma ZC.ktl_L (ℓ : Work.Kernels.LogLambdaData) : ZC 1 0 (fun z : ℍ => ℓ.L z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  have h1 := (h z (by rw [ktl_im_of_contour hz]; exact ht)).2.2.2.2.2.2.2.2.2.1
  have hzt : ‖(z : ℂ)‖ = t := ktl_norm_coe ht hz
  rw [hzt] at h1
  simpa using h1

/-- `W` is `O(1)`. -/
lemma ZC.ktl_W (ℓ : Work.Kernels.LogLambdaData) : ZC 0 0 (fun z : ℍ => WFun z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  have h1 := (h z (by rw [ktl_im_of_contour hz]; exact ht)).2.2.2.2.2.2.2.2.2.2.1
  simpa using h1

/-- `U² - V²` is `O(1)`. -/
lemma ZC.ktl_D2 (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 0 (fun z : ℍ => UFun z ^ 2 - VFun z ^ 2) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  have h1 := (h z (by rw [ktl_im_of_contour hz]; exact ht)).2.2.2.2.2.2.2.2.2.2.2.1
  simpa using h1

/-- `E10ref` is `O(1)`. -/
lemma ZC.ktl_E10ref (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 0 (fun z : ℍ => Compact.E10ref z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  have h1 := (h z (by rw [ktl_im_of_contour hz]; exact ht)).2.2.2.2.2.2.2.2.2.2.2.2.1
  simpa using h1

/-- `E14ref` is `O(1)`. -/
lemma ZC.ktl_E14ref (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 0 (fun z : ℍ => Compact.E14ref z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  have h1 := (h z (by rw [ktl_im_of_contour hz]; exact ht)).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simpa using h1

/-- `Dref` is `O(e^{2πt})`. -/
lemma ZCg.ktl_Dref (ℓ : Work.Kernels.LogLambdaData) :
    ZCg 0 2 (fun z : ℍ => Compact.Dref z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  exact ZCg.of_Eptinv2 hC (fun z hz => (h z hz).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

/-- `jref` is `O(e^{2πt})`. -/
lemma ZCg.ktl_jref (ℓ : Work.Kernels.LogLambdaData) :
    ZCg 0 2 (fun z : ℍ => Work.Asymptotics.kmfd_jref z) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  exact ZCg.of_Eptinv2 hC (fun z hz => (h z hz).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

/-- `W - 1 = O(e^{-πt})`. -/
lemma ZC.ktl_Wsub1 (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 1 (fun z : ℍ => WFun z - 1) := by
  obtain ⟨C, hC, h⟩ := Work.Residues.WFun_decay
  refine ⟨C, hC, fun z t ht hz => ?_⟩
  have h1 := h z (by rw [ktl_im_of_contour hz]; exact ht)
  rw [ktl_im_of_contour hz] at h1
  simpa using h1

/-- `E₈ - 1 = O(e^{-2πt})`. -/
lemma ZC.ktl_E8sub1 (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 2 (fun z : ℍ => E8Fun z - 1) :=
  (ZC.of_isBigOq ktl_E8_sub_one_isBigOq).mono (by norm_num) (by norm_num)

/-- `E₆ - 1 = O(e^{-2πt})`. -/
lemma ZC.ktl_E6sub1 (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 2 (fun z : ℍ => E6Fun z - 1) :=
  (ZC.of_isBigOq Work.Asymptotics.E6_minus_one).mono (by norm_num) (by norm_num)

/-- `E₄³ - 1 = O(e^{-2πt})`. -/
lemma ZC.ktl_E4cube (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 2 (fun z : ℍ => E4Fun z ^ 3 - 1) :=
  (ZC.of_isBigOq Work.Asymptotics.E4cube_minus_one).mono (by norm_num) (by norm_num)

/-- `Δ = O(e^{-2πt})`. -/
lemma ZC.ktl_Delta (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 2 (fun z : ℍ => DeltaFun z) := by
  have h1 : ZC 0 4 (fun z : ℍ => DeltaFun z - Work.Residues.Ept z ^ 2) := ZC.ktl_Delta_dev ℓ
  have h2 : ZC 0 2 (fun z : ℍ => Work.Residues.Ept z ^ 2) := ZC.Ept_pow 2
  have h : ZC 0 2 (fun z : ℍ => (DeltaFun z - Work.Residues.Ept z ^ 2)
      + Work.Residues.Ept z ^ 2) := (h1.add h2).mono (m' := 0) (n' := 2) (by norm_num) (by norm_num)
  exact h.congr (fun z => by ring)

/-- `E14 = O(1)`. -/
lemma ZC.ktl_E14 (ℓ : Work.Kernels.LogLambdaData) : ZC 0 0 (fun z : ℍ => E14Fun z) := by
  have h1 : ZC 0 0 (fun z : ℍ => Compact.dE14 z) :=
    (ZC.ktl_dE14 ℓ).mono (m' := 0) (n' := 0) (by norm_num) (by norm_num)
  have h2 : ZC 0 0 (fun z : ℍ => Compact.E14ref z) := ZC.ktl_E14ref ℓ
  have h : ZC 0 0 (fun z : ℍ => Compact.dE14 z + Compact.E14ref z) := (h1.add h2).mono (m' := 0) (n' := 0) (by norm_num) (by norm_num)
  exact h.congr (fun z => by simp only [Compact.dE14]; ring)

/-- `E10 = O(1)`. -/
lemma ZC.ktl_E10 (ℓ : Work.Kernels.LogLambdaData) : ZC 0 0 (fun z : ℍ => E10Fun z) := by
  have h1 : ZC 0 0 (fun z : ℍ => Compact.dE10 z) :=
    (ZC.ktl_dE10 ℓ).mono (m' := 0) (n' := 0) (by norm_num) (by norm_num)
  have h2 : ZC 0 0 (fun z : ℍ => Compact.E10ref z) := ZC.ktl_E10ref ℓ
  have h : ZC 0 0 (fun z : ℍ => Compact.dE10 z + Compact.E10ref z) := (h1.add h2).mono (m' := 0) (n' := 0) (by norm_num) (by norm_num)
  exact h.congr (fun z => by simp only [Compact.dE10]; ring)

/-- `(U²-V²) - 1 = O(e^{-πt})`. -/
lemma ZC.ktl_D2sub1 (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 1 (fun z : ℍ => (UFun z ^ 2 - VFun z ^ 2) - 1) := by
  have h1 : ZC 0 1 (fun z : ℍ => (16 : ℂ) * Work.Residues.Ept z) :=
    ((ZC.const 0 le_rfl (16 : ℂ)).mul (ZC.Ept)).mono (m' := 0) (n' := 1)
      (by norm_num) (by norm_num)
  have h2 : ZC 0 1 (fun z : ℍ => (144 : ℂ) * Work.Residues.Ept z ^ 2) :=
    ((ZC.const 0 le_rfl (144 : ℂ)).mul (ZC.Ept_pow 2)).mono (m' := 0) (n' := 1)
      (by norm_num) (by norm_num)
  have h3 : ZC 0 1 (fun z : ℍ => Compact.dD2 z) :=
    (ZC.ktl_dD2 ℓ).mono (m' := 0) (n' := 1) (by norm_num) (by norm_num)
  have h : ZC 0 1 (fun z : ℍ => Compact.dD2 z + (16 : ℂ) * Work.Residues.Ept z
      - (144 : ℂ) * Work.Residues.Ept z ^ 2) := ((h3.add h1).sub h2).mono (m' := 0) (n' := 1) (by norm_num) (by norm_num)
  exact h.congr (fun z => by simp only [Compact.dD2, Compact.D2ref]; ring)

/-- `E₈W - 1 = O(e^{-πt})`. -/
lemma ZC.ktl_E8W (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 1 (fun z : ℍ => E8Fun z * WFun z - 1) := by
  have h1 : ZC 0 1 (fun z : ℍ => (E8Fun z - 1) * WFun z) :=
    (((ZC.ktl_E8sub1 ℓ).mono (m' := 0) (n' := 1) (by norm_num) (by norm_num)).mul
      (ZC.ktl_W ℓ)).mono (m' := 0) (n' := 1) (by norm_num) (by norm_num)
  have h : ZC 0 1 (fun z : ℍ => (E8Fun z - 1) * WFun z + (WFun z - 1)) :=
    (h1.add (ZC.ktl_Wsub1 ℓ)).mono (m' := 0) (n' := 1) (by norm_num) (by norm_num)
  exact h.congr (fun z => by ring)

/-- `E₈W - E₆(U²-V²) = O(e^{-πt})`. -/
lemma ZC.ktl_Az (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 1 (fun z : ℍ => E8Fun z * WFun z - E6Fun z * (UFun z ^ 2 - VFun z ^ 2)) := by
  have hA : ZC 0 1 (fun z : ℍ => (E8Fun z - 1) * WFun z) :=
    (((ZC.ktl_E8sub1 ℓ).mono (m' := 0) (n' := 1) (by norm_num) (by norm_num)).mul
      (ZC.ktl_W ℓ)).mono (m' := 0) (n' := 1) (by norm_num) (by norm_num)
  have hB : ZC 0 1 (fun z : ℍ => (E6Fun z - 1) * (UFun z ^ 2 - VFun z ^ 2)) :=
    (((ZC.ktl_E6sub1 ℓ).mono (m' := 0) (n' := 1) (by norm_num) (by norm_num)).mul
      (ZC.ktl_D2 ℓ)).mono (m' := 0) (n' := 1) (by norm_num) (by norm_num)
  have h : ZC 0 1 (fun z : ℍ => (E8Fun z - 1) * WFun z + (WFun z - 1)
      - (E6Fun z - 1) * (UFun z ^ 2 - VFun z ^ 2) - ((UFun z ^ 2 - VFun z ^ 2) - 1)) :=
    (((hA.add (ZC.ktl_Wsub1 ℓ)).sub hB).sub (ZC.ktl_D2sub1 ℓ)).mono (m' := 0) (n' := 1)
      (by norm_num) (by norm_num)
  exact h.congr (fun z => by ring)

/-- `Lref` is `O(1+t)` on the contour. -/
lemma ZC.ktl_Lref (ℓ : Work.Kernels.LogLambdaData) :
    ZC 1 0 (fun z : ℍ => Compact.Lref ℓ z) := by
  have h1 : ZC 1 0 (fun z : ℍ => ℓ.L z) := ZC.ktl_L ℓ
  have h2 : ZC 1 0 (fun z : ℍ => -Compact.dL ℓ z) :=
    ((ZC.ktl_dL ℓ).neg).mono (m' := 1) (n' := 0) (by norm_num) (by norm_num)
  have h : ZC 1 0 (fun z : ℍ => ℓ.L z + -Compact.dL ℓ z) :=
    (h1.add h2).mono (m' := 1) (n' := 0) (by norm_num) (by norm_num)
  exact h.congr (fun z => by simp only [Compact.dL]; ring)

/-- `E₁₀ · 𝓛 - Xc = O((1+t) e^{-πt})`. -/
lemma ZC.ktl_E10L (ℓ : Work.Kernels.LogLambdaData) :
    ZC 1 1 (fun z : ℍ => E10Fun z * ℓ.L z - Compact.Xc ℓ z) := by
  have hA : ZC 1 1 (fun z : ℍ => Compact.dE10 z * ℓ.L z) :=
    ((ZC.ktl_dE10 ℓ).mul (ZC.ktl_L ℓ)).mono (m' := 1) (n' := 1) (by norm_num) (by norm_num)
  have hB1 : ZC 1 1 (fun z : ℍ => (-264 : ℂ) * (Work.Residues.Ept z ^ 2 * Compact.Lref ℓ z)) :=
    ((ZC.const 0 le_rfl (-264 : ℂ)).mul ((ZC.Ept_pow 2).mul (ZC.ktl_Lref ℓ))).mono
      (m' := 1) (n' := 1) (by norm_num) (by norm_num)
  have hB2 : ZC 1 1 (fun z : ℍ => (-8 : ℂ) * Work.Residues.Ept z) :=
    ((ZC.const 0 le_rfl (-8 : ℂ)).mul ZC.Ept).mono (m' := 1) (n' := 1)
      (by norm_num) (by norm_num)
  have hB3 : ZC 1 1 (fun z : ℍ => (12 : ℂ) * Work.Residues.Ept z ^ 2) :=
    ((ZC.const 0 le_rfl (12 : ℂ)).mul (ZC.Ept_pow 2)).mono (m' := 1) (n' := 1)
      (by norm_num) (by norm_num)
  have hC : ZC 1 1 (fun z : ℍ => Compact.E10ref z * Compact.dL ℓ z) :=
    ((ZC.ktl_E10ref ℓ).mul (ZC.ktl_dL ℓ)).mono (m' := 1) (n' := 1) (by norm_num) (by norm_num)
  have h : ZC 1 1 (fun z : ℍ => Compact.dE10 z * ℓ.L z
      + (-264 : ℂ) * (Work.Residues.Ept z ^ 2 * Compact.Lref ℓ z)
      + (-8 : ℂ) * Work.Residues.Ept z
      + (12 : ℂ) * Work.Residues.Ept z ^ 2
      + Compact.E10ref z * Compact.dL ℓ z) :=
    ((((hA.add hB1).add hB2).add hB3).add hC).mono (m' := 1) (n' := 1) (by norm_num) (by norm_num)
  refine h.congr (fun z => ?_)
  simp only [Compact.dE10, Compact.dL, Compact.E10ref, Compact.Lref]
  ring

/-! ## `T`-invariance of `j` -/

lemma ktl_jInvariantFun_vadd_int (n : ℤ) (hn : n = 1 ∨ n = -1) (w : ℍ) :
    jInvariantFun ((n : ℝ) +ᵥ w) = jInvariantFun w := by
  rcases hn with h | h
  · rw [h, Int.cast_one]; exact Work.Kernels.KernelFacts.jInvariantFun_vadd_one w
  · rw [h, Int.cast_neg, Int.cast_one]
    have h1 := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ w)
    have h2 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ w) = w := by rw [← add_vadd]; norm_num
    rw [h2] at h1
    exact h1.symm

/-! ## The `Sh`-bound and the `d = 8` tile bracket -/

/-- `Sh τ z - 1 = O((scale w)^N e^{π Im(Sw) - π t})` for `τ = n + w`. -/
lemma TB.ktl_Shsub1 (ℓ : Work.Kernels.LogLambdaData) :
    TB Real.pi 1 (fun w n z => Compact.Sh ((n : ℝ) +ᵥ w) z - 1) := by
  obtain ⟨Cz, hCz, hzc⟩ := ZC.ktl_E4cube ℓ
  obtain ⟨Cd, hCd, hzd⟩ := ZC.ktl_Delta ℓ
  obtain ⟨Cj, Nj, hCj, hNj, hj⟩ := Work.Asymptotics.EtailE.E_bdd_j
  refine ⟨Cz + Cd * Cj, Nj, 0, by positivity, hNj, le_rfl, fun w n z t hn hw hz ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := by linarith [hw.2]
  have hsw1 : (1 : ℝ) ≤ (scale w) ^ Nj := Real.one_le_rpow (one_le_scale w) hNj
  have him : (0 : ℝ) ≤ (ModularGroup.S • w).im := by linarith [hw.2]
  have hE : Real.exp (-(2 * Real.pi * t)) ≤ (scale w) ^ Nj
      * Real.exp (Real.pi * (ModularGroup.S • w).im - Real.pi * t) := by
    have h1 : Real.exp (-(2 * Real.pi * t))
        ≤ Real.exp (Real.pi * (ModularGroup.S • w).im - Real.pi * t) := by
      rw [Real.exp_le_exp]; nlinarith [him, ht1, Real.pi_pos]
    have h2 : Real.exp (Real.pi * (ModularGroup.S • w).im - Real.pi * t)
        ≤ (scale w) ^ Nj * Real.exp (Real.pi * (ModularGroup.S • w).im - Real.pi * t) := by
      have hp := Real.exp_pos (Real.pi * (ModularGroup.S • w).im - Real.pi * t)
      nlinarith [hsw1, hp]
    linarith
  have hE2 : Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t)
      ≤ (scale w) ^ Nj * Real.exp (Real.pi * (ModularGroup.S • w).im - Real.pi * t) := by
    have h1 : Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t)
        ≤ Real.exp (Real.pi * (ModularGroup.S • w).im - Real.pi * t) := by
      rw [Real.exp_le_exp]
      have h2 := ht
      nlinarith [him, h2, Real.pi_pos]
    have h3 : Real.exp (Real.pi * (ModularGroup.S • w).im - Real.pi * t)
        ≤ (scale w) ^ Nj * Real.exp (Real.pi * (ModularGroup.S • w).im - Real.pi * t) := by
      have hp := Real.exp_pos (Real.pi * (ModularGroup.S • w).im - Real.pi * t)
      nlinarith [hsw1, hp]
    linarith
  have h1 : ‖E4Fun z ^ 3 - 1‖ ≤ Cz * (1 + t) ^ (0:ℝ) * Real.exp (-(2 * Real.pi * t)) :=
    hzc z t ht1 hz
  have h2 : ‖DeltaFun z‖ ≤ Cd * (1 + t) ^ (0:ℝ) * Real.exp (-(2 * Real.pi * t)) :=
    hzd z t ht1 hz
  have h3 : ‖jInvariantFun ((n : ℝ) +ᵥ w)‖
      ≤ Cj * (scale w) ^ Nj * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
    have := hj w hw
    simpa only [ktl_jInvariantFun_vadd_int n hn w] using this
  have hsh : Compact.Sh ((n : ℝ) +ᵥ w) z - 1
      = (E4Fun z ^ 3 - 1) - DeltaFun z * jInvariantFun ((n : ℝ) +ᵥ w) := by
    simp only [Compact.Sh]; ring
  change ‖Compact.Sh ((n : ℝ) +ᵥ w) z - 1‖ ≤ (Cz + Cd * Cj) * (scale w) ^ Nj
    * (1 + t) ^ (0:ℝ) * Real.exp (Real.pi * (ModularGroup.S • w).im - 1 * Real.pi * t)
  rw [hsh]
  have hprod : ‖DeltaFun z * jInvariantFun ((n : ℝ) +ᵥ w)‖
      ≤ Cd * Cj * (scale w) ^ Nj * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) := by
    rw [norm_mul]
    have hbase : Cd * (1 + t) ^ (0:ℝ) * Real.exp (-(2 * Real.pi * t))
        * (Cj * (scale w) ^ Nj * Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
        = Cd * Cj * (scale w) ^ Nj
          * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t) := by
      have hre : Cd * (1 + t) ^ (0:ℝ) * Real.exp (-(2 * Real.pi * t))
          * (Cj * (scale w) ^ Nj * Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
          = Cd * Cj * (scale w) ^ Nj * (1 + t) ^ (0:ℝ)
            * (Real.exp (-(2 * Real.pi * t))
              * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) := by ring
      rw [hre, ← Real.exp_add, Real.rpow_zero, mul_one,
        show -(2 * Real.pi * t) + 2 * Real.pi * (ModularGroup.S • w).im
          = 2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t from by ring]
    rw [← hbase]
    exact mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
  refine le_trans (norm_sub_le _ _) ?_
  have hE2' : Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t)
      ≤ Real.exp (Real.pi * (ModularGroup.S • w).im - Real.pi * t) := by
    rw [Real.exp_le_exp]; nlinarith [him, ht, Real.pi_pos]
  have hCzn : (0:ℝ) ≤ Cz := hCz.le
  have hCdj : (0:ℝ) ≤ Cd * Cj := mul_nonneg hCd.le hCj.le
  have h0t : (0:ℝ) ≤ (1 + t) ^ (0:ℝ) := Real.rpow_nonneg (by linarith) 0
  have hswN : (0:ℝ) ≤ (scale w) ^ Nj := Real.rpow_nonneg (scale_pos w).le Nj
  have hA : Cz * (1 + t) ^ (0:ℝ) * Real.exp (-(2 * Real.pi * t))
      ≤ Cz * (1 + t) ^ (0:ℝ) * ((scale w) ^ Nj
          * Real.exp (Real.pi * (ModularGroup.S • w).im - Real.pi * t)) :=
    mul_le_mul_of_nonneg_left hE (mul_nonneg hCzn h0t)
  have hB : Cd * Cj * (scale w) ^ Nj
        * Real.exp (2 * Real.pi * (ModularGroup.S • w).im - 2 * Real.pi * t)
      ≤ Cd * Cj * (scale w) ^ Nj
        * Real.exp (Real.pi * (ModularGroup.S • w).im - Real.pi * t) :=
    mul_le_mul_of_nonneg_left hE2' (mul_nonneg hCdj hswN)
  have hgoal : (Cz + Cd * Cj) * (scale w) ^ Nj * (1 + t) ^ (0:ℝ)
      * Real.exp (Real.pi * (ModularGroup.S • w).im - 1 * Real.pi * t)
      = Cz * (1 + t) ^ (0:ℝ) * ((scale w) ^ Nj
          * Real.exp (Real.pi * (ModularGroup.S • w).im - Real.pi * t))
        + Cd * Cj * (scale w) ^ Nj
          * Real.exp (Real.pi * (ModularGroup.S • w).im - Real.pi * t) := by
    rw [Real.rpow_zero, mul_one]
    have h2' : Real.exp (Real.pi * (ModularGroup.S • w).im - 1 * Real.pi * t)
        = Real.exp (Real.pi * (ModularGroup.S • w).im - Real.pi * t) := by
      congr 1; ring
    rw [h2']; ring
  rw [hgoal]
  linarith [le_trans h1 hA, le_trans hprod hB]

/-! ## `br0` in dimension `8` -/

lemma TB.ktl_br0_8 (ℓ : Work.Kernels.LogLambdaData) :
    TB 0 0 (fun w n z => Compact.br0 8 ℓ ((n : ℝ) +ᵥ w) z) := by
  have h1 : TB 0 0 (fun w n z => (3456 : ℂ) * (Compact.Xc ℓ z * E4Fun ((n : ℝ) +ᵥ w))) :=
    (TB.const_mul 3456 (TB.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TB.E4)).mono
      (le_refl 0) (by norm_num)
  have h2 : TB 0 0 (fun w n z => (1728 : ℂ) * Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)) :=
    (TB.const_mul 1728 (TB.psi4 ℓ)).mono (le_refl 0) (by norm_num)
  refine (h1.sub h2).congr (fun w n z => ?_)
  simp only [Compact.br0_8]
  ring

/-! ## The `d = 8` tile bracket -/

lemma TB.ktl_G8 (ℓ : Work.Kernels.LogLambdaData) :
    TB Real.pi 1 (fun w n z => Compact.brMinus ℓ 8 ((n : ℝ) +ᵥ w) z
      + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 8 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hA1 : TB Real.pi 1 (fun w n z => (-3456 : ℂ)
      * ((E10Fun z * ℓ.L z - Compact.Xc ℓ z) * E4Fun ((n : ℝ) +ᵥ w))) :=
    (TB.const_mul (-3456) (TB.mul_ZC zero_le_one (ZC.ktl_E10L ℓ) TB.E4)).mono
      (by linarith [Real.pi_pos]) (by norm_num)
  have hA2 : TB Real.pi 1 (fun w n z => (-1 : ℂ)
      * ((E8Fun z * WFun z - E6Fun z * (UFun z ^ 2 - VFun z ^ 2))
          * Work.Residues.Lamb ℓ ((n : ℝ) +ᵥ w))) :=
    (TB.const_mul (-1) (TB.mul_ZC (le_refl 0) (ZC.ktl_Az ℓ) (TB.lamb ℓ))).mono
      (le_refl Real.pi) (by norm_num)
  have hA3 : TB Real.pi 1 (fun w n z => (1728 : ℂ) * ((E8Fun z * WFun z - 1)
      * Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w))) :=
    (TB.const_mul 1728 (TB.mul_ZC (le_refl 0) (ZC.ktl_E8W ℓ) (TB.psi4 ℓ))).mono
      (by linarith [Real.pi_pos]) (by norm_num)
  have hA4 : TB Real.pi 1 (fun w n z => (Compact.Sh ((n : ℝ) +ᵥ w) z - 1)
      * Compact.br0 8 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TB.mul (TB.ktl_Shsub1 ℓ) (TB.ktl_br0_8 ℓ)).mono (by linarith [Real.pi_pos])
      (by norm_num)
  refine (TB.add (TB.add (TB.add hA1 hA2) hA3) hA4).congr (fun w n z => ?_)
  simp only [Compact.brMinus_eight, Compact.br0_8, Work.Residues.bracket8e,
    Work.Residues.Lamb, Compact.Xc, Work.Kernels.c1728]
  ring

/-! ## The `d = 24` tile bracket: the coefficients `c₁, …, c₈` -/

/-- `j²Δ = j·(jΔ)` on the tiles. -/
lemma TB.ktl_j2Delta (ℓ : Work.Kernels.LogLambdaData) :
    TB (2 * Real.pi) 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) ^ 2 * DeltaFun ((n : ℝ) +ᵥ w)) := by
  refine ((TB.j.mul TB.jDelta).mono (by linarith [Real.pi_pos]) (by norm_num)).congr
    (fun w n z => ?_)
  ring

/-- `j·(ψ₄E₈ - ψ₂E₁₀)` on the tiles. -/
lemma TB.ktl_jpsiCombo (ℓ : Work.Kernels.LogLambdaData) :
    TB Real.pi 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) * psiCombo ℓ ((n : ℝ) +ᵥ w)) :=
  (TB.j.mul (TB.psi_combo ℓ)).mono (by linarith [Real.pi_pos]) (by norm_num)

lemma TB.ktl_c1 (ℓ : Work.Kernels.LogLambdaData) :
    TB Real.pi 0 (fun w n z => Work.Asymptotics.kmfd_c1 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hjD : TB Real.pi 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.jDelta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hjp : TB Real.pi 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) * psiCombo ℓ ((n : ℝ) +ᵥ w)) :=
    TB.ktl_jpsiCombo ℓ
  have hD : TB Real.pi 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TB Real.pi 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    (TB.psi2E10 ℓ).mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp4 : TB Real.pi 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    (TB.psi4E8 ℓ).mono (by linarith [Real.pi_pos]) (le_refl 0)
  refine (TB.add (TB.add (TB.add (TB.add (TB.const_mul (27648 : ℂ) hjD)
      (TB.const_mul (24 : ℂ) hjp)) (TB.const_mul (-20570112 : ℂ) hD))
      (TB.const_mul (15744 : ℂ) hp2)) (TB.const_mul (-29568 : ℂ) hp4)).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c1, psiCombo]
  ring

lemma TB.ktl_c2 (ℓ : Work.Kernels.LogLambdaData) :
    TB (2 * Real.pi) 0 (fun w n z => Work.Asymptotics.kmfd_c2 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hj2D : TB (2 * Real.pi) 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) ^ 2 * DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.ktl_j2Delta ℓ
  have hjD : TB (2 * Real.pi) 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.jDelta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hD : TB (2 * Real.pi) 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TB (2 * Real.pi) 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    (TB.psi2E10 ℓ).mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp4 : TB (2 * Real.pi) 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    (TB.psi4E8 ℓ).mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hjp2 : TB (2 * Real.pi) 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w)
        * (Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w))) :=
    TB.jpsi2E10 ℓ
  have hjp4 : TB (2 * Real.pi) 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w)
        * (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))) :=
    TB.jpsi4E8 ℓ
  have hX2 : TB (2 * Real.pi) 0 (fun w n z => Compact.Xc ℓ z
      * (jInvariantFun ((n : ℝ) +ᵥ w) ^ 2 * DeltaFun ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) hj2D).mono (le_refl (2 * Real.pi)) (by norm_num)
  have hX1 : TB (2 * Real.pi) 0 (fun w n z => Compact.Xc ℓ z
      * (jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TB.jDelta).mono (by linarith [Real.pi_pos])
      (by norm_num)
  have hX0 : TB (2 * Real.pi) 0 (fun w n z => Compact.Xc ℓ z * DeltaFun ((n : ℝ) +ᵥ w)) :=
    (TB.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TB.Delta).mono (by linarith [Real.pi_pos])
      (by norm_num)
  refine (TB.add (TB.add (TB.add (TB.add (TB.add (TB.add (TB.add (TB.add
    (TB.const_mul (-3456 : ℂ) hX2) (TB.const_mul (4976640 : ℂ) hX1))
    (TB.const_mul (-1192402944 : ℂ) hX0)) (TB.const_mul (41472 : ℂ) hjD))
    (TB.const_mul (1080 : ℂ) hjp2)) (TB.const_mul (648 : ℂ) hjp4))
    (TB.const_mul (31850496 : ℂ) hD)) (TB.const_mul (-651456 : ℂ) hp2))
    (TB.const_mul (-551232 : ℂ) hp4)).congr (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c2]
  ring

lemma TB.ktl_c3 (ℓ : Work.Kernels.LogLambdaData) :
    TB 0 0 (fun w n z => Work.Asymptotics.kmfd_c3 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hD : TB 0 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TB 0 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    TB.psi2E10 ℓ
  have hp4 : TB 0 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    TB.psi4E8 ℓ
  refine (TB.add (TB.add (TB.const_mul (-5271257088 : ℂ) hD)
    (TB.const_mul (3142656 : ℂ) hp2)) (TB.const_mul (-3142656 : ℂ) hp4)).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c3]
  ring

lemma TB.ktl_c4 (ℓ : Work.Kernels.LogLambdaData) :
    TB 0 0 (fun w n z => Work.Asymptotics.kmfd_c4 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hjD : TB 0 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)) := TB.jDelta
  have hD : TB 0 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TB 0 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    TB.psi2E10 ℓ
  have hp4 : TB 0 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    TB.psi4E8 ℓ
  have hX1 : TB 0 0 (fun w n z => Compact.Xc ℓ z
      * (jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TB.jDelta).mono (le_refl 0) (by norm_num)
  have hX0 : TB 0 0 (fun w n z => Compact.Xc ℓ z * DeltaFun ((n : ℝ) +ᵥ w)) :=
    (TB.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TB.Delta).mono (by linarith [Real.pi_pos])
      (by norm_num)
  refine (TB.add (TB.add (TB.add (TB.add (TB.const_mul (597196800 : ℂ) hX1)
    (TB.const_mul (-382205952000 : ℂ) hX0)) (TB.const_mul (8623521792 : ℂ) hD))
    (TB.const_mul (-178689024 : ℂ) hp2)) (TB.const_mul (-119909376 : ℂ) hp4)).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c4]
  ring

lemma TB.ktl_c5 (ℓ : Work.Kernels.LogLambdaData) :
    TB 0 0 (fun w n z => Work.Asymptotics.kmfd_c5 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hD : TB 0 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TB 0 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    TB.psi2E10 ℓ
  have hp4 : TB 0 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    TB.psi4E8 ℓ
  refine (TB.add (TB.add (TB.const_mul (-496867737600 : ℂ) hD)
    (TB.const_mul (287539200 : ℂ) hp2)) (TB.const_mul (-287539200 : ℂ) hp4)).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c5]
  ring

lemma TB.ktl_c6 (ℓ : Work.Kernels.LogLambdaData) :
    TB 0 0 (fun w n z => Work.Asymptotics.kmfd_c6 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hjD : TB 0 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)) := TB.jDelta
  have hD : TB 0 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TB 0 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    TB.psi2E10 ℓ
  have hp4 : TB 0 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    TB.psi4E8 ℓ
  have hX1 : TB 0 0 (fun w n z => Compact.Xc ℓ z
      * (jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TB.jDelta).mono (le_refl 0) (by norm_num)
  have hX0 : TB 0 0 (fun w n z => Compact.Xc ℓ z * DeltaFun ((n : ℝ) +ᵥ w)) :=
    (TB.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TB.Delta).mono (by linarith [Real.pi_pos])
      (by norm_num)
  refine (TB.add (TB.add (TB.add (TB.add (TB.const_mul (47775744000 : ℂ) hX1)
    (TB.const_mul (-34398535680000 : ℂ) hX0)) (TB.const_mul (917294284800 : ℂ) hD))
    (TB.const_mul (-15460761600 : ℂ) hp2)) (TB.const_mul (-8427110400 : ℂ) hp4)).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c6]
  ring

lemma TB.ktl_c7 (ℓ : Work.Kernels.LogLambdaData) :
    TB 0 0 (fun w n z => Work.Asymptotics.kmfd_c7 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hD : TB 0 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TB 0 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    TB.psi2E10 ℓ
  have hp4 : TB 0 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    TB.psi4E8 ℓ
  refine (TB.add (TB.add (TB.const_mul (-9172942848000 : ℂ) hD)
    (TB.const_mul (5308416000 : ℂ) hp2)) (TB.const_mul (-5308416000 : ℂ) hp4)).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c7]
  ring

lemma TB.ktl_c8 (ℓ : Work.Kernels.LogLambdaData) :
    TB 0 0 (fun w n z => Work.Asymptotics.kmfd_c8 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hD : TB 0 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TB 0 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    TB.psi2E10 ℓ
  have hp4 : TB 0 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    TB.psi4E8 ℓ
  refine (TB.add (TB.add (TB.const_mul (27518828544000 : ℂ) hD)
    (TB.const_mul (-15925248000 : ℂ) hp2)) (TB.const_mul (15925248000 : ℂ) hp4)).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_c8]
  ring

/-! ## The `d = 24` tile bracket: `A24`, `B24`, `C24`, `kmfd_dA` -/

lemma ZC.ktl_E14L (ℓ : Work.Kernels.LogLambdaData) :
    ZC 1 0 (fun z : ℍ => E14Fun z * ℓ.L z) :=
  ((ZC.ktl_E14 ℓ).mul (ZC.ktl_L ℓ)).mono (m' := 1) (n' := 0) (by norm_num) (by norm_num)

lemma ZC.ktl_E10D2 (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 0 (fun z : ℍ => E10Fun z * (UFun z ^ 2 - VFun z ^ 2)) :=
  ((ZC.ktl_E10 ℓ).mul (ZC.ktl_D2 ℓ)).mono (m' := 0) (n' := 0) (by norm_num) (by norm_num)

lemma ZC.ktl_dA1 (ℓ : Work.Kernels.LogLambdaData) :
    ZC 1 3 (fun z : ℍ => Compact.dE14 z * ℓ.L z + Compact.E14ref z * Compact.dL ℓ z) := by
  have h1 : ZC 1 3 (fun z : ℍ => Compact.dE14 z * ℓ.L z) :=
    ((ZC.ktl_dE14 ℓ).mul (ZC.ktl_L ℓ)).mono (m' := 1) (n' := 3) (by norm_num) (by norm_num)
  have h2 : ZC 0 3 (fun z : ℍ => Compact.E14ref z * Compact.dL ℓ z) :=
    ((ZC.ktl_E14ref ℓ).mul (ZC.ktl_dL ℓ)).mono (m' := 0) (n' := 3) (by norm_num) (by norm_num)
  exact (h1.add h2).mono (m' := 1) (n' := 3) (by norm_num) (by norm_num)

lemma ZC.ktl_dA2 (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 3 (fun z : ℍ => Compact.dE10 z * (UFun z ^ 2 - VFun z ^ 2)
      + Compact.E10ref z * Compact.dD2 z) := by
  have h1 : ZC 0 3 (fun z : ℍ => Compact.dE10 z * (UFun z ^ 2 - VFun z ^ 2)) :=
    ((ZC.ktl_dE10 ℓ).mul (ZC.ktl_D2 ℓ)).mono (m' := 0) (n' := 3) (by norm_num) (by norm_num)
  have h2 : ZC 0 3 (fun z : ℍ => Compact.E10ref z * Compact.dD2 z) :=
    ((ZC.ktl_E10ref ℓ).mul (ZC.ktl_dD2 ℓ)).mono (m' := 0) (n' := 3) (by norm_num) (by norm_num)
  exact (h1.add h2).mono (m' := 0) (n' := 3) (by norm_num) (by norm_num)

/-- `jref · dW = O(e^{-πt})`. -/
lemma ZC.ktl_jref_dW (ℓ : Work.Kernels.LogLambdaData) :
    ZC 0 1 (fun z : ℍ => Work.Asymptotics.kmfd_jref z * Compact.dW z) := by
  obtain ⟨C1, hC1, h1⟩ := ZCg.ktl_jref ℓ
  obtain ⟨C2, hC2, h2⟩ := ZC.ktl_dW ℓ
  refine ⟨C1 * C2, by positivity, fun z t ht hz => ?_⟩
  rw [norm_mul]
  have h3 : Real.exp (2 * Real.pi * t) * Real.exp (-(3 * Real.pi * t))
      ≤ Real.exp (-(1 * Real.pi * t)) := by
    rw [← Real.exp_add, Real.exp_le_exp]; nlinarith [Real.pi_pos, ht]
  calc ‖Work.Asymptotics.kmfd_jref z‖ * ‖Compact.dW z‖
      ≤ (C1 * (1 + t) ^ (0:ℝ) * Real.exp (2 * Real.pi * t))
        * (C2 * (1 + t) ^ (0:ℝ) * Real.exp (-(3 * Real.pi * t))) :=
        mul_le_mul (h1 z t ht hz) (h2 z t ht hz) (norm_nonneg _) (by positivity)
    _ = C1 * C2 * (1 + t) ^ (0:ℝ)
        * (Real.exp (2 * Real.pi * t) * Real.exp (-(3 * Real.pi * t))) := by
        rw [Real.rpow_zero, mul_one]; ring
    _ ≤ C1 * C2 * (1 + t) ^ (0:ℝ) * Real.exp (-(1 * Real.pi * t)) := by
        refine mul_le_mul_of_nonneg_left h3 (by positivity)

lemma TB.ktl_dA (ℓ : Work.Kernels.LogLambdaData) :
    TB 0 3 (fun w n z => Work.Asymptotics.kmfd_dA ℓ ((n : ℝ) +ᵥ w) z) := by
  have hT1 : TB (-(2 * Real.pi)) 0
      (fun w n _ => (-3456 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) := TB.const_mul (-3456) TB.Delta
  have hT2 : TB 0 0 (fun w n _ =>
      -(Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)
        - Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))) :=
    (TB.sub (TB.psi2E10 ℓ) (TB.psi4E8 ℓ)).neg
  have hp1 : TB (-(2 * Real.pi)) (0 + 3)
      (fun w n z => (Compact.dE14 z * ℓ.L z + Compact.E14ref z * Compact.dL ℓ z)
        * ((-3456 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w))) :=
    TB.mul_ZC zero_le_one (ZC.ktl_dA1 ℓ) hT1
  have hp2 : TB 0 (0 + 3)
      (fun w n z => (Compact.dE10 z * (UFun z ^ 2 - VFun z ^ 2)
          + Compact.E10ref z * Compact.dD2 z)
        * (-(Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)
          - Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)))) :=
    TB.mul_ZC (le_refl 0) (ZC.ktl_dA2 ℓ) hT2
  refine (TB.add (hp1.mono (by linarith [Real.pi_pos]) (by norm_num))
    (hp2.mono (le_refl 0) (by norm_num))).congr (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_dA]
  ring

lemma TB.ktl_A24 (ℓ : Work.Kernels.LogLambdaData) :
    TB 0 0 (fun w n z => Compact.A24 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hT1 : TB (-(2 * Real.pi)) 0
      (fun w n _ => (-3456 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) := TB.const_mul (-3456) TB.Delta
  have hT2 : TB 0 0 (fun w n _ =>
      -(Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)
        - Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))) :=
    (TB.sub (TB.psi2E10 ℓ) (TB.psi4E8 ℓ)).neg
  have hp1 : TB (-(2 * Real.pi)) 0
      (fun w n z => (E14Fun z * ℓ.L z) * ((-3456 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC zero_le_one (ZC.ktl_E14L ℓ) hT1).mono (le_refl (-(2 * Real.pi))) (by norm_num)
  have hp2 : TB 0 0
      (fun w n z => (E10Fun z * (UFun z ^ 2 - VFun z ^ 2))
        * (-(Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)
          - Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)))) :=
    (TB.mul_ZC (le_refl 0) (ZC.ktl_E10D2 ℓ) hT2).mono (le_refl 0) (by norm_num)
  refine (TB.add (hp1.mono (by linarith [Real.pi_pos]) (by norm_num)) hp2).congr
    (fun w n z => ?_)
  simp only [Compact.A24]
  ring

lemma TB.ktl_B24 (ℓ : Work.Kernels.LogLambdaData) :
    TB 0 0 (fun w n z => Compact.B24 ℓ ((n : ℝ) +ᵥ w)) := by
  have h1 : TB 0 0 (fun w n _ => (-3456 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    (TB.const_mul (-3456) TB.Delta).mono (by linarith [Real.pi_pos]) (le_refl 0)
  have h2 : TB 0 0
      (fun w n _ => (2 : ℂ) * (Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w))) :=
    TB.const_mul 2 (TB.psi2E10 ℓ)
  have h3 : TB 0 0
      (fun w n _ => (2 : ℂ) * (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))) :=
    TB.const_mul 2 (TB.psi4E8 ℓ)
  refine (TB.sub (TB.add h1 h2) h3).congr (fun w n z => ?_)
  simp only [Compact.B24]
  ring

lemma TB.ktl_C24 (ℓ : Work.Kernels.LogLambdaData) :
    TB (2 * Real.pi) 0 (fun w n z => Compact.C24 ℓ ((n : ℝ) +ᵥ w)) := by
  have h1 : TB (2 * Real.pi) 0 (fun w n _ =>
      (Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w))
        * jInvariantFun ((n : ℝ) +ᵥ w)) :=
    ((TB.psi2E10 ℓ).mul TB.j).mono (by linarith [Real.pi_pos]) (by norm_num)
  have hsub : TB (2 * Real.pi) 0
      (fun w n _ => (1728 : ℂ) - jInvariantFun ((n : ℝ) +ᵥ w)) :=
    TB.sub ((TB.const (1728 : ℂ)).mono (by linarith [Real.pi_pos]) (le_refl 0)) TB.j
  have h2 : TB (2 * Real.pi) 0 (fun w n _ =>
      (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))
        * ((1728 : ℂ) - jInvariantFun ((n : ℝ) +ᵥ w))) :=
    ((TB.psi4E8 ℓ).mul hsub).mono (by linarith [Real.pi_pos]) (by norm_num)
  refine (TB.add h1 h2).congr (fun w n z => ?_)
  simp only [Compact.C24, mul_assoc]

/-! ## The deviation `kmfd_dev` -/

lemma TB.of_ZC {m n : ℝ} {f : ℍ → ℂ} (hm : 0 ≤ m) (hf : ZC m n f) :
    TB 0 n (fun _ _ z => f z) := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨C, 0, m, hC, le_refl 0, hm, fun w k z t hk hw hz ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := by linarith [hw.2]
  have h1 := hb z t ht1 hz
  have hexp : Real.exp (0 * (ModularGroup.S • w).im - n * Real.pi * t)
      = Real.exp (-(n * Real.pi * t)) := by congr 1; ring
  rw [hexp, Real.rpow_zero, mul_one]
  exact h1

lemma TB.ktl_einv2 : TB 0 (-2) (fun _ _ z => Compact.einv2 z) := by
  refine ⟨1, 0, 0, one_pos, le_refl 0, le_refl 0, fun w n z t hn hw hz ht => ?_⟩
  have h1 : ‖Compact.einv2 z‖ = Real.exp (2 * Real.pi * t) := by
    rw [Compact.einv2, norm_pow, norm_inv, ktl_norm_Ept hz]
    rw [show ((Real.exp (-(Real.pi * t)))⁻¹) ^ 2 = Real.exp (2 * Real.pi * t) from by
      rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; ring]
  rw [h1]
  have hexp : (0:ℝ) * (ModularGroup.S • w).im - (-2) * Real.pi * t = 2 * Real.pi * t := by ring
  rw [hexp]
  simp

lemma TB.ktl_Nf (ℓ : Work.Kernels.LogLambdaData) :
    TB 0 0 (fun w n z => Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) := by
  have hDX : TB 0 0 (fun w n z => Compact.Xc ℓ z * DeltaFun ((n : ℝ) +ᵥ w)) :=
    (TB.mul_ZC zero_le_one (ZC.ktl_Xc ℓ) TB.Delta).mono (by linarith [Real.pi_pos])
      (by norm_num)
  have hD : TB 0 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TB 0 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    TB.psi2E10 ℓ
  have hp4 : TB 0 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    TB.psi4E8 ℓ
  refine (TB.add (TB.add (TB.add (TB.const_mul (-3456 : ℂ) hDX) (TB.const_mul 3456 hD))
    (TB.const_mul (-3 : ℂ) hp2)) (TB.const_mul 3 hp4)).congr (fun w n z => ?_)
  simp only [Compact.Nf]
  ring

lemma TB.ktl_Mf (ℓ : Work.Kernels.LogLambdaData) :
    TB (2 * Real.pi) 0 (fun w n z => -Compact.Mf ℓ ((n : ℝ) +ᵥ w)) := by
  have hD : TB (2 * Real.pi) 0 (fun w n _ => DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.Delta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hjD : TB (2 * Real.pi) 0
      (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.jDelta.mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp2 : TB (2 * Real.pi) 0
      (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)) :=
    (TB.psi2E10 ℓ).mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hp4 : TB (2 * Real.pi) 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)) :=
    (TB.psi4E8 ℓ).mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hjp2 : TB (2 * Real.pi) 0 (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w)
      * (Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w))) := TB.jpsi2E10 ℓ
  have hjp4 : TB (2 * Real.pi) 0 (fun w n _ => jInvariantFun ((n : ℝ) +ᵥ w)
      * (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))) := TB.jpsi4E8 ℓ
  have h1 : TB (2 * Real.pi) 0
      (fun w n _ => (-41472 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    TB.const_mul (-41472) hD
  have h2 : TB (2 * Real.pi) 0 (fun w n _ => (-3456 : ℂ)
      * (jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)
        - (768 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w))) :=
    TB.const_mul (-3456) (TB.sub hjD (TB.const_mul (768 : ℂ) hD))
  have h3 : TB (2 * Real.pi) 0 (fun w n _ =>
      Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)
        * ((3 : ℂ) * jInvariantFun ((n : ℝ) +ᵥ w) - 1152)) := by
    have ha : TB (2 * Real.pi) 0 (fun w n _ =>
        (3 : ℂ) * (jInvariantFun ((n : ℝ) +ᵥ w) * (Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w)
          * E10Fun ((n : ℝ) +ᵥ w)))) := TB.const_mul 3 hjp2
    have hb : TB (2 * Real.pi) 0 (fun w n _ =>
        (1152 : ℂ) * (Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w))) :=
      TB.const_mul 1152 hp2
    refine (TB.sub ha hb).congr (fun w n z => ?_)
    ring
  have h4 : TB (2 * Real.pi) 0 (fun w n _ =>
      Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)
        * ((2880 : ℂ) - 3 * jInvariantFun ((n : ℝ) +ᵥ w))) := by
    have ha : TB (2 * Real.pi) 0 (fun w n _ =>
        (2880 : ℂ) * (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))) :=
      TB.const_mul 2880 hp4
    have hb : TB (2 * Real.pi) 0 (fun w n _ =>
        (3 : ℂ) * (jInvariantFun ((n : ℝ) +ᵥ w) * (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)
          * E8Fun ((n : ℝ) +ᵥ w)))) := TB.const_mul 3 hjp4
    refine (TB.sub ha hb).congr (fun w n z => ?_)
    ring
  refine (TB.neg (TB.add (TB.add (TB.add h1 h2) h3) h4)).congr (fun w n z => ?_)
  simp only [Compact.Mf]
  ring

lemma TB.ktl_br0b (ℓ : Work.Kernels.LogLambdaData) :
    TB (2 * Real.pi) 0 (fun w n z => -Compact.Mf ℓ ((n : ℝ) +ᵥ w)
      + (720 - jInvariantFun ((n : ℝ) +ᵥ w)) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) := by
  have hM : TB (2 * Real.pi) 0 (fun w n z => -Compact.Mf ℓ ((n : ℝ) +ᵥ w)) := TB.ktl_Mf ℓ
  have hN : TB 0 0 (fun w n z => Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) := TB.ktl_Nf ℓ
  have h720 : TB (2 * Real.pi) 0
      (fun w n z => (720 : ℂ) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) :=
    (TB.const_mul 720 hN).mono (by linarith [Real.pi_pos]) (le_refl 0)
  have hjN : TB (2 * Real.pi) 0
      (fun w n z => jInvariantFun ((n : ℝ) +ᵥ w) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) :=
    (TB.mul TB.j hN).mono (by linarith [Real.pi_pos]) (by norm_num)
  refine (TB.add hM (TB.sub h720 hjN)).congr (fun w n z => ?_)
  ring

lemma TB.ktl_dSh (ℓ : Work.Kernels.LogLambdaData) :
    TB (2 * Real.pi) 4 (fun w n z => Work.Asymptotics.kmfd_dSh ((n : ℝ) +ᵥ w) z) := by
  have hA : TB (2 * Real.pi) 4 (fun _ _ z => E4Fun z ^ 3 - Work.Asymptotics.kmfd_E4refc z) :=
    (TB.of_ZC (le_refl 0) (ZC.ktl_E4cref_dev ℓ)).mono (by linarith [Real.pi_pos]) (le_refl 4)
  have hB : TB 0 4 (fun _ _ z => DeltaFun z - Work.Residues.Ept z ^ 2) :=
    TB.of_ZC (le_refl 0) (ZC.ktl_Delta_dev ℓ)
  have hjB : TB (2 * Real.pi) 4
      (fun w n z => jInvariantFun ((n : ℝ) +ᵥ w) * (DeltaFun z - Work.Residues.Ept z ^ 2)) :=
    (TB.mul TB.j hB).mono (a₁ := 2 * Real.pi) (b₁ := 4) (by linarith [Real.pi_pos])
      (by norm_num)
  refine (TB.sub hA hjB).congr (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_dSh]

lemma TB.ktl_dShbr0 (ℓ : Work.Kernels.LogLambdaData) :
    TB Real.pi 1 (fun w n z => Work.Asymptotics.kmfd_dSh ((n : ℝ) +ᵥ w) z
      * Compact.br0 24 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hdSh : TB (2 * Real.pi) 4
      (fun w n z => Work.Asymptotics.kmfd_dSh ((n : ℝ) +ᵥ w) z) := TB.ktl_dSh ℓ
  have hA : TB 0 4 (fun _ _ z => E4Fun z ^ 3 - Work.Asymptotics.kmfd_E4refc z) :=
    TB.of_ZC (le_refl 0) (ZC.ktl_E4cref_dev ℓ)
  have hB : TB 0 4 (fun _ _ z => DeltaFun z - Work.Residues.Ept z ^ 2) :=
    TB.of_ZC (le_refl 0) (ZC.ktl_Delta_dev ℓ)
  have hbr0a : TB 0 (-2)
      (fun w n z => -(Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) * Compact.einv2 z) :=
    (TB.mul ((TB.ktl_Nf ℓ).neg) TB.ktl_einv2).mono (a₁ := 0) (b₁ := -2) (by norm_num)
      (by norm_num)
  have hbr0b : TB (2 * Real.pi) 0 (fun w n z => -Compact.Mf ℓ ((n : ℝ) +ᵥ w)
      + (720 - jInvariantFun ((n : ℝ) +ᵥ w)) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) := TB.ktl_br0b ℓ
  have e1 : TB Real.pi 1 (fun w n z => (E4Fun z ^ 3 - Work.Asymptotics.kmfd_E4refc z)
      * (-(Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) * Compact.einv2 z)) :=
    (TB.mul hA hbr0a).absorb_gen (by norm_num) (by linarith [Real.pi_pos])
  have e2 : TB Real.pi 1 (fun w n z => (E4Fun z ^ 3 - Work.Asymptotics.kmfd_E4refc z)
      * (-Compact.Mf ℓ ((n : ℝ) +ᵥ w)
        + (720 - jInvariantFun ((n : ℝ) +ᵥ w)) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) z)) :=
    (TB.mul hA hbr0b).absorb_gen (by norm_num) (by linarith [Real.pi_pos])
  have e3 : TB Real.pi 1 (fun w n z =>
      (-(jInvariantFun ((n : ℝ) +ᵥ w) * (DeltaFun z - Work.Residues.Ept z ^ 2)))
        * (-(Compact.Nf ℓ ((n : ℝ) +ᵥ w) z) * Compact.einv2 z)) :=
    (TB.mul (TB.mul TB.j hB).neg hbr0a).absorb_gen (by norm_num) (by linarith [Real.pi_pos])
  have e4 : TB Real.pi 1 (fun w n z =>
      (-(jInvariantFun ((n : ℝ) +ᵥ w) * (DeltaFun z - Work.Residues.Ept z ^ 2)))
        * (-Compact.Mf ℓ ((n : ℝ) +ᵥ w)
          + (720 - jInvariantFun ((n : ℝ) +ᵥ w)) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) z)) :=
    (TB.mul (TB.mul TB.j hB).neg hbr0b).absorb_gen (by norm_num) (by linarith [Real.pi_pos])
  refine (TB.add (TB.add e1 e2) (TB.add e3 e4)).congr (fun w n z => ?_)
  rw [Compact.br0_24]
  simp only [Work.Asymptotics.kmfd_dSh]
  ring

lemma TB.ktl_dev (ℓ : Work.Kernels.LogLambdaData) :
    TB Real.pi 1 (fun w n z => Work.Asymptotics.kmfd_dev ℓ ((n : ℝ) +ᵥ w) z) := by
  have hdA : TB 0 3 (fun w n z => Work.Asymptotics.kmfd_dA ℓ ((n : ℝ) +ᵥ w) z) := TB.ktl_dA ℓ
  have hA24 : TB 0 0 (fun w n z => Compact.A24 ℓ ((n : ℝ) +ᵥ w) z) := TB.ktl_A24 ℓ
  have hB24 : TB 0 0 (fun w n z => Compact.B24 ℓ ((n : ℝ) +ᵥ w)) := TB.ktl_B24 ℓ
  have hC24 : TB (2 * Real.pi) 0 (fun w n z => Compact.C24 ℓ ((n : ℝ) +ᵥ w)) := TB.ktl_C24 ℓ
  have h1 : TB Real.pi 1
      (fun w n z => Compact.Dref z * Work.Asymptotics.kmfd_dA ℓ ((n : ℝ) +ᵥ w) z) :=
    (TB.mul_ZCg (le_refl 0) (ZCg.ktl_Dref ℓ) hdA).absorb_gen (by norm_num)
      (by linarith [Real.pi_pos])
  have h2 : TB Real.pi 1
      (fun w n z => Compact.dDelta z * Compact.A24 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TB.mul_ZC (le_refl 0) (ZC.ktl_dDelta ℓ) hA24).absorb_gen (by norm_num)
      (by linarith [Real.pi_pos])
  have h3 : TB Real.pi 1
      (fun w n z => Compact.dW z * Compact.C24 ℓ ((n : ℝ) +ᵥ w)) :=
    (TB.mul_ZC (le_refl 0) (ZC.ktl_dW ℓ) hC24).absorb_gen (by norm_num)
      (by linarith [Real.pi_pos])
  have h4a : TB Real.pi 1 (fun w n z =>
      Compact.dW z * (jInvariantFun ((n : ℝ) +ᵥ w) * Compact.B24 ℓ ((n : ℝ) +ᵥ w))) :=
    (TB.mul_ZC (le_refl 0) (ZC.ktl_dW ℓ) (TB.j.mul hB24)).absorb_gen (by norm_num)
      (by linarith [Real.pi_pos])
  have h4b : TB Real.pi 1 (fun w n z =>
      (Work.Asymptotics.kmfd_jref z * Compact.dW z) * Compact.B24 ℓ ((n : ℝ) +ᵥ w)) :=
    (TB.mul_ZC (le_refl 0) (ZC.ktl_jref_dW ℓ) hB24).absorb_gen (by norm_num)
      (by linarith [Real.pi_pos])
  have h5 : TB Real.pi 1 (fun w n z =>
      ((jInvariantFun z - Work.Asymptotics.kmfd_jref z) * WFun z)
        * Compact.B24 ℓ ((n : ℝ) +ᵥ w)) :=
    (TB.mul_ZC (le_refl 0)
      (((ZC.ktl_jdev ℓ).mul (ZC.ktl_W ℓ)).mono (m' := 0) (n' := 2) (by norm_num) (by norm_num))
      hB24).absorb_gen (by norm_num) (by linarith [Real.pi_pos])
  have h4 : TB Real.pi 1 (fun w n z =>
      Compact.dW z * (jInvariantFun ((n : ℝ) +ᵥ w) * Compact.B24 ℓ ((n : ℝ) +ᵥ w))
        - (Work.Asymptotics.kmfd_jref z * Compact.dW z) * Compact.B24 ℓ ((n : ℝ) +ᵥ w)) :=
    TB.sub h4a h4b
  have h6 : TB Real.pi 1 (fun w n z => Work.Asymptotics.kmfd_dSh ((n : ℝ) +ᵥ w) z
      * Compact.br0 24 ℓ ((n : ℝ) +ᵥ w) z) := TB.ktl_dShbr0 ℓ
  refine (TB.add (TB.sub (TB.add (TB.add h1 h2) (TB.add h3 h4)) h5) h6).congr
    (fun w n z => ?_)
  simp only [Work.Asymptotics.kmfd_dev]
  ring

/-! ## The `d = 24` tile bracket -/

lemma TB.ktl_G24 (ℓ : Work.Kernels.LogLambdaData) :
    TB Real.pi 1 (fun w n z => Compact.brMinus ℓ 24 ((n : ℝ) +ᵥ w) z
      + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 24 ℓ ((n : ℝ) +ᵥ w) z) := by
  have hp1 : TB Real.pi 1 (fun w n z => Work.Residues.Ept z ^ 1
      * Work.Asymptotics.kmfd_c1 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TB.mul_ZC (le_refl 0) (ZC.Ept_pow 1) (TB.ktl_c1 ℓ)).absorb_gen (by push_cast; norm_num)
      (by push_cast; nlinarith [Real.pi_pos])
  have hp2 : TB Real.pi 1 (fun w n z => Work.Residues.Ept z ^ 2
      * Work.Asymptotics.kmfd_c2 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TB.mul_ZC (le_refl 0) (ZC.Ept_pow 2) (TB.ktl_c2 ℓ)).absorb_gen (by push_cast; norm_num)
      (by push_cast; nlinarith [Real.pi_pos])
  have hp3 : TB Real.pi 1 (fun w n z => Work.Residues.Ept z ^ 3
      * Work.Asymptotics.kmfd_c3 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TB.mul_ZC (le_refl 0) (ZC.Ept_pow 3) (TB.ktl_c3 ℓ)).absorb_gen (by push_cast; norm_num)
      (by push_cast; nlinarith [Real.pi_pos])
  have hp4 : TB Real.pi 1 (fun w n z => Work.Residues.Ept z ^ 4
      * Work.Asymptotics.kmfd_c4 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TB.mul_ZC (le_refl 0) (ZC.Ept_pow 4) (TB.ktl_c4 ℓ)).absorb_gen (by push_cast; norm_num)
      (by push_cast; nlinarith [Real.pi_pos])
  have hp5 : TB Real.pi 1 (fun w n z => Work.Residues.Ept z ^ 5
      * Work.Asymptotics.kmfd_c5 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TB.mul_ZC (le_refl 0) (ZC.Ept_pow 5) (TB.ktl_c5 ℓ)).absorb_gen (by push_cast; norm_num)
      (by push_cast; nlinarith [Real.pi_pos])
  have hp6 : TB Real.pi 1 (fun w n z => Work.Residues.Ept z ^ 6
      * Work.Asymptotics.kmfd_c6 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TB.mul_ZC (le_refl 0) (ZC.Ept_pow 6) (TB.ktl_c6 ℓ)).absorb_gen (by push_cast; norm_num)
      (by push_cast; nlinarith [Real.pi_pos])
  have hp7 : TB Real.pi 1 (fun w n z => Work.Residues.Ept z ^ 7
      * Work.Asymptotics.kmfd_c7 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TB.mul_ZC (le_refl 0) (ZC.Ept_pow 7) (TB.ktl_c7 ℓ)).absorb_gen (by push_cast; norm_num)
      (by push_cast; nlinarith [Real.pi_pos])
  have hp8 : TB Real.pi 1 (fun w n z => Work.Residues.Ept z ^ 8
      * Work.Asymptotics.kmfd_c8 ℓ ((n : ℝ) +ᵥ w) z) :=
    (TB.mul_ZC (le_refl 0) (ZC.Ept_pow 8) (TB.ktl_c8 ℓ)).absorb_gen (by push_cast; norm_num)
      (by push_cast; nlinarith [Real.pi_pos])
  have hBR : TB Real.pi 1 (fun w n z => Work.Asymptotics.kmfd_BR ℓ ((n : ℝ) +ᵥ w) z) := by
    refine (TB.add (TB.add (TB.add (TB.add (TB.add (TB.add (TB.add hp1 hp2) hp3) hp4)
      hp5) hp6) hp7) hp8).congr (fun w n z => ?_)
    simp only [Work.Asymptotics.kmfd_BR_expansion]
    ring
  refine (TB.add hBR (TB.ktl_dev ℓ)).congr (fun w n z => ?_)
  rw [Work.Asymptotics.kmfd_bracket_decomp]


/-! ## The target -/

/-- **The `K_-` half of the sharp cusp-`i∞` tail on the cusp-`±1` tiles.** -/
theorem KMinusTileTail (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    TB Real.pi 1
      (fun (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) =>
        Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z) := by
  have hG : TB Real.pi 1 (fun w n z => Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
      + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z) := by
    rcases hd with rfl | rfl
    · exact TB.ktl_G8 ℓ
    · exact TB.ktl_G24 ℓ
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hG
  refine ⟨(3456 * Real.pi)⁻¹ * 16 * C, N, M, by positivity, hN, hM, ?_⟩
  intro w n z t hn hw hz ht
  have hjv : jInvariantFun ((n : ℝ) +ᵥ w) = jInvariantFun w := ktl_jInvariantFun_vadd_int n hn w
  have hSheq : Compact.Sh ((n : ℝ) +ᵥ w) z = Compact.Sh w z := by
    simp only [Compact.Sh, hjv]
  have hge := Work.Asymptotics.EtailE.E_Sh_ge hw ht hz
  have hSne : Compact.Sh ((n : ℝ) +ᵥ w) z ≠ 0 := by
    intro h0
    rw [hSheq] at h0
    rw [h0, norm_zero] at hge
    norm_num at hge
  have hid := Compact.tail_identity ℓ d hd ((n : ℝ) +ᵥ w) z hSne
  have hinv : ‖(Compact.Sh ((n : ℝ) +ᵥ w) z)⁻¹‖ ≤ 16 := by
    rw [hSheq]; exact Work.Asymptotics.EtailE.E_Sh_inv_bound hw ht hz
  have hbr : ‖Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
      + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z‖
      ≤ C * (scale w) ^ N * (1 + t) ^ M
          * Real.exp (Real.pi * (ModularGroup.S • w).im - 1 * Real.pi * t) :=
    hb w n z t hn hw hz ht
  have hnorm : ‖((3456 : ℂ) * (Real.pi : ℂ)) * (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
        - Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z)‖
      = ‖(Compact.Sh ((n : ℝ) +ᵥ w) z)⁻¹ * (Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
          + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z)‖ := by
    rw [hid, norm_neg]
  have hconst : ‖((3456 : ℂ) * (Real.pi : ℂ))‖ = 3456 * Real.pi := by
    rw [norm_mul, show ‖(3456 : ℂ)‖ = 3456 by norm_num, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hkey : ((3456 : ℝ) * Real.pi) * ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
        - Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖
      ≤ 16 * (C * (scale w) ^ N * (1 + t) ^ M
          * Real.exp (Real.pi * (ModularGroup.S • w).im - 1 * Real.pi * t)) := by
    have h1 : ‖(Compact.Sh ((n : ℝ) +ᵥ w) z)⁻¹ * (Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
            + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z)‖
        = ((3456 : ℝ) * Real.pi) * ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
            - Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖ := by
      rw [← hnorm, norm_mul, hconst]
    rw [← h1]
    calc ‖(Compact.Sh ((n : ℝ) +ᵥ w) z)⁻¹ * (Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
            + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z)‖
        ≤ ‖(Compact.Sh ((n : ℝ) +ᵥ w) z)⁻¹‖
          * ‖Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
            + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z‖ := norm_mul_le _ _
      _ ≤ 16 * ‖Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) z
            + Compact.Sh ((n : ℝ) +ᵥ w) z * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) z‖ :=
          mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
      _ ≤ 16 * (C * (scale w) ^ N * (1 + t) ^ M
            * Real.exp (Real.pi * (ModularGroup.S • w).im - 1 * Real.pi * t)) :=
          mul_le_mul_of_nonneg_left hbr (by norm_num)
  calc ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
        - Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖
      = ((3456 * Real.pi)⁻¹) * (((3456 : ℝ) * Real.pi)
          * ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) z
            - Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) z‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    _ ≤ ((3456 * Real.pi)⁻¹) * (16 * (C * (scale w) ^ N * (1 + t) ^ M
          * Real.exp (Real.pi * (ModularGroup.S • w).im - 1 * Real.pi * t))) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = ((3456 * Real.pi)⁻¹ * 16 * C) * (scale w) ^ N * (1 + t) ^ M
          * Real.exp (Real.pi * (ModularGroup.S • w).im - 1 * Real.pi * t) := by ring

end

end Work.Asymptotics.Tile
