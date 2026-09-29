import Mathlib
import Submission.Work.CNum.CpxSound
import Submission.Work.CNum.NrmSpec
import Submission.Work.CNum.ExpISpec
import Submission.Work.CNum.CsOfSpec
import Submission.Work.CNum.MemIvS
import Submission.Work.CNum.IvMSpec
import Submission.Work.CNum.C2_mem
import Submission.Work.CNum.C2_clockwise
import Submission.Work.CNum.AlpBound
import Submission.Work.CNum.C2_setup
import Submission.Work.CNum.C2_sqrt_Ra
import Submission.Work.CNum.C2_T_eq
import Submission.Work.CNum.exp_phi_eq
import Submission.Work.CNum.PtC2YBound

/-!
# `Work.CNum.PtC2Spec` — the certified boundary point `ψ_C(e^{2πik/1024})` on the cusp arc

For `245 ≤ k ≤ 779` (the second, "large" arc `(α, 2π-α)` of the unit circle, subdivided at the
`1024`-th roots of unity), the fixed-point rectangle `ptC2 k` of `Work.CNum.Fx` contains the exact
boundary value `ψ_C(e^{2πik/1024})`.

Everything is explicit.  Writing `a = kπ/1024`, `θ = 2a = 2πk/1024` and

* `C2T θ = √(2A(γ - cos θ))` (the modulus of the principal square root of `Ra(e^{iθ})`, which is
  `-i·C2T θ·e^{iθ/2}` on the cusp arc, `C2_sqrt_Ra`),
* `QR θ = 2(1+c²) sin(θ/2)`,

the analytic input is the closed form

`ψ_C(e^{iθ}) = (3/4)·W(e^{iθ}) = i·(C2T θ - QR θ)·e^{iθ/2}/dR`, `dR = 2(c²-1) = 429/50`,

and the certificate is the interval-arithmetic chain

`expI k ∋ e^{ia}` ⟶ `cosT ∋ cos θ` ⟶ `Y ∋ 2A(γ-cos θ)` ⟶ `P = IvS Y ∋ C2T θ`,
`Q = (629/50)·(expI k).im ∋ QR θ` ⟶ `i(P-Q)·(expI k) ∋ i(C2T θ - QR θ)e^{ia}`
⟶ `·(50/429)·(3/4)`.

The only non-symbolic input is the mantissa bound `Y.hi·SC < 2^70` needed for `IvS`, which is the
kernel-checked integer certificate `PtC2YBound`; the sharpness of `IvS`'s lower endpoint (i.e.
`Y.lo ≥ 0`) is bypassed by clamping with `Iv.nonneg`, which leaves `IvS` unchanged.
-/

namespace Work.CNum

open Work.ANum

/-! ## Elementary scalars -/

/-- `ψ_C = (3/4)·W`, since `Complex.sqrt = (·)^{1/2}` definitionally. -/
private lemma psiCEq (z : ℂ) : Submission.CDTPlan.psiC z = (3 / 4) * Wfun z := by
  unfold Submission.CDTPlan.psiC Submission.CDTPlan.lune Wfun Ra AR BR dR cR
  rw [Complex.sqrt]
  push_cast
  ring_nf

/-- `(max a 0).toNat = a.toNat`, so that `Iv.nonneg` does not change `IvS`. -/
private lemma toNat_max_zero (a : ℤ) : (max a 0).toNat = a.toNat := by
  rcases le_or_gt (0 : ℤ) a with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right (le_of_lt h), Int.toNat_of_nonpos (le_of_lt h)]
    simp

/-- Clamping an interval to nonnegative values does not change `IvS`. -/
private lemma IvS_nonneg (I : Iv) : IvS (Iv.nonneg I) = IvS I := by
  have h : (max I.lo 0).toNat = I.lo.toNat := toNat_max_zero I.lo
  simp only [IvS, sqrtLo, sqrtHi, Iv.nonneg]
  rw [h]

/-! ## The location of the arc -/

/-- `α < 245·π/512`; this is what puts the grid points `kπ/512`, `245 ≤ k ≤ 779`, inside the
cusp arc `(α, 2π - α)`. -/
private lemma alpLt245 : alpR < 245 * Real.pi / 512 := by
  have h := AlpBound.2
  have hp := Real.pi_gt_d4
  linarith

/-- `kπ/512 ∈ (α, 2π - α)` for `245 ≤ k ≤ 779`. -/
private lemma arc_mem {k : ℕ} (h1 : 245 ≤ k) (h2 : k ≤ 779) :
    (k : ℝ) * Real.pi / 512 ∈ Set.Ioo alpR (2 * Real.pi - alpR) := by
  have hk1 : (245 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
  have hk2 : (k : ℝ) ≤ 779 := by exact_mod_cast h2
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  constructor
  · have h : (245 : ℝ) * Real.pi / 512 ≤ (k : ℝ) * Real.pi / 512 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      nlinarith
    linarith [alpLt245]
  · have h : (k : ℝ) * Real.pi / 512 ≤ (779 : ℝ) * Real.pi / 512 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      nlinarith
    have h779 : (779 : ℝ) * Real.pi / 512 = 2 * Real.pi - 245 * Real.pi / 512 := by ring
    linarith [alpLt245]

/-! ## The value of `W` on the cusp arc -/

/-- On the cusp arc `(α, 2π - α)` the principal square root of the radicand is
`-i·C2T θ·e^{iθ/2}`, so that

`W(e^{iθ}) = i·(C2T θ - QR θ)·e^{iθ/2}/dR`. -/
private lemma Wfun_arc {θ : ℝ} (h : θ ∈ Set.Ioo alpR (2 * Real.pi - alpR)) :
    Wfun (Complex.exp (Complex.I * (θ : ℂ))) =
      Complex.I * (((C2T θ - QR θ : ℝ)) : ℂ) *
        Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) / ((dR : ℂ)) := by
  have h1 : Complex.sqrt (Ra (Complex.exp (Complex.I * (θ : ℂ)))) =
      -(Complex.I * (C2T θ : ℂ)) * Complex.exp (Complex.I * ((θ/2 : ℝ) : ℂ)) := by
    have hh := C2_sqrt_Ra h
    rwa [show ((θ : ℂ)) / 2 = ((θ/2 : ℝ) : ℂ) by push_cast; ring] at hh
  have h2 : Complex.exp (Complex.I * (θ : ℂ)) - 1 =
      2 * Complex.I * (Real.sin (θ/2) : ℂ) * Complex.exp (Complex.I * ((θ/2 : ℝ) : ℂ)) :=
    ExpPhi.exp_I_sub_one θ
  have hfac : (1 + (cR : ℂ) ^ 2) * (2 * Complex.I * (Real.sin (θ/2) : ℂ) *
        Complex.exp (Complex.I * ((θ/2 : ℝ) : ℂ))) +
      (-(Complex.I * (C2T θ : ℂ))) * Complex.exp (Complex.I * ((θ/2 : ℝ) : ℂ)) =
      Complex.I * (((QR θ - C2T θ : ℝ)) : ℂ) * Complex.exp (Complex.I * ((θ/2 : ℝ) : ℂ)) := by
    rw [show (((QR θ - C2T θ : ℝ)) : ℂ) = (QR θ : ℂ) - (C2T θ : ℂ) by push_cast; ring]
    rw [show (QR θ : ℂ) = 2 * (1 + (cR : ℂ) ^ 2) * (Real.sin (θ/2) : ℂ) by
      rw [QR]; push_cast; ring]
    ring
  rw [Wfun, h2, h1, hfac]
  rw [show (((QR θ - C2T θ : ℝ)) : ℂ) = -(((C2T θ - QR θ : ℝ)) : ℂ) by push_cast; ring]
  rw [div_eq_mul_inv]
  ring

/-! ## The certificate -/

theorem PtC2Spec {k : ℕ} (h1 : 245 ≤ k) (h2 : k ≤ 779) : Work.CNum.Cpx.Mem (Work.CNum.ptC2 k) (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (k : ℂ) / 1024)))) := by
  have hk1024 : k ≤ 1024 := by omega
  set a : ℝ := (k : ℝ) * Real.pi / 1024 with hadef
  have h2a : 2 * a = (k : ℝ) * Real.pi / 512 := by rw [hadef]; ring
  have harc : 2 * a ∈ Set.Ioo alpR (2 * Real.pi - alpR) := by
    rw [h2a]; exact arc_mem h1 h2
  -- the grid point
  have hEa : (expI k).Mem (Complex.exp (Complex.I * ((a : ℝ) : ℂ))) := by
    have hE0 := ExpISpec (k := k) hk1024
    have harg : Complex.exp (Complex.I * ((k : ℂ) * ↑Real.pi / 1024)) =
        Complex.exp (Complex.I * ((a : ℝ) : ℂ)) := by
      congr 1; rw [hadef]; push_cast; ring
    rwa [harg] at hE0
  have hEre : (expI k).re.Mem (Real.cos a) := by
    have h := hEa.1
    rwa [show Complex.I * ((a : ℝ) : ℂ) = ((a : ℝ) : ℂ) * Complex.I by ring,
      Complex.exp_ofReal_mul_I_re] at h
  have hEim : (expI k).im.Mem (Real.sin a) := by
    have h := hEa.2
    rwa [show Complex.I * ((a : ℝ) : ℂ) = ((a : ℝ) : ℂ) * Complex.I by ring,
      Complex.exp_ofReal_mul_I_im] at h
  -- `cosT ∋ cos θ`
  have hcosT : (Iv.sub (Iv.sq (expI k).re) (Iv.sq (expI k).im)).Mem (Real.cos (2*a)) := by
    have h := Iv.mem_sub (Iv.mem_sq hEre) (Iv.mem_sq hEim)
    rwa [show Real.cos a * Real.cos a - Real.sin a * Real.sin a = Real.cos (2*a) by
      rw [Real.cos_two_mul']; ring] at h
  -- `Y ∋ 2A(γ - cos θ)`
  have hA : (ratIv 791282 10000).Mem (2 * AR) := by
    have h := RatIvSpec (p := 791282) (q := 10000) (by norm_num)
    convert h using 1
    norm_num [AR, cR]
  have hB : (ratIv 27559 395641).Mem gamR := by
    have h := RatIvSpec (p := 27559) (q := 395641) (by norm_num)
    convert h using 1
    rw [gamR_eq_rat]; norm_num
  have hY : (ptC2Y k).Mem (2 * AR * (gamR - Real.cos (2*a))) :=
    IvMSpec hA (Iv.mem_sub hB hcosT)
  have hcg : Real.cos (2*a) < gamR := cos_lt_gamR harc
  have hvnn : 0 ≤ 2 * AR * (gamR - Real.cos (2*a)) := by
    have hAR : 0 < AR := by norm_num [AR, cR]
    nlinarith
  -- `P = IvS Y ∋ C2T θ`
  have hP : (IvS (ptC2Y k)).Mem (C2T (2*a)) := by
    have hb : ((Iv.nonneg (ptC2Y k)).hi).toNat * SC.toNat < 2^70 := by
      show (ptC2Y k).hi.toNat * SC.toNat < 2^70
      exact PtC2YBound h1 h2
    have h := MemIvS (Iv.mem_nonneg hY hvnn) (Iv.nonneg_lo_nonneg (ptC2Y k)) hb
    rw [IvS_nonneg (ptC2Y k)] at h
    exact h
  -- `Q ∋ QR θ`
  have hQ : (IvM (ratIv 629 50) (expI k).im).Mem (QR (2*a)) := by
    have h1' : (ratIv 629 50).Mem (2 * (1 + cR^2)) := by
      have h := RatIvSpec (p := 629) (q := 50) (by norm_num)
      convert h using 1
      norm_num [cR]
    have h := IvMSpec h1' hEim
    convert h using 1
    rw [QR, show (2*a)/2 = a by ring]
  -- the complex factor `i·(C2T θ - QR θ)`
  have hZ : (⟨⟨(0 : ℤ), 0⟩, Iv.sub (IvS (ptC2Y k)) (IvM (ratIv 629 50) (expI k).im)⟩ : Cpx).Mem
      (Complex.I * (((C2T (2*a) - QR (2*a) : ℝ)) : ℂ)) := by
    have hPQ := Iv.mem_sub hP hQ
    refine ⟨?_, ?_⟩
    · simp [Iv.Mem, m2r]
    · simpa [Complex.mul_im] using hPQ
  have hinner : (Cpx.mul ⟨⟨(0 : ℤ), 0⟩, Iv.sub (IvS (ptC2Y k)) (IvM (ratIv 629 50) (expI k).im)⟩
      (expI k)).Mem
      (Complex.I * (((C2T (2*a) - QR (2*a) : ℝ)) : ℂ) *
        Complex.exp (Complex.I * ((a : ℝ) : ℂ))) :=
    mem_mul hZ hEa
  have hstep1 := mem_mulr hinner (RatIvSpec (p := 50) (q := 429) (by norm_num))
  have hstep2 := mem_mulr hstep1 (RatIvSpec (p := 3) (q := 4) (by norm_num))
  simp only [Int.cast_ofNat, Nat.cast_ofNat] at hstep2
  -- the exact value
  have hval : Submission.CDTPlan.psiC (Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (k : ℂ) / 1024)))
      = ((Complex.I * (((C2T (2*a) - QR (2*a) : ℝ)) : ℂ) *
            Complex.exp (Complex.I * ((a : ℝ) : ℂ))) * (((50 : ℝ)/429 : ℝ) : ℂ)) *
          (((3 : ℝ)/4 : ℝ) : ℂ) := by
    have harg : (2 * (Real.pi : ℂ) * (k : ℂ) / 1024 : ℂ) = ((2*a : ℝ) : ℂ) := by
      rw [hadef]; push_cast; ring
    have h2a' : (2*a)/2 = a := by ring
    have hd : dR = (429 : ℝ)/50 := by norm_num [dR, cR]
    rw [harg, psiCEq, Wfun_arc harc, h2a', hd]
    have hdiv : ∀ X : ℂ, X / (((429 : ℝ)/50 : ℝ) : ℂ) = X * (((50 : ℝ)/429 : ℝ) : ℂ) := by
      intro X
      rw [show X / (((429 : ℝ)/50 : ℝ) : ℂ) = X * ((((429 : ℝ)/50 : ℝ) : ℂ))⁻¹ from rfl]
      rw [show ((((429 : ℝ)/50 : ℝ) : ℂ))⁻¹ = (((50 : ℝ)/429 : ℝ) : ℂ) by norm_num]
    rw [hdiv]
    push_cast
    ring
  rw [hval]
  exact hstep2

end Work.CNum
