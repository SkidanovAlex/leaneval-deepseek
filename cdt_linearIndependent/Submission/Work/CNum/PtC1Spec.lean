import Mathlib
import Submission.Work.CNum.CpxSound
import Submission.Work.CNum.NrmSpec
import Submission.Work.CNum.ExpISpec
import Submission.Work.CNum.CsOfSpec
import Submission.Work.CNum.MemIvS
import Submission.Work.CNum.IvMSpec
import Submission.Work.CNum.exp_phi_eq
import Submission.Work.CNum.Wfun_exp
import Submission.Work.CNum.AlpBound

/-!
# `Work.CNum.PtC1Spec` — soundness of the point table `ptC1` on the first arc

`ptC1 k = (3/4) · W1 k 1` is the mantissa-level interval enclosure of the boundary value
`ψ_C(e^{iθ_k})`, `θ_k = 2πk/1024`, on the first arc `(-α, α)` of the unit circle (`k ≤ 244`).

The mathematical content is entirely in `Wfun_exp`: for `θ ∈ (-α, α)`,

`Wfun (e^{iθ}) = -((P(θ) + i Q(θ)) e^{iθ/2})/d`,  `P = √(2A(cos θ - γ))`, `Q = 2(1+c²) sin(θ/2)`,

and `ψ_C = (3/4)·Wfun` (`lune (23/10) = -Wfun`).  The interval computation `W1` evaluates
`cos θ = cos²(θ/2) - sin²(θ/2)` from the table `expI k ∋ e^{iθ_k/2}`, then takes the outward
interval square root `IvS` of `2A(cos θ - γ)` and the product with `1/d = 50/429`.

The two *numerical* side conditions of `MemIvS` (nonnegativity of the lower endpoint of
`X k = 2A(cos θ_k - γ)` and the binary-search range bound) are finite computations on `k ≤ 244`;
they are verified in one kernel evaluation of the `Bool`-valued test `sideOK` over `List.range 245`.
-/

namespace Work.CNum

open Work.ANum

/-! ## The interval `X k` and the finite side conditions -/

/-- The interval `2A·(cos θ_k - γ)` of `W1`. -/
private def Xk (k : ℕ) : Iv :=
  IvM (ratIv 791282 10000)
    (Iv.sub (Iv.sub (Iv.sq (expI k).re) (Iv.sq (expI k).im)) (ratIv 27559 395641))

/-- The two side conditions of `MemIvS` for `Xk k`, as a kernel-checkable `Bool` test. -/
private def sideOK (k : ℕ) : Bool :=
  decide ((0 : ℤ) ≤ (Xk k).lo) && decide ((Xk k).hi.toNat * SC.toNat < 2 ^ 70)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
private lemma sideOK_all : (List.range 245).all sideOK = true := by decide

/-! ## Algebraic reductions -/

/-- The paper's `lune c` is `-Wfun` (at `c = cR`): both numerators are
`(1+c²)(z-1) + √((1+c²)²(1+z)² - 16c²z)` and both denominators are `2(c²-1) = d`. -/
private lemma lune_eq_neg_Wfun (z : ℂ) : Submission.CDTPlan.lune (23 / 10) z = -Wfun z := by
  simp only [Submission.CDTPlan.lune, Wfun, Ra, Complex.sqrt, cR, AR, BR, dR]
  push_cast
  ring_nf

private lemma psiC_eq (z : ℂ) : Submission.CDTPlan.psiC z = ((3 / 4 : ℝ) : ℂ) * Wfun z := by
  rw [Submission.CDTPlan.psiC, lune_eq_neg_Wfun]
  push_cast
  ring

/-- `Wfun_exp` with the reciprocal `1/d = 50/429` in place of the division. -/
private lemma Wfun_exp_div {θ : ℝ} (h : θ ∈ Set.Ioo (-alpR) alpR) :
    Wfun (Complex.exp (Complex.I * (θ : ℂ))) =
      -(((PR θ : ℂ) + Complex.I * (QR θ : ℂ)) * ((1 / dR : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))) := by
  have hd : dR = 429 / 50 := by rw [dR, cR]; norm_num
  have hd' : (dR : ℂ) ≠ 0 := by rw [hd]; norm_num
  rw [Wfun_exp h]
  rw [show ((1 / dR : ℝ) : ℂ) = 1 / (dR : ℂ) by push_cast; ring]
  field_simp

/-! ## The main interval assembly -/

private theorem PtC1_aux (k : ℕ) (hk : k ≤ 244)
    (hlo : (0 : ℤ) ≤ (Xk k).lo) (hhi : (Xk k).hi.toNat * SC.toNat < 2 ^ 70) :
    Cpx.Mem (ptC1 k)
      (Submission.CDTPlan.psiC
        (Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (k : ℂ) / 1024)))) := by
  set θ : ℝ := 2 * Real.pi * (k : ℝ) / 1024 with hθdef
  have hkR : (k : ℝ) ≤ 244 := by exact_mod_cast hk
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  -- the angle lies on the first arc
  have hθmem : θ ∈ Set.Ioo (-alpR) alpR := by
    have halp := AlpBound
    constructor
    · have h2 : (0 : ℝ) ≤ θ := by rw [hθdef]; positivity
      linarith [halp.1]
    · have h3 : θ ≤ 61 * Real.pi / 128 := by
        rw [hθdef]
        nlinarith [hpi0, hkR]
      have h4 : 61 * Real.pi / 128 < 1.4973 := by
        nlinarith [Real.pi_lt_d6, hpi0]
      linarith [halp.1]
  -- the analytic value of `Wfun` on the arc
  have hW := Wfun_exp_div hθmem
  -- the table entry `expI k` encloses `e^{iθ/2}`
  have hE0 := ExpISpec (k := k) (by omega : k ≤ 1024)
  have harg : (k : ℂ) * (Real.pi : ℂ) / 1024 = ((θ / 2 : ℝ) : ℂ) := by
    rw [hθdef]; push_cast; ring
  have hE : Cpx.Mem (expI k) (Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))) := by
    simpa only [harg] using hE0
  have hEr : (expI k).re.Mem (Real.cos (θ / 2)) ∧ (expI k).im.Mem (Real.sin (θ / 2)) := by
    have h' : Cpx.Mem (expI k)
        ((↑(Real.cos (θ / 2)) : ℂ) + (↑(Real.sin (θ / 2)) : ℂ) * Complex.I) := by
      have h := hE
      rw [show Complex.I * ((θ / 2 : ℝ) : ℂ) = (((θ / 2 : ℝ)) : ℂ) * Complex.I by ring] at h
      rwa [Complex.exp_ofReal_mul_I] at h
    have hre : ((↑(Real.cos (θ / 2)) : ℂ)
        + (↑(Real.sin (θ / 2)) : ℂ) * Complex.I).re = Real.cos (θ / 2) := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    have him : ((↑(Real.cos (θ / 2)) : ℂ)
        + (↑(Real.sin (θ / 2)) : ℂ) * Complex.I).im = Real.sin (θ / 2) := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
    exact ⟨hre ▸ h'.1, him ▸ h'.2⟩
  -- `cos θ` from the half-angle
  have hcos : (Iv.sub (Iv.sq (expI k).re) (Iv.sq (expI k).im)).Mem (Real.cos θ) := by
    have h1 := Iv.mem_sub (Iv.mem_sq hEr.1) (Iv.mem_sq hEr.2)
    have key : Real.cos θ
        = Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2) := by
      have h := Real.cos_two_mul' (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at h
      rw [h]; ring
    rwa [← key] at h1
  -- `2A(cos θ - γ)` in `Xk k`
  have hX : (Xk k).Mem (2 * AR * (Real.cos θ - gamR)) := by
    have ha : (ratIv 791282 10000).Mem ((791282 : ℝ) / 10000) := RatIvSpec (by norm_num)
    have ha2 : (2 : ℝ) * AR = 791282 / 10000 := by norm_num [AR, cR]
    have ha' : (ratIv 791282 10000).Mem (2 * AR) := by rw [ha2]; exact ha
    have hc0 : (ratIv 27559 395641).Mem ((27559 : ℝ) / 395641) := RatIvSpec (by norm_num)
    have hc : (ratIv 27559 395641).Mem gamR := by
      rw [gamR_eq_rat]; exact hc0
    exact IvMSpec ha' (Iv.mem_sub hcos hc)
  -- the square root `P(θ) = √(2A(cos θ - γ))`
  have hP : (IvS (Xk k)).Mem (PR θ) := by
    have h0 : 0 ≤ m2r (Xk k).lo := div_nonneg (by exact_mod_cast hlo) SC_posR.le
    exact MemIvS hX h0 hhi
  -- `Q(θ) = 2(1+c²) sin(θ/2)`
  have hQ : (IvM (ratIv 629 50) (expI k).im).Mem (QR θ) := by
    have hq : (ratIv 629 50).Mem ((629 : ℝ) / 50) := RatIvSpec (by norm_num)
    have hq2 : (2 : ℝ) * (1 + cR ^ 2) = 629 / 50 := by norm_num [cR]
    have hq' : (ratIv 629 50).Mem (2 * (1 + cR ^ 2)) := by rw [hq2]; exact hq
    exact IvMSpec hq' hEr.2
  -- `1/d = 50/429`
  have hd : (ratIv 50 429).Mem (1 / dR) := by
    have hd0 : (ratIv 50 429).Mem ((50 : ℝ) / 429) := RatIvSpec (by norm_num)
    have h2 : (50 : ℝ) / 429 = 1 / dR := by
      have : dR = 429 / 50 := by rw [dR, cR]; norm_num
      rw [this]; norm_num
    rwa [h2] at hd0
  -- the product `(P + iQ)/d`
  have hI : (⟨IvS (Xk k), IvM (ratIv 629 50) (expI k).im⟩ : Cpx).Mem
      ((PR θ : ℂ) + Complex.I * (QR θ : ℂ)) := by
    exact ⟨by simpa using hP, by simpa using hQ⟩
  have hinner : (Cpx.mulr ⟨IvS (Xk k), IvM (ratIv 629 50) (expI k).im⟩ (ratIv 50 429)).Mem
      ((PR θ + Complex.I * (QR θ)) * ((1 / dR : ℝ) : ℂ)) :=
    mem_mulr hI hd
  -- multiply by `e^{iθ/2}` and negate
  have houter : (Cpx.mul
      (Cpx.mulr ⟨IvS (Xk k), IvM (ratIv 629 50) (expI k).im⟩ (ratIv 50 429))
        (expI k)).Mem
      (((PR θ + Complex.I * (QR θ)) * ((1 / dR : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))) := mem_mul hinner hE
  have hneg := mem_neg houter
  have hW1 : (W1 k 1).Mem (Wfun (Complex.exp (Complex.I * (θ : ℂ)))) := by
    rw [hW]
    rw [show W1 k 1 = Cpx.neg (Cpx.mul
      (Cpx.mulr ⟨IvS (Xk k), IvM (ratIv 629 50) (expI k).im⟩ (ratIv 50 429))
        (expI k)) from rfl]
    exact hneg
  -- the final multiplication by `3/4`
  have h34 : (ratIv 3 4).Mem ((3 : ℝ) / 4) := RatIvSpec (by norm_num)
  have hpt : (ptC1 k).Mem ((Wfun (Complex.exp (Complex.I * (θ : ℂ)))) * ((3 / 4 : ℝ) : ℂ)) := by
    rw [show ptC1 k = Cpx.mulr (W1 k 1) (ratIv 3 4) from rfl]
    exact mem_mulr hW1 h34
  rw [show (2 * (Real.pi : ℂ) * (k : ℂ) / 1024) = ((θ : ℝ) : ℂ) by
    rw [hθdef]; push_cast; ring]
  rw [psiC_eq]
  convert hpt using 1
  ring

theorem PtC1Spec {k : ℕ} (hk : k ≤ 244) : Work.CNum.Cpx.Mem (Work.CNum.ptC1 k) (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (2 * (Real.pi : ℂ) * (k : ℂ) / 1024)))) := by
  have hmem : k ∈ List.range 245 := List.mem_range.mpr (by omega)
  have hk' : sideOK k = true := (List.all_eq_true.mp sideOK_all) k hmem
  rw [sideOK, Bool.and_eq_true] at hk'
  exact PtC1_aux k hk (of_decide_eq_true hk'.1) (of_decide_eq_true hk'.2)

end Work.CNum
