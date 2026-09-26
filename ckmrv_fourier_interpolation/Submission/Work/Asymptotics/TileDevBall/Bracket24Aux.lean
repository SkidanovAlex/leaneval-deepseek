/-
# Auxiliary calculus and atoms for the `d = 24` tile bracket bound

This file collects the `BBdd`-calculus additions and the atom bounds used by
`Submission/Work/Asymptotics/TileDevBall/bracket24Ball.lean`, whose target is

  `‖brMinus ℓ 24 τ ζ + Sh τ ζ · br0 24 ℓ τ ζ‖ ≤ C (scale w)^N`

for `w ∈ E = KEpsilon`, `n = ±1`, `τ = n +ᵥ w` and `ζ` in the ball `‖ζ - S • w‖ ≤ 29/20`
with `3 ≤ Im ζ`.

The calculus `BBdd c d F` (of `TileDevBall/BallShape.lean`) records the bound

  `‖F w ζ‖ ≤ C (scale w)^N e^{c Im (S • w)} e^{d Im ζ}`

on the ball.  The `τ`-atoms at `τ = n +ᵥ w` carry a factor `e^{2π Im (S • w)}` (the `j`-atoms),
the `ζ`-atoms a factor `e^{-kπ Im ζ}`; the ball inequality `Im ζ ≥ Im (S • w) - 29/20`
(`Ball.im_ge`) makes a *pair* `(c, d)` with `c + d ≤ 0` uniformly bounded.  The main addition
here is therefore

* `BBdd.toGood` : `BBdd c d F → c + d ≤ 0 → BBdd 0 0 F`,

the "collapse" of the two exponential weights, together with the `ζ`-atom converters
`BBddOfEptpow`, `BBddOfEptinv2`, `BBddOfZAtom`, `BBddOfZAtom0` and the atom inventory
(`tDB`, `tP2E10B`, `tP4E8B`, `tPSB`, `tjDB`, `zEptB`, …).

Every atom here is proved from the workspace's existing `Bdd`/`BBdd` bounds
(`EtailE/Atoms.lean`, `tile_Bdd_atoms.lean`, `KMFDZDevs.lean`, `Tile/psi_combo_small.lean`).
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.KMFDDefs
import Submission.Work.Asymptotics.KMFDZDevs
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.tile_Bdd_atoms
import Submission.Work.Asymptotics.Tile.psi_combo_small
import Submission.Work.Asymptotics.TileDevBall.BallShape
import Submission.Work.Asymptotics.TileDevBall.BallAtoms
import Submission.Work.Asymptotics.TileDevBall.kplusDev8Ball

set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics.TileDevBall

open Work.Kernels
open Work.Asymptotics.EtailE (Bdd)
open Work.Residues (Ept)

/-! ## §1  Geometry of the ball and the collapse of the two weights -/

/-- Ball geometry: `|Im ζ - Im (S • w)| ≤ 29/20`. -/
lemma ball_im_sub_le {w ζ : ℍ} (h : Ball w ζ) :
    |ζ.im - (ModularGroup.S • w).im| ≤ 29 / 20 := by
  have h2 : |ζ.im - (ModularGroup.S • w).im|
      ≤ ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ := by
    have h3 := Complex.abs_im_le_norm ((ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ))
    rwa [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im] at h3
  exact le_trans h2 h.hball

/-- **Collapse of the two exponential weights.**  Since `|Im ζ - Im (S • w)| ≤ 29/20` on the
ball, a `BBdd c d` bound gives `e^{c Im(S•w)} e^{d Im ζ} ≤ e^{|d|·29/20} e^{(c+d) Im(S•w)}`, so
`BBdd c d F → BBdd (c+d) 0 F`. -/
lemma BBddShift {c d : ℝ} {F : ℍ → ℍ → ℂ} (h : BBdd c d F) : BBdd (c + d) 0 F := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C * Real.exp (|d| * (29 / 20)) + 1, N, by positivity, hN, fun w ζ hw => ?_⟩
  have h1 := hb w ζ hw
  have hdist : |ζ.im - (ModularGroup.S • w).im| ≤ 29 / 20 := ball_im_sub_le hw
  have h4 : d * ζ.im ≤ d * (ModularGroup.S • w).im + |d| * (29 / 20) := by
    have h5 : d * (ζ.im - (ModularGroup.S • w).im) ≤ |d| * (29 / 20) := by
      calc d * (ζ.im - (ModularGroup.S • w).im)
          ≤ |d * (ζ.im - (ModularGroup.S • w).im)| := le_abs_self _
        _ = |d| * |ζ.im - (ModularGroup.S • w).im| := abs_mul d _
        _ ≤ |d| * (29 / 20) := mul_le_mul_of_nonneg_left hdist (abs_nonneg d)
    linarith
  have h6 : Real.exp (d * ζ.im)
      ≤ Real.exp (d * (ModularGroup.S • w).im) * Real.exp (|d| * (29 / 20)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr h4
  have h7 : Real.exp (c * (ModularGroup.S • w).im) * Real.exp (d * ζ.im)
      ≤ Real.exp ((c + d) * (ModularGroup.S • w).im) * Real.exp (|d| * (29 / 20)) := by
    calc Real.exp (c * (ModularGroup.S • w).im) * Real.exp (d * ζ.im)
        ≤ Real.exp (c * (ModularGroup.S • w).im)
            * (Real.exp (d * (ModularGroup.S • w).im)
                * Real.exp (|d| * (29 / 20))) :=
          mul_le_mul_of_nonneg_left h6 (Real.exp_pos _).le
      _ = Real.exp ((c + d) * (ModularGroup.S • w).im) * Real.exp (|d| * (29 / 20)) := by
          have h8 : Real.exp (c * (ModularGroup.S • w).im)
              * Real.exp (d * (ModularGroup.S • w).im)
              = Real.exp ((c + d) * (ModularGroup.S • w).im) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [show Real.exp (c * (ModularGroup.S • w).im)
                * (Real.exp (d * (ModularGroup.S • w).im) * Real.exp (|d| * (29 / 20)))
              = (Real.exp (c * (ModularGroup.S • w).im)
                  * Real.exp (d * (ModularGroup.S • w).im)) * Real.exp (|d| * (29 / 20))
              from by ring, h8]
  have hC0 : (0 : ℝ) ≤ C := hC.le
  have hsc : (0 : ℝ) ≤ (scale w) ^ N := Real.rpow_nonneg (hw.scale_pos).le N
  calc ‖F w ζ‖ ≤ C * (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im)
        * Real.exp (d * ζ.im) := h1
    _ = C * (scale w) ^ N
          * (Real.exp (c * (ModularGroup.S • w).im) * Real.exp (d * ζ.im)) := by ring
    _ ≤ C * (scale w) ^ N
          * (Real.exp ((c + d) * (ModularGroup.S • w).im) * Real.exp (|d| * (29 / 20))) :=
          mul_le_mul_of_nonneg_left h7 (mul_nonneg hC0 hsc)
    _ = C * Real.exp (|d| * (29 / 20)) * (scale w) ^ N
          * Real.exp ((c + d) * (ModularGroup.S • w).im) := by ring
    _ ≤ (C * Real.exp (|d| * (29 / 20)) + 1) * (scale w) ^ N
          * Real.exp ((c + d) * (ModularGroup.S • w).im) := by
          have hge1 : (1 : ℝ) ≤ (scale w) ^ N := Real.one_le_rpow hw.one_le_scale hN
          have hE : 0 < Real.exp ((c + d) * (ModularGroup.S • w).im) := Real.exp_pos _
          have hT : (0 : ℝ) < C * Real.exp (|d| * (29 / 20)) := by positivity
          nlinarith [hge1, hE, hT, hsc]
    _ = (C * Real.exp (|d| * (29 / 20)) + 1) * (scale w) ^ N
          * Real.exp ((c + d) * (ModularGroup.S • w).im) * Real.exp (0 * ζ.im) := by
          rw [zero_mul, Real.exp_zero, mul_one]

namespace BBdd

/-- A `BBdd c d` bound with `c + d ≤ 0` is a plain `BBdd 0 0` bound on the ball. -/
lemma toGood {c d : ℝ} {F : ℍ → ℍ → ℂ} (h : BBdd c d F) (hcd : c + d ≤ 0) :
    BBdd 0 0 F :=
  (BBddShift h).mono hcd le_rfl

/-- A `BBdd c d` bound with `c ≤ 0` and `d ≤ 0` is a plain `BBdd 0 0` bound. -/
lemma monoZero {c d : ℝ} {F : ℍ → ℍ → ℂ} (h : BBdd c d F) (hc : c ≤ 0) (hd : d ≤ 0) :
    BBdd 0 0 F :=
  h.mono hc hd

end BBdd

/-- `BBdd c d` is closed under sums (at a common pair). -/
lemma BBdd.addS {c d : ℝ} {F G : ℍ → ℍ → ℂ} (hF : BBdd c d F) (hG : BBdd c d G) :
    BBdd c d (fun w ζ => F w ζ + G w ζ) := by
  simpa only [max_self] using hF.add hG

/-- `BBdd c d` is closed under differences (at a common pair). -/
lemma BBdd.subS {c d : ℝ} {F G : ℍ → ℍ → ℂ} (hF : BBdd c d F) (hG : BBdd c d G) :
    BBdd c d (fun w ζ => F w ζ - G w ζ) := by
  simpa only [max_self] using hF.sub hG

/-- `BBdd 0 0` is closed under negation. -/
lemma BBdd.negGood {F : ℍ → ℍ → ℂ} (hF : BBdd 0 0 F) : BBdd 0 0 (fun w ζ => -F w ζ) :=
  hF.neg

/-- `BBdd 0 0` is closed under sums. -/
lemma addGood {F G : ℍ → ℍ → ℂ} (hF : BBdd 0 0 F) (hG : BBdd 0 0 G) :
    BBdd 0 0 (fun w ζ => F w ζ + G w ζ) :=
  hF.addS hG

/-- `BBdd 0 0` is closed under differences. -/
lemma subGood {F G : ℍ → ℍ → ℂ} (hF : BBdd 0 0 F) (hG : BBdd 0 0 G) :
    BBdd 0 0 (fun w ζ => F w ζ - G w ζ) :=
  hF.subS hG

/-- `max a b ≤ 0` from `a ≤ 0` and `b ≤ 0`; the shape produced by `BBdd.add`. -/
lemma maxZero {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) : max a b ≤ 0 := max_le ha hb

/-! ## §2  `ζ`-atom converters -/

lemma norm_Ept_pow (z : ℍ) (k : ℕ) :
    ‖Ept z‖ ^ k = Real.exp (-(k * Real.pi * z.im)) := by
  rw [Work.Residues.norm_Ept, ← Real.exp_nat_mul]
  congr 1
  ring

lemma norm_Ept_sq_inv (z : ℍ) :
    (‖Ept z‖ ^ 2)⁻¹ = Real.exp (2 * Real.pi * z.im) := by
  rw [norm_Ept_pow z 2, ← Real.exp_neg]
  congr 1
  ring

/-- **`ζ`-atom in the general shape.**  If `‖f z‖ ≤ C (1+‖z‖)^m e^{-K Im z}` for `Im z ≥ 3`,
then `BBdd 0 (-K)` (the polynomial factor `(1 + ‖z‖)^m` is absorbed into `(scale w)^m`,
because `‖z‖ ≤ (49/20)·scale w` on the ball). -/
lemma BBddOfZAtom {K m C : ℝ} {f : ℍ → ℂ} (hC : 0 ≤ C) (hm : 0 ≤ m)
    (h : ∀ z : ℍ, 3 ≤ z.im →
      ‖f z‖ ≤ C * (1 + ‖(z : ℂ)‖) ^ m * Real.exp ((-K) * z.im)) :
    BBdd 0 (-K) (fun _ z => f z) := by
  refine ⟨C * 4 ^ m + 1, m, by positivity, hm, fun w ζ hw => ?_⟩
  have h1 := h ζ hw.him
  have hz : (1 : ℝ) + ‖(ζ : ℂ)‖ ≤ 4 * scale w := by
    have h2 := hw.norm_le_scaled
    have h3 := hw.one_le_scale
    linarith
  have hz0 : (0 : ℝ) ≤ 1 + ‖(ζ : ℂ)‖ := by positivity
  have h4 : (1 + ‖(ζ : ℂ)‖) ^ m ≤ (4 * scale w) ^ m := Real.rpow_le_rpow hz0 hz hm
  have h5 : (4 * scale w) ^ m = 4 ^ m * (scale w) ^ m :=
    Real.mul_rpow (by norm_num) (hw.scale_pos).le
  have h6 : (0 : ℝ) ≤ (scale w) ^ m := Real.rpow_nonneg (hw.scale_pos).le m
  have h7 : (0 : ℝ) ≤ 4 ^ m := Real.rpow_nonneg (by norm_num) m
  calc ‖f ζ‖ ≤ C * (1 + ‖(ζ : ℂ)‖) ^ m * Real.exp ((-K) * ζ.im) := h1
    _ ≤ C * (4 ^ m * (scale w) ^ m) * Real.exp ((-K) * ζ.im) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC) (Real.exp_pos _).le
        rw [← h5]; exact h4
    _ = C * 4 ^ m * (scale w) ^ m * Real.exp ((-K) * ζ.im) := by ring
    _ ≤ (C * 4 ^ m + 1) * (scale w) ^ m * Real.exp ((-K) * ζ.im) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        nlinarith [h6, h7]
    _ = (C * 4 ^ m + 1) * (scale w) ^ m * Real.exp (0 * (ModularGroup.S • w).im)
          * Real.exp (-K * ζ.im) := by
        rw [zero_mul, Real.exp_zero, mul_one]

/-- `ζ`-atom with `K = 0` (polynomially bounded `ζ`-function). -/
lemma BBddOfZAtom0 {m C : ℝ} {f : ℍ → ℂ} (hC : 0 ≤ C) (hm : 0 ≤ m)
    (h : ∀ z : ℍ, 3 ≤ z.im → ‖f z‖ ≤ C * (1 + ‖(z : ℂ)‖) ^ m) :
    BBdd 0 0 (fun _ z => f z) := by
  have h' : BBdd 0 (-(0 : ℝ)) (fun _ z => f z) :=
    BBddOfZAtom (K := 0) hC hm (fun z hz => by
      have h1 := h z hz
      simpa using h1)
  simpa using h'

/-- **`ζ`-atom of `Ept`-order `k`.**  If `‖f z‖ ≤ C ‖Ept z‖^k` for `Im z ≥ 3` then
`BBdd 0 (-(kπ))`. -/
lemma BBddOfEptpow {k : ℕ} {f : ℍ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z : ℍ, 3 ≤ z.im → ‖f z‖ ≤ C * ‖Ept z‖ ^ k) :
    BBdd 0 (-(k * Real.pi)) (fun _ z => f z) := by
  refine BBddOfZAtom (K := k * Real.pi) (m := 0) hC (le_refl 0) (fun z hz => ?_)
  have h1 := h z hz
  rw [norm_Ept_pow z k] at h1
  refine le_trans h1 ?_
  rw [Real.rpow_zero, mul_one]
  have : Real.exp (-(k * Real.pi * z.im)) = Real.exp ((-(k * Real.pi)) * z.im) := by
    congr 1; ring
  rw [this]

/-- **`ζ`-atom of `Ept⁻²`-order.**  If `‖f z‖ ≤ C (‖Ept z‖²)⁻¹` for `Im z ≥ 3` then
`BBdd 0 (2π)`. -/
lemma BBddOfEptinv2 {f : ℍ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z : ℍ, 3 ≤ z.im → ‖f z‖ ≤ C * (‖Ept z‖ ^ 2)⁻¹) :
    BBdd 0 (2 * Real.pi) (fun _ z => f z) := by
  have h' : BBdd 0 (-(-(2 * Real.pi))) (fun _ z => f z) :=
    BBddOfZAtom (K := -(2 * Real.pi)) (m := 0) hC (le_refl 0) (fun z hz => ?_)
  · simpa using h'
  · have h1 := h z hz
    rw [norm_Ept_sq_inv z] at h1
    refine le_trans h1 ?_
    rw [Real.rpow_zero, mul_one]
    have h2 : Real.exp (2 * Real.pi * z.im) = Real.exp ((-(-(2 * Real.pi))) * z.im) := by
      congr 1; ring
    rw [h2]

/-! ## §3  The `τ`-atoms at `τ = n +ᵥ w`, `n = ±1` -/

/-- `Δ(τ)` at `τ = n +ᵥ w` is `O(e^{-2π Im(S • w)})`. -/
lemma tDB (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd (-(2 * Real.pi)) 0 (fun (w : ℍ) (_ : ℍ) => DeltaFun ((n:ℝ)+ᵥw)) :=
  BBdd.of_bdd (Work.Asymptotics.Bdd.shift EtailE.E_bdd_Delta
    (fun τ => Work.Kernels.KernelFacts.DeltaFun_vadd_one τ) n hn)

/-- `ψ₂(τ)E₁₀(τ)` at `τ = n +ᵥ w` is polynomially bounded. -/
lemma tP2E10B (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (_ : ℍ) =>
      Work.Kernels.psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw)) :=
  BBdd.of_bdd (by
    simpa using ((Work.Asymptotics.Bdd.vadd_psi2 ℓ n hn).mul
      (Work.Asymptotics.Bdd.vadd_E10 n hn)))

/-- `ψ₄(τ)E₈(τ)` at `τ = n +ᵥ w` is polynomially bounded. -/
lemma tP4E8B (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (_ : ℍ) =>
      Work.Kernels.psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw)) :=
  BBdd.of_bdd (by
    simpa using ((Work.Asymptotics.Bdd.vadd_psi4 ℓ n hn).mul
      (Work.Asymptotics.Bdd.vadd_E8 n hn)))

/-- The `T`-cocycle of `psiCombo` for `n = ±1`. -/
lemma psiCombo_cocycle (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) (w : ℍ) :
    Work.Asymptotics.Tile.psiCombo ℓ ((n:ℝ)+ᵥw)
      = Work.Asymptotics.Tile.psiCombo ℓ w
        + (n:ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w) := by
  rcases hn with h | h
  · rw [h, Int.cast_one]
    push_cast
    rw [one_mul]
    exact Work.Asymptotics.Tile.psiCombo_vadd_one ℓ w
  · rw [h, Int.cast_neg, Int.cast_one]
    push_cast
    rw [neg_one_mul]
    exact Work.Asymptotics.Tile.psiCombo_vadd_neg_one ℓ w

/-- `ψ₄(τ)E₈(τ) - ψ₂(τ)E₁₀(τ)` at `τ = n +ᵥ w` is `O(e^{-π Im(S • w)})`: the `T`-cocycle
`psiCombo(τ+1) = psiCombo τ + πi Xfun τ` together with `Bdd (-2π)` (`psiCombo` at `τ ∈ E`)
and `Bdd (-π)` for `Xfun`. -/
lemma Bdd_psiCombo_shift (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    Bdd (-Real.pi) (fun (w : ℍ) =>
      Work.Kernels.psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw)
        - Work.Kernels.psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw)) := by
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := EtailE.E_bdd_psi4E8_sub ℓ
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := Work.Asymptotics.Tile.E_bdd_Xfun
  refine ⟨C1 + Real.pi * C2, max N1 N2, by positivity, le_max_of_le_left hN1, fun w hw => ?_⟩
  have hH0 : 0 ≤ (ModularGroup.S • w).im := Work.Asymptotics.EtailE.E_im_S_nonneg hw
  have hs1 : (1:ℝ) ≤ scale w := Work.Kernels.one_le_scale w
  have hN1' : (scale w) ^ N1 ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hN2' : (scale w) ^ N2 ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have hnc : ‖((n:ℂ))‖ = 1 := by
    rw [Complex.norm_intCast]
    rcases hn with h | h <;> rw [h] <;> norm_num
  have hb1 : ‖Work.Asymptotics.Tile.psiCombo ℓ w‖ ≤ C1 * (scale w) ^ N1
      * Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) := h1 w hw
  have hb2 : ‖Work.Residues.Xfun w‖ ≤ C2 * (scale w) ^ N2
      * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := h2 w hw
  have hexp1 : Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im)
      ≤ Real.exp ((-Real.pi) * (ModularGroup.S • w).im) :=
    Real.exp_le_exp.mpr (by nlinarith [hH0, Real.pi_pos])
  have hmain : ‖Work.Asymptotics.Tile.psiCombo ℓ ((n:ℝ)+ᵥw)‖
      ≤ C1 * (scale w) ^ N1 * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)
        + Real.pi * (C2 * (scale w) ^ N2 * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)) := by
    calc ‖Work.Asymptotics.Tile.psiCombo ℓ ((n:ℝ)+ᵥw)‖
        = ‖Work.Asymptotics.Tile.psiCombo ℓ w
            + (n:ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w)‖ := by
          rw [psiCombo_cocycle ℓ n hn w]
      _ ≤ ‖Work.Asymptotics.Tile.psiCombo ℓ w‖
            + ‖(n:ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w)‖ := norm_add_le _ _
      _ = ‖Work.Asymptotics.Tile.psiCombo ℓ w‖ + Real.pi * ‖Work.Residues.Xfun w‖ := by
          rw [norm_mul, hnc, one_mul, norm_mul, norm_mul, Complex.norm_I, mul_one,
            Work.Asymptotics.EtailE.norm_pi]
      _ ≤ C1 * (scale w) ^ N1 * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)
            + Real.pi * (C2 * (scale w) ^ N2 * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)) := by
          refine add_le_add (le_trans hb1 ?_) (mul_le_mul_of_nonneg_left hb2 Real.pi_pos.le)
          exact mul_le_mul_of_nonneg_left hexp1
            (mul_nonneg hC1.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
  have hNmax : (0:ℝ) ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_nonneg (Work.Kernels.scale_pos w).le _
  have hfinal : C1 * (scale w) ^ N1 * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)
        + Real.pi * (C2 * (scale w) ^ N2 * Real.exp ((-Real.pi) * (ModularGroup.S • w).im))
      ≤ (C1 + Real.pi * C2) * (scale w) ^ (max N1 N2)
        * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by
    have hE : 0 < Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := Real.exp_pos _
    have hb1' : C1 * (scale w) ^ N1 ≤ C1 * (scale w) ^ (max N1 N2) :=
      mul_le_mul_of_nonneg_left hN1' hC1.le
    have hb2' : Real.pi * (C2 * (scale w) ^ N2) ≤ Real.pi * (C2 * (scale w) ^ (max N1 N2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN2' hC2.le) Real.pi_pos.le
    calc C1 * (scale w) ^ N1 * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)
          + Real.pi * (C2 * (scale w) ^ N2 * Real.exp ((-Real.pi) * (ModularGroup.S • w).im))
        = (C1 * (scale w) ^ N1 + Real.pi * (C2 * (scale w) ^ N2))
            * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by ring
      _ ≤ (C1 * (scale w) ^ (max N1 N2) + Real.pi * (C2 * (scale w) ^ (max N1 N2)))
            * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) :=
          mul_le_mul_of_nonneg_right (add_le_add hb1' hb2') hE.le
      _ = (C1 + Real.pi * C2) * (scale w) ^ (max N1 N2)
            * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by ring
  have hgoal : ‖Work.Kernels.psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw)
        - Work.Kernels.psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw)‖
      = ‖Work.Asymptotics.Tile.psiCombo ℓ ((n:ℝ)+ᵥw)‖ := rfl
  rw [hgoal]
  exact le_trans hmain hfinal

/-- `ψ₄(τ)E₈(τ) - ψ₂(τ)E₁₀(τ)` at `τ = n +ᵥ w`, in the `BBdd` calculus. -/
lemma tPSB (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd (-Real.pi) 0 (fun (w : ℍ) (_ : ℍ) =>
      Work.Kernels.psi4 ℓ ((n:ℝ)+ᵥw) * E8Fun ((n:ℝ)+ᵥw)
        - Work.Kernels.psi2 ℓ ((n:ℝ)+ᵥw) * E10Fun ((n:ℝ)+ᵥw)) :=
  BBdd.of_bdd (Bdd_psiCombo_shift ℓ n hn)

/-- `j(τ)Δ(τ)` at `τ = n +ᵥ w`: the `e^{2π Im(S•w)}` of `j` and the `e^{-2π Im(S•w)}` of `Δ`
cancel. -/
lemma tjDB (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (_ : ℍ) =>
      jInvariantFun ((n:ℝ)+ᵥw) * DeltaFun ((n:ℝ)+ᵥw)) :=
  ((tj n hn).mul (tDB n hn)).toGood (by nlinarith [Real.pi_pos])

/-! ## §4  The `ζ`-atoms -/

/-- `Ept z ^ k` is `BBdd 0 (-(kπ))`. -/
lemma zEptB (k : ℕ) : BBdd 0 (-(k * Real.pi)) (fun _ (z : ℍ) => Ept z ^ k) := by
  refine BBddOfEptpow (C := 1) zero_le_one (fun z _ => ?_)
  rw [one_mul]
  exact le_of_eq (norm_pow _ _)

/-- `k · Ept z` is `BBdd 0 (-π)`. -/
lemma zEpt1mulB (k : ℂ) : BBdd 0 (-Real.pi) (fun _ (z : ℍ) => k * Ept z) := by
  have h : BBdd 0 (-(((1:ℕ):ℝ) * Real.pi)) (fun _ (z : ℍ) => k * Ept z ^ 1) :=
    (zEptB 1).const_mul k
  have h' : BBdd 0 (-Real.pi) (fun _ (z : ℍ) => k * Ept z ^ 1) :=
    h.mono (c' := 0) (d' := -Real.pi) (le_refl 0) (le_of_eq (by norm_num))
  refine BBdd.congr ?_ h'
  funext w z
  rw [pow_one]

/-- `Xc ℓ z = πiz + c` is polynomially bounded. -/
lemma zXcB (ℓ : LogLambdaData) : BBdd 0 0 (fun _ z => Compact.Xc ℓ z) := by
  refine BBddOfZAtom0 (m := 1) (C := Real.pi + ‖Compact.cuspC ℓ‖ + 1) (by positivity)
    (by norm_num) (fun z _ => ?_)
  have h1 : ‖Compact.Xc ℓ z‖ ≤ Real.pi * ‖(z : ℂ)‖ + ‖Compact.cuspC ℓ‖ := by
    rw [Compact.Xc]
    refine le_trans (norm_add_le _ _) (le_of_eq ?_)
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Work.Asymptotics.EtailE.norm_pi]
  have h3 : Real.pi * ‖(z : ℂ)‖ + ‖Compact.cuspC ℓ‖
      ≤ (Real.pi + ‖Compact.cuspC ℓ‖ + 1) * (1 + ‖(z : ℂ)‖) := by
    nlinarith [Real.pi_pos, norm_nonneg (z : ℂ), norm_nonneg (Compact.cuspC ℓ)]
  simpa [Real.rpow_one] using le_trans h1 h3

/-- The `kmfd_zdevs` package at the threshold `3 ≤ Im z` used on the ball. -/
lemma kmfd_zdevs3 (ℓ : LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 3 ≤ z.im →
      ‖Compact.dDelta z‖ ≤ C * ‖Ept z‖ ^ 2 ∧
      ‖Compact.dW z‖ ≤ C * ‖Ept z‖ ^ 3 ∧
      ‖Compact.dD2 z‖ ≤ C * ‖Ept z‖ ^ 3 ∧
      ‖Compact.dL ℓ z‖ ≤ C * ‖Ept z‖ ^ 3 ∧
      ‖Compact.dE14 z‖ ≤ C * ‖Ept z‖ ^ 4 ∧
      ‖Compact.dE10 z‖ ≤ C * ‖Ept z‖ ^ 4 ∧
      ‖E4Fun z ^ 3 - Work.Asymptotics.kmfd_E4refc z‖ ≤ C * ‖Ept z‖ ^ 4 ∧
      ‖DeltaFun z - Ept z ^ 2‖ ≤ C * ‖Ept z‖ ^ 4 ∧
      ‖jInvariantFun z - Work.Asymptotics.kmfd_jref z‖ ≤ C * ‖Ept z‖ ^ 2 ∧
      ‖ℓ.L z‖ ≤ C * (1 + ‖(z : ℂ)‖) ∧
      ‖WFun z‖ ≤ C ∧
      ‖UFun z ^ 2 - VFun z ^ 2‖ ≤ C ∧
      ‖Compact.E10ref z‖ ≤ C ∧
      ‖Compact.E14ref z‖ ≤ C ∧
      ‖Compact.Dref z‖ ≤ C * (‖Ept z‖ ^ 2)⁻¹ ∧
      ‖Work.Asymptotics.kmfd_jref z‖ ≤ C * (‖Ept z‖ ^ 2)⁻¹ ∧
      ‖Work.Asymptotics.kmfd_E4refc z‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.kmfd_zdevs ℓ
  exact ⟨C, hC, fun z hz => h z (by linarith)⟩

/-- `Dref z = Δ(z)⁻¹` (reference value) is `O(e^{2π Im z})`. -/
lemma zDrefB (ℓ : LogLambdaData) : BBdd 0 (2 * Real.pi) (fun _ z => Compact.Dref z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfEptinv2 hC.le (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  exact h15

/-- `einv2 z = Ept z⁻²` is `BBdd 0 (2π)`. -/
lemma zEinv2B : BBdd 0 (2 * Real.pi) (fun _ z => Compact.einv2 z) := by
  refine BBddOfEptinv2 (C := 1) zero_le_one (fun z _ => ?_)
  have h1 : ‖Compact.einv2 z‖ = (‖Ept z‖ ^ 2)⁻¹ := by
    simp only [Compact.einv2, norm_pow, norm_inv, inv_pow]
  rw [h1, one_mul]

/-- `jref z = (1+240E²)³(E⁻²+24)` is `O(e^{2π Im z})`. -/
lemma zjrefB (ℓ : LogLambdaData) :
    BBdd 0 (2 * Real.pi) (fun _ z => Work.Asymptotics.kmfd_jref z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfEptinv2 hC.le (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  exact h16

/-- `kmfd_E4refc z = (1+240E²)³` is polynomially bounded. -/
lemma zE4refcB (ℓ : LogLambdaData) :
    BBdd 0 0 (fun _ z => Work.Asymptotics.kmfd_E4refc z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfZAtom0 (m := 0) hC.le (le_refl 0) (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  simpa using h17

/-- `E10ref z` is polynomially bounded. -/
lemma zE10refB (ℓ : LogLambdaData) : BBdd 0 0 (fun _ z => Compact.E10ref z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfZAtom0 (m := 0) hC.le (le_refl 0) (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  simpa using h13

/-- `E14ref z` is polynomially bounded. -/
lemma zE14refB (ℓ : LogLambdaData) : BBdd 0 0 (fun _ z => Compact.E14ref z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfZAtom0 (m := 0) hC.le (le_refl 0) (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  simpa using h14

/-- `W(ζ)` is polynomially bounded. -/
lemma zWB (ℓ : LogLambdaData) : BBdd 0 0 (fun _ z => WFun z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfZAtom0 (m := 0) hC.le (le_refl 0) (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  simpa using h11

/-- `U(ζ)² - V(ζ)²` is polynomially bounded. -/
lemma zD2B (ℓ : LogLambdaData) : BBdd 0 0 (fun _ z => UFun z ^ 2 - VFun z ^ 2) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfZAtom0 (m := 0) hC.le (le_refl 0) (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  simpa using h12

/-- `𝓛(ζ)` is polynomially bounded. -/
lemma zLB (ℓ : LogLambdaData) : BBdd 0 0 (fun _ z => ℓ.L z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfZAtom0 (m := 1) hC.le (by norm_num) (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  simpa using h10

/-- `D2ref ζ = 1 + 16E - 144E²` is polynomially bounded. -/
lemma zD2refB : BBdd 0 0 (fun _ z => Compact.D2ref z) := by
  have h1 : BBdd 0 0 (fun _ (z : ℍ) => (1:ℂ) + 16 * Ept z) :=
    addGood (BBdd.const (1 : ℂ)) ((zEpt1mulB 16).toGood (by nlinarith [Real.pi_pos]))
  have h2 : BBdd 0 0 (fun _ (z : ℍ) => ((1:ℂ) + 16 * Ept z) + (-144:ℂ) * Ept z ^ 2) :=
    addGood h1 ((zEptB 2).const_mul (-144:ℂ) |>.toGood (by nlinarith [Real.pi_pos]))
  refine BBdd.congr ?_ h2
  funext w z
  simp only [Compact.D2ref]
  ring

/-- `Wref ζ = 1 - 8E + 24E²` is polynomially bounded. -/
lemma zWrefB : BBdd 0 0 (fun _ z => Compact.Wref z) := by
  have h1 : BBdd 0 0 (fun _ (z : ℍ) => (1:ℂ) + (-8:ℂ) * Ept z) :=
    addGood (BBdd.const (1 : ℂ)) ((zEpt1mulB (-8)).toGood (by nlinarith [Real.pi_pos]))
  have h2 : BBdd 0 0 (fun _ (z : ℍ) => ((1:ℂ) + (-8:ℂ) * Ept z) + (24:ℂ) * Ept z ^ 2) :=
    addGood h1 ((zEptB 2).const_mul (24:ℂ) |>.toGood (by nlinarith [Real.pi_pos]))
  refine BBdd.congr ?_ h2
  funext w z
  simp only [Compact.Wref]
  ring

/-- `Lref ℓ ζ = Xc - 8E + 12E²` is polynomially bounded. -/
lemma zLrefB (ℓ : LogLambdaData) : BBdd 0 0 (fun _ z => Compact.Lref ℓ z) := by
  have h1 : BBdd 0 0 (fun _ (z : ℍ) => Compact.Xc ℓ z + (-8:ℂ) * Ept z) :=
    addGood (zXcB ℓ) ((zEpt1mulB (-8)).toGood (by nlinarith [Real.pi_pos]))
  have h2 : BBdd 0 0 (fun _ (z : ℍ) => (Compact.Xc ℓ z + (-8:ℂ) * Ept z) + (12:ℂ) * Ept z ^ 2) :=
    addGood h1 ((zEptB 2).const_mul (12:ℂ) |>.toGood (by nlinarith [Real.pi_pos]))
  refine BBdd.congr ?_ h2
  funext w z
  simp only [Compact.Lref]
  ring

/-! ### The `ζ`-deviations -/

/-- `dDelta ζ = Δ(ζ)⁻¹ - Dref ζ` is `O(e^{-2π Im ζ})`. -/
lemma zdDeltaB (ℓ : LogLambdaData) :
    BBdd 0 (-(2 * Real.pi)) (fun _ z => Compact.dDelta z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfEptpow (k := 2) hC.le (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  exact h1

/-- `dW ζ = W(ζ) - Wref ζ` is `O(e^{-3π Im ζ})`. -/
lemma zdWB (ℓ : LogLambdaData) :
    BBdd 0 (-(3 * Real.pi)) (fun _ z => Compact.dW z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfEptpow (k := 3) hC.le (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  exact h2

/-- `dD2 ζ` is `O(e^{-3π Im ζ})`. -/
lemma zdD2B (ℓ : LogLambdaData) :
    BBdd 0 (-(3 * Real.pi)) (fun _ z => Compact.dD2 z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfEptpow (k := 3) hC.le (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  exact h3

/-- `dL ζ` is `O(e^{-3π Im ζ})`. -/
lemma zdLB (ℓ : LogLambdaData) :
    BBdd 0 (-(3 * Real.pi)) (fun _ z => Compact.dL ℓ z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfEptpow (k := 3) hC.le (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  exact h4

/-- `dE14 ζ` is `O(e^{-4π Im ζ})`. -/
lemma zdE14B (ℓ : LogLambdaData) :
    BBdd 0 (-(4 * Real.pi)) (fun _ z => Compact.dE14 z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfEptpow (k := 4) hC.le (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  exact h5

/-- `dE10 ζ` is `O(e^{-4π Im ζ})`. -/
lemma zdE10B (ℓ : LogLambdaData) :
    BBdd 0 (-(4 * Real.pi)) (fun _ z => Compact.dE10 z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfEptpow (k := 4) hC.le (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  exact h6

/-- `E₄(ζ)³ - (1+240E²)³` is `O(e^{-4π Im ζ})`. -/
lemma zE4cdevB (ℓ : LogLambdaData) :
    BBdd 0 (-(4 * Real.pi)) (fun _ z => E4Fun z ^ 3 - Work.Asymptotics.kmfd_E4refc z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfEptpow (k := 4) hC.le (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  exact h7

/-- `Δ(ζ) - E²` is `O(e^{-4π Im ζ})`. -/
lemma zDdiffB (ℓ : LogLambdaData) :
    BBdd 0 (-(4 * Real.pi)) (fun _ z => DeltaFun z - Ept z ^ 2) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfEptpow (k := 4) hC.le (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  exact h8

/-- `j(ζ) - jref ζ` is `O(e^{-2π Im ζ})`. -/
lemma zjdevB (ℓ : LogLambdaData) :
    BBdd 0 (-(2 * Real.pi)) (fun _ z => jInvariantFun z - Work.Asymptotics.kmfd_jref z) := by
  obtain ⟨C, hC, h⟩ := kmfd_zdevs3 ℓ
  refine BBddOfEptpow (k := 2) hC.le (fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h z hz
  exact h9

end Work.Asymptotics.TileDevBall
