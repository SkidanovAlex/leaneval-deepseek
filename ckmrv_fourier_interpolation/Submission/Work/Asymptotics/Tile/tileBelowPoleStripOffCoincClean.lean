/-
# The resonant strip off the coincidences, from the ball bound
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Tile.tileStripOffCoincDefs
import Submission.Work.Asymptotics.Tile.tileStripOffCoincEndgame
import Submission.Work.Asymptotics.Tile.halfDevClearOffAxis24Plus
import Submission.Work.Asymptotics.TileDevBall.BallShape
import Submission.Work.Asymptotics.KMFDDefs
import Submission.Work.Asymptotics.KMFDZDevs
import Submission.Work.Asymptotics.Tile.tile_tau_atoms
import Submission.Work.Asymptotics.Tile.psi_combo_small
import Submission.Work.Asymptotics.Compact.gfun_eq
import Submission.Work.Asymptotics.TileDevBall.kplusDev8Ball
import Submission.Work.Asymptotics.TileDevBall.kplusDev24Ball
import Submission.Work.Asymptotics.TileNumBallTS.Assembly
import Submission.Work.Asymptotics.continuous_AfunFun

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open Work.Kernels
open scoped MatrixGroups UpperHalfPlane

noncomputable section

abbrev KBall (w ζ : ℍ) : Prop := Work.Asymptotics.TileDevBall.Ball w ζ

/-! ## The two-exponent bookkeeping calculus with the tile index `n` -/

/-- `KB c d F`: on the ball (`w ∈ E`, `‖ζ - S • w‖ ≤ 29/20`, `3 ≤ Im ζ`) and for `n = ±1`,

  `‖F w n ζ‖ ≤ C (scale w)^N exp (c Im (S • w) + d Im ζ)`. -/
def KB (c d : ℝ) (F : ℍ → ℤ → ℍ → ℂ) : Prop :=
  ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w ζ : ℍ) (n : ℤ), (n = 1 ∨ n = -1) →
    KBall w ζ →
    ‖F w n ζ‖ ≤ C * (Work.Kernels.scale w) ^ N
      * Real.exp (c * (ModularGroup.S • w).im + d * ζ.im)

namespace KB

variable {c d c' d' c₁ d₁ c₂ d₂ : ℝ} {F G : ℍ → ℤ → ℍ → ℂ}

lemma mono (hc : c ≤ c') (hd : d ≤ d') (h : KB c d F) : KB c' d' F := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, fun w ζ n hn hw => ?_⟩
  refine le_trans (hb w ζ n hn hw) ?_
  have hx : 0 ≤ (ModularGroup.S • w).im := hw.S_im_nonneg
  have hy : 0 ≤ ζ.im := le_of_lt hw.im_pos
  have h1 : c * (ModularGroup.S • w).im ≤ c' * (ModularGroup.S • w).im :=
    mul_le_mul_of_nonneg_right hc hx
  have h2 : d * ζ.im ≤ d' * ζ.im := mul_le_mul_of_nonneg_right hd hy
  have h0 : 0 ≤ C * (Work.Kernels.scale w) ^ N :=
    mul_nonneg hC.le (Real.rpow_nonneg (hw.scale_pos).le N)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) h0

lemma reduce (hd : d ≤ 0) (hcd : c + d ≤ 0) (h : KB c d F) : KB 0 0 F := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C * Real.exp (-(d * (29 / 20))), N, by positivity, hN, fun w ζ n hn hw => ?_⟩
  refine le_trans (hb w ζ n hn hw) ?_
  have hk := Work.Asymptotics.TileDevBall.Ball.exp_le_const_im (w := w) (ζ := ζ) hw hd hcd
  have h0 : 0 ≤ C * (Work.Kernels.scale w) ^ N :=
    mul_nonneg hC.le (Real.rpow_nonneg (hw.scale_pos).le N)
  calc C * (Work.Kernels.scale w) ^ N
        * Real.exp (c * (ModularGroup.S • w).im + d * ζ.im)
      = C * (Work.Kernels.scale w) ^ N
          * (Real.exp (c * (ModularGroup.S • w).im) * Real.exp (d * ζ.im)) := by
        rw [Real.exp_add]
    _ ≤ C * (Work.Kernels.scale w) ^ N * Real.exp (-(d * (29 / 20))) :=
        mul_le_mul_of_nonneg_left hk h0
    _ = C * Real.exp (-(d * (29 / 20))) * (Work.Kernels.scale w) ^ N
          * Real.exp (0 * (ModularGroup.S • w).im + 0 * ζ.im) := by
        simp only [zero_mul, add_zero, Real.exp_zero, mul_one]
        ring

lemma mul (hF : KB c₁ d₁ F) (hG : KB c₂ d₂ G) :
    KB (c₁ + c₂) (d₁ + d₂) (fun w n ζ => F w n ζ * G w n ζ) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hF
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hG
  refine ⟨C1 * C2, N1 + N2, by positivity, by linarith, fun w ζ n hn hw => ?_⟩
  have e1 := hb1 w ζ n hn hw
  have e2 := hb2 w ζ n hn hw
  have hX : (0:ℝ) < Work.Kernels.scale w := hw.scale_pos
  have hkey1 : (Work.Kernels.scale w) ^ N1 * (Work.Kernels.scale w) ^ N2
      = (Work.Kernels.scale w) ^ (N1 + N2) := (Real.rpow_add hX N1 N2).symm
  have hkey2 : Real.exp (c₁ * (ModularGroup.S • w).im + d₁ * ζ.im)
        * Real.exp (c₂ * (ModularGroup.S • w).im + d₂ * ζ.im)
      = Real.exp ((c₁ + c₂) * (ModularGroup.S • w).im + (d₁ + d₂) * ζ.im) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [norm_mul]
  calc ‖F w n ζ‖ * ‖G w n ζ‖
      ≤ (C1 * (Work.Kernels.scale w) ^ N1
            * Real.exp (c₁ * (ModularGroup.S • w).im + d₁ * ζ.im))
        * (C2 * (Work.Kernels.scale w) ^ N2
            * Real.exp (c₂ * (ModularGroup.S • w).im + d₂ * ζ.im)) :=
        mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
    _ = C1 * C2 * (Work.Kernels.scale w) ^ (N1 + N2)
          * Real.exp ((c₁ + c₂) * (ModularGroup.S • w).im + (d₁ + d₂) * ζ.im) := by
        rw [show (C1 * (Work.Kernels.scale w) ^ N1
              * Real.exp (c₁ * (ModularGroup.S • w).im + d₁ * ζ.im))
            * (C2 * (Work.Kernels.scale w) ^ N2
              * Real.exp (c₂ * (ModularGroup.S • w).im + d₂ * ζ.im))
          = C1 * C2 * ((Work.Kernels.scale w) ^ N1 * (Work.Kernels.scale w) ^ N2)
            * (Real.exp (c₁ * (ModularGroup.S • w).im + d₁ * ζ.im)
                * Real.exp (c₂ * (ModularGroup.S • w).im + d₂ * ζ.im)) from by ring,
          hkey1, hkey2]

lemma add (hF : KB c₁ d₁ F) (hG : KB c₂ d₂ G) :
    KB (max c₁ c₂) (max d₁ d₂) (fun w n ζ => F w n ζ + G w n ζ) := by
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := hF
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := hG
  refine ⟨C1 + C2, max N1 N2, by positivity, le_max_of_le_left hN1, fun w ζ n hn hw => ?_⟩
  refine le_trans (norm_add_le _ _) ?_
  have hN1' : (Work.Kernels.scale w) ^ N1 ≤ (Work.Kernels.scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hw.one_le_scale (le_max_left _ _)
  have hN2' : (Work.Kernels.scale w) ^ N2 ≤ (Work.Kernels.scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hw.one_le_scale (le_max_right _ _)
  have hx : 0 ≤ (ModularGroup.S • w).im := hw.S_im_nonneg
  have hy : 0 ≤ ζ.im := le_of_lt hw.im_pos
  have hexp1 : Real.exp (c₁ * (ModularGroup.S • w).im + d₁ * ζ.im)
      ≤ Real.exp (max c₁ c₂ * (ModularGroup.S • w).im + max d₁ d₂ * ζ.im) :=
    Real.exp_le_exp.mpr (by
      have a : c₁ * (ModularGroup.S • w).im ≤ max c₁ c₂ * (ModularGroup.S • w).im :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hx
      have b : d₁ * ζ.im ≤ max d₁ d₂ * ζ.im :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hy
      linarith)
  have hexp2 : Real.exp (c₂ * (ModularGroup.S • w).im + d₂ * ζ.im)
      ≤ Real.exp (max c₁ c₂ * (ModularGroup.S • w).im + max d₁ d₂ * ζ.im) :=
    Real.exp_le_exp.mpr (by
      have a : c₂ * (ModularGroup.S • w).im ≤ max c₁ c₂ * (ModularGroup.S • w).im :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hx
      have b : d₂ * ζ.im ≤ max d₁ d₂ * ζ.im :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hy
      linarith)
  have hA := hb1 w ζ n hn hw
  have hB := hb2 w ζ n hn hw
  have hA0 : 0 ≤ C1 * (Work.Kernels.scale w) ^ N1 :=
    mul_nonneg hC1.le (Real.rpow_nonneg hw.scale_pos.le _)
  have hSmax : 0 ≤ (Work.Kernels.scale w) ^ (max N1 N2) :=
    Real.rpow_nonneg hw.scale_pos.le _
  have he : 0 ≤ Real.exp (max c₁ c₂ * (ModularGroup.S • w).im + max d₁ d₂ * ζ.im) :=
    (Real.exp_pos _).le
  have h1 : C1 * (Work.Kernels.scale w) ^ N1
        * Real.exp (c₁ * (ModularGroup.S • w).im + d₁ * ζ.im)
      ≤ C1 * (Work.Kernels.scale w) ^ (max N1 N2)
        * Real.exp (max c₁ c₂ * (ModularGroup.S • w).im + max d₁ d₂ * ζ.im) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hN1' hC1.le) hexp1 (Real.exp_pos _).le
      (mul_nonneg hC1.le hSmax)
  have h2 : C2 * (Work.Kernels.scale w) ^ N2
        * Real.exp (c₂ * (ModularGroup.S • w).im + d₂ * ζ.im)
      ≤ C2 * (Work.Kernels.scale w) ^ (max N1 N2)
        * Real.exp (max c₁ c₂ * (ModularGroup.S • w).im + max d₁ d₂ * ζ.im) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hN2' hC2.le) hexp2 (Real.exp_pos _).le
      (mul_nonneg hC2.le hSmax)
  have hgoal : C1 * (Work.Kernels.scale w) ^ (max N1 N2)
        * Real.exp (max c₁ c₂ * (ModularGroup.S • w).im + max d₁ d₂ * ζ.im)
      + C2 * (Work.Kernels.scale w) ^ (max N1 N2)
        * Real.exp (max c₁ c₂ * (ModularGroup.S • w).im + max d₁ d₂ * ζ.im)
      = (C1 + C2) * (Work.Kernels.scale w) ^ (max N1 N2)
        * Real.exp (max c₁ c₂ * (ModularGroup.S • w).im + max d₁ d₂ * ζ.im) := by
    ring
  linarith [le_trans hA h1, le_trans hB h2, hgoal]

lemma neg (h : KB c d F) : KB c d (fun w n ζ => -F w n ζ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  exact ⟨C, N, hC, hN, fun w ζ n hn hw => by rw [norm_neg]; exact hb w ζ n hn hw⟩

lemma sub (hF : KB c₁ d₁ F) (hG : KB c₂ d₂ G) :
    KB (max c₁ c₂) (max d₁ d₂) (fun w n ζ => F w n ζ - G w n ζ) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma const (k : ℂ) : KB 0 0 (fun _ _ _ => k) := by
  refine ⟨max ‖k‖ 1, 0, lt_of_lt_of_le zero_lt_one (le_max_right _ _), le_rfl,
    fun w ζ n hn hw => ?_⟩
  simp only [Real.rpow_zero, zero_mul, add_zero, Real.exp_zero, mul_one]
  exact le_max_left _ _

lemma const_mul (k : ℂ) (h : KB c d F) : KB c d (fun w n ζ => k * F w n ζ) := by
  have h1 : KB (0 + c) (0 + d) (fun w n ζ => k * F w n ζ) := (const k).mul h
  simpa using h1

lemma of_BBdd {F : ℍ → ℍ → ℂ} (h : Work.Asymptotics.TileDevBall.BBdd c d F) :
    KB c d (fun w _ ζ => F w ζ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, fun w ζ n hn hw => ?_⟩
  refine le_trans (hb w ζ hw) (le_of_eq ?_)
  rw [Real.exp_add]; ring

lemma cast (hc : c = c') (hd : d = d') (h : KB c d F) : KB c' d' F := by
  rw [← hc, ← hd]; exact h

lemma add0 (hF : KB 0 0 F) (hG : KB 0 0 G) :
    KB 0 0 (fun w n ζ => F w n ζ + G w n ζ) := by
  simpa using hF.add hG

lemma mul0 (hF : KB 0 0 F) (hG : KB 0 0 G) :
    KB 0 0 (fun w n ζ => F w n ζ * G w n ζ) := by
  simpa using hF.mul hG

lemma sub0 (hF : KB 0 0 F) (hG : KB 0 0 G) :
    KB 0 0 (fun w n ζ => F w n ζ - G w n ζ) := by
  simpa using hF.sub hG

lemma mul0c {c d : ℝ} (hF : KB 0 0 F) (hG : KB c d G) :
    KB c d (fun w n ζ => F w n ζ * G w n ζ) :=
  KB.cast (by ring) (by ring) (hF.mul hG)

lemma mulc0 {c d : ℝ} (hF : KB c d F) (hG : KB 0 0 G) :
    KB c d (fun w n ζ => F w n ζ * G w n ζ) :=
  KB.cast (by ring) (by ring) (hF.mul hG)

lemma congr (h : KB c d F) (hFG : ∀ w n ζ, F w n ζ = G w n ζ) : KB c d G := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  exact ⟨C, N, hC, hN, fun w ζ n hn hw => by rw [← hFG w n ζ]; exact hb w ζ n hn hw⟩

end KB

/-! ## The `ζ`-atoms on the ball -/

lemma ept_pow_norm (k : ℕ) (ζ : ℍ) :
    ‖Work.Residues.Ept ζ‖ ^ k = Real.exp (-((k : ℝ) * Real.pi * ζ.im)) := by
  rw [Work.Residues.norm_Ept, ← Real.exp_nat_mul]
  congr 1; push_cast; ring

lemma KB.of_zeta_eptpow {C : ℝ} (hC : 0 < C) {k : ℕ} {f : ℍ → ℂ}
    (h : ∀ z : ℍ, 1 ≤ z.im → ‖f z‖ ≤ C * ‖Work.Residues.Ept z‖ ^ k) :
    KB 0 (-((k : ℝ) * Real.pi)) (fun _ _ ζ => f ζ) := by
  refine ⟨C, 0, hC, le_rfl, fun w ζ n hn hw => ?_⟩
  have hz : 1 ≤ ζ.im := le_trans (by norm_num) hw.him
  have h1 := h ζ hz
  have hgoal : C * (Work.Kernels.scale w) ^ (0 : ℝ)
      * Real.exp (0 * (ModularGroup.S • w).im + (-((k : ℝ) * Real.pi)) * ζ.im)
      = C * Real.exp (-((k : ℝ) * Real.pi * ζ.im)) := by
    have hthis : (-((k : ℝ) * Real.pi)) * ζ.im = -((k : ℝ) * Real.pi * ζ.im) := by ring
    rw [hthis, Real.rpow_zero, zero_mul, zero_add]
    ring
  rw [hgoal]
  rwa [ept_pow_norm k ζ] at h1

lemma KB.of_zeta_scale {C : ℝ} (hC : 0 < C) (m : ℕ) {f : ℍ → ℂ}
    (h : ∀ z : ℍ, 1 ≤ z.im → ‖f z‖ ≤ C * (1 + ‖(z : ℂ)‖) ^ m) :
    KB 0 0 (fun _ _ ζ => f ζ) := by
  refine ⟨C * (69 / 20 : ℝ) ^ m, (m : ℝ), by positivity, by positivity,
    fun w ζ n hn hw => ?_⟩
  have hz : 1 ≤ ζ.im := le_trans (by norm_num) hw.him
  have h1 := h ζ hz
  have hb := hw.norm_le_scaled
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := hw.one_le_scale
  have h2 : 1 + ‖(ζ : ℂ)‖ ≤ (69 / 20 : ℝ) * Work.Kernels.scale w := by linarith
  have h3 : (1 + ‖(ζ : ℂ)‖) ^ m
      ≤ ((69 / 20 : ℝ)) ^ m * (Work.Kernels.scale w) ^ m := by
    calc (1 + ‖(ζ : ℂ)‖) ^ m ≤ ((69 / 20 : ℝ) * Work.Kernels.scale w) ^ m :=
          pow_le_pow_left₀ (by positivity) h2 m
      _ = ((69 / 20 : ℝ)) ^ m * (Work.Kernels.scale w) ^ m := by rw [mul_pow]
  have hE : Real.exp (0 * (ModularGroup.S • w).im + 0 * ζ.im) = 1 := by
    rw [zero_mul, zero_mul, add_zero, Real.exp_zero]
  rw [hE, mul_one]
  refine le_trans h1 ?_
  calc C * (1 + ‖(ζ : ℂ)‖) ^ m
      ≤ C * (((69 / 20 : ℝ)) ^ m * (Work.Kernels.scale w) ^ m) :=
        mul_le_mul_of_nonneg_left h3 hC.le
    _ = C * (69 / 20 : ℝ) ^ m * (Work.Kernels.scale w) ^ (m : ℝ) := by
        rw [← Real.rpow_natCast (Work.Kernels.scale w) m]; ring


/-! ## The `τ`-atoms on the tiles -/

lemma tau_Delta (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n _ => Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := tile_tau_atoms ℓ
  exact ⟨C, N, hC, hN, fun w ζ n hn hw => by
    simpa only [zero_mul, add_zero, Real.exp_zero, mul_one] using (hb w n hn hw.hw).2.2.2.2.1⟩

lemma tau_E4 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n _ => Work.Kernels.E4Fun ((n : ℝ) +ᵥ w)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := tile_tau_atoms ℓ
  exact ⟨C, N, hC, hN, fun w ζ n hn hw => by
    simpa only [zero_mul, add_zero, Real.exp_zero, mul_one] using (hb w n hn hw.hw).1⟩

lemma tau_E6 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n _ => Work.Kernels.E6Fun ((n : ℝ) +ᵥ w)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := tile_tau_atoms ℓ
  exact ⟨C, N, hC, hN, fun w ζ n hn hw => by
    simpa only [zero_mul, add_zero, Real.exp_zero, mul_one] using (hb w n hn hw.hw).2.1⟩

lemma tau_E8 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n _ => Work.Kernels.E8Fun ((n : ℝ) +ᵥ w)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := tile_tau_atoms ℓ
  exact ⟨C, N, hC, hN, fun w ζ n hn hw => by
    simpa only [zero_mul, add_zero, Real.exp_zero, mul_one] using (hb w n hn hw.hw).2.2.1⟩

lemma tau_E10 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n _ => Work.Kernels.E10Fun ((n : ℝ) +ᵥ w)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := tile_tau_atoms ℓ
  exact ⟨C, N, hC, hN, fun w ζ n hn hw => by
    simpa only [zero_mul, add_zero, Real.exp_zero, mul_one] using (hb w n hn hw.hw).2.2.2.1⟩

lemma tau_p2 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := tile_tau_atoms ℓ
  exact ⟨C, N, hC, hN, fun w ζ n hn hw => by
    simpa only [zero_mul, add_zero, Real.exp_zero, mul_one]
      using (hb w n hn hw.hw).2.2.2.2.2.1⟩

lemma tau_p4 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := tile_tau_atoms ℓ
  exact ⟨C, N, hC, hN, fun w ζ n hn hw => by
    simpa only [zero_mul, add_zero, Real.exp_zero, mul_one]
      using (hb w n hn hw.hw).2.2.2.2.2.2.1⟩

lemma tau_j (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) 0
      (fun w n _ => Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := tile_tau_atoms ℓ
  exact ⟨C, N, hC, hN, fun w ζ n hn hw => by
    simpa only [zero_mul, add_zero, Real.exp_zero, mul_one]
      using (hb w n hn hw.hw).2.2.2.2.2.2.2.2⟩

lemma tau_invDelta (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) 0
      (fun w n _ => (Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w))⁻¹) := by
  obtain ⟨C, N, hC, hN, hb⟩ := tile_tau_atoms ℓ
  refine ⟨C, N, hC, hN, fun w ζ n hn hw => ?_⟩
  have h := (hb w n hn hw.hw).2.2.2.2.2.2.2.1
  simpa only [zero_mul, add_zero, Real.exp_zero, mul_one] using h

lemma tau_p2E10 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n _ => Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w)
      * Work.Kernels.E10Fun ((n : ℝ) +ᵥ w)) :=
  (tau_p2 ℓ).mul0 (tau_E10 ℓ)

lemma tau_p4E8 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)
      * Work.Kernels.E8Fun ((n : ℝ) +ᵥ w)) :=
  (tau_p4 ℓ).mul0 (tau_E8 ℓ)

lemma tau_jDelta (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n _ => Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
      * Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w)) := by
  exact KB.congr ((tau_E4 ℓ).mul0 ((tau_E4 ℓ).mul0 (tau_E4 ℓ)))
    (fun w n ζ => by
      have h := Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun ((n : ℝ) +ᵥ w)
      rw [mul_comm (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w))
        (Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w)), h]
      ring)

lemma tau_j2Delta (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) 0 (fun w n _ => Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) ^ 2
      * Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w)) := by
  refine KB.cast (c := 2 * Real.pi + 0) (d := 0 + 0) (by ring) (by ring) ?_
  exact KB.congr ((tau_j ℓ).mul (tau_jDelta ℓ)) (fun w n ζ => by ring)

lemma tau_jp2E10 (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) 0 (fun w n _ => Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
      * (Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w)
        * Work.Kernels.E10Fun ((n : ℝ) +ᵥ w))) :=
  KB.cast (by ring) (by ring) ((tau_j ℓ).mul (tau_p2E10 ℓ))

lemma tau_jp4E8 (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) 0 (fun w n _ => Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
      * (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)
        * Work.Kernels.E8Fun ((n : ℝ) +ᵥ w))) :=
  KB.cast (by ring) (by ring) ((tau_j ℓ).mul (tau_p4E8 ℓ))

/-! ## The sharp `ψ`-combination on the tiles -/

lemma psiCombo_sharp (ℓ : Work.Kernels.LogLambdaData) :
    KB (-Real.pi) 0
      (fun w n _ => Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)
          * Work.Kernels.E8Fun ((n : ℝ) +ᵥ w)
        - Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w)
          * Work.Kernels.E10Fun ((n : ℝ) +ᵥ w)) := by
  obtain ⟨CZ, NZ, hCZ, hNZ, hZb⟩ := Work.Asymptotics.EtailE.E_bdd_psi4E8_sub ℓ
  obtain ⟨CX, NX, hCX, hNX, hXb⟩ := E_bdd_Xfun
  have hCpos : (0 : ℝ) < CZ + Real.pi * CX := by
    have := mul_pos Real.pi_pos hCX; linarith
  refine ⟨CZ + Real.pi * CX, max NZ NX, hCpos, le_max_of_le_left hNZ,
    fun w ζ n hn hw => ?_⟩
  have hSnn : 0 ≤ (ModularGroup.S • w).im := Work.Asymptotics.EtailE.E_im_S_nonneg hw.hw
  have hsc1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hZbw := hZb w hw.hw
  have hXbw := hXb w hw.hw
  have hexpZ : Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im)
      ≤ Real.exp ((-Real.pi) * (ModularGroup.S • w).im) :=
    Real.exp_le_exp.mpr (by nlinarith [hSnn, Real.pi_pos])
  have hZ' : ‖psiCombo ℓ w‖ ≤ CZ * (Work.Kernels.scale w) ^ (max NZ NX)
      * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by
    refine le_trans hZbw ?_
    have h1 : CZ * (Work.Kernels.scale w) ^ NZ
        ≤ CZ * (Work.Kernels.scale w) ^ (max NZ NX) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hsc1 (le_max_left _ _)) hCZ.le
    exact mul_le_mul h1 hexpZ (Real.exp_pos _).le
      (mul_nonneg hCZ.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _))
  have hX' : ‖Work.Residues.Xfun w‖ ≤ CX * (Work.Kernels.scale w) ^ (max NZ NX)
      * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by
    refine le_trans hXbw ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hsc1 (le_max_right _ _)) hCX.le)
      (Real.exp_pos _).le
  have hcoc : psiCombo ℓ ((n : ℝ) +ᵥ w)
      = psiCombo ℓ w + (n : ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w) := by
    rcases hn with h | h
    · rw [h]; push_cast; rw [one_mul]; exact psiCombo_vadd_one ℓ w
    · rw [h]; push_cast; rw [neg_one_mul]; exact psiCombo_vadd_neg_one ℓ w
  have hcn : ‖(n : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast]; rcases hn with h | h <;> rw [h] <;> norm_num
  have hk : ‖(n : ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w)‖
      = Real.pi * ‖Work.Residues.Xfun w‖ := by
    rw [norm_mul, norm_mul, norm_mul, hcn, one_mul, Complex.norm_I, mul_one,
      Work.Asymptotics.EtailE.norm_pi]
  have hmain : ‖psiCombo ℓ ((n : ℝ) +ᵥ w)‖
      ≤ (CZ + Real.pi * CX) * (Work.Kernels.scale w) ^ (max NZ NX)
        * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by
    rw [hcoc]
    calc ‖psiCombo ℓ w + (n : ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w)‖
        ≤ ‖psiCombo ℓ w‖ + ‖(n : ℂ) * ((Real.pi : ℂ) * Complex.I * Work.Residues.Xfun w)‖ :=
          norm_add_le _ _
      _ ≤ CZ * (Work.Kernels.scale w) ^ (max NZ NX)
            * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)
          + Real.pi * (CX * (Work.Kernels.scale w) ^ (max NZ NX)
            * Real.exp ((-Real.pi) * (ModularGroup.S • w).im)) := by
          rw [hk]
          exact add_le_add hZ' (mul_le_mul_of_nonneg_left hX' Real.pi_pos.le)
      _ = (CZ + Real.pi * CX) * (Work.Kernels.scale w) ^ (max NZ NX)
            * Real.exp ((-Real.pi) * (ModularGroup.S • w).im) := by ring
  refine le_trans hmain (le_of_eq ?_)
  rw [zero_mul, add_zero]

lemma tau_jPsiCombo (ℓ : Work.Kernels.LogLambdaData) :
    KB Real.pi 0 (fun w n _ => Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
      * (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * Work.Kernels.E8Fun ((n : ℝ) +ᵥ w)
        - Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w)
          * Work.Kernels.E10Fun ((n : ℝ) +ᵥ w))) := by
  refine KB.cast (c := 2 * Real.pi + -Real.pi) (d := 0 + 0) (by ring) (by ring) ?_
  exact KB.congr ((tau_j ℓ).mul (psiCombo_sharp ℓ)) (fun w n ζ => by simp only [psiCombo])


/-! ## Helper: sums/subtractions with dominated exponents -/

namespace KB

variable {c d c' d' : ℝ} {F G : ℍ → ℤ → ℍ → ℂ}

lemma add_of_le {c d c' d' : ℝ} (hcd : c' ≤ c) (hdd : d' ≤ d)
    (hF : KB c d F) (hG : KB c' d' G) :
    KB c d (fun w n ζ => F w n ζ + G w n ζ) :=
  KB.cast (max_eq_left hcd) (max_eq_left hdd) (hF.add hG)

lemma sub_of_le {c d c' d' : ℝ} (hcd : c' ≤ c) (hdd : d' ≤ d)
    (hF : KB c d F) (hG : KB c' d' G) :
    KB c d (fun w n ζ => F w n ζ - G w n ζ) :=
  KB.cast (max_eq_left hcd) (max_eq_left hdd) (hF.sub hG)

/-- `KB.reduce` with the bound first (so the exponents are determined by it). -/
lemma reduce' {c d : ℝ} (h : KB c d F) (hd : d ≤ 0) (hcd : c + d ≤ 0) : KB 0 0 F :=
  reduce hd hcd h

/-- `KB.cast` with the bound first. -/
lemma castr {c d c' d' : ℝ} (h : KB c d F) (hc : c = c') (hd : d = d') : KB c' d' F :=
  cast hc hd h

/-- Product of a uniform bound with a `KB 0 d` bound, preserving both exponents. -/
lemma mul_00_0d' {d : ℝ} (hF : KB 0 0 F) (hG : KB 0 d G) :
    KB 0 d (fun w n ζ => F w n ζ * G w n ζ) := by
  have h := hF.mul hG
  simpa using h

/-- Product of a uniform bound with a `KB 0 d` bound (`d ≤ 0`), giving a uniform bound. -/
lemma mul_00_0d {d : ℝ} (hF : KB 0 0 F) (hG : KB 0 d G) (hd : d ≤ 0) :
    KB 0 0 (fun w n ζ => F w n ζ * G w n ζ) :=
  KB.reduce' (hF.mul hG) (by linarith) (by linarith)

end KB

/-! ## The `ζ`-atoms on the ball -/

lemma KB.of_zeta_eptinv2 {C : ℝ} (hC : 0 < C) {f : ℍ → ℂ}
    (h : ∀ z : ℍ, 1 ≤ z.im → ‖f z‖ ≤ C * (‖Work.Residues.Ept z‖ ^ 2)⁻¹) :
    KB 0 (2 * Real.pi) (fun _ _ ζ => f ζ) := by
  refine ⟨C, 0, hC, le_rfl, fun w ζ n hn hw => ?_⟩
  have hz : 1 ≤ ζ.im := le_trans (by norm_num) hw.him
  have h1 := h ζ hz
  have h2 : (‖Work.Residues.Ept ζ‖ ^ 2)⁻¹ = Real.exp (2 * Real.pi * ζ.im) := by
    rw [ept_pow_norm 2 ζ, ← Real.exp_neg]
    congr 1; ring
  rw [h2] at h1
  have hgoal : C * (Work.Kernels.scale w) ^ (0 : ℝ)
      * Real.exp (0 * (ModularGroup.S • w).im + (2 * Real.pi) * ζ.im)
      = C * Real.exp (2 * Real.pi * ζ.im) := by
    rw [Real.rpow_zero, zero_mul, zero_add]
    ring
  rw [hgoal]
  exact h1

lemma z_Ept_pow (k : ℕ) :
    KB 0 (-((k : ℝ) * Real.pi)) (fun _ _ ζ => (Work.Residues.Ept ζ) ^ k) := by
  refine KB.of_zeta_eptpow (C := 1) (k := k) (by norm_num) (f := fun ζ => (Work.Residues.Ept ζ) ^ k)
    (fun z hz => ?_)
  rw [norm_pow]
  simp

lemma z_dDelta (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (-(2 * Real.pi)) (fun _ _ ζ => Compact.dDelta ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_eptpow (C := C) (k := 2) hC (fun z hz => (hb z hz).1)

lemma z_dW (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (-(3 * Real.pi)) (fun _ _ ζ => Compact.dW ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_eptpow (C := C) (k := 3) hC (fun z hz => (hb z hz).2.1)

lemma z_dD2 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (-(3 * Real.pi)) (fun _ _ ζ => Compact.dD2 ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_eptpow (C := C) (k := 3) hC (fun z hz => (hb z hz).2.2.1)

lemma z_dL (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (-(3 * Real.pi)) (fun _ _ ζ => Compact.dL ℓ ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_eptpow (C := C) (k := 3) hC (fun z hz => (hb z hz).2.2.2.1)

lemma z_dE14 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (-(4 * Real.pi)) (fun _ _ ζ => Compact.dE14 ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_eptpow (C := C) (k := 4) hC (fun z hz => (hb z hz).2.2.2.2.1)

lemma z_dE10 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (-(4 * Real.pi)) (fun _ _ ζ => Compact.dE10 ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_eptpow (C := C) (k := 4) hC (fun z hz => (hb z hz).2.2.2.2.2.1)

lemma z_E4cubeDev (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (-(4 * Real.pi))
      (fun _ _ ζ => Work.Kernels.E4Fun ζ ^ 3 - Work.Asymptotics.kmfd_E4refc ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_eptpow (C := C) (k := 4) hC (fun z hz => (hb z hz).2.2.2.2.2.2.1)

lemma z_DeltaDev (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (-(4 * Real.pi))
      (fun _ _ ζ => Work.Kernels.DeltaFun ζ - (Work.Residues.Ept ζ) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_eptpow (C := C) (k := 4) hC (fun z hz => (hb z hz).2.2.2.2.2.2.2.1)

lemma z_jDev (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (-(2 * Real.pi))
      (fun _ _ ζ => Work.Kernels.jInvariantFun ζ - Work.Asymptotics.kmfd_jref ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_eptpow (C := C) (k := 2) hC (fun z hz => (hb z hz).2.2.2.2.2.2.2.2.1)

lemma z_L (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun _ _ ζ => ℓ.L ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_scale (C := C) hC 1 (fun z hz => by simpa using (hb z hz).2.2.2.2.2.2.2.2.2.1)

lemma z_W (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun _ _ ζ => Work.Kernels.WFun ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_scale (C := C) hC 0 (fun z hz => by simpa using (hb z hz).2.2.2.2.2.2.2.2.2.2.1)

lemma z_D2 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun _ _ ζ => Work.Kernels.UFun ζ ^ 2 - Work.Kernels.VFun ζ ^ 2) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_scale (C := C) hC 0 (fun z hz => by simpa using (hb z hz).2.2.2.2.2.2.2.2.2.2.2.1)

lemma z_E10ref (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun _ _ ζ => Compact.E10ref ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_scale (C := C) hC 0 (fun z hz => by simpa using (hb z hz).2.2.2.2.2.2.2.2.2.2.2.2.1)

lemma z_E14ref (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun _ _ ζ => Compact.E14ref ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_scale (C := C) hC 0 (fun z hz => by simpa using (hb z hz).2.2.2.2.2.2.2.2.2.2.2.2.2.1)

lemma z_Dref (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (2 * Real.pi) (fun _ _ ζ => Compact.Dref ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_eptinv2 (C := C) hC (fun z hz => (hb z hz).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

lemma z_jref (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (2 * Real.pi) (fun _ _ ζ => Work.Asymptotics.kmfd_jref ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_eptinv2 (C := C) hC (fun z hz => (hb z hz).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)

lemma z_E4refc (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun _ _ ζ => Work.Asymptotics.kmfd_E4refc ζ) := by
  obtain ⟨C, hC, hb⟩ := kmfd_zdevs ℓ
  exact KB.of_zeta_scale (C := C) hC 0 (fun z hz => by simpa using (hb z hz).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)

lemma z_Xc (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun _ _ ζ => Compact.Xc ℓ ζ) := by
  refine KB.of_zeta_scale (C := Real.pi + ‖Compact.cuspC ℓ‖) (by positivity) 1 (fun z hz => ?_)
  have h1 : ‖Compact.Xc ℓ z‖ ≤ Real.pi * ‖(z : ℂ)‖ + ‖Compact.cuspC ℓ‖ := by
    rw [Compact.Xc]
    refine le_trans (norm_add_le _ _) (le_of_eq ?_)
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have h2 : (0:ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
  have h3 : (0:ℝ) ≤ ‖Compact.cuspC ℓ‖ := norm_nonneg _
  calc ‖Compact.Xc ℓ z‖ ≤ Real.pi * ‖(z : ℂ)‖ + ‖Compact.cuspC ℓ‖ := h1
    _ ≤ (Real.pi + ‖Compact.cuspC ℓ‖) * (1 + ‖(z : ℂ)‖) ^ 1 := by
        rw [pow_one]; nlinarith [Real.pi_pos, h2, h3]

/-! ## Derived `ζ`-atoms -/

lemma z_E14 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun _ _ ζ => Work.Kernels.E14Fun ζ) :=
  KB.congr (KB.add_of_le (c := 0) (d := 0) (c' := 0) (d' := -(4 * Real.pi))
    (le_refl 0) (by linarith [Real.pi_pos]) (z_E14ref ℓ) (z_dE14 ℓ))
    (fun w n ζ => by rw [Compact.dE14]; ring)

lemma z_E10 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun _ _ ζ => Work.Kernels.E10Fun ζ) :=
  KB.congr (KB.add_of_le (c := 0) (d := 0) (c' := 0) (d' := -(4 * Real.pi))
    (le_refl 0) (by linarith [Real.pi_pos]) (z_E10ref ℓ) (z_dE10 ℓ))
    (fun w n ζ => by rw [Compact.dE10]; ring)

lemma z_E4cube (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun _ _ ζ => Work.Kernels.E4Fun ζ ^ 3) :=
  KB.congr (KB.add_of_le (c := 0) (d := 0) (c' := 0) (d' := -(4 * Real.pi))
    (le_refl 0) (by linarith [Real.pi_pos]) (z_E4refc ℓ) (z_E4cubeDev ℓ))
    (fun w n ζ => by ring)

lemma z_Delta (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (-(2 * Real.pi)) (fun _ _ ζ => Work.Kernels.DeltaFun ζ) :=
  KB.congr (KB.add_of_le (c := 0) (d := -(2 * Real.pi)) (c' := 0) (d' := -(4 * Real.pi))
    (le_refl 0) (by linarith [Real.pi_pos]) (z_Ept_pow 2) (z_DeltaDev ℓ))
    (fun w n ζ => by ring)

lemma z_j (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (2 * Real.pi) (fun _ _ ζ => Work.Kernels.jInvariantFun ζ) :=
  KB.congr (KB.add_of_le (c := 0) (d := 2 * Real.pi) (c' := 0) (d' := -(2 * Real.pi))
    (le_refl 0) (by linarith [Real.pi_pos]) (z_jref ℓ) (z_jDev ℓ))
    (fun w n ζ => by ring)

lemma z_invDelta (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (2 * Real.pi) (fun _ _ ζ => (Work.Kernels.DeltaFun ζ)⁻¹) :=
  KB.congr (KB.add_of_le (c := 0) (d := 2 * Real.pi) (c' := 0) (d' := -(2 * Real.pi))
    (le_refl 0) (by linarith [Real.pi_pos]) (z_Dref ℓ) (z_dDelta ℓ))
    (fun w n ζ => by rw [Compact.dDelta]; ring)


/-! ## The `K₋^{(24)}` bracket on the ball -/

/-- `Nf` is `O((scale w)^N)` on the tiles. -/
lemma kB_Nf (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have h1 : KB 0 0 (fun w n ζ => (-3456 : ℂ) * (DeltaFun ((n : ℝ) +ᵥ w) * Compact.Xc ℓ ζ)) :=
    KB.const_mul (-3456) (KB.reduce' ((tau_Delta ℓ).mul (z_Xc ℓ)) (by linarith) (by linarith))
  have h2 : KB 0 0 (fun w n ζ => (3456 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    KB.const_mul 3456 (tau_Delta ℓ)
  have h3 : KB 0 0 (fun w n ζ => (-3 : ℂ) * (psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w))) :=
    KB.const_mul (-3) (tau_p2E10 ℓ)
  have h4 : KB 0 0 (fun w n ζ => (3 : ℂ) * (psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))) :=
    KB.const_mul 3 (tau_p4E8 ℓ)
  exact KB.congr (((h1.add0 h2).add0 h3).add0 h4) (fun w n ζ => by rw [Compact.Nf]; ring)

/-- `Mf` is `O((scale w)^N e^{2π Im (S w)})` on the tiles. -/
lemma kB_Mf (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) 0 (fun w n ζ => Compact.Mf ℓ ((n : ℝ) +ᵥ w)) := by
  have hp2j : KB (2 * Real.pi) 0 (fun w n ζ => (psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w)) * jInvariantFun ((n : ℝ) +ᵥ w)) :=
    KB.congr (tau_jp2E10 ℓ) (fun w n ζ => by ring)
  have hp4j : KB (2 * Real.pi) 0 (fun w n ζ => (psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w)) * jInvariantFun ((n : ℝ) +ᵥ w)) :=
    KB.congr (tau_jp4E8 ℓ) (fun w n ζ => by ring)
  have h1 : KB (2 * Real.pi) 0 (fun w n ζ => (3 : ℂ) * ((psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w)) * jInvariantFun ((n : ℝ) +ᵥ w))) := KB.const_mul 3 hp2j
  have h2 : KB (2 * Real.pi) 0 (fun w n ζ => (-3 : ℂ) * ((psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w)) * jInvariantFun ((n : ℝ) +ᵥ w))) := KB.const_mul (-3) hp4j
  have h3 : KB 0 0 (fun w n ζ => (-41472 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    KB.const_mul _ (tau_Delta ℓ)
  have h4 : KB 0 0 (fun w n ζ => (3456 * 768 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    KB.const_mul _ (tau_Delta ℓ)
  have h5 : KB 0 0 (fun w n ζ => (-3456 : ℂ) * (DeltaFun ((n : ℝ) +ᵥ w)
      * jInvariantFun ((n : ℝ) +ᵥ w))) :=
    KB.const_mul _ (KB.congr (tau_jDelta ℓ) (fun w n ζ => by ring))
  have h6 : KB 0 0 (fun w n ζ => (-1152 : ℂ) * (psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p2E10 ℓ)
  have h7 : KB 0 0 (fun w n ζ => (2880 : ℂ) * (psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p4E8 ℓ)
  have hA := KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 2 * Real.pi) (d' := 0)
    (le_refl _) (le_refl _) h1 h2
  have hB := KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 0) (d' := 0)
    (by positivity) (le_refl 0) hA h3
  have hC := KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 0) (d' := 0)
    (by positivity) (le_refl 0) hB h4
  have hD := KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 0) (d' := 0)
    (by positivity) (le_refl 0) hC h5
  have hE := KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 0) (d' := 0)
    (by positivity) (le_refl 0) hD h6
  have hF := KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 0) (d' := 0)
    (by positivity) (le_refl 0) hE h7
  exact KB.congr hF (fun w n ζ => by rw [Compact.Mf]; ring)

/-- `A₂₄` is `O((scale w)^N)` on the tiles. -/
lemma kB_A24 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Compact.A24 ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have h1 : KB 0 0 (fun w n ζ => (-3456 : ℂ) * (DeltaFun ((n : ℝ) +ᵥ w)
      * (E14Fun ζ * ℓ.L ζ))) :=
    KB.const_mul (-3456) (KB.mul0 (tau_Delta ℓ) (KB.mul0 (z_E14 ℓ) (z_L ℓ)))
  have h2 : KB 0 0 (fun w n ζ => (-1 : ℂ) * ((psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w) - psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))
        * (E10Fun ζ * (UFun ζ ^ 2 - VFun ζ ^ 2)))) :=
    KB.const_mul (-1) (KB.mul0 ((tau_p2E10 ℓ).sub0 (tau_p4E8 ℓ))
      (KB.mul0 (z_E10 ℓ) (z_D2 ℓ)))
  exact KB.congr (h1.add0 h2) (fun w n ζ => by rw [Compact.A24]; ring)

/-- `B₂₄` is `O((scale w)^N)`. -/
lemma kB_B24 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Compact.B24 ℓ ((n : ℝ) +ᵥ w)) := by
  have h1 : KB 0 0 (fun w n ζ => (-3456 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    KB.const_mul (-3456) (tau_Delta ℓ)
  have h2 : KB 0 0 (fun w n ζ => (2 : ℂ) * (psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w))) := KB.const_mul 2 (tau_p2E10 ℓ)
  have h3 : KB 0 0 (fun w n ζ => (-2 : ℂ) * (psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w))) := KB.const_mul (-2) (tau_p4E8 ℓ)
  exact KB.congr ((h1.add0 h2).add0 h3) (fun w n ζ => by rw [Compact.B24]; ring)

/-- `1728 - j(n +ᵥ w)` is `O((scale w)^N e^{2π Im (S w)})`. -/
lemma kB_1728_sub_j (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) 0 (fun w n ζ => (1728 : ℂ) - jInvariantFun ((n : ℝ) +ᵥ w)) :=
  KB.castr ((KB.const (1728 : ℂ)).sub (tau_j ℓ))
    (by rw [max_eq_right]; positivity) (by rw [max_eq_left]; norm_num)

/-- `(ψ₂E₁₀)(τ)·j(τ)` is `O((scale w)^N e^{2π Im (S w)})`. -/
lemma kB_p2E10_j (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) 0 (fun w n ζ => (psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w)) * jInvariantFun ((n : ℝ) +ᵥ w)) :=
  KB.congr (tau_jp2E10 ℓ) (fun w n ζ => by ring)

/-- `(ψ₄E₈)(τ)·j(τ)` is `O((scale w)^N e^{2π Im (S w)})`. -/
lemma kB_p4E8_j (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) 0 (fun w n ζ => (psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w)) * jInvariantFun ((n : ℝ) +ᵥ w)) :=
  KB.congr (tau_jp4E8 ℓ) (fun w n ζ => by ring)

/-- `C₂₄` is `O((scale w)^N e^{2π Im (S w)})`. -/
lemma kB_C24 (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) 0 (fun w n ζ => Compact.C24 ℓ ((n : ℝ) +ᵥ w)) := by
  have h1 : KB (2 * Real.pi) 0 (fun w n ζ => (psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w)) * jInvariantFun ((n : ℝ) +ᵥ w)) := kB_p2E10_j ℓ
  have h2 : KB (2 * Real.pi) 0 (fun w n ζ => (psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w)) * ((1728 : ℂ) - jInvariantFun ((n : ℝ) +ᵥ w))) :=
    KB.castr ((tau_p4E8 ℓ).mul (kB_1728_sub_j ℓ)) (by ring) (by ring)
  exact KB.congr (KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 2 * Real.pi) (d' := 0)
    (le_refl _) (le_refl _) h1 h2) (fun w n ζ => by rw [Compact.C24])

/-- `kmfd_dA` is `O((scale w)^N)` on the tiles. -/
lemma kB_dA (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (-(3 * Real.pi)) (fun w n ζ => Work.Asymptotics.kmfd_dA ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have hL : KB 0 (-(4 * Real.pi)) (fun _ _ ζ => Compact.dE14 ζ * ℓ.L ζ) :=
    KB.castr ((z_dE14 ℓ).mul (z_L ℓ)) (by ring) (by ring)
  have hL2 : KB 0 (-(3 * Real.pi)) (fun _ _ ζ => Compact.E14ref ζ * Compact.dL ℓ ζ) :=
    KB.castr ((z_E14ref ℓ).mul (z_dL ℓ)) (by ring) (by ring)
  have hsum1 : KB 0 (-(3 * Real.pi)) (fun _ _ ζ => Compact.E14ref ζ * Compact.dL ℓ ζ
      + Compact.dE14 ζ * ℓ.L ζ) :=
    KB.add_of_le (c := 0) (d := -(3 * Real.pi)) (c' := 0) (d' := -(4 * Real.pi))
      (le_refl 0) (by linarith [Real.pi_pos]) hL2 hL
  have h1 : KB 0 (-(3 * Real.pi)) (fun w n ζ => (-3456 : ℂ) * (DeltaFun ((n : ℝ) +ᵥ w)
      * (Compact.E14ref ζ * Compact.dL ℓ ζ + Compact.dE14 ζ * ℓ.L ζ))) :=
    KB.const_mul (-3456) (KB.mul_00_0d' (tau_Delta ℓ) hsum1)
  have hD2 : KB 0 (-(4 * Real.pi)) (fun _ _ ζ => Compact.dE10 ζ * (UFun ζ ^ 2 - VFun ζ ^ 2)) :=
    KB.castr ((z_dE10 ℓ).mul (z_D2 ℓ)) (by ring) (by ring)
  have hD2b : KB 0 (-(3 * Real.pi)) (fun _ _ ζ => Compact.E10ref ζ * Compact.dD2 ζ) :=
    KB.castr ((z_E10ref ℓ).mul (z_dD2 ℓ)) (by ring) (by ring)
  have hsum2 : KB 0 (-(3 * Real.pi)) (fun _ _ ζ => Compact.E10ref ζ * Compact.dD2 ζ
      + Compact.dE10 ζ * (UFun ζ ^ 2 - VFun ζ ^ 2)) :=
    KB.add_of_le (c := 0) (d := -(3 * Real.pi)) (c' := 0) (d' := -(4 * Real.pi))
      (le_refl 0) (by linarith [Real.pi_pos]) hD2b hD2
  have h2 : KB 0 (-(3 * Real.pi)) (fun w n ζ => (-1 : ℂ) * ((psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w) - psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w))
        * (Compact.E10ref ζ * Compact.dD2 ζ
          + Compact.dE10 ζ * (UFun ζ ^ 2 - VFun ζ ^ 2)))) :=
    KB.const_mul (-1) (KB.mul_00_0d' ((tau_p2E10 ℓ).sub0 (tau_p4E8 ℓ)) hsum2)
  exact KB.congr (KB.add_of_le (c := 0) (d := -(3 * Real.pi)) (c' := 0) (d' := -(3 * Real.pi))
    (le_refl 0) (le_refl _) h1 h2) (fun w n ζ => by
      rw [Work.Asymptotics.kmfd_dA]; ring)

/-- `kmfd_dSh` is `O((scale w)^N e^{2π Im (S w)} e^{-4π Im ζ})`. -/
lemma kB_dSh (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) (-(4 * Real.pi))
      (fun w n ζ => Work.Asymptotics.kmfd_dSh ((n : ℝ) +ᵥ w) ζ) := by
  have h1 : KB 0 (-(4 * Real.pi)) (fun w n ζ => Work.Kernels.E4Fun ζ ^ 3
      - Work.Asymptotics.kmfd_E4refc ζ) := z_E4cubeDev ℓ
  have h2 : KB (2 * Real.pi) (-(4 * Real.pi)) (fun w n ζ => jInvariantFun ((n : ℝ) +ᵥ w)
      * (Work.Kernels.DeltaFun ζ - (Work.Residues.Ept ζ) ^ 2)) :=
    KB.castr ((tau_j ℓ).mul (z_DeltaDev ℓ)) (by ring) (by ring)
  refine KB.congr (KB.castr (h1.sub h2) (by rw [max_eq_right]; positivity)
    (by rw [max_self])) ?_
  intro w n ζ
  rw [Work.Asymptotics.kmfd_dSh]

/-- `einv2` is `O(e^{2π Im ζ})`. -/
lemma z_einv2 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (2 * Real.pi) (fun _ _ ζ => Compact.einv2 ζ) := by
  refine KB.of_zeta_eptinv2 (C := 1) (by norm_num) (fun z hz => ?_)
  rw [Compact.einv2, norm_pow, norm_inv, inv_pow]
  simp

/-- `br0 24` is `O((scale w)^N e^{2π Im (S w)} e^{2π Im ζ})`. -/
lemma kB_br0_24 (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) (2 * Real.pi)
      (fun w n ζ => Compact.br0 24 ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have h1 : KB 0 (2 * Real.pi) (fun w n ζ => - Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ
      * Compact.einv2 ζ) :=
    KB.castr ((KB.congr (KB.const_mul (-1) (kB_Nf ℓ)) (fun w n ζ => by ring)).mul
      (z_einv2 ℓ)) (by ring) (by ring)
  have hjNf : KB (2 * Real.pi) 0 (fun w n ζ => jInvariantFun ((n : ℝ) +ᵥ w)
      * Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.castr ((tau_j ℓ).mul (kB_Nf ℓ)) (by ring) (by ring)
  have h2 : KB (2 * Real.pi) 0 (fun w n ζ => - Compact.Mf ℓ ((n : ℝ) +ᵥ w)) :=
    KB.congr (KB.const_mul (-1) (kB_Mf ℓ)) (fun w n ζ => by ring)
  have h3 : KB 0 0 (fun w n ζ => (720 : ℂ) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.const_mul 720 (kB_Nf ℓ)
  have h4 : KB (2 * Real.pi) 0 (fun w n ζ => - jInvariantFun ((n : ℝ) +ᵥ w)
      * Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.congr (KB.const_mul (-1) hjNf) (fun w n ζ => by ring)
  have h5 : KB (2 * Real.pi) 0 (fun w n ζ => - Compact.Mf ℓ ((n : ℝ) +ᵥ w)
      + (- jInvariantFun ((n : ℝ) +ᵥ w) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ
        + (720 : ℂ) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ)) :=
    KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 2 * Real.pi) (d' := 0)
      (le_refl _) (le_refl _) h2
      (KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 0) (d' := 0)
        (by positivity) (le_refl 0) h4 h3)
  refine KB.congr (KB.castr (h5.add h1) (by rw [max_eq_left]; positivity)
    (by rw [max_eq_right]; positivity)) ?_
  intro w n ζ
  rw [Compact.br0_24]
  ring_nf

/-! ## The coefficients `kmfd_c1, …, kmfd_c8` -/

lemma kB_c1 (ℓ : Work.Kernels.LogLambdaData) :
    KB Real.pi 0 (fun w n ζ => Work.Asymptotics.kmfd_c1 ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have h0 : KB Real.pi 0 (fun w n ζ => (24 : ℂ) * (jInvariantFun ((n : ℝ) +ᵥ w)
      * psiCombo ℓ ((n : ℝ) +ᵥ w))) := KB.const_mul 24 (tau_jPsiCombo ℓ)
  have h1 : KB 0 0 (fun w n ζ => (27648 : ℂ) * (jInvariantFun ((n : ℝ) +ᵥ w)
      * DeltaFun ((n : ℝ) +ᵥ w))) := KB.const_mul 27648 (tau_jDelta ℓ)
  have h2 : KB 0 0 (fun w n ζ => (-20570112 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    KB.const_mul _ (tau_Delta ℓ)
  have h3 : KB 0 0 (fun w n ζ => (15744 : ℂ) * (psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p2E10 ℓ)
  have h4 : KB 0 0 (fun w n ζ => (-29568 : ℂ) * (psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p4E8 ℓ)
  have h01 := KB.add_of_le (c := Real.pi) (d := 0) (c' := 0) (d' := 0) (by positivity)
    (le_refl 0) h0 h1
  have h012 := KB.add_of_le (c := Real.pi) (d := 0) (c' := 0) (d' := 0) (by positivity)
    (le_refl 0) h01 h2
  have h0123 := KB.add_of_le (c := Real.pi) (d := 0) (c' := 0) (d' := 0) (by positivity)
    (le_refl 0) h012 h3
  exact KB.congr (KB.add_of_le (c := Real.pi) (d := 0) (c' := 0) (d' := 0) (by positivity)
    (le_refl 0) h0123 h4) (fun w n ζ => by
      simp only [Work.Asymptotics.kmfd_c1, psiCombo]; ring)

lemma kB_c2 (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) 0 (fun w n ζ => Work.Asymptotics.kmfd_c2 ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have h1 : KB (2 * Real.pi) 0 (fun w n ζ => (-3456 : ℂ) * (Compact.Xc ℓ ζ
      * (jInvariantFun ((n : ℝ) +ᵥ w) ^ 2 * DeltaFun ((n : ℝ) +ᵥ w)))) :=
    KB.const_mul (-3456) (KB.castr ((z_Xc ℓ).mul (tau_j2Delta ℓ)) (by ring) (by ring))
  have h2 : KB 0 0 (fun w n ζ => (4976640 : ℂ) * (Compact.Xc ℓ ζ
      * (jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)))) :=
    KB.const_mul _ ((z_Xc ℓ).mul0c (tau_jDelta ℓ))
  have h3 : KB 0 0 (fun w n ζ => (-1192402944 : ℂ)
      * (Compact.Xc ℓ ζ * DeltaFun ((n : ℝ) +ᵥ w))) :=
    KB.const_mul _ ((z_Xc ℓ).mul0c (tau_Delta ℓ))
  have h4 : KB (2 * Real.pi) 0 (fun w n ζ => (41472 : ℂ) * (jInvariantFun ((n : ℝ) +ᵥ w)
      * DeltaFun ((n : ℝ) +ᵥ w))) :=
    KB.const_mul _ (KB.castr ((tau_j ℓ).mul (tau_Delta ℓ)) (by ring) (by ring))
  have h5 : KB (2 * Real.pi) 0 (fun w n ζ => (1080 : ℂ) * (jInvariantFun ((n : ℝ) +ᵥ w)
      * (psi2 ℓ ((n : ℝ) +ᵥ w) * E10Fun ((n : ℝ) +ᵥ w)))) :=
    KB.const_mul _ (tau_jp2E10 ℓ)
  have h6 : KB (2 * Real.pi) 0 (fun w n ζ => (648 : ℂ) * (jInvariantFun ((n : ℝ) +ᵥ w)
      * (psi4 ℓ ((n : ℝ) +ᵥ w) * E8Fun ((n : ℝ) +ᵥ w)))) :=
    KB.const_mul _ (tau_jp4E8 ℓ)
  have h7 : KB 0 0 (fun w n ζ => (31850496 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    KB.const_mul _ (tau_Delta ℓ)
  have h8 : KB 0 0 (fun w n ζ => (-651456 : ℂ) * (psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p2E10 ℓ)
  have h9 : KB 0 0 (fun w n ζ => (-551232 : ℂ) * (psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p4E8 ℓ)
  have a1 := KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 0) (d' := 0)
    (by positivity) (le_refl 0) h1 h2
  have a2 := KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 0) (d' := 0)
    (by positivity) (le_refl 0) a1 h3
  have a3 := KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 2 * Real.pi) (d' := 0)
    (le_refl _) (le_refl _) a2 h4
  have a4 := KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 2 * Real.pi) (d' := 0)
    (le_refl _) (le_refl _) a3 h5
  have a5 := KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 2 * Real.pi) (d' := 0)
    (le_refl _) (le_refl _) a4 h6
  have a6 := KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 0) (d' := 0)
    (by positivity) (le_refl 0) a5 h7
  have a7 := KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 0) (d' := 0)
    (by positivity) (le_refl 0) a6 h8
  exact KB.congr (KB.add_of_le (c := 2 * Real.pi) (d := 0) (c' := 0) (d' := 0)
    (by positivity) (le_refl 0) a7 h9) (fun w n ζ => by simp only [Work.Asymptotics.kmfd_c2]; ring)

lemma kB_c3 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Work.Asymptotics.kmfd_c3 ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have h1 : KB 0 0 (fun w n ζ => (-5271257088 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    KB.const_mul _ (tau_Delta ℓ)
  have h2 : KB 0 0 (fun w n ζ => (3142656 : ℂ) * (psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p2E10 ℓ)
  have h3 : KB 0 0 (fun w n ζ => (-3142656 : ℂ) * (psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p4E8 ℓ)
  exact KB.congr ((h1.add0 h2).add0 h3) (fun w n ζ => by
    simp only [Work.Asymptotics.kmfd_c3]; ring)

lemma kB_c4 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Work.Asymptotics.kmfd_c4 ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have h1 : KB 0 0 (fun w n ζ => (597196800 : ℂ) * (Compact.Xc ℓ ζ
      * (jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)))) :=
    KB.const_mul _ ((z_Xc ℓ).mul0c (tau_jDelta ℓ))
  have h2 : KB 0 0 (fun w n ζ => (-382205952000 : ℂ)
      * (Compact.Xc ℓ ζ * DeltaFun ((n : ℝ) +ᵥ w))) :=
    KB.const_mul _ ((z_Xc ℓ).mul0c (tau_Delta ℓ))
  have h3 : KB 0 0 (fun w n ζ => (8623521792 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    KB.const_mul _ (tau_Delta ℓ)
  have h4 : KB 0 0 (fun w n ζ => (-178689024 : ℂ) * (psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p2E10 ℓ)
  have h5 : KB 0 0 (fun w n ζ => (-119909376 : ℂ) * (psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p4E8 ℓ)
  exact KB.congr ((((h1.add0 h2).add0 h3).add0 h4).add0 h5)
    (fun w n ζ => by simp only [Work.Asymptotics.kmfd_c4]; ring)

lemma kB_c5 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Work.Asymptotics.kmfd_c5 ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have h1 : KB 0 0 (fun w n ζ => (-496867737600 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    KB.const_mul _ (tau_Delta ℓ)
  have h2 : KB 0 0 (fun w n ζ => (287539200 : ℂ) * (psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p2E10 ℓ)
  have h3 : KB 0 0 (fun w n ζ => (-287539200 : ℂ) * (psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p4E8 ℓ)
  exact KB.congr ((h1.add0 h2).add0 h3) (fun w n ζ => by
    simp only [Work.Asymptotics.kmfd_c5]; ring)

lemma kB_c6 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Work.Asymptotics.kmfd_c6 ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have h1 : KB 0 0 (fun w n ζ => (47775744000 : ℂ) * (Compact.Xc ℓ ζ
      * (jInvariantFun ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)))) :=
    KB.const_mul _ ((z_Xc ℓ).mul0c (tau_jDelta ℓ))
  have h2 : KB 0 0 (fun w n ζ => (-34398535680000 : ℂ)
      * (Compact.Xc ℓ ζ * DeltaFun ((n : ℝ) +ᵥ w))) :=
    KB.const_mul _ ((z_Xc ℓ).mul0c (tau_Delta ℓ))
  have h3 : KB 0 0 (fun w n ζ => (917294284800 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    KB.const_mul _ (tau_Delta ℓ)
  have h4 : KB 0 0 (fun w n ζ => (-15460761600 : ℂ) * (psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p2E10 ℓ)
  have h5 : KB 0 0 (fun w n ζ => (-8427110400 : ℂ) * (psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p4E8 ℓ)
  exact KB.congr ((((h1.add0 h2).add0 h3).add0 h4).add0 h5)
    (fun w n ζ => by simp only [Work.Asymptotics.kmfd_c6]; ring)

lemma kB_c7 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Work.Asymptotics.kmfd_c7 ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have h1 : KB 0 0 (fun w n ζ => (-9172942848000 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    KB.const_mul _ (tau_Delta ℓ)
  have h2 : KB 0 0 (fun w n ζ => (5308416000 : ℂ) * (psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p2E10 ℓ)
  have h3 : KB 0 0 (fun w n ζ => (-5308416000 : ℂ) * (psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p4E8 ℓ)
  exact KB.congr ((h1.add0 h2).add0 h3) (fun w n ζ => by
    simp only [Work.Asymptotics.kmfd_c7]; ring)

lemma kB_c8 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Work.Asymptotics.kmfd_c8 ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have h1 : KB 0 0 (fun w n ζ => (27518828544000 : ℂ) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    KB.const_mul _ (tau_Delta ℓ)
  have h2 : KB 0 0 (fun w n ζ => (-15925248000 : ℂ) * (psi2 ℓ ((n : ℝ) +ᵥ w)
      * E10Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p2E10 ℓ)
  have h3 : KB 0 0 (fun w n ζ => (15925248000 : ℂ) * (psi4 ℓ ((n : ℝ) +ᵥ w)
      * E8Fun ((n : ℝ) +ᵥ w))) := KB.const_mul _ (tau_p4E8 ℓ)
  exact KB.congr ((h1.add0 h2).add0 h3) (fun w n ζ => by
    simp only [Work.Asymptotics.kmfd_c8]; ring)

/-- The reference bracket `kmfd_BR` is `O((scale w)^N)`. -/
lemma kB_BR (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Work.Asymptotics.kmfd_BR ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have h1 : KB 0 0 (fun w n ζ => (Work.Residues.Ept ζ) ^ 1
      * Work.Asymptotics.kmfd_c1 ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.reduce' ((z_Ept_pow 1).mul (kB_c1 ℓ)) (by push_cast; linarith [Real.pi_pos])
      (by push_cast; linarith [Real.pi_pos])
  have h2 : KB 0 0 (fun w n ζ => (Work.Residues.Ept ζ) ^ 2
      * Work.Asymptotics.kmfd_c2 ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.reduce' ((z_Ept_pow 2).mul (kB_c2 ℓ)) (by push_cast; linarith [Real.pi_pos])
      (by push_cast; linarith [Real.pi_pos])
  have h3 : KB 0 0 (fun w n ζ => (Work.Residues.Ept ζ) ^ 3
      * Work.Asymptotics.kmfd_c3 ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.reduce' ((z_Ept_pow 3).mul (kB_c3 ℓ)) (by push_cast; linarith [Real.pi_pos])
      (by push_cast; linarith [Real.pi_pos])
  have h4 : KB 0 0 (fun w n ζ => (Work.Residues.Ept ζ) ^ 4
      * Work.Asymptotics.kmfd_c4 ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.reduce' ((z_Ept_pow 4).mul (kB_c4 ℓ)) (by push_cast; linarith [Real.pi_pos])
      (by push_cast; linarith [Real.pi_pos])
  have h5 : KB 0 0 (fun w n ζ => (Work.Residues.Ept ζ) ^ 5
      * Work.Asymptotics.kmfd_c5 ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.reduce' ((z_Ept_pow 5).mul (kB_c5 ℓ)) (by push_cast; linarith [Real.pi_pos])
      (by push_cast; linarith [Real.pi_pos])
  have h6 : KB 0 0 (fun w n ζ => (Work.Residues.Ept ζ) ^ 6
      * Work.Asymptotics.kmfd_c6 ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.reduce' ((z_Ept_pow 6).mul (kB_c6 ℓ)) (by push_cast; linarith [Real.pi_pos])
      (by push_cast; linarith [Real.pi_pos])
  have h7 : KB 0 0 (fun w n ζ => (Work.Residues.Ept ζ) ^ 7
      * Work.Asymptotics.kmfd_c7 ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.reduce' ((z_Ept_pow 7).mul (kB_c7 ℓ)) (by push_cast; linarith [Real.pi_pos])
      (by push_cast; linarith [Real.pi_pos])
  have h8 : KB 0 0 (fun w n ζ => (Work.Residues.Ept ζ) ^ 8
      * Work.Asymptotics.kmfd_c8 ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.reduce' ((z_Ept_pow 8).mul (kB_c8 ℓ)) (by push_cast; linarith [Real.pi_pos])
      (by push_cast; linarith [Real.pi_pos])
  exact KB.congr (((((((h1.add0 h2).add0 h3).add0 h4).add0 h5).add0 h6).add0 h7).add0 h8)
    (fun w n ζ => by rw [Work.Asymptotics.kmfd_BR_expansion]; ring)


/-- The `j(τ)(Δ(z) - E(z)²)` term of `kmfd_dSh`. -/
lemma kB_dShB (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) (-(4 * Real.pi)) (fun w n ζ => jInvariantFun ((n : ℝ) +ᵥ w)
      * (Work.Kernels.DeltaFun ζ - (Work.Residues.Ept ζ) ^ 2)) :=
  KB.castr ((tau_j ℓ).mul (z_DeltaDev ℓ)) (by ring) (by ring)

/-- The deviation of the `K₋^{(24)}` bracket from its main part is `O((scale w)^N)`. -/
lemma kB_dev (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Work.Asymptotics.kmfd_dev ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have hNf := kB_Nf ℓ
  have hMf := kB_Mf ℓ
  have hEinv := z_einv2 ℓ
  have hW := z_W ℓ
  have hB24 := kB_B24 ℓ
  have hA24 := kB_A24 ℓ
  have hDref := z_Dref ℓ
  have hC24 := kB_C24 ℓ
  have hdA := kB_dA ℓ
  have hdW := z_dW ℓ
  have hjDev := z_jDev ℓ
  have hjτ := tau_j ℓ
  have hjref := z_jref ℓ
  have hA := z_E4cubeDev ℓ
  have hB := kB_dShB ℓ
  -- the `Dref * dA` term
  have t1 : KB 0 0 (fun w n ζ => Compact.Dref ζ * Work.Asymptotics.kmfd_dA ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.reduce' (hDref.mul hdA) (by linarith only [Real.pi_pos])
      (by linarith only [Real.pi_pos])
  have t2 : KB 0 0 (fun w n ζ => Compact.dDelta ζ * Compact.A24 ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.reduce' ((z_dDelta ℓ).mul hA24) (by linarith only [Real.pi_pos])
      (by linarith only [Real.pi_pos])
  have t3 : KB 0 0 (fun w n ζ => Compact.C24 ℓ ((n : ℝ) +ᵥ w) * Compact.dW ζ) :=
    KB.reduce' (hC24.mul hdW) (by linarith only [Real.pi_pos]) (by linarith only [Real.pi_pos])
  have t4 : KB 0 0 (fun w n ζ => jInvariantFun ((n : ℝ) +ᵥ w) * (Compact.dW ζ
      * Compact.B24 ℓ ((n : ℝ) +ᵥ w))) :=
    KB.reduce' (hjτ.mul (hdW.mul hB24)) (by linarith only [Real.pi_pos])
      (by linarith only [Real.pi_pos])
  have t5 : KB 0 0 (fun w n ζ => Work.Asymptotics.kmfd_jref ζ * (Compact.dW ζ
      * Compact.B24 ℓ ((n : ℝ) +ᵥ w))) :=
    KB.reduce' (hjref.mul (hdW.mul hB24)) (by linarith only [Real.pi_pos])
      (by linarith only [Real.pi_pos])
  have t6 : KB 0 0 (fun w n ζ => (jInvariantFun ζ - Work.Asymptotics.kmfd_jref ζ)
      * (Work.Kernels.WFun ζ * Compact.B24 ℓ ((n : ℝ) +ᵥ w))) :=
    KB.reduce' (hjDev.mul (hW.mul0 hB24)) (by linarith only [Real.pi_pos])
      (by linarith only [Real.pi_pos])
  -- the eight monomials of `kmfd_dSh * br0_24`
  have hNfE : KB 0 (2 * Real.pi) (fun w n ζ => Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ
      * Compact.einv2 ζ) := KB.castr (hNf.mul hEinv) (by ring) (by ring)
  have hNfγ : KB (2 * Real.pi) 0 (fun w n ζ => jInvariantFun ((n : ℝ) +ᵥ w)
      * Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.castr (hjτ.mul hNf) (by ring) (by ring)
  have hN7 : KB 0 0 (fun w n ζ => (720 : ℂ) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ) :=
    KB.const_mul 720 hNf
  have u1 : KB 0 0 (fun w n ζ => (Work.Kernels.E4Fun ζ ^ 3
      - Work.Asymptotics.kmfd_E4refc ζ) * (Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ
        * Compact.einv2 ζ)) :=
    KB.reduce' (hA.mul hNfE) (by linarith only [Real.pi_pos])
      (by linarith only [Real.pi_pos])
  have u2 : KB 0 0 (fun w n ζ => (Work.Kernels.E4Fun ζ ^ 3
      - Work.Asymptotics.kmfd_E4refc ζ) * Compact.Mf ℓ ((n : ℝ) +ᵥ w)) :=
    KB.reduce' (hA.mul hMf) (by linarith only [Real.pi_pos])
      (by linarith only [Real.pi_pos])
  have u3 : KB 0 0 (fun w n ζ => (Work.Kernels.E4Fun ζ ^ 3
      - Work.Asymptotics.kmfd_E4refc ζ) * ((720 : ℂ) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ)) :=
    KB.reduce' (hA.mul hN7) (by linarith only [Real.pi_pos]) (by linarith only [Real.pi_pos])
  have u4 : KB 0 0 (fun w n ζ => (Work.Kernels.E4Fun ζ ^ 3
      - Work.Asymptotics.kmfd_E4refc ζ) * (jInvariantFun ((n : ℝ) +ᵥ w)
        * Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ)) :=
    KB.reduce' (hA.mul hNfγ) (by linarith only [Real.pi_pos])
      (by linarith only [Real.pi_pos])
  have u5 : KB 0 0 (fun w n ζ => (jInvariantFun ((n : ℝ) +ᵥ w)
      * (Work.Kernels.DeltaFun ζ - (Work.Residues.Ept ζ) ^ 2))
        * (Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ * Compact.einv2 ζ)) :=
    KB.reduce' (hB.mul hNfE) (by linarith only [Real.pi_pos])
      (by linarith only [Real.pi_pos])
  have u6 : KB 0 0 (fun w n ζ => (jInvariantFun ((n : ℝ) +ᵥ w)
      * (Work.Kernels.DeltaFun ζ - (Work.Residues.Ept ζ) ^ 2))
        * Compact.Mf ℓ ((n : ℝ) +ᵥ w)) :=
    KB.reduce' (hB.mul hMf) (by linarith only [Real.pi_pos])
      (by linarith only [Real.pi_pos])
  have u7 : KB 0 0 (fun w n ζ => (jInvariantFun ((n : ℝ) +ᵥ w)
      * (Work.Kernels.DeltaFun ζ - (Work.Residues.Ept ζ) ^ 2))
        * ((720 : ℂ) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ)) :=
    KB.reduce' (hB.mul hN7) (by linarith only [Real.pi_pos])
      (by linarith only [Real.pi_pos])
  have u8 : KB 0 0 (fun w n ζ => (jInvariantFun ((n : ℝ) +ᵥ w)
      * (Work.Kernels.DeltaFun ζ - (Work.Residues.Ept ζ) ^ 2))
        * (jInvariantFun ((n : ℝ) +ᵥ w) * Compact.Nf ℓ ((n : ℝ) +ᵥ w) ζ)) :=
    KB.reduce' (hB.mul hNfγ) (by linarith only [Real.pi_pos])
      (by linarith only [Real.pi_pos])
  -- assemble:  t1 + t2 + t3 + (t4 - t5) - t6 + (u5 - u1) + (u6 - u2) + (u3 - u4) + (u8 - u7)
  have s1 := (t1.add0 t2).add0 t3
  have s2 := s1.add0 (t4.sub0 t5)
  have s3 := s2.add0 (t6.neg)
  have s4 := s3.add0 (u5.sub0 u1)
  have s5 := s4.add0 (u6.sub0 u2)
  have s6 := s5.add0 (u3.sub0 u4)
  have s7 := s6.add0 (u8.sub0 u7)
  refine KB.congr s7 ?_
  intro w n ζ
  simp only [Work.Asymptotics.kmfd_dev, Work.Asymptotics.kmfd_dSh, Compact.br0_24]
  ring

/-- The `K₋^{(24)}` bracket is `O((scale w)^N)` on the ball. -/
lemma kB_bracket24 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Compact.brMinus ℓ 24 ((n : ℝ) +ᵥ w) ζ
      + Compact.Sh ((n : ℝ) +ᵥ w) ζ * Compact.br0 24 ℓ ((n : ℝ) +ᵥ w) ζ) := by
  refine KB.congr ((kB_BR ℓ).add0 (kB_dev ℓ)) ?_
  intro w n ζ
  rw [Work.Asymptotics.kmfd_bracket_decomp]

/-- The cleared `K₋^{(24)}` deviation is `O((scale w)^N)` on the ball. -/
lemma kMinusDev24 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Compact.Sh ((n : ℝ) +ᵥ w) ζ
      * (Kernels.KMinus ℓ 24 ((n : ℝ) +ᵥ w) ζ
          - Compact.Gminus 24 ℓ ((n : ℝ) +ᵥ w) ζ)) := by
  obtain ⟨C, N, hC, hN, hbr⟩ := kB_bracket24 ℓ
  have hpos : (0 : ℝ) < C / (3456 * Real.pi) := div_pos hC (by positivity)
  refine ⟨C / (3456 * Real.pi), N, hpos, hN, fun w ζ n hn hw => ?_⟩
  change ‖Compact.Sh ((n : ℝ) +ᵥ w) ζ * (Kernels.KMinus ℓ 24 ((n : ℝ) +ᵥ w) ζ
      - Compact.Gminus 24 ℓ ((n : ℝ) +ᵥ w) ζ)‖
    ≤ C / (3456 * Real.pi) * Work.Kernels.scale w ^ N
      * Real.exp (0 * (ModularGroup.S • w).im + 0 * ζ.im)
  by_cases hSh : Compact.Sh ((n : ℝ) +ᵥ w) ζ = 0
  · simp only [hSh, zero_mul, norm_zero]
    have h' : (0 : ℝ) ≤ C / (3456 * Real.pi) := le_of_lt hpos
    exact mul_nonneg (mul_nonneg h' (Real.rpow_nonneg hw.scale_pos.le N)) (Real.exp_nonneg _)
  · have hti := Compact.tail_identity ℓ 24 (Or.inr rfl) ((n : ℝ) +ᵥ w) ζ hSh
    have h3456 : (((3456 : ℂ) * (Real.pi : ℂ))) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      exact_mod_cast Real.pi_ne_zero
    have hkey : Compact.Sh ((n : ℝ) +ᵥ w) ζ
        * (Kernels.KMinus ℓ 24 ((n : ℝ) +ᵥ w) ζ
            - Compact.Gminus 24 ℓ ((n : ℝ) +ᵥ w) ζ)
        = - (Compact.brMinus ℓ 24 ((n : ℝ) +ᵥ w) ζ
              + Compact.Sh ((n : ℝ) +ᵥ w) ζ * Compact.br0 24 ℓ ((n : ℝ) +ᵥ w) ζ)
            / ((3456 : ℂ) * (Real.pi : ℂ)) := by
      rw [eq_div_iff h3456]
      calc Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * (Kernels.KMinus ℓ 24 ((n : ℝ) +ᵥ w) ζ
                  - Compact.Gminus 24 ℓ ((n : ℝ) +ᵥ w) ζ) * ((3456 : ℂ) * (Real.pi : ℂ))
          = Compact.Sh ((n : ℝ) +ᵥ w) ζ * (((3456 : ℂ) * (Real.pi : ℂ))
              * (Kernels.KMinus ℓ 24 ((n : ℝ) +ᵥ w) ζ
                  - Compact.Gminus 24 ℓ ((n : ℝ) +ᵥ w) ζ)) := by ring
        _ = - (Compact.brMinus ℓ 24 ((n : ℝ) +ᵥ w) ζ
              + Compact.Sh ((n : ℝ) +ᵥ w) ζ * Compact.br0 24 ℓ ((n : ℝ) +ᵥ w) ζ) := by
            rw [hti, mul_neg]
            congr 1
            field_simp
    rw [hkey, norm_div, norm_neg]
    have hb := hbr w ζ n hn hw
    have h3456n : ‖((3456 : ℂ) * (Real.pi : ℂ))‖ = 3456 * Real.pi := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [h3456n]
    refine le_trans (div_le_div_of_nonneg_right hb (by positivity)) ?_
    simp only [Real.rpow_zero, zero_mul, zero_mul, add_zero, Real.exp_zero, mul_one]
    refine le_trans (le_of_eq ?_) (le_refl _)
    rw [div_eq_mul_inv]
    ring

/-! ## The small-`scale` part of the ball bound -/

set_option maxHeartbeats 1000000

/-! ## The small-`scale` compact boxes -/

/-- A closed box in `ℂ` containing `ζ` when `scale w ≤ 8` and `‖ζ - S • w‖ ≤ 29/20`. -/
private def tbfsKboxZ : Set ℂ := {z | ‖z‖ ≤ 11} ∩ {z | (1 : ℝ) / 2 ≤ z.im}

private lemma mem_tbfsKboxZ {z : ℂ} :
    z ∈ tbfsKboxZ ↔ ‖z‖ ≤ 11 ∧ (1 : ℝ) / 2 ≤ z.im := by
  rw [tbfsKboxZ]; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]

private lemma isClosed_tbfsKboxZ : IsClosed tbfsKboxZ := by
  rw [tbfsKboxZ]
  exact (isClosed_le continuous_norm continuous_const).inter
    (isClosed_Ici.preimage Complex.continuous_im)

private lemma isCompact_tbfsKboxZ : IsCompact tbfsKboxZ :=
  IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) 11) isClosed_tbfsKboxZ (by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (mem_tbfsKboxZ.mp hz).1)

/-- A closed box in `ℂ` containing `τ = n +ᵥ w` when `scale w ≤ 8`. -/
private def tbfsKboxT : Set ℂ :=
  {z | |z.re| ≤ 2} ∩ {z | (1 : ℝ) / 100 ≤ z.im} ∩ {z | z.im ≤ 1}

private lemma mem_tbfsKboxT {z : ℂ} :
    z ∈ tbfsKboxT ↔ |z.re| ≤ 2 ∧ (1 : ℝ) / 100 ≤ z.im ∧ z.im ≤ 1 := by
  rw [tbfsKboxT]; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; tauto

private lemma isClosed_tbfsKboxT : IsClosed tbfsKboxT := by
  rw [tbfsKboxT]
  exact ((isClosed_le (Complex.continuous_re.abs) continuous_const).inter
    (isClosed_Ici.preimage Complex.continuous_im)).inter
    (isClosed_Iic.preimage Complex.continuous_im)

private lemma isCompact_tbfsKboxT : IsCompact tbfsKboxT := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) 3) isClosed_tbfsKboxT ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [mem_tbfsKboxT] at hz
  obtain ⟨ha, hb, hc⟩ := hz
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 := abs_le.mp ha
  have h2 : z.im ≤ 3 := by linarith
  nlinarith [norm_nonneg z, sq_nonneg z.re, sq_nonneg z.im]

private def tbfsKZ : Set ℍ := (↑) ⁻¹' tbfsKboxZ
private def tbfsKT : Set ℍ := (↑) ⁻¹' tbfsKboxT

private lemma isCompact_tbfsKZ : IsCompact tbfsKZ :=
  UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage' isCompact_tbfsKboxZ (by
    intro z hz
    rw [UpperHalfPlane.range_coe]
    exact lt_of_lt_of_le (by norm_num) (mem_tbfsKboxZ.mp hz).2)

private lemma isCompact_tbfsKT : IsCompact tbfsKT :=
  UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage' isCompact_tbfsKboxT (by
    intro z hz
    rw [UpperHalfPlane.range_coe]
    exact lt_of_lt_of_le (by norm_num) (mem_tbfsKboxT.mp hz).2.1)

/-! ## The region lies in the compact box -/

/-- **The small-`scale` tile lies in the compact box `tbfsKT × tbfsKZ`.** -/
private lemma tbfs_mem_box {w ζ : ℍ} (n : ℤ) (hn : n = 1 ∨ n = -1)
    (hw : w ∈ Work.Asymptotics.KEpsilon) (hsc : Work.Kernels.scale w ≤ 8)
    (hball : ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20) :
    (((n : ℝ) +ᵥ w), ζ) ∈ tbfsKT ×ˢ tbfsKZ := by
  have hwD : w ∈ Work.Asymptotics.DomainD := (Work.Asymptotics.mem_KEpsilon.mp hw).1
  have hwim2 : 2 ≤ (ModularGroup.S • w).im := (Work.Asymptotics.mem_KEpsilon.mp hw).2
  have hwimpos : 0 < w.im := w.im_pos
  have hscale : Work.Kernels.scale w = 1 + (w.im)⁻¹ + ‖(w : ℂ)‖ := rfl
  have hinv_le : (w.im)⁻¹ ≤ 7 := by
    rw [hscale] at hsc
    have := norm_nonneg (w : ℂ)
    linarith
  have hwim_ge7 : (1 : ℝ) / 7 ≤ w.im := by
    have h1 : (w.im)⁻¹ * w.im = 1 := inv_mul_cancel₀ hwimpos.ne'
    have h2 : (w.im)⁻¹ * w.im ≤ 7 * w.im := mul_le_mul_of_nonneg_right hinv_le hwimpos.le
    rw [h1] at h2
    linarith
  have hwim_ge : (1 : ℝ) / 100 ≤ w.im := by linarith
  have hwim_le : w.im ≤ 1 := by
    have := Work.Asymptotics.E_im_le_half hw
    linarith
  have hwre : |w.re| ≤ 1 := by
    rw [abs_le]
    exact ⟨le_of_lt hwD.1, le_of_lt hwD.2.1⟩
  have hwnorm_ge : (1 : ℝ) / 9 ≤ ‖(w : ℂ)‖ :=
    le_trans (by linarith) (Work.Kernels.im_le_coe_norm w)
  refine ⟨?_, ?_⟩
  · rw [tbfsKT, Set.mem_preimage, mem_tbfsKboxT, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
      UpperHalfPlane.vadd_re, UpperHalfPlane.vadd_im]
    have hnabs : |(n : ℝ)| = 1 := by
      rcases hn with h | h <;> rw [h] <;> norm_num
    refine ⟨?_, by linarith, by linarith⟩
    calc |(n : ℝ) + w.re| ≤ |(n : ℝ)| + |w.re| := abs_add_le _ _
      _ ≤ 2 := by linarith [hnabs, hwre]
  · rw [tbfsKZ, Set.mem_preimage, mem_tbfsKboxZ, UpperHalfPlane.coe_im]
    have hnormpos : (0 : ℝ) < ‖(w : ℂ)‖ := norm_pos_iff.mpr w.ne_zero
    have hSnorm : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 9 := by
      rw [Work.Asymptotics.EtailE.E_norm_S]
      rw [inv_le_comm₀ hnormpos (by norm_num : (0 : ℝ) < 9)]
      linarith
    have hζnorm : ‖(ζ : ℂ)‖ ≤ 11 := by
      have h1 : ‖(ζ : ℂ)‖ ≤ ‖((ModularGroup.S • w : ℍ) : ℂ)‖
          + ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ := by
        have h2 := norm_add_le ((ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ))
          ((ModularGroup.S • w : ℍ) : ℂ)
        have h3 : (ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)
            + ((ModularGroup.S • w : ℍ) : ℂ) = (ζ : ℂ) := by ring
        rw [h3] at h2
        linarith [h2]
      linarith [h1, hSnorm, hball]
    have hζim : (1 : ℝ) / 2 ≤ ζ.im := by
      have him : |ζ.im - (ModularGroup.S • w).im| ≤ 29 / 20 := by
        have h := Complex.abs_im_le_norm ((ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ))
        rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im] at h
        exact le_trans h hball
      have := (abs_le.mp him).1
      linarith
    exact ⟨hζnorm, hζim⟩

/-! ## Continuity of the scalar building blocks -/

private lemma continuous_E2Fun' : Continuous (Work.Kernels.E2Fun : ℍ → ℂ) :=
  Work.Kernels.ClassicalFacts.E2Fun_mem_InP.1.continuous

private lemma continuous_E4Fun' : Continuous (Work.Kernels.E4Fun : ℍ → ℂ) :=
  Work.Kernels.ClassicalFacts.E4Fun_mem_InP.1.continuous

private lemma continuous_E6Fun' : Continuous (Work.Kernels.E6Fun : ℍ → ℂ) :=
  Work.Kernels.ClassicalFacts.E6Fun_mem_InP.1.continuous

private lemma continuous_DeltaFun' : Continuous (Work.Kernels.DeltaFun : ℍ → ℂ) :=
  Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1.continuous

private lemma continuous_psi2' (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) := by
  have hU : Continuous (Work.Kernels.UFun : ℍ → ℂ) :=
    (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4
  have hW : Continuous (Work.Kernels.WFun : ℍ → ℂ) :=
    (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.continuous).pow 4
  have hV : Continuous (Work.Kernels.VFun : ℍ → ℂ) :=
    (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.continuous).pow 4
  have hxi2 : Continuous (Work.Kernels.xi2Fun : ℍ → ℂ) := by
    rw [show Work.Kernels.xi2Fun = fun τ => Work.Kernels.UFun τ + Work.Kernels.WFun τ from rfl]
    exact hU.add hW
  have h : (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) = fun τ : ℍ =>
      Work.Kernels.xi2Fun τ * ℓ.L τ
        + (-(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) * ℓ.L_S τ := by
    funext τ
    show Work.Kernels.xi2Fun τ * ℓ.L τ
        + SlashAction.map (2 : ℤ) ModularGroup.S Work.Kernels.xi2Fun τ * ℓ.L_S τ = _
    rw [Work.Kernels.KernelFacts.xi2Fun_slash_S τ]
  rw [h]
  exact (hxi2.mul ℓ.holo.continuous).add
    (((hU.add hV).neg).mul ℓ.holo_S.continuous)

private lemma continuous_psi4' (ℓ : Work.Kernels.LogLambdaData) :
    Continuous (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) := by
  have hU : Continuous (Work.Kernels.UFun : ℍ → ℂ) :=
    (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.1.continuous).pow 4
  have hW : Continuous (Work.Kernels.WFun : ℍ → ℂ) :=
    (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.1.continuous).pow 4
  have hV : Continuous (Work.Kernels.VFun : ℍ → ℂ) :=
    (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.1.continuous).pow 4
  have hxi4 : Continuous (Work.Kernels.xi4Fun : ℍ → ℂ) := by
    rw [show Work.Kernels.xi4Fun
        = fun τ => Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
            - 2 * Work.Kernels.VFun τ ^ 2 from rfl]
    exact ((hU.pow 2).add (hW.pow 2)).sub ((hV.pow 2).const_mul 2)
  have h : (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) = fun τ : ℍ =>
      Work.Kernels.xi4Fun τ * ℓ.L τ
        + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
            - 2 * Work.Kernels.WFun τ ^ 2) * ℓ.L_S τ := by
    funext τ
    show Work.Kernels.xi4Fun τ * ℓ.L τ
        + SlashAction.map (4 : ℤ) ModularGroup.S Work.Kernels.xi4Fun τ * ℓ.L_S τ = _
    rw [Work.Kernels.KernelFacts.xi4S_apply τ]
  rw [h]
  exact (hxi4.mul ℓ.holo.continuous).add
    ((((hU.pow 2).add (hV.pow 2)).sub ((hW.pow 2).const_mul 2)).mul ℓ.holo_S.continuous)

private lemma continuous_Ept' : Continuous (Work.Residues.Ept : ℍ → ℂ) := by
  rw [show (Work.Residues.Ept : ℍ → ℂ)
      = fun τ : ℍ => Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ)) from by funext τ; rfl]
  exact Complex.continuous_exp.comp
    ((continuous_const.mul continuous_const).mul UpperHalfPlane.continuous_coe)

private lemma continuous_Ept_zpow (m : ℤ) :
    Continuous (fun τ : ℍ => (Work.Residues.Ept τ) ^ m) := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg m
  · rw [hk, show (fun τ : ℍ => (Work.Residues.Ept τ) ^ ((k : ℤ))) = fun τ : ℍ =>
        (Work.Residues.Ept τ) ^ k from by funext τ; rw [zpow_natCast]]
    exact continuous_Ept'.pow k
  · rw [hk, show (fun τ : ℍ => (Work.Residues.Ept τ) ^ (-((k : ℤ)))) = fun τ : ℍ =>
        ((Work.Residues.Ept τ) ^ k)⁻¹ from by
      funext τ; rw [zpow_neg, zpow_natCast]]
    exact (continuous_Ept'.pow k).inv₀ (fun τ => pow_ne_zero k (Work.Residues.Ept_ne_zero τ))

private lemma continuous_Gcoef' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (i j : Fin 2) :
    Continuous (Work.Asymptotics.Compact.Gcoef d ℓ i j) := by
  have h2 : Continuous (Work.Kernels.E2Fun : ℍ → ℂ) := continuous_E2Fun'
  have h4 : Continuous (Work.Kernels.E4Fun : ℍ → ℂ) := continuous_E4Fun'
  have h6 : Continuous (Work.Kernels.E6Fun : ℍ → ℂ) := continuous_E6Fun'
  have hD : Continuous (Work.Kernels.DeltaFun : ℍ → ℂ) := continuous_DeltaFun'
  have h2p : Continuous (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) := continuous_psi2' ℓ
  have h4p : Continuous (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) := continuous_psi4' ℓ
  have ht : Continuous (fun τ : ℍ => (τ : ℂ)) := UpperHalfPlane.continuous_coe
  have hp1 : Continuous (Work.Asymptotics.Compact.phi1) := by
    unfold Work.Asymptotics.Compact.phi1
    fun_prop (disch := assumption)
  have hp2 : Continuous (Work.Asymptotics.Compact.phi2t) := by
    unfold Work.Asymptotics.Compact.phi2t
    fun_prop (disch := assumption)
  rcases hd with rfl | rfl
  · unfold Work.Asymptotics.Compact.Gcoef
    rw [if_pos rfl]
    split_ifs <;> fun_prop (disch := assumption)
  · unfold Work.Asymptotics.Compact.Gcoef
    rw [if_neg (by norm_num : ¬ (24 : ℕ) = 8)]
    split_ifs <;> fun_prop (disch := assumption)

/-- Joint continuity of `Gfun` as a function of `(τ,ζ)`. -/
private lemma continuous_Gfun_joint (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    Continuous (fun q : ℍ × ℍ => Work.Asymptotics.Compact.Gfun d ℓ q.1 q.2) := by
  have hcoe2 : Continuous (fun q : ℍ × ℍ => (q.2 : ℂ)) :=
    UpperHalfPlane.continuous_coe.comp continuous_snd
  have hc : ∀ i j : Fin 2, Continuous (fun q : ℍ × ℍ =>
      Work.Asymptotics.Compact.Gcoef d ℓ i j q.1) :=
    fun i j => (continuous_Gcoef' ℓ d hd i j).comp continuous_fst
  have hz : Continuous (fun q : ℍ × ℍ => (Work.Residues.Ept q.2) ^ (-2 : ℤ)) :=
    (continuous_Ept_zpow (-2)).comp continuous_snd
  simp only [Work.Asymptotics.Compact.Gfun]
  exact (((hc 0 0).add (hcoe2.mul (hc 0 1)))).add
    (hz.mul ((hc 1 0).add (hcoe2.mul (hc 1 1))))

/-- Joint continuity of `Sh` as a function of `(τ,ζ)`. -/
private lemma continuous_Sh_joint :
    Continuous (fun q : ℍ × ℍ => Work.Asymptotics.Compact.Sh q.1 q.2) := by
  have hDz : Continuous (fun q : ℍ × ℍ => Work.Kernels.DeltaFun q.2) :=
    continuous_DeltaFun'.comp continuous_snd
  have hj : Continuous (fun q : ℍ × ℍ => Work.Kernels.jInvariantFun q.1) :=
    (continuous_E4Fun'.pow 3).div continuous_DeltaFun'
      (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ) |>.comp continuous_fst
  simp only [Work.Asymptotics.Compact.Sh]
  exact ((continuous_E4Fun'.comp continuous_snd).pow 3).sub (hDz.mul hj)

/-! ## The small-`scale` bound -/

/-- **The small-`scale` cleared ball bound.**  For `scale w ≤ 8` the cleared numerator is
bounded by a constant: the pair `(n +ᵥ w, ζ)` lies in the compact box `tbfsKT × tbfsKZ`, and the
cleared numerator agrees with the continuous holomorphic representative
`-2Δ(ζ)AfunFun (n+ᵥw) ζ - 2Sh (n+ᵥw) ζ · Gfun (n+ᵥw) ζ` off the coincidence locus. -/
private lemma tbfs_region_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    ∃ M : ℝ, 0 < M ∧ ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon →
      Work.Kernels.scale w ≤ 8 → ∀ ζ : ℍ,
        ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20 →
        ‖2 * (Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
            * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖ ≤ M := by
  have hDz : Continuous (fun q : ℍ × ℍ => Work.Kernels.DeltaFun q.2) :=
    continuous_DeltaFun'.comp continuous_snd
  have hA : Continuous (fun q : ℍ × ℍ => Work.Asymptotics.AfunFun ℓ d q.1 q.2) :=
    Work.Asymptotics.continuous_AfunFun ℓ d
  have hSh := continuous_Sh_joint
  have hG := continuous_Gfun_joint ℓ d hd
  let g : ℍ × ℍ → ℝ := fun q =>
    ‖-2 * Work.Kernels.DeltaFun q.2 * Work.Asymptotics.AfunFun ℓ d q.1 q.2
      - 2 * Work.Asymptotics.Compact.Sh q.1 q.2 * Work.Asymptotics.Compact.Gfun d ℓ q.1 q.2‖
  have hmain : Continuous g := by
    show Continuous (fun q : ℍ × ℍ =>
      ‖-2 * Work.Kernels.DeltaFun q.2 * Work.Asymptotics.AfunFun ℓ d q.1 q.2
        - 2 * Work.Asymptotics.Compact.Sh q.1 q.2
            * Work.Asymptotics.Compact.Gfun d ℓ q.1 q.2‖)
    exact (((continuous_const.mul hDz).mul hA).sub
      ((continuous_const.mul hSh).mul hG)).norm
  obtain ⟨M, hM⟩ := ((isCompact_tbfsKT.prod isCompact_tbfsKZ).image hmain).bddAbove
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro w hw hsc ζ hball
  have hp : (((n : ℝ) +ᵥ w), ζ) ∈ tbfsKT ×ˢ tbfsKZ := tbfs_mem_box n hn hw hsc hball
  have hbound : g (((n : ℝ) +ᵥ w), ζ) ≤ M := hM (Set.mem_image_of_mem g hp)
  have hle : ‖2 * (Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
        * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
            - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
      ≤ ‖-2 * Work.Kernels.DeltaFun ζ * Work.Asymptotics.AfunFun ℓ d ((n : ℝ) +ᵥ w) ζ
          - 2 * Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ‖ := by
    by_cases hShz : Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ = 0
    · rw [hShz, mul_zero, zero_mul, mul_zero, norm_zero]
      exact norm_nonneg _
    · have hj : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
          ≠ Work.Kernels.jInvariantFun ζ := by
        intro hJ
        exact hShz (by
          rw [Work.Asymptotics.Compact.Sh, hJ,
            Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun, sub_self])
      have hA' := Work.Asymptotics.Kfun_mul_slope_eq_AfunFun ℓ d hd
        ((n : ℝ) +ᵥ w) ζ hj
      have hSh_eq : Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
          = -Work.Kernels.DeltaFun ζ
              * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
                  - Work.Kernels.jInvariantFun ζ) := by
        rw [Work.Asymptotics.Compact.Sh,
          ← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun ζ]
        ring
      have hgoal : 2 * (Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
            * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))
          = -2 * Work.Kernels.DeltaFun ζ * Work.Asymptotics.AfunFun ℓ d ((n : ℝ) +ᵥ w) ζ
            - 2 * Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
                * Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ := by
        rw [hSh_eq, mul_sub]
        rw [show (-Work.Kernels.DeltaFun ζ
                * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
                    - Work.Kernels.jInvariantFun ζ)) * Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
              = -Work.Kernels.DeltaFun ζ
                * ((Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
                    - Work.Kernels.jInvariantFun ζ) * Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ)
              from by ring]
        rw [mul_comm (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
          - Work.Kernels.jInvariantFun ζ) (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ), hA']
        ring
      rw [hgoal]
  exact le_trans hle (le_trans hbound (le_max_left _ _))


/-- **The small-`scale` tile ball bound** (the third input of `TileNumBallTS.of_pieces`). -/
private theorem tbfs_smallScale (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∃ M : ℝ, 0 < M ∧ ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon →
      Work.Kernels.scale w ≤ 8 → ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : ℍ,
        ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20 →
        ‖2 * (Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
            * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖ ≤ M := by
  obtain ⟨M1, hM1, h1⟩ := tbfs_region_bound ℓ d hd 1 (Or.inl rfl)
  obtain ⟨M2, hM2, h2⟩ := tbfs_region_bound ℓ d hd (-1) (Or.inr rfl)
  refine ⟨max M1 M2, lt_of_lt_of_le hM1 (le_max_left _ _), ?_⟩
  intro w hw hsc n hn ζ hball
  rcases hn with h | h
  · subst h
    exact le_trans (h1 w hw hsc ζ hball) (le_max_left _ _)
  · subst h
    exact le_trans (h2 w hw hsc ζ hball) (le_max_right _ _)

/-! ## The `d = 8` bracket on the ball -/

/-- `IsBigOq f n` gives the `KB` atom with exponent `-2nπ`. -/
lemma kb_of_isBigOq {f : ℍ → ℂ} {n : ℕ} (h : IsBigOq f n) :
    KB 0 (-(2 * (n : ℝ) * Real.pi)) (fun _ _ ζ => f ζ) := by
  obtain ⟨C, hC, hf⟩ := h
  have hmain : KB 0 (-(((2 * n : ℕ) : ℝ) * Real.pi)) (fun _ _ ζ => f ζ) :=
    KB.of_zeta_eptpow (C := C) (k := 2 * n) hC (fun z hz => by
      have h1 := hf z hz
      have h2 : ‖Work.Kernels.qParamFun z‖ ^ n = ‖Work.Residues.Ept z‖ ^ (2 * n) := by
        rw [show Work.Kernels.qParamFun z = (Work.Residues.Ept z) ^ 2
          from Compact.qParamFun_eq_Ept_sq z, norm_pow, ← pow_mul]
      rw [h2] at h1
      exact h1)
  refine KB.castr hmain (by ring) ?_
  push_cast
  ring

/-- `E₆ - 1 = O(e^{-2π Im})`. -/
lemma kb8_E6sub1 : KB 0 (-(2 * Real.pi)) (fun _ _ ζ => Work.Kernels.E6Fun ζ - 1) := by
  have h := kb_of_isBigOq (n := 1) E6_minus_one
  simpa using h

/-- `E₄³ - 1 = O(e^{-2π Im})`. -/
lemma kb8_E4cube1 : KB 0 (-(2 * Real.pi)) (fun _ _ ζ => Work.Kernels.E4Fun ζ ^ 3 - 1) := by
  have h := kb_of_isBigOq (n := 1) E4cube_minus_one
  simpa using h

/-- `E₈ - 1 = O(e^{-2π Im})`. -/
lemma kb8_E8sub1 : KB 0 (-(2 * Real.pi)) (fun _ _ ζ => Work.Kernels.E8Fun ζ - 1) := by
  have h := kb_of_isBigOq (n := 1) ktl_E8_sub_one_isBigOq
  simpa using h

/-- `W - 1 = O(e^{-π Im})`. -/
lemma kb8_Wsub1 : KB 0 (-Real.pi) (fun _ _ ζ => Work.Kernels.WFun ζ - 1) := by
  obtain ⟨C, hC, h⟩ := Work.Residues.WFun_decay
  have hmain : KB 0 (-(((1 : ℕ) : ℝ) * Real.pi)) (fun _ _ ζ => Work.Kernels.WFun ζ - 1) :=
    KB.of_zeta_eptpow (C := C) (k := 1) hC (fun z hz => by
      have h1 := h z hz
      rw [← Work.Residues.norm_Ept] at h1
      simpa using h1)
  have hcast : KB 0 (-Real.pi) (fun _ _ ζ => Work.Kernels.WFun ζ - 1) :=
    KB.castr hmain (by ring) (by push_cast; ring)
  exact hcast

/-- `(U² - V²) - 1 = O(e^{-π Im})`. -/
lemma kb8_D2sub1 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (-Real.pi) (fun _ _ ζ => (Work.Kernels.UFun ζ ^ 2 - Work.Kernels.VFun ζ ^ 2) - 1) := by
  have h1 : KB 0 (-Real.pi) (fun _ _ ζ => (16 : ℂ) * Work.Residues.Ept ζ) :=
    KB.congr (KB.castr (KB.const_mul (16 : ℂ) (z_Ept_pow 1)) (by ring)
      (by push_cast; ring)) (fun w n ζ => by ring)
  have h2 : KB 0 (-(2 * Real.pi)) (fun _ _ ζ => (-144 : ℂ) * Work.Residues.Ept ζ ^ 2) :=
    KB.congr (KB.castr (KB.const_mul (-144 : ℂ) (z_Ept_pow 2)) (by ring)
      (by push_cast; ring)) (fun w n ζ => by ring)
  have h3 : KB 0 (-(3 * Real.pi)) (fun _ _ ζ => Compact.dD2 ζ) := z_dD2 ℓ
  have h12 := KB.add_of_le (c := 0) (d := -Real.pi) (c' := 0) (d' := -(2 * Real.pi))
    (le_refl 0) (by linarith [Real.pi_pos]) h1 h2
  refine KB.congr (KB.add_of_le (c := 0) (d := -Real.pi) (c' := 0) (d' := -(3 * Real.pi))
    (le_refl 0) (by linarith [Real.pi_pos]) h12 h3) (fun w n ζ => ?_)
  rw [Compact.dD2, Compact.D2ref]
  ring

/-- `E₈W - 1 = O(e^{-π Im})`. -/
lemma kb8_E8Wsub1 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (-Real.pi) (fun _ _ ζ => Work.Kernels.E8Fun ζ * Work.Kernels.WFun ζ - 1) := by
  have h1 : KB 0 (-Real.pi) (fun _ _ ζ => (Work.Kernels.E8Fun ζ - 1) * Work.Kernels.WFun ζ) :=
    KB.mono (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      ((kb8_E8sub1).mul (z_W ℓ))
  refine KB.congr (KB.add_of_le (c := 0) (d := -Real.pi) (c' := 0) (d' := -Real.pi)
    (le_refl 0) (le_refl _) h1 (kb8_Wsub1)) (fun w n ζ => by ring)

/-- `E₈W - E₆(U² - V²) = O(e^{-π Im})`. -/
lemma kb8_Az (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 (-Real.pi) (fun _ _ ζ => Work.Kernels.E8Fun ζ * Work.Kernels.WFun ζ
      - Work.Kernels.E6Fun ζ * (Work.Kernels.UFun ζ ^ 2 - Work.Kernels.VFun ζ ^ 2)) := by
  have h1 : KB 0 (-Real.pi) (fun _ _ ζ => Work.Kernels.E8Fun ζ * Work.Kernels.WFun ζ - 1) :=
    kb8_E8Wsub1 ℓ
  have h2 : KB 0 (-(2 * Real.pi)) (fun _ _ ζ => (Work.Kernels.E6Fun ζ - 1)
      * (Work.Kernels.UFun ζ ^ 2 - Work.Kernels.VFun ζ ^ 2)) :=
    KB.castr ((kb8_E6sub1).mul (z_D2 ℓ)) (by ring) (by ring)
  have h3 : KB 0 (-Real.pi) (fun _ _ ζ => (Work.Kernels.UFun ζ ^ 2
      - Work.Kernels.VFun ζ ^ 2) - 1) := kb8_D2sub1 ℓ
  have h23 := KB.add_of_le (c := 0) (d := -Real.pi) (c' := 0) (d' := -(2 * Real.pi))
    (le_refl 0) (by linarith [Real.pi_pos]) h3 h2
  refine KB.congr (KB.sub_of_le (c := 0) (d := -Real.pi) (c' := 0) (d' := -Real.pi)
    (le_refl 0) (le_refl _) h1 h23) (fun w n ζ => by ring)

/-- `Λ = E₄·(ψ₄E₈ - ψ₂E₁₀)/Δ` on the tiles is `O(e^{π Im (S w)})`. -/
lemma kb8_lamb (ℓ : Work.Kernels.LogLambdaData) :
    KB Real.pi 0 (fun w n _ => Work.Residues.Lamb ℓ ((n : ℝ) +ᵥ w)) := by
  have h : KB Real.pi 0 (fun w n _ => Work.Kernels.E4Fun ((n : ℝ) +ᵥ w)
      * (Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * Work.Kernels.E8Fun ((n : ℝ) +ᵥ w)
        - Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * Work.Kernels.E10Fun ((n : ℝ) +ᵥ w))
      * (Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w))⁻¹) := by
    have h1 := (tau_E4 ℓ).mul (psiCombo_sharp ℓ)
    have h2 := h1.mul (tau_invDelta ℓ)
    refine KB.castr h2 (by ring) (by ring)
  refine KB.congr h (fun w n ζ => ?_)
  rw [Work.Residues.Lamb_eq]
  ring

/-- `Sh(τ,·) - 1 = O(e^{2π Im (S w)} e^{-2π Im ζ})`. -/
lemma kb8_Shsub1 (ℓ : Work.Kernels.LogLambdaData) :
    KB (2 * Real.pi) (-(2 * Real.pi)) (fun w n ζ => Compact.Sh ((n : ℝ) +ᵥ w) ζ - 1) := by
  have h1 : KB 0 (-(2 * Real.pi)) (fun _ _ ζ => Work.Kernels.E4Fun ζ ^ 3 - 1) := kb8_E4cube1
  have h2 : KB (2 * Real.pi) (-(2 * Real.pi))
      (fun w n ζ => Work.Kernels.DeltaFun ζ * Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)) :=
    KB.castr ((z_Delta ℓ).mul (tau_j ℓ)) (by ring) (by ring)
  have h1' : KB (2 * Real.pi) (-(2 * Real.pi))
      (fun _ _ ζ => Work.Kernels.E4Fun ζ ^ 3 - 1) :=
    KB.mono (by positivity) (le_refl _) h1
  refine KB.congr (KB.sub_of_le (c := 2 * Real.pi) (d := -(2 * Real.pi)) (c' := 2 * Real.pi)
    (d' := -(2 * Real.pi)) (le_refl _) (le_refl _) h1' h2) (fun w n ζ => ?_)
  simp only [Compact.Sh]
  ring

/-- `E₁₀·𝓛 - Xc = O((scale w)^N)`. -/
lemma kb8_E10L (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun _ _ ζ => Work.Kernels.E10Fun ζ * ℓ.L ζ - Compact.Xc ℓ ζ) :=
  KB.sub0 ((z_E10 ℓ).mul0 (z_L ℓ)) (z_Xc ℓ)

/-- `br0 8 = O((scale w)^N)` on the tiles. -/
lemma kb8_br0_8 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Compact.br0 8 ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have h1 : KB 0 0 (fun w n ζ => (3456 : ℂ)
      * (Work.Kernels.E4Fun ((n : ℝ) +ᵥ w) * Compact.Xc ℓ ζ)) :=
    KB.const_mul 3456 ((tau_E4 ℓ).mul0 (z_Xc ℓ))
  have h2 : KB 0 0 (fun w n ζ => (1728 : ℂ) * Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)) :=
    KB.const_mul 1728 (tau_p4 ℓ)
  refine KB.congr (KB.sub0 h1 h2) (fun w n ζ => ?_)
  rw [Compact.br0_8]
  ring

/-- **The `d = 8` bracket is polynomially bounded on the ball.** -/
lemma kB_bracket8 (ℓ : Work.Kernels.LogLambdaData) :
    KB 0 0 (fun w n ζ => Compact.brMinus ℓ 8 ((n : ℝ) +ᵥ w) ζ
      + Compact.Sh ((n : ℝ) +ᵥ w) ζ * Compact.br0 8 ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have hA1 : KB 0 0 (fun w n ζ => (-3456 : ℂ)
      * ((Work.Kernels.E10Fun ζ * ℓ.L ζ - Compact.Xc ℓ ζ)
          * Work.Kernels.E4Fun ((n : ℝ) +ᵥ w))) :=
    KB.const_mul (-3456) ((kb8_E10L ℓ).mul0 (tau_E4 ℓ))
  have hA2 : KB 0 0 (fun w n ζ => (-1 : ℂ)
      * ((Work.Kernels.E8Fun ζ * Work.Kernels.WFun ζ
          - Work.Kernels.E6Fun ζ * (Work.Kernels.UFun ζ ^ 2 - Work.Kernels.VFun ζ ^ 2))
          * Work.Residues.Lamb ℓ ((n : ℝ) +ᵥ w))) :=
    KB.const_mul (-1) (KB.reduce' ((kb8_Az ℓ).mul (kb8_lamb ℓ))
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hA3 : KB 0 0 (fun w n ζ => (1728 : ℂ)
      * ((Work.Kernels.E8Fun ζ * Work.Kernels.WFun ζ - 1)
          * Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w))) :=
    KB.const_mul 1728 (KB.reduce' ((kb8_E8Wsub1 ℓ).mul (tau_p4 ℓ))
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  have hA4 : KB 0 0 (fun w n ζ => (Compact.Sh ((n : ℝ) +ᵥ w) ζ - 1)
      * Compact.br0 8 ℓ ((n : ℝ) +ᵥ w) ζ) :=
    (KB.reduce' (kb8_Shsub1 ℓ) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])).mul0 (kb8_br0_8 ℓ)
  refine KB.congr (((hA1.add0 hA2).add0 hA3).add0 hA4) (fun w n ζ => ?_)
  simp only [Compact.brMinus_eight, Compact.br0_8, Work.Residues.bracket8e,
    Work.Residues.Lamb, Compact.Xc, Work.Kernels.c1728]
  ring

/-! ## The assembly -/

/-- The `K₊` half-deviation on the ball. -/
lemma kPlusBall (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : ℍ,
        ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20 → 3 ≤ ζ.im →
        ‖Compact.Sh ((n : ℝ) +ᵥ w) ζ
          * (Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) ζ
              - Compact.Gplus d ((n : ℝ) +ᵥ w) ζ)‖
        ≤ C * (Work.Kernels.scale w) ^ N := by
  rcases hd with rfl | rfl
  · exact TileDevBall.kplusDev8Ball ℓ
  · exact TileDevBall.kplusDev24Ball ℓ

/-- The bracket bound on the ball, both dimensions. -/
lemma bracketBall (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : ℍ,
        ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20 → 3 ≤ ζ.im →
        ‖Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) ζ
          + Compact.Sh ((n : ℝ) +ᵥ w) ζ * Compact.br0 d ℓ ((n : ℝ) +ᵥ w) ζ‖
        ≤ C * (Work.Kernels.scale w) ^ N := by
  rcases hd with rfl | rfl
  · obtain ⟨C, N, hC, hN, hb⟩ := kB_bracket8 ℓ
    refine ⟨C, N, hC, hN, ?_⟩
    intro w hw n hn ζ hball him
    have hB : KBall w ζ := ⟨hw, hball, him⟩
    have h := hb w ζ n hn hB
    simpa only [zero_mul, add_zero, Real.exp_zero, mul_one] using h
  · obtain ⟨C, N, hC, hN, hb⟩ := kB_bracket24 ℓ
    refine ⟨C, N, hC, hN, ?_⟩
    intro w hw n hn ζ hball him
    have hB : KBall w ζ := ⟨hw, hball, him⟩
    have h := hb w ζ n hn hB
    simpa only [zero_mul, add_zero, Real.exp_zero, mul_one] using h

/-- **The resonant strip of the tile deviation, away from the coincidences.** -/
theorem tileBelowPoleStripOffCoincClean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) : Work.Asymptotics.Tile.TileBelowPoleStripOffCoinc ℓ d := by
  have hball := TileNumBallTS.of_pieces ℓ d hd (kPlusBall ℓ d hd) (bracketBall ℓ d hd)
    (tbfs_smallScale ℓ d hd)
  exact tileStripOffCoincEndgame ℓ d hd hball

end

end Work.Asymptotics.Tile
