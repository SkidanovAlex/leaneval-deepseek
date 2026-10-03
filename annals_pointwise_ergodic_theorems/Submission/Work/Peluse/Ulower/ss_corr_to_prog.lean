import Mathlib
import Submission.Work.Peluse.Ulower.dualFn_fourier_unfold
import Submission.Work.Peluse.Ulower.dualFn_tsum_le
import Submission.Work.Peluse.Ulower.progAvgSum_eq_l1
import Submission.Work.Peluse.Ulower.poly_diff_bound
import Submission.Work.Peluse.Ulower.sum_Icc_block_decomp
import Submission.Work.Peluse.Ulower.sum_Icc_subblock_decomp
import Submission.Work.Peluse.Ulower.dvd_eval_sub_eval

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower

noncomputable section

/-! ## The additive character `e(x) = exp(2πix)` -/

/-- The additive character `e(x) = exp(2πix)`. -/
def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma ee_intCast (n : ℤ) : ee (n : ℝ) = 1 := by
  unfold ee
  rw [show 2 * Real.pi * Complex.I * (n : ℝ) = (n : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

lemma ee_neg (x : ℝ) : ee (-x) = (ee x)⁻¹ := by
  have h := ee_add x (-x)
  rw [add_neg_cancel, ee_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  refine (Complex.norm_eq_one_iff _).mpr ⟨2 * Real.pi * x, ?_⟩
  unfold ee
  congr 1
  push_cast
  ring

/-- `‖e(x) - e(y)‖ = ‖e(x-y) - 1‖`. -/
lemma norm_ee_sub_eq (x y : ℝ) : ‖ee x - ee y‖ = ‖ee (x - y) - 1‖ := by
  have h : ee x - ee y = ee y * (ee (x - y) - 1) := by
    rw [mul_sub, mul_one, ← ee_add]
    ring_nf
  rw [h, norm_mul, norm_ee, one_mul]

/-- First-order bound at small increments. -/
lemma norm_ee_sub_one_le {t : ℝ} (ht : 2 * Real.pi * |t| ≤ 1) :
    ‖ee t - 1‖ ≤ 2 * (2 * Real.pi * |t|) := by
  have hE : ee t = Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := rfl
  have hzn : ‖(2 * Real.pi * Complex.I * (t : ℂ))‖ = 2 * Real.pi * |t| := by
    have hc : (2 * Real.pi * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    have h1 : ‖(((2 * Real.pi * t : ℝ)) : ℂ)‖ = |2 * Real.pi * t| := by simp
    have h2 : |2 * Real.pi * t| = 2 * Real.pi * |t| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    rw [hc]
    calc ‖(((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I‖
        = ‖(((2 * Real.pi * t : ℝ)) : ℂ)‖ := by rw [norm_mul, Complex.norm_I, mul_one]
      _ = |2 * Real.pi * t| := h1
      _ = 2 * Real.pi * |t| := h2
  have hsmall : ‖(2 * Real.pi * Complex.I * (t : ℂ))‖ ≤ 1 := by rw [hzn]; exact ht
  rw [hE, ← hzn]
  exact Complex.norm_exp_sub_one_le hsmall

/-! ## Phases of the polynomial `P` -/

/-- The phase `y ↦ e(ξ P(y))`. -/
def ph (P : Polynomial ℤ) (ξ : ℝ) (y : ℤ) : ℂ := ee (ξ * ((P.eval y : ℤ) : ℝ))

lemma ph_add (P : Polynomial ℤ) (x y : ℝ) (n : ℤ) :
    ph P (x + y) n = ph P x n * ph P y n := by
  unfold ph
  rw [← ee_add]
  congr 1
  ring

/-- The periodic part `y ↦ e(a P(y)/t)` of the phase. -/
def phT (P : Polynomial ℤ) (a : ℤ) (t : ℕ) (y : ℤ) : ℂ :=
  ee ((a : ℝ) * ((P.eval y : ℤ) : ℝ) / (t : ℝ))

lemma phT_period {P : Polynomial ℤ} {a : ℤ} {t : ℕ} (ht : 1 ≤ t) {y y' : ℤ}
    (h : (t : ℤ) ∣ y - y') : phT P a t y = phT P a t y' := by
  obtain ⟨k, hk⟩ := dvd_eval_sub_eval (P := P) h
  have htR : (t : ℝ) ≠ 0 := by positivity
  have hk' : (((P.eval y : ℤ) : ℝ) - ((P.eval y' : ℤ) : ℝ)) = (t : ℝ) * (k : ℝ) := by
    rw [← Int.cast_sub, hk]
    push_cast
    ring
  have hkey : (a : ℝ) * ((P.eval y : ℤ) : ℝ) / (t : ℝ)
      - (a : ℝ) * ((P.eval y' : ℤ) : ℝ) / (t : ℝ) = ((k * a : ℤ) : ℝ) := by
    have h1 : (a : ℝ) * ((P.eval y : ℤ) : ℝ) - (a : ℝ) * ((P.eval y' : ℤ) : ℝ)
        = (t : ℝ) * ((k * a : ℤ) : ℝ) := by
      rw [← mul_sub, hk']
      push_cast
      ring
    rw [div_sub_div_same, h1, mul_div_cancel_left₀ _ htR]
  have hAB : (a : ℝ) * ((P.eval y : ℤ) : ℝ) / (t : ℝ)
      = ((k * a : ℤ) : ℝ) + (a : ℝ) * ((P.eval y' : ℤ) : ℝ) / (t : ℝ) :=
    sub_eq_iff_eq_add.mp hkey
  rw [phT, phT, hAB, ee_add, ee_intCast, one_mul]

lemma ph_split {P : Polynomial ℤ} {a : ℤ} {t : ℕ} (ht : 1 ≤ t) (ξ : ℝ) (y : ℤ) :
    ph P ξ y = phT P a t y * ph P (ξ - (a : ℝ) / (t : ℝ)) y := by
  have ht0 : (t : ℝ) ≠ 0 := by positivity
  unfold ph phT
  rw [← ee_add]
  congr 1
  field_simp
  ring

/-! ## Window correlations -/

/-- The windowed phase correlation `∑_{y ∈ [1,N]} e(ξP(y)) f(u+y)`. -/
def winN (P : Polynomial ℤ) (ξ : ℝ) (f : ℤ → ℂ) (N : ℕ) (u : ℤ) : ℂ :=
  ∑ y ∈ Finset.Icc 1 N, ph P ξ (y : ℤ) * f (u + (y : ℤ))

/-- The same on an arbitrary block `[b+1, b+L]`. -/
def winB (P : Polynomial ℤ) (ξ : ℝ) (f : ℤ → ℂ) (b L : ℕ) (u : ℤ) : ℂ :=
  ∑ y ∈ Finset.Icc (b + 1) (b + L), ph P ξ (y : ℤ) * f (u + (y : ℤ))

lemma winN_eq_winB (P : Polynomial ℤ) (ξ : ℝ) (f : ℤ → ℂ) (N : ℕ) (u : ℤ) :
    winN P ξ f N u = winB P ξ f 0 N u := by
  unfold winN winB
  norm_num

lemma symIcc_card (L : ℕ) : (Work.Peluse.symIcc L).card = 2 * L + 1 := by
  rw [Work.Peluse.symIcc]
  have h := Int.card_Icc_of_le (a := -(L : ℤ)) (b := (L : ℤ)) (by omega)
  have h2 : ((Finset.Icc (-(L : ℤ)) (L : ℤ)).card : ℤ) = ((2 * L + 1 : ℕ) : ℤ) := by
    rw [h]; push_cast; ring
  exact_mod_cast h2

/-- The progression average at `N' = q = 1` is the `ℓ¹`-norm. -/
lemma progAvgSum_one_one (f : ℤ → ℂ) :
    Work.Peluse.progAvgSum 1 ((1 : ℕ) : ℤ) f = ∑' x : ℤ, ‖f x‖ := by
  rw [Work.Peluse.progAvgSum]
  have h1 : (∑' x : ℤ, ‖Work.Peluse.progAvg 1 ((1 : ℕ) : ℤ) f x‖)
      = ∑' x : ℤ, ‖f (x + 1)‖ := by
    apply tsum_congr
    intro x
    have hpt : Work.Peluse.progAvg 1 ((1 : ℕ) : ℤ) f x = f (x + 1) := by
      rw [Work.Peluse.progAvg, Finset.Icc_self, Finset.sum_singleton]
      norm_num
    rw [hpt]
  rw [h1]
  exact Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) (fun z : ℤ => ‖f z‖)

/-- **The fold.**  A correlation of the dual function with the character `e(ξ·)` bounds the `ℓ¹`-mass
of the windowed phase correlations `u ↦ ∑_y e(ξP(y)) f₁(u+y)`. -/
theorem fold_mass {P : Polynomial ℤ} {Ns N : ℕ} (hN : 1 ≤ N) {f₀ f₁ : ℤ → ℂ} {ξ γ : ℝ}
    (hs0 : Work.Peluse.SupportIn f₀ Ns) (hs1 : Work.Peluse.SupportIn f₁ Ns)
    (hb0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1)
    (hξ : γ * (Ns : ℝ) ≤
      ‖∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x * ee (ξ * (x : ℝ))‖) :
    γ * (Ns : ℝ) * (N : ℝ) ≤ ∑ u ∈ Work.Peluse.symIcc Ns, ‖winN P ξ f₁ N u‖ := by
  classical
  have hfin0 : Work.Peluse.FinSuppZ f₀ := Work.Peluse.FinSuppZ.of_supportIn hs0
  have hfin1 : Work.Peluse.FinSuppZ f₁ := Work.Peluse.FinSuppZ.of_supportIn hs1
  have hunf := dualFn_fourier_unfold hN P hfin0 hfin1 ξ
  have hexpeq : ∀ x : ℤ,
      Complex.exp (2 * Real.pi * Complex.I * ξ * (x : ℝ)) = ee (ξ * (x : ℝ)) := by
    intro x; unfold ee; congr 1; push_cast; ring
  simp only [hexpeq] at hunf
  have hsupp0 : ∀ u : ℤ, u ∉ Work.Peluse.symIcc Ns → f₀ u = 0 := by
    intro u hu
    refine hs0 u ?_
    rw [progAvgSum_mem_symIcc_iff_natAbs] at hu
    exact not_le.mp hu
  have hkey : (∑ y ∈ Finset.Icc 1 N, ee (ξ * ((P.eval (y : ℤ) : ℤ) : ℝ)) *
          (∑' u : ℤ, f₀ u * ee (ξ * (u : ℝ)) * f₁ (u + (y : ℤ))))
      = ∑ u ∈ Work.Peluse.symIcc Ns, (f₀ u * ee (ξ * (u : ℝ))) * winN P ξ f₁ N u := by
    have hinner : ∀ y : ℤ, (∑' u : ℤ, f₀ u * ee (ξ * (u : ℝ)) * f₁ (u + y))
        = ∑ u ∈ Work.Peluse.symIcc Ns, f₀ u * ee (ξ * (u : ℝ)) * f₁ (u + y) := by
      intro y
      refine tsum_eq_sum (s := Work.Peluse.symIcc Ns) (fun u hu => ?_)
      rw [hsupp0 u hu, zero_mul, zero_mul]
    simp only [hinner, winN, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    refine Finset.sum_congr rfl (fun y hy => ?_)
    simp only [ph]
    ring
  rw [hkey] at hunf
  have h2 : γ * (Ns : ℝ) ≤ ‖((N : ℂ))⁻¹‖ *
      ‖∑ u ∈ Work.Peluse.symIcc Ns, (f₀ u * ee (ξ * (u : ℝ))) * winN P ξ f₁ N u‖ := by
    calc γ * (Ns : ℝ) ≤ ‖((N : ℂ))⁻¹ *
          ∑ u ∈ Work.Peluse.symIcc Ns, (f₀ u * ee (ξ * (u : ℝ))) * winN P ξ f₁ N u‖ := by
          rw [← hunf]; exact hξ
      _ = _ := norm_mul _ _
  rw [norm_inv, Complex.norm_natCast] at h2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h3 : γ * (Ns : ℝ) * (N : ℝ) ≤
      ‖∑ u ∈ Work.Peluse.symIcc Ns, (f₀ u * ee (ξ * (u : ℝ))) * winN P ξ f₁ N u‖ := by
    have h := mul_le_mul_of_nonneg_right h2 (le_of_lt hNpos)
    have h' : ((N : ℝ)⁻¹ *
        ‖∑ u ∈ Work.Peluse.symIcc Ns, (f₀ u * ee (ξ * (u : ℝ))) * winN P ξ f₁ N u‖) * (N : ℝ)
        = ‖∑ u ∈ Work.Peluse.symIcc Ns, (f₀ u * ee (ξ * (u : ℝ))) * winN P ξ f₁ N u‖ := by
      rw [mul_comm ((N : ℝ)⁻¹), mul_assoc, inv_mul_cancel₀ (ne_of_gt hNpos), mul_one]
    rw [h'] at h
    exact h
  refine le_trans h3 (le_trans (norm_sum_le _ _) ?_)
  refine Finset.sum_le_sum (fun u hu => ?_)
  rw [norm_mul, norm_mul, norm_ee, mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb0 u)

/-! ## The main theorem -/

/-- **Peluse's §9 at the correlation level** for the progression `(x, x+y, x+P(y))`. -/
theorem ss_corr_to_prog {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h1 : Work.Peluse.PeluseU2Inverse) (h2 : Work.Peluse.PeluseMajorArc P) :
    ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
      ∀ (Ns N : ℕ) (f₀ f₁ : ℤ → ℂ) (γ : ℝ),
        1 ≤ N → 1 ≤ Ns → Work.Peluse.Scaled Ns N P.natDegree → N ≤ Ns →
        Work.Peluse.SupportIn f₀ Ns → Work.Peluse.SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        0 < γ → γ ≤ 1 →
        (∃ ξ : ℝ, γ * (Ns : ℝ) ≤ ‖∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x *
            Complex.exp (2 * Real.pi * Complex.I * ξ * (x : ℝ))‖) →
        ∃ q N' : ℕ, 1 ≤ q ∧
          (q : ℝ) ≤ (C : ℝ) * (γ⁻¹) ^ K ∧
          1 ≤ N' ∧ N' ≤ N ∧
          γ ^ K * (N : ℝ) / (C : ℝ) ≤ (N' : ℝ) ∧
          γ ^ K * (Ns : ℝ) / (C : ℝ) ≤ Work.Peluse.progAvgSum N' (q : ℤ) f₁ := by
  classical
  obtain ⟨Cc, hCcpos, Kh, hKh, hMA⟩ := h2
  obtain ⟨CP, hCPpos, hCP⟩ := poly_diff_bound P (by omega)
  -- the numerical constants
  set K1 : ℝ := max 1024 (max (1024 / CP) (1024 * Cc)) with hK1
  have hK1pos : (0 : ℝ) < K1 := lt_max_of_lt_left (by norm_num)
  have hK1CP : 8 ≤ K1 * CP := by
    have h1 : 1024 / CP ≤ K1 := le_trans (le_max_left _ _) (le_max_right _ _)
    have h2 : (1024 / CP) * CP = 1024 := div_mul_cancel₀ 1024 (ne_of_gt hCPpos)
    nlinarith [h1, h2, hCPpos]
  have hK1pi : 256 * Real.pi ≤ K1 := by
    have h1 : (1024 : ℝ) ≤ K1 := le_max_left _ _
    nlinarith [h1, Real.pi_lt_four]
  set CD : ℝ := max 8 (max Cc (K1 * Cc * CP)) with hCD
  have hCD8 : (8 : ℝ) ≤ CD := le_max_left _ _
  have hCDc : Cc ≤ CD := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCDK : K1 * Cc * CP ≤ CD := le_trans (le_max_right _ _) (le_max_right _ _)
  set Cnat : ℕ := 4 * (⌈CD⌉₊ + 1) with hCnat
  have hCnat_ge : CD ≤ (Cnat : ℝ) := by
    have h1 : CD ≤ (⌈CD⌉₊ : ℝ) := Nat.le_ceil CD
    have h2 : ((⌈CD⌉₊ : ℝ) + 1) ≤ (Cnat : ℝ) := by
      rw [hCnat]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈CD⌉₊]
    linarith
  have hCnat8 : (8 : ℝ) ≤ (Cnat : ℝ) := le_trans hCD8 hCnat_ge
  have hCnatc : Cc ≤ (Cnat : ℝ) := le_trans hCDc hCnat_ge
  have hCnatK : K1 * Cc * CP ≤ (Cnat : ℝ) := le_trans hCDK hCnat_ge
  have hCnat2K : 2 * (K1 * Cc * CP) ≤ (Cnat : ℝ) := by
    have h : 2 * CD ≤ (Cnat : ℝ) := by
      have h1 : CD ≤ (⌈CD⌉₊ : ℝ) := Nat.le_ceil CD
      rw [hCnat]; push_cast; linarith
    linarith [hCDK]
  refine ⟨Cnat, Kh + 1, by omega, by omega, ?_⟩
  intro Ns N f₀ f₁ γ hN1 hNs1 hScaled hNNs hs0 hs1 hb0 hb1 hγ0 hγ1 hcorr
  obtain ⟨ξ, hξ⟩ := hcorr
  have hξ' : γ * (Ns : ℝ) ≤
      ‖∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x * ee (ξ * (x : ℝ))‖ := by
    have h : (∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x *
          Complex.exp (2 * Real.pi * Complex.I * ξ * (x : ℝ)))
        = ∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x * ee (ξ * (x : ℝ)) := by
      apply tsum_congr; intro x
      unfold ee
      congr 1
      push_cast
      try ring
    rwa [h] at hξ
  -- ### the `ℓ¹`-mass of `f₁`
  have hmass : γ * (Ns : ℝ) ≤ ∑' x : ℤ, ‖f₁ x‖ := by
    have hfin1 : Work.Peluse.FinSuppZ f₁ := Work.Peluse.FinSuppZ.of_supportIn hs1
    have hFsup : Work.Peluse.SupportIn (Work.Peluse.dualFn N P f₀ f₁) (Work.Peluse.dSup P Ns N) :=
      Work.Peluse.Tools.dualFn_supportIn hN1 P f₀ f₁ hs0 hs1 hNNs
    set S : Finset ℤ := Work.Peluse.symIcc (Work.Peluse.dSup P Ns N) with hS
    have hz1 : ∀ x : ℤ, x ∉ S → Work.Peluse.dualFn N P f₀ f₁ x * ee (ξ * (x : ℝ)) = 0 := by
      intro x hx
      rw [hS, progAvgSum_mem_symIcc_iff_natAbs] at hx
      rw [hFsup x (not_le.mp hx), zero_mul]
    have hz2 : ∀ x : ℤ, x ∉ S → ‖Work.Peluse.dualFn N P f₀ f₁ x‖ = 0 := by
      intro x hx
      rw [hS, progAvgSum_mem_symIcc_iff_natAbs] at hx
      rw [norm_eq_zero, hFsup x (not_le.mp hx)]
    have hbnd : ‖∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x * ee (ξ * (x : ℝ))‖
        ≤ ∑' x : ℤ, ‖Work.Peluse.dualFn N P f₀ f₁ x‖ := by
      rw [tsum_eq_sum (s := S) hz1, tsum_eq_sum (s := S) hz2]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun x hx => ?_))
      rw [norm_mul, norm_ee, mul_one]
    exact le_trans hξ' (le_trans hbnd (dualFn_tsum_le hN1 P f₀ f₁ hb0 hfin1))
  -- ### the rational structure of `ξ`
  obtain ⟨t, ht1, htle, htdist⟩ := hMA Ns N f₀ f₁ ξ γ hd hNs1 hN1 hγ0 hγ1 hs0 hs1 hb0 hb1 hξ
  rcases le_or_gt (γ ^ (Kh + 1) * (N : ℝ)) (Cnat : ℝ) with heasy | hhard
  · -- #### the easy case `N' = q = 1`
    refine ⟨1, 1, le_rfl, ?_, le_rfl, hN1, ?_, ?_⟩
    · have hg1 : (1 : ℝ) ≤ γ⁻¹ := (one_le_inv₀ hγ0).mpr hγ1
      have hinv1 : (1 : ℝ) ≤ (γ⁻¹) ^ (Kh + 1) := one_le_pow₀ hg1
      nlinarith [hCnat8, hinv1]
    · rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Cnat : ℝ))]
      simpa using heasy
    · rw [progAvgSum_one_one]
      have hNsR : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast hNs1
      have hpow : γ ^ (Kh + 1) ≤ γ * (Cnat : ℝ) := by
        have h3 : γ ^ (Kh + 1) ≤ γ := by
          calc γ ^ (Kh + 1) = γ ^ Kh * γ := by rw [pow_succ]
            _ ≤ 1 * γ := mul_le_mul_of_nonneg_right (pow_le_one₀ (le_of_lt hγ0) hγ1) (le_of_lt hγ0)
            _ = γ := one_mul γ
        nlinarith [hCnat8]
      have hle : γ ^ (Kh + 1) * (Ns : ℝ) / (Cnat : ℝ) ≤ γ * (Ns : ℝ) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Cnat : ℝ))]
        nlinarith [hpow, hNsR]
      exact le_trans hle hmass
  · -- #### the hard case
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hNsR : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast hNs1
    have hNs1' : (1 : ℝ) ≤ (Ns : ℝ) := by exact_mod_cast hNs1
    have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
    have hgam_ne : (γ : ℝ) ^ Kh ≠ 0 := by positivity
    obtain ⟨a, haeq⟩ : ∃ a : ℤ, |(t : ℝ) * ξ - (a : ℝ)| = distInt ((t : ℝ) * ξ) :=
      ⟨round ((t : ℝ) * ξ), rfl⟩
    set βr : ℝ := ξ - (a : ℝ) / (t : ℝ) with hβr
    have hβle : |βr| ≤ Cc * (γ⁻¹) ^ Kh / ((N : ℝ) ^ P.natDegree * (t : ℝ)) := by
      have hmul : (t : ℝ) * |βr| = |(t : ℝ) * ξ - (a : ℝ)| := by
        have h1 : (t : ℝ) * βr = (t : ℝ) * ξ - (a : ℝ) := by
          rw [hβr, mul_sub, mul_div_cancel₀ _ (ne_of_gt htR)]
        rw [← h1, abs_mul, abs_of_pos htR]
      have h2 : (t : ℝ) * |βr| ≤ Cc * (γ⁻¹) ^ Kh / (N : ℝ) ^ P.natDegree := by
        rw [hmul, haeq]; exact htdist
      have h3 : |βr| * ((N : ℝ) ^ P.natDegree * (t : ℝ)) ≤ Cc * (γ⁻¹) ^ Kh := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ P.natDegree)] at h2
        nlinarith [h2]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ P.natDegree * (t : ℝ))]
      linarith [h3]
    -- the window parameters
    have hden : (0 : ℝ) < K1 * Cc * CP := by positivity
    set xg : ℝ := γ ^ (Kh + 1) * (N : ℝ) / (K1 * Cc * CP) with hxg
    have hxg1 : ((1 : ℕ) : ℝ) ≤ xg := by
      have h0 : K1 * Cc * CP ≤ γ ^ (Kh + 1) * (N : ℝ) := le_trans hCnatK (le_of_lt hhard)
      rw [hxg, le_div_iff₀ hden]
      simpa using h0
    set Mr : ℕ := min N ⌊xg⌋₊ with hMr
    have hMr1 : 1 ≤ Mr := le_min hN1 (Nat.le_floor hxg1)
    have hMrN : Mr ≤ N := min_le_left _ _
    have hMrle : (Mr : ℝ) ≤ xg := by
      rw [hMr]
      calc (((min N ⌊xg⌋₊ : ℕ)) : ℝ) ≤ ((⌊xg⌋₊ : ℕ) : ℝ) := by
            exact_mod_cast min_le_right N ⌊xg⌋₊
        _ ≤ xg := Nat.floor_le (le_of_lt (by rw [hxg]; positivity))
    have hMrlo : γ ^ (Kh + 1) * (N : ℝ) / (Cnat : ℝ) ≤ (Mr : ℝ) := by
      rcases le_or_gt (⌊xg⌋₊) N with hc | hc
      · have h1 : Mr = ⌊xg⌋₊ := min_eq_right hc
        have h2 : xg / 2 ≤ ((⌊xg⌋₊ : ℕ) : ℝ) := by
          rcases le_or_gt xg 2 with hc2 | hc2
          · have h4 : (1:ℝ) ≤ ((⌊xg⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_floor hxg1
            linarith
          · have h4 : ((⌊xg⌋₊ : ℕ) : ℝ) ≤ xg := Nat.floor_le (le_of_lt (by rw [hxg]; positivity))
            have h5 : xg - 1 ≤ ((⌊xg⌋₊ : ℕ) : ℝ) := by
              have := Nat.lt_floor_add_one xg
              linarith
            linarith
        rw [h1]
        have h6 : γ ^ (Kh + 1) * (N : ℝ) / (Cnat : ℝ) ≤ xg / 2 := by
          rw [hxg, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have h7 : (K1 * Cc * CP) * 2 ≤ (Cnat : ℝ) := by rw [mul_comm]; exact hCnat2K
          calc γ ^ (Kh + 1) * (N : ℝ) * ((K1 * Cc * CP) * 2)
              = (γ ^ (Kh + 1) * (N : ℝ)) * ((K1 * Cc * CP) * 2) := by ring
            _ ≤ (γ ^ (Kh + 1) * (N : ℝ)) * (Cnat : ℝ) :=
                mul_le_mul_of_nonneg_left h7 (by positivity)
        exact le_trans h6 h2
      · have h1 : Mr = N := min_eq_left (le_of_lt hc)
        rw [h1, div_le_iff₀ (by positivity : (0:ℝ) < (Cnat:ℝ))]
        have hg : γ ^ (Kh + 1) ≤ 1 := pow_le_one₀ (le_of_lt hγ0) hγ1
        have hg2 : γ ^ (Kh + 1) ≤ (Cnat : ℝ) := le_trans hg (by linarith [hCnat8])
        calc γ ^ (Kh + 1) * (N : ℝ) ≤ (Cnat : ℝ) * (N : ℝ) :=
              mul_le_mul_of_nonneg_right hg2 (le_of_lt hNpos)
          _ = (N : ℝ) * (Cnat : ℝ) := by ring
    set Lr : ℕ := t * Mr with hLr
    have hLr1 : 1 ≤ Lr := by
      rw [hLr]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hLrA : (Lr : ℝ) ≤ γ ^ (Kh + 1) * (t : ℝ) * (N : ℝ) / (K1 * Cc * CP) := by
      rw [hLr, Nat.cast_mul]
      calc (t : ℝ) * (Mr : ℝ) ≤ (t : ℝ) * xg :=
            mul_le_mul_of_nonneg_left hMrle (by positivity)
        _ = γ ^ (Kh + 1) * (t : ℝ) * (N : ℝ) / (K1 * Cc * CP) := by rw [hxg]; ring
    have htk : (t : ℝ) * γ ^ (Kh + 1) ≤ Cc * γ := by
      have h1 : (t : ℝ) * γ ^ (Kh + 1) ≤ (Cc * (γ⁻¹) ^ Kh) * γ ^ (Kh + 1) :=
        mul_le_mul_of_nonneg_right htle (by positivity)
      have h2 : (Cc * (γ⁻¹) ^ Kh) * γ ^ (Kh + 1) = Cc * γ := by
        rw [inv_pow, pow_succ]
        calc Cc * (γ ^ Kh)⁻¹ * (γ ^ Kh * γ)
            = Cc * ((γ ^ Kh)⁻¹ * γ ^ Kh) * γ := by ring
          _ = Cc * 1 * γ := by rw [inv_mul_cancel₀ hgam_ne]
          _ = Cc * γ := by ring
      rwa [h2] at h1
    have hLrB : (Lr : ℝ) ≤ γ * (N : ℝ) / (K1 * CP) := by
      refine le_trans hLrA ?_
      have h1 : ℕ := 0
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc γ ^ (Kh + 1) * (t : ℝ) * (N : ℝ) * ((K1 : ℝ) * CP)
          = ((t : ℝ) * γ ^ (Kh + 1)) * ((N : ℝ) * ((K1 : ℝ) * CP)) := by ring
        _ ≤ (Cc * γ) * ((N : ℝ) * ((K1 : ℝ) * CP)) :=
            mul_le_mul_of_nonneg_right htk (by positivity)
        _ = γ * (N : ℝ) * ((K1 : ℝ) * Cc * CP) := by ring
    have hLr8 : (Lr : ℝ) ≤ γ * (N : ℝ) / 8 := by
      refine le_trans hLrB ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      calc γ * (N : ℝ) * 8 = 8 * (γ * (N : ℝ)) := by ring
        _ ≤ ((K1 : ℝ) * CP) * (γ * (N : ℝ)) :=
            mul_le_mul_of_nonneg_right hK1CP (by positivity)
        _ = γ * (N : ℝ) * ((K1 : ℝ) * CP) := by ring
    have hLrN : Lr ≤ N := by
      have h1 : (Lr : ℝ) ≤ (N : ℝ) := by
        refine le_trans hLr8 ?_
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 8)]
        nlinarith [hγ1, hNpos]
      exact_mod_cast h1
    -- the block decomposition
    set Jn : ℕ := N / Lr with hJn
    have hJL : Jn * Lr ≤ N := Nat.div_mul_le_self N Lr
    have hJ1 : 1 ≤ Jn := Nat.one_le_div_iff (by omega : 0 < Lr) |>.mpr hLrN
    have hrem_lt : N - Jn * Lr < Lr := by
      have h2 : Jn * Lr + N % Lr = N := by
        rw [hJn]
        exact Nat.div_add_mod' N Lr
      have h3 : N % Lr < Lr := Nat.mod_lt N (by omega)
      omega
    have hrem : ((N - Jn * Lr : ℕ) : ℝ) ≤ γ * (N : ℝ) / 8 := by
      have h2 : ((N - Jn * Lr : ℕ) : ℝ) < (Lr : ℝ) := by exact_mod_cast hrem_lt
      linarith [h2, hLr8]
    have hblk : ∀ u : ℤ, ‖winN P ξ f₁ N u‖ ≤
        (∑ j ∈ Finset.Icc 1 Jn, ‖winB P ξ f₁ ((j - 1) * Lr) Lr u‖)
          + ((N - Jn * Lr : ℕ) : ℝ) := by
      intro u
      rw [winN_eq_winB]
      have h0 : winB P ξ f₁ 0 N u
          = ∑ y ∈ Finset.Icc 1 N, ph P ξ (y : ℤ) * f₁ (u + (y : ℤ)) := by
        unfold winB; norm_num
      rw [h0, sum_Icc_block_decomp (L := Lr) (J := Jn) (N := N) hLr1 hJL
        (fun y : ℕ => ph P ξ (y : ℤ) * f₁ (u + (y : ℤ)))]
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · have h2 : (∑ j ∈ Finset.Icc 1 Jn,
              ‖∑ y ∈ Finset.Icc ((j - 1) * Lr + 1) (j * Lr),
                ph P ξ (y : ℤ) * f₁ (u + (y : ℤ))‖)
            ≤ ∑ j ∈ Finset.Icc 1 Jn, ‖winB P ξ f₁ ((j - 1) * Lr) Lr u‖ := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          have hset : j * Lr = (j - 1) * Lr + Lr := by
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            conv_lhs => rw [← Nat.sub_add_cancel hj1]
            rw [Nat.add_mul, one_mul]
          rw [hset]
          exact le_of_eq (by unfold winB; rfl)
        exact le_trans (norm_sum_le (Finset.Icc 1 Jn)
          (fun j => ∑ y ∈ Finset.Icc ((j - 1) * Lr + 1) (j * Lr),
            ph P ξ (y : ℤ) * f₁ (u + (y : ℤ)))) h2
      · have h1 : ‖∑ y ∈ Finset.Icc (Jn * Lr + 1) N, ph P ξ (y : ℤ) * f₁ (u + (y : ℤ))‖
            ≤ ∑ y ∈ Finset.Icc (Jn * Lr + 1) N, ‖ph P ξ (y : ℤ) * f₁ (u + (y : ℤ))‖ :=
          norm_sum_le _ _
        have h3 : ∑ y ∈ Finset.Icc (Jn * Lr + 1) N, ‖ph P ξ (y : ℤ) * f₁ (u + (y : ℤ))‖
            ≤ ∑ y ∈ Finset.Icc (Jn * Lr + 1) N, (1 : ℝ) :=
          Finset.sum_le_sum (fun y hy => by
            have hp : ‖ph P ξ (y : ℤ)‖ = 1 := by simp only [ph]; exact norm_ee _
            rw [norm_mul, hp, one_mul]
            exact hb1 _)
        have h4 : ∑ y ∈ Finset.Icc (Jn * Lr + 1) N, (1 : ℝ)
            = ((N - Jn * Lr : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [Nat.card_Icc]
          have hcard : N + 1 - (Jn * Lr + 1) = N - Jn * Lr :=
            Nat.add_sub_add_right N 1 (Jn * Lr)
          rw [hcard]
        exact le_trans h1 (le_trans h3 (le_of_eq h4))
    -- sum over `u`
    have hsum : γ * (Ns : ℝ) * (N : ℝ) / 2 ≤
        ∑ j ∈ Finset.Icc 1 Jn, ∑ u ∈ Work.Peluse.symIcc Ns, ‖winB P ξ f₁ ((j - 1) * Lr) Lr u‖ := by
      have hfold := fold_mass (P := P) (Ns := Ns) (N := N) hN1 hs0 hs1 hb0 hξ'
      have h1 : ∑ u ∈ Work.Peluse.symIcc Ns, ‖winN P ξ f₁ N u‖ ≤
          (∑ u ∈ Work.Peluse.symIcc Ns,
              ∑ j ∈ Finset.Icc 1 Jn, ‖winB P ξ f₁ ((j - 1) * Lr) Lr u‖)
            + ((Work.Peluse.symIcc Ns).card : ℝ) * ((N - Jn * Lr : ℕ) : ℝ) := by
        calc ∑ u ∈ Work.Peluse.symIcc Ns, ‖winN P ξ f₁ N u‖
            ≤ ∑ u ∈ Work.Peluse.symIcc Ns,
                ((∑ j ∈ Finset.Icc 1 Jn, ‖winB P ξ f₁ ((j - 1) * Lr) Lr u‖)
                  + ((N - Jn * Lr : ℕ) : ℝ)) :=
              Finset.sum_le_sum (fun u hu => hblk u)
          _ = _ := by
              rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [Finset.sum_comm] at h1
      have hcard : ((Work.Peluse.symIcc Ns).card : ℝ) = 2 * (Ns : ℝ) + 1 := by
        rw [symIcc_card]; push_cast; ring
      have hterm : ((Work.Peluse.symIcc Ns).card : ℝ) * ((N - Jn * Lr : ℕ) : ℝ)
          ≤ γ * (Ns : ℝ) * (N : ℝ) / 2 := by
        rw [hcard]
        have hNs1' : (1 : ℝ) ≤ (Ns : ℝ) := by exact_mod_cast hNs1
        have h1 : (2 * (Ns : ℝ) + 1) ≤ 4 * (Ns : ℝ) := by linarith
        have h2 : ((N - Jn * Lr : ℕ) : ℝ) ≤ γ * (N : ℝ) / 8 := hrem
        calc (2 * (Ns : ℝ) + 1) * ((N - Jn * Lr : ℕ) : ℝ)
            ≤ (4 * (Ns : ℝ)) * (γ * (N : ℝ) / 8) :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = γ * (Ns : ℝ) * (N : ℝ) / 2 := by ring_nf
      linarith [hfold, h1, hterm]
    -- pigeonhole over the blocks
    obtain ⟨j₀, hj₀mem, hj₀max⟩ := Finset.exists_max_image (Finset.Icc 1 Jn)
      (fun j => ∑ u ∈ Work.Peluse.symIcc Ns, ‖winB P ξ f₁ ((j - 1) * Lr) Lr u‖)
      ⟨1, by simp [hJ1]⟩
    have hj₀lb : γ * (Ns : ℝ) * (Lr : ℝ) / 2 ≤
        ∑ u ∈ Work.Peluse.symIcc Ns, ‖winB P ξ f₁ ((j₀ - 1) * Lr) Lr u‖ := by
      have hcardJ : ((Finset.Icc 1 Jn).card : ℝ) = (Jn : ℝ) := by
        rw [Nat.card_Icc]; simp
      have hmax : ∑ j ∈ Finset.Icc 1 Jn,
            ∑ u ∈ Work.Peluse.symIcc Ns, ‖winB P ξ f₁ ((j - 1) * Lr) Lr u‖
          ≤ (Jn : ℝ) * ∑ u ∈ Work.Peluse.symIcc Ns, ‖winB P ξ f₁ ((j₀ - 1) * Lr) Lr u‖ := by
        calc ∑ j ∈ Finset.Icc 1 Jn,
              ∑ u ∈ Work.Peluse.symIcc Ns, ‖winB P ξ f₁ ((j - 1) * Lr) Lr u‖
            ≤ ∑ j ∈ Finset.Icc 1 Jn,
                ∑ u ∈ Work.Peluse.symIcc Ns, ‖winB P ξ f₁ ((j₀ - 1) * Lr) Lr u‖ :=
              Finset.sum_le_sum (fun j hj => hj₀max j hj)
          _ = (Finset.Icc 1 Jn).card •
                ∑ u ∈ Work.Peluse.symIcc Ns, ‖winB P ξ f₁ ((j₀ - 1) * Lr) Lr u‖ :=
              Finset.sum_const _
          _ = _ := by rw [nsmul_eq_mul]; rw [hcardJ]
      have hJnLr : (Jn : ℝ) * (Lr : ℝ) ≤ (N : ℝ) := by exact_mod_cast hJL
      have hJnpos : (0 : ℝ) < (Jn : ℝ) := by exact_mod_cast hJ1
      have h2 : γ * (Ns : ℝ) * (N : ℝ) / 2 / (Jn : ℝ) ≤
          ∑ u ∈ Work.Peluse.symIcc Ns, ‖winB P ξ f₁ ((j₀ - 1) * Lr) Lr u‖ := by
        rw [div_le_iff₀ hJnpos]
        nlinarith [hsum, hmax]
      have h3 : γ * (Ns : ℝ) * (Lr : ℝ) / 2 ≤
          γ * (Ns : ℝ) * (N : ℝ) / 2 / (Jn : ℝ) := by
        rw [div_div, le_div_iff₀ (by positivity : (0:ℝ) < 2 * (Jn:ℝ))]
        calc γ * (Ns : ℝ) * (Lr : ℝ) / 2 * (2 * (Jn : ℝ))
            = γ * (Ns : ℝ) * ((Jn : ℝ) * (Lr : ℝ)) := by ring
          _ ≤ γ * (Ns : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_left hJnLr (by positivity)
      linarith [h2, h3]
    -- the phase approximation on the block `j₀`
    set b0 : ℕ := (j₀ - 1) * Lr with hb0
    have hb0t : (t : ℤ) ∣ (b0 : ℤ) := by
      rw [hb0, hLr, Nat.cast_mul, Nat.cast_mul]
      exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
    -- per-term phase bound
    have hphase : ∀ (u : ℤ) (m r : ℕ), m ∈ Finset.Icc 1 Mr → r ∈ Finset.Icc 1 t →
        ‖ph P ξ ((b0 + (m - 1) * t + r : ℕ) : ℤ)
            * f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))
          - ph P βr ((b0 + 1 : ℕ) : ℤ) * phT P a t (r : ℤ)
            * f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖
        ≤ (γ / 16) * ‖f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖ := by
      intro u m r hm hr
      set Y : ℕ := b0 + (m - 1) * t + r with hY
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmM : m ≤ Mr := (Finset.mem_Icc.mp hm).2
      have hrt : r ≤ t := (Finset.mem_Icc.mp hr).2
      have hper : phT P a t ((Y : ℕ) : ℤ) = phT P a t (r : ℤ) := by
        rw [hY]
        refine phT_period ht1 ?_
        have hkey : (((b0 + (m - 1) * t + r : ℕ)) : ℤ) - (r : ℤ)
            = (b0 : ℤ) + ((m : ℤ) - 1) * (t : ℤ) := by
          push_cast [Nat.cast_sub hm1]
          ring
        rw [hkey]
        exact dvd_add hb0t (dvd_mul_left (t : ℤ) ((m : ℤ) - 1))
      have hsp : ph P ξ ((Y : ℕ) : ℤ)
          = phT P a t (r : ℤ) * ph P βr ((Y : ℕ) : ℤ) := by
        rw [← hper]; exact ph_split ht1 ξ _
      have hj₀le : j₀ * Lr ≤ N :=
        le_trans (Nat.mul_le_mul_right Lr (Finset.mem_Icc.mp hj₀mem).2) hJL
      have hbLr : b0 + Lr = j₀ * Lr := by
        rw [hb0]
        conv_rhs => rw [← Nat.sub_add_cancel (Finset.mem_Icc.mp hj₀mem).1]
        rw [Nat.add_mul, one_mul]
      have hYN : Y ≤ N := by
        have h1 : (m - 1) * t + r ≤ t * Mr := by
          have h2 : (m - 1) * t ≤ (Mr - 1) * t :=
            Nat.mul_le_mul_right t (Nat.sub_le_sub_right hmM 1)
          have h4 : (Mr - 1) * t + t = t * Mr := by
            rw [Nat.mul_comm t Mr]
            conv_rhs => rw [← Nat.sub_add_cancel hMr1]
            rw [Nat.add_mul, one_mul]
          calc (m - 1) * t + r ≤ (Mr - 1) * t + t := Nat.add_le_add h2 hrt
            _ = t * Mr := h4
        rw [hY, Nat.add_assoc]
        calc b0 + ((m - 1) * t + r) ≤ b0 + t * Mr := Nat.add_le_add_left h1 b0
          _ = b0 + Lr := by rw [hLr]
          _ = j₀ * Lr := hbLr
          _ ≤ N := hj₀le
      have hbN : b0 + 1 ≤ N := by
        have h4 : (j₀ - 1) * Lr + 1 ≤ j₀ * Lr := by
          rw [← hbLr]
          omega
        omega
      have hbd := hCP N Y (b0 + 1) hN1 hYN hbN
      have hd : |(Y : ℝ) - ((b0 + 1 : ℕ) : ℝ)| ≤ (Lr : ℝ) := by
        have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        have h1 : b0 + 1 ≤ Y := by
          rw [hY, Nat.add_assoc]
          exact Nat.add_le_add_left (le_trans hr1 (Nat.le_add_left r ((m - 1) * t))) b0
        have h2 : Y ≤ b0 + 1 + Lr := by
          have h3 : (m - 1) * t + r ≤ t * Mr := by
            have h4 : (m - 1) * t ≤ (Mr - 1) * t :=
              Nat.mul_le_mul_right t (Nat.sub_le_sub_right hmM 1)
            have h6 : (Mr - 1) * t + t = t * Mr := by
              rw [Nat.mul_comm t Mr]
              conv_rhs => rw [← Nat.sub_add_cancel hMr1]
              rw [Nat.add_mul, one_mul]
            calc (m - 1) * t + r ≤ (Mr - 1) * t + t := Nat.add_le_add h4 hrt
              _ = t * Mr := h6
          rw [hY, Nat.add_assoc]
          calc b0 + ((m - 1) * t + r) ≤ b0 + t * Mr := Nat.add_le_add_left h3 b0
            _ = b0 + Lr := by rw [hLr]
            _ ≤ b0 + 1 + Lr := by omega
        have h7 : (Y : ℝ) - ((b0 + 1 : ℕ) : ℝ) ≤ (Lr : ℝ) := by
          have h9 : Y - (b0 + 1) ≤ Lr := Nat.sub_le_iff_le_add.mpr (by omega)
          rw [← Nat.cast_sub h1]
          exact_mod_cast h9
        rw [abs_of_nonneg (by
          have h5 : ((b0 + 1 : ℕ) : ℝ) ≤ (Y : ℝ) := by exact_mod_cast h1
          linarith)]
        exact h7
      have hmain : |βr| * (CP * (N : ℝ) ^ (P.natDegree - 1) * (Lr : ℝ)) ≤ γ / 1024 := by
        have hstep : |βr| * (CP * (N : ℝ) ^ (P.natDegree - 1) * (Lr : ℝ))
            ≤ (Cc * (γ⁻¹) ^ Kh / ((N : ℝ) ^ P.natDegree * (t : ℝ)))
              * (CP * (N : ℝ) ^ (P.natDegree - 1)
                  * (γ ^ (Kh + 1) * (t : ℝ) * (N : ℝ) / (K1 * Cc * CP))) :=
          mul_le_mul hβle (mul_le_mul_of_nonneg_left hLrA (by positivity)) (by positivity) (by positivity)
        refine le_trans hstep ?_
        have hfac : (Cc * (γ⁻¹) ^ Kh / ((N : ℝ) ^ P.natDegree * (t : ℝ)))
              * (CP * (N : ℝ) ^ (P.natDegree - 1)
                  * (γ ^ (Kh + 1) * (t : ℝ) * (N : ℝ) / (K1 * Cc * CP)))
            = (γ / K1) * ((N : ℝ) ^ (P.natDegree - 1) * (N : ℝ) / (N : ℝ) ^ P.natDegree) := by
          rw [inv_pow, pow_succ]
          field_simp
          try ring
        have hNd : (N : ℝ) ^ (P.natDegree - 1) * (N : ℝ) = (N : ℝ) ^ P.natDegree := by
          conv_rhs => rw [show P.natDegree = (P.natDegree - 1) + 1 by omega]
          rw [pow_succ]
        rw [hfac, hNd, div_self (by positivity : (N : ℝ) ^ P.natDegree ≠ 0), mul_one]
        have h2 : γ / K1 ≤ γ / 1024 := by
          have h1024 : (1024 : ℝ) ≤ K1 := by rw [hK1]; exact le_max_left _ _
          rw [div_le_div_iff₀ hK1pos (by norm_num : (0 : ℝ) < 1024)]
          nlinarith [h1024, hγ0]
        exact h2
      have hbound1 : ‖ph P βr ((Y : ℕ) : ℤ) - ph P βr (((b0 + 1 : ℕ)) : ℤ)‖ ≤ γ / 16 := by
        simp only [ph]
        rw [norm_ee_sub_eq]
        set Dy : ℝ := βr * ((P.eval (Y : ℤ) : ℤ) : ℝ) - βr * ((P.eval ((b0 + 1 : ℕ) : ℤ) : ℤ) : ℝ) with hDy
        have hΔ : |Dy| ≤ γ / 1024 := by
          have hfac2 : Dy = βr * (((P.eval (Y : ℤ) : ℤ) : ℝ)
              - ((P.eval ((b0 + 1 : ℕ) : ℤ) : ℤ) : ℝ)) := by rw [hDy]; ring
          have hΔ1 : |Dy| ≤ |βr| * (CP * (N : ℝ) ^ (P.natDegree - 1) * (Lr : ℝ)) := by
            rw [hfac2, abs_mul]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [← (show ((P.eval ((Y : ℕ) : ℤ) : ℤ) : ℝ) = ((P.eval (Y : ℤ) : ℤ) : ℝ) by push_cast; ring)]
            exact le_trans hbd (mul_le_mul_of_nonneg_left hd (by positivity))
          exact le_trans hΔ1 hmain
        have hsmall : 2 * Real.pi * |Dy| ≤ 1 := by
          have h6 : 2 * Real.pi * (γ / 1024) ≤ 1 := by nlinarith [Real.pi_lt_four, hγ0, hγ1]
          nlinarith [hΔ, h6, Real.pi_pos]
        have hstep2 : ‖ee Dy - 1‖ ≤ 2 * (2 * Real.pi * |Dy|) := norm_ee_sub_one_le hsmall
        have hstep3 : 2 * (2 * Real.pi * |Dy|) ≤ γ / 16 := by
          have h6 : 2 * (2 * Real.pi * |Dy|) ≤ 2 * (2 * Real.pi * (γ / 1024)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΔ (by positivity)) (by norm_num)
          have h7 : 2 * (2 * Real.pi * (γ / 1024)) ≤ γ / 16 := by nlinarith [Real.pi_lt_four, hγ0]
          linarith [h6, h7]
        exact le_trans hstep2 hstep3
      calc ‖ph P ξ ((Y : ℕ) : ℤ) * f₁ (u + ((Y : ℕ) : ℤ))
            - ph P βr ((b0 + 1 : ℕ) : ℤ) * phT P a t (r : ℤ) * f₁ (u + ((Y : ℕ) : ℤ))‖
          = ‖phT P a t (r : ℤ) * ((ph P βr ((Y : ℕ) : ℤ) - ph P βr (((b0 + 1 : ℕ)) : ℤ))
              * f₁ (u + ((Y : ℕ) : ℤ)))‖ := by
            rw [hsp]; ring_nf
        _ = ‖ph P βr ((Y : ℕ) : ℤ) - ph P βr (((b0 + 1 : ℕ)) : ℤ)‖ * ‖f₁ (u + ((Y : ℕ) : ℤ))‖ := by
            have hT : ‖phT P a t (r : ℤ)‖ = 1 := by simp only [phT]; exact norm_ee _
            rw [norm_mul, norm_mul, hT, one_mul]
        _ ≤ (γ / 16) * ‖f₁ (u + ((Y : ℕ) : ℤ))‖ :=
            mul_le_mul_of_nonneg_right hbound1 (norm_nonneg _)
    -- the periodised block sum
    set perF : ℤ → ℂ := fun u => ph P βr ((b0 + 1 : ℕ) : ℤ) * ∑ r ∈ Finset.Icc 1 t,
        phT P a t (r : ℤ) * ∑ m ∈ Finset.Icc 1 Mr,
          f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ)) with hperF
    have hperapprox : ∀ u : ℤ, ‖winB P ξ f₁ b0 Lr u - perF u‖
        ≤ (γ / 16) * ((Lr : ℝ)) := by
      intro u
      have hwin : winB P ξ f₁ b0 Lr u
          = ∑ r ∈ Finset.Icc 1 t, ∑ m ∈ Finset.Icc 1 Mr,
              ph P ξ ((b0 + (m - 1) * t + r : ℕ) : ℤ)
                * f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ)) := by
        have h0 : winB P ξ f₁ b0 Lr u
            = ∑ y ∈ Finset.Icc (b0 + 1) (b0 + t * Mr),
                ph P ξ (y : ℤ) * f₁ (u + (y : ℤ)) := by
          unfold winB; rw [hLr]
        rw [h0, sum_Icc_subblock_decomp (t := t) (M := Mr) (b := b0) ht1
          (fun y : ℕ => ph P ξ (y : ℤ) * f₁ (u + (y : ℤ)))]
        rw [Finset.sum_comm]
      have hper2 : perF u = ∑ r ∈ Finset.Icc 1 t, ∑ m ∈ Finset.Icc 1 Mr,
              ph P βr ((b0 + 1 : ℕ) : ℤ) * phT P a t (r : ℤ)
                * f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ)) := by
        rw [hperF]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r hr => ?_)
        refine Finset.sum_congr rfl (fun m hm => ?_)
        ring
      rw [hwin, hper2, ← Finset.sum_sub_distrib]
      simp only [← Finset.sum_sub_distrib]
      have hstepA : (∑ r ∈ Finset.Icc 1 t, ∑ m ∈ Finset.Icc 1 Mr,
            ‖ph P ξ ((b0 + (m - 1) * t + r : ℕ) : ℤ)
                * f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))
              - ph P βr ((b0 + 1 : ℕ) : ℤ) * phT P a t (r : ℤ)
                * f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖) ≤
          ∑ r ∈ Finset.Icc 1 t, ∑ m ∈ Finset.Icc 1 Mr,
            (γ / 16) * ‖f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖ := by
        refine Finset.sum_le_sum (fun r hr => ?_)
        refine Finset.sum_le_sum (fun m hm => hphase u m r hm hr)
      have hstepB : ‖∑ r ∈ Finset.Icc 1 t, ∑ m ∈ Finset.Icc 1 Mr,
            (ph P ξ ((b0 + (m - 1) * t + r : ℕ) : ℤ)
                * f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))
              - ph P βr ((b0 + 1 : ℕ) : ℤ) * phT P a t (r : ℤ)
                * f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ)))‖ ≤
          ∑ r ∈ Finset.Icc 1 t, ∑ m ∈ Finset.Icc 1 Mr,
            (γ / 16) * ‖f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖ :=
        le_trans (norm_sum_le _ _)
          (le_trans (Finset.sum_le_sum (fun r hr => norm_sum_le _ _)) hstepA)
      refine le_trans hstepB ?_
      have hM : ∑ r ∈ Finset.Icc 1 t, ∑ m ∈ Finset.Icc 1 Mr,
            (γ / 16) * ‖f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖
          ≤ ∑ r ∈ Finset.Icc 1 t, (γ / 16) * (Mr : ℝ) := by
        refine Finset.sum_le_sum (fun r hr => ?_)
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ m ∈ Finset.Icc 1 Mr, ‖f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖
            ≤ ∑ m ∈ Finset.Icc 1 Mr, (1 : ℝ) := Finset.sum_le_sum (fun m hm => hb1 _)
          _ = Mr := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel]
      have h3 : ∑ r ∈ Finset.Icc 1 t, (γ / 16) * (Mr : ℝ) = (γ / 16) * (Lr : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have ht : (Finset.Icc 1 t).card = t := by rw [Nat.card_Icc, Nat.add_sub_cancel]
        rw [ht, hLr, Nat.cast_mul]
        ring
      linarith [hM, h3.le]
    -- lower bound for the periodised sums
    have hperlow : γ * (Ns : ℝ) * (Lr : ℝ) / 4 ≤ ∑ u ∈ Work.Peluse.symIcc Ns, ‖perF u‖ := by
      have h1 : ∀ u : ℤ, ‖winB P ξ f₁ b0 Lr u‖
          ≤ ‖perF u‖ + (γ / 16) * (Lr : ℝ) := by
        intro u
        have h2 := abs_le.mp (abs_norm_sub_norm_le (winB P ξ f₁ b0 Lr u) (perF u))
        have h3 := hperapprox u
        linarith [h2.1, h3]
      have h2 : ∑ u ∈ Work.Peluse.symIcc Ns, ‖winB P ξ f₁ b0 Lr u‖
          ≤ (∑ u ∈ Work.Peluse.symIcc Ns, ‖perF u‖)
            + ((Work.Peluse.symIcc Ns).card : ℝ) * ((γ / 16) * (Lr : ℝ)) := by
        calc ∑ u ∈ Work.Peluse.symIcc Ns, ‖winB P ξ f₁ b0 Lr u‖
            ≤ ∑ u ∈ Work.Peluse.symIcc Ns, (‖perF u‖ + (γ / 16) * (Lr : ℝ)) :=
              Finset.sum_le_sum (fun u hu => h1 u)
          _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Work.Peluse.symIcc Ns).card : ℝ) = 2 * (Ns : ℝ) + 1 := by
        rw [symIcc_card]; push_cast; ring
      have h3 : ((Work.Peluse.symIcc Ns).card : ℝ) * ((γ / 16) * (Lr : ℝ))
          ≤ γ * (Ns : ℝ) * (Lr : ℝ) / 4 := by
        rw [hcard]
        calc (2 * (Ns : ℝ) + 1) * ((γ / 16) * (Lr : ℝ))
            ≤ (4 * (Ns : ℝ)) * ((γ / 16) * (Lr : ℝ)) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              linarith [hNsR, hNs1']
          _ = γ * (Ns : ℝ) * (Lr : ℝ) / 4 := by ring
      linarith [hj₀lb, h2, h3]
    -- residue split
    have hsplit : ∑ u ∈ Work.Peluse.symIcc Ns, ‖perF u‖
        ≤ ∑ r ∈ Finset.Icc 1 t, ∑ u ∈ Work.Peluse.symIcc Ns,
            ‖∑ m ∈ Finset.Icc 1 Mr, f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖ := by
      rw [hperF]
      have h1 : ∀ u : ℤ, ‖ph P βr ((b0 + 1 : ℕ) : ℤ) * ∑ r ∈ Finset.Icc 1 t,
            phT P a t (r : ℤ) * ∑ m ∈ Finset.Icc 1 Mr,
              f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖
          ≤ ∑ r ∈ Finset.Icc 1 t, ‖∑ m ∈ Finset.Icc 1 Mr,
              f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖ := by
        intro u
        simp only [ph]
        rw [norm_mul, norm_ee, one_mul]
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun r hr => ?_))
        simp only [phT]
        rw [norm_mul, norm_ee, one_mul]
      calc ∑ u ∈ Work.Peluse.symIcc Ns, ‖ph P βr ((b0 + 1 : ℕ) : ℤ) * ∑ r ∈ Finset.Icc 1 t,
            phT P a t (r : ℤ) * ∑ m ∈ Finset.Icc 1 Mr,
              f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖
          ≤ ∑ u ∈ Work.Peluse.symIcc Ns, ∑ r ∈ Finset.Icc 1 t, ‖∑ m ∈ Finset.Icc 1 Mr,
              f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖ :=
            Finset.sum_le_sum (fun u hu => h1 u)
        _ = ∑ r ∈ Finset.Icc 1 t, ∑ u ∈ Work.Peluse.symIcc Ns, ‖∑ m ∈ Finset.Icc 1 Mr,
              f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖ := Finset.sum_comm
    obtain ⟨r₀, hr₀mem, hr₀max⟩ := Finset.exists_max_image (Finset.Icc 1 t)
      (fun r => ∑ u ∈ Work.Peluse.symIcc Ns,
        ‖∑ m ∈ Finset.Icc 1 Mr, f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖)
      ⟨1, by simp [ht1]⟩
    have hr₀lb : γ * (Ns : ℝ) * (Lr : ℝ) / (4 * (t : ℝ)) ≤
        ∑ u ∈ Work.Peluse.symIcc Ns,
          ‖∑ m ∈ Finset.Icc 1 Mr, f₁ (u + ((b0 + (m - 1) * t + r₀ : ℕ) : ℤ))‖ := by
      have hcardt : ((Finset.Icc 1 t).card : ℝ) = (t : ℝ) := by
        rw [Nat.card_Icc]; simp
      have hmax : ∑ r ∈ Finset.Icc 1 t, ∑ u ∈ Work.Peluse.symIcc Ns,
            ‖∑ m ∈ Finset.Icc 1 Mr, f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖
          ≤ (t : ℝ) * ∑ u ∈ Work.Peluse.symIcc Ns,
            ‖∑ m ∈ Finset.Icc 1 Mr, f₁ (u + ((b0 + (m - 1) * t + r₀ : ℕ) : ℤ))‖ := by
        calc ∑ r ∈ Finset.Icc 1 t, ∑ u ∈ Work.Peluse.symIcc Ns,
              ‖∑ m ∈ Finset.Icc 1 Mr, f₁ (u + ((b0 + (m - 1) * t + r : ℕ) : ℤ))‖
            ≤ ∑ r ∈ Finset.Icc 1 t, ∑ u ∈ Work.Peluse.symIcc Ns,
                ‖∑ m ∈ Finset.Icc 1 Mr, f₁ (u + ((b0 + (m - 1) * t + r₀ : ℕ) : ℤ))‖ :=
              Finset.sum_le_sum (fun r hr => hr₀max r hr)
          _ = (Finset.Icc 1 t).card • (∑ u ∈ Work.Peluse.symIcc Ns,
                ‖∑ m ∈ Finset.Icc 1 Mr, f₁ (u + ((b0 + (m - 1) * t + r₀ : ℕ) : ℤ))‖) :=
              Finset.sum_const _
          _ = _ := by rw [nsmul_eq_mul]; rw [hcardt]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (t : ℝ))]
      nlinarith [hperlow, hsplit, hmax]
    -- the progression average
    refine ⟨t, Mr, ht1, ?_, hMr1, hMrN, hMrlo, ?_⟩
    · -- `t ≤ Cnat * (γ⁻¹)^(Kh+1)`
      have hg1 : (1 : ℝ) ≤ (γ⁻¹) ^ Kh := one_le_pow₀ ((one_le_inv₀ hγ0).mpr hγ1)
      have hg1' : (1 : ℝ) ≤ γ⁻¹ := (one_le_inv₀ hγ0).mpr hγ1
      have h2 : (γ⁻¹) ^ Kh ≤ (γ⁻¹) ^ (Kh + 1) := by
        rw [pow_succ]
        exact le_mul_of_one_le_right (by positivity) hg1'
      calc (t : ℝ) ≤ Cc * (γ⁻¹) ^ Kh := htle
        _ ≤ (Cnat : ℝ) * (γ⁻¹) ^ (Kh + 1) := mul_le_mul hCnatc h2 (by positivity) (by positivity)
    · -- the progression average bound
      set x0 : ℤ := (b0 : ℤ) + (r₀ : ℤ) - (t : ℤ) with hx0
      have hAl : ∀ u : ℤ, ‖∑ m ∈ Finset.Icc 1 Mr, f₁ (u + ((b0 + (m - 1) * t + r₀ : ℕ) : ℤ))‖
          = ‖∑ m ∈ Finset.Icc 1 Mr, f₁ ((u + x0) + (t : ℤ) * (m : ℤ))‖ := by
        intro u
        congr 1
        refine Finset.sum_congr rfl (fun m hm => ?_)
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        congr 1
        rw [hx0]
        push_cast [Nat.cast_sub hm1]
        ring
      -- summability
      have hsumm : Summable (fun x : ℤ => ‖Work.Peluse.progAvg Mr (t : ℤ) f₁ x‖) := by
        refine summable_of_ne_finset_zero (s := Work.Peluse.symIcc (Ns + t * Mr)) (fun x hx => ?_)
        rw [norm_eq_zero]
        rw [Work.Peluse.progAvg]
        refine mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero (fun m hm => ?_)))
        rw [progAvgSum_mem_symIcc_iff_natAbs] at hx
        have hmle : m ≤ Mr := (Finset.mem_Icc.mp hm).2
        refine hs1 _ ?_
        have h2 : (x : ℤ).natAbs ≤ (x + (t : ℤ) * (m : ℤ)).natAbs + ((t : ℤ) * (m : ℤ)).natAbs := by
          have h3 := Int.natAbs_sub_le (x + (t : ℤ) * (m : ℤ)) ((t : ℤ) * (m : ℤ))
          simpa using h3
        have h4 : ((t : ℤ) * (m : ℤ)).natAbs = t * m := by
          rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
        rw [h4] at h2
        have h5 := not_le.mp hx
        have h6 : t * m ≤ Mr * t := by
          rw [Nat.mul_comm t m]
          exact Nat.mul_le_mul_right t hmle
        have h10 : t * m ≤ t * Mr := le_trans h6 (le_of_eq (Nat.mul_comm Mr t))
        have h7 : Ns < (x + (t : ℤ) * (m : ℤ)).natAbs := by
          have h8 : Ns + t * Mr < (x + (t : ℤ) * (m : ℤ)).natAbs + t * m :=
            lt_of_lt_of_le (not_le.mp hx) h2
          have h9 : (x + (t : ℤ) * (m : ℤ)).natAbs + t * m
              ≤ (x + (t : ℤ) * (m : ℤ)).natAbs + t * Mr := Nat.add_le_add_left h10 _
          omega
        exact h7
      have hpos : (0 : ℝ) < (Mr : ℝ) := by exact_mod_cast hMr1
      have hpa : ∀ x : ℤ, ‖Work.Peluse.progAvg Mr (t : ℤ) f₁ x‖
          = (Mr : ℝ)⁻¹ * ‖∑ m ∈ Finset.Icc 1 Mr, f₁ (x + (t : ℤ) * (m : ℤ))‖ := by
        intro x
        rw [Work.Peluse.progAvg, norm_mul, norm_inv, Complex.norm_natCast]
      have h7 : (Mr : ℝ)⁻¹ * ∑ u ∈ Work.Peluse.symIcc Ns,
          ‖∑ m ∈ Finset.Icc 1 Mr, f₁ (u + ((b0 + (m - 1) * t + r₀ : ℕ) : ℤ))‖
          ≤ Work.Peluse.progAvgSum Mr (t : ℤ) f₁ := by
        have h8 : ∑ u ∈ Work.Peluse.symIcc Ns,
              ‖∑ m ∈ Finset.Icc 1 Mr, f₁ (u + ((b0 + (m - 1) * t + r₀ : ℕ) : ℤ))‖
            = (Mr : ℝ) * ∑ u ∈ Work.Peluse.symIcc Ns,
                ‖Work.Peluse.progAvg Mr (t : ℤ) f₁ (u + x0)‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun u hu => ?_)
          rw [hpa, hAl u]
          field_simp
        rw [h8, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
        calc ∑ u ∈ Work.Peluse.symIcc Ns, ‖Work.Peluse.progAvg Mr (t : ℤ) f₁ (u + x0)‖
            = ∑ x ∈ (Work.Peluse.symIcc Ns).image (fun u : ℤ => u + x0),
                ‖Work.Peluse.progAvg Mr (t : ℤ) f₁ x‖ := by
              rw [Finset.sum_image (fun a ha b hb hab => add_right_cancel hab)]
          _ ≤ ∑' x : ℤ, ‖Work.Peluse.progAvg Mr (t : ℤ) f₁ x‖ :=
              Summable.sum_le_tsum _ (fun x _ => norm_nonneg _) hsumm
          _ = Work.Peluse.progAvgSum Mr (t : ℤ) f₁ := rfl
      have h9 : γ * (Ns : ℝ) * (Lr : ℝ) / (4 * (t : ℝ)) = (Mr : ℝ) * (γ * (Ns : ℝ) / 4) := by
        rw [hLr, Nat.cast_mul]
        field_simp
        try ring
      have h10 : γ * (Ns : ℝ) / (4) ≤ (Mr : ℝ)⁻¹ * (γ * (Ns : ℝ) * (Lr : ℝ) / (4 * (t : ℝ))) := by
        rw [h9]
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
      calc γ ^ (Kh + 1) * (Ns : ℝ) / (Cnat : ℝ)
          ≤ γ * (Ns : ℝ) / 4 := by
            have h3 : γ ^ (Kh + 1) ≤ γ * (Cnat : ℝ) / 4 := by
              have h4 : γ ^ Kh ≤ 1 := pow_le_one₀ (le_of_lt hγ0) hγ1
              have h4' : γ ^ (Kh + 1) ≤ γ := by
                calc γ ^ (Kh + 1) = γ ^ Kh * γ := by rw [pow_succ]
                  _ ≤ 1 * γ := mul_le_mul_of_nonneg_right h4 (le_of_lt hγ0)
                  _ = γ := one_mul γ
              have h5 : γ ≤ γ * (Cnat : ℝ) / 4 := by
                rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
                nlinarith [hCnat8, hγ0]
              linarith [h4', h5]
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Cnat : ℝ))]
            have h6 : γ ^ (Kh + 1) * (Ns : ℝ) ≤ (γ * (Cnat : ℝ) / 4) * (Ns : ℝ) :=
              mul_le_mul_of_nonneg_right h3 (by positivity)
            have h7 : (γ * (Cnat : ℝ) / 4) * (Ns : ℝ) = γ * (Ns : ℝ) / 4 * (Cnat : ℝ) := by ring
            linarith [h6, h7.le]
        _ ≤ (Mr : ℝ)⁻¹ * (γ * (Ns : ℝ) * (Lr : ℝ) / (4 * (t : ℝ))) := h10
        _ ≤ (Mr : ℝ)⁻¹ * ∑ u ∈ Work.Peluse.symIcc Ns,
              ‖∑ m ∈ Finset.Icc 1 Mr, f₁ (u + ((b0 + (m - 1) * t + r₀ : ℕ) : ℤ))‖ := by
            refine mul_le_mul_of_nonneg_left hr₀lb (by positivity)
        _ ≤ Work.Peluse.progAvgSum Mr (t : ℤ) f₁ := h7

end

end Work.Peluse.Ulower
