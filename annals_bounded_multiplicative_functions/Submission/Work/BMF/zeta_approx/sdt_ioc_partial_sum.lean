import Mathlib
import Submission.Work.BMF.sdt_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `∑_{M<n≤L} n^{-iτ}` from the second-derivative test

Given the van der Corput second-derivative-test bound (`hsdt`), we bound the partial
sum `∑_{M<n≤L} n^{-iτ}` by `C·(√(τ/(8π)) + M·√(8π/τ))`.

The proof applies `hsdt` to the phase `f(x) = -(τ/(2π))·log x`, whose second
derivative is `τ/(2π x²)`, on the interval `[M, L]` with `r = τ/(8π M²)`; the
condition `r ≤ f'' ≤ 4r` reduces to `M ≤ x ≤ 2M`, which holds because
`M < x < L ≤ 2M`.
-/

open scoped BigOperators Topology
open Filter

namespace Work.BMF.zeta_approx

/-- First derivative of the phase `phaseFn t x = -(t/(2π))·log x`. -/
lemma hasDerivAt_phaseFn (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (Work.BMF.phaseFn t) (-(t / (2 * Real.pi)) * x⁻¹) x := by
  unfold Work.BMF.phaseFn
  exact (Real.hasDerivAt_log hx).const_mul _

lemma deriv_phaseFn (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    deriv (Work.BMF.phaseFn t) x = -(t / (2 * Real.pi)) * x⁻¹ :=
  (hasDerivAt_phaseFn t hx).deriv

/-- Second derivative of the phase. -/
lemma deriv_deriv_phaseFn (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    deriv (deriv (Work.BMF.phaseFn t)) x = t / (2 * Real.pi * x ^ 2) := by
  have hev : deriv (Work.BMF.phaseFn t) =ᶠ[𝓝 x]
      (fun y => -(t / (2 * Real.pi)) * y⁻¹) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact deriv_phaseFn t hy
  have h1 : HasDerivAt (fun y => -(t / (2 * Real.pi)) * y⁻¹)
      (-(t / (2 * Real.pi)) * (-(x ^ 2)⁻¹)) x :=
    (hasDerivAt_inv hx).const_mul _
  have h2 := h1.congr_of_eventuallyEq hev
  rw [h2.deriv]
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  field_simp

/-- `phaseFn t` is `C²` on intervals lying in the positive reals. -/
lemma contDiffOn_phaseFn (t : ℝ) {M L : ℝ} (hM : 0 < M) :
    ContDiffOn ℝ 2 (Work.BMF.phaseFn t) (Set.Icc M L) := by
  have hsub : Set.Icc M L ⊆ {0}ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (lt_of_lt_of_le hM hx.1)
  have hlog : ContDiffOn ℝ 2 Real.log (Set.Icc M L) := Real.contDiffOn_log.mono hsub
  unfold Work.BMF.phaseFn
  exact contDiffOn_const.mul hlog

/-- Reindex a sum over `Ioc (M:ℤ) (L:ℤ)` as a sum over `Ioc M L`. -/
lemma sum_Ioc_intCast (F : ℤ → ℂ) (M L : ℕ) :
    (∑ m ∈ Finset.Ioc M L, F (m : ℤ)) = ∑ k ∈ Finset.Ioc (M : ℤ) (L : ℤ), F k := by
  apply Finset.sum_nbij (fun m : ℕ => (m : ℤ))
  · intro m hm
    simp only [Finset.mem_Ioc] at hm ⊢
    omega
  · intro a _ b _ h
    exact Nat.cast_injective h
  · intro k hk
    change k ∈ Finset.Ioc (M : ℤ) (L : ℤ) at hk
    simp only [Finset.mem_Ioc] at hk
    have hk0 : 0 ≤ k := by omega
    refine ⟨k.toNat, ?_, ?_⟩
    · change k.toNat ∈ Finset.Ioc M L
      simp only [Finset.mem_Ioc]
      have := Int.toNat_of_nonneg hk0
      omega
    · exact Int.toNat_of_nonneg hk0
  · intro m _
    rfl

/-- `n^{-iτ} = exp(2πi·phaseFn τ n)` for positive natural `n`. -/
lemma cpow_neg_I_mul_eq_phaseR (τ : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    (m : ℂ) ^ (-(Complex.I * (τ : ℂ))) = Work.BMF.phaseR τ (m : ℝ) := by
  have hm0 : (m : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show (0 : ℕ) < m by omega)
  have hlog : Complex.log ((m : ℂ)) = ((Real.log (m : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast (n := m), Complex.ofReal_log hmpos.le]
  rw [Complex.cpow_def_of_ne_zero hm0, hlog]
  unfold Work.BMF.phaseR
  congr 1
  push_cast
  ring

theorem sdt_ioc_partial_sum
    (hsdt : ∃ C : ℝ, 0 < C ∧ ∀ {a : ℤ} {n : ℕ}, 1 ≤ n → ∀ f : ℝ → ℝ, ∀ r : ℝ, 0 < r →
      ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) ((a : ℝ) + n)) →
      (∀ x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + n), r ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ 4 * r) →
      ‖∑ k ∈ Finset.Icc (a + 1) (a + (n : ℤ)),
          Complex.exp (((2 * Real.pi * f (k : ℝ) : ℝ) : ℂ) * Complex.I)‖
        ≤ C * ((n : ℝ) * Real.sqrt r + 1 / Real.sqrt r)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M L : ℕ) (τ : ℝ), 1 ≤ M → M < L → L ≤ 2 * M → 0 < τ →
      ‖∑ n ∈ Finset.Ioc M L, ((n : ℂ) ^ (-(Complex.I * (τ : ℂ))))‖
        ≤ C * (Real.sqrt (τ / (8 * Real.pi)) + (M : ℝ) * Real.sqrt (8 * Real.pi / τ)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hsdt
  refine ⟨C₀, hC₀pos, ?_⟩
  intro M L τ hM hML hL2M hτ
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show (0 : ℕ) < M by omega)
  have hMLle : M ≤ L := le_of_lt hML
  have hL2M' : (L : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hL2M
  have hn1 : 1 ≤ L - M := by omega
  set r : ℝ := τ / (8 * Real.pi * (M : ℝ) ^ 2) with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  -- Rewriting the integer interval endpoints
  have hsubst : ((M : ℤ) : ℝ) = (M : ℝ) := by simp
  have hsum_cast : ((M : ℤ) : ℝ) + (↑(L - M) : ℝ) = (L : ℝ) := by
    rw [Int.cast_natCast, Nat.cast_sub hMLle]; ring
  have hIcc : Set.Icc ((M : ℤ) : ℝ) (((M : ℤ) : ℝ) + (↑(L - M) : ℝ))
      = Set.Icc (M : ℝ) (L : ℝ) := by rw [hsum_cast, hsubst]
  have hIoo : Set.Ioo ((M : ℤ) : ℝ) (((M : ℤ) : ℝ) + (↑(L - M) : ℝ))
      = Set.Ioo (M : ℝ) (L : ℝ) := by rw [hsum_cast, hsubst]
  have hcont : ContDiffOn ℝ 2 (Work.BMF.phaseFn τ)
      (Set.Icc ((M : ℤ) : ℝ) (((M : ℤ) : ℝ) + (↑(L - M) : ℝ))) := by
    rw [hIcc]; exact contDiffOn_phaseFn τ hMpos
  have hderiv : ∀ x ∈ Set.Ioo ((M : ℤ) : ℝ) (((M : ℤ) : ℝ) + (↑(L - M) : ℝ)),
      r ≤ deriv (deriv (Work.BMF.phaseFn τ)) x
        ∧ deriv (deriv (Work.BMF.phaseFn τ)) x ≤ 4 * r := by
    intro x hx
    rw [hIoo] at hx
    rw [Set.mem_Ioo] at hx
    obtain ⟨hxM, hxL⟩ := hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hxle : x ≤ 2 * (M : ℝ) := by linarith
    rw [deriv_deriv_phaseFn τ hx0]
    constructor
    · rw [hr, div_le_div_iff₀ (by positivity : (0:ℝ) < 8 * Real.pi * (M:ℝ)^2)
          (by positivity : (0:ℝ) < 2 * Real.pi * x^2)]
      have hx2 : x ^ 2 ≤ (2 * (M:ℝ)) ^ 2 := pow_le_pow_left₀ hxpos.le hxle 2
      have hx4 : x ^ 2 ≤ 4 * (M:ℝ) ^ 2 := by nlinarith [hx2]
      refine mul_le_mul_of_nonneg_left ?_ hτ.le
      have := mul_le_mul_of_nonneg_left hx4 (show (0:ℝ) ≤ 2 * Real.pi by positivity)
      nlinarith [this]
    · rw [hr]
      have h4 : (4:ℝ) * (τ / (8 * Real.pi * (M:ℝ)^2)) = τ / (2 * Real.pi * (M:ℝ)^2) := by
        field_simp
        ring
      rw [h4, div_le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi * x^2)
          (by positivity : (0:ℝ) < 2 * Real.pi * (M:ℝ)^2)]
      have hMx2 : (M:ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hMpos.le hxM.le 2
      refine mul_le_mul_of_nonneg_left ?_ hτ.le
      exact mul_le_mul_of_nonneg_left hMx2 (show (0:ℝ) ≤ 2 * Real.pi by positivity)
  have hkey := hC₀ (a := (M : ℤ)) (n := L - M) hn1 (Work.BMF.phaseFn τ) r hrpos hcont hderiv
  -- Identify the `hsdt` sum with the target sum
  have hTeq : (∑ k ∈ Finset.Icc ((M : ℤ) + 1) ((M : ℤ) + (↑(L - M) : ℤ)),
        Complex.exp (((2 * Real.pi * Work.BMF.phaseFn τ (k : ℝ) : ℝ) : ℂ) * Complex.I))
      = ∑ m ∈ Finset.Ioc M L, ((m : ℂ) ^ (-(Complex.I * (τ : ℂ)))) := by
    have hidx : Finset.Icc ((M : ℤ) + 1) ((M : ℤ) + (↑(L - M) : ℤ))
        = Finset.Ioc (M : ℤ) (L : ℤ) := by
      have hcast : (M : ℤ) + (↑(L - M) : ℤ) = (L : ℤ) := by
        rw [Nat.cast_sub hMLle]; ring
      rw [hcast]
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hidx]
    have step1 : (∑ k ∈ Finset.Ioc (M : ℤ) (L : ℤ),
          Complex.exp (((2 * Real.pi * Work.BMF.phaseFn τ (k : ℝ) : ℝ) : ℂ) * Complex.I))
        = ∑ k ∈ Finset.Ioc (M : ℤ) (L : ℤ), Work.BMF.phaseR τ (k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      exact (Work.BMF.phaseR_eq_exp_phaseFn τ (k : ℝ)).symm
    rw [step1]
    rw [← sum_Ioc_intCast (fun k : ℤ => Work.BMF.phaseR τ (k : ℝ)) M L]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hcast : ((m : ℤ) : ℝ) = (m : ℝ) := by simp
    rw [hcast]
    exact (cpow_neg_I_mul_eq_phaseR τ m (by omega)).symm
  -- The numerical comparison
  have hnle : (↑(L - M) : ℝ) ≤ (M : ℝ) := by
    rw [Nat.cast_sub hMLle]; linarith
  have hsqrt_r : Real.sqrt r = Real.sqrt τ / (Real.sqrt (8 * Real.pi) * (M:ℝ)) := by
    rw [hr, Real.sqrt_div hτ.le (8 * Real.pi * (M:ℝ)^2),
        Real.sqrt_mul (by positivity : (0:ℝ) ≤ 8 * Real.pi) ((M:ℝ)^2),
        Real.sqrt_sq hMpos.le]
  have hsqrt_eq : (M : ℝ) * Real.sqrt r = Real.sqrt (τ / (8 * Real.pi)) := by
    rw [hsqrt_r, Real.sqrt_div hτ.le (8 * Real.pi)]
    have hst : Real.sqrt τ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hτ)
    have hsp : Real.sqrt (8 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have hMne : (M:ℝ) ≠ 0 := ne_of_gt hMpos
    field_simp
  have hone_eq : 1 / Real.sqrt r = (M : ℝ) * Real.sqrt (8 * Real.pi / τ) := by
    rw [hsqrt_r, Real.sqrt_div (by positivity : (0:ℝ) ≤ 8 * Real.pi) τ]
    have hst : Real.sqrt τ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hτ)
    have hsp : Real.sqrt (8 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have hMne : (M:ℝ) ≠ 0 := ne_of_gt hMpos
    field_simp
  rw [← hTeq]
  refine le_trans hkey ?_
  apply mul_le_mul_of_nonneg_left _ hC₀pos.le
  have h1 : (↑(L - M) : ℝ) * Real.sqrt r ≤ Real.sqrt (τ / (8 * Real.pi)) := by
    calc (↑(L - M) : ℝ) * Real.sqrt r
        ≤ (M : ℝ) * Real.sqrt r := mul_le_mul_of_nonneg_right hnle (Real.sqrt_nonneg r)
      _ = Real.sqrt (τ / (8 * Real.pi)) := hsqrt_eq
  have h2 : 1 / Real.sqrt r ≤ (M : ℝ) * Real.sqrt (8 * Real.pi / τ) := le_of_eq hone_eq
  linarith

end Work.BMF.zeta_approx
