/-
# Shared vocabulary for the interval (`Icc`) form of the inverse Weyl estimate

This module collects the elementary objects and lemmas used by the proof of
`Work.KMTAreas.A4.lip2WeylIcc` and by the lemmas delegated for it:

* the unit complex exponential `ee x = exp (2 π i x)` and its laws (`ee_add`, `ee_norm`,
  `star_ee`, `continuous_ee`, registered for `fun_prop`);
* the identification of the windowed sum `winSumIcc` with the `Icc`-sum of the window times the
  phase (`winSumIcc_eq_sum`), the factored form of the window (`win_eq`), and Fourier inversion
  of the smoothing weight (`lipSchPsi_eq_integral`, `lipSchPsi_eq_integral_ee`);
* the pigeonhole `exists_fiber_card_le` used to extract a common denominator from the individual
  denominators produced by the inverse Weyl estimate at the previous degree;
* the predicates `IWfree d C K` and `IWlin d C K`: the **inverse Weyl estimate for a plain sum of
  a polynomial phase**, τ-free and with an additional linear term (the latter being the form in
  which the windowed estimate is applied).
-/
import Mathlib
import Submission.Work.KMTAreas.A4.eeDef
import Submission.Work.KMTAreas.A4.lip2Kernel

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped BigOperators
open Polynomial
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

-- `ee` (`e (x) = exp (2 π i x)`) is defined in `Submission.Work.KMTAreas.A4.eeDef`.

theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The same exponential, with the real part of the exponent exposed. -/
theorem ee_eq (x : ℝ) : ee x = Complex.exp (((2 * Real.pi * x : ℝ)) * Complex.I) := by
  rw [ee]; congr 1; push_cast; ring

theorem ee_zero : ee 0 = 1 := by simp [ee]

theorem ee_norm (x : ℝ) : ‖ee x‖ = 1 := by
  have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))
      = (((2 * Real.pi * x : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [ee, h]
  simpa using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

theorem ee_norm_le (x : ℝ) : ‖ee x‖ ≤ 1 := le_of_eq (ee_norm x)

theorem ee_neg (x : ℝ) : ee (-x) = (ee x)⁻¹ := by
  have h : ee x * ee (-x) = 1 := by
    have h2 := ee_add x (-x)
    rw [add_neg_cancel, ee_zero] at h2
    exact h2.symm
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h)

/-- The complex conjugate of `ee x` is `ee (-x)`. -/
theorem star_ee (x : ℝ) : star (ee x) = ee (-x) := by
  rw [ee_eq, ee_eq, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- A product of a phase and the conjugate of another is the phase of the difference. -/
theorem ee_mul_star_ee (x y : ℝ) : ee x * star (ee y) = ee (x - y) := by
  rw [star_ee, ← ee_add, sub_eq_add_neg]

theorem continuous_ee : Continuous ee := by
  have h : ee = fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := rfl
  rw [h]
  fun_prop

attribute [fun_prop] continuous_ee

/-- The windowed sum of `lip2Defs` is the `Icc`-sum of the window times the exponential of the
polynomial phase, in the `ee` notation. -/
theorem winSumIcc_eq_sum (M : ℝ) (γ : FreqCircle) (ξ : ℝ) (P : Polynomial ℤ) (s : ℤ)
    (a b : ℤ) :
    winSumIcc M γ ξ P s a b
      = ∑ n ∈ Finset.Icc a b, win M γ (n - s) *
          ee (ξ * ((P.eval n : ℤ) : ℝ)) := by
  rw [winSumIcc]
  exact Finset.sum_congr rfl fun n _ => by congr 1

/-- The window is the inverse Fourier transform of the bump: `win M γ m = M⁻¹ ψ(m/M) e (m γ)`,
where `ψ = lipSchPsi`. -/
theorem win_eq (M : ℝ) (γ : FreqCircle) (m : ℤ) :
    win M γ m = ((M : ℂ)⁻¹) * (lipSchPsi : ℝ → ℂ) ((m : ℝ) / M) * (fourier m γ : ℂ) := rfl

/-- **Fourier inversion.**  `ψ x = ∫ u, 𝐞 (u * x) χ u`, where `ψ = lipSchPsi` and `χ = lipSchChi`. -/
theorem lipSchPsi_eq_integral (x : ℝ) :
    (lipSchPsi : ℝ → ℂ) x
      = ∫ u : ℝ, (lipSchChi : ℝ → ℂ) u *
          Complex.exp (2 * Real.pi * Complex.I * ((u * x : ℝ) : ℂ)) := by
  have h1 : (lipSchPsi : ℝ → ℂ) x = FourierTransformInv.fourierInv (lipSchChi : ℝ → ℂ) x := by
    have h := congrFun (SchwartzMap.fourierInv_coe (Work.KMTAreas.A4.lipSchChi)) x
    simpa [lipSchPsi] using h
  rw [h1]
  rw [Real.fourierInv_eq (lipSchChi : ℝ → ℂ) x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [Real.inner_apply, Circle.smul_def, smul_eq_mul]
  rw [Real.fourierChar_apply, mul_comm]
  congr 1
  push_cast
  ring

/-- The Fourier inversion of `lipSchPsi` in the `ee` notation. -/
theorem lipSchPsi_eq_integral_ee (x : ℝ) :
    (lipSchPsi : ℝ → ℂ) x = ∫ u : ℝ, (lipSchChi : ℝ → ℂ) u * ee (u * x) := by
  rw [lipSchPsi_eq_integral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  congr 1

/-- The Fourier character `𝐞 t` (a `Circle` element) is our `ee t`. -/
theorem circle_char_eq_ee (t : ℝ) : ((Real.fourierChar t : Circle) : ℂ) = ee t := by
  rw [Real.fourierChar_apply, ee]
  congr 1
  push_cast
  ring_nf

theorem norm_lipSchChi_le_one (u : ℝ) : ‖(lipSchChi : ℝ → ℂ) u‖ ≤ 1 :=
  lipSchChi_norm_le_one u

/-- **Pigeonhole.**  A `Finset` whose elements carry values in `[1,Q]` has a fibre of size at
least `T.card / Q`.  This is the pigeonhole over the individual denominators produced by the
inverse Weyl estimate at the previous degree. -/
theorem exists_fiber_card_le (T : Finset ℤ) (f : ℤ → ℕ) (Q : ℝ) (hQ : 1 ≤ Q)
    (hf : ∀ h ∈ T, 1 ≤ f h ∧ (f h : ℝ) ≤ Q) :
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Q ∧
      (T.card : ℝ) ≤ Q * ((T.filter (fun h => f h = q)).card : ℝ) := by
  classical
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  · rw [hT0]
    refine ⟨1, le_refl 1, ?_, ?_⟩
    · simpa using hQ
    · simp
  · by_contra hcon
    push_neg at hcon
    set S : Finset ℕ := T.image f with hS
    have hpart : T.card = ∑ q ∈ S, (T.filter (fun h => f h = q)).card := by
      rw [hS]
      exact Finset.card_eq_sum_card_fiberwise (fun h hh => Finset.mem_image_of_mem f hh)
    obtain ⟨q₀, hq₀mem, hq₀max⟩ := Finset.exists_mem_eq_sup S (hTne.image f)
        (fun q => (T.filter (fun h => f h = q)).card)
    have hmax : ∀ q ∈ S, (T.filter (fun h => f h = q)).card
        ≤ (T.filter (fun h => f h = q₀)).card := by
      intro q hq
      rw [← hq₀max]
      exact Finset.le_sup (f := fun q => (T.filter (fun h => f h = q)).card) hq
    have hcardS : T.card ≤ S.card * (T.filter (fun h => f h = q₀)).card := by
      rw [hpart]
      calc ∑ q ∈ S, (T.filter (fun h => f h = q)).card
          ≤ S.card • (T.filter (fun h => f h = q₀)).card :=
            Finset.sum_le_card_nsmul _ _ _ (fun q hq => hmax q hq)
        _ = S.card * (T.filter (fun h => f h = q₀)).card := nsmul_eq_mul _ _
    have hq₀1 : 1 ≤ q₀ := by
      rw [hS, Finset.mem_image] at hq₀mem
      obtain ⟨h, hh, rfl⟩ := hq₀mem
      exact (hf h hh).1
    have hq₀Q : (q₀ : ℝ) ≤ Q := by
      rw [hS, Finset.mem_image] at hq₀mem
      obtain ⟨h, hh, rfl⟩ := hq₀mem
      exact (hf h hh).2
    have hSle : ((S.card : ℕ) : ℝ) ≤ Q := by
      have hsub : S ⊆ Finset.Icc 1 ⌊Q⌋₊ := by
        intro q hq
        rw [Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · rw [hS, Finset.mem_image] at hq
          obtain ⟨h, hh, rfl⟩ := hq
          exact (hf h hh).1
        · rw [hS, Finset.mem_image] at hq
          obtain ⟨h, hh, rfl⟩ := hq
          exact Nat.le_floor (hf h hh).2
      have h1 : S.card ≤ (Finset.Icc 1 ⌊Q⌋₊).card := Finset.card_le_card hsub
      have h2 : (Finset.Icc 1 ⌊Q⌋₊).card = ⌊Q⌋₊ := by rw [Nat.card_Icc]; omega
      have h3 : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le (le_trans zero_le_one hQ)
      calc ((S.card : ℕ) : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by
            rw [← h2]; exact_mod_cast h1
        _ ≤ Q := h3
    have hfib : Q * ((T.filter (fun h => f h = q₀)).card : ℝ) < (T.card : ℝ) :=
      hcon q₀ hq₀1 hq₀Q
    have hcast : (T.card : ℝ)
        ≤ ((S.card : ℕ) : ℝ) * ((T.filter (fun h => f h = q₀)).card : ℝ) := by
      exact_mod_cast hcardS
    have h2 : ((S.card : ℕ) : ℝ) * ((T.filter (fun h => f h = q₀)).card : ℝ)
        ≤ Q * ((T.filter (fun h => f h = q₀)).card : ℝ) :=
      mul_le_mul_of_nonneg_right hSle (by positivity)
    linarith [hcast, h2, hfib]

/-- **The inverse Weyl estimate for a plain polynomial phase** (no linear term).

`IWfree d C K` says: for every integer polynomial `Q` of degree `d`, every real `ξ`, every
interval `Icc a b` of integers and every `ε ∈ (0,1]`: if the interval is longer than `C ε^(-K)`
and the plain exponential sum of `n ↦ ξ Q(n)` has modulus at least `ε · #(Icc a b)`, then
`ξ · (Q.coeff d)` is within `C ε^(-K)/(#(Icc a b))^d` of an integer multiple of `1/q` for some
`q ≤ C ε^(-K)`. -/
def IWfree (d : ℕ) (C K : ℝ) : Prop :=
  ∀ (Q : Polynomial ℤ) (ξ : ℝ) (a b : ℤ) (ε : ℝ),
    Q.natDegree = d → a ≤ b → 0 < ε → ε ≤ 1 →
    C * ε ^ (-K) ≤ (((b - a : ℤ) : ℝ) + 1) →
    ε * (((b - a : ℤ) : ℝ) + 1) ≤
      ‖∑ n ∈ Finset.Icc a b, ee (ξ * ((Q.eval n : ℤ) : ℝ))‖ →
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C * ε ^ (-K) ∧
      ∃ m : ℤ, |(q : ℝ) * ξ * ((Q.coeff d : ℤ) : ℝ) - (m : ℝ)|
        ≤ C * ε ^ (-K) / ((((b - a : ℤ) : ℝ) + 1) ^ d)

/-- **The inverse Weyl estimate for a plain polynomial phase with a linear term.**

This is the form in which the estimate is applied to the *windowed* sum: the reduction to a plain
sum produces an extra linear phase `n ↦ -t n` whose coefficient is not controlled, while the
conclusion is only about the top coefficient `ξ · Q.coeff d` (the differencing step of the Weyl
argument kills the linear term). -/
def IWlin (d : ℕ) (C K : ℝ) : Prop :=
  ∀ (Q : Polynomial ℤ) (ξ τ : ℝ) (a b : ℤ) (ε : ℝ),
    Q.natDegree = d → a ≤ b → 0 < ε → ε ≤ 1 →
    C * ε ^ (-K) ≤ (((b - a : ℤ) : ℝ) + 1) →
    ε * (((b - a : ℤ) : ℝ) + 1) ≤
      ‖∑ n ∈ Finset.Icc a b, ee (ξ * ((Q.eval n : ℤ) : ℝ) + τ * (n : ℝ))‖ →
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C * ε ^ (-K) ∧
      ∃ m : ℤ, |(q : ℝ) * ξ * ((Q.coeff d : ℤ) : ℝ) - (m : ℝ)|
        ≤ C * ε ^ (-K) / ((((b - a : ℤ) : ℝ) + 1) ^ d)

end Work.KMTAreas.A4
