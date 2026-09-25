import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs
import Submission.Work.BourgainPlan.IonescuWainger.hasFreqSupport_mul_pow
import Submission.Work.BourgainPlan.IonescuWainger.hasFreqSupport_sum

/-!
# The quadratic weight `1 + ε² n²` does not spread the frequency support

If the Fourier transform of `g ∈ ℓ²(ℤ)` vanishes a.e. outside `E`, and `n ↦ (1 + ε² n²) g(n)` is
also in `ℓ²`, then the Fourier transform of the weighted sequence vanishes a.e. outside the
closure of `E`.

This is the elementary input of Tao's weighted `ℓ²` argument for the Ionescu–Wainger multiplier
theorem: the weight is a polynomial of degree `2`, so on the Fourier side it is a differential
operator of order `2` and hence local; the support can only grow by taking the closure.

The proof splits the weight as a *sum* of two band-limited pieces: the identity term `g` (whose
frequency support is contained in `E ⊆ closure E`) and the quadratic term `ε² (n² g)` (handled by
`hasFreqSupport_mul_pow`, again with support in `closure E`).  A finite sum of band-limited ℓ²
sequences has frequency support in the union of the supports (`hasFreqSupport_sum`), and single
terms may be scaled by constants (`hasFreqSupport_const_mul`).
-/

open MeasureTheory
open scoped lp BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- A constant multiple of a sequence with frequency support in `E` also has frequency support in
`E`: the Fourier transform is linear in the coefficients. -/
theorem hasFreqSupport_const_mul {f : ℤ → ℂ} (hf : Memℓp f 2) {E : Set Circle}
    (h : HasFreqSupport f hf E) (c : ℂ) :
    HasFreqSupport (fun n => c * f n) (hf.const_mul c) E := by
  simp only [HasFreqSupport] at h ⊢
  have hft : ftLp (fun n => c * f n) (hf.const_mul c) = c • ftLp f hf := by
    simp only [ftLp]
    rw [show (⟨fun n => c * f n, hf.const_mul c⟩ : lp (fun _ : ℤ => ℂ) 2)
          = c • (⟨f, hf⟩ : lp (fun _ : ℤ => ℂ) 2) from rfl]
    rw [map_smul]
  rw [hft]
  filter_upwards [Lp.coeFn_smul c (ftLp f hf), h] with θ h1 h2 hθE
  rw [h1]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2 hθE, mul_zero]

/-- **The quadratic weight `1 + ε² n²` does not spread the frequency support.**  If the Fourier
transform of `g ∈ ℓ²(ℤ)` vanishes a.e. outside `E` and `n ↦ (1 + ε² n²) g(n)` is also in `ℓ²`,
then the Fourier transform of the weighted sequence vanishes a.e. outside the closure of `E`. -/
theorem hasFreqSupport_quadratic_weight {g : ℤ → ℂ} {E : Set Circle} {ε : ℝ} (hε : 0 ≤ ε)
    (hg : Memℓp g 2) (hE : HasFreqSupport g hg E)
    {hW : Memℓp (fun n : ℤ => (1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2) * g n) 2} :
    HasFreqSupport (fun n : ℤ => (1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2) * g n) hW (closure E) := by
  by_cases hε0 : ε = 0
  · -- `ε = 0`: the weight is identically `1`.
    subst hε0
    have hcongr : ∀ n : ℤ,
        (fun n : ℤ => (1 + ((0 : ℝ) : ℂ) ^ 2 * (n : ℂ) ^ 2) * g n) n = g n := by
      intro n; simp
    exact (mulPow_hasFreqSupport_congr hcongr hW hg).mpr
      (mulPow_hasFreqSupport_mono hE subset_closure)
  · -- `ε ≠ 0`: the weight is `g + ε² · (n² g)`, a sum of two band-limited sequences.
    have hmem2 : Memℓp (fun n : ℤ => (n : ℂ) ^ 2 * g n) 2 := by
      have hdiff : Memℓp (fun n : ℤ => (1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2) * g n - g n) 2 :=
        hW.sub hg
      have hscaled : Memℓp (fun n : ℤ =>
          ((ε : ℂ) ^ 2)⁻¹ * ((1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2) * g n - g n)) 2 :=
        hdiff.const_mul (((ε : ℂ) ^ 2)⁻¹)
      have hεC : (ε : ℂ) ≠ 0 := by exact_mod_cast hε0
      have hε2 : (ε : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hεC
      refine memℓp_congr_aux
        (f := fun n : ℤ => ((ε : ℂ) ^ 2)⁻¹ * ((1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2) * g n - g n))
        (g := fun n : ℤ => (n : ℂ) ^ 2 * g n) ?_ hscaled
      intro n
      rw [show ((1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2) * g n - g n)
            = (ε : ℂ) ^ 2 * ((n : ℂ) ^ 2 * g n) by ring]
      rw [← mul_assoc, inv_mul_cancel₀ hε2, one_mul]
    have h1 : HasFreqSupport g hg (closure E) := mulPow_hasFreqSupport_mono hE subset_closure
    have h2 : HasFreqSupport (fun n : ℤ => (n : ℂ) ^ 2 * g n) hmem2 (closure E) :=
      hasFreqSupport_mul_pow 2 hg hE hmem2
    have hw : Memℓp (fun n : ℤ => (ε : ℂ) ^ 2 * ((n : ℂ) ^ 2 * g n)) 2 :=
      hmem2.const_mul ((ε : ℂ) ^ 2)
    have hw' : HasFreqSupport (fun n : ℤ => (ε : ℂ) ^ 2 * ((n : ℂ) ^ 2 * g n)) hw
        (closure E) :=
      hasFreqSupport_const_mul hmem2 h2 ((ε : ℂ) ^ 2)
    -- The weight as a two-term sum, indexed by `Bool`.
    have hfam : ∀ b : Bool,
        Memℓp (bif b then g else fun n : ℤ => (ε : ℂ) ^ 2 * ((n : ℂ) ^ 2 * g n)) 2 := by
      intro b; cases b
      · exact hw
      · exact hg
    have hfsupp : ∀ b : Bool,
        HasFreqSupport (bif b then g else fun n : ℤ => (ε : ℂ) ^ 2 * ((n : ℂ) ^ 2 * g n))
          (hfam b) (closure E) := by
      intro b; cases b
      · exact (mulPow_hasFreqSupport_congr
          (f := fun n : ℤ => (ε : ℂ) ^ 2 * ((n : ℂ) ^ 2 * g n))
          (g := fun n : ℤ => (ε : ℂ) ^ 2 * ((n : ℂ) ^ 2 * g n))
          (fun n => rfl) (hfam false) hw).mpr hw'
      · exact (mulPow_hasFreqSupport_congr (f := g) (g := g)
          (fun n => rfl) (hfam true) hg).mpr h1
    have hsum := hasFreqSupport_sum
      (f := fun b : Bool => bif b then g else fun n : ℤ => (ε : ℂ) ^ 2 * ((n : ℂ) ^ 2 * g n))
      (E := fun _ : Bool => closure E) hfam hfsupp
    rw [Set.iUnion_const] at hsum
    refine (mulPow_hasFreqSupport_congr
      (f := fun m : ℤ =>
        ∑ b : Bool, (bif b then g else fun n : ℤ => (ε : ℂ) ^ 2 * ((n : ℂ) ^ 2 * g n)) m)
      (g := fun n : ℤ => (1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2) * g n)
      ?_ (memℓp_sum hfam) hW).mp hsum
    intro m
    rw [Fintype.sum_bool]
    simp only [cond_true, cond_false]
    ring

end Work.BourgainPlan.IonescuWainger
