import Mathlib
import Submission.Work.TMComp.LocCantor.C8_jump
import Submission.Work.TMComp.LocCantor.jump_subseq
import Submission.Work.TMComp.LocCantor.ae_subseq_integral

/-!
# The jump integral tends to `0` for a.e. phase, along a vanishing sequence

This file proves `jump_tendsto_ae`.  The input hypothesis is the vanishing of the
`(K2)`-integral over `K ×ˢ (0,1]` along a sequence `e j ↓ 0`:

`∫ p in K ×ˢ (0,1], K2 α lam (p.1 + i e_j) p.2 → 0.`

* Fubini (`integral_prod_Ioc_eq`) rewrites the joint integral as the iterated integral
  `∫_{y ∈ (0,1]} ∫_{E ∈ K} K2 α lam (E + i e_j) y`, and
  `MeasureTheory.Integrable.prod_left_ae` shows that for a.e. `y` the `E`-section is integrable.
* `ae_subseq_integral` then extracts a strictly monotone `φ` with
  `∫_{E ∈ K} K2 α lam (E + i e_{φ j}) y → 0` for a.e. `y`.
* For such a `y`, `jump_subseq` (whose pointwise input is `Psi_jump_cube_le_eight_K2`) upgrades
  this to the vanishing of `∫_{E ∈ K} ‖cayley (Ψ (E+iε)) - cayley (Ψ (E-iε))‖` for a further
  vanishing sequence `ε`.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace Work.TMComp.LocCantor

/-- The imaginary part of `E + ε i` is `ε`. -/
private lemma im_ofReal_add_mul_I (E ε : ℝ) : ((E : ℂ) + (ε : ℂ) * Complex.I).im = ε := by
  simp [Complex.add_im, Complex.mul_im]

/-- The imaginary part of `E + ε i` is positive for `ε > 0`. -/
private lemma im_ofReal_add_mul_I_pos (E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 < ((E : ℂ) + (ε : ℂ) * Complex.I).im := by
  rw [im_ofReal_add_mul_I]; exact hε

/-- Joint integrability on `K ×ˢ (0,1]` becomes integrability for the product of the two
restricted measures. -/
private lemma integrable_prod_of_integrableOn (f : ℝ → ℝ → ℝ) {K : Set ℝ}
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (K ×ˢ Set.Ioc (0 : ℝ) 1)) :
    Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict K).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact hf

/-- **Fubini for `K ×ˢ (0,1]`**: the joint integral is the iterated integral, the phase integral
taken first. -/
private lemma integral_prod_Ioc_eq (f : ℝ → ℝ → ℝ) {K : Set ℝ}
    (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict K).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))) :
    (∫ p in K ×ˢ Set.Ioc (0 : ℝ) 1, f p.1 p.2) = ∫ y in (0 : ℝ)..1, ∫ E in K, f E y := by
  have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume :=
    Measure.volume_eq_prod ℝ ℝ
  rw [hvol, ← Measure.prod_restrict, integral_prod_symm _ hf]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

theorem jump_tendsto_ae (α lam : ℝ) {K : Set ℝ} (hK : MeasurableSet K) (hKfin : MeasureTheory.volume K < ⊤) (e : ℕ → ℝ) (he : ∀ j : ℕ, 0 < e j) (he0 : Filter.Tendsto e Filter.atTop (nhds 0)) (hint : ∀ j : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Work.TMComp.LocCantor.K2 α lam ((p.1 : ℂ) + (e j : ℂ) * Complex.I) p.2) (K ×ˢ Set.Ioc (0 : ℝ) 1)) (h : Filter.Tendsto (fun j : ℕ => ∫ p in K ×ˢ Set.Ioc (0 : ℝ) 1, Work.TMComp.LocCantor.K2 α lam ((p.1 : ℂ) + (e j : ℂ) * Complex.I) p.2) Filter.atTop (nhds 0)) : ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)), ∃ e' : ℕ → ℝ, (∀ j : ℕ, 0 < e' j) ∧ Filter.Tendsto e' Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun j : ℕ => ∫ E in K, ‖Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam ((E : ℂ) + (e' j : ℂ) * Complex.I) y) - Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam ((E : ℂ) - (e' j : ℂ) * Complex.I) y)‖) Filter.atTop (nhds 0) := by
  -- Integrability of the joint integrand as a function on the product of the restricted measures.
  have hprod : ∀ j : ℕ, Integrable
      (fun p : ℝ × ℝ => K2 α lam ((p.1 : ℂ) + (e j : ℂ) * Complex.I) p.2)
      ((volume.restrict K).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    fun j => integrable_prod_of_integrableOn (K := K)
      (f := fun E y => K2 α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y) (hint j)
  -- Fubini: the joint integral is the iterated integral.
  have hFub : (fun j : ℕ => ∫ y in (0 : ℝ)..1,
        ∫ E in K, K2 α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y)
      = fun j : ℕ => ∫ p in K ×ˢ Set.Ioc (0 : ℝ) 1,
          K2 α lam ((p.1 : ℂ) + (e j : ℂ) * Complex.I) p.2 :=
    funext fun j => (integral_prod_Ioc_eq _ (hprod j)).symm
  have hlim : Tendsto (fun j : ℕ => ∫ y in (0 : ℝ)..1,
      ∫ E in K, K2 α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y) atTop (nhds 0) := by
    rw [hFub]
    exact h
  -- Integrability of the `y`-sections of the iterated integral.
  have hFint : ∀ j : ℕ, IntegrableOn
      (fun y : ℝ => ∫ E in K, K2 α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y)
      (Set.Ioc (0 : ℝ) 1) :=
    fun j => (hprod j).integral_prod_right
  -- Nonnegativity of the `y`-sections.
  have hFnonneg : ∀ j : ℕ, 0 ≤ᵐ[((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))]
      (fun y : ℝ => ∫ E in K, K2 α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y) :=
    fun j => Filter.Eventually.of_forall fun y =>
      integral_nonneg fun E =>
        K2_nonneg α lam (im_ofReal_add_mul_I_pos E (he j)) y
  -- A.e. integrability of the `E`-sections, for all `j` simultaneously.
  have hsec : ∀ᵐ y ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)),
      ∀ j : ℕ, Integrable (fun E : ℝ => K2 α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y)
        (volume.restrict K) :=
    MeasureTheory.ae_all_iff.mpr fun j => (hprod j).prod_left_ae
  -- Extract the subsequence making the `E`-integral of `K2` vanish a.e.
  obtain ⟨φ, hφ, hconv⟩ := ae_subseq_integral (F := fun j y =>
    ∫ E in K, K2 α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y) hFnonneg hFint hlim
  filter_upwards [hconv, hsec] with y hy hysec
  obtain ⟨φ', hφ', hlim'⟩ := jump_subseq α lam hK hKfin y (fun j => e (φ j))
    (fun j => he (φ j)) hy (fun j => hysec (φ j))
  exact ⟨fun j => e (φ (φ' j)), fun j => he (φ (φ' j)),
    he0.comp (hφ.tendsto_atTop.comp hφ'.tendsto_atTop), hlim'⟩

end Work.TMComp.LocCantor
