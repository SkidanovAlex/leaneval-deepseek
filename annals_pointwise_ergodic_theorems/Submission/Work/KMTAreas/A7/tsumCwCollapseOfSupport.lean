import Mathlib
import Submission.Work.KMTAreas.A7.HiKmodNAux
import Submission.Work.KMTAreas.A7.periodizeEqSelfOfMemRealArc

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar Work.Analysis.IWMultiplier

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## Auxiliary support and periodisation lemmas

These reproduce, verbatim, the `private` helpers of the template
`Submission/Work/KMTAreas/A7/hiKmodN_fibre.lean`; being `private` there they cannot be imported,
so they are re-proved here in the same shape. -/

/-- The arcs grow with their scale. -/
private lemma realArc_subset_of_le {k K : ℤ} (h : k ≤ K) :
    Work.Analysis.IonescuWainger.realArc k ⊆ Work.Analysis.IonescuWainger.realArc K := by
  intro x hx
  rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at hx ⊢
  have hle : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ K := zpow_le_zpow_right₀ (by norm_num) h
  exact ⟨by linarith [hx.1, hle], by linarith [hx.2, hle]⟩

/-- **A non-vanishing periodisation detects a real representative in the support.** -/
private theorem exists_coe_of_periodize_ne_zero {m : ℝ → ℂ} {ξ : Circ}
    (h : Work.Analysis.IonescuWainger.periodize m ξ ≠ 0) :
    ∃ x : ℝ, m x ≠ 0 ∧ ((x : ℝ) : Circ) = ξ := by
  set y : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hydef
  have hyξ : ((y : ℝ) : Circ) = ξ := by
    rw [hydef]; exact AddCircle.coe_equivIco
  have hper : Work.Analysis.IonescuWainger.periodize m ξ = ∑' k : ℤ, m (y + (k : ℝ)) := by
    rw [← hyξ, Work.KMTContract.periodizeCoeEqTsum]
  have hne : ∃ k : ℤ, m (y + (k : ℝ)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact h (by rw [hper]; simp [hcon])
  obtain ⟨k, hk⟩ := hne
  refine ⟨y + (k : ℝ), hk, ?_⟩
  rw [AddCircle.coe_add, hyξ]
  have hk0 : (((k : ℝ)) : Circ) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  rw [hk0, add_zero]

/-- `fourier (T := 1) n` at a real point is the character `e(n·)`. -/
private lemma fourier_coe_eq_ee (n : ℤ) (y : ℝ) :
    fourier (T := 1) n ((y : ℝ) : Circ) = Work.KMTAreas.A7.ee ((n : ℝ) * y) := by
  rw [fourier_coe_apply, Work.KMTAreas.A7.ee]
  congr 1
  push_cast
  ring

/-- `fourier (T := 1) (-n)` at a real point is the character `e(-n·)`. -/
private lemma fourier_coe_eq_ee_neg (n : ℤ) (y : ℝ) :
    fourier (T := 1) (-n) ((y : ℝ) : Circ) = Work.KMTAreas.A7.ee (-(n : ℝ) * y) := by
  rw [fourier_coe_eq_ee]
  congr 1
  push_cast
  ring

/-- **The aliasing vanishing of the periodisation.**  If `m` is supported in the arc `ℝ_{≤k}`, if
`α ≠ α₁` are two frequencies of a set which is non-aliasing at the coarser scale `K ≥ k`, then
`periodize m` vanishes on the translate `ℝ_{≤k} - (α - α₁)`. -/
private theorem periodize_eq_zero_of_aliasing {m : ℝ → ℂ} {k K : ℤ} (hkK : k ≤ K)
    {A : Finset Circ} (hNA : Work.Analysis.IonescuWainger.NonAliasing K A)
    (hmk : ∀ x : ℝ, m x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k)
    {α α₁ : Circ} (hα : α ∈ A) (hα₁ : α₁ ∈ A) (h : α ≠ α₁) {y : ℝ}
    (hyk : y ∈ Work.Analysis.IonescuWainger.realArc k) :
    Work.Analysis.IonescuWainger.periodize m (((y : ℝ) : Circ) - (α - α₁)) = 0 := by
  by_contra hne
  obtain ⟨x, hxne, hxc⟩ := exists_coe_of_periodize_ne_zero hne
  have hxK := realArc_subset_of_le hkK (hmk x hxne)
  have hyK := realArc_subset_of_le hkK hyk
  have heq : α + ((x : ℝ) : Circ) = α₁ + ((y : ℝ) : Circ) := by
    rw [hxc]; abel
  exact h (hNA α hα α₁ hα₁ x hxK y hyK heq).1

/-- **The one-variable collapse at equal arc scales.**

This is `Work.KMTAreas.A7.tsum_cw_collapse_derived` of
`Submission/Work/KMTAreas/A7/hiKmodN_fibre.lean` (currently `private`, ~line 130), specialised to
the case in which the non-aliasing scale `K` equals the support scale `k` (there the template
carries a hypothesis `hkK : k ≤ K`; here one takes `K = k`).  It is the de Leeuw fibre computation
that turns the `cw`-convolution of two band-limited symbols into the product.

The proof follows the template:
* the master identity `Work.KMTAreas.A7.tsum_cw_fourier_eq_integral_aux` (in `HiKmodNAux.lean`)
  rewrites `∑' j, cw m j * e(-jη) * cw f (a-j) = ∫ y, f y * e(-ay) * periodize m ((y : Circle) - η)`;
* if `α ≠ α₁` the integrand vanishes: a non-vanishing `periodize m` at `(y : Circle) - (α - α₁)`
  would produce `x` with `m x ≠ 0` and `α + x = α₁ + y`, impossible for `x, y ∈ realArc k` by
  `NonAliasing` (the private helper `periodize_eq_zero_of_aliasing` of the template, together with
  `exists_coe_of_periodize_ne_zero`);
* if `α = α₁` then `periodize m ((y : Circle)) = m y` for `y ∈ realArc k` by
  `periodizeEqSelfOfMemRealArc`, which yields `cw (fun x => m x * f x) a`. -/
theorem tsumCwCollapseOfSupport {m f : ℝ → ℂ} (hm : ContDiff ℝ 2 m)
    (hcs : HasCompactSupport m) (hf : MeasureTheory.Integrable f)
    {k : ℤ} (hk4 : (2 : ℝ) ^ k ≤ 1 / 4)
    {A : Finset Work.Analysis.IonescuWainger.Circle}
    (hNA : Work.Analysis.IonescuWainger.NonAliasing k A)
    (hmk : ∀ x : ℝ, m x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k)
    (hfk : ∀ x : ℝ, f x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k)
    {α α₁ : Work.Analysis.IonescuWainger.Circle} (hα : α ∈ A) (hα₁ : α₁ ∈ A) (a : ℤ) :
    (∑' j : ℤ, Work.KMTAreas.A7.cw m j * fourier (T := 1) (-j) (α - α₁)
        * Work.KMTAreas.A7.cw f (a - j))
      = if α = α₁ then Work.KMTAreas.A7.cw (fun x => m x * f x) a else 0 := by
  by_cases h : α = α₁
  · subst h
    rw [tsum_cw_fourier_eq_integral_aux hm hcs hf (α - α) a, if_pos rfl, sub_self]
    rw [show (fun y : ℝ => f y * fourier (T := 1) (-a) ((y : ℝ) : Circ)
          * Work.Analysis.IonescuWainger.periodize m (((y : ℝ) : Circ) - 0))
        = fun y : ℝ => (m y * f y) * Work.KMTAreas.A7.ee (-(a : ℝ) * y) from by
      funext y
      rw [sub_zero, fourier_coe_eq_ee_neg]
      by_cases hy : f y = 0
      · rw [hy]; ring
      · rw [periodizeEqSelfOfMemRealArc hk4 hmk (hfk y hy)]
        ring]
    rfl
  · rw [tsum_cw_fourier_eq_integral_aux hm hcs hf (α - α₁) a, if_neg h]
    rw [show (fun y : ℝ => f y * fourier (T := 1) (-a) ((y : ℝ) : Circ)
          * Work.Analysis.IonescuWainger.periodize m (((y : ℝ) : Circ) - (α - α₁)))
        = fun _ => 0 from by
      funext y
      by_cases hy : f y = 0
      · rw [hy]; ring
      · rw [periodize_eq_zero_of_aliasing (le_refl k) hNA hmk hα hα₁ h (hfk y hy)]
        ring]
    simp

end

end Work.KMTAreas.A7
