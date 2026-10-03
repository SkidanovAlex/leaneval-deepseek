import Mathlib
import Submission.Work.KMTAreas.A7.hiCrudeMult
import Submission.Work.KMTPlan.A6.symD_period_contDiff

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped BigOperators

/-! ### Smoothness of the factors of the fibre symbol

The fibre symbol of the large-scale estimate is the product
`(z₁,z₂) ↦ φ_N(z₁) · φ̃_N(z₂) · weylAvg(z₁,z₂)`.
Each factor is smooth: `φ_N` and `φ̃_N` are differences of rescalings of the fixed smooth cutoff
`η` (`contDiff_kmtEta`), and `weylAvg` is a finite average of the exponentials
`e(ξ₁n + ξ₂P(n))`, which are smooth in `(ξ₁,ξ₂)` because `e` is `exp ∘` an `ℝ`-linear map.
Finally `φ_N` and `φ̃_N` have compact support, so the product does. -/

/-- Additivity of the character `e(x) = exp (2πix)`. -/
private lemma ee_add_lin (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee
  rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ↑(x + y)
      = (2 * ↑Real.pi * Complex.I * ↑x) + (2 * ↑Real.pi * Complex.I * ↑y) by
    push_cast; ring]
  rw [Complex.exp_add]

/-- The exponential of an `ℝ`-linear function of two variables is smooth to every order. -/
private lemma contDiff_ee_lin (n : ℕ) (c₁ c₂ : ℝ) :
    ContDiff ℝ n (fun z : ℝ × ℝ => ee (c₁ * z.1 + c₂ * z.2)) := by
  have h : (fun z : ℝ × ℝ => ee (c₁ * z.1 + c₂ * z.2)) =
      fun z => ee (c₁ * z.1) * ee (c₂ * z.2) := funext fun z => ee_add_lin _ _
  rw [h]
  exact ((contDiff_ee_const_mul n c₁).comp contDiff_fst).mul
      ((contDiff_ee_const_mul n c₂).comp contDiff_snd)

/-- The bump `φ_N` is smooth to every order. -/
private lemma contDiff_varphiN_all (N k : ℕ) : ContDiff ℝ 4 (varphiN N k) := by
  unfold varphiN
  split
  · exact (contDiff_kmtEta 4).comp (contDiff_const.mul contDiff_id)
  · exact ((contDiff_kmtEta 4).comp (contDiff_const.mul contDiff_id)).sub
      ((contDiff_kmtEta 4).comp (contDiff_const.mul contDiff_id))

/-- The `d`-fold rescaled bump `φ̃_N` is smooth to every order. -/
private lemma contDiff_varphitildeN_all (d N k : ℕ) : ContDiff ℝ 4 (varphitildeN d N k) := by
  unfold varphitildeN
  split
  · exact (contDiff_kmtEta 4).comp (contDiff_const.mul contDiff_id)
  · exact ((contDiff_kmtEta 4).comp (contDiff_const.mul contDiff_id)).sub
      ((contDiff_kmtEta 4).comp (contDiff_const.mul contDiff_id))

/-- Each summand `n ↦ e(α₁n+α₂P(n)) e(ξ₁n+ξ₂P(n))` of the discrete Weyl average is smooth in
`(ξ₁,ξ₂)`: the arithmetic character is a constant and the archimedean one is an exponential of a
linear function. -/
private lemma contDiff_momPhase (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (n : ℤ) :
    ContDiff ℝ 4 (fun z : ℝ × ℝ => momPhase P N α₁ α₂ z.1 z.2 n) := by
  have h : (fun z : ℝ × ℝ => momPhase P N α₁ α₂ z.1 z.2 n) =
      fun z => (fourier (T := 1) n α₁ * fourier (T := 1) (P.eval n) α₂)
        * ee ((n : ℝ) * z.1 + PevalR P (n : ℝ) * z.2) := by
    funext z
    unfold momPhase
    rw [show z.1 * (n : ℝ) + z.2 * PevalR P (n : ℝ)
        = (n : ℝ) * z.1 + PevalR P (n : ℝ) * z.2 by ring]
  rw [h]
  exact contDiff_const.mul (contDiff_ee_lin 4 (n : ℝ) (PevalR P (n : ℝ)))

/-- The discrete Weyl average `E_{n ∈ (N/2,N]} e(α₁n+α₂P(n)) e(ξ₁n+ξ₂P(n))` is smooth in
`(ξ₁,ξ₂)` — it is a finite average of smooth functions. -/
private lemma contDiff_weylAvg (P : Polynomial ℤ) (N : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) :
    ContDiff ℝ 4 (fun z : ℝ × ℝ => weylAvg P N α₁ α₂ z.1 z.2) := by
  show ContDiff ℝ 4 fun z : ℝ × ℝ =>
    (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, momPhase P N α₁ α₂ z.1 z.2 (n : ℤ)
  exact contDiff_const.mul (ContDiff.sum fun n _ => contDiff_momPhase P N α₁ α₂ (n : ℤ))

theorem contDiff_hasCompactSupport_fibreSymbol (P : Polynomial ℤ) (N k₁ k₂ : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) : ContDiff ℝ 4 (fun z : ℝ × ℝ => Work.KMTAreas.A7.varphiN N k₁ z.1 * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ z.2 * Work.KMTAreas.A7.weylAvg P N α₁ α₂ z.1 z.2) ∧ HasCompactSupport (fun z : ℝ × ℝ => Work.KMTAreas.A7.varphiN N k₁ z.1 * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ z.2 * Work.KMTAreas.A7.weylAvg P N α₁ α₂ z.1 z.2) := by
  have hφ : ContDiff ℝ 4 (varphiN N k₁) := contDiff_varphiN_all N k₁
  have hψ : ContDiff ℝ 4 (varphitildeN P.natDegree N k₂) :=
    contDiff_varphitildeN_all P.natDegree N k₂
  have hw : ContDiff ℝ 4 (fun z : ℝ × ℝ => weylAvg P N α₁ α₂ z.1 z.2) :=
    contDiff_weylAvg P N α₁ α₂
  refine ⟨?_, ?_⟩
  · exact ((hφ.comp contDiff_fst).mul (hψ.comp contDiff_snd)).mul hw
  · refine HasCompactSupport.of_support_subset_isCompact
      (((hasCompactSupport_varphiN N k₁).isCompact).prod
        ((hasCompactSupport_varphitildeN P.natDegree N k₂).isCompact)) ?_
    intro z hz
    rw [Function.mem_support] at hz
    exact ⟨subset_closure (fun h => hz (by simp [h])),
      subset_closure (fun h => hz (by simp [h]))⟩

end Work.KMTAreas.A7
