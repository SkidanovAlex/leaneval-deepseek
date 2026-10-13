import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongLWP.Sobolev.EqcProduct
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongEps.HQoAux

theorem integral_sq_basis_second_le {G : ℝ → ℝ → ℝ} {a b c d C K : ℝ}
    (h₁ : MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pzIter 2 G x.1 x.2) ^ 2)
      (Set.Icc a b ×ˢ Set.Icc c d))
    (h₂ : MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2)
      (Set.Icc a b ×ˢ Set.Icc c d))
    (h₃ : MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2)
      (Set.Icc a b ×ˢ Set.Icc c d))
    (h₄ : MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => (Work.Spaces.pthIter 2 G x.1 x.2) ^ 2)
      (Set.Icc a b ×ˢ Set.Icc c d))
    (hb₁ : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pzIter 2 G z θ) ^ 2 ≤ C * K)
    (hb₂ : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pz (Work.Spaces.pth G) z θ) ^ 2 ≤ C * K)
    (hb₃ : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pth (Work.Spaces.pz G) z θ) ^ 2 ≤ C * K)
    (hb₄ : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pthIter 2 G z θ) ^ 2 ≤ C * K) :
    ∫ x in Set.Icc a b ×ˢ Set.Icc c d,
        (|Work.Spaces.pzIter 2 G x.1 x.2| + |Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2|
          + |Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2| + |Work.Spaces.pthIter 2 G x.1 x.2|) ^ 2
      ≤ 16 * C * K := by
  -- The elementary pointwise inequality `(Σ|pᵢ|)² ≤ 4 Σ pᵢ²`.
  have hpt : ∀ p q r t : ℝ, (|p| + |q| + |r| + |t|) ^ 2 ≤ 4 * (p^2 + q^2 + r^2 + t^2) := by
    intro p q r t
    have h1 : |p|^2 = p^2 := sq_abs p
    have h2 : |q|^2 = q^2 := sq_abs q
    have h3 : |r|^2 = r^2 := sq_abs r
    have h4 : |t|^2 = t^2 := sq_abs t
    nlinarith [sq_nonneg (|p| - |q|), sq_nonneg (|p| - |r|), sq_nonneg (|p| - |t|),
      sq_nonneg (|q| - |r|), sq_nonneg (|q| - |t|), sq_nonneg (|r| - |t|),
      abs_nonneg p, abs_nonneg q, abs_nonneg r, abs_nonneg t]
  -- Integrated form of `hpt` for four arbitrary functions on the rectangle.
  have key : ∀ (f₁ f₂ f₃ f₄ : ℝ × ℝ → ℝ),
      IntegrableOn (fun x => (f₁ x)^2) (Set.Icc a b ×ˢ Set.Icc c d) →
      IntegrableOn (fun x => (f₂ x)^2) (Set.Icc a b ×ˢ Set.Icc c d) →
      IntegrableOn (fun x => (f₃ x)^2) (Set.Icc a b ×ˢ Set.Icc c d) →
      IntegrableOn (fun x => (f₄ x)^2) (Set.Icc a b ×ˢ Set.Icc c d) →
      ∫ x in Set.Icc a b ×ˢ Set.Icc c d, (|f₁ x| + |f₂ x| + |f₃ x| + |f₄ x|) ^ 2
        ≤ 4 * ((∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₁ x)^2)
            + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₂ x)^2)
            + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₃ x)^2)
            + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₄ x)^2)) := by
    intro f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄
    have h12 : Integrable (fun x => (f₁ x)^2 + (f₂ x)^2)
        (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := h₁.add h₂
    have h123 : Integrable (fun x => (f₁ x)^2 + (f₂ x)^2 + (f₃ x)^2)
        (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := h12.add h₃
    have hgi : Integrable (fun x => 4 * ((f₁ x)^2 + (f₂ x)^2 + (f₃ x)^2 + (f₄ x)^2))
        (volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := h123.add h₄ |>.const_mul 4
    have hm := integral_mono_of_nonneg (μ := volume.restrict (Set.Icc a b ×ˢ Set.Icc c d))
      (f := fun x => (|f₁ x| + |f₂ x| + |f₃ x| + |f₄ x|) ^ 2)
      (g := fun x => 4 * ((f₁ x)^2 + (f₂ x)^2 + (f₃ x)^2 + (f₄ x)^2))
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      hgi (Filter.Eventually.of_forall fun x => hpt (f₁ x) (f₂ x) (f₃ x) (f₄ x))
    calc ∫ x in Set.Icc a b ×ˢ Set.Icc c d, (|f₁ x| + |f₂ x| + |f₃ x| + |f₄ x|) ^ 2
        = ∫ x, (|f₁ x| + |f₂ x| + |f₃ x| + |f₄ x|) ^ 2
            ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := rfl
      _ ≤ ∫ x, 4 * ((f₁ x)^2 + (f₂ x)^2 + (f₃ x)^2 + (f₄ x)^2)
            ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)) := hm
      _ = 4 * ((∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₁ x)^2)
            + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₂ x)^2)
            + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₃ x)^2)
            + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (f₄ x)^2)) := by
          rw [integral_const_mul, integral_add h123 h₄, integral_add h12 h₃, integral_add h₁ h₂]
  have hkey := key (fun x : ℝ × ℝ => Work.Spaces.pzIter 2 G x.1 x.2)
      (fun x : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2)
      (fun x : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2)
      (fun x : ℝ × ℝ => Work.Spaces.pthIter 2 G x.1 x.2) h₁ h₂ h₃ h₄
  -- Fubini: the rectangle integral of each square is the corresponding iterated integral.
  have e₁ : ∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pzIter 2 G x.1 x.2) ^ 2
      = ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pzIter 2 G z θ) ^ 2 :=
    MeasureTheory.setIntegral_prod
      (fun x : ℝ × ℝ => (Work.Spaces.pzIter 2 G x.1 x.2) ^ 2) h₁
  have e₂ : ∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2
      = ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pz (Work.Spaces.pth G) z θ) ^ 2 :=
    MeasureTheory.setIntegral_prod
      (fun x : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2) h₂
  have e₃ : ∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2
      = ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pth (Work.Spaces.pz G) z θ) ^ 2 :=
    MeasureTheory.setIntegral_prod
      (fun x : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2) h₃
  have e₄ : ∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pthIter 2 G x.1 x.2) ^ 2
      = ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pthIter 2 G z θ) ^ 2 :=
    MeasureTheory.setIntegral_prod
      (fun x : ℝ × ℝ => (Work.Spaces.pthIter 2 G x.1 x.2) ^ 2) h₄
  have hb₁' : (∫ x in Set.Icc a b ×ˢ Set.Icc c d,
      (Work.Spaces.pzIter 2 G x.1 x.2) ^ 2) ≤ C * K := e₁ ▸ hb₁
  have hb₂' : (∫ x in Set.Icc a b ×ˢ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2) ≤ C * K := e₂ ▸ hb₂
  have hb₃' : (∫ x in Set.Icc a b ×ˢ Set.Icc c d,
      (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2) ≤ C * K := e₃ ▸ hb₃
  have hb₄' : (∫ x in Set.Icc a b ×ˢ Set.Icc c d,
      (Work.Spaces.pthIter 2 G x.1 x.2) ^ 2) ≤ C * K := e₄ ▸ hb₄
  have hkey' : ∫ x in Set.Icc a b ×ˢ Set.Icc c d,
        (|Work.Spaces.pzIter 2 G x.1 x.2| + |Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2|
          + |Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2| + |Work.Spaces.pthIter 2 G x.1 x.2|) ^ 2
      ≤ 4 * ((∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pzIter 2 G x.1 x.2) ^ 2)
          + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2)
          + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2)
          + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pthIter 2 G x.1 x.2) ^ 2)) := hkey
  calc ∫ x in Set.Icc a b ×ˢ Set.Icc c d,
        (|Work.Spaces.pzIter 2 G x.1 x.2| + |Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2|
          + |Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2| + |Work.Spaces.pthIter 2 G x.1 x.2|) ^ 2
      ≤ 4 * ((∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pzIter 2 G x.1 x.2) ^ 2)
          + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pz (Work.Spaces.pth G) x.1 x.2) ^ 2)
          + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pth (Work.Spaces.pz G) x.1 x.2) ^ 2)
          + (∫ x in Set.Icc a b ×ˢ Set.Icc c d, (Work.Spaces.pthIter 2 G x.1 x.2) ^ 2)) := hkey'
    _ ≤ 4 * (C * K + C * K + C * K + C * K) := by linarith [hb₁', hb₂', hb₃', hb₄']
    _ = 16 * C * K := by ring

end Work.FTS.StrongEps.HQoAux
