import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.E5Aux2.DensN0Pointwise
import Submission.Work.FTS.StrongEps.E5Aux2.DensNPointwise
import Submission.Work.FTS.StrongEps.E5Aux2.DensTransportBound
import Submission.Work.FTS.StrongEps.E5Aux2.AbsL12densLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

theorem N0_N_Transport_dens_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
        {ε τ C₀ B : ℝ} {g : Work.FTS.Galerkin.Fam} {Maj : ℝ → ℝ},
      Work.FTS.StrongEps.EpsDecay α ρ Φs E ε τ g Maj →
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        ≤ C₀ * α ^ 2 →
      Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        ≤ B →
      ∀ s ∈ Set.Ioi (0 : ℝ),
        ‖Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N0 α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) z θ) s‖
          ≤ C * (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2) ∧
        ‖Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ)
            z θ) s‖
          ≤ C * (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2) ∧
        ‖Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) s‖
          ≤ C * (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2) := by
  obtain ⟨C0, hC0pos, hC0⟩ := DensN0Pointwise
  obtain ⟨C1, hC1pos, hC1⟩ := DensNPointwise
  obtain ⟨C2, hC2pos, hC2⟩ := DensTransportBound
  refine ⟨C0 + C1 + C2, by linarith, ?_⟩
  intro α hαIoc ρ Φs E ε τ C₀ B g Maj hDec hClass hXn hXn6 s hs
  have hα0 : 0 < α := hαIoc.1
  have hC₀0 : 0 ≤ C₀ := by
    have hX : 0 ≤ Work.FTS.Nonlin.Xn α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    nlinarith only [hX, hXn, pow_pos hα0 2]
  have hB0 : 0 ≤ B := by
    have hX : 0 ≤ Work.FTS.StrongGlobal.Xn6 α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 6 _
    linarith only [hX, hXn6]
  have hs0 : (0 : ℝ) < s := hs
  have h1C : 0 ≤ 1 + C₀ := by linarith
  have h1B : 0 ≤ 1 + B := by linarith
  have hX0 : 0 ≤ Maj s / s + 1 / (1 + s) ^ 2 := by
    have h1 : 0 ≤ Maj s / s := div_nonneg (hDec.1 s) hs0.le
    have h2 : 0 ≤ 1 / (1 + s) ^ 2 := by positivity
    linarith only [h1, h2]
  have hpos : 0 ≤ (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2) :=
    mul_nonneg (mul_nonneg h1C h1B) hX0
  have hQ0 : 0 ≤ Maj s + s / (1 + s) ^ 2 := by
    have h1 : 0 ≤ s / (1 + s) ^ 2 := div_nonneg hs0.le (sq_nonneg _)
    linarith only [hDec.1 s, h1]
  have hQs : (Maj s + s / (1 + s) ^ 2) / s = Maj s / s + 1 / (1 + s) ^ 2 := by
    field_simp
  have hcoe0 : C0 * (1 + C₀) * (1 + B) ≤ (C0 + C1 + C2) * (1 + C₀) * (1 + B) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) h1C) h1B
  have hcoe1 : C1 * (1 + C₀) * (1 + B) ≤ (C0 + C1 + C2) * (1 + C₀) * (1 + B) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) h1C) h1B
  have hcoe2 : C2 * (1 + C₀) * (1 + B) ≤ (C0 + C1 + C2) * (1 + C₀) * (1 + B) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) h1C) h1B
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right hcoe0 hX0)
    have h := AbsL12densLe (Y := fun z θ => Work.Construction.N0 α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) z θ) (s := s)
      (A := C0 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2)) hs
      (mul_nonneg (mul_nonneg (mul_nonneg hC0pos.le h1C) h1B) hQ0)
      (fun θ hθ => hC0 (α := α) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (τ := τ) (C₀ := C₀) (B := B) (g := g) (Maj := Maj) hαIoc hDec hClass hXn hXn6 s hs θ hθ)
    have h2 : C0 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) / s
        = C0 * (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2) := by
      rw [show C0 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) / s
          = C0 * (1 + C₀) * (1 + B) * ((Maj s + s / (1 + s) ^ 2) / s) from by ring, hQs]
    simpa only [Real.norm_eq_abs, h2] using h
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right hcoe1 hX0)
    have h := AbsL12densLe (Y := fun z θ => Work.Construction.N α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.StrongEps.JfamP ρ ε g)) τ) z θ) (s := s)
      (A := C1 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2)) hs
      (mul_nonneg (mul_nonneg (mul_nonneg hC1pos.le h1C) h1B) hQ0)
      (fun θ hθ => hC1 (α := α) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (τ := τ) (C₀ := C₀) (B := B) (g := g) (Maj := Maj) hαIoc hDec hClass hXn hXn6 s hs θ hθ)
    have h2 : C1 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) / s
        = C1 * (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2) := by
      rw [show C1 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) / s
          = C1 * (1 + C₀) * (1 + B) * ((Maj s + s / (1 + s) ^ 2) / s) from by ring, hQs]
    simpa only [Real.norm_eq_abs, h2] using h
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right hcoe2 hX0)
    have h := AbsL12densLe (Y := Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) (s := s)
      (A := C2 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2)) hs
      (mul_nonneg (mul_nonneg (mul_nonneg hC2pos.le h1C) h1B) hQ0)
      (fun θ hθ => hC2 (α := α) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (τ := τ) (C₀ := C₀) (B := B) (g := g) (Maj := Maj) hαIoc hDec hXn hXn6 s hs θ hθ)
    have h2 : C2 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) / s
        = C2 * (1 + C₀) * (1 + B) * (Maj s / s + 1 / (1 + s) ^ 2) := by
      rw [show C2 * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) / s
          = C2 * (1 + C₀) * (1 + B) * ((Maj s + s / (1 + s) ^ 2) / s) from by ring, hQs]
    simpa only [Real.norm_eq_abs, h2] using h

end Work.FTS.StrongEps.E5Aux2
