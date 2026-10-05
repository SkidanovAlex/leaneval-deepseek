import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.lagPt_contDiff_one
import Submission.Work.RPB.B2.chordSurf_immersed
import Submission.Work.RPV.levelPt_omega
import Submission.Work.RPB.B5.lagData_imm_aux
import Submission.Work.RPB.B5.lagPt_chart_indep
import Submission.Work.RPB.B5.lagPt_collar_level_derivs
import Submission.Work.RPB.B5.lagPt_collar_deriv_t_ne_zero
import Submission.Work.RPB.B5.lagPt_chart_derivs
import Submission.Work.RPB.B5.lagPt_right_derivs

/-!
# B5: the assembled family `ℓ = lagPt W Γc Ac rho` is an immersion

`Work.RPB.B5.lagData_imm`: for `τ ∈ [0,1]`, `x t ∈ ℝ` the two tangent vectors
`∂_x ℓ τ (x,t)` and `∂_t ℓ τ (x,t)` of the assembled family
(`Submission/Work/RPB/B5/Defs.lean`) are linearly independent.  This is the `imm` field of
`Work.RPV.LagFamily`.

The proof is a case split on the branch of `lagPt`:

* **collar** (`x ≤ -√2`): `ℓ` is `levelPt (Γc τ (sig x) t) (sig x) (Ac τ (sig x) t)`, so the level
  function `K₀ ∘ ℓ` is independent of `t` along the slice and equals `-y²/2` along `y ↦ ℓ τ y t`
  (`Work.RPV.K0_levelPt`); its derivative in `x` is `-x ≠ 0` and in `t` is `0`.  Applying
  `fderiv K₀` to a vanishing combination `u • ∂_x ℓ + v • ∂_t ℓ = 0` gives `u = 0`, and then
  `v • ∂_t ℓ = 0` with `∂_t ℓ ≠ 0` (the reduced coordinate `uproj ∘ ℓ = Γc τ (sig x) ·` and
  `hemb`), so `v = 0`.  The derivative of `K₀ ∘ ℓ` in `x` at the junction `x = -√2`, where the
  formula for `ℓ` changes, is computed from the left with `deriv_eq_of_eqOn_Ioc`.
* **chart** (`-√2 < x ≤ 0`): `ℓ = W τ t (rho τ x t)`, so
  `∂_x ℓ = ∂_x rho • ∂_ρ W` and `∂_t ℓ = ∂_t rho • ∂_ρ W + ∂_t W` (`lagPt_chart_derivs`); the
  chart tangents `∂_ρ W`, `∂_t W` are independent on `0 < ρ ≤ π²/4` (`lagPt_chart_indep`), and
  `∂_x rho ≠ 0` (`hrhoderiv`) forces `v = 0` and then `u = 0`.
* **right half** (`x > 0`): `lagPt` is `tau π` of the reflected left half; the linear part
  `tauLinear π` is injective (`tauLinear_pi_injective`), so the independence at `(x,t)` follows
  from the left-half independence at `(-x, t - π)` (`lagPt_right_derivs`).
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- Algebra of the chord-swap transport: if `u • L (-A') + v • L B' = 0` then
`L ((-u) • A' + v • B') = 0`. -/
private lemma tauLinear_transport (L : Work.RPV.PS →L[ℝ] Work.RPV.PS) {A' B' : Work.RPV.PS}
    {u v : ℝ} (h : u • L (-A') + v • L B' = 0) : L ((-u) • A' + v • B') = 0 := by
  have h1 : L (u • (-A') + v • B') = 0 := by
    rw [map_add, map_smul, map_smul]
    exact h
  have h2 : u • (-A') = (-u) • A' := by rw [smul_neg, neg_smul]
  rwa [h2] at h1

theorem lagData_imm (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a)
    (hsm : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ContDiff ℝ 1 (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t (u v : ℝ),
      u • deriv (fun y => lagPt D.W D.Γc D.Ac D.rho τ y t) x
        + v • deriv (fun s => lagPt D.W D.Γc D.Ac D.rho τ x s) t = 0 →
      u = 0 ∧ v = 0 := by
  intro τ hτ
  have hFcd : ContDiff ℝ 1 (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) := hsm τ hτ
  have hleft : ∀ x : ℝ, x ≤ 0 → ∀ t (u v : ℝ),
      u • deriv (fun y => lagPt D.W D.Γc D.Ac D.rho τ y t) x
        + v • deriv (fun s => lagPt D.W D.Γc D.Ac D.rho τ x s) t = 0 → u = 0 ∧ v = 0 := by
    intro x hx0 t u v h
    by_cases hxle : x ≤ -Real.sqrt 2
    · -- collar region `x ≤ -√2`: the level function `K₀` separates the two tangents
      obtain ⟨hKx, hKt⟩ := lagPt_collar_level_derivs CI a ha D hsm τ hτ x hxle t
      have hne := lagPt_collar_deriv_t_ne_zero CI a ha D hsm τ hτ x hxle t
      have hFat : DifferentiableAt ℝ
          (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) (x, t) :=
        hFcd.contDiffAt.differentiableAt (by norm_num)
      have hK0at : DifferentiableAt ℝ (fun P : Work.RPV.PS => Work.RPV.K0 P)
          (lagPt D.W D.Γc D.Ac D.rho τ x t) :=
        contDiff_K0.contDiffAt.differentiableAt (by norm_num)
      have hAx : deriv (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ y t) x
          = (fderiv ℝ (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) (x, t))
              ((1 : ℝ), (0 : ℝ)) :=
        (hasDerivAt_slice_fst hFat).deriv
      have hBt : deriv (fun s : ℝ => lagPt D.W D.Γc D.Ac D.rho τ x s) t
          = (fderiv ℝ (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) (x, t))
              ((0 : ℝ), (1 : ℝ)) :=
        (hasDerivAt_slice_snd hFat).deriv
      have hKchain : deriv (fun y : ℝ => Work.RPV.K0 (lagPt D.W D.Γc D.Ac D.rho τ y t)) x
          = (fderiv ℝ (fun P : Work.RPV.PS => Work.RPV.K0 P)
                (lagPt D.W D.Γc D.Ac D.rho τ x t))
              ((fderiv ℝ (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) (x, t))
                ((1 : ℝ), (0 : ℝ))) := by
        simpa only [Function.comp_def] using
          (hK0at.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_slice_fst hFat)).deriv
      have hKchaint : deriv (fun s : ℝ => Work.RPV.K0 (lagPt D.W D.Γc D.Ac D.rho τ x s)) t
          = (fderiv ℝ (fun P : Work.RPV.PS => Work.RPV.K0 P)
                (lagPt D.W D.Γc D.Ac D.rho τ x t))
              ((fderiv ℝ (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) (x, t))
                ((0 : ℝ), (1 : ℝ))) := by
        simpa only [Function.comp_def] using
          (hK0at.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_slice_snd hFat)).deriv
      have hfx : (fderiv ℝ (fun P : Work.RPV.PS => Work.RPV.K0 P)
            (lagPt D.W D.Γc D.Ac D.rho τ x t))
          ((fderiv ℝ (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) (x, t))
            ((1 : ℝ), (0 : ℝ))) = -x := by
        rw [← hKchain, hKx]
      have hft : (fderiv ℝ (fun P : Work.RPV.PS => Work.RPV.K0 P)
            (lagPt D.W D.Γc D.Ac D.rho τ x t))
          ((fderiv ℝ (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) (x, t))
            ((0 : ℝ), (1 : ℝ))) = 0 := by
        rw [← hKchaint, hKt]
      have h1 : u • (fderiv ℝ (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) (x, t))
              ((1 : ℝ), (0 : ℝ))
            + v • (fderiv ℝ (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) (x, t))
              ((0 : ℝ), (1 : ℝ)) = 0 := by
        rw [← hAx, ← hBt]
        exact h
      have h2 : (fderiv ℝ (fun P : Work.RPV.PS => Work.RPV.K0 P)
            (lagPt D.W D.Γc D.Ac D.rho τ x t))
          (u • (fderiv ℝ (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) (x, t))
              ((1 : ℝ), (0 : ℝ))
            + v • (fderiv ℝ (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) (x, t))
              ((0 : ℝ), (1 : ℝ))) = 0 := by
        rw [h1, map_zero]
      rw [map_add, map_smul, map_smul, hfx, hft] at h2
      have hux : u * x = 0 := by
        simp only [smul_eq_mul, mul_zero, add_zero, mul_neg, neg_eq_zero] at h2
        exact h2
      have hu : u = 0 := by
        rcases mul_eq_zero.mp hux with h4 | h4
        · exact h4
        · exfalso
          have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
          linarith
      have hv : v = 0 := by
        by_contra hvne
        have h5 : v • (fderiv ℝ (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) (x, t))
              ((0 : ℝ), (1 : ℝ)) = 0 := by
          have h6 := h1
          rw [hu, zero_smul, zero_add] at h6
          exact h6
        have h7 : (fderiv ℝ (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) (x, t))
              ((0 : ℝ), (1 : ℝ)) = 0 := by
          rcases smul_eq_zero.mp h5 with h8 | h8
          · exact absurd h8 hvne
          · exact h8
        exact hne (by rw [hBt, h7])
      exact ⟨hu, hv⟩
    · -- chart region `-√2 < x ≤ 0`
      have hx : -Real.sqrt 2 < x := not_le.mp hxle
      have hxIoc : x ∈ Set.Ioc (-Real.sqrt 2) 0 := ⟨hx, hx0⟩
      obtain ⟨hdx, hdt⟩ := lagPt_chart_derivs CI a ha D hsm τ hτ x hxIoc t
      have hrng := D.hrhoval τ hτ x hxIoc t
      have hrx : deriv (fun y : ℝ => D.rho τ y t) x ≠ 0 := D.hrhoderiv τ hτ x hxIoc t
      have hV := lagPt_chart_indep CI a ha D τ hτ t (D.rho τ x t) ⟨hrng.1, hrng.2⟩
      have h1 : (u * deriv (fun y : ℝ => D.rho τ y t) x
              + v * deriv (fun s : ℝ => D.rho τ x s) t)
            • deriv (fun ρ' : ℝ => D.W τ t ρ') (D.rho τ x t)
          + v • deriv (fun s : ℝ => D.W τ s (D.rho τ x t)) t = 0 := by
        have h0 := h
        rw [hdx, hdt] at h0
        rw [smul_smul, smul_add, smul_smul, ← add_assoc] at h0
        rw [add_smul]
        exact h0
      obtain ⟨hα, hv⟩ := hV _ _ h1
      have hu : u = 0 := by
        rw [hv] at hα
        have h2 : u * deriv (fun y : ℝ => D.rho τ y t) x = 0 := by simpa using hα
        exact (mul_eq_zero.mp h2).resolve_right hrx
      exact ⟨hu, hv⟩
  intro x t u v h
  by_cases hx0 : x ≤ 0
  · exact hleft x hx0 t u v h
  · -- right half `x > 0`: `lagPt` is `tau π` of the reflected left half
    have hx : 0 < x := not_le.mp hx0
    obtain ⟨hdx, hdt⟩ := lagPt_right_derivs CI a ha D hsm τ hτ x hx t
    have h1 : u • Work.RPV.tauLinear Real.pi
          (-(deriv (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ y (t - Real.pi)) (-x)))
        + v • Work.RPV.tauLinear Real.pi
          (deriv (fun s : ℝ => lagPt D.W D.Γc D.Ac D.rho τ (-x) s) (t - Real.pi)) = 0 := by
      rw [← hdx, ← hdt]
      exact h
    have h2 := tauLinear_transport (Work.RPV.tauLinear Real.pi) h1
    have h3 : (-u) • deriv (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ y (t - Real.pi)) (-x)
        + v • deriv (fun s : ℝ => lagPt D.W D.Γc D.Ac D.rho τ (-x) s) (t - Real.pi) = 0 :=
      tauLinear_pi_injective (by rw [h2, map_zero])
    obtain ⟨hu, hv⟩ := hleft (-x) (by linarith) (t - Real.pi) (-u) v h3
    exact ⟨by linarith, hv⟩

end Work.RPB.B5
