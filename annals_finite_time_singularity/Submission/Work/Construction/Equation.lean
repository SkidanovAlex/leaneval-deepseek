/-
# The CONSTRUCTION area: the derivation of the `g`-equation (`gEquationFinal`, tex 1343-1369)

This module contains the *algebraic* chain of §Modulation of Elgindi's paper:

* `UVR_sub` — the substitution `Φ = Φ̃ + (1/(4α))sin(2θ)L₁₂(F)` in the quadratic form
  `2U(Φ)∂_θF + 2αV(Φ)D_zF - 2ℛ(Φ)F`, where `U, V, ℛ` are the operators of (Relations)/(PhitoU);
* `MainLHS_explicit` — the expansion of the left hand side of (tex 1345) with `F = F_* + g`,
  using `L₁₂(F_*) = 2α/(1+z)`, the identity `F_* + z∂_zF_* - (1/α)L₁₂(F_*)F_* = 0` and the
  definition of `𝓛_Γ`;
* `MainLHS_eq_N` — the identity `MainLHS(F,Φ) = N(F,Φ)` (tex 1345);
* `intermediate_geqn` — the intermediate equation (tex 1349);
* `gEquationFinal` — the paper's `\eqref{gEquationFinal}`, i.e. `IsGSol`.

## A sign discrepancy with the LaTeX source (recorded, and resolved here)

The paper rewrites `(intermediategeqn)` as
`𝓛_Γ^T(g) = -(Γ/c)(2z²/(1+z)³)L₁₂(3 D_θg/(1+z))(0) - μF_* - (μ+λ+μλ)z∂_zF_* + N₀+N+N_*`
(tex 1361).  With the paper's own definitions (`𝕡(f) = f - (Γ/c)(2z²/(1+z)³)L₁₂(f)(0)` and
`𝓛_Γ^T = 𝓛_Γ - 𝕡(3 D_θg/(1+z))`, whose *minus* sign is forced by the paper's remark
`L₁₂(𝕡 f)(0) = 0`), the correct sign of the projector term is **plus**:
`𝓛_Γ(g) - 3 D_θg/(1+z) = 𝓛_Γ^T(g) - AK·L₁₂(3 D_θg/(1+z))(0)`, so
`𝓛_Γ^T(g) = AK·(L₁₂(3 D_θg/(1+z))(0) - 2αμ) + N₀+N+N_*`
once `λ = -2μ/(1+μ)` (`hlam`) is chosen.  The paper's displayed rewrite, and the defining
relation `μ̄ = L₁₂(3 D_θg/(1+z))(0) + 2αμ` that follows from it, carry the opposite sign of the
term `L₁₂(3 D_θg/(1+z))(0)`.

The *final* equation `\eqref{gEquationFinal}` — written in terms of the coefficient
`μ̄ := L₁₂(N₀)(0) + L₁₂(N)(0)` in front of `AK` — is unaffected: both conventions give
`𝓛_Γ^T(g) = -μ̄ AK + N₀+N+N_*`, the only difference being that the present (definition-driven)
convention fixes the modulation constant to be
`μ = (1/(2α))(L₁₂(N₀)(0)+L₁₂(N)(0)) + (1/(2α))L₁₂(3 D_θg/(1+z))(0)`
(sign of the last term opposite to the paper's display), i.e.
`mufun = (mubar + L₁₂(3 D_θg/(1+z))(0))/(2α)`.  This is the relation proved here in
`gEquationFinal`, with the hypothesis `2αμ = μ̄ + L₁₂(3 D_θg/(1+z))(0)`.

Nothing downstream depends on which of the two conventions is used: the consistency of
`L₁₂(g)(0) = 0` (`LGammaT_L12_zero`) and the size of `μ` (`mu_estimate`) are the same in both.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic
import Submission.Work.Construction.L12_Fstar_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-! ## Unfolding the projector and the transport term -/

theorem LGammaT_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Coercivity.LGammaT α f z θ
      = Work.Coercivity.LGamma α f z θ - Work.Coercivity.Transport f z θ
        + AK α z θ * L12 (Work.Coercivity.Transport f) 0 := by
  rw [Work.Coercivity.LGammaT, Work.Coercivity.Proj, Work.Coercivity.Transport]
  simp only [AK, Work.Coercivity.L12f, L12]
  ring

theorem Transport_eq (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Coercivity.Transport f z θ
      = 3 * s2 θ * Work.Spaces.pth f z θ / (1 + z) := by
  rw [Work.Coercivity.Transport, Work.Spaces.Dth, s2]
  ring

/-! ## The substitution `Φ = Φ̃ + Θ` (tex 1338-1344) -/

/-- **The substitution lemma** (tex 1338-1344): writing `Φ = Φ̃ + Θ` with
`Θ = (1/(4α)) sin(2θ) L₁₂(F)` and using the two evaluations
`U(Θ) = -3Θ + (1/4) sin(2θ)(F,K)`, `V(Θ) = (1/(2α))c2m(θ)L₁₂(F)`,
`ℛ(Θ) = (1/(2α))L₁₂(F) - (1/2)sin²θ (F,K)` (the paper's `U, V, ℛ` evaluations, with
`z∂_z L₁₂(F) = -(F,K)` and `∂_θ Θ = (1/(2α))cos(2θ)L₁₂(F)`), the quadratic form splits as
`UVR(F,Φ) = UVR(F,Φ̃) - (1/α)L₁₂(F)F - (3/(2α))sin2θ L₁₂(F)∂_θF + c2m(θ)L₁₂(F)D_zF
   + (1/2)sin2θ (F,K)∂_θF + sin²θ (F,K)F`.

The last two terms are the two angular-moment terms of `N` (tex `\eqref{N}`); the paper
displays them with coefficients `-α` and `-2α`, which differ from the exact `-1/2` and `-1`
by the factor `2α`. -/
theorem UVR_sub (α : ℝ) (hα : 0 < α) {F Φ Φt Θ : ℝ → ℝ → ℝ} (z θ : ℝ)
    (hcos : Real.cos θ ≠ 0)
    (h1 : Φ z θ = Φt z θ + Θ z θ)
    (h2 : Work.Spaces.pz Φ z θ = Work.Spaces.pz Φt z θ + Work.Spaces.pz Θ z θ)
    (h3 : Work.Spaces.pth Φ z θ = Work.Spaces.pth Φt z θ + Work.Spaces.pth Θ z θ)
    (h4 : Θ z θ = (1 / (4 * α)) * s2 θ * L12 F z)
    (h5 : z * Work.Spaces.pz Θ z θ = -(1 / (4 * α)) * s2 θ * FK F z)
    (h6 : Work.Spaces.pth Θ z θ = (1 / (2 * α)) * Real.cos (2 * θ) * L12 F z) :
    UVR α F Φ z θ = UVR α F Φt z θ - (1 / α) * L12 F z * F z θ
      - (3 / (2 * α)) * s2 θ * L12 F z * Work.Spaces.pth F z θ
      + c2m θ * L12 F z * Work.Spaces.Dz F z θ
      + (1 / 2) * s2 θ * FK F z * Work.Spaces.pth F z θ
      + Real.sin θ ^ 2 * FK F z * F z θ := by
  have hz' : α * z * Work.Spaces.pz Θ z θ = α * (z * Work.Spaces.pz Θ z θ) := by ring
  have hs' : α * Real.sin θ * z * Work.Spaces.pz Θ z θ
      = α * Real.sin θ * (z * Work.Spaces.pz Θ z θ) := by ring
  have hsincos : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ; linarith
  have key : UVR α F Φ z θ = UVR α F Φt z θ + UVR α F Θ z θ := by
    simp only [UVR, Uop, Vop, Rop]
    rw [h1, h2, h3]
    ring
  have key2 : UVR α F Θ z θ
      = -(1 / α) * L12 F z * F z θ
        - (3 / (2 * α)) * s2 θ * L12 F z * Work.Spaces.pth F z θ
        + c2m θ * L12 F z * Work.Spaces.Dz F z θ
        + (1 / 2) * s2 θ * FK F z * Work.Spaces.pth F z θ
        + Real.sin θ ^ 2 * FK F z * F z θ := by
    simp only [UVR, Uop, Vop, Rop]
    rw [hz', hs', h5, h6, h4]
    rw [s2, c2m, Real.sin_two_mul, Real.cos_two_mul, Real.tan_eq_sin_div_cos]
    field_simp
    rw [hsincos]
    ring
  rw [key, key2]
  ring

/-! ## The expansion of the left hand side of tex 1345 -/

theorem MainLHS_explicit {α μ lam : ℝ} (hα : 0 < α) {F g : ℝ → ℝ → ℝ} (z θ : ℝ)
    (hz : (1 : ℝ) + z ≠ 0)
    (hF : F z θ = Fstar α z θ + g z θ)
    (hDz : Work.Spaces.Dz F z θ
      = Work.Spaces.Dz (Fstar α) z θ + Work.Spaces.Dz g z θ)
    (hpth : Work.Spaces.pth F z θ
      = Work.Spaces.pth (Fstar α) z θ + Work.Spaces.pth g z θ)
    (hL : L12 F z = L12 (Fstar α) z + L12 g z)
    (hLstar : L12 (Fstar α) z = 2 * α / (1 + z))
    (hstat : Fstar α z θ + Work.Spaces.Dz (Fstar α) z θ
      - (1 / α) * L12 (Fstar α) z * Fstar α z θ = 0) :
    MainLHS α μ lam F z θ
      = μ * Fstar α z θ + (μ + lam + μ * lam) * Work.Spaces.Dz (Fstar α) z θ
        + Work.Coercivity.LGamma α g z θ
        - (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth g z θ
        + μ * g z θ + (μ + lam + μ * lam) * Work.Spaces.Dz g z θ
        - N0 α F g z θ := by
  have key : MainLHS α μ lam F z θ
      - (μ * Fstar α z θ + (μ + lam + μ * lam) * Work.Spaces.Dz (Fstar α) z θ
        + Work.Coercivity.LGamma α g z θ
        - (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth g z θ
        + μ * g z θ + (μ + lam + μ * lam) * Work.Spaces.Dz g z θ
        - N0 α F g z θ)
      = Fstar α z θ + Work.Spaces.Dz (Fstar α) z θ
        - (1 / α) * L12 (Fstar α) z * Fstar α z θ := by
    rw [MainLHS, N0, Work.Coercivity.LGamma, Work.Coercivity.L]
    rw [show Work.Coercivity.L12f g z = L12 g z from rfl]
    rw [hF, hDz, hpth, hL, hLstar, Fstar, Work.FM.Fstar]
    field_simp
    ring_nf
  linarith [key, hstat]

/-! ## `MainLHS(F,Φ) = N(F,Φ)` (tex 1345) -/

theorem MainLHS_eq_N (α μ lam : ℝ) (hα : 0 < α) {F Φ : ℝ → ℝ → ℝ}
    (hstat : StatEqF α μ lam F Φ)
    (h2 : ∀ z θ, Work.Spaces.pz Φ z θ
      = Work.Spaces.pz (PhiTil α F Φ) z θ + Work.Spaces.pz (Theta α F) z θ)
    (h3 : ∀ z θ, Work.Spaces.pth Φ z θ
      = Work.Spaces.pth (PhiTil α F Φ) z θ + Work.Spaces.pth (Theta α F) z θ)
    (h5 : ∀ z θ, z * Work.Spaces.pz (Theta α F) z θ
      = -(1 / (4 * α)) * s2 θ * FK F z)
    (h6 : ∀ z θ, Work.Spaces.pth (Theta α F) z θ
      = (1 / (2 * α)) * Real.cos (2 * θ) * L12 F z) :
    ∀ z θ, Real.cos θ ≠ 0 → MainLHS α μ lam F z θ = N α F Φ z θ := by
  intro z θ hcos
  have h1 : Φ z θ = PhiTil α F Φ z θ + Theta α F z θ := by
    simp only [PhiTil]; ring
  have h4 : Theta α F z θ = (1 / (4 * α)) * s2 θ * L12 F z := rfl
  have hsub := UVR_sub α hα z θ hcos h1 (h2 z θ) (h3 z θ) h4 (h5 z θ) (h6 z θ)
  have hst : (1 + μ) * F z θ + (1 + μ) * (1 + lam) * Work.Spaces.Dz F z θ
      + UVR α F Φ z θ = 0 := hstat z θ
  have hkey : MainLHS α μ lam F z θ
      = -UVR α F Φ z θ - (1 / α) * L12 F z * F z θ
        - (3 / (2 * α)) * s2 θ * L12 F z * Work.Spaces.pth F z θ
        + c2m θ * L12 F z * Work.Spaces.Dz F z θ := by
    rw [MainLHS]
    linarith [hst]
  rw [hkey, hsub, N]
  simp only [UVR, Uop, Vop, Rop, PhiTil]
  ring

/-! ## The intermediate equation (tex 1349) -/

theorem intermediate_geqn (α μ lam : ℝ) (hα : 0 < α) {F g Φ : ℝ → ℝ → ℝ}
    (hstatF : StatEqF α μ lam F Φ)
    (h2 : ∀ z θ, Work.Spaces.pz Φ z θ
      = Work.Spaces.pz (PhiTil α F Φ) z θ + Work.Spaces.pz (Theta α F) z θ)
    (h3 : ∀ z θ, Work.Spaces.pth Φ z θ
      = Work.Spaces.pth (PhiTil α F Φ) z θ + Work.Spaces.pth (Theta α F) z θ)
    (h5 : ∀ z θ, z * Work.Spaces.pz (Theta α F) z θ
      = -(1 / (4 * α)) * s2 θ * FK F z)
    (h6 : ∀ z θ, Work.Spaces.pth (Theta α F) z θ
      = (1 / (2 * α)) * Real.cos (2 * θ) * L12 F z)
    (hF : ∀ z θ, F z θ = Fstar α z θ + g z θ)
    (hDz : ∀ z θ, Work.Spaces.Dz F z θ
      = Work.Spaces.Dz (Fstar α) z θ + Work.Spaces.Dz g z θ)
    (hpth : ∀ z θ, Work.Spaces.pth F z θ
      = Work.Spaces.pth (Fstar α) z θ + Work.Spaces.pth g z θ)
    (hL : ∀ z, L12 F z = L12 (Fstar α) z + L12 g z)
    (hLstar : ∀ z, L12 (Fstar α) z = 2 * α / (1 + z))
    (hstatS : ∀ z θ, Fstar α z θ + Work.Spaces.Dz (Fstar α) z θ
      - (1 / α) * L12 (Fstar α) z * Fstar α z θ = 0) :
    ∀ z θ, 0 < z → Real.cos θ ≠ 0 →
      Work.Coercivity.LGamma α g z θ
        - (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth g z θ
      = -μ * Fstar α z θ - (μ + lam + μ * lam) * Work.Spaces.Dz (Fstar α) z θ
        + N0 α F g z θ + N α F Φ z θ + Nstar μ lam g z θ := by
  intro z θ hz hcos
  have hz1 : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
  have hN := MainLHS_eq_N α μ lam hα hstatF h2 h3 h5 h6 z θ hcos
  have hex := MainLHS_explicit (α := α) (μ := μ) (lam := lam) hα z θ hz1
    (hF z θ) (hDz z θ) (hpth z θ) (hL z) (hLstar z) (hstatS z θ)
  have hNS : Nstar μ lam g z θ
      = -μ * g z θ - (μ + lam + μ * lam) * Work.Spaces.Dz g z θ := rfl
  rw [← hN, hex, hNS]
  ring

/-! ## The `g`-equation `\eqref{gEquationFinal}` -/

/-- **The `g`-equation** `\eqref{gEquationFinal}` (tex 1369): with the modulation constants
satisfying the paper's choice `μ + λ + μλ = -μ` (i.e. `λ = -2μ/(1+μ)`) and the relation
`2αμ = μ̄ + L₁₂(3 D_θg/(1+z))(0)` fixing `μ` (see the module docstring for the sign of the
latter), the modulation `g` solves the stationary equation `IsGSol`. -/
theorem gEquationFinal (α μ lam : ℝ) (hα : 0 < α) {F g Φ : ℝ → ℝ → ℝ}
    (hstatF : StatEqF α μ lam F Φ)
    (h2 : ∀ z θ, Work.Spaces.pz Φ z θ
      = Work.Spaces.pz (PhiTil α F Φ) z θ + Work.Spaces.pz (Theta α F) z θ)
    (h3 : ∀ z θ, Work.Spaces.pth Φ z θ
      = Work.Spaces.pth (PhiTil α F Φ) z θ + Work.Spaces.pth (Theta α F) z θ)
    (h5 : ∀ z θ, z * Work.Spaces.pz (Theta α F) z θ
      = -(1 / (4 * α)) * s2 θ * FK F z)
    (h6 : ∀ z θ, Work.Spaces.pth (Theta α F) z θ
      = (1 / (2 * α)) * Real.cos (2 * θ) * L12 F z)
    (hF : ∀ z θ, F z θ = Fstar α z θ + g z θ)
    (hDz : ∀ z θ, Work.Spaces.Dz F z θ
      = Work.Spaces.Dz (Fstar α) z θ + Work.Spaces.Dz g z θ)
    (hpth : ∀ z θ, Work.Spaces.pth F z θ
      = Work.Spaces.pth (Fstar α) z θ + Work.Spaces.pth g z θ)
    (hL : ∀ z, L12 F z = L12 (Fstar α) z + L12 g z)
    (hLstar : ∀ z, L12 (Fstar α) z = 2 * α / (1 + z))
    (hstatS : ∀ z θ, Fstar α z θ + Work.Spaces.Dz (Fstar α) z θ
      - (1 / α) * L12 (Fstar α) z * Fstar α z θ = 0)
    (hlam : μ + lam + μ * lam = -μ)
    (hmu : 2 * α * μ = mubar (N0 α F g) (N α F Φ)
      + L12 (Work.Coercivity.Transport g) 0) :
    IsGSol α μ lam F g Φ := by
  intro z θ hzθ
  obtain ⟨hz0, hθ0, hθ1⟩ := hzθ
  have hz : 0 < z := hz0
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  have hT : Work.Coercivity.Transport g z θ
      = (3 / (2 * α)) * s2 θ * L12 (Fstar α) z * Work.Spaces.pth g z θ := by
    have hz1 : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
    have ha : α ≠ 0 := ne_of_gt hα
    rw [Transport_eq, hLstar z, s2]
    field_simp
  have hFst : -μ * Fstar α z θ - (μ + lam + μ * lam) * Work.Spaces.Dz (Fstar α) z θ
      = -(2 * α * μ) * AK α z θ := by
    have h1 : Work.Spaces.Dz (Fstar α) z θ = Fstar α z θ - 2 * α * AK α z θ := by
      have h := Fstar_sub_DzFstar (α := α) (z := z) (θ := θ) hα
        (show (-1 : ℝ) < z by linarith)
      linarith [h]
    rw [hlam, h1]
    ring
  have hint := intermediate_geqn α μ lam hα hstatF h2 h3 h5 h6 hF hDz hpth hL hLstar hstatS
    z θ hz hcos
  have hmid := hint
  rw [hFst] at hmid
  have hAK : -(2 * α * μ) * AK α z θ
      + AK α z θ * L12 (Work.Coercivity.Transport g) 0
      = -mubar (N0 α F g) (N α F Φ) * AK α z θ := by
    rw [hmu]
    ring
  rw [LGammaT_eq, hT, hmid, gRHS]
  linarith [hAK]

end Work.Construction
