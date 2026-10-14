import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.MeridianDyn.Bridge.mainLHS_sub_N_eq
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.Stability.MainLHSSubN

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set
open scoped Topology

namespace Work.FTS.MeridianDyn

set_option autoImplicit false

/-! ## The modulation constants -/



/-- **The defining relation of the delivered modulation constant**
`Work.FTS.Galerkin.muDyn = Construction.mufunS` (the sign fix of `FTS_MUFUN_SIGN.md` §5):
`2α·muDyn = μ̄ + L₁₂(Transport g)(0)`.  This is `Work.Construction.two_mul_mufunS` with `muDyn`
unfolded once to `mufunS`; nothing else about `muDyn` is used anywhere below. -/
theorem two_mul_muDyn {α : ℝ} (hα : α ≠ 0) (Φ g : Fam) (τ : ℝ) :
    2 * α * Galerkin.muDyn α Φ g τ
      = Work.Construction.mubar
          (Work.Construction.N0 α (Work.Construction.Ftau α g τ) (Galerkin.slice g τ))
          (Work.Construction.N α (Work.Construction.Ftau α g τ) (Galerkin.slice Φ τ))
        + Work.Construction.L12 (Work.Coercivity.Transport (Galerkin.slice g τ)) 0 := by
  have h : Galerkin.muDyn α Φ g τ
      = Work.Construction.mufunS α
          (Work.Construction.N0 α (Work.Construction.Ftau α g τ) (Galerkin.slice g τ))
          (Work.Construction.N α (Work.Construction.Ftau α g τ) (Galerkin.slice Φ τ))
          (Galerkin.slice g τ) := rfl
  rw [h]
  exact Work.Construction.two_mul_mufunS α _ _ (Galerkin.slice g τ) hα


/-! ## The pointwise derivation of `(E)` with its defect -/

/-- **The dynamic profile equation with its defect.**  From the fake-time equation
`Work.FTS.Galerkin.IsDynEqOn` and the static derivation data `ProfDerivData`, the full profile
`F = F_* + g` satisfies `(E)` up to the explicit defect `(2αμ - μ̄ - L₁₂(Transport g)(0))·AK`:

  `∂_τF + (1+μ)F + (1-μ)D_zF + UVR α F Φ = (2αμ - μ̄ - L₁₂(Transport (g τ))(0))·AK α z θ`,

at every point `(z,θ)` of the open quadrant and every `τ > 0`, where `μ = muDyn α Φ g τ` and
`μ̄ = mubar (N₀) (N)`. -/
theorem dynEqF_pointwise {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φ g : Fam}
    (hD : ProfDerivData α Φ g) (hEq : Galerkin.IsDynEqOn α Φ g)
    {z θ τ : ℝ} (hzθ : (z, θ) ∈ Work.Construction.Qd) (hτ : 0 < τ)
    (hne : 1 + Galerkin.muDyn α Φ g τ ≠ 0) :
    deriv (fun s => profFam α g z θ s) τ
      + (1 + Galerkin.muDyn α Φ g τ) * profFam α g z θ τ
      + (1 - Galerkin.muDyn α Φ g τ) * Work.Spaces.Dz (slice (profFam α g) τ) z θ
      + Work.Construction.UVR α (slice (profFam α g) τ) (slice Φ τ) z θ
      = (2 * α * Galerkin.muDyn α Φ g τ
          - Work.Construction.mubar
              (Work.Construction.N0 α (Work.Construction.Ftau α g τ) (Galerkin.slice g τ))
              (Work.Construction.N α (Work.Construction.Ftau α g τ) (Galerkin.slice Φ τ))
          - Work.Construction.L12 (Work.Coercivity.Transport (Galerkin.slice g τ)) 0)
        * Work.Construction.AK α z θ := by
  have hz0 : 0 < z := hzθ.1
  have hθ0 : 0 < θ := hzθ.2.1
  have hθ1 : θ < Real.pi / 2 := hzθ.2.2
  have hznn : 0 ≤ z := le_of_lt hz0
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  have hz1 : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
  -- the fake-time equation, as an identity of `deriv`s
  have hdyn := (hEq z θ τ hτ.le hzθ).hasDerivAt (Ici_mem_nhds hτ)
  have hdyn' : deriv (fun s => g z θ s) τ
      = -(Work.Coercivity.LGammaT α (Galerkin.slice g τ) z θ)
        + Work.Construction.gRHS α (Galerkin.muDyn α Φ g τ) (Galerkin.lamDyn α Φ g τ)
            (Work.Construction.Ftau α g τ) (Galerkin.slice Φ τ) (Galerkin.slice g τ) z θ := by
    rw [hdyn.deriv]
    rfl
  -- the modulation state whose rates are `κ = 1+μ`, `b = 1+λ`
  set M : Work.Stability.ModState :=
    ⟨fun _ => 1 + Galerkin.muDyn α Φ g τ, fun _ => 1 + Galerkin.lamDyn α Φ g τ⟩ with hM
  have hMk : M.kappa τ = 1 + Galerkin.muDyn α Φ g τ := rfl
  have hMb : M.b τ = 1 + Galerkin.lamDyn α Φ g τ := rfl
  -- the three static ingredients
  have hS9 := Bridge.mainLHS_sub_N_eq (α := α) (g := g) (Φ := Φ) (M := M) (τ := τ)
    hα hα1 hzθ
    (hD.h2 z θ τ hzθ hτ) (hD.h3 z θ τ hzθ hτ) (hD.h5 z θ τ hzθ hτ) (hD.h6 z θ τ hzθ hτ)
    (hD.hDz z θ τ hzθ hτ) (hD.hpth z θ τ hzθ hτ) (hD.hL z τ hznn hτ)
  have hS8 := Bridge.gRHS_sub_gDynRHS (α := α) (g := g) (Φ := Φ) (M := M) (z := z) (θ := θ)
    (τ := τ) hα (by linarith) hne hMk hMb
  have h1 : Galerkin.slice Φ τ z θ
      = Work.Construction.PhiTil α (Work.Construction.Ftau α g τ)
          (Galerkin.slice Φ τ) z θ
        + Work.Construction.Theta α (Work.Construction.Ftau α g τ) z θ := by
    simp only [Work.Construction.PhiTil]; ring
  have hsub := Work.Stability.MainLHSSubN (α := α) (μ := M.kappa τ - 1) (lam := M.b τ - 1)
    hα z θ hcos h1 (hD.h2 z θ τ hzθ hτ) (hD.h3 z θ τ hzθ hτ) (hD.h5 z θ τ hzθ hτ)
    (hD.h6 z θ τ hzθ hτ)
  -- the coefficient identities of the rate dictionary
  have hcK : 1 + (M.kappa τ - 1) = 1 + Galerkin.muDyn α Φ g τ := by rw [hMk]; ring
  have hcB : (1 + (M.kappa τ - 1)) * (1 + (M.b τ - 1)) = 1 - Galerkin.muDyn α Φ g τ := by
    rw [hMk, hMb]
    have hlam : Galerkin.lamDyn α Φ g τ
        = Work.Construction.lamfun (Galerkin.muDyn α Φ g τ) := rfl
    rw [hlam, ← Work.Stability.kappaStar_eq (Galerkin.muDyn α Φ g τ),
      ← Work.Stability.bStar_eq_lamfun (Galerkin.muDyn α Φ g τ)]
    have hk : 1 + (Work.Stability.kappaStar (Galerkin.muDyn α Φ g τ) - 1)
        = Work.Stability.kappaStar (Galerkin.muDyn α Φ g τ) := by ring
    have hb2 : 1 + (Work.Stability.bStar (Galerkin.muDyn α Φ g τ) - 1)
        = Work.Stability.bStar (Galerkin.muDyn α Φ g τ) := by ring
    rw [hk, hb2]
    exact Work.Stability.kappaStar_mul_bStar _ hne
  rw [hcB, hcK] at hsub
  -- combine
  have step1 : deriv (fun s => g z θ s) τ
      + Work.Coercivity.LGammaT α (Galerkin.slice g τ) z θ
      = Work.Construction.gRHS α (Galerkin.muDyn α Φ g τ) (Galerkin.lamDyn α Φ g τ)
          (Work.Construction.Ftau α g τ) (Galerkin.slice Φ τ) (Galerkin.slice g τ) z θ := by
    rw [hdyn']; ring
  have step5 : deriv (fun s => g z θ s) τ
      + (1 + Galerkin.muDyn α Φ g τ) * Work.Construction.Ftau α g τ z θ
      + (1 - Galerkin.muDyn α Φ g τ) * Work.Spaces.Dz (Work.Construction.Ftau α g τ) z θ
      + Work.Construction.UVR α (Work.Construction.Ftau α g τ) (Galerkin.slice Φ τ) z θ
      = (2 * α * Galerkin.muDyn α Φ g τ
          - Work.Construction.mubar
              (Work.Construction.N0 α (Work.Construction.Ftau α g τ) (Galerkin.slice g τ))
              (Work.Construction.N α (Work.Construction.Ftau α g τ) (Galerkin.slice Φ τ))
          - Work.Construction.L12 (Work.Coercivity.Transport (Galerkin.slice g τ)) 0)
        * Work.Construction.AK α z θ := by
    linarith [step1, hS9, hsub, hS8]
  -- transfer to the family notation
  have hFτ : deriv (fun s => profFam α g z θ s) τ = deriv (fun s => g z θ s) τ := by
    have hfun : (fun s => profFam α g z θ s)
        = fun s => Work.Construction.Fstar α z θ + g z θ s := by
      funext s; rw [profFam_eq]
    rw [hfun, deriv_const_add]
  rw [hFτ]
  exact step5

/-! ## `(E)` from the fake-time equation -/

/-- **`(E)` from the fake-time equation, with no `L₁₂`-zero-mode hypothesis.**  Since the sign
fix the defining relation `2α·muDyn = μ̄ + L₁₂(Transport g)(0)` (`two_mul_muDyn`) makes the defect
of `dynEqF_pointwise` vanish *identically*, so the fake-time equation `IsDynEqOn` alone gives the
dynamic profile equation `(E)` for the full profile `F = F_* + g` at the rate `μ = muDyn α Φ g τ`,
on the open quadrant and for `τ > 0`. -/
theorem DynEqF_of_isDynEqOn {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φ g : Fam}
    (hD : ProfDerivData α Φ g) (hEq : Galerkin.IsDynEqOn α Φ g)
    (hne : ∀ τ : ℝ, 0 ≤ τ → 1 + Galerkin.muDyn α Φ g τ ≠ 0) :
    DynEqF α (Galerkin.muDyn α Φ g) (profFam α g) Φ := by
  intro z θ τ hzθ hτ
  have h := dynEqF_pointwise hα hα1 hD hEq hzθ hτ (hne τ hτ.le)
  -- the defect vanishes identically: `2α·muDyn = μ̄ + L₁₂(Transport g)(0)`
  have hrel := two_mul_muDyn (ne_of_gt hα) Φ g τ
  have hzero : (2 * α * Galerkin.muDyn α Φ g τ
      - Work.Construction.mubar
          (Work.Construction.N0 α (Work.Construction.Ftau α g τ) (Galerkin.slice g τ))
          (Work.Construction.N α (Work.Construction.Ftau α g τ) (Galerkin.slice Φ τ))
      - Work.Construction.L12 (Work.Coercivity.Transport (Galerkin.slice g τ)) 0) = 0 := by
    rw [hrel]; ring
  rw [hzero, zero_mul] at h
  exact h

/-- **`(E)` only reads the profile on the open quadrant.**  Two profile families that agree on
`Qd` (for every fake time) satisfy the same dynamic profile equation: the equation is built from
the values, the `D_z`-derivative and the `UVR`-combination of the profile, all of which are
determined by the values on a neighbourhood of the point, where `θ ∈ (0,π/2)`. -/
theorem DynEqF_congr_on_quadrant {α : ℝ} {μ : ℝ → ℝ} {F G Φ : Fam}
    (hFG : ∀ z θ τ : ℝ, 0 < θ → θ < Real.pi / 2 → F z θ τ = G z θ τ)
    (h : DynEqF α μ F Φ) : DynEqF α μ G Φ := by
  intro z θ τ hzθ hτ
  have hz := h z θ τ hzθ hτ
  have hθ0 : 0 < θ := hzθ.2.1
  have hθ1 : θ < Real.pi / 2 := hzθ.2.2
  have hmem : (θ, τ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.univ := ⟨⟨hθ0, hθ1⟩, trivial⟩
  -- the fake-time derivative
  have h1 : deriv (fun s => G z θ s) τ = deriv (fun s => F z θ s) τ :=
    Filter.EventuallyEq.deriv_eq
      (Filter.Eventually.of_forall fun s => (hFG z θ s hθ0 hθ1).symm)
  -- the value
  have h2 : G z θ τ = F z θ τ := (hFG z θ τ hθ0 hθ1).symm
  -- the `D_z` derivatives of the slices
  have h3 : Work.Spaces.Dz (slice G τ) z θ = Work.Spaces.Dz (slice F τ) z θ := by
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    congr 1
    exact Filter.EventuallyEq.deriv_eq
      (Filter.Eventually.of_forall fun z' => (hFG z' θ τ hθ0 hθ1).symm)
  -- the `UVR` combination
  have h4 : Work.Construction.UVR α (slice G τ) (slice Φ τ) z θ
      = Work.Construction.UVR α (slice F τ) (slice Φ τ) z θ := by
    have hth : (fun θ' => slice G τ z θ') =ᶠ[𝓝 θ] fun θ' => slice F τ z θ' := by
      filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩] with θ' hθ''
      exact (hFG z θ' τ hθ''.1 hθ''.2).symm
    have hv : slice G τ z θ = slice F τ z θ := (hFG z θ τ hθ0 hθ1).symm
    simp only [Work.Construction.UVR, Work.Construction.Uop, Work.Construction.Vop,
      Work.Construction.Rop, Work.Spaces.pz, Work.Spaces.pth]
    rw [hth.deriv_eq, h3, hv]
  rw [h1, h2, h3, h4]
  exact hz

/-- **`(E)` for the odd extension of the profile.**  The family `profFamOdd α g` (the full profile
`F_* + g` extended oddly in `θ`, which is the family the physical meridian profile uses)
satisfies the same equation `(E)`: on `Qd` it agrees with `profFam α g`. -/
theorem DynEqF_of_isDynEqOn_odd {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φ g : Fam}
    (hD : ProfDerivData α Φ g) (hEq : Galerkin.IsDynEqOn α Φ g)
    (hne : ∀ τ : ℝ, 0 ≤ τ → 1 + Galerkin.muDyn α Φ g τ ≠ 0) :
    DynEqF α (Galerkin.muDyn α Φ g) (profFamOdd α g) Φ :=
  DynEqF_congr_on_quadrant (fun _ θ _ hθ _ => (profFamOdd_of_nonneg (le_of_lt hθ)).symm)
    (DynEqF_of_isDynEqOn hα hα1 hD hEq hne)


end Work.FTS.MeridianDyn
