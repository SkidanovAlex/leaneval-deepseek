/-
# `Work.FTS_RegExport.RXR5L.NsData_C1Jet` — the `N_*`-jet data of the sanitised family

The term

  `N_*(μ,λ,g) = -μ·g - (μ + λ + μλ)·D_z g`   (`Work.Construction.Nstar`)

of the right-hand side of the fake-time equation, evaluated on the dynamically computed clock
functions `μ(τ) = muDyn (pExp α) Φ g τ`, `λ(τ) = lamDyn (pExp α) Φ g τ` and on the sanitised
family `SG α g = gS α (tauExt g)`, carries the `C1Jet`-data of `R5Parts` (the two fields `hNsJet`
and `hNsZ` of `Work.FTS.RegPkgGal.Der.R5Parts_of_pieces`, i.e. the hypothesis shape of the
consumers `r5Parts_proved` / `forall_regPkg_of_parts'`).

## The route (three inputs, two library lemmas)

The identity is the one of `Work.FTS.RegPkgGal.Der.jet_Nstar` and
`Work.FTS.RegPkgGal.Der.zderiv_Nstar`: `N_*` is a sum of two *products*, and `D_z g` is
differentiated as a whole, so no second `z`-derivative of `g` is ever needed.

* the `Jet`-data of `SG α g` and of the slot `D_z (SG α g)(·,·,τ)` come from
  `RXR5L/SG_C1Jet` (`Jet` of the sanitised family) resp. from the hypothesis `hO1`
  (`C1Jet` of `D_z (SG α g)`, whose `Jet` half is its value bound/Hölder modulus); the two
  constants are unified by `Jet_mono`;
* the clock data `|μ τ|, |λ τ| ≤ max M L` and the `α`-Hölder moduli `≤ max M L · |τ-τ'|^α` come
  from `hMuB` (`M`) and `hMuH` (`L`), again via a common constant;
* the `z`-derivative data of the two slots with the common constant `max NG N₂` come from the
  `zderiv`-halves of the two `C1Jet`-hypotheses.

Then `NsData = N_*(μ τ, λ τ, SG α g(·,·,τ))` with constant `N₁ = max Nj Nz`, where `Nj` is the
`Jet`-constant produced by `jet_Nstar` and `Nz` the derivative bound of `zderiv_Nstar`; the two
conclusions are converted to the stated shape by `Jet.congr` (`gSlice` = λ-abstraction) and by
definitional unfolding (`HasDerivAt` with the same `λ`-abstraction).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS_RegExport.RXR5L.SG_C1Jet
import Submission.Work.FTS.RegPkgGal.Der.jet_Nstar
import Submission.Work.FTS.RegPkgGal.Der.zderiv_Nstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR5L

set_option autoImplicit false

theorem NsData_C1Jet {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hO1 : ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂
        (fun z θ τ => Work.Spaces.Dz (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃
        (fun z θ τ => Work.Spaces.Dth (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ))
    (hMuB : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ| ≤ M ∧
      |Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ| ≤ M)
    (hMuH : ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ
        - Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ'| ≤ L * |τ - τ'| ^ α ∧
      |Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ
        - Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ'| ≤ L * |τ - τ'| ^ α) :
    ∃ N₁ : ℝ, 0 ≤ N₁ ∧
      Work.FTS.Regularity.Jet α S N₁ (fun z θ τ => Work.Construction.Nstar
        (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ)
        (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ)
        (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z θ) ∧
      ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
        ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.Nstar
          (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ)
          (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ)
          (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z' θ) d z ∧
          |d| ≤ N₁ := by
  obtain ⟨N₂, N₃, hN₂0, hN₃0, hC1₂, hC1₃⟩ := hO1
  obtain ⟨NG, hNG0, hC1G⟩ := SG_C1Jet hα hα13 hOK hS hSt1
  obtain ⟨M, hM0, hMB⟩ := hMuB
  obtain ⟨L, hL0, hLH⟩ := hMuH
  -- the two `Jet`-slots on a common constant `max NG N₂`
  have hJGN : Work.FTS.Regularity.Jet α S (max NG N₂) (Work.FTS_RegExport.RXR5.SG α g) :=
    Jet_mono hC1G.1 (le_max_left NG N₂)
  have hJZN : Work.FTS.Regularity.Jet α S (max NG N₂)
      (fun z θ τ => Work.Spaces.Dz (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ) :=
    Jet_mono hC1₂.1 (le_max_right NG N₂)
  -- the two `z`-derivative slots on the same constant
  have hDG : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.FTS_RegExport.RXR5.SG α g z' θ τ) d z ∧
        |d| ≤ max NG N₂ := by
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hC1G.2 τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb (le_max_left NG N₂)⟩
  have hDZ : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Spaces.Dz
          (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z' θ) d z ∧
        |d| ≤ max NG N₂ := by
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hC1₂.2 τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb (le_max_right NG N₂)⟩
  -- the clock bounds on the common constant `max M L`
  have hmuB : ∀ τ ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
        (Work.FTS_RegExport.RXR5.SG α g) τ| ≤ max M L :=
    fun τ hτ => le_trans (hMB τ hτ).1 (le_max_left M L)
  have hlamB : ∀ τ ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
        (Work.FTS_RegExport.RXR5.SG α g) τ| ≤ max M L :=
    fun τ hτ => le_trans (hMB τ hτ).2 (le_max_left M L)
  have hMuhH : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ
        - Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ'|
        ≤ max M L * |τ - τ'| ^ α :=
    fun τ hτ τ' hτ' => le_trans (hLH τ hτ τ' hτ').1
      (mul_le_mul_of_nonneg_right (le_max_right M L) (Real.rpow_nonneg (abs_nonneg _) α))
  have hLamhH : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ
        - Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ'|
        ≤ max M L * |τ - τ'| ^ α :=
    fun τ hτ τ' hτ' => le_trans (hLH τ hτ τ' hτ').2
      (mul_le_mul_of_nonneg_right (le_max_right M L) (Real.rpow_nonneg (abs_nonneg _) α))
  -- the clock data in the shape `jet_Nstar` / `zderiv_Nstar` consume
  have hmuPair : 0 ≤ max M L ∧ ∀ τ ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ| ≤ max M L ∧
      ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ
          - Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ'|
          ≤ max M L * |τ - τ'| ^ α :=
    ⟨le_trans hM0 (le_max_left M L), fun τ hτ => ⟨hmuB τ hτ, hMuhH τ hτ⟩⟩
  have hlamPair : ∀ τ ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SΨ α Φs E g)
          (Work.FTS_RegExport.RXR5.SG α g) τ| ≤ max M L ∧
      ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ
          - Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ'|
          ≤ max M L * |τ - τ'| ^ α :=
    fun τ hτ => ⟨hlamB τ hτ, hLamhH τ hτ⟩
  -- the two library lemmas at the sanitised family and the dynamic clocks
  obtain ⟨Nj, hJet⟩ := Work.FTS.RegPkgGal.Der.jet_Nstar (α := α) (S := S)
    (g := Work.FTS_RegExport.RXR5.SG α g)
    (mu := fun τ => Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ)
    (lam := fun τ => Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ)
    (N := max NG N₂) (Nmu := max M L) hα hS hJGN hJZN hmuPair hlamPair
  obtain ⟨Nz, hNz0, hZderiv⟩ := Work.FTS.RegPkgGal.Der.zderiv_Nstar (α := α) (S := S)
    (g := Work.FTS_RegExport.RXR5.SG α g)
    (mu := fun τ => Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ)
    (lam := fun τ => Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g) (Work.FTS_RegExport.RXR5.SG α g) τ)
    (N := max NG N₂) (Nmu := max M L) hα hS hDG hDZ
    ⟨le_trans hM0 (le_max_left M L), hmuB⟩ hlamB
  refine ⟨max Nj Nz, le_trans hJet.1 (le_max_left Nj Nz), ?_, ?_⟩
  · refine Work.FTS.Regularity.Jet.congr (Jet_mono hJet (le_max_left Nj Nz)) ?_
    intro z θ τ _ _ _
    rfl
  · intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hZderiv τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb (le_max_right Nj Nz)⟩

end Work.FTS_RegExport.RXR5L
