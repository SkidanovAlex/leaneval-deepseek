import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXR5L.ProdDefs
import Submission.Work.FTS_RegExport.RXT.velVanish2
import Submission.Work.FTS_RegExport.RXR5.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

/-! ## §1 The three-element set of `RXT.velVanish2`

The `Q` of the `vanish0` leaf lives in a three-element set written with the sanitised family
`GR α g` and the reflected stream function `ΦR α Φs E g`; the coefficients `CoefR`, `CoefV`,
`CoefU` of `ProdDefs` are the *same* objects (`Rop (pExp α) Φ̃_τ`, `Vop Φ̃_τ`,
`Uop (pExp α) Φ̃_τ / sin 2θ`), so membership is `rfl`-level. -/

/-- The three-element set of `RXT.velVanish2`, as a named definition (so that the memberships
below are checked by `rfl` against the leaf's own statement). -/
def coefSet (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (τ : ℝ) : Set (ℝ → ℝ → ℝ) :=
  ({(Work.Construction.Rop (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)),
    Work.Construction.Vop
      (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ),
    fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ / Real.sin (2 * θ)} :
        Set (ℝ → ℝ → ℝ))

theorem coeff_mem_coefSet (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (τ : ℝ) :
    CoefR α Φs E g τ ∈ coefSet α Φs E g τ := by
  simp only [coefSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact Or.inl rfl

theorem coefV_mem_coefSet (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (τ : ℝ) :
    CoefV α Φs E g τ ∈ coefSet α Φs E g τ := by
  simp only [coefSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact Or.inr (Or.inl rfl)

theorem coefU_mem_coefSet (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (τ : ℝ) :
    CoefU α Φs E g τ ∈ coefSet α Φs E g τ := by
  simp only [coefSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact Or.inr (Or.inr rfl)

/-! ## §2 The residual vanishes identically at `z = 0`

`psiR` is *by definition* `Theta (pExp α) (Ftau (pExp α) (GR α g) τ)` on `z ≤ 0`, and `PhiTil`
subtracts exactly that `Theta`; so `PhiT α Φs E g τ 0 θ = 0` for every `θ` — no hypothesis
needed.  Consequently `pth (PhiT α Φs E g τ) 0 θ = 0` (the derivative of a function vanishing
identically in `θ`), and with `z = 0` the `z`-factors of `Rop` and `Uop` die as well. -/

theorem PhiT_zero (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (τ θ : ℝ) : PhiT α Φs E g τ 0 θ = 0 := by
  simp only [PhiT, Work.FTS_RegExport.RXT.v2_PhiT, Work.Construction.PhiTil,
    Work.FTS.Galerkin.slice_apply, Work.FTS.RegExportIface.psiR_of_nonpos (le_refl (0 : ℝ))]
  simp [Work.FTS.RegExportIface.RXT.GR]

theorem pth_PhiT_zero (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (τ θ : ℝ) : Work.Spaces.pth (PhiT α Φs E g τ) 0 θ = 0 := by
  have hfun : (fun θ' => PhiT α Φs E g τ 0 θ') = fun _ => 0 :=
    funext fun θ' => PhiT_zero α Φs E g τ θ'
  simp only [Work.Spaces.pth]
  rw [hfun]
  simp

/-- The `vanish0` coefficient data of the three slots
`CoefR α Φs E g τ = Rop (pExp α) Φ̃_τ`, `CoefV α Φs E g τ = Vop Φ̃_τ`,
`CoefU α Φs E g τ = Uop (pExp α) Φ̃_τ / sin 2θ`:

* order-`0` and first-`D_z`/`D_θ` slot bounds `≤ A·min z 1` on the open quadrant, uniformly in
  `τ ∈ [0,S]` (the `j+i ≤ 1` cases of `RXT.velVanish2`; the `j+i ≤ 2` version is available but only
  `≤ 1` is needed here),
* and the axis values: all three coefficients vanish at `z = 0`.

Route: `RXT.velVanish2` gives, for every `Q` in the three-element set, `∀ j i, j+i ≤ 2 →
|mixed j i Q z θ| ≤ M·min z 1` with `Q` written via
`RegExportIface.phiTil (pExp α) (GR α g) (ΦR α Φs E g) τ` = `PhiT α Φs E g τ` (same object,
`ProdDefs.PhiT`), so the bounds are `rfl`-level after rewriting `mixed 0 0 = id`, `mixed 1 0 = Dz`,
`mixed 0 1 = Dth`.
For `z = 0`: `PhiT α Φs E g τ 0 θ = 0` for **all** `θ` (the `z ≤ 0` branch of `psiR` is exactly the
`Theta (pExp α) (Ftau (pExp α) (GR α g) τ)` subtracted in `PhiTil`), hence also
`pz (PhiT α Φs E g τ) 0 θ = 0` and `pth (PhiT α Φs E g τ) 0 θ = 0` (derivative of an identically
zero function), and each of `Rop`, `Vop`, `Uop` of `Φ̃` then vanishes at `z = 0`. -/
theorem coef_bounds {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∃ A : ℝ, 0 ≤ A ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.Spaces.Dth (Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ) z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.Spaces.Dz (Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ) z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.Spaces.Dth (Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ) z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.Spaces.Dz (Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ) z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.Spaces.Dth (Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ) z θ| ≤ A * min z 1) ∧
      (∀ z θ τ, 0 < z → 0 < θ → θ < π / 2 → τ ∈ Set.Icc 0 S →
        |Work.Spaces.Dz (Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ) z θ| ≤ A * min z 1) ∧
      (∀ θ τ, θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
        Work.FTS_RegExport.RXR5L.CoefR α Φs E g τ 0 θ = 0 ∧
        Work.FTS_RegExport.RXR5L.CoefV α Φs E g τ 0 θ = 0 ∧
        Work.FTS_RegExport.RXR5L.CoefU α Φs E g τ 0 θ = 0) := by
  intro S hS
  -- the `j + i ≤ 2` slot bound of the leaf, sampled at `(j,i) = (0,0), (0,1), (1,0)`
  obtain ⟨M, hM⟩ := Work.FTS_RegExport.RXT.velVanish2 (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hμ S hS
  have hmm : ∀ z : ℝ, 0 < z → (0 : ℝ) ≤ min z 1 := fun z hz => le_min hz.le zero_le_one
  have hMA : ∀ z : ℝ, 0 < z → M * min z 1 ≤ max M 0 * min z 1 :=
    fun z hz => mul_le_mul_of_nonneg_right (le_max_left M 0) (hmm z hz)
  -- the nine slot bounds, sampled from `hM` at the three slots
  have slot : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ Q ∈ coefSet α Φs E g τ, ∀ z θ,
      0 < z → 0 < θ → θ < π / 2 →
        |Q z θ| ≤ M * min z 1 ∧ |Work.Spaces.Dth Q z θ| ≤ M * min z 1 ∧
          |Work.Spaces.Dz Q z θ| ≤ M * min z 1 := by
    intro τ' hτ' Q hQ z θ hz hθ hθ2
    have h00 := hM τ' hτ' z θ hz hθ hθ2 Q hQ 0 0 (by norm_num)
    have h01 := hM τ' hτ' z θ hz hθ hθ2 Q hQ 0 1 (by norm_num)
    have h10 := hM τ' hτ' z θ hz hθ hθ2 Q hQ 1 0 (by norm_num)
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter, Work.Spaces.DthIter] at h00 h01 h10
    exact ⟨h00, h01, h10⟩
  refine ⟨max M 0, le_max_right M 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `|CoefR|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefR α Φs E g τ) (coeff_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).1 (hMA z hz)
  · -- `|D_θ CoefR|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefR α Φs E g τ) (coeff_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).2.1 (hMA z hz)
  · -- `|D_z CoefR|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefR α Φs E g τ) (coeff_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).2.2 (hMA z hz)
  · -- `|CoefV|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefV α Φs E g τ) (coefV_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).1 (hMA z hz)
  · -- `|D_θ CoefV|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefV α Φs E g τ) (coefV_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).2.1 (hMA z hz)
  · -- `|D_z CoefV|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefV α Φs E g τ) (coefV_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).2.2 (hMA z hz)
  · -- `|CoefU|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefU α Φs E g τ) (coefU_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).1 (hMA z hz)
  · -- `|D_θ CoefU|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefU α Φs E g τ) (coefU_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).2.1 (hMA z hz)
  · -- `|D_z CoefU|`
    intro z θ τ hz hθ hθ2 hτ
    exact le_trans (slot τ hτ (CoefU α Φs E g τ) (coefU_mem_coefSet α Φs E g τ)
      z θ hz hθ hθ2).2.2 (hMA z hz)
  · -- the axis values at `z = 0`
    intro θ τ _ _
    exact ⟨by simp [CoefR, Work.Construction.Rop, PhiT_zero, pth_PhiT_zero],
      by simp [CoefV, Work.Construction.Vop, PhiT_zero, pth_PhiT_zero],
      by simp [CoefU, Work.Construction.Uop, PhiT_zero]⟩

end Work.FTS_RegExport.RXR5L

end
