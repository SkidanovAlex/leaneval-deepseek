import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N` is local on the open quadrant

The nonlinear term `N` of the modulation chapter (`Work.Construction.N`, the paper's
`\eqref{N}`) is built from three kinds of ingredients:

* pointwise evaluations of `F` and of `Φ̃ = Φ - (1/(4α)) sin(2θ) L₁₂(F)` at `(z,θ)`
  (`Rop`, `Uop`, `Vop`, and the two angular-moment terms),
* the *first* partial derivatives `∂_z`, `∂_θ` of `F` and of `Φ̃` (`pz`, `pth`; the
  operators `Dz`, `Dth` are pointwise multiples of these),
* the angular moment `(F,K)_{L²_θ}(z) = ∫_0^{π/2} F(z,θ) K(θ) dθ`.

All of these depend on `F`, `Φ` only through their values on the open quadrant
`Qd = (0,∞) × (0,π/2)` — the derivatives because `deriv` is local and `Qd` is open, and
the two integral quantities (`L₁₂` and `(F,K)`) because the complement of `Qd` inside the
domain has measure zero (`Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ`).  This module
records that fact: two profiles that agree on the open quadrant give the same `N`.

The statements of the helper lemmas are phrased with the predicate `AgreeQ` ("agree
pointwise on the open quadrant"), which is exactly the hypothesis of the target theorem.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_FinalLeaves.SolFire

/-- `AgreeQ f f'`: the profiles `f` and `f'` agree at every point of the open quadrant
`(0,∞) × (0,π/2)`.  This is the hypothesis of `N_congr_of_agreeOnQ`; the operators of the
modulation chapter only see the values of a profile on that set. -/
def AgreeQ (f f' : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = f' z θ

theorem AgreeQ.symm {f f' : ℝ → ℝ → ℝ} (h : AgreeQ f f') : AgreeQ f' f :=
  fun z θ hz hθ hθ2 => (h z θ hz hθ hθ2).symm

/-- The open quadrant is open, so `deriv` sees only the values of a profile on it. -/
theorem isOpen_Qd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

theorem mem_Qd {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ, hθ2⟩

/-! ## Locality of the first partial derivatives -/

/-- Profiles agreeing on the open quadrant have the same `z`-slice derivative at every
point of the quadrant. -/
lemma pz_agreeQ {f f' : ℝ → ℝ → ℝ} (h : AgreeQ f f') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.pz f z θ = Work.Spaces.pz f' z θ :=
  Work.Spaces.pz_congr_of_isOpen isOpen_Qd
    (fun y hy => h y.1 y.2 hy.1 hy.2.1 hy.2.2) (mem_Qd hz hθ hθ2)

/-- Profiles agreeing on the open quadrant have the same `θ`-slice derivative at every
point of the quadrant. -/
lemma pth_agreeQ {f f' : ℝ → ℝ → ℝ} (h : AgreeQ f f') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.pth f z θ = Work.Spaces.pth f' z θ :=
  Work.Spaces.pth_congr_of_isOpen isOpen_Qd
    (fun y hy => h y.1 y.2 hy.1 hy.2.1 hy.2.2) (mem_Qd hz hθ hθ2)

/-- `D_z = z ∂_z` is local on the open quadrant. -/
lemma Dz_agreeQ {f f' : ℝ → ℝ → ℝ} (h : AgreeQ f f') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  simp only [Work.Spaces.Dz, pz_agreeQ h hz hθ hθ2]

/-- `D_θ = sin(2θ) ∂_θ` is local on the open quadrant. -/
lemma Dth_agreeQ {f f' : ℝ → ℝ → ℝ} (h : AgreeQ f f') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  simp only [Work.Spaces.Dth, pth_agreeQ h hz hθ hθ2]

/-! ## Locality of `Uop`, `Vop`, `Rop` -/

/-- `Uop α Ψ = -3Ψ - α z ∂_zΨ` is local on the open quadrant. -/
lemma Uop_agreeQ {α : ℝ} {Ψ Ψ' : ℝ → ℝ → ℝ} (h : AgreeQ Ψ Ψ') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Construction.Uop α Ψ z θ = Work.Construction.Uop α Ψ' z θ := by
  simp only [Work.Construction.Uop, h z θ hz hθ hθ2, pz_agreeQ h hz hθ hθ2]

/-- `Vop Ψ = ∂_θΨ - tan θ · Ψ` is local on the open quadrant. -/
lemma Vop_agreeQ {Ψ Ψ' : ℝ → ℝ → ℝ} (h : AgreeQ Ψ Ψ') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Construction.Vop Ψ z θ = Work.Construction.Vop Ψ' z θ := by
  simp only [Work.Construction.Vop, h z θ hz hθ hθ2, pth_agreeQ h hz hθ hθ2]

/-- `ℛ(Ψ) = (2 sin θ Ψ + α sin θ z ∂_zΨ + cos θ ∂_θΨ)/cos θ` is local on the open
quadrant. -/
lemma Rop_agreeQ {α : ℝ} {Ψ Ψ' : ℝ → ℝ → ℝ} (h : AgreeQ Ψ Ψ') {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Construction.Rop α Ψ z θ = Work.Construction.Rop α Ψ' z θ := by
  simp only [Work.Construction.Rop, h z θ hz hθ hθ2, pz_agreeQ h hz hθ hθ2,
    pth_agreeQ h hz hθ hθ2]

/-! ## Locality of `L₁₂`, `Θ`, `Φ̃` and of the angular moment `(F,K)` -/

/-- `L₁₂` only sees the values of a profile on the open quadrant
(`Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ`, transported to `Construction.L12`). -/
lemma L12_agreeQ {f f' : ℝ → ℝ → ℝ} (h : AgreeQ f f') {z : ℝ} (hz : 0 < z) :
    Work.Construction.L12 f z = Work.Construction.L12 f' z :=
  Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (a := f) (b := f') (z := z)
    (le_of_lt hz) h

/-- `Θ = (1/(4α)) sin(2θ) L₁₂(F)` is local on the open quadrant. -/
lemma Theta_agreeQ {α : ℝ} {F F' : ℝ → ℝ → ℝ} (hF : AgreeQ F F') {z θ : ℝ}
    (hz : 0 < z) (_hθ : 0 < θ) (_hθ2 : θ < Real.pi / 2) :
    Work.Construction.Theta α F z θ = Work.Construction.Theta α F' z θ := by
  simp only [Work.Construction.Theta, L12_agreeQ hF hz]

/-- `Φ̃ = Φ - Θ` is local on the open quadrant. -/
lemma PhiTil_agreeQ {α : ℝ} {F F' Φ Φ' : ℝ → ℝ → ℝ}
    (hF : AgreeQ F F') (hΦ : AgreeQ Φ Φ') :
    AgreeQ (Work.Construction.PhiTil α F Φ) (Work.Construction.PhiTil α F' Φ') :=
  fun z θ hz hθ hθ2 => by
    simp only [Work.Construction.PhiTil, Theta_agreeQ hF hz hθ hθ2, hΦ z θ hz hθ hθ2]

/-- The angular moment `(F,K)_{L²_θ}(z) = ∫_0^{π/2} F(z,θ) K(θ) dθ` is local on the open
quadrant: at a fixed `z > 0` the two profiles agree for every `θ ∈ (0,π/2)`, i.e. almost
everywhere on `Iθ = [0,π/2]`. -/
lemma FK_agreeQ {F F' : ℝ → ℝ → ℝ} (hF : AgreeQ F F') {z : ℝ} (hz : 0 < z) :
    Work.Construction.FK F z = Work.Construction.FK F' z := by
  simp only [Work.Construction.FK]
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
  filter_upwards [Work.FTS.GalFields.RHS.ae_mem_Ioo_of_mem_Iθ_gal] with θ hθ hθI
  obtain ⟨h1, h2⟩ := hθ hθI
  rw [hF z θ hz h1 h2]

/-! ## The target -/

/-- **`N` is local on the open quadrant**: profiles `(F, Φ)` and `(F', Φ')` that agree
pointwise on `(0,∞) × (0,π/2)` give the same `N` at every point of that quadrant. -/
theorem N_congr_of_agreeOnQ {α : ℝ} {F F' Φ Φ' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hF : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → F z' θ' = F' z' θ')
    (hΦ : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → Φ z' θ' = Φ' z' θ') :
    Work.Construction.N α F Φ z θ = Work.Construction.N α F' Φ' z θ := by
  have hFT : AgreeQ F F' := hF
  have hΦT : AgreeQ Φ Φ' := hΦ
  have hPT : AgreeQ (Work.Construction.PhiTil α F Φ)
      (Work.Construction.PhiTil α F' Φ') := PhiTil_agreeQ hFT hΦT
  have hRop : Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α F' Φ') z θ :=
    Rop_agreeQ (α := α) hPT hz hθ hθ2
  have hUop : Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α F' Φ') z θ :=
    Uop_agreeQ (α := α) hPT hz hθ hθ2
  have hVop : Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α F' Φ') z θ :=
    Vop_agreeQ hPT hz hθ hθ2
  have hFz := hF z θ hz hθ hθ2
  have hpthF := pth_agreeQ hFT hz hθ hθ2
  have hDzF := Dz_agreeQ hFT hz hθ hθ2
  have hFK := FK_agreeQ hFT hz
  simp only [Work.Construction.N, hRop, hUop, hVop, hFz, hpthF, hDzF, hFK]

end Work.FTS_FinalLeaves.SolFire
