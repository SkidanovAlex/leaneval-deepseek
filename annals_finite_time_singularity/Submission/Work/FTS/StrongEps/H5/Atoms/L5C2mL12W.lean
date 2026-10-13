import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.StrongEps.H5.LevelShift
import Submission.Work.FTS.OpenPkg.angmul_field
import Submission.Work.FTS.StrongPersist.dthU_c2m_bound6
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.GalFields.RHS.sharpN0_defs
import Submission.Work.FTS.StrongEps.H5.Atoms.DthUC2mProfileData

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.Atoms

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-! ## The two pointwise multiplier identities

`D_z` and `D_θ` applied to a product of an angular factor with a second factor: since `D_z` is
`z∂_z` and the angular factor does not depend on `z`, the derivative only hits the second factor;
for a *radial* second factor the surviving derivative falls on the angular factor alone.  Both
identities are consequences of `deriv_const_mul_field` and hold *everywhere*, not merely on the
open quadrant. -/

/-- `D_z (a(θ)·g(z,θ)) = a(θ)·D_z g(z,θ)`. -/
theorem Dz_ang_mul (a : ℝ → ℝ) (g : Work.FTS.Galerkin.Fn) :
    Work.Spaces.Dz (fun z θ => a θ * g z θ)
      = fun z θ => a θ * Work.Spaces.Dz g z θ := by
  funext z θ
  show z * deriv (fun z' => a θ * g z' θ) z = a θ * (z * deriv (fun z' => g z' θ) z)
  rw [deriv_const_mul_field (a θ)]
  ring

/-- `D_θ (a(θ)·r(z)) = (D_θ a)(θ)·r(z)`, where `Work.Spaces.dthU a θ = sin(2θ)·a'(θ)` is the
one-variable avatar of `D_θ` on a `θ`-only profile. -/
theorem Dth_ang_radial_mul (a : ℝ → ℝ) (r : ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => a θ * r z)
      = fun z θ => Work.Spaces.dthU a θ * r z := by
  funext z θ
  show Real.sin (2 * θ) * deriv (fun θ' => a θ' * r z) θ
      = Real.sin (2 * θ) * deriv a θ * r z
  have h : (fun θ' => a θ' * r z) = fun θ' => r z * a θ' := by funext θ'; ring
  rw [h, deriv_const_mul_field (r z)]
  ring

/- The angular data of the derivative profile `D_θ c₂m` — `D_θ c₂m = -3 sin(2θ)²` is `C^∞`
and its `D_θ`-iterates of orders `1..4` are the orders `2..5` of `c₂m`, hence decay like
`sin(2θ)` — is proved in the sibling module
`Submission.Work.FTS.StrongEps.H5.Atoms.DthUC2mProfileData` (imported above), as
`Work.FTS.StrongEps.H5.Atoms.DthUC2mProfileData`. -/

/-- **The `L5` data of the angular atom `c₂(θ)·L₁₂(w)(z)`**, conditional on the `L5`-data of
`L₁₂(w)` (lemma `L5L12W`, passed as the hypothesis `hL12`).

Route: on the open quadrant `Dz (fun z θ => c₂(θ)·L₁₂(w)(z)) = c₂(θ) · Dz (fun z θ => L₁₂(w)(z))`
and `Dth (fun z θ => c₂(θ)·L₁₂(w)(z)) = (Dth c₂)(θ) · L₁₂(w)(z)` (`H5.Dz_mul_eqOn_Q0` /
`H5.Dth_mul_eqOn_Q0` plus `Dth` of a radial function is `0`).  Both are products of an angular
factor with an `HQo α 4` factor, so `Work.FTS.OpenPkg.angmul_field` (the level-four
angular-multiplication rule, which asks for `|a θ| ≤ B` and `|DthIter i a 0 θ| ≤ B · sin(2θ)`,
`1 ≤ i ≤ 4`, on `Iθ`) applies with `a = c₂`
(`Work.FTS.GalFields.RHS.smoothOpen_c2m_ang`, `Work.FTS.Nonlinear.Pieces.abs_c2m_le_two`,
`Work.FTS.Nonlinear.Pieces.DthIter_c2m_le`) — for the `D_θ`-derivative of the atom the angular
factor is `Dth c₂`, whose iterates `DthIter i (Dth c₂) = DthIter (i+1) c₂` need the same
pointwise bound at angular orders `≤ 5` (`Work.FTS.StrongPersist.dthU_c2m_bound6`).  The norms of
`c₂·L₁₂(w)` and of `c₂·Dz(L₁₂(w))` are bounded by `Cang · 1000 · Xn α (L₁₂ w)` resp.
`Cang · 1000 · Xn α (Dz (L₁₂ w))`, with `Cang` the constant of `angmul_field`; use the `L5`-bound
`a` of `hL12` for both. -/
theorem L5C2mL12W
    (hL12 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
      ∃ a : ℝ, 0 < a ∧ ∀ {w : Work.FTS.Galerkin.Fn},
        Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
        Work.Spaces.HkNorm α 6 w ≤ B →
        Work.FTS.StrongEps.H5.L5 α (fun z θ => Work.Construction.L12 w z) a) :
    ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
    ∃ a : ℝ, 0 < a ∧ ∀ {w : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.FTS.StrongEps.H5.L5 α
        (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) a := by
  intro α hαI C₀ B
  have hα : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  -- the two universal constants
  obtain ⟨Cang, hCangpos, hang⟩ := Work.FTS.OpenPkg.angmul_field
  obtain ⟨Cd, hCdpos, hCdSm, hCdB, hCdIt⟩ := DthUC2mProfileData
  -- the `L5`-data of the radial atom
  obtain ⟨aL, haLpos, hLdat⟩ := hL12 hαI (C₀ := C₀) (B := B)
  -- the common constant of the answer
  set A : ℝ := Cang * 1000 * aL + Cang * Cd * aL + 1 with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hle1 : Cang * 1000 * aL ≤ A := by
    rw [hAdef]; linarith [show (0 : ℝ) ≤ Cang * Cd * aL by positivity]
  have hle2 : Cang * Cd * aL ≤ A := by
    rw [hAdef]; linarith [show (0 : ℝ) ≤ Cang * 1000 * aL by positivity]
  refine ⟨A, hApos, ?_⟩
  intro w hw hXnw hX6
  -- the `L5`-data of `L₁₂(w)`
  have hLw : Work.FTS.StrongEps.H5.L5 α (fun z θ => Work.Construction.L12 w z) aL :=
    hLdat hw hXnw hX6
  have hgsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 w z) := hLw.qo.1
  have hgmem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 w z) := hLw.qo.2
  have hgX : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 w z) ≤ aL := hLw.bd
  -- the angular data of `c₂m`
  have hc2mSm : Work.FTS.EllipticEst.SmoothOpen
      (fun _ (θ : ℝ) => Work.Construction.c2m θ) :=
    Work.FTS.GalFields.RHS.smoothOpen_c2m_ang
  have hc2mB : ∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ 1000 :=
    fun θ _ => Work.FTS.GalFields.RHS.abs_c2m_le_thousand θ
  have hc2mIt : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
        ≤ 1000 * Real.sin (2 * θ) :=
    fun i hi hi4 => Work.FTS.GalFields.RHS.DthIter_c2m_le_sin i hi hi4
  -- the three applications of the angular-multiplication rule
  have hA1 := hang α hα hα1 (fun θ => Work.Construction.c2m θ)
    (fun z θ => Work.Construction.L12 w z) 1000 hc2mSm hc2mB hc2mIt hgsm hgmem
  have hA2 := hang α hα hα1 (fun θ => Work.Construction.c2m θ)
    (Work.Spaces.Dz (fun z θ => Work.Construction.L12 w z)) 1000 hc2mSm hc2mB hc2mIt
    hLw.qoDz.1 hLw.qoDz.2
  have hA3 := hang α hα hα1 (fun θ => Work.Spaces.dthU Work.Construction.c2m θ)
    (fun z θ => Work.Construction.L12 w z) Cd hCdSm hCdB hCdIt hgsm hgmem
  -- smoothness of the atom and of its two derivatives
  have hfsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hc2mSm hgsm
  -- the `D_z`-slot
  have hDzmem : Work.Spaces.HkMem α 4
      (Work.Spaces.Dz (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hA2.1 (fun z _ θ _ => by
      rw [Dz_ang_mul (fun θ => Work.Construction.c2m θ)
        (fun z θ => Work.Construction.L12 w z)])
  have hDzb : Work.FTS.Nonlin.Xn α
      (Work.Spaces.Dz (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z)) ≤ A := by
    rw [Dz_ang_mul (fun θ => Work.Construction.c2m θ)
      (fun z θ => Work.Construction.L12 w z)]
    exact le_trans hA2.2 (le_trans (mul_le_mul_of_nonneg_left hLw.bdDz (by positivity)) hle1)
  -- the `D_θ`-slot
  have hDthmem : Work.Spaces.HkMem α 4
      (Work.Spaces.Dth (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hA3.1 (fun z _ θ _ => by
      rw [Dth_ang_radial_mul (fun θ => Work.Construction.c2m θ)
        (fun z => Work.Construction.L12 w z)])
  have hDthb : Work.FTS.Nonlin.Xn α
      (Work.Spaces.Dth (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z)) ≤ A := by
    rw [Dth_ang_radial_mul (fun θ => Work.Construction.c2m θ)
      (fun z => Work.Construction.L12 w z)]
    exact le_trans hA3.2 (le_trans (mul_le_mul_of_nonneg_left hgX (by positivity)) hle2)
  -- the six fields of `L5`
  refine ⟨⟨hfsm, hA1.1⟩,
    le_trans hA1.2 (le_trans (mul_le_mul_of_nonneg_left hgX (by positivity)) hle1),
    ⟨hfsm.Dz, hDzmem⟩, hDzb,
    ⟨hfsm.Dth, hDthmem⟩, hDthb⟩

end

end Work.FTS.StrongEps.H5.Atoms
