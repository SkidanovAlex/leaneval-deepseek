import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.FTS.OpenPkg.hkMem_prod_open_M
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row24
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Open.smoothOpen_FK_radial
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.FTS.H2.QangAux
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.FTS.Nonlinear.Open.Row24Aux.angMulScaledOpen
import Submission.Work.FTS.Nonlinear.Open.Row24Aux.RnLeRadial
import Submission.Work.FTS.Nonlinear.Open.Row24Aux.qgSliceAe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1600000

/-- **Row 24 of the §8 table** in the open-quadrant (primed) vocabulary: the `ℋ⁴`-honesty and the
norm bound of the piece

  `N₅^{gg} = -sin²θ · FK(g) · g`,   `FK(g)(z) = ∫_θ K(θ)·g(z,θ) dθ`,

i.e. the slot of the nonlinearity in which the coefficient is the *angular moment* `FK g` of the
test function itself.  The two conjuncts are proved together below:

* **`ℋ⁴`-honesty.**  `N₅^{gg}` is the product of the radial function `FK g` with
  `h := c·(-sin²θ)·g`, where `c := Ci/B`: the angular factor `-sin²θ` (scaled so that its
  ℋ⁴-norm-loss `Ci` of `N4Norm'.angmul` is exactly met) is harmless in `ℋ⁴`
  (`Row24Aux.angMulScaledOpen`), the radial factor is in `ℋ⁴` with `Xn (FK g) ≤ Ci·Xn g`
  (`N4Norm'.fkH`), and the product `r·h` is honest by the radial measure-theoretic route
  `OpenPkg.hkMem_prod_open_M`: the radial slots `b ≤ 3` of `FK g` are bounded by the angular
  moments (`RNP.M_bound`, via `DzdIter_Qang_ae` and Cauchy–Schwarz against `Ktheta`), and the
  top slot `b = 4` is absorbed by the radial Hardy bound `(h z θ)² ≤ Qg h θ` for a.e. `θ`
  (`Row24Aux.qgSliceAe`).  Finally `HkMem` is transported across the constant `c⁻¹`.
* **The norm bound.**  `HkSq α 4 (FK g · h) ≤ C·(M + ∫_z (D_z⁴ FK g)²w²)·HkSq α 4 h` is the
  uniform radial product estimate `RNP.hkSq_prod_le_rad_int` fed with the pointwise majorant
  `RNP24.hkIntegrand_prod_le_rad_uniform` (a universal constant `C₂`), with the radial data
  `RNP24.dzIter_mixed_mul_rad` (the Leibniz expansions) and the integrability/bound of the top
  radial slot `Row24Aux.RnLeRadial` (`∫_z (D_z⁴ FK g)²w² ≤ 9(π/2)·HkSq α 4 g`).  Both `M` and
  that integral are `≤ 9(π/2)·|g|²`, so `HkSq (FK g · h) ≤ C₂·9π·Ci⁴·|g|⁴`, whence
  `Xn (FK g · h) ≤ √(C₂·9π·Ci⁴)·|g|²`; dividing by `c = Ci/B` gives the stated constant
  `K = (B/Ci)·√(C₂·9π·Ci⁴) + 1` (the `+1` only to make it manifestly positive).

The hypotheses `StarPkgo α Cs Φs`, `EllPkgGo α Ce g Φg` and `N4Extra' IP α₂ Ct` are not needed:
the row is a pure norm estimate, and `GalClass` enters only through `SmoothQuad`/`HkMem α 6`/
`DecayAll`/`L12 g 0 = 0`. -/
theorem Row24 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5gg g) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gg g) ≤ K * (Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨hCi, hα₂pos⟩ := hN.pos
  obtain ⟨B, hBpos, hSmoothInt, hbound, hdth⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  obtain ⟨C₂, hC₂pos, h6⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.hkIntegrand_prod_le_rad_uniform
  refine ⟨(B / Ci) * Real.sqrt (C₂ * (9 * Real.pi * Ci ^ 4)) + 1, by positivity, ?_⟩
  intro α g Φs Φg hα hα1 hαα₂ hgal hstar hell
  -- ## the regularity of the datum
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hsm : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 g := hgal.reg.2.1
  have hmem5 : Work.Spaces.HkMem α 5 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem6
  have hmem4 : Work.Spaces.HkMem α 4 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem5
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hO : Work.FTS.EllipticEst.SmoothOpen g := Work.FTS.H2.SmoothQuad.toSmoothOpen hsm
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hHk : Work.Spaces.HkSq α 4 g = (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (Real.sq_sqrt (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g)).symm
  have hdec3 : ∀ i : ℕ, i ≤ 3 → ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z => Work.Spaces.DzIter i g z θ) Filter.atTop (nhds 0) := by
    intro i hi θ hθ
    have h := hgal.decay.2 0 i (by omega) θ hθ
    simpa only [Work.Spaces.mixed_zero_right] using h
  have hdec0 : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0) := by
    intro θ hθ
    have h := hdec3 0 (by norm_num) θ hθ
    simpa only [Work.Spaces.DzIter_zero] using h
  -- ## the scaled angular profile `c·(-sin²θ)` and the datum `h = c·(-sin²θ)·g`
  set c : ℝ := Ci / B with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcB : c * B = Ci := by rw [hc]; field_simp
  obtain ⟨hmem_h, hXn_h⟩ :=
    Work.FTS.Nonlinear.Open.Row24Aux.angMulScaledOpen hN hBpos hcB hSmoothInt hbound hdth
      hO hmem4 hIoc
  set h : ℝ → ℝ → ℝ := fun z θ => c * (-((Real.sin θ)^2)) * g z θ with hh
  have hsh : Work.FTS.LocData.SmoothQuad h := by
    rw [hh]
    exact Work.FTS.LocData.smoothQuad_mul
      (Work.FTS.LocData.smoothQuad_const_mul c (hSmoothInt.1.of_le le_top)) hsm
  have hhsm : Work.FTS.EllipticEst.SmoothOpen h := Work.FTS.H2.SmoothQuad.toSmoothOpen hsh
  have hdech : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => h z θ) Filter.atTop (nhds 0) := by
    intro θ hθ
    have h1 : (fun z => h z θ) = fun z => (c * (-((Real.sin θ)^2))) * g z θ := by
      funext z; rw [hh]
    rw [h1]
    simpa only [mul_zero] using (hdec0 θ hθ).const_mul (c * (-((Real.sin θ)^2)))
  -- ## the radial factor `FK g`: `C⁴`, its Leibniz expansions, its jet bound, its `L²(w²)` bound
  have hR4 : ContDiffOn ℝ 4 (fun z => Work.Construction.FK g z) (Set.Ioi (0:ℝ)) :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.fk_contDiffOn_four hα hα1 hsm hmem6
  obtain ⟨hDz, hMx⟩ := Work.FTS.Nonlinear.Pieces.RNP.RNP24.dzIter_mixed_mul_rad hR4 hsh
  have hMbound : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0:ℝ),
      (Work.Elliptic.DzdIter b (Work.Construction.FK g) z) ^ 2
        ≤ (9 * (Real.pi / 2)) * Work.Spaces.HkSq α 4 g :=
    Work.FTS.Nonlinear.Pieces.RNP.M_bound hsm hmem4 hdec3
  obtain ⟨hRnInt, hRnLe⟩ := Work.FTS.Nonlinear.Open.Row24Aux.RnLeRadial hsm hmem4 hα1 hα
  have hQg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0:ℝ), (h z θ) ^ 2 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ :=
    Work.FTS.Nonlinear.Open.Row24Aux.qgSliceAe hsh hmem_h hdech
  -- ## the pointwise majorant of `HkIntegrand (FK g · h)`
  set M : ℝ := (9 * (Real.pi / 2)) * Work.Spaces.HkSq α 4 g with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (by positivity) (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g)
  have hbd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0:ℝ),
        Work.Spaces.HkIntegrand α 4 (fun z θ => Work.Construction.FK g z * h z θ) z θ
          ≤ C₂ * (M * Work.Spaces.HkIntegrand α 4 h z θ
              + (Work.Elliptic.DzdIter 4 (fun z => Work.Construction.FK g z) z) ^ 2
                * (Work.Spaces.w z) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg h θ) := by
    filter_upwards [hQg, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hq hθI
    intro z hz
    exact h6 hM0 hMbound hDz hMx hθI hz (fun z' hz' => hq z' hz')
  -- ## the `ℋ⁴`-norm of the product, through the uniform radial product estimate
  have hmain := Work.FTS.Nonlinear.Pieces.RNP.hkSq_prod_le_rad_int (C := C₂) hC₂pos hM0
    hsh hmem_h hbd hRnInt
  have hHkh : Work.Spaces.HkSq α 4 h = (Work.FTS.Nonlin.Xn α h) ^ 2 :=
    (Real.sq_sqrt (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 h)).symm
  have hMX : M = (9 * (Real.pi / 2)) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by rw [hM, hHk]
  have hRn2 : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 (fun z => Work.Construction.FK g z) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      ≤ (9 * (Real.pi / 2)) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    rw [← hHk]; exact hRnLe
  have hsum : M + (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 (fun z => Work.Construction.FK g z) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ 9 * Real.pi * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    rw [hMX]
    linarith [hRn2]
  have hXh2 : (Work.FTS.Nonlin.Xn α h) ^ 2
      ≤ (Ci * Ci * Work.FTS.Nonlin.Xn α g) ^ 2 := by
    have h0 : 0 ≤ Ci * Ci * Work.FTS.Nonlin.Xn α g := by
      have := hN.pos.1; positivity
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 h) hXn_h 2
  have hstep : Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.FK g z * h z θ)
      ≤ (C₂ * (9 * Real.pi * Ci ^ 4)) * (Work.FTS.Nonlin.Xn α g) ^ 4 := by
    refine hmain.trans ?_
    have hA : C₂ * (M + ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 4 (fun z => Work.Construction.FK g z) z) ^ 2
            * (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 4 h
        ≤ C₂ * (9 * Real.pi * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * (Ci * Ci * Work.FTS.Nonlin.Xn α g) ^ 2 := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hsum hC₂pos.le) ?_ ?_ ?_
      · rw [hHkh]
        exact hXh2
      · exact Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 h
      · positivity
    refine hA.trans (le_of_eq ?_)
    ring
  have hXn_final : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK g z * h z θ)
      ≤ Real.sqrt (C₂ * (9 * Real.pi * Ci ^ 4)) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK g z * h z θ)
        = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.FK g z * h z θ)) := rfl
      _ ≤ Real.sqrt ((C₂ * (9 * Real.pi * Ci ^ 4))
            * (Work.FTS.Nonlin.Xn α g) ^ 4) := Real.sqrt_le_sqrt hstep
      _ = Real.sqrt (C₂ * (9 * Real.pi * Ci ^ 4)) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
        rw [Real.sqrt_mul (by positivity),
          show (Work.FTS.Nonlin.Xn α g) ^ 4 = ((Work.FTS.Nonlin.Xn α g) ^ 2) ^ 2 from by ring,
          Real.sqrt_sq (by positivity)]
  -- ## the `ℋ⁴`-honesty of the product, through the radial measure-theoretic route
  have hfk := hN.fkH α hIoc g (Work.FTS.OpenPkg.HQo_of_RegQ hreg4) hgal.l12
  have hrmem : Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) := hfk.1
  have hrsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK g z) :=
    Work.FTS.Nonlinear.Open.smoothOpen_FK_radial hα hα1 hsm hmem4 hgal.l12
      hell.smooth hell.V.1.1
  have hK3 : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.Nonlinear.RadialProd.smE θ
        * Work.FTS.Nonlinear.RadialProd.Qg h θ) Work.Spaces.Iθ :=
    (Work.FTS.OpenPkg.integrable_smE_Qg_le_open α h hhsm hmem_h).1
  have hmem_prod : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.FK g z * h z θ) :=
    Work.FTS.OpenPkg.hkMem_prod_open_M α (fun z => Work.Construction.FK g z) h M
      hrsm hhsm hrmem hmem_h hMbound hK3 hQg
  -- ## `N₅^{gg} = c⁻¹·(FK g · h)`, and the two conjuncts
  have hN5 : Work.FTS.Nonlin.N5gg g
      = fun z θ => c⁻¹ * (Work.Construction.FK g z * h z θ) := by
    funext z θ
    rw [hh, Work.FTS.Nonlin.N5gg]
    field_simp
  constructor
  · rw [hN5]
    exact Work.FTS.LocData.HkMem_const_mul α 4 c⁻¹ hmem_prod
  · rw [hN5, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
      abs_of_pos (by positivity : (0 : ℝ) < c⁻¹)]
    calc c⁻¹ * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK g z * h z θ)
        ≤ c⁻¹ * (Real.sqrt (C₂ * (9 * Real.pi * Ci ^ 4))
            * (Work.FTS.Nonlin.Xn α g) ^ 2) :=
          mul_le_mul_of_nonneg_left hXn_final (by positivity)
      _ = (B / Ci) * Real.sqrt (C₂ * (9 * Real.pi * Ci ^ 4))
            * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
          rw [hc]; field_simp
      _ ≤ ((B / Ci) * Real.sqrt (C₂ * (9 * Real.pi * Ci ^ 4)) + 1)
            * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
          have h1 : 0 ≤ (B / Ci) * Real.sqrt (C₂ * (9 * Real.pi * Ci ^ 4)) := by positivity
          have h2 : 0 ≤ (Work.FTS.Nonlin.Xn α g) ^ 2 := by positivity
          nlinarith [h1, h2]

end Work.FTS.Nonlinear.Open
