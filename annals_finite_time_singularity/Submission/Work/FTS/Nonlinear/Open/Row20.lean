/-
# Row 20 of the §8 table in the open-quadrant (primed) vocabulary

`Work.FTS.Nonlinear.Open.Row20`: the `ℋ⁴`-honesty and the `IP`-bound of the piece

  `N₄^{gg} = -(1/2)·FK(g)·D_θ g`,      `FK(g)(z) = ∫_θ K(θ) g(z,θ) dθ`,

in the primed context `N4Norm'`/`N4Extra'` with the open-quadrant packages
`StarPkgo`/`EllPkgGo`.

## Route

Write `r z = -(1/2)·FK(g)(z)` and `h = D_θ g`, so that `N₄^{gg} = r·h` (`rfl`).

* **The `IP`-bound.**  The primed transport clause `N4Extra'.t1` has the *flat* shape
  `|IP α (f·D_θ g) g| ≤ Ct·α^{-1/2}·|f|_{ℋ⁴}·|g|_{ℋ⁴}²` with the honesty hypothesis
  `HQo α 4 f = SmoothOpen f ∧ HkMem α 4 f` on the coefficient.  So the whole bound rests on
  `SmoothOpen (fun z _ => FK g z)` — *not* provided by the interface (`fkH` gives only the
  `ℋ⁴`-membership) — which is the delivered
  `Work.FTS.Nonlinear.Open.smoothOpen_FK_radial`: `L₁₂(g)` is `C^∞` on `(0,∞)` (because
  `Vop(Φ̃_g) = Vop Φ_g - c₂ₘ(θ)·L₁₂(g)` is `C^∞` and `Vop Φ_g` is), and
  `FK(g) = -z·∂_z L₁₂(g)` (`OpenPkg.deriv_L12_eq`), a derivative of a `C^∞` radial function.
  With `fkH`: `|(1/2)FK g|_{ℋ⁴} ≤ (1/2)·Ci·X`, so `K = Ct·Ci/2 + 1` closes the row.

* **The `ℋ⁴`-honesty conjunct** is new relative to the un-primed row 20 (which proved only the
  `IP`-bound): `FK(g)·D_θ g` is a *radial* `ℋ⁴`-coefficient times `D_θ g`, and the primed
  `radialMul` clause asks for the full `SmoothOpen` of the coefficient plus the decay of all
  its iterates at `z = ∞` — neither of which is available here.  The route used instead is the
  *finite-order* one: `M_bound` bounds the radial jets `(D_z^b FK g)² ≤ (9π/2)·HkSq α 4 g`
  (`b ≤ 3`) directly by the angular moments (`Qang_sq_le_const` + Hardy in `z`), and the
  pointwise product majorant `RNP24.hkIntegrand_prod_le_rad_uniform` needs only those,
  together with the radial Hardy bound `(h z θ)² ≤ Qg h θ` for a.e. `θ`
  (`sda_HkSqSwap_open` + `g_sq_le_Qg_open`).  The measure-theoretic assembly is the delivered
  `Work.FTS.OpenPkg.hkMem_prod_open_M`, the `M`-version of `OpenPkg.hkMem_prod_open`.

All constants are absolute (independent of `α`, of the profiles and of the truncation) apart
from the two interface constants `Ci`, `Ct`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row20
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row24
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.OpenPkg.C4Factors
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dth
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.Nonlinear.Open.smoothOpen_FK_radial
import Submission.Work.FTS.OpenPkg.hkMem_prod_open_M

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

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem Row20 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N4gg α g) ∧
      |IP α (Work.FTS.Nonlin.N4gg α g) g| ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
  have hCt0 : 0 < Ct := hE.pos.1
  have hCi0 : 0 < Ci := hN.pos.1
  refine ⟨Ct * Ci / 2 + 1, by positivity, ?_⟩
  intro α g Φs Φg hα hα1 hαα₂ hgal hs hell
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hreg : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  -- the regularity of `g`, at the orders the estimates need
  have hsm : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 g := hgal.reg.2.1
  have hmem5 : Work.Spaces.HkMem α 5 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem6
  have hmem4 : Work.Spaces.HkMem α 4 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem5
  have h0 : Work.Construction.L12 g 0 = 0 := hgal.l12
  -- `FK g` is `C^∞` on the open quadrant (this is what the primed `t1` clause consumes)
  have hFKsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK g z) :=
    smoothOpen_FK_radial hα hα1 hsm hmem4 h0 hell.smooth hell.V.1.1
  -- `FK g` is in `ℋ⁴`, with norm `≤ Ci·|g|`
  have hfk := hN.fkH α hIoc g (Work.FTS.OpenPkg.HQo_of_RegQ hreg) hgal.l12
  -- the radial coefficient `r = -(1/2)·FK g` and the angular factor `h = D_θ g`
  set r : ℝ → ℝ := fun z => -(1 / 2) * Work.Construction.FK g z with hrdef
  have hrsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) := by
    rw [hrdef]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-(1 / 2)) hFKsm
  have hrmem : Work.Spaces.HkMem α 4 (fun z _ => r z) := by
    rw [hrdef]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-(1 / 2)) hfk.1
  set h : Fn := Work.Spaces.Dth g with hdef
  have hreg5 : Work.FTS.Nonlin.RegQ α 5 g :=
    ⟨hsm, hmem5, fun a b hab => hgal.reg.2.2 a b (by omega)⟩
  have hregh : Work.FTS.Nonlin.RegQ α 4 h := Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα hreg5
  have hhmem : Work.Spaces.HkMem α 4 h := hregh.2.1
  have hhsm : Work.FTS.EllipticEst.SmoothOpen h := by
    rw [hdef]
    exact (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hsm).Dth
  -- the `z = ∞` decay of the slices of `g`
  have hdec3 : ∀ i : ℕ, i ≤ 3 → ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z => Work.Spaces.DzIter i g z θ) Filter.atTop (nhds 0) := by
    intro i hi θ hθ
    have hd := hgal.decay.2 0 i (by omega) θ hθ
    simpa only [Work.Spaces.mixed_zero_right] using hd
  have hdech : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => h z θ) Filter.atTop (nhds 0) := by
    intro θ hθ
    have hd := hgal.decay.2 1 0 (by norm_num) θ hθ
    rw [hdef]
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
      using hd
  -- the pointwise bound on the radial jets of `r` (`b ≤ 3`), from the angular moments
  have hMb : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter b r z) ^ 2 ≤ (9 * (π / 2)) * Work.Spaces.HkSq α 4 g := by
    intro b hb z hz
    have hM := Work.FTS.Nonlinear.Pieces.RNP.M_bound hsm hmem4 hdec3 b hb z hz
    have hid : Work.Elliptic.DzdIter b r z
        = -(1 / 2) * Work.Elliptic.DzdIter b (Work.Construction.FK g) z := by
      rw [hrdef]
      have h1 : Work.Elliptic.DzdIter b (fun z => -(1 / 2) * Work.Construction.FK g z) z
          = Work.Spaces.DzIter b (fun z θ => -(1 / 2) * Work.Construction.FK g z) z 0 :=
        (Work.Elliptic.DzIter_rad (fun z => -(1 / 2) * Work.Construction.FK g z) b z 0).symm
      have h2 : Work.Spaces.DzIter b (fun z θ => -(1 / 2) * Work.Construction.FK g z) z 0
          = -(1 / 2) * Work.Spaces.DzIter b (fun z θ => Work.Construction.FK g z) z 0 :=
        congrFun (congrFun (Work.FTS.Nonlinear.Pieces.RowsN0Aux.DzIter_const_mul b (-(1 / 2))
          (fun z θ => Work.Construction.FK g z)) z) 0
      have h3 : Work.Spaces.DzIter b (fun z θ => Work.Construction.FK g z) z 0
          = Work.Elliptic.DzdIter b (Work.Construction.FK g) z :=
        Work.Elliptic.DzIter_rad (Work.Construction.FK g) b z 0
      rw [h1, h2, h3]
    rw [hid]
    nlinarith [hM, sq_nonneg (Work.Elliptic.DzdIter b (Work.Construction.FK g) z),
      Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g]
  -- the radial Hardy bound for `h = D_θ g`, for a.e. angle
  have hQg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ), (h z θ) ^ 2 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ := by
    obtain ⟨-, -, hslice⟩ := Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α h hhsm hhmem
    filter_upwards [hslice, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hint hθ
    intro z hz
    have hintpsi : MeasureTheory.IntegrableOn
        (fun s => Work.FTS.Nonlinear.RadialProd.psiZ h s θ) Work.Spaces.Iz := by
      refine MeasureTheory.Integrable.mono' hint ?_ ?_
      · refine Work.H2.T1Q.aesm_Iz_of_continuousOn ?_
        exact (Work.FTS.OpenPkg.continuousOn_psiZ_open h hhsm).comp
          ((continuous_id.prodMk continuous_const).continuousOn)
          (fun s hs => ⟨hs, hθ⟩)
      · filter_upwards with s
        rw [Real.norm_of_nonneg (Work.FTS.Nonlinear.RadialProd.psiZ_nonneg h s θ)]
        exact Work.FTS.Nonlinear.RadialProd.psiZ_le_HkIntegrand_of_Ioo α h hθ s
    exact Work.FTS.OpenPkg.g_sq_le_Qg_open h hhsm hθ
      (hdech θ (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)) hintpsi hz
  have hK3 := (Work.FTS.OpenPkg.integrable_smE_Qg_le_open α h hhsm hhmem).1
  -- the `ℋ⁴`-honesty of the product `r·h = N₄^{gg}`
  have hmem_prod : Work.Spaces.HkMem α 4 (fun z θ => r z * h z θ) :=
    Work.FTS.OpenPkg.hkMem_prod_open_M α r h ((9 * (π / 2)) * Work.Spaces.HkSq α 4 g)
      hrsm hhsm hrmem hhmem hMb hK3 hQg
  have hN4eq : Work.FTS.Nonlin.N4gg α g = fun z θ => r z * h z θ := by
    funext z θ
    simp only [Work.FTS.Nonlin.N4gg, hrdef, hdef]
  -- the `IP`-bound, by the primed transport clause `t1`
  have hqo : Work.FTS.VocabO.HQo α 4 (fun z θ => r z) := ⟨hrsm, hrmem⟩
  have ht1 := hE.t1 α hIoc (fun z θ => r z) g hqo hreg
  have hXf : Work.FTS.Nonlin.Xn α (fun z θ => r z) ≤ (1 / 2) * (Ci * Work.FTS.Nonlin.Xn α g) := by
    rw [hrdef, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
      show |(-(1 / 2) : ℝ)| = (1 / 2) by norm_num]
    exact mul_le_mul_of_nonneg_left hfk.2 (by norm_num)
  refine ⟨hN4eq ▸ hmem_prod, ?_⟩
  rw [hN4eq]
  refine ht1.trans ?_
  have hstep : Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α (fun z θ => r z)
        * Work.FTS.Nonlin.Xn α g ^ 2
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * ((1 / 2) * (Ci * Work.FTS.Nonlin.Xn α g))
        * Work.FTS.Nonlin.Xn α g ^ 2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hXf (mul_nonneg hE.pos.1.le (Real.rpow_nonneg hα.le _)))
      (pow_nonneg hX0 2)
  refine hstep.trans ?_
  have harith : Ct * α ^ (-(1 / 2 : ℝ)) * ((1 / 2) * (Ci * Work.FTS.Nonlin.Xn α g))
        * Work.FTS.Nonlin.Xn α g ^ 2
      = (Ct * Ci / 2) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by ring
  rw [harith]
  exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (Real.rpow_nonneg hα.le _)
    (pow_nonneg hX0 3))

end Work.FTS.Nonlinear.Open
