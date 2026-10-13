/-
# `E4R3/N4C/rows/rowsN5a` — row 24 of the honest §8 table

`Work.FTS.StrongEps.E4R3.N4C.rows.rowsN5a` proves the `N₅^{gg}` row of the honest (class-`C`)
§8 table:

  `Xn α (N₅^{gg} g) ≤ K · (Xn α g)²`,   `N₅^{gg} = -sin²θ·FK(g)·g`,

in the honest context `CtxT` (profile data `ClassC α g ∧ CoerAdmO α g`, open-quadrant elliptic
packages) and with a constant `K` independent of `α ∈ (0, 1]`.

## Route

`N₅^{gg} = a(θ)·(FK g · g)` with the *angular* profile `a θ = -(sin θ)²` and the *radial*
product `FK g · g`.  Both steps are lossless in `α`:

* the angular step is `OpenPkg.angmul_field` at the profile `a` (`angSq_data` supplies the two
  hypotheses `|a θ| ≤ Bs`, `|D_θ^i a| ≤ Bs·sin 2θ`);
* the radial product is bounded by `HkSq_prod_le_open_M` below (the `Rr`-version
  `OpenPkg.HkSq_prod_le_open` needs the radial Hardy inequality for `FK g`, i.e. the decay
  `D_z^b (FK g) → 0` at `z = ∞`, which the honest class does **not** provide; the *constant*
  majorant `M = (∫_θ K_θ²)·HkSq α 4 g` of the radial slots `b ≤ 3`, coming from the angular
  moment bound `Qang_sq_le_const_open`, is what replaces it).

The identification `D_z^b (FK g) = Qang g b` (`b ≤ 3`, `z > 0`) of `dzdIter_FK_eq_qang_open` —
the open-quadrant port of `RNP24.dzdIter_FK_eq_qang` — is what makes the moment bound apply to
the radial factor, and `Rr (FK g) ≤ (Xn α (FK g))² ≤ (Cf·Xn α g)²` (via `Rr_le_HkSq` and the
`fkH`-clause) closes the `D_z^4`-slot.

The remaining ingredients (`so_FKw` for the smoothness of the angular moment, `fkH_field` for
its `ℋ⁴`-honesty, `sda_HkSqSwap_open`/`g_sq_le_Qg_open` for the a.e. radial Hardy bound of the
`g`-side) are already delivered in the honest class.  Nothing here uses the interfaces `hN`,
`hE`: the row is a statement about the concrete piece.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.Hon
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.HonDecay
import Submission.Work.FTS.OpenPkg.hkMem_prod_open_M
import Submission.Work.FTS.OpenPkg.angmul_field
import Submission.Work.FTS.OpenPkg.fkH_field
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.StrongEps.E4R3.Qang_sq_le_const_open
import Submission.Work.FTS.StrongPersist.QangAe6
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.NMemAux
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.rows

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.FTS.Galerkin (Fn)

/-! ## The angular moment `FK g` is the `D_z`-tower of `Qang g 0` -/

/-- **`D_z^b (FK g) = Qang g b` on `(0,∞)`, for `b ≤ 3`**, in the open-quadrant class
`SmoothOpen g` + `HkMem α 4 g` (no decay, no interior smoothness through `z = 0`).

`FK g = Qang g 0` (the two angular weights agree), and the angular moments satisfy the divided
derivative `(Qang g j)' z = Qang g (j+1) z / z` for `j ≤ 2` pointwise on `(0,∞)`
(`QangOpen.hasDerivAt_Qang_open`), so `DzdIter_eq_of_hasDerivAt'` gives all the iterates up to
`3`. -/
theorem dzdIter_FK_eq_qang_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter b (fun z => Work.Construction.FK g z) z
        = Work.Elliptic.Qang g b z := by
  have hFK : ∀ z : ℝ, Work.Construction.FK g z = Work.Elliptic.Qang g 0 z := by
    intro z
    rw [Work.Construction.FK, Work.Elliptic.Qang]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [Work.Elliptic.Ktheta_eq_K]
    simp only [Work.Spaces.DzIter_zero]
    ring
  have hpt : ∀ i ≤ 3, ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z
        = Work.Elliptic.Qang g i z :=
    fun i hi z hz => Work.FTS.StrongPersist.DzdIter_eq_of_hasDerivAt' 2 (fun _ => rfl)
      (fun j hj z hz => Work.FTS.OpenPkg.QangOpen.hasDerivAt_Qang_open α g hO hmem hj hz
        (Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α g hO hmem (by omega)))
      i (by omega) z hz
  intro b hb z hz
  rw [Work.FTS.StrongPersist.DzdIter_congr_Ioi (fun y _ => hFK y) b z hz, hpt b hb z hz]

/-! ## The integrated radial-product bound with a constant radial majorant -/

/-- **The `ℋ⁴`-bound for the radial product `r·g` with a constant majorant `M` of the radial
slots `b ≤ 3`.**

This is `Work.FTS.OpenPkg.HkSq_prod_le_open` with the radial quantity `Rr r` of the first term
(the slots `b ≤ 3`) replaced by the caller's constant `M`; the `D_z^4`-slot keeps the sharp
`Rr r`.  The proof is the corresponding one-quantity swap of the slice bound
(`slice_le_open_M`, integrated). -/
theorem HkSq_prod_le_open_M (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (M : ℝ)
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z))
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hrm : Work.Spaces.HkMem α 4 (fun z _ => r z))
    (hgm : Work.Spaces.HkMem α 4 g)
    (hM : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter b r z) ^ 2 ≤ M)
    (hK3 : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.Nonlinear.RadialProd.smE θ
        * Work.FTS.Nonlinear.RadialProd.Qg g θ) Work.Spaces.Iθ)
    (hK3le : (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
        * Work.FTS.Nonlinear.RadialProd.Qg g θ) ≤ Work.Spaces.HkSq α 4 g)
    (hQg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ), (g z θ) ^ 2 ≤ Work.FTS.Nonlinear.RadialProd.Qg g θ) :
    Work.Spaces.HkSq α 4 (fun z θ => r z * g z θ)
      ≤ 2 * Work.FTS.OpenPkg.prodK
          * (M + Work.FTS.Nonlinear.RadialProd.Rr r) * Work.Spaces.HkSq α 4 g := by
  have hPint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz :=
    Work.FTS.OpenPkg.integrable_DzdIter_sq_open α r hr hrm 4 (by norm_num)
  have hPle : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ Work.FTS.Nonlinear.RadialProd.Rr r := by
    rw [Work.FTS.Nonlinear.RadialProd.Rr]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.FTS.Nonlinear.RadialProd.integrable_Rint α r hrm)
      (Filter.Eventually.of_forall fun z => ?_)
    exact Finset.single_le_sum
      (f := fun i => (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_range.mpr (by norm_num))
  have hRnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.Rr r :=
    Work.FTS.Nonlinear.RadialProd.Rr_nonneg r
  have hHnn : 0 ≤ Work.Spaces.HkSq α 4 g :=
    Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g
  have hK3nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
      * Work.FTS.Nonlinear.RadialProd.Qg g θ :=
    MeasureTheory.integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem
      measurableSet_Icc (fun θ hθ => mul_nonneg
        (Work.FTS.Nonlinear.RadialProd.smE_nonneg hθ)
        (Work.FTS.Nonlinear.RadialProd.Qg_nonneg g θ)))
  set G : ℝ → ℝ := fun z => Work.FTS.OpenPkg.prodK * M * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 g z θ)
      + Work.FTS.OpenPkg.prodK
        * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
            * Work.FTS.Nonlinear.RadialProd.Qg g θ) with hG
  have hGint : MeasureTheory.Integrable G (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hG]
    exact (hgm.2.const_mul _).add ((hPint.const_mul _).mul_const _)
  have hmono : Work.Spaces.HkSq α 4 (fun z θ => r z * g z θ)
      ≤ ∫ z in Work.Spaces.Iz, G z := by
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 4 _ z θ) hGint ?_
    have hmeas : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
        = MeasureTheory.volume.restrict Work.Spaces.Iz :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))
    rw [← hmeas]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [hG]
    exact Work.FTS.OpenPkg.slice_le_open_M α r g M hr hg hM hK3 hQg hgm hz
  have hval : (∫ z in Work.Spaces.Iz, G z)
      = Work.FTS.OpenPkg.prodK * M * Work.Spaces.HkSq α 4 g
        + Work.FTS.OpenPkg.prodK * (∫ z in Work.Spaces.Iz,
              (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg g θ) := by
    rw [hG]
    simp only []
    rw [MeasureTheory.integral_add (hgm.2.const_mul _) ((hPint.const_mul _).mul_const _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const,
      MeasureTheory.integral_const_mul]
    rfl
  rw [hval] at hmono
  have hPK : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
          * Work.FTS.Nonlinear.RadialProd.Qg g θ)
      ≤ Work.FTS.Nonlinear.RadialProd.Rr r * Work.Spaces.HkSq α 4 g :=
    mul_le_mul hPle hK3le hK3nn hRnn
  have hPK2 : Work.FTS.OpenPkg.prodK * ((∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.RadialProd.smE θ
          * Work.FTS.Nonlinear.RadialProd.Qg g θ))
      ≤ Work.FTS.OpenPkg.prodK * (Work.FTS.Nonlinear.RadialProd.Rr r
          * Work.Spaces.HkSq α 4 g) :=
    mul_le_mul_of_nonneg_left hPK (le_of_lt Work.FTS.OpenPkg.prodK_pos)
  have hM0 : 0 ≤ M :=
    le_trans (sq_nonneg (Work.Elliptic.DzdIter 0 r 1))
      (hM 0 (by norm_num) 1 (Set.mem_Ioi.mpr (by norm_num)))
  have hPKnn : 0 ≤ Work.FTS.OpenPkg.prodK * M * Work.Spaces.HkSq α 4 g :=
    mul_nonneg (mul_nonneg (le_of_lt Work.FTS.OpenPkg.prodK_pos) hM0) hHnn
  have hR2nn : 0 ≤ Work.FTS.OpenPkg.prodK * (Work.FTS.Nonlinear.RadialProd.Rr r
      * Work.Spaces.HkSq α 4 g) :=
    mul_nonneg (le_of_lt Work.FTS.OpenPkg.prodK_pos) (mul_nonneg hRnn hHnn)
  nlinarith [hmono, hPK2, hPKnn, hR2nn, hM0, hRnn, hHnn,
    le_of_lt Work.FTS.OpenPkg.prodK_pos]

/-! ## Row 24 of the honest §8 table -/

theorem rowsN5a (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gg g) ≤ K * Work.FTS.Nonlin.Xn α g ^ 2 := by
  obtain ⟨Cf, hCfpos, hfkH⟩ := Work.FTS.OpenPkg.fkH_field
  obtain ⟨Cang, hCangpos, hang⟩ := Work.FTS.OpenPkg.angmul_field
  obtain ⟨Bs, hBspos, haSO, haB, haIt⟩ := Work.FTS.StrongEps.EpsZero.ClassCHk.angSq_data
  set K1 : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hK1def
  have hK1nn : 0 ≤ K1 := by
    rw [hK1def]
    exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  set K : ℝ := Cang * Bs * Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2)) + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have : 0 ≤ Cang * Bs * Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2)) := by
      refine mul_nonneg (mul_nonneg hCangpos.le hBspos.le) (Real.sqrt_nonneg _)
    linarith
  refine ⟨K, hKpos, ?_⟩
  intro α g Φs Φg hctx
  have hα : 0 < α := hctx.hα
  have hα1 : α ≤ 1 := hctx.hα1
  have hgSO : Work.FTS.EllipticEst.SmoothOpen g := hctx.hSmoothOpen
  have hmem4 : Work.Spaces.HkMem α 4 g := hctx.hkMem4
  have h0 : Work.Construction.L12 g 0 = 0 := hctx.hL12
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hXsq : Work.Spaces.HkSq α 4 g = (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    (Real.sq_sqrt (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g)).symm
  -- ## the smoothness and the `ℋ⁴`-honesty of the angular moment `FK g`
  have hFKsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.FK g z) :=
    Work.FTS.StrongEps.EpsZero.ClassCHk.so_FKw hctx.hg
  obtain ⟨hFKmem, hFKbd⟩ := hfkH α hα hα1 g ⟨hgSO, hmem4⟩ h0
  -- ## the pointwise bound on the radial slots `b ≤ 3`
  have hpt : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK g z) z) ^ 2
        ≤ K1 * Work.Spaces.HkSq α 4 g := by
    intro b hb z hz
    have hq := Work.FTS.StrongEps.E4R3.Qang_sq_le_const_open (α := α) (g := g)
      hα hα1 hgSO hmem4 (i := b) hb (z := z) hz
    rw [dzdIter_FK_eq_qang_open hgSO hmem4 b hb z hz, hK1def]
    exact hq
  -- ## the a.e. radial Hardy bound for the slices of `g`
  have hQg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ),
        (g z θ) ^ 2 ≤ Work.FTS.Nonlinear.RadialProd.Qg g θ := by
    obtain ⟨-, -, hslice⟩ :=
      Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α g hgSO hmem4
    filter_upwards [hslice, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hint hθ
    intro z hz
    have hθI : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hdec : Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0) := by
      have hd := hctx.hdecay.1 0 0 (by norm_num) θ hθI
      simpa using hd
    have hintpsi : MeasureTheory.IntegrableOn
        (fun s => Work.FTS.Nonlinear.RadialProd.psiZ g s θ) Work.Spaces.Iz := by
      refine MeasureTheory.Integrable.mono' hint ?_ ?_
      · refine Work.H2.T1Q.aesm_Iz_of_continuousOn ?_
        exact (Work.FTS.OpenPkg.continuousOn_psiZ_open g hgSO).comp
          ((continuous_id.prodMk continuous_const).continuousOn) (fun s hs => ⟨hs, hθ⟩)
      · filter_upwards with s
        rw [Real.norm_of_nonneg (Work.FTS.Nonlinear.RadialProd.psiZ_nonneg g s θ)]
        exact Work.FTS.Nonlinear.RadialProd.psiZ_le_HkIntegrand_of_Ioo α g hθ s
    exact Work.FTS.OpenPkg.g_sq_le_Qg_open g hgSO hθ hdec hintpsi hz
  have hK3 := Work.FTS.OpenPkg.integrable_smE_Qg_le_open α g hgSO hmem4
  -- ## the radial product `FK g · g`
  have hmemF : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.FK g z * g z θ) :=
    Work.FTS.OpenPkg.hkMem_prod_open_M α (fun z => Work.Construction.FK g z) g
      (K1 * Work.Spaces.HkSq α 4 g) hFKsm hgSO hFKmem hmem4 hpt hK3.1 hQg
  have hSQ := HkSq_prod_le_open_M α (fun z => Work.Construction.FK g z) g
    (K1 * Work.Spaces.HkSq α 4 g) hFKsm hgSO hFKmem hmem4 hpt hK3.1 hK3.2 hQg
  have hRr : Work.FTS.Nonlinear.RadialProd.Rr (fun z => Work.Construction.FK g z)
      ≤ Cf ^ 2 * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    have h2 : Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.FK g z)
        = (Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)) ^ 2 :=
      (Real.sq_sqrt (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4
        (fun z θ => Work.Construction.FK g z))).symm
    calc Work.FTS.Nonlinear.RadialProd.Rr (fun z => Work.Construction.FK g z)
        ≤ Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.FK g z) :=
          Work.FTS.Nonlinear.RadialProd.Rr_le_HkSq α (fun z => Work.Construction.FK g z)
      _ = (Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)) ^ 2 := h2
      _ ≤ (Cf * Work.FTS.Nonlin.Xn α g) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 _) hFKbd 2
      _ = Cf ^ 2 * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
  -- ## the `ℋ⁴`-bound of the radial product
  have hXprod : Work.FTS.Nonlin.Xn α
        (fun z θ => Work.Construction.FK g z * g z θ)
      ≤ Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2))
          * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
    have hMx : K1 * Work.Spaces.HkSq α 4 g
          + Work.FTS.Nonlinear.RadialProd.Rr (fun z => Work.Construction.FK g z)
        ≤ (K1 + Cf ^ 2) * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
      rw [hXsq]
      nlinarith [hRr]
    have hCnn : 0 ≤ 2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Work.FTS.OpenPkg.prodK_pos))
        (by positivity)
    have hkey : Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.FK g z * g z θ)
        ≤ (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2))
            * (Work.FTS.Nonlin.Xn α g) ^ 4 := by
      refine hSQ.trans ?_
      have hstep : 2 * Work.FTS.OpenPkg.prodK
            * (K1 * Work.Spaces.HkSq α 4 g
              + Work.FTS.Nonlinear.RadialProd.Rr (fun z => Work.Construction.FK g z))
            * Work.Spaces.HkSq α 4 g
          ≤ 2 * Work.FTS.OpenPkg.prodK * ((K1 + Cf ^ 2) * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * Work.Spaces.HkSq α 4 g := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMx ?_) ?_
        · exact mul_nonneg (by norm_num) (le_of_lt Work.FTS.OpenPkg.prodK_pos)
        · exact Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g
      calc 2 * Work.FTS.OpenPkg.prodK
            * (K1 * Work.Spaces.HkSq α 4 g
              + Work.FTS.Nonlinear.RadialProd.Rr (fun z => Work.Construction.FK g z))
            * Work.Spaces.HkSq α 4 g
          ≤ 2 * Work.FTS.OpenPkg.prodK * ((K1 + Cf ^ 2) * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * Work.Spaces.HkSq α 4 g := hstep
        _ = 2 * Work.FTS.OpenPkg.prodK * ((K1 + Cf ^ 2) * (Work.FTS.Nonlin.Xn α g) ^ 2)
            * (Work.FTS.Nonlin.Xn α g) ^ 2 := by rw [hXsq]
        _ = (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2))
            * (Work.FTS.Nonlin.Xn α g) ^ 4 := by ring
    calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK g z * g z θ)
        = Real.sqrt (Work.Spaces.HkSq α 4
            (fun z θ => Work.Construction.FK g z * g z θ)) := rfl
      _ ≤ Real.sqrt ((2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2))
            * (Work.FTS.Nonlin.Xn α g) ^ 4) := Real.sqrt_le_sqrt hkey
      _ = Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2))
            * (Work.FTS.Nonlin.Xn α g) ^ 2 := by
          rw [Real.sqrt_mul hCnn,
            show (Work.FTS.Nonlin.Xn α g) ^ 4
                = ((Work.FTS.Nonlin.Xn α g) ^ 2) ^ 2 from by ring,
            Real.sqrt_sq (by positivity)]
  -- ## the angular factor `-sin²θ`
  have hN5 : Work.FTS.Nonlin.N5gg g
      = fun z θ => (-(Real.sin θ) ^ 2)
          * (Work.Construction.FK g z * g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N5gg]
    ring
  obtain ⟨-, hXnang⟩ := hang α hα hα1 (fun θ => -((Real.sin θ) ^ 2))
    (fun z θ => Work.Construction.FK g z * g z θ) Bs haSO haB haIt
    (Work.FTS.OpenPkg.smoothOpen_sepMul hFKsm hgSO) hmemF
  rw [hN5]
  refine hXnang.trans ?_
  have hstep : Cang * Bs * Work.FTS.Nonlin.Xn α
        (fun z θ => Work.Construction.FK g z * g z θ)
      ≤ Cang * Bs * (Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2))
          * (Work.FTS.Nonlin.Xn α g) ^ 2) :=
    mul_le_mul_of_nonneg_left hXprod (mul_nonneg hCangpos.le hBspos.le)
  refine hstep.trans ?_
  rw [hKdef]
  have hfac : Cang * Bs * (Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2))
        * (Work.FTS.Nonlin.Xn α g) ^ 2)
      = (Cang * Bs * Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2)))
        * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
  rw [hfac]
  have hSnn : 0 ≤ Cang * Bs * Real.sqrt (2 * Work.FTS.OpenPkg.prodK * (K1 + Cf ^ 2)) := by
    refine mul_nonneg (mul_nonneg hCangpos.le hBspos.le) (Real.sqrt_nonneg _)
  nlinarith [sq_nonneg (Work.FTS.Nonlin.Xn α g), hSnn]

end Work.FTS.StrongEps.E4R3.N4C.rows
