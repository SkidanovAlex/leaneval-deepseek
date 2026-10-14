import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.one_le_mul_w

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.SecondDerivDz

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 800000

/-!
# The second angular derivative of `D_z^a (E g)` is bounded by `Xn₆`

This is the `D_z^a`-shifted version (`a ≤ 2`) of
`Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6`, i.e. §2 of
`Submission/Work/FTS_EllLimOK/ProducerH/NOTES_pkgBoxH.md`.

The point is the slice ODE of `Work.FTS.ClassCHon.lzero1_slice_DzIter`: for `Ψ = E g` with
`bslOp α Ψ = g` on the open quadrant, the slice `θ ↦ D_z^a Ψ(z,θ)` solves

  `S'' = tan θ · S' + (cos θ)⁻² S − 6 S − G`,   `G = D_z^a g + α² D_z^{a+2}Ψ + 5α D_z^{a+1}Ψ`,

so that `Work.FTS_EllLimOK.ProducerH.SecondDeriv.slice_second_deriv_le_six` (the sharp constant
`6`) applied to `S = D_z^a (E g)(z,·)` and `G = Lzero1 (D_z^a (E g)(z,·))` bounds `S''` by

  `6 · max (|D_z^a (E g)| , |½ sin 2θ · ∂_θ D_z^a (E g) + D_z^a (E g)| , |G|)`

on `(0,π/2)`, with the constant *uniform in `z`*.  All three quantities are `mixed` jets of order
`≤ 4` (`D_z^a`, `D_z^{a+1}`, `D_z^{a+2}` of `E g`, and `D_z^a` of the source `g`, the latter being
an order-`≤ 2` jet of a class-`C` element), hence bounded by `K · Xn₆ α g` on the box
`[a,b] × (0,π/2)` by `ProducerH.MixedJets.mixed_jets_le_Xn6` and
`FTS/StrongEps/SupPort/classC_mixed_sup_le`.
-/

theorem second_theta_deriv_DzIter_le_Xn6 {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK α 6 Ce g (E g))
    (a : ℕ) (ha : a ≤ 2) {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ ≤ b₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Ioo 0 (π / 2),
        |deriv (deriv (fun θ' => Work.Spaces.DzIter a (E g) z θ')) θ|
          ≤ K * Work.FTS.StrongGlobal.Xn6 α g := by
  have hα1 : α ≤ 1 := by linarith
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  -- the pointwise mixed-jet bound of `E g`
  obtain ⟨Km, hKm0, hKm⟩ :=
    Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6 hα hα4 hE
  have hCg0 : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  -- the constant (uniform in `g`, `z`, `θ`)
  let M : ℝ := max (max Km ((3 : ℝ) / 2 * Km))
    (10 / Real.sqrt (Work.Spaces.gam α - 1) + α ^ 2 * Km + 5 * α * Km)
  have hKmM : Km ≤ M := by
    show Km ≤ max (max Km ((3 : ℝ) / 2 * Km))
      (10 / Real.sqrt (Work.Spaces.gam α - 1) + α ^ 2 * Km + 5 * α * Km)
    exact le_trans (le_max_left Km ((3 : ℝ) / 2 * Km)) (le_max_left _ _)
  have hKmM2 : (3 : ℝ) / 2 * Km ≤ M := by
    show (3 : ℝ) / 2 * Km ≤ max (max Km ((3 : ℝ) / 2 * Km))
      (10 / Real.sqrt (Work.Spaces.gam α - 1) + α ^ 2 * Km + 5 * α * Km)
    exact le_trans (le_max_right Km ((3 : ℝ) / 2 * Km)) (le_max_left _ _)
  have hCM : 10 / Real.sqrt (Work.Spaces.gam α - 1) + α ^ 2 * Km + 5 * α * Km ≤ M := by
    show 10 / Real.sqrt (Work.Spaces.gam α - 1) + α ^ 2 * Km + 5 * α * Km
      ≤ max (max Km ((3 : ℝ) / 2 * Km))
        (10 / Real.sqrt (Work.Spaces.gam α - 1) + α ^ 2 * Km + 5 * α * Km)
    exact le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le hKm0 hKmM
  refine ⟨6 * M, mul_pos (by norm_num) hMpos, ?_⟩
  intro g hg z hz θ hθ
  obtain ⟨hz1, -⟩ := hz
  have hzpos : 0 < z := lt_of_lt_of_le ha₀ hz1
  have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  have hSm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).2.2.smooth
  -- ## the slice form of `Lzero1 (D_z^a Ψ(z,·))`
  have hLfun : Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.DzIter a (E g) z t)
      = fun θ => -deriv (deriv (fun θ'' => Work.Spaces.DzIter a (E g) z θ'')) θ
          + deriv (fun θ'' => Real.tan θ'' * Work.Spaces.DzIter a (E g) z θ'') θ
          - 6 * Work.Spaces.DzIter a (E g) z θ := by
    funext θ'
    simp only [Work.FTS.EllipticEst.Lzero1]
  -- ## smoothness of the slice
  have hSsm : ContDiffOn ℝ 2 (fun θ'' => Work.Spaces.DzIter a (E g) z θ'') (Set.Ioo 0 (π / 2)) :=
    ((hSm.mixed a 0).curry_θ hzpos).of_le (by norm_num)
  -- ## the slice ODE, with source `Lzero1 (D_z^a Ψ(z,·))`
  have heq : ∀ θ' ∈ Set.Ioo 0 (π / 2),
      deriv (deriv (fun θ'' => Work.Spaces.DzIter a (E g) z θ'')) θ'
        = Real.tan θ' * deriv (fun θ'' => Work.Spaces.DzIter a (E g) z θ'') θ'
          + ((Real.cos θ') ^ 2)⁻¹ * Work.Spaces.DzIter a (E g) z θ'
          - 6 * Work.Spaces.DzIter a (E g) z θ'
          - Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.DzIter a (E g) z t) θ' := by
    intro θ' hθ'
    have hcos : 0 < Real.cos θ' :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ'.1, Real.pi_pos], hθ'.2⟩
    have hSd : HasDerivAt (fun θ'' => Work.Spaces.DzIter a (E g) z θ'')
        (deriv (fun θ'' => Work.Spaces.DzIter a (E g) z θ'') θ') θ' :=
      ((hSsm.contDiffAt (isOpen_Ioo.mem_nhds hθ')).differentiableAt (by norm_num)).hasDerivAt
    have htan : HasDerivAt Real.tan (((Real.cos θ') ^ 2)⁻¹) θ' := by
      simpa only [one_div] using Real.hasDerivAt_tan (ne_of_gt hcos)
    have hprod : deriv (fun θ'' => Real.tan θ'' * Work.Spaces.DzIter a (E g) z θ'') θ'
        = ((Real.cos θ') ^ 2)⁻¹ * Work.Spaces.DzIter a (E g) z θ'
          + Real.tan θ' * deriv (fun θ'' => Work.Spaces.DzIter a (E g) z θ'') θ' :=
      (htan.mul hSd).deriv
    have hL := congrFun hLfun θ'
    rw [hL, hprod]
    ring
  -- ## the source identity of `lzero1_slice_DzIter`
  have hbsl : ∀ (z' : ℝ), 0 < z' → ∀ (θ' : ℝ), 0 < θ' → θ' < π / 2 →
      Work.Elliptic.bslOp α (E g) z' θ' = g z' θ' :=
    fun z' hz' θ' h0 h1 => (hE g hg).1.1.1 z' hz' θ' h0 h1
  have hLslice : ∀ θ' ∈ Set.Ioo 0 (π / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.DzIter a (E g) z t) θ'
        = Work.Spaces.DzIter a g z θ' + α ^ 2 * Work.Spaces.DzIter (a + 2) (E g) z θ'
          + 5 * α * Work.Spaces.DzIter (a + 1) (E g) z θ' :=
    fun θ' hθ' => Work.FTS.ClassCHon.lzero1_slice_DzIter (α := α) (F := g) (Ψ := E g)
      hSm hbsl a z hzpos θ' hθ'.1 hθ'.2
  -- ## the three bounds of the slice lemma
  have hSb : ∀ θ' ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.DzIter a (E g) z θ'| ≤ M * Work.FTS.StrongGlobal.Xn6 α g := by
    intro θ' hθ'
    exact le_trans (hKm g hg a 0 (by omega) z θ' ⟨hzpos, hθ'⟩)
      (mul_le_mul_of_nonneg_right hKmM hX0)
  have hfb : ∀ θ' ∈ Set.Ioo 0 (π / 2),
      |Real.sin (2 * θ') / 2 * deriv (fun θ'' => Work.Spaces.DzIter a (E g) z θ'') θ'
          + Work.Spaces.DzIter a (E g) z θ'| ≤ M * Work.FTS.StrongGlobal.Xn6 α g := by
    intro θ' hθ'
    have hkey := Work.FTS.TransportS.SupDzAux.sda_mixed_one_eq_sin_pth hSm a hzpos hθ'
    have hrepr : Real.sin (2 * θ') / 2 * deriv (fun θ'' => Work.Spaces.DzIter a (E g) z θ'') θ'
          + Work.Spaces.DzIter a (E g) z θ'
        = (1 / 2) * Work.Spaces.mixed a 1 (E g) z θ'
          + Work.Spaces.DzIter a (E g) z θ' := by
      have h2 : Work.Spaces.pth (Work.Spaces.DzIter a (E g)) z θ'
          = deriv (fun θ'' => Work.Spaces.DzIter a (E g) z θ'') θ' := rfl
      rw [← h2, hkey]
      ring
    rw [hrepr]
    have h1 : |Work.Spaces.mixed a 1 (E g) z θ'| ≤ Km * Work.FTS.StrongGlobal.Xn6 α g :=
      hKm g hg a 1 (by omega) z θ' ⟨hzpos, hθ'⟩
    have h0 : |Work.Spaces.DzIter a (E g) z θ'| ≤ Km * Work.FTS.StrongGlobal.Xn6 α g :=
      hKm g hg a 0 (by omega) z θ' ⟨hzpos, hθ'⟩
    have htri : |(1 / 2) * Work.Spaces.mixed a 1 (E g) z θ'
          + Work.Spaces.DzIter a (E g) z θ'|
        ≤ (1 / 2) * (Km * Work.FTS.StrongGlobal.Xn6 α g)
          + Km * Work.FTS.StrongGlobal.Xn6 α g := by
      refine le_trans (abs_add_le _ _) (add_le_add ?_ h0)
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    refine le_trans htri ?_
    have he : (1 / 2) * (Km * Work.FTS.StrongGlobal.Xn6 α g)
          + Km * Work.FTS.StrongGlobal.Xn6 α g
        = ((3 : ℝ) / 2 * Km) * Work.FTS.StrongGlobal.Xn6 α g := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hKmM2 hX0
  have hGb : ∀ θ' ∈ Set.Ioo 0 (π / 2),
      |Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.DzIter a (E g) z t) θ'|
        ≤ M * Work.FTS.StrongGlobal.Xn6 α g := by
    intro θ' hθ'
    -- the source `g` itself: an order-`≤ 2` pointwise jet bound of a class-`C` element
    have hsrc : |Work.Spaces.DzIter a g z θ'|
        ≤ (10 / Real.sqrt (Work.Spaces.gam α - 1)) * Work.FTS.StrongGlobal.Xn6 α g := by
      have h1 := Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1 hg a 0 (by omega)
        (z := z) (θ := θ') ⟨hzpos, hθ'⟩
      have hmem6 : Work.Spaces.HkMem α 6 g :=
        Work.FTS.OpenPkg.HkMem_mono_open hg.reg 6 (by norm_num) hg.mem
      have hnorm : Work.Spaces.HkNorm α 4 g ≤ Work.Spaces.HkNorm α 6 g :=
        Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 4) (by norm_num) hmem6
      exact le_trans h1 (mul_le_mul_of_nonneg_left hnorm hCg0)
    rw [hLslice θ' hθ']
    have h2 : |Work.Spaces.DzIter (a + 2) (E g) z θ'| ≤ Km * Work.FTS.StrongGlobal.Xn6 α g :=
      hKm g hg (a + 2) 0 (by omega) z θ' ⟨hzpos, hθ'⟩
    have h3 : |Work.Spaces.DzIter (a + 1) (E g) z θ'| ≤ Km * Work.FTS.StrongGlobal.Xn6 α g :=
      hKm g hg (a + 1) 0 (by omega) z θ' ⟨hzpos, hθ'⟩
    have ha2 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
    have ha5 : (0 : ℝ) ≤ 5 * α := by linarith
    have htri : |Work.Spaces.DzIter a g z θ' + α ^ 2 * Work.Spaces.DzIter (a + 2) (E g) z θ'
          + 5 * α * Work.Spaces.DzIter (a + 1) (E g) z θ'|
        ≤ |Work.Spaces.DzIter a g z θ'| + α ^ 2 * |Work.Spaces.DzIter (a + 2) (E g) z θ'|
          + 5 * α * |Work.Spaces.DzIter (a + 1) (E g) z θ'| := by
      calc |Work.Spaces.DzIter a g z θ' + α ^ 2 * Work.Spaces.DzIter (a + 2) (E g) z θ'
              + 5 * α * Work.Spaces.DzIter (a + 1) (E g) z θ'|
          ≤ |Work.Spaces.DzIter a g z θ' + α ^ 2 * Work.Spaces.DzIter (a + 2) (E g) z θ'|
            + |5 * α * Work.Spaces.DzIter (a + 1) (E g) z θ'| := abs_add_le _ _
        _ ≤ (|Work.Spaces.DzIter a g z θ'| + |α ^ 2 * Work.Spaces.DzIter (a + 2) (E g) z θ'|)
            + |5 * α * Work.Spaces.DzIter (a + 1) (E g) z θ'| :=
            add_le_add (abs_add_le _ _) le_rfl
        _ = |Work.Spaces.DzIter a g z θ'| + α ^ 2 * |Work.Spaces.DzIter (a + 2) (E g) z θ'|
            + 5 * α * |Work.Spaces.DzIter (a + 1) (E g) z θ'| := by
            simp only [abs_mul, abs_of_nonneg ha2, abs_of_nonneg ha5]
    refine le_trans htri ?_
    have hb2 := mul_le_mul_of_nonneg_left h2 ha2
    have hb3 := mul_le_mul_of_nonneg_left h3 ha5
    have hsum : |Work.Spaces.DzIter a g z θ'|
          + α ^ 2 * |Work.Spaces.DzIter (a + 2) (E g) z θ'|
          + 5 * α * |Work.Spaces.DzIter (a + 1) (E g) z θ'|
        ≤ (10 / Real.sqrt (Work.Spaces.gam α - 1) + α ^ 2 * Km + 5 * α * Km)
            * Work.FTS.StrongGlobal.Xn6 α g := by
      have hcoef : (10 / Real.sqrt (Work.Spaces.gam α - 1) + α ^ 2 * Km + 5 * α * Km)
            * Work.FTS.StrongGlobal.Xn6 α g
          = (10 / Real.sqrt (Work.Spaces.gam α - 1)) * Work.FTS.StrongGlobal.Xn6 α g
            + α ^ 2 * (Km * Work.FTS.StrongGlobal.Xn6 α g)
            + 5 * α * (Km * Work.FTS.StrongGlobal.Xn6 α g) := by ring
      linarith [hsrc, hb2, hb3, hcoef]
    exact le_trans hsum (mul_le_mul_of_nonneg_right hCM hX0)
  -- ## the slice lemma with the sharp constant `6`
  have hres := Work.FTS_EllLimOK.ProducerH.SecondDeriv.slice_second_deriv_le_six
    (S := fun θ'' => Work.Spaces.DzIter a (E g) z θ'')
    (G := fun θ' => Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.DzIter a (E g) z t) θ')
    hSsm heq (mul_nonneg hMpos.le hX0) hfb hSb hGb θ hθ
  calc |deriv (deriv (fun θ'' => Work.Spaces.DzIter a (E g) z θ'')) θ|
      ≤ 6 * (M * Work.FTS.StrongGlobal.Xn6 α g) := hres
    _ = (6 * M) * Work.FTS.StrongGlobal.Xn6 α g := by ring

end Work.FTS_EllLimOK.ProducerH.SecondDerivDz
