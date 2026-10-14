import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.Tail.FK_Fstar_add
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Stability.ZcutSmoothCompact

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsWPLim

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## Pointwise convergence of the slots at a point of the open quadrant -/



/-! ## The `F_*`-shift: mixed slots and the angular moment -/

/-- `F_*` is `C^∞` on the open quadrant. -/
theorem smoothOpen_Fstar (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
  Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)

/-- `SmoothOpen` is closed under sums. -/
theorem smoothOpen_add {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall] at hf hg ⊢
  intro n
  exact (hf n).add (hg n)


/-- **`F_*`-additivity of the mixed slots**: on the open quadrant, the mixed operators of the
profile `F = F_* + w` split into those of `F_*` and those of `w`. -/
theorem mixed_Fstar_add {α : ℝ} {w : Fn} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hw : Work.FTS.EllipticEst.SmoothOpen w) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => Work.Construction.Fstar α z θ + w z θ) z θ
      = Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ + Work.Spaces.mixed j i w z θ :=
  Work.FTS.EllipticEst.SmoothOpen.mixed_add (smoothOpen_Fstar α) hw j i z θ hz hθ.1 hθ.2

/-- The `θ`-slice of `w·K` is integrable on `Iθ` for `z > 0`, from `SmoothOpen w` and
`HkMem α 4 w` (the statement is `integrableOn_slice_of_SmoothOpen_HkMem` with the division by
`z` undone). -/
theorem integrableOn_slice_mul_K {α z : ℝ} {w : Fn}
    (hw : Work.FTS.EllipticEst.SmoothOpen w) (hwm : Work.Spaces.HkMem α 4 w) (hz : 0 < z) :
    IntegrableOn (fun θ => w z θ * Work.Spaces.K θ) Work.Spaces.Iθ := by
  have h := Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hw hwm hz
  have h2 : IntegrableOn (fun θ => (Work.Spaces.K θ * w z θ / z) * z) Work.Spaces.Iθ :=
    h.mul_const z
  refine IntegrableOn.congr_fun h2 ?_ measurableSet_Icc
  intro θ _
  field_simp

/-- **`F_*`-additivity of the angular moment `FK`**, from the honest class `HQo α 4 w` of the
perturbation (no `GalClass` hypothesis is needed: only the integrability of the `θ`-slice of
`w·K`). -/
theorem FK_Fstar_add_of_SmoothOpen_HkMem {α : ℝ} {w : Fn}
    (hw : Work.FTS.EllipticEst.SmoothOpen w) (hwm : Work.Spaces.HkMem α 4 w) {z : ℝ}
    (hz : 0 < z) :
    Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + w z θ) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK w z :=
  Work.FTS.GalFields.Tail.FK_Fstar_add
    (fun z' hz' => integrableOn_slice_mul_K hw hwm hz') hz

/-! ## `sin (2θ) ≠ 0` on the open quadrant -/

/-- `sin (2θ) ≠ 0` for `θ ∈ (0, π/2)`: the quotient by `sin (2θ)` used to pass from the slot
`mixed 0 1 = D_θ` to the bare `∂_θ` is legitimate on the open quadrant. -/
theorem sin_two_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Real.sin (2 * θ) ≠ 0 := by
  have h1 : 0 < 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ < Real.pi := by linarith [hθ.2]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)

/-! ## The pointwise limit of `N` from the slots of `PhiTil` -/

/-- **The pointwise limit of `Construction.N`.**  `N α F Φ` is a scalar expression in the eight
quantities `F z θ`, `∂_θF(z,θ)`, `D_zF(z,θ)`, `FK F z`, `Φ̃(z,θ)`, `∂_zΦ̃(z,θ)`,
`∂_θΦ̃(z,θ)` with `Φ̃ = PhiTil α F Φ`; the hypotheses control the slots of `F` (order `≤ 1`),
`FK F z`, and the slots of `Φ̃` itself (order `≤ 1`) — which is exactly what the limit lemma
needs, since `Φ` enters `N` only through `PhiTil α F Φ`. -/
theorem N_tendsto_of_PhiTil {α : ℝ} {F : ℕ → Fn} {Fl : Fn} {Ψ : ℕ → Fn} {Ψl : Fn}
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hF : ∀ j i : ℕ, j + i ≤ 1 →
      Tendsto (fun n : ℕ => Work.Spaces.mixed j i (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Fl z θ)))
    (hFK : Tendsto (fun n : ℕ => Work.Construction.FK (F n) z) Filter.atTop
      (nhds (Work.Construction.FK Fl z)))
    (hΨ : ∀ j i : ℕ, j + i ≤ 1 →
      Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (F n) (Ψ n)) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i (Work.Construction.PhiTil α Fl Ψl) z θ))) :
    Tendsto (fun n : ℕ => Work.Construction.N α (F n) (Ψ n) z θ) Filter.atTop
      (nhds (Work.Construction.N α Fl Ψl z θ)) := by
  have hsin := sin_two_ne_zero hθ
  -- the eight slots of the scalar expression `NNF`
  have hFZ : Tendsto (fun n : ℕ => F n z θ) Filter.atTop (nhds (Fl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
      using hF 0 0 (by norm_num)
  have hFZD : Tendsto (fun n : ℕ => Work.Spaces.Dz (F n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dz Fl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hF 1 0 (by norm_num)
  have hFTH' : Tendsto (fun n : ℕ => Real.sin (2 * θ) * Work.Spaces.pth (F n) z θ) Filter.atTop
      (nhds (Real.sin (2 * θ) * Work.Spaces.pth Fl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth] using hF 0 1 (by norm_num)
  have hFTH : Tendsto (fun n : ℕ => Work.Spaces.pth (F n) z θ) Filter.atTop
      (nhds (Work.Spaces.pth Fl z θ)) := by
    have h := hFTH'.const_mul (Real.sin (2 * θ))⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hsin, one_mul] using h
  have hPZ : Tendsto (fun n : ℕ => Work.Spaces.pz
      (Work.Construction.PhiTil α (F n) (Ψ n)) z θ) Filter.atTop
      (nhds (Work.Spaces.pz (Work.Construction.PhiTil α Fl Ψl) z θ)) := by
    have h : Tendsto (fun n : ℕ => z * Work.Spaces.pz
        (Work.Construction.PhiTil α (F n) (Ψ n)) z θ) Filter.atTop
        (nhds (z * Work.Spaces.pz (Work.Construction.PhiTil α Fl Ψl) z θ)) := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
        Work.Spaces.DthIter_zero, Work.Spaces.Dz] using hΨ 1 0 (by norm_num)
    have h2 := h.const_mul z⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hz), one_mul] using h2
  have hPTH : Tendsto (fun n : ℕ => Work.Spaces.pth
      (Work.Construction.PhiTil α (F n) (Ψ n)) z θ) Filter.atTop
      (nhds (Work.Spaces.pth (Work.Construction.PhiTil α Fl Ψl) z θ)) := by
    have h : Tendsto (fun n : ℕ => Real.sin (2 * θ) * Work.Spaces.pth
        (Work.Construction.PhiTil α (F n) (Ψ n)) z θ) Filter.atTop
        (nhds (Real.sin (2 * θ) * Work.Spaces.pth
          (Work.Construction.PhiTil α Fl Ψl) z θ)) := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
        Work.Spaces.DthIter_zero, Work.Spaces.Dth] using hΨ 0 1 (by norm_num)
    have h2 := h.const_mul (Real.sin (2 * θ))⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hsin, one_mul] using h2
  have hP : Tendsto (fun n : ℕ => Work.Construction.PhiTil α (F n) (Ψ n) z θ) Filter.atTop
      (nhds (Work.Construction.PhiTil α Fl Ψl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
      using hΨ 0 0 (by norm_num)
  have key := Work.FTS.StrongEps.NNF_tendsto (α := α) (z := z) (θ := θ)
    (FZ := Fl z θ) (FTH := Work.Spaces.pth Fl z θ) (FZD := Work.Spaces.Dz Fl z θ)
    (FKV := Work.Construction.FK Fl z)
    (P := Work.Construction.PhiTil α Fl Ψl z θ)
    (PZ := Work.Spaces.pz (Work.Construction.PhiTil α Fl Ψl) z θ)
    (PTH := Work.Spaces.pth (Work.Construction.PhiTil α Fl Ψl) z θ)
    hFZ hFTH hFZD hFK hP hPZ hPTH
  convert key using 1
  · funext n
    exact Work.FTS.StrongEps.N_eq_NNF α (F n) (Ψ n) z θ
  · congr 1

end Work.FTS.StrongEps.EpsWPLim
