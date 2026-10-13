/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.StrongEps.PZeroAux.classC_Pz`

The projection `P₀ = Pz` of `Submission/Work/FTS/StrongEps/PZero.lean` preserves the elliptic
source class `Work.FTS.ClassC.ClassC`: from a datum `f` whose *mollifier* clauses are
`SoftClass` (open-quadrant smoothness, `ℋ⁸`-honesty, the boundary traces up to order `7`, the
axis condition, no angular junk), whose angular moment `F_*f` is `C^∞` on `(0,∞)`, and for which
the projected profile has vanishing zero mode `L₁₂(Pz f)(0) = 0`, the projection `Pz f` lies in
`ClassC α`.

Since `Pz f = f - (L₁₂ f 0 / pzNorm) • bump`, every clause is either inherited from `f` (the
linearity of `SmoothOpen`, `HkMem`, `BdryTraces`, `F_*`, of the axis limit and of the `L₁₂`-mode)
or comes from the *explicit* correction profile `bump` of `BumpDefs.lean`, which is smooth
everywhere and supported in the box `[1/2,1] × [π/8,3π/8]` strictly inside the open quadrant:

* `hkMem_bump` — `bump ∈ ℋᵏ` for every `k`, from the box support
  (`GalLimit.Closure.hkMem_of_suppIn`);
* `bdryTraces_bump` — all boundary traces of `bump` vanish (`GalBasis.bdryTraces_of_suppIn`);
* `fstar_bump_eq` — `F_*(bump)` is *explicit*, namely `z ↦ zCut z · ∫ thCut θ sinθcos²θ dθ`
  (because `bump z θ = zCut z · thCut θ` factorises), hence `C^∞` on `(0,∞)`.

Nothing here is a reduction: the only "analytic" inputs on `f` are the two *hypotheses* of the
statement (`SoftClass`, the smoothness of `F_*f`) and the zero-mode hypothesis `hl12`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.MolClassC
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.GalBasis.bdryTraces_of_suppIn
import Submission.Work.FTS.GalBasis.Defs
import Submission.Work.FTS.GalLimit.Closure.phi_HQo
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.PZeroAux

/-! ## Elementary facts about the correction profile `bump` -/

/-- The angular factor of `bump` vanishes identically off the open interval `(0, π/2)`. -/
theorem classC_Pz_bump_eq_zero_of_not_mem_Ioo {z θ : ℝ} (hθ : θ ∉ Set.Ioo 0 (π / 2)) :
    bump z θ = 0 := by
  rw [bump_eq_zero_iff]
  rcases not_and_or.mp hθ with h | h
  · exact Or.inr (Or.inr (Or.inl (by linarith [not_lt.mp h, Real.pi_pos])))
  · exact Or.inr (Or.inr (Or.inr (by linarith [not_lt.mp h, Real.pi_pos])))

/-- `bump` is supported in the box `[1/2,1] × [π/8,3π/8]`, strictly inside the open quadrant. -/
theorem classC_Pz_suppIn_bump : Work.FTS.GalBasis.SuppIn bump (1 / 2) 1 (π / 8) := by
  intro z θ h
  by_contra hne
  have hne' : bump z θ ≠ 0 := hne
  rw [bump_ne_zero_iff] at hne'
  obtain ⟨hz, hth⟩ := hne'
  rcases h with h | h
  · exact h ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  · refine h ⟨?_, ?_⟩
    · linarith [hth.1, Real.pi_pos]
    · linarith [hth.2]

/-- `bump` is `C^∞` on the open quadrant `z > -1`, `0 < θ < π/2` (it is `C^∞` everywhere). -/
theorem classC_Pz_smoothQuad_bump : Work.FTS.LocData.SmoothQuad bump :=
  contDiffOn_iff_forall_nat_le.mpr (fun m _ => (contDiff_bump m).contDiffOn)

/-- **`bump ∈ ℋᵏ`** for every `α` and every `k`, by the box support of `bump`. -/
theorem classC_Pz_hkMem_bump (α : ℝ) (k : ℕ) : Work.Spaces.HkMem α k bump :=
  Work.FTS.GalLimit.Closure.hkMem_of_suppIn α k (by norm_num) (by norm_num)
    (by linarith [Real.pi_pos]) classC_Pz_smoothQuad_bump classC_Pz_suppIn_bump

/-- **All the boundary traces of `bump` vanish**, by the box support of `bump`. -/
theorem classC_Pz_bdryTraces_bump (α : ℝ) (k : ℕ) : Work.FTS.Nonlin.BdryTraces α k bump :=
  Work.FTS.GalBasis.bdryTraces_of_suppIn (f := bump) (a := 1 / 2) (b := 1) (δ := π / 8)
    (by norm_num) (by linarith [Real.pi_pos]) classC_Pz_suppIn_bump α k

/-- **The angular moment of `bump` is explicit.**  Since `bump z θ = zCut z · thCut θ`
factorises, the angular integration can be performed once and for all:
`F_*(bump)(z) = zCut z · ∫_θ thCut θ sinθcos²θ dθ`.  In particular `F_*(bump)` is smooth on
`(0,∞)` (it is a constant multiple of the smooth cut-off `zCut`). -/
theorem classC_Pz_fstar_bump_eq (z : ℝ) :
    Work.Elliptic.Fstar bump z
      = zCut z * (∫ θ in Work.Spaces.Iθ, thCut θ * Work.Elliptic.sinCos2 θ) := by
  rw [Work.Elliptic.Fstar]
  have hcongr : (fun θ => bump z θ * Work.Elliptic.sinCos2 θ)
      = fun θ => zCut z * (thCut θ * Work.Elliptic.sinCos2 θ) := by
    funext θ
    rw [bump]
    ring
  rw [hcongr, MeasureTheory.integral_const_mul]

/-- `Pz f` rewritten as `f + c • bump`, the shape in which the linear closure lemmas apply. -/
theorem classC_Pz_Pz_eq_add_smul (f : ℝ → ℝ → ℝ) :
    Pz f = f + (-(Work.Construction.L12 f 0 / pzNorm)) • bump := by
  rw [Work.FTS.StrongEps.Pz, sub_eq_add_neg, neg_smul]

/-- The two angular normalisations of the workspace (`EllSol.normTh` and `ClassC.normTh`) agree. -/
theorem classC_Pz_normTh_eq (g : ℝ → ℝ → ℝ) :
    Work.FTS.ClassC.normTh g = Work.FTS.EllSol.normTh g := rfl

/-! ## The main theorem -/

theorem classC_Pz {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.StrongEps.SoftClass α f)
    (hfsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar f) (Set.Ioi 0))
    (hl12 : Work.Construction.L12 (Work.FTS.StrongEps.Pz f) 0 = 0) :
    Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz f) := by
  rw [classC_Pz_Pz_eq_add_smul f]
  -- the sign of the correction
  set c : ℝ := -(Work.Construction.L12 f 0 / pzNorm) with hc
  -- the `HkMem`-clause of `f` at order `0`
  have hmem0f : Work.Spaces.HkMem α 0 f :=
    Work.FTS.IPGen.HkMem_mono_le hf.reg 0 (by norm_num) hf.mem8
  -- the correction profile `c • bump`
  have hb_smooth : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * bump z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' c smoothOpen_bump
  have hb_mem : Work.Spaces.HkMem α 8 (fun z θ => c * bump z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 8 c (classC_Pz_hkMem_bump α 8)
  have hb_mem0 : Work.Spaces.HkMem α 0 (fun z θ => c * bump z θ) :=
    Work.FTS.IPGen.HkMem_mono_le hb_smooth 0 (by norm_num) hb_mem
  have hb_bdry : Work.FTS.Nonlin.BdryTraces α 7 (fun z θ => c * bump z θ) :=
    Work.FTS.ClassC.bdryTraces_smul (classC_Pz_bdryTraces_bump α 7) c
  -- the linear combinations
  have hreg : Work.FTS.EllipticEst.SmoothOpen (f + c • bump) :=
    Work.FTS.EllipticEst.smoothOpen_add hf.reg hb_smooth
  have hmem8 : Work.Spaces.HkMem α 8 (f + c • bump) :=
    Work.FTS.EllipticEst.HkMem_add_open hf.reg hb_smooth hf.mem8 hb_mem
  have hmem10 : Work.Spaces.HkMem α 10 (f + c • bump) :=
    Work.FTS.EllipticEst.HkMem_add_open hf.reg hb_smooth hf.mem10
      (Work.FTS.LocData.HkMem_const_mul α 10 c (classC_Pz_hkMem_bump α 10))
  have hmem7 : Work.Spaces.HkMem α 7 (f + c • bump) :=
    Work.FTS.IPGen.HkMem_mono_le hreg 7 (by norm_num) hmem8
  have htr7 : Work.FTS.Nonlin.BdryTraces α 7 (f + c • bump) :=
    Work.FTS.ClassC.bdryTraces_add hf.reg hb_smooth hf.tr7 hb_bdry
  have htr6 : Work.FTS.Nonlin.BdryTraces α 6 (f + c • bump) :=
    Work.FTS.ClassC.bdryTraces_mono (show 6 ≤ 7 by norm_num) htr7
  -- the angular moment clause
  have hfsm' : ∀ m : ℕ,
      ContDiffOn ℝ m (Work.Elliptic.Fstar (f + c • bump)) (Set.Ioi 0) := by
    intro m
    have hintf : ∀ z : ℝ, 0 < z →
        IntegrableOn (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      fun z hz => Work.FTS.ClassC.slice_sinCos2_integrable hf.reg hmem0f hz
    have hintb : ∀ z : ℝ, 0 < z →
        IntegrableOn (fun θ => bump z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      fun z hz => Work.FTS.ClassC.slice_sinCos2_integrable smoothOpen_bump
        (Work.FTS.IPGen.HkMem_mono_le smoothOpen_bump 0 (by norm_num)
          (classC_Pz_hkMem_bump α 8)) hz
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
        Work.Elliptic.Fstar (f + c • bump) z
          = Work.Elliptic.Fstar f z
              + c * (zCut z * (∫ θ in Work.Spaces.Iθ, thCut θ * Work.Elliptic.sinCos2 θ)) := by
      intro z hz
      have h1 : Work.Elliptic.Fstar (f + c • bump) z
          = Work.Elliptic.Fstar (fun z' θ => f z' θ + c * bump z' θ) z :=
        Work.FTS.ClassC.Fstar_congr_pt (fun z' θ => rfl) z
      have h2 : Work.Elliptic.Fstar (fun z' θ => f z' θ + c * bump z' θ) z
          = Work.Elliptic.Fstar f z + c * Work.Elliptic.Fstar bump z :=
        Work.FTS.EllSol.Fstar_add_mul (f := f) (h := bump) (c := c) (z := z)
          (hintf z hz) (hintb z hz)
      rw [h1, h2, classC_Pz_fstar_bump_eq z]
    have hsmooth : ContDiffOn ℝ m
        (fun z : ℝ => Work.Elliptic.Fstar f z
          + c * (zCut z * (∫ θ in Work.Spaces.Iθ,
              thCut θ * Work.Elliptic.sinCos2 θ))) (Set.Ioi 0) :=
      (hfsm m).add ((contDiffOn_const (c := c)).mul
        (((contDiff_zCut m).contDiffOn).mul
          (contDiffOn_const (c := ∫ θ in Work.Spaces.Iθ,
            thCut θ * Work.Elliptic.sinCos2 θ))))
    exact (contDiffOn_congr hpt).mpr hsmooth
  -- the axis clause
  have haxis : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Tendsto (fun z => (f + c • bump) z θ / z) (𝓝[>] 0) (𝓝 0) := by
    intro θ hθ
    have heq : (fun z => (f + c • bump) z θ / z)
        = fun z => f z θ / z + c * (bump z θ / z) := by
      funext z
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    have hzero : Tendsto (fun z => bump z θ / z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with z hz
      rw [bump, bump_zCut_eq_zero_of_lt hz.2]
      ring
    have hlim : Tendsto (fun z => f z θ / z + c * (bump z θ / z)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h1 : Tendsto (fun z => f z θ / z) (𝓝[>] (0 : ℝ)) (𝓝 0) := hf.axis θ hθ
      have h2 : Tendsto (fun z => c * (bump z θ / z)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using hzero.const_mul c
      simpa using h1.add h2
    exact hlim
  refine ⟨?_, hreg, hmem7, hmem8, hmem10, htr6, htr7, hfsm', haxis, ?_, ?_⟩
  · -- `normTh (f + c • bump) = f + c • bump`
    have hnormf : Work.FTS.ClassC.normTh f = f := by
      rw [classC_Pz_normTh_eq, hf.norm]
    funext z θ
    by_cases hθ : θ ∈ Set.Ioo 0 (π / 2)
    · rw [Work.FTS.ClassC.normTh_apply_of_mem hθ]
    · rw [Work.FTS.ClassC.normTh_apply_of_not_mem hθ]
      have hfz : f z θ = 0 := by
        have h := congr_fun (congr_fun hnormf z) θ
        rw [Work.FTS.ClassC.normTh_apply_of_not_mem hθ] at h
        exact h.symm
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hfz,
        classC_Pz_bump_eq_zero_of_not_mem_Ioo hθ, mul_zero, add_zero]
  · -- the zero mode of `L₁₂`
    rw [hc, show f + (-(Work.Construction.L12 f 0 / pzNorm)) • bump = Pz f from
      (classC_Pz_Pz_eq_add_smul f).symm]
    exact hl12
  · -- the θ-traces (lead install R6, 2026-10-11)
    exact Work.FTS.ClassC.thetaTraces_add hf.reg hb_smooth hf.thTr
      (Work.FTS.PhiStar.thetaTraces_of_bdryTraces
        (Work.FTS.ClassC.bdryTraces_smul (classC_Pz_bdryTraces_bump α 10) c))

end Work.FTS.StrongEps.PZeroAux
