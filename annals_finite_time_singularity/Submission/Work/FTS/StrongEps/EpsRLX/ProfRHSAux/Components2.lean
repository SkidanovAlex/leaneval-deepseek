import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongEps.EpsRLX.LGTDiffClassC
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Components
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.bump_mixed_EpsSq_le
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongPersist.H6Row6.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_MuLamOK.RowReduction
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# `N_aux.ZTruncClassC` — `ClassC` is invariant under the truncation `ztrunc`

`ztrunc w z θ = if 0 < z then w z θ else 0` agrees with `w` everywhere on the half-plane
`z > 0`, i.e. on the open set `Ioi 0 ×ˢ univ`.  Every field of `ClassC α w` is

* an open-quadrant value (`reg : SmoothOpen`, and the values of `w`, of its `z`-slices
  (`fsm`), of the ratio `w z θ / z` near `z = 0⁺` (`axis`), or of the nonlocal operator
  `L₁₂` (`l12`), whose defining integral runs over `s > z ≥ 0`),
* `HkMem α k` (integrals over `Iz = [0,∞)`, whose weight `w(z) = (1+z)²/z²` vanishes at
  `z = 0`), or
* a one-sided trace/limit (`BdryTraces`, `ThetaTraces`, taken at `z > 0`, as `z → 0⁺`,
  as `z → ∞`, or as `θ → 0⁺`, `θ → π/2⁻`),

and none of these sees the values of `w` at `z ≤ 0`.  The `norm` field is the exception in a
different way: it is the only field that needs the *weak* vanishing hypothesis `hz` on `w`
(for `θ ∉ (0,π/2)` and `z > 0`), since `ztrunc` does not modify the values at `z > 0`.

The `θ`-part of the traces is free: `hw.norm` already gives `w z 0 = w z (π/2) = 0` for every
`z`, and `ztrunc` agrees with `w` there.
-/

/-! ## The slots of `ztrunc` on the open half-plane -/

/-- The mixed slots of `ztrunc w` and `w` agree at every point of the open half-plane
`z > 0` (with no smoothness hypothesis: the derivative operators are local). -/
theorem ztrunc_mixed_eq {w : Fn} (b a : ℕ) {z θ : ℝ} (hz : 0 < z) :
    Work.Spaces.mixed b a (ztrunc w) z θ = Work.Spaces.mixed b a w z θ := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have h : Set.EqOn (Function.uncurry (ztrunc w)) (Function.uncurry w)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := fun p hp => ztrunc_of_pos hp.1
  exact Work.FTS.RegPkgGal.mixed_congr_of_isOpen hV h b a (x := (z, θ))
    ⟨by simpa using hz, trivial⟩

/-! ## The boundary traces -/

/-- Composition with `z ↦ z * (· * w z)²` preserves eventual equality (`w` the radial
weight of `Work.Spaces`). -/
private theorem eeq_mul_w_sq {l : Filter ℝ} {u v : ℝ → ℝ} (h : u =ᶠ[l] v) :
    (fun z => z * (u z * Work.Spaces.w z) ^ 2) =ᶠ[l]
      (fun z => z * (v z * Work.Spaces.w z) ^ 2) := by
  filter_upwards [h] with z hz
  rw [hz]

/-- Composition with `θ ↦ sin(2θ)^{1-γ} * (·)²` preserves eventual equality. -/
private theorem eeq_sin_gam_sq {α : ℝ} {l : Filter ℝ} {u v : ℝ → ℝ} (h : u =ᶠ[l] v) :
    (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (u θ) ^ 2) =ᶠ[l]
      (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (v θ) ^ 2) := by
  filter_upwards [h] with θ hθ
  rw [hθ]

/-- `BdryTraces` is invariant under `ztrunc`: the four boundary directions only see the
germ of the mixed slots along `z > 0`. -/
theorem ztrunc_bdryTraces {α : ℝ} {k : ℕ} {w : Fn}
    (h : Work.FTS.Nonlin.BdryTraces α k w) :
    Work.FTS.Nonlin.BdryTraces α k (ztrunc w) := by
  intro a b hab
  obtain ⟨hA, hB⟩ := h a b hab
  refine ⟨fun θ hθ => ⟨?_, ?_⟩, fun z hz0 => ⟨?_, ?_⟩⟩
  · refine (Filter.tendsto_congr' (eeq_mul_w_sq ?_)).mpr (hA θ hθ).1
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [ztrunc_mixed_eq b a hz]
  · refine (Filter.tendsto_congr' (eeq_mul_w_sq ?_)).mpr (hA θ hθ).2
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    rw [ztrunc_mixed_eq b a hz]
  · refine (Filter.tendsto_congr' (eeq_sin_gam_sq ?_)).mpr (hB z hz0).1
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    rw [ztrunc_mixed_eq b a hz0]
  · refine (Filter.tendsto_congr' (eeq_sin_gam_sq ?_)).mpr (hB z hz0).2
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    rw [ztrunc_mixed_eq b a hz0]

/-- `ThetaTraces` is invariant under `ztrunc` (the `θ`-traces are taken at `z > 0`). -/
theorem ztrunc_thetaTraces {α : ℝ} {k : ℕ} {w : Fn}
    (h : Work.FTS.PhiStar.ThetaTraces α k w) :
    Work.FTS.PhiStar.ThetaTraces α k (ztrunc w) := by
  intro s hs z hz
  obtain ⟨h1, h2⟩ := h s hs z hz
  refine ⟨?_, ?_⟩
  · refine (Filter.tendsto_congr' (eeq_sin_gam_sq ?_)).mpr h1
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    rw [ztrunc_mixed_eq s 0 hz]
  · refine (Filter.tendsto_congr' (eeq_sin_gam_sq ?_)).mpr h2
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    rw [ztrunc_mixed_eq s 0 hz]

/-! ## The angular moment, the normalisation, the axis condition and `L₁₂` -/

/-- The angular moment `F_*(z) = ∫_θ w z θ sin θ cos²θ` of `ztrunc w` equals that of `w` for
every `z > 0`. -/
theorem ztrunc_Fstar {w : Fn} {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Fstar (ztrunc w) z = Work.Elliptic.Fstar w z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
  intro θ hθ
  simp only [ztrunc_of_pos hz]

/-- `ztrunc w` is angularly normalised as soon as `w` vanishes off the open quadrant for
`z > 0`. -/
theorem ztrunc_normTh {w : Fn}
    (hz : ∀ z θ : ℝ, 0 < z → θ ∉ Set.Ioo 0 (Real.pi / 2) → w z θ = 0) :
    Work.FTS.ClassC.normTh (ztrunc w) = ztrunc w := by
  funext z θ
  by_cases hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · simp [Work.FTS.ClassC.normTh, hθ]
  · rw [Work.FTS.ClassC.normTh_apply_of_not_mem hθ]
    by_cases hzpos : 0 < z
    · rw [ztrunc_of_pos hzpos, hz z θ hzpos hθ]
    · exact (ztrunc_of_nonpos hzpos).symm

/-- The axis condition transfers to `ztrunc`. -/
theorem ztrunc_axis {w : Fn}
    (h : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Tendsto (fun z => w z θ / z) (𝓝[>] 0) (𝓝 0)) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Tendsto (fun z => ztrunc w z θ / z) (𝓝[>] 0) (𝓝 0) := by
  intro θ hθ
  refine (Filter.tendsto_congr' ?_).mpr (h θ hθ)
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [ztrunc_of_pos hz]

/-- The zero mode of `L₁₂` is unchanged by the truncation: its defining integral runs over
`s > z ≥ 0`, where `ztrunc w = w`. -/
theorem ztrunc_L12 (w : Fn) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (ztrunc w) z = Work.Construction.L12 w z :=
  Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ hz
    (fun _ _ hz' _ _ => ztrunc_of_pos hz')

/-! ## The target -/

/-- **`ClassC` is invariant under the truncation `ztrunc`.**

`ztrunc w z θ = if 0 < z then w z θ else 0` agrees with `w` on the whole half-plane `z > 0`, and
every field of `ClassC α w` is either an open-quadrant value (`reg : SmoothOpen`, `norm`,
`fsm`, `axis`, `l12`), an integral over `Iz = [0,∞)` whose integrand vanishes at `z = 0`
(`mem`, `mem8`, `mem10`), or a one-sided trace/limit taken at `z ∈ Ioi 0` or as `z → 0⁺`, `z → ∞`,
`θ → 0⁺`, `θ → π/2⁻` (`tr`, `tr7`, `thTr`).  Note `hw.norm : normTh w = w` already gives
`w z 0 = w z (π/2) = 0` for every `z`, so the `θ`-part of the fields is free. -/
theorem ztrunc_classC {α : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hw : Work.FTS.ClassC.ClassC α w)
    (hz : ∀ z θ : ℝ, 0 < z → θ ∉ Set.Ioo 0 (Real.pi / 2) → w z θ = 0) :
    Work.FTS.ClassC.ClassC α
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w) := by
  refine { norm := ztrunc_normTh hz, reg := smoothOpen_ztrunc hw.reg,
           mem := HkMem_ztrunc hw.mem, mem8 := HkMem_ztrunc hw.mem8,
           mem10 := HkMem_ztrunc hw.mem10,
           tr := ztrunc_bdryTraces hw.tr, tr7 := ztrunc_bdryTraces hw.tr7,
           fsm := ?_, axis := ztrunc_axis hw.axis,
           l12 := by rw [ztrunc_L12 w le_rfl, hw.l12],
           thTr := ztrunc_thetaTraces hw.thTr }
  intro m
  exact (hw.fsm m).congr (fun z hz' => ztrunc_Fstar hz')

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rowsNT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The honest §8 row table, rows 8–26** (the `NRows2` obligation of the level-four
nonlinear estimate), in the class-`C` context `CtxT`. -/
theorem rowsNT (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.VocabO2.NRows2 IP α K g Φs Φg := by
  obtain ⟨K1, hK1, h1⟩ := rows.rowsN1 IP hN hE
  obtain ⟨K2, hK2, h2⟩ := rows.rowsN2a IP hN hE
  obtain ⟨K3, hK3, h3⟩ := rows.rowsN2b IP hN hE
  obtain ⟨K4, hK4, h4⟩ := rows.rowsN3a IP hN hE
  obtain ⟨K5, hK5, h5⟩ := rows.rowsN3b IP hN hE
  obtain ⟨K6, hK6, h6⟩ := rows.rowsN4a IP hN hE
  obtain ⟨K7, hK7, h7⟩ := rows.rowsN4b IP hN hE
  obtain ⟨K8, hK8, h8⟩ := rows.rowsN5a IP hN hE
  obtain ⟨K9, hK9, h9⟩ := rows.rowsN5b IP hN hE
  set K : ℝ := K1 + K2 + K3 + K4 + K5 + K6 + K7 + K8 + K9 + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hle1 : K1 ≤ K := by rw [hKdef]; linarith
  have hle2 : K2 ≤ K := by rw [hKdef]; linarith
  have hle3 : K3 ≤ K := by rw [hKdef]; linarith
  have hle4 : K4 ≤ K := by rw [hKdef]; linarith
  have hle5 : K5 ≤ K := by rw [hKdef]; linarith
  have hle6 : K6 ≤ K := by rw [hKdef]; linarith
  have hle7 : K7 ≤ K := by rw [hKdef]; linarith
  have hle8 : K8 ≤ K := by rw [hKdef]; linarith
  have hle9 : K9 ≤ K := by rw [hKdef]; linarith
  refine ⟨K, hKpos, ?_⟩
  intro α g Φs Φg hctx
  obtain ⟨hr8, hr9, hr10, hr11⟩ := h1 hctx
  obtain ⟨hr12, hr13⟩ := h2 hctx
  obtain ⟨hr14, hr15⟩ := h3 hctx
  obtain ⟨hr16, hr17⟩ := h4 hctx
  obtain ⟨hr18, hr19⟩ := h5 hctx
  obtain ⟨hr20, hr21⟩ := h6 hctx
  obtain ⟨hr22, hr23⟩ := h7 hctx
  have hr24 := h8 hctx
  obtain ⟨hr25, hr26⟩ := h9 hctx
  -- the four elementary factors occurring on the right-hand sides
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hctx.hα.le _
  have hB : 0 ≤ α ^ (3 / 2 : ℝ) := Real.rpow_nonneg hctx.hα.le _
  have hS : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hP : 0 ≤ α ^ 2 := pow_nonneg hctx.hα.le 2
  have hQ : 0 ≤ α ^ 3 := pow_nonneg hctx.hα.le 3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hr8.trans (mul_le_mul_of_nonneg_right hle1 (mul_nonneg hA (pow_nonneg hX0 2)))
  · exact hr9.trans (mul_le_mul_of_nonneg_right hle1 (mul_nonneg hS hX0))
  · exact hr10.trans (mul_le_mul_of_nonneg_right hle1 (mul_nonneg hS hX0))
  · exact hr11.trans (mul_le_mul_of_nonneg_right hle1 hP)
  · exact hr12.trans (mul_le_mul_of_nonneg_right hle2 (mul_nonneg hA (pow_nonneg hX0 3)))
  · exact hr13.trans (mul_le_mul_of_nonneg_right hle2 (mul_nonneg hB hX0))
  · exact hr14.trans (mul_le_mul_of_nonneg_right hle3 (mul_nonneg hS (pow_nonneg hX0 2)))
  · exact hr15.trans (mul_le_mul_of_nonneg_right hle3 hP)
  · exact hr16.trans (mul_le_mul_of_nonneg_right hle4 (pow_nonneg hX0 3))
  · exact hr17.trans (mul_le_mul_of_nonneg_right hle4 (mul_nonneg hB hX0))
  · exact hr18.trans (mul_le_mul_of_nonneg_right hle5 (mul_nonneg hB (pow_nonneg hX0 2)))
  · exact hr19.trans (mul_le_mul_of_nonneg_right hle5 hQ)
  · exact hr20.trans (mul_le_mul_of_nonneg_right hle6 (mul_nonneg hA (pow_nonneg hX0 3)))
  · exact hr21.trans (mul_le_mul_of_nonneg_right hle6 (mul_nonneg hB hX0))
  · exact hr22.trans (mul_le_mul_of_nonneg_right hle7 (mul_nonneg hS (pow_nonneg hX0 2)))
  · exact hr23.trans (mul_le_mul_of_nonneg_right hle7 hQ)
  · exact hr24.trans (mul_le_mul_of_nonneg_right hle8 (pow_nonneg hX0 2))
  · exact hr25.trans (mul_le_mul_of_nonneg_right hle9 (mul_nonneg hS hX0))
  · exact hr26.trans (mul_le_mul_of_nonneg_right hle9 hP)

end Work.FTS.StrongEps.E4R3.N4C
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRHSPSup =====
section

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **A common `L₁₂`-zero-mode bound of the mollified right-hand side, in family form.** -/
theorem epsWP_corr_le_fam {α T KW : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {G : ℕ → Fam} {ε : ℕ → ℝ}
    (hρ : IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    (hsm : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ (ε n) Φs E (G n) s))
    (hKW : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 4 (epsWP α ρ (ε n) Φs E (G n) s) ∧
        Work.FTS.Nonlin.Xn α (epsWP α ρ (ε n) Φs E (G n) s) ≤ KW) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      |Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0| ≤ Cc := by
  obtain ⟨C, hC0, hZ⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨CJ, hCJ0, hSqJ⟩ := HkSq_Jeps_le ρ hρ.moll
  refine ⟨C * Real.exp (CJ / 2) * max KW 0 + 1, by positivity, ?_⟩
  intro n s hs
  have hεn : 0 < ε n := (hε n).1
  have hεn1 : ε n ≤ 1 := (hε n).2
  have hexp1 : Real.exp (CJ * ε n / 2) ≤ Real.exp (CJ / 2) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hCJ0, hεn1]
  obtain ⟨hmem, hbnd⟩ := hKW n s hs
  have hsm' : ∀ m : ℕ, ContDiffOn ℝ m (Function.uncurry (epsWP α ρ (ε n) Φs E (G n) s)) Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsm n s hs)
  have hWmem : Work.Spaces.HkMem α 4 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) :=
    HkMem_Jeps hρ.moll hα hεn hsm' hmem
  have hWsm : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) :=
    smoothOpen_Jeps ρ hρ hεn hsm'
  have h1 := hZ α hα.1 hα.2 _ ⟨hWsm, hWmem⟩
  have hKW0 : 0 ≤ KW := le_trans (Work.Spaces.HkNorm_nonneg α 4 _) hbnd
  have hsqW : Work.Spaces.HkSq α 4 (epsWP α ρ (ε n) Φs E (G n) s) ≤ KW ^ 2 := by
    have h : Work.Spaces.HkSq α 4 (epsWP α ρ (ε n) Φs E (G n) s)
        = (Work.FTS.Nonlin.Xn α (epsWP α ρ (ε n) Φs E (G n) s)) ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 _)]
    rw [h]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 _) hbnd 2
  have hXnJ : Work.FTS.Nonlin.Xn α (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s))
      ≤ Real.exp (CJ / 2) * max KW 0 := by
    have hsq := hSqJ α hα 4 (ε n) hεn hεn1 _ hsm' hmem hWmem
    have hkey : Work.Spaces.HkSq α 4 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s))
        ≤ Real.exp (CJ * ε n) * KW ^ 2 :=
      le_trans hsq (mul_le_mul_of_nonneg_left hsqW (Real.exp_pos _).le)
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 4 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)))
        ≤ Real.sqrt (Real.exp (CJ * ε n) * KW ^ 2) := Real.sqrt_le_sqrt hkey
      _ = Real.exp (CJ * ε n / 2) * KW := by
          rw [Real.sqrt_mul (Real.exp_pos _).le, Real.sqrt_sq hKW0, ← Real.exp_half]
      _ ≤ Real.exp (CJ / 2) * max KW 0 :=
          mul_le_mul hexp1 (le_max_left _ _) hKW0 (Real.exp_pos _).le
  have h2 : |Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0|
      ≤ C * (Real.exp (CJ / 2) * max KW 0) :=
    le_trans h1 (mul_le_mul_of_nonneg_left hXnJ hC0.le)
  have h3 : 0 ≤ C * (Real.exp (CJ / 2) * max KW 0) :=
    mul_nonneg hC0.le (mul_nonneg (Real.exp_pos _).le (le_max_right _ _))
  linarith [h2]

/-- **A common sup bound for `epsRHSP` on a compact, in family form.** -/
theorem epsRHSP_sup_le_fam {α C₀ Ce Cs T B Cc : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {G : ℕ → Fam} {ε : ℕ → ℝ}
    (hρ : IsSmoothKernel ρ) (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1)
    {K K' : Set (ℝ × ℝ)} (hKc : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hKK' : K ⊆ K')
    (hshift : ∀ n : ℕ, ∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ ε n → |q.2| ≤ ε n →
      (zShift p.1 q.1, thShift p.2 q.2) ∈ K')
    (hB0 : 0 ≤ B)
    (hwp : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K',
      |epsWP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ B)
    (hCc0 : 0 ≤ Cc)
    (hcorr : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      |Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0| ≤ Cc) :
    ∃ B' : ℝ, 0 < B' ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T, ∀ p : ℝ × ℝ, p ∈ K →
      |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ B' := by
  obtain ⟨Cb, hCb0, hbump⟩ := exists_bound_mixed_bump K hKc
  have hpz : 0 < pzNorm := PZeroAux.pzNorm_pos
  refine ⟨B + (Cc / pzNorm) * Cb + 1, by positivity, ?_⟩
  intro n s hs p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
  have hsplit : epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2
      = Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2
        - (Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
          * bump p.1 p.2 := by
    rw [epsRHSP_eq_Pz_Jeps_epsWP, Pz_apply]
  have hJ : |Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2| ≤ B :=
    abs_Jeps_le_sup ρ hρ.moll (hε n).1 hz ⟨hθ0, hθ1⟩
      (fun q hq1 hq2 => hwp n s hs (zShift p.1 q.1, thShift p.2 q.2) (hshift n p hp q hq1 hq2)) hB0
  have hbu : |bump p.1 p.2| ≤ Cb := by
    have h := hbump 0 0 (by norm_num) p hp
    simpa [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using h
  have hcor : |(Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
      * bump p.1 p.2| ≤ (Cc / pzNorm) * Cb := by
    rw [abs_mul]
    have hL := hcorr n s hs
    have hc : |Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm|
        ≤ Cc / pzNorm := by
      rw [abs_div, abs_of_pos hpz]
      exact div_le_div_of_nonneg_right hL hpz.le
    exact mul_le_mul hc hbu (abs_nonneg _) (div_nonneg hCc0 hpz.le)
  rw [hsplit]
  have htri : |Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2
        - (Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
          * bump p.1 p.2|
      ≤ |Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2|
        + |(Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
          * bump p.1 p.2| := by
    have h := abs_add_le (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2)
      (-((Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
        * bump p.1 p.2))
    simpa only [sub_eq_add_neg, abs_neg] using h
  calc |Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2
        - (Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
          * bump p.1 p.2|
      ≤ |Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2|
        + |(Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
          * bump p.1 p.2| := htri
    _ ≤ B + (Cc / pzNorm) * Cb := add_le_add hJ hcor
    _ ≤ B + (Cc / pzNorm) * Cb + 1 := by linarith


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Components2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The quadratic-in-`(F_*, W)` term `N₀` -/

/-- **`N₀ α (F_* + W) W → 0`.**  Unfolding `N₀` at `F = F_* + W`, `g = W` gives the six summands

`(3/2α)(sin 2θ)L₁₂(F_*)∂_θF_*`, `-c₂ₘL₁₂(F_*)D_zF_*`, `(1/α)L₁₂(W)W`,
`(3/2α)(sin 2θ)L₁₂(W)∂_θF`, `-c₂ₘL₁₂(W)D_zF`, `-c₂ₘL₁₂(F_*)D_zW`,

each of which is a (bounded) constant or the bounded factor `c₂ₘ` times a vanishing mixed
derivative: `∂_θF_*`, `D_zF_*`, `W`, `∂_θF`, `D_zF`, `D_zW`. -/
theorem tendsto_N0 {α : ℝ} {W : Fn} (hW : Work.FTS.ClassC.ClassC α W) {l : Filter ℝ} {z : ℝ}
    (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Construction.N0 α (Work.Construction.Ftot α W) W z θ)
      l (𝓝 0) := by
  set A : ℝ := Work.Construction.L12 (Work.Construction.Fstar α) z with hA
  set L : ℝ := Work.Construction.L12 W z with hL
  have hfun : (fun θ : ℝ => Work.Construction.N0 α (Work.Construction.Ftot α W) W z θ)
      = fun θ : ℝ =>
          (3 / (2 * α)) * A * Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          + (-Work.Construction.c2m θ * A * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
          + (1 / α) * L * W z θ
          + (3 / (2 * α)) * L * Work.Spaces.Dth (Work.Construction.Ftot α W) z θ
          + (-Work.Construction.c2m θ * L * Work.Spaces.Dz (Work.Construction.Ftot α W) z θ)
          + (-Work.Construction.c2m θ * A * Work.Spaces.Dz W z θ) := by
    funext θ
    simp only [Work.Construction.N0, A, L, Work.Spaces.Dth, Work.Construction.s2] <;> ring
  -- the six summands
  have n1 : Filter.Tendsto (fun θ : ℝ =>
      (3 / (2 * α)) * A * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) l (𝓝 0) := by
    simpa using (tendsto_Dth_Fstar hc).const_mul ((3 / (2 * α)) * A)
  have hbA : ∀ᶠ θ in l, |-(Work.Construction.c2m θ) * A| ≤ 2 * |A| := by
    filter_upwards with θ
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (abs_c2m_le_two θ) (abs_nonneg A)
  have hbL : ∀ᶠ θ in l, |-(Work.Construction.c2m θ) * L| ≤ 2 * |L| := by
    filter_upwards with θ
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (abs_c2m_le_two θ) (abs_nonneg L)
  have n2 : Filter.Tendsto (fun θ : ℝ => -Work.Construction.c2m θ * A
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) l (𝓝 0) :=
    tendsto_mul_comm_of_eventually_bounded (tendsto_Dz_Fstar hc) hbA
  have n3 : Filter.Tendsto (fun θ : ℝ => (1 / α) * L * W z θ) l (𝓝 0) := by
    have h : Filter.Tendsto (fun θ : ℝ => ((1 / α) * L) * Work.Spaces.mixed 0 0 W z θ)
        l (𝓝 0) := by
      simpa using (hc.slot 0 0 (by norm_num)).const_mul ((1 / α) * L)
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero, mul_assoc]
      using h
  have n4 : Filter.Tendsto (fun θ : ℝ =>
      (3 / (2 * α)) * L * Work.Spaces.Dth (Work.Construction.Ftot α W) z θ) l (𝓝 0) := by
    simpa using (tendsto_Dth_Ftot hW hc).const_mul ((3 / (2 * α)) * L)
  have n5 : Filter.Tendsto (fun θ : ℝ => -Work.Construction.c2m θ * L
      * Work.Spaces.Dz (Work.Construction.Ftot α W) z θ) l (𝓝 0) :=
    tendsto_mul_comm_of_eventually_bounded (tendsto_Dz_Ftot hW hc) hbL
  have n6 : Filter.Tendsto (fun θ : ℝ => -Work.Construction.c2m θ * A
      * Work.Spaces.mixed 1 0 W z θ) l (𝓝 0) :=
    tendsto_mul_comm_of_eventually_bounded (hc.slot 0 1 (by norm_num)) hbA
  have h6 : Filter.Tendsto (fun θ : ℝ => -Work.Construction.c2m θ * A
      * Work.Spaces.Dz W z θ) l (𝓝 0) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero, Work.Spaces.Dz, Work.Spaces.pz] using n6
  rw [hfun]
  simpa using ((((n1.add n2).add n3).add n4).add n5).add h6

/-! ## The elliptic-correction term `N` -/

/-- **`N α (F_* + W) (Φs + Φg) → 0`.**  The five summands of `N`, reassociated so that the
stream-function factor carries the bounds of `ProfRHSAux/Bounds`,

`2ℛ(Φ̃)F`, `-2U(Φ̃)∂_θF`, `-2αV(Φ̃)D_zF`, `-(1/2)(sin 2θ)(F,K)∂_θF`, `-sin²θ (F,K) F`,

all carry the vanishing factor `F`, `D_θF` or `D_zF`; the first through `|ℛ(Φ̃)| ≤ CR`, the
second through `|U(Φ̃)| ≤ CU·|sin 2θ|` (which converts `∂_θF` into `D_θF`), the third through
`|V(Φ̃)| ≤ CV`. -/
theorem tendsto_N {α Cs Ce : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W Φg : Fn}
    (hW : Work.FTS.ClassC.ClassC α W) (hell : Work.FTS.VocabO.EllPkgGo α Ce W Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {l : Filter ℝ} {z : ℝ}
    (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Construction.N α (Work.Construction.Ftot α W)
      (fun z θ => Φs z θ + Φg z θ) z θ) l (𝓝 0) := by
  obtain ⟨CR, hCR0, hCR⟩ := RopPsiBound hα hW hell hstar hc.hz
  obtain ⟨CU, hCU0, hCU⟩ := UopPsiBound hα hW hell hstar hc.hz
  obtain ⟨CV, hCV0, hCV⟩ := VopPsiBound hα hW hell hstar hc.hz
  have hbR : ∀ᶠ θ in l, |2 * Work.Construction.Rop α (PsiTot α Φs W Φg) z θ| ≤ 2 * CR := by
    filter_upwards [hc.hquad] with θ hθ
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (hCR θ hθ.1 hθ.2) (by norm_num)
  have hbV : ∀ᶠ θ in l, |-(2 * α) * Work.Construction.Vop (PsiTot α Φs W Φg) z θ|
      ≤ 2 * α * CV := by
    filter_upwards [hc.hquad] with θ hθ
    have h2a : (0 : ℝ) ≤ 2 * α := by linarith [hα.1]
    calc |-(2 * α) * Work.Construction.Vop (PsiTot α Φs W Φg) z θ|
        = (2 * α) * |Work.Construction.Vop (PsiTot α Φs W Φg) z θ| := by
          rw [abs_mul, abs_neg, abs_of_nonneg h2a]
      _ ≤ (2 * α) * CV := mul_le_mul_of_nonneg_left (hCV θ hθ.1 hθ.2) h2a
  -- the five summands
  have t1 : Filter.Tendsto (fun θ : ℝ => 2 * (Work.Construction.Rop α (PsiTot α Φs W Φg) z θ
      * Work.Construction.Ftot α W z θ)) l (𝓝 0) := by
    have h := tendsto_mul_comm_of_eventually_bounded (tendsto_Ftot hc) hbR
    simpa only [mul_assoc] using h
  have hbU : ∀ᶠ θ in l, |-(2 : ℝ) * (Work.Construction.Uop α (PsiTot α Φs W Φg) z θ
      * Work.Spaces.pth (Work.Construction.Ftot α W) z θ)|
      ≤ |(2 * CU) * Work.Spaces.Dth (Work.Construction.Ftot α W) z θ| := by
    filter_upwards [hc.hquad] with θ hθ
    have hs2 : Work.Construction.s2 θ ≠ 0 := by
      have h2θ : 0 < 2 * θ := by linarith [hθ.1]
      have h2π : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h2θ h2π)
    have hUop : |Work.Construction.Uop α (PsiTot α Φs W Φg) z θ|
        ≤ CU * |Work.Construction.s2 θ| := by
      calc |Work.Construction.Uop α (PsiTot α Φs W Φg) z θ|
          = |(Work.Construction.Uop α (PsiTot α Φs W Φg) z θ / Work.Construction.s2 θ)
              * Work.Construction.s2 θ| := by rw [div_mul_cancel₀ _ hs2]
        _ = |Work.Construction.Uop α (PsiTot α Φs W Φg) z θ / Work.Construction.s2 θ|
              * |Work.Construction.s2 θ| := by rw [abs_mul]
        _ ≤ CU * |Work.Construction.s2 θ| := by
            have hq : |Work.Construction.Uop α (PsiTot α Φs W Φg) z θ
                / Work.Construction.s2 θ| ≤ CU := by
              rw [abs_div]
              exact (div_le_iff₀ (abs_pos.mpr hs2)).mpr (hCU θ hθ.1 hθ.2)
            exact mul_le_mul_of_nonneg_right hq
              (abs_nonneg (Work.Construction.s2 θ))
    have hp : (0 : ℝ) ≤ |Work.Spaces.pth (Work.Construction.Ftot α W) z θ| := abs_nonneg _
    calc |-(2 : ℝ) * (Work.Construction.Uop α (PsiTot α Φs W Φg) z θ
          * Work.Spaces.pth (Work.Construction.Ftot α W) z θ)|
        = 2 * (|Work.Construction.Uop α (PsiTot α Φs W Φg) z θ|
            * |Work.Spaces.pth (Work.Construction.Ftot α W) z θ|) := by
          rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
      _ ≤ 2 * ((CU * |Work.Construction.s2 θ|)
            * |Work.Spaces.pth (Work.Construction.Ftot α W) z θ|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hUop hp)
            (by norm_num : (0 : ℝ) ≤ 2)
      _ = |(2 * CU) * Work.Spaces.Dth (Work.Construction.Ftot α W) z θ| := by
          have h2CU : (0 : ℝ) ≤ 2 * CU := by linarith
          rw [Work.Spaces.Dth, Work.Construction.s2, abs_mul, abs_of_nonneg h2CU, abs_mul]
          ring
  have t2 : Filter.Tendsto (fun θ : ℝ => -(2 : ℝ) * (Work.Construction.Uop α (PsiTot α Φs W Φg) z θ
      * Work.Spaces.pth (Work.Construction.Ftot α W) z θ)) l (𝓝 0) :=
    tendsto_zero_of_eventually_abs_le
      (by simpa using (tendsto_Dth_Ftot hW hc).const_mul (2 * CU)) hbU
  have t3 : Filter.Tendsto (fun θ : ℝ => -(2 * α) * (Work.Construction.Vop (PsiTot α Φs W Φg) z θ
      * Work.Spaces.Dz (Work.Construction.Ftot α W) z θ)) l (𝓝 0) := by
    have h := tendsto_mul_comm_of_eventually_bounded (tendsto_Dz_Ftot hW hc) hbV
    simpa only [mul_assoc] using h
  have t4 : Filter.Tendsto (fun θ : ℝ =>
      -(1 / 2) * Work.Construction.FK (Work.Construction.Ftot α W) z
      * Work.Spaces.Dth (Work.Construction.Ftot α W) z θ) l (𝓝 0) := by
    simpa using (tendsto_Dth_Ftot hW hc).const_mul
      (-(1 / 2) * Work.Construction.FK (Work.Construction.Ftot α W) z)
  have t5 : Filter.Tendsto (fun θ : ℝ => -(Real.sin θ ^ 2)
      * Work.Construction.FK (Work.Construction.Ftot α W) z
      * Work.Construction.Ftot α W z θ) l (𝓝 0) := by
    have hb5 : ∀ᶠ θ in l, |-(Real.sin θ ^ 2)
        * Work.Construction.FK (Work.Construction.Ftot α W) z| ≤ 1 * |Work.Construction.FK (Work.Construction.Ftot α W) z| := by
      filter_upwards with θ
      have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
      rw [abs_mul, abs_neg]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      nlinarith [h1, abs_nonneg (Real.sin θ)]
    have h := tendsto_mul_comm_of_eventually_bounded (tendsto_Ftot hc) hb5
    simpa only [mul_assoc, one_mul] using h
  have hfun : (fun θ : ℝ => Work.Construction.N α (Work.Construction.Ftot α W)
      (fun z θ => Φs z θ + Φg z θ) z θ)
      = fun θ : ℝ =>
          2 * (Work.Construction.Rop α (PsiTot α Φs W Φg) z θ
              * Work.Construction.Ftot α W z θ)
          + (-(2 : ℝ) * (Work.Construction.Uop α (PsiTot α Φs W Φg) z θ
              * Work.Spaces.pth (Work.Construction.Ftot α W) z θ))
          + (-(2 * α) * (Work.Construction.Vop (PsiTot α Φs W Φg) z θ
              * Work.Spaces.Dz (Work.Construction.Ftot α W) z θ))
          + (-(1 / 2) * Work.Construction.FK (Work.Construction.Ftot α W) z
              * Work.Spaces.Dth (Work.Construction.Ftot α W) z θ)
          + (-(Real.sin θ ^ 2) * Work.Construction.FK (Work.Construction.Ftot α W) z
              * Work.Construction.Ftot α W z θ) := by
    funext θ
    simp only [Work.Construction.N, PsiTot, Work.Spaces.Dth, Work.Construction.s2]
    ring
  rw [hfun]
  simpa using (((t1.add t2).add t3).add t4).add t5

/-! ## The assembly -/

/-- **`gRHS α μ λ (F_* + W) (Φs + Φg) W → 0`** for any constants `μ, λ`. -/
theorem tendsto_gRHS {α Cs Ce mu lam : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W Φg : Fn}
    (hW : Work.FTS.ClassC.ClassC α W) (hell : Work.FTS.VocabO.EllPkgGo α Ce W Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {l : Filter ℝ} {z : ℝ}
    (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.Construction.gRHS α mu lam
      (Work.Construction.Ftot α W) (fun z θ => Φs z θ + Φg z θ) W z θ) l (𝓝 0) := by
  set mb : ℝ := Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α W) W)
      (Work.Construction.N α (Work.Construction.Ftot α W) (fun z θ => Φs z θ + Φg z θ)) with hmb
  have hAK : Filter.Tendsto (fun θ : ℝ => (-mb) * Work.Construction.AK α z θ) l (𝓝 0) := by
    simpa using (tendsto_AK hc).const_mul (-mb)
  have hN0 := tendsto_N0 hW hc
  have hN := tendsto_N hα hW hell hstar hc
  have hNs := tendsto_Nstar hc mu lam
  have h12 : Filter.Tendsto (fun θ : ℝ => (-mb) * Work.Construction.AK α z θ
      + Work.Construction.N0 α (Work.Construction.Ftot α W) W z θ) l (𝓝 0) := by
    simpa using hAK.add hN0
  have h123 : Filter.Tendsto (fun θ : ℝ => (-mb) * Work.Construction.AK α z θ
      + Work.Construction.N0 α (Work.Construction.Ftot α W) W z θ
      + Work.Construction.N α (Work.Construction.Ftot α W)
          (fun z θ => Φs z θ + Φg z θ) z θ) l (𝓝 0) := by
    simpa using h12.add hN
  have hfun : (fun θ : ℝ => Work.Construction.gRHS α mu lam
      (Work.Construction.Ftot α W) (fun z θ => Φs z θ + Φg z θ) W z θ)
      = fun θ : ℝ =>
          (-mb) * Work.Construction.AK α z θ
          + Work.Construction.N0 α (Work.Construction.Ftot α W) W z θ
          + Work.Construction.N α (Work.Construction.Ftot α W)
              (fun z θ => Φs z θ + Φg z θ) z θ
          + Work.Construction.Nstar mu lam W z θ := by
    funext θ
    simp only [Work.Construction.gRHS, mb] <;> ring
  rw [hfun]
  simpa using h123.add hNs

/-- **`profRHS α Φs E W → 0`** at the fixed `z > 0`, along the endpoint filter `l`. -/
theorem tendsto_profRHS {α Ce Cs : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W : Fn} {E : Fn → Fn}
    (hW : Work.FTS.ClassC.ClassC α W) (hell : Work.FTS.VocabO.EllPkgGo α Ce W (E W))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {l : Filter ℝ} {z : ℝ}
    (hc : TraceCtx α W l z) :
    Filter.Tendsto (fun θ : ℝ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W z θ)
      l (𝓝 0) := by
  have hsplit : (fun θ : ℝ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W z θ)
      = fun θ : ℝ => -(Work.Coercivity.LGammaT α W z θ)
          + Work.Construction.gRHS α
              (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E
                  (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)))
                (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)) 0)
              (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E
                  (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)))
                (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)) 0)
              (Work.Construction.Ftot α W) (fun z θ => Φs z θ + E W z θ) W z θ := rfl
  rw [hsplit]
  have h1 : Filter.Tendsto (fun θ : ℝ => -(Work.Coercivity.LGammaT α W z θ)) l (𝓝 0) := by
    simpa using (tendsto_LGammaT hc).neg
  have h2 : Filter.Tendsto (fun θ : ℝ => Work.Construction.gRHS α
      (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)))
        (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)) 0)
      (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)))
        (Work.FTS.Galerkin.famOf (fun _ : ℝ => W)) 0)
      (Work.Construction.Ftot α W) (fun z θ => Φs z θ + E W z θ) W z θ) l (𝓝 0) :=
    tendsto_gRHS hα hW hell hstar hc
  simpa using h1.add h2

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
end
end
