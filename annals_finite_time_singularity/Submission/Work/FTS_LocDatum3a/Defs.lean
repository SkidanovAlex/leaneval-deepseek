import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocDataExt.Final
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.Physical.BiotSavart.bsAdmissibleStripFull_comp_clock
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.LogInt
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagCurveIRho
import Submission.Work.FTS.StrongEps.EpsODE
import Submission.Work.FTS.StrongEps.MolClassC
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSlotInt
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3DataFinal
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.Spaces.bt_prod_integrable
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Flat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsTransfer/Flat.lean` — the flat (`wip`) form of the slot pairings

`Work.Coercivity.wip ρ A B = ∫_z ∫_θ A z θ * B z θ * ρ z θ` is the flat pairing out of which
`H1IP` is built, while `Work.FTS.TransportS.slotPairing ρ a b u v` is the `ρ · D_z^bD_θ^a u ·
D_z^bD_θ^a v` slot pairing.  Here we record

* `wip_eq_flat` — the same integral with the weight in front (the form in which the transfer
  estimate is stated);
* `slotPairing_eq_wip` — the slot pairing is the flat pairing of the two slots;
* `sqrt_wip_self_le_HkNorm` — the diagonal of a leaf pairing is bounded by the `ℋ¹`-norm
  (`JepsTransfer.leaf_pairIntegral_le_HkSq`);
* `lintegral_leaf_le_HkSq` — the corresponding `∫⁻`-bound, which gives the log-side
  integrability;
* `logW_nonneg_of_leaf` — nonnegativity of the log weight of a leaf.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- For `volume.restrict Iθ` the two endpoints `0`, `π/2` are null. -/
private theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The flat pairing, with the weight put in front. -/
theorem wip_eq_flat (ρ A B : ℝ → ℝ → ℝ) :
    Work.Coercivity.wip ρ A B
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ * B z θ := by
  rw [Work.Coercivity.wip]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
  ring

/-- The slot pairing of a weight at the slot `(a,b)` is the flat pairing of the two slots. -/
theorem slotPairing_eq_wip (ρ : ℝ → ℝ → ℝ) (a b : ℕ) (X Y : Fn) :
    Work.FTS.TransportS.slotPairing ρ a b X Y
      = Work.Coercivity.wip ρ (Work.Spaces.mixed b a X) (Work.Spaces.mixed b a Y) := by
  rw [wip_eq_flat]
  rfl

/-- The diagonal of a leaf pairing is dominated by the squared `ℋ¹`-norm. -/
theorem sqrt_wip_self_le_HkNorm {α : ℝ} (hα : 0 < α) {u : Fn}
    (hmem : Work.Spaces.HkMem α 1 u) {a b : ℕ} (hab : a + b ≤ 1)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    Real.sqrt (Work.Coercivity.wip ρ (Work.Spaces.mixed b a u) (Work.Spaces.mixed b a u))
      ≤ Work.Spaces.HkNorm α 1 u := by
  have h := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.leaf_pairIntegral_le_HkSq
    hα hmem hab hρ
  have h' : Work.FTS.TransportS.slotPairing ρ a b u u ≤ Work.Spaces.HkSq α 1 u := by
    rw [Work.FTS.TransportS.slotPairing]
    have heq : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed b a u z θ * Work.Spaces.mixed b a u z θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ρ z θ * (Work.Spaces.mixed b a u z θ) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
      ring
    rw [heq]
    exact h
  have he : Work.Coercivity.wip ρ (Work.Spaces.mixed b a u) (Work.Spaces.mixed b a u)
      = Work.FTS.TransportS.slotPairing ρ a b u u :=
    (slotPairing_eq_wip ρ a b u u).symm
  rw [Work.Spaces.HkNorm, he]
  exact Real.sqrt_le_sqrt h'

/-- **The `∫⁻`-domination of a leaf pairing at level one.** -/
theorem lintegral_leaf_le_HkSq {α : ℝ} (hα : 0 < α) {u : Fn}
    (hmem : Work.Spaces.HkMem α 1 u) {a b : ℕ} (hab : a + b ≤ 1)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (ρ z θ * (Work.Spaces.mixed b a u z θ) ^ 2))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 1 u) := by
  have hHk : ENNReal.ofReal (Work.Spaces.HkSq α 1 u)
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 u z θ) := by
    rw [Work.Spaces.HkSq]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
      (Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 1 u z θ)]
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 1 u z θ)
  rw [hHk]
  refine MeasureTheory.lintegral_mono_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  refine MeasureTheory.lintegral_mono_ae ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  exact ENNReal.ofReal_le_ofReal
    (Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα hρ (f := u) hθ hab)

/-- The log weight of a leaf is nonnegative. -/
theorem logW_nonneg_of_leaf {α : ℝ} {a : ℕ} {w : ℝ → ℝ → ℝ}
    (hw : Work.FTS.TransportS.IsLeafW α a w) :
    ∀ y : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y := by
  intro y
  rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply]
  refine mul_nonneg (Work.FTS.StrongEps.HkSqAux.logJac_nonneg y.1 y.2) ?_
  exact Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hw (Real.exp y.1)
    ⟨le_of_lt (Real.arctan_pos.mpr (Real.exp_pos y.2)),
      le_of_lt (Real.arctan_lt_pi_div_two _)⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsGdotThird =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn Fam slice)

/-! ## Bridge 0 — the two copies of `IsBslSolPos`

`ClassC.EllPkgK` carries `StrongGlobal.IsBslSolPos` (a three-way split of the boundary conjuncts)
while `StrongPersist.EllPkgK` carries `StrongPersist.IsBslSolPos` (paired); the two are equivalent
by repackaging. -/

/-- The two `IsBslSolPos` copies agree. -/
theorem isBslSolPos_toStrongPersist {α : ℝ} {F Ψ : Fn}
    (h : Work.FTS.StrongGlobal.IsBslSolPos α F Ψ) :
    Work.FTS.StrongPersist.IsBslSolPos α F Ψ :=
  ⟨h.1, fun z hz => ⟨h.2.1 z hz, h.2.2.1 z hz⟩, h.2.2.2⟩

/-! ## Bridge 1 — `H6Adm` at the mollified slice from `ClassC`

`H6Adm α f` (`StrongPersist/Vocab.lean`) is the class of the level-three estimates
(`L3Data.lin`, `L3Data.rhs`).  Its fields are `HQo α 6 f` (`SmoothOpen f` and `HkMem α 6 f`),
`VanishTheta f`, the axis condition `f 0 θ = 0 ∧ pz f 0 θ = 0` and `L₁₂ f 0 = 0`.

`ClassC α f` gives everything except the axis condition and `VanishTheta`, and both of those are
supplied by the defining `if` of `Jeps` (`Jeps_eq_zero`): `J_ε h` vanishes at `z = 0` and at
`θ = 0, π/2`.  The first radial derivative at the axis then vanishes as well, because `f` is
identically `0` for `z ≤ 0` and `ClassC.axis` states `f z θ / z → 0` as `z → 0⁺`, so the two-sided
difference quotient `(f z θ - f 0 θ)/z` tends to `0`. -/

/-- A profile vanishing identically on a radial line has `pz = 0` on it. -/
theorem pz_zero_of_eq_zero {f : Fn} {θ : ℝ} (h : ∀ z : ℝ, f z θ = 0) :
    Work.Spaces.pz f 0 θ = 0 := by
  have hfun : (fun z : ℝ => f z θ) = fun _ => 0 := funext h
  show deriv (fun z : ℝ => f z θ) 0 = 0
  rw [hfun, deriv_const]

/-- **The axis derivative of a profile that vanishes off the open quadrant and satisfies the
`ClassC` axis condition**: `pz f 0 θ = 0` for `θ ∈ (0,π/2)`. -/
theorem pz_zero_of_tendsto_div {f : Fn} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hzero : ∀ z : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → f z θ = 0)
    (hax : Tendsto (fun z : ℝ => f z θ / z) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Work.Spaces.pz f 0 θ = 0 := by
  have hf0 : f 0 θ = 0 := hzero 0 (by simp)
  have hleft : Tendsto (fun z : ℝ => f z θ / z) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : ¬ (0 < z) := not_lt.mpr (le_of_lt hz)
    rw [hzero z (fun hc => hz0 hc.1)]
    simp
  have htwo : Tendsto (fun z : ℝ => f z θ / z) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hsplit : (𝓝[≠] (0 : ℝ)) = 𝓝[<] (0 : ℝ) ⊔ 𝓝[>] (0 : ℝ) := by
      have hcompl : ({0} : Set ℝ)ᶜ = Set.Iio 0 ∪ Set.Ioi 0 := by
        ext z
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Iio,
          Set.mem_Ioi]
        constructor
        · intro hz
          rcases lt_trichotomy z 0 with h | h | h
          · exact Or.inl h
          · exact absurd h hz
          · exact Or.inr h
        · rintro (h | h)
          · exact ne_of_lt h
          · exact ne_of_gt h
      rw [hcompl, nhdsWithin_union]
    rw [hsplit]
    exact tendsto_sup.mpr ⟨hleft, hax⟩
  have hderiv : HasDerivAt (fun z : ℝ => f z θ) 0 0 := by
    refine hasDerivAt_iff_tendsto_slope.mpr ?_
    show Tendsto (fun z : ℝ => slope (fun z : ℝ => f z θ) 0 z) (𝓝[≠] (0 : ℝ)) (𝓝 0)
    have hfun : (fun z : ℝ => slope (fun z : ℝ => f z θ) 0 z)
        = fun z : ℝ => f z θ / z := by
      funext z
      rw [slope_def_field, hf0, sub_zero, sub_zero]
    rw [hfun]
    exact htwo
  show deriv (fun z : ℝ => f z θ) 0 = 0
  rw [hderiv.deriv]

/-- **Bridge 1.** A `ClassC` profile that vanishes off the open quadrant — in particular
`J_ε h` — is in the level-three class `H6Adm`. -/
theorem H6Adm_of_classC_of_eqzero {α : ℝ} {f : Fn}
    (hf : Work.FTS.ClassC.ClassC α f)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → f z θ = 0) :
    Work.FTS.StrongPersist.H6Adm α f := by
  refine ⟨?_, ?_, ?_, hf.l12⟩
  · exact ⟨hf.reg, Work.FTS.OpenPkg.HkMem_mono_open hf.reg 6 (by norm_num) hf.mem⟩
  · exact ⟨fun z => hzero z 0 (by simp), fun z => hzero z (π / 2) (by simp)⟩
  · intro θ hθ
    by_cases hI : θ ∈ Set.Ioo 0 (π / 2)
    · exact ⟨hzero 0 θ (by simp),
        pz_zero_of_tendsto_div hI (fun z hz => hzero z θ hz) (hf.axis θ hI)⟩
    · have hz0 : ∀ z : ℝ, f z θ = 0 := fun z => hzero z θ (fun hc => hI hc.2)
      exact ⟨hz0 0, pz_zero_of_eq_zero hz0⟩


/-! ## Bridge 2 — `Ell6Ctx` at the mollified slice -/

/-- **Bridge 2.** `Ell6Ctx` at a `ClassC` profile, from `hEll` (the `ClassC` copies of `EllPkgGo`
and `EllPkgK`) and `hstar` — the `ClassC` counterpart of `ell6Ctx_of_classC`. -/
theorem Ell6Ctx_of_classC {α Ce Cs : ℝ} {E : Fn → Fn} {Φs f : Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hf : Work.FTS.ClassC.ClassC α f) :
    Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs f (fun z θ => Φs z θ + E f z θ) :=
  ⟨hstar,
    ⟨isBslSolPos_toStrongPersist (hEll f hf).2.sol, (hEll f hf).2.smooth, (hEll f hf).2.R,
      (hEll f hf).2.U, (hEll f hf).2.V⟩,
    rfl, (hEll f hf).1⟩

/-! ## The target — RETIRED (2026-10-12)

The design's level-three `dbd` statement for the **un-projected** scheme —

  `EpsGdotThird : L3Data → … → IsEpsSol → EpsReg → (hsmW : C^∞ of epsWU) → (hb4) → (hb6) →
     ∃ Cd > 0, ∀ τ ∈ Ioo 0 T, HkMem α 3 (gdot g τ) ∧ HkNorm α 3 (gdot g τ) ≤ Cd`

— sat here with a `sorry` as the *record* of a statement that was returned **mis-stated** by a
prover (it carried neither `hα1` nor `hsmW`).  It was repaired and **proved** as
`Submission/Work/FTS/StrongEps/EpsGdotThirdH.lean` (`EpsGdotThirdH`) on the *projected* scheme
`IsEpsSolP`, which is the scheme the route actually uses (`EpsReg`/`IsEpsSol` are superseded by
`EpsRegP`/`IsEpsSolP`).  The declaration has therefore been withdrawn: keeping a live `sorry` in a
file that *other areas' modules import* (`RawE6Aux/bdata_blkN0.lean`, the S2 chain) polluted their
cones for no gain.  The record of the old statement and its known defects is in
`NOTES_session2.md` / `NOTES_EpsGdotThird_FALSE.md`; the bridges above
(`isBslSolPos_toStrongPersist`, `pz_zero_of_eqzero`, `pz_zero_of_tendsto_div`,
`H6Adm_of_classC_of_eqzero`, `H6Adm_Jfam`, `Ell6Ctx_of_classC`) remain, and are `sorry`-free. -/

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.RadBound.L12fSlotLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.RadBound

/-- **The radial slot bound for `L₁₂ f`.**

For a datum `f` of the open-quadrant class (`SmoothOpen f`, `HkMem α 4 f`) with vanishing zero
mode `L₁₂(f)(0) = 0`, the sum of the weighted squares of the first five `z∂_z`-iterates of the
radial function `L₁₂(f)` is integrable on `Iz = [0,∞)` and its integral is controlled by the
`ℋ⁴`-energy `HkSq α 4 f`, with a constant independent of `α ∈ (0,1]` and of `f`.

This is the localisation of the `k = 0` part of Elgindi's Prop. `L12H` (tex 1276--1290) to a
single radial slot; it is the open-quadrant (`SmoothOpen`) version of the estimate proved inside
`Work.FTS.OpenPkg.l12H_field` (that file bounds `Xn α (L₁₂ f)`; the underlying sum bound is
re-derived here because the consumer needs the radial sum itself rather than the norm).  The
proof is the same: the `k = 0` slot is the weighted Hardy inequality `∫ (L₁₂ f)² w² ≤ 107 ∫ (Qang f 0)² w²`
and, for `1 ≤ c ≤ 4`, the iterate is the angular moment `D_z^c (L₁₂ f) = -Qang f (c-1)`
(`l12_open_bundle`), whose weighted square integral is bounded by
`(∫_θ K_θ²)·HkSq α 4 f` (`Qang_sq_w_sq_integral_open`).  The constant is `111·∫_θ K_θ² + 1`. -/
theorem L12fSlotLe :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Construction.L12 f 0 = 0 →
      MeasureTheory.IntegrableOn (fun z : ℝ =>
          ∑ c ∈ Finset.range 5, (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ c ∈ Finset.range 5,
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α 4 f := by
  -- the universal constant `∫_θ K_θ²` (independent of `α`)
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAKdef
  have hAKnn : 0 ≤ AK := by
    rw [hAKdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  refine ⟨111 * AK + 1, by linarith, ?_⟩
  intro α hα f hsm hmem h0
  have hαpos : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- the two definitions of `L₁₂` agree, so the hypothesis transfers
  have h0e : Work.Elliptic.L12 f 0 = 0 := by
    rw [← Work.FTS.H2.constructionL12_eq_ellipticL12 f]
    exact h0
  obtain ⟨hgen, hInt0, hBnd0⟩ :=
    Work.FTS.OpenPkg.l12_open_bundle α f hαpos hα1 hsm hmem h0e
  set u : ℝ → ℝ := fun z => Work.Elliptic.L12 f z with hudef
  have hgen' : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) u z = - Work.Elliptic.Qang f k z := by
    intro k hk z hz
    rw [hudef]
    exact hgen k hk z hz
  -- ## the a.e. transfer `D_z^i (L₁₂ f) = -Qang f (i-1)` on `Iz`, `1 ≤ i ≤ 4`
  have htrans : ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Elliptic.Qang f (i - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2
          = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi hi4
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with z hz0 hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    have hsub : i - 1 ≤ 3 := by omega
    have key : Work.Elliptic.DzdIter i u z = - Work.Elliptic.Qang f (i - 1) z := by
      have h := hgen' (i - 1) hsub z hzpos
      rwa [show i - 1 + 1 = i by omega] at h
    rw [key, neg_sq]
  -- ## integrability of every weighted slot
  have hInt : ∀ i : ℕ, i ≤ 4 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    intro i hi4
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hInt0
    · exact (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hαpos hα1 hsm hmem
        (i := i - 1) (by omega)).1.congr (htrans i h hi4)
  have hsum_int : ∀ i ∈ Finset.range 5, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  -- ## the bounds of the individual slots
  have hBnd0' : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 107 * (AK * Work.Spaces.HkSq α 4 f) := by
    have hb : (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang f 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hBnd0
    have hQ := (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hαpos hα1 hsm hmem
      (i := 0) (by norm_num)).2
    rw [← hAKdef] at hQ
    exact le_trans hb (mul_le_mul_of_nonneg_left hQ (by norm_num))
  have hBndI : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ AK * Work.Spaces.HkSq α 4 f := by
    intro i hi hi4
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htrans i hi hi4)]
    exact (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hαpos hα1 hsm hmem
      (i := i - 1) (by omega)).2
  -- ## the sum of the slots
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 111 * (AK * Work.Spaces.HkSq α 4 f) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 5) hsum_int,
      Finset.sum_range_succ']
    have h4 : (∑ i ∈ Finset.range 4, (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (i + 1) u z) ^ 2 * (Work.Spaces.w z) ^ 2))
        ≤ ∑ _i ∈ Finset.range 4, AK * Work.Spaces.HkSq α 4 f :=
      Finset.sum_le_sum fun i hi => by
        rw [Finset.mem_range] at hi
        exact hBndI (i + 1) (by omega) (by omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
    refine le_trans (add_le_add h4 hBnd0') (le_of_eq ?_)
    ring
  -- ## integrability of the whole `z`-sum
  have hsumInt : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ i ∈ Finset.range 5,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    MeasureTheory.integrable_finsetSum (Finset.range 5) hsum_int
  -- ## back to `Work.Coercivity.L12f`
  have hfun : Work.Coercivity.L12f f = u := by
    funext z
    have h1 : Work.Coercivity.L12f f = Work.Construction.L12 f := rfl
    rw [hudef, h1]
    exact congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 f) z
  have hcongr : (fun z : ℝ => ∑ c ∈ Finset.range 5,
        (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = (fun z : ℝ => ∑ c ∈ Finset.range 5,
        (Work.Elliptic.DzdIter c u z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    funext z
    rw [hfun]
  constructor
  · rw [hcongr]
    exact hsumInt
  · rw [hcongr]
    refine le_trans hsum_le ?_
    have hknn : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
    nlinarith

end Work.FTS.StrongEps.EpsRLX.RadBound
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.PZeroAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Uniform bounds for the correction profile `bump`

The only `α`-dependence of `Work.Spaces.HkIntegrand α k f` is through the angular weight
`Wt α z θ = w z · sin(2θ)^{-γ(α)/2}`, with `γ(α) = 1 + α/10` increasing in `α`.  On `Iθ` the
base `sin(2θ)` lies in `[0,1]`, where `x ↦ x^{p}` is *antitone*, so the weight is increasing in
`α`: this is the first lemma.  It upgrades the per-`α` bounds of `BumpDefs.lean`
(`exists_bound_HkIntegrand_bump`) to a single bound valid for all `α ∈ (0,1]` and `k ≤ 6`. -/

/-- **Monotonicity of the `ℋ^k`-integrand in the parameter `α`.**  For `0 < α ≤ β`, on the
angular interval `Iθ = [0,π/2]` the weight `Wt α z θ` grows with `α` (the exponent `γ(α)/2`
grows and the base `sin(2θ) ∈ [0,1]`), so every summand of `HkIntegrand` grows termwise. -/
theorem HkIntegrand_gam_mono {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (k : ℕ)
    (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k f z θ ≤ Work.Spaces.HkIntegrand β k f z θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hga : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hgb : 0 < Work.Spaces.gam β := Work.Spaces.gam_pos hβ0
  have hexp : -(Work.Spaces.gam β / 2) ≤ -(Work.Spaces.gam α / 2) := by
    have h : Work.Spaces.gam α ≤ Work.Spaces.gam β := by
      rw [Work.Spaces.gam, Work.Spaces.gam]; linarith
    linarith
  have hrpow : Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))
      ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.gam β / 2)) := by
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h, Real.zero_rpow (by intro hc; linarith [hga]),
        Real.zero_rpow (by intro hc; linarith [hgb])]
    · exact Real.rpow_le_rpow_of_exponent_ge h hs1 hexp
  have hw0 : 0 ≤ Work.Spaces.w z := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hterm : ∀ a : ℝ,
      (a * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
        ≤ (a * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam β / 2)))) ^ 2 := by
    intro a
    have hA0 : 0 ≤ Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)) :=
      mul_nonneg hw0 (Real.rpow_nonneg hs0 _)
    have hAB : Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))
        ≤ Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam β / 2)) :=
      mul_le_mul_of_nonneg_left hrpow hw0
    have hsq : (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        ≤ (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam β / 2))) ^ 2 :=
      pow_le_pow_left₀ hA0 hAB 2
    calc (a * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
        = a ^ 2 * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
          ring
      _ ≤ a ^ 2 * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam β / 2))) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg a)
      _ = (a * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam β / 2)))) ^ 2 := by
          ring
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  refine add_le_add (le_refl _) ?_
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hc : 1 ≤ i ∧ i + j ≤ k
  · rw [if_pos hc, if_pos hc]
    simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
    exact hterm _
  · rw [if_neg hc, if_neg hc]

/-- The correction profile `bump` lies in `ℋᵏ` for every parameter `α` and every order `k`: its
support is the box `[1/2,1] × [π/8, 3π/8]`, strictly inside the open quadrant, and `bump` is
`C^∞` on the whole plane (`Work.FTS.GalLimit.Closure.hkMem_of_suppIn`). -/
theorem hkMem_bump (α : ℝ) (k : ℕ) : Work.Spaces.HkMem α k Work.FTS.StrongEps.bump := by
  refine Work.FTS.GalLimit.Closure.hkMem_of_suppIn α k (a := 1 / 2) (b := 1)
    (δ := Real.pi / 8) (by norm_num) (by norm_num) (by linarith [Real.pi_pos]) ?_ ?_
  · exact contDiffOn_iff_forall_nat_le.mpr
      (fun m _ => (Work.FTS.StrongEps.contDiff_bump m).contDiffOn)
  · intro z θ h
    rw [Work.FTS.StrongEps.bump_eq_zero_iff]
    rcases h with h | h
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h
      · exact Or.inl (le_of_lt h)
      · exact Or.inr (Or.inl (le_of_lt h))
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h
      · exact Or.inr (Or.inr (Or.inl (by linarith [h, Real.pi_pos])))
      · exact Or.inr (Or.inr (Or.inr (by linarith)))

/-- **The correction profile is uniformly bounded in `ℋᵏ`.**  There is a single constant `B`
with `‖bump‖_{ℋᵏ} ≤ B` for every `α ∈ (0,1]` and every `k ≤ 6`.

The `ℋᵏ`-integrand of `bump` vanishes off the box `[1/2,1] × [π/4,3π/8]`
(`HkIntegrand_bump_eq_zero_of_not_mem`), and on that box it is bounded by the `α`-independent
constant supplied by `exists_bound_HkIntegrand_bump` at `α = 1`, `k = 6`, by the monotonicity in
`k` (`OpenPkg.HkIntegrand_mono_le`) and in `α` (`HkIntegrand_gam_mono`).  The squared norm is
then bounded with `HkSq_le_of_bound` (the `z`-support ends at `R = 1`). -/
theorem exists_HkNorm_bump_le :
    ∃ B : ℝ, 0 < B ∧ ∀ α ∈ Set.Ioc 0 1, ∀ k : ℕ, k ≤ 6 →
      Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump ≤ B := by
  obtain ⟨M, hMnn, hM⟩ := Work.FTS.StrongEps.exists_bound_HkIntegrand_bump 1 6
  refine ⟨max 1 (Real.sqrt (M * (Real.pi / 2) * (1 + 1))), lt_max_of_lt_left one_pos, ?_⟩
  intro α hα k hk
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hbound : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump z θ ≤ M := by
    intro z hz θ hθ
    refine le_trans (le_trans ?_ (Work.FTS.OpenPkg.HkIntegrand_mono_le 1 hk _ z θ)) (hM z θ)
    exact HkIntegrand_gam_mono hα0 hα1 k _ hθ
  have hfg : ∀ z θ : ℝ, 1 < z → Work.FTS.StrongEps.bump z θ = 0 := by
    intro z θ hz
    rw [Work.FTS.StrongEps.bump_eq_zero_iff]
    exact Or.inr (Or.inl (le_of_lt hz))
  have hsq := Work.Spaces.HkSq_le_of_bound α k Work.FTS.StrongEps.bump 1 M
    (by norm_num) hMnn hfg hbound
  rw [Work.Spaces.HkNorm]
  exact le_trans (Real.sqrt_le_sqrt hsq) (le_max_right _ _)

/-! ## Two elementary closure properties used by the assembly -/

/-- `ℋᵏ` is closed under multiplication by a constant, with no smoothness hypothesis: the
integrand is homogeneous of degree two (`Galerkin.Hilbert.HkIntegrand_const_mul`), and the
integral is linear for constants. -/
theorem HkMem_const_mul_gen {α : ℝ} {k : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => c * f z θ) := by
  obtain ⟨h1, h2⟩ := hm
  constructor
  · intro z hz
    have hfun : (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
      funext fun θ => Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α k c f z θ
    rw [hfun]
    exact (h1 z hz).const_mul _
  · have hfun : (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      rw [show (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
            = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ from
          funext fun θ => Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α k c f z θ]
      rw [MeasureTheory.integral_const_mul]
    rw [hfun]
    exact h2.const_mul _

/-- Scalar multiples of a `SmoothOpen` function are `SmoothOpen` (the open-quadrant class is
closed under `C^∞`-multiplication and contains the constants). -/
theorem smoothOpen_const_mul_gen (c : ℝ) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * F z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => c * F z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => c * F p.1 p.2)
    Work.FTS.EllipticEst.Q0
  have hF' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => F p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hF
  exact (contDiffOn_const (c := c) (s := Work.FTS.EllipticEst.Q0)).mul hF'

/-! ## The bound -/

/-- **`P₀` is bounded on `ℋᵏ`, uniformly in the parameter `α` and the order `k ≤ 6`.**

`P₀ f = f + (−c) • bump` with `c = L₁₂ f 0 / pzNorm`; the subadditivity of the norm on the open
quadrant (`HkNorm_add_fts`), its absolute homogeneity (`HkNorm_const_mul`), the proven zero-mode
bound `|L₁₂ f 0| ≤ 3 |f|_{ℋ⁴}` (`OpenPkg.l12zero_field`), the monotonicity `|f|_{ℋ⁴} ≤ |f|_{ℋ⁶}`
and the uniform bound `‖bump‖_{ℋᵏ} ≤ B` give the constant
`A = √2 (1 + 3 B / pzNorm)`. -/
theorem hkNorm_Pz_le :
    ∃ A : ℝ, 0 < A ∧ ∀ α ∈ Set.Ioc 0 1, ∀ k : ℕ, k ≤ 6 → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkNorm α k (Work.FTS.StrongEps.Pz f) ≤ A * Work.Spaces.HkNorm α 6 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨B, hBpos, hB⟩ := exists_HkNorm_bump_le
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := pzNorm_pos
  have hC₁nn : 0 ≤ C₁ := hC₁pos.le
  refine ⟨Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm), ?_, ?_⟩
  · have h1 : 0 < C₁ * B / Work.FTS.StrongEps.pzNorm :=
      div_pos (mul_pos hC₁pos hBpos) hpzpos
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  · intro α hα k hk f hfsm hm6
    have hα0 : 0 < α := hα.1
    have hα1 : α ≤ 1 := hα.2
    have hmemk : Work.Spaces.HkMem α k f :=
      Work.FTS.OpenPkg.HkMem_mono_open hfsm k hk hm6
    have hmem4 : Work.Spaces.HkMem α 4 f :=
      Work.FTS.OpenPkg.HkMem_mono_open hfsm 4 (by norm_num) hm6
    -- the zero-mode bound and the descent `ℋ⁶ → ℋ⁴`
    have hl12 : |Work.Construction.L12 f 0| ≤ C₁ * Work.Spaces.HkNorm α 4 f := by
      simpa only [Work.FTS.Nonlin.Xn] using hC₁ α hα0 hα1 f ⟨hfsm, hmem4⟩
    have hnorm46 : Work.Spaces.HkNorm α 4 f ≤ Work.Spaces.HkNorm α 6 f :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 4) (by norm_num) hm6
    have hnormk6 : Work.Spaces.HkNorm α k f ≤ Work.Spaces.HkNorm α 6 f :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := k) hk hm6
    have hcoefnn : 0 ≤ C₁ / Work.FTS.StrongEps.pzNorm := div_nonneg hC₁nn hpzpos.le
    -- the correction coefficient is controlled by the `ℋ⁶`-norm
    have hc_bound : |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
        ≤ (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 6 f := by
      rw [abs_div, abs_of_pos hpzpos]
      calc |Work.Construction.L12 f 0| / Work.FTS.StrongEps.pzNorm
          ≤ (C₁ * Work.Spaces.HkNorm α 4 f) / Work.FTS.StrongEps.pzNorm :=
            div_le_div_of_nonneg_right hl12 hpzpos.le
        _ = (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 f := by ring
        _ ≤ (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 6 f :=
            mul_le_mul_of_nonneg_left hnorm46 hcoefnn
    -- the correction profile
    have hbmem : Work.Spaces.HkMem α k Work.FTS.StrongEps.bump := hkMem_bump α k
    have hbnorm : Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump ≤ B := hB α hα k hk
    have hgbump : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry Work.FTS.StrongEps.bump)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun n => Work.FTS.StrongEps.smoothOpen_bump.forall n
    have hgsm : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry (fun z θ => (-(Work.Construction.L12 f 0
          / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun n => (smoothOpen_const_mul_gen (-(Work.Construction.L12 f 0
        / Work.FTS.StrongEps.pzNorm)) Work.FTS.StrongEps.smoothOpen_bump).forall n
    have hgmem : Work.Spaces.HkMem α k
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
      HkMem_const_mul_gen _ hbmem
    -- `Pz f` in the additive shape needed by the subadditivity lemma
    have hPz : Work.FTS.StrongEps.Pz f
        = fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ := by
      funext z θ
      rw [Work.FTS.StrongEps.Pz_apply]
      ring
    rw [hPz]
    have hadd := Work.FTS.EllipticEst.HkNorm_add_fts α k
      (fun n => hfsm.forall n) hgsm hmemk hgmem
    have hcm : Work.Spaces.HkNorm α k
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ)
        = |-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)|
          * Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump :=
      Work.FTS.EllipticEst.HkNorm_const_mul α k _ hgbump
    rw [hcm, abs_neg] at hadd
    calc Work.Spaces.HkNorm α k (fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f
            + |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
              * Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump) := hadd
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 6 f
            + (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 6 f * B) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hnormk6 ?_) (Real.sqrt_nonneg 2)
          exact mul_le_mul hc_bound hbnorm (Work.Spaces.HkNorm_nonneg _ _ _)
            (mul_nonneg hcoefnn (Work.Spaces.HkNorm_nonneg _ _ _))
      _ = Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.HkNorm α 6 f := by ring

end Work.FTS.StrongEps.PZeroAux
end
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

/-- Profiles in the self-similar variables `(z,θ)`, curried. -/
abbrev Fn : Type := ℝ → ℝ → ℝ

/-- The **radial factor** of the localised order-`6` datum:
`locG α L β (hLoc α) = locR α L β(z)·Γ(θ)`
(`Work.FTS.LocDataExt.locG_locR_Gam`). -/
abbrev locR (α L β : ℝ) : ℝ → ℝ := Work.FTS.LocDataExt.locR α L β

/-- The localised order-`6` datum of the strong-solution route (`Work.FTS.LocData6.locG6`). -/
abbrev locG6 (α L β : ℝ) : Fn := Work.FTS.LocData6.locG6 α L β

/-- The log-coordinate mollifier `J_ε` of the `ε`-scheme. -/
abbrev Jeps (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : Fn → Fn := Work.FTS.StrongEps.Jeps ρ ε

/-- The `sin θ cos²θ`-moment `F_* g z = ∫_θ g(z,θ) sin θ cos²θ dθ` of the elliptic layer. -/
abbrev Fstar : Fn → ℝ → ℝ := Work.Elliptic.Fstar


theorem locG6_eq_locR_mul (α L β : ℝ) :
    locG6 α L β = fun z θ => locR α L β z * Work.Spaces.Gam α θ :=
  Work.FTS.LocDataExt.locG_eq_locR_Gam α L β

end Work.FTS_LocDatum3a
end
end
