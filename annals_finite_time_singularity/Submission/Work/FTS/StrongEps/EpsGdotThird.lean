/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsGdotThird.lean` — the `ℋ³`-membership and bound of `gdot` at
the `ε`-level

The requested theorem `Work.FTS.StrongEps.EpsGdotThird` is the `ε`-level counterpart of the level
three estimate in the form used by E5's `dbd` brick: for an `ε`-solution `g` of the scheme on
`[0,T]` whose *mollified* slices have `ℋ⁴`-size `≤ C₀α²` and `ℋ⁶`-size `≤ B`, the fake-time
derivative `gdot g τ` is `ℋ³`-honest with a size depending only on the data, uniformly for
`τ ∈ (0,T)`.

## The route, and the two hypothesis groups it needs

At an interior fake time, `IsEpsSol.gdot_eq` (`Gdot.lean`) identifies, on the open quadrant
`Qd = Ioi 0 ×ˢ Ioo 0 (π/2)`,

  `gdot g τ = epsRHS α ρ ε Φs E g τ = J_ε (epsWU α ρ ε Φs E g τ)`

(`epsRHS_eq_Jeps_epsW`, `rfl`), and `HkMem_congr_Q0` / `HkSq_congr_open`
(`EllipticEst/Cert/GbarSin/HkMem_congr_Q0.lean`, `EllipticEst/HkSq_congr_open.lean`) show that both
conjuncts of the conclusion are statements about the *open quadrant only*.  The two sides of
`epsW` are the profiles whose level-three estimates `L3Data.lin` / `L3Data.rhs` supply (their
`H6Adm`- and `Ell6Ctx`-data are available at the *mollified* slice `J_ε g_τ` through the bridges
below).  What remains is the `ℋ³`-boundedness of the *mollifier* on the profile `epsW`, and this is
where the statement as written does not carry the hypotheses of the theorems on disk:

* every theorem that produces `HkMem α k (J_ε f)` or `HkSq α k (J_ε f)` — `HkMem_Jeps`,
  `HkSq_Jeps_le`, `HkSq_Jeps_step_le` and the whole `HkSqAux/` chapter — is stated for
  `α ∈ Set.Ioc 0 1`, the range in which the two weight comparisons `Wt_shift_le` /
  `wTheta_shift_ge_le` are available; the hypothesis `hα : α ∈ Set.Ioc 0 α₂` with
  `L3Data.pos : 0 < α₂` gives no upper bound on `α` (in the intended instantiation the scheme runs
  at `pExp α = 3α ≤ 1`, cf. `Regularity.pExp_le_one`);
* those same theorems take `∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad` for the *input*
  `f`, i.e. `C^∞` of `epsW` on the quadrant, and their proofs consume it twice — for the slot
  commutation `mixed j i (J_ε f) = J_ε (mixed j i f)` that produces the pointwise bound, and for
  the a.e. strong measurability / local integrability of `f` that the Jensen and Tonelli steps
  need.  `EpsReg`/`EpsDatum` supply only joint `C¹` of the family plus `SmoothOpen` of the
  *unmollified* slice, `HkMem α 6`, and `ClassC` of the *mollified* slice — nothing about the
  scheme's right-hand side.  The sibling statement that proves the same conclusion for the limit
  family, `EpsLimDbd_aux` (`EpsLimDbdFixed.lean`), carries the corresponding clauses explicitly
  (`hlinc : ContDiffOn ℝ 3 (uncurry (linPart α (slice g τ))) Q0`, `hrhsc : …(dynRHS …)…`), as do
  `StrongPersist/Dbd.lean`, `StrongPersist/S6Final.lean` and `GalLimit/Defs.EqExtra`
  (`HQo α 4 (dynLin α g τ + dynRHS α Φ g τ)`);
* the *additivity* of `HkSq`/`HkMem` over the two sides `linPart α (J_ε g_τ)` and `gRHS …`
  (`HkAddFin`, `CoercivityFix.Assembly.HkMem_add_open`, `HkSq_add_le_of_pointwise`) is stated for
  `ContDiffOn`-regular summands (or for a pointwise slot inequality), so it too needs regularity of
  the summands that `L3Data` — a membership *and* norm-size statement — does not provide.

## What is proved here

The bridges that turn the scheme's own hypotheses into the inputs of `L3Data`: the `ClassC`-level
counterparts of `ell6Ctx_of_classC` and of the `MuLamOK` clause.  They are needed by *every* route
to the statement, including the one that adds the missing clauses above.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsODE
import Submission.Work.FTS.StrongEps.Gdot
import Submission.Work.FTS.StrongEps.EpsLimDbdFixed
import Submission.Work.FTS.StrongPersist.L3DataFinal
import Submission.Work.FTS.StrongEps.HkSq_Jeps_le
import Submission.Work.FTS.StrongPersist.HkAddFin
import Submission.Work.FTS.OpenPkg.Basic

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

/-- **Bridge 1, at the `ε`-scheme's mollified slice.**  Every slice `J_ε g_τ` of the mollified
family is in `H6Adm`, from the `ClassC` clause of `EpsDatum`. -/
theorem H6Adm_Jfam {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε T τ : ℝ} {g : Fam}
    (hreg : EpsReg α ρ ε T g) (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    Work.FTS.StrongPersist.H6Adm α (slice (Jfam ρ ε g) τ) := by
  have hC : Work.FTS.ClassC.ClassC α (slice (Jfam ρ ε g) τ) := (hreg.2 τ hτ).2.2
  refine H6Adm_of_classC_of_eqzero hC ?_
  intro z θ hzq
  exact Jeps_eq_zero ρ ε (slice g τ) (fun hc => hzq ⟨hc.1, hc.2⟩)

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
