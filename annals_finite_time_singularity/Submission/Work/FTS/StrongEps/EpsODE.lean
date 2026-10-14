import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.RegPkgGal.R7d.chain_rule_along_curve
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.EpsODEDefs
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7e.support_strip_zL =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter
open scoped Topology Real

set_option maxHeartbeats 1600000

namespace Work.FTS.RegPkgGal.R7e

/-- **Finite speed of propagation in the fake time**, with the Lipschitz hypothesis for the
velocity field available only on `z > L`.  The support threshold is the usual `L·e^{aS}`, because
the backward characteristic starting above it never crosses `z = L`
(`R7e.curve_box_zL`). -/
theorem support_strip_zL {S a b c L : ℝ} (hS : 0 < S) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hL : 0 ≤ L)
    {F : ℝ → ℝ → ℝ → ℝ} {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ}
    (hFjoint : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Ioo (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S))))
    (hVjoint : ContinuousOn (fun p : ℝ × ℝ × ℝ => (Vz p.1 p.2.1 p.2.2, Vθ p.1 p.2.1 p.2.2))
      (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S))))
    (hVlipL : ∃ K : NNReal, ∀ τ ∈ Set.Icc 0 S, LipschitzOnWith K
      (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ))
      (Set.prod (Set.Ioi L) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hcscont : ContinuousOn (fun p : ℝ × ℝ × ℝ => cs p.1 p.2.1 p.2.2)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S))))
    (hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => F z θ s)
        (-(Vz z θ τ * Work.Spaces.Dz (fun z θ => F z θ τ) z θ
          + Vθ z θ τ * Work.Spaces.pth (fun z θ => F z θ τ) z θ
          + cs z θ τ * F z θ τ)) τ)
    (hVz0 : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → 0 ≤ Vz z θ τ)
    (hVza : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → Vz z θ τ ≤ a)
    (hVθb : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |Vθ z θ τ| ≤ b)
    (hVθ0 : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z 0 τ = 0)
    (hVθπ : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z (Real.pi / 2) τ = 0)
    (hcsc : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |cs z θ τ| ≤ c)
    (hInit : ∀ z θ : ℝ, L < z → 0 < θ → θ < Real.pi / 2 → F z θ 0 = 0) :
    ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L * Real.exp (a * S) < z → 0 < θ → θ < Real.pi / 2 →
      F z θ τ = 0 := by
  intro τ hτ z θ hz hθ0 hθπ
  obtain ⟨hτ0, hτS⟩ := hτ
  have hexp1 : (1:ℝ) ≤ Real.exp (a * S) := Real.one_le_exp (by positivity)
  have hzL : L < z := by nlinarith [hL, hexp1, hz]
  have hzpos : 0 < z := lt_of_le_of_lt (by nlinarith [hL, hexp1]) hz
  rcases eq_or_lt_of_le hτ0 with h0 | hpos
  · rw [← h0]
    exact hInit z θ hzL hθ0 hθπ
  obtain ⟨K, hK⟩ := hVlipL
  have hK0 : (0:ℝ) ≤ (K:ℝ) := K.2
  -- the backward characteristic, together with its a priori box
  obtain ⟨α, hα0', hαode, hbox⟩ := curve_box_zL (K := K) hS ha hb hL hK hVjoint hVz0 hVza hVθb
    hVθ0 hVθπ hpos hτS hz hθ0 hθπ
  have hzm_pos : 0 < z * Real.exp (-(a * τ)) := by positivity
  have hθm_pos : 0 < θ * Real.exp (-((K:ℝ) * τ)) := by positivity
  have hθM_lt : Real.pi / 2 - (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * τ)) < Real.pi / 2 := by
    have h1 : 0 < (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * τ)) :=
      mul_pos (by linarith) (Real.exp_pos _)
    linarith
  -- the composite and its exponential-factor equation
  set G : ℝ → ℝ := fun s => F (α s).1 (α s).2 (τ - s) with hG
  set csG : ℝ → ℝ := fun s => cs (α s).1 (α s).2 (τ - s) with hcsG
  have hderiv : ∀ t ∈ Set.Ioo 0 τ, HasDerivAt G (csG t * G t) t := by
    intro t ht
    obtain ⟨hb1, hb2⟩ := hbox t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hz_t : 0 < (α t).1 := lt_of_lt_of_le hzm_pos hb1.1
    have hθ_t : 0 < (α t).2 := lt_of_lt_of_le hθm_pos hb2.1
    have hθ_t' : (α t).2 < Real.pi / 2 := lt_of_le_of_lt hb2.2 hθM_lt
    have hτt : 0 < τ - t := by linarith [ht.2]
    have hτtS : τ - t ≤ S := by linarith [ht.1, hτS]
    have hτtS' : τ - t < S := by linarith [ht.1, hτS]
    have hFd : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2)
        ((α t).1, (α t).2, τ - t) := by
      have hmem : ((α t).1, (α t).2, τ - t) ∈
          Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Ioo (0:ℝ) (Real.pi/2)) (Set.Icc (0:ℝ) S)) :=
        Set.mem_prod.mpr ⟨hz_t,
          Set.mem_prod.mpr ⟨⟨hθ_t, hθ_t'⟩, ⟨le_of_lt hτt, hτtS⟩⟩⟩
      have hnhds : Set.prod (Set.Ioi (0:ℝ))
          (Set.prod (Set.Ioo (0:ℝ) (Real.pi/2)) (Set.Icc (0:ℝ) S)) ∈
          𝓝 ((α t).1, (α t).2, τ - t) :=
        prod_mem_nhds (isOpen_Ioi.mem_nhds hz_t)
          (prod_mem_nhds (isOpen_Ioo.mem_nhds ⟨hθ_t, hθ_t'⟩) (Icc_mem_nhds hτt hτtS'))
      exact (hFjoint.differentiableOn (by norm_num)).differentiableAt hnhds
    have hEq' : HasDerivAt (fun s => F (α t).1 (α t).2 s)
        (-(Vz (α t).1 (α t).2 (τ - t) * Work.Spaces.Dz (fun z θ => F z θ (τ - t)) (α t).1 (α t).2
          + Vθ (α t).1 (α t).2 (τ - t) * Work.Spaces.pth (fun z θ => F z θ (τ - t)) (α t).1 (α t).2
          + cs (α t).1 (α t).2 (τ - t) * F (α t).1 (α t).2 (τ - t))) (τ - t) :=
      hEq (α t).1 (α t).2 (τ - t) hz_t hθ_t hθ_t' hτt hτtS
    have hα' : HasDerivAt α
        (-((α t).1 * Vz (α t).1 (α t).2 (τ - t)), -(Vθ (α t).1 (α t).2 (τ - t))) t :=
      (hαode t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hcr := Work.FTS.RegPkgGal.R7d.chain_rule_along_curve (Vz := Vz) (Vθ := Vθ) (cs := cs)
      (α := α) (τ₀ := τ) (t := t) hFd hα' hEq'
    simpa [hG, hcsG] using hcr
  have hGcont : ContinuousOn G (Set.Icc (0:ℝ) τ) := by
    have hαcont : ContinuousOn α (Set.Icc (0:ℝ) τ) := fun t ht => (hαode t ht).continuousWithinAt
    have hγ : ContinuousOn (fun s : ℝ => ((α s).1, (α s).2, τ - s)) (Set.Icc (0:ℝ) τ) :=
      ((continuous_fst.comp_continuousOn hαcont).prodMk
        ((continuous_snd.comp_continuousOn hαcont).prodMk
          (continuousOn_const.sub continuousOn_id)))
    have hmap : MapsTo (fun s : ℝ => ((α s).1, (α s).2, τ - s)) (Set.Icc (0:ℝ) τ)
        (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Ioo (0:ℝ) (Real.pi/2)) (Set.Icc (0:ℝ) S))) := by
      intro s hs
      obtain ⟨hb1, hb2⟩ := hbox s hs
      have hz_s : 0 < (α s).1 := lt_of_lt_of_le hzm_pos hb1.1
      have hθ_s : 0 < (α s).2 := lt_of_lt_of_le hθm_pos hb2.1
      have hθ_s' : (α s).2 < Real.pi / 2 := lt_of_le_of_lt hb2.2 hθM_lt
      exact Set.mem_prod.mpr ⟨hz_s, Set.mem_prod.mpr ⟨⟨hθ_s, hθ_s'⟩,
        ⟨by linarith [hs.2], by linarith [hs.1, hτS]⟩⟩⟩
    have := hFjoint.continuousOn.comp hγ hmap
    simpa [hG, Function.comp_def] using this
  have hcsGcont : ContinuousOn csG (Set.Icc (0:ℝ) τ) := by
    have hαcont : ContinuousOn α (Set.Icc (0:ℝ) τ) := fun t ht => (hαode t ht).continuousWithinAt
    have hγ : ContinuousOn (fun s : ℝ => ((α s).1, (α s).2, τ - s)) (Set.Icc (0:ℝ) τ) :=
      ((continuous_fst.comp_continuousOn hαcont).prodMk
        ((continuous_snd.comp_continuousOn hαcont).prodMk
          (continuousOn_const.sub continuousOn_id)))
    have hmap : MapsTo (fun s : ℝ => ((α s).1, (α s).2, τ - s)) (Set.Icc (0:ℝ) τ)
        (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi/2)) (Set.Icc (0:ℝ) S))) := by
      intro s hs
      obtain ⟨hb1, hb2⟩ := hbox s hs
      have hz_s : 0 < (α s).1 := lt_of_lt_of_le hzm_pos hb1.1
      have hθ_s : 0 < (α s).2 := lt_of_lt_of_le hθm_pos hb2.1
      have hθ_s' : (α s).2 < Real.pi / 2 := lt_of_le_of_lt hb2.2 hθM_lt
      exact Set.mem_prod.mpr ⟨hz_s, Set.mem_prod.mpr ⟨⟨le_of_lt hθ_s, le_of_lt hθ_s'⟩,
        ⟨by linarith [hs.2], by linarith [hs.1, hτS]⟩⟩⟩
    have := hcscont.comp hγ hmap
    simpa [hcsG, Function.comp_def] using this
  -- the initial point of the characteristic lies above `L`, so `F` vanishes there
  have hGτ : G τ = 0 := by
    obtain ⟨hb1, hb2⟩ := hbox τ ⟨le_of_lt hpos, le_rfl⟩
    have hzτ : L < (α τ).1 := by
      have h1 : z * Real.exp (-(a * τ)) ≤ (α τ).1 := hb1.1
      have h2 : L * Real.exp (a * S) * Real.exp (-(a * τ)) < z * Real.exp (-(a * τ)) :=
        mul_lt_mul_of_pos_right hz (Real.exp_pos _)
      have hexp3 : Real.exp (a * S) * Real.exp (-(a * τ)) = Real.exp (a * (S - τ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h3 : L * Real.exp (a * S) * Real.exp (-(a * τ)) = L * Real.exp (a * (S - τ)) := by
        rw [mul_assoc, hexp3]
      have h4 : L ≤ L * Real.exp (a * (S - τ)) := by
        have h5 : (1:ℝ) ≤ Real.exp (a * (S - τ)) := Real.one_le_exp (by nlinarith [ha, hτS])
        nlinarith [hL, h5]
      linarith
    have hθτ : 0 < (α τ).2 := lt_of_lt_of_le hθm_pos hb2.1
    have hθτ' : (α τ).2 < Real.pi / 2 := lt_of_le_of_lt hb2.2 hθM_lt
    have hsub : τ - τ = 0 := by ring
    show F (α τ).1 (α τ).2 (τ - τ) = 0
    rw [hsub]
    exact hInit _ _ hzτ hθτ hθτ'
  have hfinal := Work.FTS.RegPkgGal.R7d.exp_ode_const hpos hderiv hGcont hcsGcont hGτ
  simpa [hG, hcsG, hα0'] using hfinal

end Work.FTS.RegPkgGal.R7e
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsODE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## E2 — existence for the scheme -/

/-- **E2 — existence for the `ε`-scheme** (Galerkin/energy route).

*The mathematics.*  The scheme is `∂_τ g = J_ε[𝓛(J_ε g) + 𝓡(Ψ(J_ε g), J_ε g)]` in the space of
profiles: one approximates `g` by a finite-dimensional (Galerkin) family, where the projected ODE
is well-posed by Picard–Lindelöf, uses the **ε-level energy inequalities of the projected system**
to obtain a uniform bound in the discretisation parameter, extracts a limit by compactness
(`exists_locUnif_subseq_of_uniform_H6`, `LocUnif/`) and identifies it with an `ε`-solution on
`[0,T]` (no blow-up can occur before `T`: the a-priori bound is exactly what rules it out).

**There is no single-norm Picard.**  The right-hand side contains the unbounded `z∂_z`
(the design's `𝓛_Γ^T`), so `‖rhs u − rhs v‖_{ℋ⁴} ≲ ‖u − v‖_{ℋ⁵}` and no `ℋ⁴`-contraction exists;
and the mollifier does **not** recover the lost derivative `ε`-uniformly — `HkSq_Jeps_succ_le` is
**false** (`NOTES_HkSq_Jeps_succ_le_FALSE.md`), so the `ε^{-1}`-gain route is closed.  See
`NOTES.md` §"third stretch" and §"the `E2` hypothesis".

*Statement note (finding of this stretch).*  `hAp : EpsAprioriBdd` bounds **genuine `ε`-solutions
only**, so it cannot be consumed by the Galerkin argument, which needs the bound for the
*approximants*; that bound must come from the projected system's own energy estimates (the
ε-level analogue of the frozen `Apriori.galerkin_bound_explicit`).  The statement below therefore
records the design's target, and the honest hypothesis (energy data for the projected system) is
the one a proof will need; see `NOTES.md` for the frozen template
(`Work.FTS.Galerkin.{GalerkinODE, Existence, ODEApply, Compactness, Limit}`).

`IsEpsSol` itself is the honest *pointwise* statement (a `HasDerivWithinAt` of the `τ`-slice at
every point of the open quadrant); the limit of the approximants is transferred to it because the
mollified right-hand side is continuous and the identity holds a.e.

**NOT proved, and refuted in this shape.**  On the *un-projected* scheme the class-`C`/`axis`
invariant cannot be preserved: the scheme's right-hand side is *minus* the paper's stationary
residual, so `profRHS(0)(z,θ)/z → −4αΓ(θ)/c < 0`, which violates `axis` for every small `τ > 0`
(`EpsLocalPStar/StatResidual.lean`, `profRHS_eq_neg_dynLHS`, `sorry`-free; see `NOTES_session16.md`
§7).  The `sorry` on the theorem below is therefore a **record of a false statement**, not a gap to
be filled as it stands: the E2a re-design is the projected small-ball shape (`EpsLocalPStar`,
`EpsLocalPSmall`, `StarPkgo2`), and `EpsE2`'s proof (`EpsE2.lean`) is conditional on it. -/
theorem IsEpsSol.local {α ε Ce : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    (hρ : IsSmoothKernel ρ) (hε : 0 < ε)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) :
    ∀ M : ℝ, 0 ≤ M → ∃ δ : ℝ, 0 < δ ∧ ∀ h₀ : Fn, EpsDatum α ρ ε h₀ →
      Work.FTS.StrongGlobal.Xn6 α h₀ ≤ M →
      ∃ h : Fam, IsEpsSol α ρ ε δ Φs E h₀ h ∧ EpsReg α ρ ε δ h ∧
        ∀ τ ∈ Set.Icc 0 δ, Work.FTS.StrongGlobal.Xn6 α (slice h τ) ≤ 2 * M + 1 := by
  sorry

/-! **E2 (continuation)**: restart `IsEpsSol.local` every `δ(M)` and concatenate; the glued
solution stays in `EpsReg`, so `hAp` applies to it and keeps every restart datum at `Xn6 ≤ M`.
-/
-- **E2 is PROVED** — but not here: its proof consumes `EpsGlue` (`EpsGlue.lean`), which imports
-- this module for the very definitions below, so the declaration has been moved to
-- `Submission/Work/FTS/StrongEps/EpsE2.lean` (module `Submission.Work.FTS.StrongEps.EpsE2`),
-- where it carries the same fully qualified name `Work.FTS.StrongEps.IsEpsSol.exists_of_aprioriH`
-- and is `sorry`-free.  Import that module to use E2.  (Importing both would be a name clash.)

/-! *Note (added after the v2 ruling; the hypothesis `0 ≤ M` was missing).*  For `M < 0` the
statement above is **not provable**: `EpsAprioriBddH` then says that every regular `ε`-solution on
`[0,T']` (`0 < T' ≤ T`) has `Xn6 ≤ M < 0`, while `Xn6 = HkNorm ≥ 0`, so `hAp` is equivalent to
"there is no regular `ε`-solution on `[0,T']`" — contradicted by the conclusion, which *asserts*
one exists with `Xn6 ≤ M`.  So `0 ≤ M` is part of the honest statement (in E4 the value is
`M = K e^{KT} ≥ 0`).

**The continuation half is `Submission/Work/FTS/StrongEps/EpsGlue.lean`**
(`Work.FTS.StrongEps.EpsGlue`), which proves exactly this theorem with the conclusion of
`IsEpsSol.local` (item **E2a**) in place of `hρ`/`hε`/`hEll`; instantiating it with the proved E2a
is all that separates this statement from a proof. -/

/-! ## E3 — the `ε`-energy inequality

**E3 is `Submission/Work/FTS/StrongEps/EpsE3.lean`** (`Work.FTS.StrongEps.EpsSol_IP6_energy_deriv_le`,
`sorry`-free), with the ε-level pairing estimate `Work.FTS.StrongEps.EpsSol_IP6_pair_le` as its
analytic core.  It is stated for the energy

  `e(τ) = IP6 1 … 1 α (slice (Jfam ρ ε g) τ) (slice (Jfam ρ ε g) τ)`

of the **mollified** family — the pairing and the profile for which the frozen level-six clause work
(`H6Lin`, `H6Pair`, `L6Ctx`) is stated; `Sq6 = HkSq α 6` and `IP6 1 … 1 · ·` are equivalent on the
`HQo α 6`-class (`IP6_lo_coeffs` one way, `IP6_cs_coeffs` the other).  The theorem's inputs are
exactly (i) the external level-six row `H6Pair`, (ii) the level-six context `L6Ctx` for the
mollified family at every fake time, (iii) the regularity data of the scheme's right-hand side
`smoothness/HkMem α 7 (epsW)/HkMem α 6 (epsRHS)` together with the one commutator-control clause
`ε‖epsW‖₇‖h‖₆ ≤ K7(1+e)`, and (iv) the **ε-level energy identity** `hid` (the `IP6`-analogue of
`StrongPersist.H6EnergyDeriv`, i.e. a statement about `IsEpsSol` and the slot derivatives of the
slices along the flow, not a bound).  The earlier statement below — in `HkSq`-terms, for the
*unmollified* slice, with the a-priori bounds `hCC`/`hbd`/`hmem` and the elliptic hypothesis `hEll`
as inputs — is recovered from the proved form by two further steps, both now spelled out here
because they are *not* part of E3's analytic content:

* the **transfer of the profile**: `HkSq α 6 (slice g τ) ≤ C (1 + IP6 … (J_ε (slice g τ)) (J_ε (slice g τ)))`,
  which is the approximation-of-the-identity `HkSq α 6 (f − J_ε f) ≤ (C₀ε)² HkSq α 7 f`
  (`HkSq_Jeps_sub_le`) together with `(a+b)² ≤ 2a² + 2b²` and `IP6_lo_coeffs`; its hypothesis is the
  same `ε·‖slice g τ‖₇²`-control as `h7`;
* the identification of the *mollified* energy identity with the scheme's (this is where a smooth
  kernel is used: the frozen clauses need `SmoothOpen` of the paired profile, and
  `Jeps_contDiffOn` provides it for `J_ε` of an `L²`-profile).

Both are stated in `NOTES.md` §"the `E3` chain", with the exact clauses they consume. -/

/-! ## E4 — the bootstrap -/


end Work.FTS.StrongEps
end
end
