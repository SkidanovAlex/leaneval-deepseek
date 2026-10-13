import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.Slots.v2_SlotJetsTendsto
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_lip_approx
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_tendsto
import Submission.Work.FTS_RegExport.RXT.SysAux.pertSlot_contDiffOn
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXT0.SJC.slotJetsTendsto
import Submission.Work.FTS_RegExport.RXT0.SJC.slotJetLipschitzApprox
import Submission.Work.FTS_RegExport.RXT0.SJC.slotJetContinuousOn
import Submission.Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn
import Submission.Work.FTS_RegExport.RXT.Sys.slot_tau_cont_alpha

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.slotJetsJointCont` — joint continuity of the slot jets of the residual

For a family `g` satisfying the RX-T0 hypothesis bundle, the mixed jets `D_z^jD_θ^i`, `j + i ≤ 2`,
of the three transport slots `𝒱(Φ̃(τ))`, `ℛ(Φ̃(τ))`, `𝒰(Φ̃(τ))/sin 2θ` of the residual
`Φ̃(τ) = PhiTil (pExp α) (g(τ)) (E (g(τ)))` are jointly continuous on the slab
`z > 0`, `θ ∈ (0,π/2)`, `τ ∈ [0,S]`.

The proof splits the three variables:

* **in `τ`** — the limit slots are Lipschitz in `τ` (uniformly in `(z,θ)`): the class-`C`
  approximating sequences `gn` of the `LimApprox` clause of `DynOK'` have slot jets Lipschitz in
  `τ` (`SJC.slotJetLipschitzApprox`, the jet-level `pertSlot_lip_approx`) and converge pointwise to
  the slot jets of the limit (`SJC.slotJetsTendsto`), so `Sys.lipschitz_of_approx` transfers the
  Lipschitz bound to the limit (`slotJetsLipschitzOnHorizon`);
* **in `(z,θ)` at frozen `τ`** — the residual is `C³` on the open quadrant
  (`Sys.pert_tilde_contDiffOn`), whence the slot jets of order `≤ 2` are continuous
  (`SJC.slotJetContinuousOn`);
* the two bounds are glued by the elementary ε-argument `jointContOnSlab_of_lipschitz`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)
open Work.FTS.FinalV2 (Sol DynOK' EllLimOK3)
open Work.FTS.Final (EllPkgGo)
open Work.FTS.ClassC (ClassC EllPkgK)

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {α Ce C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

/-- **Slab assembly.** A function `(z,θ,τ) ↦ F z θ τ` on the slab
`(0,∞) × (0,π/2) × [0,S]` is jointly continuous as soon as it is Lipschitz in `τ` (with
constant `K ≥ 0`, valid on the whole open quadrant) and its `(z,θ)`-slice at every `τ ∈ [0,S]`
is continuous on the open quadrant.

The point of the statement is that no *uniform* regularity in `τ` of the `(z,θ)`-slices is
needed: the `τ`-increment is estimated at the point itself (`hLip`), the spatial increment at the
frozen time `p.2.2` (`hspat`). -/
theorem jointContOnSlab_of_lipschitz {S K : ℝ} {F : ℝ → ℝ → ℝ → ℝ} (hK : 0 ≤ K)
    (hLip : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |F z θ τ - F z θ τ'| ≤ K * |τ - τ'|)
    (hspat : ∀ τ ∈ Set.Icc (0:ℝ) S,
      ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 τ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
  intro p hp
  obtain ⟨hz, hθ, hτ⟩ := hp
  obtain ⟨hθ0, hθ1⟩ := hθ
  obtain ⟨hτ0, hτS⟩ := hτ
  -- ## the `τ`-increment is infinitesimal
  have hgtend : Filter.Tendsto (fun q : ℝ × ℝ × ℝ => K * |q.2.2 - p.2.2|)
      (𝓝[Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)] p) (𝓝 0) := by
    have h1 : Filter.Tendsto (fun q : ℝ × ℝ × ℝ => q.2.2)
        (𝓝[Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)] p)
        (𝓝 p.2.2) :=
      (continuous_snd.snd.tendsto p).mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto (fun q : ℝ × ℝ × ℝ => q.2.2 - p.2.2)
        (𝓝[Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)] p)
        (𝓝 (p.2.2 - p.2.2)) :=
      h1.sub_const p.2.2
    have h3 : Filter.Tendsto (fun q : ℝ × ℝ × ℝ => |q.2.2 - p.2.2|)
        (𝓝[Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)] p) (𝓝 0) := by
      simpa using h2.abs
    simpa using h3.const_mul K
  -- ## the `τ`-difference tends to `0`
  have hdiff : Filter.Tendsto (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2 - F q.1 q.2.1 p.2.2)
      (𝓝[Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)] p) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmin : Filter.Tendsto (fun q : ℝ × ℝ × ℝ =>
        min (K * |q.2.2 - p.2.2|) ‖F q.1 q.2.1 q.2.2 - F q.1 q.2.1 p.2.2‖)
        (𝓝[Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)] p) (𝓝 0) :=
      squeeze_zero (fun q => le_min (mul_nonneg hK (abs_nonneg _)) (norm_nonneg _))
        (fun q => min_le_left _ _) hgtend
    refine hmin.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    obtain ⟨hqτ, -⟩ := hq.2.2
    have h := hLip q.1 q.2.1 hq.1 hq.2.1.1 hq.2.1.2 q.2.2 ⟨hqτ, hq.2.2.2⟩ p.2.2 ⟨hτ0, hτS⟩
    rw [min_eq_right]
    simpa [Real.norm_eq_abs] using h
  -- ## the `p.2.2`-slice is continuous at `p`
  have hsp : ContinuousWithinAt (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) p := by
    have hQ : Set.MapsTo (fun q : ℝ × ℝ × ℝ => (q.1, q.2.1))
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))
        (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)) :=
      fun q hq => ⟨hq.1, hq.2.1⟩
    have hgc : ContinuousWithinAt (fun q : ℝ × ℝ × ℝ => (q.1, q.2.1))
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) p :=
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousWithinAt
    have hfc : ContinuousWithinAt (fun q : ℝ × ℝ => F q.1 q.2 p.2.2)
        (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)) (p.1, p.2.1) :=
      hspat p.2.2 ⟨hτ0, hτS⟩ (p.1, p.2.1) ⟨hz, hθ0, hθ1⟩
    have hcomp := hfc.comp (f := fun q : ℝ × ℝ × ℝ => (q.1, q.2.1)) (x := p) hgc hQ
    simpa [Function.comp_def] using hcomp
  -- ## add the two pieces
  have hsum := hsp.tendsto.add hdiff
  have hfun : (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 p.2.2 + (F q.1 q.2.1 q.2.2 - F q.1 q.2.1 p.2.2))
      = fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2 := by
    funext q; ring
  rw [hfun] at hsum
  have hgoal : Filter.Tendsto (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2)
      (𝓝[Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)] p)
      (𝓝 (F p.1 p.2.1 p.2.2)) := by
    simpa only [add_zero] using hsum
  exact hgoal

/-- **The limit slot jets are Lipschitz in the fake time.** The three slots of the residual
`Φ̃(τ) = PhiTil (pExp α) (slice g τ) (E (slice g τ))` have mixed jets of order `≤ 2` which are
Lipschitz in `τ` on every horizon `[0,S]`, with a constant that is uniform in `(z,θ)` on the
open quadrant.  Obtained by passing to the limit in `SJC.slotJetLipschitzApprox` along the
class-`C` approximating families of the `LimApprox` clause, using the pointwise jet convergence
`SJC.slotJetsTendsto` and `Sys.lipschitz_of_approx`. -/
theorem slotJetsLipschitzOnHorizon
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, ClassC (pExp α) u →
      EllPkgGo (pExp α) Ce u (E u) ∧ EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E)
    (hOK : DynOK' (pExp α) C₀ Φs E g) {S : ℝ} (hS : 0 < S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (|Work.Spaces.mixed j i (Work.Construction.Rop (pExp α)
            (Work.Construction.PhiTil (pExp α) (slice g τ) (E (slice g τ)))) z θ
          - Work.Spaces.mixed j i (Work.Construction.Rop (pExp α)
            (Work.Construction.PhiTil (pExp α) (slice g τ') (E (slice g τ')))) z θ|
        ≤ K * |τ - τ'|) ∧
      (|Work.Spaces.mixed j i (Work.Construction.Vop
            (Work.Construction.PhiTil (pExp α) (slice g τ) (E (slice g τ)))) z θ
          - Work.Spaces.mixed j i (Work.Construction.Vop
            (Work.Construction.PhiTil (pExp α) (slice g τ') (E (slice g τ')))) z θ|
        ≤ K * |τ - τ'|) ∧
      (|Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α)
            (Work.Construction.PhiTil (pExp α) (slice g τ) (E (slice g τ))) z θ
            / Real.sin (2 * θ)) z θ
          - Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α)
            (Work.Construction.PhiTil (pExp α) (slice g τ') (E (slice g τ'))) z θ
            / Real.sin (2 * θ)) z θ| ≤ K * |τ - τ'|) := by
  obtain ⟨gn, B, L, hApprox, hLipC, hJetC, -⟩ := hOK.2 S hS
  obtain ⟨K, hK0, hK⟩ := Work.FTS_RegExport.RXT0.SJC.slotJetLipschitzApprox (E := E)
    hα hα13 hEll hS (fun n τ hτ => (hApprox n τ hτ).1) hLipC
  refine ⟨K, hK0, ?_⟩
  intro τ hτ τ' hτ' j i hji z θ hz hθ hθ2
  refine ⟨?_, ?_, ?_⟩
  · -- the `ℛ`-slot
    exact Work.FTS_RegExport.RXT.Sys.lipschitz_of_approx (K := K)
      (fun n τ hτ τ' hτ' => (hK n τ hτ τ' hτ' j i hji z θ hz hθ hθ2).1)
      (fun σ hσ => (Work.FTS_RegExport.RXT0.SJC.slotJetsTendsto hα hα13 hEll hEL3 hOK hS
        hApprox hJetC hσ j i hji z θ hz hθ hθ2).1)
      τ hτ τ' hτ'
  · -- the `𝒱`-slot
    exact Work.FTS_RegExport.RXT.Sys.lipschitz_of_approx (K := K)
      (fun n τ hτ τ' hτ' => (hK n τ hτ τ' hτ' j i hji z θ hz hθ hθ2).2.1)
      (fun σ hσ => (Work.FTS_RegExport.RXT0.SJC.slotJetsTendsto hα hα13 hEll hEL3 hOK hS
        hApprox hJetC hσ j i hji z θ hz hθ hθ2).2.1)
      τ hτ τ' hτ'
  · -- the `𝒰/sin 2θ`-slot
    exact Work.FTS_RegExport.RXT.Sys.lipschitz_of_approx (K := K)
      (fun n τ hτ τ' hτ' => (hK n τ hτ τ' hτ' j i hji z θ hz hθ hθ2).2.2)
      (fun σ hσ => (Work.FTS_RegExport.RXT0.SJC.slotJetsTendsto hα hα13 hEll hEL3 hOK hS
        hApprox hJetC hσ j i hji z θ hz hθ hθ2).2.2)
      τ hτ τ' hτ'

theorem slotJetsJointCont {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∀ j i : ℕ, j + i ≤ 2 →
      (ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i
        (fun z θ => Work.Construction.Vop
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice g p.2.2) (E (Work.FTS.Galerkin.slice g p.2.2))) z θ)
        p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))) ∧
      (ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i
        (fun z θ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice g p.2.2) (E (Work.FTS.Galerkin.slice g p.2.2))) z θ)
        p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))) ∧
      (ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i
        (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
            (Work.FTS.Galerkin.slice g p.2.2) (E (Work.FTS.Galerkin.slice g p.2.2))) z θ
          / Real.sin (2 * θ)) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))) := by
  intro S hS j i hji
  obtain ⟨K, hK0, hlip⟩ := slotJetsLipschitzOnHorizon (α := α) (C₀ := C₀) (Ce := Ce)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hOK hS
  have hX : ∀ τ ∈ Set.Icc (0:ℝ) S, ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.Construction.PhiTil (pExp α) (slice g τ) (E (slice g τ)) z θ))
      Work.FTS.EllipticEst.Q0 :=
    fun τ hτ => Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn hα hα13 hEL3 hOK τ hτ.1
  refine ⟨?_, ?_, ?_⟩
  · refine jointContOnSlab_of_lipschitz (K := K)
      (F := fun z θ τ => Work.Spaces.mixed j i (Work.Construction.Vop
        (Work.Construction.PhiTil (pExp α) (slice g τ) (E (slice g τ)))) z θ) hK0 ?_ ?_
    · intro z θ hz hθ hθ2 τ hτ τ' hτ'
      exact (hlip τ hτ τ' hτ' j i hji z θ hz hθ hθ2).2.1
    · intro τ hτ
      exact (Work.FTS_RegExport.RXT0.SJC.slotJetContinuousOn (α := pExp α) (hX := hX τ hτ)
        j i hji).1
  · refine jointContOnSlab_of_lipschitz (K := K)
      (F := fun z θ τ => Work.Spaces.mixed j i (Work.Construction.Rop (pExp α)
        (Work.Construction.PhiTil (pExp α) (slice g τ) (E (slice g τ)))) z θ) hK0 ?_ ?_
    · intro z θ hz hθ hθ2 τ hτ τ' hτ'
      exact (hlip τ hτ τ' hτ' j i hji z θ hz hθ hθ2).1
    · intro τ hτ
      exact (Work.FTS_RegExport.RXT0.SJC.slotJetContinuousOn (α := pExp α) (hX := hX τ hτ)
        j i hji).2.1
  · refine jointContOnSlab_of_lipschitz (K := K)
      (F := fun z θ τ => Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (pExp α)
        (Work.Construction.PhiTil (pExp α) (slice g τ) (E (slice g τ))) z θ
        / Real.sin (2 * θ)) z θ) hK0 ?_ ?_
    · intro z θ hz hθ hθ2 τ hτ τ' hτ'
      exact (hlip τ hτ τ' hτ' j i hji z θ hz hθ hθ2).2.2
    · intro τ hτ
      exact (Work.FTS_RegExport.RXT0.SJC.slotJetContinuousOn (α := pExp α) (hX := hX τ hτ)
        j i hji).2.2

end Work.FTS_RegExport.RXT0
