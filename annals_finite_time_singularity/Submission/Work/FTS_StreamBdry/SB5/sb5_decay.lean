import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Stmts
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.Components
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongEps.PZeroAux.bumpHkNormBound
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkLeafSqFKf
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.nsumData
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.Inputs.residual_slot_jetsB
import Submission.Work.FTS_StreamBdry.Inputs.slice_assy
import Submission.Work.FTS_StreamBdry.Inputs.slice_slots
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.FTS_StreamBdry.SB4.Thetapart_dz_bound
import Submission.Work.FTS_StreamBdry.SB4.l12_zero_plainE
import Submission.Work.FTS_StreamBdry.SB5.Core
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound2
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SB6.clauses3
import Submission.Work.FTS_StreamBdry.SBpsiP.DzJ_crux
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.FTS_StreamBdry.sb2_dthDV_proved
import Submission.Work.FTS_StreamBdry.sb5_barrier_proved
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.WeakRHS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Apriori4Proofs/WeakRHS.lean` — the *weak-input* regularity of the scheme's right-hand side

The interface item **(V)** of the level-four chapter (`NOTES_fourthChapterB_leaf_proof3.md` §3)
asks for the per-slice regularity of `epsRHSP α ρ ε Φs E g s`.  The point of this module is that

* **(V) is free** from `EpsRegP` + the packages (`smoothOpen_epsRHSP_fam`), and
* the **joint** (`(τ,z,θ)`)-continuity of `epsRHSP` — which the `C^∞`-on-the-closed-slab interface
  item (I) was supplying — is *also* free: `epsRHSP α ρ ε Φs E g τ = ∂_τ g(·,·,τ)` by
  `IsEpsSolP`, and `∂_τ g` is continuous on the (interior) slab because `EpsRegP` makes the family
  jointly `C¹` (`continuousOn_epsRHSP_joint_Ioo`).

Once the joint continuity of `epsRHSP` is available, the mixed slots of its mollified projection
are jointly continuous *by the compact-`p`-window argument of* `Jeps_mixed_continuousOn` — with the
raw family replaced by the (jointly continuous) right-hand side
(`Jeps_mixed_continuousOn_fam`, the family-level form of that lemma).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false


/-! ## Joint continuity of `epsRHSP` from the `C¹`-regularity of the flow

The scheme's right-hand side *is* the fake-time derivative of the flow (`IsEpsSolP.eq`), and
`EpsRegP` makes the uncurried family jointly `C¹` on the slab.  Hence `epsRHSP` agrees, on the
interior slab, with the (continuous) third partial derivative of the family — no smoothness of
`epsRHSP` as a *functional* of the profile, and in particular no continuity of `E` in the profile, is
used.  This is the substitute for interface item (I) of `NOTES_fourthChapterB_leaf_proof3.md` §3. -/

/-- **Joint continuity of `epsRHSP` on the interior slab** (with the `(τ,(z,θ))`-order of the
consumers). -/
theorem continuousOn_epsRHSP_joint_Ioo {ρ : ℝ × ℝ → ℝ}
    {α ε T : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (hregP : Work.FTS.StrongEps.EpsRegP α ρ ε T g)
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
  -- the uncurried family, in `(z, θ, τ)`-order
  set Φ : ℝ × (ℝ × ℝ) → ℝ := fun p => g p.1 p.2.1 p.2.2 with hΦ
  -- the interior slab, in `(z, θ, τ)`-order (open, so `fderiv` and `fderivWithin` agree)
  set u : Set (ℝ × (ℝ × ℝ)) :=
    Set.Ioi 0 ×ˢ (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo 0 T) with hu
  have huopen : IsOpen u := isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_Ioo)
  have hu_sub : u ⊆ Set.Ioi 0 ×ˢ (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 T) := by
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.1.le, hp.2.2.2.le⟩
  have hCd : ContDiffOn ℝ 1 Φ u := hregP.1.mono hu_sub
  have hcont : ContinuousOn (fderiv ℝ Φ) u :=
    hCd.continuousOn_fderiv_of_isOpen huopen le_rfl
  -- the value of `fderiv` in the `τ`-direction is the fake-time derivative
  have hkey : ∀ q ∈ Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad,
      Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2
        = fderiv ℝ Φ (q.2.1, (q.2.2, q.1)) (0, (0, 1)) := by
    intro q hq
    obtain ⟨hqτ1, hqτ2⟩ := hq.1
    obtain ⟨hz, hθ⟩ := hq.2
    have hmem : (q.2.1, (q.2.2, q.1)) ∈ u :=
      ⟨hz, ⟨hθ.1, hθ.2⟩, hqτ1, hqτ2⟩
    have hfder : HasFDerivAt Φ (fderiv ℝ Φ (q.2.1, (q.2.2, q.1)))
        (q.2.1, (q.2.2, q.1)) :=
      (((hCd.contDiffWithinAt hmem).contDiffAt (huopen.mem_nhds hmem)).differentiableAt
        one_ne_zero).hasFDerivAt
    have hcurve : HasDerivAt (fun s : ℝ => (q.2.1, (q.2.2, s))) (0, (0, 1)) q.1 :=
      (hasDerivAt_const (c := q.2.1) (x := q.1)).prodMk
        ((hasDerivAt_const (c := q.2.2) (x := q.1)).prodMk (hasDerivAt_id q.1))
    have hcomp : HasDerivAt (fun s : ℝ => Φ (q.2.1, (q.2.2, s)))
        ((fderiv ℝ Φ (q.2.1, (q.2.2, q.1))) (0, (0, 1))) q.1 :=
      hfder.comp_hasDerivAt (f := fun s : ℝ => (q.2.1, (q.2.2, s))) q.1 hcurve
    have hsol' : HasDerivAt (fun s : ℝ => Φ (q.2.1, (q.2.2, s)))
        (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2) q.1 := by
      have hh : (fun s : ℝ => Φ (q.2.1, (q.2.2, s)))
          = fun s : ℝ => g q.2.1 q.2.2 s := rfl
      rw [hh]
      exact (hsol.2 q.2.1 q.2.2 q.1 hz hθ ⟨hqτ1.le, hqτ2.le⟩).hasDerivAt
        (Icc_mem_nhds hqτ1 hqτ2)
    exact (hcomp.unique hsol').symm
  -- assemble: the composite of `fderiv Φ` with the (continuous) relabelling and evaluation
  have hreorder : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1)))
      (Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) :=
    ((continuous_snd.fst).prodMk ((continuous_snd.snd).prodMk continuous_fst)).continuousOn
  have hmaps : Set.MapsTo (fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1)))
      (Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) u := by
    intro q hq
    obtain ⟨hqτ1, hqτ2⟩ := hq.1
    obtain ⟨hz, hθ⟩ := hq.2
    exact ⟨hz, ⟨hθ.1, hθ.2⟩, hqτ1, hqτ2⟩
  have hcomp2 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      fderiv ℝ Φ (q.2.1, (q.2.2, q.1)) (0, (0, 1)))
      (Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
    have h1 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
        fderiv ℝ Φ (q.2.1, (q.2.2, q.1)))
        (Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) :=
      hcont.comp hreorder hmaps
    exact ((ContinuousLinearMap.apply ℝ ℝ (0, (0, 1))).continuous.comp_continuousOn h1)
  refine hcomp2.congr (fun q hq => ?_)
  exact hkey q hq

/-! ## The closed-slab form

The interior form above is enough for the *a.e.* statements (the τ-endpoints are null), but the
closed-slab form is what the interface items consume, and it is available as well: the third partial
derivative of a jointly `C¹` function is continuous **on the closed slab**, because the slab is a
product of two open sets with `Icc 0 T` (a set with `UniqueDiffOn`, for `0 < T`), so
`fderivWithin ℝ Φ s` is continuous on `s` (`ContDiffOn.continuousOn_fderivWithin`) and equals the
within-derivative in the `τ`-direction there. -/


end Work.FTS.StrongEps.E4R3.Apriori4Proofs
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_ztrunc_agree =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

/-- **The `N`-block is unchanged by the truncation on the open quadrant.**

`ztrunc w` and `w` agree on the whole half-plane `z > 0`, which is an open neighbourhood of every
point of `Qd = Ioi 0 ×ˢ Ioo 0 (π/2)`.  `N α (Ftot α w) Φ` is built from `F = Ftot α w` and its
first derivatives (`pz`, `pth`, `Dz`) — germ-local, hence equal — and from the two nonlocal
quantities `L12 F z` (an `s`-integral over `s > z ≥ 0`) and `FK F z` (a `θ`-integral at fixed
`z > 0`), which are unchanged because `ztrunc w = w` on `Ioi 0`.  The `Φ`-argument is the same on
both sides.

Useful lemmas: `Construction.L12AddFstar`, `FTS_RegExport.RXR5.L12_congr_of_agreeOnQ`,
`RXR5.FK_congr_of_agreeOnQ`, `GalFields.RHS.L12f_congr_of_agreeOnQ`, plus the open-strip
congruences for `pz`/`pth`/`Dz` (`Spaces.pz_congr_of_isOpen`, `Spaces.Dz_congr_of_isOpen`,
`Spaces.DthIter_DzIter_eqOn_of_isOpen`-style) and the `PhiTil`/`Rop`/`Uop`/`Vop` unfolding.

The whole bundle of those congruences is already assembled in
`Work.FTS_RegExport.RXR5.Basic` as `RXR5.N_congr_of_agreeOnQ`: for two pairs `(F, Φ)`, `(F', Φ')`
that agree on the open quadrant, `N α F Φ = N α F' Φ'` there.  Hence it suffices to know that
`Ftot α (ztrunc w)` and `Ftot α w` agree on `Qd` (they do, since `Fstar α` is common and
`ztrunc w = w` for `z > 0`) and that the `Φ`-argument is literally the same on both sides. -/
theorem N_ztrunc_agree {α : ℝ} {Φs w Φg : Work.FTS.Galerkin.Fn} :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α
          (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w))
          (fun z θ => Φs z θ + Φg z θ) z θ
        = Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ) z θ := by
  intro z θ hzθ
  obtain ⟨hz, hθ, hθ2⟩ := hzθ
  exact Work.FTS_RegExport.RXR5.N_congr_of_agreeOnQ
    (F := Work.Construction.Ftot α (ztrunc w))
    (F' := Work.Construction.Ftot α w)
    (Φ := fun z θ => Φs z θ + Φg z θ)
    (Φ' := fun z θ => Φs z θ + Φg z θ)
    (fun z θ hz' _ _ => by
      show Work.Construction.Fstar α z θ + ztrunc w z θ
          = Work.Construction.Fstar α z θ + w z θ
      rw [ztrunc_of_pos hz'])
    (fun _ _ _ _ _ => rfl) hz hθ hθ2

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc_pkgs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)
open scoped Real Topology

set_option autoImplicit false

/-! # `N_aux.ZTruncPkgs` — the elliptic packages are invariant under `ztrunc`

`ztrunc w z θ = if 0 < z then w z θ else 0` agrees with `w` on the whole half-plane `z > 0`.
Everything the two elliptic packages see is either

* the source itself, evaluated **on the open quadrant** (`IsBslSol`'s equation, the vanishing of
  `Uop`'s θ-traces, the `CoefTh`/`CoefThMem` fields), or
* a local operator applied to the residual `PhiTil α w Φg` (`Rop`, `Uop`, `Vop`), or
* an integral / `L²`-type quantity (`HkSq`, `Xn`, `HkMem`), which is blind to the null set
  `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}`.

The whole content is therefore the agreement of `PhiTil α (ztrunc w) Φg` with
`PhiTil α w Φg` on `z > 0`, which follows from `L₁₂ (ztrunc w) z = L₁₂ w z` for `z ≥ 0`: the
defining integral of `L₁₂` runs over `s > z ≥ 0`, where `ztrunc w = w`.

The congruence lemmas below are stated for agreement on the whole half-plane `{z > 0}` (which is
what we actually have here); they are the τ-free analogues of the quadrant lemmas of
`Work.FTS_RegExport.RXR5`.
-/

section Helpers

/-- `L₁₂`'s angular density only sees the values of the source at `s > 0`. -/
theorem L12dens_ztrunc (w : Fn) {s : ℝ} (hs : 0 < s) :
    Work.Construction.L12dens (ztrunc w) s = Work.Construction.L12dens w s := by
  unfold Work.Construction.L12dens Work.FM.L12dens
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [ztrunc_of_pos hs])

/-- `L₁₂` is unchanged by the truncation for every `z ≥ 0`. -/
theorem L12_ztrunc (w : Fn) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (ztrunc w) z = Work.Construction.L12 w z := by
  unfold Work.Construction.L12 Work.FM.L12
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun s hs => L12dens_ztrunc w (lt_of_le_of_lt hz hs))

/-- The singular part `Θ` is unchanged by the truncation. -/
theorem Theta_ztrunc (α : ℝ) (w : Fn) {z θ : ℝ} (hz : 0 ≤ z) :
    Work.Construction.Theta α (ztrunc w) z θ = Work.Construction.Theta α w z θ := by
  simp only [Work.Construction.Theta, L12_ztrunc w hz]

/-- The elliptic residual `PhiTil` is unchanged by the truncation on the half-plane `z > 0`. -/
theorem PhiTil_ztrunc (α : ℝ) (w Φg : Fn) :
    ∀ z θ : ℝ, 0 < z → Work.Construction.PhiTil α (ztrunc w) Φg z θ
      = Work.Construction.PhiTil α w Φg z θ := by
  intro z θ hz
  simp only [Work.Construction.PhiTil, Theta_ztrunc α w hz.le]

/-! ### The residual on the two angular boundary lines -/

/-- `PhiTil` reduces to `Φ` on the line `θ = 0` (the `sin 2θ`-factor of `Θ` vanishes). -/
theorem PhiTil_line_zero (α : ℝ) (F Φ : Fn) (z : ℝ) :
    Work.Construction.PhiTil α F Φ z 0 = Φ z 0 := by
  simp [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]

/-- `PhiTil` reduces to `Φ` on the line `θ = π/2`. -/
theorem PhiTil_line_halfpi (α : ℝ) (F Φ : Fn) (z : ℝ) :
    Work.Construction.PhiTil α F Φ z (π / 2) = Φ z (π / 2) := by
  simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
  have h : Real.sin (2 * (π / 2)) = 0 := by
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
  rw [h, mul_zero, zero_mul, sub_zero]

/-! ### Locality of the operators of §Modulation -/

/-- Agreement on the half-plane `z > 0` gives agreement of `∂_z`. -/
theorem pz_congr_half {Ψ Ψ' : Fn} (h : ∀ z θ : ℝ, 0 < z → Ψ z θ = Ψ' z θ)
    (z θ : ℝ) (hz : 0 < z) : Work.Spaces.pz Ψ z θ = Work.Spaces.pz Ψ' z θ := by
  simp only [Work.Spaces.pz]
  exact Filter.EventuallyEq.deriv_eq (by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' θ hz')

/-- Agreement on the half-plane `z > 0` gives agreement of `∂_θ`. -/
theorem pth_congr_half {Ψ Ψ' : Fn} (h : ∀ z θ : ℝ, 0 < z → Ψ z θ = Ψ' z θ)
    (z θ : ℝ) (hz : 0 < z) : Work.Spaces.pth Ψ z θ = Work.Spaces.pth Ψ' z θ := by
  simp only [Work.Spaces.pth]
  exact Filter.EventuallyEq.deriv_eq (Filter.Eventually.of_forall (fun θ' => h z θ' hz))

/-- `Rop` is local on the half-plane `z > 0`. -/
theorem Rop_congr_half {α : ℝ} {Ψ Ψ' : Fn}
    (h : ∀ z θ : ℝ, 0 < z → Ψ z θ = Ψ' z θ) :
    ∀ z θ : ℝ, 0 < z → Work.Construction.Rop α Ψ z θ = Work.Construction.Rop α Ψ' z θ := by
  intro z θ hz
  have hpz : Work.Spaces.pz Ψ z θ = Work.Spaces.pz Ψ' z θ := pz_congr_half h z θ hz
  have hpth : Work.Spaces.pth Ψ z θ = Work.Spaces.pth Ψ' z θ := pth_congr_half h z θ hz
  simp only [Work.Construction.Rop]
  rw [h z θ hz, hpz, hpth]

/-- `Uop` is local on the half-plane `z > 0`. -/
theorem Uop_congr_half {α : ℝ} {Ψ Ψ' : Fn}
    (h : ∀ z θ : ℝ, 0 < z → Ψ z θ = Ψ' z θ) :
    ∀ z θ : ℝ, 0 < z → Work.Construction.Uop α Ψ z θ = Work.Construction.Uop α Ψ' z θ := by
  intro z θ hz
  have hpz : Work.Spaces.pz Ψ z θ = Work.Spaces.pz Ψ' z θ := pz_congr_half h z θ hz
  simp only [Work.Construction.Uop]
  rw [h z θ hz, hpz]

/-- `Vop` is local on the half-plane `z > 0`. -/
theorem Vop_congr_half {Ψ Ψ' : Fn}
    (h : ∀ z θ : ℝ, 0 < z → Ψ z θ = Ψ' z θ) :
    ∀ z θ : ℝ, 0 < z → Work.Construction.Vop Ψ z θ = Work.Construction.Vop Ψ' z θ := by
  intro z θ hz
  have hpth : Work.Spaces.pth Ψ z θ = Work.Spaces.pth Ψ' z θ := pth_congr_half h z θ hz
  simp only [Work.Construction.Vop]
  rw [h z θ hz, hpth]

/-- `Uop / sin 2θ` is local on the half-plane `z > 0`. -/
theorem Uop_div_s2_congr_half {α : ℝ} {Ψ Ψ' : Fn}
    (h : ∀ z θ : ℝ, 0 < z → Ψ z θ = Ψ' z θ) :
    ∀ z θ : ℝ, 0 < z →
      Work.Construction.Uop α Ψ z θ / Work.Construction.s2 θ
        = Work.Construction.Uop α Ψ' z θ / Work.Construction.s2 θ :=
  fun z θ hz => by rw [Uop_congr_half h z θ hz]

/-! ### The flat angular norms

`supAbsO` is the supremum over the *open* quadrant and `CoefTh`/`CoefThMem` are built from
`supAbsO (D_z^b D_θ^i ∂_θ ·)`, so all three only see the open quadrant. -/

/-- `supAbsO` only depends on the values on the open quadrant. -/
theorem supAbsO_congr_trunc {f f' : Fn} (h : Work.FTS.EllipticEst.AgreeOnQ f f') :
    Work.FTS.H2.supAbsO f = Work.FTS.H2.supAbsO f' := by
  unfold Work.FTS.H2.supAbsO
  have hset : {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧ y = |f z θ|}
      = {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧ y = |f' z θ|} := by
    ext y
    constructor
    · rintro ⟨z, hz, θ, hθ, hθ', rfl⟩
      exact ⟨z, hz, θ, hθ, hθ', by rw [h z θ hz hθ hθ']⟩
    · rintro ⟨z, hz, θ, hθ, hθ', rfl⟩
      exact ⟨z, hz, θ, hθ, hθ', by rw [h z θ hz hθ hθ']⟩
  rw [hset]

/-- `CoefTh` only depends on the values on the open quadrant. -/
theorem CoefTh_congr_trunc (l : ℕ) {f f' : Fn}
    (h : Work.FTS.EllipticEst.AgreeOnQ f f') :
    Work.FTS.VocabO.CoefTh l f = Work.FTS.VocabO.CoefTh l f' := by
  simp only [Work.FTS.VocabO.CoefTh]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with _hbi
  · exact supAbsO_congr_trunc (h.pth.mixed b i)
  · rfl

/-- `CoefThMem` only depends on the values on the open quadrant. -/
theorem CoefThMem_congr_trunc (l : ℕ) {f f' : Fn}
    (h : Work.FTS.EllipticEst.AgreeOnQ f f') :
    Work.FTS.VocabO.CoefThMem l f → Work.FTS.VocabO.CoefThMem l f' := by
  intro hf b i hbi
  obtain ⟨K, hK⟩ := hf b i hbi
  refine ⟨K, fun z θ hz hθ hθ' => ?_⟩
  rw [← (h.pth.mixed b i) z θ hz hθ hθ']
  exact hK z θ hz hθ hθ'

/-! ### `VanishTheta` of `Uop`, transferred along the two boundary lines -/

/-- `Uop`'s vanishing on the two angular boundary lines only depends on the boundary values of
its argument (through the `z`-slices at `θ = 0` and `θ = π/2`). -/
theorem vanishTheta_Uop_of_line_eq {α : ℝ} {Ψ Ψ' : Fn}
    (h0 : ∀ z, Ψ z 0 = Ψ' z 0) (h1 : ∀ z, Ψ z (π / 2) = Ψ' z (π / 2))
    (hv : Work.Spaces.VanishTheta (Work.Construction.Uop α Ψ')) :
    Work.Spaces.VanishTheta (Work.Construction.Uop α Ψ) := by
  have key : ∀ θb : ℝ, (∀ z, Ψ z θb = Ψ' z θb) →
      ∀ z, Work.Construction.Uop α Ψ z θb = Work.Construction.Uop α Ψ' z θb := by
    intro θb hb z
    have hs : (fun z' => Ψ z' θb) = (fun z' => Ψ' z' θb) := funext hb
    have hp : Work.Spaces.pz Ψ z θb = Work.Spaces.pz Ψ' z θb := by
      simp only [Work.Spaces.pz, hs]
    simp only [Work.Construction.Uop]
    rw [hb z, hp]
  exact ⟨fun z => by rw [key 0 h0 z]; exact hv.1 z,
    fun z => by rw [key (π / 2) h1 z]; exact hv.2 z⟩

end Helpers

/-- **The two elliptic packages are invariant under the truncation `ztrunc`.**

The only place the packages see the source is through `PhiTil α g Φg = Φg - (1/(4α))·sin 2θ·L12 g`,
and `L12 (ztrunc w) z = L12 w z` for every `z ≥ 0` (the defining integral runs over `s > z ≥ 0`,
where `ztrunc w = w`).  Hence `Rop/Uop/Vop (PhiTil α (ztrunc w) Φg)` agree with the `w`-versions on
the open quadrant, and `sol : IsBslSol(·)Pos` constrains the source only through the equation on
the open quadrant.  The `Xn`/`HkNorm` right-hand sides agree by `N_aux.HkNorm_ztrunc`.

Useful lemmas: `N_aux.HkSq_ztrunc`, `N_aux.HkNorm_ztrunc`, `N_aux.Xn_ztrunc`,
`N_aux.smoothOpen_ztrunc`, `EllipticEst.RPFresh.smoothOpen_congr`,
`EllipticEst.HkSq_congr_open`, `H6Pair6Aux.HkMem_congr_Qd`, `StrongGlobal.IsBslSolPos.congr`,
`FTS_RegExport.RXR5.L12_congr_of_agreeOnQ`, and the open-strip congruence lemmas for
`pz`/`pth` (`Spaces.pz_congr_of_isOpen`, `Spaces.Dz_congr_of_isOpen`,
`EllipticEst.SmoothOpen.DzIter_congr`). -/
theorem ztrunc_pkgs {α Ce : ℝ} {w Φg : Work.FTS.Galerkin.Fn}
    (hw : Work.FTS.ClassC.ClassC α w)
    (hgo : Work.FTS.VocabO.EllPkgGo α Ce w Φg)
    (hK : Work.FTS.ClassC.EllPkgK α 6 Ce w Φg) :
    (Work.FTS.VocabO.EllPkgGo α Ce
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w) Φg ∧
      Work.FTS.ClassC.EllPkgK α 6 Ce
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w) Φg) := by
  have hPhi : ∀ z θ : ℝ, 0 < z →
      Work.Construction.PhiTil α (ztrunc w) Φg z θ = Work.Construction.PhiTil α w Φg z θ :=
    PhiTil_ztrunc α w Φg
  -- agreement of the residual on the open quadrant, in both directions
  have hPhiQ : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Construction.PhiTil α (ztrunc w) Φg) (Work.Construction.PhiTil α w Φg) :=
    fun z θ hz _ _ => hPhi z θ hz
  have hPhiQ' : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Construction.PhiTil α w Φg) (Work.Construction.PhiTil α (ztrunc w) Φg) :=
    fun z θ hz hθ hθ2 => (hPhiQ z θ hz hθ hθ2).symm
  -- the three transported residuals
  have hRQ : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Construction.Rop α (Work.Construction.PhiTil α (ztrunc w) Φg))
      (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg)) :=
    fun z θ hz _ _ => Rop_congr_half (α := α) hPhi z θ hz
  have hRQ' : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg))
      (Work.Construction.Rop α (Work.Construction.PhiTil α (ztrunc w) Φg)) :=
    fun z θ hz hθ hθ2 => (hRQ z θ hz hθ hθ2).symm
  have hUQ : Work.FTS.EllipticEst.AgreeOnQ
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α (ztrunc w) Φg) z θ
        / Work.Construction.s2 θ)
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α w Φg) z θ
        / Work.Construction.s2 θ) :=
    fun z θ hz _ _ => Uop_div_s2_congr_half (α := α) hPhi z θ hz
  have hUQ' : Work.FTS.EllipticEst.AgreeOnQ
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α w Φg) z θ
        / Work.Construction.s2 θ)
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α (ztrunc w) Φg) z θ
        / Work.Construction.s2 θ) :=
    fun z θ hz hθ hθ2 => (hUQ z θ hz hθ hθ2).symm
  have hVQ : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Construction.Vop (Work.Construction.PhiTil α (ztrunc w) Φg))
      (Work.Construction.Vop (Work.Construction.PhiTil α w Φg)) :=
    fun z θ hz _ _ => Vop_congr_half hPhi z θ hz
  have hVQ' : Work.FTS.EllipticEst.AgreeOnQ
      (Work.Construction.Vop (Work.Construction.PhiTil α w Φg))
      (Work.Construction.Vop (Work.Construction.PhiTil α (ztrunc w) Φg)) :=
    fun z θ hz hθ hθ2 => (hVQ z θ hz hθ hθ2).symm
  -- ## the `ℋ⁴` package
  have hGoNew : Work.FTS.VocabO.EllPkgGo α Ce (ztrunc w) Φg := by
    obtain ⟨sol, hsmooth, hR, hU, hV, hvanishU, hVth⟩ := hgo
    obtain ⟨hs1, hs2, hs3, hs4⟩ := sol
    refine ⟨⟨fun z hz θ hθ hθ2 => ?_, hs2, hs3, hs4⟩, hsmooth, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ztrunc_of_pos hz]
      exact hs1 z hz θ hθ hθ2
    · -- the `R` field
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Work.FTS.EllipticEst.RPFresh.smoothOpen_congr hR.1.1 hRQ
      · exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
          (fun z θ hq => hRQ' z θ hq.1 hq.2.1 hq.2.2) hR.1.2
      · have hXn : Work.FTS.Nonlin.Xn α
            (Work.Construction.Rop α (Work.Construction.PhiTil α (ztrunc w) Φg))
            = Work.FTS.Nonlin.Xn α
              (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg)) := by
          simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
            Work.FTS.EllipticEst.HkSq_congr_open α 4 hRQ]
        rw [hXn, Xn_ztrunc α w]
        exact hR.2
    · -- the `U` field
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Work.FTS.EllipticEst.RPFresh.smoothOpen_congr hU.1.1 hUQ
      · exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
          (fun z θ hq => hUQ' z θ hq.1 hq.2.1 hq.2.2) hU.1.2
      · have hXn : Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α (ztrunc w) Φg) z θ
              / Work.Construction.s2 θ)
            = Work.FTS.Nonlin.Xn α
              (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α w Φg) z θ
                / Work.Construction.s2 θ) := by
          simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
            Work.FTS.EllipticEst.HkSq_congr_open α 4 hUQ]
        rw [hXn, Xn_ztrunc α w]
        exact hU.2
    · -- the `V` field
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Work.FTS.EllipticEst.RPFresh.smoothOpen_congr hV.1.1 hVQ
      · exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
          (fun z θ hq => hVQ' z θ hq.1 hq.2.1 hq.2.2) hV.1.2
      · have hXn : Work.FTS.Nonlin.Xn α
            (Work.Construction.Vop (Work.Construction.PhiTil α (ztrunc w) Φg))
            = Work.FTS.Nonlin.Xn α
              (Work.Construction.Vop (Work.Construction.PhiTil α w Φg)) := by
          simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
            Work.FTS.EllipticEst.HkSq_congr_open α 4 hVQ]
        rw [hXn, Xn_ztrunc α w]
        exact hV.2
    · -- `VanishTheta` of `Uop`: only the two boundary lines matter, and there `PhiTil` is `Φg`
      exact vanishTheta_Uop_of_line_eq
        (fun z => by rw [PhiTil_line_zero α (ztrunc w) Φg z, PhiTil_line_zero α w Φg z])
        (fun z => by rw [PhiTil_line_halfpi α (ztrunc w) Φg z, PhiTil_line_halfpi α w Φg z])
        hvanishU
    · -- the `CoefTh`/`CoefThMem` field of `Vop`
      refine ⟨?_, ?_⟩
      · exact CoefThMem_congr_trunc 1 hVQ' hVth.1
      · rw [CoefTh_congr_trunc 1 hVQ, Xn_ztrunc α w]
        exact hVth.2
  -- ## the `ℋ⁶` package
  have hKNew : Work.FTS.ClassC.EllPkgK α 6 Ce (ztrunc w) Φg := by
    obtain ⟨sol, hsmooth, hR, hU, hV⟩ := hK
    obtain ⟨ks1, ks2, ks3, ks4⟩ := sol
    refine ⟨⟨fun z hz θ hθ hθ2 => ?_, ks2, ks3, ks4⟩, hsmooth, ?_, ?_, ?_⟩
    · rw [ztrunc_of_pos hz]
      exact ks1 z hz θ hθ hθ2
    · -- the `R` field
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Work.FTS.EllipticEst.RPFresh.smoothOpen_congr hR.1.1 hRQ
      · exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
          (fun z θ hq => hRQ' z θ hq.1 hq.2.1 hq.2.2) hR.1.2
      · have hN : Work.Spaces.HkNorm α 6
            (Work.Construction.Rop α (Work.Construction.PhiTil α (ztrunc w) Φg))
            = Work.Spaces.HkNorm α 6
              (Work.Construction.Rop α (Work.Construction.PhiTil α w Φg)) := by
          simp only [Work.Spaces.HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α 6 hRQ]
        rw [hN, HkNorm_ztrunc α 6 w]
        exact hR.2
    · -- the `U` field
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Work.FTS.EllipticEst.RPFresh.smoothOpen_congr hU.1.1 hUQ
      · exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
          (fun z θ hq => hUQ' z θ hq.1 hq.2.1 hq.2.2) hU.1.2
      · have hN : Work.Spaces.HkNorm α 6
            (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α (ztrunc w) Φg) z θ
              / Work.Construction.s2 θ)
            = Work.Spaces.HkNorm α 6
              (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α w Φg) z θ
                / Work.Construction.s2 θ) := by
          simp only [Work.Spaces.HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α 6 hUQ]
        rw [hN, HkNorm_ztrunc α 6 w]
        exact hU.2
    · -- the `V` field
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Work.FTS.EllipticEst.RPFresh.smoothOpen_congr hV.1.1 hVQ
      · exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
          (fun z θ hq => hVQ' z θ hq.1 hq.2.1 hq.2.2) hV.1.2
      · have hN : Work.Spaces.HkNorm α 6
            (Work.Construction.Vop (Work.Construction.PhiTil α (ztrunc w) Φg))
            = Work.Spaces.HkNorm α 6
              (Work.Construction.Vop (Work.Construction.PhiTil α w Φg)) := by
          simp only [Work.Spaces.HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α 6 hVQ]
        rw [hN, HkNorm_ztrunc α 6 w]
        exact hV.2
  exact ⟨hGoNew, hKNew⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.NBlk_hkMem6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.NBlk_hkMem6` — the twenty pieces of the `N`-block are honest in `ℋ⁶`

For every level-six datum `(w, Φs, Φg)` of the E4 node (`ClassC α w`, `Xn α w ≤ C₀ α²`,
`w` vanishing off the open quadrant, `EllPkgGo α Ce w Φg`, `ClassC.EllPkgK α 6 Ce w Φg`,
`StarPkg6 α Cs Φs`) and every `k < 20`, the `k`-th product-form piece
`ClassCRHS.NBlk α w Φs Φg k` of the nonlinear term is honest in `ℋ⁶`.

## The route

The twenty pieces `NBlk α w Φs Φg k` are — up to the permutation `NBlkPerm` of the two
factors of each piece and the two elementary `(z+1)/z`-shifts (valid on the open quadrant,
where `z ≠ 0`) — literally the twenty pieces `pcs α w Φg Φs k` of the **level-six `N`-row**
(`H6Rows.Npair6SupAux.nsP0 … nsP19`), whose `ℋ⁶`-honesty and `C⁶`-regularity on the open
quadrant is the *proved* statement `H6Row6.NS6.pieces`, from the bundled level-six data
`H6Row6.NS6.Data α Ce Cs w Φg Φs`.

We assemble that data from the hypotheses of the task:

* `SmoothOpen w`, `HkMem α 7 w`, `L₁₂(w)(0) = 0` are fields of `ClassC α w`;
* `HkMem α 6 w` is the level-descent of `HkMem α 7 w` (`OpenPkg.HkMem_mono_open`);
* `H6Adm α w` is `StrongEps.H6Adm_of_classC_of_eqzero` (the off-quadrant vanishing);
* `SmoothOpen Φg` is `EllPkgGo.smooth`, `SmoothOpen Φs` is `StarPkg6.smooth`;
* `StrongPersist.EllPkgK α 6 Ce w Φg` is the repackaging of `ClassC.EllPkgK α 6 Ce w Φg`
  (`Apriori4Proofs.blocks.N_aux.ellPkgK_toStrongPersist`);
* `HkMem α 6 (FK w)` is `Npair6BWork.fk_hkMem`;
* the `ℋ⁶ × ℋ⁶` product rule is the unconditional level-six product rule of
  `StrongPersist.N6.prod_field_of6` (its two analytic inputs `prod_majorant6`, `exc_bound6`
  are proved for every `α ∈ (0,1]`, so no smallness threshold is needed).

All the analytic work (the pricing of the elliptic/star coefficients, the `FK`-slots, the
`𝒲^{6,∞}`-product rules) is inside `NS6.pieces`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongEps.E4R3.Nblock6

open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongPersist.H6Rows.Npair6SupAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The permutation of the twenty pieces that matches the product forms `ClassCRHS.NBlk`
(ordered `N1gg, N1gs, …, N5ss`) with the level-six row pieces `H6Row6.pcs` (ordered
`nsP0, …, nsP19`): within each block of four the two factors are swapped
(`k ↦ 3−k` for `k mod 4 ∈ {0,1}`, `k ↦ 5−k` for `k mod 4 ∈ {2,3}`). -/
def NBlkPerm : ℕ → ℕ
  | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0
  | 4 => 7 | 5 => 6 | 6 => 5 | 7 => 4
  | 8 => 11 | 9 => 10 | 10 => 9 | 11 => 8
  | 12 => 15 | 13 => 14 | 14 => 13 | 15 => 12
  | 16 => 19 | 17 => 18 | 18 => 17 | _ => 16

/-- **The `NBlk` pieces are the level-six row pieces, up to the permutation `NBlkPerm`.**

On the open quadrant the two product forms agree: the only differences are the order of the
two factors, the association of the scalar, and the `(z+1)/z` / `z/(1+z)` shifts of the star
pieces (an identity on `z ≠ 0`), plus `FK F_* = α·2z/(1+z)² = 2α·hKer` for the `(F_*,K)`-slot. -/
theorem NBlk_eq_pcs_piece {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (w Φs Φg : Fn)
    (k : ℕ) (hk : k < 20) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k z θ
        = Work.FTS.StrongPersist.H6Row6.pcs α w Φg Φs (NBlkPerm k) z θ := by
  intro z θ hzθ
  have hz : z ≠ 0 := ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hzθ).1
  have h1z : (1 : ℝ) + z ≠ 0 := by
    have h2 := (Work.FTS.EllipticEst.mem_Q0.mp hzθ).1
    positivity
  interval_cases k <;>
    · simp only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.StrongPersist.H6Row6.pcs, NBlkPerm,
        nsP0, nsP1, nsP2, nsP3, nsP4, nsP5, nsP6, nsP7, nsP8, nsP9, nsP10, nsP11,
        nsP12, nsP13, nsP14, nsP15, nsP16, nsP17, nsP18, nsP19,
        coefR1, coefR2, coefU1, coefU2, coefV1, coefV2, coefKs, coefKf,
        slotFs, slotTs, slotZs, slotTf, slotZf, angSin2,
        Work.FTS.Nonlin.PhiTg, Work.FTS.Nonlin.PhiTs, Work.FTS.VocabO2.PhiTs,
        Work.Spaces.hKer, Work.FTS.Nonlin.FK_Fstar hα hα1]
      try field_simp
      try ring

theorem NBlk_hkMem6 : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    ∀ k ∈ Finset.range 20, Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) := by
  intro C₀ Ce Cs α hαI Φs w Φg hw hXw hzero hgo hK hstar k hk
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hαI
  have hklt : k < 20 := Finset.mem_range.mp hk
  -- ## the level-six slice data
  have hmem6w : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem
  have hkfm : Work.Spaces.HkMem α 6 (fun z (_ : ℝ) => Work.Construction.FK w z) :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.fk_hkMem α ⟨hα0, hα1⟩ w hw.reg hmem6w
  have hadm : Work.FTS.StrongPersist.H6Adm α w :=
    Work.FTS.StrongEps.H6Adm_of_classC_of_eqzero hw hzero
  -- ## the unconditional level-six product rule
  have hmul : ∀ u v : Fn, Work.FTS.EllipticEst.SmoothOpen u →
      Work.Spaces.HkMem α 6 u → Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α 6 v →
      Work.Spaces.HkMem α 6 (fun z θ => u z θ * v z θ) := by
    obtain ⟨C, hC, hCpr⟩ := Work.FTS.StrongPersist.N6.prod_field_of6
      Work.FTS.StrongPersist.N6.prod_majorant6 Work.FTS.StrongPersist.N6.exc_bound6
    intro u v hus hum hvs hvm
    exact (hCpr α hα0 hα1 u v ⟨hus, hum⟩ ⟨hvs, hvm⟩).1
  have D : Work.FTS.StrongPersist.H6Row6.NS6.Data α Ce Cs w Φg Φs :=
    ⟨hα0, hα1, hw.reg, hmem6w, hw.mem, hgo.smooth, hstar.smooth, hw.l12, hstar,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ellPkgK_toStrongPersist hK,
      hkfm, hadm, hmul⟩
  -- ## transfer the membership along the piece identity
  have hk20 : NBlkPerm k < 20 := by interval_cases k <;> decide
  exact Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
    (fun z θ hzθ => (NBlk_eq_pcs_piece hα0 hα1 w Φs Φg k hklt z θ hzθ).symm)
    (Work.FTS.StrongPersist.H6Row6.NS6.pieces D (NBlkPerm k) hk20).2

end Work.FTS.StrongEps.E4R3.Nblock6
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.EpsWPSemitameAux.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.RawE6Aux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The assembly of the five blocks -/

/-- **The assembly**: the five `BData`s of the blocks of `epsWBlk` give the three conjuncts of
the semi-tame estimate with the single constant `√(16·(KL+KM+K0+KN+KS+1)) + 1`.  (The proof is
the arithmetic core of `Apriori4Proofs.semitame_blk_of_blocks`, with the `μ̄`-bound of the
`blkMu`-block supplied as an explicit hypothesis instead of being extracted from the elliptic
packages.) -/
theorem semitame_of_bdata {C₀ Ce Cs α : ℝ} (hα : α ∈ Set.Ioc 0 1)
    {KL KM K0 KN KS : ℝ} (hKL : 0 < KL) (hKM : 0 < KM) (hK0 : 0 < K0) (hKN : 0 < KN)
    (hKS : 0 < KS)
    (hL : ∀ {w : Fn}, Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → w z θ = 0) →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KL
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkLin α w))
    (hM : ∀ {Φs w Φg : Fn}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      |Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w Φg| ≤ 1 / 2 →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KM
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkMu α Φs w Φg))
    (h0 : ∀ {w : Fn}, Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → w z θ = 0) →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w K0
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w))
    (hN : ∀ {Φs w Φg : Fn}, Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KN
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN α Φs w Φg))
    (hS : ∀ {w : Fn} (μ lam : ℝ), Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → |μ| ≤ 1 / 2 → |lam| ≤ 1 →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KS
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkNstar w μ lam)) :
    ∀ {Φs w Φg : Fn} {μ lam : ℝ}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 → |μ| ≤ 1 / 2 → |lam| ≤ 1 →
      |Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w Φg| ≤ 1 / 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → w z θ = 0) →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      Work.FTS.VocabO.HQo α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam)
          ≤ (Real.sqrt (16 * (KL + KM + K0 + KN + KS + 1)) + 1)
            * (1 + Work.Spaces.HkNorm α 5 w) ∧
      Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam)
          ≤ (Real.sqrt (16 * (KL + KM + K0 + KN + KS + 1)) + 1)
              * (1 + Work.Spaces.HkNorm α 7 w)
            + (Real.sqrt (16 * (KL + KM + K0 + KN + KS + 1)) + 1)
              * (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by
  set Ktot : ℝ := KL + KM + K0 + KN + KS + 1 with hKtot
  have hKtot0 : 0 < Ktot := by rw [hKtot]; linarith
  set C : ℝ := Real.sqrt (16 * Ktot) + 1 with hC
  have hCsq : Real.sqrt (16 * Ktot) ≤ C := by rw [hC]; linarith [Real.sqrt_nonneg (16 * Ktot)]
  intro Φs w Φg μ lam hcls hXw hμ hlam hμblk hzero hgo hK hstar
  have hα0 : 0 < α := hα.1
  set A1 : Fn := fun z θ => - Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkLin α w z θ with hA1
  set A2 : Fn := fun z θ => - Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkMu α Φs w Φg z θ with hA2
  set A3 : Fn := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN0 α w with hA3
  set A4 : Fn := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkN α Φs w Φg with hA4
  set A5 : Fn := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkNstar w μ lam with hA5
  have hsum : Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam
      = Work.FTS.StrongEps.E4R3.Apriori4Proofs.sum5 A1 A2 A3 A4 A5 := by
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk_eq_sum5, ← hA1, ← hA2, ← hA3, ← hA4, ← hA5]
  have eL : Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KL A1 := by
    rw [hA1]; exact (hL hcls hXw hzero).neg
  have eM : Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KM A2 := by
    rw [hA2]
    exact (hM hcls hXw hμblk).neg
  have e0 : Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w K0 A3 := by
    rw [hA3]; exact h0 hcls hXw hzero
  have eN : Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KN A4 := by
    rw [hA4]; exact hN hcls hXw hzero hgo hK hstar
  have eS : Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KS A5 := by
    rw [hA5]; exact hS μ lam hcls hXw hμ hlam
  have hm6 : Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam) := by
    rw [hsum]
    exact Work.FTS.StrongEps.E4R3.Apriori4Proofs.hkMem_sum5 eL.sm eM.sm e0.sm eN.sm eS.sm
      eL.hm eM.hm e0.hm eN.hm eS.hm
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam) := by
    rw [hsum]
    exact Work.FTS.StrongEps.E4R3.Apriori4Proofs.smoothOpen_sum5 eL.sm eM.sm e0.sm eN.sm eS.sm
  have m4 : ∀ {B : Fn}, Work.FTS.EllipticEst.SmoothOpen B → Work.Spaces.HkMem α 6 B →
      Work.Spaces.HkMem α 4 B := fun hs hm =>
    Work.FTS.OpenPkg.HkMem_mono_open hs 4 (by norm_num) hm
  have hsq4 : Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam)
      ≤ 16 * Ktot * (1 + Work.Spaces.HkSq α 5 w) := by
    rw [hsum]
    have hs := Work.FTS.StrongEps.E4R3.Apriori4Proofs.hkSq_sum5 hα0 eL.sm eM.sm e0.sm eN.sm eS.sm
      (m4 eL.sm eL.hm) (m4 eM.sm eM.hm) (m4 e0.sm e0.hm) (m4 eN.sm eN.hm) (m4 eS.sm eS.hm)
    have hS5 := Work.Spaces.HkSq_nonneg α 5 w
    have hbound : Work.Spaces.HkSq α 4 A1 + Work.Spaces.HkSq α 4 A2 + Work.Spaces.HkSq α 4 A3
        + Work.Spaces.HkSq α 4 A4 + Work.Spaces.HkSq α 4 A5
        ≤ Ktot * (1 + Work.Spaces.HkSq α 5 w) := by
      rw [hKtot]
      nlinarith [eL.b4, eM.b4, e0.b4, eN.b4, eS.b4, hS5, hKL, hKM, hK0, hKN, hKS]
    calc Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.sum5 A1 A2 A3 A4 A5)
        ≤ 16 * (Work.Spaces.HkSq α 4 A1 + Work.Spaces.HkSq α 4 A2 + Work.Spaces.HkSq α 4 A3
            + Work.Spaces.HkSq α 4 A4 + Work.Spaces.HkSq α 4 A5) := hs
      _ ≤ 16 * (Ktot * (1 + Work.Spaces.HkSq α 5 w)) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = 16 * Ktot * (1 + Work.Spaces.HkSq α 5 w) := by ring
  have hsq6 : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam)
      ≤ 16 * Ktot * ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by
    rw [hsum]
    have hs := Work.FTS.StrongEps.E4R3.Apriori4Proofs.hkSq_sum5 hα0 eL.sm eM.sm e0.sm eN.sm eS.sm
      eL.hm eM.hm e0.hm eN.hm eS.hm
    have hS7 := Work.Spaces.HkSq_nonneg α 7 w
    have hS6 := Work.Spaces.HkSq_nonneg α 6 w
    have hbound : Work.Spaces.HkSq α 6 A1 + Work.Spaces.HkSq α 6 A2 + Work.Spaces.HkSq α 6 A3
        + Work.Spaces.HkSq α 6 A4 + Work.Spaces.HkSq α 6 A5
        ≤ Ktot * ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by
      rw [hKtot]
      nlinarith [eL.b6, eM.b6, e0.b6, eN.b6, eS.b6, hS7, hS6,
        sq_nonneg (1 + Work.Spaces.HkSq α 6 w), hKL, hKM, hK0, hKN, hKS]
    calc Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.E4R3.Apriori4Proofs.sum5 A1 A2 A3 A4 A5)
        ≤ 16 * (Work.Spaces.HkSq α 6 A1 + Work.Spaces.HkSq α 6 A2 + Work.Spaces.HkSq α 6 A3
            + Work.Spaces.HkSq α 6 A4 + Work.Spaces.HkSq α 6 A5) := hs
      _ ≤ 16 * (Ktot * ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2)) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = 16 * Ktot * ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by ring
  have hHQ : Work.FTS.VocabO.HQo α 6
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam) := ⟨hsm, hm6⟩
  have hN5 : Work.Spaces.HkNorm α 5 w = Real.sqrt (Work.Spaces.HkSq α 5 w) := rfl
  have hN6 : Work.Spaces.HkNorm α 6 w = Real.sqrt (Work.Spaces.HkSq α 6 w) := rfl
  have hN7 : Work.Spaces.HkNorm α 7 w = Real.sqrt (Work.Spaces.HkSq α 7 w) := rfl
  have sqrt_one_add_le : ∀ {x : ℝ}, 0 ≤ x → Real.sqrt (1 + x) ≤ 1 + Real.sqrt x := by
    intro x hx
    have hnn : 0 ≤ 1 + Real.sqrt x := by linarith [Real.sqrt_nonneg x]
    rw [← Real.sqrt_sq hnn]
    refine Real.sqrt_le_sqrt ?_
    have hsq : (1 + Real.sqrt x) ^ 2 = 1 + 2 * Real.sqrt x + x := by
      rw [add_sq, one_pow, Real.sq_sqrt hx]; ring
    rw [hsq]; linarith [Real.sqrt_nonneg x]
  have sqrt_add_le' : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b →
      Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    have hnn : 0 ≤ Real.sqrt a + Real.sqrt b := by
      linarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
    rw [← Real.sqrt_sq hnn]
    refine Real.sqrt_le_sqrt ?_
    have hsq : (Real.sqrt a + Real.sqrt b) ^ 2 = a + 2 * (Real.sqrt a * Real.sqrt b) + b := by
      rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
    rw [hsq]
    have h2 : 0 ≤ 2 * (Real.sqrt a * Real.sqrt b) := by positivity
    linarith
  refine ⟨hHQ, ?_, ?_⟩
  · rw [Work.Spaces.HkNorm]
    have hS5 := Work.Spaces.HkSq_nonneg α 5 w
    calc Real.sqrt (Work.Spaces.HkSq α 4
            (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam))
        ≤ Real.sqrt (16 * Ktot * (1 + Work.Spaces.HkSq α 5 w)) := Real.sqrt_le_sqrt hsq4
      _ = Real.sqrt (16 * Ktot) * Real.sqrt (1 + Work.Spaces.HkSq α 5 w) := by
          rw [Real.sqrt_mul (by positivity)]
      _ ≤ Real.sqrt (16 * Ktot) * (1 + Real.sqrt (Work.Spaces.HkSq α 5 w)) :=
          mul_le_mul_of_nonneg_left (sqrt_one_add_le hS5) (Real.sqrt_nonneg _)
      _ = Real.sqrt (16 * Ktot) * (1 + Work.Spaces.HkNorm α 5 w) := by rw [hN5]
      _ ≤ C * (1 + Work.Spaces.HkNorm α 5 w) :=
          mul_le_mul_of_nonneg_right hCsq (by linarith [Work.Spaces.HkNorm_nonneg α 5 w])
  · rw [Work.Spaces.HkNorm]
    have hS6 := Work.Spaces.HkSq_nonneg α 6 w
    have hS7 := Work.Spaces.HkSq_nonneg α 7 w
    have hsq : Real.sqrt ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2)
        ≤ (1 + Work.Spaces.HkNorm α 7 w) + (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by
      have h1 : Real.sqrt (1 + Work.Spaces.HkSq α 7 w) ≤ 1 + Work.Spaces.HkNorm α 7 w := by
        refine le_trans (sqrt_one_add_le hS7) (le_of_eq ?_)
        rw [hN7]
      have h2 : Real.sqrt ((1 + Work.Spaces.HkSq α 6 w) ^ 2)
          = 1 + Work.Spaces.HkSq α 6 w := Real.sqrt_sq (by linarith)
      have h3 : 1 + Work.Spaces.HkSq α 6 w ≤ (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by
        rw [hN6]
        nlinarith [Real.sq_sqrt hS6, Real.sqrt_nonneg (Work.Spaces.HkSq α 6 w)]
      calc Real.sqrt ((1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) ^ 2)
          ≤ Real.sqrt (1 + Work.Spaces.HkSq α 7 w)
              + Real.sqrt ((1 + Work.Spaces.HkSq α 6 w) ^ 2) :=
            sqrt_add_le' (by linarith) (by positivity)
        _ = Real.sqrt (1 + Work.Spaces.HkSq α 7 w) + (1 + Work.Spaces.HkSq α 6 w) := by rw [h2]
        _ ≤ (1 + Work.Spaces.HkNorm α 7 w) + (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by
            linarith [h1, h3]
    calc Real.sqrt (Work.Spaces.HkSq α 6
            (Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWBlk α Φs w Φg μ lam))
        ≤ Real.sqrt (16 * Ktot * ((1 + Work.Spaces.HkSq α 7 w)
            + (1 + Work.Spaces.HkSq α 6 w) ^ 2)) := Real.sqrt_le_sqrt hsq6
      _ = Real.sqrt (16 * Ktot) * Real.sqrt ((1 + Work.Spaces.HkSq α 7 w)
            + (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by rw [Real.sqrt_mul (by positivity)]
      _ ≤ Real.sqrt (16 * Ktot) * ((1 + Work.Spaces.HkNorm α 7 w)
            + (1 + Work.Spaces.HkNorm α 6 w) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
      _ ≤ C * ((1 + Work.Spaces.HkNorm α 7 w) + (1 + Work.Spaces.HkNorm α 6 w) ^ 2) :=
          mul_le_mul_of_nonneg_right hCsq (by
            have h7 := Work.Spaces.HkNorm_nonneg α 7 w
            have h6 := Work.Spaces.HkNorm_nonneg α 6 w
            positivity)
      _ = C * (1 + Work.Spaces.HkNorm α 7 w) + C * (1 + Work.Spaces.HkNorm α 6 w) ^ 2 := by ring


end Work.FTS.StrongEps.E4R3.RawE6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.EpsWPSemitameAux.BlkMu =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.RawE6Aux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem bdata_blkMu (C₀ : ℝ) :
    ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ KM : ℝ, 0 < KM ∧ ∀ {Φs w Φg : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      |Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w Φg| ≤ 1 / 2 →
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.BData α w KM
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkMu α Φs w Φg) := by
  intro α hαI
  obtain ⟨KAK, hKAKpos, hAK⟩ := Work.FTS.StrongPersist.AK6_mem_norm
  obtain ⟨CT, hCTpos, hCT⟩ := Work.FTS.StrongPersist.L3Aux.Transport_L12_zero_le
  set KM : ℝ := (1 + CT * C₀) ^ 2 * KAK ^ 2 + 1 with hKM
  have hKMpos : 0 < KM := by rw [hKM]; positivity
  refine ⟨KM, hKMpos, ?_⟩
  intro Φs w Φg hcls hXw hμ
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hAKmem : Work.Spaces.HkMem α 6 (Work.Construction.AK α) := (hAK α hα0 hα1).1
  have hAKnorm : Work.Spaces.HkNorm α 6 (Work.Construction.AK α) ≤ KAK := (hAK α hα0 hα1).2
  have hAKsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  have hm4w : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hcls.reg 4 (by norm_num) hcls.mem
  have htr : |Work.Coercivity.L12f (Work.Coercivity.Transport w) 0|
      ≤ CT * Work.FTS.Nonlin.Xn α w := hCT α w hα0 hα1 hm4w
  -- `C₀ ≥ 0`, so that `C₀ α² ≤ C₀` for `α ≤ 1`
  have hC₀0 : 0 ≤ C₀ := by
    by_contra hneg
    have hlt : C₀ < 0 := lt_of_not_ge hneg
    have hprod : C₀ * α ^ 2 < 0 := mul_neg_of_neg_of_pos hlt (by positivity)
    have hxw : 0 ≤ Work.FTS.Nonlin.Xn α w := Work.Spaces.HkNorm_nonneg α 4 w
    linarith [hXw, hprod, hxw]
  -- the modulation identity: `2α μ = mubar + L₁₂(Transport w)(0)`
  have hkey := Work.Construction.two_mul_mufunS α
    (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
    (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) w
    (ne_of_gt hα0)
  have hmuBlk : Work.Construction.mufunS α
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) w
      = Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w Φg := rfl
  rw [hmuBlk] at hkey
  have hL12eq : Work.Construction.L12 (Work.Coercivity.Transport w) 0
      = Work.Coercivity.L12f (Work.Coercivity.Transport w) 0 := rfl
  rw [hL12eq] at hkey
  have hmubar : Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ))
      = 2 * α * Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w Φg
        - Work.Coercivity.L12f (Work.Coercivity.Transport w) 0 := by
    linarith [hkey]
  -- the bound on the scalar `mubar`
  have h1 : |2 * α * Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w Φg| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hα0]
    have hprod : α * |Work.FTS.StrongEps.E4R3.Apriori4Proofs.muBlk α Φs w Φg| ≤ 1 / 2 := by
      have hmm := mul_le_mul hα1 hμ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      linarith [hmm]
    linarith [hprod]
  have h2 : |Work.Coercivity.L12f (Work.Coercivity.Transport w) 0|
      ≤ CT * (C₀ * α ^ 2) := le_trans htr (mul_le_mul_of_nonneg_left hXw hCTpos.le)
  have h4 : α ^ 2 ≤ 1 := by
    have h := mul_self_le_mul_self hα0.le hα1
    nlinarith [h]
  have h3 : CT * (C₀ * α ^ 2) ≤ CT * C₀ := by
    refine mul_le_mul_of_nonneg_left ?_ hCTpos.le
    have hle : α ^ 2 * C₀ ≤ 1 * C₀ := mul_le_mul_of_nonneg_right h4 hC₀0
    linarith [hle]
  have hMBex : |Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ))|
      ≤ 1 + CT * C₀ := by
    rw [hmubar]
    refine (abs_sub _ _).trans ?_
    linarith [h1, h2, h3]
  have hMB0 : 0 ≤ 1 + CT * C₀ := by
    have hC0 : 0 ≤ CT * C₀ := mul_nonneg hCTpos.le hC₀0
    linarith
  -- `AK`'s level-six energy
  have hAKsq : Work.Spaces.HkSq α 6 (Work.Construction.AK α) ≤ KAK ^ 2 := by
    have hs := Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 (Work.Construction.AK α))
    rw [Work.Spaces.HkNorm] at hAKnorm
    have h2 := Real.sqrt_nonneg (Work.Spaces.HkSq α 6 (Work.Construction.AK α))
    nlinarith [hAKnorm, h2, hs, hKAKpos]
  have hAKsq4 : Work.Spaces.HkSq α 4 (Work.Construction.AK α) ≤ KAK ^ 2 :=
    le_trans (Work.FTS.StrongPersist.H6Aux.HkSq_mono_order α (by norm_num) hAKmem) hAKsq
  -- the block is the scalar `mubar` times `AK α`
  have hshape : Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkMu α Φs w Φg
      = fun z θ => Work.Construction.mubar
          (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
          (Work.Construction.N α (Work.Construction.Ftot α w)
            (fun z θ => Φs z θ + Φg z θ)) * Work.Construction.AK α z θ := rfl
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkMu α Φs w Φg) := by
    rw [hshape]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul _ hAKsmo
  have hmem : Work.Spaces.HkMem α 6
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blkMu α Φs w Φg) := by
    rw [hshape]
    exact Work.FTS.LocData.HkMem_const_mul α 6 _ hAKmem
  have hMBsq : (Work.Construction.mubar
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ))) ^ 2
      ≤ (1 + CT * C₀) ^ 2 := by
    calc (Work.Construction.mubar _ _) ^ 2 = |Work.Construction.mubar _ _| ^ 2 := (sq_abs _).symm
      _ ≤ (1 + CT * C₀) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hMBex 2
  have hconst : KAK ^ 2 * (1 + CT * C₀) ^ 2 ≤ KM := by
    rw [hKM]; linarith [sq_nonneg KAK, sq_nonneg (1 + CT * C₀)]
  refine ⟨hsm, hmem, ?_, ?_⟩
  · rw [hshape, Work.FTS.StrongEps.HkSq_const_mul]
    have hSs5 : 0 ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
    have h1 : Work.Spaces.HkSq α 4 (Work.Construction.AK α)
        * (Work.Construction.mubar _ _) ^ 2 ≤ KAK ^ 2 * (1 + CT * C₀) ^ 2 :=
      mul_le_mul hAKsq4 hMBsq (sq_nonneg _) (sq_nonneg KAK)
    have h2 : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith
    nlinarith [h1, hconst, hSs5, hKMpos]
  · rw [hshape, Work.FTS.StrongEps.HkSq_const_mul]
    have hSs6 : 0 ≤ Work.Spaces.HkSq α 6 w := Work.Spaces.HkSq_nonneg α 6 w
    have hSs7 : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
    have h1 : Work.Spaces.HkSq α 6 (Work.Construction.AK α)
        * (Work.Construction.mubar _ _) ^ 2 ≤ KAK ^ 2 * (1 + CT * C₀) ^ 2 :=
      mul_le_mul hAKsq hMBsq (sq_nonneg _) (sq_nonneg KAK)
    have h2 : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by linarith
    have h3 : (0 : ℝ) ≤ KM * (1 + Work.Spaces.HkSq α 6 w) ^ 2 := by positivity
    nlinarith [h1, hconst, hSs7, h2, h3, hKMpos]

end Work.FTS.StrongEps.E4R3.RawE6Aux
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.slice_inputs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

theorem slice_inputs {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp a) u →
      Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp a) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp a) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp a) E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp a) Cs Φs)
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp a) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ, 0 ≤ τ → ∃ M L Mf : ℝ,
      ContDiffOn ℝ 3 (Function.uncurry
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) Work.Construction.Qd ∧
      Work.FTS.StreamBdryIface.SlotBd (Work.FTS.Regularity.pExp a)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) M ∧
      Work.FTS.StreamBdryIface.SrcOK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) L Mf := by
  exact slice_inputs_of_pieces ha ha13 hEll hEL hStar hSol hOK hreg hG
    (fun τ hτ => srcOK_Ftau ha ha13 hreg hG τ hτ)
    (fun τ hτ => residual_slot_jetsB ha ha13 hEll hEL hStar hSol hOK τ hτ)
    (fun τ hτ => by
      obtain ⟨C, hC0, -, hU, -, hV⟩ := theta_part_jets ha ha13 hOK hreg hG τ hτ
      exact ⟨C, hC0, hU, hV⟩)

end Work.FTS_StreamBdry.Inputs
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB5.sb5_decay =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB5.sb5_decay` — decay of the `U`-slot part outside the support

The producer `sb5_decay`, assembled from `SB5.Core.sb5_decay_core` (Phragmén–Lindelöf comparison
for the ground-state operator and dilate difference quotients) and the SB3 bounds.
See `Submission/Work/FTS_StreamBdry/SB5/Prep.lean`, `Ang.lean`, `Core.lean` for the helpers.
-/

namespace Work.FTS_StreamBdry.SB5

open scoped Real Topology
open Set Filter MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## §11 The producer -/
end
end Work.FTS_StreamBdry.SB5
end
