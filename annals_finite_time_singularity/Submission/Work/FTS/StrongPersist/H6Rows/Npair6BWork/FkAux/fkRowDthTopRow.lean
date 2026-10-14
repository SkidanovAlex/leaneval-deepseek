import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDth6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDthShiftLow
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowsAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkShiftHigh_shiftF
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FKstarSlotPiece
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NSplit6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSupO
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.PkgJets.L12jets_classC
import Submission.Work.FTS_EllLimOK.ThetaJets.Theta_jets_le
import Submission.Work.FTS_MuLamOK.Main
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.NS6.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Row6.NS6

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## `C⁶`-bookkeeping on the open quadrant -/

/-- `C⁶`-regularity of a two-variable function on the open quadrant `Q0`. -/
notation "CD6" u:max => ContDiffOn ℝ 6 (Function.uncurry u) Work.FTS.EllipticEst.Q0

theorem cd6_congr {u v : Fn}
    (h : ∀ z θ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → u z θ = v z θ) (hu : CD6 u) : CD6 v :=
  hu.congr (fun p hp => (h p.1 p.2 hp).symm)

theorem cd6_add {u v : Fn} (hu : CD6 u) (hv : CD6 v) :
    CD6 (fun z θ => u z θ + v z θ) := by
  have h : Function.uncurry (fun z θ => u z θ + v z θ)
      = Function.uncurry u + Function.uncurry v := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]; exact hu.add hv

theorem cd6_mul {u v : Fn} (hu : CD6 u) (hv : CD6 v) :
    CD6 (fun z θ => u z θ * v z θ) := by
  have h : Function.uncurry (fun z θ => u z θ * v z θ)
      = Function.uncurry u * Function.uncurry v := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]; exact hu.mul hv

theorem cd6_const_mul (c : ℝ) {u : Fn} (hu : CD6 u) : CD6 (fun z θ => c * u z θ) := by
  have h : Function.uncurry (fun z θ => c * u z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry u p := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]; exact (contDiffOn_const (c := c)).mul hu

theorem cd6_radial {X : ℝ → ℝ} (hX : ContDiffOn ℝ 6 X (Set.Ioi 0)) :
    CD6 (fun z (_ : ℝ) => X z) := by
  have h : Function.uncurry (fun z (_ : ℝ) => X z) = fun p : ℝ × ℝ => X p.1 := rfl
  rw [h]
  exact hX.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

theorem cd6_sinSq : CD6 (fun (_ : ℝ) (θ : ℝ) => Real.sin θ ^ 2) :=
  (Work.FTS.StrongPersist.H6Pair6Aux.so_snd (by fun_prop)).forall 6

theorem cd6_inv_add_one (c : ℝ) : CD6 (fun z (_ : ℝ) => c / (1 + z)) := by
  have h1 : ContDiffOn ℝ 6 (fun z : ℝ => (1 + z)⁻¹) (Set.Ioi 0) := by
    refine (contDiffOn_const.add contDiffOn_id).inv ?_
    intro z hz
    have hz0 : (0 : ℝ) < z := hz
    show ¬ (1 + z = 0)
    intro h
    linarith
  have h2 : ContDiffOn ℝ 6 (fun z : ℝ => c * (1 + z)⁻¹) (Set.Ioi 0) :=
    (contDiffOn_const (c := c)).mul h1
  refine cd6_congr (u := fun z (_ : ℝ) => c * (1 + z)⁻¹) (fun z θ _ => ?_) (cd6_radial h2)
  rw [div_eq_mul_inv]

/-- A point of the open quadrant has `z ≠ 0`. -/
theorem ne_zero_of_mem {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) : z ≠ 0 :=
  ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp h).1

/-- A point of the open quadrant has `1 + z ≠ 0`. -/
theorem ne_add_one_of_mem {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    (1 : ℝ) + z ≠ 0 := by
  have hz := (Work.FTS.EllipticEst.mem_Q0.mp h).1
  positivity

/-! ## The two elementary shift identities -/

/-- `((z+1)/z·X) · (c·(z/(1+z)·Y)) = c·X·Y`: the product of a coefficient written with the
radial factor `(z+1)/z` and a slot written with the factor `z/(1+z)` is the plain product. -/
theorem shift_mul (c X Y z : ℝ) (hz : z ≠ 0) (h1z : (1 : ℝ) + z ≠ 0) :
    ((z + 1) / z * X) * (c * (z / (1 + z) * Y)) = c * X * Y := by
  field_simp
  ring

/-- The same identity for the `(F_*,K)`-pieces, where the star angular moment
`FK (F_*) z = α·2z/(1+z)²` replaces the coefficient. -/
theorem shift_fk (α Y z : ℝ) (h1z : (1 : ℝ) + z ≠ 0) :
    ((-α) / (1 + z)) * (z / (1 + z) * Y)
      = -(1 / 2) * (α * (2 * z / (1 + z) ^ 2)) * Y := by
  field_simp


/-- The `-2α`-variant of `shift_fk_sq` (the form in which the `sin²θ`-pieces present the
star angular moment `(F_*,K) = α·2z/(1+z)²`). -/
theorem shift_fk_sq2 (α S Y z : ℝ) (h1z : (1 : ℝ) + z ≠ 0) :
    ((-2 * α) / (1 + z)) * (S * (z / (1 + z) * Y))
      = -(S) * (α * (2 * z / (1 + z) ^ 2)) * Y := by
  field_simp

/-- **Packaging helper**: a function `X` which is `C⁶` and `ℋ⁶` and agrees with `Y` on the open
quadrant is itself `C⁶` and `ℋ⁶`. -/
theorem piece_both {α : ℝ} (X Y : Fn) (hX : CD6 X) (hm : Work.Spaces.HkMem α 6 X)
    (h : ∀ z θ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → X z θ = Y z θ) :
    CD6 Y ∧ Work.Spaces.HkMem α 6 Y :=
  ⟨cd6_congr h hX, Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd h hm⟩

/-! ## Iteration over `Finset.range` -/

theorem hkMem_sum_range {α : ℝ} :
    ∀ (N : ℕ) (u : ℕ → Fn), (∀ k < N, CD6 (u k)) → (∀ k < N, Work.Spaces.HkMem α 6 (u k)) →
      CD6 (fun z θ => ∑ k ∈ Finset.range N, u k z θ) ∧
      Work.Spaces.HkMem α 6 (fun z θ => ∑ k ∈ Finset.range N, u k z θ) := by
  intro N
  induction N with
  | zero =>
      intro u _ _
      have h0 : (fun z θ => ∑ k ∈ Finset.range 0, u k z θ) = fun _ _ : ℝ => 0 := by
        funext z θ; simp
      refine ⟨?_, ?_⟩
      · rw [h0]; exact contDiffOn_const
      · rw [h0]; exact Work.FTS.EllipticEst.HkMem_zero α 6
  | succ n ih =>
      intro u hcd hmem
      obtain ⟨hcdn, hmemn⟩ := ih u (fun k hk => hcd k (Nat.lt_succ_of_lt hk))
        (fun k hk => hmem k (Nat.lt_succ_of_lt hk))
      have hsn : (fun z θ => ∑ k ∈ Finset.range (n + 1), u k z θ)
          = fun z θ => (∑ k ∈ Finset.range n, u k z θ) + u n z θ := by
        funext z θ; rw [Finset.sum_range_succ]
      rw [hsn]
      exact ⟨cd6_add hcdn (hcd n (Nat.lt_succ_self n)),
        (Work.FTS.StrongPersist.HkAddFin hcdn (hcd n (Nat.lt_succ_self n)) hmemn
          (hmem n (Nat.lt_succ_self n))).1⟩

/-! ## The bundled level-six data of the slice

The fields are exactly the slice data that `L6Ctx` supplies (`H6Adm` of the slice, the
order-seven honesty, `SmoothOpen` of the perturbation and star stream functions, the
level-six star package and the level-six perturbation package), plus the `ℋ⁶`-membership of
the angular moment `FK f` (which carries the existential constant of `N6_fkH`). -/
structure Data (α Ce Cs : ℝ) (f Ef Φs : Fn) : Prop where
  /-- `0 < α ≤ 1`. -/
  hα : 0 < α
  hα1 : α ≤ 1
  /-- the slice is smooth on the open quadrant. -/
  fsm : Work.FTS.EllipticEst.SmoothOpen f
  /-- the slice is honest in `ℋ⁶`. -/
  fm : Work.Spaces.HkMem α 6 f
  /-- the slice is honest in `ℋ⁷` (needed for `D_θ`, `D_z` and `L₁₂`-smoothness). -/
  f7 : Work.Spaces.HkMem α 7 f
  /-- the perturbation stream function is smooth on the open quadrant. -/
  Efsm : Work.FTS.EllipticEst.SmoothOpen Ef
  /-- the star stream function is smooth on the open quadrant. -/
  Φssm : Work.FTS.EllipticEst.SmoothOpen Φs
  /-- the zero mode of `L₁₂` vanishes. -/
  l12 : Work.Construction.L12 f 0 = 0
  /-- the level-six star package. -/
  star : Work.FTS.StrongPersist.StarPkg6 α Cs Φs
  /-- the level-six perturbation package. -/
  ell : Work.FTS.StrongPersist.EllPkgK α 6 Ce f Ef
  /-- the angular moment `FK f` is honest in `ℋ⁶`. -/
  kfm : Work.Spaces.HkMem α 6 (fun z (_ : ℝ) => Work.Construction.FK f z)
  /-- the slice is in the honest level-six class (for the `FK f`-fields of the row). -/
  hadm : Work.FTS.StrongPersist.H6Adm α f
  /-- the `ℋ⁶ × ℋ⁶` product rule on the open-quadrant class (`N6_prod`). -/
  mulSm : ∀ (u v : Fn), Work.FTS.EllipticEst.SmoothOpen u → Work.Spaces.HkMem α 6 u →
    Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α 6 v →
    Work.Spaces.HkMem α 6 (fun z θ => u z θ * v z θ)

/-! ## The derived coefficient/slot data -/

section DataLemmas

variable {α Ce Cs : ℝ} {f Ef Φs : Fn}

theorem Data.phiTs (D : Data α Ce Cs f Ef Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.PhiTs α Φs) :=
  (Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs D.hα D.hα1 D.Φssm).1

theorem Data.hR1w (D : Data α Ce Cs f Ef Φs) : Work.Spaces.WlInfMem α 6
    (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) :=
  D.star.RW6.1

theorem Data.hU1w (D : Data α Ce Cs f Ef Φs) : Work.Spaces.WlInfMem α 6
    (fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      / Work.Construction.s2 θ)) := D.star.UszW6.1


def Data.reg (D : Data α Ce Cs f Ef Φs) :=
  Work.FTS.PhiStar.StarPkgo2Aux.FieldRegularity α (Work.FTS.VocabO2.PhiTs α Φs) D.phiTs

theorem Data.hR1c (D : Data α Ce Cs f Ef Φs) : CD6 (fun z θ => (z + 1) / z
    * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) := D.reg.1.forall 6


theorem Data.hV1zw (D : Data α Ce Cs f Ef Φs) : Work.Spaces.WlInfMem α 6
    (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) :=
  D.star.VzW6.1

theorem Data.hV1zc (D : Data α Ce Cs f Ef Φs) : CD6
    (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) :=
  D.reg.2.2.1.forall 6

theorem Data.hU1c (D : Data α Ce Cs f Ef Φs) : CD6 (fun z θ => (z + 1) / z
    * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
  D.reg.2.2.2.2.1.forall 6

theorem Data.hR2s (D : Data α Ce Cs f Ef Φs) : Work.FTS.EllipticEst.SmoothOpen
    (Work.Construction.Rop α (Work.Construction.PhiTil α f Ef)) := D.ell.R.1.1

theorem Data.hR2m (D : Data α Ce Cs f Ef Φs) : Work.Spaces.HkMem α 6
    (Work.Construction.Rop α (Work.Construction.PhiTil α f Ef)) := D.ell.R.1.2

theorem Data.hU2s (D : Data α Ce Cs f Ef Φs) : Work.FTS.EllipticEst.SmoothOpen
    (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
      / Work.Construction.s2 θ) := D.ell.U.1.1

theorem Data.hU2m (D : Data α Ce Cs f Ef Φs) : Work.Spaces.HkMem α 6
    (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
      / Work.Construction.s2 θ) := D.ell.U.1.2

theorem Data.hV2s (D : Data α Ce Cs f Ef Φs) : Work.FTS.EllipticEst.SmoothOpen
    (Work.Construction.Vop (Work.Construction.PhiTil α f Ef)) := D.ell.V.1.1

theorem Data.hV2m (D : Data α Ce Cs f Ef Φs) : Work.Spaces.HkMem α 6
    (Work.Construction.Vop (Work.Construction.PhiTil α f Ef)) := D.ell.V.1.2

theorem Data.hR2c (D : Data α Ce Cs f Ef Φs) :
    CD6 (Work.Construction.Rop α (Work.Construction.PhiTil α f Ef)) := D.hR2s.forall 6

theorem Data.hU2c (D : Data α Ce Cs f Ef Φs) : CD6 (fun z θ =>
    Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ / Work.Construction.s2 θ) :=
  D.hU2s.forall 6

theorem Data.hV2c (D : Data α Ce Cs f Ef Φs) :
    CD6 (Work.Construction.Vop (Work.Construction.PhiTil α f Ef)) := D.hV2s.forall 6

theorem Data.hS1w (D : Data α Ce Cs f Ef Φs) :
    Work.Spaces.WlInfMem α 6 (Work.Construction.Fstar α) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.Fstar_W6
  exact (h α D.hα D.hα1).1

theorem Data.hS2w (D : Data α Ce Cs f Ef Φs) :
    Work.Spaces.WlInfMem α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.DthFstar_W6
  exact (h α D.hα D.hα1).1

theorem Data.hS3w (D : Data α Ce Cs f Ef Φs) :
    Work.Spaces.WlInfMem α 6 (Work.Spaces.Dz (Work.Construction.Fstar α)) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.DzFstar_W6
  exact (h α D.hα D.hα1).1

theorem Data.hSqW (D : Data α Ce Cs f Ef Φs) :
    Work.Spaces.WlInfMem α 6 (fun (_ : ℝ) (θ : ℝ) => Real.sin θ ^ 2) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.WlInf_sinSq
  exact (h α D.hα D.hα1).1

theorem Data.hS1s (D : Data α Ce Cs f Ef Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
  Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α

theorem Data.hS1c (D : Data α Ce Cs f Ef Φs) : CD6 (Work.Construction.Fstar α) :=
  D.hS1s.forall 6

theorem Data.hS2c (D : Data α Ce Cs f Ef Φs) :
    CD6 (Work.Spaces.Dth (Work.Construction.Fstar α)) := D.hS1s.Dth.forall 6

theorem Data.hS3c (D : Data α Ce Cs f Ef Φs) :
    CD6 (Work.Spaces.Dz (Work.Construction.Fstar α)) := D.hS1s.Dz.forall 6

theorem Data.hSh1s (D : Data α Ce Cs f Ef Φs) : Work.FTS.EllipticEst.SmoothOpen
    (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
  exact (h α ⟨D.hα, D.hα1⟩).1.1

theorem Data.hSh1m (D : Data α Ce Cs f Ef Φs) : Work.Spaces.HkMem α 6
    (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
  exact (h α ⟨D.hα, D.hα1⟩).1.2.1

theorem Data.hSh2s (D : Data α Ce Cs f Ef Φs) : Work.FTS.EllipticEst.SmoothOpen
    (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
  exact (h α ⟨D.hα, D.hα1⟩).2.1.1

theorem Data.hSh2m (D : Data α Ce Cs f Ef Φs) : Work.Spaces.HkMem α 6
    (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
  exact (h α ⟨D.hα, D.hα1⟩).2.1.2.1

theorem Data.hSh3s (D : Data α Ce Cs f Ef Φs) : Work.FTS.EllipticEst.SmoothOpen
    (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
  exact (h α ⟨D.hα, D.hα1⟩).2.2.1

theorem Data.hSh3m (D : Data α Ce Cs f Ef Φs) : Work.Spaces.HkMem α 6
    (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
  exact (h α ⟨D.hα, D.hα1⟩).2.2.2.1

def Data.hdesc (D : Data α Ce Cs f Ef Φs) :=
  Work.FTS.IPGen.HkMem_descent (α := α) (k := 6) (f := f) (by linarith [D.hα]) D.fsm D.f7

theorem Data.hfcd (D : Data α Ce Cs f Ef Φs) : CD6 f := D.fsm.forall 6

theorem Data.hTfcd (D : Data α Ce Cs f Ef Φs) : CD6 (Work.Spaces.Dth f) :=
  D.fsm.Dth.forall 6

theorem Data.hTzcd (D : Data α Ce Cs f Ef Φs) : CD6 (Work.Spaces.Dz f) :=
  D.fsm.Dz.forall 6

theorem Data.hTfm (D : Data α Ce Cs f Ef Φs) : Work.Spaces.HkMem α 6 (Work.Spaces.Dth f) :=
  D.hdesc.2.1

theorem Data.hTzm (D : Data α Ce Cs f Ef Φs) : Work.Spaces.HkMem α 6 (Work.Spaces.Dz f) :=
  D.hdesc.2.2

theorem Data.hSh4s (D : Data α Ce Cs f Ef Φs) : CD6 (fun z θ => z / (1 + z) * f z θ) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.mulPhi6
  exact (h D.hα D.hα1 D.fsm D.fm).1.forall 6

theorem Data.hSh4m (D : Data α Ce Cs f Ef Φs) : Work.Spaces.HkMem α 6
    (fun z θ => z / (1 + z) * f z θ) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.mulPhi6
  exact (h D.hα D.hα1 D.fsm D.fm).2.1

theorem Data.hSh5s (D : Data α Ce Cs f Ef Φs) : CD6
    (fun z θ => z / (1 + z) * Work.Spaces.Dth f z θ) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.mulPhi6
  exact (h D.hα D.hα1 D.fsm.Dth D.hTfm).1.forall 6

theorem Data.hSh5m (D : Data α Ce Cs f Ef Φs) : Work.Spaces.HkMem α 6
    (fun z θ => z / (1 + z) * Work.Spaces.Dth f z θ) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.mulPhi6
  exact (h D.hα D.hα1 D.fsm.Dth D.hTfm).2.1

theorem Data.hSh6s (D : Data α Ce Cs f Ef Φs) : CD6
    (fun z θ => z / (1 + z) * Work.Spaces.Dz f z θ) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.mulPhi6
  exact (h D.hα D.hα1 D.fsm.Dz D.hTzm).1.forall 6

theorem Data.hSh6m (D : Data α Ce Cs f Ef Φs) : Work.Spaces.HkMem α 6
    (fun z θ => z / (1 + z) * Work.Spaces.Dz f z θ) := by
  obtain ⟨C, -, h⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.mulPhi6
  exact (h D.hα D.hα1 D.fsm.Dz D.hTzm).2.1

theorem Data.hFK3 (D : Data α Ce Cs f Ef Φs) : (fun z (_ : ℝ) => Work.Construction.FK f z)
    = fun z (_ : ℝ) => 3 * Work.Elliptic.Fstar f z := by
  funext z θ
  exact congrFun (Work.FTS.StrongPersist.L3Rhs.NfkAux.fk_eq_three_Fstar f) z

theorem Data.hFstarf_sm (D : Data α Ce Cs f Ef Φs) :
    ContDiffOn ℝ 6 (fun z : ℝ => Work.Elliptic.Fstar f z) (Set.Ioi 0) :=
  Work.FTS.EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk α 7 f D.fsm D.f7 (by norm_num)

theorem Data.hKfcd (D : Data α Ce Cs f Ef Φs) :
    CD6 (fun z (_ : ℝ) => Work.Construction.FK f z) := by
  refine cd6_congr (u := fun z (_ : ℝ) => 3 * Work.Elliptic.Fstar f z) (fun z θ _ => ?_)
    (cd6_const_mul 3 (cd6_radial D.hFstarf_sm))
  rw [← congrFun (congrFun D.hFK3 z) θ]

theorem Data.wlInfInv (D : Data α Ce Cs f Ef Φs) (c : ℝ) :
    Work.Spaces.WlInfMem α 6 (fun z (_ : ℝ) => c / (1 + z)) :=
  Work.FTS.StrongPersist.H6Row6.radial_inv_wlInf6 c α D.hα D.hα1

theorem Data.cd6Inv (D : Data α Ce Cs f Ef Φs) (c : ℝ) :
    CD6 (fun z (_ : ℝ) => c / (1 + z)) :=
  cd6_inv_add_one c

theorem Data.hKinw (D : Data α Ce Cs f Ef Φs) :
    Work.Spaces.WlInfMem α 6 (fun z (_ : ℝ) => (-α) / (1 + z)) :=
  D.wlInfInv (-α)

theorem Data.hKinc (D : Data α Ce Cs f Ef Φs) : CD6 (fun z (_ : ℝ) => (-α) / (1 + z)) :=
  D.cd6Inv (-α)

theorem Data.hKin2w (D : Data α Ce Cs f Ef Φs) :
    Work.Spaces.WlInfMem α 6 (fun z (_ : ℝ) => (-2 * α) / (1 + z)) :=
  D.wlInfInv (-2 * α)

theorem Data.hKin2c (D : Data α Ce Cs f Ef Φs) : CD6 (fun z (_ : ℝ) => (-2 * α) / (1 + z)) :=
  D.cd6Inv (-2 * α)

/-- **The seven `FK f ×`-membership fields of the row** (`Npair6BWork.hkMem_fk_mul`): the
angular moment `FK f` paired with `f`, `D_θf`, `F_*`, `D_θF_*` and the three `sin²θ`-versions. -/
theorem Data.fk7 (D : Data α Ce Cs f Ef Φs) :
    (Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.FK f z * f z θ) ∧
     Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.FK f z
        * Work.Spaces.Dth f z θ) ∧
     Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.FK f z
        * Work.Construction.Fstar α z θ) ∧
     Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.FK f z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
     Work.Spaces.HkMem α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
        * f z θ) ∧
     Work.Spaces.HkMem α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
        * Work.Spaces.Dth f z θ) ∧
     Work.Spaces.HkMem α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
        * Work.Construction.Fstar α z θ)) :=
  Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul α ⟨D.hα, D.hα1⟩ f
    (Work.FTS.Nonlin.Xn α f)
    (Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.datData_of_H6Adm D.hadm D.f7 le_rfl)

end DataLemmas

end Work.FTS.StrongPersist.H6Row6.NS6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDthTopRow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option maxHeartbeats 1600000

/-- **Fubini for a radial coefficient.**  For a product-integrable `p ↦ r p.1 · G p.1 p.2` with
`r` depending on `z` alone, the product integral is the iterated integral with `r z` pulled out of
the angular integral.  (`integral_const_mul` is unconditional, so no integrability of the slices
is needed.) -/
private lemma integral_prod_radial {r : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => r p.1 * G p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∫ p, r p.1 * G p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ z in Work.Spaces.Iz, r z * (∫ θ in Work.Spaces.Iθ, G z θ) := by
  rw [MeasureTheory.integral_prod _ hInt]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact MeasureTheory.integral_const_mul (r z) (fun θ => G z θ)

/-- Elementary arithmetic: `(7)·(64·(A·X)) ≤ (448(A+1)+1)·a·X` for `A, X ≥ 0` and `a ≥ 1`
(the factor `64 = 2^6` bounds the binomial coefficients of the Leibniz expansion, and
`a = α^{-3} ≥ 1` is the `α`-power price). -/
private lemma final_arith {A X a : ℝ} (hA : 0 ≤ A) (hX : 0 ≤ X) (ha : 1 ≤ a) :
    (7 : ℝ) * (64 * (A * X)) ≤ (448 * (A + 1) + 1) * a * X := by
  nlinarith [mul_nonneg hA hX, mul_nonneg (mul_nonneg hA hX) (sub_nonneg.mpr ha),
    sq_nonneg X]

/-- **The assembly of `fkRowDthTopRow`** (the `(a,b) = (0,6)` angular-moment slot), with the three
per-summand inputs (the shifted slots for `1 ≤ b₁ ≤ 3` and `4 ≤ b₁ ≤ 6`, and the
product-integrability of the `b₁ = 0` slot) as explicit hypotheses.  This is the (private)
`fkRowDth6_core` of `FkAux/fkRowDth6.lean`, re-created here because "private" is not importable. -/
theorem fkRowDthTopRow_core
    (hLow : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ) (b₁ : ℕ),
        Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
        1 ≤ b₁ → b₁ ≤ 3 → Work.FTS.TransportS.IsLeafW α 0 ρ →
        (MeasureTheory.Integrable (fun p : ℝ × ℝ =>
            Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
              * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                  * Work.Spaces.mixed 6 0 f p.1 p.2))
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
          |∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
                * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                    * Work.Spaces.mixed 6 0 f p.1 p.2)
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
            ≤ C * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)))
    (hHigh : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ) (b₁ : ℕ),
        Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
        4 ≤ b₁ → b₁ ≤ 6 → Work.FTS.TransportS.IsLeafW α 0 ρ →
        (MeasureTheory.Integrable (fun p : ℝ × ℝ =>
            Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
              * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                  * Work.Spaces.mixed 6 0 f p.1 p.2))
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
          |∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
                * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                    * Work.Spaces.mixed 6 0 f p.1 p.2)
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
            ≤ C * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)))
    (hZero : ∀ α ∈ Set.Ioc 0 1,
      ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ),
        Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
        Work.FTS.TransportS.IsLeafW α 0 ρ →
        MeasureTheory.Integrable (fun p : ℝ × ℝ =>
            Work.Construction.FK f p.1
              * (ρ p.1 p.2 * Work.Spaces.mixed 6 1 f p.1 p.2
                  * Work.Spaces.mixed 6 0 f p.1 p.2))
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ),
        Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
        Work.FTS.TransportS.IsLeafW α 0 ρ →
        |Work.FTS.TransportS.slotPairing ρ 0 6
            (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) f|
          ≤ C * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M)
              * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨CL, hCLpos, hLow⟩ := hLow
  obtain ⟨CH, _hCHpos, hHigh⟩ := hHigh
  obtain ⟨CZ, hCZpos, hCZ⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaIbpPiece
  refine ⟨448 * (max (max CL CH) CZ + 1) + 1, by positivity, ?_⟩
  intro α hαmem f M ρ hdat hρ
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hαmem
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hS0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  -- ## the smoothness of the two factors of the coefficient
  have hFKcd : ContDiffOn ℝ 6
      (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.contDiffOn6_FK α hαmem f M hdat
  have hdthcd : ContDiffOn ℝ 6 (Function.uncurry (Work.Spaces.Dth f))
      Work.FTS.EllipticEst.Q0 := hdat.sm.Dth.forall 6
  -- ## the pointwise Leibniz identity on the open quadrant
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * Work.Spaces.mixed 6 0
          (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) z θ
        * Work.Spaces.mixed 6 0 f z θ
      = ∑ b₁ ∈ Finset.range 7, (Nat.choose 6 b₁ : ℝ) *
          (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z
            * (ρ z θ * Work.Spaces.mixed (6 - b₁) 1 f z θ
                * Work.Spaces.mixed 6 0 f z θ)) := by
    intro z θ hz hθ0 hθ1
    have h := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leibniz_rad_any
      (r := fun z => Work.Construction.FK f z) (g := Work.Spaces.Dth f)
      hFKcd hdthcd (j := 6) (i := 0) (by norm_num) z θ hz hθ0 hθ1
    rw [h, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.mixed_Dth_one]
    ring
  -- ## the same identity almost everywhere on the product measure
  have hae : (fun p : ℝ × ℝ =>
        ρ p.1 p.2 * Work.Spaces.mixed 6 0
            (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2)
      =ᵐ[((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))]
      (fun p : ℝ × ℝ => ∑ b₁ ∈ Finset.range 7, (Nat.choose 6 b₁ : ℝ) *
          (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2))) :=
    Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => hpt z θ hz hθ0 hθ1)
  -- ## the product-integrability of every summand
  have hsum_int : ∀ b₁ ∈ Finset.range 7, MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Nat.choose 6 b₁ : ℝ) *
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
          * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
              * Work.Spaces.mixed 6 0 f p.1 p.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    intro b₁ hb₁
    have hb : b₁ ≤ 6 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁)
    have hbase : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
          * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
              * Work.Spaces.mixed 6 0 f p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      -- ## the `b₁ = 0` slot: the angular integration by parts
      rcases Nat.eq_zero_or_pos b₁ with h0 | hpos
      · subst h0
        simpa using hZero α hαmem f M ρ hdat hρ
      · rcases lt_or_ge b₁ 4 with h4 | h4
        · exact (hLow α hαmem f M ρ b₁ hdat (by omega) (by omega) hρ).1
        · exact (hHigh α hαmem f M ρ b₁ hdat (by omega) (by omega) hρ).1
    exact (hbase.const_mul ((Nat.choose 6 b₁ : ℝ))).congr
      (Filter.Eventually.of_forall fun p => by ring)
  have hIntSum : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ∑ b₁ ∈ Finset.range 7, (Nat.choose 6 b₁ : ℝ) *
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
          * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
              * Work.Spaces.mixed 6 0 f p.1 p.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.integrable_finsetSum _ hsum_int
  have hIntFull : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ρ p.1 p.2 * Work.Spaces.mixed 6 0
          (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) p.1 p.2
        * Work.Spaces.mixed 6 0 f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hIntSum.congr hae.symm
  -- ## the product-measure form of the slot pairing
  have hprod : Work.FTS.TransportS.slotPairing ρ 0 6
      (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) f
      = ∫ p, ρ p.1 p.2 * Work.Spaces.mixed 6 0
            (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integral_prod _ hIntFull).symm
  -- ## the Leibniz expansion of the product integral
  have hexp : (∫ p, ρ p.1 p.2 * Work.Spaces.mixed 6 0
            (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∑ b₁ ∈ Finset.range 7, (Nat.choose 6 b₁ : ℝ) *
          (∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
                * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                    * Work.Spaces.mixed 6 0 f p.1 p.2)
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [MeasureTheory.integral_congr_ae hae]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun b₁ _ => ?_
      exact MeasureTheory.integral_const_mul _ _
    · intro b₁ hb₁
      exact hsum_int b₁ hb₁
  -- ## the per-summand bounds
  have hterm : ∀ b₁ ∈ Finset.range 7,
      |∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ max (max CL CH) CZ * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
    intro b₁ hb₁
    have hb : b₁ ≤ 6 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁)
    have hCBnn : (0 : ℝ) ≤ (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have hCL_le : CL ≤ max (max CL CH) CZ :=
      le_trans (le_max_left CL CH) (le_max_left (max CL CH) CZ)
    have hCH_le : CH ≤ max (max CL CH) CZ :=
      le_trans (le_max_right CL CH) (le_max_left (max CL CH) CZ)
    have hCZ_le : CZ ≤ max (max CL CH) CZ := le_max_right (max CL CH) CZ
    have hscale : ∀ c : ℝ, c ≤ max (max CL CH) CZ →
        c * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)
          ≤ max (max CL CH) CZ * (1 + M) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := by
      intro c hc
      refine mul_le_mul_of_nonneg_right ?_ (by linarith)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (by linarith)) (by linarith)
    rcases Nat.eq_zero_or_pos b₁ with h0 | hpos
    · -- ## the `b₁ = 0` slot: the angular integration by parts
      subst h0
      have hcase : (∫ p, Work.Elliptic.DzdIter 0 (fun z => Work.Construction.FK f z) p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed (6 - 0) 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
          = ∫ z in Work.Spaces.Iz, Work.Construction.FK f z *
              (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed 6 1 f z θ
                * Work.Spaces.mixed 6 0 f z θ) := by
        simpa using integral_prod_radial (r := fun z => Work.Construction.FK f z)
          (G := fun z θ => ρ z θ * Work.Spaces.mixed 6 1 f z θ
            * Work.Spaces.mixed 6 0 f z θ)
          (hZero α hαmem f M ρ hdat hρ)
      rw [hcase]
      exact le_trans (hCZ hα0 hα1 hdat 0 6 ρ (by norm_num) hρ) (hscale CZ hCZ_le)
    · rcases lt_or_ge b₁ 4 with h4 | h4
      · exact le_trans (hLow α hαmem f M ρ b₁ hdat (by omega) (by omega) hρ).2
          (hscale CL hCL_le)
      · exact le_trans (hHigh α hαmem f M ρ b₁ hdat h4 hb hρ).2
          (hscale CH hCH_le)
  -- ## the final arithmetic
  rw [hprod, hexp]
  have hsum_bound : |∑ b₁ ∈ Finset.range 7, (Nat.choose 6 b₁ : ℝ) *
        (∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
              * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                  * Work.Spaces.mixed 6 0 f p.1 p.2)
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)))|
      ≤ ∑ b₁ ∈ Finset.range 7, (64 : ℝ) *
          (max (max CL CH) CZ * (1 + M) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b₁ hb₁ => ?_)
    have hch : |(Nat.choose 6 b₁ : ℝ)| ≤ 64 := by
      have h1 : Nat.choose 6 b₁ ≤ 64 := by
        have h2 := Nat.choose_le_two_pow 6 b₁
        norm_num at h2 ⊢
        exact h2
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast h1
    have hb := hterm b₁ hb₁
    rw [abs_mul]
    exact (mul_le_mul hch hb (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  refine le_trans hsum_bound ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hα3 : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := one_le_alpha_rpow hα0 hα1
  have hCmax0 : (0 : ℝ) ≤ max (max CL CH) CZ :=
    le_trans hCZpos.le (le_max_right (max CL CH) CZ)
  have hX0 : (0 : ℝ) ≤ (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  calc (7 : ℝ) * (64 * (max (max CL CH) CZ * (1 + M) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f)))
      = (7 : ℝ) * (64 * (max (max CL CH) CZ
            * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)))) := by ring
    _ ≤ (448 * (max (max CL CH) CZ + 1) + 1) * α ^ (-(3 : ℝ))
          * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) :=
        final_arith hCmax0 hX0 hα3
    _ = (448 * (max (max CL CH) CZ + 1) + 1) * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f) := by ring

/-- **The top `z`-slot `(a,b) = (0,6)` of the angular-moment row `(FK f)·D_θf`** (the same
statement as the `sorry` left at the top level of `FkAux/fkRowDth6.lean`, whose private
`fkRowDth6_core` is already proved).

`|slotPairing ρ 0 6 (fun z θ => FK f z * D_θ f z θ) f| ≤ C α^{-3}(1+M)²(1 + HkSq α 6 f)` for a
datum `DatData α f M` and a leaf weight `ρ` of the slot `a = 0`.

Route (all ingredients PROVED in the tree; only the assembly is new):
* the radial Leibniz `FkAux.leibniz_rad_any` with `r := fun z => FK f z`, `g := Work.Spaces.Dth f`,
  `j := 6`, `i := 0` (radial factor `C⁶` by `contDiffOn6_FK`), plus `mixed_Dth_one`;
* product-integrability from `fkRowDthZeroSlot` (`b₁ = 0`) and `fkRowDthShiftLow` /
  `fkRowDthShiftHigh` (`1 ≤ b₁ ≤ 3` resp. `4 ≤ b₁ ≤ 6`), which also give
  `|∫_p ·| ≤ C(1+M)²(1+HkSq α 6 f)` for each summand (as product integrals over
  `(volume.restrict Iz).prod (volume.restrict Iθ)`);
* the `b₁ = 0` value is `FkAux.fkThetaIbpPiece`;
* `Finset.abs_sum_le_sum_abs` + `Σ_{b₁≤6} C(6,b₁) = 64` + finite arithmetic.
The template to copy is the private `fkRowDth6_core` in `FkAux/fkRowDth6.lean` (it must be
re-created: it is `private`, hence not importable). -/
theorem fkRowDthTopRow : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      Work.FTS.TransportS.IsLeafW α 0 ρ →
      |Work.FTS.TransportS.slotPairing ρ 0 6
          (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := fkRowDthTopRow_core fkRowDthShiftLow fkRowDthShiftHigh fkRowDthZeroSlot

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
end
end
