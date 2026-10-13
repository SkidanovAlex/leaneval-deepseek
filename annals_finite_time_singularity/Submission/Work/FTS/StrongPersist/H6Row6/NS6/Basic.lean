/-
# `H6Row6/NS6/Basic` — the shared data and the `C⁶`-bookkeeping for `nsum_split6`

This module collects everything the twenty per-piece arguments of
`Submission/Work/FTS/StrongPersist/H6Row6/nsum_split6.lean` have in common:

* the `C⁶`-bookkeeping lemmas on the open quadrant (`CD6` and its closure under sums,
  products, constants, radial and angular factors);
* the elementary shift identities that turn a product of a `𝒲^{6,∞}`-priced coefficient
  (written with the factor `(z+1)/z`) and an `ℋ⁶`-priced slot (written with the factor
  `z/(1+z)`) back into the shape of the piece;
* the iteration of the two finiteness rows over `Finset.range`;
* the structure `Data` bundling the level-six hypotheses on `(f, Ef, Φs)` — the slice data of
  `L6Ctx` — together with the derived facts about the coefficients
  (`ℛ`, `𝒰/sin 2θ`, `𝒱` of the star and perturbation stream functions), the slots
  (`F_*`, `D_θF_*`, `D_zF_*`, `f`, `D_θf`, `D_zf`), their shifts, and the angular moment
  `FK f`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.H6Row6.Pieces
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NSplit6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.mulPhi6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FKstarSlotPiece
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.FieldRegularity
import Submission.Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs
import Submission.Work.FTS.StrongPersist.Fstar_W6
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.DzFstar_W6
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.Basic
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.StrongPersist.HkAddFin
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Row6.radial_inv_wlInf6

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

/-- The `sin²θ`-variant of `shift_fk`. -/
theorem shift_fk_sq (α S Y z : ℝ) (h1z : (1 : ℝ) + z ≠ 0) :
    ((-α) / (1 + z)) * (S * (z / (1 + z) * Y))
      = -(1 / 2) * (α * (2 * z / (1 + z) ^ 2)) * S * Y := by
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

theorem Data.hV1w (D : Data α Ce Cs f Ef Φs) : Work.Spaces.WlInfMem α 6
    (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) := D.star.VW6.1

def Data.reg (D : Data α Ce Cs f Ef Φs) :=
  Work.FTS.PhiStar.StarPkgo2Aux.FieldRegularity α (Work.FTS.VocabO2.PhiTs α Φs) D.phiTs

theorem Data.hR1c (D : Data α Ce Cs f Ef Φs) : CD6 (fun z θ => (z + 1) / z
    * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) := D.reg.1.forall 6

theorem Data.hV1c (D : Data α Ce Cs f Ef Φs) :
    CD6 (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) := D.reg.2.1.forall 6

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
