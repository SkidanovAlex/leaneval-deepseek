import Submission.Work.ThomBordism.chainSetup
import Submission.Work.Cohomology.cupH
import Submission.Work.Cohomology.cupBilinear
import Submission.Work.Cohomology.cupLeibniz

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type} (Z : RealBundle B F ι)

/-!
# The cochain-level Thom map `psi`: the Leibniz steps (sorry-free toolkit)

This module carries the part of `chainSetup_psi_cochainDiff.lean` that is proved: the
cochain-map ingredients for the cup map

  `psiAbs Z n U τ W hW m a = cup (pullAbs a) (tauRepAt τ)`,

namely the Leibniz rule in the shape needed (`psiAbs_d_cup`), the pullback commuting with the
differential (`pullAbs_cochainDiff`), the cocycle condition of the chosen representative
(`tauRepAt_cochainDiff`) and the degree-cast bookkeeping (`subtype_val_cast`,
`sset_of_d_transfer`, `eq_transport_cancel`, `cast_congrArg`).

Import this module to obtain all of them; the remaining statement (`psiAbs_relDiff`, the
`relDiffLM`-form of the cochain-map property) lives in `chainSetup_psi_cochainDiff`.
-/
/-- Bilinearity of the Alexander–Whitney cup product, in the vocabulary of `cupH.lean`. -/
theorem cupBilin_holds (X : SSet) : CupBilin ℤ X := fun n m => cupBilinear ℤ X n m

/-- The Leibniz rule for the Alexander–Whitney cup product, in the vocabulary of `cupH.lean`. -/
theorem leibniz_holds (X : SSet) : Leibniz ℤ X := fun α β => cupLeibniz ℤ X α β

/-!
## Remaining sub-steps of `psiAbs_diff` (exact, not mathematics)

1. `cochainDiff`-form of the cocycle condition: from `tauRepAt_cocycle` (`relDiffLM … = 0`) get
   `cochainDiff ℤ (TopCat.toSSet.obj Y) τ̃.1 = 0`.  The bridge is
   `Work.Cohomology.SSetCochainComplex_d_apply` together with the `rfl`-lemma
   `singularCochainComplex R X = SSetCochainComplex R (TopCat.toSSet.obj X)`
   (`Submission/Work/Cohomology/AlexanderWhitney.lean:247`), applied to the coercion of
   `relDiffLM_coe` (`rfl`).
2. `leibniz_left ℤ X (leibniz_holds X) (cupBilin_holds X) m n (pullAbs …) τ̃.1 hc` gives, in degree
   `(m+1)+n` (cast-free!),
   `((SSetCochainComplex ℤ X).d (m+n) ((m+1)+n)).hom (cup (pullAbs …) τ̃.1)
      = cup (cochainDiff (pullAbs …)) τ̃.1`.
3. Convert the left differential to the one of `TotComplex` at the same degree pair.  The proof
   body of `leibniz_left` (`Submission/Work/Cohomology/cupH.lean:314-330`) does exactly this
   conversion for the consecutive pair via `SSetCochainComplex_d_apply` and the transport
   `hh ▸ γ`, `hh := Nat.add_right_comm n 1 m`; the same pattern applies here with
   `m ↔ n` (`m` the base degree, `n` the Thom degree).
4. `Subtype.ext` (the two sides are the same cochain, degrees `(m+1)+n` on both sides) and use
   `cochainDiff (pullAbs …) = pullAbs (cochainDiff …)` (the pullback is a cochain map, i.e.
   `HomologicalComplex.Hom.comm` for `dualChainMap`; mind the coercion of `pullAbs`, which lands in
   `↥((singularCochainComplex …).X ·)` rather than in `Cochain …`, so the statement of the
   commutativity needs an ascription on one side).

## The shape now on disk (session 2026, third pass)

`psiAbs_relDiff` is the restatement asked for: `relDiffLM` on the left, the `Nat.add_right_comm`
cast on the right, so both sides are `↥(relKern …)` and the coercions agree by
`subtype_val_cast`.  It elaborates (body still a documented `sorry`).  `psiAbs_diff` is kept as the
derived form in the `leibniz_left` degrees; it is exactly `psiAbs_relDiff` with the cast pushed
across `HomologicalComplex.of.d` (`dif_pos` on `if h : i + 1 = j`).

Proof route for `psiAbs_relDiff`, with every ingredient already proved on disk:

1. `hc`: the cocycle condition of `tauRepAt` in `cochainDiff` form — `relDiffLM_coe` (rfl) →
   coercion → `SSetCochainComplex_d_apply`.
2. `hkey := leibniz_left ℤ X (leibniz_holds X) (cupBilin_holds X) m n (pullAbs …) τ̃.1 hc`.
3. `hpull`: `cochainDiff (pullAbs …) = pullAbs (cochainDiff …)` — `HomologicalComplex.Hom.comm`
   for `dualChainMap`, then both sides into `cochainDiff` via `SSetCochainComplex_d_apply`.
4. the differential-transfer (`psiAbs_diff` from `psiAbs_relDiff`): `HomologicalComplex.of.d`'s
   `if h : i + 1 = j` at the two pairs `(m+n, (m+n)+1)` and `(m+n, (m+1)+n)`, discharged by
   `dif_pos (Nat.add_right_comm m 1 n).symm` and `Category.comp_id`, plus the `eqToHom`-vs-transport
   identification (`eqToHom (congrArg X h) = h ▸ ·` on elements, by `cases h; rfl`).
5. `Subtype.ext` and the two sides are the same cochain (`hkey` after `hpull`, with `rfl` for the
   cup's shape).

## Two further facts found while filling the bridges (session 2026, second pass)

* `HomologicalComplex.of.d` for the `up`-shape is (`Mathlib/Algebra/Homology/HomologicalComplex.lean`,
  l. 895) `of.d X d i j := if h : i + 1 = j then d _ ≫ eqToHom (by rw [h]) else 0`.  So the
  differential of `TotComplex Z W` at the *shifted* pair `(m+n, (m+1)+n)` is
  `relDiff (m+n) ≫ eqToHom (Nat.add_right_comm m 1 n).symm`, obtained by `dif_pos` — that is the
  differential-transfer of step 3.  (`of_d (j) : of.d X d j (j+1) = d j` is `@[simp]`, which handles
  the *consecutive* pairs.)
* The **statement** of `psiAbs_diff` as written above hits a coercion friction Lean reports as
  "`psiAbs … : TotC Z W (m+n)` but expected `↥((TotComplex Z W).X (m+n))`".  Both types are the same
  `↥(relKern …)`, so an explicit ascription `(psiAbs … : ↥((TotComplex Z W).X (m+n)))` (or phrasing
  the lemma with `relDiffLM` plus the `Nat.add_right_comm` cast) removes it.  Prefer the latter: it
  keeps the whole computation inside the `relKern`/`relDiffLM` vocabulary, which is also the shape
  that `chainSetup_psi_cochainDiff` (with `relDiffLM` on the left) can consume directly.
-/


/-- The coercion of a subtype element commutes with a transport along an equality of the ambient
degree. -/
theorem subtype_val_cast (W : Set B) {a b : ℕ} (h : a = b) (x : TotC Z W a) :
    ((h ▸ x : TotC Z W b) : ↥((singularCochainComplex ℤ
        (TopCat.of ↥(Z.proj ⁻¹' W))).X b))
      = (congrArg (fun j => ↥((singularCochainComplex ℤ
          (TopCat.of ↥(Z.proj ⁻¹' W))).X j)) h) ▸
          (x : ↥((singularCochainComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W))).X a)) := by
  cases h
  rfl

/-! ## The five steps of `psiAbs_relDiff`

Steps 1-3 are proved below as separate lemmas; steps 4 (the differential transfer
`HomologicalComplex.of.d` shifted pair, by `dif_pos`) and 5 (`Subtype.ext` + `rfl` for the cup's
shape) are what is left of `psiAbs_relDiff`. -/

/-- **Step 1.** The cocycle condition of the chosen representative, in `cochainDiff` form
(via `relDiffLM_coe`, the coercion, and `SSetCochainComplex_d_apply`). -/
theorem tauRepAt_cochainDiff (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B)
    (hW : W ⊆ U) :
    cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))
      ((tauRepAt Z n U τ W hW).1 :
        Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n) = 0 := by
  have h := tauRepAt_cocycle Z n U τ W hW
  have h2 := congrArg (fun x : ↥(relKern ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (n + 1)) =>
    (x : ↥((singularCochainComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W))).X (n + 1)))) h
  simp only [relDiffLM_coe, Submodule.coe_zero] at h2
  have h3 : ((SSetCochainComplex ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))).d n (n + 1)).hom
      ((tauRepAt Z n U τ W hW).1 :
        Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n) = 0 := h2
  rw [SSetCochainComplex_d_apply] at h3
  exact h3

/-- **Step 2.** The Leibniz rule with the cocycle on the right, i.e. `leibniz_left` instantiated at
`(m, n)` with `pullAbs` and the representative. -/
theorem psiAbs_d_cup (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (m : ℕ) (a : BaseC W m) :
    ((SSetCochainComplex ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))).d (m + n) ((m + 1) + n)).hom
        (cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))
          (pullAbs Z W m a : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) m)
          ((tauRepAt Z n U τ W hW).1 :
            Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n))
      = cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))
          (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))
            (pullAbs Z W m a : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) m))
          ((tauRepAt Z n U τ W hW).1 :
            Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n) :=
  leibniz_left ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))
    (leibniz_holds _) (cupBilin_holds _) m n
    (pullAbs Z W m a : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) m)
    ((tauRepAt Z n U τ W hW).1 :
      Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n)
    (tauRepAt_cochainDiff Z n U τ W hW)

/-- **Step 3.** The pullback of cochains commutes with the differential. -/
theorem pullAbs_cochainDiff (W : Set B) (m : ℕ) (a : BaseC W m) :
    cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))
        (pullAbs Z W m a : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) m)
      = (pullAbs Z W (m + 1) (cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) a) :
          Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) (m + 1)) := by
  have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.Hom.comm
    (dualChainMap ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (TopCat.of ↥W)
      (TopCat.ofHom (Work.Thom.pieceProj Z W))) m (m + 1))
  have h2 := LinearMap.congr_fun h a
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [← SSetCochainComplex_d_apply, ← SSetCochainComplex_d_apply]
  exact h2

/-! ## The differential of `psiAbs`, in the shape consumed by `chainSetup_psi_cochainDiff`

Stated with `relDiffLM` on the left (which is the shape `chainSetup_psi_cochainDiff` wants) and the
`Nat.add_right_comm`-cast on the right, so that both sides are elements of `↥(relKern …)` and the
coercions agree definitionally (`subtype_val_cast` above descends the cast to underlying cochains). -/
/-- `eqToHom` on the degree modules of a cochain complex, along a degree equality, is the
transport of elements. -/
theorem eqToHom_X_eq_rec {K : CochainComplex (ModuleCat ℤ) ℕ} {a b : ℕ} (e : a = b)
    (x : K.X a) : (eqToHom (congrArg (fun j => K.X j) e)).hom x = e ▸ x := by
  cases e
  rfl

/-- **Step 4.** The differential at the shifted degree pair, in terms of the consecutive one. -/
theorem sset_of_d_transfer (X : SSet) {m n : ℕ} (u : Cochain ℤ X (m + n)) :
    ((SSetCochainComplex ℤ X).d (m + n) ((m + 1) + n)).hom u
      = (Nat.add_right_comm m 1 n).symm ▸
          (((SSetCochainComplex ℤ X).d (m + n) ((m + n) + 1)).hom u) := by
  have h : (m + 1) + n = (m + n) + 1 := Nat.add_right_comm m 1 n
  have hof : ((SSetCochainComplex ℤ X).d (m + n) ((m + 1) + n))
      = (ModuleCat.ofHom (cochainDiffLM ℤ X (m + n))) ≫
        eqToHom (congrArg (fun t => (SSetCochainComplex ℤ X).X t) h).symm := by
    dsimp only [SSetCochainComplex, CochainComplex.of.d]
    rw [dif_pos h.symm]
  have hof2 : ((SSetCochainComplex ℤ X).d (m + n) ((m + n) + 1))
      = ModuleCat.ofHom (cochainDiffLM ℤ X (m + n)) :=
    SSetCochainComplex_d ℤ X (m + n)
  rw [hof, hof2, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact eqToHom_X_eq_rec (K := SSetCochainComplex ℤ X) h.symm _

/-- Transport along an equality and back. -/
theorem eq_transport_cancel {α : Sort*} {a b : α} (h : a = b) {P : α → Sort*}
    (x : P b) : h ▸ (h.symm ▸ x) = x := by
  cases h
  rfl

/-- A `congrArg`-cast of the degree modules of a cochain complex is the transport of elements. -/
theorem cast_congrArg {K : CochainComplex (ModuleCat ℤ) ℕ} {a b : ℕ} (h : a = b)
    (x : ↥(K.X a)) : ((congrArg (fun j => ↥(K.X j)) h) ▸ x) = h ▸ x := by
  cases h
  rfl



/-- **The differential of `TotComplex` at the shifted degree pair** `(m+n, (m+1)+n)` is the
transport of the consecutive differential `(m+n, (m+n)+1)`.  This is the relative-cochain analogue
of `sset_of_d_transfer`, and the tool that carries the cone's differential. -/
theorem totComplex_d_transfer (n : ℕ) (W : Set B) {m : ℕ} (x : TotC Z W (m + n)) :
    ((TotComplex Z W).d (m + n) ((m + 1) + n)).hom x
      = (Nat.add_right_comm m 1 n).symm ▸
          (((TotComplex Z W).d (m + n) ((m + n) + 1)).hom x) := by
  have h : (m + 1) + n = (m + n) + 1 := Nat.add_right_comm m 1 n
  have hof : ((TotComplex Z W).d (m + n) ((m + 1) + n))
      = (ModuleCat.ofHom (relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (m + n))) ≫
        eqToHom (congrArg (fun t => (TotComplex Z W).X t) h).symm := by
    dsimp only [TotComplex, relComplex, CochainComplex.of.d]
    rw [dif_pos h.symm]
    rfl
  have hof2 : ((TotComplex Z W).d (m + n) ((m + n) + 1))
      = ModuleCat.ofHom (relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (m + n)) := by
    dsimp only [TotComplex, relComplex]
    rw [CochainComplex.of_d]
    rfl
  rw [hof, hof2, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact eqToHom_X_eq_rec (K := TotComplex Z W) h.symm
    ((ModuleCat.Hom.hom (ModuleCat.ofHom
      (relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (m + n)))) x)



/-- Transport along an equality and back (the other order). -/
theorem eq_transport_cancel' {α : Sort*} {a b : α} (h : a = b) {P : α → Sort*}
    (x : P a) : h.symm ▸ (h ▸ x) = x := by
  cases h
  rfl



/-- The consecutive differential of `TotComplex` is `relDiffLM`. -/
theorem totComplex_d_consecutive (n : ℕ) (W : Set B) {m : ℕ} (x : TotC Z W (m + n)) :
    ((TotComplex Z W).d (m + n) ((m + n) + 1)).hom x
      = relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (m + n) x := by
  dsimp only [TotComplex, relComplex]
  rw [CochainComplex.of_d]
  rfl



/-- `psiAbs` is additive in its base argument (the cup is bilinear, `pullAbs` is linear). -/
theorem psiAbs_add (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (m : ℕ) (a a' : BaseC W m) :
    psiAbs Z n U τ W hW m (a + a')
      = psiAbs Z n U τ W hW m a + psiAbs Z n U τ W hW m a' := by
  apply Subtype.ext
  show cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))
        (((pullAbs Z W m) (a + a') :
          Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) m))
        ((tauRepAt Z n U τ W hW).1 :
          Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n)
      = cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))
          ((pullAbs Z W m a : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) m))
          ((tauRepAt Z n U τ W hW).1 :
            Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n)
        + cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))
          ((pullAbs Z W m a' : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) m))
          ((tauRepAt Z n U τ W hW).1 :
            Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n)
  rw [map_add]
  exact (cupBilinear ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) m n).1 _ _ _

/-- `psiAbs` is `ℤ`-linear in its base argument. -/
theorem psiAbs_smul (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (m : ℕ) (c : ℤ) (a : BaseC W m) :
    psiAbs Z n U τ W hW m (c • a) = c • psiAbs Z n U τ W hW m a := by
  apply Subtype.ext
  show cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))
        (((pullAbs Z W m) (c • a) :
          Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) m))
        ((tauRepAt Z n U τ W hW).1 :
          Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n)
      = c • cup ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W)))
          ((pullAbs Z W m a : Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) m))
          ((tauRepAt Z n U τ W hW).1 :
            Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) n)
  rw [map_smul]
  exact (cupBilinear ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))) m n).2.1 _ _ _

/-- `psiAbs` as a `ℤ`-linear map in its base argument. -/
def psiAbsLM (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (m : ℕ) : BaseC W m →ₗ[ℤ] TotC Z W (m + n) :=
  { toFun := psiAbs Z n U τ W hW m
    map_add' := psiAbs_add Z n U τ W hW m
    map_smul' := psiAbs_smul Z n U τ W hW m }



/-- The coboundary of a coboundary vanishes, for `cochainDiffLM` (definitionally
`cochainDiff_cochainDiff`). -/
theorem cochainDiffLM_cochainDiffLM (X : SSet) {k : ℕ} (α : Cochain ℤ X k) :
    cochainDiffLM ℤ X (k + 1) (cochainDiffLM ℤ X k α) = 0 :=
  cochainDiff_cochainDiff (R := ℤ) X α


end

end Work.ThomBordism
