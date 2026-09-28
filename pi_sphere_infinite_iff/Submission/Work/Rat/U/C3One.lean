import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Serre.Models
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.liftSurjectiveSerreFibration
import Submission.Work.Serre.homotopicLiftsOfJoinedFibre
import Submission.Work.Serre.pathSpaceAaction
import Submission.Work.Serre.PathSpaceTorsor
import Submission.Work.Serre.simpHomPrism
import Submission.Work.Serre.prismLiftDefs
import Submission.Work.Serre.actRel_const
import Submission.Work.Rat.U.FamModel
import Submission.Work.Serre.c3oneAssembly
import Submission.Work.Serre.skeletonMap_kernel_of_iso
import Submission.Work.Serre.jointKillStepKernel
import Submission.Work.Serre.genStep_extension
import Submission.Work.Serre.killStepExtension
import Submission.Work.Serre.towerStepMap
import Submission.Work.Serre.baseStageFamMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# C3 for finite coefficients at `n = 1`: a model of `K(A,1)` is rationally acyclic

`Work.Serre.serreC3FiniteOne`: for a finite abelian `A`, every model of `K(A,1)` is rationally
acyclic.  This is the base case of `Work.Serre.SerreC3Finite`; it cannot be reached by the loop
induction (`Work.Serre.ratAcyclic_of_model_succ`), because the fibre of the path–loop fibration of
`X` is `Ω X`, whose `π₀` is `A ≠ 1`, so the mapping theorem does not apply.

## The proof (the `famSpace` route, session 12)

The workspace contains a **rationally acyclic range model of `K(A,1)`** for finite abelian `A`:
`Work.RatHurewicz.famSpace` (a product of lens spaces), with `Work.RatHurewicz.famIsZeroRatH`
(`H_t = 0` for `0 < t ≤ 2N+2`), `famPiOne`, `famSubsingletonPi`, `famSubsingletonPiZero`.
So it suffices to find ONE space `Γ` mapping to `X` and to `famSpace` with `π_i`-isomorphisms in a
range, and to apply the range Whitehead theorem twice (`Work.Serre.ratH_isZero_of_two_models`).

`Γ` is the top stage `Work.Serre.E3aModel.towerB X pt (famBaseState X pt) (N+1)` of the model
tower of `X`:

* the base stage `famBaseState` is the `1`-skeleton of `X` with the `2`-cells killing
  `ker π₁(skelMap)`, mapping to `X` by `E3aModel.baseMap` (`π₁`-bijective) and to `famSpace` by the
  map of `Work.Serre.baseStageFamMap` (built from `skeletonMap_kernel_of_iso` and
  `attachG_killStep_bijective`, also `π₁`-bijective);
* each step of the tower attaches cells along constant maps (`genStep`) and along loops killing
  `ker π_{n+2}(g)` (`killStep`); both extensions of the `famSpace`-map exist by
  `Work.Serre.genStep_extension`/`killStepExtension` (the latter because `π_{n+2}(famSpace) = 0` in
  the range), giving `Work.Serre.towerStepMap`, and they keep `π₁` bijective;
* hence `Work.Serre.ratH_isZero_of_rangeModel` yields `H_t(X;ℚ) = 0` for `0 < t < N`, and
  `N` is arbitrary.

Everything on the *homotopy* side is supplied by the tower's own fields (`StA.bij`) and
`E3aModel.towerB_piMapN_bijective`; the map to `famSpace` only needs the extension lemmas above.

The material further down the file (the transfer for the path–loop fibration, the orbit sum
`orbitTransfer_spec`, the square shapes `ActJoin`/`PlainJoin` and their adapters) is the earlier
route of `C3ONE_PLAN.md`/`C3ONE_SESSION9.md`; it is *not* used by the proof above but is kept as
the record of that route.  Note that the imports of this file must avoid
`Submission.Work.Serre.serreE2dSimplex` (its `Work.Serre.homeoToCM` clashes with the one in
`Submission.Work.Serre.Csr.Defs`, which the `famSpace` route needs).
-/

open CategoryTheory Simplicial
open scoped Simplicial

namespace Work.Serre

/-! ## Helper lemmas for the transfer argument (session 9)

The first component of the `k`-th prism piece `Work.Serre.pp m k` is the degeneracy
`Fin.predAbove k`; consequently the push-forward along the path fibration of a *fibrewise* homotopy
over a simplex is a degenerate simplex of `X`.  This is the "degenerate chain" input of the
transfer argument (see `C3ONE_SESSION9.md`, piece (D3)). -/

/-- The collapse map `psi m k` of the `k`-th prism piece is `Fin.predAbove k`. -/
theorem psi_eq_predAbove (m : ℕ) (k : Fin (m + 1)) (j : Fin (m + 2)) :
    psi m k j = Fin.predAbove k j := by
  apply Fin.ext
  rw [psi_apply]
  simp only [Fin.predAbove]
  by_cases h : (j : ℕ) ≤ (k : ℕ)
  · rw [if_pos h]
    rw [dif_neg (by simp [Fin.lt_def]; omega)]
    simp
  · rw [if_neg h]
    rw [dif_pos (by simp [Fin.lt_def]; omega)]
    simp

theorem psi_eq_predAbove_fun (m : ℕ) (k : Fin (m + 1)) :
    (psi m k : Fin (m + 2) → Fin (m + 1)) = Fin.predAbove k :=
  funext fun j => psi_eq_predAbove m k j

/-- **The push-forward of a prism piece is a degenerate simplex.**  For a fibrewise homotopy `P`
over a simplex `sm` (i.e. `evalOne ∘ P = sm ∘ fst`), each of the `m + 1` prism pieces
`P ∘ pp m k` pushes forward to the *degenerate* simplex `sm ∘ (degeneracy)` of the singular
simplicial set of `X`. -/
theorem prismPiece_degenerate {X : Type} [TopologicalSpace X] (pt : X) (m : ℕ)
    (sm : C(↥(stdSimplex ℝ (Fin (m + 1))), X))
    (P : C(↥(stdSimplex ℝ (Fin (m + 1))) × unitInterval, Work.StemsB.PathSpace X pt))
    (hP : (Work.StemsB.evalOne X pt).comp P = sm.comp ContinuousMap.fst)
    (k : Fin (m + 1)) :
    ((TopCat.of X).toSSetObjEquivT (Opposite.op (SimplexCategory.mk (m + 1)))).symm
        ((Work.StemsB.evalOne X pt).comp (P.comp (Work.Serre.pp m k))) ∈
      (TopCat.toSSet.obj (TopCat.of X)).degenerate (m + 1) := by
  set x : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk m)) :=
    ((TopCat.of X).toSSetObjEquivT (Opposite.op (SimplexCategory.mk m))).symm sm with hx
  have hkey : ((TopCat.of X).toSSetObjEquivT (Opposite.op (SimplexCategory.mk (m + 1)))).symm
      ((Work.StemsB.evalOne X pt).comp (P.comp (Work.Serre.pp m k)))
      = (TopCat.toSSet.obj (TopCat.of X)).σ k x := by
    apply ((TopCat.of X).toSSetObjEquivT (Opposite.op (SimplexCategory.mk (m + 1)))).injective
    rw [Equiv.apply_symm_apply]
    ext z
    rw [TopCat.toSSetObjEquivT_σ_apply]
    rw [show (Fin.predAbove k) = (psi m k : Fin (m + 2) → Fin (m + 1)) from
      (psi_eq_predAbove_fun m k).symm]
    rw [hx, Equiv.apply_symm_apply]
    simp only [ContinuousMap.comp_apply]
    rw [show (Work.StemsB.evalOne X pt) (P ((Work.Serre.pp m k) z)) =
        sm ((Work.Serre.pp m k) z).1 from
      congrFun (congrArg DFunLike.coe hP) ((Work.Serre.pp m k) z)]
    rw [Work.Serre.pp_fst]
  rw [hkey]
  refine ⟨m, Nat.lt_succ_self m, SimplexCategory.σ k, ?_⟩
  exact ⟨x, rfl⟩

/-! ## The orbit-sum transfer (assembly, session 9)

For a chosen family `l` of lifts of the singular simplices of `X` to the path space, the
**orbit-sum transfer** on generators is

  `τ(σ) = Σ_{a ∈ A} [act a ∘ l σ]`.

Its push-forward along `evalOne` is `|A| • id` *exactly*, which is the input of the transfer
argument (see `C3ONE_SESSION9.md`). -/

/-- The **orbit-sum transfer** for the path fibration of `X`, for a chosen family `l` of lifts of
the singular simplices of `X`.  On the generator of a simplex `σ` it is the sum over `A` of the
generators of the lifted simplices `act a ∘ l σ`. -/
noncomputable def orbitTransfer {X : Type} [TopologicalSpace X] (pt : X)
    (A : Type) [AddCommGroup A] [Fintype A]
    (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt))
    (l : ∀ n : ℕ,
      (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk n)) →
      (TopCat.toSSet.obj (TopCat.of (Work.StemsB.PathSpace X pt))).obj
        (Opposite.op (SimplexCategory.mk n)))
    (n : ℕ) :
    (Work.Cohomology.singularChains ℚ (TopCat.of X)).X n ⟶
      (Work.Cohomology.singularChains ℚ (TopCat.of (Work.StemsB.PathSpace X pt))).X n :=
  CategoryTheory.Limits.Cofan.IsColimit.desc
    ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan (ModuleCat.of ℚ ℚ) n)
    (fun a => ∑ b : A, SSet.ιChainComplex
      (X := TopCat.toSSet.obj (TopCat.of (Work.StemsB.PathSpace X pt)))
      (R := ModuleCat.of ℚ ℚ)
      ((TopCat.toSSet.map (TopCat.ofHom (act b))).app (Opposite.op (SimplexCategory.mk n))
        (l n a)))

/-- The values of the orbit-sum transfer on the generators. -/
theorem orbitTransfer_spec {X : Type} [TopologicalSpace X] (pt : X)
    (A : Type) [AddCommGroup A] [Fintype A]
    (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt))
    (l : ∀ n : ℕ,
      (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk n)) →
      (TopCat.toSSet.obj (TopCat.of (Work.StemsB.PathSpace X pt))).obj
        (Opposite.op (SimplexCategory.mk n)))
    (n : ℕ)
    (a : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk n))) :
    SSet.ιChainComplex (X := TopCat.toSSet.obj (TopCat.of X)) (R := ModuleCat.of ℚ ℚ) a ≫
        orbitTransfer pt A act l n =
      ∑ b : A, SSet.ιChainComplex
        (X := TopCat.toSSet.obj (TopCat.of (Work.StemsB.PathSpace X pt)))
        (R := ModuleCat.of ℚ ℚ)
        ((TopCat.toSSet.map (TopCat.ofHom (act b))).app (Opposite.op (SimplexCategory.mk n))
          (l n a)) :=
  CategoryTheory.Limits.Cofan.IsColimit.fac _ _ a




/-! ## Vocabulary for the coherent-prism induction (session 9, UPDATE 5)

`ActJoin` is the square shape used by `Work.Serre.pathSpaceAaction` and `Work.Serre.actRel_const`;
`difOf` is the `A`-element joining two lifts of the same simplex (defined through the transitivity
of the action on the fibre components); `cOf` is the shift attached to a face in the induction (see
`C3ONE_SESSION9.md`). -/

/-- `ActJoin pt act a e e'`: the path `act a e` is homotopic rel endpoints to `e'` in the fibre of
the path fibration, in the square shape of `Work.Serre.pathSpaceAaction`. -/
def ActJoin {X : Type} [TopologicalSpace X] {A : Type} (pt : X)
    (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt)) (a : A)
    (e e' : Work.StemsB.PathSpace X pt) : Prop :=
  ∃ H : C(unitInterval × unitInterval, X),
    (∀ t : unitInterval, H (0, t) = (act a e).1 t) ∧
    (∀ t : unitInterval, H (1, t) = e'.1 t) ∧
    (∀ s : unitInterval, H (s, 0) = pt) ∧
    (∀ s : unitInterval, H (s, 1) = (Work.StemsB.evalOne X pt) e)

/-- **The `A`-difference of two lifts of the same simplex**, evaluated at a point (existence from
the transitivity of the action on the fibre components). -/
noncomputable def difOf {X : Type} [TopologicalSpace X] {A : Type} [AddCommGroup A] [Fintype A]
    (pt : X) (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt))
    (htrans : ∀ (e e' : Work.StemsB.PathSpace X pt),
      (Work.StemsB.evalOne X pt) e = (Work.StemsB.evalOne X pt) e' →
      ∃ a : A, ActJoin pt act a e e')
    {n : ℕ} (X₁ X₂ : C(↥(stdSimplex ℝ (Fin (n + 1))), Work.StemsB.PathSpace X pt))
    (h : (Work.StemsB.evalOne X pt).comp X₁ = (Work.StemsB.evalOne X pt).comp X₂)
    (z : ↥(stdSimplex ℝ (Fin (n + 1)))) : A :=
  Classical.choose (htrans (X₁ z) (X₂ z) (congrFun (congrArg DFunLike.coe h) z))

/-- The defining property of `difOf`. -/
theorem difOf_spec {X : Type} [TopologicalSpace X] {A : Type} [AddCommGroup A] [Fintype A]
    (pt : X) (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt))
    (htrans : ∀ (e e' : Work.StemsB.PathSpace X pt),
      (Work.StemsB.evalOne X pt) e = (Work.StemsB.evalOne X pt) e' →
      ∃ a : A, ActJoin pt act a e e')
    {n : ℕ} (X₁ X₂ : C(↥(stdSimplex ℝ (Fin (n + 1))), Work.StemsB.PathSpace X pt))
    (h : (Work.StemsB.evalOne X pt).comp X₁ = (Work.StemsB.evalOne X pt).comp X₂)
    (z : ↥(stdSimplex ℝ (Fin (n + 1)))) :
    ActJoin pt act (difOf pt act htrans X₁ X₂ h z) (X₁ z) (X₂ z) :=
  Classical.choose_spec (htrans (X₁ z) (X₂ z) (congrFun (congrArg DFunLike.coe h) z))

/-- The shift attached to the face `i` of the `(n+1)`-simplex `τ`: the `A`-difference between the
`i`-th face of the lift `l (n+1) τ` and the lift of the `i`-th face of `τ`. -/
noncomputable def cOf {X : Type} [TopologicalSpace X] {A : Type} [AddCommGroup A] [Fintype A]
    (pt : X) (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt))
    (htrans : ∀ (e e' : Work.StemsB.PathSpace X pt),
      (Work.StemsB.evalOne X pt) e = (Work.StemsB.evalOne X pt) e' →
      ∃ a : A, ActJoin pt act a e e')
    (l : ∀ m : ℕ, C(↥(stdSimplex ℝ (Fin (m + 1))), X) →
      C(↥(stdSimplex ℝ (Fin (m + 1))), Work.StemsB.PathSpace X pt))
    (hl : ∀ (m : ℕ) (τ : C(↥(stdSimplex ℝ (Fin (m + 1))), X)),
      (Work.StemsB.evalOne X pt).comp (l m τ) = τ)
    (n : ℕ) (τ : C(↥(stdSimplex ℝ (Fin (n + 2))), X)) (i : Fin (n + 2)) : A :=
  difOf pt act htrans ((l (n + 1) τ).comp (Work.Serre.cof (n + 1) i))
    (l n (τ.comp (Work.Serre.cof (n + 1) i)))
    (by rw [← ContinuousMap.comp_assoc, hl (n + 1) τ,
       hl n (τ.comp (Work.Serre.cof (n + 1) i))])
    (stdSimplex.vertex 0)


/-- The first-half rescaling `t ↦ 2 t` of the unit interval, clamped to `[0,1]`. -/
def twoT (t : unitInterval) : unitInterval :=
  ⟨min (2 * (t : ℝ)) 1, ⟨le_min (mul_nonneg (by norm_num) t.2.1) zero_le_one,
    min_le_right _ _⟩⟩

theorem twoT_coe (t : unitInterval) : (twoT t : ℝ) = min (2 * (t : ℝ)) 1 := rfl

@[simp]
theorem twoT_zero : twoT 0 = 0 := by
  apply Subtype.ext
  rw [twoT_coe]
  norm_num

@[simp]
theorem twoT_one : twoT 1 = 1 := by
  apply Subtype.ext
  rw [twoT_coe]
  norm_num

/-- The second-half rescaling `t ↦ 2 t - 1` of the unit interval, clamped. -/
def twoTsub (t : unitInterval) : unitInterval :=
  ⟨max (2 * (t : ℝ) - 1) 0, ⟨le_max_right _ _, by
    have h := t.2.2
    exact max_le (by linarith) (by norm_num)⟩⟩

theorem twoTsub_coe (t : unitInterval) : (twoTsub t : ℝ) = max (2 * (t : ℝ) - 1) 0 := rfl

@[simp]
theorem twoTsub_zero : twoTsub 0 = 0 := by
  apply Subtype.ext
  rw [twoTsub_coe]
  norm_num

@[simp]
theorem twoTsub_one : twoTsub 1 = 1 := by
  apply Subtype.ext
  rw [twoTsub_coe]
  norm_num

/-- The reversal `t ↦ 1 - t` of the unit interval. -/
def oneSub (t : unitInterval) : unitInterval :=
  ⟨1 - (t : ℝ), ⟨by linarith [t.2.2], by linarith [t.2.1]⟩⟩

theorem oneSub_coe (t : unitInterval) : (oneSub t : ℝ) = 1 - (t : ℝ) := rfl

@[simp]
theorem oneSub_zero : oneSub 0 = 1 := by
  apply Subtype.ext
  rw [oneSub_coe]
  norm_num

@[simp]
theorem oneSub_one : oneSub 1 = 0 := by
  apply Subtype.ext
  rw [oneSub_coe]
  norm_num

/-- **Gluing two squares along their common middle edge.**  Given a homotopy from `p` to `q` and
one from `q` to `r`, with the same vertical boundary (`·,0 ↦ pt`, `·,1 ↦ x`), there is one from `p`
to `r`. -/
theorem square_trans {X : Type} [TopologicalSpace X] {pt x : X} {p q r : C(unitInterval, X)}
    {H₁ H₂ : C(unitInterval × unitInterval, X)}
    (h₁₀ : ∀ t, H₁ (0, t) = p t) (h₁₁ : ∀ t, H₁ (1, t) = q t)
    (h₁₂ : ∀ s, H₁ (s, 0) = pt) (h₁₃ : ∀ s, H₁ (s, 1) = x)
    (h₂₀ : ∀ t, H₂ (0, t) = q t) (h₂₁ : ∀ t, H₂ (1, t) = r t)
    (h₂₂ : ∀ s, H₂ (s, 0) = pt) (h₂₃ : ∀ s, H₂ (s, 1) = x) :
    ∃ H : C(unitInterval × unitInterval, X),
      (∀ t, H (0, t) = p t) ∧ (∀ t, H (1, t) = r t) ∧
      (∀ s, H (s, 0) = pt) ∧ (∀ s, H (s, 1) = x) := by
  classical
  have hcont : Continuous fun u : unitInterval × unitInterval =>
      if (u.1 : ℝ) ≤ 1 / 2 then H₁ (twoT u.1, u.2) else H₂ (twoTsub u.1, u.2) := by
    refine continuous_if_le ?_ continuous_const ?_ ?_ ?_
    · exact continuous_subtype_val.comp continuous_fst
    · refine (H₁.continuous.comp ?_).continuousOn
      refine Continuous.prodMk (Continuous.subtype_mk ?_ ?_) continuous_snd
      · exact (continuous_const.mul (continuous_subtype_val.comp continuous_fst)).min
          continuous_const
      · intro u
        exact ⟨le_min (mul_nonneg (by norm_num) u.1.2.1) zero_le_one, min_le_right _ _⟩
    · refine (H₂.continuous.comp ?_).continuousOn
      refine Continuous.prodMk (Continuous.subtype_mk ?_ ?_) continuous_snd
      · exact ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).sub
          continuous_const).max continuous_const
      · intro u
        exact ⟨le_max_right _ _, max_le (by have h := u.1.2.2; linarith) (by norm_num)⟩
    · intro u hu
      have h1 : twoT u.1 = 1 := by
        apply Subtype.ext
        rw [twoT_coe, hu]
        norm_num
      have h2 : twoTsub u.1 = 0 := by
        apply Subtype.ext
        rw [twoTsub_coe, hu]
        norm_num
      rw [h1, h2, h₁₁, h₂₀]
  refine ⟨⟨_, hcont⟩, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [ContinuousMap.coe_mk, if_pos (by norm_num : ((0 : unitInterval) : ℝ) ≤ 1/2),
      twoT_zero, h₁₀]
  · intro t
    rw [ContinuousMap.coe_mk, if_neg (by norm_num : ¬ (((1 : unitInterval) : ℝ) ≤ 1/2)),
      twoTsub_one, h₂₁]
  · intro s
    rw [ContinuousMap.coe_mk]
    by_cases h : (s.1 : ℝ) ≤ 1 / 2
    · rw [if_pos h, h₁₂]
    · rw [if_neg h, h₂₂]
  · intro s
    rw [ContinuousMap.coe_mk]
    by_cases h : (s.1 : ℝ) ≤ 1 / 2
    · rw [if_pos h, h₁₃]
    · rw [if_neg h, h₂₃]

/-- **Uniqueness of the `A`-difference** of two lifts of the same simplex (reviewed as
`Serre/difOf_unique`): if `a` joins the two lifts at a point and `b` joins them at another, then
`a = b`.  Consequence (with `difOf_spec`): the element `difOf …` is *constant* along the simplex. -/
theorem difOf_unique {X : Type} [TopologicalSpace X] {A : Type} [AddCommGroup A] [Fintype A]
    (pt : X) (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt))
    (hfree : ∀ (a b : A) (e : Work.StemsB.PathSpace X pt),
      (∃ H : C(unitInterval × unitInterval, X),
        (∀ t : unitInterval, H (0, t) = (act a e).1 t) ∧
        (∀ t : unitInterval, H (1, t) = (act b e).1 t) ∧
        (∀ s : unitInterval, H (s, 0) = pt) ∧
        (∀ s : unitInterval, H (s, 1) = (Work.StemsB.evalOne X pt) e)) ↔ a = b)
    {n : ℕ} (X₁ X₂ : C(↥(stdSimplex ℝ (Fin (n + 1))), Work.StemsB.PathSpace X pt))
    (h₁ : (Work.StemsB.evalOne X pt).comp X₁ = (Work.StemsB.evalOne X pt).comp X₂)
    (z z' : ↥(stdSimplex ℝ (Fin (n + 1)))) (a b : A)
    (ha : ∃ H : C(unitInterval × unitInterval, X),
        (∀ t : unitInterval, H (0, t) = (act a (X₁ z)).1 t) ∧
        (∀ t : unitInterval, H (1, t) = (X₂ z).1 t) ∧
        (∀ s : unitInterval, H (s, 0) = pt) ∧
        (∀ s : unitInterval, H (s, 1) = (Work.StemsB.evalOne X pt) (X₁ z)))
    (hb : ∃ H : C(unitInterval × unitInterval, X),
        (∀ t : unitInterval, H (0, t) = (act b (X₁ z')).1 t) ∧
        (∀ t : unitInterval, H (1, t) = (X₂ z').1 t) ∧
        (∀ s : unitInterval, H (s, 0) = pt) ∧
        (∀ s : unitInterval, H (s, 1) = (Work.StemsB.evalOne X pt) (X₁ z'))) :
    a = b := by
  classical
  -- the action preserves the endpoint, extracted from freeness at `a = b`
  have hact : ∀ c : A, (Work.StemsB.evalOne X pt).comp (act c) = Work.StemsB.evalOne X pt := by
    intro c
    ext e
    obtain ⟨H, h0, h1, hs0, hs1⟩ := (hfree c c e).mpr rfl
    have h2 : (act c e).1 1 = (Work.StemsB.evalOne X pt) e := by rw [← h0 1, hs1 0]
    change ((act c) e).1 1 = (Work.StemsB.evalOne X pt) e
    exact h2
  -- propagate `ha` from `z` to `z'`
  obtain ⟨H₂, hH₂0, hH₂1, hH₂s0, hH₂s1⟩ :=
    Work.Serre.actRel_const pt A act hact (n := n) ((Work.StemsB.evalOne X pt).comp X₁)
      X₁ X₂ rfl h₁.symm z z' a
      ⟨ha.choose, ha.choose_spec.1, ha.choose_spec.2.1, ha.choose_spec.2.2.1, ha.choose_spec.2.2.2⟩
  -- the second square, reversed in the first variable
  obtain ⟨H₃, hH₃0, hH₃1, hH₃s0, hH₃s1⟩ := hb
  let Hrev : C(unitInterval × unitInterval, X) :=
    ⟨fun u => H₃ (oneSub u.1, u.2), by
      refine H₃.continuous.comp (Continuous.prodMk ?_ continuous_snd)
      exact Continuous.subtype_mk (f := fun u : unitInterval × unitInterval =>
        1 - ((u.1 : unitInterval) : ℝ))
        (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
        (fun u => ⟨by linarith [u.1.2.2], by linarith [u.1.2.1]⟩)⟩
  have hrev0 : ∀ t, Hrev (0, t) = (X₂ z').1 t := by
    intro t
    have h1 : Hrev (0, t) = H₃ (oneSub 0, t) := rfl
    rw [h1, oneSub_zero, hH₃1]
  have hrev1 : ∀ t, Hrev (1, t) = (act b (X₁ z')).1 t := by
    intro t
    have h1 : Hrev (1, t) = H₃ (oneSub 1, t) := rfl
    rw [h1, oneSub_one, hH₃0]
  have hrevs0 : ∀ s, Hrev (s, 0) = pt := by
    intro s
    have h1 : Hrev (s, 0) = H₃ (oneSub s, (0 : unitInterval)) := rfl
    rw [h1, hH₃s0]
  have hrevs1 : ∀ s, Hrev (s, 1) = (Work.StemsB.evalOne X pt) (X₁ z') := by
    intro s
    have h1 : Hrev (s, 1) = H₃ (oneSub s, (1 : unitInterval)) := rfl
    rw [h1, hH₃s1]
  -- glue the two squares
  obtain ⟨H, hH0, hH1, hHs0, hHs1⟩ :=
    square_trans (pt := pt) (x := (Work.StemsB.evalOne X pt) (X₁ z'))
      (p := (act a (X₁ z')).1) (q := (X₂ z').1) (r := (act b (X₁ z')).1)
      hH₂0 hH₂1 hH₂s0 hH₂s1 hrev0 hrev1 hrevs0 hrevs1
  exact (hfree a b (X₁ z')).mp ⟨H, hH0, hH1, hHs0, hHs1⟩


/-- **The `A`-difference of two lifts of the same simplex is independent of the point**:
`difOf` is constant along the simplex.  This is the corner-consistency input of the
coherent-prism induction. -/
theorem difOf_eq {X : Type} [TopologicalSpace X] {A : Type} [AddCommGroup A] [Fintype A]
    (pt : X) (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt))
    (htrans : ∀ (e e' : Work.StemsB.PathSpace X pt),
      (Work.StemsB.evalOne X pt) e = (Work.StemsB.evalOne X pt) e' →
      ∃ a : A, ActJoin pt act a e e')
    (hfree : ∀ (a b : A) (e : Work.StemsB.PathSpace X pt),
      (∃ H : C(unitInterval × unitInterval, X),
        (∀ t : unitInterval, H (0, t) = (act a e).1 t) ∧
        (∀ t : unitInterval, H (1, t) = (act b e).1 t) ∧
        (∀ s : unitInterval, H (s, 0) = pt) ∧
        (∀ s : unitInterval, H (s, 1) = (Work.StemsB.evalOne X pt) e)) ↔ a = b)
    {n : ℕ} (X₁ X₂ : C(↥(stdSimplex ℝ (Fin (n + 1))), Work.StemsB.PathSpace X pt))
    (h : (Work.StemsB.evalOne X pt).comp X₁ = (Work.StemsB.evalOne X pt).comp X₂)
    (z z' : ↥(stdSimplex ℝ (Fin (n + 1)))) :
    difOf pt act htrans X₁ X₂ h z = difOf pt act htrans X₁ X₂ h z' :=
  difOf_unique pt act hfree X₁ X₂ h z z' _ _
    (difOf_spec pt act htrans X₁ X₂ h z) (difOf_spec pt act htrans X₁ X₂ h z')


/-- The shift attached to the face `i` of the `(m+2)`-simplex `σ`: the `A`-difference between the
`i`-th face of the lift `l (m+2) σ` and the lift of the `i`-th face of `σ`.  This is the shift that
appears in the ends of the level-`m` prism (`C3ONE_SESSION9.md`, UPDATE 8). -/
noncomputable def cOfTop {X : Type} [TopologicalSpace X] {A : Type} [AddCommGroup A] [Fintype A]
    (pt : X) (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt))
    (htrans : ∀ (e e' : Work.StemsB.PathSpace X pt),
      (Work.StemsB.evalOne X pt) e = (Work.StemsB.evalOne X pt) e' →
      ∃ a : A, ActJoin pt act a e e')
    (l : ∀ m : ℕ, C(↥(stdSimplex ℝ (Fin (m + 1))), X) →
      C(↥(stdSimplex ℝ (Fin (m + 1))), Work.StemsB.PathSpace X pt))
    (hl : ∀ (m : ℕ) (τ : C(↥(stdSimplex ℝ (Fin (m + 1))), X)),
      (Work.StemsB.evalOne X pt).comp (l m τ) = τ)
    (m : ℕ) (σ : C(↥(stdSimplex ℝ (Fin (m + 3))), X)) (i : Fin (m + 3)) : A :=
  difOf pt act htrans ((l (m + 2) σ).comp (Work.Serre.cof (m + 2) i))
    (l (m + 1) (σ.comp (Work.Serre.cof (m + 2) i)))
    (by rw [← ContinuousMap.comp_assoc, hl (m + 2) σ,
       hl (m + 1) (σ.comp (Work.Serre.cof (m + 2) i))])
    (stdSimplex.vertex 0)

/-- The defining property of `cOfTop` at the base vertex: the two ends of the level-`m` prism are
joined there (by construction of the shift). -/
theorem cOfTop_spec_base {X : Type} [TopologicalSpace X] {A : Type} [AddCommGroup A] [Fintype A]
    (pt : X) (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt))
    (htrans : ∀ (e e' : Work.StemsB.PathSpace X pt),
      (Work.StemsB.evalOne X pt) e = (Work.StemsB.evalOne X pt) e' →
      ∃ a : A, ActJoin pt act a e e')
    (l : ∀ m : ℕ, C(↥(stdSimplex ℝ (Fin (m + 1))), X) →
      C(↥(stdSimplex ℝ (Fin (m + 1))), Work.StemsB.PathSpace X pt))
    (hl : ∀ (m : ℕ) (τ : C(↥(stdSimplex ℝ (Fin (m + 1))), X)),
      (Work.StemsB.evalOne X pt).comp (l m τ) = τ)
    (m : ℕ) (σ : C(↥(stdSimplex ℝ (Fin (m + 3))), X)) (i : Fin (m + 3)) :
    ActJoin pt act (cOfTop pt act htrans l hl m σ i)
      (((l (m + 2) σ).comp (Work.Serre.cof (m + 2) i)) (stdSimplex.vertex 0))
      ((l (m + 1) (σ.comp (Work.Serre.cof (m + 2) i))) (stdSimplex.vertex 0)) :=
  difOf_spec pt act htrans ((l (m + 2) σ).comp (Work.Serre.cof (m + 2) i))
    (l (m + 1) (σ.comp (Work.Serre.cof (m + 2) i))) _ (stdSimplex.vertex 0)

/-- The defining property of `cOfTop` at **every** point of the simplex (using the constancy
`difOf_eq`): the two ends of the level-`m` prism are joined everywhere by the *same* element. -/
theorem cOfTop_spec {X : Type} [TopologicalSpace X] {A : Type} [AddCommGroup A] [Fintype A]
    (pt : X) (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt))
    (htrans : ∀ (e e' : Work.StemsB.PathSpace X pt),
      (Work.StemsB.evalOne X pt) e = (Work.StemsB.evalOne X pt) e' →
      ∃ a : A, ActJoin pt act a e e')
    (hfree : ∀ (a b : A) (e : Work.StemsB.PathSpace X pt),
      (∃ H : C(unitInterval × unitInterval, X),
        (∀ t : unitInterval, H (0, t) = (act a e).1 t) ∧
        (∀ t : unitInterval, H (1, t) = (act b e).1 t) ∧
        (∀ s : unitInterval, H (s, 0) = pt) ∧
        (∀ s : unitInterval, H (s, 1) = (Work.StemsB.evalOne X pt) e)) ↔ a = b)
    (l : ∀ m : ℕ, C(↥(stdSimplex ℝ (Fin (m + 1))), X) →
      C(↥(stdSimplex ℝ (Fin (m + 1))), Work.StemsB.PathSpace X pt))
    (hl : ∀ (m : ℕ) (τ : C(↥(stdSimplex ℝ (Fin (m + 1))), X)),
      (Work.StemsB.evalOne X pt).comp (l m τ) = τ)
    (m : ℕ) (σ : C(↥(stdSimplex ℝ (Fin (m + 3))), X)) (i : Fin (m + 3))
    (z : ↥(stdSimplex ℝ (Fin (m + 2)))) :
    ActJoin pt act (cOfTop pt act htrans l hl m σ i)
      (((l (m + 2) σ).comp (Work.Serre.cof (m + 2) i)) z)
      ((l (m + 1) (σ.comp (Work.Serre.cof (m + 2) i))) z) := by
  have hz : cOfTop pt act htrans l hl m σ i =
      difOf pt act htrans ((l (m + 2) σ).comp (Work.Serre.cof (m + 2) i))
        (l (m + 1) (σ.comp (Work.Serre.cof (m + 2) i)))
        (by rw [← ContinuousMap.comp_assoc, hl (m + 2) σ,
           hl (m + 1) (σ.comp (Work.Serre.cof (m + 2) i))]) z :=
    difOf_eq pt act htrans hfree ((l (m + 2) σ).comp (Work.Serre.cof (m + 2) i))
      (l (m + 1) (σ.comp (Work.Serre.cof (m + 2) i)))
      (by rw [← ContinuousMap.comp_assoc, hl (m + 2) σ,
         hl (m + 1) (σ.comp (Work.Serre.cof (m + 2) i))]) (stdSimplex.vertex 0) z
  rw [hz]
  exact difOf_spec pt act htrans _ _ _ z

/-! ## The unshifted square shape and its adapter lemmas

`Work.Serre.pathSpaceAactionNat` phrases the action's properties with the **unshifted** first
boundary `H (0,t) = e.1 t`, whereas `Work.Serre.ActJoin` carries an `act a` there.  The two are
related by rewriting a single boundary condition (`hact`), and these are the lemmas that make the
clauses of `pathSpaceAactionNat` usable in the `ActJoin` world (see `C3ONE_SESSION9.md`, UPDATE 10).
They are what the bottom level of the coherent-prism induction consumes. -/

/-- The **unshifted** square shape, exactly as `Work.Serre.pathSpaceAactionNat` produces it: a
homotopy from `e` to `e'` relative to the endpoints, with no `act` in the first boundary. -/
def PlainJoin {X : Type} [TopologicalSpace X] (pt : X)
    (e e' : Work.StemsB.PathSpace X pt) : Prop :=
  ∃ H : C(unitInterval × unitInterval, X),
    (∀ t : unitInterval, H (0, t) = e.1 t) ∧
    (∀ t : unitInterval, H (1, t) = e'.1 t) ∧
    (∀ s : unitInterval, H (s, 0) = pt) ∧
    (∀ s : unitInterval, H (s, 1) = (Work.StemsB.evalOne X pt) e)

/-- `ActJoin a e e'` is `PlainJoin` of the shifted source. -/
theorem actJoin_iff_plainJoin {X : Type} [TopologicalSpace X] {A : Type}
    (pt : X) (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt))
    (hact : ∀ a, (Work.StemsB.evalOne X pt).comp (act a) = Work.StemsB.evalOne X pt)
    (a : A) (e e' : Work.StemsB.PathSpace X pt) :
    ActJoin pt act a e e' ↔ PlainJoin pt (act a e) e' := by
  have h : (Work.StemsB.evalOne X pt) (act a e) = (Work.StemsB.evalOne X pt) e :=
    congrFun (congrArg DFunLike.coe (hact a)) e
  constructor
  · rintro ⟨H, h0, h1, hs0, hs1⟩
    exact ⟨H, h0, h1, hs0, by rw [h]; exact hs1⟩
  · rintro ⟨H, h0, h1, hs0, hs1⟩
    exact ⟨H, h0, h1, hs0, by rw [← h]; exact hs1⟩

/-- The action preserves the unshifted square (the third conjunct of
`Work.Serre.pathSpaceAactionNat`), in the `PlainJoin` form. -/
theorem plainJoin_act {X : Type} [TopologicalSpace X] {A : Type}
    (pt : X) (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt))
    (hact : ∀ a, (Work.StemsB.evalOne X pt).comp (act a) = Work.StemsB.evalOne X pt)
    (hpres : ∀ (e e' : Work.StemsB.PathSpace X pt), PlainJoin pt e e' → ∀ a : A,
      ∃ H : C(unitInterval × unitInterval, X),
        (∀ t : unitInterval, H (0, t) = (act a e).1 t) ∧
        (∀ t : unitInterval, H (1, t) = (act a e').1 t) ∧
        (∀ s : unitInterval, H (s, 0) = pt) ∧
        (∀ s : unitInterval, H (s, 1) = (Work.StemsB.evalOne X pt) e))
    (a : A) (e e' : Work.StemsB.PathSpace X pt) (h : PlainJoin pt e e') :
    PlainJoin pt (act a e) (act a e') := by
  obtain ⟨H, h0, h1, hs0, hs1⟩ := hpres e e' h a
  have hh : (Work.StemsB.evalOne X pt) (act a e) = (Work.StemsB.evalOne X pt) e :=
    congrFun (congrArg DFunLike.coe (hact a)) e
  exact ⟨H, h0, h1, hs0, by rw [hh]; exact hs1⟩

/-- The multiplicativity of the action up to homotopy (the fourth conjunct of
`Work.Serre.pathSpaceAactionNat`), in the `PlainJoin` form: `act a (act b e)` is joined to
`act (a + b) e`. -/
theorem plainJoin_mul {X : Type} [TopologicalSpace X] {A : Type} [AddCommGroup A]
    (pt : X) (act : A → C(Work.StemsB.PathSpace X pt, Work.StemsB.PathSpace X pt))
    (hact : ∀ a, (Work.StemsB.evalOne X pt).comp (act a) = Work.StemsB.evalOne X pt)
    (hmul : ∀ (a b : A) (e : Work.StemsB.PathSpace X pt),
      ∃ H : C(unitInterval × unitInterval, X),
        (∀ t : unitInterval, H (0, t) = (act a (act b e)).1 t) ∧
        (∀ t : unitInterval, H (1, t) = (act (a + b) e).1 t) ∧
        (∀ s : unitInterval, H (s, 0) = pt) ∧
        (∀ s : unitInterval, H (s, 1) = (Work.StemsB.evalOne X pt) e))
    (a b : A) (e : Work.StemsB.PathSpace X pt) :
    PlainJoin pt (act a (act b e)) (act (a + b) e) := by
  obtain ⟨H, h0, h1, hs0, hs1⟩ := hmul a b e
  have h1' : (Work.StemsB.evalOne X pt) (act b e) = (Work.StemsB.evalOne X pt) e :=
    congrFun (congrArg DFunLike.coe (hact b)) e
  have h2' : (Work.StemsB.evalOne X pt) (act a (act b e)) =
      (Work.StemsB.evalOne X pt) (act b e) :=
    congrFun (congrArg DFunLike.coe (hact a)) (act b e)
  have hh : (Work.StemsB.evalOne X pt) (act a (act b e)) = (Work.StemsB.evalOne X pt) e :=
    h2'.trans h1'
  exact ⟨H, h0, h1, hs0, by rw [hh]; exact hs1⟩

/-- `PlainJoin` is symmetric: reverse the first variable of the square (via `oneSub`).  This is
what lets two `PlainJoin`s be composed when the shared path is the target of one and the source of
the other (the `square_trans` glue of the bottom level). -/
theorem plainJoin_symm {X : Type} [TopologicalSpace X] (pt : X)
    {e e' : Work.StemsB.PathSpace X pt} (h : PlainJoin pt e e') : PlainJoin pt e' e := by
  obtain ⟨H, h0, h1, hs0, hs1⟩ := h
  have hb : (Work.StemsB.evalOne X pt) e = (Work.StemsB.evalOne X pt) e' := by
    have h₁ : (Work.StemsB.evalOne X pt) e = H (1, 1) := (hs1 1).symm
    have h₂ : H (1, 1) = (Work.StemsB.evalOne X pt) e' := by
      show H (1, 1) = (e'.1 : C(unitInterval, X)) 1
      exact h1 1
    exact h₁.trans h₂
  refine ⟨⟨fun u => H (oneSub u.1, u.2), ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine H.continuous.comp (Continuous.prodMk ?_ continuous_snd)
    exact Continuous.subtype_mk (f := fun u : unitInterval × unitInterval =>
      1 - ((u.1 : unitInterval) : ℝ))
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
      (fun u => ⟨by linarith [u.1.2.2], by linarith [u.1.2.1]⟩)
  · intro t
    show H (oneSub (0 : unitInterval), t) = e'.1 t
    rw [oneSub_zero]
    exact h1 t
  · intro t
    show H (oneSub (1 : unitInterval), t) = e.1 t
    rw [oneSub_one]
    exact h0 t
  · intro s
    show H (oneSub s, 0) = pt
    exact hs0 (oneSub s)
  · intro s
    show H (oneSub s, 1) = (Work.StemsB.evalOne X pt) e'
    rw [hs1 (oneSub s)]
    exact hb

/-! ## The `famSpace` route to `serreC3FiniteOne` (session 12)

The workspace contains a rationally acyclic *range model* of `K(A,1)` for finite abelian `A`
(`Work.RatHurewicz.famSpace`, with `famIsZeroRatH`).  To compare an arbitrary model `X` of `K(A,1)`
with it we build one space `Γ` carrying `π`-isomorphisms into both: the model tower of `X`
(`Work.Serre.E3aModel.towerB`) together with a map to `famSpace` that is extended up the tower.

The invariant of the recursion is only "*the map is a bijection on `π₁`*": the tower's own structure
map is already `π₁`-bijective at every level, so no kernel bookkeeping is needed.  At each level the
`famSpace`-map is extended over the generator cells (`Work.Serre.genStep_extension`) and the killing
cells (`Work.Serre.killStepExtension`, whose hypothesis is that `π_{n+2}` of the target vanishes —
true for `famSpace` in the range). -/

section FamRoute

open CategoryTheory.Limits

/-- The base stage of the model tower used by the `famSpace` route: the `1`-skeleton of `X` with
the `2`-cells killing `ker π₁(skelMap X pt)`, mapping to `X` by `E3aModel.baseMap`. -/
noncomputable def famBaseState (X : Type) [TopologicalSpace X] (pt : X) : CWModel.StA X pt 0 where
  Y := E3aModel.BaseSpace X pt
  inst := inferInstance
  y₀ := E3aModel.basePt X pt
  g := E3aModel.baseMap X pt
  gbase := E3aModel.baseMap_base X pt
  conn := E3aModel.pathConnectedSpace_baseSpace X pt
  bij := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact E3aModel.baseMap_pi1_bij X pt

/-- **Homotopy-group bijectivity at every base point from triviality in a range.**  If `h : Γ → L`
induces a bijection on `π₁` and both sides are trivial in degrees `2 ≤ i ≤ N` at the base point,
then `π_i(h)` is bijective at *every* base point of the path connected `Γ`, for `i ≤ N`.  The
statement at another base point follows from the base point change along a path
(`Work.Serre.bijective_piMapN_of_joined`). -/
theorem piMapN_bijective_of_subsingleton {Γ L : Type} [TopologicalSpace Γ] [TopologicalSpace L]
    [PathConnectedSpace Γ] (h : C(Γ, L)) (γ₀ : Γ) (N : ℕ)
    (h0 : Subsingleton (HomotopyGroup (Fin 0) Γ γ₀))
    (h0L : Subsingleton (HomotopyGroup (Fin 0) L (h γ₀)))
    (h1 : Function.Bijective (piMapN h 1 γ₀))
    (hsub : ∀ i : ℕ, 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) Γ γ₀))
    (hsubL : ∀ i : ℕ, 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) L (h γ₀))) :
    ∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (piMapN h i x) := by
  intro i hi x
  have hbγ : Function.Bijective (piMapN h i γ₀) := by
    rcases Nat.eq_zero_or_pos i with h0i | hpos
    · subst h0i
      refine ⟨fun a b _ => h0.elim a b, fun y => ⟨default, h0L.elim _ _⟩⟩
    · rcases Nat.lt_or_ge 1 i with hlt | hle
      · have hi2 : 2 ≤ i := by omega
        refine ⟨fun a b _ => (hsub i hi2 hi).elim a b,
          fun y => ⟨default, (hsubL i hi2 hi).elim _ _⟩⟩
      · have hi1 : i = 1 := by omega
        subst hi1
        exact h1
  exact bijective_piMapN_of_joined h (PathConnectedSpace.joined γ₀ x) i hbγ

/-- **The range form of the `famSpace` route.**  Let `X` be a model of `K(A,1)` and `L` a space
with `π₀(L) = 0`, `π_i(L) = 0` for `2 ≤ i ≤ N` and `H_t(L;ℚ) = 0` for `0 < t ≤ N`, together with a
group isomorphism `π₁(X,pt) ≃* π₁(L,l₀)`.  Then `H_t(X;ℚ) = 0` for `0 < t < N`.

The common space is the top stage `E3aModel.towerB X pt (famBaseState X pt) (N+1)` of the model
tower of `X`: its structure map is `π_i`-bijective for `i ≤ N` into `X`
(`E3aModel.towerB_piMapN_bijective`), and the `L`-map built from `baseStageFamMap` and extended by
`towerStepMap` is `π_i`-bijective as well, so two applications of the range Whitehead theorem
(`Work.Serre.ratH_isZero_of_two_models`) transport the vanishing. -/
theorem ratH_isZero_of_rangeModel {A : Type} [AddCommGroup A]
    (X : Type) [TopologicalSpace X] (pt : X)
    (hX : IsEMSpace A 1 (by norm_num : 0 < 1) X pt) (N : ℕ)
    {L : Type} [TopologicalSpace L] (l₀ : L) (hLpc : PathConnectedSpace L)
    (hL0 : Subsingleton (HomotopyGroup (Fin 0) L l₀))
    (hLsub : ∀ i : ℕ, 2 ≤ i → i ≤ N + 2 → Subsingleton (HomotopyGroup (Fin i) L l₀))
    (hLvan : ∀ t : ℕ, 0 < t → t ≤ N → IsZero (ratH (TopCat.of L) t))
    (φ : HomotopyGroup (Fin 1) X pt ≃* HomotopyGroup (Fin 1) L l₀) :
    ∀ t : ℕ, 0 < t → t < N → IsZero (ratH (TopCat.of X) t) := by
  classical
  haveI hXpc : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero pt (hX.2 0 (by norm_num))
  -- the `L`-map on the base stage
  obtain ⟨gL, hgLbase, hgLbij⟩ := baseStageFamMap (X := X) pt l₀ φ
  -- the `L`-map at every level of the tower
  have key : ∀ k : ℕ, k ≤ N + 1 → ∃ h : C((E3aModel.towerB X pt (famBaseState X pt) k).Y, L),
      h (E3aModel.towerB X pt (famBaseState X pt) k).y₀ = l₀ ∧
      Function.Bijective (piMapN h 1 (E3aModel.towerB X pt (famBaseState X pt) k).y₀) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨gL, hgLbase, hgLbij⟩
    | succ k ih =>
      intro hk
      obtain ⟨h, hb, hbij⟩ := ih (by omega)
      exact towerStepMap (E3aModel.towerB X pt (famBaseState X pt) k) l₀ h hb hbij
        (hLsub (k + 2) (by omega) (by omega))
  obtain ⟨hN, hNbase, hNbij⟩ := key (N + 1) le_rfl
  let Γ := (E3aModel.towerB X pt (famBaseState X pt) (N + 1)).Y
  let γ₀ := (E3aModel.towerB X pt (famBaseState X pt) (N + 1)).y₀
  let gΓ := (E3aModel.towerB X pt (famBaseState X pt) (N + 1)).g
  haveI hΓpc : PathConnectedSpace Γ := (E3aModel.towerB X pt (famBaseState X pt) (N + 1)).conn
  haveI hΓ0 : Subsingleton (HomotopyGroup (Fin 0) Γ γ₀) :=
    (HomotopyGroup.pi0EquivZerothHomotopy (X := Γ) (x := γ₀)).injective.subsingleton
  haveI hZΓ : Subsingleton (ZerothHomotopy Γ) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp hΓpc).2
  -- the `X`-side: the structure map of the top stage
  have hg : ∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (piMapN gΓ i x) :=
    E3aModel.towerB_piMapN_bijective X pt (famBaseState X pt) N
  -- the `L`-side
  have hh : ∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (piMapN hN i x) :=
    piMapN_bijective_of_subsingleton hN γ₀ N hΓ0 (hNbase.symm ▸ hL0) hNbij
      (fun i hi hiN => by
        haveI : Subsingleton (HomotopyGroup (Fin i) X (gΓ γ₀)) :=
          (E3aModel.towerB X pt (famBaseState X pt) (N + 1)).gbase.symm ▸ hX.2 i (by omega)
        exact ((hg i hiN γ₀).injective).subsingleton)
      (fun i hi hiN => hNbase.symm ▸ hLsub i hi (by omega))
  exact ratH_isZero_of_two_models γ₀ gΓ hN N hg hh (fun t ht htN => hLvan t ht htN)

/-- **A model of `K(A,1)` for finite abelian `A` has vanishing rational homology in a range.**
`A` is written as a finite product of cyclic groups, and compared with the product-of-lens-spaces
range model `Work.RatHurewicz.famSpace` of `K(A,1)`, which is rationally acyclic in the range. -/
theorem ratH_isZero_of_isEMSpace_one_finite (A : Type) [AddCommGroup A] [Fintype A]
    (X : Type) [TopologicalSpace X] (pt : X)
    (hX : IsEMSpace A 1 (by norm_num : 0 < 1) X pt) (N : ℕ) :
    ∀ t : ℕ, 0 < t → t < N → IsZero (ratH (TopCat.of X) t) := by
  classical
  obtain ⟨ι, hι, n, hn, ⟨eA⟩⟩ := Work.RatHurewicz.finiteAbelianProdZmod A
  letI := hι
  haveI hne : ∀ i, NeZero (n i) := fun i => ⟨hn i⟩
  obtain ⟨eL⟩ := Work.RatHurewicz.famPiOne (ι := ι) (n := n) (N := N)
  obtain ⟨eX⟩ := hX.1
  refine ratH_isZero_of_rangeModel X pt hX N
    (Work.RatHurewicz.famProjCM ι n N (Work.RatHurewicz.famBase ι N))
    (Work.RatHurewicz.famPathConnected (ι := ι) (n := n) (N := N))
    (Work.RatHurewicz.famSubsingletonPiZero (ι := ι) (n := n) (N := N)
      (Work.RatHurewicz.famProjCM ι n N (Work.RatHurewicz.famBase ι N)))
    (fun i hi hiN => Work.RatHurewicz.famSubsingletonPi (ι := ι) (n := n) (N := N)
      (i := i) hi (by omega))
    (fun t ht htN => Work.RatHurewicz.famIsZeroRatH (ι := ι) (n := n) (N := N) t ht (by omega))
    ((eX.trans eA.toMultiplicative).trans eL.symm)

end FamRoute

theorem serreC3FiniteOne :
    ∀ (A : Type) [AddCommGroup A] [Fintype A] (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpace A 1 (by norm_num : 0 < 1) X pt → Work.Serre.RatAcyclic X := by
  intro A _ _ X _ pt hX
  refine ratAcyclic_of_ratH_vanishing pt (hX.2 0 (by norm_num)) ?_
  intro t ht
  exact ratH_isZero_of_isEMSpace_one_finite A X pt hX (t + 1) t ht (by omega)

end Work.Serre
