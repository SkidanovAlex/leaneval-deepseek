import Submission.Work.ThomBordism.chainSetup_psi_cochainDiff
import Submission.Work.Cohomology.CompactSupport

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The mapping cone of the cochain-level Thom map `ψ`

`Work.ThomBordism.psiAbs` is the cochain-level Thom map of a piece: the cup product with the chosen
relative representative `tauRepAt`.  Its cochain-map property (`psiAbs_diff`, with the toolkit in
`chainSetup_psi_aux`) is proved in `Submission.Work.ThomBordism.chainSetup_psi_cochainDiff`.

This module introduces the **mapping cone** of that cochain map, in the indexing

  `ConeC m = Base^{m+1} ⊕ Tot^{m+n}`,

with differential `coneD (a,b) = (- d a, ψ a + tD b)`, where `tD = totShiftD Z n W m` is the
differential of `TotComplex` at the shifted degree pair `(m+n, (m+1)+n)`.

This indexing is chosen so that **no degree cast occurs**: the source of the second component is
`Tot^{m+n}`, both `ψ^{m+1}` and `tD` land in `Tot^{(m+1)+n}`, and the target of the first component
`Base^{(m+1)+1}` is *syntactically* the first component of `ConeC (m+1)`.

The lowest degree `ConeC 0 = Base^1 ⊕ Tot^n` receives its primitives from the **Extra** term
`ExtraC = Base^0 ⊕ Tot^{n-1}`, with `extraD (a,b) = (-d a, ψ a + tD' b)`; for `n = 0` the truncated
subtraction makes the `Tot`-component inert, which is precisely the convention the bottom degree
needs.  Cyclicity of the cone at degree `m` (every cycle is a boundary, Extra supplying the
primitives at `m = 0`) is what `localThomMap` bijectivity is equivalent to.

## Status

* `coneD_comp` (**`d² = 0`**) is **proved** (`map_neg`/`neg_neg` + `cochainDiffLM_cochainDiffLM` for
  the first component; `psiAbs_diff` at `m+1`, `totShiftD_add` and the composition of consecutive
  `TotComplex` differentials for the second, closed by `abel_nf`);
* the definitions (`ConeC`, `coneD`, `totShiftD`, `ExtraC`, `extraD`) and the cyclicity predicates
  (`ConeCycle`, `ConeBoundaryPos`, `ConeCyclicPos`, `ConeCyclicZero`) are complete.

## Elaboration notes for whoever continues here (all paid for)

1. **Do not `apply Prod.ext`** to a goal whose left-hand side is a pair obtained from a `show`:
   the components come out as `(…, …).1 = 0.1` / `(…).2 = 0.2` and no lemma matches.  State the two
   components as `have h1 : (…).1 = 0` and `have h2 : (…).2 = 0` (with `show` inside to unfold
   `coneD`), then finish with `exact Prod.ext h1 h2`.
2. **Never re-spell `cochainDiffLM ℤ (baseSSet W) k a` for `a : BaseC W k`** in a hypothesis: the
   elaborator expects the unfolded `chainComplex`-form of the argument type and rejects `a`.  Work
   on the terms as they appear in the goal (after `show`), and let
   `cochainDiffLM_cochainDiffLM` (in `chainSetup_psi_aux`) do the vanishing step.  Its proof is a
   *defeq* `exact cochainDiff_cochainDiff (R := ℤ) X α` — note the ring must be given as `(R := ℤ)`,
   since positional application binds `R` first.
3. `cochainDiffLM … (-x)` is `LinearMap`-negation: use `map_neg` **first**, then `neg_neg`.
4. `HomologicalComplex.d_comp_d` is not applied to its indices in that order (they are implicit and
   discharged by unification): state the composite `(d i j ≫ d j k).hom b = 0` and
   `rw [HomologicalComplex.d_comp_d, ModuleCat.hom_zero, LinearMap.zero_apply]` (as in
   `rc_diff_comp_zero`), then `rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h`.
5. `abel` leaves goals in this shape; use **`abel_nf`**.
-/

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type} (Z : RealBundle B F ι)

/-- The simplicial set of the base piece `W`. -/
abbrev baseSSet (W : Set B) : SSet := TopCat.toSSet.obj (TopCat.of ↥W)

/-- The simplicial set of the piece of the total space over `W`. -/
abbrev pieceSSet (W : Set B) : SSet := TopCat.toSSet.obj (TopCat.of ↥(Z.proj ⁻¹' W))

/-- The degrees of the cone of the Thom cup map: `ConeC m = Base^{m+1} ⊕ Tot^{m+n}`. -/
abbrev ConeC (n : ℕ) (W : Set B) (m : ℕ) : Type := BaseC W (m + 1) × TotC Z W (m + n)

/-- The differential of `TotComplex` at the shifted degree pair `(m+n, (m+1)+n)`, as a map of the
relative cochain modules `TotC`. -/
def totShiftD (n : ℕ) (W : Set B) (m : ℕ) : TotC Z W (m + n) → TotC Z W ((m + 1) + n) :=
  fun b => ((TotComplex Z W).d (m + n) ((m + 1) + n)).hom b

/-- The differential of `TotComplex` at the pair `(n-1, n)` (used by the Extra term).  For `n = 0`
the truncated subtraction makes this the zero map. -/
def totDpred (n : ℕ) (W : Set B) : TotC Z W (n - 1) → TotC Z W (0 + n) :=
  fun b => ((TotComplex Z W).d (n - 1) (0 + n)).hom b

/-- `totShiftD` is additive (it is a differential of `TotComplex`). -/
theorem totShiftD_add (n : ℕ) (W : Set B) (m : ℕ) (b b' : TotC Z W (m + n)) :
    totShiftD Z n W m (b + b') = totShiftD Z n W m b + totShiftD Z n W m b' := by
  show ((TotComplex Z W).d (m + n) ((m + 1) + n)).hom (b + b')
      = ((TotComplex Z W).d (m + n) ((m + 1) + n)).hom b
        + ((TotComplex Z W).d (m + n) ((m + 1) + n)).hom b'
  rw [map_add]

/-- `totShiftD` is additive, negative and subtractive (it is a differential of `TotComplex`). -/
theorem totShiftD_neg (n : ℕ) (W : Set B) (m : ℕ) (b : TotC Z W (m + n)) :
    totShiftD Z n W m (-b) = -totShiftD Z n W m b := by
  show ((TotComplex Z W).d (m + n) ((m + 1) + n)).hom (-b)
      = -((TotComplex Z W).d (m + n) ((m + 1) + n)).hom b
  rw [map_neg]

/-- `totShiftD` is subtractive (see `totShiftD_neg`). -/
theorem totShiftD_sub (n : ℕ) (W : Set B) (m : ℕ) (b b' : TotC Z W (m + n)) :
    totShiftD Z n W m (b - b') = totShiftD Z n W m b - totShiftD Z n W m b' := by
  show ((TotComplex Z W).d (m + n) ((m + 1) + n)).hom (b - b')
      = ((TotComplex Z W).d (m + n) ((m + 1) + n)).hom b
        - ((TotComplex Z W).d (m + n) ((m + 1) + n)).hom b'
  rw [map_sub]

/-- The differential of the cone: `(a,b) ↦ (-da, ψ a + tD b)`. -/
def coneD (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U) (m : ℕ) :
    ConeC Z n W m → ConeC Z n W (m + 1) :=
  fun p => (-(cochainDiffLM ℤ (baseSSet W) (m + 1) p.1),
    (psiAbsLM Z n U τ W hW (m + 1) p.1 + totShiftD Z n W m p.2))

/-- **The cone differential is additive** (each of its three ingredients is).  This is what lets the
converse leg combine the primitive supplied by the injectivity step with the one supplied by the
surjectivity step into the single primitive `ConeBoundaryPos` asks for.

The two components are proved without ever producing a projection: `simp only [Prod.mk.injEq]` on
the explicit `(…, …) = (…, …)` goal gives the component equations in *literal* form, which `abel`
then normalises (the `(…).1`-shaped goals of `apply Prod.ext` do not, cf. the header notes). -/
theorem coneD_add (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (m : ℕ) (x y : ConeC Z n W m) :
    coneD Z n U τ W hW m (x + y) = coneD Z n U τ W hW m x + coneD Z n U τ W hW m y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, e⟩ := y
  show (-(cochainDiffLM ℤ (baseSSet W) (m + 1) (a + c)),
        psiAbsLM Z n U τ W hW (m + 1) (a + c) + totShiftD Z n W m (b + e))
      = (-(cochainDiffLM ℤ (baseSSet W) (m + 1) a),
          psiAbsLM Z n U τ W hW (m + 1) a + totShiftD Z n W m b)
        + (-(cochainDiffLM ℤ (baseSSet W) (m + 1) c),
            psiAbsLM Z n U τ W hW (m + 1) c + totShiftD Z n W m e)
  simp only [map_add, totShiftD_add, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> abel

/-- The differential of the cone, applied to an explicit pair. -/
theorem coneD_apply (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (m : ℕ) (a : BaseC W (m + 1)) (b : TotC Z W (m + n)) :
    coneD Z n U τ W hW m (a, b)
      = (-(cochainDiffLM ℤ (baseSSet W) (m + 1) a),
          psiAbsLM Z n U τ W hW (m + 1) a + totShiftD Z n W m b) :=
  rfl

/-- **The cone is a complex**: `d² = 0`.

The computation is pointwise: with `C = cochainDiffLM ℤ (baseSSet W) (m+1)`, `ψ = psiAbsLM … (m+1)`
and `tD = totShiftD Z n W m`, one has `coneD m (a,b) = (-(C a), ψ a + tD b)`, hence
`coneD (m+1) (coneD m (a,b)) = (C (C a), ψ' (-(C a)) + tD' (ψ a + tD b))`.  The first component
vanishes by `cochainDiff_cochainDiff`; the second is
`-(ψ' (C a)) + (tD' (ψ a) + tD' (tD b)) = -(ψ' (C a)) + (ψ' (C a) + 0) = 0`
using `psiAbs_diff` at `m+1` for `tD' (ψ a) = ψ' (C a)` and the composition of consecutive
differentials of `TotComplex` for `tD' (tD b) = 0`. -/
theorem coneD_comp (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (m : ℕ) (p : ConeC Z n W m) :
    coneD Z n U τ W hW (m + 1) (coneD Z n U τ W hW m p) = 0 := by
  obtain ⟨a, b⟩ := p
  have h1 : (coneD Z n U τ W hW (m + 1) (coneD Z n U τ W hW m (a, b))).1 = 0 := by
    show -(cochainDiffLM ℤ (baseSSet W) ((m + 1) + 1)
        (-(cochainDiffLM ℤ (baseSSet W) (m + 1) a))) = 0
    rw [map_neg, neg_neg, cochainDiffLM_cochainDiffLM]
  have h2 : (coneD Z n U τ W hW (m + 1) (coneD Z n U τ W hW m (a, b))).2 = 0 := by
    show psiAbsLM Z n U τ W hW ((m + 1) + 1)
          (-(cochainDiffLM ℤ (baseSSet W) (m + 1) a))
        + totShiftD Z n W (m + 1)
            (psiAbsLM Z n U τ W hW (m + 1) a + totShiftD Z n W m b) = 0
    rw [map_neg, totShiftD_add]
    have hDD : totShiftD Z n W (m + 1) (totShiftD Z n W m b) = 0 := by
      show ((TotComplex Z W).d ((m + 1) + n) (((m + 1) + 1) + n)).hom
          (((TotComplex Z W).d (m + n) ((m + 1) + n)).hom b) = 0
      have hcomp : (((TotComplex Z W).d (m + n) ((m + 1) + n)) ≫
          ((TotComplex Z W).d ((m + 1) + n) (((m + 1) + 1) + n))).hom b = 0 := by
        rw [HomologicalComplex.d_comp_d, ModuleCat.hom_zero, LinearMap.zero_apply]
      rw [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
      exact hcomp
    have hψ : totShiftD Z n W (m + 1) (psiAbsLM Z n U τ W hW (m + 1) a)
        = psiAbsLM Z n U τ W hW ((m + 1) + 1)
            (cochainDiffLM ℤ (baseSSet W) (m + 1) a) := by
      show ((TotComplex Z W).d ((m + 1) + n) (((m + 1) + 1) + n)).hom
          (psiAbs Z n U τ W hW (m + 1) a)
        = psiAbs Z n U τ W hW ((m + 1) + 1)
            (cochainDiffLM ℤ (baseSSet W) (m + 1) a)
      rw [psiAbs_diff Z n U τ W hW (m + 1) a]
      rfl
    rw [hDD, hψ]
    abel_nf
  exact Prod.ext h1 h2

/-- The **Extra** term of the cone: `ExtraC = Base^0 ⊕ Tot^{n-1}`. -/
abbrev ExtraC (n : ℕ) (W : Set B) : Type := BaseC W 0 × TotC Z W (n - 1)

/-- The differential of the Extra term into the degree-`0` part of the cone. -/
def extraD (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U) :
    ExtraC Z n W → ConeC Z n W 0 :=
  fun p => (-(cochainDiffLM ℤ (baseSSet W) 0 p.1),
    (psiAbsLM Z n U τ W hW 0 p.1 + totDpred Z n W p.2))

/-- A cone-`m`-cycle. -/
def ConeCycle (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (m : ℕ) (p : ConeC Z n W m) : Prop := coneD Z n U τ W hW m p = 0

/-- `p` is a boundary at the positive degree `m + 1`: it lies in the image of `coneD m`. -/
def ConeBoundaryPos (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (m : ℕ) (p : ConeC Z n W (m + 1)) : Prop :=
  ∃ q : ConeC Z n W m, coneD Z n U τ W hW m q = p

/-- **Cyclicity of the cone at the positive degree `m + 1`.** -/
def ConeCyclicPos (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (m : ℕ) : Prop :=
  ∀ p : ConeC Z n W (m + 1), ConeCycle Z n U τ W hW (m + 1) p → ConeBoundaryPos Z n U τ W hW m p

/-- **The forward direction, injectivity half (positive degrees).**

If the cone is cyclic at degree `m`, then every cone-`(m+1)`-cycle `(a, b)` has its base component
`a` a coboundary: `a = - d a'` for some `a' ∈ Base^m`.  Read through the cone differential
`coneD m (a',b') = (-d a', ψ a' + tD b')`, this is exactly the injectivity half of the statement
that `ψ` induces an isomorphism in the corresponding degree: a cycle `a` whose `ψ`-image is a
boundary is itself a boundary.

Note the shape: the cycle hypothesis is stated as `ConeCycle … (m+1) (a, b)`, i.e. as
`coneD (m+1) (a,b) = 0`; this avoids re-spelling `cochainDiffLM … a` (see the header notes). -/
theorem coneCyclicPos_inj (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B)
    (hW : W ⊆ U) (m : ℕ) (h : ConeCyclicPos Z n U τ W hW m)
    {a : BaseC W ((m + 1) + 1)} {b : TotC Z W ((m + 1) + n)}
    (hcyc : ConeCycle Z n U τ W hW (m + 1) (a, b)) :
    ∃ a' : BaseC W (m + 1), cochainDiffLM ℤ (baseSSet W) (m + 1) a' = -a := by
  obtain ⟨q, hq⟩ := h (a, b) hcyc
  obtain ⟨a', b'⟩ := q
  have h1 : -(cochainDiffLM ℤ (baseSSet W) (m + 1) a') = a := by
    have h2 := congrArg Prod.fst hq
    simpa only [coneD_apply] using h2
  exact ⟨a', by rw [← h1, neg_neg]⟩

/-- **The forward direction, surjectivity half (positive degrees).**

If the cone is cyclic at degree `m`, then every cycle `b ∈ Tot^{(m+1)+n}` is `ψ^{m+1}` of a *cycle*
of `Base^{m+1}` up to a boundary: `(0, b) = coneD m q`, i.e. `b = ψ^{m+1} q.1 + tD q.2` with
`d q.1 = 0`.  This is the surjectivity half of `ψ` inducing an isomorphism in the corresponding
degree. -/
theorem coneCyclicPos_surj (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B)
    (hW : W ⊆ U) (m : ℕ) (h : ConeCyclicPos Z n U τ W hW m)
    {b : TotC Z W ((m + 1) + n)} (hb : totShiftD Z n W (m + 1) b = 0) :
    ∃ q : ConeC Z n W m, coneD Z n U τ W hW m q = (0, b) := by
  have hcyc : ConeCycle Z n U τ W hW (m + 1) ((0 : BaseC W ((m + 1) + 1)), b) := by
    show coneD Z n U τ W hW (m + 1) ((0 : BaseC W ((m + 1) + 1)), b) = 0
    rw [coneD_apply]
    simp only [map_zero, neg_zero, zero_add, hb]
    rfl
  exact h ((0 : BaseC W ((m + 1) + 1)), b) hcyc

/-- **Cyclicity of the cone at degree `0`** (the primitives come from the Extra term). -/
def ConeCyclicZero (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U) :
    Prop :=
  ∀ p : ConeC Z n W 0, ConeCycle Z n U τ W hW 0 p → ∃ q : ExtraC Z n W, extraD Z n U τ W hW q = p

/-- **The forward direction at degree `0`, injectivity half (Extra primitives).**

If the cone is cyclic at degree `0` -- every degree-`0` cycle is `extraD` of an element of the Extra
term -- then every degree-`0` cone-cycle `(a, b)` has its base component `a` a coboundary *from
degree `0`*: `a = -d a'` for some `a' ∈ Base^0`.  This is the injectivity half of `ψ` being an
isomorphism in degree `1`, and it is the case the Extra term exists for: the primitives live one
degree below `ConeC 0`, where `ConeC` itself has nothing.

The pattern is that of `coneCyclicPos_inj`, with `extraD` in place of `coneD`. -/
theorem coneCyclicZero_inj (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B)
    (hW : W ⊆ U) (h : ConeCyclicZero Z n U τ W hW)
    {a : BaseC W (0 + 1)} {b : TotC Z W (0 + n)}
    (hcyc : ConeCycle Z n U τ W hW 0 (a, b)) :
    ∃ a' : BaseC W 0, cochainDiffLM ℤ (baseSSet W) 0 a' = -a := by
  obtain ⟨q, hq⟩ := h (a, b) hcyc
  obtain ⟨a', b'⟩ := q
  have h1 : -(cochainDiffLM ℤ (baseSSet W) 0 a') = a := by
    have h2 := congrArg Prod.fst hq
    simpa only [extraD] using h2
  exact ⟨a', by rw [← h1, neg_neg]⟩

/-- **The forward direction at degree `0`, surjectivity half (Extra primitives).**

Every cycle `b ∈ Tot^n` is the second component of an `extraD`-image of `(0, b)`: the degree-`0`
analogue of `coneCyclicPos_surj`, proved by the same `(0, b)` trick. -/
theorem coneCyclicZero_surj (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B)
    (hW : W ⊆ U) (h : ConeCyclicZero Z n U τ W hW) {b : TotC Z W (0 + n)}
    (hb : totShiftD Z n W 0 b = 0) :
    ∃ q : ExtraC Z n W, extraD Z n U τ W hW q = (0, b) := by
  have hcyc : ConeCycle Z n U τ W hW 0 ((0 : BaseC W (0 + 1)), b) := by
    show coneD Z n U τ W hW 0 ((0 : BaseC W (0 + 1)), b) = 0
    rw [coneD_apply]
    simp only [map_zero, neg_zero, zero_add, hb]
    rfl
  exact h ((0 : BaseC W (0 + 1)), b) hcyc



/-- The first component of a zero product (a `rfl`-lemma, handy in `simp only` sets). -/
@[simp] theorem prod_zero_fst {α β : Type} [Zero α] [Zero β] :
    ((0 : α × β)).1 = 0 := rfl

/-- The second component of a zero product (a `rfl`-lemma). -/
@[simp] theorem prod_zero_snd {α β : Type} [Zero α] [Zero β] :
    ((0 : α × β)).2 = 0 := rfl

/-- **First component of the cone-cycle condition.**  A cone-`(m+1)`-cycle has its base component a
cycle of the base complex.  This is the reverse of the extraction used in `coneCyclicPos_inj`, and
the starting point of the converse leg (`δ` injective ∧ `δ` surjective ⟹ cyclicity). -/
theorem coneCycle_fst (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (m : ℕ) {a : BaseC W ((m + 1) + 1)} {b : TotC Z W ((m + 1) + n)}
    (h : ConeCycle Z n U τ W hW (m + 1) (a, b)) :
    cochainDiffLM ℤ (baseSSet W) ((m + 1) + 1) a = 0 := by
  have h2 := congrArg Prod.fst h
  simpa only [coneD_apply, neg_eq_zero, prod_zero_fst] using h2

/-- **Second component of the cone-cycle condition.**  A cone-`(m+1)`-cycle `(a,b)` satisfies
`ψ a + tD b = 0`, i.e. `ψ a` is the negative of a `Tot`-boundary of `b` — which is what makes
`coneCyclicPos_inj`'s hypothesis match the elementwise injectivity statement for `ψ`. -/
theorem coneCycle_snd (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (m : ℕ) {a : BaseC W ((m + 1) + 1)} {b : TotC Z W ((m + 1) + n)}
    (h : ConeCycle Z n U τ W hW (m + 1) (a, b)) :
    psiAbsLM Z n U τ W hW ((m + 1) + 1) a + totShiftD Z n W (m + 1) b = 0 := by
  have h2 := congrArg Prod.snd h
  simpa only [coneD_apply, prod_zero_snd] using h2


/-- `totDpred` is additive (it is a differential of `TotComplex`). -/
theorem totDpred_add (n : ℕ) (W : Set B) (b b' : TotC Z W (n - 1)) :
    totDpred Z n W (b + b') = totDpred Z n W b + totDpred Z n W b' := by
  show ((TotComplex Z W).d (n - 1) (0 + n)).hom (b + b')
      = ((TotComplex Z W).d (n - 1) (0 + n)).hom b
        + ((TotComplex Z W).d (n - 1) (0 + n)).hom b'
  rw [map_add]

/-- **The Extra differential is additive** — the degree-`0` twin of `coneD_add`, and the ingredient
the degree-`0` converse assembly (combining the primitive from the injectivity step with the one from
the surjectivity step) needs.  Proved by the projection-free component route. -/
theorem extraD_add (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (x y : ExtraC Z n W) :
    extraD Z n U τ W hW (x + y) = extraD Z n U τ W hW x + extraD Z n U τ W hW y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, e⟩ := y
  show (-(cochainDiffLM ℤ (baseSSet W) 0 (a + c)),
        psiAbsLM Z n U τ W hW 0 (a + c) + totDpred Z n W (b + e))
      = (-(cochainDiffLM ℤ (baseSSet W) 0 a),
          psiAbsLM Z n U τ W hW 0 a + totDpred Z n W b)
        + (-(cochainDiffLM ℤ (baseSSet W) 0 c),
            psiAbsLM Z n U τ W hW 0 c + totDpred Z n W e)
  simp only [map_add, totDpred_add, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> abel


end

end Work.ThomBordism
