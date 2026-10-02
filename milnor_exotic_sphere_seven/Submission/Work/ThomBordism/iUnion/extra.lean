import Submission.Work.ThomBordism.chainSetup_cone
import Submission.Work.ThomBordism.Tower.ConeTheory
import Submission.Work.ThomBordism.coneCyclicZero_of_inj_surj

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The `Extra` term of the mapping cone: restrictions, naturality, gluing

The mapping cone of the cochain-level Thom map `psiAbs` is

  `ConeC m = Base^{m+1} ⊕ Tot^{m+n}`,  `coneD m (a,b) = (- d a, ψ^{m+1} a + tD b)`,

and its degree-`0` primitives live one degree below `ConeC 0`, in the **Extra** term
`ExtraC = Base^0 ⊕ Tot^{n-1}`, with `extraD (a,b) = (- d a, ψ^0 a + tD' b)`.

This module develops the tower theory of the Extra term, so that the *bottom* of the tower
(the degrees `ConeC 0` and `ConeC 1`, whose primitives are supplied by the pieces' behaviour in
degrees `0` and `1`) can be argued exactly as the positive degrees are in
`Submission/Work/ThomBordism/Tower/`:

* `extraRes` — the restriction of the Extra term along `W ⊆ W'`, with its laws
  (`extraRes_apply`, `extraRes_zero`, `extraRes_add`, `extraRes_sub`, `extraRes_comp`,
  `extraRes_self`, `extraRes_proof_irrel`, `extraRes_surjective`);
* `totDpred` — the incoming total differential of the Extra term (`n - 1 → 0 + n`), with
  `totDpred_zero_degree` (the truncated case `n = 0`), `totDpred_succ` (the consecutive form),
  `totDpred_neg`, `totDpred_sub` and the naturality `rcResLM_totDpred`;
* `coneRes_extraD` — **naturality of the Extra differential**, `coneRes` on the cone side and
  `extraRes` on the Extra side;
* `coneD_zero_extraD` — **`coneD 0 ∘ extraD = 0`** (the augmented complex is a complex);
* `extraD_zero`, `extraD_neg`, `extraD_sub` — the additive laws of `extraD`;
* `extraGlue`, `extraRes_eq_of_forall` — gluing and separation of compatible families of Extra
  elements over an increasing open family.
-/

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The restriction of the Extra term -/

/-- The restriction of the Extra term of the mapping cone along an inclusion of pieces:
`baseRes` in degree `0` on the base component and the relative-cochain restriction in degree
`n - 1` on the total component.  This is the degree `-1` analogue of `coneRes`. -/
def extraRes (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h : W ⊆ W') :
    ExtraC Z n W' → ExtraC Z n W :=
  fun q => (baseRes h 0 q.1,
    rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (n - 1) q.2)

/-- The defining formula of `extraRes`. -/
theorem extraRes_apply (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h : W ⊆ W')
    (q : ExtraC Z n W') :
    extraRes Z n h q = (baseRes h 0 q.1,
      rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (n - 1) q.2) := rfl

/-- `extraRes` sends zero to zero. -/
@[simp] theorem extraRes_zero (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h : W ⊆ W') :
    extraRes Z n h (0 : ExtraC Z n W') = 0 := by
  refine Prod.ext ?_ ?_
  · show baseRes h 0 (0 : BaseC W' 0) = (0 : BaseC W 0)
    simp
  · show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (n - 1)
        (0 : TotC Z W' (n - 1)) = (0 : TotC Z W (n - 1))
    simp

/-- `extraRes` is additive. -/
theorem extraRes_add (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h : W ⊆ W')
    (q q' : ExtraC Z n W') : extraRes Z n h (q + q') = extraRes Z n h q + extraRes Z n h q' := by
  refine Prod.ext ?_ ?_
  · show baseRes h 0 ((q + q').1) = baseRes h 0 q.1 + baseRes h 0 q'.1
    rw [Prod.fst_add, map_add]
  · show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (n - 1) ((q + q').2)
        = rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (n - 1) q.2
          + rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (n - 1) q'.2
    rw [Prod.snd_add, map_add]

/-- `extraRes` is negated by negation. -/
theorem extraRes_neg (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h : W ⊆ W')
    (q : ExtraC Z n W') : extraRes Z n h (-q) = -extraRes Z n h q := by
  refine Prod.ext ?_ ?_
  · show baseRes h 0 ((-q).1) = -(baseRes h 0 q.1)
    rw [Prod.fst_neg, map_neg]
  · show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (n - 1) ((-q).2)
        = -(rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (n - 1) q.2)
    rw [Prod.snd_neg, map_neg]

/-- `extraRes` is subtractive. -/
theorem extraRes_sub (Z : RealBundle B F ι) (n : ℕ) {W W' : Set B} (h : W ⊆ W')
    (q q' : ExtraC Z n W') : extraRes Z n h (q - q') = extraRes Z n h q - extraRes Z n h q' := by
  refine Prod.ext ?_ ?_
  · show baseRes h 0 ((q - q').1) = baseRes h 0 q.1 - baseRes h 0 q'.1
    rw [Prod.fst_sub, map_sub]
  · show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (n - 1) ((q - q').2)
        = rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (n - 1) q.2
          - rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (n - 1) q'.2
    rw [Prod.snd_sub, map_sub]

/-- `extraRes` is compatible with composition of inclusions. -/
theorem extraRes_comp (Z : RealBundle B F ι) (n : ℕ) {S S' T : Set B} (h : S ⊆ S')
    (h' : S' ⊆ T) (q : ExtraC Z n T) :
    extraRes Z n h (extraRes Z n h' q) = extraRes Z n (h.trans h') q := by
  refine Prod.ext ?_ ?_
  · show baseRes h 0 (baseRes h' 0 q.1) = baseRes (h.trans h') 0 q.1
    rw [← LinearMap.comp_apply, baseRes_comp]
  · show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (n - 1)
        (rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h') (n - 1) q.2)
      = rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (h.trans h')) (n - 1) q.2
    have hpm : Set.preimage_mono (f := Z.proj) (h.trans h')
        = (Set.preimage_mono (f := Z.proj) h).trans (Set.preimage_mono (f := Z.proj) h') :=
      Subsingleton.elim _ _
    rw [← LinearMap.comp_apply, rcResLM_comp, hpm]

/-- `extraRes` along a self-inclusion is the identity. -/
theorem extraRes_self (Z : RealBundle B F ι) (n : ℕ) {S : Set B} (h : S ⊆ S)
    (q : ExtraC Z n S) : extraRes Z n h q = q := by
  refine Prod.ext ?_ ?_
  · show baseRes h 0 q.1 = q.1
    rw [baseRes_self h 0]
    rfl
  · show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono (f := Z.proj) h) (n - 1) q.2
      = q.2
    have hf : Set.preimage_mono (f := Z.proj) h = Set.Subset.refl (Z.proj ⁻¹' S) :=
      Subsingleton.elim _ _
    rw [hf]
    exact rcResLM_self (Work.Thom.zeroComplement Z) (Set.Subset.refl (Z.proj ⁻¹' S)) (n - 1) q.2

/-- `extraRes` does not depend on the proof of the inclusion. -/
theorem extraRes_proof_irrel (Z : RealBundle B F ι) (n : ℕ) {S T : Set B} (h h' : S ⊆ T) :
    extraRes Z n h = extraRes Z n h' := by
  have : h = h' := Subsingleton.elim _ _
  rw [this]

/-- `extraRes` is surjective (both components are restrictions of cochains of larger pieces). -/
theorem extraRes_surjective (Z : RealBundle B F ι) (n : ℕ) {S T : Set B} (h : S ⊆ T) :
    Function.Surjective (extraRes Z n h) := by
  intro q
  obtain ⟨a, ha⟩ := baseRes_surjective h 0 q.1
  obtain ⟨b, hb⟩ := rcResLM_surjective (Work.Thom.zeroComplement Z) (Set.preimage_mono h)
    (n - 1) q.2
  exact ⟨(a, b), Prod.ext ha hb⟩

/-! ## The incoming total differential of the Extra term -/

/-- **Naturality of the total differential at an arbitrary degree pair.**  The restriction of a
relative cochain to a smaller piece commutes with the differential of `TotComplex`, at *any* pair of
degrees `(i, j)`: the two sides are `(dualChainMap …).f i` followed by `d i j` and `d i j` followed
by `(dualChainMap …).f j`, which agree by `HomologicalComplex.Hom.comm`.

Stating this with the degrees as *variables* avoids all arithmetic bookkeeping: the consecutive case
is a restatement in terms of `rcDiff` (where `rcResLM_comm` applies), and the non-consecutive case
has both sides zero. -/
theorem rcResLM_relD (Z : RealBundle B F ι) {S T : Set B} (h : S ⊆ T) (i j : ℕ) (x : TotC Z T i) :
    rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) j
        (((TotComplex Z T).d i j).hom x)
      = ((TotComplex Z S).d i j).hom
          (rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) i x) := by
  by_cases hij : i + 1 = j
  · subst hij
    -- the consecutive case: reduce `d i (i+1)` to `relDiffLM` and use `rcResLM_comm`
    have hT : ((TotComplex Z T).d i (i + 1))
        = relDiff ℤ (TopCat.of ↥(Z.proj ⁻¹' T)) (relPiece Z T) i :=
      relComplex_d ℤ (TopCat.of ↥(Z.proj ⁻¹' T)) (relPiece Z T) i
    have hS : ((TotComplex Z S).d i (i + 1))
        = relDiff ℤ (TopCat.of ↥(Z.proj ⁻¹' S)) (relPiece Z S) i :=
      relComplex_d ℤ (TopCat.of ↥(Z.proj ⁻¹' S)) (relPiece Z S) i
    rw [hT, hS]
    exact rcResLM_comm (A := Work.Thom.zeroComplement Z) (Set.preimage_mono h) i x
  · -- the non-consecutive case: both differentials vanish
    have hT : ((TotComplex Z T).d i j) = 0 :=
      (TotComplex Z T).shape i j (by simpa only [ComplexShape.up_Rel] using hij)
    have hS : ((TotComplex Z S).d i j) = 0 :=
      (TotComplex Z S).shape i j (by simpa only [ComplexShape.up_Rel] using hij)
    rw [hT, hS]
    simp

/-- **The incoming total differential of the Extra term commutes with the restriction.**  This is
`rcResLM_relD` at the pair `(n - 1, 0 + n)`. -/
theorem rcResLM_totDpred (Z : RealBundle B F ι) (n : ℕ) {S T : Set B} (h : S ⊆ T)
    (x : TotC Z T (n - 1)) :
    rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (0 + n) (totDpred Z n T x)
      = totDpred Z n S (rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (n - 1) x) :=
  rcResLM_relD Z h (n - 1) (0 + n) x

/-! ## Naturality of the Extra differential -/

/-- **Naturality of the Extra differential.**  Restricting `extraD q` from the piece `W'` to `W` is
`extraD` of the restricted element.  The base component is `baseRes_comm`, the total component is
the naturality `psiAbs_natural` of the cochain-level Thom map together with `rcResLM_totDpred`. -/
theorem coneRes_extraD (Z : RealBundle B F ι) (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n)
    {W W' : Set B} (h : W ⊆ W') (hW : W ⊆ U) (hW' : W' ⊆ U) (q : ExtraC Z n W') :
    coneRes Z n h 0 (extraD Z n U τ W' hW' q) = extraD Z n U τ W hW (extraRes Z n h q) := by
  obtain ⟨a, b⟩ := q
  refine Prod.ext ?_ ?_
  · show baseRes h (0 + 1) (-(cochainDiffLM ℤ (baseSSet W') 0 a))
      = -(cochainDiffLM ℤ (baseSSet W) 0 (baseRes h 0 a))
    rw [map_neg, baseRes_comm]
  · show rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (0 + n)
        (psiAbs Z n U τ W' hW' 0 a + totDpred Z n W' b)
      = psiAbs Z n U τ W hW 0 (baseRes h 0 a)
        + totDpred Z n W (rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono h) (n - 1) b)
    rw [map_add, Tower.psiAbs_natural Z n U τ h hW hW' 0 a, rcResLM_totDpred Z n h b]

/-! ## The additive laws of `extraD` -/

/-- `extraD` vanishes on zero. -/
theorem extraD_zero (Z : RealBundle B F ι) (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n)
    (W : Set B) (hW : W ⊆ U) :
    extraD Z n U τ W hW (0 : ExtraC Z n W) = 0 := by
  show (-(cochainDiffLM ℤ (baseSSet W) 0 (0 : BaseC W 0)),
      psiAbsLM Z n U τ W hW 0 (0 : BaseC W 0) + totDpred Z n W (0 : TotC Z W (n - 1)))
    = (0 : ConeC Z n W 0)
  simp only [map_zero, totDpred_zero Z n W, neg_zero, add_zero]
  rfl

/-- The incoming total differential of the Extra term is negated by negation. -/
theorem totDpred_neg (Z : RealBundle B F ι) (n : ℕ) (W : Set B) (b : TotC Z W (n - 1)) :
    totDpred Z n W (-b) = -totDpred Z n W b := by
  show ((TotComplex Z W).d (n - 1) (0 + n)).hom (-b)
      = -((TotComplex Z W).d (n - 1) (0 + n)).hom b
  rw [map_neg]

/-- `extraD` is negated by negation. -/
theorem extraD_neg (Z : RealBundle B F ι) (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n)
    (W : Set B) (hW : W ⊆ U) (q : ExtraC Z n W) :
    extraD Z n U τ W hW (-q) = -extraD Z n U τ W hW q := by
  obtain ⟨a, b⟩ := q
  refine Prod.ext ?_ ?_
  · show -(cochainDiffLM ℤ (baseSSet W) 0 (-a)) = -(-(cochainDiffLM ℤ (baseSSet W) 0 a))
    rw [map_neg, neg_neg]
  · show psiAbsLM Z n U τ W hW 0 (-a) + totDpred Z n W (-b)
      = -(psiAbsLM Z n U τ W hW 0 a + totDpred Z n W b)
    rw [map_neg, totDpred_neg, neg_add]

/-- `extraD` is subtractive. -/
theorem extraD_sub (Z : RealBundle B F ι) (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n)
    (W : Set B) (hW : W ⊆ U) (q q' : ExtraC Z n W) :
    extraD Z n U τ W hW (q - q') = extraD Z n U τ W hW q - extraD Z n U τ W hW q' := by
  rw [sub_eq_add_neg, extraD_add, extraD_neg, sub_eq_add_neg]

/-! ## The augmented complex is a complex: `coneD 0 ∘ extraD = 0` -/

/-- **`coneD 0 ∘ extraD = 0`.**  The first component is `cochainDiff_cochainDiff`; the second is
`psiAbs_diff` at degree `0` (which turns `totShiftD 0 (ψ^0 a)` into `ψ^1 (d a)`) together with the
composition of the consecutive differentials of `TotComplex` (which kills
`totShiftD 0 (totDpred b)`). -/
theorem coneD_zero_extraD (Z : RealBundle B F ι) (n : ℕ) (U : Set B)
    (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U) (q : ExtraC Z n W) :
    coneD Z n U τ W hW 0 (extraD Z n U τ W hW q) = 0 := by
  obtain ⟨a, b⟩ := q
  have h1 : (coneD Z n U τ W hW 0 (extraD Z n U τ W hW (a, b))).1 = 0 := by
    show -(cochainDiffLM ℤ (baseSSet W) (0 + 1)
        (-(cochainDiffLM ℤ (baseSSet W) 0 a))) = 0
    rw [map_neg, neg_neg, cochainDiffLM_cochainDiffLM]
  have h2 : (coneD Z n U τ W hW 0 (extraD Z n U τ W hW (a, b))).2 = 0 := by
    show psiAbsLM Z n U τ W hW (0 + 1) (-(cochainDiffLM ℤ (baseSSet W) 0 a))
      + totShiftD Z n W 0
          (psiAbsLM Z n U τ W hW 0 a + totDpred Z n W b) = 0
    rw [map_neg, totShiftD_add]
    have hDD : totShiftD Z n W 0 (totDpred Z n W b) = 0 := by
      show ((TotComplex Z W).d (0 + n) ((0 + 1) + n)).hom
          (((TotComplex Z W).d (n - 1) (0 + n)).hom b) = 0
      have hcomp : (((TotComplex Z W).d (n - 1) (0 + n)) ≫
          ((TotComplex Z W).d (0 + n) ((0 + 1) + n))).hom b = 0 := by
        rw [HomologicalComplex.d_comp_d, ModuleCat.hom_zero, LinearMap.zero_apply]
      rw [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
      exact hcomp
    have hψ : totShiftD Z n W 0 (psiAbsLM Z n U τ W hW 0 a)
        = psiAbsLM Z n U τ W hW (0 + 1) (cochainDiffLM ℤ (baseSSet W) 0 a) := by
      show ((TotComplex Z W).d (0 + n) ((0 + 1) + n)).hom (psiAbs Z n U τ W hW 0 a)
        = psiAbs Z n U τ W hW (0 + 1) (cochainDiffLM ℤ (baseSSet W) 0 a)
      rw [psiAbs_diff Z n U τ W hW 0 a]
      rfl
    rw [hDD, hψ]
    abel_nf
  exact Prod.ext h1 h2

/-! ## Gluing and separation for the Extra term -/

/-- **Gluing of a compatible family of Extra elements.** -/
theorem extraGlue (Z : RealBundle B F ι) (n : ℕ) (W : ℕ → Set B) (hopen : ∀ a, IsOpen (W a))
    (hmono : ∀ a b, a ≤ b → W a ⊆ W b) (q : (a : ℕ) → ExtraC Z n (W a))
    (hq : ∀ a b (hab : a ≤ b), extraRes Z n (hmono a b hab) (q b) = q a) :
    ∃! Q : ExtraC Z n (⋃ a, W a), ∀ a, extraRes Z n (Set.subset_iUnion W a) Q = q a := by
  obtain ⟨g, hg, -⟩ := baseGlue W hopen (fun a b h => hmono a b h) 0
    (fun a => (q a).1) (fun a b hab => by
      have := congrArg Prod.fst (hq a b hab)
      simpa only [extraRes_apply] using this)
  obtain ⟨g', hg', -⟩ := Tower.totGlue Z W hopen hmono (n - 1)
    (fun a => (q a).2) (fun a b hab => by
      have := congrArg Prod.snd (hq a b hab)
      simpa only [extraRes_apply] using this)
  refine ⟨(g, g'), ?_, ?_⟩
  · intro a
    exact Prod.ext (hg a) (hg' a)
  · intro Y hY
    refine Prod.ext ?_ ?_
    · refine baseRes_eq_of_forall W hopen (fun a b h => hmono a b h) 0 (fun a => ?_)
      have h1 := congrArg Prod.fst (hY a)
      simp only [extraRes_apply] at h1
      exact h1.trans (hg a).symm
    · refine totRes_eq_of_forall Z W hopen hmono (n - 1) (fun a => ?_)
      have h1 := congrArg Prod.snd (hY a)
      simp only [extraRes_apply] at h1
      exact h1.trans (hg' a).symm

/-- **Separation for the Extra tower.**  Two elements of the Extra term over the union of an
increasing open family which restrict to the same element on every piece are equal. -/
theorem extraRes_eq_of_forall (Z : RealBundle B F ι) (n : ℕ) (W : ℕ → Set B)
    (hopen : ∀ a, IsOpen (W a)) (hmono : ∀ a b, a ≤ b → W a ⊆ W b)
    {x y : ExtraC Z n (⋃ a, W a)}
    (h : ∀ a, extraRes Z n (Set.subset_iUnion W a) x = extraRes Z n (Set.subset_iUnion W a) y) :
    x = y := by
  refine Prod.ext ?_ ?_
  · exact baseRes_eq_of_forall W hopen (fun a b h => hmono a b h) 0
      (fun a => by have := congrArg Prod.fst (h a); simpa only [extraRes_apply] using this)
  · exact totRes_eq_of_forall Z W hopen hmono (n - 1)
      (fun a => by have := congrArg Prod.snd (h a); simpa only [extraRes_apply] using this)

end

end Work.ThomBordism
