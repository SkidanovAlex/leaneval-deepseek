import Mathlib
import Submission.Work.ThomBordism.localThom_iUnion_aux
import Submission.Work.ThomBordism.iUnion.extra
import Submission.Work.ThomBordism.psiClassHyp
import Submission.Work.ThomBordism.chainSetup_psi_aux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Lifting `Extra`-cycles from a piece to a larger piece

The augmented mapping cone of the cochain-level Thom map `ψ` has, one degree below `ConeC 0`, the
**Extra** term `ExtraC Z n W = BaseC W 0 × TotC Z W (n-1)`, with differential

  `extraD (a,b) = (- d a, ψ⁰ a + totDpred b)`.

`Work.ThomBordism.extraKerLift` states that a **cycle** of the Extra term over a piece `S`
(`extraD_S e = 0`) can be **lifted** to a cycle over any larger piece `W ⊇ S` restricting to `e`,
provided two pieces of information over `S` are available:

* `h0` — injectivity of the local Thom map in degree `0` over `S` (`ψ⁰` injective);
* `hlow` — `PieceCoh Z S (n-1) = 0` (the degree `n-1` vanishing of the Thom pair over `S`).

Both hold for the pieces occurring in the union/limit step
(`Work.ThomBordism.localThom_iUnion_of_fibreGenerator`), where `h0` comes from the local Thom
property of the pieces and `hlow` from `n = finrank ℝ F`
(`Work.Thom.subsingleton_PieceCoh_of_lt_finrank`).

## The proof

Write `e = (a, b)` with `a ∈ C⁰(S)`, `b ∈ C^{n-1}(X|_S, A)` (cochain degree `n-1`).

1. `extraD e = 0` says `d a = 0` and `ψ⁰ a + d b = 0` (`d b` = `totDpred b`, the differential
   `(n-1, n)` of the total complex).
2. Passing to cohomology: `[ψ⁰ a] = 0` because `d b` is a coboundary, and `[ψ⁰ a] = δ⁰([a])` by
   `psiClassHyp`.  Hence `h0` forces `[a] = 0`, and since the cochain complex starts in degree `0`,
   `a = 0`.
3. Then `d b = 0`, i.e. `b` is a cocycle in degree `n-1`; by `hlow` its class vanishes, so
   `b = d β` is a coboundary over `S`.
4. Lift `β` to `W` (restriction of cochains is surjective) and set `b' := d β̃`.  Then `b'` is a
   cocycle over `W` (`d² = 0`) restricting to `b` (naturality of the restriction), so
   `r := (0, b')` has `extraD_W r = 0` and `extraRes r = (0, b) = e`.

The two index bookkeeping lemmas are `cochain_homologyπ_eq_zero_iff_prev` (a cycle of vanishing
class is the differential of a cochain in degree `(ComplexShape.up ℕ).prev`, uniformly for
`j = 0`, where the statement says `z = 0`) and `totDpred_eq_relDiffLM` (the differential
`(n-1, 0+n)` is the consecutive differential `(n-1, (n-1)+1)`, transported).
-/

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism.iUnion

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## Two pieces of index/dictionary bookkeeping -/

/-- **A cycle of vanishing class is the differential of a cochain one degree below.**  For a
cochain complex indexed by `ℕ`, a cycle `z` in degree `j` has vanishing class iff it is
`d (prev j) j` of some cochain.  (For `j = 0` one has `prev 0 = 0` and `d 0 0 = 0`, so the
statement reads `z = 0`, which is the correct content: there is nothing below degree `0`.) -/
theorem cochain_homologyπ_eq_zero_iff_prev {C : CochainComplex (ModuleCat ℤ) ℕ}
    [∀ i, C.HasHomology i] (j : ℕ) (z : C.cycles j) :
    (C.homologyπ j).hom z = 0 ↔ ∃ w : C.X ((ComplexShape.up ℕ).prev j),
      (C.d ((ComplexShape.up ℕ).prev j) j).hom w = (C.iCycles j).hom z := by
  constructor
  · intro hz
    let S : ShortComplex (ModuleCat ℤ) :=
      ShortComplex.mk (C.toCycles ((ComplexShape.up ℕ).prev j) j) (C.homologyπ j)
        (C.toCycles_comp_homologyπ ((ComplexShape.up ℕ).prev j) j)
    have hS : S.Exact := S.exact_of_g_is_cokernel
      (C.homologyIsCokernel ((ComplexShape.up ℕ).prev j) j rfl)
    have hrk : (C.toCycles ((ComplexShape.up ℕ).prev j) j).hom.range
        = (C.homologyπ j).hom.ker := ShortComplex.Exact.moduleCat_range_eq_ker hS
    have hz' : z ∈ (C.homologyπ j).hom.ker := by
      rw [LinearMap.mem_ker]
      exact hz
    rw [← hrk] at hz'
    obtain ⟨w, hw⟩ := hz'
    refine ⟨w, ?_⟩
    have h3 := congrArg
      (fun (g : C.X ((ComplexShape.up ℕ).prev j) ⟶ C.X j) => g.hom w)
      (HomologicalComplex.toCycles_i C ((ComplexShape.up ℕ).prev j) j)
    rw [ModuleCat.hom_comp] at h3
    rw [← h3]
    change (C.iCycles j).hom
      ((ConcreteCategory.hom (C.toCycles ((ComplexShape.up ℕ).prev j) j)) w) = _
    rw [hw]
  · rintro ⟨w, hw⟩
    have h1 : C.toCycles ((ComplexShape.up ℕ).prev j) j w = z := by
      apply Work.Cohomology.iCycles_injective_K C j
      rw [iCycles_toCycles' (C := C) ((ComplexShape.up ℕ).prev j) j w, hw]
    rw [← h1]
    exact cochain_homologyπ_toCycles_eq_zero ((ComplexShape.up ℕ).prev j) j w

/-- **The degree-zero base dictionary.**  A degree-`0` singular cocycle with vanishing cohomology
class is zero: `H⁰` of the singular cochain complex is its group of `0`-cocycles, since there is
nothing in degree `-1`. -/
theorem baseClass_zero_eq_zero (W : Set B) (a : BaseC W 0)
    (ha : cochainDiff ℤ (baseSSet W) a = 0) :
    cohomologyClassOf ℤ (baseSSet W) a ha = 0 → a = 0 := by
  intro h
  have hz : (SSetCochainComplex ℤ (baseSSet W)).homologyπ 0
      (cocycleOf ℤ (baseSSet W) a ha) = 0 := h
  obtain ⟨w, hw⟩ := (cochain_homologyπ_eq_zero_iff_prev (C := SSetCochainComplex ℤ (baseSSet W))
    0 (cocycleOf ℤ (baseSSet W) a ha)).mp hz
  have hd0 : (SSetCochainComplex ℤ (baseSSet W)).d ((ComplexShape.up ℕ).prev 0) 0 = 0 :=
    HomologicalComplex.shape (SSetCochainComplex ℤ (baseSSet W)) ((ComplexShape.up ℕ).prev 0) 0
      (by rw [ComplexShape.up_Rel]; omega)
  have hzero : (HomologicalComplex.iCycles (SSetCochainComplex ℤ (baseSSet W)) 0).hom
      (cocycleOf ℤ (baseSSet W) a ha) = 0 := by
    have h2 := hw.symm
    rw [hd0] at h2
    simpa using h2
  rw [← Work.Cohomology.iCycles_cocycleOf ℤ (baseSSet W) a ha]
  exact hzero

/-- **The `totDpred`/`relDiffLM` transfer.**  The differential `(n-1) → (0+n)` of the total complex
(i.e. `totDpred`) is the consecutive differential `(n-1) → ((n-1)+1)`, transported along the
equality of degrees. -/
theorem totDpred_eq_relDiffLM (Z : RealBundle B F ι) (n : ℕ) (W : Set B)
    {hsh : n - 1 + 1 = 0 + n} (x : TotC Z W (n - 1)) :
    totDpred Z n W x
      = hsh ▸ (relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (n - 1) x) := by
  show ((TotComplex Z W).d (n - 1) (0 + n)).hom x = _
  have hof : ((TotComplex Z W).d (n - 1) (0 + n))
      = (ModuleCat.ofHom (relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (n - 1))) ≫
        eqToHom (congrArg (fun t => (TotComplex Z W).X t) hsh) := by
    dsimp only [TotComplex, relComplex, CochainComplex.of.d]
    rw [dif_pos hsh]
    rfl
  rw [hof, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact eqToHom_X_eq_rec (K := TotComplex Z W) hsh
    ((ModuleCat.Hom.hom (ModuleCat.ofHom (relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W))
      (relPiece Z W) (n - 1)))) x)

/-- **A `totDpred`-coboundary has vanishing class.**  The degree-`n` class of `totDpred b` is zero:
it is the differential `(n-1) → n` of `b`. -/
theorem relClass_eq_zero_of_totDpred (Z : RealBundle B F ι) (n : ℕ) (W : Set B)
    (b : TotC Z W (n - 1)) (z : TotC Z W (0 + n))
    (hz : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (0 + n) z = 0)
    (h : z = -totDpred Z n W b) :
    relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz = 0 := by
  have hcycle : relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) z hz
      = ((relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)).toCycles (n - 1) (0 + n))
          (-b) := by
    apply Work.Cohomology.iCycles_injective_K
    rw [Work.Cohomology.iCycles_relCocycleOf, iCycles_toCycles']
    rw [h]
    show -totDpred Z n W b
      = ((relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)).d (n - 1) (0 + n)).hom (-b)
    rw [map_neg]
    rfl
  rw [relClassOf_eq_homologyπ' Z W (0 + n) z hz, hcycle]
  exact cochain_homologyπ_toCycles_eq_zero
    (C := relComplex ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W)) (n - 1) (0 + n) (-b)

/-! ## The lift -/

theorem extraKerLift {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
    (U : Set B) (τ : Work.Thom.PieceCoh Z U n) {S W : Set B} (hSW : S ⊆ W) (hS : S ⊆ U)
    (hW : W ⊆ U)
    (h0 : Function.Injective (Work.Thom.localThomMap Z n S
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' U) (Z.proj ⁻¹' S) (Set.preimage_mono hS) n).hom τ) 0))
    (hlow : Subsingleton (Work.Thom.PieceCoh Z S (n - 1)))
    (e : Work.ThomBordism.ExtraC Z n S) (he : Work.ThomBordism.extraD Z n U τ S hS e = 0) :
    ∃ r : Work.ThomBordism.ExtraC Z n W,
      Work.ThomBordism.extraD Z n U τ W hW r = 0 ∧
      Work.ThomBordism.extraRes Z n hSW r = e := by
  obtain ⟨a, b⟩ := e
  -- ## Step 1: the two components of `extraD e = 0`
  have he1 : -(cochainDiffLM ℤ (baseSSet S) 0 a) = (0 : BaseC S (0 + 1)) := by
    have h := congrArg Prod.fst he
    simpa only [extraD, prod_zero_fst] using h
  have he2 : psiAbsLM Z n U τ S hS 0 a + totDpred Z n S b = 0 := by
    have h := congrArg Prod.snd he
    simpa only [extraD, prod_zero_snd] using h
  have ha : cochainDiff ℤ (baseSSet S) a = 0 := by
    have h : cochainDiffLM ℤ (baseSSet S) 0 a = 0 := by simpa using he1
    simpa using h
  -- ## Step 2: `d a = 0` makes `psiAbs a` a cocycle
  have hcyc : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' S)) (relPiece Z S) (0 + n)
      (psiAbs Z n U τ S hS 0 a) = 0 := by
    have h := psiAbs_relDiff Z n U τ S hS 0 a
    rw [ha] at h
    rw [show psiAbs Z n U τ S hS (0 + 1) (0 : BaseC S (0 + 1)) = 0 from
      map_zero (psiAbsLM Z n U τ S hS (0 + 1))] at h
    exact h.trans (totC_cast_zero Z S (Nat.add_right_comm 0 1 n))
  -- ## Step 3: `[psiAbs a] = 0`, hence `[a] = 0` by injectivity, hence `a = 0`
  have hcls : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' S)) (relPiece Z S)
      (psiAbs Z n U τ S hS 0 a) hcyc = 0 := by
    refine relClass_eq_zero_of_totDpred Z n S b (psiAbs Z n U τ S hS 0 a) hcyc ?_
    exact eq_neg_of_add_eq_zero_left he2
  have hψ := psiClassHyp Z n U τ S hS 0 a ha hcyc
  have hltm : Work.Thom.localThomMap Z n S
      ((pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' S) (Set.preimage_mono hS) n).hom τ) 0
      (cohomologyClassOf ℤ (baseSSet S) a ha) = 0 := by
    rw [← hψ]
    exact hcls
  have hc0 : cohomologyClassOf ℤ (baseSSet S) a ha = 0 :=
    h0 (by rw [hltm, map_zero])
  have ha0 : a = 0 := baseClass_zero_eq_zero S a ha hc0
  -- ## Step 4: `b` is a cocycle in degree `n-1` over `S`, of vanishing class
  have hb1 : totDpred Z n S b = 0 := by
    have h := he2
    rw [show psiAbsLM Z n U τ S hS 0 a = (0 : TotC Z S (0 + n)) from by rw [ha0, map_zero]] at h
    simpa using h
  have hsh : n - 1 + 1 = 0 + n := by omega
  have hbcoc : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' S)) (relPiece Z S) (n - 1) b = 0 := by
    have h := totDpred_eq_relDiffLM Z n S (hsh := hsh) b
    rw [hb1] at h
    exact totC_cast_eq_zero Z S hsh _ h.symm
  have hbcls : relClassOf ℤ (TopCat.of ↥(Z.proj ⁻¹' S)) (relPiece Z S) b hbcoc = 0 := by
    haveI : Subsingleton (relCohomology ℤ (TopCat.of ↥(Z.proj ⁻¹' S)) (relPiece Z S)
        (n - 1)) := hlow
    exact Subsingleton.elim _ _
  obtain ⟨β, hβ⟩ := (cochain_homologyπ_eq_zero_iff_prev (n - 1)
      (relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' S)) (relPiece Z S) b hbcoc)).mp hbcls
  rw [Work.Cohomology.iCycles_relCocycleOf ℤ (TopCat.of ↥(Z.proj ⁻¹' S)) (relPiece Z S) b
    hbcoc] at hβ
  -- ## Step 5: lift `β` to `W` and take `b' = d β̃`
  obtain ⟨βW, hβW⟩ := rcResLM_surjective (Work.Thom.zeroComplement Z) (Set.preimage_mono hSW)
    ((ComplexShape.up ℕ).prev (n - 1)) β
  let b' : TotC Z W (n - 1) := ((TotComplex Z W).d ((ComplexShape.up ℕ).prev (n - 1)) (n - 1)).hom βW
  have hresb' : rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono hSW) (n - 1) b' = b := by
    have h := rcResLM_relD Z hSW ((ComplexShape.up ℕ).prev (n - 1)) (n - 1) βW
    rw [hβW] at h
    exact h.trans hβ
  have hrelW : relDiffLM ℤ (TopCat.of ↥(Z.proj ⁻¹' W)) (relPiece Z W) (n - 1) b' = 0 := by
    have hcomp : (((TotComplex Z W).d ((ComplexShape.up ℕ).prev (n - 1)) (n - 1)) ≫
        ((TotComplex Z W).d (n - 1) ((n - 1) + 1))).hom βW = 0 := by
      rw [HomologicalComplex.d_comp_d, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomp
    rw [← relComplex_d_apply Z W (n - 1) b']
    exact hcomp
  have hb'tot : totDpred Z n W b' = 0 := by
    rw [totDpred_eq_relDiffLM Z n W (hsh := hsh) b', hrelW, totC_cast_zero Z W hsh]
  -- ## Step 6: `r = (0, b')` is the answer
  refine ⟨(0, b'), ?_, ?_⟩
  · show (-(cochainDiffLM ℤ (baseSSet W) 0 (0 : BaseC W 0)),
        psiAbsLM Z n U τ W hW 0 (0 : BaseC W 0) + totDpred Z n W b')
      = (0 : ConeC Z n W 0)
    simp only [map_zero, hb'tot, neg_zero, zero_add]
    rfl
  · show (baseRes hSW 0 (0 : BaseC W 0),
        rcResLM (Work.Thom.zeroComplement Z) (Set.preimage_mono hSW) (n - 1) b') = (a, b)
    rw [map_zero, hresb']
    exact Prod.ext ha0.symm rfl

end

end Work.ThomBordism.iUnion
