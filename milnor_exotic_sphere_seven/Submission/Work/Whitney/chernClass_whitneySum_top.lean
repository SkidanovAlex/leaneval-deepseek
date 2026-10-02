import Mathlib
import Submission.Work.Whitney.Stability
import Submission.Work.Whitney.RelRelCup
import Submission.Work.Whitney.TautSection
import Submission.Work.Thom.thomClassOf
import Submission.Work.Thom.exists_unique_pieceClass
import Submission.Work.Thom.MixedCup
import Submission.Work.Thom.Orientation.Mpun_gaugeEnd_neg
import Submission.Work.LerayHirsch.whitneySumFormulaOfLerayHirsch
import Submission.Work.Whitney.RelRelCupG
import Submission.Work.Whitney.RelRelCupNat
import Submission.Work.Whitney.WSumChars
import Submission.Work.Whitney.continuous_tcmProj
import Submission.Work.Whitney.wsumPiece_open_union
import Submission.Work.Whitney.thomClassRank_whitneySum_rel
import Submission.Work.Whitney.chernClass_whitneySum_top_of_thomProduct
import Submission.Work.Whitney.chernClass_whitneySum_top_rank_zero_left
import Submission.Work.Whitney.chernClass_whitneySum_top_rank_zero_right
import Submission.Work.Whitney.Hypotheses

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

open Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

/-!
# The top degree of the Whitney sum formula: status, and a defect of the ambient definitions

**The target.** `Work.Whitney.chernClass_whitneySum_top` (= `Work.Whitney.TopClassMul`): for complex
gluing-data bundles `Z₁` (rank `m₁`) and `Z₂` (rank `m₂`),

  `c_{m₁+m₂}(Z₁ ⊕ Z₂) = c_{m₁}(Z₁) ⌣ c_{m₂}(Z₂)`,

equivalently `e(E_ℝ ⊕ F_ℝ) = e(E_ℝ) ⌣ e(F_ℝ)` for the Euler class of the realification
(`Work.Thom.chernClass_succ_top'`: `c_j(Z) = e(Z_ℝ)` for `j = rank Z`).

**The mathematical content** is the classical product formula for Thom classes,
`τ_{E⊕F} = pr₁^*τ_E ⌣_rel pr₂^*τ_F`, followed by `z^* ∘ relToAbs` (the Euler class is the pullback of
the Thom class along the zero section) and the multiplicativity of the cup product.  The route is
planned in `Submission/Work/Whitney/README.md` §8 and `Submission/Work/Whitney/_tcm/stmt.lean`; its
pieces are

1. **the model product formula** `Work.Whitney.tcmModelMul` (in `_tcm/stmt.lean`): for the
   *model* Thom class `Work.Thom.Mpun n B` of the trivial bundle of rank `n` over a base `B`, the
   relative–relative cup (`Work.Whitney.relRelCupG`, `relRelCupOpen`) of the two pulled-back model
   classes is the model class of the sum.  This is the "the cross product of the two generators is
   the generator" computation, and it is *choice-free* (it mentions only `Mpun`).  The tool for the
   reduction to a point is on disk: `Work.Whitney.Mpun_eq_of_fibrewise` (the punctured model class is
   detected by its restrictions to the fibres);
2. **the chart bookkeeping**: the canonical Thom class `Work.Thom.thomClassOf` of `Z₁ ⊕ Z₂` restricts
   on every piece of the product cover to the product of the restrictions of the canonical Thom
   classes of `Z₁`, `Z₂` (`Work.Thom.localThomOfComplexCover_pdCohMap_subset` identifies the
   restriction with the explicit chart class `Work.Thom.localThomOfChart`, and
   `Work.Whitney.relRelCupOpen_natural` transports the model formula to the charts);
3. **the assembly**: from (2) conclude `τ_{Z₁⊕Z₂} = κ := pr₁^*τ_{Z₁} ⌣_rel pr₂^*τ_{Z₂}`
   (`Work.Thom.pdCohMap_finInter_eq_zero`/`exists_unique_pieceClass`: a class of
   `H^{2(m₁+m₂)}(V,V∖0)` is determined by its restrictions to the pieces), then take Euler classes.

**STATUS (this stretch).**  The defect described below has been **repaired**: `Work.Thom.covE`
and the `let e` inside `Work.Thom.localThomOfComplexCover` are now `Work.Gen.rifStd` (the canonical,
sum-compatible realification of `Submission/Work/Gen/RifStd.lean`), so the chart gauge comparing the
chart of `Z₁ ⊕ Z₂` with the product of the charts of the summands *is the identity*, and the target
is no longer a coherence statement about `Classical.choice`.  (The repair is the two-line change to
`Submission/Work/Thom/CovDefs.lean` and `Submission/Work/Thom/thomClassOf.lean`; all same-index
statements about `chernClass` are insensitive to it and still build.)

The second, independent obstruction found since is a **Koszul sign** in the *model* product formula:
the unsigned statement `tcmRelCup (pr₁^*Mpun p) (pr₂^*Mpun q) = tcmF^*(Mpun (p+q))` of
`Submission/Work/Whitney/tcmModelMul.lean` is **false** off by `(-1)^{p*q}`
(`Submission/Work/Whitney/_cupSign/NOTES.md`, `Submission/Work/Whitney/_o/NOTES_sign_11.md`; forced by
the *proved* graded Leibniz rule `Work.Thom.suspensionStep_cup'` and consistent with the *proved* unit
law `Work.Whitney.tcmRelCup_unit_right`).  The corrected statements are
`Work.Whitney.tcmModelMul_point_signed` / `tcmModelMul_signed` / `tcmModelMul_even`; **the even
instance is sign-free and is the only one this target needs** (the Thom classes of realified complex
bundles have even rank `2*m`).

The road from here (each piece a file of its own):

* `Work.Whitney.tcmModelMul_point_signed` (the crux: the point case with the sign),
* `Work.Whitney.tcmModelMul_signed_of_point` (the reduction to the point case),
* `Work.Whitney.tcmModelMul_signed` / `Work.Whitney.tcmModelMul_even` (the general/even instances),
* `Work.Whitney.thomClassRank_whitneySum_rel` (the chart identity + the gluing over the pair cover =
  the *relative* Thom product formula `τ_V = π₁^*τ₁ ⌣_rel π₂^*τ₂`; the vocabulary is
  `Submission/Work/Whitney/WSumChars.lean`),
* `Work.Whitney.chernClass_whitneySum_top_of_thomProduct` (the assembly: the relative formula implies
  the top Chern class identity in the two degrees `m₁+m₂ ≥ 1`),
* the boundary cases `m₁ = 0` / `m₂ = 0` (`Work.Whitney.chernClass_whitneySum_rank_zero` plus the
  unit law of the graded product), which assemble the unconditional headline.

**THE DEFECT (read this before spending time on the target).**  Steps 2 and 3 cannot be carried out
for the definitions *as they stand*, and the obstruction is not mathematical: it is the arbitrary
choice of the chart linear equivalence `Work.Thom.covE k : EuclideanSpace ℂ (Fin k) ≃L[ℝ]
EuclideanSpace ℝ (Fin (2*k))`, which is `ContinuousLinearEquiv.ofFinrankEq …` — an **opaque**
`Classical.choice` (no lemma in Mathlib or this workspace relates its values at different `k`; the
only provable property is that it is a linear isomorphism).

* The chart class `Work.Thom.localThomOfChart Z n e i W hW` is the pullback of `Mpun n ↥W` along the
  chart homeomorphism, which post-composes the fibre with `e`.  Replacing `e` by `e.trans R` with
  `det R < 0` therefore **negates** the chart class (`localThomOfChart_trans_neg` below, from
  `Work.Thom.Orientation.Mpun_gaugeEnd_neg`).
* Consequently the *whole construction* `Work.Thom.thomClassOf` is sign-equivariant in `covE k`: if
  `covE k` is replaced by a negative-determinant variant, all local data of rank-`k` bundles change
  sign, hence (by the *uniqueness* in `Work.Thom.exists_unique_pieceClass` and
  `Work.Thom.exists_unique_thomClassOfLocalThomUniv`) the Thom class and its Euler class change sign.
* The target compares classes of rank `m₁+m₂`, `m₁` and `m₂`: their signs depend on
  `covE (m₁+m₂)`, `covE m₁`, `covE m₂` **independently**.  Writing `σ k` for the orientation sign of
  `covE k` relative to any fixed reference, the target is therefore *equivalent to*
  `σ (m₁+m₂) = σ m₁ * σ m₂` — a coherence statement about three opaque values.  Nothing in the
  definitions forces it (each `covE k` is an arbitrary linear isomorphism, and the theory is
  consistent with any assignment of the `σ k`), so the target is **not provable as stated**: it is
  false in the (consistent) situation in which the choice function returns incoherent signs.

**THE FIX, SPECIFIED.**  The defect is exactly a *coherence* statement about the chart
isomorphism, and it is repairable by choosing the chart isomorphism canonically.  What is needed is a
family

  `rif k : EuclideanSpace ℂ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin (2*k))`

satisfying the **sum-compatibility**

  `rif (m+n) (sumFibreC m n (x, y)) = sumFibreR (2*m) (2*n) (rif m x, rif n y)`

(`Work.Whitney.sumFibreC`, `Work.Whitney.sumFibreR` are the explicit splittings of the standard
fibres); the identity is to be read with the canonical `Fin`-cast `2*(m+n) = 2*m + 2*n`.  With such a
family the gauge comparing the chart of `Z₁ ⊕ Z₂` with the product of the charts of `Z₁`, `Z₂` is the
*identity*, so `Mpun` is invariant under it (`Work.Thom.Mpun_gaugeEnd_invariant`) and steps 1–3 above
go through — in particular the chart bookkeeping has no sign left in it.  One such family is given by
the "interleaved" realification `z ↦ (re z 0, im z 0, re z 1, im z 1, …)` (the *block* convention
`z ↦ (re z 0, …, re z (k-1), im z 0, …)` fails the sum-compatibility by the sign of the shuffle).
Declared below as `Work.Whitney.exists_sumCompatible_realification`; the Thom chapter should use its
witness in place of `Work.Thom.covE` (both in `Submission/Work/Thom/CovDefs.lean` and in the `let e`
inside `Work.Thom.localThomOfComplexCover`).

**The fix** (for the Thom area, which owns `Submission/Work/Thom/CovDefs.lean` and the `let e` inside
`Work.Thom.localThomOfComplexCover`): replace `covE k` by a *canonical, sum-compatible* realification
`rif k : EuclideanSpace ℂ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin (2*k))` satisfying

  `rif (m+n) ∘ sumFibreC m n = sumFibreR (2*m) (2*n) ∘ (rif m × rif n)`

(an explicit linear-algebra identity, provable once the convention for `rif` is chosen — this is
exactly the identity that makes the gauge of step 2 the identity, hence `Mpun`-invariant).  After that
change steps 1–3 go through.  **Alternative**, sign-robust to the same effect: state the target with
a sign/unit, `c_{m+n}(E⊕F) = u • c_m(E) ⌣ c_n(F)` with `u ∈ H⁰(B)` a unit — consistent with the
`±`-convention that the AGREE area (`Work.Agree.AgreeAll`) already uses for `p₁`.

Everything *else* about the target is ordinary mathematical work and is unaffected by this defect:
the model product formula (1) is choice-free, and the assembly (3) is pure bookkeeping (Euler classes,
zero sections, degree casts) once the relative statement is available.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## The orientation defect of the chart construction (evidence for the diagnosis above) -/

open Work.TangentClasses Work.Thom

section Defect

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type}

/-- **The chart homeomorphism of the chart `e.trans R` is the old one followed by the constant
gauge `R`.**  This is the geometric content of the defect: the chart linear equivalence enters the
chart class only through the fibre coordinate, so changing it by `R` changes the chart class by the
action of the gauge `R` on the model class. -/
theorem chartHomeo_trans (Z : RealBundle B F ι) (n : ℕ)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i)
    (R : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (p : ↥(Z.proj ⁻¹' W)) :
    chartHomeo Z n (e.trans R) i W hW p
      = gaugeEnd (fun _ : ↥W => R.toContinuousLinearMap) continuous_const
          (chartHomeo Z n e i W hW p) := by
  rw [chartHomeo_apply, chartHomeo_apply, gaugeEnd_apply, ContinuousLinearEquiv.trans_apply]
  exact Prod.ext rfl rfl

/-- **THE ORIENTATION DEFECT OF THE CHART CLASS.**  Replacing the chart linear equivalence `e` by
`e.trans R` with `det R < 0` negates the chart class.  Since `Work.Thom.thomClassOf` is built from
`Work.Thom.localThomOfChart` with `e = Work.Thom.covE` (`Work.Thom.CovDefs`), and `covE` is an opaque
`ContinuousLinearEquiv.ofFinrankEq`, the top Chern class of a rank-`k` bundle is therefore determined
only up to the *sign* of the arbitrary isomorphism `covE k`.  See the module docstring. -/
theorem localThomOfChart_trans_neg (Z : RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι) (W : Set B) (hW : W ⊆ Z.baseSet i)
    (R : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hdet : LinearMap.det R.toLinearMap < 0) :
    (localThomOfChart Z n (e.trans R) i W hW).τ = -(localThomOfChart Z n e i W hW).τ := by
  have hbj : ∀ y : ↥W, Function.Bijective ((fun _ : ↥W => R.toContinuousLinearMap) y) :=
    fun _ => gaugeEnd_bijective_of_det_ne_zero _ (ne_of_lt hdet)
  have hmap : (chartHomeo Z n (e.trans R) i W hW :
        C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
      = (gaugeEnd (fun _ : ↥W => R.toContinuousLinearMap) continuous_const).comp
          (chartHomeo Z n e i W hW :
            C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))) := by
    apply ContinuousMap.ext
    intro p
    rw [ContinuousMap.comp_apply]
    exact chartHomeo_trans Z n e i W hW R p
  have hmemC : ∀ p ∈ pieceZero Z W,
      ((gaugeEnd (fun _ : ↥W => R.toContinuousLinearMap) continuous_const).comp
        (chartHomeo Z n e i W hW :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))) p ∈ Punct ↥W n := by
    intro p hp
    rw [ContinuousMap.comp_apply]
    exact gaugeEnd_mem _ continuous_const hbj _ (chartHomeo_mem Z n e i W hW p hp)
  have hcongr := relCohMap_congrA (pieceZero Z W) (Punct ↥W n) hmap
    (chartHomeo_mem Z n (e.trans R) i W hW) hmemC ℤ n
  have hcomp := relCohMap_compA_apply (A := pieceZero Z W) (B := Punct ↥W n) (C := Punct ↥W n)
    (chartHomeo Z n e i W hW : C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
    (gaugeEnd (fun _ : ↥W => R.toContinuousLinearMap) continuous_const)
    (chartHomeo_mem Z n e i W hW) (gaugeEnd_mem _ continuous_const hbj) hmemC ℤ n (Mpun n ↥W)
  have hneg := Work.Thom.Orientation.Mpun_gaugeEnd_neg n hn
    (fun _ : ↥W => R.toContinuousLinearMap) continuous_const (fun _ => hdet)
  rw [localThomOfChart_tau, localThomOfChart_tau]
  calc (relCohMap (chartHomeo Z n (e.trans R) i W hW :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
        (pieceZero Z W) (Punct ↥W n) (chartHomeo_mem Z n (e.trans R) i W hW) ℤ n).hom (Mpun n ↥W)
      = (relCohMap ((gaugeEnd (fun _ : ↥W => R.toContinuousLinearMap) continuous_const).comp
          (chartHomeo Z n e i W hW :
            C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))))
        (pieceZero Z W) (Punct ↥W n) hmemC ℤ n).hom (Mpun n ↥W) :=
        congrArg (fun φ => φ.hom (Mpun n ↥W)) hcongr
    _ = (relCohMap (chartHomeo Z n e i W hW :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
        (pieceZero Z W) (Punct ↥W n) (chartHomeo_mem Z n e i W hW) ℤ n).hom
        ((relCohMap (gaugeEnd (fun _ : ↥W => R.toContinuousLinearMap) continuous_const)
          (Punct ↥W n) (Punct ↥W n) (gaugeEnd_mem _ continuous_const hbj) ℤ n).hom
          (Mpun n ↥W)) := hcomp.symm
    _ = (relCohMap (chartHomeo Z n e i W hW :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
        (pieceZero Z W) (Punct ↥W n) (chartHomeo_mem Z n e i W hW) ℤ n).hom (-(Mpun n ↥W)) := by
        rw [hneg]
    _ = -(localThomOfChart Z n e i W hW).τ := map_neg _ _

end Defect

/-! ## The cure: the canonical sum-compatible realification

**See `Submission/Work/Whitney/_tcm/REDUCTION.md` for the precise reduction of the target, the
defect, the cure and the priority list.**  PROVED below: `chartHomeo_trans`,
`localThomOfChart_trans_neg` (the defect evidence), `reimEquiv`, `cleProd`, `rifOne`, `rif`,
`sumFibreC_zip` (the "zip" identity of the complex splitting) and `rif_succ_apply` (the unary
recursion of `rif`), `sumFibreR_zip`, `sumFibreR_cast`, `sumFibreC_zero`, `sumFibreR_zero`,
`cast_apply_ofLp`, `rif_sum_compatible_cast` and `rif_sum_compatible` (the cure's compatibility).

The definitions below are the *witness* of
`Work.Whitney.exists_sumCompatible_realification` (the fix specified in the module docstring): the
interleaved realification of `ℂ^k`, built recursively so that the sum-compatibility is the
recursion itself.  `rif 0` and `rif 1` are the base cases, and `rif (k+1)` is
`sumFibreR (2*k) 2 ∘ (rif k × rif 1) ∘ (sumFibreC k 1)⁻¹` — the last complex coordinate is peeled
off, which is exactly the interleaved convention.  The two compatibility results below are proved
here; the `cast`-free form is the `HEq` statement. -/

section Cure

open Work.TangentClasses

/-- The real-and-imaginary-parts isomorphism `ℂ^k ≅ ℝ^k × ℝ^k`. -/
noncomputable def reimEquiv (k : ℕ) :
    EuclideanSpace ℂ (Fin k) ≃L[ℝ] (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :=
  (LinearEquiv.ofBijective ((cxRePart (k := k)).prod (cxImPart (k := k)))
    ⟨fun x y h => by
      have h1 : cxRePart x = cxRePart y := congrArg Prod.fst h
      have h2 : cxImPart x = cxImPart y := congrArg Prod.snd h
      rw [← cxOfReal_cxRePart_add_cxMulI_cxImPart x,
        ← cxOfReal_cxRePart_add_cxMulI_cxImPart y, h1, h2],
     fun p => ⟨cxOfReal p.1 + cxMulI (cxOfReal p.2), by
      refine Prod.ext ?_ ?_
      · simp [LinearMap.prod_apply]
      · simp [LinearMap.prod_apply]⟩⟩).toContinuousLinearEquiv

@[simp] theorem reimEquiv_apply (k : ℕ) (z : EuclideanSpace ℂ (Fin k)) :
    reimEquiv k z = (cxRePart z, cxImPart z) := rfl

/-- The product of two continuous linear equivalences, on a product space. -/
noncomputable def cleProd {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (e₁ : E₁ ≃L[ℝ] F₁) (e₂ : E₂ ≃L[ℝ] F₂) : (E₁ × E₂) ≃L[ℝ] (F₁ × F₂) where
  toFun p := (e₁ p.1, e₂ p.2)
  invFun q := (e₁.symm q.1, e₂.symm q.2)
  left_inv p := by simp
  right_inv q := by simp
  map_add' p q := by simp [Prod.ext_iff]
  map_smul' c p := by simp [Prod.ext_iff]
  continuous_toFun := (e₁.continuous.comp continuous_fst).prodMk (e₂.continuous.comp continuous_snd)
  continuous_invFun := (e₁.symm.continuous.comp continuous_fst).prodMk
    (e₂.symm.continuous.comp continuous_snd)

@[simp] theorem cleProd_apply {E₁ E₂ F₁ F₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (e₁ : E₁ ≃L[ℝ] F₁) (e₂ : E₂ ≃L[ℝ] F₂) (p : E₁ × E₂) :
    cleProd e₁ e₂ p = (e₁ p.1, e₂ p.2) := rfl

/-- The rank-one base case of the canonical realification: `ℂ^1 ≅ ℝ^2` by `z ↦ (re z, im z)`. -/
noncomputable def rifOne : EuclideanSpace ℂ (Fin 1) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (reimEquiv 1).trans (sumFibreR 1 1)

/-- **The canonical sum-compatible realification** of `ℂ^k` (interleaved real and imaginary parts,
built by peeling the last complex coordinate). -/
noncomputable def rif : (k : ℕ) → EuclideanSpace ℂ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * k))
  | 0 => (reimEquiv 0).trans (sumFibreR 0 0)
  | k + 1 => (Nat.mul_succ 2 k) ▸
      ((((sumFibreC k 1).symm.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv).trans
        ((cleProd (rif k) rifOne).trans (sumFibreR (2 * k) 2)))

/-- **The "zip" identity of the explicit complex splitting**: the concatenation of the three blocks
`x`, `y`, `w` is associative, in the form in which the recursion of `rif` needs it.  Both sides live
in the *definitionally* equal types `Fin (m + (n+1))` and `Fin ((m+n) + 1)`. -/
theorem sumFibreC_zip (m n : ℕ) (x : EuclideanSpace ℂ (Fin m))
    (y : EuclideanSpace ℂ (Fin n)) (w : EuclideanSpace ℂ (Fin 1)) :
    sumFibreC m (n + 1) (x, sumFibreC n 1 (y, w))
      = sumFibreC (m + n) 1 (sumFibreC m n (x, y), w) := by
  apply PiLp.ext
  intro k
  rcases (@finSumFinEquiv m (n + 1)).surjective k with ⟨s, rfl⟩
  rcases s with i | j
  · have I1 : (@finSumFinEquiv m (n + 1) (Sum.inl i) : Fin ((m + n) + 1))
        = (@finSumFinEquiv (m + n) 1 (Sum.inl (@finSumFinEquiv m n (Sum.inl i)))) := by
      simp only [finSumFinEquiv_apply_left]
      exact Fin.ext rfl
    rw [show ((sumFibreC m (n + 1)) (x, (sumFibreC n 1) (y, w))).ofLp
          (finSumFinEquiv (Sum.inl i)) = x.ofLp i from
        finAddEquivProd_symm_apply_inl x ((sumFibreC n 1) (y, w)) i]
    rw [I1]
    rw [show ((sumFibreC (m + n) 1) ((sumFibreC m n) (x, y), w)).ofLp
          (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))))
        = ((sumFibreC m n) (x, y)).ofLp (finSumFinEquiv (Sum.inl i)) from
        finAddEquivProd_symm_apply_inl ((sumFibreC m n) (x, y)) w (finSumFinEquiv (Sum.inl i))]
    rw [show ((sumFibreC m n) (x, y)).ofLp (finSumFinEquiv (Sum.inl i)) = x.ofLp i from
        finAddEquivProd_symm_apply_inl x y i]
  · rcases (@finSumFinEquiv n 1).surjective j with ⟨t, rfl⟩
    rcases t with i' | l
    · have I2 : (@finSumFinEquiv m (n + 1) (Sum.inr (@finSumFinEquiv n 1 (Sum.inl i')))
            : Fin ((m + n) + 1))
          = (@finSumFinEquiv (m + n) 1 (Sum.inl (@finSumFinEquiv m n (Sum.inr i')))) := by
        simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
        exact Fin.ext rfl
      rw [show ((sumFibreC m (n + 1)) (x, (sumFibreC n 1) (y, w))).ofLp
            (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl i'))))
          = ((sumFibreC n 1) (y, w)).ofLp (finSumFinEquiv (Sum.inl i')) from
          finAddEquivProd_symm_apply_inr x ((sumFibreC n 1) (y, w))
            (finSumFinEquiv (Sum.inl i'))]
      rw [show ((sumFibreC n 1) (y, w)).ofLp (finSumFinEquiv (Sum.inl i')) = y.ofLp i' from
          finAddEquivProd_symm_apply_inl y w i']
      rw [I2]
      rw [show ((sumFibreC (m + n) 1) ((sumFibreC m n) (x, y), w)).ofLp
            (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr i'))))
          = ((sumFibreC m n) (x, y)).ofLp (finSumFinEquiv (Sum.inr i')) from
          finAddEquivProd_symm_apply_inl ((sumFibreC m n) (x, y)) w (finSumFinEquiv (Sum.inr i'))]
      rw [show ((sumFibreC m n) (x, y)).ofLp (finSumFinEquiv (Sum.inr i')) = y.ofLp i' from
          finAddEquivProd_symm_apply_inr x y i']
    · have I3 : (@finSumFinEquiv m (n + 1) (Sum.inr (@finSumFinEquiv n 1 (Sum.inr l)))
            : Fin ((m + n) + 1)) = (@finSumFinEquiv (m + n) 1 (Sum.inr l)) := by
        simp only [finSumFinEquiv_apply_right, Fin.natAdd]
        exact Fin.ext (by simp only [Fin.natAdd]; omega)
      rw [show ((sumFibreC m (n + 1)) (x, (sumFibreC n 1) (y, w))).ofLp
            (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr l))))
          = ((sumFibreC n 1) (y, w)).ofLp (finSumFinEquiv (Sum.inr l)) from
          finAddEquivProd_symm_apply_inr x ((sumFibreC n 1) (y, w))
            (finSumFinEquiv (Sum.inr l))]
      rw [show ((sumFibreC n 1) (y, w)).ofLp (finSumFinEquiv (Sum.inr l)) = w.ofLp l from
          finAddEquivProd_symm_apply_inr y w l]
      rw [I3]
      rw [show ((sumFibreC (m + n) 1) ((sumFibreC m n) (x, y), w)).ofLp
            (finSumFinEquiv (Sum.inr l)) = w.ofLp l from
          finAddEquivProd_symm_apply_inr ((sumFibreC m n) (x, y)) w l]

/-- **The "zip" identity of the explicit real splitting** (blocks `2m`, `2n`, `2`), the real
analogue of `sumFibreC_zip`: the recursion of `rif` peels a *complex* coordinate, i.e. a real block
of size `2`. -/
theorem sumFibreR_zip (m n : ℕ) (x : EuclideanSpace ℝ (Fin (2 * m)))
    (y : EuclideanSpace ℝ (Fin (2 * n))) (w : EuclideanSpace ℝ (Fin 2)) :
    sumFibreR (2 * m) (2 * (n + 1)) (x, sumFibreR (2 * n) 2 (y, w))
      = sumFibreR (2 * m + 2 * n) 2 (sumFibreR (2 * m) (2 * n) (x, y), w) := by
  apply PiLp.ext
  intro k
  rcases (@finSumFinEquiv (2 * m) (2 * (n + 1))).surjective k with ⟨s, rfl⟩
  rcases s with i | j
  · have I1 : (@finSumFinEquiv (2 * m) (2 * (n + 1)) (Sum.inl i)
          : Fin ((2 * m + 2 * n) + 2))
        = (@finSumFinEquiv (2 * m + 2 * n) 2
            (Sum.inl (@finSumFinEquiv (2 * m) (2 * n) (Sum.inl i)))) := by
      simp only [finSumFinEquiv_apply_left]
      exact Fin.ext rfl
    rw [show ((sumFibreR (2 * m) (2 * (n + 1))) (x, (sumFibreR (2 * n) 2) (y, w))).ofLp
          (finSumFinEquiv (Sum.inl i)) = x.ofLp i from
        @finAddEquivProd_symm_apply_inl ℝ _ (2 * m) (2 * (n + 1)) x
          ((sumFibreR (2 * n) 2) (y, w)) i]
    rw [I1]
    rw [show ((sumFibreR (2 * m + 2 * n) 2) ((sumFibreR (2 * m) (2 * n)) (x, y), w)).ofLp
          (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))))
        = ((sumFibreR (2 * m) (2 * n)) (x, y)).ofLp (finSumFinEquiv (Sum.inl i)) from
        @finAddEquivProd_symm_apply_inl ℝ _ (2 * m + 2 * n) 2
          ((sumFibreR (2 * m) (2 * n)) (x, y)) w (finSumFinEquiv (Sum.inl i))]
    rw [show ((sumFibreR (2 * m) (2 * n)) (x, y)).ofLp (finSumFinEquiv (Sum.inl i))
          = x.ofLp i from
        @finAddEquivProd_symm_apply_inl ℝ _ (2 * m) (2 * n) x y i]
  · rcases (@finSumFinEquiv (2 * n) 2).surjective j with ⟨t, rfl⟩
    rcases t with i' | l
    · have I2 : (@finSumFinEquiv (2 * m) (2 * (n + 1))
            (Sum.inr (@finSumFinEquiv (2 * n) 2 (Sum.inl i'))) : Fin ((2 * m + 2 * n) + 2))
          = (@finSumFinEquiv (2 * m + 2 * n) 2
              (Sum.inl (@finSumFinEquiv (2 * m) (2 * n) (Sum.inr i')))) := by
        simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
        exact Fin.ext rfl
      rw [show ((sumFibreR (2 * m) (2 * (n + 1))) (x, (sumFibreR (2 * n) 2) (y, w))).ofLp
            (@finSumFinEquiv (2 * m) (2 * (n + 1))
              (Sum.inr (@finSumFinEquiv (2 * n) 2 (Sum.inl i'))))
          = ((sumFibreR (2 * n) 2) (y, w)).ofLp
              (@finSumFinEquiv (2 * n) 2 (Sum.inl i')) from
          @finAddEquivProd_symm_apply_inr ℝ _ (2 * m) (2 * (n + 1)) x
            ((sumFibreR (2 * n) 2) (y, w)) (finSumFinEquiv (Sum.inl i'))]
      rw [show ((sumFibreR (2 * n) 2) (y, w)).ofLp
            (@finSumFinEquiv (2 * n) 2 (Sum.inl i')) = y.ofLp i' from
          @finAddEquivProd_symm_apply_inl ℝ _ (2 * n) 2 y w i']
      rw [I2]
      rw [show ((sumFibreR (2 * m + 2 * n) 2) ((sumFibreR (2 * m) (2 * n)) (x, y), w)).ofLp
            (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr i'))))
          = ((sumFibreR (2 * m) (2 * n)) (x, y)).ofLp (finSumFinEquiv (Sum.inr i')) from
          @finAddEquivProd_symm_apply_inl ℝ _ (2 * m + 2 * n) 2
            ((sumFibreR (2 * m) (2 * n)) (x, y)) w (finSumFinEquiv (Sum.inr i'))]
      rw [show ((sumFibreR (2 * m) (2 * n)) (x, y)).ofLp (finSumFinEquiv (Sum.inr i'))
            = y.ofLp i' from
          @finAddEquivProd_symm_apply_inr ℝ _ (2 * m) (2 * n) x y i']
    · have I3 : (@finSumFinEquiv (2 * m) (2 * (n + 1))
            (Sum.inr (@finSumFinEquiv (2 * n) 2 (Sum.inr l))) : Fin ((2 * m + 2 * n) + 2))
          = (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inr l)) := by
        simp only [finSumFinEquiv_apply_right]
        exact Fin.ext (by simp only [Fin.natAdd]; omega)
      rw [show ((sumFibreR (2 * m) (2 * (n + 1))) (x, (sumFibreR (2 * n) 2) (y, w))).ofLp
            (@finSumFinEquiv (2 * m) (2 * (n + 1))
              (Sum.inr (@finSumFinEquiv (2 * n) 2 (Sum.inr l))))
          = ((sumFibreR (2 * n) 2) (y, w)).ofLp
              (@finSumFinEquiv (2 * n) 2 (Sum.inr l)) from
          @finAddEquivProd_symm_apply_inr ℝ _ (2 * m) (2 * (n + 1)) x
            ((sumFibreR (2 * n) 2) (y, w)) (finSumFinEquiv (Sum.inr l))]
      rw [show ((sumFibreR (2 * n) 2) (y, w)).ofLp
            (@finSumFinEquiv (2 * n) 2 (Sum.inr l)) = w.ofLp l from
          @finAddEquivProd_symm_apply_inr ℝ _ (2 * n) 2 y w l]
      rw [I3]
      rw [show ((sumFibreR (2 * m + 2 * n) 2) ((sumFibreR (2 * m) (2 * n)) (x, y), w)).ofLp
            (finSumFinEquiv (Sum.inr l)) = w.ofLp l from
          @finAddEquivProd_symm_apply_inr ℝ _ (2 * m + 2 * n) 2
            ((sumFibreR (2 * m) (2 * n)) (x, y)) w l]

/-- **The coordinate of a transported element**: casting an element of `ℝ^a` along an equality of
indices only changes the index (`Fin.cast`).  This is the coordinate layer needed to compare
`sumFibreR`/`sumFibreC` at the two forms `2*(m+n)` and `2*m + 2*n` of the same index. -/
theorem cast_apply_ofLp {a b : ℕ} (h : a = b) (x : EuclideanSpace ℝ (Fin a)) (i : Fin b) :
    (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) x).ofLp i
      = x.ofLp (Fin.cast h.symm i) := by
  subst h
  rfl

/-- The degenerate ("second block empty") case of the complex zip: `sumFibreC m 0` is the projection
onto the first block. -/
theorem sumFibreC_zero (m : ℕ) (x : EuclideanSpace ℂ (Fin m)) (y : EuclideanSpace ℂ (Fin 0)) :
    sumFibreC m 0 (x, y) = x := by
  apply PiLp.ext
  intro i
  rw [show (sumFibreC m 0 (x, y)).ofLp i = x.ofLp i from
    @finAddEquivProd_symm_apply_inl ℂ _ m 0 x y i]

/-- The degenerate ("second block empty") case of the real zip: `sumFibreR (2*m) 0` is the projection
onto the first block. -/
theorem sumFibreR_zero (m : ℕ) (x : EuclideanSpace ℝ (Fin (2 * m)))
    (y : EuclideanSpace ℝ (Fin 0)) :
    sumFibreR (2 * m) 0 (x, y) = x := by
  apply PiLp.ext
  intro i
  rw [show (sumFibreR (2 * m) 0 (x, y)).ofLp i = x.ofLp i from
    @finAddEquivProd_symm_apply_inl ℝ _ (2 * m) 0 x y i]

/-- **The index bridge for `sumFibreR`**: transporting the result of `sumFibreR` along the equality
`2*(m+n) = 2*m + 2*n` (and the transported first block) is the same as computing `sumFibreR` in the
second form.  This is the coordinate layer that lets the induction step of
`rif_sum_compatible_cast` compare `sumFibreR (2*(m+n)) 2` with `sumFibreR (2*m + 2*n) 2`. -/
theorem sumFibreR_cast (m n : ℕ)
    (h : 2 * (m + n) = 2 * m + 2 * n) (h' : 2 * (m + n) + 2 = 2 * m + 2 * n + 2)
    (A : EuclideanSpace ℝ (Fin (2 * (m + n)))) (w : EuclideanSpace ℝ (Fin 2)) :
    cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h')
        (sumFibreR (2 * (m + n)) 2 (A, w))
      = sumFibreR (2 * m + 2 * n) 2
          (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) A, w) := by
  apply PiLp.ext
  intro k
  rcases (@finSumFinEquiv (2 * m + 2 * n) 2).surjective k with ⟨s, rfl⟩
  rcases s with i | l
  · have hk : (Fin.cast h'.symm (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inl i))
          : Fin (2 * (m + n) + 2))
        = (@finSumFinEquiv (2 * (m + n)) 2 (Sum.inl (Fin.cast h.symm i))) := Fin.ext rfl
    rw [show (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h')
          (sumFibreR (2 * (m + n)) 2 (A, w))).ofLp
          (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inl i))
        = (sumFibreR (2 * (m + n)) 2 (A, w)).ofLp
          (Fin.cast h'.symm (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inl i))) from
      cast_apply_ofLp h' _ _]
    rw [hk]
    rw [show (sumFibreR (2 * (m + n)) 2 (A, w)).ofLp
          (@finSumFinEquiv (2 * (m + n)) 2 (Sum.inl (Fin.cast h.symm i)))
        = A.ofLp (Fin.cast h.symm i) from
      @finAddEquivProd_symm_apply_inl ℝ _ (2 * (m + n)) 2 A w (Fin.cast h.symm i)]
    rw [show (sumFibreR (2 * m + 2 * n) 2
          (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) A, w)).ofLp
          (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inl i))
        = (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) A).ofLp i from
      @finAddEquivProd_symm_apply_inl ℝ _ (2 * m + 2 * n) 2
        (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) A) w i]
    exact (cast_apply_ofLp h A i).symm
  · have hk : (Fin.cast h'.symm (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inr l))
          : Fin (2 * (m + n) + 2))
        = (@finSumFinEquiv (2 * (m + n)) 2 (Sum.inr l)) :=
      Fin.ext (by
        first
          | simp [Fin.natAdd, h]
          | (simp only [finSumFinEquiv_apply_right, Fin.natAdd, h]; rfl)
          | (simp only [finSumFinEquiv_apply_right, Fin.natAdd]; omega))
    rw [show (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h')
          (sumFibreR (2 * (m + n)) 2 (A, w))).ofLp
          (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inr l))
        = (sumFibreR (2 * (m + n)) 2 (A, w)).ofLp
          (Fin.cast h'.symm (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inr l))) from
      cast_apply_ofLp h' _ _]
    rw [hk]
    rw [show (sumFibreR (2 * (m + n)) 2 (A, w)).ofLp
          (@finSumFinEquiv (2 * (m + n)) 2 (Sum.inr l)) = w.ofLp l from
      @finAddEquivProd_symm_apply_inr ℝ _ (2 * (m + n)) 2 A w l]
    rw [show (sumFibreR (2 * m + 2 * n) 2
          (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) A, w)).ofLp
          (@finSumFinEquiv (2 * m + 2 * n) 2 (Sum.inr l)) = w.ofLp l from
      @finAddEquivProd_symm_apply_inr ℝ _ (2 * m + 2 * n) 2
        (cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) h) A) w l]

/-- **The unary recursion of `rif`** (up to the canonical cast `2*(k+1) = 2*k+2`): peeling the last
complex coordinate. -/
theorem rif_succ_apply (k : ℕ) (p : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin 1)) :
    HEq (rif (k + 1) (sumFibreC k 1 p)) (sumFibreR (2 * k) 2 (rif k p.1, rifOne p.2)) := by
  apply heq_of_eq
  rw [rif]
  simp only [ContinuousLinearEquiv.trans_apply, cleProd_apply]
  exact congrArg (fun q : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin 1) =>
      sumFibreR (2 * k) 2 (rif k q.1, rifOne q.2))
    (ContinuousLinearEquiv.symm_apply_apply (sumFibreC k 1) p)

/-- **The sum-compatibility of `rif`** (the `HEq` form of
`Work.Whitney.exists_sumCompatible_realification`). -/
theorem rif_sum_compatible_cast (m n : ℕ) (x : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin n)) :
    cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) (Nat.mul_add 2 m n))
        (rif (m + n) (sumFibreC m n x))
      = sumFibreR (2 * m) (2 * n) (rif m x.1, rif n x.2) := by
  induction n with
  | zero =>
    have hx : x.2 = 0 := Subsingleton.elim _ _
    rw [hx, sumFibreC_zero, sumFibreR_zero]
    exact eq_of_heq ((cast_heq _ _).trans (heq_of_eq (rfl : rif (m + 0) x.1 = rif m x.1)))
  | succ n ih =>
    set p := (sumFibreC n 1).symm x.2 with hp
    obtain ⟨y, w⟩ := p
    have hyw : sumFibreC n 1 (y, w) = x.2 := by
      rw [hp]; exact (sumFibreC n 1).apply_symm_apply x.2
    have hxeq : x = (x.1, sumFibreC n 1 (y, w)) := by
      rw [hyw]
    rw [hxeq]
    simp only [Prod.fst, Prod.snd]
    have ih' : cast (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) (Nat.mul_add 2 m n))
        (rif (m + n) (sumFibreC m n (x.1, y)))
        = sumFibreR (2 * m) (2 * n) (rif m x.1, rif n y) := by
      simpa using ih (x.1, y)
    rw [sumFibreC_zip]
    rw [show rif (m + (n + 1)) (sumFibreC (m + n) 1 (sumFibreC m n (x.1, y), w))
        = sumFibreR (2 * (m + n)) 2 (rif (m + n) (sumFibreC m n (x.1, y)), rifOne w) from
      eq_of_heq (rif_succ_apply (m + n) (sumFibreC m n (x.1, y), w))]
    rw [sumFibreR_cast m n (Nat.mul_add 2 m n) (Nat.mul_add 2 m (n + 1))
      (rif (m + n) (sumFibreC m n (x.1, y))) (rifOne w)]
    rw [show rif (n + 1) (sumFibreC n 1 (y, w))
        = sumFibreR (2 * n) 2 (rif n y, rifOne w) from
      eq_of_heq (rif_succ_apply n (y, w))]
    rw [sumFibreR_zip m n (rif m x.1) (rif n y) (rifOne w)]
    rw [← ih']

/-- **THE SUM-COMPATIBLE CANONICAL REALIFICATION**: the `HEq` form of
`Work.Whitney.rif_sum_compatible_cast` (the two sides live in the definitionally unrelated types
`ℝ^{2*(m+n)}` and `ℝ^{2*m+2*n}`, related by `Nat.mul_add`). -/
theorem rif_sum_compatible (m n : ℕ) (x : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin n)) :
    HEq (rif (m + n) (sumFibreC m n x)) (sumFibreR (2 * m) (2 * n) (rif m x.1, rif n x.2)) :=
  (cast_heq (congrArg (fun t : ℕ => EuclideanSpace ℝ (Fin t)) (Nat.mul_add 2 m n))
    (rif (m + n) (sumFibreC m n x))).symm.trans (heq_of_eq (rif_sum_compatible_cast m n x))

end Cure

end

section Target

noncomputable section

/-- **THE TOP DEGREE OF THE WHITNEY SUM FORMULA** (= `Work.Whitney.TopClassMul`, the multiplicativity
of the Euler class of a direct sum).  `chernClass m m Z` is the Euler class of the realification of
`Z` (`Work.Thom.chernClass_succ_top'`), so the assertion is `e(E_ℝ ⊕ F_ℝ) = e(E_ℝ) ⌣ e(F_ℝ)`.

**PROVED** from the three pieces below (see the STATUS block in the module docstring): the relative
Thom product formula `Work.Whitney.thomClassRank_whitneySum_rel` (whose chart bookkeeping uses the
canonical realification `Work.Gen.rifStd` = `Work.Thom.covE`, the sum-compatibility
`Work.Gen.rifStd_sum_compatible_cast`, and the sign-free even model formula
`Work.Whitney.tcmModelMul_even'`), its Euler-class consequence
`Work.Whitney.chernClass_whitneySum_top_of_thomProduct`, and the two rank-zero boundary cases
`Work.Whitney.chernClass_whitneySum_top_rank_zero_left`/`_right`. -/
theorem chernClass_whitneySum_top {m₁ m₂ : ℕ} {B : Type} [TopologicalSpace B]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) :
    Work.Thom.chernClass (m₁ + m₂) (m₁ + m₂) (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Whitney.cupChern m₁ m₂ (Work.Thom.chernClass m₁ m₁ Z₁)
          (Work.Thom.chernClass m₂ m₂ Z₂) := by
  rcases Nat.eq_zero_or_pos m₁ with h₁ | h₁
  · -- rank-0 first summand: the boundary case, `Work.Whitney.chernClass_whitneySum_rank_zero`
    subst h₁
    exact Work.Whitney.chernClass_whitneySum_top_rank_zero_left Z₁ Z₂
  · rcases Nat.eq_zero_or_pos m₂ with h₂ | h₂
    · -- rank-0 second summand (`Nat.add` recurses on its second argument, so `m₁ + 0` is `m₁`)
      subst h₂
      exact Work.Whitney.chernClass_whitneySum_top_rank_zero_right Z₁ Z₂
    · -- both ranks positive: the Thom-product route
      have hm₁ : 1 ≤ m₁ := h₁
      have hm₂ : 1 ≤ m₂ := h₂
      -- the two coordinate projections of the total space of the sum
      let π₁ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
          (Work.Thom.realification Z₁).TotalSpace) :=
        ⟨fun p => ⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).1⟩,
          Work.Whitney.continuous_realification_whitneySum_fst Z₁ Z₂⟩
      let π₂ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
          (Work.Thom.realification Z₂).TotalSpace) :=
        ⟨fun p => ⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).2⟩,
          Work.Whitney.continuous_realification_whitneySum_snd Z₁ Z₂⟩
      have hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).1⟩ := fun _ => rfl
      have hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).2⟩ := fun _ => rfl
      -- the two pieces are open and cover the complement of the zero section
      obtain ⟨hAopen, hCopen, hset⟩ :=
        Work.Whitney.wsumPiece_open_union Z₁ Z₂ π₁ π₂ hπ₁ hπ₂
      -- the relative Thom product formula, and its Euler-class consequence
      exact Work.Whitney.chernClass_whitneySum_top_of_thomProduct hm₁ hm₂ Z₁ Z₂ π₁ π₂ hπ₁ hπ₂
        hset hAopen hCopen
        (Work.Whitney.thomClassRank_whitneySum_rel hm₁ hm₂ Z₁ Z₂ π₁ π₂ hπ₁ hπ₂ hset hAopen hCopen)

/-- **THE WHITNEY SUM FORMULA IN THE TOP DEGREE**, in the `Prop`-form `Work.Whitney.TopClassMul`
consumed by the Leray–Hirsch area (`Submission/Work/LerayHirsch/Splitting.lean`,
`whitneySumFormula_one_one_of_topClassMul.lean`, `WhitneyParacompact.lean`): the
`∀`-quantification of `Work.Whitney.chernClass_whitneySum_top` over all bases, covers and ranks. -/
theorem topClassMul_proof : Work.Whitney.TopClassMul :=
  fun Z₁ Z₂ => Work.Whitney.chernClass_whitneySum_top Z₁ Z₂

end

end Target

end Work.Whitney
