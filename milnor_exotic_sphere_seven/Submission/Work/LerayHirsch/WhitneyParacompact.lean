import Mathlib
import Submission.Work.LerayHirsch.Splitting
import Submission.Work.LerayHirsch.SplitsOverProj
import Submission.Work.LerayHirsch.whitneySumFormulaOfLerayHirsch
import Submission.Work.LerayHirsch.t2Space_projSpace
import Submission.Work.LerayHirsch.paracompactSpace_projSpace

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The Whitney sum formula over paracompact Hausdorff bases

This module *restates* the Whitney sum formula over paracompact Hausdorff bases
(`Work.LerayHirsch.WhitneySumFormulaPar`) and proves the assembly in that form:

  `∀ Z, LerayHirschFull Z`  (from `KunnethCP`, subproject KUNNETH)
  `∀ N, WhitneySumFormulaPar 1 N`  (the line-bundle case — over paracompact Hausdorff bases, which is
    the form the induction needs; it is the input isolated in `Submission/Work/LerayHirsch/SplitLines.lean`)
  ⟹  `c_k(E ⊕ F) = Σ_{i+j=k} c_i(E) ⌣ c_j(F)` for all bundles `E`, `F` over a paracompact Hausdorff
  base.

The induction is the one of `whitneySumFormulaOfLerayHirsch.lean`; the change is that the splitting
`SplitsOverProj Z₁` is now *proved* by `Work.LerayHirsch.splitsOverProj_of_paracompact`, whose two
hypotheses on `P(E)` are the *instances* `Work.LerayHirsch.t2Space_projSpace` and
`Work.LerayHirsch.paracompactSpace_projSpace`; consequently the recursive calls run over the
intermediate bases `P(Z₁)`, `P(Q)`, …, which are paracompact Hausdorff by the same two instances.

This is *not* available over an arbitrary topological base: `SplitsOverProj` is false there (the
chart-wise functional `v ↦ (v_k/z_k)·s` has a non-block-diagonal transition cocycle), and every
consumer in this project (GEN, AGREE, THOM) works over a compact, hence paracompact Hausdorff, base.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {B' : Type} [TopologicalSpace B']

/-- **The Whitney sum formula over paracompact Hausdorff bases**: for complex bundles `Z₁`, `Z₂` of
ranks `m₁`, `m₂` over a paracompact Hausdorff base, `c_k(Z₁ ⊕ Z₂) = Σ_{i+j=k} c_i(Z₁) ⌣ c_j(Z₂)`.

This is `Work.LerayHirsch.WhitneySumFormula` with the base assumed paracompact Hausdorff, which is
the form in which the splitting principle of this chapter is available. -/
def WhitneySumFormulaPar (m₁ m₂ : ℕ) : Prop :=
  ∀ {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B] {ι₁ ι₂ : Type}
    [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) (k : ℕ),
    chernClass (m₁ + m₂) k (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Whitney.chernProductSum Z₁ Z₂ k

/-- The unrestricted Whitney formula implies its paracompact-Hausdorff form. -/
theorem whitneySumFormulaPar_of_whitneySumFormula {m₁ m₂ : ℕ}
    (h : WhitneySumFormula m₁ m₂) : WhitneySumFormulaPar m₁ m₂ := by
  intro B _ _ _ ι₁ ι₂ _ _ Z₁ Z₂ k
  exact h Z₁ Z₂ k

/-- **The Whitney sum formula for a rank-`0` first summand** (paracompact form). -/
theorem whitneySumFormulaPar_rank_zero (m₂ : ℕ) : WhitneySumFormulaPar 0 m₂ := by
  intro B _ _ _ ι₁ ι₂ _ _ Z₁ Z₂ k
  obtain ⟨e₁⟩ := Work.Whitney.nonempty_bundleIso_whitneySum_comm (Z₁ := Z₁) (Z₂ := Z₂)
  obtain ⟨e₂⟩ := Work.Whitney.nonempty_bundleIso_sumCore_of_subsingleton (𝕜 := ℂ) (B := B)
    (F₁ := EuclideanSpace ℂ (Fin m₂)) (F₂ := EuclideanSpace ℂ (Fin 0))
    (F := EuclideanSpace ℂ (Fin (m₂ + 0))) (Work.Whitney.sumFibreC m₂ 0) Z₂ Z₁
  exact (Work.Whitney.chernClass_BundleIso_of_eq (by omega : 0 + m₂ = m₂ + 0) _ _ e₁ k).trans
    ((Work.Whitney.chernClass_BundleIso_of_eq (by omega : m₂ + 0 = m₂) _ _ e₂ k).trans
      (chernProductSum_rank_zero_first Z₁ Z₂ k).symm)

/-- **The induction step** (paracompact form): the Whitney formula in rank `p` implies it in rank
`p + 1`.  The only difference from `Work.LerayHirsch.whitneySumFormula_succ` is that the splitting
`SplitsOverProj Z₁` is *proved* here, by `Work.LerayHirsch.splitsOverProj_of_paracompact`, from the
two instances for `P(Z₁)` supplied by the hypotheses `hT2`, `hPar`. -/
theorem whitneySumFormulaPar_succ (p : ℕ)
    (hLH : ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι), LerayHirschFull Z)
    (hLine : ∀ N : ℕ, WhitneySumFormulaPar 1 N)
    (IH : ∀ m₂, WhitneySumFormulaPar p m₂) :
    ∀ m₂, WhitneySumFormulaPar (p + 1) m₂ := by
  intro m₂ B _ _ _ ι₁ ι₂ _ _ Z₁ Z₂ k
  haveI : T2Space (ProjSpace Z₁) := t2Space_projSpace Z₁
  haveI : ParacompactSpace (ProjSpace Z₁) := paracompactSpace_projSpace Z₁
  obtain ⟨Q, ⟨e⟩⟩ := splitsOverProj_of_paracompact Z₁
  -- pull back to the projectivisation
  refine (CohMap_projMap_injective_of_LerayHirschFull (m := p + 1) (by omega) Z₁ (hLH Z₁)
    (2 * k)) ?_
  rw [← Work.Thom.chernClass_comap, Work.Whitney.whitneySum_bundleComap,
    Work.Whitney.chernProductSum_CohMap]
  -- now over `ProjSpace Z₁`
  set W : VectorBundleCore ℂ (ProjSpace Z₁) (EuclideanSpace ℂ (Fin m₂)) ι₂ :=
    Work.Thom.bundleComap Z₂ (projMap Z₁) with hW
  -- step 1: replace `π^*Z₁` by `ℓ ⊕ Q`
  have hstep1 : chernClass ((p + 1) + m₂) k
        (Work.Whitney.whitneySum (Work.Thom.bundleComap Z₁ (projMap Z₁)) W)
      = chernClass ((1 + p) + m₂) k
        (Work.Whitney.whitneySum (Work.Whitney.whitneySum (tautLine Z₁) Q) W) := by
    obtain ⟨e'⟩ := nonempty_bundleIso_whitneySum_first (Z₁ := Work.Thom.bundleComap Z₁ (projMap Z₁))
      (Z₁' := Work.Whitney.whitneySum (tautLine Z₁) Q) (Z₂ := W) e
    exact Work.Whitney.chernClass_BundleIso_of_eq (by omega : (p + 1) + m₂ = (1 + p) + m₂) _ _ e' k
  rw [hstep1]
  -- step 2: reassociate
  have hstep2 : chernClass ((1 + p) + m₂) k
        (Work.Whitney.whitneySum (Work.Whitney.whitneySum (tautLine Z₁) Q) W)
      = chernClass (1 + (p + m₂)) k
        (Work.Whitney.whitneySum (tautLine Z₁) (Work.Whitney.whitneySum Q W)) := by
    obtain ⟨e'⟩ := nonempty_bundleIso_whitneySum_assoc (tautLine Z₁) Q W
    exact Work.Whitney.chernClass_BundleIso_of_eq (by omega : (1 + p) + m₂ = 1 + (p + m₂)) _ _ e' k
  rw [hstep2]
  -- step 3: the line-bundle case
  have hstep3 : chernClass (1 + (p + m₂)) k
        (Work.Whitney.whitneySum (tautLine Z₁) (Work.Whitney.whitneySum Q W))
      = Work.Whitney.chernProductSum (tautLine Z₁) (Work.Whitney.whitneySum Q W) k :=
    hLine (p + m₂) (tautLine Z₁) (Work.Whitney.whitneySum Q W) k
  rw [hstep3]
  -- step 4: the algebraic step (associativity of the convolution), with the induction hypothesis
  have hstep4 : Work.Whitney.chernProductSum (tautLine Z₁) (Work.Whitney.whitneySum Q W) k
      = Work.Whitney.chernProductSum (Work.Whitney.whitneySum (tautLine Z₁) Q) W k := by
    have hQWs : chernSeries (Work.Whitney.whitneySum Q W)
        = convSeries (chernSeries Q) (chernSeries W) :=
      chernSeries_whitneySum_eq_convSeries Q W (fun j => IH m₂ Q W j)
    have hlQ : convSeries (chernSeries (tautLine Z₁)) (chernSeries Q)
        = chernSeries (Work.Whitney.whitneySum (tautLine Z₁) Q) :=
      (chernSeries_whitneySum_eq_convSeries (tautLine Z₁) Q
        (fun j => hLine p (tautLine Z₁) Q j)).symm
    rw [chernProductSum_eq_convSeries, hQWs, ← convSeries_assoc, hlQ,
      ← chernProductSum_eq_convSeries]
  rw [hstep4]
  -- step 5: `whitneySum ℓ Q ≅ π^*Z₁`
  refine (chernProductSum_congr_first (Work.Whitney.whitneySum (tautLine Z₁) Q)
    (Work.Thom.bundleComap Z₁ (projMap Z₁)) W k ?_)
  intro i
  exact Work.Whitney.chernClass_BundleIso_of_eq (by omega : 1 + p = p + 1)
    (Work.Whitney.whitneySum (tautLine Z₁) Q) (Work.Thom.bundleComap Z₁ (projMap Z₁)) e.symm i

/-- **The Whitney sum formula in all ranks over paracompact Hausdorff bases**, from the
Leray–Hirsch theorem, the line-bundle case and the two instances for the projectivisation. -/
theorem whitneySumFormulaPar_of_lerayHirsch
    (hLH : ∀ {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι), LerayHirschFull Z)
    (hLine : ∀ N : ℕ, WhitneySumFormulaPar 1 N) :
    ∀ m₁ m₂ : ℕ, WhitneySumFormulaPar m₁ m₂ := by
  intro m₁
  induction m₁ using Nat.strong_induction_on with
  | _ m ih =>
    intro m₂
    rcases m with _ | _ | p
    · exact whitneySumFormulaPar_rank_zero m₂
    · exact hLine m₂
    · exact whitneySumFormulaPar_succ (p + 1) hLH hLine
        (fun m₂ => ih (p + 1) (by omega) m₂) m₂

end

end Work.LerayHirsch
