import Mathlib
import Submission.Work.Diff.EXT.evolX.compLadderDefs
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.evolX.dvcDefs
import Submission.Work.Diff.EXT.evolX.pairingSplitNB

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `dvc` sections are mdifferentiable

`Work.Diff.EXT.evolX.dvcFieldSmooth`: for a vector-valued operator `U` whose *pairing*
`pairVec g U` has smooth jets near `x` (`Work.Diff.EXT.JetSmoothOp`), the covariant-derivative
sections `y ↦ dvc g K U c F y` are mdifferentiable near `x` (for smooth fields `F`).

## The ladder

The proof runs an induction on the number `j` of covariant derivatives, with the two invariants
(on an open set `V ∋ x`)

* `dvcFieldMD g K U j V` — the sections `dvc g K U j F` (for smooth `F`) are mdifferentiable at
  every point of `V`;
* `dvcFieldPair g K U j V` — the `j`-th jet of the pairing operator is the pairing with the `j`-th
  covariant derivative of `U`:
  `jetAll g j (K+1) (pairVec g U) (dvcTup K j F W) = ⟪dvc g K U j F, W⟫` on `V`.

`dvcFieldPair (j+1)` is deduced from `dvcFieldPair j` and `dvcFieldMD j` by the Leibniz (product)
rule for the metric pairing (`Work.Diff.EXT.evolX.pairingSplitNB`, which needs only
*mdifferentiability at the point*), while `dvcFieldMD j` is deduced from `dvcFieldPair j` and the
hypothesis `hU` (smoothness of the jets of the pairing) by the *pairing-to-section* step
(`dvcFieldSectionOfChartPairing`): the pairings of `dvc g K U j F` with the chart frame determine
the section.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

section Ladder

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Auxiliary facts -/

/-- The reindexing `Fin ((K+j)+1) ≃ Fin ((K+1)+j)` (the value-preserving bijection). -/
def dvcFieldCastEquiv (K j : ℕ) : Fin ((K + j) + 1) ≃ Fin ((K + 1) + j) where
  toFun r := ⟨(r : ℕ), by have := r.isLt; omega⟩
  invFun r := ⟨(r : ℕ), by have := r.isLt; omega⟩
  left_inv r := Fin.ext rfl
  right_inv r := Fin.ext rfl

/-- **Splitting a sum over `Fin ((K+1)+j)` at its last term.** -/
theorem dvcField_sum_univ_split (K j : ℕ) {α : Type*} [AddCommMonoid α]
    (f : Fin ((K + 1) + j) → α) :
    (∑ r : Fin ((K + 1) + j), f r)
      = (∑ r : Fin (K + j), f (Fin.castLE (by omega) r)) + f (⟨K + j, by omega⟩) := by
  have h1 : (∑ r : Fin ((K + 1) + j), f r)
      = ∑ r : Fin ((K + j) + 1), f (dvcFieldCastEquiv K j r) :=
    (Fintype.sum_equiv (dvcFieldCastEquiv K j) (fun r : Fin ((K + j) + 1) =>
      f (dvcFieldCastEquiv K j r)) f (fun r => rfl)).symm
  rw [h1, Fin.sum_univ_castSucc]
  have e1 : (∑ i : Fin (K + j), f (dvcFieldCastEquiv K j i.castSucc))
      = ∑ i : Fin (K + j), f (Fin.castLE (by omega) i) :=
    Finset.sum_congr rfl (fun i _ => by congr 1)
  have e2 : f (dvcFieldCastEquiv K j (Fin.last (K + j)))
      = f (⟨K + j, by omega⟩ : Fin ((K + 1) + j)) := by
    congr 1
  rw [e1, e2]

/-- **Linearity of the metric pairing in the first argument**, for a difference of a vector and a
finite sum. -/
theorem dvcField_inner_sub_sum (g : Submission.Diff.SMet I M) {y : M}
    (a w : TangentSpace I y) {ι : Type*} [Fintype ι] (c : ι → TangentSpace I y) :
    g.inner y (a - ∑ i, c i) w = g.inner y a w - ∑ i, g.inner y (c i) w := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  change inner ℝ (a - ∑ i, c i) w = inner ℝ a w - ∑ i, inner ℝ (c i) w
  rw [inner_sub_left, sum_inner]

/-! ## The two invariants of the ladder -/

/-- **`dvcFieldMD g K U j V`**: the `j`-th covariant derivative of `U` is mdifferentiable at every
point of `V` (on smooth tuples). -/
noncomputable def dvcFieldMD (g : Submission.Diff.SMet I M) (K : ℕ)
    (U : (Fin K → TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (j : ℕ) (V : Set M) : Prop :=
  ∀ (F : Fin (K + j) → TField (I := I) (M := M)), (∀ i, SmoothF (F i)) →
    ∀ y ∈ V, MDifferentiableAt I I.tangent
      (fun z : M => Bundle.TotalSpace.mk' E z (dvc g K U j F z)) y

/-- **`dvcFieldPair g K U j V`**: the `j`-th jet of `pairVec g U` is the pairing of the `j`-th
covariant derivative of `U` with the extra field, at every point of `V`. -/
noncomputable def dvcFieldPair (g : Submission.Diff.SMet I M) (K : ℕ)
    (U : (Fin K → TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (j : ℕ) (V : Set M) : Prop :=
  ∀ (F : Fin (K + j) → TField (I := I) (M := M)) (W : TField (I := I) (M := M)),
    (∀ i, SmoothF (F i)) → SmoothF W → ∀ y ∈ V,
      jetAll g j (K + 1) (pairVec g U) (dvcTup (I := I) (M := M) K j F W) y
        = g.inner y (dvc g K U j F y) (W y)

variable {g : Submission.Diff.SMet I M} {K : ℕ}
  {U : (Fin K → TField (I := I) (M := M)) → (y : M) → TangentSpace I y} {j : ℕ}

theorem dvcFieldMD_mono {V V' : Set M} (h : V' ⊆ V)
    (hV : dvcFieldMD (I := I) (M := M) g K U j V) :
    dvcFieldMD (I := I) (M := M) g K U j V' :=
  fun F hF y hy => hV F hF y (h hy)

theorem dvcFieldPair_mono {V V' : Set M} (h : V' ⊆ V)
    (hV : dvcFieldPair (I := I) (M := M) g K U j V) :
    dvcFieldPair (I := I) (M := M) g K U j V' :=
  fun F W hF hW y hy => hV F W hF hW y (h hy)

/-- **The base case of the ladder identity.** -/
theorem dvcFieldPair_zero (g : Submission.Diff.SMet I M) (K : ℕ)
    (U : (Fin K → TField (I := I) (M := M)) → (y : M) → TangentSpace I y) :
    dvcFieldPair (I := I) (M := M) g K U 0 Set.univ := by
  intro F W hF hW y hy
  have hone : (fun i : Fin K =>
      dvcTup (I := I) (M := M) K 0 F W (Fin.castSucc i)) = F :=
    funext (fun i => dvcTup_zero_castSucc (I := I) (M := M) K F W i)
  have htwo : dvcTup (I := I) (M := M) K 0 F W (Fin.last K) = W :=
    dvcTup_zero_last (I := I) (M := M) K F W
  simp only [jetAll, dvc_zero, pairVec]
  rw [hone, htwo]

/-- **The inductive step of the ladder identity**: the `(j+1)`-st jet of the pairing is the pairing
of the `(j+1)`-st covariant derivative of `U`, given the same statement at level `j` and the
mdifferentiability of the level-`j` derivative. -/
theorem dvcFieldPair_succ (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    {K : ℕ} (U : (Fin K → TField (I := I) (M := M)) → (y : M) → TangentSpace I y) (j : ℕ)
    {V : Set M} (hVo : IsOpen V)
    (hMD : dvcFieldMD (I := I) (M := M) g K U j V)
    (hPA : dvcFieldPair (I := I) (M := M) g K U j V) :
    dvcFieldPair (I := I) (M := M) g K U (j + 1) V := by
  intro F W hF hW y hy
  have hBs : ∀ i : Fin (K + j), SmoothF ((fun i : Fin (K + j) => F i.succ) i) := fun i => hF i.succ
  have hWmd : MDifferentiableAt I I.tangent
      (fun z : M => Bundle.TotalSpace.mk' E z (W z)) y :=
    hW.contMDiffAt.mdifferentiableAt (by simp)
  have hPA' : (fun z : M => jetAll g j (K + 1) (pairVec g U)
        (dvcTup (I := I) (M := M) K j (fun i : Fin (K + j) => F i.succ) W) z)
      =ᶠ[𝓝 y] (fun z : M => g.inner z
        (dvc g K U j (fun i : Fin (K + j) => F i.succ) z) (W z)) := by
    filter_upwards [hVo.mem_nhds hy] with z hz
    exact hPA (fun i : Fin (K + j) => F i.succ) W hBs hW z hz
  have hstep : jetAll g (j + 1) (K + 1) (pairVec g U)
        (dvcTup (I := I) (M := M) K (j + 1) F W) y
      = mvfderiv I (fun z : M => jetAll g j (K + 1) (pairVec g U)
            (dvcTup (I := I) (M := M) K j (fun i : Fin (K + j) => F i.succ) W) z) y (F 0 y)
        - ∑ s : Fin ((K + 1) + j), jetAll g j (K + 1) (pairVec g U)
            (Function.update (dvcTup (I := I) (M := M) K j
                (fun i : Fin (K + j) => F i.succ) W) s
              (dirF g ((dvcTup (I := I) (M := M) K j
                (fun i : Fin (K + j) => F i.succ) W) s) (F 0))) y := by
    simp only [jetAll, extStep]
    simp only [dvcTup_succ_apply, dvcTup_apply_zero]
  have hdir : mvfderiv I (fun z : M => jetAll g j (K + 1) (pairVec g U)
        (dvcTup (I := I) (M := M) K j (fun i : Fin (K + j) => F i.succ) W) z) y (F 0 y)
      = g.inner y (lcOf g (dvc g K U j (fun i : Fin (K + j) => F i.succ)) y (F 0 y)) (W y)
        + g.inner y (dvc g K U j (fun i : Fin (K + j) => F i.succ) y)
            (lcOf g W y (F 0 y)) := by
    rw [mvfderiv_congr_of_eventuallyEq_real' (I := I) (M := M) hPA']
    exact pairingSplitNB (I := I) (M := M) hLC g
      (hMD (fun i : Fin (K + j) => F i.succ) hBs y hy) hWmd
  have hcorr : (∑ s : Fin ((K + 1) + j), jetAll g j (K + 1) (pairVec g U)
        (Function.update (dvcTup (I := I) (M := M) K j
            (fun i : Fin (K + j) => F i.succ) W) s
          (dirF g ((dvcTup (I := I) (M := M) K j
            (fun i : Fin (K + j) => F i.succ) W) s) (F 0))) y)
      = (∑ r : Fin (K + j), g.inner y (dvc g K U j
            (Function.update (fun i : Fin (K + j) => F i.succ) r
              (dirF g ((fun i : Fin (K + j) => F i.succ) r) (F 0))) y) (W y))
        + g.inner y (dvc g K U j (fun i : Fin (K + j) => F i.succ) y)
            (lcOf g W y (F 0 y)) := by
    rw [dvcField_sum_univ_split (K := K) (j := j)]
    have hupd : ∀ r : Fin (K + j), (∀ i, SmoothF ((Function.update
        (fun i : Fin (K + j) => F i.succ) r
          (dirF g ((fun i : Fin (K + j) => F i.succ) r) (F 0))) i)) :=
      fun r => smoothF_update' (I := I) (M := M) hBs r
        (Work.Diff.EXT.dirF_smooth (I := I) (M := M) hLC g (hBs r) (hF 0))
    congr 1
    · refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [dvcTup_castLE (I := I) (M := M) K j (fun i : Fin (K + j) => F i.succ) W r,
        dvcTup_update (I := I) (M := M) K j (fun i : Fin (K + j) => F i.succ) W r
          (dirF g ((fun i : Fin (K + j) => F i.succ) r) (F 0))]
      exact hPA (Function.update (fun i : Fin (K + j) => F i.succ) r
          (dirF g ((fun i : Fin (K + j) => F i.succ) r) (F 0))) W (hupd r) hW y hy
    · rw [dvcTup_last (I := I) (M := M) K j (fun i : Fin (K + j) => F i.succ) W,
        dvcTup_update_last (I := I) (M := M) K j (fun i : Fin (K + j) => F i.succ) W
          (dirF g W (F 0))]
      exact hPA (fun i : Fin (K + j) => F i.succ) (dirF g W (F 0)) hBs
        (Work.Diff.EXT.dirF_smooth (I := I) (M := M) hLC g hW (hF 0)) y hy
  have hrhs : g.inner y (dvc g K U (j + 1) F y) (W y)
      = g.inner y (lcOf g (dvc g K U j (fun i : Fin (K + j) => F i.succ)) y (F 0 y)) (W y)
        - (∑ r : Fin (K + j), g.inner y (dvc g K U j
              (Function.update (fun i : Fin (K + j) => F i.succ) r
                (dirF g ((fun i : Fin (K + j) => F i.succ) r) (F 0))) y) (W y)) := by
    rw [dvc_succ (I := I) (M := M) g K U j]
    simp only [dvStep]
    rw [dvcField_inner_sub_sum (I := I) (M := M) g
      (lcOf g (dvc g K U j (fun i : Fin (K + j) => F i.succ)) y (F 0 y)) (W y)
      (fun r : Fin (K + j) => dvc g K U j
        (Function.update (fun i : Fin (K + j) => F i.succ) r
          (dirF g ((fun i : Fin (K + j) => F i.succ) r) (F 0))) y)]
  rw [hstep, hdir, hcorr, hrhs]
  ring

/-- **The pairing-to-section step**: from the mdifferentiability of the pairings of `V` with the
chart frame at `x`, the section `V` is mdifferentiable at `x`.

This is the pointwise-`MDifferentiableAt` version of `Work.EXT.lc_section_of_inner`
(`Submission/Work/EXT/lcSmooth_noBoundary.lean`), adapted to an explicit metric `g` and to the
chart frame `chartFrame` (the Gram-inverse construction of the coefficients). -/
theorem dvcFieldSectionOfChartPairing (g : Submission.Diff.SMet I M)
    {V : (y : M) → TangentSpace I y} {x : M}
    (h : ∀ i : Fin (Module.finrank ℝ E), MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => g.inner y (V y) (chartFrame (I := I) (M := M) x i y)) x) :
    MDifferentiableAt I I.tangent
      (fun z : M => Bundle.TotalSpace.mk' E z (V z)) x := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) := inferInstance
  set triv := FiberBundle.trivializationAt E (TangentSpace I) x with htriv
  have hp : x ∈ triv.baseSet := by
    rw [htriv, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H x
  choose Z hZ hZeq using fun i : Fin (Module.finrank ℝ E) =>
    Work.Diff.T.exists_global_eventuallyEq_symmL (I := I) (M := M) x
      (Module.finBasis ℝ E i) (mem_chart_source H x)
  have hZ' : ∀ i, CMDiff ∞ (T% (Z i)) := fun i => hZ i
  have hP : ∀ j : Fin (Module.finrank ℝ E),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun q : M => g.inner q (V q) (Z j q)) x := by
    intro j
    refine (h j).congr_of_eventuallyEq ?_
    filter_upwards [hZeq j] with q hq
    exact congrArg (fun w => g.inner q (V q) w) hq
  set Gm : M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun q => Matrix.gram ℝ (fun i => Z i q) with hGm
  have hentry : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => Gm q i j) x := by
    intro i j
    have h1 : CMDiff ∞ (fun q : M => inner ℝ (Z i q) (Z j q)) :=
      ContMDiff.inner_bundle (hZ' i) (hZ' j)
    simpa only [hGm, Matrix.gram_apply] using h1.contMDiffAt
  have det_smooth : ∀ (A : M → Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ),
      (∀ i j, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => A q i j) x) →
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => (A q).det) x := by
    intro A hA
    have hsum : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M =>
        ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A q (σ i) i) x :=
      ContMDiffAt.sum (t := Finset.univ) fun σ _ =>
        ContMDiffAt.mul (contMDiffAt_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ)))
          (ContMDiffAt.prod (t := Finset.univ) (f := fun i q => A q (σ i) i)
            (fun i _ => hA (σ i) i))
    refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    show (A q).det = ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A q (σ i) i
    rw [Matrix.det_apply]
    exact Finset.sum_congr rfl fun σ _ => by simp [Units.smul_def, zsmul_eq_mul]
  have hdetGm : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => (Gm q).det) x := det_smooth Gm hentry
  have hadj : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => (Gm q).adjugate a b) x := by
    intro a b
    have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun q : M => ((fun q : M => (Gm q).updateRow b (Pi.single a (1 : ℝ))) q).det) x :=
      det_smooth (fun q : M => (Gm q).updateRow b (Pi.single a (1 : ℝ))) (fun i j => ?_)
    · simpa only [Matrix.adjugate_apply] using h1
    · by_cases hij : i = b
      · subst hij
        have hself : (fun q : M => (Gm q).updateRow i (Pi.single a (1 : ℝ)) i j)
            = fun _ : M => (Pi.single a (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ) j := by
          funext q
          exact congrFun (Matrix.updateRow_self (M := Gm q) (i := i)
            (b := Pi.single a (1 : ℝ))) j
        rw [hself]
        exact contMDiffAt_const
      · have hne : (fun q : M => (Gm q).updateRow b (Pi.single a (1 : ℝ)) i j)
            = fun q : M => Gm q i j := by
          funext q
          exact congrFun (Matrix.updateRow_ne (M := Gm q) (i := b)
            (b := Pi.single a (1 : ℝ)) hij) j
        rw [hne]
        exact hentry i j
  have hdetx_ne : (Gm x).det ≠ 0 := by
    have hframe : LinearIndependent ℝ
        (fun i => triv.symmL ℝ x ((Module.finBasis ℝ E) i)) := by
      have hker : LinearMap.ker
          ((triv.symmL ℝ x : E →L[ℝ] TangentSpace I x) : E →ₗ[ℝ] TangentSpace I x) = ⊥ := by
        rw [LinearMap.ker_eq_bot']
        intro y hy
        have h2 : (triv.symmL ℝ x) y = 0 := by simpa using hy
        have h1 := Trivialization.continuousLinearMapAt_symmL (e := triv) (R := ℝ) hp y
        rw [h2, map_zero] at h1
        exact h1.symm
      have h1 := (Module.finBasis ℝ E).linearIndependent.map'
        ((triv.symmL ℝ x : E →L[ℝ] TangentSpace I x) : E →ₗ[ℝ] TangentSpace I x) hker
      convert h1 using 1
      ext i
      rfl
    have hLI : LinearIndependent ℝ (fun i => Z i x) := by
      rw [show (fun i => Z i x)
        = fun i => triv.symmL ℝ x ((Module.finBasis ℝ E) i) from
        funext fun i => (hZeq i).eq_of_nhds]
      exact hframe
    have hpos : (Gm x).PosDef := by
      rw [hGm]
      exact Matrix.posDef_gram_of_linearIndependent hLI
    exact (hpos.det_pos).ne'
  have hinv : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => ((Gm q)ᵀ)⁻¹ a b) x := by
    intro a b
    have hdetT : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => ((Gm q)ᵀ).det) x := by
      simpa only [Matrix.det_transpose] using hdetGm
    have hadjT : ∀ i j : Fin (Module.finrank ℝ E),
        ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => ((Gm q)ᵀ).adjugate i j) x := by
      intro i j
      simpa only [← Matrix.adjugate_transpose, Matrix.transpose_apply] using hadj j i
    have hdetT_ne : ((Gm x)ᵀ).det ≠ 0 := by
      simpa only [Matrix.det_transpose] using hdetx_ne
    have hfun : (fun q : M => ((Gm q)ᵀ)⁻¹ a b)
        = fun q => (((Gm q)ᵀ).det)⁻¹ * ((Gm q)ᵀ).adjugate a b := by
      funext q
      rw [Matrix.inv_def]
      simp
    rw [hfun]
    have hinv1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => (((Gm q)ᵀ).det)⁻¹) x :=
      ((ContDiffAt.inv contDiffAt_id hdetT_ne).contMDiffAt).comp x hdetT
    exact ContMDiffAt.mul hinv1 (hadjT a b)
  set cf : M → (Fin (Module.finrank ℝ E) → ℝ) :=
    fun q => ((Gm q)ᵀ)⁻¹ *ᵥ (fun j => g.inner q (V q) (Z j q)) with hcf
  have hcf_md : ∀ a, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun q : M => cf q a) x := by
    intro a
    have hfun : (fun q : M => cf q a)
        = fun q => ∑ j, ((Gm q)ᵀ)⁻¹ a j * g.inner q (V q) (Z j q) := by
      funext q
      rw [hcf]
      exact Matrix.mulVec_apply _ _ _
    rw [hfun]
    have h := MDifferentiableAt.sum (t := Finset.univ) (fun j _ =>
      MDifferentiableAt.mul ((hinv a j).mdifferentiableAt (by simp)) (hP j))
    have hgoal : (∑ i : Fin (Module.finrank ℝ E),
          (fun q : M => ((Gm q)ᵀ)⁻¹ a i) * (fun q : M => g.inner q (V q) (Z i q)))
        = fun q : M => ∑ j, ((Gm q)ᵀ)⁻¹ a j * g.inner q (V q) (Z j q) := by
      funext q
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl (fun j _ => rfl)
    rw [← hgoal]
    exact h
  set W : (q : M) → TangentSpace I q := fun q => ∑ i, (cf q) i • Z i q with hWdef
  have hW : MDifferentiableAt I I.tangent
      (fun z : M => Bundle.TotalSpace.mk' E z (W z)) x := by
    have h1 : MDifferentiableAt I I.tangent
        (T% (fun q : M => ∑ i, (cf q) i • Z i q)) x :=
      MDifferentiableAt.sum_section (I := I) (s := Finset.univ)
        (t := fun i (q : M) => (cf q) i • Z i q)
        (fun i _ => MDifferentiableAt.smul_section (hcf_md i)
          ((hZ' i).contMDiffAt.mdifferentiableAt (by simp)))
    simpa only [hWdef] using h1
  have hgood : ∀ᶠ q in 𝓝 x,
      q ∈ triv.baseSet ∧ (∀ i, Z i q = triv.symmL ℝ q ((Module.finBasis ℝ E) i))
        ∧ ((Gm q).det ≠ 0) := by
    have h1 : ∀ᶠ q in 𝓝 x, ∀ i, Z i q = triv.symmL ℝ q ((Module.finBasis ℝ E) i) :=
      Filter.eventually_all.2 hZeq
    have h2 : ∀ᶠ q in 𝓝 x, (Gm q).det ≠ 0 :=
      hdetGm.continuousAt.eventually_ne hdetx_ne
    filter_upwards [triv.open_baseSet.mem_nhds hp, h1, h2] with q hq1 hq2 hq3
    exact ⟨hq1, hq2, hq3⟩
  have hVW : V =ᶠ[𝓝 x] W := by
    filter_upwards [hgood] with q hq
    obtain ⟨hqb, hqZ, hqdet⟩ := hq
    have hunit : IsUnit ((Gm q)ᵀ).det := by
      refine isUnit_iff_ne_zero.mpr ?_
      simpa only [Matrix.det_transpose] using hqdet
    have hrepr : (∑ i, ((Module.finBasis ℝ E).coord i
          (triv.continuousLinearMapAt ℝ q (V q)))
          • (Module.finBasis ℝ E) i) = triv.continuousLinearMapAt ℝ q (V q) := by
      simpa only [Module.Basis.coord_apply] using
        (Module.Basis.sum_repr (Module.finBasis ℝ E) (triv.continuousLinearMapAt ℝ q (V q)))
    have hexp : V q
        = ∑ i, ((Module.finBasis ℝ E).coord i
            (triv.continuousLinearMapAt ℝ q (V q))) • Z i q := by
      conv_lhs => rw [← Trivialization.symmL_continuousLinearMapAt (e := triv) (R := ℝ) hqb (V q)]
      conv_lhs => rw [← hrepr, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      exact congrArg (fun w => ((Module.finBasis ℝ E).coord i
        (triv.continuousLinearMapAt ℝ q (V q))) • w) (hqZ i).symm
    have hsys : ((Gm q)ᵀ) *ᵥ (fun i =>
          (Module.finBasis ℝ E).coord i (triv.continuousLinearMapAt ℝ q (V q)))
        = fun j => inner ℝ (V q) (Z j q) := by
      funext j
      rw [Matrix.mulVec_apply_eq_sum]
      conv_rhs => rw [hexp, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.transpose_apply, hGm, Matrix.gram_apply, real_inner_smul_left]
      ring
    have hcfq : cf q = fun i =>
        (Module.finBasis ℝ E).coord i (triv.continuousLinearMapAt ℝ q (V q)) := by
      have h2 := congrArg (fun w => ((Gm q)ᵀ)⁻¹ *ᵥ w) hsys
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec] at h2
      rw [hcf]
      exact h2.symm
    show V q = ∑ i, (cf q) i • Z i q
    simp only [hcfq]
    exact hexp
  have hTVW : (fun z : M => Bundle.TotalSpace.mk' E z (V z))
      =ᶠ[𝓝 x] (fun z : M => Bundle.TotalSpace.mk' E z (W z)) := by
    filter_upwards [hVW] with q hq
    exact congrArg (fun v : TangentSpace I q => Bundle.TotalSpace.mk' E q v) hq
  exact hW.congr_of_eventuallyEq hTVW

/-- **The mdifferentiability of the level-`j` derivative, from the ladder identity and the
smoothness of the jets of the pairing.** -/
theorem dvcFieldMD_of_pair (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (K : ℕ) (U : (Fin K → TField (I := I) (M := M)) → (y : M) → TangentSpace I y) (j : ℕ)
    {V VU : Set M} (hVo : IsOpen V)
    (hPA : dvcFieldPair (I := I) (M := M) g K U j V)
    (hVU : ∀ y ∈ VU, ∀ (l : ℕ) (G : Fin ((K + 1) + l) → TField (I := I) (M := M)),
        (∀ i, SmoothF (G i)) →
          MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun z : M => jetAll g l (K + 1) (pairVec g U) G z) y) :
    dvcFieldMD (I := I) (M := M) g K U j (V ∩ VU) := by
  intro F hF y hy
  obtain ⟨hyV, hyVU⟩ := hy
  choose Z hZs hZeq using fun i : Fin (Module.finrank ℝ E) =>
    Work.Diff.T.exists_global_eventuallyEq_symmL (I := I) (M := M) y
      (Module.finBasis ℝ E i) (mem_chart_source H y)
  have hZs' : ∀ i : Fin (Module.finrank ℝ E), SmoothF (Z i) := fun i => hZs i
  have hpair : ∀ i : Fin (Module.finrank ℝ E), MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun z : M => g.inner z (dvc g K U j F z) (Z i z)) y := by
    intro i
    have h1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z : M => jetAll g j (K + 1) (pairVec g U)
        (dvcTup (I := I) (M := M) K j F (Z i)) z) y :=
      hVU y hyVU j _ (smoothF_dvcTup (I := I) (M := M) hF (hZs' i))
    have h2 : (fun z : M => jetAll g j (K + 1) (pairVec g U)
        (dvcTup (I := I) (M := M) K j F (Z i)) z)
        =ᶠ[𝓝 y] (fun z : M => g.inner z (dvc g K U j F z) (Z i z)) := by
      filter_upwards [hVo.mem_nhds hyV] with z hz
      exact hPA F (Z i) hF (hZs' i) z hz
    exact h1.congr_of_eventuallyEq h2.symm
  have hpair' : ∀ i : Fin (Module.finrank ℝ E), MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun z : M => g.inner z (dvc g K U j F z)
        (chartFrame (I := I) (M := M) y i z)) y := by
    intro i
    refine (hpair i).congr_of_eventuallyEq ?_
    filter_upwards [hZeq i] with z hz
    have hthis : chartFrame (I := I) (M := M) y i z = Z i z := hz.symm
    rw [hthis]
  exact dvcFieldSectionOfChartPairing (I := I) (M := M) g hpair'

/-- **The ladder**: at every level `j` there is an open set `V ∋ x` on which both invariants hold. -/
theorem dvcField_ladder (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (x : M) {K : ℕ}
    (U : (Fin K → TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (hU : JetSmoothOp (I := I) (M := M) g (K + 1) (pairVec (I := I) (M := M) g U) x) :
    ∀ j : ℕ, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      dvcFieldMD (I := I) (M := M) g K U j V ∧
        dvcFieldPair (I := I) (M := M) g K U j V := by
  obtain ⟨VU, hVUo, hVUx, hVU⟩ : ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ (l : ℕ) (G : Fin ((K + 1) + l) → TField (I := I) (M := M)),
        (∀ i, SmoothF (G i)) →
          MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun z : M => jetAll g l (K + 1) (pairVec g U) G z) y := by
    have hUev : ∀ᶠ y in 𝓝 x, ∀ (l : ℕ) (G : Fin ((K + 1) + l) → TField (I := I) (M := M)),
        (∀ i, SmoothF (G i)) →
          MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun z : M => jetAll g l (K + 1) (pairVec g U) G z) y := hU
    obtain ⟨s, hs, hsp⟩ := hUev.exists_mem
    obtain ⟨t, hts, hto, hxt⟩ := _root_.mem_nhds_iff.mp hs
    exact ⟨t, hto, hxt, fun y hy => hsp y (hts hy)⟩
  intro j
  induction j with
  | zero =>
      refine ⟨VU, hVUo, hVUx, ?_, ?_⟩
      · have h := dvcFieldMD_of_pair (I := I) (M := M) hLC g K U 0 isOpen_univ
          (dvcFieldPair_zero (I := I) (M := M) g K U) hVU
        rwa [Set.univ_inter] at h
      · exact dvcFieldPair_mono (I := I) (M := M) (Set.subset_univ VU)
          (dvcFieldPair_zero (I := I) (M := M) g K U)
  | succ j ih =>
      obtain ⟨V, hVo, hVx, hMD, hPA⟩ := ih
      have hsucc := dvcFieldPair_succ (I := I) (M := M) hLC g U j hVo hMD hPA
      refine ⟨V ∩ VU, hVo.inter hVUo, ⟨hVx, hVUx⟩, ?_, ?_⟩
      · exact dvcFieldMD_of_pair (I := I) (M := M) hLC g K U (j + 1) hVo hsucc hVU
      · exact dvcFieldPair_mono (I := I) (M := M) Set.inter_subset_left hsucc

end Ladder

theorem dvcFieldSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) {K : ℕ}
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (hU : Work.Diff.EXT.JetSmoothOp (I := I) (M := M) g (K + 1)
      (Work.Diff.EXT.evolX.pairVec (I := I) (M := M) g U) x)
    (c : ℕ) (F : Fin (K + c) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ i, Work.Diff.EXT.SmoothF (I := I) (M := M) (F i)) :
    Filter.Eventually (fun y : M => MDifferentiableAt I I.tangent
      (fun z : M => Bundle.TotalSpace.mk' E z
        (Work.Diff.EXT.evolX.dvc (I := I) (M := M) g K U c F z)) y) (nhds x) := by
  obtain ⟨V, hVo, hVx, hMD, -⟩ := dvcField_ladder (I := I) (M := M) hLC g x U hU c
  exact Filter.mem_of_superset (hVo.mem_nhds hVx) (fun y hy => hMD F hF y hy)

end Work.Diff.EXT.evolX
