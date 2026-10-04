/-
# Layer D: the base-generalised Galerkin machinery

The Galerkin scheme of Layer D evolves the metric `u = g₀ + genMap D ε c` by the ODE
`u' = J ρ ε (P u)`, where `P` is the DeTurck operator with reference metric `g₀` and `J ρ ε` is the
Friedrichs mollifier.  The *corrected* scheme — which is what the `ε`-uniform energy estimate
needs — evolves the **same** metric by `u' = J ρ ε (P (J ρ ε u))`: the operator `P` is evaluated at
the *smoothed* metric.

Writing `a₀ := J ρ ε g₀` and using that `J ρ ε` maps the symmetric Galerkin space to itself, the
smoothed metric is `J ρ ε (g₀ + genMap D ε c) = a₀ + genMap D ε (Λ c)` for an affine map `Λ`; hence
the corrected vector field has the shape

  `Ψ(c) = (1/2) · jFamilyCoeff D ρ ε (P (a₀ + genMap D ε d))`,   `d = Λ c`,

i.e. the *same* concrete chart expression as in `Work.Diff.STE.D.psiConc`, but with the affine
foreground `g₀ + genMap D ε c` replaced by `a₀ + genMap D ε c`.

This module sets up that base-generalised version of the machinery: the affine foreground `fore`,
the positivity predicate `IsPosF`, the jet pair `jetPB`, the localised component `FzB`, the
directional integrand `UfunB` and the concrete vector field `psiConcB`.  The analytic lemmas about
them (the second-order Taylor bound, the Lipschitz bound, the continuity of the localised
component and of the directional integrand, and the positivity ball) are proved in the sibling
modules.

The mathematical content of *this* module is entirely structural: the affinity of the chart `2`-jet
of `fore a₀ D ε c` in the coefficients (`chartJetOf_fore_affine`, from which `jetPB_eq_dir` and the
smoothness of the jet pair follow), the membership of the jet pair in the smoothness locus of the
DeTurck operator when the foreground is positive definite, and the identification of the localised
component with `weight · LamFun (pPhiFun (jet pair))`.
-/
import Mathlib
import Submission.Work.Diff.STE.D.psi.abs_Fz_sub_le
import Submission.Work.Diff.STE.D.psi.JetAffine
import Submission.Work.Diff.STE.D.psi.abs_pref_le
import Submission.Work.Diff.STE.D.psi.abs_coord_factor_le
import Submission.Work.Diff.STE.D.psi.chartJetOf_jSym_bound
import Submission.Work.Diff.STE.D.psi.contDiffOn_secChartVal_chart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open Classical
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D.Base

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M} {ε : ℝ}

noncomputable section


/-! ## 0. Support bookkeeping -/

/-- The half-open cube `(-1/2, 1/2]ⁿ`, the fundamental domain of the localised components. -/
abbrev halfCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))

/-- The support of a sum is contained in any set containing both supports. -/
lemma support_add_subset {β : Type*} {T : Set β} {f g : β → ℝ}
    (hf : Function.support f ⊆ T) (hg : Function.support g ⊆ T) :
    Function.support (f + g) ⊆ T := by
  intro x hx
  by_contra hxT
  have h1 : f x = 0 := by by_contra h; exact hxT (hf h)
  have h2 : g x = 0 := by by_contra h; exact hxT (hg h)
  exact hx (by rw [Pi.add_apply, h1, h2, add_zero])

/-- The support of a difference is contained in any set containing both supports. -/
lemma support_sub_subset₂ {β : Type*} {T : Set β} {f g : β → ℝ}
    (hf : Function.support f ⊆ T) (hg : Function.support g ⊆ T) :
    Function.support (f - g) ⊆ T := by
  intro x hx
  by_contra hxT
  have h1 : f x = 0 := by by_contra h; exact hxT (hf h)
  have h2 : g x = 0 := by by_contra h; exact hxT (hg h)
  exact hx (by rw [Pi.sub_apply, h1, h2, sub_zero])

/-- The support of `f - g - h` is contained in any set containing the three supports. -/
lemma support_sub_subset {β : Type*} {T : Set β} {f g h : β → ℝ}
    (hf : Function.support f ⊆ T) (hg : Function.support g ⊆ T) (hh : Function.support h ⊆ T) :
    Function.support (fun x => f x - g x - h x) ⊆ T := by
  intro x hx
  by_contra hxT
  have h1 : f x = 0 := by by_contra h; exact hxT (hf h)
  have h2 : g x = 0 := by by_contra h; exact hxT (hg h)
  have h3 : h x = 0 := by by_contra h; exact hxT (hh h)
  exact hx (show f x - g x - h x = 0 by rw [h1, h2, h3]; ring)

/-- The support of a finite pointwise sum is contained in any set containing all the supports. -/
lemma support_finset_sum_subset {ι β : Type*} (s : Finset ι) {T : Set β} (f : ι → β → ℝ)
    (h : ∀ i ∈ s, Function.support (f i) ⊆ T) :
    Function.support (fun x => ∑ i ∈ s, f i x) ⊆ T := by
  intro x hx
  by_contra hxT
  refine hx (Finset.sum_eq_zero fun i hi => ?_)
  by_contra hne
  exact hxT (h i hi hne)

/-! ## 1. The affine foreground with an arbitrary symmetric base -/

/-- **The pointwise sum of two sections.** -/
def addForm (a h : Bil (I := I) (M := M)) : Bil (I := I) (M := M) := fun x => a x + h x

@[simp] lemma addForm_apply (a h : Bil (I := I) (M := M)) (x : M) (u v : TangentSpace I x) :
    addForm (I := I) (M := M) a h x u v = a x u v + h x u v := rfl

lemma addForm_eq_add (a h : Bil (I := I) (M := M)) :
    addForm (I := I) (M := M) a h = a + h := rfl

/-- **The affine foreground** `a₀ + genMap D ε c` with an arbitrary base section `a₀`. -/
def fore (a₀ : Bil (I := I) (M := M)) (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ε : ℝ) (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Bil (I := I) (M := M) :=
  addForm (I := I) (M := M) a₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)

@[simp] lemma fore_apply (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (x : M) (u v : TangentSpace I x) :
    fore (I := I) (M := M) a₀ D ε c x u v
      = a₀ x u v + Work.Diff.STE.D.genMap (I := I) (M := M) D ε c x u v := rfl

lemma fore_eq_add (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    fore (I := I) (M := M) a₀ D ε c
      = a₀ + Work.Diff.STE.D.genMap (I := I) (M := M) D ε c := rfl

/-- **Positivity of the foreground.** -/
def IsPosF (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
    0 < fore (I := I) (M := M) a₀ D ε c x v v

/-- The foreground of a symmetric base is symmetric. -/
lemma isSymm_fore (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (hs : IsSymm (I := I) a₀) :
    IsSymm (I := I) (fore (I := I) (M := M) a₀ D ε c) := by
  intro x u v
  simp only [fore_apply]
  rw [hs x u v, Work.Diff.STE.D.isSymm_genMap (I := I) (M := M) D ε c x u v]

/-- The foreground has smooth chart data as soon as the base does. -/
lemma chartData_fore (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (ha₀ : ChartData (I := I) (M := M) a₀) :
    ChartData (I := I) (M := M) (fore (I := I) (M := M) a₀ D ε c) :=
  Work.Diff.STE.D.GenMap.chartData_add (I := I) (M := M) ha₀
    (Work.Diff.STE.D.ChartData_genMap (I := I) (M := M) D ε c)

/-! ## 2. Affinity of the chart jet of the foreground -/

/-- **The chart `2`-jet of the affine foreground is affine in the coefficients.** -/
theorem chartJetOf_fore_affine
    (a₀ : Bil (I := I) (M := M))
    (ha₀ : ChartData (I := I) (M := M) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    chartJetOf (I := I) (M := M) (fore (I := I) (M := M) a₀ D ε c) x₀ y
      = chartJetOf (I := I) (M := M) a₀ x₀ y
        + ∑ z, c z • chartJetOf (I := I) (M := M)
            (jSym (I := I) (M := M) D ε z) x₀ y := by
  classical
  -- the spanning vectors of the Galerkin family have smooth chart data
  have hjFamily : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ChartData (I := I) (M := M) (Work.Diff.STE.B3.jFamily (I := I) (M := M) D ε z) := by
    intro z
    simpa only [Work.Diff.STE.B3.jFamily] using
      GenMap.jVec_chartData (I := I) (M := M) D ε z.1 z.2.1 z.2.2.1 z.2.2.2
  have hjSym : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ChartData (I := I) (M := M) (jSym (I := I) (M := M) D ε z) := by
    intro z
    rw [jSym]
    exact GenMap.chartData_add (I := I) (M := M) (hjFamily z)
      (hjFamily (idxSwap (E := E) (ι₀ := ι₀) ε z))
  have hsummand : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ChartData (I := I) (M := M) (c z • jSym (I := I) (M := M) D ε z) :=
    fun z => GenMap.chartData_smul (I := I) (M := M) (c z) (hjSym z)
  have hsum : ∀ t : Finset (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε),
      chartJetOf (I := I) (M := M)
          (∑ z ∈ t, c z • jSym (I := I) (M := M) D ε z) x₀ y
        = ∑ z ∈ t, c z • chartJetOf (I := I) (M := M)
            (jSym (I := I) (M := M) D ε z) x₀ y := by
    intro t
    induction t using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        exact Work.Diff.STE.D.psi.chartJetOf_zero (I := I) (M := M) x₀ y
    | insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [Work.Diff.STE.D.psi.chartJetOf_add_of_chartData (I := I) (M := M) x₀ hy
          (c a • jSym (I := I) (M := M) D ε a)
          (∑ z ∈ t, c z • jSym (I := I) (M := M) D ε z)
          (hsummand a)
          (GenMap.chartData_finset_sum (I := I) (M := M) t
            (fun z => c z • jSym (I := I) (M := M) D ε z) (fun z _ => hsummand z))]
        rw [Work.Diff.STE.D.psi.chartJetOf_smul_of_chartData (I := I) (M := M) x₀ hy (c a)
          (jSym (I := I) (M := M) D ε a) (hjSym a), ih]
  -- assembly
  rw [fore_eq_add (I := I) (M := M) a₀ D ε c]
  rw [Work.Diff.STE.D.psi.chartJetOf_add_of_chartData (I := I) (M := M) x₀ hy (a₀)
    (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c) ha₀
    (Work.Diff.STE.D.ChartData_genMap (I := I) (M := M) D ε c)]
  rw [show Work.Diff.STE.D.genMap (I := I) (M := M) D ε c
      = ∑ z ∈ Finset.univ, c z • jSym (I := I) (M := M) D ε z from rfl]
  rw [hsum Finset.univ]

/-! ## 3. The base-generalised jet pair -/

/-- **The pair of spatial `2`-jets** of the background metric `g₀` and of the affine foreground
`a₀ + genMap D ε c`. -/
noncomputable def jetPB (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) (y : E) :
    Work.Diff.STE.deTurck.JetPair (E := E) :=
  (chartJetOf (I := I) (M := M) g₀.inner x₀ y,
   chartJetOf (I := I) (M := M) (fore (I := I) (M := M) a₀ D ε c) x₀ y)

@[simp] lemma jetPB_fst (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) (y : E) :
    (jetPB (I := I) (M := M) a₀ D ε x₀ c y).1
      = chartJetOf (I := I) (M := M) g₀.inner x₀ y := rfl

@[simp] lemma jetPB_snd (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) (y : E) :
    (jetPB (I := I) (M := M) a₀ D ε x₀ c y).2
      = chartJetOf (I := I) (M := M)
          (fore (I := I) (M := M) a₀ D ε c) x₀ y := rfl

/-- **The jet pair in the form "constant pair plus linear combination of the direction vectors".** -/
theorem jetPB_eq_dir (a₀ : Bil (I := I) (M := M))
    (ha₀ : ChartData (I := I) (M := M) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    jetPB (I := I) (M := M) a₀ D ε x₀ c y =
      (chartJetOf (I := I) (M := M) g₀.inner x₀ y,
       chartJetOf (I := I) (M := M) a₀ x₀ y)
      + ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          c z • Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε x₀ z y := by
  unfold jetPB Work.Diff.STE.D.jetDir
  rw [chartJetOf_fore_affine (I := I) (M := M) a₀ ha₀ D ε x₀ c hy]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_mk, Work.Diff.STE.D.psi.smul_zero_tri,
      Finset.sum_const_zero, add_zero]
  · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_mk, Finset.sum_apply, Pi.smul_apply,
      Pi.zero_apply, smul_zero, zero_add]

/-- **The jet pair is affine in the coefficients**: its Fréchet derivative is the constant linear
part `jetDirLin`. -/
lemma hasFDerivAt_jetPB (a₀ : Bil (I := I) (M := M))
    (ha₀ : ChartData (I := I) (M := M) a₀)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    HasFDerivAt (fun c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
        jetPB (I := I) (M := M) a₀ D ε x₀ c y)
      (Work.Diff.STE.D.psi.jetDirLin (I := I) (M := M) g₀ D ε x₀ y) c₀ := by
  have hconst : HasFDerivAt
      (fun _ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
        (chartJetOf (I := I) (M := M) g₀.inner x₀ y,
         chartJetOf (I := I) (M := M) a₀ x₀ y))
      (0 : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) →L[ℝ]
        Work.Diff.STE.deTurck.JetPair (E := E)) c₀ :=
    hasFDerivAt_const _ _
  have hlin : HasFDerivAt
      (fun c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
        ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          c z • Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε x₀ z y)
      (Work.Diff.STE.D.psi.jetDirLin (I := I) (M := M) g₀ D ε x₀ y) c₀ := by
    have h := (Work.Diff.STE.D.psi.jetDirLin (I := I) (M := M) g₀ D ε x₀ y :
      (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) →L[ℝ]
        Work.Diff.STE.deTurck.JetPair (E := E)).hasFDerivAt (x := c₀)
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun c => ?_)
    simp only [Work.Diff.STE.D.psi.jetDirLin_apply]
  have hsum := (hconst.add hlin).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun c =>
      (jetPB_eq_dir (I := I) (M := M) a₀ ha₀ D ε x₀ c hy))
  simpa only [zero_add] using hsum

/-! ## 4. The joint chart DeTurck expression and its domain -/

/-- **The joint chart DeTurck expression** `(c, y) ↦ pPhiFun (jetPB a₀ D ε x₀ c (flatToE x₀ y))`. -/
noncomputable def PhiB (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) :
    (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
        (Fin (Module.finrank ℝ E) → ℝ) → Work.Diff.EXT.MatE (E := E) :=
  fun q => Work.Diff.STE.D.pPhiFun (E := E)
    (jetPB (I := I) (M := M) a₀ D ε x₀ q.1
      (Work.Diff.STE.flatToE (I := I) x₀ q.2))

/-- **The domain of the joint chart DeTurck expression.** -/
def DomB (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) :
    Set ((Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ×
        (Fin (Module.finrank ℝ E) → ℝ)) :=
  {q | Work.Diff.STE.flatToE (I := I) x₀ q.2 ∈ (extChartAt I x₀).target} ∩
    (fun q => jetPB (I := I) (M := M) a₀ D ε x₀ q.1
      (Work.Diff.STE.flatToE (I := I) x₀ q.2)) ⁻¹'
      Work.Diff.STE.deTurck.pPhiDom (E := E)

/-- **The jet pair of a positive definite symmetric foreground lies in the smoothness locus of the
DeTurck operator.** -/
lemma jetPB_mem_pPhiDom (hg : ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M)
    (a₀ : Bil (I := I) (M := M)) (hs : IsSymm (I := I) a₀)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) {y : Fin (Module.finrank ℝ E) → ℝ}
    (hpos : IsPosF (I := I) (M := M) a₀ D ε c)
    (hy : Work.Diff.STE.flatToE (I := I) x₀ y ∈ (extChartAt I x₀).target) :
    jetPB (I := I) (M := M) a₀ D ε x₀ c (Work.Diff.STE.flatToE (I := I) x₀ y)
      ∈ Work.Diff.STE.deTurck.pPhiDom (E := E) := by
  have hsym : IsSymm (I := I) (fore (I := I) (M := M) a₀ D ε c) := isSymm_fore a₀ D ε c hs
  constructor
  · have hsrc : (extChartAt I x₀).symm (Work.Diff.STE.flatToE (I := I) x₀ y)
        ∈ (chartAt H x₀).source := by
      rw [← extChartAt_source (I := I) x₀]
      exact PartialEquiv.map_target (extChartAt I x₀) hy
    have hpd : (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ x₀
        ((extChartAt I x₀).symm (Work.Diff.STE.flatToE (I := I) x₀ y)))).PosDef :=
      Work.Diff.STE.deTurck.posDef_gmat (I := I) g₀ x₀ hsrc
    rw [jetPB_fst (I := I) (M := M) a₀ D ε x₀ c (Work.Diff.STE.flatToE (I := I) x₀ y),
      Work.Diff.STE.D.psi.chartJetOf_fst_inner (I := I) (M := M)]
    exact ne_of_gt (Matrix.PosDef.det_pos hpd)
  · rw [jetPB_snd (I := I) (M := M) a₀ D ε x₀ c (Work.Diff.STE.flatToE (I := I) x₀ y),
      Work.Diff.STE.D.psi.chartJetOf_fst (I := I) (M := M)]
    exact ne_of_gt (Work.Diff.STE.D.psi.chartMatOf_det_pos_of_posDef (I := I) (M := M) _ x₀
      hsym hpos hy)

noncomputable def FzB (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun c y => D.R z.1 (secChart (I := I) (M := M) g₀
      (fore (I := I) (M := M) a₀ D ε c) (D.x₀ z.1))
    z.2.1 z.2.2.1 y

/-- **The directional integrand**: the derivative of the chart DeTurck expression in the direction
of the `z'`-th coefficient, with the weights of the localised component. -/
noncomputable def UfunB (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun c₀ y => D.psi z.1 y * Real.sqrt (D.dens z.1 y) *
    ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
      coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j (D.e z.1 z.2.1 (D.pt z.1 y))
        * coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k (D.e z.1 z.2.2.1 (D.pt z.1 y))
        * (Work.Diff.STE.D.pPhiFunD (E := E)
              (jetPB (I := I) (M := M) a₀ D ε (D.x₀ z.1) c₀
                (Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y))
              (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε (D.x₀ z.1) z'
                (Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y))) j k

@[simp] lemma FzB_apply (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (y : Fin (Module.finrank ℝ E) → ℝ) :
    FzB (I := I) (M := M) a₀ D ε z c y =
      D.R z.1 (secChart (I := I) (M := M) g₀
        (fore (I := I) (M := M) a₀ D ε c) (D.x₀ z.1)) z.2.1 z.2.2.1 y := rfl

/-- **The localised component as weight times the weight functional.** -/
lemma FzB_eq_LamFun (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    {y : Fin (Module.finrank ℝ E) → ℝ}
    (hy : Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y ∈ (extChartAt I (D.x₀ z.1)).target) :
    FzB (I := I) (M := M) a₀ D ε z c y =
      (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
        Work.Diff.STE.D.psi.LamFun (I := I) (M := M) D ε z y
          (Work.Diff.STE.D.pPhiFun (E := E)
            (jetPB (I := I) (M := M) a₀ D ε (D.x₀ z.1) c
              (Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y))) := by
  have hpt : (extChartAt I (D.x₀ z.1)) (D.pt z.1 y)
      = Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y :=
    (extChartAt I (D.x₀ z.1)).right_inv hy
  simp only [FzB, Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat,
    Work.Diff.STE.D.secChart_apply, Work.Diff.STE.D.secChartVal, hpt,
    Work.Diff.STE.D.pPhiJetOf_apply, Work.Diff.STE.D.pPhiFun,
    Work.Diff.STE.D.psi.LamFun_apply, jetPB]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The directional integrand as weight times the weight functional.** -/
lemma UfunB_eq_LamFun (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (y : Fin (Module.finrank ℝ E) → ℝ) :
    UfunB (I := I) (M := M) a₀ D ε z z' c y =
      (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
        Work.Diff.STE.D.psi.LamFun (I := I) (M := M) D ε z y
          (Work.Diff.STE.D.pPhiFunD (E := E)
            (jetPB (I := I) (M := M) a₀ D ε (D.x₀ z.1) c
              (Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y))
            (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε (D.x₀ z.1) z'
              (Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y))) := by
  rw [UfunB, Work.Diff.STE.D.psi.LamFun_apply]

/-- The support of the localised component lies in the half-open cube. -/
lemma support_FzB_subset (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Function.support (FzB (I := I) (M := M) a₀ D ε z c) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) := by
  rw [Function.support_subset_iff]
  intro y hy
  rw [Set.mem_pi]
  intro j _
  rw [Set.mem_Ioc]
  have hχ : D.χ z.1 y ≠ 0 := by
    intro h0
    exact hy (by
      simp only [FzB, Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.psi, h0, zero_mul])
  have hmem := D.hχsupp z.1 hχ
  have hIoo := Set.mem_pi.mp hmem j (Set.mem_univ j)
  rw [Set.mem_Ioo] at hIoo
  exact ⟨hIoo.1, le_of_lt hIoo.2⟩

/-- The support of the directional integrand lies in the half-open cube. -/
lemma support_UfunB_subset (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Function.support (UfunB (I := I) (M := M) a₀ D ε z z' c) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) := by
  rw [Function.support_subset_iff]
  intro y hy
  rw [Set.mem_pi]
  intro j _
  rw [Set.mem_Ioc]
  have hψ : D.psi z.1 y ≠ 0 := by
    intro h0
    exact hy (by simp only [UfunB, h0, zero_mul])
  have hχ : D.χ z.1 y ≠ 0 := fun h0 =>
    hψ (by simp only [Work.Diff.STE.B3Data.psi, h0, zero_mul])
  have hmem := D.hχsupp z.1 hχ
  have hIoo := Set.mem_pi.mp hmem j (Set.mem_univ j)
  rw [Set.mem_Ioo] at hIoo
  exact ⟨hIoo.1, le_of_lt hIoo.2⟩

/-! ## 6. The concrete base-generalised Galerkin vector field -/

/-- **The concrete base-generalised vector field** attached to the data: for every coefficient
family `c`,

  `psiConcB c z = (1/2) · jFamilyCoeff D ρ ε (secChart g₀ (a₀ + genMap D ε c) (x₀ z.1)) z`. -/
noncomputable def psiConcB (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ :=
  fun z => (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε
    (secChart (I := I) (M := M) g₀ (fore (I := I) (M := M) a₀ D ε c) (D.x₀ z.1)) z

lemma psiConcB_apply (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    psiConcB (I := I) (M := M) a₀ D ρ ε c z =
      (1 / 2 : ℝ) * Work.Diff.STE.B3.jFamilyCoeff D ρ ε
        (secChart (I := I) (M := M) g₀ (fore (I := I) (M := M) a₀ D ε c) (D.x₀ z.1)) z :=
  rfl

end

end Work.Diff.STE.D.Base
