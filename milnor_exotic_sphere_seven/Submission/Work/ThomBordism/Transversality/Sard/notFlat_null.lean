import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Strat
import Submission.Work.ThomBordism.Transversality.Sard.flowBox
import Submission.Work.ThomBordism.Transversality.Sard.prodForm_null
import Submission.Work.ThomBordism.Transversality.Sard.volume_image_null_of_local
import Submission.Work.ThomBordism.Transversality.Sard.isCriticalPoint_comp
import Submission.Work.ThomBordism.Transversality.Sard.scalarPartial

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The non-flat step of rectangular Sard's theorem

This file proves `Work.ThomBordism.Transversality.Sard.notFlat_null` (`Sard.NotFlatStep`): the image
of the critical set of a `C^∞` map `ℝ^{n+1} → ℝ^{m+1}` on the piece where the derivative does not
vanish is null, given Sard's theorem for `C^∞` maps `ℝⁿ → ℝᵐ`.

The proof is the classical straightening + Fubini argument, in coordinates:

* at a point `x` with `df_x ≠ 0` pick a vector `v` and a target coordinate `j` with
  `((df_x) v) j ≠ 0`; then `σ := fun y => (f y) j` has `dσ_x ≠ 0` (as `dσ_x = (proj j) ∘ df_x`);
* the localized flow box `Sard.flowBoxOn` straightens `σ` (this file, from `Sard/flowBox.lean`);
* in the chart, the map becomes a *product-form* map `(t, u) ↦ (t, γ (t,u))` after rotating the
  target so that the `j`-th coordinate comes first; the localized Fubini step
  `Sard.prodForm_nullOn` (this file, from `Sard/prodForm_null.lean`) then shows that the image of
  its critical set is null, and a linear equivalence (a coordinate permutation) transports nullity
  back to `ℝ^{m+1}`.

## Main results

* `Sard.flowBoxOn` — the flow box of a submersion with smoothness assumed only on an open set;
* `Sard.prodForm_nullOn` — the Fubini step with smoothness assumed only on an open set;
* `Sard.notFlat_null` — the non-flat step.
-/

open scoped ContDiff MeasureTheory Topology
open MeasureTheory Set Filter

set_option linter.style.haveILetI false

namespace Work.ThomBordism.Transversality.Sard

open Work.ThomBordism.Transversality (CInf CInfOn CInfAt IsCriticalPoint SardEuclid SardEuclidOn)

noncomputable section

/-! ## Transporting null sets along a linear equivalence -/

/-- **A continuous linear equivalence maps null sets to null sets.**  If `s ⊆ F` has measure zero,
then so does `e ⁻¹' s ⊆ E`, for `e : E ≃L[ℝ] F` between finite-dimensional real normed spaces whose
`volume` is a Haar measure. -/
theorem volume_preimage_eq_zero_of_continuousLinearEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasureSpace F] [BorelSpace F]
    [MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure E)]
    [MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure F)]
    (e : E ≃L[ℝ] F) {s : Set F} (hs : (volume : Measure F) s = 0) :
    (volume : Measure E) (e ⁻¹' s) = 0 := by
  haveI : MeasureTheory.Measure.IsAddHaarMeasure ((volume : Measure E).map e) :=
    ContinuousLinearEquiv.isAddHaarMeasure_map e (volume : Measure E)
  have hsmul : (volume : Measure E).map e =
      ((volume : Measure E).map e).addHaarScalarFactor (volume : Measure F) •
        (volume : Measure F) := Measure.isAddLeftInvariant_eq_smul _ _
  obtain ⟨t, hst, ht_meas, ht⟩ := exists_measurable_superset_of_null hs
  rw [← nonpos_iff_eq_zero]
  calc (volume : Measure E) (e ⁻¹' s)
      ≤ (volume : Measure E) (e ⁻¹' t) := measure_mono (preimage_mono hst)
    _ = ((volume : Measure E).map e) t := by rw [Measure.map_apply e.continuous.measurable ht_meas]
    _ = 0 := by rw [hsmul, Measure.smul_apply, ht]; simp

/-! ## The coordinate rotation of the target -/

/-- The continuous linear map `z ↦ (z (i.succAbove t))_t : ℝ^{m+1} → ℝ^m`, i.e. the coordinates of
`z` other than the `j`-th one, indexed by `Fin m` through `Fin.succAbove`. -/
def restrictCoords (m : ℕ) (j : Fin (m+1)) :
    EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  ((EuclideanSpace.equiv (Fin m) ℝ).symm : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)) ∘L
    (ContinuousLinearMap.pi fun t : Fin m => EuclideanSpace.proj (j.succAbove t))

theorem restrictCoords_apply (m : ℕ) (j : Fin (m+1)) (z : EuclideanSpace ℝ (Fin (m+1)))
    (t : Fin m) : restrictCoords m j z t = z (j.succAbove t) := by
  rw [restrictCoords]
  simp

/-- The continuous linear map `z ↦ (z j, (z (j.succAbove t))_t)` moving the `j`-th coordinate of
`ℝ^{m+1}` to the front. -/
def rotateFirst (m : ℕ) (j : Fin (m+1)) :
    EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)) :=
  (EuclideanSpace.proj j).prod (restrictCoords m j)

theorem rotateFirst_apply (m : ℕ) (j : Fin (m+1)) (z : EuclideanSpace ℝ (Fin (m+1))) :
    rotateFirst m j z = (z j, restrictCoords m j z) := rfl

theorem rotateFirst_injective (m : ℕ) (j : Fin (m+1)) :
    Function.Injective (rotateFirst m j) := by
  intro z z' h
  have h1 : z j = z' j := congrArg Prod.fst h
  have h2 : restrictCoords m j z = restrictCoords m j z' := congrArg Prod.snd h
  have h2' : ∀ t : Fin m, z (j.succAbove t) = z' (j.succAbove t) := by
    intro t
    have := congrArg (fun w : EuclideanSpace ℝ (Fin m) => w t) h2
    simpa [restrictCoords_apply] using this
  ext i
  by_cases hi : i = j
  · subst hi; exact h1
  · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hi
    exact h2' t

theorem finrank_rotate (m : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+1)))
      = Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin m)) := by
  rw [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin,
    finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin m), Fintype.card_fin]
  simp only [Module.finrank_self]
  omega

/-- The coordinate rotation `z ↦ (z j, (z (i.succAbove t))_t)` as a continuous linear equivalence. -/
def rotateEquiv (m : ℕ) (j : Fin (m+1)) :
    EuclideanSpace ℝ (Fin (m+1)) ≃L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)) :=
  ContinuousLinearEquiv.ofBijective (rotateFirst m j)
    (LinearMap.ker_eq_bot.mpr (rotateFirst_injective m j))
    (LinearMap.range_eq_top.mpr ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_rotate m)).mp (rotateFirst_injective m j)))

theorem rotateEquiv_apply (m : ℕ) (j : Fin (m+1)) (z : EuclideanSpace ℝ (Fin (m+1))) :
    rotateEquiv m j z = (z j, restrictCoords m j z) := rfl

/-! ## Derivatives of the coordinate maps -/

theorem fderiv_coord {n m : ℕ} {f : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (m+1))}
    {y : EuclideanSpace ℝ (Fin (n+1))} (hf : DifferentiableAt ℝ f y) (j : Fin (m+1)) :
    fderiv ℝ (fun y => f y j) y = (EuclideanSpace.proj j).comp (fderiv ℝ f y) := by
  have h1 : HasFDerivAt f (fderiv ℝ f y) y := hf.hasFDerivAt
  have h2 := ((EuclideanSpace.proj j :
    EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ)).hasFDerivAt.comp y h1
  simpa only [EuclideanSpace.coe_proj, Function.comp_def] using h2.fderiv

theorem fderiv_restrictCoords {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (m+1))}
    {y : EuclideanSpace ℝ (Fin (n+1))} (hf : DifferentiableAt ℝ f y) (j : Fin (m+1)) :
    fderiv ℝ (fun y => restrictCoords m j (f y)) y
      = (restrictCoords m j).comp (fderiv ℝ f y) :=
  (((restrictCoords m j).hasFDerivAt.comp y hf.hasFDerivAt)).fderiv

/-- The derivative of the rotated map is the rotation of the derivative: this is how criticality is
transported through the coordinate rotation of the target. -/
theorem fderiv_rotate_comp {n m : ℕ}
    {A : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (m+1))}
    {y : EuclideanSpace ℝ (Fin (n+1))} (hA : DifferentiableAt ℝ A y) (j : Fin (m+1)) :
    fderiv ℝ (fun y => rotateFirst m j (A y)) y
      = (rotateFirst m j).comp (fderiv ℝ A y) :=
  ((rotateFirst m j).hasFDerivAt.comp y hA.hasFDerivAt).fderiv

/-! ## The product form of the critical set -/

/-- **The critical points of a product-form map are the critical points of its slices**, in the
localized form needed here: only differentiability of `γ` at `p` is used. -/
theorem isCriticalPoint_prodForm_of_hasFDerivAt {n m : ℕ}
    {γ : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {p : ℝ × EuclideanSpace ℝ (Fin n)}
    (hγ : HasFDerivAt γ (fderiv ℝ γ p) p) :
    IsCriticalPoint (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, γ p)) p ↔
      IsCriticalPoint (fun x : EuclideanSpace ℝ (Fin n) => γ (p.1, x)) p.2 := by
  have h1 : fderiv ℝ (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, γ p)) p
      = (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n))).prod (fderiv ℝ γ p) :=
    (hasFDerivAt_fst.prodMk hγ).fderiv
  have h2 : fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => γ (p.1, x)) p.2
      = (fderiv ℝ γ p).comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n))) :=
    (hγ.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)).fderiv
  rw [IsCriticalPoint, IsCriticalPoint, h1, h2, surjective_fst_prod_iff]

/-- The same statement in the form in which the flow-box argument uses it: for `γ` differentiable at
every point of an open set, the critical set of the product-form map is the union of the critical
sets of its slices. -/
theorem isCriticalPoint_prodForm_iff_of_contDiffOn
    {n m : ℕ} {Ω : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    {γ : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} (hγ : CInfOn γ Ω)
    {p : ℝ × EuclideanSpace ℝ (Fin n)} (hp : p ∈ Ω) :
    IsCriticalPoint (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, γ p)) p ↔
      IsCriticalPoint (fun x : EuclideanSpace ℝ (Fin n) => γ (p.1, x)) p.2 :=
  isCriticalPoint_prodForm_of_hasFDerivAt
    ((hγ.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt

/-! ## The flow box of a submersion, localized -/

/-- **The flow box theorem, with smoothness assumed only on an open set.**  Let `σ : ℝ^{n+1} → ℝ`
be `C^∞` at every point of an open set `V ∋ x` with `dσ_x ≠ 0`.  Then `σ` is, near `x`, the first
coordinate of a `C^∞` chart: there are open sets `N ∋ x`, `N ⊆ V` and `Ω ∋ (σ x, 0)` in
`ℝ × ker (dσ_x)` and a `C^∞` surjection `g : Ω → N` with `σ (g u) = u.1` and `g (σ x, 0) = x`.

This is the localized form of `Sard.flowBox` (which assumes `σ` smooth everywhere) needed when `σ`
is only known to be smooth on a neighbourhood of the point of interest; it is the same proof as
`Sard.exists_levelSet_param_smooth` with the level coordinate kept. -/
theorem flowBoxOn {n : ℕ}
    {V : Set (EuclideanSpace ℝ (Fin (n+1)))} (hV : IsOpen V)
    {σ : EuclideanSpace ℝ (Fin (n+1)) → ℝ}
    (hσ : ∀ y ∈ V, CInfAt σ y)
    {x : EuclideanSpace ℝ (Fin (n+1))} (hxV : x ∈ V) (hσ' : fderiv ℝ σ x ≠ 0) :
    ∃ (N : Set (EuclideanSpace ℝ (Fin (n+1)))) (Ω : Set (ℝ × ↥((fderiv ℝ σ x).ker)))
      (g : ℝ × ↥((fderiv ℝ σ x).ker) → EuclideanSpace ℝ (Fin (n+1))),
      IsOpen N ∧ x ∈ N ∧ N ⊆ V ∧ IsOpen Ω ∧ (σ x, 0) ∈ Ω ∧ g (σ x, 0) = x ∧
        CInfOn g Ω ∧ (∀ u ∈ Ω, g u ∈ N) ∧ (∀ u ∈ Ω, σ (g u) = u.1) ∧
        (∀ y ∈ N, ∃ u ∈ Ω, g u = y) := by
  classical
  have hstrict : HasStrictFDerivAt σ (fderiv ℝ σ x) x := (hσ x hxV).hasStrictFDerivAt (by simp)
  have hrange : (fderiv ℝ σ x).range = ⊤ := by
    obtain ⟨v₀, hv₀⟩ : ∃ v, fderiv ℝ σ x v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hσ' (ContinuousLinearMap.ext hc)
    rw [LinearMap.range_eq_top]
    intro t
    refine ⟨(t / fderiv ℝ σ x v₀) • v₀, ?_⟩
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ t hv₀
  have hker : (fderiv ℝ σ x).ker.ClosedComplemented :=
    ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range _
  let D := HasStrictFDerivAt.implicitFunctionDataOfComplemented σ (fderiv ℝ σ x) hstrict hrange hker
  let e := D.toOpenPartialHomeomorph
  let p : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] ↥(fderiv ℝ σ x).ker := Classical.choose hker
  have he_coe : (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) = D.prodFun := rfl
  have hprod : D.prodFun = fun y => (σ y, p (y - x)) := by
    funext y
    simp only [ImplicitFunctionData.prodFun_apply]
    rfl
  have he_eq : ∀ y, e y = (σ y, p (y - x)) := fun y => by
    rw [show e y = D.prodFun y from congrFun he_coe y, hprod]
  have hfst : ∀ z : EuclideanSpace ℝ (Fin (n+1)), (e z).1 = σ z := fun z => by rw [he_eq]
  have hex : e x = (σ x, 0) := by rw [he_eq]; simp
  have hxsrc : x ∈ e.source := D.pt_mem_toOpenPartialHomeomorph_source
  -- `e` is `C^∞` on `V`, because `σ` is
  have hpsnd : ∀ y, ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin (n+1)) => p (z - x)) y :=
    fun y => (((p : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] ↥(fderiv ℝ σ x).ker).contDiff).comp
      (contDiff_id.sub contDiff_const)).contDiffAt
  have he_smOn : ContDiffOn ℝ ∞ (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) V := by
    intro y hy
    rw [he_coe, hprod]
    exact ((hσ y hy).prodMk (hpsnd y)).contDiffWithinAt
  -- the open set of points at which the derivative of the chart is invertible
  have hle1 : (0 : ℕ∞ω) + 1 ≤ ∞ := by
    rw [show (0 : ℕ∞ω) + 1 = (↑(0 + 1) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = (↑(⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hfdcont : ContinuousOn
      (fun y => fderiv ℝ (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) y) V :=
    (ContDiffOn.fderiv_of_isOpen he_smOn hV hle1).continuousOn_zero
  have hGopen : IsOpen (V ∩ (fun y => fderiv ℝ
      (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) y) ⁻¹'
        {L : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] ℝ × ↥(fderiv ℝ σ x).ker | L.IsInvertible}) :=
    hfdcont.isOpen_inter_preimage hV isOpen_setOf_isInvertible
  obtain ⟨W₀, hW₀open, hW₀mem, hW₀sub, hW₀right, hW₀sm⟩ :=
    contDiffOn_symm_of_contDiffOn hGopen (he_smOn.mono inter_subset_left)
      (fun y hy => hy.2) ⟨hxV, by rw [he_coe]; exact D.isInvertible_fderiv_prodFun⟩ hxsrc
  set W₁ : Set (ℝ × ↥(fderiv ℝ σ x).ker) :=
    W₀ ∩ (e.target ∩ (e.symm : ℝ × ↥(fderiv ℝ σ x).ker → EuclideanSpace ℝ (Fin (n+1))) ⁻¹' V)
    with hW₁def
  have hW₁open : IsOpen W₁ := hW₀open.inter (e.isOpen_inter_preimage_symm hV)
  have hW₁mem : e x ∈ W₁ := by
    refine ⟨hW₀mem, e.map_source hxsrc, ?_⟩
    show (e.symm : ℝ × ↥(fderiv ℝ σ x).ker → EuclideanSpace ℝ (Fin (n+1))) (e x) ∈ V
    rw [e.left_inv hxsrc]
    exact hxV
  have hW₁sm : ContDiffOn ℝ ∞
      (e.symm : ℝ × ↥(fderiv ℝ σ x).ker → EuclideanSpace ℝ (Fin (n+1))) W₁ :=
    hW₀sm.mono inter_subset_left
  have hW₁right : ∀ z ∈ W₁, e (e.symm z) = z := fun z hz => hW₀right z hz.1
  have hW₁V : ∀ z ∈ W₁,
      (e.symm : ℝ × ↥(fderiv ℝ σ x).ker → EuclideanSpace ℝ (Fin (n+1))) z ∈ V :=
    fun z hz => hz.2.2
  refine ⟨e.source ∩ e ⁻¹' W₁, W₁,
    (e.symm : ℝ × ↥(fderiv ℝ σ x).ker → EuclideanSpace ℝ (Fin (n+1))),
    e.isOpen_inter_preimage hW₁open, ⟨hxsrc, hW₁mem⟩, ?_, hW₁open, (by rw [← hex]; exact hW₁mem),
    ?_, hW₁sm, ?_, ?_, ?_⟩
  · -- `N ⊆ V`
    intro y hy
    rw [← e.left_inv hy.1]
    exact hW₁V (e y) hy.2
  · -- `g (σ x, 0) = x`
    rw [← hex]
    exact e.left_inv hxsrc
  · -- `g` maps `Ω` into `N`
    intro u hu
    refine ⟨e.symm.map_source (hW₁def ▸ hu).2.1, ?_⟩
    show (e : EuclideanSpace ℝ (Fin (n+1)) → ℝ × ↥(fderiv ℝ σ x).ker) (e.symm u) ∈ W₁
    rw [hW₁right u hu]
    exact hu
  · -- `σ (g u) = u.1`
    intro u hu
    have h := congrArg Prod.fst (hW₁right u hu)
    rw [hfst] at h
    exact h
  · -- every point of `N` is `g u` for some `u ∈ Ω`
    intro y hy
    exact ⟨e y, hy.2, e.left_inv hy.1⟩

/-! ## Covering an open set by compact sets -/

/-- **An open subset of a finite-dimensional real normed space is a countable union of compact
subsets contained in it.**  The compact sets are closed balls centred at the points of a countable
Lindelöf subcover of the cover of `Ω` by closed balls contained in `Ω`. -/
theorem exists_countable_isCompact_cover_isOpen {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Ω : Set E} (hΩ : IsOpen Ω) :
    ∃ S : Set (Set E), S.Countable ∧ (∀ K ∈ S, IsCompact K) ∧ (∀ K ∈ S, K ⊆ Ω) ∧
      Ω = ⋃₀ S := by
  classical
  have hu : ∀ p : E, ∃ r : ℝ, p ∈ Ω → 0 < r ∧ Metric.closedBall p r ⊆ Ω := by
    intro p
    by_cases hp : p ∈ Ω
    · obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hΩ p hp
      exact ⟨ε/2, fun _ => ⟨by linarith,
        (Metric.closedBall_subset_ball (by linarith)).trans hsub⟩⟩
    · exact ⟨1, fun h => absurd h hp⟩
  choose r hr using hu
  obtain ⟨t, htc, htΩ, hcov⟩ := (HereditarilyLindelofSpace.isLindelof Ω).elim_nhds_subcover
    (fun p => Metric.closedBall p (r p)) (fun p hp => Metric.closedBall_mem_nhds p ((hr p hp).1))
  refine ⟨(fun p => Metric.closedBall p (r p)) '' t, htc.image _, ?_, ?_, ?_⟩
  · rintro K ⟨p, hpt, rfl⟩
    exact isCompact_closedBall p (r p)
  · rintro K ⟨p, hpt, rfl⟩
    exact (hr p (htΩ p hpt)).2
  · rw [Set.sUnion_image]
    refine Subset.antisymm hcov ?_
    intro p hp
    obtain ⟨x, hx⟩ := mem_iUnion.mp hp
    obtain ⟨hxt, hpN⟩ := mem_iUnion.mp hx
    exact (hr x (htΩ x hxt)).2 hpN

/-! ## The localized Fubini step -/

/-- **The Fubini step of rectangular Sard's theorem, with smoothness assumed only on an open set.**
If Sard's theorem holds for `C^∞` maps `ℝⁿ → ℝᵐ` (`hIH`), then the critical values of the
product-form map `p ↦ (p.1, γ p)` have measure zero, for `γ` only `C^∞` on the open set `Ω`.

The proof is the one of `Sard.prodForm_null`, with the critical set only relatively closed: `Ω` is
exhausted by compacta `K`, on which the critical set is closed (the derivative is continuous there)
and hence the critical image is compact; each time-slice of each piece is contained in the critical
image of the corresponding slice map, null by `hIH`, and Tonelli finishes. -/
theorem prodForm_nullOn {n m : ℕ}
    (hIH : SardEuclidOn n m)
    {Ω : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    {γ : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hγ : CInfOn γ Ω) :
    volume ((fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, γ p)) ''
      ({p | IsCriticalPoint (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, γ p)) p} ∩ Ω)) = 0 := by
  classical
  set G : ℝ × EuclideanSpace ℝ (Fin n) → ℝ × EuclideanSpace ℝ (Fin m) :=
    fun p => (p.1, γ p) with hGdef
  have hle1 : (0 : ℕ∞ω) + 1 ≤ ∞ := by
    rw [show (0 : ℕ∞ω) + 1 = (↑(0 + 1) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = (↑(⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hGOn : ContDiffOn ℝ smoothHeight G Ω := by
    rw [hGdef]
    exact ContDiffOn.prodMk contDiffOn_fst hγ
  have hGfd : ContinuousOn (fun p => fderiv ℝ G p) Ω :=
    (ContDiffOn.fderiv_of_isOpen hGOn hΩ hle1).continuousOn_zero
  have hGopen : IsOpen (Ω ∩ {p | Function.Surjective (fderiv ℝ G p)}) :=
    hGfd.isOpen_inter_preimage hΩ isOpen_setOf_surjective_clm
  set Cf : Set (ℝ × EuclideanSpace ℝ (Fin n)) :=
    (Ω ∩ {p | Function.Surjective (fderiv ℝ G p)})ᶜ with hCfdef
  have hCfclosed : IsClosed Cf := hGopen.isClosed_compl
  have hcrit : ∀ p ∈ Ω, (IsCriticalPoint G p ↔ p ∈ Cf) := by
    intro p hp
    rw [hCfdef, IsCriticalPoint]
    simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, hp, true_and]
  obtain ⟨S, hSc, hScomp, hSsub, hScov⟩ := exists_countable_isCompact_cover_isOpen hΩ
  haveI : Countable ↥S := hSc.to_subtype
  have hpiece : ∀ i : ↥S,
      volume (G '' ({p | IsCriticalPoint G p} ∩ (i : Set (ℝ × EuclideanSpace ℝ (Fin n))))) = 0 := by
    intro i
    have hKcrit_eq : {p | IsCriticalPoint G p} ∩ (i : Set (ℝ × EuclideanSpace ℝ (Fin n)))
        = Cf ∩ (i : Set _) := by
      ext p
      constructor
      · rintro ⟨hp, hpi⟩
        exact ⟨(hcrit p (hSsub i.1 i.2 hpi)).mp hp, hpi⟩
      · rintro ⟨hpC, hpi⟩
        exact ⟨(hcrit p (hSsub i.1 i.2 hpi)).mpr hpC, hpi⟩
    have hKcrit : IsCompact ({p | IsCriticalPoint G p} ∩ (i : Set _)) := by
      rw [hKcrit_eq]
      exact IsCompact.of_isClosed_subset (hScomp i.1 i.2)
        (hCfclosed.inter (hScomp i.1 i.2).isClosed) inter_subset_right
    have hcont : ContinuousOn G ({p | IsCriticalPoint G p} ∩ (i : Set _)) := by
      intro p hp
      exact ((hGOn.contDiffAt (hΩ.mem_nhds (hSsub i.1 i.2 hp.2))).continuousAt).continuousWithinAt
    have hmeas : MeasurableSet (G '' ({p | IsCriticalPoint G p} ∩ (i : Set _))) :=
      (hKcrit.image_of_continuousOn hcont).isClosed.measurableSet
    refine Measure.measure_prod_null_of_ae_null hmeas (Filter.Eventually.of_forall fun t => ?_)
    have hΩt : IsOpen {u : EuclideanSpace ℝ (Fin n) | (t, u) ∈ Ω} :=
      hΩ.preimage (continuous_const.prodMk continuous_id)
    have hγt : CInfOn (fun u => γ (t, u)) {u : EuclideanSpace ℝ (Fin n) | (t, u) ∈ Ω} := by
      have hlin : ContDiff ℝ smoothHeight (fun u : EuclideanSpace ℝ (Fin n) => (t, u)) :=
        contDiff_const.prodMk contDiff_id
      exact hγ.comp hlin.contDiffOn (fun u hu => hu)
    refine measure_mono_null ?_ (hIH (fun u => γ (t, u)) {u | (t, u) ∈ Ω} hΩt hγt)
    rintro y ⟨p, hp, hpG⟩
    obtain ⟨hpcrit, hpi⟩ := hp
    have hp1 : p.1 = t := congrArg Prod.fst hpG
    have hγp : γ p = y := congrArg Prod.snd hpG
    have hpΩ : p ∈ Ω := hSsub i.1 i.2 hpi
    refine ⟨p.2, ⟨?_, ?_⟩, ?_⟩
    · have h := (isCriticalPoint_prodForm_iff_of_contDiffOn hΩ hγ hpΩ).mp hpcrit
      rwa [hp1] at h
    · show (t, p.2) ∈ Ω
      rw [show (t, p.2) = p from Prod.ext hp1.symm rfl]
      exact hpΩ
    · show γ (t, p.2) = y
      rw [← hp1]
      exact hγp
  have hmain : volume (G '' ({p | IsCriticalPoint G p} ∩ Ω)) = 0 := by
    have hunion : ({p | IsCriticalPoint G p} ∩ Ω)
        = ⋃ i : ↥S, ({p | IsCriticalPoint G p} ∩ (i : Set _)) := by
      rw [hScov, Set.sUnion_eq_iUnion, Set.inter_iUnion]
    rw [hunion, Set.image_iUnion, ← nonpos_iff_eq_zero]
    calc volume (⋃ i : ↥S, G '' ({p | IsCriticalPoint G p} ∩ (i : Set _)))
        ≤ ∑' i : ↥S, volume (G '' ({p | IsCriticalPoint G p} ∩ (i : Set _))) := measure_iUnion_le _
      _ = 0 := by simp [hpiece]
  simpa [hGdef] using hmain

/-! ## The non-flat step -/

theorem notFlat_null {n m : ℕ}
    (hIH : Work.ThomBordism.Transversality.SardEuclidOn n m)
    {f : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (m+1))}
    {U : Set (EuclideanSpace ℝ (Fin (n+1)))} (hU : IsOpen U)
    (hf : Work.ThomBordism.Transversality.CInfOn f U) :
    MeasureTheory.volume (f '' (({x | Work.ThomBordism.Transversality.IsCriticalPoint f x}
      \ Work.ThomBordism.Transversality.Zk f 1) ∩ U)) = 0 := by
  classical
  refine volume_image_null_of_local (n := n) (m := m + 1) (f := f)
    (S := ({x | IsCriticalPoint f x} \ Zk f 1) ∩ U) ?_
  intro x hx
  obtain ⟨hxcrit, hxU⟩ := hx
  obtain ⟨hxcrit', hxnotZk⟩ := hxcrit
  -- the derivative of `f` at `x` does not vanish
  have hdf : fderiv ℝ f x ≠ 0 := by
    intro h
    exact hxnotZk (mem_Zk.mpr (vanishToOrder_one_iff.mpr h))
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin (n+1)), fderiv ℝ f x v ≠ 0 := by
    by_contra h
    push Not at h
    exact hdf (ContinuousLinearMap.ext h)
  obtain ⟨j, hj⟩ : ∃ j : Fin (m+1), (fderiv ℝ f x v) j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (by ext t; exact h t)
  -- the scalar coordinate `σ` with non-vanishing derivative
  set σ : EuclideanSpace ℝ (Fin (n+1)) → ℝ := fun y => f y j with hσdef
  have hf_diff : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have hσ_at : ∀ y ∈ U, CInfAt σ y := by
    intro y hy
    rw [hσdef]
    exact ContDiffAt.comp y
      (((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] ℝ).contDiff).contDiffAt)
      (hf.contDiffAt (hU.mem_nhds hy))
  have hσv : fderiv ℝ σ x v ≠ 0 := by
    rw [hσdef, fderiv_coord hf_diff j]
    simpa using hj
  have hσ' : fderiv ℝ σ x ≠ 0 := fun h => hσv (by rw [h]; simp)
  -- the flow box of `σ` at `x`
  obtain ⟨N, Ω, g, hNopen, hxN, hNU, hΩopen, hσxΩ, hgx, hgsm, hgN, hgσ, hgcov⟩ :=
    flowBoxOn hU hσ_at hxU hσ'
  -- the parameter space `ker (dσ_x)` is `n`-dimensional
  have hσrange : (fderiv ℝ σ x).toLinearMap.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    exact ⟨(t / fderiv ℝ σ x v) • v, by
      rw [map_smul, smul_eq_mul]
      exact div_mul_cancel₀ t hσv⟩
  have hkerfin : Module.finrank ℝ ↥((fderiv ℝ σ x).ker) = n := by
    have h := LinearMap.finrank_range_add_finrank_ker ((fderiv ℝ σ x).toLinearMap)
    have htop : Module.finrank ℝ ↥((fderiv ℝ σ x).toLinearMap.range) = 1 := by
      rw [hσrange]
      simp
    have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n + 1 := by
      rw [finrank_euclideanSpace, Fintype.card_fin]
    rw [htop, hE] at h
    omega
  let L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] ↥((fderiv ℝ σ x).ker) :=
    (LinearEquiv.ofFinrankEq (EuclideanSpace ℝ (Fin n)) ↥((fderiv ℝ σ x).ker)
      (by rw [finrank_euclideanSpace, Fintype.card_fin, hkerfin])).toContinuousLinearEquiv
  -- the chart written with the parameter space `ℝ × ℝⁿ`
  let β : ℝ × EuclideanSpace ℝ (Fin n) → ℝ × ↥((fderiv ℝ σ x).ker) := fun p => (p.1, L p.2)
  have hβcont : Continuous β := continuous_fst.prodMk (L.continuous.comp continuous_snd)
  let Ω' : Set (ℝ × EuclideanSpace ℝ (Fin n)) := β ⁻¹' Ω
  have hΩ'open : IsOpen Ω' := hΩopen.preimage hβcont
  have hβsm : CInfOn β Ω' :=
    ContDiffOn.prodMk contDiffOn_fst
      (((L : EuclideanSpace ℝ (Fin n) →L[ℝ] ↥((fderiv ℝ σ x).ker)).contDiff).comp_contDiffOn
        contDiffOn_snd)
  let gg : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n+1)) := fun p => g (β p)
  have hggsm : CInfOn gg Ω' := hgsm.comp hβsm (fun p hp => hp)
  have hggN : ∀ p ∈ Ω', gg p ∈ N := fun p hp => hgN (β p) hp
  have hggσ : ∀ p ∈ Ω', σ (gg p) = p.1 := fun p hp => hgσ (β p) hp
  have hgg_diff : ∀ p ∈ Ω', DifferentiableAt ℝ (fun u => f (gg u)) p := by
    intro p hp
    exact DifferentiableAt.comp p
      ((hf.contDiffAt (hU.mem_nhds (hNU (hggN p hp)))).differentiableAt (by simp))
      ((hggsm.contDiffAt (hΩ'open.mem_nhds hp)).differentiableAt (by simp))
  -- the remaining target coordinates, as a function on the parameter space
  let γ : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) :=
    fun p => restrictCoords m j (f (gg p))
  have hγsm : CInfOn γ Ω' :=
    (restrictCoords m j).contDiff.comp_contDiffOn
      (hf.comp hggsm (fun p hp => hNU (hggN p hp)))
  -- on `Ω'` the map is the rotated composite
  have hGprop : ∀ p ∈ Ω', (p.1, γ p) = rotateFirst m j (f (gg p)) := by
    intro p hp
    have h1 : f (gg p) j = p.1 := by
      have h := hggσ p hp
      rwa [hσdef] at h
    rw [rotateFirst_apply]
    exact Prod.ext h1.symm rfl
  -- criticality transfers through the rotation
  have hcrit_transfer : ∀ p ∈ Ω', IsCriticalPoint (fun u => f (gg u)) p →
      IsCriticalPoint (fun q => (q.1, γ q)) p := by
    intro p hp hc
    have heq : (fun q : ℝ × EuclideanSpace ℝ (Fin n) => (q.1, γ q))
        =ᶠ[𝓝 p] (fun q => rotateFirst m j (f (gg q))) :=
      Filter.Eventually.mono (hΩ'open.mem_nhds hp) fun q hq => hGprop q hq
    have hfd : fderiv ℝ (fun q => rotateFirst m j (f (gg q))) p
        = (rotateFirst m j).comp (fderiv ℝ (fun u => f (gg u)) p) :=
      ((rotateFirst m j).hasFDerivAt.comp p (hgg_diff p hp).hasFDerivAt).fderiv
    rw [IsCriticalPoint] at hc ⊢
    rw [heq.fderiv_eq, hfd]
    intro hsurj
    exact hc fun y => by
      obtain ⟨z, hz⟩ := hsurj (rotateFirst m j y)
      exact ⟨z, rotateFirst_injective m j hz⟩
  -- the Fubini step, and the transport of nullity along the rotation
  have hGnull : volume ((fun q : ℝ × EuclideanSpace ℝ (Fin n) => (q.1, γ q)) ''
      ({p | IsCriticalPoint (fun q : ℝ × EuclideanSpace ℝ (Fin n) => (q.1, γ q)) p} ∩ Ω')) = 0 :=
    prodForm_nullOn hIH hΩ'open hγsm
  haveI : MeasureTheory.Measure.IsAddHaarMeasure
      (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))) :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ)
      (volume : Measure (EuclideanSpace ℝ (Fin m)))
  have hnull : volume ((rotateEquiv m j) ⁻¹'
      ((fun q : ℝ × EuclideanSpace ℝ (Fin n) => (q.1, γ q)) ''
        ({p | IsCriticalPoint (fun q : ℝ × EuclideanSpace ℝ (Fin n) => (q.1, γ q)) p}
          ∩ Ω'))) = 0 :=
    volume_preimage_eq_zero_of_continuousLinearEquiv (rotateEquiv m j) hGnull
  -- conclusion
  refine ⟨N, hNopen, hxN, ?_⟩
  refine measure_mono_null (fun z hz => ?_) hnull
  have hsub : f '' ({y | IsCriticalPoint f y} ∩ N) ⊆ (rotateEquiv m j) ⁻¹'
      ((fun q : ℝ × EuclideanSpace ℝ (Fin n) => (q.1, γ q)) ''
        ({p | IsCriticalPoint (fun q : ℝ × EuclideanSpace ℝ (Fin n) => (q.1, γ q)) p}
          ∩ Ω')) := by
    rintro z ⟨y, ⟨hycrit, hyN⟩, rfl⟩
    obtain ⟨u, huΩ, hgu⟩ := hgcov y hyN
    set q : ℝ × EuclideanSpace ℝ (Fin n) := (u.1, L.symm u.2) with hqdef
    have hβq : β q = u := by
      rw [hqdef]
      exact Prod.ext rfl (L.apply_symm_apply u.2)
    have hqΩ' : q ∈ Ω' := by
      show β q ∈ Ω
      rw [hβq]
      exact huΩ
    have hggq : gg q = y := by
      show g (β q) = y
      rw [hβq, hgu]
    have hcritq : IsCriticalPoint (fun u' => f (gg u')) q :=
      isCriticalPoint_comp
        ((hf.contDiffAt (hU.mem_nhds (hNU (hggN q hqΩ')))).differentiableAt (by simp))
        ((hggsm.contDiffAt (hΩ'open.mem_nhds hqΩ')).differentiableAt (by simp))
        (by rw [hggq]; exact hycrit)
    have hGcrit : IsCriticalPoint (fun q : ℝ × EuclideanSpace ℝ (Fin n) => (q.1, γ q)) q :=
      hcrit_transfer q hqΩ' hcritq
    refine ⟨q, ⟨hGcrit, hqΩ'⟩, ?_⟩
    have hfj : f y j = q.1 := by
      have h := hggσ q hqΩ'
      rw [hσdef] at h
      rwa [hggq] at h
    have hrot : rotateEquiv m j (f y) = (q.1, γ q) := by
      rw [rotateEquiv_apply, hfj, ← hggq]
    exact hrot.symm
  obtain ⟨y, hy, rfl⟩ := hz
  exact hsub ⟨y, ⟨hy.1.1.1, hy.2⟩, rfl⟩

end

end Work.ThomBordism.Transversality.Sard
