/-
  `Work.WilE7.DimAPI.rankLocusAux` — the auxiliary lemmas for `rankLocus_nullDimLE`
  (hence for the Sard step of the BV lexicographic induction, `E7_prop_main`).

  Nothing here is specific to the target statement: the file collects
   * the Fréchet derivative of the equation family `z ↦ (a ↦ eaEval c (h a) z)` of a stratum,
     both pointwise (`fderiv_eaFamily_apply`) and as the linear map `jac` (`jac_apply`,
     `fderiv_eaFamily_apply_jac`, `mem_ker_jac_iff`);
   * its analyticity (`eaFamily_analyticAt`);
   * the elementary linear-algebra lemma that a linear map whose restriction to a subspace `K`
     has image of dimension `≤ r` cannot map `K` onto `ℝ^{r+1}`
     (`not_surj_restrict_of_finrank_le`);
   * the coordinate projection `coordMap` used by `NullDimLE`, its linear-map form `coordLin`
     (a composition `(x ↦ x ∘ e) ∘ basePrLin`, i.e. `projE e ∘ projFirst ∘ absPt`), its derivative
     (`fderiv_coordMap_apply`) and its analyticity (`coordMap_analyticAt`);
   * the identification of the set appearing in `NullDimLE` with `coordMap '' ·`
     (`image_coordMap`).
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval
import Submission.Work.WilE5.Strat.flatConormalTools

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.DimAPI
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-! ## 1. The Fréchet derivative of the equation family of a stratum -/

/-- Pointwise form of the derivative of the family `z ↦ (a ↦ eaEval c (h a) z)`: its `a`-th
component at `v` is `∑ᵢ eaEval c (eaD c i (h a)) z * v i`. -/
theorem fderiv_eaFamily_apply {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (z v : Fin k → ℝ) :
    fderiv ℝ (fun w : Fin k → ℝ => fun a : Fin j => eaEval c (h a) w) z v
      = fun a : Fin j => ∑ i : Fin k, eaEval c (eaD c i (h a)) z * v i := by
  rw [(hasFDerivAt_pi.mpr fun a => Work.WilE5.Calc.hasFDerivAt_eaEval c (h a) z).fderiv]
  funext a
  rw [ContinuousLinearMap.pi_apply]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- `jac S z` is the matrix-times-vector of the symbolic derivatives of the equations. -/
theorem jac_apply {p q : ℕ} (S : Stratum p q) (z v : Fin (p + q) → ℝ) :
    jac S z v
      = fun a : Fin S.j => ∑ l : Fin (p + q), eaEval S.X.c (eaD S.X.c l (S.h a)) z * v l := by
  rw [jac]
  simp only [Matrix.mulVecLin_apply]
  rfl

/-- The derivative of the equation family of an absolute stratum, compared with `jac`. -/
theorem fderiv_eaFamily_apply_jac {N : ℕ} (S : Stratum 0 N) (z v : Fin (0 + N) → ℝ) :
    fderiv ℝ (fun w : Fin (0 + N) → ℝ => fun a : Fin S.j => eaEval S.X.c (S.h a) w) z v
      = jac S z v := by
  rw [fderiv_eaFamily_apply, jac_apply]

/-- Membership in the kernel of `jac S z`, in pointwise form. -/
theorem mem_ker_jac_iff {N : ℕ} (S : Stratum 0 N) (z v : Fin (0 + N) → ℝ) :
    v ∈ LinearMap.ker (jac S z) ↔
      fderiv ℝ (fun w : Fin (0 + N) → ℝ => fun a : Fin S.j => eaEval S.X.c (S.h a) w) z v = 0 := by
  rw [LinearMap.mem_ker, ← fderiv_eaFamily_apply_jac S z v]

/-- The equation family of a stratum is analytic everywhere. -/
theorem eaFamily_analyticAt {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (x : Fin k → ℝ) :
    AnalyticAt ℝ (fun w : Fin k → ℝ => fun a : Fin j => eaEval c (h a) w) x :=
  AnalyticAt.pi fun a => Work.WilE5.Strat.analyticAt_eaEval c (h a) x

/-! ## 2. A linear map cannot surject from a subspace of small image -/

/-- If the image of the subspace `K` under `M` has dimension `≤ r`, then the composite `L ∘ M`
cannot map `K` onto `ℝ^{r+1}`. -/
theorem not_surj_restrict_of_finrank_le {N r n : ℕ} (K : Submodule ℝ (Fin N → ℝ))
    (M : (Fin N → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (L : (Fin n → ℝ) →ₗ[ℝ] (Fin (r + 1) → ℝ))
    (hK : Module.finrank ℝ (K.map M) ≤ r) :
    ¬ ∀ w : Fin (r + 1) → ℝ, ∃ v : Fin N → ℝ, v ∈ K ∧ (L.comp M) v = w := by
  intro h
  have htop : K.map (L.comp M) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    rw [Submodule.mem_map]
    obtain ⟨v, hv, hvw⟩ := h w
    exact ⟨v, hv, hvw⟩
  have hmap : K.map (L.comp M) = (K.map M).map L := by
    ext w
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨M v, ⟨v, hv, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
  have hle : Module.finrank ℝ (K.map (L.comp M)) ≤ r := by
    rw [hmap]
    exact le_trans (Submodule.finrank_map_le L (K.map M)) hK
  have htopfr : Module.finrank ℝ (⊤ : Submodule ℝ (Fin (r + 1) → ℝ)) = r + 1 := by
    rw [Submodule.topEquiv.finrank_eq, Module.finrank_fin_fun]
  rw [htop, htopfr] at hle
  omega

/-! ## 3. The coordinate projection `projE e ∘ projFirst n m ∘ absPt` -/

/-- The coordinate map of `NullDimLE`: `z ↦ (i ↦ z (e i))`, read through the identification
`Fin (n+m) ≃ Fin (0 + (n+m))`. -/
def coordMap (n m r : ℕ) (e : Fin r ↪ Fin n) : (Fin (0 + (n + m)) → ℝ) → (Fin r → ℝ) :=
  fun z i => z (Fin.cast (Nat.zero_add (n + m)).symm (Fin.castAdd m (e i)))

/-- `coordMap` as a linear map, factored as `(x ↦ x ∘ e) ∘ basePrLin n m`. -/
def coordLin (n m r : ℕ) (e : Fin r ↪ Fin n) : (Fin (0 + (n + m)) → ℝ) →ₗ[ℝ] (Fin r → ℝ) :=
  (LinearMap.funLeft ℝ ℝ e).comp (basePrLin n m)

theorem coordLin_apply (n m r : ℕ) (e : Fin r ↪ Fin n) (v : Fin (0 + (n + m)) → ℝ) :
    coordLin n m r e v = fun i : Fin r => basePrLin n m v (e i) := by
  funext i
  simp [coordLin, LinearMap.comp_apply, LinearMap.funLeft]

/-- `coordMap` is the underlying function of the continuous linear map obtained by composing the
coordinate projections. -/
theorem coordMap_eq_clm (n m r : ℕ) (e : Fin r ↪ Fin n) :
    coordMap n m r e = ⇑(ContinuousLinearMap.pi (fun i : Fin r =>
      (ContinuousLinearMap.proj (Fin.cast (Nat.zero_add (n + m)).symm (Fin.castAdd m (e i))) :
        (Fin (0 + (n + m)) → ℝ) →L[ℝ] ℝ))) := by
  funext z i
  simp [coordMap, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]

theorem coordMap_eq_coordLin (n m r : ℕ) (e : Fin r ↪ Fin n)
    (z : Fin (0 + (n + m)) → ℝ) :
    coordMap n m r e z = coordLin n m r e z := by
  funext i
  simp [coordMap, coordLin, LinearMap.comp_apply, LinearMap.funLeft, basePrLin]

/-- The derivative of the coordinate map. -/
theorem fderiv_coordMap_apply (n m r : ℕ) (e : Fin r ↪ Fin n)
    (z v : Fin (0 + (n + m)) → ℝ) :
    fderiv ℝ (coordMap n m r e) z v = coordLin n m r e v := by
  rw [coordMap_eq_clm, ContinuousLinearMap.fderiv]
  funext i
  simp [coordLin, LinearMap.comp_apply, LinearMap.funLeft_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply, basePrLin]

/-- The coordinate map is analytic everywhere. -/
theorem coordMap_analyticAt (n m r : ℕ) (e : Fin r ↪ Fin n) (x : Fin (0 + (n + m)) → ℝ) :
    AnalyticAt ℝ (coordMap n m r e) x := by
  have hpi := (ContinuousLinearMap.pi (fun i : Fin r =>
    (ContinuousLinearMap.proj (Fin.cast (Nat.zero_add (n + m)).symm (Fin.castAdd m (e i))) :
      (Fin (0 + (n + m)) → ℝ) →L[ℝ] ℝ))).analyticAt x
  simpa [coordMap_eq_clm] using hpi

/-- The set of `NullDimLE` is the image of `coordMap`. -/
theorem image_coordMap (n m r : ℕ) (e : Fin r ↪ Fin n) (A : Set (Fin (0 + (n + m)) → ℝ)) :
    (fun x : Fin n → ℝ => x ∘ e) '' (projFirst n m '' (absPt '' A))
      = coordMap n m r e '' A := by
  rw [← Set.image_comp, ← Set.image_comp]
  congr 1

end Work.WilE7.DimAPI
