import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.Wilkies.Defs
import Submission.Work.WilE7.Auxiliary.existsDetSubmatrixNeZero
import Submission.Work.WilE7.Dim.image_mem_nhds_of_surj_fderiv

/-!
# The dimension of a chart is bounded by the dimension of any set containing it

`WilkiesDesign.DimLE X μ` is the o-minimal dimension bound `dim X ≤ μ`: every projection of `X`
to `μ + 1` coordinates has empty interior.  This file proves that if an analytic chart
`γ : ℝⁿ → ℝᵠ` with injective differential at `0` maps a neighbourhood of `0` into `X`
(`γ s ∈ X` for `s` near `0`), then `n ≤ μ`.

The proof is the linear-algebra part of the inverse function theorem:

* `dim (im (fderiv γ 0)) = n`, so if `n > μ` there are `μ + 1` coordinates of `ℝᵠ` on which the
  derivative `fderiv γ 0` has full rank: a coordinate projection `P` with `P ∘ fderiv γ 0`
  surjective (`exists_coordProj_surjective`, proved below from the maximal-minor extraction
  `Work.WilE7.Auxiliary.existsDetSubmatrixNeZero`).
* `P ∘ γ` is then an analytic map with surjective derivative at `0`, hence open at `0`
  (`image_mem_nhds_of_surj_fderiv`): it sends the neighbourhood `{s | γ s ∈ X}` of `0` to a
  neighbourhood of `(P ∘ γ) 0`, which therefore contains a nonempty open set `O`.
* Since `O ⊆ P '' X` (the corresponding coordinate projection of `X`), that projection has
  nonempty interior, contradicting `DimLE X μ`.
-/

open Matrix

namespace Work.WilE7.Dim

/-! ## The linear algebra input: a coordinate projection of full rank

For an injective linear map `T : ℝⁿ → ℝᵠ` there are `m ≤ n` coordinates `e : Fin m ↪ Fin q` of
the target such that `v ↦ (T v) ∘ e` is surjective.  The source of full rank is the classical
maximal-minor fact (`existsDetSubmatrixNeZero`): the `n × q` matrix of `T` has rank `n`, so `n`
of its columns are independent.
-/

/-- The coordinate projection `ℝ^q → ℝ^n` onto the coordinates `σ`, as a continuous linear map. -/
def coordProj {n q : ℕ} (σ : Fin n → Fin q) : (Fin q → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun k => ContinuousLinearMap.proj (σ k))

lemma coordProj_apply {n q : ℕ} (σ : Fin n → Fin q) (u : Fin q → ℝ) : coordProj σ u = u ∘ σ :=
  rfl

/-- `mulVecLin` of the matrix of `T` is `T`. -/
lemma mulVecLin_toMatrix' {n q : ℕ} {T : (Fin n → ℝ) →L[ℝ] (Fin q → ℝ)} :
    (LinearMap.toMatrix' (T : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ))).mulVecLin =
      (T : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ)) := by
  rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']

/-- The matrix of an injective linear map has rank the dimension of its source. -/
lemma rank_toMatrix'_of_injective {n q : ℕ} {T : (Fin n → ℝ) →L[ℝ] (Fin q → ℝ)}
    (hT : Function.Injective T) :
    (LinearMap.toMatrix' (T : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ))).rank = n := by
  rw [Matrix.rank, mulVecLin_toMatrix' (T := T), LinearMap.finrank_range_of_inj hT,
    Module.finrank_fintype_fun_eq_card]
  simp

/-- Matrix-vector multiplication by the matrix of `T` is `T`. -/
lemma toMatrix'_mulVec' {n q : ℕ} {T : (Fin n → ℝ) →L[ℝ] (Fin q → ℝ)} (x : Fin n → ℝ) :
    LinearMap.toMatrix' (T : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ)) *ᵥ x = T x :=
  LinearMap.toMatrix'_mulVec _ x

/-- The transpose of a selected square submatrix multiplies by the selected coordinates:
`(Aᵀ *ᵥ x) k = (M *ᵥ x) (σ k)` for `A = (Mᵀ).submatrix id σ`. -/
lemma submatrix_transpose_mulVec {n q : ℕ} {M : Matrix (Fin q) (Fin n) ℝ} {σ : Fin n → Fin q}
    (x : Fin n → ℝ) :
    ((Mᵀ).submatrix id σ)ᵀ *ᵥ x = fun k => (M *ᵥ x) (σ k) := by
  funext k
  simp [Matrix.mulVec, dotProduct]

/-- If the selected square submatrix of `M` has nonzero determinant, the selection `σ` is
injective. -/
lemma injective_of_submatrix_det_ne_zero {n q : ℕ} {M : Matrix (Fin q) (Fin n) ℝ}
    {σ : Fin n → Fin q} (hdet : ((Mᵀ).submatrix id σ).det ≠ 0) : Function.Injective σ := by
  have hunit : IsUnit ((Mᵀ).submatrix id σ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hli : LinearIndependent ℝ ((Mᵀ).submatrix id σ).col :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr hunit
  intro k k' hkk'
  exact hli.injective (by funext i; simp [Matrix.col_apply, Matrix.submatrix_apply, hkk'])

/-- The coordinate projection onto the selected coordinates, applied to `T x`, is matrix-vector
multiplication by the transpose of the selected square submatrix of the matrix of `T`. -/
lemma coordProj_toMatrix'_eq {n q : ℕ} {T : (Fin n → ℝ) →L[ℝ] (Fin q → ℝ)}
    {M : Matrix (Fin q) (Fin n) ℝ} {σ : Fin n → Fin q}
    (hM : M = LinearMap.toMatrix' (T : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ))) (x : Fin n → ℝ) :
    coordProj σ (T x) = ((Mᵀ).submatrix id σ)ᵀ *ᵥ x := by
  rw [coordProj_apply (σ := σ), submatrix_transpose_mulVec (M := M) (σ := σ) x]
  funext k
  rw [Function.comp_apply, ← toMatrix'_mulVec' (T := T) x, ← hM]

/-- The coordinate projection onto the selected coordinates is injective on the range of `T`. -/
lemma injective_coordProj_comp {n q : ℕ} {T : (Fin n → ℝ) →L[ℝ] (Fin q → ℝ)}
    {M : Matrix (Fin q) (Fin n) ℝ} {σ : Fin n → Fin q}
    (hM : M = LinearMap.toMatrix' (T : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ)))
    (hdet : ((Mᵀ).submatrix id σ).det ≠ 0) :
    Function.Injective (((coordProj σ : (Fin q → ℝ) →ₗ[ℝ] (Fin n → ℝ)).comp
      (T : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ)))) := by
  have hunitT : IsUnit (((Mᵀ).submatrix id σ)ᵀ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hdet)
  have hmulT : Function.Injective (((Mᵀ).submatrix id σ)ᵀ).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunitT
  intro x x' hxx'
  refine hmulT ?_
  rw [← coordProj_toMatrix'_eq (T := T) hM x, ← coordProj_toMatrix'_eq (T := T) hM x']
  exact hxx'

/-- On spaces of the same dimension, injectivity of the coordinate projection followed by `T`
implies surjectivity. -/
lemma surjective_coordProj_comp {n q : ℕ} {T : (Fin n → ℝ) →L[ℝ] (Fin q → ℝ)}
    {σ : Fin n → Fin q}
    (hinj : Function.Injective (((coordProj σ : (Fin q → ℝ) →ₗ[ℝ] (Fin n → ℝ)).comp
      (T : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ))))) :
    Function.Surjective (((coordProj σ : (Fin q → ℝ) →ₗ[ℝ] (Fin n → ℝ)).comp
      (T : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ)))) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := Fin n → ℝ)
    (V₂ := Fin n → ℝ)
    (f := ((coordProj σ : (Fin q → ℝ) →ₗ[ℝ] (Fin n → ℝ)).comp
      (T : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ)))) rfl).mp hinj

/-- For an injective linear `T : ℝⁿ → ℝᵠ` there are `n` coordinates of `ℝᵠ` on which `T` is a
bijection. -/
lemma exists_coordProj_bijective {n q : ℕ} {T : (Fin n → ℝ) →L[ℝ] (Fin q → ℝ)}
    (hT : Function.Injective T) :
    ∃ σ : Fin n ↪ Fin q, Function.Bijective (fun v : Fin n → ℝ => (T v) ∘ σ) := by
  let M : Matrix (Fin q) (Fin n) ℝ := LinearMap.toMatrix' (T : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ))
  have hM : M = LinearMap.toMatrix' (T : (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ)) := rfl
  obtain ⟨σ, hσ⟩ := Work.WilE7.Auxiliary.existsDetSubmatrixNeZero Mᵀ
    (by rw [Matrix.rank_transpose, hM]; exact rank_toMatrix'_of_injective (T := T) hT)
  have hdet : ((Mᵀ).submatrix id σ).det ≠ 0 := hσ
  have hσinj : Function.Injective σ := injective_of_submatrix_det_ne_zero (M := M) (σ := σ) hdet
  have hinj := injective_coordProj_comp (T := T) (M := M) (σ := σ) hM hdet
  have hsurj := surjective_coordProj_comp (T := T) (σ := σ) hinj
  exact ⟨⟨σ, hσinj⟩, hinj, hsurj⟩

/-- **The linear algebra input.**  For an injective linear `T : ℝⁿ → ℝᵠ` and `m ≤ n` there are
`m` coordinates `e` of `ℝᵠ` such that `v ↦ (T v) ∘ e` is surjective onto `ℝ^m`. -/
lemma exists_coordProj_surjective {n q m : ℕ} (hm : m ≤ n)
    {T : (Fin n → ℝ) →L[ℝ] (Fin q → ℝ)} (hT : Function.Injective T) :
    ∃ e : Fin m ↪ Fin q, Function.Surjective (fun v : Fin n → ℝ => (T v) ∘ e) := by
  obtain ⟨σ, hbij⟩ := exists_coordProj_bijective hT
  obtain ⟨_, hσsurj⟩ := hbij
  -- restate surjectivity without the beta-redex, so that it can be used for rewriting
  have hsurj : ∀ u : Fin n → ℝ, ∃ v : Fin n → ℝ, (T v) ∘ ⇑σ = u := by
    intro u
    obtain ⟨v, hv⟩ := hσsurj u
    exact ⟨v, hv⟩
  refine ⟨⟨fun a => σ (Fin.castLE hm a), σ.injective.comp (Fin.castLE_injective hm)⟩, ?_⟩
  intro z
  obtain ⟨v, hv⟩ := hsurj (Function.extend (Fin.castLE hm) z 0)
  refine ⟨v, ?_⟩
  funext a
  show (T v) (⇑σ (Fin.castLE hm a)) = z a
  rw [show (T v) (⇑σ (Fin.castLE hm a)) = ((T v) ∘ ⇑σ) (Fin.castLE hm a) from rfl, hv]
  exact Function.Injective.extend_apply (Fin.castLE_injective hm) z 0 a

/-! ## The dimension bound for a chart -/

theorem dimLE_of_chart {q n μ : ℕ} {X : Set (Fin q → ℝ)} (hX : WilkiesDesign.DimLE X μ)
    {γ : (Fin n → ℝ) → (Fin q → ℝ)} (hγ : AnalyticAt ℝ γ 0)
    (hinj : Function.Injective (fderiv ℝ γ 0))
    (hmem : Filter.Eventually (fun s : Fin n → ℝ => γ s ∈ X) (nhds (0 : Fin n → ℝ))) :
    n ≤ μ := by
  by_contra hcon
  -- `μ + 1 ≤ n ≤ q`: we may choose `μ + 1` coordinates meeting the image of the derivative
  have hm : μ + 1 ≤ n := Nat.lt_iff_add_one_le.mp (Nat.lt_of_not_le hcon)
  obtain ⟨e, he⟩ := exists_coordProj_surjective (m := μ + 1) (T := fderiv ℝ γ 0) hm hinj
  -- the coordinate projection onto those coordinates, as a continuous linear map
  let P : (Fin q → ℝ) →L[ℝ] (Fin (μ + 1) → ℝ) := coordProj e
  have hP : ∀ u : Fin q → ℝ, P u = u ∘ e := fun u => coordProj_apply e u
  -- `P ∘ γ` is analytic at `0` with surjective derivative
  have hψan : AnalyticAt ℝ (fun s : Fin n → ℝ => P (γ s)) 0 :=
    (P.analyticAt (γ 0)).comp hγ
  have hψstr : HasStrictFDerivAt (fun s : Fin n → ℝ => P (γ s)) (P.comp (fderiv ℝ γ 0)) 0 :=
    HasStrictFDerivAt.comp (x := (0 : Fin n → ℝ)) P.hasStrictFDerivAt hγ.hasStrictFDerivAt
  have hψder : fderiv ℝ (fun s : Fin n → ℝ => P (γ s)) 0 = P.comp (fderiv ℝ γ 0) :=
    hψstr.hasFDerivAt.fderiv
  have hsurj : Function.Surjective (fderiv ℝ (fun s : Fin n → ℝ => P (γ s)) 0) := by
    rw [hψder]
    intro y
    obtain ⟨v, hv⟩ := he y
    exact ⟨v, by rw [ContinuousLinearMap.comp_apply, hP]; exact hv⟩
  -- hence the image of the neighbourhood `{s | γ s ∈ X}` of `0` contains an open set
  have hmem' : {s : Fin n → ℝ | γ s ∈ X} ∈ nhds (0 : Fin n → ℝ) := hmem
  have hnhds : (fun s : Fin n → ℝ => P (γ s)) '' {s : Fin n → ℝ | γ s ∈ X} ∈
      nhds ((fun s : Fin n → ℝ => P (γ s)) 0) :=
    image_mem_nhds_of_surj_fderiv hψan hsurj _ hmem'
  obtain ⟨O, hOsub, hOopen, hO0⟩ := mem_nhds_iff.mp hnhds
  -- that open set lies in the `e`-coordinate projection of `X`
  have hOsubX : O ⊆ (fun x : Fin q → ℝ => x ∘ e) '' X := by
    intro y hy
    obtain ⟨s, hs, hsy⟩ := hOsub hy
    exact ⟨γ s, hs, (by rw [← hsy]; exact (hP (γ s)).symm)⟩
  -- contradicting `DimLE X μ`
  obtain ⟨y, hy⟩ := Set.Nonempty.mono (interior_maximal hOsubX hOopen) ⟨P (γ 0), hO0⟩
  rw [hX e] at hy
  simpa using hy

end Work.WilE7.Dim
