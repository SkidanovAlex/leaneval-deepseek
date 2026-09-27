import Mathlib
import Submission.Work.Whitney.OrientedAtlas
import Submission.Work.Whitney.PairDet

/-!
# Chart independence of the sign comparison of two double points

`Work.Whitney.pairDet f c₁ c₂ a b` is the signed determinant of the "two sheet" map of a candidate
double point `(a,b)` of `f : M → ℝ^{2n}`, read through the two charts `c₁, c₂`.  The number
`pairDet f c₁ c₂ p₁ p₂ * pairDet f c₃ c₄ q₁ q₂` is the comparison of the two double points
`(p₁,p₂)` and `(q₁,q₂)`; its **sign** is the geometric datum used by Whitney's cancellation.

The purpose of this file is to show that this sign does not depend on the choice of charts, as soon
as the charts belong to an oriented atlas `A` (`Work.Whitney.IsOrientedAtlas`).  Consequently the
predicate `Work.Whitney.OppositeSign A f p₁ p₂ q₁ q₂` — "some (equivalently every) choice of
charts of `A` at the four points makes the product negative" — is equivalent to the inequality for
any *fixed* choice of such charts, which is the content of `Work.Whitney.oppositeSign_iff`.

The mathematical heart is the change-of-chart formula

`pairDet f c c₂ p p₂ = pairDet f c' c₂ p p₂ * det (D (c' ∘ c.symm) (c p))`

for two charts `c, c'` of an oriented atlas: the transition `c' ∘ c.symm` is a local
diffeomorphism with *positive* Jacobian determinant (`IsOrientedAtlas`), so replacing `c` by `c'`
multiplies `pairDet` by a positive number; signs are therefore chart independent.  The
chain rule is applied in the form `D (f ∘ c.symm) = D (f ∘ c'.symm) ∘ D (c' ∘ c.symm)`.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-! ## Linear algebra of the two-chart determinant -/

/-- **Determinant factorisation**, first block.  If the first factor of a `coprod` is precomposed
with `T` (`L = L' ∘ T`), then the determinant of the composite
`pairEquiv ∘ (L coprod N)` picks up the factor `det T`. -/
theorem det_comp_coprod_left {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Module.Free ℝ E] [Module.Finite ℝ E]
    (P : F ≃ₗ[ℝ] E × E) (L L' N : E →L[ℝ] F) (T : E →L[ℝ] E) (h : L = L'.comp T) :
    LinearMap.det (P.toLinearMap.comp ((L.coprod N).toLinearMap)) =
      LinearMap.det (P.toLinearMap.comp ((L'.coprod N).toLinearMap)) * T.det := by
  have hcop : (L.coprod N) = ((L'.coprod N).comp (T.prodMap (ContinuousLinearMap.id ℝ E))) := by
    apply ContinuousLinearMap.ext
    rintro ⟨x, y⟩
    simp [h, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.coe_prodMap']
  have h2 : (L.coprod N).toLinearMap = ((L'.coprod N).toLinearMap).comp
      ((T.prodMap (ContinuousLinearMap.id ℝ E)).toLinearMap) := by
    rw [hcop]; rfl
  rw [h2]
  rw [show P.toLinearMap.comp (((L'.coprod N).toLinearMap).comp
        ((T.prodMap (ContinuousLinearMap.id ℝ E)).toLinearMap)) =
      (P.toLinearMap.comp ((L'.coprod N).toLinearMap)).comp
        ((T.prodMap (ContinuousLinearMap.id ℝ E)).toLinearMap) from rfl]
  rw [LinearMap.det_comp]
  congr 1
  rw [ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
    show (↑(ContinuousLinearMap.id ℝ E) : E →ₗ[ℝ] E) = LinearMap.id from rfl,
    LinearMap.det_id, mul_one]

/-- **Determinant factorisation**, second block.  If the second factor of a `coprod` is precomposed
with `T` (`N = N' ∘ T`), then the determinant of the composite
`pairEquiv ∘ (L coprod N)` picks up the factor `det T`. -/
theorem det_comp_coprod_right {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Module.Free ℝ E] [Module.Finite ℝ E]
    (P : F ≃ₗ[ℝ] E × E) (L N N' : E →L[ℝ] F) (T : E →L[ℝ] E) (h : N = N'.comp T) :
    LinearMap.det (P.toLinearMap.comp ((L.coprod N).toLinearMap)) =
      LinearMap.det (P.toLinearMap.comp ((L.coprod N').toLinearMap)) * T.det := by
  have hcop : (L.coprod N) = ((L.coprod N').comp ((ContinuousLinearMap.id ℝ E).prodMap T)) := by
    apply ContinuousLinearMap.ext
    rintro ⟨x, y⟩
    simp [h, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.coe_prodMap']
  have h2 : (L.coprod N).toLinearMap = ((L.coprod N').toLinearMap).comp
      (((ContinuousLinearMap.id ℝ E).prodMap T).toLinearMap) := by
    rw [hcop]; rfl
  rw [h2]
  rw [show P.toLinearMap.comp (((L.coprod N').toLinearMap).comp
        (((ContinuousLinearMap.id ℝ E).prodMap T).toLinearMap)) =
      (P.toLinearMap.comp ((L.coprod N').toLinearMap)).comp
        (((ContinuousLinearMap.id ℝ E).prodMap T).toLinearMap) from rfl]
  rw [LinearMap.det_comp]
  congr 1
  rw [ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
    show (↑(ContinuousLinearMap.id ℝ E) : E →ₗ[ℝ] E) = LinearMap.id from rfl,
    LinearMap.det_id, one_mul]

/-- If the two-chart determinant is nonzero then the **first** chart representation is injective. -/
theorem injective_fst_of_det_coprod_ne_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Module.Free ℝ E] [Module.Finite ℝ E]
    (P : F ≃ₗ[ℝ] E × E) (L N : E →L[ℝ] F)
    (h : LinearMap.det (P.toLinearMap.comp ((L.coprod N).toLinearMap)) ≠ 0) :
    Function.Injective ⇑L := by
  set A := P.toLinearMap.comp ((L.coprod N).toLinearMap) with hA
  have hker : A.ker = ⊥ := by
    by_contra hk
    exact h ((LinearMap.det_eq_zero_iff_ker_ne_bot).2 hk)
  have hinj : Function.Injective ⇑A := LinearMap.ker_eq_bot.mp hker
  intro x y hxy
  have h1 : A (x, 0) = A (y, 0) := by
    show P.toLinearMap ((L.coprod N) (x, 0)) = P.toLinearMap ((L.coprod N) (y, 0))
    rw [show (L.coprod N) (x, 0) = L x from by simp [ContinuousLinearMap.coprod_apply],
      show (L.coprod N) (y, 0) = L y from by simp [ContinuousLinearMap.coprod_apply], hxy]
  have := hinj h1
  exact (Prod.ext_iff.mp this).1

/-- If the two-chart determinant is nonzero then the **second** chart representation is
injective. -/
theorem injective_snd_of_det_coprod_ne_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Module.Free ℝ E] [Module.Finite ℝ E]
    (P : F ≃ₗ[ℝ] E × E) (L N : E →L[ℝ] F)
    (h : LinearMap.det (P.toLinearMap.comp ((L.coprod N).toLinearMap)) ≠ 0) :
    Function.Injective ⇑N := by
  set A := P.toLinearMap.comp ((L.coprod N).toLinearMap) with hA
  have hker : A.ker = ⊥ := by
    by_contra hk
    exact h ((LinearMap.det_eq_zero_iff_ker_ne_bot).2 hk)
  have hinj : Function.Injective ⇑A := LinearMap.ker_eq_bot.mp hker
  intro x y hxy
  have h1 : A (0, x) = A (0, y) := by
    show P.toLinearMap ((L.coprod N) (0, x)) = P.toLinearMap ((L.coprod N) (0, y))
    rw [show (L.coprod N) (0, x) = N x from by simp [ContinuousLinearMap.coprod_apply],
      show (L.coprod N) (0, y) = N y from by simp [ContinuousLinearMap.coprod_apply], hxy]
  have := hinj h1
  exact (Prod.ext_iff.mp this).2

/-! ## Change of chart -/

/-- The transition map of two charts of an oriented atlas, `u ↦ c' (c.symm u)`, is differentiable
at `c p`: this follows from the positivity of its Jacobian determinant, since the `fderiv` of a
non-differentiable map is `0` (of determinant `0` in positive dimension). -/
theorem differentiableAt_transition {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))}
    (hA : IsOrientedAtlas A)
    {c c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ A) (hc' : c' ∈ A) {p : M} (hp : p ∈ c.source) (hp' : p ∈ c'.source) :
    DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => c' (c.symm u)) (c p) := by
  by_contra h
  have hpos := (hA.2 c hc c' hc' p hp hp')
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    rw [finrank_euclideanSpace_fin]; omega
  have hz : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c' (c.symm u)) (c p)).det = 0 := by
    rw [fderiv_zero_of_not_differentiableAt h, ContinuousLinearMap.det]
    rw [show (↑(0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = 0 from rfl]
    rw [LinearMap.det_zero, zero_pow hfin]
  rw [hz] at hpos
  exact lt_irrefl 0 hpos

/-- **Change of the first chart.**  For two charts `c, c'` of an oriented atlas containing `p`,
`pairDet f c c₂ p p₂` differs from `pairDet f c' c₂ p p₂` by the determinant of the transition
`c' ∘ c.symm` at `c p`. -/
theorem pairDet_change_first {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : IsOrientedAtlas A) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (c c' c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ A) (hc' : c' ∈ A) (p p₂ : M) (hp : p ∈ c.source) (hp' : p ∈ c'.source)
    (hdiff : DifferentiableAt ℝ
      (fun u : EuclideanSpace ℝ (Fin n) => f (c'.symm u)) (c' p)) :
    pairDet f c c₂ p p₂ = pairDet f c' c₂ p p₂ *
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c' (c.symm u)) (c p)).det := by
  have hτ : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => c' (c.symm u)) (c p) :=
    differentiableAt_transition hn hA hc hc' hp hp'
  have hval : c' (c.symm (c p)) = c' p := by rw [c.left_inv hp]
  have hevent : ∀ᶠ u in 𝓝 (c p), c.symm u ∈ c'.source :=
    (c.tendsto_symm hp).eventually (c'.open_source.mem_nhds hp')
  have hEE : (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u)) =ᶠ[𝓝 (c p)]
      (fun u => f (c'.symm u)) ∘ (fun u : EuclideanSpace ℝ (Fin n) => c' (c.symm u)) := by
    filter_upwards [hevent] with u hu
    simp only [Function.comp_apply]
    rw [c'.left_inv hu]
  have hchain : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u)) (c p) =
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c'.symm u)) (c' p)).comp
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c' (c.symm u)) (c p)) := by
    rw [hEE.fderiv_eq]
    rw [fderiv_comp (c p) (by rw [hval]; exact hdiff) hτ, hval]
  rw [pairDet, pairDet]
  exact det_comp_coprod_left (Work.Projection.pairEquiv n) _ _ _ _ hchain

/-- **Change of the second chart.**  For two charts `c₂, c₂'` of an oriented atlas containing `p₂`,
`pairDet f c c₂ p p₂` differs from `pairDet f c c₂' p p₂` by the determinant of the transition
`c₂' ∘ c₂.symm` at `c₂ p₂`. -/
theorem pairDet_change_second {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : IsOrientedAtlas A) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (c c₂ c₂' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc₂ : c₂ ∈ A) (hc₂' : c₂' ∈ A) (p p₂ : M) (hp₂ : p₂ ∈ c₂.source)
    (hp₂' : p₂ ∈ c₂'.source)
    (hdiff : DifferentiableAt ℝ
      (fun u : EuclideanSpace ℝ (Fin n) => f (c₂'.symm u)) (c₂' p₂)) :
    pairDet f c c₂ p p₂ = pairDet f c c₂' p p₂ *
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c₂' (c₂.symm u)) (c₂ p₂)).det := by
  have hτ : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => c₂' (c₂.symm u)) (c₂ p₂) :=
    differentiableAt_transition hn hA hc₂ hc₂' hp₂ hp₂'
  have hval : c₂' (c₂.symm (c₂ p₂)) = c₂' p₂ := by rw [c₂.left_inv hp₂]
  have hevent : ∀ᶠ u in 𝓝 (c₂ p₂), c₂.symm u ∈ c₂'.source :=
    (c₂.tendsto_symm hp₂).eventually (c₂'.open_source.mem_nhds hp₂')
  have hEE : (fun u : EuclideanSpace ℝ (Fin n) => f (c₂.symm u)) =ᶠ[𝓝 (c₂ p₂)]
      (fun u => f (c₂'.symm u)) ∘ (fun u : EuclideanSpace ℝ (Fin n) => c₂' (c₂.symm u)) := by
    filter_upwards [hevent] with u hu
    simp only [Function.comp_apply]
    rw [c₂'.left_inv hu]
  have hchain : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₂.symm u)) (c₂ p₂) =
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₂'.symm u)) (c₂' p₂)).comp
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c₂' (c₂.symm u)) (c₂ p₂)) := by
    rw [hEE.fderiv_eq]
    rw [fderiv_comp (c₂ p₂) (by rw [hval]; exact hdiff) hτ, hval]
  rw [pairDet, pairDet]
  exact det_comp_coprod_right (Work.Projection.pairEquiv n) _ _ _ _ hchain

/-- If the two-chart determinant `pairDet f c c₂ p p₂` is nonzero then the chart representation of
`f` through the **first** chart is differentiable at `c p`. -/
theorem differentiableAt_fst_of_pairDet_ne_zero {n : ℕ} (hn : 1 ≤ n) {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (c c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (p p₂ : M)
    (h : pairDet f c c₂ p p₂ ≠ 0) :
    DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c.symm u)) (c p) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  rw [pairDet] at h
  have hinj := injective_fst_of_det_coprod_ne_zero (Work.Projection.pairEquiv n)
    (fderiv ℝ (fun u => f (c.symm u)) (c p)) (fderiv ℝ (fun u => f (c₂.symm u)) (c₂ p₂)) h
  by_contra hna
  have hL0 : fderiv ℝ (fun u => f (c.symm u)) (c p) = 0 :=
    fderiv_zero_of_not_differentiableAt hna
  obtain ⟨x, hx⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  have hx0 : fderiv ℝ (fun u => f (c.symm u)) (c p) x = 0 := by rw [hL0]; rfl
  exact hx (hinj (by rw [hx0]; simp))

/-- If the two-chart determinant `pairDet f c c₂ p p₂` is nonzero then the chart representation of
`f` through the **second** chart is differentiable at `c₂ p₂`. -/
theorem differentiableAt_snd_of_pairDet_ne_zero {n : ℕ} (hn : 1 ≤ n) {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (c c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (p p₂ : M)
    (h : pairDet f c c₂ p p₂ ≠ 0) :
    DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₂.symm u)) (c₂ p₂) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  rw [pairDet] at h
  have hinj := injective_snd_of_det_coprod_ne_zero (Work.Projection.pairEquiv n)
    (fderiv ℝ (fun u => f (c.symm u)) (c p)) (fderiv ℝ (fun u => f (c₂.symm u)) (c₂ p₂)) h
  by_contra hna
  have hL0 : fderiv ℝ (fun u => f (c₂.symm u)) (c₂ p₂) = 0 :=
    fderiv_zero_of_not_differentiableAt hna
  obtain ⟨x, hx⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  have hx0 : fderiv ℝ (fun u => f (c₂.symm u)) (c₂ p₂) x = 0 := by rw [hL0]; rfl
  exact hx (hinj (by rw [hx0]; simp))

/-- In dimension `0` the model space is a point and every two-chart determinant equals `1`; both
sides of `oppositeSign_iff` are then false. -/
theorem pairDet_eq_one_of_n_eq_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * 0)))
    (c c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 0))) (a b : M) :
    pairDet f c c' a b = 1 := by
  haveI : Subsingleton (EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0)) :=
    inferInstance
  have hL : fderiv ℝ (fun u => f (c.symm u)) (c a) = 0 := Subsingleton.elim _ _
  have hN : fderiv ℝ (fun u => f (c'.symm u)) (c' b) = 0 := Subsingleton.elim _ _
  rw [pairDet, hL, hN]
  have hzero : ContinuousLinearMap.coprod (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ]
        EuclideanSpace ℝ (Fin 0)) (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ]
        EuclideanSpace ℝ (Fin 0)) = 0 := by
    apply ContinuousLinearMap.ext
    rintro ⟨x, y⟩
    simp [ContinuousLinearMap.coprod_apply]
  rw [hzero]
  simp

/-! ## The main statement -/

theorem oppositeSign_iff {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : Work.Whitney.IsOrientedAtlas A)
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p₁ p₂ q₁ q₂ : M)
    (c₁ c₂ c₃ c₄ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc₁ : c₁ ∈ A) (hc₂ : c₂ ∈ A) (hc₃ : c₃ ∈ A) (hc₄ : c₄ ∈ A)
    (hp₁ : p₁ ∈ c₁.source) (hp₂ : p₂ ∈ c₂.source) (hq₁ : q₁ ∈ c₃.source) (hq₂ : q₂ ∈ c₄.source) :
    (Work.Whitney.pairDet f c₁ c₂ p₁ p₂ * Work.Whitney.pairDet f c₃ c₄ q₁ q₂ < 0) ↔
      Work.Whitney.OppositeSign A f p₁ p₂ q₁ q₂ := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    constructor
    · intro h
      have h' : (1 : ℝ) * 1 < 0 := by
        rwa [pairDet_eq_one_of_n_eq_zero, pairDet_eq_one_of_n_eq_zero] at h
      exact absurd h' (by norm_num)
    · rintro ⟨d₁, d₂, d₃, d₄, -, -, -, -, -, -, -, -, hneg⟩
      rw [pairDet_eq_one_of_n_eq_zero, pairDet_eq_one_of_n_eq_zero] at hneg
      exact absurd hneg (by norm_num)
  · constructor
    · intro h
      exact ⟨c₁, c₂, c₃, c₄, hc₁, hc₂, hc₃, hc₄, hp₁, hp₂, hq₁, hq₂, h⟩
    · rintro ⟨d₁, d₂, d₃, d₄, hd₁, hd₂, hd₃, hd₄, hdp₁, hdp₂, hdq₁, hdq₂, hneg⟩
      have hX : pairDet f d₁ d₂ p₁ p₂ ≠ 0 := by
        intro hz
        rw [hz, zero_mul] at hneg
        exact (lt_irrefl (0 : ℝ)) hneg
      have hY : pairDet f d₃ d₄ q₁ q₂ ≠ 0 := by
        intro hz
        rw [hz, mul_zero] at hneg
        exact (lt_irrefl (0 : ℝ)) hneg
      have hd₁d : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (d₁.symm u))
          (d₁ p₁) := differentiableAt_fst_of_pairDet_ne_zero hn f d₁ d₂ p₁ p₂ hX
      have hd₂d : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (d₂.symm u))
          (d₂ p₂) := differentiableAt_snd_of_pairDet_ne_zero hn f d₁ d₂ p₁ p₂ hX
      have hd₃d : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (d₃.symm u))
          (d₃ q₁) := differentiableAt_fst_of_pairDet_ne_zero hn f d₃ d₄ q₁ q₂ hY
      have hd₄d : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (d₄.symm u))
          (d₄ q₂) := differentiableAt_snd_of_pairDet_ne_zero hn f d₃ d₄ q₁ q₂ hY
      set T₁ := (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => d₁ (c₁.symm u)) (c₁ p₁)).det
        with hT₁def
      set T₂ := (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => d₂ (c₂.symm u)) (c₂ p₂)).det
        with hT₂def
      set T₃ := (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => d₃ (c₃.symm u)) (c₃ q₁)).det
        with hT₃def
      set T₄ := (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => d₄ (c₄.symm u)) (c₄ q₂)).det
        with hT₄def
      have hT₁ : 0 < T₁ := hA.2 c₁ hc₁ d₁ hd₁ p₁ hp₁ hdp₁
      have hT₂ : 0 < T₂ := hA.2 c₂ hc₂ d₂ hd₂ p₂ hp₂ hdp₂
      have hT₃ : 0 < T₃ := hA.2 c₃ hc₃ d₃ hd₃ q₁ hq₁ hdq₁
      have hT₄ : 0 < T₄ := hA.2 c₄ hc₄ d₄ hd₄ q₂ hq₂ hdq₂
      have e1 : pairDet f c₁ c₂ p₁ p₂ = pairDet f d₁ c₂ p₁ p₂ * T₁ :=
        pairDet_change_first hn A hA f c₁ d₁ c₂ hc₁ hd₁ p₁ p₂ hp₁ hdp₁ hd₁d
      have e2 : pairDet f d₁ c₂ p₁ p₂ = pairDet f d₁ d₂ p₁ p₂ * T₂ :=
        pairDet_change_second hn A hA f d₁ c₂ d₂ hc₂ hd₂ p₁ p₂ hp₂ hdp₂ hd₂d
      have e3 : pairDet f c₃ c₄ q₁ q₂ = pairDet f d₃ c₄ q₁ q₂ * T₃ :=
        pairDet_change_first hn A hA f c₃ d₃ c₄ hc₃ hd₃ q₁ q₂ hq₁ hdq₁ hd₃d
      have e4 : pairDet f d₃ c₄ q₁ q₂ = pairDet f d₃ d₄ q₁ q₂ * T₄ :=
        pairDet_change_second hn A hA f d₃ c₄ d₄ hc₄ hd₄ q₁ q₂ hq₂ hdq₂ hd₄d
      have hrw : pairDet f c₁ c₂ p₁ p₂ * pairDet f c₃ c₄ q₁ q₂ =
          (T₁ * T₂ * T₃ * T₄) *
            (pairDet f d₁ d₂ p₁ p₂ * pairDet f d₃ d₄ q₁ q₂) := by
        rw [e1, e2, e3, e4]; ring
      rw [hrw]
      exact mul_neg_of_pos_of_neg (mul_pos (mul_pos (mul_pos hT₁ hT₂) hT₃) hT₄) hneg

end Work.Whitney
