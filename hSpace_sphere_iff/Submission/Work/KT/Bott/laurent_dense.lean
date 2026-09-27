import Mathlib
import Submission.Work.KT.Fund.Laurent

namespace Work.KT.Bott

theorem laurent_dense (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (f : C(X × Sph ℂ, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : LaurentPolynomial C(X, ℂ), ‖laurentMap X p - f‖ < ε := by
  classical
  -- The coordinate `z` on `X × S¹` and its inverse, as elements of `C(X × S¹, ℂ)`.
  -- (`C(X × S¹, ℂ)` has no usable `Inv` instance -- inversion is not continuous at `0` -- so
  -- the inverse is taken as the underlying continuous map of the unit `(zUnit X)⁻¹`.)
  set z : C(X × Sph ℂ, ℂ) := (zUnit X : C(X × Sph ℂ, ℂ)) with hz
  set zinv : C(X × Sph ℂ, ℂ) := ((zUnit X)⁻¹ : (C(X × Sph ℂ, ℂ))ˣ).val with hzinv
  -- The generating set: the pullbacks of functions on `X`, together with `z` and `z⁻¹`.
  set G : Set C(X × Sph ℂ, ℂ) :=
    Set.range (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))) ∪ {z} ∪ {zinv} with hG
  set A : StarSubalgebra ℂ C(X × Sph ℂ, ℂ) := StarAlgebra.adjoin ℂ G with hA
  -- `star` of a pullback is the pullback of the `star` (pullback is a `⋆`-algebra map).
  have hstar_pull : ∀ a : C(X, ℂ),
      star (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X)) a)
        = pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X)) (star a) :=
    fun a => (map_star (ContinuousMap.compStarAlgHom' ℂ ℂ
      (ContinuousMap.fst : C(X × Sph ℂ, X))) a).symm
  -- `star z = z⁻¹`, pointwise: on the unit circle `ζ̄ = ζ⁻¹`.
  have hstar_z : star z = zinv := by
    rw [hz, hzinv]
    ext y
    simp only [ContinuousMap.star_apply, zUnit_apply]
    show star (y.2 : ℂ) = ((y.2 : ℂ))⁻¹
    rw [RCLike.inv_eq_conj]
    · rfl
    · have h := y.2.2
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
      exact h
  -- Each generator, and its `star`, lies in the image of `laurentMap X`.
  have hmem_gen : ∀ x ∈ G, x ∈ Set.range (laurentMap X) ∧ star x ∈ Set.range (laurentMap X) := by
    intro x hx
    rw [hG] at hx
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hx
    rcases hx with (⟨a, rfl⟩ | rfl) | rfl
    · exact ⟨⟨LaurentPolynomial.C a, laurentMap_C X a⟩,
        ⟨LaurentPolynomial.C (star a), by rw [laurentMap_C, hstar_pull]⟩⟩
    · exact ⟨⟨LaurentPolynomial.T 1, by rw [hz, laurentMap_T]; norm_num⟩,
        ⟨LaurentPolynomial.T (-1), by rw [hstar_z, hzinv, laurentMap_T]; norm_num⟩⟩
    · exact ⟨⟨LaurentPolynomial.T (-1), by rw [hzinv, laurentMap_T]; norm_num⟩,
        ⟨LaurentPolynomial.T 1, by rw [← hstar_z, star_star, hz, laurentMap_T]; norm_num⟩⟩
  -- Consequently every element of the star subalgebra `A` lies in the image of `laurentMap X`.
  have hA_le : ∀ x ∈ A, x ∈ Set.range (laurentMap X) ∧ star x ∈ Set.range (laurentMap X) := by
    intro x hx
    rw [hA] at hx
    refine StarAlgebra.adjoin_induction (mem := fun y hy => hmem_gen y hy)
      (algebraMap := fun r => ?_) (add := fun y y' _ _ ihy ihy' => ?_)
      (mul := fun y y' _ _ ihy ihy' => ?_) (star := fun y _ ihy => ?_) hx
    · -- constants
      refine ⟨⟨LaurentPolynomial.C (ContinuousMap.const X r), ?_⟩,
        ⟨LaurentPolynomial.C (ContinuousMap.const X (star r)), ?_⟩⟩
      · rw [laurentMap_C]; ext y; simp [pullAlg, ContinuousMap.const_apply]
      · rw [laurentMap_C]; ext y; simp [pullAlg, ContinuousMap.const_apply]
    · -- sums
      obtain ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩ := ihy
      obtain ⟨⟨q, hq⟩, ⟨q', hq'⟩⟩ := ihy'
      exact ⟨⟨p + q, by rw [map_add, hp, hq]⟩,
        ⟨p' + q', by rw [map_add, hp', hq', star_add]⟩⟩
    · -- products
      obtain ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩ := ihy
      obtain ⟨⟨q, hq⟩, ⟨q', hq'⟩⟩ := ihy'
      exact ⟨⟨p * q, by rw [map_mul, hp, hq]⟩,
        ⟨p' * q', by rw [map_mul, hp', hq', star_mul, mul_comm]⟩⟩
    · -- star
      exact ⟨ihy.2, by rw [star_star]; exact ihy.1⟩
  have hsub : (A : Set C(X × Sph ℂ, ℂ)) ⊆ Set.range (laurentMap X) :=
    fun x hx => (hA_le x hx).1
  -- `A` separates points: distinct `X`-coordinates by a pullback, distinct `S¹`-coordinates by `z`.
  have hsep : A.SeparatesPoints := by
    intro y₁ y₂ hy
    obtain ⟨x₁, s₁⟩ := y₁
    obtain ⟨x₂, s₂⟩ := y₂
    by_cases hx : x₁ = x₂
    · -- same `X`-coordinate: use `z`
      subst hx
      have hs : s₁ ≠ s₂ := by intro h; exact hy (by rw [h])
      refine ⟨z, ⟨z, ?_, rfl⟩, ?_⟩
      · rw [hA]; exact StarAlgebra.subset_adjoin ℂ G (by rw [hG]; simp)
      · intro h
        rw [hz] at h
        simp only [zUnit_apply] at h
        exact hs (Subtype.ext h)
    · -- different `X`-coordinates: separate them by a continuous function, as a pullback
      obtain ⟨g, hg1, hg2, -⟩ :=
        exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := x₁))
          (isClosed_singleton (x := x₂)) (Set.disjoint_singleton.mpr hx)
      let a : C(X, ℂ) := ⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
      refine ⟨a.comp ContinuousMap.fst, ⟨a.comp ContinuousMap.fst, ?_, rfl⟩, ?_⟩
      · rw [hA]; exact StarAlgebra.subset_adjoin ℂ G (by
          rw [hG]; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_range]
          exact Or.inl (Or.inl ⟨a, rfl⟩))
      · intro h
        change a x₁ = a x₂ at h
        change (g x₁ : ℂ) = (g x₂ : ℂ) at h
        rw [hg1 (by simp), hg2 (by simp)] at h
        norm_num at h
  -- Complex Stone--Weierstrass: `A` is dense, and contained in the image of `laurentMap X`.
  have htop : A.topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hcl : closure (A : Set C(X × Sph ℂ, ℂ)) = ⊤ := by
    rw [← StarSubalgebra.topologicalClosure_coe A, htop]
    rfl
  have hmem : f ∈ closure (Set.range (laurentMap X)) :=
    closure_mono hsub (by rw [hcl]; exact Set.mem_univ f)
  -- `f` is within `ε` of the image of `laurentMap X`.
  obtain ⟨g, hg, hgd⟩ := Metric.mem_closure_iff.mp hmem ε hε
  obtain ⟨p, rfl⟩ := hg
  exact ⟨p, by simpa [dist_eq_norm, norm_sub_rev] using hgd⟩

end Work.KT.Bott
