import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.CWComplex.Classical.Basic

namespace Commons.Topology.CWComplex

open Set

/-- **Transport of a CW-complex structure across a homeomorphism.**

Given a CW-complex structure on all of `Y` whose cell types are `hC.cell n`, and a
homeomorphism `e : Y ≃ₜ Y'`, there is a CW-complex structure on all of `Y'` whose
`n`-cells are indexed by a type equivalent to `hC.cell n`.

The construction picks a point `e (map n i 0)` in the image of each open cell and uses
those points (a subset of `Y'`) as the indexing type of the `n`-cells of `Y'`; the
characteristic maps are obtained by postcomposing the old ones with `e`. -/
theorem exists_cwComplex_homeomorph_univ {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']
    (hC : Topology.CWComplex (X := Y) Set.univ) (e : Y ≃ₜ Y') :
    ∃ hC' : Topology.CWComplex (X := Y') Set.univ,
      ∀ n : ℕ, Nonempty (hC'.cell n ≃ hC.cell n) := by
  -- The point `e (map n i 0)` distinguishes the `n`-cells of `hC`.
  have hf : ∀ n, Function.Injective (fun i : hC.cell n => e (hC.map n i 0)) := by
    intro n i j hij
    by_contra hne
    have hne' : (⟨n, i⟩ : Σ n, hC.cell n) ≠ ⟨n, j⟩ := by
      intro h; exact hne (eq_of_heq (Sigma.mk.inj h).2)
    have hd := Topology.RelCWComplex.disjoint_openCell_of_ne (C := (Set.univ : Set Y)) hne'
    have hi : hC.map n i 0 ∈ Topology.RelCWComplex.openCell (C := (Set.univ : Set Y)) n i :=
      mem_image_of_mem _ (by simp [Metric.mem_ball])
    have hj : hC.map n j 0 ∈ Topology.RelCWComplex.openCell (C := (Set.univ : Set Y)) n j :=
      mem_image_of_mem _ (by simp [Metric.mem_ball])
    have heq : hC.map n i 0 = hC.map n j 0 := e.injective hij
    rw [heq] at hi
    exact (Set.disjoint_left.mp hd) hi hj
  -- New `n`-cells of `Y'`: the image under `e` of the chosen point in each old `n`-cell.
  let φ : ∀ n, Set.range (fun i : hC.cell n => e (hC.map n i 0)) ≃ hC.cell n :=
    fun n => (Equiv.ofInjective _ (hf n)).symm
  have himg : ∀ (n : ℕ) (j : Set.range (fun i : hC.cell n => e (hC.map n i 0)))
      (s : Set (Fin n → ℝ)),
      ((hC.map n (φ n j)).transEquiv e.toEquiv) '' s = e.toEquiv '' (hC.map n (φ n j) '' s) := by
    intro n j s
    rw [PartialEquiv.coe_transEquiv, Set.image_comp]
  refine ⟨{ cell := fun n => Set.range (fun i : hC.cell n => e (hC.map n i 0))
            map := fun n j => (hC.map n (φ n j)).transEquiv e.toEquiv
            source_eq := by
              intro n j
              simp [PartialEquiv.transEquiv_source, hC.source_eq]
            continuousOn := by
              intro n j
              simpa only [PartialEquiv.coe_transEquiv, Homeomorph.coe_toEquiv] using
                e.continuous.comp_continuousOn (hC.continuousOn n (φ n j))
            continuousOn_symm := by
              intro n j
              rw [PartialEquiv.coe_transEquiv_symm, PartialEquiv.transEquiv_target]
              exact ContinuousOn.comp (hC.continuousOn_symm n (φ n j))
                ((e.symm.continuous.continuousOn).mono (subset_univ _)) (fun x hx => hx)
            pairwiseDisjoint' := by
              rintro ⟨n, j⟩ - ⟨m, k⟩ - hab
              change Disjoint (((hC.map n (φ n j)).transEquiv e.toEquiv) '' Metric.ball 0 1)
                (((hC.map m (φ m k)).transEquiv e.toEquiv) '' Metric.ball 0 1)
              have hΦ : (⟨n, φ n j⟩ : Σ t, hC.cell t) ≠ ⟨m, φ m k⟩ := by
                intro h
                apply hab
                obtain ⟨h1, h2⟩ := Sigma.mk.inj h
                subst h1
                have h2' : φ n j = φ n k := eq_of_heq h2
                have h3 : j = k := (φ n).injective h2'
                subst h3
                rfl
              have hd := Topology.RelCWComplex.disjoint_openCell_of_ne (C := (Set.univ : Set Y)) hΦ
              rw [himg n j (Metric.ball 0 1), himg m k (Metric.ball 0 1)]
              refine Set.disjoint_image_image (fun x hx y hy hxy => ?_)
              have hxy' : x = y := e.injective hxy
              rw [← hxy'] at hy
              exact (Set.disjoint_left.mp hd) hx hy
            mapsTo' := by
              intro n j
              obtain ⟨I₀, hI₀⟩ := hC.mapsTo' n (φ n j)
              refine ⟨fun m => (I₀ m).map ((φ m).symm).toEmbedding, ?_⟩
              intro x hx
              have hx' := hI₀ hx
              simp only [Set.mem_iUnion, Set.mem_image] at hx' ⊢
              obtain ⟨m, hm, k, hk, t, ht, htk⟩ := hx'
              refine ⟨m, hm, (φ m).symm k, ?_, t, ht, ?_⟩
              · rw [Finset.mem_map_equiv]
                simpa using hk
              · simp only [PartialEquiv.coe_transEquiv, Function.comp_apply,
                  Equiv.apply_symm_apply, htk]
            closed' := by
              intro A _ hA
              have hB : ∀ n (j : hC.cell n),
                  IsClosed (e ⁻¹' A ∩ hC.map n j '' Metric.closedBall 0 1) := by
                intro n j
                have h := hA n ((φ n).symm j)
                have himg2 : ((hC.map n (φ n ((φ n).symm j))).transEquiv e.toEquiv) ''
                    Metric.closedBall 0 1 = e '' (hC.map n j '' Metric.closedBall 0 1) := by
                  rw [PartialEquiv.coe_transEquiv, Set.image_comp, Equiv.apply_symm_apply (φ n) j,
                    Homeomorph.coe_toEquiv]
                rw [himg2] at h
                have hthis : e ⁻¹' A ∩ hC.map n j '' Metric.closedBall 0 1 =
                    e ⁻¹' (A ∩ e '' (hC.map n j '' Metric.closedBall 0 1)) := by
                  rw [Set.preimage_inter, Set.preimage_image_eq _ e.injective]
                rw [hthis]
                exact h.preimage e.continuous
              have hBc : IsClosed (e ⁻¹' A) := hC.closed' (e ⁻¹' A) (fun x _ => trivial) hB
              have hAeq : A = e '' (e ⁻¹' A) := (Set.image_preimage_eq A e.surjective).symm
              rw [hAeq]
              exact e.isClosedMap (e ⁻¹' A) hBc
            union' := by
              apply Set.eq_univ_iff_forall.mpr
              intro y
              have hy : e.symm y ∈ (⋃ (n : ℕ) (j : hC.cell n),
                  hC.map n j '' Metric.closedBall 0 1) := by
                rw [hC.union']; trivial
              simp only [Set.mem_iUnion, Set.mem_image] at hy
              obtain ⟨n, k, t, ht, htk⟩ := hy
              simp only [Set.mem_iUnion, Set.mem_image]
              refine ⟨n, (φ n).symm k, t, ht, ?_⟩
              simp only [PartialEquiv.coe_transEquiv, Function.comp_apply,
                Equiv.apply_symm_apply, htk, Homeomorph.coe_toEquiv,
                Homeomorph.apply_symm_apply] }, ?_⟩
  · intro n
    exact ⟨φ n⟩

end Commons.Topology.CWComplex