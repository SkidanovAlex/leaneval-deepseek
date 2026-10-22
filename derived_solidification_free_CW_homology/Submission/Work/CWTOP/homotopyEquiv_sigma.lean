import Mathlib

/-!
# Disjoint unions of homotopy equivalences

If `e i : A i ≃ₕ B i` is a homotopy equivalence for every `i`, then the induced map
`Σ i, A i → Σ i, B i` between the disjoint unions is again a homotopy equivalence.

The mathematical content is the auxiliary statement `homotopic_sigmaMap`: homotopic maps
`f i, g i : C(A i, B i)` induce homotopic maps `Σ i, A i → Σ i, B i`.  The homotopy is
obtained from the degreewise homotopies `I × A i → B i` by the homeomorphism
`I × (Σ i, A i) ≅ Σ i, (A i × I)` (`(Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib`).

This is the "disjoint unions are computed degreewise" input used in the CW induction for the
comparison `ℤ[X] → A(X)` of the solidification project (hole 10).
-/

namespace Work.CWTOP

open scoped ContinuousMap unitInterval

/-- **Homotopic maps induce homotopic maps on disjoint unions.**
If `f i` and `g i` are homotopic for every `i`, then `Sigma.map id f` and `Sigma.map id g`
are homotopic as maps `Σ i, A i → Σ i, B i`. -/
theorem homotopic_sigmaMap {ι : Type} {A B : ι → Type} [∀ i, TopologicalSpace (A i)]
    [∀ i, TopologicalSpace (B i)] {f g : ∀ i, C(A i, B i)}
    (h : ∀ i, (f i).Homotopic (g i)) :
    (⟨Sigma.map id (fun i => ⇑(f i)), continuous_sigma_map.2 fun i => (f i).continuous⟩ :
        C(Σ i, A i, Σ i, B i)).Homotopic
      ⟨Sigma.map id (fun i => ⇑(g i)), continuous_sigma_map.2 fun i => (g i).continuous⟩ := by
  classical
  let F : ∀ i, (f i).Homotopy (g i) := fun i => (h i).some
  let G : ∀ i, C(A i × I, B i) := fun i =>
    ((F i).toContinuousMap).comp ((Homeomorph.prodComm (A i) I) : C(A i × I, I × A i))
  have hcont : Continuous (Sigma.map id (fun i => ⇑(G i))) :=
    continuous_sigma_map.2 fun i => (G i).continuous
  refine ⟨{
    toFun := (⟨Sigma.map id (fun i => ⇑(G i)), hcont⟩ : C(Σ i, A i × I, Σ i, B i)).comp
      ((Homeomorph.prodComm I (Σ i, A i)).trans (Homeomorph.sigmaProdDistrib (X := A)) :
        C(I × (Σ i, A i), Σ i, A i × I))
    map_zero_left := by
      intro x
      obtain ⟨i, a⟩ := x
      simp [G, F, Sigma.map_mk, Prod.swap_prod_mk]
    map_one_left := by
      intro x
      obtain ⟨i, a⟩ := x
      simp [G, F, Sigma.map_mk, Prod.swap_prod_mk] }⟩

/-- **A disjoint union of homotopy equivalences is a homotopy equivalence.**
Given homotopy equivalences `A i ≃ₕ B i` for all `i`, the induced map on the disjoint unions
`Σ i, A i → Σ i, B i` is a homotopy equivalence. -/
theorem homotopyEquiv_sigma {ι : Type} (A B : ι → Type) [∀ i, TopologicalSpace (A i)]
    [∀ i, TopologicalSpace (B i)]
    (e : ∀ i, ContinuousMap.HomotopyEquiv (TopCat.of (A i)) (TopCat.of (B i))) :
    Nonempty (ContinuousMap.HomotopyEquiv (TopCat.of (Σ i, A i)) (TopCat.of (Σ i, B i))) := by
  classical
  refine ⟨{
    toFun := ⟨Sigma.map id (fun i => ⇑((e i).toFun)),
      continuous_sigma_map.2 fun i => (e i).toFun.continuous⟩
    invFun := ⟨Sigma.map id (fun i => ⇑((e i).invFun)),
      continuous_sigma_map.2 fun i => (e i).invFun.continuous⟩
    left_inv := ?_
    right_inv := ?_ }⟩
  · obtain ⟨H⟩ := homotopic_sigmaMap (f := fun i => (e i).invFun.comp (e i).toFun)
      (g := fun i => ContinuousMap.id (A i)) (fun i => (e i).left_inv)
    refine ⟨H.cast ?_ ?_⟩
    · ext1 x
      obtain ⟨i, a⟩ := x
      rfl
    · ext1 x
      obtain ⟨i, a⟩ := x
      rfl
  · obtain ⟨H⟩ := homotopic_sigmaMap (f := fun i => (e i).toFun.comp (e i).invFun)
      (g := fun i => ContinuousMap.id (B i)) (fun i => (e i).right_inv)
    refine ⟨H.cast ?_ ?_⟩
    · ext1 x
      obtain ⟨i, a⟩ := x
      rfl
    · ext1 x
      obtain ⟨i, a⟩ := x
      rfl

end Work.CWTOP
