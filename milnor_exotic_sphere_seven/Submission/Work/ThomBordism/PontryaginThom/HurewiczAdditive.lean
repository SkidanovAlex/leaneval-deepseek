import Submission.Work.ThomBordism.PontryaginThom.WedgeIsland

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Additivity of the Hurewicz class, inside the Pontryagin–Thom island

`Work.Stems.hurewiczChain_transAt` (`Work.Stems`, copied into the island by `WedgeIsland.lean`) says
that the Hurewicz chain map is additive under the cube concatenation `GenLoop.transAt`.  Descending
to `HomotopyGroup` — which is how `Work.Stems.hurewiczMap_mul` is proved in the Stems chapter — gives
the multiplicativity of the Hurewicz map; here it is stated for the island's descent
`hurewiczClassOf` of `Work.Stems.hurewiczChain`:

* `hurewiczClassOf_mul` — `hurewiczClassOf (α * β) = hurewiczClassOf α + hurewiczClassOf β`;
* `hurewiczClassOf_one` — `hurewiczClassOf 1 = 0` (the unit class is the class of the constant cube,
  whose Hurewicz class vanishes because it factors through a point);
* `hurewiczClassOf_finsetProd` — the same for a finite product, the form in which additivity over
  families (`Additivity.lean`) consumes it.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.ThomBordism.PontryaginThom

noncomputable section

open Work.Cohomology

/-- **The Hurewicz class is additive under the group structure**:
`hurewiczClassOf (α * β) = hurewiczClassOf α + hurewiczClassOf β`.

This is the descent of the pinch computation `Work.Stems.hurewiczChain_transAt`, exactly as
`Work.Stems.hurewiczMap_mul` descends it (that proof cannot be imported here; see
`WedgeIsland.lean`). -/
theorem hurewiczClassOf_mul {T : Type} [TopologicalSpace T] {t₀ : T} {n : ℕ} (hn : 1 ≤ n)
    [Nonempty (Fin n)] (α β : HomotopyGroup (Fin n) T t₀) :
    hurewiczClassOf n hn t₀ (α * β) = hurewiczClassOf n hn t₀ α + hurewiczClassOf n hn t₀ β := by
  induction α using Quotient.inductionOn with
  | h p =>
    induction β using Quotient.inductionOn with
    | h q =>
      simp only [HomotopyGroup.mul_spec (i := (⟨0, hn⟩ : Fin n)), hurewiczClassOf_mk]
      exact Work.Stems.hurewiczChain_transAt n hn ⟨0, hn⟩ p q

/-- **The Hurewicz class of the unit class vanishes** (the unit is the class of the constant cube,
whose lift to the sphere is constant and therefore induces `0` on positive-degree homology). -/
theorem hurewiczClassOf_one {T : Type} [TopologicalSpace T] {t₀ : T} {n : ℕ} (hn : 1 ≤ n)
    [Nonempty (Fin n)] :
    hurewiczClassOf n hn t₀ (1 : HomotopyGroup (Fin n) T t₀) = 0 := by
  have hconst : Work.Stems.cubeLift n hn (GenLoop.const : Ω^ (Fin n) T t₀)
      = ContinuousMap.const (Work.Stems.sphere n) t₀ := by
    ext z
    obtain ⟨q, rfl⟩ := (Work.Stems.collapseMap_isQuotientMap n hn).surjective z
    rw [← ContinuousMap.comp_apply, Work.Stems.cubeLift_comp]
    rfl
  have hz : Work.Stems.hurewiczChain n hn t₀ (GenLoop.const : Ω^ (Fin n) T t₀) = 0 := by
    simp only [Work.Stems.hurewiczChain, hconst, Work.Stems.hurewiczClass_eq_hm]
    simpa using congrArg (fun g => g (Work.Stems.sphereGenerator n hn))
      (Work.Stems.wfs_hm_const' (n := n) (A := Work.Stems.sphere n) t₀ hn)
  rw [HomotopyGroup.one_def]
  change Work.Stems.hurewiczChain n hn t₀ (GenLoop.const : Ω^ (Fin n) T t₀) = 0
  exact hz

/-- **Additivity for finite products**: the Hurewicz class of a finite product is the sum of the
Hurewicz classes. -/
theorem hurewiczClassOf_finsetProd {ι : Type} {T : Type} [TopologicalSpace T] {t₀ : T} {n : ℕ}
    (hn : 1 ≤ n) [Nonempty (Fin n)] [Nontrivial (Fin n)] (s : Finset ι)
    (f : ι → HomotopyGroup (Fin n) T t₀) :
    hurewiczClassOf n hn t₀ (∏ i ∈ s, f i) = ∑ i ∈ s, hurewiczClassOf n hn t₀ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      exact hurewiczClassOf_one (T := T) (t₀ := t₀) (n := n) (hn := hn)
  | insert a s ha ih =>
      rw [Finset.prod_insert (s := s) (f := f) ha, Finset.sum_insert (s := s) ha,
        hurewiczClassOf_mul (T := T) (t₀ := t₀) (n := n) (hn := hn) (f a) (s.prod f), ih]

/-- Additivity for a `Fintype`-indexed product (the form used by the assembly). -/
theorem hurewiczClassOf_prod {ι : Type} [Fintype ι] {T : Type} [TopologicalSpace T] {t₀ : T}
    {n : ℕ} (hn : 1 ≤ n) [Nonempty (Fin n)] [Nontrivial (Fin n)]
    (f : ι → HomotopyGroup (Fin n) T t₀) :
    hurewiczClassOf n hn t₀ (∏ i, f i) = ∑ i, hurewiczClassOf n hn t₀ (f i) := by
  simpa using hurewiczClassOf_finsetProd (n := n) (hn := hn) (t₀ := t₀) (Finset.univ : Finset ι) f

end

end Work.ThomBordism.PontryaginThom
