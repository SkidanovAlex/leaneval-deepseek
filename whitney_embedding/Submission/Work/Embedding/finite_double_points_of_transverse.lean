import Mathlib
import Submission.Work.Embedding.exists_isolated_double_point
import Submission.Work.Embedding.immersion_locally_injective
import Submission.Work.Embedding.finite_of_isClosed_forall_isolated

/-!
# Finiteness of the self-intersections of a self-transverse immersion

On a **compact** manifold `M`, an **immersion** `g : M → ℝ^{2n}` whose sheets meet transversally at
every double point has only finitely many double points.

The proof combines three facts, one for each hypothesis of the statement.

* `Work.Embedding.immersion_locally_injective` — an immersion is **locally injective**: around every
  point there is an open neighbourhood on which `g` is injective.  (This is where the immersion
  hypothesis is used; without it self-intersections can accumulate at a critical point of `g`, e.g.
  `g t = (t^2, e^{-1/t^2} sin (1/t))`.)

* `Work.Embedding.isClosed_doubleSet_of_locallyInjective` (below) — the double point set
  `D = {p | p.1 ≠ p.2 ∧ g p.1 = g p.2}` is **closed** in `M × M`: off the diagonal it is contained
  in the closed set `{g p.1 = g p.2}`, while near the diagonal local injectivity of `g` makes the
  diagonal an interior point of `Dᶜ`.

* `Work.Embedding.exists_isolated_double_point` — **transversality** at a double point makes that
  double point *isolated*: the two sheets meet in a single point in suitable open neighbourhoods.

So `D` is a closed subset of the compact space `M × M`, all of whose points are isolated, and
`Work.Embedding.finite_of_isClosed_forall_isolated` (a compact discrete set is finite) gives that
`D` is finite.
-/

namespace Work.Embedding

open scoped Manifold ContDiff
open Set Filter Topology

/-- The set of double points `{p | p.1 ≠ p.2 ∧ g p.1 = g p.2}` of a locally injective map with
values in a Hausdorff space is closed: away from the diagonal it is contained in the closed set
`{p | g p.1 = g p.2}`, while near the diagonal local injectivity of `g` shows that the diagonal lies
in the interior of the complement. -/
theorem isClosed_doubleSet_of_locallyInjective {M Y : Type*} [TopologicalSpace M]
    [TopologicalSpace Y] [T2Space Y] (g : M → Y) (hg : Continuous g)
    (hloc : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ Set.InjOn g U) :
    IsClosed {p : M × M | p.1 ≠ p.2 ∧ g p.1 = g p.2} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro q hq
  by_cases hdiag : q.1 = q.2
  · -- Near the diagonal there are no double points, by local injectivity.
    obtain ⟨U, hUo, hxU, hInj⟩ := hloc q.1
    refine ⟨U ×ˢ U, ?_, hUo.prod hUo, ⟨hxU, hdiag ▸ hxU⟩⟩
    rintro r ⟨hr1, hr2⟩ hrD
    exact hrD.1 (hInj hr1 hr2 hrD.2)
  · -- Off the diagonal, `g q.1 ≠ g q.2`, and `{g r.1 ≠ g r.2}` is an open neighbourhood.
    have hgne : g q.1 ≠ g q.2 := fun h => hq ⟨hdiag, h⟩
    have hcl : IsClosed {r : M × M | g r.1 = g r.2} :=
      isClosed_eq (hg.comp continuous_fst) (hg.comp continuous_snd)
    refine ⟨{r : M × M | g r.1 ≠ g r.2}, ?_, hcl.isOpen_compl, hgne⟩
    rintro r hr ⟨-, hr2⟩
    exact hr hr2

/-- On a **compact** manifold, an **immersion** `g : M → ℝ^{2n}` whose sheets meet transversally at
every double point has only finitely many double points.  (The immersion hypothesis is necessary:
without it, transverse double points can accumulate at a critical point on the diagonal, e.g.
`g t = (t^2, e^{-1/t^2} sin (1/t))`.)

Suggested proof: the double point set `D` is (i) covered by neighbourhoods each meeting it in at most
one point — off the diagonal by `Work.Embedding.exists_isolated_double_point`, and near the diagonal
by local injectivity of the immersion `g` — and (ii) closed in the compact `M × M` (`{p | g p.1 =
g p.2}` is closed and every point of `D` away from the diagonal is isolated); conclude by extracting
a finite subcover. -/
theorem finite_double_points_of_transverse {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    [CompactSpace M]
    (g : M → EuclideanSpace ℝ (Fin (2*n))) (hg : ContMDiff (𝓡 n) (𝓡 (2*n)) ∞ g)
    (himm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n)) g x))
    (htrans : ∀ x y : M, x ≠ y → g x = g y →
      (mfderiv (𝓡 n) (𝓡 (2*n)) g x).range ⊔ (mfderiv (𝓡 n) (𝓡 (2*n)) g y).range = ⊤) :
    {p : M × M | p.1 ≠ p.2 ∧ g p.1 = g p.2}.Finite := by
  -- The double point set is closed (local injectivity of the immersion) and all of its points are
  -- isolated (transversality), so the compactness lemma applies.
  have hcl := isClosed_doubleSet_of_locallyInjective g hg.continuous
    (immersion_locally_injective g hg himm)
  refine finite_of_isClosed_forall_isolated hcl fun p hp => ?_
  obtain ⟨U, V, hUo, hVo, hxU, hyV, -, hmain⟩ :=
    exists_isolated_double_point g hg hp.1 hp.2 (htrans p.1 p.2 hp.1 hp.2)
  refine ⟨U ×ˢ V, hUo.prod hVo, ⟨hxU, hyV⟩, ?_⟩
  rintro q ⟨hqUV, hqD⟩
  obtain ⟨he1, he2⟩ := hmain q.1 hqUV.1 q.2 hqUV.2 hqD.2
  exact Prod.ext he1 he2

end Work.Embedding
