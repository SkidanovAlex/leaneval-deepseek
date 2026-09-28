import Mathlib
import Submission.Work.RatHurewicz.cycleModelDefs
import Submission.Work.StemsB.PiMap
import Submission.Work.Serre.CWModel.piOneSurjective

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- The only point of the cube `I¹ = Fin 1 → I` is its `0`-th coordinate. -/
private theorem fin_one_fun_eq (x : Fin 1 → I) : (fun _ : Fin 1 => x 0) = x := by
  funext i
  fin_cases i
  rfl

/-- **Path compression gives `CompressRel` in dimension `1`.**

If every path in `Y` whose endpoints lie in `A` is homotopic relative to its endpoints to a path
with image in `A`, then every map `(I¹, ∂I¹) → (Y, A)` is homotopic relative to `∂I¹` into `A`.

The domain `I¹ = Fin 1 → I` is the unit interval (its only point is `x 0`), and the homotopy is
obtained by reading a path homotopy `F` as a homotopy of cubes through `(x, s) ↦ F (s, x 0)`; its
`0`-end is the original map because `x = (fun _ => x 0)` for the index type `Fin 1`. -/
theorem compressRel_one_of_paths {Y : Type} [TopologicalSpace Y] {A : Set Y}
    (h : ∀ (y z : Y), y ∈ A → z ∈ A → (p : Path y z) → ∃ q : Path y z,
      (∀ t, q t ∈ A) ∧ Nonempty (Path.Homotopic p q)) :
    CompressRel Y A 1 := by
  intro f hb
  have hz0 : (fun _ : Fin 1 => (0 : I)) ∈ Cube.boundary (Fin 1) := ⟨0, Or.inl rfl⟩
  have hz1 : (fun _ : Fin 1 => (1 : I)) ∈ Cube.boundary (Fin 1) := ⟨0, Or.inr rfl⟩
  have hb0 : f (fun _ : Fin 1 => (0 : I)) ∈ A := hb _ hz0
  have hb1 : f (fun _ : Fin 1 => (1 : I)) ∈ A := hb _ hz1
  -- the path in `Y` underlying `f`
  let p : Path (f (fun _ : Fin 1 => (0 : I))) (f (fun _ : Fin 1 => (1 : I))) :=
    Path.mk ⟨fun s => f (fun _ : Fin 1 => s), by fun_prop⟩ rfl rfl
  have hp : ∀ s : I, p s = f (fun _ : Fin 1 => s) := fun s => rfl
  obtain ⟨q, hqA, hqn⟩ := h _ _ hb0 hb1 p
  obtain ⟨hF⟩ := hqn
  have F : p.Homotopy q := Classical.choice hF
  have hF0 : ∀ s : I, F (0, s) = p s := fun s => F.map_zero_left s
  have hF1 : ∀ s : I, F (1, s) = q s := fun s => F.map_one_left s
  have hFbd : ∀ (t s : I), s ∈ ({0, 1} : Set I) → F (t, s) = p s :=
    fun t s hs => ContinuousMap.HomotopyRel.eq_fst F t hs
  refine ⟨⟨fun x => F (x.2, x.1 0), by fun_prop⟩, ?_, ?_, ?_⟩
  · intro x
    show F (0, x 0) = f x
    rw [hF0 (x 0), hp (x 0), fin_one_fun_eq x]
  · intro x hx t
    show F (t, x 0) = f x
    have hx0 : x 0 ∈ ({0, 1} : Set I) := by
      obtain ⟨i, hi⟩ := hx
      fin_cases i
      exact hi
    rw [hFbd t (x 0) hx0, hp (x 0), fin_one_fun_eq x]
  · intro x
    show F (1, x 0) ∈ A
    rw [hF1 (x 0)]
    exact hqA (x 0)

/-- **The `1`-skeleton generates `π₁` of the model.**  For the simplex data `D` (definitions in `Submission.Work.RatHurewicz.cycleModelDefs`), suppose every path in `Model D` between two points of the `1`-skeleton `skeleton D` is homotopic, relative to its endpoints, to a path with image in the `1`-skeleton (this hypothesis is the statement `Work.RatHurewicz.compress_to_skeleton`, proved in parallel). Then for every base point `y₀` of the `1`-skeleton, the map on `π₁` induced by the inclusion of the `1`-skeleton is surjective.

Intended proof: represent an element of `HomotopyGroup (Fin 1) (Model D) y₀` by a generalized loop `γ : Ω^(Fin 1) (Model D) y₀`, view it as a path `Path y₀ y₀` (the domain `Fin 1 → I` is the unit interval, and the boundary condition says the two ends are `y₀`), compress it with `hcomp` to a path in the skeleton, and show that the resulting generalized loop of `↥(skeleton D)` maps to the same class; `Work.StemsB.πmap_apply_mk` and the `GenLoop`/`Path` dictionary of `Mathlib/Topology/Homotopy/HomotopyGroup.lean` are the tools, and the existing `Work.Serre.CWModel.πmap_setIncl_surjective_of_compressRel` (`Submission/Work/Serre/CWModel/piOneSurjective.lean`) can very likely be used directly once `hcomp` is rephrased as `CompressRel (Model D) (skeleton D) 1`. -/
theorem skeletonPiOne_surjective {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    (D : Work.RatHurewicz.MData X n x₀)
    (hcomp : ∀ (y z : Work.RatHurewicz.Model D), y ∈ Work.RatHurewicz.skeleton D →
      z ∈ Work.RatHurewicz.skeleton D → (p : Path y z) → ∃ q : Path y z,
        (∀ t, q t ∈ Work.RatHurewicz.skeleton D) ∧ Nonempty (Path.Homotopic p q))
    (y₀ : ↥(Work.RatHurewicz.skeleton D)) :
    Function.Surjective (Work.StemsB.πmap (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥(Work.RatHurewicz.skeleton D), Work.RatHurewicz.Model D)) 0 y₀) := by
  have hc : Work.RatHurewicz.CompressRel (Work.RatHurewicz.Model D)
      (Work.RatHurewicz.skeleton D) 1 := compressRel_one_of_paths hcomp
  exact Work.Serre.CWModel.πmap_setIncl_surjective_of_compressRel 0 hc y₀

end

end Work.RatHurewicz
