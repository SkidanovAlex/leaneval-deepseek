import Mathlib
import Submission.Work.ANALYTIC.zcomboPieces
import Submission.Work.ANALYTIC.pointsDetectSetup

/-!
# The pieces of the cover: `Work.ANALYTIC.piece_family_covers`

Given a finite family of maps `φ j : V ⟶ T` (`j : Fin m`) out of a light profinite set, coefficients
`c j`, and a point `u` of `V`, this file produces the pattern function `f : Fin m → Fin m` whose
piece `pieceSet V T φ f` contains `u` and whose class coefficient sums vanish.

The construction is elementary: at the point `u` the family `j ↦ φ j u` induces a partition of
`Fin m` into fibres, and `f` sends every index to the *least* index of its fibre.  Then
`f k = f i ↔ φ k u = φ i u`, which gives

* `f` is idempotent,
* the class `{k | f k = f i}` is exactly the fibre `{k | φ k u = φ i u}`, so its coefficient sum
  vanishes by the fibre-sum computation `Work.ANALYTIC.fiber_sum_eq_zero`,
* `u` lies in the piece of `f`, since `f i = f j` forces `φ i u = φ (f i) u = φ (f j) u = φ j u`.

The hypothesis `hind` enters only through `fiber_sum_eq_zero`: it is the linear independence of the
point classes of an injective tuple of points of `T` (Scholze, *Lectures on Analytic Geometry*,
Prop. 2.1), applied to the relation `∑ j, c j • [φ j u] = 0` obtained from the hypothesis `h` by
evaluating the combination of `zmap`s at the point `u`
(`Work.ANALYTIC.pointValue_zmap_combo`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid Opposite Classical

noncomputable section

namespace Work.ANALYTIC

/-- **The combinatorial core of the covering.**  For a point `u : ↥V` such that the coefficient
sum over every fibre `{k | φ k u = φ i u}` vanishes, there is an idempotent pattern function `f`
whose classes are exactly the fibres of `u` (so that its class coefficient sums vanish) and such
that `u` lies in the piece of `f`.

The pattern `f` sends each index `i` to the least index of its fibre `{k | φ k u = φ i u}`. -/
theorem exists_fiber_pattern (V T : LightProfinite.{0}) (m : ℕ) (φ : Fin m → (V ⟶ T))
    (u : ↥V) (c : Fin m → ℤ)
    (hfib : ∀ i : Fin m, ∑ k ∈ Finset.univ.filter (fun k => φ k u = φ i u), c k = 0) :
    ∃ f : Fin m → Fin m, (∀ i, f (f i) = f i) ∧
      (∀ i, ∑ k ∈ Finset.univ.filter (fun k => f k = f i), c k = 0) ∧
      (∀ i j, f i = f j → φ i u = φ j u) := by
  classical
  -- the fibre of `i` under `k ↦ φ k u`
  let S : Fin m → Finset (Fin m) := fun i => Finset.univ.filter (fun k => φ k u = φ i u)
  have hne : ∀ i, (S i).Nonempty := fun i => ⟨i, by simp [S]⟩
  -- the least index of each fibre
  let f : Fin m → Fin m := fun i => (S i).min' (hne i)
  have hfS : ∀ i, f i ∈ S i := fun i => Finset.min'_mem _ _
  have hfval : ∀ i, φ (f i) u = φ i u := fun i => (Finset.mem_filter.mp (hfS i)).2
  -- `f k = f i` exactly when `k` and `i` lie in the same fibre
  have hfiff : ∀ k i, f k = f i ↔ φ k u = φ i u := by
    intro k i
    constructor
    · intro hki
      have hv : φ (f k) u = φ (f i) u := by rw [hki]
      rw [hfval k, hfval i] at hv
      exact hv
    · intro hki
      have h1 : f k ≤ f i :=
        Finset.min'_le (S k) (f i)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hfval i).trans hki.symm⟩)
      have h2 : f i ≤ f k :=
        Finset.min'_le (S i) (f k)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hfval k).trans hki⟩)
      exact le_antisymm h1 h2
  refine ⟨f, ?_, ?_, ?_⟩
  · -- idempotence: `f i` lies in the fibre of `i`, so its own fibre is the same
    intro i
    exact (hfiff (f i) i).mpr (hfval i)
  · -- the class of `f i` is the fibre of `i`, whose coefficient sum vanishes
    intro i
    have hset : (Finset.univ.filter (fun k => f k = f i)) = S i := by
      apply Finset.filter_congr
      intro k _
      exact hfiff k i
    rw [hset]
    exact hfib i
  · -- `u` lies in the piece: `f i = f j` forces `φ i u = φ j u`
    intro i j hij
    calc φ i u = φ (f i) u := (hfval i).symm
      _ = φ (f j) u := by rw [hij]
      _ = φ j u := hfval j

/-- **The pieces of the family cover `V`.**  If a finite `ℤ`-linear combination of maps
`φ j : V ⟶ T` vanishes at every point of `V` (hypothesis `h`, via `prePt`), and the point classes
of injective tuples of points of `T` are linearly independent (`hind`), then every point `u` of `V`
lies in the piece `pieceSet V T φ f` of an idempotent pattern `f` whose class coefficient sums
`∑ k ∈ {k | f k = f i}, c k` all vanish. -/
theorem piece_family_covers (V T : LightProfinite.{0}) (m : ℕ)
    (φ : Fin m → (V ⟶ T)) (c : Fin m → ℤ)
    (hind : ∀ (m : ℕ) (t : Fin m → ↥T), Function.Injective t → ∀ c : Fin m → ℤ,
      (∑ j, c j • (Work.ANALYTIC.pointClassM T (t j))) = 0 → ∀ j, c j = 0)
    (h : ∀ v : ↥V, Work.ANALYTIC.prePt v (Work.ANALYTIC.zmapCombo φ c) = 0) :
    ∀ u : ↥V, ∃ f : Fin m → Fin m, (∀ i, f (f i) = f i) ∧
      (∀ i, ∑ k ∈ Finset.univ.filter (fun k => f k = f i), c k = 0) ∧
      u ∈ Work.ANALYTIC.pieceSet V T m φ f := by
  intro u
  -- evaluating the combination at the point `u` gives a relation between the point classes
  have hrel : (∑ j, c j • (Work.ANALYTIC.pointClassM T (φ j u))) = 0 := by
    have h1 : Work.ATOM.zmap (Work.ATOM.ptAt u)
        ≫ (∑ j, c j • (Work.ATOM.zmap (φ j))) = 0 := h u
    rwa [Work.ANALYTIC.pointValue_zmap_combo T V m φ c u] at h1
  -- hence the coefficient sum over every fibre vanishes
  have hfib : ∀ i : Fin m, ∑ k ∈ Finset.univ.filter (fun k => φ k u = φ i u), c k = 0 :=
    fun i => Work.ANALYTIC.fiber_sum_eq_zero T hind (fun j => φ j u) c hrel i
  -- and the combinatorial construction produces the pattern
  obtain ⟨f, hf, hc, hpiece⟩ := exists_fiber_pattern V T m φ u c hfib
  exact ⟨f, hf, hc, hpiece⟩

end Work.ANALYTIC

end
