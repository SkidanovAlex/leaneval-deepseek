import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.bandSeparatingMap_of_contMDiff

/-!
# Good drawings on a family of value bands, and their pasting

This file isolates the **bookkeeping half** of the construction of the level-separating map
`Work.Drive.N2.levelSeparatingMap` for the compact `n = 2` branch.

A "good drawing" of `M` for `f` is a smooth `g : M → ℝ³` which is injective on every level set of
`f` and whose differential is injective on `ker (df)`.  The construction of `g` proceeds block by
block: for every value band `A ⊆ ℝ` (a band around a critical value, or a regular band between two
of them) one produces a candidate `g i` which is a good drawing *on that band*, and the candidates
must agree on the overlaps of the bands.

The point of this file is that this pasting is **free**:

* `GoodDrawingOn f A g` is the conjunction of the three requirements, localised to the value band
  `A`;
* `goodDrawing_of_family` states that finitely many good drawings on *open* value bands which cover
  `f '' M` and agree on the pairwise overlaps glue to a single good drawing of `M`, provided `f` is
  smooth (the smoothness of `f` is used only to know that the set of points whose value lies in a
  given band is a neighbourhood of each of its points).

Hence the whole geometric content of the compact `n = 2` case is concentrated in the construction of
the *individual band drawings* and their *agreement*, with no further global coherence condition.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Filter Set

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- **A good drawing on the value band `A`.**  `g : M → ℝ³` is smooth near every point whose
`f`-value lies in `A`, its differential is injective on `ker (df)` there, and it separates the points
of every level set of `f` inside the band.  (Nothing is required of `g` outside the band.) -/
def GoodDrawingOn (f : M → ℝ) (A : Set ℝ) (g : M → EuclideanSpace ℝ (Fin 3)) : Prop :=
  (∀ x : M, f x ∈ A → ContMDiffAt (𝓡 2) (𝓡 3) ∞ g x) ∧
  (∀ x : M, f x ∈ A → ∀ v : TangentSpace (𝓡 2) x,
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) g x v = 0 → v = 0) ∧
  (∀ x y : M, f x ∈ A → f y ∈ A → f x = f y → g x = g y → x = y)

lemma GoodDrawingOn.mono {f : M → ℝ} {A A' : Set ℝ} {g : M → EuclideanSpace ℝ (Fin 3)}
    (h : GoodDrawingOn f A' g) (hsub : A ⊆ A') : GoodDrawingOn f A g :=
  ⟨fun x hx => h.1 x (hsub hx),
    fun x hx v h1 h2 => h.2.1 x (hsub hx) v h1 h2,
    fun x y hx hy hfxy hg => h.2.2 x y (hsub hx) (hsub hy) hfxy hg⟩

/-- The evident good drawing of the whole of `M` from a parametrisation of the value axis: if
`g : M → ℝ³` is smooth and satisfies the two separation properties everywhere then
`GoodDrawingOn f univ g` holds. -/
lemma goodDrawingOn_univ {f : M → ℝ} {g : M → EuclideanSpace ℝ (Fin 3)}
    (hsm : ∀ x : M, ContMDiffAt (𝓡 2) (𝓡 3) ∞ g x)
    (himm : ∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) g x v = 0 → v = 0)
    (hinj : ∀ x y : M, f x = f y → g x = g y → x = y) :
    GoodDrawingOn f univ g :=
  ⟨fun x _ => hsm x, fun x _ => himm x, fun x y _ _ => hinj x y⟩

open Classical in
/-- **Pasting finitely many good drawings.**

If `A i` (`i : Fin m`) is a finite family of *open* value bands covering `f '' M`, each carrying a
good drawing `g i`, and any two of the drawings agree wherever both bands are active, then the
drawings glue to one good drawing of `M` for `f`.

The pasted drawing is `G x = g (sel x) x` where `sel x` is the smallest index whose band contains
`f x`: on the open neighbourhood `f ⁻¹' A (sel x)` of `x` the function `G` coincides *exactly* with
`g (sel x)`, since on that neighbourhood the agreement hypothesis rewrites every other active piece
as `g (sel x)`. -/
theorem goodDrawing_of_family {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    {m : ℕ} (A : Fin m → Set ℝ) (hA : ∀ i, IsOpen (A i))
    (g : Fin m → M → EuclideanSpace ℝ (Fin 3))
    (hcover : ∀ x : M, ∃ i, f x ∈ A i)
    (hrows : ∀ i, GoodDrawingOn f (A i) (g i))
    (hagree : ∀ i j : Fin m, i ≠ j → ∀ x : M, f x ∈ A i → f x ∈ A j → g i x = g j x) :
    ∃ G : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (𝓡 2) (𝓡 3) ∞ G ∧
      (∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) G x v = 0 → v = 0) ∧
      (∀ x y : M, f x = f y → G x = G y → x = y) := by
  classical
  -- the index selector
  have hne : ∀ x : M, (Finset.univ.filter (fun i : Fin m => f x ∈ A i)).Nonempty := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let sel : M → Fin m := fun x => (Finset.univ.filter (fun i : Fin m => f x ∈ A i)).min' (hne x)
  have hsel_mem : ∀ x : M, f x ∈ A (sel x) := fun x =>
    (Finset.mem_filter.mp (Finset.min'_mem _ (hne x))).2
  have hsel_le : ∀ x : M, ∀ i : Fin m, f x ∈ A i → sel x ≤ i := fun x i hi =>
    Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  let G : M → EuclideanSpace ℝ (Fin 3) := fun x => g (sel x) x
  -- the key local fact: on the band of the selector, `G` is the selected piece
  have hlocal : ∀ x : M, ∀ y : M, f y ∈ A (sel x) → G y = g (sel x) y := by
    intro x y hy
    show g (sel y) y = g (sel x) y
    rcases eq_or_ne (sel y) (sel x) with h | h
    · rw [h]
    · exact hagree (sel y) (sel x) h y (hsel_mem y) hy
  have hEv : ∀ x : M, G =ᶠ[𝓝 x] g (sel x) := by
    intro x
    have hopen : f ⁻¹' A (sel x) ∈ 𝓝 x :=
      (hA (sel x)).preimage hf.continuous |>.mem_nhds (hsel_mem x)
    filter_upwards [hopen] with y hy
    exact hlocal x y hy
  refine ⟨G, ?_, ?_, ?_⟩
  · intro x
    exact ((hrows (sel x)).1 x (hsel_mem x)).congr_of_eventuallyEq (hEv x)
  · intro x v h1 h2
    have h3 : mfderiv (𝓡 2) (𝓡 3) (g (sel x)) x v = 0 := by
      have h2' := h2
      rw [(hEv x).mfderiv_eq] at h2'
      exact h2'
    exact (hrows (sel x)).2.1 x (hsel_mem x) v h1 h3
  · intro x y hfxy hGxy
    have hx : f x ∈ A (sel x) := hsel_mem x
    have hy : f y ∈ A (sel y) := hsel_mem y
    have hval : g (sel x) x = g (sel y) y := hGxy
    rcases eq_or_ne (sel x) (sel y) with h | h
    · rw [h] at hx hval
      exact (hrows (sel y)).2.2 x y hx hy hfxy hval
    · have hfs : f x ∈ A (sel y) := by rw [hfxy]; exact hy
      have h1 : g (sel x) x = g (sel y) x := hagree (sel x) (sel y) h x hx hfs
      have h2 : g (sel y) x = g (sel y) y := h1 ▸ hval
      exact (hrows (sel y)).2.2 x y hfs hy hfxy h2

/-- **A regular band carries a good drawing.**  This is the immediate corollary of the proved band
transport `Work.Drive.N2.bandSeparatingMap_of_contMDiff`: for a level flow `Φ` over `[a,b]` (no
critical values in the interval) and any picture `A` which is injective and immersive on the top
level `f ⁻¹' {b}`, the transported drawing `z ↦ A (Φ (b - f z, z))` is a good drawing on the band. -/
theorem goodDrawingOn_band {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (f : M → ℝ) {a b : ℝ} (hab : a ≤ b) {Φ : ℝ × M → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hΦsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ) (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦf : ∀ x : M, ∀ t : ℝ, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b →
      f (Φ (t, x)) = f x + t)
    (hΦcomp : ∀ x : M, ∀ s t : ℝ, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b →
      f x + t + s ∈ Set.Icc a b → Φ (s, Φ (t, x)) = Φ (s + t, x))
    (A : M → EuclideanSpace ℝ (Fin 3)) (hA : ContMDiff (𝓡 2) (𝓡 3) ∞ A)
    (hAinj : ∀ x y : M, f x = b → f y = b → A x = A y → x = y)
    (hAimm : ∀ y : M, f y = b → ∀ v : TangentSpace (𝓡 2) y,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y v = 0 → mfderiv (𝓡 2) (𝓡 3) A y v = 0 → v = 0) :
    GoodDrawingOn f (Set.Ioo a b) (fun z => A (Φ (b - f z, z))) := by
  obtain ⟨h1, h2, h3⟩ := bandSeparatingMap_of_contMDiff f hab hf hΦsm hΦ0 hΦf hΦcomp A hA hAinj hAimm
  exact ⟨fun x hx => h1 x (Set.Ioo_subset_Icc_self hx),
    fun x hx v hv hg => h2 x v (Set.Ioo_subset_Icc_self hx) hv hg,
    fun x y hx hy hxy hg => h3 x y (Set.Ioo_subset_Icc_self hx) (Set.Ioo_subset_Icc_self hy) hxy hg⟩

end Work.Drive.N2
