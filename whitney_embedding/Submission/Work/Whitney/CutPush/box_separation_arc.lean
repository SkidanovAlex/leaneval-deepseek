import Mathlib

/-!
# Box separation for an arc family

If every time slice of a continuous family `Φ : ℝ → ℝ → ℝ^m` is injective on `[0,1]`, then at each
base point `(s₀, x₀)` of the trail, and for every open neighbourhood `V` of `x₀`, the box `O × B`
can be shrunk so that `Φ s x ∈ B` with `x ∈ [0,1]` forces `x ∈ V`.

This is the arc version of `Work.Isotopy.exists_box_separation` (where the source is a compact
manifold); here the compactness comes from `Icc 0 1` and the conclusion is only asserted for
`x ∈ Icc 0 1`, which is all the velocity-patching argument consumes.
-/

open scoped Manifold ContDiff
open Topology Set MeasureTheory

namespace Work.Whitney.CutPush

/-- **Box separation for an arc family.** -/
theorem box_separation_arc {m : ℕ}
    (Φ : ℝ → ℝ → EuclideanSpace ℝ (Fin m)) (hc : Continuous (Function.uncurry Φ))
    (hinj : ∀ s : ℝ, Set.InjOn (Φ s) (Set.Icc (0 : ℝ) 1))
    (s₀ : ℝ) (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1)
    (V : Set ℝ) (hV : IsOpen V) (hx₀V : x₀ ∈ V)
    (O₀ : Set ℝ) (hO₀ : IsOpen O₀) (hs₀ : s₀ ∈ O₀)
    (W₀ : Set (EuclideanSpace ℝ (Fin m))) (hW₀ : IsOpen W₀) (hw₀ : Φ s₀ x₀ ∈ W₀) :
    ∃ (O : Set ℝ) (B : Set (EuclideanSpace ℝ (Fin m))),
      IsOpen O ∧ s₀ ∈ O ∧ O ⊆ O₀ ∧ IsOpen B ∧ Φ s₀ x₀ ∈ B ∧ B ⊆ W₀ ∧
      Bornology.IsBounded B ∧ (∀ s ∈ O, ∀ x ∈ Set.Icc (0 : ℝ) 1, Φ s x ∈ B → x ∈ V) := by
  classical
  obtain ⟨r₁, hr₁pos, hr₁sub⟩ := Metric.isOpen_iff.mp hW₀ (Φ s₀ x₀) hw₀
  set K : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ Vᶜ with hKdef
  have hKcompact : IsCompact K := isCompact_Icc.inter_right hV.isClosed_compl
  set f : ℝ → ℝ := fun x => dist (Φ s₀ x) (Φ s₀ x₀) with hfdef
  have hs₀cont : Continuous (Φ s₀) := by
    have h : Continuous (Function.uncurry Φ ∘ fun x : ℝ => (s₀, x)) :=
      hc.comp (continuous_const.prodMk continuous_id)
    simpa [Function.uncurry, Function.comp_def] using h
  have hfcont : Continuous f := by
    rw [hfdef]
    exact hs₀cont.dist continuous_const
  have hfpos : ∀ x ∈ K, (0 : ℝ) < f x := by
    intro x hx
    rw [hKdef] at hx
    obtain ⟨hxI, hxV⟩ := hx
    rw [hfdef, dist_pos]
    intro hxe
    exact hxV (by rw [hinj s₀ hxI hx₀ hxe]; exact hx₀V)
  obtain ⟨δ, hδpos, hδle⟩ := hKcompact.exists_forall_le' hfcont.continuousOn hfpos
  set n : Set (ℝ × ℝ) := {p | δ / 2 < dist (Function.uncurry Φ p) (Φ s₀ x₀)} with hndef
  have hnopen : IsOpen n := by
    rw [hndef]
    exact isOpen_lt continuous_const (hc.dist continuous_const)
  have hgn : ({s₀} : Set ℝ) ×ˢ K ⊆ n := by
    rintro ⟨r, x⟩ ⟨hr, hx⟩
    simp only [Set.mem_singleton_iff] at hr
    rw [hndef]
    simp only [Set.mem_ofPred_eq]
    rw [hr]
    exact lt_of_lt_of_le (by linarith : δ / 2 < δ) (hδle x hx)
  obtain ⟨u, v, huopen, hvopen, hsu, hKv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hKcompact hnopen hgn
  refine ⟨u ∩ O₀, Metric.ball (Φ s₀ x₀) (min r₁ (δ / 2)),
    huopen.inter hO₀, ⟨hsu (Set.mem_singleton s₀), hs₀⟩, Set.inter_subset_right,
    Metric.isOpen_ball, Metric.mem_ball_self (lt_min hr₁pos (by linarith)), ?_,
    Metric.isBounded_ball, ?_⟩
  · intro y hy
    apply hr₁sub
    rw [Metric.mem_ball] at hy ⊢
    have hmin := min_le_left r₁ (δ / 2)
    linarith
  · intro s hs x hxI hxB
    rw [Set.mem_inter_iff] at hs
    by_contra hxV
    have hxK : x ∈ K := by
      rw [hKdef, Set.mem_inter_iff, Set.mem_compl_iff]
      exact ⟨hxI, hxV⟩
    have hmem : (s, x) ∈ u ×ˢ v := ⟨hs.1, hKv hxK⟩
    have hgt : δ / 2 < dist (Function.uncurry Φ (s, x)) (Φ s₀ x₀) := by
      have h := huv hmem
      simpa only [hndef, Set.mem_ofPred_eq] using h
    have hgt' : δ / 2 < dist (Φ s x) (Φ s₀ x₀) := hgt
    rw [Metric.mem_ball] at hxB
    have hlt : dist (Φ s x) (Φ s₀ x₀) < δ / 2 := by
      have hmin := min_le_right r₁ (δ / 2)
      linarith
    exact absurd hgt' (not_lt.mpr (le_of_lt hlt))

end Work.Whitney.CutPush
