import Mathlib
import Submission.Work.Drive.Mono.FiberModel.Defs
import Submission.Work.Drive.Mono.FiberModel.planar_closure_facts_main

open LeanEval.KnotTheory.PardonDistortion Set
open scoped Topology

namespace Work.Drive.Mono.WindowCase

noncomputable section

/-! ## Closing the interior of a half-space cut of a convex body

For a closed convex set `W` of the plane with nonempty interior and a continuous linear functional
`f`, the closure of the part of `interior W` strictly above a level `c` is the part of `W` at or
above `c`, provided only that the strict part is nonempty.  The degenerate case is exactly when the
level is a supporting value of `f` on `W`; the hypothesis `hex` rules it out, and then a point of
`W` with `f = c` is reached by the segments joining it to an interior point with `f > c`. -/
theorem closure_interior_setOf_gt (W : Set (ℝ × ℝ)) (hWc : Convex ℝ W) (hWcl : IsClosed W)
    (hWi : (interior W).Nonempty) (f : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ)
    (hex : ∃ X ∈ interior W, c < f X) :
    closure (interior W ∩ {X : ℝ × ℝ | c < f X}) = W ∩ {X : ℝ × ℝ | c ≤ f X} := by
  have hdens : W ⊆ closure (interior W) := by
    rw [hWc.closure_interior_eq_closure_of_nonempty_interior hWi, hWcl.closure_eq]
  refine le_antisymm ?_ ?_
  · refine closure_minimal ?_ (hWcl.inter (isClosed_le continuous_const f.continuous))
    rintro X ⟨hXW, hXf⟩
    simp only [Set.mem_ofPred_eq] at hXf
    exact ⟨interior_subset hXW, le_of_lt hXf⟩
  · rintro X ⟨hXW, hXf⟩
    simp only [Set.mem_ofPred_eq] at hXf
    rcases lt_or_eq_of_le hXf with hlt | heq
    · have hmem : X ∈ closure (interior W) := hdens hXW
      rw [mem_closure_iff] at hmem ⊢
      intro O hO hXO
      obtain ⟨Y, hY1, hY2⟩ := hmem (O ∩ {Y : ℝ × ℝ | c < f Y})
        (hO.inter (isOpen_lt continuous_const f.continuous)) ⟨hXO, hlt⟩
      refine ⟨Y, hY1.1, hY2, ?_⟩
      simpa only [Set.mem_ofPred_eq] using hY1.2
    · obtain ⟨X₀, hX₀int, hX₀f⟩ := hex
      rw [mem_closure_iff]
      intro O hO hXO
      set g : ℝ → ℝ × ℝ := fun t => t • X₀ + (1 - t) • X with hg
      have hcont : Continuous g := by rw [hg]; fun_prop
      have hg0 : g 0 = X := by rw [hg]; simp
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ), g t ∈ O :=
        (hcont.tendsto 0).eventually (hO.mem_nhds (by rw [hg0]; exact hXO))
      obtain ⟨δ, hδpos, hδsub⟩ := Metric.eventually_nhds_iff.mp hev
      set t : ℝ := min δ 1 / 2 with ht
      have htpos : 0 < t := by
        rw [ht]; have := lt_min hδpos one_pos; linarith
      have htδ : t < δ := by rw [ht]; have := min_le_left δ 1; linarith
      have ht1 : t < 1 := by rw [ht]; have := min_le_right δ 1; linarith
      refine ⟨g t, hδsub ?_, ?_, ?_⟩
      · rw [Real.dist_eq, sub_zero, abs_of_pos htpos]; exact htδ
      · have hcombo : t • X₀ + (1 - t) • X ∈ interior W :=
          hWc.combo_interior_closure_mem_interior hX₀int (subset_closure hXW)
            (a := t) (b := 1 - t) (by linarith) (by linarith) (by ring)
        rw [hg]; exact hcombo
      · rw [hg]
        simp only [Set.mem_ofPred_eq]
        have hval : f (t • X₀ + (1 - t) • X) = t * f X₀ + (1 - t) * f X := by
          simp [map_add, map_smul]
        rw [hval, ← heq]
        nlinarith [hX₀f]

/-- The first-coordinate version, upward. -/
theorem closure_interior_fst_ge (W : Set (ℝ × ℝ)) (hWc : Convex ℝ W) (hWcl : IsClosed W)
    (hWi : (interior W).Nonempty) (c : ℝ) (hex : ∃ X ∈ interior W, c < X.1) :
    closure (interior W ∩ {X : ℝ × ℝ | c < X.1}) = W ∩ {X : ℝ × ℝ | c ≤ X.1} :=
  closure_interior_setOf_gt W hWc hWcl hWi (ContinuousLinearMap.fst ℝ ℝ ℝ) c hex

/-- The first-coordinate version, downward. -/
theorem closure_interior_fst_le (W : Set (ℝ × ℝ)) (hWc : Convex ℝ W) (hWcl : IsClosed W)
    (hWi : (interior W).Nonempty) (c : ℝ) (hex : ∃ X ∈ interior W, X.1 < c) :
    closure (interior W ∩ {X : ℝ × ℝ | X.1 < c}) = W ∩ {X : ℝ × ℝ | X.1 ≤ c} := by
  have h := closure_interior_setOf_gt W hWc hWcl hWi (-(ContinuousLinearMap.fst ℝ ℝ ℝ)) (-c)
    (by obtain ⟨X, hX, hXc⟩ := hex; exact ⟨X, hX, by simpa using neg_lt_neg hXc⟩)
  have h1 : {X : ℝ × ℝ | -c < (-(ContinuousLinearMap.fst ℝ ℝ ℝ)) X} = {X : ℝ × ℝ | X.1 < c} := by
    ext X; simp [neg_lt_neg_iff]
  have h2 : {X : ℝ × ℝ | -c ≤ (-(ContinuousLinearMap.fst ℝ ℝ ℝ)) X} = {X : ℝ × ℝ | X.1 ≤ c} := by
    ext X; simp [neg_le_neg_iff]
  rw [h1, h2] at h
  exact h

/-- The second-coordinate version. -/
theorem closure_interior_snd_ge (W : Set (ℝ × ℝ)) (hWc : Convex ℝ W) (hWcl : IsClosed W)
    (hWi : (interior W).Nonempty) (c : ℝ) (hex : ∃ X ∈ interior W, c < X.2) :
    closure (interior W ∩ {X : ℝ × ℝ | c < X.2}) = W ∩ {X : ℝ × ℝ | c ≤ X.2} :=
  closure_interior_setOf_gt W hWc hWcl hWi (ContinuousLinearMap.snd ℝ ℝ ℝ) c hex

/-- The closure and the closure-interior of the planar image of a level of the tilted sweep, in the
one-sphere window. -/
theorem tls_planar_facts
    (s : ℝ) (hs : 0 < s) (c : EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ)
    (v : EuclideanSpace ℝ (Fin 3))
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hh : 0 < h) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hv : v ≠ 0)
    (hwinP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y)
    (hwinM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h)
    (hwallP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y)
    (hwallM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h ∧ lam < ℓ y) :
    interior (closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam))
      = interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) ∩
        {X : ℝ × ℝ | h < |X.1 - Work.Drive.Mono.FiberModel.slabA u c v| ∨ lam < X.2} ∧
    closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam)
      = Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ ∩
        ({X : ℝ × ℝ | Work.Drive.Mono.FiberModel.slabA u c v + h ≤ X.1} ∪
         {X : ℝ × ℝ | X.1 ≤ Work.Drive.Mono.FiberModel.slabA u c v - h} ∪
         {X : ℝ × ℝ | lam ≤ X.2}) := by
  have hmain := Work.Drive.Mono.FiberModel.planar_closure_facts_main
    s c σ u v h lam ℓ hv hℓv hℓne hh
  obtain ⟨hcl, hint, -, -, -, -⟩ := hmain
  have hWc : Convex ℝ (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) :=
    Work.Drive.Mono.FiberModel.convex_boxShadow s c σ v ℓ
  have hWcl : IsClosed (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) := by
    rw [Work.Drive.Mono.FiberModel.boxShadow_eq_closure_image s c σ v ℓ]
    exact isClosed_closure
  -- interior points witnessing that the three cutting levels are not supporting values
  have hmem_int : ∀ y ∈ Submission.PBox s c σ,
      Work.Drive.Mono.FiberModel.levPair v ℓ y ∈
        interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) := by
    intro y hy
    rw [← Work.Drive.Mono.FiberModel.image_PBox_eq_interior_boxShadow (s := s) c σ hv hℓv hℓne]
    exact ⟨y, hy, rfl⟩
  have hexP : ∃ X ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ),
      Work.Drive.Mono.FiberModel.slabA u c v + h < X.1 := by
    obtain ⟨y, hy, hygt⟩ := hwinP
    exact ⟨Work.Drive.Mono.FiberModel.levPair v ℓ y, hmem_int y hy,
      by simpa [Work.Drive.Mono.FiberModel.levPair, Work.Drive.Mono.FiberModel.slabA] using hygt⟩
  have hexM : ∃ X ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ),
      X.1 < Work.Drive.Mono.FiberModel.slabA u c v - h := by
    obtain ⟨y, hy, hylt⟩ := hwinM
    exact ⟨Work.Drive.Mono.FiberModel.levPair v ℓ y, hmem_int y hy,
      by simpa [Work.Drive.Mono.FiberModel.levPair, Work.Drive.Mono.FiberModel.slabA] using hylt⟩
  have hexL : ∃ X ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ),
      lam < X.2 := by
    obtain ⟨y, hy, -, hylam⟩ := hwallP
    exact ⟨Work.Drive.Mono.FiberModel.levPair v ℓ y, hmem_int y hy,
      by simpa [Work.Drive.Mono.FiberModel.levPair] using hylam⟩
  have hWi : (interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)).Nonempty :=
    hexP.imp fun _ hX => hX.1
  have hp := closure_interior_fst_ge (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
    hWc hWcl hWi (Work.Drive.Mono.FiberModel.slabA u c v + h) hexP
  have hm := closure_interior_fst_le (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
    hWc hWcl hWi (Work.Drive.Mono.FiberModel.slabA u c v - h) hexM
  have hc := closure_interior_snd_ge (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
    hWc hWcl hWi lam hexL
  refine ⟨?_, ?_⟩
  · rw [hint]
    ext X
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
  · rw [hcl]
    simp only [Work.Drive.Mono.FiberModel.wingPlus, Work.Drive.Mono.FiberModel.wingMinus,
      Work.Drive.Mono.FiberModel.cap0]
    rw [hp, hm, hc]
    ext X; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]; tauto

end

end Work.Drive.Mono.WindowCase
