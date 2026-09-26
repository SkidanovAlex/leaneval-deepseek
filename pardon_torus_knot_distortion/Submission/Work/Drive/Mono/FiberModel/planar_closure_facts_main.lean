import Mathlib
import Submission.Work.Drive.Mono.FiberModel.Defs
import Submission.Work.Drive.Mono.FiberModel.planar_basic
import Submission.Work.Drive.Mono.FiberModel.planarImage
import Submission.Work.Drive.Mono.FiberModel.planar_pieces
import Submission.Work.Drive.Mono.FiberModel.planar_closure_facts

/-!
# The planar closure facts of the fibre model, for an arbitrary open `U`

`Z = planarImage s c σ u v h ℓ lam` is `interior W ∩ chamber` (`planarImage_eq`), where
`chamber a h lam = {|x₁ - a| > h ∨ lam ≤ x₂}` and `W = boxShadow s c σ v ℓ` is the convex shadow of
the closed box.  This file proves, for an arbitrary *open* plane set `U`, the two plane facts that
the fibre model needs:

* `closure (U ∩ chamber a h lam) = closure (U ∩ {a + h < x₁}) ∪ closure (U ∩ {x₁ < a - h}) ∪
  closure (U ∩ {lam < x₂})` (`closure_inter_chamber_eq`): the closed level half-plane
  `{lam ≤ x₂}` has the same closure inside an open set as the open one `{lam < x₂}`;
* `interior (closure (U ∩ chamber a h lam)) = U ∩ ({h < |x₁ - a|} ∪ {lam < x₂})`
  (`interior_closure_inter_chamber_eq`, `U` open and convex): the interior is obtained by replacing
  the closed level condition by the open one and the slab condition by its two open wings.

Specialising to `U = interior W` and combining with `convex_wingPlus`, `convex_wingMinus`,
`convex_cap0` (and `interior_closure_eq_self_of_isOpen_convex` for the third identity) gives
`planar_closure_facts_main`.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped Topology

namespace Work.Drive.Mono.FiberModel

noncomputable section

/-! ## Membership in the chamber and its three open pieces -/

theorem mem_chamber (a h lam : ℝ) (X : ℝ × ℝ) :
    (X ∈ chamber a h lam) ↔ h < |X.1 - a| ∨ lam ≤ X.2 := by
  simp [chamber]

theorem subset_chamber_of_slab_gt (a h lam : ℝ) :
    {X : ℝ × ℝ | a + h < X.1} ⊆ chamber a h lam := by
  rintro X hX
  have hX' : a + h < X.1 := by simpa using hX
  rw [mem_chamber]
  exact Or.inl (lt_abs.mpr (Or.inl (by linarith)))

theorem subset_chamber_of_slab_lt (a h lam : ℝ) :
    {X : ℝ × ℝ | X.1 < a - h} ⊆ chamber a h lam := by
  rintro X hX
  have hX' : X.1 < a - h := by simpa using hX
  rw [mem_chamber]
  exact Or.inl (lt_abs.mpr (Or.inr (by linarith)))

theorem subset_chamber_of_level_lt (a h lam : ℝ) :
    {X : ℝ × ℝ | lam < X.2} ⊆ chamber a h lam := by
  rintro X hX
  have hX' : lam < X.2 := by simpa using hX
  rw [mem_chamber]
  exact Or.inr (le_of_lt hX')

/-! ## The closure of `U ∩ chamber` for open `U` -/

/-- **Inside an open set the closed and the open level half-plane have the same closure.** -/
theorem closure_inter_le_snd_eq_closure_inter_lt_snd (U : Set (ℝ × ℝ)) (hU : IsOpen U) (lam : ℝ) :
    closure (U ∩ {X : ℝ × ℝ | lam ≤ X.2}) = closure (U ∩ {X : ℝ × ℝ | lam < X.2}) := by
  refine le_antisymm (closure_minimal ?_ isClosed_closure)
    (closure_mono (inter_subset_inter_right U ?_))
  · rintro X ⟨hXU, hXle⟩
    have hXle' : lam ≤ X.2 := by simpa using hXle
    rcases lt_or_eq_of_le hXle' with hlt | heq
    · exact subset_closure ⟨hXU, Set.mem_ofPred_eq.mpr hlt⟩
    · rw [mem_closure_iff]
      intro o ho hXo
      obtain ⟨ε, hεpos, -, hεo⟩ := exists_perturbed_snd (ho.inter hU) ⟨hXo, hXU⟩ 1 one_pos
      refine ⟨(X.1, X.2 + ε), hεo.1, hεo.2, Set.mem_ofPred_eq.mpr ?_⟩
      show lam < X.2 + ε
      rw [heq]; linarith
  · intro Z hZ
    exact Set.mem_ofPred_eq.mpr (le_of_lt (by simpa using hZ))

/-- **The perturbation step.**  Inside the open set `U ∩ B`, a point with `|x₁ - a| ≤ h` and
`x₂ ≤ lam` can be moved, staying in `U ∩ B`, to a point with `|x₁ - a| < h` and `x₂ < lam`: move
slightly towards the line `x₁ = a` and slightly down. -/
theorem exists_mem_of_abs_le {U B : Set (ℝ × ℝ)} (hUB : IsOpen (U ∩ B)) {X : ℝ × ℝ}
    (hX : X ∈ U ∩ B) {a h lam : ℝ} (hh : 0 < h) (h1 : |X.1 - a| ≤ h) (h2 : X.2 ≤ lam) :
    ∃ Y ∈ U ∩ B, |Y.1 - a| < h ∧ Y.2 < lam := by
  set c : ℝ → ℝ × ℝ := fun t => ((1 - t / 2) * X.1 + (t / 2) * a, X.2 - t / 2) with hc
  have hcont : Continuous c := by rw [hc]; fun_prop
  have hc0 : c 0 = X := by rw [hc]; ext <;> simp
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ U ∩ B :=
    (hcont.tendsto 0).eventually (hUB.mem_nhds (by rw [hc0]; exact hX))
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.eventually_nhds_iff.mp hev
  have htpos : 0 < min δ 1 / 2 := by
    have := lt_min hδpos one_pos; linarith
  have htδ : min δ 1 / 2 < δ := by
    have := min_le_left δ (1 : ℝ); linarith
  have hmem : c (min δ 1 / 2) ∈ U ∩ B :=
    hδsub (by rw [Real.dist_eq, sub_zero, abs_of_pos htpos]; exact htδ)
  refine ⟨c (min δ 1 / 2), hmem, ?_, ?_⟩
  · show |(1 - min δ 1 / 2 / 2) * X.1 + (min δ 1 / 2 / 2) * a - a| < h
    have ht1 : min δ 1 / 2 / 2 ≤ 1 := by
      have := min_le_right δ (1 : ℝ); linarith
    have ht2 : 0 < min δ 1 / 2 / 2 := by positivity
    have hrew : (1 - min δ 1 / 2 / 2) * X.1 + (min δ 1 / 2 / 2) * a - a
        = (1 - min δ 1 / 2 / 2) * (X.1 - a) := by ring
    rw [hrew, abs_mul, abs_of_nonneg (by linarith)]
    have hstep : (1 - min δ 1 / 2 / 2) * h < h := by nlinarith
    nlinarith
  · show X.2 - min δ 1 / 2 / 2 < lam
    have ht2 : 0 < min δ 1 / 2 / 2 := by positivity
    linarith

/-- **The closure of `U ∩ chamber` is the union of the closures of the three open pieces.** -/
theorem closure_inter_chamber_eq (U : Set (ℝ × ℝ)) (hU : IsOpen U) (a h lam : ℝ) (hh : 0 < h) :
    closure (U ∩ chamber a h lam)
      = closure (U ∩ {X : ℝ × ℝ | a + h < X.1}) ∪ closure (U ∩ {X : ℝ × ℝ | X.1 < a - h})
        ∪ closure (U ∩ {X : ℝ × ℝ | lam < X.2}) := by
  rw [chamber_eq a h lam hh]
  have hset : U ∩ ({X : ℝ × ℝ | a + h < X.1} ∪ {X : ℝ × ℝ | X.1 < a - h}
      ∪ {X : ℝ × ℝ | lam ≤ X.2})
      = (U ∩ {X : ℝ × ℝ | a + h < X.1}) ∪ (U ∩ {X : ℝ × ℝ | X.1 < a - h})
        ∪ (U ∩ {X : ℝ × ℝ | lam ≤ X.2}) := by
    ext X
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
    tauto
  rw [hset, closure_union, closure_union, closure_inter_le_snd_eq_closure_inter_lt_snd U hU lam]

/-! ## The interior of `closure (U ∩ chamber)` for open convex `U` -/

/-- **The interior of `closure (U ∩ chamber)`.**  For open convex `U` the interior is `U` cut by the
open slab wings and the open upper level half-plane. -/
theorem interior_closure_inter_chamber_eq (U : Set (ℝ × ℝ)) (hUo : IsOpen U) (hUc : Convex ℝ U)
    (a h lam : ℝ) (hh : 0 < h) :
    interior (closure (U ∩ chamber a h lam))
      = U ∩ ({X : ℝ × ℝ | h < |X.1 - a|} ∪ {X : ℝ × ℝ | lam < X.2}) := by
  have hUeq : interior (closure U) = U := interior_closure_eq_self_of_isOpen_convex hUc hUo
  refine le_antisymm ?_ ?_
  · intro X hX
    have hXU : X ∈ U := by
      have h1 : interior (closure (U ∩ chamber a h lam)) ⊆ interior (closure U) :=
        interior_mono (closure_mono inter_subset_left)
      rw [hUeq] at h1
      exact h1 hX
    refine ⟨hXU, ?_⟩
    by_contra hbad
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hbad
    obtain ⟨h1, h2⟩ := hbad
    obtain ⟨δ, hδpos, hδsub⟩ :=
      Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hX)
    obtain ⟨Y, hY, hY1, hY2⟩ := exists_mem_of_abs_le (U := U) (B := Metric.ball X δ)
      (hUo.inter Metric.isOpen_ball) ⟨hXU, Metric.mem_ball_self hδpos⟩ hh h1 h2
    obtain ⟨hYU, hYball⟩ := hY
    have hYcl : Y ∈ closure (U ∩ chamber a h lam) := hδsub (Metric.mem_ball.mp hYball)
    set O : Set (ℝ × ℝ) :=
      U ∩ Metric.ball X δ ∩ {Z : ℝ × ℝ | |Z.1 - a| < h} ∩ {Z : ℝ × ℝ | Z.2 < lam} with hO
    have hOopen : IsOpen O := by
      rw [hO]
      exact ((hUo.inter Metric.isOpen_ball).inter
        (isOpen_lt ((continuous_fst.sub continuous_const).abs) continuous_const)).inter
        (isOpen_lt continuous_snd continuous_const)
    have hYO : Y ∈ O := by
      rw [hO]
      exact ⟨⟨⟨hYU, hYball⟩, hY1⟩, hY2⟩
    have hOdisj : O ∩ (U ∩ chamber a h lam) = ∅ := by
      rw [← not_nonempty_iff_eq_empty]
      rintro ⟨Z, hZO, hZU, hZc⟩
      rw [hO] at hZO
      obtain ⟨⟨⟨-, -⟩, hZabs⟩, hZlam⟩ := hZO
      have hZabs' : |Z.1 - a| < h := by simpa using hZabs
      have hZlam' : Z.2 < lam := by simpa using hZlam
      rw [mem_chamber] at hZc
      rcases hZc with habs | hle
      · exact absurd hZabs' (not_lt.mpr (le_of_lt habs))
      · exact absurd hZlam' (not_lt.mpr hle)
    have hYnotcl : Y ∉ closure (U ∩ chamber a h lam) := by
      intro hmem
      have hne : (O ∩ (U ∩ chamber a h lam)).Nonempty := by
        rw [mem_closure_iff] at hmem
        exact hmem O hOopen hYO
      rw [hOdisj] at hne
      exact Set.not_nonempty_empty hne
    exact hYnotcl hYcl
  · rintro X ⟨hXU, hXc⟩
    rcases hXc with habs | hlt
    · have habs' : h < |X.1 - a| := by simpa using habs
      rcases lt_abs.mp habs' with h' | h'
      · have hO : IsOpen (U ∩ {Z : ℝ × ℝ | a + h < Z.1}) :=
          hUo.inter (isOpen_lt continuous_const continuous_fst)
        have hsub : U ∩ {Z : ℝ × ℝ | a + h < Z.1} ⊆ closure (U ∩ chamber a h lam) := by
          rintro Z ⟨hZU, hZ⟩
          exact subset_closure ⟨hZU, subset_chamber_of_slab_gt a h lam hZ⟩
        exact interior_maximal hsub hO ⟨hXU, Set.mem_ofPred_eq.mpr (by linarith)⟩
      · have hO : IsOpen (U ∩ {Z : ℝ × ℝ | Z.1 < a - h}) :=
          hUo.inter (isOpen_lt continuous_fst continuous_const)
        have hsub : U ∩ {Z : ℝ × ℝ | Z.1 < a - h} ⊆ closure (U ∩ chamber a h lam) := by
          rintro Z ⟨hZU, hZ⟩
          exact subset_closure ⟨hZU, subset_chamber_of_slab_lt a h lam hZ⟩
        exact interior_maximal hsub hO ⟨hXU, Set.mem_ofPred_eq.mpr (by linarith)⟩
    · have hlt' : lam < X.2 := by simpa using hlt
      have hO : IsOpen (U ∩ {Z : ℝ × ℝ | lam < Z.2}) :=
        hUo.inter (isOpen_lt continuous_const continuous_snd)
      have hsub : U ∩ {Z : ℝ × ℝ | lam < Z.2} ⊆ closure (U ∩ chamber a h lam) := by
        rintro Z ⟨hZU, hZ⟩
        exact subset_closure ⟨hZU, subset_chamber_of_level_lt a h lam hZ⟩
      exact interior_maximal hsub hO ⟨hXU, Set.mem_ofPred_eq.mpr hlt'⟩

/-! ## The main statement -/

/-- **The pieces and the interior of the planar image of a level of the tilted sweep.** -/
theorem planar_closure_facts_main (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : LeanEval.KnotTheory.PardonDistortion.R3) (h lam : ℝ)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) (hh : 0 < h) :
    closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam)
      = Work.Drive.Mono.FiberModel.wingPlus (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
          (Work.Drive.Mono.FiberModel.slabA u c v) h ∪
        Work.Drive.Mono.FiberModel.wingMinus (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
          (Work.Drive.Mono.FiberModel.slabA u c v) h ∪
        Work.Drive.Mono.FiberModel.cap0 (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) lam ∧
    interior (closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam)) =
      interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) ∩
        ({X : ℝ × ℝ | h < |X.1 - Work.Drive.Mono.FiberModel.slabA u c v|} ∪
          {X : ℝ × ℝ | lam < X.2}) ∧
    interior (closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam)) =
      interior (Work.Drive.Mono.FiberModel.wingPlus (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
          (Work.Drive.Mono.FiberModel.slabA u c v) h) ∪
        interior (Work.Drive.Mono.FiberModel.wingMinus (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
          (Work.Drive.Mono.FiberModel.slabA u c v) h) ∪
        interior (Work.Drive.Mono.FiberModel.cap0 (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) lam) ∧
    Convex ℝ (Work.Drive.Mono.FiberModel.wingPlus (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
          (Work.Drive.Mono.FiberModel.slabA u c v) h) ∧
    Convex ℝ (Work.Drive.Mono.FiberModel.wingMinus (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
          (Work.Drive.Mono.FiberModel.slabA u c v) h) ∧
    Convex ℝ (Work.Drive.Mono.FiberModel.cap0 (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) lam)
:= by
  have hZ := planarImage_eq s c σ u v h lam ℓ hv hℓv hℓne
  have hUo : IsOpen (interior (boxShadow s c σ v ℓ)) := isOpen_interior
  have hUc : Convex ℝ (interior (boxShadow s c σ v ℓ)) := (convex_boxShadow s c σ v ℓ).interior
  refine ⟨?_, ?_, ?_, convex_wingPlus s c σ v ℓ (slabA u c v) h,
    convex_wingMinus s c σ v ℓ (slabA u c v) h, convex_cap0 s c σ v ℓ lam⟩
  · rw [hZ, wingPlus, wingMinus, cap0]
    exact closure_inter_chamber_eq _ hUo _ _ _ hh
  · rw [hZ]
    exact interior_closure_inter_chamber_eq _ hUo hUc _ _ _ hh
  · have h3 : interior (closure (interior (boxShadow s c σ v ℓ) ∩ {X : ℝ × ℝ | slabA u c v + h < X.1}))
        = interior (boxShadow s c σ v ℓ) ∩ {X : ℝ × ℝ | slabA u c v + h < X.1} :=
      interior_closure_eq_self_of_isOpen_convex
        (hUc.inter (convex_setOf_fst_gt (slabA u c v + h)))
        (hUo.inter (isOpen_lt continuous_const continuous_fst))
    have h4 : interior (closure (interior (boxShadow s c σ v ℓ) ∩ {X : ℝ × ℝ | X.1 < slabA u c v - h}))
        = interior (boxShadow s c σ v ℓ) ∩ {X : ℝ × ℝ | X.1 < slabA u c v - h} :=
      interior_closure_eq_self_of_isOpen_convex
        (hUc.inter (convex_setOf_fst_lt (slabA u c v - h)))
        (hUo.inter (isOpen_lt continuous_fst continuous_const))
    have h5 : interior (closure (interior (boxShadow s c σ v ℓ) ∩ {X : ℝ × ℝ | lam < X.2}))
        = interior (boxShadow s c σ v ℓ) ∩ {X : ℝ × ℝ | lam < X.2} :=
      interior_closure_eq_self_of_isOpen_convex
        (hUc.inter (convex_setOf_snd_gt lam))
        (hUo.inter (isOpen_lt continuous_const continuous_snd))
    rw [hZ, wingPlus, wingMinus, cap0,
      interior_closure_inter_chamber_eq _ hUo hUc _ _ _ hh, h3, h4, h5]
    ext X
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hU, habs | hlam⟩
      · rcases lt_abs.mp habs with h' | h'
        · exact Or.inl (Or.inl ⟨hU, by linarith⟩)
        · exact Or.inl (Or.inr ⟨hU, by linarith⟩)
      · exact Or.inr ⟨hU, hlam⟩
    · rintro ((⟨hU, h'⟩ | ⟨hU, h'⟩) | ⟨hU, h'⟩)
      · exact ⟨hU, Or.inl (lt_abs.mpr (Or.inl (by linarith)))⟩
      · exact ⟨hU, Or.inl (lt_abs.mpr (Or.inr (by linarith)))⟩
      · exact ⟨hU, Or.inr h'⟩

end

end Work.Drive.Mono.FiberModel
