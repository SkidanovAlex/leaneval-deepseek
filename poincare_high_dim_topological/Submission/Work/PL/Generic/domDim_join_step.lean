import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic
import Submission.Work.PL.Generic.exists_ioc_smul_add_of_mem_convexHull_insert
import Submission.Work.PL.Generic.domDim_of_isBounded_subset_affineSubspace

namespace Work.PL.Generic

open Set Metric

/-- `finrank ℝ (PL.E m) = m`. -/
theorem finrank_E (m : ℕ) : Module.finrank ℝ (PL.E m) = m := by
  show Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m
  rw [finrank_euclideanSpace]; simp

/-- The direction of the affine span of a finset of `n + 1` points has dimension at most `n`. -/
theorem finrank_direction_affineSpan_finset_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    [DecidableEq V] (t : Finset V) {n : ℕ} (hc : t.card = n + 1) :
    Module.finrank ℝ (affineSpan ℝ (t : Set V)).direction ≤ n := by
  rw [direction_affineSpan]
  have h := finrank_vectorSpan_image_finset_le (k := ℝ) (id : V → V) t hc
  rw [Finset.image_id] at h
  exact h

/-- An affine subspace is closed under two-point affine combinations. -/
theorem affineSubspace_add_smul_vsub_mem {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : AffineSubspace ℝ V) {a b : V} (ha : a ∈ Q) (hb : b ∈ Q)
    (c : ℝ) : a +ᵥ (c • (b -ᵥ a)) ∈ Q := by
  have h1 : b -ᵥ a ∈ Q.direction := AffineSubspace.vsub_mem_direction hb ha
  have h2 : c • (b -ᵥ a) ∈ Q.direction := Submodule.smul_mem _ c h1
  have h3 : (c • (b -ᵥ a)) +ᵥ a ∈ Q :=
    (AffineSubspace.vadd_mem_iff_mem_direction (c • (b -ᵥ a)) ha).mpr h2
  simpa [vadd_eq_add, add_comm] using h3

/-- Case A of the one-vertex join step: a point of the "new part" of `simp (s ∪ {y})` which also
lies in `simp σ` forces `y` into the affine span of `s ∪ σ`. -/
theorem mem_affineSpan_union_of_mem_simp_insert {m : ℕ} {s σ : Finset (PL.E m)} {y x : PL.E m}
    (hx : x ∈ PL.simp (s ∪ {y})) (hx' : x ∉ PL.simp s) (hxσ : x ∈ PL.simp σ) :
    y ∈ (affineSpan ℝ ((s : Set (PL.E m)) ∪ (σ : Set (PL.E m))) : Set (PL.E m)) := by
  classical
  set Q := affineSpan ℝ ((s : Set (PL.E m)) ∪ (σ : Set (PL.E m))) with hQ
  have hleS : affineSpan ℝ (s : Set (PL.E m)) ≤ Q := affineSpan_mono ℝ Set.subset_union_left
  have hleσ : affineSpan ℝ (σ : Set (PL.E m)) ≤ Q := affineSpan_mono ℝ Set.subset_union_right
  have hS : PL.simp s ⊆ (Q : Set (PL.E m)) := fun a ha => hleS (PL.simp_subset_affineSpan s ha)
  have hσ : PL.simp σ ⊆ (Q : Set (PL.E m)) := fun a ha => hleσ (PL.simp_subset_affineSpan σ ha)
  by_cases hs : s = ∅
  · have hxy : x = y := by
      have h1 : PL.simp (s ∪ {y}) = ({y} : Set (PL.E m)) := by
        rw [hs, Finset.empty_union, PL.simp_singleton]
      rw [h1] at hx
      simpa using hx
    rw [← hxy]
    exact hσ hxσ
  · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.2 hs
    obtain ⟨μ, hμ, p, hp, hxp⟩ :=
      exists_ioc_smul_add_of_mem_convexHull_insert hne hx hx'
    have hμne : μ ≠ 0 := ne_of_gt hμ.1
    have hid : y = x +ᵥ (((μ - 1) / μ) • (p -ᵥ x)) := by
      rw [hxp]
      simp only [vsub_eq_sub, vadd_eq_add, smul_add, smul_sub, smul_smul]
      match_scalars <;> field_simp <;> ring
    rw [hid]
    exact affineSubspace_add_smul_vsub_mem Q (hσ hxσ) (hS hp) _

/-- The one-vertex general-position step ("new part" of a join).
`hy : y ∉ affineSpan s` gives the unique join decomposition `x = (1-μ)p + μy`, `p ∈ simp s`; `hgen`
is the general-position condition: either `y` is outside the affine span of `s ∪ σ`, in which case the
set is empty (an affine combination argument), or that span is everything, in which case the set lies
in the affine intersection `affineSpan (s ∪ {y}) ⊓ affineSpan σ`, whose dimension is bounded by
`|s| + (|σ| - 1) - m` via the dimension formula for intersecting affine subspaces, so that
`Work.PL.Generic.domDim_of_isBounded_subset_affineSubspace` applies (the set is inside the compact
`simp σ`).  Used by `Work.PL.Generic.gp_pairs` with `s = (pr.1.erase u).image y`, `σ = S`. -/
theorem domDim_join_step {m : ℕ} {s σ : Finset (PL.E m)} {y : PL.E m}
    (hy : y ∉ (affineSpan ℝ (s : Set (PL.E m)) : Set (PL.E m)))
    (hgen : y ∉ (affineSpan ℝ ((s : Set (PL.E m)) ∪ (σ : Set (PL.E m))) : Set (PL.E m)) ∨
      affineSpan ℝ ((s : Set (PL.E m)) ∪ (σ : Set (PL.E m))) = ⊤) :
    PL.DomDim ((PL.simp (s ∪ {y}) \ PL.simp s) ∩ PL.simp σ)
      ((s.card : ℤ) + (σ.card : ℤ) - 1 - (Module.finrank ℝ (PL.E m) : ℤ)) := by
  classical
  by_cases hσ : σ = ∅
  · have hAempty : (PL.simp (s ∪ {y}) \ PL.simp s) ∩ PL.simp σ = ∅ := by
      rw [hσ, PL.simp_empty, Set.inter_empty]
    rw [hAempty]
    exact PL.DomDim.empty _
  set Q := affineSpan ℝ ((s : Set (PL.E m)) ∪ (σ : Set (PL.E m))) with hQ
  set T := affineSpan ℝ ((s : Set (PL.E m)) ∪ ({y} : Set (PL.E m))) with hT
  set W := affineSpan ℝ (σ : Set (PL.E m)) with hW
  rcases hgen with hyout | htop
  · have hempty : (PL.simp (s ∪ {y}) \ PL.simp s) ∩ PL.simp σ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨⟨hx1, hx2⟩, hx3⟩
      exact hyout (mem_affineSpan_union_of_mem_simp_insert hx1 hx2 hx3)
    rw [hempty]
    exact PL.DomDim.empty _
  · have hfin : (Module.finrank ℝ (PL.E m) : ℤ) = (m : ℤ) := by
      rw [finrank_E]
    have hys : y ∉ s := by
      intro h
      exact hy (subset_affineSpan ℝ (s : Set (PL.E m)) (by simpa using h))
    have hTcard : (s ∪ {y}).card = s.card + 1 := by
      rw [Finset.union_singleton, Finset.card_insert_of_notMem hys]
    have hTle : Module.finrank ℝ T.direction ≤ s.card := by
      have hTeq : T = affineSpan ℝ ((s ∪ {y} : Finset (PL.E m)) : Set (PL.E m)) := by
        rw [hT]
        congr 1
        rw [Finset.coe_union, Finset.coe_singleton]
      rw [hTeq]
      exact finrank_direction_affineSpan_finset_le _ hTcard
    have hAF : (PL.simp (s ∪ {y}) \ PL.simp s) ∩ PL.simp σ ⊆
        ((T ⊓ W : AffineSubspace ℝ (PL.E m)) : Set (PL.E m)) := by
      rintro x ⟨hx1, hxσ'⟩
      refine ⟨?_, ?_⟩
      · have h : PL.simp (s ∪ {y}) ⊆ (T : Set (PL.E m)) := by
          rw [hT]
          simpa [Finset.coe_union, Finset.coe_singleton] using PL.simp_subset_affineSpan (s ∪ {y})
        exact h hx1.1
      · have h : PL.simp σ ⊆ (W : Set (PL.E m)) := by
          rw [hW]
          exact PL.simp_subset_affineSpan σ
        exact h hxσ'
    rcases Set.eq_empty_or_nonempty ((T ⊓ W : AffineSubspace ℝ (PL.E m)) : Set (PL.E m)) with hF | ⟨z, hz⟩
    · have hAempty : (PL.simp (s ∪ {y}) \ PL.simp s) ∩ PL.simp σ = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        have h := hAF hx
        rw [hF] at h
        exact h
      rw [hAempty]
      exact PL.DomDim.empty _
    · have hbd : Bornology.IsBounded ((PL.simp (s ∪ {y}) \ PL.simp s) ∩ PL.simp σ) :=
        (PL.isBounded_simp (s ∪ {y})).subset (fun x hx => hx.1.1)
      have hσne : σ.Nonempty := Finset.nonempty_iff_ne_empty.2 hσ
      have hσ1 : 1 ≤ σ.card := by have := Finset.card_pos.2 hσne; omega
      have hWle : Module.finrank ℝ W.direction ≤ σ.card - 1 := by
        rw [hW]
        exact finrank_direction_affineSpan_finset_le σ (by omega : σ.card = (σ.card - 1) + 1)
      have hFdir : (T ⊓ W).direction = T.direction ⊓ W.direction :=
        AffineSubspace.direction_inf_of_mem hz.1 hz.2
      have hsupdir : (T ⊔ W).direction = T.direction ⊔ W.direction := by
        rw [AffineSubspace.direction_sup hz.1 hz.2]
        simp
      have hTsupW : T ⊔ W = ⊤ := by
        have hle : Q ≤ T ⊔ W := by
          rw [hQ]
          rw [affineSpan_le]
          rintro a (ha | ha)
          · exact (le_sup_left : T ≤ T ⊔ W) (by rw [hT]; exact subset_affineSpan ℝ _ (Set.mem_union_left _ ha))
          · exact (le_sup_right : W ≤ T ⊔ W) (by rw [hW]; exact subset_affineSpan ℝ _ ha)
        rw [htop] at hle
        exact top_le_iff.1 hle
      have hdim : (Module.finrank ℝ (T ⊓ W).direction : ℤ) ≤
          (s.card : ℤ) + (σ.card : ℤ) - 1 - (Module.finrank ℝ (PL.E m) : ℤ) := by
        rw [hfin, hFdir]
        have key := Submodule.finrank_sup_add_finrank_inf_eq T.direction W.direction
        have hsup : Module.finrank ℝ ↥(T.direction ⊔ W.direction) = m := by
          rw [← hsupdir, hTsupW, AffineSubspace.direction_top, finrank_top, finrank_E]
        have hTl : (Module.finrank ℝ T.direction : ℤ) ≤ (s.card : ℤ) := by exact_mod_cast hTle
        have hWl : (Module.finrank ℝ W.direction : ℤ) ≤ (σ.card : ℤ) - 1 := by
          have := hWle; omega
        have hsupz : (Module.finrank ℝ ↥(T.direction ⊔ W.direction) : ℤ) = (m : ℤ) := by
          rw [hsup]
        omega
      exact domDim_of_isBounded_subset_affineSubspace hbd hAF hdim

end Work.PL.Generic
