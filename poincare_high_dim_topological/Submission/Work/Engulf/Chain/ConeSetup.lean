import Mathlib
import Submission.Work.Engulf.Chain.ConeDefs
import Submission.Work.Engulf.Defs

/-!
# Newmann §12: the geometric API of the cone complex `Γ ∪ a ∗ σ`

Helper lemmas for `Work.Engulf.Chain.cone_l7hyp`: the barycentric ("relative interior") lemma for
simplicial complexes, and the elementary geometry of the cone over a face `σ`.
-/

open Set Metric PL

namespace Work.Engulf.Chain

variable {N : ℕ}

/-! ## The barycentric lemma -/

/-- If `y ∈ simp t` and `y` is a convex combination of the vertices of `s` with *strictly
positive* coefficients, then `s ⊆ t`. -/
theorem subset_of_pos_weights {K : Cx N} {s t : Finset (E N)} (hs : s ∈ K.faces)
    (ht : t ∈ K.faces) {y : E N} (hy : y ∈ simp t) {c : E N → ℝ}
    (hpos : ∀ v ∈ s, 0 < c v) (hsum : ∑ v ∈ s, c v = 1) (hcombo : ∑ v ∈ s, c v • v = y) :
    s ⊆ t := by
  have hy_s : y ∈ simp s := by
    rw [PL.simp, ← hcombo]
    exact (convex_convexHull ℝ (s : Set (E N))).sum_mem
      (fun v hv => le_of_lt (hpos v hv)) hsum
      (fun v hv => subset_convexHull ℝ _ (by simpa using hv))
  have hy_inter : y ∈ simp (s ∩ t) := by
    rw [← Work.Engulf.simp_inter hs ht]; exact ⟨hy_s, hy⟩
  obtain ⟨μ, hμ0, hμ1, hμc⟩ := Finset.mem_convexHull.mp hy_inter
  rw [Finset.centerMass_eq_of_sum_1 _ _ hμ1,
    Finset.sum_congr rfl (fun i _ => by rw [id_eq])] at hμc
  set ν : E N → ℝ := fun v => if hv : v ∈ s ∩ t then μ v else 0 with hν
  have hνsum : ∑ v ∈ s, ν v = 1 := by
    have h1 : ∑ v ∈ s ∩ t, ν v = ∑ v ∈ s, ν v :=
      Finset.sum_subset Finset.inter_subset_left
        (fun v _ hvn => by simp only [hν, dite_eq_right hvn])
    have h2 : ∑ v ∈ s ∩ t, ν v = ∑ v ∈ s ∩ t, μ v :=
      Finset.sum_congr rfl (fun v hv => by simp only [hν, dite_eq_left hv])
    rw [← h1, h2, hμ1]
  have hνvec : ∑ v ∈ s, ν v • v = y := by
    have h1 : ∑ v ∈ s ∩ t, ν v • v = ∑ v ∈ s, ν v • v :=
      Finset.sum_subset Finset.inter_subset_left
        (fun v _ hvn => by simp only [hν, dite_eq_right hvn, zero_smul])
    have h2 : ∑ v ∈ s ∩ t, ν v • v = ∑ v ∈ s ∩ t, μ v • v :=
      Finset.sum_congr rfl (fun v hv => by simp only [hν, dite_eq_left hv])
    rw [← h1, h2, hμc]
  have hkey := AffineIndependent.eq_of_sum_eq_sum_subtype (k := ℝ) (s := s) (K.indep hs)
    (hsum.trans hνsum.symm) (hcombo.trans hνvec.symm)
  intro v hv
  by_contra hvt
  have hmem : v ∉ s ∩ t := fun h => hvt (Finset.mem_inter.mp h).2
  have hz : ν v = 0 := by simp only [hν, dite_eq_right hmem]
  have := hpos v hv
  rw [hkey v hv, hz] at this
  exact lt_irrefl 0 this

/-- The centroid (average of the vertices) of a finite vertex set. -/
noncomputable def centroid (s : Finset (E N)) : E N := (s.card : ℝ)⁻¹ • ∑ v ∈ s, v

theorem centroid_mem_simp {s : Finset (E N)} (hs : s.Nonempty) : centroid s ∈ simp s := by
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  rw [PL.simp]
  have h1 : ∑ v ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard]
  have h2 : ∑ v ∈ s, (s.card : ℝ)⁻¹ • v = centroid s := by
    simp only [centroid, Finset.smul_sum]
  rw [← h2]
  exact (convex_convexHull ℝ (s : Set (E N))).sum_mem
    (fun v _ => inv_nonneg.mpr (Nat.cast_nonneg _)) h1
    (fun v hv => subset_convexHull ℝ _ (by simpa using hv))

/-- The centroid of a face of `K` lies in another face `simp t` only if `s ⊆ t`. -/
theorem subset_of_centroid_mem {K : Cx N} {s t : Finset (E N)} (hs : s ∈ K.faces)
    (ht : t ∈ K.faces) (h : centroid s ∈ simp t) : s ⊆ t := by
  have hsne : s.Nonempty := K.nonempty_of_mem_faces hs
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hsne
  have hposcard : 0 < (s.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hsne)
  refine subset_of_pos_weights hs ht h (fun v _ => inv_pos.mpr hposcard) ?_ ?_
  · rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard]
  · simp only [centroid, Finset.smul_sum]

/-! ## The cone complex `Γ ∪ a ∗ σ` -/

theorem mem_coneFaces_insert {Γ : Cx N} {σ u : Finset (E N)} {a : E N}
    (hu : u ∈ Γ.faces ∨ u = ∅) (huσ : u ⊆ σ) : insert a u ∈ coneFaces Γ σ a :=
  Or.inr ⟨u, hu, huσ, rfl⟩

theorem faces_subset_coneFaces {Γ : Cx N} (σ : Finset (E N)) (a : E N) :
    Γ.faces ⊆ coneFaces Γ σ a := Set.subset_union_left

theorem a_notMem_sigma {Γ : Cx N} {σ : Finset (E N)} {a : E N}
    (hσ : σ ∈ Γ.faces) (ha : a ∉ Γ.space) : a ∉ σ :=
  fun h => ha (Γ.subset_space hσ (by simpa using h))

theorem erase_mem_faces_or_empty {Γ : Cx N} {σ : Finset (E N)} (hσ : σ ∈ Γ.faces)
    (w : E N) : σ.erase w ∈ Γ.faces ∨ σ.erase w = ∅ := by
  by_cases h : σ.erase w = ∅
  · exact Or.inr h
  · exact Or.inl (Γ.down_closed hσ (Finset.erase_subset w σ) (Finset.nonempty_iff_ne_empty.mpr h))

theorem insert_a_erase_mem_faces {Γ Γ' : Cx N} {σ : Finset (E N)} {a : E N}
    (hΓ' : Γ'.faces = coneFaces Γ σ a) (hσ : σ ∈ Γ.faces) (w : E N) :
    insert a (σ.erase w) ∈ Γ'.faces := by
  rw [hΓ']
  exact mem_coneFaces_insert (erase_mem_faces_or_empty hσ w) (Finset.erase_subset w σ)

/-- The lateral boundary of the cone is the union of the cones over the `σ \ {w}`. -/
theorem coneBd_eq {σ : Finset (E N)} {a : E N} (ha : a ∉ σ) :
    coneBd a σ = ⋃ w ∈ σ, simp (insert a (σ.erase w)) := by
  unfold coneBd
  refine Set.iUnion₂_congr (fun w hw => ?_)
  rw [Finset.erase_insert_of_ne (a := a) (b := w) (s := σ)]
  intro h; exact ha (h ▸ hw)

/-- A cone face meets the old space `Γ.space` exactly in the simplex on its base. -/
theorem cone_face_inter_space {Γ Γ' : Cx N} {σ u : Finset (E N)} {a : E N}
    (hΓ' : Γ'.faces = coneFaces Γ σ a) (ha : a ∉ Γ.space)
    (hu : u ∈ Γ.faces ∨ u = ∅) (huσ : u ⊆ σ) :
    simp (insert a u) ∩ Γ.space = simp u := by
  have hufaces : insert a u ∈ Γ'.faces := by rw [hΓ']; exact mem_coneFaces_insert hu huσ
  have hGfaces : Γ.faces ⊆ Γ'.faces := by rw [hΓ']; exact faces_subset_coneFaces σ a
  refine Subset.antisymm ?_ ?_
  · rintro x ⟨hx, hxG⟩
    obtain ⟨t, ht, hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hxG
    have ht' : t ∈ Γ'.faces := hGfaces ht
    have hsub : x ∈ simp t ∩ simp (insert a u) := ⟨hxt, hx⟩
    rw [Work.Engulf.simp_inter ht' hufaces] at hsub
    have hant : a ∉ t := fun h => ha (Γ.subset_space ht (by simpa using h))
    have hti : t ∩ insert a u = t ∩ u := Finset.inter_insert_of_notMem hant
    rw [hti] at hsub
    exact Work.Engulf.simp_mono Finset.inter_subset_right hsub
  · rcases hu with hu | rfl
    · exact subset_inter (Work.Engulf.simp_mono (Finset.subset_insert a u))
        (Γ.convexHull_subset_space hu)
    · rw [Work.Engulf.simp_empty]; exact subset_inter (Set.empty_subset _) (Set.empty_subset _)

theorem coneBd_inter_space_subset {Γ Γ' : Cx N} {σ : Finset (E N)} {a : E N}
    (hΓ' : Γ'.faces = coneFaces Γ σ a) (ha : a ∉ Γ.space) (hσ : σ ∈ Γ.faces) :
    coneBd a σ ∩ Γ.space ⊆ simp σ := by
  rw [coneBd_eq (a_notMem_sigma hσ ha)]
  rintro x ⟨hx, hxG⟩
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
  have hx' : x ∈ simp (σ.erase w) := by
    have h2 := cone_face_inter_space hΓ' ha (erase_mem_faces_or_empty hσ w)
      (Finset.erase_subset w σ)
    rw [← h2]; exact ⟨hxw, hxG⟩
  exact Work.Engulf.simp_mono (Finset.erase_subset w σ) hx'

/-- The cone over all of `σ` is not contained in `H ∪ coneBd a σ`. -/
theorem not_simp_insert_sigma_subset {Γ Γ' : Cx N} {σ : Finset (E N)} {a : E N}
    {H : Set (E N)} (hΓ' : Γ'.faces = coneFaces Γ σ a) (hH : Work.Engulf.IsSubSp Γ H)
    (ha : a ∉ Γ.space) (hσ : σ ∈ Γ.faces) :
    ¬ (simp (insert a σ) ⊆ H ∪ coneBd a σ) := by
  intro hsub
  have hasig : insert a σ ∈ Γ'.faces := by
    rw [hΓ']; exact mem_coneFaces_insert (Or.inl hσ) (le_refl σ)
  have hy : centroid (insert a σ) ∈ simp (insert a σ) :=
    centroid_mem_simp (Finset.insert_nonempty a σ)
  have hane : a ∉ σ := a_notMem_sigma hσ ha
  rcases hsub hy with hyH | hyB
  · obtain ⟨t, ht, hyt, htsub⟩ := hH.2 _ hyH
    have ht' : t ∈ Γ'.faces := by rw [hΓ']; exact faces_subset_coneFaces σ a ht
    have hle : insert a σ ⊆ t := subset_of_centroid_mem hasig ht' hyt
    have : a ∈ t := hle (Finset.mem_insert_self a σ)
    exact ha (Γ.subset_space ht (by simpa using this))
  · rw [coneBd_eq hane] at hyB
    obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp hyB
    have hle : insert a σ ⊆ insert a (σ.erase w) :=
      subset_of_centroid_mem hasig (insert_a_erase_mem_faces hΓ' hσ w) hyw
    have hw' : w ∈ insert a (σ.erase w) := hle (Finset.mem_insert_of_mem hw)
    rcases Finset.mem_insert.mp hw' with h | h
    · exact hane (by rw [← h]; exact hw)
    · exact Finset.notMem_erase w σ h

/-- An old face `s` whose simplex is contained in `H ∪ coneBd a σ` is contained in `H`. -/
theorem subset_H_of_subset_union {Γ Γ' : Cx N} {σ s : Finset (E N)} {a : E N}
    {H : Set (E N)} (hΓ' : Γ'.faces = coneFaces Γ σ a) (hH : Work.Engulf.IsSubSp Γ H)
    (ha : a ∉ Γ.space) (hσ : σ ∈ Γ.faces) (hσH : simp σ ⊆ H) (hs : s ∈ Γ.faces)
    (h : simp s ⊆ H ∪ coneBd a σ) : simp s ⊆ H := by
  have hsne : s.Nonempty := Γ.nonempty_of_mem_faces hs
  have hy : centroid s ∈ simp s := centroid_mem_simp hsne
  have hsG : s ∈ Γ'.faces := by rw [hΓ']; exact faces_subset_coneFaces σ a hs
  have hane : a ∉ σ := a_notMem_sigma hσ ha
  rcases h hy with hyH | hyB
  · obtain ⟨t, ht, hyt, htsub⟩ := hH.2 _ hyH
    have ht' : t ∈ Γ'.faces := by rw [hΓ']; exact faces_subset_coneFaces σ a ht
    exact (Work.Engulf.simp_mono (subset_of_centroid_mem hsG ht' hyt)).trans htsub
  · rw [coneBd_eq hane] at hyB
    obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp hyB
    have hle : s ⊆ insert a (σ.erase w) :=
      subset_of_centroid_mem hsG (insert_a_erase_mem_faces hΓ' hσ w) hyw
    have hsσ : s ⊆ σ := by
      intro v hv
      rcases Finset.mem_insert.mp (hle hv) with hva | hv'
      · rw [hva] at hv
        exact absurd (Γ.subset_space hs (by simpa using hv)) ha
      · exact Finset.mem_of_mem_erase hv'
    exact (Work.Engulf.simp_mono hsσ).trans hσH

/-! ## `coneK`, `topOf` and the face sets -/

theorem topOf_singleton {N : ℕ} (a : E N) (σ : Finset (E N)) (hane : a ∉ σ) :
    Work.Engulf.topOf {a} σ = simp σ := by
  have h1 : ∀ w ∈ ({a} : Finset (E N)), ({a} ∪ σ).erase w = σ := by
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    rw [Finset.singleton_union, Finset.erase_insert_eq_erase,
      Finset.erase_eq_of_notMem hane]
  unfold Work.Engulf.topOf
  rw [show (⋃ w ∈ ({a} : Finset (E N)), simp (({a} ∪ σ).erase w))
        = (⋃ w ∈ ({a} : Finset (E N)), simp σ) from
      Set.iUnion₂_congr (fun w hw => by rw [h1 w hw])]
  ext x
  simp only [Set.mem_iUnion, exists_prop, Finset.mem_singleton]
  constructor
  · rintro ⟨y, rfl, hx⟩; exact hx
  · intro hx; exact ⟨a, rfl, hx⟩

theorem coneFaces_finite {Γ : Cx N} {σ : Finset (E N)} {a : E N}
    (hfin : Γ.faces.Finite) : (coneFaces Γ σ a).Finite := by
  refine hfin.union ?_
  refine Set.Finite.subset (Finset.finite_toSet (insert a σ).powerset) ?_
  rintro t ⟨s, hs, hsσ, rfl⟩
  rw [Finset.mem_coe, Finset.mem_powerset]
  exact Finset.insert_subset_insert a hsσ

theorem dimLE_of_faces_eq {Γ Γ' : Cx N} {σ : Finset (E N)} {a : E N} {p q : ℕ}
    (hΓ' : Γ'.faces = coneFaces Γ σ a) (hdim : DimLE Γ (p + 1))
    (hcard : σ.card = q + 1) (hq : q ≤ p) : DimLE Γ' (p + 1) := by
  intro t ht
  rw [hΓ'] at ht
  rcases ht with ht | ⟨u, hu, huσ, rfl⟩
  · exact hdim t ht
  · have h1 : (insert a u).card ≤ σ.card + 1 :=
      (Finset.card_insert_le a u).trans (Nat.succ_le_succ (Finset.card_le_card huσ))
    omega

theorem isSubSp_mono_faces {Γ Γ' : Cx N} {S : Set (E N)} (h : Γ.faces ⊆ Γ'.faces)
    (hS : Work.Engulf.IsSubSp Γ S) : Work.Engulf.IsSubSp Γ' S := by
  obtain ⟨T, hT, rfl⟩ := (Work.Engulf.isSubSp_iff Γ S).1 hS
  exact Work.Engulf.isSubSp_of_faces (hT.trans h)

theorem isSubSp_coneBd {Γ Γ' : Cx N} {σ : Finset (E N)} {a : E N}
    (hΓ' : Γ'.faces = coneFaces Γ σ a) (hσ : σ ∈ Γ.faces) (hane : a ∉ σ) :
    Work.Engulf.IsSubSp Γ' (coneBd a σ) := by
  rw [coneBd_eq hane]
  refine ⟨?_, ?_⟩
  · rintro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
    exact Γ'.convexHull_subset_space (insert_a_erase_mem_faces hΓ' hσ w) hxw
  · rintro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨insert a (σ.erase w), insert_a_erase_mem_faces hΓ' hσ w, hxw,
      fun y hy => Set.mem_iUnion₂.mpr ⟨w, hw, hy⟩⟩

theorem isSubSp_coneK {Γ Γ' : Cx N} {σ : Finset (E N)} {a : E N} {H : Set (E N)}
    (hΓ' : Γ'.faces = coneFaces Γ σ a) (hσ : σ ∈ Γ.faces) (hane : a ∉ σ) :
    Work.Engulf.IsSubSp Γ' (coneK Γ H σ a) := by
  have hGfaces : Γ.faces ⊆ Γ'.faces := by rw [hΓ']; exact faces_subset_coneFaces σ a
  refine Work.Engulf.isSubSp_union (Work.Engulf.isSubSp_of_faces ?_) (isSubSp_coneBd hΓ' hσ hane)
  rintro t ⟨ht, -, -⟩
  exact hGfaces ht

/-- `coneK ∪ topOf {a} σ = H ∪ coneBd a σ`. -/
theorem coneK_union_topOf {Γ : Cx N} {H : Set (E N)} {σ : Finset (E N)} {a : E N}
    (hH : Work.Engulf.IsSubSp Γ H) (hσ : σ ∈ Γ.faces) (hσH : simp σ ⊆ H) (hane : a ∉ σ) :
    coneK Γ H σ a ∪ Work.Engulf.topOf {a} σ = H ∪ coneBd a σ := by
  rw [topOf_singleton a σ hane]
  refine Subset.antisymm ?_ ?_
  · rintro x ((hx | hx) | hx)
    · obtain ⟨s, ⟨hs, hsH, -⟩, hxs⟩ := Set.mem_iUnion₂.mp hx
      exact Or.inl (hsH hxs)
    · exact Or.inr hx
    · exact Or.inl (hσH hx)
  · rintro x (hx | hx)
    · obtain ⟨s, hs, hxs, hsH⟩ := hH.2 x hx
      rcases eq_or_ne s σ with rfl | hsne
      · exact Or.inr hxs
      · exact Or.inl (Or.inl (Set.mem_iUnion₂.mpr ⟨s, ⟨hs, hsH, hsne⟩, hxs⟩))
    · exact Or.inl (Or.inr hx)

/-- `coneK Γ H σ a ∩ simp (insert a σ) = coneBd a σ` (condition (12.1)). -/
theorem coneK_inter_simp_insert {Γ Γ' : Cx N} {H : Set (E N)} {σ : Finset (E N)} {a : E N}
    (hΓ' : Γ'.faces = coneFaces Γ σ a) (ha : a ∉ Γ.space) (hσ : σ ∈ Γ.faces)
    (hσH : simp σ ⊆ H) (hprinc : ∀ s ∈ Γ.faces, simp s ⊆ H → σ ⊆ s → s = σ) :
    coneK Γ H σ a ∩ simp (insert a σ) = coneBd a σ := by
  have hane : a ∉ σ := a_notMem_sigma hσ ha
  have hsig : insert a σ ∈ Γ'.faces := by
    rw [hΓ']; exact mem_coneFaces_insert (Or.inl hσ) (le_refl σ)
  have hGfaces : Γ.faces ⊆ Γ'.faces := by rw [hΓ']; exact faces_subset_coneFaces σ a
  refine Subset.antisymm ?_ ?_
  · rintro x ⟨hxK, hxs⟩
    rcases hxK with hxK | hxB
    · obtain ⟨s, ⟨hs, hsH, hsne⟩, hxs'⟩ := Set.mem_iUnion₂.mp hxK
      have hsG : s ∈ Γ'.faces := hGfaces hs
      have hmem : x ∈ simp (s ∩ σ) := by
        have h1 : x ∈ simp s ∩ simp (insert a σ) := ⟨hxs', hxs⟩
        rw [Work.Engulf.simp_inter hsG hsig] at h1
        have has : a ∉ s := fun h => ha (Γ.subset_space hs (by simpa using h))
        have hsi : s ∩ insert a σ = s ∩ σ := Finset.inter_insert_of_notMem has
        rwa [hsi] at h1
      have hssub : s ∩ σ ⊂ σ := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, ?_⟩
        intro hcontra
        exact hsne (hprinc s hs hsH (by rw [← hcontra]; exact Finset.inter_subset_left))
      obtain ⟨w, hwσ, hws⟩ :=
        (Finset.ssubset_iff_of_subset Finset.inter_subset_right).mp hssub
      have hsub : s ∩ σ ⊆ σ.erase w := by
        intro v hv
        rw [Finset.mem_erase]
        exact ⟨fun hvw => hws (hvw ▸ hv), (Finset.mem_inter.mp hv).2⟩
      have hxw : x ∈ simp (insert a (σ.erase w)) :=
        Work.Engulf.simp_mono (hsub.trans (Finset.subset_insert a (σ.erase w))) hmem
      rw [coneBd_eq hane]
      exact Set.mem_iUnion₂.mpr ⟨w, hwσ, hxw⟩
    · exact hxB
  · rintro x hxB
    refine ⟨Or.inr hxB, ?_⟩
    rw [coneBd_eq hane] at hxB
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hxB
    exact Work.Engulf.simp_mono (Finset.insert_subset_insert a (Finset.erase_subset w σ)) hxw

end Work.Engulf.Chain
