/-
A6 `Geo/DualStretch` — basic API for the low/high skeleta.
-/
import Submission.Work.Geo.DualStretch.Defs

open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

open PL (E Cx closedCube openCube)

variable {n : ℕ}

/-! ### Elementary API -/

/-- A subface spans a subset of the simplex. -/
theorem simp_mono {σ τ : Finset (E n)} (h : σ ⊆ τ) : PL.simp σ ⊆ PL.simp τ :=
  convexHull_mono (by exact_mod_cast h)

/-- The barycentre of a nonempty finite set lies in the simplex it spans. -/
theorem bary_mem_simp {s : Finset (E n)} (hs : s.Nonempty) : bary s ∈ PL.simp s := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  have hb : bary s = s.centerMass (fun _ => (1 : ℝ)) (fun v : E n => v) := by
    rw [Finset.centerMass, Finset.sum_const, nsmul_eq_mul, mul_one]
    simp [bary, hcard.ne']
  rw [hb, PL.simp]
  exact Finset.centerMass_mem_convexHull (s := (s : Set (E n))) (t := s)
    (w := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) (by simpa using hcard)
    (z := fun v => v) (fun v hv => by simpa using hv)

/-- Every face of a complex triangulating `closedCube β` spans a subset of that cube. -/
theorem simp_subset_closedCube {β : ℝ} {P : Cx n} (hsp : P.space = closedCube β)
    {s : Finset (E n)} (hs : s ∈ P.faces) : PL.simp s ⊆ closedCube β := by
  rw [← hsp]
  exact Geometry.SimplicialComplex.convexHull_subset_space hs

theorem Low_subset_space (P : Cx n) (p : ℕ) : Low P p ⊆ P.space := by
  rintro x ⟨s, hs, -, hx⟩
  exact Geometry.SimplicialComplex.convexHull_subset_space hs hx

theorem High_subset_space (P : Cx n) (p : ℕ) : High P p ⊆ P.space := by
  rintro x ⟨T, hT, hne, hchain, hcard, hx⟩
  obtain ⟨σ, hσT, hmax⟩ := Finset.exists_max_image T (fun σ => σ.card) hne
  have hσ : σ ∈ P.faces := hT (by simpa using hσT)
  have hsub : ∀ τ ∈ T, τ ⊆ σ := by
    intro τ hτT
    rcases hchain τ hτT σ hσT with h | h
    · exact h
    · have hcard_eq : τ.card = σ.card := le_antisymm (hmax τ hτT) (Finset.card_le_card h)
      have hστ : σ = τ := Finset.eq_of_subset_of_card_le h (le_of_eq hcard_eq)
      rw [hστ]
  have hle : PL.simp (T.image bary) ⊆ PL.simp σ := by
    rw [PL.simp]
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro y hy
    rw [Finset.mem_coe, Finset.mem_image] at hy
    obtain ⟨τ, hτT, rfl⟩ := hy
    have hτ : τ ∈ P.faces := hT (by simpa using hτT)
    exact simp_mono (hsub τ hτT)
      (bary_mem_simp (Geometry.SimplicialComplex.nonempty_of_mem_faces hτ))
  exact Geometry.SimplicialComplex.convexHull_subset_space hσ (hle hx)

/-- The topological boundary of the cube. -/
theorem bdryCube_eq (β : ℝ) :
    bdryCube (n := n) β = ⋃ i : Fin n, {x : E n | |x i| = β} := by
  ext x; simp [bdryCube]

theorem isClosed_bdryCube (β : ℝ) : IsClosed (bdryCube (n := n) β) := by
  rw [bdryCube_eq]
  exact isClosed_iUnion_of_finite fun i =>
    isClosed_eq (by fun_prop : Continuous fun x : E n => |x i|) continuous_const

/-- The smaller closed cube sits in the larger open cube. -/
theorem closedCube_subset_openCube {α β : ℝ} (hαβ : α < β) :
    closedCube (n := n) α ⊆ openCube (n := n) β := by
  intro x hx i
  exact lt_of_le_of_lt (hx i) hαβ

theorem openCube_subset_closedCube {β : ℝ} : openCube (n := n) β ⊆ closedCube (n := n) β :=
  fun x hx i => le_of_lt (hx i)

/-! ### `low_dom` -/

/-- The `p`-skeleton is `p`-dominated (Newman's `DomDim`). -/
theorem low_dom (P : Cx n) (hP : P.faces.Finite) (p : ℕ) : PL.DomDim (Low P p) (p : ℤ) := by
  refine ⟨hP.toFinset.filter (fun s => s.card ≤ p + 1), ?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_filter] at hs
    have : (s.card : ℤ) ≤ (p : ℤ) + 1 := by
      have h1 : s.card ≤ p + 1 := hs.2
      omega
    simpa using this
  · intro x hx
    obtain ⟨s, hs, hcard, hxs⟩ := hx
    simp only [mem_iUnion₂]
    exact ⟨s, Finset.mem_filter.2 ⟨by simpa using hs, by simpa using hcard⟩, hxs⟩

/-! ### The cover of `High` used for `high_dom` -/

/-- The candidate cover of `High P p` by barycentre-simplices of chains of large faces. -/
noncomputable def highCover (P : Cx n) (hP : P.faces.Finite) (p : ℕ) : Finset (Finset (E n)) :=
  (hP.toFinset.powerset.filter
    (fun T => T.Nonempty ∧ IsChain T ∧ ∀ σ ∈ T, p + 2 ≤ σ.card)).image (fun T => T.image bary)

theorem High_subset_highCover (P : Cx n) (hP : P.faces.Finite) (p : ℕ) :
    High P p ⊆ ⋃ s ∈ highCover P hP p, PL.simp s := by
  rintro x ⟨T, hT, hne, hchain, hcard, hx⟩
  simp only [mem_iUnion₂]
  refine ⟨T.image bary, ?_, hx⟩
  refine Finset.mem_image.2 ⟨T, ?_, rfl⟩
  refine Finset.mem_filter.2 ⟨?_, hne, hchain, hcard⟩
  have : (T : Set (Finset (E n))) ⊆ (hP.toFinset : Set (Finset (E n))) :=
    fun σ hσ => by simpa using hT hσ
  simpa [Finset.mem_powerset, Finset.coe_subset] using this

end Work.Geo.DualStretch
