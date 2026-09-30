import Mathlib
import Submission.Work.Serre.DiscPair.collarDefs

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

/-- A convex combination of two points of the unit interval which are `< M` is `< M`. -/
lemma convexComb_lt_of_lt {x y : unitInterval} {M : ℝ} (hx : (x : ℝ) < M) (hy : (y : ℝ) < M)
    (t : unitInterval) : (Set.Icc.convexComb x y t : ℝ) < M := by
  rw [Set.Icc.coe_convexComb]
  rcases eq_or_lt_of_le (t.2.2 : (t : ℝ) ≤ 1) with ht | ht
  · rw [ht]; simpa using hy
  · have h1 : 0 < 1 - (t : ℝ) := by linarith
    have h2 : (1 - (t : ℝ)) * (x : ℝ) < (1 - (t : ℝ)) * M := mul_lt_mul_of_pos_left hx h1
    have h3 : (t : ℝ) * (y : ℝ) ≤ (t : ℝ) * M := mul_le_mul_of_nonneg_left (le_of_lt hy) t.2.1
    nlinarith

/-- A convex combination of two positive points of the unit interval is positive. -/
lemma convexComb_pos_of_pos {x y : unitInterval} (hx : 0 < (x : ℝ)) (hy : 0 < (y : ℝ))
    (t : unitInterval) : 0 < (Set.Icc.convexComb x y t : ℝ) := by
  rw [Set.Icc.coe_convexComb]
  rcases eq_or_lt_of_le (t.2.1 : (0 : ℝ) ≤ (t : ℝ)) with ht | ht
  · rw [← ht]; simpa using hx
  · have h1 : 0 ≤ 1 - (t : ℝ) := by linarith [t.2.2]
    have h2 : 0 < (t : ℝ) * (y : ℝ) := mul_pos ht hy
    have h3 : 0 ≤ (1 - (t : ℝ)) * (x : ℝ) := mul_nonneg h1 (le_of_lt hx)
    linarith

/-- The point `1/4` of the unit interval. -/
noncomputable def qtr : unitInterval := ⟨1/4, by norm_num⟩

@[simp] lemma coe_qtr : ((qtr : unitInterval) : ℝ) = 1/4 := rfl

/-- **The collar models are homotopy equivalent to the spaces they come from.**
`cylSet₁ = (X × {0}) ∪ (A × (0,1/2))` deformation retracts onto `X × {0} ≅ X` by `t ↦ (1-s) t`,
and `cylSet₂ = A × (0,1/2)` onto `A × {1/4} ≅ A`; both homotopy equivalences are the projections
`(x,t) ↦ x`. -/
theorem collarSetHomotopyEquiv (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    (∃ e : ContinuousMap.HomotopyEquiv
        ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) X,
      ∀ z, e.toFun z = z.1.1) ∧
    (∃ e : ContinuousMap.HomotopyEquiv
        ↥(cylSet₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)
        ↥(cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q),
      ∀ z, e.toFun z = ⟨z.1.1, z.2.2.2⟩) := by
  constructor
  · -- ## Part 1: the projection `cylSet₁ → X`
    have h0mem : ∀ x : X, (x, (0 : unitInterval)) ∈
        cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q := by
      intro x
      show ((0 : unitInterval) : ℝ) < 1 / 2 ∧ ((0 : unitInterval) = 0 ∨
        x ∈ cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)
      exact ⟨by norm_num, Or.inl rfl⟩
    have hsec : Continuous fun x : X =>
        (⟨(x, (0 : unitInterval)), h0mem x⟩ :
          ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)) :=
      Continuous.subtype_mk (continuous_id.prodMk continuous_const) h0mem
    have hproj : Continuous fun z :
        ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) => z.1.1 :=
      continuous_fst.comp continuous_subtype_val
    have hHmem : ∀ a : unitInterval ×
        ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q),
        (a.2.1.1, Set.Icc.convexComb (0 : unitInterval) a.2.1.2 a.1) ∈
          cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q := by
      intro a
      have hz : ((a.2.1.2 : unitInterval) : ℝ) < 1 / 2 ∧
          (a.2.1.2 = 0 ∨ a.2.1.1 ∈
            cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) := a.2.2
      refine ⟨convexComb_lt_of_lt (x := (0 : unitInterval)) (y := a.2.1.2) (M := 1 / 2)
        (by norm_num) hz.1 a.1, ?_⟩
      rcases hz.2 with h | h
      · exact Or.inl (by rw [h]; simp)
      · exact Or.inr h
    have hHcont : Continuous fun a : unitInterval ×
        ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) =>
        (a.2.1.1, Set.Icc.convexComb (0 : unitInterval) a.2.1.2 a.1) := by
      refine Continuous.prodMk ?_ ?_
      · exact continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
      · have hp : Continuous fun a : unitInterval ×
            ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) =>
            ((0 : unitInterval), (a.2.1.2, a.1)) := by fun_prop
        exact Set.Icc.continuous_convexComb_prod.comp hp
    have hHcont' : Continuous fun a : unitInterval ×
        ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) =>
        (⟨(a.2.1.1, Set.Icc.convexComb (0 : unitInterval) a.2.1.2 a.1), hHmem a⟩ :
          ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)) :=
      hHcont.subtype_mk hHmem
    refine ⟨ContinuousMap.HomotopyEquiv.mk
      ⟨fun z => z.1.1, hproj⟩
      ⟨fun x => ⟨(x, (0 : unitInterval)), h0mem x⟩, hsec⟩ ?_ ?_, ?_⟩
    · -- `invFun ∘ toFun` is homotopic to the identity
      refine ⟨ContinuousMap.Homotopy.mk
        ⟨fun a => ⟨(a.2.1.1, Set.Icc.convexComb (0 : unitInterval) a.2.1.2 a.1), hHmem a⟩,
          hHcont'⟩ ?_ ?_⟩
      · intro z
        refine Subtype.ext (Prod.ext rfl ?_)
        simp
      · intro z
        refine Subtype.ext (Prod.ext rfl ?_)
        simp
    · -- `toFun ∘ invFun` is the identity
      refine ⟨ContinuousMap.Homotopy.mk ContinuousMap.snd ?_ ?_⟩ <;> intro x <;> rfl
    · intro z
      rfl
  · -- ## Part 2: the projection `cylSet₂ → A`
    have hqmem : ∀ a : ↥(cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q),
        (a.1, qtr) ∈ cylSet₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q := by
      intro a
      show 0 < ((qtr : unitInterval) : ℝ) ∧ ((qtr : unitInterval) : ℝ) < 1 / 2 ∧
        a.1 ∈ cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q
      exact ⟨by norm_num [qtr], by norm_num [qtr], a.2⟩
    have hsec : Continuous fun a :
        ↥(cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) =>
        (⟨(a.1, qtr), hqmem a⟩ :
          ↥(cylSet₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)) :=
      Continuous.subtype_mk (continuous_subtype_val.prodMk continuous_const) hqmem
    have hproj : Continuous fun z :
        ↥(cylSet₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) =>
        (⟨z.1.1, z.2.2.2⟩ :
          ↥(cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)) :=
      Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) (fun z => z.2.2.2)
    have hHmem : ∀ a : unitInterval ×
        ↥(cylSet₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q),
        (a.2.1.1, Set.Icc.convexComb qtr a.2.1.2 a.1) ∈
          cylSet₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q := by
      intro a
      have hz : 0 < ((a.2.1.2 : unitInterval) : ℝ) ∧
          ((a.2.1.2 : unitInterval) : ℝ) < 1 / 2 ∧ a.2.1.1 ∈
            cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q := a.2.2
      exact ⟨convexComb_pos_of_pos (x := qtr) (y := a.2.1.2) (by norm_num [qtr]) hz.1 a.1,
        convexComb_lt_of_lt (x := qtr) (y := a.2.1.2) (M := 1 / 2) (by norm_num [qtr]) hz.2.1 a.1,
        hz.2.2⟩
    have hHcont : Continuous fun a : unitInterval ×
        ↥(cylSet₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) =>
        (a.2.1.1, Set.Icc.convexComb qtr a.2.1.2 a.1) := by
      refine Continuous.prodMk ?_ ?_
      · exact continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
      · have hp : Continuous fun a : unitInterval ×
            ↥(cylSet₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) =>
            (qtr, (a.2.1.2, a.1)) := by fun_prop
        exact Set.Icc.continuous_convexComb_prod.comp hp
    have hHcont' : Continuous fun a : unitInterval ×
        ↥(cylSet₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) =>
        (⟨(a.2.1.1, Set.Icc.convexComb qtr a.2.1.2 a.1), hHmem a⟩ :
          ↥(cylSet₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)) :=
      hHcont.subtype_mk hHmem
    refine ⟨ContinuousMap.HomotopyEquiv.mk
      ⟨fun z => ⟨z.1.1, z.2.2.2⟩, hproj⟩
      ⟨fun a => ⟨(a.1, qtr), hqmem a⟩, hsec⟩ ?_ ?_, ?_⟩
    · -- `invFun ∘ toFun` is homotopic to the identity
      refine ⟨ContinuousMap.Homotopy.mk
        ⟨fun a => ⟨(a.2.1.1, Set.Icc.convexComb qtr a.2.1.2 a.1), hHmem a⟩, hHcont'⟩ ?_ ?_⟩
      · intro z
        refine Subtype.ext (Prod.ext rfl ?_)
        simp
      · intro z
        refine Subtype.ext (Prod.ext rfl ?_)
        simp
    · -- `toFun ∘ invFun` is the identity
      refine ⟨ContinuousMap.Homotopy.mk ContinuousMap.snd ?_ ?_⟩ <;> intro a <;> rfl
    · intro z
      rfl

namespace Work.Serre.DiscPair

/-- The same statement as `Work.Serre.DiscPair.collarSetHomotopyEquiv`, under the (redundant)
namespace nesting used by `Work.Serre.DiscPair.subPairMapQuasiIso`; kept for compatibility. -/
theorem collarSetHomotopyEquiv (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    (∃ e : ContinuousMap.HomotopyEquiv
        ↥(cylSet₁ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) X,
      ∀ z, e.toFun z = z.1.1) ∧
    (∃ e : ContinuousMap.HomotopyEquiv
        ↥(cylSet₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)
        ↥(cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q),
      ∀ z, e.toFun z = ⟨z.1.1, z.2.2.2⟩) :=
  _root_.Work.Serre.DiscPair.collarSetHomotopyEquiv D Γ ι f q

end Work.Serre.DiscPair

end Work.Serre.DiscPair
