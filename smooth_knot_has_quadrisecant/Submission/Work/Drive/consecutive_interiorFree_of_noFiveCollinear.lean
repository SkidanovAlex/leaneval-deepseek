import Mathlib
import Submission.Work.Drive.quadrisecantSpreadDefs
import Submission.Work.Drive.quadrisecantConsecutive

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 2000000

/-- **The geometric content of `NoFiveCollinear`.**  On a knot with no five collinear points, the
consecutive sub-secants of a quadrisecant (in one of the two possible orders of the two middles) are
interior-free: a knot point strictly inside a consecutive sub-secant would be a fifth collinear knot
point, distinct from the four. -/
theorem consecutive_interiorFree_of_noFiveCollinear {r : ℝ → Space}
    (hr : IsSmoothKnot r)
    (hn5 : NoFiveCollinear r)
    {a b z w : AddCircle period}
    (hd : QuadDistinct a b z w)
    (hz : IsMiddleOnChord r a b z)
    (hw : IsMiddleOnChord r a b w) :
    (ChordInteriorFree r a z ∧ ChordInteriorFree r z w ∧ ChordInteriorFree r w b) ∨
      (ChordInteriorFree r a w ∧ ChordInteriorFree r w z ∧ ChordInteriorFree r z b) := by
  obtain ⟨hab, haz, haw, hbz, hbw, hzw⟩ := hd
  set D : Space := knotMap r b - knotMap r a with hD
  have hDne : D ≠ 0 := by
    intro h0
    have hba : knotMap r b = knotMap r a := sub_eq_zero.mp (by simpa [hD] using h0)
    exact hab (knotMap_injective hr hba).symm
  set γ : ℝ → Space := fun t => knotMap r a + t • D with hγ
  have hγinj : Function.Injective γ := by
    intro s t hst
    have h1 : s • D = t • D := add_left_cancel hst
    have h2 : (s - t) • D = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · linarith
    · exact absurd h hDne
  have hγ0 : γ 0 = knotMap r a := by simp [hγ]
  have hγ1 : γ 1 = knotMap r b := by simp only [hγ, one_smul, hD]; abel
  have hcontra : ∀ (c : Fin 5 → AddCircle period), Function.Injective c →
      (∀ i, ∃ t : ℝ, knotMap r (c i) = γ t) → False := by
    intro c hc hline
    refine hn5 ⟨c, hc, knotMap r a, D, hDne, fun i => ?_⟩
    obtain ⟨t, ht⟩ := hline i
    exact ⟨t, by rw [ht, hγ]⟩
  obtain ⟨θz, hθz, hzγ⟩ : ∃ θ : ℝ, θ ∈ Set.Ioo (0:ℝ) 1 ∧ γ θ = knotMap r z := by
    rw [IsMiddleOnChord, openSegment_eq_image'] at hz
    obtain ⟨θ, hθ, hθeq⟩ := hz
    exact ⟨θ, hθ, by simpa [hγ, hD] using hθeq⟩
  obtain ⟨θw, hθw, hwγ⟩ : ∃ θ : ℝ, θ ∈ Set.Ioo (0:ℝ) 1 ∧ γ θ = knotMap r w := by
    rw [IsMiddleOnChord, openSegment_eq_image'] at hw
    obtain ⟨θ, hθ, hθeq⟩ := hw
    exact ⟨θ, hθ, by simpa [hγ, hD] using hθeq⟩
  have hθz0 : 0 < θz := hθz.1
  have hθz1 : θz < 1 := hθz.2
  have hθw0 : 0 < θw := hθw.1
  have hθw1 : θw < 1 := hθw.2
  have hθzw : θz ≠ θw := fun h =>
    hzw (knotMap_injective hr (by rw [← hzγ, ← hwγ]; exact congrArg γ h))
  -- a knot point strictly inside a chord of the line, with a new coordinate
  have coord_mem : ∀ {P Q m : AddCircle period} {tP tQ : ℝ},
      γ tP = knotMap r P → γ tQ = knotMap r Q → IsMiddleOnOpenChord r P Q m →
      ∃ φ : ℝ, φ ∈ Set.Ioo (0:ℝ) 1 ∧ knotMap r m = γ ((1 - φ) * tP + φ * tQ) := by
    intro P Q m tP tQ hP hQ hm
    rw [IsMiddleOnOpenChord, openSegment_eq_image'] at hm
    obtain ⟨φ, hφ, hφeq⟩ := hm
    refine ⟨φ, hφ, ?_⟩
    have hsub : knotMap r Q - knotMap r P = (tQ - tP) • D := by rw [← hP, ← hQ, hγ]; module
    rw [hsub] at hφeq
    have h2 : knotMap r m = knotMap r a + (tP + φ * (tQ - tP)) • D := by
      rw [← hφeq, ← hP, hγ]
      module
    have h3 : knotMap r a + (tP + φ * (tQ - tP)) • D = γ ((1 - φ) * tP + φ * tQ) := by
      rw [hγ]; congr 1; ring
    rw [h2, h3]
  -- five collinear points from a point with a new coordinate
  have hno : ∀ (m : AddCircle period) (s : ℝ), knotMap r m = γ s →
      s ≠ 0 → s ≠ 1 → s ≠ θz → s ≠ θw → False := by
    intro m s hs h0 h1 hz' hw'
    have hcoord : ∀ i : Fin 5, knotMap r (![a, b, z, w, m] i) = γ (![0, 1, θz, θw, s] i) := by
      intro i; fin_cases i
      · simpa using hγ0.symm
      · simpa using hγ1.symm
      · simpa using hzγ.symm
      · simpa using hwγ.symm
      · simpa using hs
    refine hcontra ![a, b, z, w, m] ?_ (fun i => ⟨![0, 1, θz, θw, s] i, hcoord i⟩)
    have hcoordinj : Function.Injective ![0, 1, θz, θw, s] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    intro i j hij
    refine hcoordinj (hγinj ?_)
    rw [← hcoord i, ← hcoord j, hij]
  -- the two possible orders of the middles
  rcases middle_dichotomy hr hz hw hzw with hord | hord
  · -- `w` strictly between `a` and `z`: the order is a, w, z, b
    have hlt : θw < θz := by
      obtain ⟨φ, hφ, hφeq⟩ := coord_mem (tP := 0) (tQ := θz) hγ0 hzγ hord
      have : θw = (1 - φ) * 0 + φ * θz := hγinj (by rw [hwγ]; exact hφeq)
      nlinarith [hφ.1, hφ.2, hθz0]
    right
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      obtain ⟨φ, hφ, hφeq⟩ := coord_mem (tP := 0) (tQ := θw) hγ0 hwγ hm
      exact hno m ((1 - φ) * 0 + φ * θw) hφeq
        (by nlinarith [hφ.1, hφ.2, hθw0]) (by nlinarith [hφ.1, hφ.2, hθw1])
        (by nlinarith [hφ.1, hφ.2, hθw0]) (by nlinarith [hφ.1, hφ.2, hlt])
    · intro m hm
      obtain ⟨φ, hφ, hφeq⟩ := coord_mem (tP := θw) (tQ := θz) hwγ hzγ hm
      exact hno m ((1 - φ) * θw + φ * θz) hφeq
        (by nlinarith [hφ.1, hφ.2, hθw0]) (by nlinarith [hφ.1, hφ.2, hlt, hθz1])
        (by nlinarith [hφ.1, hφ.2, hlt]) (by nlinarith [hφ.1, hφ.2])
    · intro m hm
      obtain ⟨φ, hφ, hφeq⟩ := coord_mem (tP := θz) (tQ := 1) hzγ hγ1 hm
      exact hno m ((1 - φ) * θz + φ * 1) hφeq
        (by nlinarith [hφ.1, hφ.2, hθz0]) (by nlinarith [hφ.1, hφ.2])
        (by nlinarith [hφ.1, hφ.2, hlt]) (by nlinarith [hφ.1, hφ.2, hlt, hθz1])
  · -- `z` strictly between `a` and `w`: the order is a, z, w, b
    have hlt : θz < θw := by
      obtain ⟨φ, hφ, hφeq⟩ := coord_mem (tP := 0) (tQ := θw) hγ0 hwγ hord
      have : θz = (1 - φ) * 0 + φ * θw := hγinj (by rw [hzγ]; exact hφeq)
      nlinarith [hφ.1, hφ.2, hθw0]
    left
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      obtain ⟨φ, hφ, hφeq⟩ := coord_mem (tP := 0) (tQ := θz) hγ0 hzγ hm
      exact hno m ((1 - φ) * 0 + φ * θz) hφeq
        (by nlinarith [hφ.1, hφ.2, hθz0]) (by nlinarith [hφ.1, hφ.2, hθz1])
        (by nlinarith [hφ.1, hφ.2, hθz0]) (by nlinarith [hφ.1, hφ.2, hlt])
    · intro m hm
      obtain ⟨φ, hφ, hφeq⟩ := coord_mem (tP := θz) (tQ := θw) hzγ hwγ hm
      exact hno m ((1 - φ) * θz + φ * θw) hφeq
        (by nlinarith [hφ.1, hφ.2, hθz0]) (by nlinarith [hφ.1, hφ.2, hlt, hθw1])
        (by nlinarith [hφ.1, hφ.2]) (by nlinarith [hφ.1, hφ.2])
    · intro m hm
      obtain ⟨φ, hφ, hφeq⟩ := coord_mem (tP := θw) (tQ := 1) hwγ hγ1 hm
      exact hno m ((1 - φ) * θw + φ * 1) hφeq
        (by nlinarith [hφ.1, hφ.2, hθw0]) (by nlinarith [hφ.1, hφ.2])
        (by nlinarith [hφ.1, hφ.2, hlt, hθw1]) (by nlinarith [hφ.1, hφ.2, hlt])

end Work.Drive
