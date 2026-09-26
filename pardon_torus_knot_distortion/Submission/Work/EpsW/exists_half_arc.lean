import Mathlib
import Submission.Work.Smooth.Plane.Defs

namespace Work.EpsW

open LeanEval.KnotTheory.PardonDistortion
open Work.Smooth.Plane
open Set

/-- **The half of an injective arc issuing from an endpoint.**  Let `a j : [0,1] → ℝ³` be a
continuous injective arc and `x` one of the two endpoints `0` or `1`.  Then there are a continuous
injective arc `g : [0,1] → ℝ³` starting at `a j x` (`g 0 = a j x`), lying in `Set.range (a j)`,
whose every other point is an *interior* point of the arc, together with a *closed* set `K` avoiding
`a j x` and containing the complementary half of the arc: `Set.range (a j) ∩ Kᶜ ⊆ Set.range g`.

(Concretely, `K = a j '' [1/2,1]` if `x = 0`, and `K = a j '' [0,1/2]` if `x = 1`, and
`g s = a j (s/2)` resp. `g s = a j (1 - s/2)`.  The hypothesis `hx` is used only to know that the
complementary endpoint `a j (1-x)` is *not* in `Set.range g`.) -/
theorem exists_half_arc {n : ℕ} {a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)}
    (hinj : ∀ j : Fin n, Function.Injective (a j))
    (j : Fin n) (x : Work.Smooth.Plane.ArcInterval) (hx : (x:ℝ) = 0 ∨ (x:ℝ) = 1) :
    ∃ (g : C(Work.Smooth.Plane.ArcInterval, R3)) (K : Set R3),
      Function.Injective g ∧ g 0 = a j x ∧ IsClosed K ∧ a j x ∉ K ∧
      Set.range (a j) ∩ Kᶜ ⊆ Set.range g ∧
      (∀ s : Work.Smooth.Plane.ArcInterval, s ≠ 0 →
        g s ∈ a j '' {y : Work.Smooth.Plane.ArcInterval | (y:ℝ) ∈ Set.Ioo 0 1}) ∧
      (Set.range g ⊆ Set.range (a j)) := by
  rcases hx with hx | hx
  · -- Case `x = 0`: the outgoing half `g s = a j (s/2)`, with `K = a j '' [1/2, 1]`.
    have hx0 : x = 0 := Subtype.ext (by simpa using hx)
    have hmem : ∀ s : ArcInterval, (s:ℝ)/2 ∈ Set.Icc (0:ℝ) 1 := fun s => by
      obtain ⟨h1, h2⟩ := s.2
      exact ⟨by linarith, by linarith⟩
    have hcont : Continuous fun s : ArcInterval => (s:ℝ)/2 := by fun_prop
    let φ : C(ArcInterval, ArcInterval) := ⟨fun s => ⟨(s:ℝ)/2, hmem s⟩, hcont.subtype_mk hmem⟩
    have hφ : ∀ s : ArcInterval, ((φ s : ArcInterval) : ℝ) = (s:ℝ)/2 := fun s => rfl
    have hφinj : Function.Injective φ := fun s t h => Subtype.ext (by
      have h' := congrArg (fun z : ArcInterval => ((z : ArcInterval) : ℝ)) h
      rw [hφ s, hφ t] at h'
      linarith)
    have hφ0 : φ 0 = x := by
      apply Subtype.ext
      rw [hφ 0, hx0]
      norm_num
    refine ⟨(a j).comp φ, a j '' {y : ArcInterval | (1/2 : ℝ) ≤ (y:ℝ)},
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Function.Injective fun s : ArcInterval => a j (φ s)
      exact (hinj j).comp hφinj
    · change a j (φ 0) = a j x
      rw [hφ0]
    · exact ((isClosed_Ici.preimage continuous_subtype_val).isCompact.image
        (a j).continuous).isClosed
    · rintro ⟨y, hy, hay⟩
      have hyx : y = x := hinj j hay
      rw [hyx, hx0] at hy
      norm_num at hy
    · rintro z ⟨⟨t, rfl⟩, hz⟩
      have ht : (t:ℝ) < 1/2 := by
        by_contra h
        have h' : (1/2:ℝ) ≤ (t:ℝ) := not_lt.mp h
        exact hz ⟨t, h', rfl⟩
      let s : ArcInterval := ⟨2*(t:ℝ), by
        obtain ⟨h1, h2⟩ := t.2
        exact ⟨by linarith, by linarith⟩⟩
      have hφs : φ s = t := by
        apply Subtype.ext
        rw [hφ s]
        show 2*(t:ℝ)/2 = (t:ℝ)
        ring
      refine ⟨s, ?_⟩
      change a j (φ s) = a j t
      rw [hφs]
    · intro s hs
      have hs0 : 0 < (s:ℝ) := by
        refine lt_of_le_of_ne s.2.1 (Ne.symm ?_)
        intro h
        exact hs (Subtype.ext (by simpa using h))
      have hmem' : (φ s : ℝ) ∈ Set.Ioo 0 1 := by
        rw [hφ s]
        obtain ⟨h1, h2⟩ := s.2
        exact ⟨by linarith, by linarith⟩
      exact ⟨φ s, hmem', rfl⟩
    · rintro z ⟨s, rfl⟩
      exact ⟨φ s, rfl⟩
  · -- Case `x = 1`: the outgoing half `g s = a j (1 - s/2)`, with `K = a j '' [0, 1/2]`.
    have hx1 : x = 1 := Subtype.ext (by simpa using hx)
    have hmem : ∀ s : ArcInterval, 1 - (s:ℝ)/2 ∈ Set.Icc (0:ℝ) 1 := fun s => by
      obtain ⟨h1, h2⟩ := s.2
      exact ⟨by linarith, by linarith⟩
    have hcont : Continuous fun s : ArcInterval => 1 - (s:ℝ)/2 := by fun_prop
    let φ : C(ArcInterval, ArcInterval) :=
      ⟨fun s => ⟨1 - (s:ℝ)/2, hmem s⟩, hcont.subtype_mk hmem⟩
    have hφ : ∀ s : ArcInterval, ((φ s : ArcInterval) : ℝ) = 1 - (s:ℝ)/2 := fun s => rfl
    have hφinj : Function.Injective φ := fun s t h => Subtype.ext (by
      have h' := congrArg (fun z : ArcInterval => ((z : ArcInterval) : ℝ)) h
      rw [hφ s, hφ t] at h'
      linarith)
    have hφ0 : φ 0 = x := by
      apply Subtype.ext
      rw [hφ 0, hx1]
      norm_num
    refine ⟨(a j).comp φ, a j '' {y : ArcInterval | (y:ℝ) ≤ 1/2},
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Function.Injective fun s : ArcInterval => a j (φ s)
      exact (hinj j).comp hφinj
    · change a j (φ 0) = a j x
      rw [hφ0]
    · exact ((isClosed_Iic.preimage continuous_subtype_val).isCompact.image
        (a j).continuous).isClosed
    · rintro ⟨y, hy, hay⟩
      have hyx : y = x := hinj j hay
      rw [hyx, hx1] at hy
      norm_num at hy
    · rintro z ⟨⟨t, rfl⟩, hz⟩
      have ht : 1/2 < (t:ℝ) := by
        by_contra h
        have h' : (t:ℝ) ≤ 1/2 := not_lt.mp h
        exact hz ⟨t, h', rfl⟩
      let s : ArcInterval := ⟨2 - 2*(t:ℝ), by
        obtain ⟨h1, h2⟩ := t.2
        exact ⟨by linarith, by linarith⟩⟩
      have hφs : φ s = t := by
        apply Subtype.ext
        rw [hφ s]
        show 1 - (2 - 2*(t:ℝ))/2 = (t:ℝ)
        ring
      refine ⟨s, ?_⟩
      change a j (φ s) = a j t
      rw [hφs]
    · intro s hs
      have hs0 : 0 < (s:ℝ) := by
        refine lt_of_le_of_ne s.2.1 (Ne.symm ?_)
        intro h
        exact hs (Subtype.ext (by simpa using h))
      have hmem' : (φ s : ℝ) ∈ Set.Ioo 0 1 := by
        rw [hφ s]
        obtain ⟨h1, h2⟩ := s.2
        exact ⟨by linarith, by linarith⟩
      exact ⟨φ s, hmem', rfl⟩
    · rintro z ⟨s, rfl⟩
      exact ⟨φ s, rfl⟩

end Work.EpsW
