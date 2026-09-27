import Mathlib

namespace Work.Drive.PushDisc

/-- **The two bigon arcs are `f`-injective** (the rows `hγ₁injf`, `hγ₂injf` that
`Work.Drive.Whitney.whitneyDiscSmooth` consumes), derived from the target's configuration:
`f` is injective on the clean region `W` up to the four double points (`hclean`), the two arcs lie in
`W` (`hγW₁`, `hγW₂`), are injective on `[0,1]` (`hγ₁inj`, `hγ₂inj`), meet only at their endpoints
(`hγdisj`), and the two double points are distinct (`hp₁p₂`, `hq₁q₂`).

Proof sketch.  Suppose `f (γ₁ s) = f (γ₁ t)` with `s, t ∈ [0,1]`.  `hclean` gives `γ₁ s = γ₁ t`
(hence `s = t`) or one of the four double-point pairings; each pairing forces the corresponding
parameter to be `0` or `1`, and `hγdisj` (together with `hγ₁0`, `hγ₁1`, `hγ₂0`, `hγ₂1`) then forces
both parameters to be the same endpoint.  The same argument with the roles of the arcs swapped (using
`hγdisj` in the reversed slot) gives `hγ₂injf`. -/
theorem arcInjOnOfHclean {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M)
    (p₁ p₂ q₁ q₂ : M) (γ₁ γ₂ : ℝ → M)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁)) :
    Set.InjOn (fun s : ℝ => f (γ₁ s)) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (fun s : ℝ => f (γ₂ s)) (Set.Icc (0 : ℝ) 1) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, le_refl _⟩
  -- Each of the four double points pins the corresponding parameter to an endpoint of `[0,1]`.
  have z₁ : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → γ₁ s = p₁ → s = 0 :=
    fun s hs h => hγ₁inj hs h0 (by rw [h, hγ₁0])
  have o₁ : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → γ₁ s = q₁ → s = 1 :=
    fun s hs h => hγ₁inj hs h1 (by rw [h, hγ₁1])
  have z₂ : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → γ₁ s = p₂ → s = 0 := by
    intro s hs h
    rcases hγdisj s hs 0 h0 (by rw [h, hγ₂0]) with ⟨e, _⟩ | ⟨e, bad⟩
    · exact e
    · exact absurd bad zero_ne_one
  have o₂ : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → γ₁ s = q₂ → s = 1 := by
    intro s hs h
    rcases hγdisj s hs 1 h1 (by rw [h, hγ₂1]) with ⟨e, bad⟩ | ⟨e, _⟩
    · exact absurd bad one_ne_zero
    · exact e
  have z₁' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → γ₂ s = p₁ → s = 0 := by
    intro s hs h
    rcases hγdisj 0 h0 s hs (by rw [hγ₁0, h]) with ⟨_, e⟩ | ⟨bad, e⟩
    · exact e
    · exact absurd bad zero_ne_one
  have o₁' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → γ₂ s = q₁ → s = 1 := by
    intro s hs h
    rcases hγdisj 1 h1 s hs (by rw [hγ₁1, h]) with ⟨bad, e⟩ | ⟨_, e⟩
    · exact absurd bad one_ne_zero
    · exact e
  have z₂' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → γ₂ s = p₂ → s = 0 :=
    fun s hs h => hγ₂inj hs h0 (by rw [h, hγ₂0])
  have o₂' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → γ₂ s = q₂ → s = 1 :=
    fun s hs h => hγ₂inj hs h1 (by rw [h, hγ₂1])
  refine ⟨?_, ?_⟩
  · intro s hs t ht h
    rcases hclean (γ₁ s) (γ₁ t) (hγW₁ s hs) (hγW₁ t ht) h with
      hh | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact hγ₁inj hs ht hh
    · rw [z₁ s hs a, z₂ t ht b]
    · rw [z₂ s hs a, z₁ t ht b]
    · rw [o₁ s hs a, o₂ t ht b]
    · rw [o₂ s hs a, o₁ t ht b]
  · intro s hs t ht h
    rcases hclean (γ₂ s) (γ₂ t) (hγW₂ s hs) (hγW₂ t ht) h with
      hh | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact hγ₂inj hs ht hh
    · rw [z₁' s hs a, z₂' t ht b]
    · rw [z₂' s hs a, z₁' t ht b]
    · rw [o₁' s hs a, o₂' t ht b]
    · rw [o₂' s hs a, o₁' t ht b]

end Work.Drive.PushDisc
