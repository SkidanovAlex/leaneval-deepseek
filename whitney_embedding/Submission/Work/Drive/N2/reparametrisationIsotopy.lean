import Mathlib
import Submission.Work.Drive.Morse

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology

/-- Periodicity of `u` propagates to shifts by integral multiples of the period:
`u (z + n * 2π) = u z`. -/
private lemma up_u (u : ℝ → ℝ) (huper : ∀ x : ℝ, u (x + 2 * Real.pi) = u x) :
    ∀ (n : ℕ) (z : ℝ), u (z + (n : ℝ) * (2 * Real.pi)) = u z := by
  intro n
  induction n with
  | zero => intro z; simp
  | succ n ih =>
    intro z
    have hz : z + (↑(n.succ) : ℝ) * (2 * Real.pi)
        = (z + (n : ℝ) * (2 * Real.pi)) + 2 * Real.pi := by
      push_cast; ring
    rw [hz, huper]
    exact ih z

/-- The downwards version of `up_u`: `u (z - n * 2π) = u z`. -/
private lemma down_u (u : ℝ → ℝ) (huper : ∀ x : ℝ, u (x + 2 * Real.pi) = u x) :
    ∀ (n : ℕ) (z : ℝ), u (z + (-(n : ℝ)) * (2 * Real.pi)) = u z := by
  intro n
  induction n with
  | zero => intro z; simp
  | succ n ih =>
    intro z
    have hz : z + (-(↑(n.succ) : ℝ)) * (2 * Real.pi)
        = (z + (-(↑n : ℝ)) * (2 * Real.pi)) - 2 * Real.pi := by
      push_cast; ring
    have hper : u ((z + (-(↑n : ℝ)) * (2 * Real.pi)) - 2 * Real.pi)
        = u (z + (-(↑n : ℝ)) * (2 * Real.pi)) := by
      have h := huper ((z + (-(↑n : ℝ)) * (2 * Real.pi)) - 2 * Real.pi)
      have hT_add : ((z + (-(↑n : ℝ)) * (2 * Real.pi)) - 2 * Real.pi) + 2 * Real.pi
          = z + (-(↑n : ℝ)) * (2 * Real.pi) := by ring
      rw [hT_add] at h
      exact h.symm
    rw [hz, hper]
    exact ih z

/-- Periodicity of `u` along integral multiples of the period. -/
private lemma int_u (u : ℝ → ℝ) (huper : ∀ x : ℝ, u (x + 2 * Real.pi) = u x)
    (k : ℤ) (z : ℝ) : u (z + (k : ℝ) * (2 * Real.pi)) = u z := by
  rcases Int.eq_nat_or_neg k with ⟨n, h | h⟩
  · subst h
    simpa using up_u u huper n z
  · subst h
    rw [Int.cast_neg, Int.cast_natCast]
    exact down_u u huper n z

/-- The lift `z ↦ z + s * u z` commutes with translation by `n` periods. -/
private lemma shift_up (u : ℝ → ℝ) (huper : ∀ x : ℝ, u (x + 2 * Real.pi) = u x) (s : ℝ)
    (n : ℕ) (z : ℝ) :
    (z + (n : ℝ) * (2 * Real.pi)) + s * u (z + (n : ℝ) * (2 * Real.pi))
      = (z + s * u z) + (n : ℝ) * (2 * Real.pi) := by
  rw [up_u u huper n z]; ring

/-- The downwards version of `shift_up`. -/
private lemma shift_down (u : ℝ → ℝ) (huper : ∀ x : ℝ, u (x + 2 * Real.pi) = u x) (s : ℝ)
    (n : ℕ) (z : ℝ) :
    (z + (-(n : ℝ)) * (2 * Real.pi)) + s * u (z + (-(n : ℝ)) * (2 * Real.pi))
      = (z + s * u z) + (-(n : ℝ)) * (2 * Real.pi) := by
  rw [down_u u huper n z]; ring

/-- The lift commutes with translation by an arbitrary integral number of periods. -/
private lemma shift_int (u : ℝ → ℝ) (huper : ∀ x : ℝ, u (x + 2 * Real.pi) = u x) (s : ℝ)
    (k : ℤ) (z : ℝ) :
    (z + (k : ℝ) * (2 * Real.pi)) + s * u (z + (k : ℝ) * (2 * Real.pi))
      = (z + s * u z) + (k : ℝ) * (2 * Real.pi) := by
  rw [int_u u huper k z]; ring

/-- A continuous function `ℝ → ℝ` which is strictly increasing and periodic-homogeneous
(`u z` periodic of period `2π`) has all its lifts `z ↦ z + s * u z` surjective: the lift is
unbounded above and below along the period, and the intermediate value theorem finishes. -/
private lemma surj_periodic_mono (u : ℝ → ℝ) (hu : Continuous u)
    (huper : ∀ x : ℝ, u (x + 2 * Real.pi) = u x) (s : ℝ)
    (hmono : StrictMono (fun x : ℝ => x + s * u x)) :
    Function.Surjective (fun x : ℝ => x + s * u x) := by
  have hcont : Continuous (fun x : ℝ => x + s * u x) :=
    continuous_id.add (continuous_const.mul hu)
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  refine hcont.surjective ?_ ?_
  · refine Monotone.tendsto_atTop_atTop hmono.monotone ?_
    intro b
    obtain ⟨n, hn⟩ := exists_nat_ge ((b - (0 + s * u 0)) / (2 * Real.pi))
    refine ⟨(n : ℝ) * (2 * Real.pi), ?_⟩
    have h1 : b - (0 + s * u 0) ≤ (n : ℝ) * (2 * Real.pi) := (div_le_iff₀ hT).mp hn
    have h2 := shift_up u huper s n 0
    simp only [zero_add] at h2
    linarith
  · refine Monotone.tendsto_atBot_atBot hmono.monotone ?_
    intro b
    obtain ⟨n, hn⟩ := exists_nat_ge (((0 + s * u 0) - b) / (2 * Real.pi))
    refine ⟨(-(n : ℝ)) * (2 * Real.pi), ?_⟩
    have h1 : (0 + s * u 0) - b ≤ (n : ℝ) * (2 * Real.pi) := (div_le_iff₀ hT).mp hn
    have h2 := shift_down u huper s n 0
    simp only [zero_add] at h2
    linarith

open scoped Manifold ContDiff Topology in
/-- **Reparametrisation isotopy of a picture (item (2) of the lead's plan).**

`c : ℝ → ℝ³` is a smooth `2π`-periodic *picture* (an embedding of the circle: equal images imply
congruence mod the period, `hcper`), and `u : ℝ → ℝ` is a smooth `2π`-periodic function.  Assume the
"lifts" `ψ_s x = x + s * u x` are strictly increasing for every `s ∈ [0,1]` (`hmono`; with the
periodicity `huper` each `ψ_s` is then a diffeo of the period).  Then the reparametrisations
`(s, x) ↦ c (x + s * u x)` form a smooth isotopy of pictures:

* the family is jointly `C^∞` on `ℝ × ℝ`;
* every time slice is an embedding of the circle: it is injective modulo the period, and each `ψ_s` is
  onto (`hsurj`, a consequence of `ψ_s (x + 2πk) = ψ_s x + 2πk → ±∞` and the intermediate value
  theorem, so that the slices are honest reparametrisations and not just injections);
* the slice at `s = 0` is the original picture.

This is the "lift `x + s·u(x)`" tool of the collar construction: it moves a picture through
reparametrisations without changing its image knot, so it can be used to match the parking
parametrisation `θ_i` on a flat collar. -/
theorem reparametrisationIsotopy (c : ℝ → EuclideanSpace ℝ (Fin 3)) (u : ℝ → ℝ)
    (hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ c)
    (hper : ∀ x : ℝ, c (x + 2 * Real.pi) = c x)
    (hcper : ∀ x y : ℝ, c x = c y → ∃ k : ℤ, y = x + k * (2 * Real.pi))
    (hu : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ u)
    (huper : ∀ x : ℝ, u (x + 2 * Real.pi) = u x)
    (hmono : ∀ s ∈ Set.Icc (0 : ℝ) 1, StrictMono (fun x : ℝ => x + s * u x)) :
    (ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun p : ℝ × ℝ => c (p.2 + p.1 * u p.2))) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x y : ℝ,
        c (x + s * u x) = c (y + s * u y) → ∃ k : ℤ, y = x + k * (2 * Real.pi)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y : ℝ, ∃ x : ℝ, y = x + s * u x) ∧
      (∀ x : ℝ, c (x + 0 * u x) = c x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- joint smoothness: compose the smooth inner map with `c`
    have h1 : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × ℝ => p.1) :=
      contMDiff_fst
    have h2 : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × ℝ => p.2) :=
      contMDiff_snd
    have h3 : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × ℝ => u p.2) :=
      hu.comp h2
    have hF : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × ℝ => p.2 + p.1 * u p.2) := h2.add (h1.mul h3)
    exact hc.comp hF
  · -- injectivity modulo the period of each slice
    intro s hs x y hxy
    obtain ⟨k, hk⟩ := hcper (x + s * u x) (y + s * u y) hxy
    refine ⟨k, ?_⟩
    have hshift := shift_int u huper s k x
    have heq : (fun z : ℝ => z + s * u z) y
        = (fun z : ℝ => z + s * u z) (x + (k : ℝ) * (2 * Real.pi)) := by
      change y + s * u y = (x + (k : ℝ) * (2 * Real.pi)) + s * u (x + (k : ℝ) * (2 * Real.pi))
      rw [hk, hshift]
    exact (hmono s hs).injective heq
  · -- surjectivity of each lift
    intro s hs y
    obtain ⟨x, hx⟩ := surj_periodic_mono u hu.continuous huper s (hmono s hs) y
    exact ⟨x, hx.symm⟩
  · -- the slice at `s = 0` is the original picture
    intro x
    simp

end Work.Drive.N2
