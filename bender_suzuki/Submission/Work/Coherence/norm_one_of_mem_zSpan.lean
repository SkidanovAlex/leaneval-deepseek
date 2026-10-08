import Mathlib
import Submission.Work.Coherence.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A vector of norm one in `ℤ[S]` (for `S` orthonormal) is `±χ`

If `S` is an orthonormal finite set of complex valued functions on a finite group and
`f ∈ ℤ[S]` satisfies `⟨f, f⟩ = 1`, then `f = χ` or `f = -χ` for some `χ ∈ S`.

The proof is the observation that, writing `f = ∑_{x ∈ S} c_x x` with `c_x ∈ ℤ`, the norm
formula `cfInner_self_eq_sum_sq` gives `∑_x c_x^2 = 1`; a sum of squares of integers equal to
one has exactly one nonzero term, which must be `±1`.
-/

noncomputable section

open Classical

namespace Work.Coherence

universe u

variable {G : Type*}

section

variable [Group G] [Fintype G]

/-- A family of integers whose sum of squares is `1` has exactly one nonzero entry, which is
`±1`. -/
theorem sum_sq_eq_one_int {ι : Type*} [Fintype ι] (c : ι → ℤ)
    (h : ∑ i, c i ^ 2 = 1) :
    ∃ i₀, (c i₀ = 1 ∨ c i₀ = -1) ∧ ∀ i, i ≠ i₀ → c i = 0 := by
  classical
  -- some coefficient is nonzero
  have hex : ∃ i, c i ≠ 0 := by
    by_contra hcon
    have h0 : ∑ i, c i ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have : c i = 0 := by
        by_contra hci
        exact hcon ⟨i, hci⟩
      simp [this]
    omega
  obtain ⟨i₀, hi₀⟩ := hex
  -- and then it is `±1`
  have hle : c i₀ ^ 2 ≤ 1 := by
    have h1 : c i₀ ^ 2 ≤ ∑ i, c i ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (c i)) (Finset.mem_univ i₀)
    rwa [h] at h1
  have hge : 1 ≤ c i₀ ^ 2 := by
    have hpos := sq_pos_of_ne_zero hi₀
    omega
  have heq : c i₀ ^ 2 = 1 := le_antisymm hle hge
  have hunit : c i₀ = 1 ∨ c i₀ = -1 := sq_eq_one_iff.mp heq
  refine ⟨i₀, hunit, ?_⟩
  -- all the other coefficients vanish because the remaining sum of squares is `0`
  intro i hi
  have herase : ∑ j ∈ Finset.univ.erase i₀, c j ^ 2 = 0 := by
    have hsplit := Finset.sum_erase_add (s := Finset.univ) (f := fun j => c j ^ 2)
      (Finset.mem_univ i₀)
    rw [h, heq] at hsplit
    omega
  have hz : c i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j))).mp herase i
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  exact sq_eq_zero_iff.mp hz

/-- **A unit vector of `ℤ[S]`.**  If `S` is orthonormal and `f ∈ ℤ[S]` has `⟨f, f⟩ = 1`, then
`f` is one of the elements of `S` up to sign. -/
theorem norm_one_of_mem_zSpan {G : Type*} [Group G] [Fintype G] {S : Finset (G → ℂ)}
    (hS : Orthonormal S) {f : G → ℂ} (hf : f ∈ ZSpan S) (h : cfInner f f = 1) :
    ∃ χ ∈ S, f = χ ∨ f = -χ := by
  classical
  obtain ⟨c, hc⟩ := mem_zSpan.mp hf
  -- the norm formula turns `⟨f, f⟩ = 1` into `∑ c_x^2 = 1` over the integers
  have hsumC : ∑ x : S, ((c x : ℤ) : ℂ) ^ 2 = 1 := by
    rw [← cfInner_self_eq_sum_sq hS hc]
    exact h
  have hs : ∑ x : S, (c x) ^ 2 = 1 := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    exact hsumC
  obtain ⟨i₀, hunit, hzero⟩ := sum_sq_eq_one_int c hs
  -- so `f` is (up to sign) the single basis vector `i₀`
  have hfval : f = (c i₀ : ℂ) • (i₀ : G → ℂ) := by
    rw [hc, Finset.sum_eq_single i₀]
    · intro b _ hb
      simp [hzero b hb]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  refine ⟨(i₀ : G → ℂ), i₀.2, ?_⟩
  rcases hunit with h1 | h1
  · left; rw [hfval, h1]; simp
  · right; rw [hfval, h1]; simp

end

end Work.Coherence
