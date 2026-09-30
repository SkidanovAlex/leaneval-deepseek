import Mathlib
import Submission.Work.BW.closedSubAux
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Character sums on a subsemigroup of the torus

The monomial character `χ_z(y) = ∏ i, y i ^ (z i)` of the torus `G_m^N` is a monoid homomorphism
in `y`. On a subsemigroup `K` of `Tor N` (closed under `tmul`, containing `tOne N`) the characters
are linearly independent as soon as they are pairwise distinct as functions on `K` (Dedekind's
theorem); this is `char_linIndep` below, proved from scratch by the classical minimality argument.

`char_sum_at_of_vanishing` is the consequence used for the Baker–Wüstholz development: a finite
`ℂ`-linear combination of characters which vanishes on `K` and which is "compatible" with
evaluation at an arbitrary point `y` (equal characters on `K` give equal values at `y`) vanishes
at `y`. The characters occurring in the combination are grouped into classes of equal restriction
to `K`; linear independence forces the coefficient sum of each class to vanish, and compatibility
then propagates the vanishing to `y`.
-/

namespace Work.BW

open Finset

/-- The monomial character `χ_z` takes the value `1` at the identity of the torus. -/
theorem torChar_tOne {N : ℕ} (z : Fin N → ℤ) : torChar z (tOne N) = 1 := by
  simp [torChar, tOne]

/-- The character `χ_z` read as a function on the points of a subset `K` of the torus. -/
noncomputable def charOn {N : ℕ} (K : Set (Fin N → ℂ)) (z : Fin N → ℤ) :
    {k : Fin N → ℂ // k ∈ K} → ℂ := fun k => torChar z k.1

/-- Linear independence, on a subsemigroup `K` of the torus, of pairwise distinct monomial
characters: a `ℂ`-linear combination of them vanishing at every point of `K` has all coefficients
zero. (Dedekind's theorem, in the form needed here.) -/
theorem char_linIndep {N : ℕ} {K : Set (Fin N → ℂ)}
    (hKm : ∀ x ∈ K, ∀ y ∈ K, tmul x y ∈ K) (hKone : tOne N ∈ K)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → {k : Fin N → ℂ // k ∈ K} → ℂ)
    (hone : ∀ i ∈ s, f i ⟨tOne N, hKone⟩ = 1)
    (hmul : ∀ i ∈ s, ∀ a b : {k : Fin N → ℂ // k ∈ K},
      f i ⟨tmul a.1 b.1, hKm a.1 a.2 b.1 b.2⟩ = f i a * f i b)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, (∀ k, f i k = f j k) → i = j)
    (hz : ∀ k : {k : Fin N → ℂ // k ∈ K}, ∑ i ∈ s, c i * f i k = 0) :
    ∀ i ∈ s, c i = 0 := by
  classical
  have H : ∀ (s : Finset ι) (c : ι → ℂ),
      (∀ i ∈ s, f i ⟨tOne N, hKone⟩ = 1) →
      (∀ i ∈ s, ∀ a b : {k : Fin N → ℂ // k ∈ K},
        f i ⟨tmul a.1 b.1, hKm a.1 a.2 b.1 b.2⟩ = f i a * f i b) →
      (∀ i ∈ s, ∀ j ∈ s, (∀ k, f i k = f j k) → i = j) →
      (∀ k : {k : Fin N → ℂ // k ∈ K}, ∑ i ∈ s, c i * f i k = 0) → ∀ i ∈ s, c i = 0 := by
    intro s
    refine Finset.strongInductionOn s ?_
    intro s ih c hone hmul hdist hz
    by_cases hcard : 1 < s.card
    · -- at least two indices: subtract a suitable multiple of one character from the relation
      obtain ⟨i₁, hi₁, i₂, hi₂, hne⟩ := Finset.one_lt_card.mp hcard
      obtain ⟨k₀, hk₀⟩ : ∃ k : {k : Fin N → ℂ // k ∈ K}, f i₁ k ≠ f i₂ k := by
        by_contra h
        refine hne (hdist i₁ hi₁ i₂ hi₂ fun k => ?_)
        by_contra h2
        exact h ⟨k, h2⟩
      -- the difference of the relation and its `k₀`-translate is supported on `s.erase i₂`
      have hrel : ∀ k : {k : Fin N → ℂ // k ∈ K},
          ∑ i ∈ s.erase i₂, (c i * (f i k₀ - f i₂ k₀)) * f i k = 0 := by
        intro k
        have h4 : ∑ i ∈ s, (c i * (f i k₀ - f i₂ k₀)) * f i k = 0 := by
          have h1 : ∑ i ∈ s, (c i * (f i k₀ - f i₂ k₀)) * f i k
              = ∑ i ∈ s, c i * f i ⟨tmul k₀.1 k.1, hKm k₀.1 k₀.2 k.1 k.2⟩
                - ∑ i ∈ s, f i₂ k₀ * (c i * f i k) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            rw [hmul i hi k₀ k]
            ring
          rw [h1, hz ⟨tmul k₀.1 k.1, hKm k₀.1 k₀.2 k.1 k.2⟩, ← Finset.mul_sum, hz k, mul_zero,
            sub_zero]
        have h5 := Finset.sum_erase_add s (fun i => (c i * (f i k₀ - f i₂ k₀)) * f i k) hi₂
        rw [h4] at h5
        have hz0 : (c i₂ * (f i₂ k₀ - f i₂ k₀)) * f i₂ k = 0 := by ring
        rw [hz0, add_zero] at h5
        exact h5
      have hone' : ∀ i ∈ s.erase i₂, f i ⟨tOne N, hKone⟩ = 1 :=
        fun i hi => hone i (Finset.mem_of_mem_erase hi)
      have hmul' : ∀ i ∈ s.erase i₂, ∀ a b : {k : Fin N → ℂ // k ∈ K},
          f i ⟨tmul a.1 b.1, hKm a.1 a.2 b.1 b.2⟩ = f i a * f i b :=
        fun i hi => hmul i (Finset.mem_of_mem_erase hi)
      have hdist' : ∀ i ∈ s.erase i₂, ∀ j ∈ s.erase i₂, (∀ k, f i k = f j k) → i = j :=
        fun i hi j hj h => hdist i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj) h
      have hci₁ : c i₁ = 0 := by
        have h0 := ih (s.erase i₂) (Finset.erase_ssubset hi₂)
          (fun i => c i * (f i k₀ - f i₂ k₀)) hone' hmul' hdist' hrel i₁
          (Finset.mem_erase.mpr ⟨hne, hi₁⟩)
        rcases mul_eq_zero.mp h0 with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h) hk₀
      -- discard the vanishing coefficient `c i₁` as well
      have hrel₁ : ∀ k : {k : Fin N → ℂ // k ∈ K}, ∑ i ∈ s.erase i₁, c i * f i k = 0 := by
        intro k
        have h5 := Finset.sum_erase_add s (fun i => c i * f i k) hi₁
        rw [hz k] at h5
        rw [hci₁, zero_mul, add_zero] at h5
        exact h5
      have hone'' : ∀ i ∈ s.erase i₁, f i ⟨tOne N, hKone⟩ = 1 :=
        fun i hi => hone i (Finset.mem_of_mem_erase hi)
      have hmul'' : ∀ i ∈ s.erase i₁, ∀ a b : {k : Fin N → ℂ // k ∈ K},
          f i ⟨tmul a.1 b.1, hKm a.1 a.2 b.1 b.2⟩ = f i a * f i b :=
        fun i hi => hmul i (Finset.mem_of_mem_erase hi)
      have hdist'' : ∀ i ∈ s.erase i₁, ∀ j ∈ s.erase i₁, (∀ k, f i k = f j k) → i = j :=
        fun i hi j hj h => hdist i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj) h
      intro i hi
      by_cases hii : i = i₁
      · rw [hii]; exact hci₁
      · exact ih (s.erase i₁) (Finset.erase_ssubset hi₁) c hone'' hmul'' hdist'' hrel₁ i
          (Finset.mem_erase.mpr ⟨hii, hi⟩)
    · have hle : s.card ≤ 1 := Nat.le_of_not_lt hcard
      rcases Nat.eq_zero_or_pos s.card with h0 | hpos
      · intro i hi
        rw [Finset.card_eq_zero.mp h0] at hi
        simp at hi
      · have h1 : s.card = 1 := by omega
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
        have ha_mem : a ∈ s := by rw [ha]; exact Finset.mem_singleton_self a
        have hfa : f a ⟨tOne N, hKone⟩ = 1 := hone a ha_mem
        intro i hi
        rw [ha, Finset.mem_singleton] at hi
        rw [hi]
        have h := hz ⟨tOne N, hKone⟩
        rw [ha, Finset.sum_singleton, hfa, mul_one] at h
        exact h
  exact H s c hone hmul hdist hz

/-- **Character sums propagate from a subsemigroup to any compatible point.** If a finite
`ℂ`-linear combination of monomial characters vanishes on the subsemigroup `K ⊆ Tor N`, and if
characters that agree on `K` also agree at `y`, then the combination vanishes at `y`. -/
theorem char_sum_at_of_vanishing {N : ℕ} {K : Set (Fin N → ℂ)}
    (hKm : ∀ x ∈ K, ∀ y ∈ K, tmul x y ∈ K) (hKone : tOne N ∈ K) (hKtor : K ⊆ Tor N)
    {ι : Type*} (s : Finset ι) (S : ι → ℂ) (w : ι → Fin N → ℤ) (y : Fin N → ℂ)
    (hzero : ∀ k ∈ K, ∑ i ∈ s, S i * torChar (w i) k = 0)
    (hcompat : ∀ i ∈ s, ∀ j ∈ s, (∀ k ∈ K, torChar (w i) k = torChar (w j) k) →
      torChar (w i) y = torChar (w j) y) :
    ∑ i ∈ s, S i * torChar (w i) y = 0 := by
  classical
  have _ := hKtor
  let φ : ι → {k : Fin N → ℂ // k ∈ K} → ℂ := fun i => charOn K (w i)
  have hmaps : ∀ i ∈ s, φ i ∈ s.image φ := fun i hi => Finset.mem_image_of_mem φ hi
  -- the coefficient of each class of characters vanishes
  have hrel : ∀ g ∈ s.image φ,
      (∑ i ∈ s.filter (fun i => φ i = g), S i) = 0 := by
    have hone : ∀ g ∈ s.image φ, g ⟨tOne N, hKone⟩ = 1 := by
      intro g hg
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hg
      simp only [φ, charOn]
      exact torChar_tOne (w i)
    have hmul : ∀ g ∈ s.image φ, ∀ a b : {k : Fin N → ℂ // k ∈ K},
        g ⟨tmul a.1 b.1, hKm a.1 a.2 b.1 b.2⟩ = g a * g b := by
      intro g hg a b
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hg
      simp only [φ, charOn]
      exact torChar_tmul (w i) a.1 b.1
    have hdist : ∀ g ∈ s.image φ, ∀ g' ∈ s.image φ, (∀ k, g k = g' k) → g = g' :=
      fun g _ g' _ h => funext h
    have hz : ∀ k : {k : Fin N → ℂ // k ∈ K},
        ∑ g ∈ s.image φ, (∑ i ∈ s.filter (fun i => φ i = g), S i) * g k = 0 := by
      intro k
      have h1 : ∑ g ∈ s.image φ, (∑ i ∈ s.filter (fun i => φ i = g), S i) * g k
          = ∑ g ∈ s.image φ, ∑ i ∈ s.filter (fun i => φ i = g), S i * φ i k := by
        apply Finset.sum_congr rfl
        intro g hg
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [← hi.2]
      rw [h1, Finset.sum_fiberwise_of_maps_to hmaps (fun i => S i * φ i k)]
      simp only [φ, charOn]
      exact hzero k.1 k.2
    exact char_linIndep hKm hKone (s.image φ)
      (fun g => ∑ i ∈ s.filter (fun i => φ i = g), S i) (fun g => g) hone hmul hdist hz
  -- evaluate at `y` and sum the (vanishing) class coefficients
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun i => S i * torChar (w i) y)]
  refine Finset.sum_eq_zero fun g hg => ?_
  by_cases hemp : (s.filter (fun i => φ i = g)).Nonempty
  · obtain ⟨i₀, hi₀⟩ := hemp
    rw [Finset.mem_filter] at hi₀
    have hconst : ∀ i ∈ s.filter (fun i => φ i = g), S i * torChar (w i) y
        = S i * torChar (w i₀) y := by
      intro i hi
      rw [Finset.mem_filter] at hi
      have hchars : ∀ k ∈ K, torChar (w i) k = torChar (w i₀) k := fun k hk => by
        have h2 : φ i ⟨k, hk⟩ = φ i₀ ⟨k, hk⟩ := by rw [hi.2, hi₀.2]
        simp only [φ, charOn] at h2
        exact h2
      rw [hcompat i hi.1 i₀ hi₀.1 hchars]
    rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul]
    have hAg : (∑ i ∈ s.filter (fun i => φ i = g), S i) = 0 := hrel g hg
    rw [hAg, zero_mul]
  · rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty]

end Work.BW
