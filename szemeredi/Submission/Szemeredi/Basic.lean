import Mathlib

open scoped BigOperators
open Filter Finset

namespace Szemeredi

/-- `A` contains a `k`-term arithmetic progression `a, a+b, ..., a+(k-1)b` with `1 ≤ b`. -/
def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ A

theorem HasAP.mono {A B : Set ℕ} (hAB : A ⊆ B) {k : ℕ} (h : HasAP A k) : HasAP B k := by
  rcases h with ⟨a, b, hb, hmem⟩
  exact ⟨a, b, hb, fun j hj => hAB (hmem j hj)⟩

/-- The elements of `A` strictly below `N`. -/
noncomputable def slice (A : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun k => k ∈ A

lemma mem_slice {A : Set ℕ} {N x : ℕ} : x ∈ slice A N ↔ x < N ∧ x ∈ A := by
  classical
  simp [slice]

lemma slice_subset_range (A : Set ℕ) (N : ℕ) : slice A N ⊆ Finset.range N := by
  intro x hx
  exact Finset.mem_range.mpr (mem_slice.mp hx).1

lemma slice_subset (A : Set ℕ) (N : ℕ) : ((slice A N : Finset ℕ) : Set ℕ) ⊆ A := by
  intro x hx
  have hx' : x ∈ slice A N := by simpa using hx
  exact (mem_slice.mp hx').2

/-- Cardinality of `A ∩ {0, ..., n}`. -/
noncomputable def countUpTo (A : Set ℕ) (n : ℕ) : ℕ := (slice A (n + 1)).card

/-- The density `|A ∩ {0,…,n}| / (n+1)`. -/
noncomputable def density (A : Set ℕ) (n : ℕ) : ℝ := (countUpTo A n : ℝ) / (n + 1)

/-- The same count, written as a real sum of the indicator (the shape used in `upperDensity`). -/
noncomputable def countInd (A : Set ℕ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), A.indicator (fun _ => (1 : ℝ)) k

lemma countInd_eq_countUpTo (A : Set ℕ) (n : ℕ) : countInd A n = (countUpTo A n : ℝ) := by
  classical
  unfold countUpTo slice countInd
  rw [Finset.sum_indicator_eq_sum_filter (s := Finset.range (n + 1))
    (f := fun _ (_ : ℕ) => (1 : ℝ)) (t := fun _ => A) (g := fun k => k)]
  simp [Finset.sum_const, nsmul_eq_mul]

lemma density_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ density A n := by
  unfold density countUpTo
  positivity

lemma density_le_one (A : Set ℕ) (n : ℕ) : density A n ≤ 1 := by
  unfold density countUpTo
  have hle : (slice A (n + 1)).card ≤ n + 1 := by
    simpa using (Finset.card_le_card (slice_subset_range A (n + 1)))
  have hle' : ((slice A (n + 1)).card : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast hle
  exact div_le_one_of_le₀ hle' (by positivity)

/-- Finite version of Szemerédi's theorem, as a predicate on `k` and density `δ`. -/
def FiniteSzemeredi (k : ℕ) (δ : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℕ, A ⊆ Finset.range N →
    δ * (N : ℝ) ≤ (A.card : ℝ) → HasAP (A : Set ℕ) k

/-- Positive `limsup` of the initial-segment densities. -/
def PositiveUpperDensity (A : Set ℕ) : Prop :=
  0 < Filter.limsup (density A) Filter.atTop

/-- Density form of Szemerédi's theorem (for one length `k`) from the finite form (for that `k`). -/
theorem ap_of_finite {k : ℕ}
    (hfin : ∀ δ : ℝ, 0 < δ → FiniteSzemeredi k δ)
    {A : Set ℕ} (hd : PositiveUpperDensity A) : HasAP A k := by
  let f : ℕ → ℝ := density A
  let L : ℝ := Filter.limsup f Filter.atTop
  have hL : 0 < L := hd
  let c : ℝ := L / 2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hcL : c < L := by
    dsimp [c]
    linarith
  have hbddBelow : (atTop : Filter ℕ).IsCoboundedUnder (· ≤ ·) f := by
    dsimp [f]
    exact Filter.isCoboundedUnder_le_of_le Filter.atTop (density_nonneg A)
  have hfreq : ∃ᶠ n in atTop, c < f n :=
    Filter.frequently_lt_of_lt_limsup (u := f) (b := c) hbddBelow hcL
  obtain ⟨N₀, hN₀⟩ := hfin c hc
  have hcofinal : ∀ m : ℕ, ∃ n ≥ m, c < f n := by
    intro m
    exact (Filter.frequently_atTop.mp hfreq) m
  obtain ⟨n, hn, hfn⟩ := hcofinal N₀
  let N : ℕ := n + 1
  let AN : Finset ℕ := slice A N
  have hNge : N₀ ≤ N := by
    dsimp [N]
    omega
  have hsub : AN ⊆ Finset.range N := slice_subset_range A N
  have hdens : c * (N : ℝ) ≤ (AN.card : ℝ) := by
    have hNpos : 0 < (N : ℝ) := by
      dsimp [N]
      positivity
    have hfn' : c < (AN.card : ℝ) / (N : ℝ) := by
      simpa [f, density, countUpTo, N, AN] using hfn
    have hmul := mul_lt_mul_of_pos_right hfn' hNpos
    have hdiv : (AN.card : ℝ) / (N : ℝ) * (N : ℝ) = (AN.card : ℝ) := by
      field_simp [hNpos.ne']
    have : c * (N : ℝ) < (AN.card : ℝ) := by
      rwa [hdiv] at hmul
    exact le_of_lt this
  exact HasAP.mono (slice_subset A N) (hN₀ N hNge AN hsub hdens)

/-- Density form of Szemerédi's theorem (for every length) from the finite form. -/
theorem infinite_ap_of_finite
    (hfin : ∀ (k : ℕ) (δ : ℝ), 0 < δ → FiniteSzemeredi k δ)
    {A : Set ℕ} (hd : PositiveUpperDensity A) :
    ∀ k : ℕ, HasAP A k := by
  intro k
  exact ap_of_finite (k := k) (hfin := hfin k) hd

/-- Trivial case `k = 0`: every set contains an AP of length `0`. -/
theorem hasAP_zero (A : Set ℕ) : HasAP A 0 := by
  refine ⟨0, 1, by norm_num, ?_⟩
  intro j hj
  omega

/-- Trivial case `k = 1`: a nonempty set contains an AP of length `1`. -/
theorem hasAP_one {A : Set ℕ} (hne : A.Nonempty) : HasAP A 1 := by
  rcases hne with ⟨a, ha⟩
  refine ⟨a, 1, by norm_num, ?_⟩
  intro j hj
  have hj0 : j = 0 := by omega
  simpa [hj0] using ha

end Szemeredi
