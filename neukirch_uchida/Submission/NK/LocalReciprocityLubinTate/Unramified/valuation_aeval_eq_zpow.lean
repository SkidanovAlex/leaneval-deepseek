import Mathlib

set_option linter.unusedVariables false

namespace NK.LocalReciprocityLubinTate.Unramified

/-- **The "ord" computation for a polynomial in a uniformiser.**

Let `w : Valuation S ℤᵐ⁰` be a valuation on a field `S`, `y ∈ S` non-zero with `w y < 1`,
`π ∈ S` with `w π = w y ^ D` for some `D ≥ 1`, and `g ∈ S[X]` non-zero of degree `< D`.  Suppose
that for every `i` in the support of `g` the coefficient `g.coeff i` has `w`-value a `ℤ`-power of
`w π`, and record the exponents in a function `K : ℕ → ℤ` (i.e. `w (g.coeff i) = (w π) ^ (K i)` for
`i ∈ g.support`).  Then `w ((aeval y) g)` is itself a `ℤ`-power of `w y`,
`w ((aeval y) g) = (w y) ^ m`, and the exponent is computed by the minimum of `i ↦ D * K i + i` on
the support: there is `i₀ ∈ g.support` with `m = D * K i₀ + i₀` and `m ≤ D * K i + i` for every
`i ∈ g.support`.

PROOF ROUTE.  `Polynomial.aeval_eq_sum_range` writes `(aeval y) g = Σ_{i ≤ g.natDegree} (g.coeff i)
• y ^ i`, a sum over `Finset.range (g.natDegree + 1)`.  With `β := w y`,
`γ := w π = β ^ D`, the `i`-th term has value
`w (g.coeff i) · β ^ i = γ ^ (K i) · β ^ i = β ^ (D * K i + i)` (for `i ∈ g.support`, and `0` for
`i ∉ g.support`, since the coefficient vanishes).  The map `i ↦ D * K i + i` is injective on the
support: if `D * K i + i = D * K j + j` with `i ≠ j` then `D ∣ |j - i|` while
`0 < |j - i| ≤ g.natDegree < D`.  So the minimum of `i ↦ D * K i + i` over the support is attained
at a unique index `i₀`, all other terms have strictly smaller `w`-value (because `β < 1` and
`n ↦ β ^ n` is strictly antitone, `zpow_right_strictAnti`), and
`Valuation.map_sum_eq_of_lt` (whose hypothesis is `w (f i) < w (f i₀)`) gives the claim. -/
theorem valuation_aeval_eq_zpow {S : Type*} [Field S] (w : Valuation S (WithZero (Multiplicative ℤ)))
    (y π : S) (D : ℕ) (hD : 1 ≤ D) (hy1 : w y < 1) (hy0 : y ≠ 0) (hπ : w π = w y ^ D)
    (g : Polynomial S) (hg0 : g ≠ 0) (hgdeg : g.natDegree < D) (K : ℕ → ℤ)
    (hK : ∀ i ∈ g.support, w (g.coeff i) = (w π) ^ (K i)) :
    ∃ m : ℤ, w ((Polynomial.aeval y) g) = w y ^ m ∧ ∃ i₀ ∈ g.support,
      m = (D : ℤ) * K i₀ + (i₀ : ℤ) ∧ ∀ i ∈ g.support, m ≤ (D : ℤ) * K i + (i : ℤ) := by
  classical
  -- `w y` is nonzero and `0 < w y`, since `y ≠ 0`.
  have hyne : w y ≠ 0 := by rwa [Valuation.ne_zero_iff]
  have hβ0 : 0 < w y := zero_lt_iff.mpr hyne
  -- `hπ` in `ℤ`-power form.
  have hπz : w π = (w y) ^ (D : ℤ) := by rw [hπ, zpow_natCast]
  -- the support is nonempty.
  have hne : g.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Polynomial.support_eq_empty]
    exact hg0
  -- the index attaining the minimum of `i ↦ D * K i + i` on the support.
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image g.support (fun i => (D:ℤ) * K i + (i:ℤ)) hne
  have hle_nat : ∀ i ∈ g.support, i ≤ g.natDegree :=
    fun i hi => Polynomial.le_natDegree_of_mem_supp i hi
  -- injectivity of `i ↦ D * K i + i` on the support.
  have hinj : ∀ i ∈ g.support, ∀ j ∈ g.support,
      (D:ℤ) * K i + (i:ℤ) = (D:ℤ) * K j + (j:ℤ) → i = j := by
    intro i hi j hj heq
    by_contra hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · -- `i < j`: then `D ∣ (j - i)` while `0 < j - i ≤ natDegree < D`.
      have hdivZ : (D:ℤ) ∣ ((j:ℤ) - (i:ℤ)) := ⟨K i - K j, by linarith⟩
      have hsub : ((j - i : ℕ) : ℤ) = (j:ℤ) - (i:ℤ) := Int.natCast_sub (le_of_lt hlt)
      rw [← hsub] at hdivZ
      have hdvd : D ∣ (j - i) := Int.ofNat_dvd.mp hdivZ
      have hpos : 0 < j - i := Nat.sub_pos_of_lt hlt
      have hle : j - i ≤ g.natDegree := by
        have h1 := hle_nat i hi; have h2 := hle_nat j hj; omega
      have := Nat.le_of_dvd hpos hdvd
      omega
    · -- `j < i`: symmetric.
      have hdivZ : (D:ℤ) ∣ ((i:ℤ) - (j:ℤ)) := ⟨K j - K i, by linarith⟩
      have hsub : ((i - j : ℕ) : ℤ) = (i:ℤ) - (j:ℤ) := Int.natCast_sub (le_of_lt hlt)
      rw [← hsub] at hdivZ
      have hdvd : D ∣ (i - j) := Int.ofNat_dvd.mp hdivZ
      have hpos : 0 < i - j := Nat.sub_pos_of_lt hlt
      have hle : i - j ≤ g.natDegree := by
        have h1 := hle_nat i hi; have h2 := hle_nat j hj; omega
      have := Nat.le_of_dvd hpos hdvd
      omega
  let f : ℕ → S := fun i => g.coeff i * y ^ i
  have hpow : ∀ i : ℕ, w (y ^ i) = (w y) ^ (i : ℤ) := by
    intro i; rw [Valuation.map_pow, zpow_natCast]
  -- the value of the `i`-th term, for `i` in the support.
  have hterm : ∀ i ∈ g.support, w (f i) = (w y) ^ ((D:ℤ) * K i + (i:ℤ)) := by
    intro i hi
    have hci : w (g.coeff i) = (w π) ^ (K i) := hK i hi
    simp only [f]
    rw [Valuation.map_mul, hci, hpow i, hπz, ← zpow_mul, ← zpow_add₀ hyne]
  -- the minimum is strict at the other indices.
  have hstrict : ∀ i ∈ g.support, i ≠ i₀ → (D:ℤ)*K i₀ + (i₀:ℤ) < (D:ℤ)*K i + (i:ℤ) := by
    intro i hi hne'
    rcases lt_or_eq_of_le (hmin i hi) with hlt | heq
    · exact hlt
    · exact absurd (hinj i₀ hi₀ i hi heq).symm hne'
  have hlt : ∀ i ∈ g.support, i ≠ i₀ → w (f i) < w (f i₀) := by
    intro i hi hne'
    rw [hterm i hi, hterm i₀ hi₀]
    exact (zpow_lt_zpow_iff_right_of_lt_one₀ hβ0 hy1).mpr (hstrict i hi hne')
  have hi₀range : i₀ ∈ Finset.range (g.natDegree + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hle_nat i₀ hi₀))
  -- the valuation of the full sum is the value of the minimal term.
  have hsum : w (∑ i ∈ Finset.range (g.natDegree + 1), f i) = w (f i₀) := by
    apply Valuation.map_sum_eq_of_lt (s := Finset.range (g.natDegree + 1)) (f := f) (j := i₀) w
      hi₀range
    intro i hmem
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hmem
    obtain ⟨hirange, hne'⟩ := hmem
    by_cases hsupp : i ∈ g.support
    · exact hlt i hsupp hne'
    · -- a vanishing coefficient contributes the term `0` of value `0`.
      have hcoeff0 : g.coeff i = 0 := by
        by_contra hc
        exact hsupp ((Polynomial.mem_support_iff).mpr hc)
      have hfi : f i = 0 := by simp [f, hcoeff0]
      rw [hfi, Valuation.map_zero]
      exact zero_lt_iff.mpr (by rw [hterm i₀ hi₀]; exact zpow_ne_zero _ hyne)
  have haeval : (Polynomial.aeval y) g = ∑ i ∈ Finset.range (g.natDegree + 1), f i := by
    rw [Polynomial.aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [f]
  refine ⟨(D:ℤ)*K i₀ + (i₀:ℤ), ?_, i₀, hi₀, rfl, ?_⟩
  · rw [haeval, hsum, hterm i₀ hi₀]
  · intro i hi
    exact hmin i hi

end NK.LocalReciprocityLubinTate.Unramified
