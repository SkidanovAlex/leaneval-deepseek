import Mathlib

namespace Commons.Data.Int

/-- **Counting the integers in a real window.**  The integers `n` with
`a ≤ n ≤ b` form the integer interval `Icc ⌈a⌉ ⌊b⌋`, which has at most
`⌈b - a⌉₊ + 1` elements. -/
lemma ncard_Icc_int_ceil_floor_le (a b : ℝ) :
    (Set.Icc (⌈a⌉ : ℤ) (⌊b⌋ : ℤ)).ncard ≤ ⌈b - a⌉₊ + 1 := by
  rw [← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]
  apply Int.toNat_le.mpr
  have hb : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
  have ha : a ≤ (⌈a⌉ : ℝ) := Int.le_ceil a
  have hc : b - a ≤ (⌈b - a⌉₊ : ℝ) := Nat.le_ceil (b - a)
  have : ((⌊b⌋ + 1 - ⌈a⌉ : ℤ) : ℝ) ≤ (((⌈b - a⌉₊ + 1 : ℕ) : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

/-- **How many residues mod `Q` can lie in a window of width `2K`?**  If `0 ≤ θ < Q` and `K ≥ 0`,
at most `⌈2K⌉ + 1` integers `r ∈ [0, Q)` satisfy `dist(r - θ, Q ℤ) ≤ K`, i.e.
`∃ z : ℤ, |r - θ - z Q| ≤ K`.

Proof sketch: for `r ∈ [0,Q)`, the only multiple of `Q` that can be within `K` of `r - θ` is `0`
(when `θ` is close to `r`), `Q` (when `θ` is close to `0` and `r` close to `Q`) or `-Q` (when `θ`
is close to `Q` and `r` close to `0`); each of these gives an interval of `r`-values of length
`2K`, which contains at most `⌈2K⌉ + 1` integers.  (Keeping the constant `⌈2K⌉ + 1` may need a small
case analysis; an explicit larger constant such as `3 * (⌈2K⌉ + 1)` or `⌈4 * K⌉₊ + 2` is also
acceptable.) -/
theorem card_residue_window_le {Q : ℕ} (hQ : 0 < Q) {θ K : ℝ} (hθ0 : 0 ≤ θ) (hθQ : θ < Q)
    (hK : 0 ≤ K) :
    Set.ncard {r : ℤ | 0 ≤ r ∧ r < (Q : ℤ) ∧ ∃ z : ℤ, |(r : ℝ) - θ - (z : ℝ) * (Q : ℝ)| ≤ K}
      ≤ ⌈2 * K⌉₊ + 1 := by
  classical
  have _hK : 0 ≤ K := hK
  have _hθ0 : 0 ≤ θ := hθ0
  have _hθQ : θ < (Q : ℝ) := hθQ
  set S : Set ℤ :=
    {r : ℤ | 0 ≤ r ∧ r < (Q : ℤ) ∧ ∃ z : ℤ, |(r : ℝ) - θ - (z : ℝ) * (Q : ℝ)| ≤ K}
  -- For every `r` pick a witness `zf r` of the distance condition (arbitrary if there is none).
  let zf : ℤ → ℤ := fun r ↦
    if h : ∃ z : ℤ, |(r : ℝ) - θ - (z : ℝ) * (Q : ℝ)| ≤ K then Classical.choose h else 0
  -- Shift `r` by the multiple of `Q` selected by its witness: it lands in the window `[θ-K, θ+K]`.
  let φ : ℤ → ℤ := fun r ↦ r - zf r * (Q : ℤ)
  have hzf : ∀ r : ℤ, (∃ z : ℤ, |(r : ℝ) - θ - (z : ℝ) * (Q : ℝ)| ≤ K) →
      |(r : ℝ) - θ - (zf r : ℝ) * (Q : ℝ)| ≤ K := by
    intro r h
    simp only [zf]
    rw [dif_pos h]
    exact Classical.choose_spec h
  have hφcast : ∀ r : ℤ, ((φ r : ℤ) : ℝ) = (r : ℝ) - (zf r : ℝ) * (Q : ℝ) := by
    intro r
    simp only [φ]
    push_cast
    ring
  have hmem : ∀ r ∈ S, φ r ∈ Set.Icc (⌈θ - K⌉ : ℤ) (⌊θ + K⌋ : ℤ) := by
    intro r hr
    have hspec := hzf r hr.2.2
    have hx : |(φ r : ℝ) - θ| ≤ K := by
      rw [hφcast r,
        show (r : ℝ) - (zf r : ℝ) * (Q : ℝ) - θ = (r : ℝ) - θ - (zf r : ℝ) * (Q : ℝ) by ring]
      exact hspec
    have h1 : θ - K ≤ (φ r : ℝ) := by
      have := (abs_le.mp hx).1
      linarith
    have h2 : (φ r : ℝ) ≤ θ + K := by
      have := (abs_le.mp hx).2
      linarith
    exact ⟨Int.ceil_le.mpr h1, Int.le_floor.mpr h2⟩
  have hinj : Set.InjOn φ S := by
    intro r hr r' hr' heq
    have hQz : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast hQ
    have hlt : |r - r'| < (Q : ℤ) := by
      have hr1 : 0 ≤ r := hr.1
      have hr2 : r < (Q : ℤ) := hr.2.1
      have hr1' : 0 ≤ r' := hr'.1
      have hr2' : r' < (Q : ℤ) := hr'.2.1
      rw [abs_lt]
      constructor <;> omega
    have hd : (zf r - zf r') * (Q : ℤ) = r - r' := by
      have h := heq
      simp only [φ] at h
      linear_combination -h
    have habs : |r - r'| = |zf r - zf r'| * (Q : ℤ) := by
      rw [← hd, abs_mul, abs_of_pos hQz]
    have hlt' : |zf r - zf r'| * (Q : ℤ) < (Q : ℤ) := by rw [← habs]; exact hlt
    have hlt1 : |zf r - zf r'| < 1 := by
      nlinarith [abs_nonneg (zf r - zf r'), hQz, hlt']
    have hzero : zf r - zf r' = 0 := by
      have := (abs_lt.mp hlt1)
      omega
    have : r - r' = 0 := by rw [← hd, hzero]; ring
    omega
  refine le_trans (Set.ncard_le_ncard_of_injOn φ hmem hinj) ?_
  have hb := ncard_Icc_int_ceil_floor_le (θ - K) (θ + K)
  have hb' : (Set.Icc (⌈θ - K⌉ : ℤ) (⌊θ + K⌋ : ℤ)).ncard ≤ ⌈2 * K⌉₊ + 1 := by
    simpa only [show θ + K - (θ - K) = 2 * K by ring] using hb
  exact hb'

end Commons.Data.Int
