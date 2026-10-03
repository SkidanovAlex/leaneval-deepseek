import Mathlib

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- For natural numbers, `c ^ 4 ≤ x` holds exactly when `c` is below
`Nat.sqrt (Nat.sqrt x) + 1`. -/
lemma pow_four_le_iff_lt_sqrt_sqrt_succ {x c : ℕ} :
    c ^ 4 ≤ x ↔ c < Nat.sqrt (Nat.sqrt x) + 1 := by
  rw [Nat.lt_succ_iff]
  constructor
  · intro h
    rw [Nat.le_sqrt', Nat.le_sqrt']
    calc (c ^ 2) ^ 2 = c ^ 4 := by ring
      _ ≤ x := h
  · intro h
    have h2 : c ^ 2 ≤ Nat.sqrt x := Nat.le_sqrt'.mp h
    have h4 : (c ^ 2) ^ 2 ≤ x := Nat.le_sqrt'.mp h2
    calc c ^ 4 = (c ^ 2) ^ 2 := by ring
      _ ≤ x := h4

/-- The number of natural pairs `(a, b)` with `a ^ 2 + b ^ 4 ≤ x` equals the sum
over `c` from `0` to `Nat.sqrt (Nat.sqrt x)` of the number `Nat.sqrt (x - c ^ 4) + 1`
of admissible first coordinates `a`.

For each fixed second coordinate `b = c`, the admissible first coordinates are
exactly those `a` with `a ^ 2 ≤ x - c ^ 4`, and there are `Nat.sqrt (x - c ^ 4) + 1`
of them. The condition `b ^ 4 ≤ x` restricts `b` to `0, …, Nat.sqrt (Nat.sqrt x)`,
so the set of pairs is the disjoint union of these rows. -/
lemma card_sq_add_pow_four_natpairs {x : ℕ} :
    ({p : ℕ × ℕ | p.1 ^ 2 + p.2 ^ 4 ≤ x}.ncard) =
      ∑ c ∈ Finset.range (Nat.sqrt (Nat.sqrt x) + 1), (Nat.sqrt (x - c ^ 4) + 1) := by
  classical
  let N : ℕ := Nat.sqrt (Nat.sqrt x) + 1
  let K : ℕ → ℕ := fun c => Nat.sqrt (x - c ^ 4) + 1
  let A : Finset ((c : ℕ) × ℕ) := (Finset.range N).sigma (fun c => Finset.range (K c))
  let φ : ((c : ℕ) × ℕ) → ℕ × ℕ := fun z => (z.2, z.1)
  have hφinj : Function.Injective φ := by
    intro z w h
    obtain ⟨c1, a1⟩ := z
    obtain ⟨c2, a2⟩ := w
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨ha, hc⟩ := h
    subst ha
    subst hc
    rfl
  have hmem : ∀ p : ℕ × ℕ, p ∈ A.image φ ↔ p.1 ^ 2 + p.2 ^ 4 ≤ x := by
    intro p
    rw [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, hzp⟩
      obtain ⟨c, a⟩ := z
      simp only [A, Finset.mem_sigma, Finset.mem_range] at hz
      obtain ⟨hc, ha⟩ := hz
      have hzp' : (a, c) = p := by simpa only [φ] using hzp
      obtain ⟨hap, hcp⟩ := Prod.ext_iff.mp hzp'
      rw [← hap, ← hcp]
      have hc4 : c ^ 4 ≤ x := pow_four_le_iff_lt_sqrt_sqrt_succ.mpr hc
      have ha2 : a ^ 2 ≤ x - c ^ 4 := by
        have : a ≤ Nat.sqrt (x - c ^ 4) := by
          apply Nat.lt_succ_iff.mp
          show a < K c
          exact ha
        exact Nat.le_sqrt'.mp this
      calc a ^ 2 + c ^ 4 ≤ (x - c ^ 4) + c ^ 4 := Nat.add_le_add_right ha2 _
        _ = x := Nat.sub_add_cancel hc4
    · intro hp
      refine ⟨⟨p.2, p.1⟩, ?_, ?_⟩
      · simp only [A, Finset.mem_sigma, Finset.mem_range, K]
        constructor
        · have : p.2 ^ 4 ≤ x := le_trans (Nat.le_add_left _ _) hp
          exact pow_four_le_iff_lt_sqrt_sqrt_succ.mp this
        · have h : p.1 ^ 2 ≤ x - p.2 ^ 4 := by omega
          exact Nat.lt_succ_of_le (Nat.le_sqrt'.mpr h)
      · simp only [φ]
  have hset : (A.image φ : Set (ℕ × ℕ)) = {p : ℕ × ℕ | p.1 ^ 2 + p.2 ^ 4 ≤ x} := by
    ext p
    exact hmem p
  rw [← hset]
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective A hφinj]
  rw [show A = (Finset.range N).sigma (fun c => Finset.range (K c)) from rfl, Finset.card_sigma]
  simp only [Finset.card_range]
  rfl

end Commons.NumberTheory.FriedlanderIwaniec
