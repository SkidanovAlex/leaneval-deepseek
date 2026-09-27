import Mathlib

namespace Work.EKLC6Core

/-- **Relative floor count.** A finite set of `σ`-indexed real tuples, each coordinate lying in
the interval `[c₀ p - R, c₀ p + R]`, whose floor map `t ↦ ⌊t/η⌋` (coordinatewise, mesh `η`) is
injective, has at most `(2N+2) ^ card σ` elements, provided `R ≤ N η`.  This is the scale-free
form of the floor count: the count depends on the *width* `R` of the box divided by the mesh `η`,
not on the absolute position `c₀`. -/
theorem floorTuple_rel_card_bound {σ ι : Type*} [Fintype σ] [DecidableEq σ] {S : Finset ι}
    {f : ι → σ → ℝ} {η R : ℝ} {c₀ : σ → ℝ} {N : ℕ}
    (hη : 0 < η) (hR : R ≤ (N : ℝ) * η)
    (hrange : ∀ x ∈ S, ∀ p, |f x p - c₀ p| ≤ R)
    (hinj : ∀ x ∈ S, ∀ x' ∈ S, (∀ p, ⌊f x p / η⌋ = ⌊f x' p / η⌋) → x = x') :
    S.card ≤ (2 * N + 2) ^ Fintype.card σ := by
  classical
  -- the coordinatewise floor map
  set g : ι → (σ → ℤ) := fun x p => ⌊f x p / η⌋ with hg
  have hinjS : Set.InjOn g (S : Set ι) := by
    intro x hx x' hx' h
    exact hinj x hx x' hx' (fun p => by simpa [hg] using congrFun h p)
  -- the window in which every coordinate floor lives
  set m : σ → ℤ := fun p => ⌊(c₀ p - R) / η⌋ with hm
  set M : σ → ℤ := fun p => ⌊(c₀ p + R) / η⌋ with hM
  have hsub : S.image g ⊆ Fintype.piFinset (fun p : σ => Finset.Icc (m p) (M p)) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hxS, rfl⟩ := hy
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_Icc]
    obtain ⟨hl, hu⟩ := abs_le.mp (hrange x hxS p)
    constructor
    · rw [hm, hg]
      exact Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) (le_of_lt hη))
    · rw [hM, hg]
      exact Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) (le_of_lt hη))
  -- each window contains at most `2N+2` integers
  have hIcc : ∀ p, (Finset.Icc (m p) (M p)).card ≤ 2 * N + 2 := by
    intro p
    rw [Int.card_Icc, Int.toNat_le]
    have hRN : R / η ≤ (N : ℝ) := by
      rw [div_le_iff₀ hη]; linarith [hR]
    have hMp : (M p : ℝ) ≤ (c₀ p + R) / η := by rw [hM]; exact Int.floor_le _
    have hmp : (c₀ p - R) / η < (m p : ℝ) + 1 := by rw [hm]; exact Int.lt_floor_add_one _
    have hkey : (c₀ p + R) / η = (c₀ p - R) / η + 2 * (R / η) := by ring
    have hstep : (M p : ℝ) - (m p : ℝ) < 2 * (R / η) + 1 := by
      have h1 : (M p : ℝ) ≤ (c₀ p - R) / η + 2 * (R / η) := by rw [← hkey]; exact hMp
      linarith
    have hlt : M p - m p < ((2 * N + 1 : ℕ) : ℤ) := by
      have h2 : 2 * (R / η) + 1 ≤ 2 * (N : ℝ) + 1 := by linarith
      have : ((M p - m p : ℤ) : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    have hlt2 : M p - m p ≤ ((2 * N : ℕ) : ℤ) := by
      have h' : M p - m p < ((2 * N : ℕ) : ℤ) + 1 := by push_cast at hlt ⊢; linarith
      exact Int.le_of_lt_add_one h'
    have h2 : ((2 * N : ℕ) : ℤ) + 2 = ((2 * N + 2 : ℕ) : ℤ) := by push_cast; ring
    linarith
  calc S.card = (S.image g).card := (Finset.card_image_of_injOn hinjS).symm
    _ ≤ (Fintype.piFinset (fun p : σ => Finset.Icc (m p) (M p))).card := Finset.card_le_card hsub
    _ = ∏ p : σ, (Finset.Icc (m p) (M p)).card := Fintype.card_piFinset _
    _ ≤ ∏ _p : σ, (2 * N + 2) :=
        Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) (fun p _ => hIcc p)
    _ = (2 * N + 2) ^ Fintype.card σ := by rw [Finset.prod_const, Finset.card_univ]

end Work.EKLC6Core
