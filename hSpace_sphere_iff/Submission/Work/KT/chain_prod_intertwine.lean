import Mathlib

namespace Work.KT

/-- If all the `W i` with `j < i < m` are `1`, then the prefix products `F` agree at `m` and at
`j + 1`. -/
private lemma F_eq_of_ones {A : Type*} [Monoid A] (W F : ℕ → A) (j : ℕ)
    (hFs : ∀ k, F (k + 1) = F k * W k) :
    ∀ m, (∀ i, j < i → i < m → W i = 1) → j + 1 ≤ m → F m = F (j + 1) := by
  intro m
  induction m with
  | zero =>
    intro _ h
    omega
  | succ m ih =>
    intro h3 hm
    rcases Nat.lt_or_eq_of_le hm with hlt | heq
    · have hle : j + 1 ≤ m := by omega
      have hstep : F (m + 1) = F m := by
        rw [hFs m]
        have hW : W m = 1 := h3 m (by omega) (by omega)
        rw [hW, mul_one]
      rw [hstep]
      exact ih (fun i hji him => h3 i hji (by omega)) hle
    · rw [← heq]

/-- Consecutive intertwining relations compose along prefix products: `F j` intertwines `p j`
with `p 0`. -/
private lemma prefix_intertwine {A : Type*} [Monoid A] (p : ℕ → A) (W F : ℕ → A) (j : ℕ)
    (hF0 : F 0 = 1) (hFs : ∀ k, F (k + 1) = F k * W k)
    (h1 : ∀ i, i < j → W i * p (i + 1) = p i * W i) :
    F j * p j = p 0 * F j := by
  have key : ∀ k, k ≤ j → F k * p k = p 0 * F k := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [hF0, one_mul, mul_one]
    | succ k ih =>
      intro hk
      have hkj : k < j := by omega
      calc F (k + 1) * p (k + 1)
          = (F k * W k) * p (k + 1) := by rw [hFs k]
        _ = F k * (W k * p (k + 1)) := by rw [mul_assoc]
        _ = F k * (p k * W k) := by rw [h1 k hkj]
        _ = (F k * p k) * W k := by rw [mul_assoc]
        _ = (p 0 * F k) * W k := by rw [ih (by omega)]
        _ = p 0 * (F k * W k) := by rw [mul_assoc]
        _ = p 0 * F (k + 1) := by rw [hFs k]
  exact key j le_rfl

/-- Chaining of intertwiners.  `F` is the sequence of prefix products of `W` (`F 0 = 1`,
`F (k+1) = F k * W k`).  If `W i` intertwines `p (i+1)` with `p i` for all `i < j`, if `W j`
intertwines `q` with `p j`, and if all later `W i` (`j < i < m`) equal `1`, then `F m` intertwines
`q` with `p 0`. -/
theorem chain_prod_intertwine {A : Type*} [Monoid A] (p : ℕ → A) (q : A) (W F : ℕ → A) (j m : ℕ)
    (hF0 : F 0 = 1) (hFs : ∀ k, F (k + 1) = F k * W k) (hjm : j < m)
    (h1 : ∀ i, i < j → W i * p (i + 1) = p i * W i)
    (h2 : W j * q = p j * W j) (h3 : ∀ i, j < i → i < m → W i = 1) :
    F m * q = p 0 * F m := by
  have hFm : F m = F (j + 1) := F_eq_of_ones W F j hFs m h3 (by omega)
  have hPF : F j * p j = p 0 * F j := prefix_intertwine p W F j hF0 hFs h1
  calc F m * q
      = F (j + 1) * q := by rw [hFm]
    _ = (F j * W j) * q := by rw [hFs j]
    _ = F j * (W j * q) := by rw [mul_assoc]
    _ = F j * (p j * W j) := by rw [h2]
    _ = (F j * p j) * W j := by rw [mul_assoc]
    _ = (p 0 * F j) * W j := by rw [hPF]
    _ = p 0 * (F j * W j) := by rw [mul_assoc]
    _ = p 0 * F (j + 1) := by rw [hFs j]
    _ = p 0 * F m := by rw [hFm]

end Work.KT
