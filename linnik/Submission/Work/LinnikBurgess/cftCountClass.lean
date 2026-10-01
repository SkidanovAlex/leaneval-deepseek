import Mathlib

namespace Work.LinnikBurgess

/-- The number of integers `0 ≤ x < p^N` lying in the residue class `c` modulo `p^k`
(`c < p^k`) is at most `p^(N-k)`: the map `x ↦ x / p^k` is injective on that class and
takes values in `range (p^(N-k))`. -/
lemma cftCountClass {p N k c : ℕ} (hp : 2 ≤ p) (hc : c < p ^ k) :
    ((Finset.range (p ^ N)).filter (fun x : ℕ => x % p ^ k = c)).card ≤ p ^ (N - k) := by
  have hp0 : 0 < p := by omega
  -- key pointwise bound: an element of the class lies below `p^N`, and its quotient
  -- by `p^k` is consequently below `p^(N-k)`
  have hkey : ∀ x : ℕ, x < p ^ N → x / p ^ k < p ^ (N - k) := by
    intro x hxlt
    by_contra hcon
    simp only [not_lt] at hcon
    have h1 : p ^ (N - k) * p ^ k ≤ (x / p ^ k) * p ^ k := Nat.mul_le_mul_right _ hcon
    have h2 : (x / p ^ k) * p ^ k ≤ x := Nat.div_mul_le_self x (p ^ k)
    have h3 : p ^ N ≤ p ^ (N - k) * p ^ k := by
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right hp0 (by omega)
    omega
  -- key pointwise injectivity: two elements of the class with the same quotient coincide
  have hinjkey : ∀ x y : ℕ, x % p ^ k = c → y % p ^ k = c →
      x / p ^ k = y / p ^ k → x = y := by
    intro x y hxmod hymod hxy
    have hx' : x = p ^ k * (x / p ^ k) + c := by
      rw [← hxmod]
      exact (Nat.div_add_mod x (p ^ k)).symm
    have hy' : y = p ^ k * (y / p ^ k) + c := by
      rw [← hymod]
      exact (Nat.div_add_mod y (p ^ k)).symm
    calc x = p ^ k * (x / p ^ k) + c := hx'
      _ = p ^ k * (y / p ^ k) + c := by rw [hxy]
      _ = y := hy'.symm
  have himg : (((Finset.range (p ^ N)).filter (fun x : ℕ => x % p ^ k = c)).image
        (fun x : ℕ => x / p ^ k)) ⊆ Finset.range (p ^ (N - k)) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_range.mpr
      (hkey x (Finset.mem_range.mp (Finset.mem_filter.mp hx).1))
  have hinj : Set.InjOn (fun x : ℕ => x / p ^ k)
      ↑((Finset.range (p ^ N)).filter (fun x : ℕ => x % p ^ k = c)) := by
    intro x hx y hy hxy
    have hx' : x ∈ (Finset.range (p ^ N)).filter (fun x : ℕ => x % p ^ k = c) := hx
    have hy' : y ∈ (Finset.range (p ^ N)).filter (fun x : ℕ => x % p ^ k = c) := hy
    exact hinjkey x y (Finset.mem_filter.mp hx').2 (Finset.mem_filter.mp hy').2 hxy
  calc ((Finset.range (p ^ N)).filter (fun x : ℕ => x % p ^ k = c)).card
      = (((Finset.range (p ^ N)).filter (fun x : ℕ => x % p ^ k = c)).image
          (fun x : ℕ => x / p ^ k)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (p ^ (N - k))).card := Finset.card_le_card himg
    _ = p ^ (N - k) := Finset.card_range _

end Work.LinnikBurgess
