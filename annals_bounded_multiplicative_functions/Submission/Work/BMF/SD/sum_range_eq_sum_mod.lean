import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/--
Reindexing a sum over `Finset.range L` by Euclidean division with remainder by `q`:
writing each `n` uniquely as `m * q + r` with `r = n % q` and `m = n / q`, the sum over
`n < L` becomes the double sum over the residue `r < q` and the quotient
`m < (L + q - 1 - r) / q` (the number of `m ≥ 0` with `m * q + r < L`).
-/
theorem sum_range_eq_sum_mod (q L : ℕ) (hq : 1 ≤ q) (f : ℕ → ℂ) :
    ∑ n ∈ Finset.range L, f n
      = ∑ r ∈ Finset.range q, ∑ m ∈ Finset.range ((L + q - 1 - r) / q), f (m * q + r) := by
  have hq0 : 0 < q := hq
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun n => ⟨n % q, n / q⟩) (fun x => x.2 * q + x.1) ?_ ?_ ?_ ?_ ?_
  · -- the image of `n ∈ range L` lies in the sigma set
    rintro a ha
    rw [Finset.mem_range] at ha
    rw [Finset.mem_sigma]
    constructor
    · rw [Finset.mem_range]; exact Nat.mod_lt a hq0
    · rw [Finset.mem_range]
      show a / q < (L + q - 1 - a % q) / q
      have hA : a / q * q + a % q = a := by
        have := Nat.div_add_mod a q
        rwa [Nat.mul_comm] at this
      have h2 : (a / q + 1) * q ≤ L + q - 1 - a % q := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      have h3 : a / q + 1 ≤ (L + q - 1 - a % q) / q :=
        (Nat.le_div_iff_mul_le hq0).mpr h2
      omega
  · -- the map `(r, m) ↦ m * q + r` maps the sigma set into `range L`
    rintro ⟨r, m⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hr, hm⟩ := hx
    rw [Finset.mem_range] at hr hm
    rw [Finset.mem_range]
    show m * q + r < L
    have h1 : m * q + q ≤ L + q - 1 - r := by
      have := (Nat.le_div_iff_mul_le hq0).mp (Nat.succ_le_of_lt hm)
      rwa [Nat.succ_mul] at this
    omega
  · -- `j ∘ i = id` on `range L`
    intro a ha
    show a / q * q + a % q = a
    have := Nat.div_add_mod a q
    rwa [Nat.mul_comm] at this
  · -- `i ∘ j = id` on the sigma set
    rintro ⟨r, m⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hr, hm⟩ := hx
    rw [Finset.mem_range] at hr
    show (⟨(m * q + r) % q, (m * q + r) / q⟩ : Sigma (fun _ : ℕ => ℕ)) = ⟨r, m⟩
    have hmod : (m * q + r) % q = r := by
      rw [Nat.mul_comm m q, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    have hdiv : (m * q + r) / q = m := by
      rw [Nat.mul_comm m q, Nat.mul_add_div hq, Nat.div_eq_of_lt hr, Nat.add_zero]
    rw [hmod, hdiv]
  · -- the summed values agree
    intro a ha
    show f a = f (a / q * q + a % q)
    have := Nat.div_add_mod a q
    rw [Nat.mul_comm] at this
    rw [this]

end Work.BMF.SD
