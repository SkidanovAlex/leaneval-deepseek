import Mathlib
import Submission.Work.Peluse.Basic

/-!
# Summing over `[m*D] = arithIcc 1 (m*D)`

A sum over the interval `1[(m*D)] = {1, …, m*D}` splits into the `m` blocks
`{q*m + 1, …, q*m + m}`, `q = 0, …, D-1`, of the *shifted* arithmetic progression
`m[D] = {m, 2m, …, Dm}`:

`∑_{k ∈ 1[m*D]} g k = ∑_{j < m} ∑_{k ∈ m[D]} g (k + (j + 1 - m))`.

The two sides list the same numbers `1, …, m*D` (in a different order), so this is
a pure reindexing.
-/

namespace Work.Peluse.Ulower

/-- `[1,N] = {1, …, N}` is the image of `{0, …, N-1}` under `u ↦ u + 1`. -/
lemma Icc_one_eq_image_range (N : ℕ) :
    Finset.Icc 1 N = (Finset.range N).image (fun u : ℕ => u + 1) := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨n - 1, by omega, by omega⟩
  · rintro ⟨u, hu, rfl⟩
    omega

/-- A sum over `[1,N]` as a sum indexed by `Fin N`. -/
lemma sum_Icc_one_eq_sum_fin (N : ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ i : Fin N, f ((i : ℕ) + 1) := by
  rw [Icc_one_eq_image_range,
    Finset.sum_image (by
      intro a _ b _ hab
      exact Nat.succ.inj hab),
    Fin.sum_univ_eq_sum_range (fun u : ℕ => f (u + 1)) N]

/-- `1[L] = {1, …, L}` (as a set of integers) is the image of `{0, …, L-1}`. -/
lemma arithIcc_one_eq_image_range (N : ℕ) :
    Work.Peluse.arithIcc 1 N
      = (Finset.range N).image (fun u : ℕ => ((u + 1 : ℕ) : ℤ)) := by
  ext x
  simp only [Work.Peluse.arithIcc, Finset.mem_image, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨n, ⟨h1, h2⟩, rfl⟩
    exact ⟨n - 1, by omega, by rw [Nat.sub_add_cancel h1, one_mul]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u + 1, ⟨by omega, by omega⟩, by rw [one_mul]⟩

/-- A sum over the interval `1[N]` as a sum indexed by `Fin N`. -/
lemma sum_arithIcc_one (N : ℕ) (g : ℤ → ℂ) :
    ∑ k ∈ Work.Peluse.arithIcc 1 N, g k
      = ∑ i : Fin N, g (((i : ℕ) + 1 : ℕ) : ℤ) := by
  rw [arithIcc_one_eq_image_range,
    Finset.sum_image (by
      intro a _ b _ hab
      exact Nat.succ.inj (Int.ofNat.inj hab)),
    Fin.sum_univ_eq_sum_range (fun u : ℕ => g (((u + 1 : ℕ) : ℤ))) N]

/-- A sum over the arithmetic progression `c[L]` as a sum indexed by `Fin L`
(the term is `f (c * (u+1))`, `u : Fin L`). -/
lemma sum_arithIcc_eq_sum_fin {c : ℤ} (hc : c ≠ 0) (D : ℕ) (f : ℤ → ℂ) :
    ∑ k ∈ Work.Peluse.arithIcc c D, f k
      = ∑ u : Fin D, f (c * (((u : ℕ) + 1 : ℕ) : ℤ)) := by
  rw [Work.Peluse.arithIcc,
    Finset.sum_image (by
      intro a _ b _ hab
      exact Int.ofNat.inj (mul_left_cancel₀ hc hab))]
  exact sum_Icc_one_eq_sum_fin D (fun n : ℕ => f (c * (n : ℤ)))

/-- **Block decomposition.** A sum over `Fin (m*D)` splits into the `m` blocks of
length `D`: the value `q*m + r` (with `r < m`, `q < D`) is hit exactly once. -/
lemma sum_fin_mul_eq_blocks (m : ℕ) (hm : 0 < m) (D : ℕ) (g : ℤ → ℂ) :
    ∑ i : Fin (m * D), g (((i : ℕ) + 1 : ℕ) : ℤ)
      = ∑ j : Fin m, ∑ u : Fin D, g (((m * (u : ℕ) + (j : ℕ) + 1 : ℕ)) : ℤ) := by
  rw [← Fintype.sum_prod_type (f := fun p : Fin m × Fin D =>
        g (((m * (p.2 : ℕ) + (p.1 : ℕ) + 1 : ℕ)) : ℤ))]
  let i : Fin m × Fin D → Fin (m * D) := fun p =>
    ⟨m * (p.2 : ℕ) + (p.1 : ℕ), by
      have h2 : (p.2 : ℕ) + 1 ≤ D := by have := p.2.isLt; omega
      calc m * (p.2 : ℕ) + (p.1 : ℕ) < m * (p.2 : ℕ) + m := by
            have := p.1.isLt; omega
        _ = m * ((p.2 : ℕ) + 1) := by rw [Nat.mul_succ]
        _ ≤ m * D := Nat.mul_le_mul_left m h2⟩
  refine (Finset.sum_bij (fun p _ => i p) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_).symm
  · intro p _ q _ hpq
    have hv : m * (p.2 : ℕ) + (p.1 : ℕ) = m * (q.2 : ℕ) + (q.1 : ℕ) :=
      congrArg Fin.val hpq
    have h1 : (p.1 : ℕ) = (q.1 : ℕ) := by
      have hmod : (m * (p.2 : ℕ) + (p.1 : ℕ)) % m
          = (m * (q.2 : ℕ) + (q.1 : ℕ)) % m := by rw [hv]
      rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt p.1.isLt,
        Nat.mod_eq_of_lt q.1.isLt] at hmod
      exact hmod
    have h2 : (p.2 : ℕ) = (q.2 : ℕ) := by
      have h := hv
      rw [h1] at h
      exact Nat.mul_left_cancel hm (Nat.add_right_cancel h)
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  · intro b _
    refine ⟨(⟨(b : ℕ) % m, Nat.mod_lt _ hm⟩, ⟨(b : ℕ) / m, ?_⟩), Finset.mem_univ _, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hm, Nat.mul_comm D m]
      exact b.isLt
    · apply Fin.ext
      exact Nat.div_add_mod (b : ℕ) m
  · intro p _
    rfl

theorem sum_arithIcc_one_eq (m D : ℕ) (g : ℤ → ℂ) :
    ∑ k ∈ Work.Peluse.arithIcc 1 (m * D), g k =
      ∑ j : Fin m, ∑ k ∈ Work.Peluse.arithIcc (m : ℤ) D,
        g (k + ((j : ℤ) + 1 - (m : ℤ))) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    simp [Work.Peluse.arithIcc]
  · have hmz : (m : ℤ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Nat.pos_iff_ne_zero.mp hm
    have hinner : ∀ j : Fin m,
        (∑ k ∈ Work.Peluse.arithIcc (m : ℤ) D,
            g (k + ((j : ℤ) + 1 - (m : ℤ))))
          = ∑ u : Fin D, g (((m * (u : ℕ) + (j : ℕ) + 1 : ℕ)) : ℤ) := by
      intro j
      rw [sum_arithIcc_eq_sum_fin (c := (m : ℤ)) hmz D
            (fun k : ℤ => g (k + ((j : ℤ) + 1 - (m : ℤ))))]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      congr 1
      push_cast
      ring
    rw [sum_arithIcc_one]
    trans ∑ j : Fin m, ∑ u : Fin D, g (((m * (u : ℕ) + (j : ℕ) + 1 : ℕ)) : ℤ)
    · exact sum_fin_mul_eq_blocks m hm D g
    · exact Finset.sum_congr rfl (fun j _ => (hinner j).symm)

end Work.Peluse.Ulower
