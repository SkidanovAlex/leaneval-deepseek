import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- An `m × r` integer matrix with more rows than columns (`r < m`) has a nontrivial integer
vector in its kernel: `∑ j, a j * q j i = 0` for all `i`.

Proof: the columns `v j = (fun i => q j i)` are `m` vectors in the `r`-dimensional `ℚ`-vector
space `Fin r → ℚ`, so they are linearly dependent; a nontrivial rational relation is cleared
of denominators to give the required integer vector. -/
theorem int_linDep_of_card_lt {r m : ℕ} (hm : r < m) (q : Fin m → Fin r → ℤ) :
    ∃ a : Fin m → ℤ, a ≠ 0 ∧ ∀ i, ∑ j, a j * q j i = 0 := by
  classical
  -- Step 1: linear dependence over `ℚ`.
  have hli : ¬ LinearIndependent ℚ (fun j : Fin m => (fun i : Fin r => (q j i : ℚ))) := by
    intro h
    have hcard := h.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_fin_fun] at hcard
    omega
  rw [Fintype.not_linearIndependent_iff] at hli
  obtain ⟨g, hg_sum, hg_nz⟩ := hli
  have hg_pt : ∀ i, ∑ j, g j * (q j i : ℚ) = 0 := by
    intro i
    have h := congr_fun hg_sum i
    simpa using h
  -- Step 2: clear denominators.
  let D : ℕ := ∏ j, (g j).den
  have hDpos : 0 < D := by
    apply Finset.prod_pos
    intro j _
    exact (g j).den_pos
  have hDne : D ≠ 0 := hDpos.ne'
  let a : Fin m → ℤ := fun j => (((D / (g j).den : ℕ) : ℤ) * (g j).num)
  have ha_cast : ∀ j, (a j : ℚ) = (D : ℚ) * g j := by
    intro j
    have hdvd : (g j).den ∣ D :=
      Finset.dvd_prod_of_mem (fun j => (g j).den) (Finset.mem_univ j)
    have hden : ((g j).den : ℚ) ≠ 0 := by exact_mod_cast (g j).den_ne_zero
    have key : ((D / (g j).den : ℕ) : ℚ) = (D : ℚ) / ((g j).den : ℚ) := by
      rw [eq_div_iff hden, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    have hDg : (D : ℚ) * g j = (D : ℚ) * (((g j).num : ℚ) / ((g j).den : ℚ)) := by
      rw [Rat.num_div_den]
    simp only [a, Int.cast_mul, Int.cast_natCast]
    rw [key, hDg]
    ring
  -- Step 3: the integer vector is annihilated by `q`.
  have hsum_int : ∀ i, ∑ j, a j * q j i = 0 := by
    intro i
    have hcast : ((∑ j, a j * q j i : ℤ) : ℚ) = ((0 : ℤ) : ℚ) := by
      push_cast
      calc ∑ j, (a j : ℚ) * (q j i : ℚ)
          = ∑ j, ((D : ℚ) * g j) * (q j i : ℚ) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [ha_cast j]
        _ = (D : ℚ) * ∑ j, g j * (q j i : ℚ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = ((0 : ℤ) : ℚ) := by rw [hg_pt i, mul_zero]; simp
    exact_mod_cast hcast
  refine ⟨a, ?_, hsum_int⟩
  -- Step 4: `a` is nonzero.
  intro ha0
  obtain ⟨j, hj⟩ := hg_nz
  have h1 : (a j : ℚ) = 0 := by rw [ha0]; simp
  rw [ha_cast j] at h1
  have hD : (D : ℚ) ≠ 0 := by exact_mod_cast hDne
  exact hj ((mul_eq_zero.mp h1).resolve_left hD)

end Work.WilC4
