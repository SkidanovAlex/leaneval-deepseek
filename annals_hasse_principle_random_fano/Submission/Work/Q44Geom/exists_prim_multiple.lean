import Mathlib
import Submission.Work.HP.Defs

namespace Work.Q44Geom

/-- Every nonzero rational vector `γ : ι → ℚ` is a positive rational multiple of a
**primitive** integer vector: there are `t : ℚ`, `0 < t`, and `l : ι → ℤ` with
`Finset.univ.gcd l = 1` and `l i = t * γ i` for all `i`.

Construction. Let `D = ∏ i, (γ i).den > 0`, so that `D * γ i ∈ ℤ` for every `i`; put
`v i = (D / (γ i).den) * (γ i).num`, so `(v i : ℚ) = D * γ i`. Since `γ ≠ 0`, some `v i ≠ 0`,
so `g := Finset.univ.gcd v ≠ 0`. Dividing `v` by `g` gives the primitive vector `l`,
and `l = (D / g) • γ` with `D / g > 0`. -/
theorem exists_prim_multiple {ι : Type*} [Fintype ι] (γ : ι → ℚ) (hγ : γ ≠ 0) :
    ∃ (t : ℚ) (l : ι → ℤ), 0 < t ∧ Work.HP.IsPrim l ∧ ∀ i, (l i : ℚ) = t * γ i := by
  classical
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hγ
  set D : ℕ := ∏ i, (γ i).den with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]; exact Finset.prod_pos (fun i _ => (γ i).den_pos)
  have hdvd : ∀ i, (γ i).den ∣ D := by
    intro i; rw [hDdef]; exact Finset.dvd_prod_of_mem (fun i => (γ i).den) (Finset.mem_univ i)
  -- integer vector `v` with `(v i : ℚ) = D * γ i`
  set v : ι → ℤ := fun i => ((D / (γ i).den : ℕ) : ℤ) * (γ i).num with hvdef
  have hv : ∀ i, (v i : ℚ) = (D : ℚ) * γ i := by
    intro i
    have h1 : (D : ℚ) = ((D / (γ i).den : ℕ) : ℚ) * ((γ i).den : ℚ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (hdvd i)]
    have h2 : γ i = ((γ i).num : ℚ) / ((γ i).den : ℚ) := (Rat.num_div_den (γ i)).symm
    have h3 : (v i : ℚ) = ((D / (γ i).den : ℕ) : ℚ) * ((γ i).num : ℚ) := by
      simp only [hvdef, Int.cast_mul, Int.cast_natCast]
    rw [h3]
    conv_rhs => rw [h2, h1]
    field_simp
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hvi0 : v i0 ≠ 0 := by
    intro h
    have hz : (v i0 : ℚ) = 0 := by rw [h]; rfl
    rw [hv i0] at hz
    exact hi0 ((mul_eq_zero.mp hz).resolve_left hDq)
  -- `g` = gcd of the coordinates of `v`, a nonzero nonnegative integer
  set g : ℤ := Finset.univ.gcd v with hgdef
  have hg_ne : g ≠ 0 := by
    rw [hgdef, Finset.gcd_ne_zero_iff]
    exact ⟨i0, Finset.mem_univ i0, hvi0⟩
  have hgnn : 0 ≤ g := Int.nonneg_of_normalize_eq_self (by rw [hgdef]; exact Finset.normalize_gcd)
  have hgpos : 0 < g := lt_of_le_of_ne hgnn (Ne.symm hg_ne)
  -- divide by `g`
  set l : ι → ℤ := fun i => v i / g with hldef
  have hgvd : ∀ i, g ∣ v i := by
    intro i; rw [hgdef]; exact Finset.gcd_dvd (Finset.mem_univ i)
  have hvgl : v = fun i => g * l i := by
    funext i
    simp only [hldef]
    rw [mul_comm g (v i / g)]
    exact (Int.ediv_mul_cancel (hgvd i)).symm
  have hnorm : normalize g = g := by rw [hgdef]; exact Finset.normalize_gcd
  have h1 : g = g * Finset.univ.gcd l := by
    calc g = Finset.univ.gcd v := hgdef
      _ = Finset.univ.gcd (fun i => g * l i) := by rw [hvgl]
      _ = normalize g * Finset.univ.gcd l := Finset.gcd_mul_left
      _ = g * Finset.univ.gcd l := by rw [hnorm]
  have hprim : Work.HP.IsPrim l := by
    rw [Work.HP.IsPrim]
    have h2 : g * Finset.univ.gcd l = g * 1 := by rw [mul_one]; exact h1.symm
    exact mul_left_cancel₀ hg_ne h2
  refine ⟨(D : ℚ) / g, l, ?_, hprim, ?_⟩
  · exact div_pos (by exact_mod_cast hDpos) (by exact_mod_cast hgpos)
  · intro i
    have hcast : (((v i / g : ℤ)) : ℚ) = (v i : ℚ) / (g : ℚ) :=
      Int.cast_div (hgvd i) (by exact_mod_cast hg_ne)
    show ((l i : ℤ) : ℚ) = (D : ℚ) / g * γ i
    simp only [hldef]
    rw [hcast, hv i]
    ring

end Work.Q44Geom
