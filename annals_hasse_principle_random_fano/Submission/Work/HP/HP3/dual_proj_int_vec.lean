import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Lat.prim_bezout

namespace Work.HP.HP3

open Finset

/-- For primitive `x : Fin (n+1) → ℤ` and `u` in the dual of `Λ_x = latOrth x`, there is an
*integer* vector `w` whose orthogonal projection onto `x^⊥` is `u`, i.e. `toR w - u ∈ ℝ·(toR x)`.

Route (paper, "one vector bound").  For every `i j` the integer vector
`y_{ij} = x i • e_j - x j • e_i` lies in `latOrth x`, so `u` pairing against it is an integer:
`(c_{ij} : ℝ) = (x i : ℝ) * u j - (x j : ℝ) * u i` for some `c_{ij} : ℤ`.  Bézout
(`Work.HP.Lat.prim_bezout`) gives `α : Fin (n+1) → ℤ` with `∑ i, α i * x i = 1`; set
`w j = ∑ i, α i * c i j` and `s = ∑ i, (α i : ℝ) * u i`.  Then
`(w j : ℝ) = (∑ α i x i) * u j - s * x j = u j - s * x j`. -/
theorem dual_proj_int_vec (n : ℕ) (x : Fin (n + 1) → ℤ) (hx : IsPrim x)
    (u : Fin (n + 1) → ℝ) (hu : u ∈ dualLat (realify (latOrth x))) :
    ∃ w : Fin (n + 1) → ℤ, ∃ s : ℝ, toR w = u - s • toR x := by
  classical
  -- Bézout coefficients for the primitive integer vector `x`.
  obtain ⟨α, hα⟩ := Work.HP.Lat.prim_bezout x hx
  -- The vector `x i • e_j - x j • e_i = single j (x i) - single i (x j)` lies in `latOrth x`,
  -- so its pairing with `u` is an integer `c i j`.
  have hpair : ∀ i j : Fin (n + 1),
      ∃ c : ℤ, (c : ℝ) = (x i : ℝ) * u j - (x j : ℝ) * u i := by
    intro i j
    have hmem : toR ((Pi.single j (x i) : Fin (n + 1) → ℤ) - Pi.single i (x j))
        ∈ realify (latOrth x) := by
      refine Submodule.mem_map.mpr
        ⟨(Pi.single j (x i) : Fin (n + 1) → ℤ) - Pi.single i (x j), ?_, rfl⟩
      rw [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply]
      simp only [Pi.sub_apply, smul_eq_mul]
      have h1 : (∑ m, (Pi.single j (x i) : Fin (n + 1) → ℤ) m * x m) = x i * x j := by
        simp [Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
      have h2 : (∑ m, (Pi.single i (x j) : Fin (n + 1) → ℤ) m * x m) = x j * x i := by
        simp [Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
      rw [Finset.sum_congr rfl (fun m _ => sub_mul _ _ _), Finset.sum_sub_distrib, h1, h2]
      ring
    obtain ⟨c, hc⟩ := hu.2 _ hmem
    refine ⟨c, ?_⟩
    have h1 : (∑ m, u m * ((Pi.single j (x i) : Fin (n + 1) → ℤ) m : ℝ))
        = (x i : ℝ) * u j := by
      rw [Finset.sum_congr rfl (fun m _ => mul_comm _ _)]
      simp [Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
    have h2 : (∑ m, u m * ((Pi.single i (x j) : Fin (n + 1) → ℤ) m : ℝ))
        = (x j : ℝ) * u i := by
      rw [Finset.sum_congr rfl (fun m _ => mul_comm _ _)]
      simp [Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
    rw [← hc]
    simp only [toR, Pi.sub_apply, Int.cast_sub]
    rw [Finset.sum_congr rfl (fun m _ => mul_sub _ _ _), Finset.sum_sub_distrib, h1, h2]
  choose c hc using hpair
  refine ⟨fun j => ∑ i, α i * c i j, ∑ i, (α i : ℝ) * u i, ?_⟩
  funext j
  have hkey : (((∑ i, α i * c i j : ℤ)) : ℝ)
      = u j - (∑ i, (α i : ℝ) * u i) * (x j : ℝ) := by
    have hcast : (((∑ i, α i * c i j : ℤ)) : ℝ) = ∑ i, (α i : ℝ) * (c i j : ℝ) := by
      push_cast
      rfl
    rw [hcast]
    calc ∑ i, (α i : ℝ) * (c i j : ℝ)
        = ∑ i, (α i : ℝ) * ((x i : ℝ) * u j - (x j : ℝ) * u i) :=
          Finset.sum_congr rfl (fun i _ => by rw [hc i j])
      _ = ∑ i, ((α i : ℝ) * (x i : ℝ) * u j - (α i : ℝ) * u i * (x j : ℝ)) :=
          Finset.sum_congr rfl (fun i _ => by ring)
      _ = (∑ i, (α i : ℝ) * (x i : ℝ) * u j) - ∑ i, (α i : ℝ) * u i * (x j : ℝ) := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ i, (α i : ℝ) * (x i : ℝ)) * u j - (∑ i, (α i : ℝ) * u i) * (x j : ℝ) := by
          rw [Finset.sum_mul, Finset.sum_mul]
    have hBez : (∑ i, (α i : ℝ) * (x i : ℝ)) = 1 := by
      have hcast' : (((∑ i, α i * x i : ℤ)) : ℝ) = ∑ i, (α i : ℝ) * (x i : ℝ) := by
        push_cast
        rfl
      rw [← hcast', hα, Int.cast_one]
    rw [hBez, one_mul]
  simpa [toR, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hkey

end Work.HP.HP3
