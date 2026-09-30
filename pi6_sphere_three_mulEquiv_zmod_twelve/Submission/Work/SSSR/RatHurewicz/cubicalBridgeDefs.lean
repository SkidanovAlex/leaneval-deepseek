import Mathlib
import Submission.Work.RatHurewicz.CubicalDefs
import Submission.Work.SSSR.Stems.Cubical.CubeFace
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.RatHurewicz
variable {R : Type} [CommRing R] [Nontrivial R]

open scoped unitInterval Topology Simplicial
open CategoryTheory AlgebraicTopology
namespace Work.SSSR.RatHurewicz

open Work.SSSR.Stems.Cubical
noncomputable section

/-- The `i`-th coordinate of a point of the cube, packaged as a real number, with the convention
`0` outside the range of the coordinates. -/
def tval (n : ℕ) (t : IC n) (i : ℕ) : ℝ := if h : i < n then (t ⟨i, h⟩ : ℝ) else 0

theorem tval_of_lt {n : ℕ} (t : IC n) {i : ℕ} (h : i < n) :
    tval n t i = (t ⟨i, h⟩ : ℝ) := by
  simp only [tval, dif_pos h]

theorem tval_of_le {n : ℕ} (t : IC n) {i : ℕ} (h : ¬ i < n) : tval n t i = 0 := by
  simp only [tval, dif_neg h]

theorem tval_nonneg {n : ℕ} (t : IC n) (i : ℕ) : 0 ≤ tval n t i := by
  rcases lt_or_ge i n with h | h
  · rw [tval_of_lt t h]; exact_mod_cast (t ⟨i, h⟩).2.1
  · rw [tval_of_le t (not_lt.mpr h)]

theorem tval_le_one {n : ℕ} (t : IC n) (i : ℕ) : tval n t i ≤ 1 := by
  rcases lt_or_ge i n with h | h
  · rw [tval_of_lt t h]; exact_mod_cast (t ⟨i, h⟩).2.2
  · rw [tval_of_le t (not_lt.mpr h)]; norm_num

theorem continuous_tval (n i : ℕ) : Continuous fun t : IC n => tval n t i := by
  rcases lt_or_ge i n with h | h
  · simp only [tval_of_lt _ h]
    have hc : Continuous fun p : IC n => p ⟨i, h⟩ := continuous_apply _
    exact continuous_subtype_val.comp hc
  · simp only [tval_of_le _ (not_lt.mpr h)]
    exact continuous_const

/-- The `k`-th partial product `∏_{i<k} t_i` of the coordinates of a cube point, as a real
number. -/
noncomputable def Pnat (n : ℕ) (t : IC n) (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, tval n t i

theorem Pnat_zero {n : ℕ} (t : IC n) : Pnat n t 0 = 1 := by
  simp [Pnat]

theorem Pnat_nonneg {n : ℕ} (t : IC n) (k : ℕ) : 0 ≤ Pnat n t k :=
  Finset.prod_nonneg fun i _ => tval_nonneg t i

theorem Pnat_succ {n : ℕ} (t : IC n) (k : ℕ) : Pnat n t (k + 1) = Pnat n t k * tval n t k :=
  Finset.prod_range_succ _ _

theorem continuous_Pnat (n k : ℕ) : Continuous fun t : IC n => Pnat n t k := by
  unfold Pnat
  exact continuous_finsetProd _ fun i _ => continuous_tval n i

/-- The `j`-th coordinate of the image of `t` in the standard simplex: the cumulative coordinate
`(∏_{i<j} t_i)·(1 - t_j)` (with `t_j := 0` for `j ≥ n`). -/
noncomputable def Hfun (n : ℕ) (t : IC n) (j : Fin (n + 1)) : ℝ :=
  Pnat n t j.1 * (1 - tval n t j.1)

theorem continuous_Hfun (n : ℕ) (j : Fin (n + 1)) :
    Continuous fun t : IC n => Hfun n t j :=
  (continuous_Pnat n j.1).mul (continuous_const.sub (continuous_tval n j.1))

theorem sum_fin_eq_sum_range (n : ℕ) (f : ℕ → ℝ) :
    (∑ j : Fin (n + 1), f j.1) = ∑ k ∈ Finset.range (n + 1), f k :=
  Fin.sum_univ_eq_sum_range f (n + 1)

theorem Hfun_eq (n : ℕ) (t : IC n) (j : Fin (n + 1)) :
    Hfun n t j = Pnat n t j.1 - Pnat n t (j.1 + 1) := by
  rw [Hfun, Pnat_succ]; ring

theorem sum_Hfun (n : ℕ) (t : IC n) : ∑ j : Fin (n + 1), Hfun n t j = 1 := by
  have h1 : ∀ j : Fin (n + 1), Hfun n t j = Pnat n t j.1 - Pnat n t (j.1 + 1) :=
    fun j => Hfun_eq n t j
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  rw [Finset.sum_sub_distrib]
  rw [sum_fin_eq_sum_range n (fun k => Pnat n t k),
    sum_fin_eq_sum_range n (fun k => Pnat n t (k + 1))]
  rw [← Finset.sum_sub_distrib]
  have hneg : (∑ k ∈ Finset.range (n + 1), (Pnat n t k - Pnat n t (k + 1)))
      = -(∑ k ∈ Finset.range (n + 1), (Pnat n t (k + 1) - Pnat n t k)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hneg, Finset.sum_range_sub (fun k => Pnat n t k) (n + 1)]
  have hlast : Pnat n t (n + 1) = 0 := by
    rw [Pnat_succ, tval_of_le t (by omega), mul_zero]
  rw [hlast, Pnat_zero]
  ring

/-- **The cumulative-coordinate map** `I^n → Δ^n`,
`t ↦ ((∏_{i<j} t_i)(1 - t_j))_{j : Fin (n+1)}`. -/
noncomputable def H (n : ℕ) : C(IC n, stdSimplex ℝ (Fin (n + 1))) where
  toFun t := ⟨fun j => Hfun n t j,
    ⟨fun j => mul_nonneg (Pnat_nonneg t _) (sub_nonneg.mpr (tval_le_one t _)),
      sum_Hfun n t⟩⟩
  continuous_toFun := Continuous.subtype_mk (continuous_pi fun j => continuous_Hfun n j) _

@[simp]
theorem H_apply (n : ℕ) (t : IC n) (j : Fin (n + 1)) : H n t j = Hfun n t j := rfl

end

end Work.SSSR.RatHurewicz
