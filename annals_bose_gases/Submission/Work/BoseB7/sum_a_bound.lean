import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseB7.FockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.sum_a_bound` — the weighted `a`-sum is bounded by the `a`-energies

`smallbox`-layer bookkeeping (FS §10, the estimates around `thm:Control3Q`): a
weighted sum `Σ_i c_i a_i` of annihilation operators is controlled, in the Fock
form `bp`, by the *weighted sum of the individual energies* `Σ_i |c_i| ⟨a_i f, a_i f⟩`
with the total weight `Σ_i |c_i|` in front.

The content is the standard "weighted Cauchy–Schwarz" for a symmetric positive
semidefinite bilinear form: writing `u_i = a_i f`, `B_{ij} = bp u_i u_j` and
`A_i = |c_i|`, one has

* (pair bound) `|B_{ij}| ≤ (B_{ii} + B_{jj})/2`, which follows from
  `0 ≤ bp (u_i ± u_j) (u_i ± u_j)`;
* (bilinearity) `bp (Σ_i c_i u_i) (Σ_i c_i u_i) = Σ_{i,j} c_i c_j B_{ij}`;
* (summation) `Σ_{i,j} A_i A_j (B_{ii}+B_{jj})/2 = (Σ_i A_i)(Σ_j A_j B_{jj})`.

No Cauchy–Schwarz square roots, and no definiteness of `bp` is needed: only
symmetry and positive semidefiniteness.

## Contents

* `SumABound.bp_abs_le` — the pair bound `|⟨u,v⟩| ≤ (⟨u,u⟩+⟨v,v⟩)/2`.
* `SumABound.bp_sum_sum` — the bilinear expansion on finite sums.
* `SumABound.weighted_amgm` — the double-sum identity above.
* `sum_a_bound` — the requested bound.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

namespace SumABound

/-- Pair bound (disguised Cauchy–Schwarz) for a symmetric positive semidefinite
bilinear form: `2|⟨u,v⟩| ≤ ⟨u,u⟩ + ⟨v,v⟩`, obtained by expanding
`0 ≤ ⟨u±v,u±v⟩`.  Only `bp_symm` and `bp_nonneg` are used. -/
lemma bp_abs_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (u v : F.H) :
    |F.bp u v| ≤ (F.bp u u + F.bp v v) / 2 := by
  have h1 : 0 ≤ F.bp (u + v) (u + v) := F.bp_nonneg _
  have h2 : 0 ≤ F.bp (u - v) (u - v) := F.bp_nonneg _
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at h1 h2
  rw [F.bp_symm v u] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- Bilinearity of the Fock form on a finite sum:
`⟨Σ_i w_i u_i, Σ_j w_j u_j⟩ = Σ_{i,j} w_i w_j ⟨u_i, u_j⟩`. -/
lemma bp_sum_sum {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (s : Finset Mode) (w : Mode → ℝ) (u : Mode → F.H) :
    F.bp (∑ i ∈ s, w i • u i) (∑ i ∈ s, w i • u i) =
      ∑ i ∈ s, ∑ j ∈ s, (w i * w j) * F.bp (u i) (u j) := by
  have h1 : (F.bp (∑ i ∈ s, w i • u i)) = ∑ i ∈ s, w i • F.bp (u i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
  rw [h1, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LinearMap.smul_apply, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- The symmetric pairing of the doubled sum: for nonnegative weights `A` and a
diagonal `B`, `Σ_{i,j} A_i A_j (B_i + B_j)/2 = (Σ_i A_i)(Σ_i A_i B_i)`. -/
lemma weighted_amgm {Mode : Type*} (s : Finset Mode) (A B : Mode → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, A i * A j * ((B i + B j) / 2)) =
      (∑ i ∈ s, A i) * (∑ i ∈ s, A i * B i) := by
  have hsplit : (∑ i ∈ s, ∑ j ∈ s, A i * A j * ((B i + B j) / 2)) =
      ((∑ i ∈ s, ∑ j ∈ s, A i * A j * B i) +
        (∑ i ∈ s, ∑ j ∈ s, A i * A j * B j)) / 2 := by
    have h2 : (∑ i ∈ s, ∑ j ∈ s, A i * A j * ((B i + B j) / 2)) =
        (∑ i ∈ s, ∑ j ∈ s, (A i * A j * B i / 2 + A i * A j * B j / 2)) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring
    rw [h2]
    simp only [Finset.sum_add_distrib, ← Finset.sum_div]
    ring
  have hD1 : (∑ i ∈ s, ∑ j ∈ s, A i * A j * B i) =
      (∑ i ∈ s, A i * B i) * (∑ j ∈ s, A j) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  have hD2 : (∑ i ∈ s, ∑ j ∈ s, A i * A j * B j) =
      (∑ i ∈ s, A i) * (∑ j ∈ s, A j * B j) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  rw [hsplit, hD1, hD2]
  ring

end SumABound

theorem sum_a_bound {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (c : Mode → ℝ) (f : F.H) :
    F.bp ((∑ i : Mode, (c i) • F.a i) f) ((∑ i : Mode, (c i) • F.a i) f) ≤
      (∑ i : Mode, |c i|) * (∑ i : Mode, |c i| * F.bp (F.a i f) (F.a i f)) := by
  have hval : (∑ i : Mode, (c i) • F.a i) f = ∑ i : Mode, (c i) • F.a i f := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [hval]
  rw [SumABound.bp_sum_sum F Finset.univ c (fun i => F.a i f)]
  have hterm : ∀ i j : Mode,
      c i * c j * F.bp (F.a i f) (F.a j f) ≤
        |c i| * |c j| *
          ((F.bp (F.a i f) (F.a i f) + F.bp (F.a j f) (F.a j f)) / 2) := by
    intro i j
    have h := SumABound.bp_abs_le F (F.a i f) (F.a j f)
    calc c i * c j * F.bp (F.a i f) (F.a j f)
        ≤ |c i * c j * F.bp (F.a i f) (F.a j f)| := le_abs_self _
      _ = |c i| * |c j| * |F.bp (F.a i f) (F.a j f)| := by rw [abs_mul, abs_mul]
      _ ≤ |c i| * |c j| *
            ((F.bp (F.a i f) (F.a i f) + F.bp (F.a j f) (F.a j f)) / 2) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
        (c i * c j) * F.bp (F.a i f) (F.a j f)
      ≤ ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
          |c i| * |c j| *
            ((F.bp (F.a i f) (F.a i f) + F.bp (F.a j f) (F.a j f)) / 2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = (∑ i : Mode, |c i|) * (∑ i : Mode, |c i| * F.bp (F.a i f) (F.a i f)) :=
        SumABound.weighted_amgm Finset.univ (fun i => |c i|)
          (fun i => F.bp (F.a i f) (F.a i f))

end Work.BoseB7
