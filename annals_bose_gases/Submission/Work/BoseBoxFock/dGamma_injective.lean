import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseB4.AntiNormal
import Submission.Work.BoseB4.DGamma_diag
import Submission.Work.BoseB4.DGamma_one
import Submission.Work.BoseB4.DGamma_quadform
import Submission.Work.BoseB4.Kafz_lower_bound_H2nd
import Submission.Work.BoseB4.Kafz_lower_bound_pointwise
import Submission.Work.BoseB4.TildeDataInst
import Submission.Work.BoseB4.a0_comp_a0d_sq
import Submission.Work.BoseB4.annC_creC_ccr
import Submission.Work.BoseB4.dGamma_diag_nonneg
import Submission.Work.BoseB4.monoOp_11_00_numOp
import Submission.Work.BoseB4.monoOp_lift_basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dGamma_injective` — the second quantisation `T ↦ dΓ(T)` is injective

On the coordinate (mode) Fock space `Work.BoseB4.RealFock m = (Fin m →₀ ℕ) →₀ ℝ` the
second quantisation of a one-particle operator
`T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)` is (`Work.BoseB4.DGamma`)

    `dGamma m T = ∑_{i j} (T e_j)_i · a_i† a_j`,   `e_j = Work.BoseB4.evec m j`.

Because `T ↦ dGamma m T` is injective, an identity of *operators* of this shape
determines the one-particle operator: this is what lets the box-side rows of FS
`lem:2ndQuand` (the kinetic word `∑_j 𝒯'_j`, the condensate word `a₀†a₀`, …) be read
back as identities of one-body operators.

## The proof

`dGamma` acts on the **one-particle sector** as `T` itself: for the one-particle
state `oneF m j` (occupation `1` in mode `j`, which is `Work.BoseB4.cre m j` applied
to the Fock vacuum `vacF m`) one has, expanding the double sum and using
`a_i oneF m j = δ_{ij} · 1` (`ann_oneF`),

    `(dGamma m T) (oneF m j) = ∑_i (T e_j)_i · oneF m i`     (`dGamma_oneF`).

Applying the Bombieri form `bomb m` against `oneF m i` — where
`bomb m (oneF m l) (oneF m i) = δ_{li}` (`bomb_oneF`), so that
`bomb m (oneF m l) (∑_i c_i • oneF m i) = c_l` (`bomb_oneF_sum`) — extracts the
matrix element:

    `bomb m (oneF m i) ((dGamma m T) (oneF m j)) = (T e_j) i`.

Hence `dGamma m T = dGamma m T'` forces all matrix elements to agree, and the
`e_j = Pi.single j 1` (`Pi.basisFun ℝ (Fin m)`) are a basis of `Fin m → ℝ`, so
`T = T'`.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace Work.BoseBoxFock

open Work.BoseB4

/-- The Fock vacuum in the monomial-coefficient model: the constant monomial. -/
private noncomputable def vacF (m : ℕ) : Work.BoseB4.RealFock m := Finsupp.single 0 (1 : ℝ)

/-- The **one-particle state** of mode `i`: occupation `1` in mode `i`, `0` elsewhere. -/
private noncomputable def oneF (m : ℕ) (i : Fin m) : Work.BoseB4.RealFock m :=
  Finsupp.single (Work.BoseB4.e m i) (1 : ℝ)

/-- The multi-index weight of a one-particle multi-index is `1` (all factorials are `0!`
or `1!`). -/
private lemma mfac_e (m : ℕ) (l : Fin m) : Work.BoseB4.mfac (Work.BoseB4.e m l) = 1 := by
  rw [Work.BoseB4.mfac, Work.BoseB4.e, Finsupp.prod_single_index]
  · simp
  · simp

/-- The one-particle multi-indices are distinct: `e i = e l ↔ i = l`. -/
private lemma e_eq_iff (m : ℕ) (i l : Fin m) :
    Work.BoseB4.e m i = Work.BoseB4.e m l ↔ i = l := by
  rw [Work.BoseB4.e, Work.BoseB4.e]
  exact Finsupp.single_left_inj one_ne_zero

/-- `ann m j (oneF m k) = δ_{jk} · (vacuum)`: annihilating mode `j` of the one-particle
state of mode `k` leaves the vacuum iff `j = k`, and `0` otherwise. -/
private lemma ann_oneF (m : ℕ) (j k : Fin m) :
    Work.BoseB4.ann m j (oneF m k) = (if j = k then (1 : ℝ) else 0) • vacF m := by
  rw [Work.BoseB4.ann_eq_sum, oneF, Finsupp.sum_single_index]
  · by_cases h : j = k
    · rw [if_pos h]
      have h1 : (Work.BoseB4.e m k) j = 1 := by
        rw [Work.BoseB4.e, Finsupp.single_apply]; simp [h]
      have hsub : Work.BoseB4.e m k - Work.BoseB4.e m j = (0 : Fin m →₀ ℕ) := by
        rw [h]; ext x; simp [Work.BoseB4.e]
      rw [h1, hsub]
      simp [vacF]
    · rw [if_neg h]
      have hz : (Work.BoseB4.e m k) j = 0 := by
        rw [Work.BoseB4.e, Finsupp.single_apply, if_neg (Ne.symm h)]
      rw [hz]
      simp
  · simp

/-- `cre` on the vacuum produces the one-particle state of that mode. -/
private lemma cre_vacF (m : ℕ) (i : Fin m) : Work.BoseB4.cre m i (vacF m) = oneF m i := by
  rw [vacF, oneF, Work.BoseB4.cre_single]
  simp

/-- The two-letter word `a_i† a_{j'}` on the one-particle state of mode `j`: it produces
the one-particle state of mode `i` iff `j' = j`. -/
private lemma cre_ann_oneF (m : ℕ) (i j' j : Fin m) :
    ((Work.BoseB4.cre m i).comp (Work.BoseB4.ann m j')) (oneF m j)
      = if j' = j then oneF m i else (0 : Work.BoseB4.RealFock m) := by
  rw [LinearMap.comp_apply, ann_oneF, map_smul, cre_vacF]
  by_cases h : j' = j
  · rw [if_pos h, if_pos h, one_smul]
  · rw [if_neg h, if_neg h, zero_smul]

/-- **`dGamma` on the one-particle sector is the one-particle operator**: the double sum
`∑_{i j'} (T e_{j'})_i · a_i† a_{j'}` collapses to the matrix elements of `T` in the
column `j`. -/
private lemma dGamma_oneF (m : ℕ) (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (j : Fin m) :
    (Work.BoseB4.dGamma m T) (oneF m j)
      = ∑ i : Fin m, (T (Work.BoseB4.evec m j) i) • oneF m i := by
  rw [Work.BoseB4.dGamma]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, cre_ann_oneF]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    rw [if_neg hj']
    simp
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The Bombieri form of two one-particle states is their Kronecker delta. -/
private lemma bomb_oneF (m : ℕ) (l i : Fin m) :
    Work.BoseB4.bomb m (oneF m l) (oneF m i) = if i = l then (1 : ℝ) else 0 := by
  rw [oneF, Work.BoseB4.bomb_single, mfac_e, mul_one, one_mul]
  rw [oneF, Finsupp.single_apply]
  by_cases h : i = l
  · rw [if_pos h, if_pos ((e_eq_iff m i l).mpr h)]
  · rw [if_neg h, if_neg (fun hh => h ((e_eq_iff m i l).mp hh))]

/-- Pairing against `oneF m l` reads off the `l`-th coefficient of a one-particle vector. -/
private lemma bomb_oneF_sum (m : ℕ) (l : Fin m) (c : Fin m → ℝ) :
    Work.BoseB4.bomb m (oneF m l) (∑ i : Fin m, c i • oneF m i) = c l := by
  rw [map_sum]
  simp only [map_smul, bomb_oneF, smul_eq_mul]
  rw [Finset.sum_eq_single l]
  · simp
  · intro i _ hi
    rw [if_neg hi]
    ring
  · intro h; exact absurd (Finset.mem_univ l) h

/-- **The second quantisation is injective**: two one-particle operators with the same
second quantisation are equal.

`dGamma` acts on the one-particle sector as the operator itself (`dGamma_oneF`), so the
pairing `bomb m (oneF m i)` against `(dGamma m T) (oneF m j)` is exactly the matrix
element `(T e_j) i`; an operator identity of this shape is therefore an identity of all
matrix elements, and `e_j = Pi.single j 1` is a basis of `Fin m → ℝ`. -/
theorem dGamma_injective {m : ℕ} {T T' : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)}
    (h : Work.BoseB4.dGamma m T = Work.BoseB4.dGamma m T') : T = T' := by
  apply Module.Basis.ext (Pi.basisFun ℝ (Fin m))
  intro j
  rw [Pi.basisFun_apply]
  show T (Work.BoseB4.evec m j) = T' (Work.BoseB4.evec m j)
  funext i
  have hj : (Work.BoseB4.dGamma m T) (oneF m j) = (Work.BoseB4.dGamma m T') (oneF m j) := by
    rw [h]
  rw [dGamma_oneF, dGamma_oneF] at hj
  have h2 := congrArg (fun v => Work.BoseB4.bomb m (oneF m i) v) hj
  simp only [bomb_oneF_sum] at h2
  exact h2

end Work.BoseBoxFock
