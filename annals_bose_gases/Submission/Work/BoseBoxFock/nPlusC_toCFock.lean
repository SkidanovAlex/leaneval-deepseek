import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Finsupp.Weight
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseBoxFock.KzOpC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.nPlusC_toCFock` — the excited number operator is the total degree

`Work.BoseBoxFock.nPlusC` is the excited number operator
`n₊ = Σ_{l ∈ Excited m} a_l† a_l` on the spectator space `cfock (Excited m)`, and
`Work.BoseB4.toCFock X : ((X →₀ ℕ) →₀ ℂ) ≃ₗ[ℂ] cfock X` identifies the Fock core with
its `Finsupp` model.  The present lemma computes `n₊` in that model: on the basis vector
`β` (`β : Excited m →₀ ℕ` records the occupations of the excited modes) it is the scalar
`Finsupp.degree β`, the total number of excited quanta.  Equivalently

    `n₊ = toCFock (Σ_β c_β (deg β) • e_β)`.

## Proof

The `Finsupp`-model computation is done for an arbitrary index type `X` with `Fintype X`
and `DecidableEq X`:

* `creF_single`, `creF_annF_single_self` — on a basis vector, `creF l ∘ annF l`
  multiplies the coefficient by the occupation `β l` (the two square roots
  `√(β_l)` and `√((β_l - 1) + 1)` multiply to `β_l`; when `β_l = 0` both sides vanish,
  which is why the natural-number subtraction causes no trouble);
* `sum_cast_degree` — `Σ_l β l = deg β` after casting both sides to `ℂ`
  (`Finsupp.degree_eq_sum`);
* `sum_creF_annF_single`, `sum_creF_annF` — summing the previous identity over the modes
  gives the total degree on a basis vector, and `Finsupp.induction_linear` extends it to
  all `f` (both sides being additive in `f`).

Finally `nPlusC_toCFock_sum` rewrites `n₊ = Σ_l (1 : ℂ) • (creC l ∘ annC l)` under the
linear equivalence `toCFock` using `annC_toCFock` and its creation twin `creC_toCFock`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

variable {m : ℕ} [NeZero m]

namespace nPlusCToCFockAux

/-! ## 1. The ladder operators on the `Finsupp` model -/

variable {X : Type*} [DecidableEq X]

/-- Creation is the image of `creF` under the linear equivalence `toCFock`. -/
lemma creC_toCFock (l : X) (f : (X →₀ ℕ) →₀ ℂ) :
    creC X l (toCFock X f) = toCFock X (creF X l f) := by
  simp [Work.BoseB4.creC]

/-- `creF l` on a basis vector: it raises the `l`-occupation with weight `√(β_l + 1)`. -/
lemma creF_single (l : X) (β : X →₀ ℕ) (c : ℂ) :
    creF X l (Finsupp.single β c)
      = (c * ((Real.sqrt ((β l : ℝ) + 1) : ℝ) : ℂ)) •
          Finsupp.single (β + Finsupp.single l 1) (1 : ℂ) := by
  rw [Work.BoseB4.creF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_smul]

/-- Removing and re-adding a quantum in the mode `l` recovers `β`, provided `β_l ≠ 0`. -/
lemma tsub_add_single (l : X) (β : X →₀ ℕ) (h : β l ≠ 0) :
    (β - Finsupp.single l 1) + Finsupp.single l 1 = β := by
  ext k
  simp only [Finsupp.add_apply, Finsupp.tsub_apply]
  by_cases hk : k = l
  · subst hk
    rw [Finsupp.single_eq_same]
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h)
  · rw [Finsupp.single_eq_of_ne hk]; simp

/-- **The one-mode diagonal of the number operator** on a basis vector: `creF l ∘ annF l`
multiplies the coefficient by the `l`-occupation `β_l`. -/
lemma creF_annF_single_self (l : X) (β : X →₀ ℕ) (c : ℂ) :
    creF X l (annF X l (Finsupp.single β c))
      = c • ((((β l : ℝ) : ℂ)) • Finsupp.single β (1 : ℂ)) := by
  rw [Work.BoseB4.annF_single]
  by_cases h : β l = 0
  · simp [h]
  · have h1 : ((β - Finsupp.single l 1 : X →₀ ℕ)) l = β l - 1 := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    have h2 : (β - Finsupp.single l 1) + Finsupp.single l 1 = β := tsub_add_single l β h
    have h3 : (((β l - 1 : ℕ) : ℝ) + 1) = (β l : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h) : β l - 1 + 1 = β l)
    rw [map_smul, creF_single, h1, h2, h3, one_mul]
    rw [smul_smul, smul_smul]
    congr 1
    rw [mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg (β l))]

/-! ## 2. Summing over the modes -/

variable [Fintype X]

omit [DecidableEq X] in
/-- The occupations of a multi-index sum to its total degree. -/
lemma sum_cast_degree (β : X →₀ ℕ) :
    (∑ l : X, (((β l : ℝ) : ℂ))) = (((Finsupp.degree β : ℕ) : ℝ) : ℂ) := by
  rw [Finsupp.degree_eq_sum, Nat.cast_sum, Complex.ofReal_sum]

/-- **The number operator on a basis vector**: summing the one-mode diagonals over all
modes multiplies by the total degree. -/
lemma sum_creF_annF_single (β : X →₀ ℕ) (c : ℂ) :
    (∑ l : X, creF X l (annF X l (Finsupp.single β c)))
      = (((Finsupp.degree β : ℕ) : ℝ) : ℂ) • Finsupp.single β c := by
  simp only [creF_annF_single_self]
  rw [← Finset.smul_sum, ← Finset.sum_smul, sum_cast_degree]
  rw [smul_comm, Finsupp.smul_single_one]

/-- **The number operator on the `Finsupp` model**: `Σ_l creF l ∘ annF l` is the total
degree.  Both sides are additive in `f`, so `Finsupp.induction_linear` reduces the
identity to the basis vectors. -/
lemma sum_creF_annF (f : (X →₀ ℕ) →₀ ℂ) :
    (∑ l : X, creF X l (annF X l f))
      = f.sum (fun β c => (((Finsupp.degree β : ℕ) : ℝ) : ℂ) • Finsupp.single β c) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Finset.sum_add_distrib, hf, hg]
    rw [Finsupp.sum_add_index'
      (h := fun β c => (((Finsupp.degree β : ℕ) : ℝ) : ℂ) • Finsupp.single β c)]
    · intro β; simp
    · intro β b1 b2; rw [Finsupp.single_add, smul_add]
  | single β c =>
    rw [Finsupp.sum_single_index
      (h := fun β c => (((Finsupp.degree β : ℕ) : ℝ) : ℂ) • Finsupp.single β c) (by simp)]
    exact sum_creF_annF_single β c

end nPlusCToCFockAux

/-! ## 3. Transport along `toCFock` -/

open nPlusCToCFockAux in
/-- `nPlusC = Σ_l (1 : ℂ) • (creC l ∘ annC l)` transported to the `Finsupp` model. -/
lemma nPlusC_toCFock_sum (f : (Excited m →₀ ℕ) →₀ ℂ) :
    nPlusC (m := m) (toCFock (Excited m) f)
      = toCFock (Excited m)
          (∑ l : Excited m, creF (Excited m) l (annF (Excited m) l f)) := by
  have hcongr : ∀ l : Excited m,
      creC (Excited m) l (annC (Excited m) l (toCFock (Excited m) f))
        = toCFock (Excited m) (creF (Excited m) l (annF (Excited m) l f)) := by
    intro l
    rw [annC_toCFock, creC_toCFock]
  simp only [nPlusC, LinearMap.sum_apply, LinearMap.comp_apply, one_smul]
  rw [Finset.sum_congr rfl (fun l _ => hcongr l), ← map_sum]

open nPlusCToCFockAux in
theorem nPlusC_toCFock {m : ℕ} [NeZero m] (f : (Work.BoseB4.Excited m →₀ ℕ) →₀ ℂ) :
    Work.BoseBoxFock.nPlusC (m := m)
        (Work.BoseB4.toCFock (Work.BoseB4.Excited m) f)
      = Work.BoseB4.toCFock (Work.BoseB4.Excited m)
          (f.sum (fun (β : Work.BoseB4.Excited m →₀ ℕ) c =>
            (((Finsupp.degree β : ℕ) : ℝ) : ℂ) • Finsupp.single β c)) := by
  rw [nPlusC_toCFock_sum]
  congr 1
  exact sum_creF_annF f

end Work.BoseBoxFock
