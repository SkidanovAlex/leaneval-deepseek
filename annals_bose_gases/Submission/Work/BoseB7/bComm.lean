import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.LinearAlgebra.Finsupp.LSum
import Submission.Work.BoseB7.boseDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.bComm` — creation operators commute, and so do annihilation operators

For the honest bosonic Fock space `boseH Mode` of `Work.BoseB7.boseDefs`
(`Mode →₀ ℕ` occupation vectors, real finitely supported states), the ladder
operators satisfy

* `bAnn i ∘ₗ bAnn j = bAnn j ∘ₗ bAnn i`,
* `bCre i ∘ₗ bCre j = bCre j ∘ₗ bCre i`.

These are the "trivial" halves of the canonical commutation relations; the
non-trivial one (`[bAnn i, bCre j] = δ_{ij}`) is `Work.BoseB7.bCCR`.

## Strategy

Both operators are built by `Finsupp.lsum`, so their action on the standard
basis vectors `|m⟩ = Finsupp.single m 1` of `boseH Mode` is immediate from
`Finsupp.lsum_single`:

* `bAnn i |m⟩ = √(m i) • |dec i m⟩`
  (`bComm_bAnn_single`; more generally `bAnn i (single m c) = (c·√(m i)) • |dec i m⟩`),
* `bCre i |m⟩ = √(m i + 1) • |inc i m⟩`
  (`bComm_bCre_single`).

Since the `|m⟩` form a basis, it suffices to check the identities there
(`bComm_ext_single`, proved by `Finsupp.induction` — pure linear algebra).
On a basis vector the two sides differ only by the order in which the two
orthogonal *index* moves `dec i`, `dec j` (resp. `inc i`, `inc j`) are applied,
which the combinatorial lemmas `dec_dec_comm` / `inc_inc_comm` of `boseDefs`
identify, and by the order of the two commuting *real* weights `√(m i)`, `√(m j)`
(trivial when `i = j`, and `occ_dec_ne` / `occ_inc_ne` when `i ≠ j`).
-/

noncomputable section

namespace Work.BoseB7

/-! ## Two pure-linear-algebra ingredients -/

/-- Two `ℝ`-linear endomorphisms of `α →₀ ℝ` that agree on the standard basis
vectors `Finsupp.single a 1` are equal.  (Pure linear algebra: those vectors
span, and `Finsupp.induction` writes every element as a sum of coefficient
multiples of them.) -/
lemma bComm_ext_single {α : Type*} {f g : (α →₀ ℝ) →ₗ[ℝ] (α →₀ ℝ)}
    (h : ∀ a : α, f (Finsupp.single a 1) = g (Finsupp.single a 1)) : f = g := by
  refine LinearMap.ext fun Ψ => ?_
  induction Ψ using Finsupp.induction with
  | zero => simp
  | single_add a b Ψ' _ _ ih =>
      have hab : Finsupp.single a b = b • Finsupp.single a (1 : ℝ) := by
        rw [Finsupp.smul_single]; simp
      rw [hab, map_add, map_add, map_smul, map_smul, h a, ih]

/-- `bAnn i` on a basis vector: `bAnn i (|m⟩ · c) = (c √(m i)) • |dec i m⟩`. -/
lemma bComm_bAnn_single {Mode : Type*} (i : Mode) (a : occIdx Mode) (c : ℝ) :
    bAnn i (Finsupp.single a c) = (c * Real.sqrt (occ i a)) • Finsupp.single (dec i a) 1 := by
  simp only [bAnn, Finsupp.lsum_single, Finsupp.lsingle_apply, LinearMap.smul_apply]
  simp [Finsupp.smul_single, mul_comm]

/-- `bCre i` on a basis vector: `bCre i (|m⟩ · c) = (c √(m i + 1)) • |inc i m⟩`. -/
lemma bComm_bCre_single {Mode : Type*} (i : Mode) (a : occIdx Mode) (c : ℝ) :
    bCre i (Finsupp.single a c) = (c * Real.sqrt (occ i a + 1)) • Finsupp.single (inc i a) 1 := by
  simp only [bCre, Finsupp.lsum_single, Finsupp.lsingle_apply, LinearMap.smul_apply]
  simp [Finsupp.smul_single, mul_comm]

/-! ## The two identities on basis vectors -/

/-- `bAnn i` and `bAnn j` commute on the basis vectors `|m⟩ = single m 1`. -/
lemma bComm_ann_double {Mode : Type*} (i j : Mode) (a : occIdx Mode) :
    bAnn i (bAnn j (Finsupp.single a 1)) = bAnn j (bAnn i (Finsupp.single a 1)) := by
  have hL : bAnn i (bAnn j (Finsupp.single a 1))
      = (Real.sqrt (occ j a) * Real.sqrt (occ i (dec j a))) •
          Finsupp.single (dec i (dec j a)) 1 := by
    simp only [bComm_bAnn_single, one_mul, map_smul, smul_smul]
  have hR : bAnn j (bAnn i (Finsupp.single a 1))
      = (Real.sqrt (occ i a) * Real.sqrt (occ j (dec i a))) •
          Finsupp.single (dec j (dec i a)) 1 := by
    simp only [bComm_bAnn_single, one_mul, map_smul, smul_smul]
  have hcoef : Real.sqrt (occ j a) * Real.sqrt (occ i (dec j a))
      = Real.sqrt (occ i a) * Real.sqrt (occ j (dec i a)) := by
    by_cases hij : i = j
    · subst hij; rfl
    · rw [occ_dec_ne hij a, occ_dec_ne (Ne.symm hij) a, mul_comm]
  rw [hL, hR, ← dec_dec_comm i j a, hcoef]

/-- `bCre i` and `bCre j` commute on the basis vectors `|m⟩ = single m 1`. -/
lemma bComm_cre_double {Mode : Type*} (i j : Mode) (a : occIdx Mode) :
    bCre i (bCre j (Finsupp.single a 1)) = bCre j (bCre i (Finsupp.single a 1)) := by
  have hL : bCre i (bCre j (Finsupp.single a 1))
      = (Real.sqrt (occ j a + 1) * Real.sqrt (occ i (inc j a) + 1)) •
          Finsupp.single (inc i (inc j a)) 1 := by
    simp only [bComm_bCre_single, one_mul, map_smul, smul_smul]
  have hR : bCre j (bCre i (Finsupp.single a 1))
      = (Real.sqrt (occ i a + 1) * Real.sqrt (occ j (inc i a) + 1)) •
          Finsupp.single (inc j (inc i a)) 1 := by
    simp only [bComm_bCre_single, one_mul, map_smul, smul_smul]
  have hcoef : Real.sqrt (occ j a + 1) * Real.sqrt (occ i (inc j a) + 1)
      = Real.sqrt (occ i a + 1) * Real.sqrt (occ j (inc i a) + 1) := by
    by_cases hij : i = j
    · subst hij; rfl
    · rw [occ_inc_ne hij a, occ_inc_ne (Ne.symm hij) a, mul_comm]
  rw [hL, hR, ← inc_inc_comm i j a, hcoef]

theorem bComm {Mode : Type*} (i j : Mode) :
    (Work.BoseB7.bAnn i ∘ₗ Work.BoseB7.bAnn j = Work.BoseB7.bAnn j ∘ₗ Work.BoseB7.bAnn i)
      ∧ (Work.BoseB7.bCre i ∘ₗ Work.BoseB7.bCre j
          = Work.BoseB7.bCre j ∘ₗ Work.BoseB7.bCre i) := by
  constructor
  · apply bComm_ext_single
    intro a
    exact bComm_ann_double i j a
  · apply bComm_ext_single
    intro a
    exact bComm_cre_double i j a

end Work.BoseB7
