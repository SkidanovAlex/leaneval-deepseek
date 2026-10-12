import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.CharP.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finsupp.Order
import Submission.Work.BoseB7.boseDefs
import Submission.Work.BoseB7.l2FormDef
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.bAdjoint` — the creation operator is the ℓ²-adjoint of annihilation

With the ℓ² form `Work.BoseB7.l2Form (occIdx Mode) f g = ∑_m f m * g m` on the
occupation-number Fock space `boseH Mode = occIdx Mode →₀ ℝ`, the creation
operator `bCre i = a_i†` (`bCre i |m⟩ = √(m i + 1)|inc i m⟩`) is the adjoint of
the annihilation operator `bAnn i = a_i` (`bAnn i |m⟩ = √(m i)|dec i m⟩`):

`⟨a_i† f, g⟩ = ⟨f, a_i g⟩`.

The proof is a two-step basis reduction:

* `bAdjoint_ss` is the identity on basis vectors `f = |a⟩·b`, `g = |m⟩·d`.  It
  reduces to the Kronecker-delta identity
  `√(occ i a + 1)·δ_{inc i a, m} = √(occ i m)·δ_{a, dec i m}` (`bAdjoint_key`),
  whose only content is the occupation-number arithmetic of `inc`/`dec`:
  `m = inc i a` forces `dec i m = a` and `occ i m = occ i a + 1`, while in the
  remaining case, where `a = dec i m`, the truncated subtraction has already
  saturated (`occ i m = 0`) so that both coefficients vanish.
* Bilinearity then extends the identity to all `f`, and a second basis
  reduction (via `Finsupp.lhom_ext`) extends it to all `g`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

/-- The ℓ² form against a basis vector, in the first argument:
`l2Form ι (single p c) g = c * g p`. -/
lemma bAdjoint_l2Form_single_left {ι : Type*} (p : ι) (c : ℝ) (g : ι →₀ ℝ) :
    l2Form ι (Finsupp.single p c) g = c * g p := by
  simp only [l2Form, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply,
    Finsupp.lapply_apply, smul_eq_mul]

/-- `bCre i` on a basis vector of the occupation-number representation:
`bCre i |m⟩ = √(m i + 1) • |inc i m⟩`. -/
lemma bAdjoint_bCre_single {Mode : Type*} (i : Mode) (a : occIdx Mode) (b : ℝ) :
    bCre i (Finsupp.single a b) = Real.sqrt ((occ i a : ℝ) + 1) • Finsupp.single (inc i a) b := by
  rw [bCre, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply]

/-- `bAnn i` on a basis vector of the occupation-number representation:
`bAnn i |m⟩ = √(m i) • |dec i m⟩`. -/
lemma bAdjoint_bAnn_single {Mode : Type*} (i : Mode) (m : occIdx Mode) (d : ℝ) :
    bAnn i (Finsupp.single m d) = Real.sqrt (occ i m : ℝ) • Finsupp.single (dec i m) d := by
  rw [bAnn, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply]

/-- If the mode `i` is unoccupied in `m`, then removing a quantum of the mode `i`
changes nothing (truncated subtraction). -/
lemma bAdjoint_dec_self_of_occ_zero {Mode : Type*} (i : Mode) (m : occIdx Mode)
    (h : occ i m = 0) : dec i m = m := by
  ext k
  simp only [dec, ULift.down_up, Finsupp.tsub_apply]
  by_cases hk : k = i
  · subst hk
    simp only [Finsupp.single_eq_same, occ] at h ⊢
    rw [h]
  · rw [Finsupp.single_eq_of_ne hk, tsub_zero]

/-- The Kronecker-delta identity behind adjointness: for every pair of occupation
vectors `a`, `m`,
`√(occ i a + 1) · δ(inc i a, m) = √(occ i m) · δ(a, dec i m)`. -/
lemma bAdjoint_key {Mode : Type*} (i : Mode) (a m : occIdx Mode) :
    Real.sqrt ((occ i a : ℝ) + 1) * ((Finsupp.single m (1 : ℝ)) (inc i a))
      = Real.sqrt (occ i m : ℝ) * ((Finsupp.single (dec i m) (1 : ℝ)) a) := by
  classical
  by_cases h1 : m = inc i a
  · rw [h1, Finsupp.single_eq_same, dec_inc_self, Finsupp.single_eq_same, occ_inc_self]
    push_cast
    ring
  · rw [Finsupp.single_eq_of_ne (Ne.symm h1), mul_zero]
    by_cases h2 : a = dec i m
    · have h0 : occ i m = 0 := by
        by_contra h0
        refine h1 ?_
        rw [h2]
        exact (inc_dec_self m (Nat.pos_of_ne_zero h0)).symm
      rw [h0]
      simp
    · rw [Finsupp.single_eq_of_ne h2, mul_zero]

/-- The adjointness identity on pairs of basis vectors with unit coefficients. -/
lemma bAdjoint_ss1 {Mode : Type*} (i : Mode) (a m : occIdx Mode) :
    l2Form (occIdx Mode) (bCre i (Finsupp.single a (1 : ℝ))) (Finsupp.single m (1 : ℝ))
      = l2Form (occIdx Mode) (Finsupp.single a (1 : ℝ))
          (bAnn i (Finsupp.single m (1 : ℝ))) := by
  rw [bAdjoint_bCre_single, bAdjoint_bAnn_single]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, one_mul,
    bAdjoint_l2Form_single_left]
  exact bAdjoint_key i a m

/-- The adjointness identity on pairs of basis vectors, with arbitrary
coefficients. -/
lemma bAdjoint_ss {Mode : Type*} (i : Mode) (a m : occIdx Mode) (b d : ℝ) :
    l2Form (occIdx Mode) (bCre i (Finsupp.single a b)) (Finsupp.single m d)
      = l2Form (occIdx Mode) (Finsupp.single a b) (bAnn i (Finsupp.single m d)) := by
  have hb : Finsupp.single a b = b • Finsupp.single a (1 : ℝ) := by
    simpa using (Finsupp.smul_single b a (1 : ℝ)).symm
  have hd : Finsupp.single m d = d • Finsupp.single m (1 : ℝ) := by
    simpa using (Finsupp.smul_single d m (1 : ℝ)).symm
  rw [hb, hd, map_smul, map_smul]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [bAdjoint_ss1 i a m]

/-- Basis reduction in the second argument: the adjointness identity holds for
`f` a basis vector and every `g`. -/
lemma bAdjoint_inner {Mode : Type*} (i : Mode) (a : occIdx Mode) (b : ℝ)
    (g : boseH Mode) :
    l2Form (occIdx Mode) (bCre i (Finsupp.single a b)) g
      = l2Form (occIdx Mode) (Finsupp.single a b) (bAnn i g) := by
  have h : l2Form (occIdx Mode) (bCre i (Finsupp.single a b))
      = (l2Form (occIdx Mode) (Finsupp.single a b)).comp (bAnn i) :=
    Finsupp.lhom_ext (fun m d => bAdjoint_ss i a m b d)
  exact congrArg (fun L : boseH Mode →ₗ[ℝ] ℝ => L g) h

theorem bAdjoint {Mode : Type*} (i : Mode) (f g : Work.BoseB7.boseH Mode) :
    Work.BoseB7.l2Form (Work.BoseB7.occIdx Mode) (Work.BoseB7.bCre i f) g
      = Work.BoseB7.l2Form (Work.BoseB7.occIdx Mode) f (Work.BoseB7.bAnn i g) := by
  refine Finsupp.induction_linear f ?_ ?_ ?_ g
  · intro g
    simp
  · intro f₁ f₂ h₁ h₂ g
    simp only [map_add, LinearMap.add_apply]
    rw [h₁ g, h₂ g]
  · intro a b g
    exact bAdjoint_inner i a b g

end Work.BoseB7
