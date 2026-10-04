import Mathlib
import Submission.Work.Diff.STE.DeTurckJet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Symmetry of the coordinate DeTurck operator `pPhi`

`Work.Diff.STE.DeTurck.pPhi = -2 · jRic + jLW` is the coordinate expression of the DeTurck operator
`P(g) = -2 Ric(g) + L_{W(g)} g` in terms of the spatial `2`-jet `(A, L, B)` of the chart matrix of
`g` (see `Submission/Work/Diff/STE/DeTurckJet.lean`).  This file proves that `pPhi` is symmetric in
its two indices, as it must be, whenever the jet data come from a metric:

* `A i j = A j i` (the metric is symmetric),
* `L (bB a) i j = L (bB a) j i` (`∂_a g_{ij}` is symmetric in `i j`),
* `B` symmetric in its first two and in its last two arguments.

The second summand `jLW i j = jnabW i j + jnabW j i` is symmetric by construction; the whole content
is the symmetry of the coordinate Ricci tensor `jRic`, the coordinate shadow of the first Bianchi
identity.

## The route

Write `Γ_{abc} = jKz L a b c` for the lowered Koszul pairing and `D_{mabc} = jKzD B m a b c` for its
derivative.  The point is that the `∂Γ`-part of a curvature component can be put into a form that
is *manifestly* symmetric under the exchange of the pairs `(a,b) ↔ (c,d)`,

  `D_{adbc} - D_{bdac} = HH B a b c d := ½(B_{adbc} + B_{bcad} - B_{acbd} - B_{bdac})`,

using only the two symmetry hypotheses on `B`.  The quadratic part

  `QQ A L a b c d = -Σ_{rs} γ^{rs} Γ_{dbr} Γ_{acs} + Σ_{rs} γ^{rs} Γ_{dar} Γ_{bcs}`

is likewise symmetric under that exchange, using only the symmetry of `γ = A⁻¹` (from `hA`) and the
symmetry `Γ_{abc} = Γ_{bac}` (from `hL`): the two "cross" terms are matched by exchanging the two
summation indices.  Hence `jRm A L B a b c d = jRm A L B c d a b` (pair exchange), and the Ricci
contraction `jRic i j = Σ_{kl} γ^{kl} jRm k i l j` is symmetric by re-indexing `k ↔ l`.

No invertibility of `A` is needed: if `A` is singular then `γ = A⁻¹ = 0`, so `jRic = 0`, while
`jLW` is symmetric unconditionally.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

namespace Work.Diff.STE.deTurck

open Work.Diff.EXT Work.Diff.STE.DeTurck

noncomputable section

namespace PPhiSymm

/-! ## Elementary index helpers -/

/-- The lowered Koszul pairing `jKz L` is symmetric in its first two indices. -/
lemma jKz_symm (L : LinMat E)
    (hL : ∀ a i j : Idx E, L (bB a) i j = L (bB a) j i) (a b c : Idx E) :
    jKz L a b c = jKz L b a c := by
  simp only [jKz]
  rw [hL c a b]
  ring

/-- The inverse of a symmetric matrix is symmetric. -/
lemma jInv_symm (A : MatE (E := E)) (hA : ∀ i j : Idx E, A i j = A j i) :
    ∀ r s : Idx E, jInv A r s = jInv A s r := by
  intro r s
  have htrans : (Matrix.of A).transpose = Matrix.of A := by
    ext i j
    simpa [Matrix.transpose_apply] using (hA i j).symm
  have h := Matrix.transpose_nonsing_inv (Matrix.of A)
  rw [htrans] at h
  have h2 := congrFun (congrFun h r) s
  rw [Matrix.transpose_apply] at h2
  exact h2.symm

/-- Exchange the two dummy variables of a double sum with a symmetric weight. -/
lemma sum_swap_symm {ι : Type*} [Fintype ι] (γ : ι → ι → ℝ) (hγ : ∀ a b, γ a b = γ b a)
    (f : ι → ι → ℝ) : (∑ k, ∑ l, γ k l * f k l) = ∑ k, ∑ l, γ k l * f l k := by
  have e : (∑ p : ι × ι, γ p.2 p.1 * f p.2 p.1) = ∑ p : ι × ι, γ p.1 p.2 * f p.1 p.2 :=
    Equiv.sum_comp (Equiv.prodComm ι ι) (fun p : ι × ι => γ p.1 p.2 * f p.1 p.2)
  have e2 : (∑ p : ι × ι, γ p.1 p.2 * f p.2 p.1) = ∑ p : ι × ι, γ p.2 p.1 * f p.2 p.1 :=
    Finset.sum_congr rfl (fun p _ => by rw [hγ p.1 p.2])
  calc ∑ k, ∑ l, γ k l * f k l
      = ∑ p : ι × ι, γ p.1 p.2 * f p.1 p.2 :=
        (Fintype.sum_prod_type (fun p : ι × ι => γ p.1 p.2 * f p.1 p.2)).symm
    _ = ∑ p : ι × ι, γ p.2 p.1 * f p.2 p.1 := e.symm
    _ = ∑ p : ι × ι, γ p.1 p.2 * f p.2 p.1 := e2.symm
    _ = ∑ k, ∑ l, γ k l * f l k := Fintype.sum_prod_type (fun p : ι × ι => γ p.1 p.2 * f p.2 p.1)

/-! ## The two pieces of a curvature component -/

/-- The `∂Γ`-part of a curvature component, in the form that is manifestly symmetric under the
exchange of the pairs of indices `(a,b) ↔ (c,d)`. -/
def HH (B : BilMat E) (a b c d : Idx E) : ℝ :=
  (1 / 2) * (B (bB a) (bB d) b c + B (bB b) (bB c) a d
    - B (bB a) (bB c) b d - B (bB b) (bB d) a c)

/-- The quadratic part of a curvature component (the two `ΓΓ` terms of the coordinate formula). -/
def QQ (A : MatE (E := E)) (L : LinMat E) (a b c d : Idx E) : ℝ :=
  - (∑ r, ∑ s, jInv A r s * jKz L d b r * jKz L a c s)
    + (∑ r, ∑ s, jInv A r s * jKz L d a r * jKz L b c s)

/-- The coordinate formula for a curvature component, split into its `∂Γ`-part `HH` (in symmetric
form) and its quadratic part `QQ`. -/
lemma jRm_eq_HH_add_QQ (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (hB1 : ∀ m a b c : Idx E, B (bB m) (bB a) b c = B (bB a) (bB m) b c)
    (hB2 : ∀ m a b c : Idx E, B (bB m) (bB a) b c = B (bB m) (bB a) c b)
    (a b c d : Idx E) :
    jRm A L B a b c d = HH B a b c d + QQ A L a b c d := by
  simp only [jRm, jKzD, HH, QQ]
  rw [hB1 a b d c, hB2 a c d b, hB2 b c d a]
  ring

/-- The `∂Γ`-part `HH` is invariant under the exchange of the two pairs of indices. -/
lemma HH_symm (B : BilMat E)
    (hB1 : ∀ m a b c : Idx E, B (bB m) (bB a) b c = B (bB a) (bB m) b c)
    (hB2 : ∀ m a b c : Idx E, B (bB m) (bB a) b c = B (bB m) (bB a) c b)
    (a b c d : Idx E) : HH B a b c d = HH B c d a b := by
  simp only [HH]
  rw [hB1 c b d a, hB2 b c d a, hB1 d a c b, hB2 a d c b, hB1 c a d b, hB2 a c d b,
    hB1 d b c a, hB2 b d c a]
  ring

/-- The quadratic part `QQ` is invariant under the exchange of the two pairs of indices. -/
lemma QQ_symm (A : MatE (E := E)) (L : LinMat E)
    (hA : ∀ i j : Idx E, A i j = A j i)
    (hL : ∀ a i j : Idx E, L (bB a) i j = L (bB a) j i) (a b c d : Idx E) :
    QQ A L a b c d = QQ A L c d a b := by
  have hK : ∀ x y z : Idx E, jKz L x y z = jKz L y x z := jKz_symm L hL
  have hγ : ∀ x y : Idx E, jInv A x y = jInv A y x := jInv_symm A hA
  -- the first `ΓΓ` term: termwise equality
  have e1 : (∑ r, ∑ s, jInv A r s * jKz L d b r * jKz L a c s)
      = ∑ r, ∑ s, jInv A r s * jKz L b d r * jKz L c a s := by
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
    rw [hK d b r, hK a c s]
  -- the second `ΓΓ` term: canonical form
  have e3 : (∑ r, ∑ s, jInv A r s * jKz L d a r * jKz L b c s)
      = ∑ r, ∑ s, jInv A r s * jKz L a d r * jKz L c b s := by
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
    rw [hK d a r, hK b c s]
  -- exchange the two summation indices of the canonical form
  have e4 : (∑ r, ∑ s, jInv A r s * jKz L a d r * jKz L c b s)
      = ∑ r, ∑ s, jInv A r s * jKz L a d s * jKz L c b r := by
    simp only [mul_assoc]
    exact sum_swap_symm (jInv A) hγ (fun r s => jKz L a d r * jKz L c b s)
  -- back to the second `ΓΓ` term of the exchanged expression
  have e5 : (∑ r, ∑ s, jInv A r s * jKz L a d s * jKz L c b r)
      = ∑ r, ∑ s, jInv A r s * jKz L b c r * jKz L d a s := by
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
    rw [← hK d a s, ← hK b c r]
    ring
  have hS2 : (∑ r, ∑ s, jInv A r s * jKz L d a r * jKz L b c s)
      = ∑ r, ∑ s, jInv A r s * jKz L b c r * jKz L d a s := by
    rw [e3, e4, e5]
  simp only [QQ]
  rw [e1, hS2]

/-! ## Pair exchange and the symmetry of the Ricci tensor -/

/-- **Pair exchange** for the coordinate curvature formula: `R_{abcd} = R_{cdab}`. -/
lemma jRm_exchange (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (hA : ∀ i j : Idx E, A i j = A j i)
    (hL : ∀ a i j : Idx E, L (bB a) i j = L (bB a) j i)
    (hB1 : ∀ m a b c : Idx E, B (bB m) (bB a) b c = B (bB a) (bB m) b c)
    (hB2 : ∀ m a b c : Idx E, B (bB m) (bB a) b c = B (bB m) (bB a) c b)
    (a b c d : Idx E) :
    jRm A L B a b c d = jRm A L B c d a b := by
  calc jRm A L B a b c d = HH B a b c d + QQ A L a b c d :=
        jRm_eq_HH_add_QQ A L B hB1 hB2 a b c d
    _ = HH B c d a b + QQ A L c d a b := by
        rw [HH_symm B hB1 hB2 a b c d, QQ_symm A L hA hL a b c d]
    _ = jRm A L B c d a b := (jRm_eq_HH_add_QQ A L B hB1 hB2 c d a b).symm

/-- The coordinate Ricci tensor is symmetric (contraction of the pair-exchange symmetric curvature
formula against the symmetric inverse Gram matrix). -/
lemma jRic_symm (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (hA : ∀ i j : Idx E, A i j = A j i)
    (hL : ∀ a i j : Idx E, L (bB a) i j = L (bB a) j i)
    (hB1 : ∀ m a b c : Idx E, B (bB m) (bB a) b c = B (bB a) (bB m) b c)
    (hB2 : ∀ m a b c : Idx E, B (bB m) (bB a) b c = B (bB m) (bB a) c b)
    (i j : Idx E) : jRic A L B i j = jRic A L B j i := by
  have hγ : ∀ x y : Idx E, jInv A x y = jInv A y x := jInv_symm A hA
  simp only [jRic]
  calc ∑ k, ∑ l, jInv A k l * jRm A L B k i l j
      = ∑ k, ∑ l, jInv A k l * jRm A L B l j k i := by
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
        rw [jRm_exchange A L B hA hL hB1 hB2 k i l j]
    _ = ∑ k, ∑ l, jInv A l k * jRm A L B k j l i := by
        rw [Finset.sum_comm]
    _ = ∑ k, ∑ l, jInv A k l * jRm A L B k j l i := by
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
        rw [hγ k l]

/-- The Lie-derivative term `jLW a b = jnabW a b + jnabW b a` is symmetric by construction. -/
lemma jLW_symm (A : MatE (E := E)) (L : LinMat E) (B : BilMat E)
    (Abar : MatE (E := E)) (Lbar : LinMat E) (Bbar : BilMat E) (i j : Idx E) :
    jLW A L B Abar Lbar Bbar i j = jLW A L B Abar Lbar Bbar j i := by
  simp only [jLW]
  ring

end PPhiSymm

theorem pPhi_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (A : Work.Diff.EXT.MatE (E := E)) (L : Work.Diff.STE.DeTurck.LinMat E)
    (B : Work.Diff.STE.DeTurck.BilMat E)
    (Abar : Work.Diff.EXT.MatE (E := E)) (Lbar : Work.Diff.STE.DeTurck.LinMat E)
    (Bbar : Work.Diff.STE.DeTurck.BilMat E)
    (hA : ∀ i j, A i j = A j i)
    (hL : ∀ (a : Fin (Module.finrank ℝ E)) (i j : Fin (Module.finrank ℝ E)),
      L (Work.Diff.EXT.bB (E := E) a) i j = L (Work.Diff.EXT.bB (E := E) a) j i)
    (hB1 : ∀ a b : Fin (Module.finrank ℝ E),
      B (Work.Diff.EXT.bB (E := E) a) (Work.Diff.EXT.bB (E := E) b)
        = B (Work.Diff.EXT.bB (E := E) b) (Work.Diff.EXT.bB (E := E) a))
    (hB2 : ∀ (a b : Fin (Module.finrank ℝ E)) (i j : Fin (Module.finrank ℝ E)),
      B (Work.Diff.EXT.bB (E := E) a) (Work.Diff.EXT.bB (E := E) b) i j
        = B (Work.Diff.EXT.bB (E := E) a) (Work.Diff.EXT.bB (E := E) b) j i) :
    ∀ i j, Work.Diff.STE.DeTurck.pPhi Abar Lbar Bbar A L B i j
      = Work.Diff.STE.DeTurck.pPhi Abar Lbar Bbar A L B j i := by
  -- the function-equality form of `hB1` at the level of components
  have hB1' : ∀ m a b c : Idx E, B (bB m) (bB a) b c = B (bB a) (bB m) b c :=
    fun m a b c => congrFun (congrFun (hB1 m a) b) c
  intro i j
  have hRic : jRic A L B i j = jRic A L B j i :=
    PPhiSymm.jRic_symm A L B hA hL hB1' hB2 i j
  have hLW : jLW A L B Abar Lbar Bbar i j = jLW A L B Abar Lbar Bbar j i :=
    PPhiSymm.jLW_symm A L B Abar Lbar Bbar i j
  simp only [pPhi]
  rw [hRic, hLW]

end

end Work.Diff.STE.deTurck
