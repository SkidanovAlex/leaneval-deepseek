import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseB4.BesselAux
import Submission.Work.BoseB4.bessel_gram_factor
import Submission.Work.BoseB4.finset_sum_creOf_comp_annOf
import Submission.Work.BoseB4.totNumOp_eq_double_sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.bessel_le_totNumOp_v2` — the Bessel bound for an orthonormal
family of modes

On the real bosonic Fock space `RealFock m` over `m` modes with the Bombieri form
`bomb m` (`⟪p,q⟫ = Σ_α α! p_α q_α`), let `g : ι → Fin m → ℝ` be coordinate
vectors whose Gram matrix is the identity on `S`,

`gram (g s) (g t) = δ_{st}`   for `s, t ∈ S`.

Then for every state `Φ`

`Σ_{s∈S} ⟪a(g_s)Φ, a(g_s)Φ⟫ ≤ ⟪N Φ, Φ⟫`,   `N = totNumOp m = Σ_l a_l† a_l`.

This is the Bessel inequality for the annihilation operators of an orthonormal
mode family, the estimate behind FS's `n₊`-bound `Σ_{s∈S} ã_s† ã_s ≤ n₊` used in
`Work.BoseB4.TildeDataInst`.

The proof is a sum-of-squares identity.  Writing `G` for the Gram matrix
`G_{ll'} = Σ_{s∈S} g_{sl} g_{sl'}` of the family, the orthonormality makes `G` an
orthogonal projection (`G² = G`, `Gᵀ = G`), so with
`W_{lp} = δ_{lp} − G_{lp}` one has

`Σ_{p} W_{lp} W_{l'p} = ((1−G)²)_{ll'} = (1−G)_{ll'}`,

i.e. `1 − G = Σ_p w_p w_pᵀ` for the columns `w_p = (W_{lp})_l`.  Since

`N = Σ_{l,l'} δ_{ll'} a_l†a_{l'}` and `Σ_{s∈S} a†(g_s)a(g_s) = Σ_{l,l'} G_{ll'} a_l†a_{l'}`
(`Work.BoseB4.totNumOp_eq_double_sum`, `Work.BoseB4.finset_sum_creOf_comp_annOf`),

`N − Σ_{s∈S} a†(g_s)a(g_s) = Σ_{l,l'} (Σ_p w_p l · w_p l') a_l†a_{l'}
                            = Σ_p a†(w_p) a(w_p)`,

a sum of positive operators.  Taking the form with `Φ` and using `a†(f)* = a(f)`
(`Work.BoseB4.CreOf_annOf_adjoint`) and the positivity of `bomb`
(`Work.BoseB4.Bomb_self_nonneg`) gives the claim.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

theorem bessel_le_totNumOp_v2 {m : ℕ} {ι : Type*} [DecidableEq ι] (g : ι → Fin m → ℝ)
    (S : Finset ι)
    (hg : ∀ s ∈ S, ∀ t ∈ S, Work.BoseB4.gram (g s) (g t) = if s = t then 1 else 0)
    (Φ : Work.BoseB4.RealFock m) :
    ∑ s ∈ S, Work.BoseB4.bomb m (Work.BoseB4.annOf m (g s) Φ) (Work.BoseB4.annOf m (g s) Φ)
      ≤ Work.BoseB4.bomb m (Work.BoseB4.totNumOp m Φ) Φ := by
  classical
  -- orthonormality of the family, in the coordinate-sum form used by the matrix lemmas
  have hg' : ∀ s ∈ S, ∀ t ∈ S, (∑ l : Fin m, g s l * g t l) = if s = t then 1 else 0 :=
    fun s hs t ht => by simpa only [gram] using hg s hs t ht
  -- the sum of the mode number operators, as a "matrix of operators"
  have hA : (∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s)))
      = besselOpMat m (fun l l' => ∑ s ∈ S, g s l * g s l') := by
    rw [finset_sum_creOf_comp_annOf (m := m) (W := g) S, besselOpMat]
  -- the total number operator, as the same kind of "matrix of operators"
  have hN : totNumOp m = besselOpMat m (fun l l' => (if l = l' then (1 : ℝ) else 0)) := by
    rw [totNumOp_eq_double_sum, besselOpMat]
  -- hence the difference is `besselOpMat` of the matrix `1 - G`
  have hsub : totNumOp m - (∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s)))
      = besselOpMat m ((fun l l' => (if l = l' then (1 : ℝ) else 0))
          - (fun l l' => ∑ s ∈ S, g s l * g s l')) := by
    rw [hN, hA, ← besselOpMat_sub]
  -- the columns `w_p` of `1 - G`: `w_p l = (1-G)_{lp}`
  set W : Fin m → Fin m → ℝ :=
    fun p l => (if l = p then (1 : ℝ) else 0) - ∑ s ∈ S, g s l * g s p with hW
  -- orthogonality: `1 - G` is a sum of rank-one matrices, `(1-G)_{ll'} = Σ_p w_p l · w_p l'`
  have hmat : ((fun l l' => (if l = l' then (1 : ℝ) else 0))
        - (fun l l' => ∑ s ∈ S, g s l * g s l'))
      = fun l l' => ∑ p : Fin m, W p l * W p l' := by
    funext l l'
    simp only [Pi.sub_apply, hW]
    exact (bessel_gram_factor g S hg' l l').symm
  -- so the difference of the operators is a sum of `a†(w_p) a(w_p)`
  have hD2 : besselOpMat m (fun l l' => ∑ p : Fin m, W p l * W p l')
      = ∑ p : Fin m, (creOf m (W p)).comp (annOf m (W p)) := by
    simp only [besselOpMat]
    rw [← finset_sum_creOf_comp_annOf (m := m) (W := W) Finset.univ]
  -- the difference is positive semi-definite
  have hDpos : 0 ≤ bomb m
      ((totNumOp m - ∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s))) Φ) Φ := by
    rw [hsub, hmat, hD2]
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    refine Finset.sum_nonneg fun p _ => ?_
    rw [CreOf_annOf_adjoint]
    exact Bomb_self_nonneg _
  -- the left-hand side is the quadratic form of the sum
  have hL : (∑ s ∈ S, bomb m (annOf m (g s) Φ) (annOf m (g s) Φ))
      = bomb m ((∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s))) Φ) Φ := by
    have h1 : (∑ s ∈ S, bomb m (annOf m (g s) Φ) (annOf m (g s) Φ))
        = ∑ s ∈ S, bomb m (creOf m (g s) (annOf m (g s) Φ)) Φ :=
      Finset.sum_congr rfl fun s _ => (CreOf_annOf_adjoint (g s) (annOf m (g s) Φ) Φ).symm
    have h2 : (∑ s ∈ S, bomb m (creOf m (g s) (annOf m (g s) Φ)) Φ)
        = bomb m ((∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s))) Φ) Φ := by
      rw [show (∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s))) Φ
          = ∑ s ∈ S, creOf m (g s) (annOf m (g s) Φ) by
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]]
      rw [map_sum, LinearMap.sum_apply]
    rw [h1, h2]
  -- transfer both sides to the second argument of `bomb`
  have hsymA : bomb m ((∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s))) Φ) Φ
      = bomb m Φ ((∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s))) Φ) := Bomb_symm _ _
  have hsymN : bomb m (totNumOp m Φ) Φ = bomb m Φ (totNumOp m Φ) := Bomb_symm _ _
  rw [hL, hsymA, hsymN]
  -- the difference of the two quadratic forms is the positive form of `N - Σ`
  have hle : bomb m Φ (totNumOp m Φ)
      - bomb m Φ ((∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s))) Φ)
      = bomb m Φ ((totNumOp m - ∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s))) Φ) := by
    rw [← map_sub, ← LinearMap.sub_apply]
  have h0 : 0 ≤ bomb m Φ ((totNumOp m
      - ∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s))) Φ) := by
    rw [Bomb_symm]
    exact hDpos
  have hfin : 0 ≤ bomb m Φ (totNumOp m Φ)
      - bomb m Φ ((∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s))) Φ) := by
    rw [hle]
    exact h0
  linarith

end Work.BoseB4
