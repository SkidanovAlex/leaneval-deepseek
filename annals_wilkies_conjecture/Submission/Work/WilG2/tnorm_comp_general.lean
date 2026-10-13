/-
  `tnorm_comp_general` : subcompositionality of the BNZ jet norm, without the normalisation
  hypothesis `Σ_{1 ≤ k ≤ r} jetCoeff k F x ≤ 1`.

  The proof follows the Faà di Bruno route of `Submission/Work/WilG2/`:

  1. `norm_iteratedFDeriv_comp_le_ofp` (Faà di Bruno over `OrderedFinpartition`) bounds the
     `n`-th derivative of `g ∘ F` by the sum over ordered set partitions of the products of the
     norms of the corresponding derivatives of `g` and `F`;
  2. the weighted counting identity `ofp_weighted_sum'` (proved here, from the
     decorated-ordered-finpartition bijection of `Bijection.lean` together with its two inverse
     laws) converts that `OrderedFinpartition` sum into the `Composition` sum
     `Σ_{c : Composition n} jetCoeff c.length g (F x) · ∏ i, jetCoeff (c.blocksFun i) F x`;
  3. `sum_composition_mul_prod_le` dominates the sum over `n ≤ r` of those by
     `Σ_{p ≤ r} jetCoeff p g (F x) · (Σ_{1 ≤ k ≤ r} jetCoeff k F x)^p`.

  Steps 2 and 3 do not require any normalisation: this is exactly the point of the statement
  (the normalised version `G2_tnorm_comp` is the special case where the inner jet sum is `≤ 1`).
-/
import Mathlib
import Submission.Work.WilG2.CompStep
import Submission.Work.WilG2.Tnorm
import Submission.Work.WilG2.Bijection
import Submission.Work.WilG2.SizeData
import Submission.Work.WilG2.InvData.left_inv
import Submission.Work.WilG2.InvData.right_inv
import Submission.Work.WilG2.sum_composition_mul_prod_le

set_option autoImplicit false
noncomputable section

namespace Work.WilG2.TCG

open Finset

/-- The bijection between decorated ordered finpartitions of `Fin m` and pairs (size datum,
permutation of `Fin m`), assembled from the two inverse laws `InvData.left_inv` and
`InvData.right_inv`. -/
def ofpDataEquiv' (m : ℕ) : OFPData m ≃ (SizeData m × Equiv.Perm (Fin m)) where
  toFun := toMid
  invFun p := invData p.1 p.2
  left_inv x := InvData.left_inv m x
  right_inv p := InvData.right_inv m p

/-- **The weighted counting identity** relating the `OrderedFinpartition` Faà di Bruno sum to the
`Composition` sum.  The left hand side is the sum of the weights of the decorated ordered
finpartitions with a given size sequence; the decorations contribute exactly the factorials
`c.length! · ∏ i, c.partSize i!`, and the bijection with (size datum, permutation) pairs turns the
right hand side into `m!` times the `Composition` sum. -/
theorem ofp_weighted_sum' (m : ℕ) (a bg : ℕ → ℝ) :
    (∑ c : OrderedFinpartition m,
        ((c.length.factorial : ℝ) * ∏ i : Fin c.length, ((c.partSize i).factorial : ℝ)) *
          (bg c.length * ∏ i : Fin c.length, a (c.partSize i)))
      = (m.factorial : ℝ) *
          ∑ c : Composition m, bg c.length * ∏ i : Fin c.length, a (c.blocksFun i) := by
  rw [← sum_ofpData a bg]
  rw [Fintype.sum_equiv (ofpDataEquiv' m) (ofpDataWeight a bg) (midWeight a bg)
    (fun x => ofpDataWeight_eq_midWeight a bg x)]
  rw [Fintype.sum_prod_type]
  have h1 : ∀ y : SizeData m,
      (∑ ρ : Equiv.Perm (Fin m), midWeight a bg (y, ρ)) =
        (m.factorial : ℝ) *
          (bg (SizeData.len y) * ∏ i : Fin (SizeData.len y), a (SizeData.sizes y i)) := by
    intro y
    show (∑ _ : Equiv.Perm (Fin m),
        (bg (SizeData.len y) * ∏ i : Fin (SizeData.len y), a (SizeData.sizes y i))) = _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul]
  have h2 : (∑ y : SizeData m,
        bg (SizeData.len y) * ∏ i : Fin (SizeData.len y), a (SizeData.sizes y i)) =
      ∑ c : Composition m, bg c.length * ∏ i : Fin c.length, a (c.blocksFun i) :=
    Fintype.sum_equiv (sizeDataEquiv m)
      (fun y : SizeData m =>
        bg (SizeData.len y) * ∏ i : Fin (SizeData.len y), a (SizeData.sizes y i))
      (fun c : Composition m => bg c.length * ∏ i : Fin c.length, a (c.blocksFun i))
      (fun y => by
        change bg (SizeData.len y) * ∏ i : Fin (SizeData.len y), a (SizeData.sizes y i) =
          bg (SizeData.toComposition y).length *
            ∏ i : Fin (SizeData.toComposition y).length,
              a ((SizeData.toComposition y).blocksFun i)
        rw [SizeData.prod_toComposition_blocksFun, SizeData.toComposition_length])
  refine (Finset.sum_congr rfl fun y _ => h1 y).trans ?_
  rw [← Finset.mul_sum, h2]

end Work.WilG2.TCG

namespace Work.WilG2

open WilkiesDesign WilkiesDesign.CG

/-- **Subcompositionality of the jet norm, without the normalisation hypothesis.**  For any
two composable `C^r` functions, the jet norm of the composite is bounded by
`Σ_{p ≤ r} jetCoeff p g (F x) · (Σ_{1 ≤ k ≤ r} jetCoeff k F x)^p` — the BNZ estimate without
the requirement that the inner jet sum be at most `1`. -/
theorem tnorm_comp_general {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (r : ℕ) (F : E → (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ) (x : E)
    (hF : ContDiffAt ℝ r F x) (hg : ContDiffAt ℝ r g (F x)) :
    WilkiesDesign.CG.tnorm r (g ∘ F) x ≤
      ∑ p ∈ Finset.range (r + 1), WilkiesDesign.CG.jetCoeff p g (F x) *
        (∑ k ∈ Finset.Ico 1 (r + 1), WilkiesDesign.CG.jetCoeff k F x) ^ p := by
  rw [WilkiesDesign.CG.tnorm_eq_sum_jetCoeff]
  calc ∑ n ∈ Finset.range (r + 1), WilkiesDesign.CG.jetCoeff n (g ∘ F) x
      ≤ ∑ n ∈ Finset.range (r + 1), ∑ c : Composition n,
          WilkiesDesign.CG.jetCoeff c.length g (F x) *
            ∏ i : Fin c.length, WilkiesDesign.CG.jetCoeff (c.blocksFun i) F x :=
        Finset.sum_le_sum fun n hn =>
          WilkiesDesign.CG.jetCoeff_comp_le_of_counting r n
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) F g x hF hg
            (TCG.ofp_weighted_sum' n (fun k => WilkiesDesign.CG.jetCoeff k F x)
              (fun p => WilkiesDesign.CG.jetCoeff p g (F x)))
    _ ≤ ∑ p ∈ Finset.range (r + 1), WilkiesDesign.CG.jetCoeff p g (F x) *
          (∑ j : Fin r, WilkiesDesign.CG.jetCoeff (j + 1) F x) ^ p :=
        Work.WilG2.sum_composition_mul_prod_le r (fun k => WilkiesDesign.CG.jetCoeff k F x)
          (fun p => WilkiesDesign.CG.jetCoeff p g (F x))
          (fun i => WilkiesDesign.CG.jetCoeff_nonneg i F x)
          (fun j => WilkiesDesign.CG.jetCoeff_nonneg j g (F x))
    _ = ∑ p ∈ Finset.range (r + 1), WilkiesDesign.CG.jetCoeff p g (F x) *
          (∑ k ∈ Finset.Ico 1 (r + 1), WilkiesDesign.CG.jetCoeff k F x) ^ p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← WilkiesDesign.CG.sum_Ico_one_eq_sum_fin r
          (fun k => WilkiesDesign.CG.jetCoeff k F x)]

end Work.WilG2
