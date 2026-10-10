import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.Shrinking.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Shrinking

open MvPolynomial

/-- **Chevalley–Warning in the shrinking form.**  Let `W` be a finite dimensional
`𝔽_p`-vector space, let `1 ≤ s` and let `F : 𝔽_p^r → W` be the homogeneous degree-`s`
"polynomial map" `F a = ∑_{e : Fin s → Fin r} (∏ j, a (e j)) • c e`.  If `s * dim W < r`
then `F` has a nonzero zero.

Proof sketch: pick a basis `b := Module.finBasis (ZMod p) W` and the coordinate
polynomials `P k := ∑ e : Fin s → Fin r, (∏ j : Fin s, MvPolynomial.X (e j)) *
MvPolynomial.C (b.coord k (c e))` for `k : Fin (finrank (ZMod p) W)`.  Each `P k` has
total degree `≤ s`: the monomial `∏ j, X (e j)` has degree `≤ s`, multiplying by a
constant does not increase it, and a sum of polynomials of degree `≤ s` has degree `≤ s`
(prove `MvPolynomial.totalDegree_finset_sum_le` by `Finset.induction` from
`MvPolynomial.totalDegree_add_le` and `MvPolynomial.totalDegree_zero`).  Since
`∑ k, (P k).totalDegree ≤ finrank W * s < r = Fintype.card (Fin r)`, Chevalley–Warning
(`MvPolynomial.char_dvd_card_solutions_of_fintype_sum_lt`) gives that `p` divides the
number of common zeros of the `P k`, a set which contains `0` (here `1 ≤ s` is used: at
`a = 0` every monomial vanishes).  Hence some nonzero `a` is a common zero, and
`b.coord k (∑ e, (∏ j, a (e j)) • c e) = 0` for all `k`, so the sum is `0`
(`Module.Basis.forall_coord_eq_zero_iff`). -/
theorem exists_ne_zero_of_polyMap_eq_zero {p : ℕ} [Fact p.Prime]
    {W : Type*} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    {s r : ℕ} (hs : 1 ≤ s) (h : s * Module.finrank (ZMod p) W < r)
    (c : (Fin s → Fin r) → W) :
    ∃ a : Fin r → ZMod p, a ≠ 0 ∧
      (∑ e : Fin s → Fin r, (∏ j : Fin s, a (e j)) • c e) = 0 := by
  classical
  -- A basis of `W` over `𝔽_p`, and the coordinate polynomials `P k`.
  let b := Module.finBasis (ZMod p) W
  let P : Fin (Module.finrank (ZMod p) W) → MvPolynomial (Fin r) (ZMod p) :=
    fun k => ∑ e : Fin s → Fin r,
      (∏ j : Fin s, MvPolynomial.X (e j)) * MvPolynomial.C (b.coord k (c e))
  -- Evaluating `P k` at `a` computes the `k`-th coordinate of `F a`.
  have hP_eval : ∀ (a : Fin r → ZMod p) (k : Fin (Module.finrank (ZMod p) W)),
      MvPolynomial.eval a (P k)
        = b.coord k (∑ e : Fin s → Fin r, (∏ j : Fin s, a (e j)) • c e) := by
    intro a k
    simp only [P, map_sum, map_mul, MvPolynomial.eval_prod, MvPolynomial.eval_X,
      MvPolynomial.eval_C, map_smul, smul_eq_mul]
  -- Each `P k` has total degree at most `s`.
  have hP_deg : ∀ k, (P k).totalDegree ≤ s := by
    intro k
    simp only [P]
    refine MvPolynomial.totalDegree_finsetSum_le (fun e _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, add_zero]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    simp [MvPolynomial.totalDegree_X]
  -- So the sum of the degrees of the `P k` is `< r`.
  have hdeg : (∑ k : Fin (Module.finrank (ZMod p) W), (P k).totalDegree)
      < Fintype.card (Fin r) := by
    calc (∑ k : Fin (Module.finrank (ZMod p) W), (P k).totalDegree)
        ≤ ∑ _k : Fin (Module.finrank (ZMod p) W), s :=
          Finset.sum_le_sum (fun k _ => hP_deg k)
      _ = Module.finrank (ZMod p) W * s := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = s * Module.finrank (ZMod p) W := Nat.mul_comm _ _
      _ < r := h
      _ = Fintype.card (Fin r) := (Fintype.card_fin r).symm
  -- `0` is a common zero, since `1 ≤ s`.
  have h0 : ∀ k, MvPolynomial.eval (0 : Fin r → ZMod p) (P k) = 0 := by
    intro k
    rw [hP_eval]
    have hz : ∀ e : Fin s → Fin r, (∏ j : Fin s, (0 : Fin r → ZMod p) (e j)) = 0 := by
      intro e
      exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, hs⟩) (by simp)
    simp only [hz, zero_smul, Finset.sum_const_zero, map_zero]
  -- Chevalley–Warning: the number of common zeros is divisible by `p`.
  have hcard := char_dvd_card_solutions_of_fintype_sum_lt (K := ZMod p) (σ := Fin r) p hdeg
  obtain ⟨m, hm⟩ := hcard
  rw [← @Nat.card_eq_fintype_card
    {a : Fin r → ZMod p // ∀ k, MvPolynomial.eval a (P k) = 0}] at hm
  have hcardne : Nat.card {a : Fin r → ZMod p // ∀ k, MvPolynomial.eval a (P k) = 0} ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨⟨0, h0⟩⟩, Finite.of_fintype _⟩
  have hpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h' | h'
    · rw [h', mul_zero] at hm; exact absurd hm hcardne
    · exact h'
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hN2 : 1 < Fintype.card {a : Fin r → ZMod p // ∀ k, MvPolynomial.eval a (P k) = 0} := by
    rw [← Nat.card_eq_fintype_card, hm]
    calc 1 < 2 := by norm_num
      _ ≤ p := hp2
      _ ≤ p * m := Nat.le_mul_of_pos_right p hpos
  -- Hence there is a common zero other than `0`.
  obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card hN2 ⟨0, h0⟩
  refine ⟨a, fun hz => ha (Subtype.ext (by simpa using hz)), ?_⟩
  -- Its coordinates all vanish, so the vector itself is zero.
  exact b.forall_coord_eq_zero_iff.mp
    (fun k => by rw [← hP_eval (a : Fin r → ZMod p) k]; exact a.2 k)

end Work.Shrinking
