/-
  WilG4c / ChartRescaleDefs — the vocabulary of the "rescale the value of a family member"
  lemma `Work.WilG4c.ChartRescaleMem` (BNZ §5.2-style affine reparametrisation of the graph).

  If `A ⊆ ℝ^{m+1}` is (the graph of) a family member written with its `m` argument
  coordinates first and its value last, then the rescaling `y ↦ c + y / K` of the value is
  obtained by

  * putting a fresh copy `u : ℝ^{m+1}` of the *old* point as the trailing block of
    `ℝ^{(m+1)+(m+1)}`, requiring `u ∈ A` (`Work.WilG5.liftLast`),
  * imposing the single degree-`2` polynomial relation `crQ = 0`, which simultaneously says
    that the first `m` coordinates of `u` and of the new point agree (`u j = z j`, the
    "diagonal" of a substitution atom, `m` equations which in the standard substitution
    construction are produced by the sum of squares Σ_j (u_j - z_j)²) and that the new value
    is `z (last m) = c + u (last m) / K` (one more squared linear equation),
  * projecting the fresh block `u` away (`Work.WilG5.projN`).

  Folding the `m` diagonal equations and the affine equation into *one* sum of squares of
  degree `2` is what keeps the degree cost of the whole operation at `D + 2` (the `+2` of a
  substitution atom) instead of `D + 3`: the relation is a single `hyp` atom, not an
  intersection of a degree-`2` and a degree-`1` hypersurface.

  This file holds the definitions and the polynomial facts; the set-theoretic identity is
  `Work.WilG4c.CrProjEq` and the `Ω`-bookkeeping is `Work.WilG4c.CrSetMem`.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG5.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-- The sum of squares imposing both the diagonal `u j = z j` (`j : Fin m`, the argument
coordinates) and the affine value relation `z (last m) = c + u (last m) / K` between the new
point `z` (first block) and the old point `u` (second block) of `ℝ^{(m+1)+(m+1)}`. -/
def crQ (m : ℕ) (K : ℕ) (c : ℝ) : MvPolynomial (Fin ((m+1)+(m+1))) ℝ :=
  (∑ i : Fin m, (MvPolynomial.X (Fin.natAdd (m+1) (Fin.castSucc i)) -
      MvPolynomial.X (Fin.castAdd (m+1) (Fin.castSucc i))) *
    (MvPolynomial.X (Fin.natAdd (m+1) (Fin.castSucc i)) -
      MvPolynomial.X (Fin.castAdd (m+1) (Fin.castSucc i)))) +
  ((MvPolynomial.X (Fin.castAdd (m+1) (Fin.last m)) - MvPolynomial.C c -
      MvPolynomial.X (Fin.natAdd (m+1) (Fin.last m)) * MvPolynomial.C ((K:ℝ)⁻¹)) *
    (MvPolynomial.X (Fin.castAdd (m+1) (Fin.last m)) - MvPolynomial.C c -
      MvPolynomial.X (Fin.natAdd (m+1) (Fin.last m)) * MvPolynomial.C ((K:ℝ)⁻¹)))

/-- The lifted set `A` (on the trailing `m+1` coordinates of `ℝ^{(m+1)+(m+1)}`) cut by the
sum of squares `crQ`.  Its projection onto the leading `m+1` coordinates is the rescaled set. -/
def crSet (m : ℕ) (K : ℕ) (c : ℝ) (A : Set (Fin (m+1) → ℝ)) : Set (Fin ((m+1)+(m+1)) → ℝ) :=
  {v | (fun i : Fin (m+1) => v (Fin.natAdd (m+1) i)) ∈ A ∧ MvPolynomial.eval v (crQ m K c) = 0}

/-- The trailing coordinate read by `liftLast` agrees with `Fin.natAdd`. -/
theorem lidxNatAdd (m : ℕ) (i : Fin (m+1)) : Work.WilG5.lidx (m+1) i = Fin.natAdd (m+1) i := rfl

/-- `crSet` is the intersection of the lifted set with the zero set of `crQ`. -/
theorem crSet_eq_liftLast (m K : ℕ) (c : ℝ) (A : Set (Fin (m+1) → ℝ)) :
    crSet m K c A =
      Work.WilG5.liftLast (m+1) A ∩ {v | MvPolynomial.eval v (crQ m K c) = 0} := by
  have hfun : ∀ v : Fin ((m+1)+(m+1)) → ℝ,
      (fun i : Fin (m+1) => v (Work.WilG5.lidx (m+1) i)) =
        (fun i : Fin (m+1) => v (Fin.natAdd (m+1) i)) :=
    fun v => funext fun i => congrArg v (lidxNatAdd m i)
  ext v
  simp only [crSet, Work.WilG5.liftLast, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [hfun v]

/-- Evaluation of `crQ` on a glued point `Fin.append z u`: the sum of the squares of the `m`
diagonal differences and of the affine value difference. -/
theorem CrQ_eval_append (m K : ℕ) (c : ℝ) (z u : Fin (m+1) → ℝ) :
    MvPolynomial.eval (Fin.append z u) (crQ m K c) =
      (∑ i : Fin m, (u (Fin.castSucc i) - z (Fin.castSucc i))^2) +
        (z (Fin.last m) - c - u (Fin.last m) * ((K:ℝ)⁻¹))^2 := by
  simp only [crQ, MvPolynomial.eval_add, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, Fin.append_left,
    Fin.append_right]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

/-- **The relation coded by `crQ`.**  For `z` (new point) and `u` (old point) in `ℝ^{m+1}`,
`crQ` vanishes on the glued point `Fin.append z u` exactly when the argument coordinates agree
and the new value is the affinely rescaled old value. -/
theorem CrQ_eval_eq_zero_iff (m K : ℕ) (c : ℝ) (z u : Fin (m+1) → ℝ) :
    MvPolynomial.eval (Fin.append z u) (crQ m K c) = 0 ↔
      (∀ i : Fin m, u (Fin.castSucc i) = z (Fin.castSucc i)) ∧
        z (Fin.last m) = c + u (Fin.last m) / (K : ℝ) := by
  rw [CrQ_eval_append]
  set S : ℝ := ∑ i : Fin m, (u (Fin.castSucc i) - z (Fin.castSucc i))^2 with hS
  set T : ℝ := (z (Fin.last m) - c - u (Fin.last m) * ((K:ℝ)⁻¹))^2 with hT
  have hSnn : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hTnn : 0 ≤ T := by rw [hT]; exact sq_nonneg _
  constructor
  · intro h
    have hS0 : S = 0 := by nlinarith
    have hT0 : T = 0 := by nlinarith
    have hvals := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg (u (Fin.castSucc i) - z (Fin.castSucc i)))).mp
      (by rw [← hS]; exact hS0)
    refine ⟨fun i => ?_, ?_⟩
    · have hi : (u (Fin.castSucc i) - z (Fin.castSucc i))^2 = 0 := hvals i (Finset.mem_univ i)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
    · have h2 : (z (Fin.last m) - c - u (Fin.last m) * ((K:ℝ)⁻¹))^2 = 0 := by
        rw [← hT]; exact hT0
      have h3 : z (Fin.last m) - c - u (Fin.last m) * ((K:ℝ)⁻¹) = 0 := sq_eq_zero_iff.mp h2
      rw [div_eq_mul_inv]; linarith
  · rintro ⟨h1, h2⟩
    have hS0 : S = 0 := by
      rw [hS]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [h1 i]; ring
    have hT0 : T = 0 := by
      rw [hT]
      have h2' : z (Fin.last m) - c - u (Fin.last m) * ((K:ℝ)⁻¹) = 0 := by
        rw [div_eq_mul_inv] at h2; linarith
      rw [h2']; ring
    rw [hS0, hT0, add_zero]

/-- `crQ` has total degree at most `2` — independently of `m`, and for every `K`, `c`
(the affine relations are linear, and they are written as squares). -/
theorem CrQ_totalDegree_le (m K : ℕ) (c : ℝ) : (crQ m K c).totalDegree ≤ 2 := by
  have hX : ∀ a : Fin ((m+1)+(m+1)),
      (MvPolynomial.X a : MvPolynomial (Fin ((m+1)+(m+1))) ℝ).totalDegree ≤ 1 :=
    fun a => Work.WilG5.td_X_le a
  have hsub : ∀ a b : Fin ((m+1)+(m+1)),
      (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin ((m+1)+(m+1))) ℝ).totalDegree ≤ 1 :=
    fun a b => (Work.WilG5.td_sub_le _ _).trans (max_le (hX a) (hX b))
  have hsubC : ∀ a : Fin ((m+1)+(m+1)),
      (MvPolynomial.X a - MvPolynomial.C c : MvPolynomial (Fin ((m+1)+(m+1))) ℝ).totalDegree ≤ 1 :=
    fun a => (Work.WilG5.td_sub_le _ _).trans
      (max_le (hX a) (le_trans (Work.WilG5.td_C_le c) (Nat.zero_le 1)))
  have hmulX : ∀ a : Fin ((m+1)+(m+1)),
      (MvPolynomial.X a * MvPolynomial.C ((K:ℝ)⁻¹) :
        MvPolynomial (Fin ((m+1)+(m+1))) ℝ).totalDegree ≤ 1 :=
    fun a => (Work.WilG5.td_mul_le _ _).trans
      (le_trans (add_le_add (hX a) (Work.WilG5.td_C_le ((K:ℝ)⁻¹))) (by norm_num))
  have haff : ∀ a b : Fin ((m+1)+(m+1)),
      ((MvPolynomial.X a - MvPolynomial.C c - MvPolynomial.X b * MvPolynomial.C ((K:ℝ)⁻¹)) :
        MvPolynomial (Fin ((m+1)+(m+1))) ℝ).totalDegree ≤ 1 := by
    intro a b
    refine (Work.WilG5.td_sub_le (MvPolynomial.X a - MvPolynomial.C c)
      (MvPolynomial.X b * MvPolynomial.C ((K:ℝ)⁻¹))).trans ?_
    exact max_le (hsubC a) (hmulX b)
  have hsum : ((∑ i : Fin m, (MvPolynomial.X (Fin.natAdd (m+1) (Fin.castSucc i)) -
      MvPolynomial.X (Fin.castAdd (m+1) (Fin.castSucc i))) *
      (MvPolynomial.X (Fin.natAdd (m+1) (Fin.castSucc i)) -
      MvPolynomial.X (Fin.castAdd (m+1) (Fin.castSucc i))) :
      MvPolynomial (Fin ((m+1)+(m+1))) ℝ)).totalDegree ≤ 2 :=
    MvPolynomial.totalDegree_finsetSum_le (fun i _ => Work.WilG5.td_sq_le
      (hsub (Fin.natAdd (m+1) (Fin.castSucc i)) (Fin.castAdd (m+1) (Fin.castSucc i))))
  rw [crQ]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le hsum ?_)
  exact Work.WilG5.td_sq_le
    (haff (Fin.castAdd (m+1) (Fin.last m)) (Fin.natAdd (m+1) (Fin.last m)))

end Work.WilG4c
