import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseRowQ2.chatTailAux
import Submission.Work.BoseRowQ2.tailIdentity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.chatTail_eq_highMode` — the high-mode identity of the lattice tail

The lattice tail matrix of the sharp mask row (`maskTailDefs`) is

    `Tail N i j = Mc N i j − ∑_k Chat N k i · Chat N k j`,
    `Mc N i j = χ̂²(vec (K i − K j))`,   `Chat N k i = χ̂(vec (K k − K i))`

with `χ̂(p) = ∫χ(x)cos⟪p,x⟫` the corpus cosine transform and `K = labVec : Lab N → ℤ³`.

The theorem below evaluates the quadratic form of `Tail` on the vector
`c = ChatW N w` (`c k = ∑_i Chat N k i · w i`) as the sum of the *high-mode*
coefficients

    `highMode N w m = ∑_k c k · χ̂(vec (m − K k))`

over the dual-lattice points `m` **outside** the cube `[−N,N]³ ∩ ℤ³`:

    `∑_{k,j} c k c j Tail N k j = ∑_{m ∉ cube N} highMode N w m ^ 2`.

## The proof

The two halves of `Tail` are handled by the same lattice Parseval mechanism, in the
`tsum` form of the sibling `Work.BoseRowQ2.tailIdentity`:

    `Tail N i j = ∑'_{m ∉ cube N} χ̂(vec (m − K i))·χ̂(vec (m − K j))`.

So it suffices to expand the square on the right and exchange the (finite) `Lab N`-sum
with the (infinite) dual-lattice sum.  The exchange is legitimate because each pair
`m ↦ χ̂(vec (m − K i))·χ̂(vec (m − K j))` is *summable* on `ℤ³`: the corpus bump is
`C^∞` with compact support, so `χ̂` decays faster than any polynomial
(`Work.BoseK15.ChiReg_corpus`), giving domination by `C·(1 + ‖vec (m − a)‖²)^{-52}`
which is summable by the lattice estimate `Work.BoseK15.sum_inv_one_add_norm_le`.

Concretely: reindex the double `Lab N`-sum as a sum over `Lab N × Lab N`
(`Fintype.sum_prod_type`), replace each `Tail` entry by its `tsum` (`tailIdentity`),
pull the constants inside the `tsum`s (`tsum_mul_left`) and exchange the two
(`Summable.tsum_finsetSum`); the pointwise expansion of the square
(`highMode_sq`) turns the resulting summand into `highMode N w m ^ 2`.

The statement of this module is `chatTail_eq_highMode`; the whole file is
`sorry`-free and rests only on `propext`, `Classical.choice` and `Quot.sound`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

open Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Summability of the `χ̂`-pair on the dual lattice

The corpus bump is smooth with compact support, so `χ̂` is Schwartz; the product
`m ↦ χ̂(vec (m − a))·χ̂(vec (m − b))` is dominated by the (translated) summable
majorant `m ↦ C·(1 + ‖vec (m − a)‖²)^{-52}`, exactly as in
`Work.BoseRowQ2.tail_eq_tsum` / `tailIdentity`. -/

/-- **Summability of the shifted decay majorant.**  For every lattice shift `a : ℤ³`
the shifted majorant `m ↦ (1 + ‖vec (m − a)‖²)⁻⁵²` is summable: it is the translate of
the summable family `n ↦ (1 + ‖vec n‖²)⁻⁵²` (`Work.BoseK15.sum_inv_one_add_norm_le`). -/
private theorem summable_shift_majorant (a : Fin 3 → ℤ) :
    Summable (fun m : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec (m - a)‖ ^ 2) ^ 52)⁻¹) := by
  obtain ⟨C0, _hC0nn, hC0⟩ := Work.BoseK15.sum_inv_one_add_norm_le 52 (by norm_num)
  have hbase : Summable (fun n : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :=
    summable_of_sum_le (fun n => by positivity) hC0
  have h := (Equiv.summable_iff (Equiv.subRight a)
    (f := fun n : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹)).mpr hbase
  exact h.congr (fun m => by simp [Function.comp, Equiv.subRight_apply])

/-- **Summability of the `χ̂`-pair.**  For all lattice shifts `i, j : ℤ³` the family
`m ↦ χ̂(vec (m − i))·χ̂(vec (m − j))` is summable on `ℤ³`: the Schwartz decay of `χ̂`
(`Work.BoseK15.ChiReg_corpus` at order `52`) bounds it by
`C·(1 + ‖vec (m − i)‖²)⁻⁵²`, whose summability is `summable_shift_majorant`, the second
factor being bounded by `|χ̂| ≤ 1` (`chiHat_abs_le_one`). -/
private theorem summable_chat_pair (N : ℕ) (i j : Lab N) :
    Summable (fun m : Fin 3 → ℤ =>
      chiHat (Work.BoseB4.vec (m - labVec N i)) * chiHat (Work.BoseB4.vec (m - labVec N j))) := by
  obtain ⟨Cchi, hCchi0, hChi⟩ := Work.BoseK15.ChiReg_corpus 52
  have hChat_le : ∀ p : E3,
      |chiHat p| ≤ Cchi * (((1 : ℝ) + ‖p‖ ^ 2) ^ 52)⁻¹ := by
    intro p
    have hD : 0 < (1 + ‖p‖ ^ 2) ^ 52 := by positivity
    rw [chiHat]
    calc |Work.BoseK15.corpusBox.hatChi p|
        = |Work.BoseK15.corpusBox.hatChi p| * (1 + ‖p‖ ^ 2) ^ 52
            * ((1 + ‖p‖ ^ 2) ^ 52)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hD), mul_one]
      _ ≤ Cchi * ((1 + ‖p‖ ^ 2) ^ 52)⁻¹ :=
          mul_le_mul_of_nonneg_right (hChi.1 p) (inv_nonneg.mpr hD.le)
  refine Summable.of_norm_bounded (g := fun m : Fin 3 → ℤ =>
    Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (m - labVec N i)‖ ^ 2) ^ 52)⁻¹)
    ((summable_shift_majorant (labVec N i)).mul_left Cchi) ?_
  intro m
  rw [Real.norm_eq_abs, abs_mul]
  calc |chiHat (Work.BoseB4.vec (m - labVec N i))|
        * |chiHat (Work.BoseB4.vec (m - labVec N j))|
      ≤ (Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (m - labVec N i)‖ ^ 2) ^ 52)⁻¹) * 1 :=
        mul_le_mul (hChat_le _) (chiHat_abs_le_one _) (abs_nonneg _)
          (mul_nonneg hCchi0 (inv_nonneg.mpr (by positivity)))
    _ = Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (m - labVec N i)‖ ^ 2) ^ 52)⁻¹ := by ring

/-! ## 2. The two elementary rearrangements -/

/-- **Exchange of a finite sum with a `tsum`** (`s = Finset.univ` form of
`Summable.tsum_finsetSum`), with the summability of each fibre as an explicit
hypothesis. -/
private lemma tsum_sum_univ {ι : Type*} [Fintype ι] {β : Type*} (f : ι → β → ℝ)
    (h : ∀ i, Summable (f i)) :
    (∑ i, ∑' b, f i b) = ∑' b, ∑ i, f i b :=
  (Summable.tsum_finsetSum (s := Finset.univ) (f := f) (fun i _ => h i)).symm

/-- **The pointwise expansion of `highMode²`**: the square of the finite sum defining
`highMode N w m` is the double sum of the products `c k · c j · χ̂(vec (m − K k))·χ̂(vec (m − K j))`. -/
private lemma highMode_sq (N : ℕ) (w : Lab N → ℝ) (m : Fin 3 → ℤ) :
    highMode N w m ^ 2 = ∑ k : Lab N, ∑ j : Lab N,
      ChatW N w k * ChatW N w j *
        (chiHat (Work.BoseB4.vec (m - labVec N k)) * chiHat (Work.BoseB4.vec (m - labVec N j))) := by
  rw [pow_two, highMode, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## 3. The high-mode identity -/

/-- **The high-mode identity.**  With `c = ChatW N w` (`c k = ∑_i χ̂(vec (K k − K i)) w i`) the
quadratic form of the lattice tail matrix `Tail = Mc − ChatᵀChat` on `c` equals the sum of the
*high-mode* coefficients `highMode N w m = ∑_k c k · χ̂(vec (m − K k))` over the lattice points
`m ∉ cube N` (the complement of `[−N,N]³`).

Proof route.  `Work.BoseRowQ2.chatTail_quad_eq` (proved in `BoseRowQ2/chatTailAux.lean`) removes
`ChatᵀChat` and identifies it with `∑_j highMode N w (labVec N j)²`
(`highMode_labVec`, `sum_chatTchat` there).  For the `Mc` half, `Mc N k j = χ̂²(vec (K k − K j))`
and the shifted lattice Parseval identity (from `Work.BoseRowQ2.chiLatticeParseval`:
`∀ a b : ℤ³, ∑'_m χ̂(vec (m−a)) χ̂(vec (m−b)) = χ̂²(vec (a−b))`) turns
`∑_{k,j} c k c j Mc N k j` into `∑'_m (∑_k c k χ̂(vec (m−K k)))² = ∑'_m highMode N w m ^ 2`
(finite sums may be pulled through the `tsum` since each `m ↦ χ̂(...)·χ̂(...)` is summable,
e.g. via absolute convergence from `χ̂` Schwartz decay).  Finally the `tsum` over `ℤ³` is split
into the cube part (`∑_{j : Lab N} highMode N w (labVec N j)²`, using
`Work.BoseRowQ2.image_labVec_eq_cube` / `labVec_inj'`) and its complement.

Formally the same content is reached directly through the `tsum` form of the tail,
`Work.BoseRowQ2.tailIdentity`: the difference of the two halves is already written over the
complement of the cube, so no splitting of a full-lattice `tsum` is needed. -/
theorem chatTail_eq_highMode (N : ℕ) (w : Work.BoseBoxFock.Lab N → ℝ) :
    (∑ k : Work.BoseBoxFock.Lab N, ∑ j : Work.BoseBoxFock.Lab N,
        Work.BoseRowQ2.ChatW N w k * Work.BoseRowQ2.ChatW N w j
          * Work.BoseRowQ2.Tail N k j)
      = ∑' m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N},
          Work.BoseRowQ2.highMode N w m.val ^ 2 := by
  classical
  -- each pair fibre is summable on the complement of the cube
  have hsumm : ∀ p : Lab N × Lab N,
      Summable (fun m : {m : Fin 3 → ℤ // m ∉ cube N} =>
        ChatW N w p.1 * ChatW N w p.2 *
          (chiHat (Work.BoseB4.vec (m.val - labVec N p.1)) *
           chiHat (Work.BoseB4.vec (m.val - labVec N p.2)))) :=
    fun p => ((summable_chat_pair N p.1 p.2).subtype _).mul_left _
  calc (∑ k : Lab N, ∑ j : Lab N, ChatW N w k * ChatW N w j * Tail N k j)
      = ∑ p : Lab N × Lab N, ChatW N w p.1 * ChatW N w p.2 * Tail N p.1 p.2 :=
        (Fintype.sum_prod_type (fun p : Lab N × Lab N =>
          ChatW N w p.1 * ChatW N w p.2 * Tail N p.1 p.2)).symm
    _ = ∑ p : Lab N × Lab N, ∑' m : {m : Fin 3 → ℤ // m ∉ cube N},
          ChatW N w p.1 * ChatW N w p.2 *
            (chiHat (Work.BoseB4.vec (m.val - labVec N p.1)) *
             chiHat (Work.BoseB4.vec (m.val - labVec N p.2))) := by
        -- rewrite each tail entry by its dual-lattice `tsum` and pull the constant inside
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [tailIdentity, tsum_mul_left]
    _ = ∑' m : {m : Fin 3 → ℤ // m ∉ cube N}, ∑ p : Lab N × Lab N,
          ChatW N w p.1 * ChatW N w p.2 *
            (chiHat (Work.BoseB4.vec (m.val - labVec N p.1)) *
             chiHat (Work.BoseB4.vec (m.val - labVec N p.2))) :=
        -- exchange the finite `Lab N × Lab N`-sum with the dual-lattice `tsum`
        tsum_sum_univ _ hsumm
    _ = ∑' m : {m : Fin 3 → ℤ // m ∉ cube N}, highMode N w m.val ^ 2 := by
        -- the pointwise expansion of the square of `highMode`
        refine tsum_congr fun m => ?_
        rw [Fintype.sum_prod_type]
        exact (highMode_sq N w m.val).symm

end Work.BoseRowQ2
