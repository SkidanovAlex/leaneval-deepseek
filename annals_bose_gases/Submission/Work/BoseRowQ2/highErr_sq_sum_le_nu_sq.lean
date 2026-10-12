import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowQ2.chatTailEst
import Submission.Work.BoseRowQ2.chiHat_sq_cubeCompl_le_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

open Work.BoseBoxFock

local notation "Z3" => Fin 3 → ℤ

/-! ## Auxiliary lemmas

The proof of `highErr_sq_sum_le_nu_sq` runs through four auxiliary facts:

* `sq_tsum_mul_le_tsum_mul_sq` — the *weighted* Cauchy–Schwarz inequality for lattice sums, the
  quantitative form of `(∑_k c_k b_k)² ≤ (∑_k c_k)(∑_k c_k b_k²)` under the bound `0 ≤ β ≤ 1`;
* `finset_tsum_le` — the Fubini step for a *finite* sum against a `tsum`, proved by induction on
  the finset (the `Summable.tsum_finsetSum` of Mathlib is avoided because its implicit
  `SummationFilter` argument makes the unification prohibitively expensive);
* `summable_abs_Fhat_compl` — the Schwartz summability of `F̂` over the complement of the cube
  (so that `nu` is an honest `ℓ¹`-mass), obtained from the shifted `|χ̂|`-summability of
  `Work.BoseRowQ2.chatTailEst` by domination;
* `finset_tsum_mul_sq_le` — the `ℓ¹`-bound `∑_{m ∈ F} ∑_k |F̂ k| χ̂(vec (m−k))² ≤ nu` for every
  *finite* set `F` of lattice points outside the cube: the finite `m`-sum is moved inside the
  `k`-sum (`finset_tsum_le`), and each resulting inner sum
  `∑_{m ∈ F} χ̂(vec (m−k))² ≤ ∑_{m ∉ cube} χ̂(vec (m−k))² ≤ 1` is
  `Work.BoseRowQ2.chiHat_sq_cubeCompl_le_one`.
-/

/-- **Weighted Cauchy–Schwarz for lattice sums.**  For a nonnegative summable weight `α` and a
nonnegative `β` bounded by `1`,

    `(∑'_i α i · β i)² ≤ (∑'_i α i) · (∑'_i α i · β i²)`.

The proof is the elementary one: Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`, with the
square roots `√α` and `√α·β`) bounds every finite partial sum, and `Real.tsum_le_of_sum_le`
passes to the sum. -/
theorem sq_tsum_mul_le_tsum_mul_sq {ι : Type*} (α β : ι → ℝ) (hα : ∀ i, 0 ≤ α i)
    (hβ : ∀ i, 0 ≤ β i) (hβ1 : ∀ i, β i ≤ 1) (hαs : Summable α) :
    (∑' i, α i * β i) ^ 2 ≤ (∑' i, α i) * (∑' i, α i * β i ^ 2) := by
  have hβs : Summable fun i => α i * β i :=
    hαs.of_nonneg_of_le (fun i => mul_nonneg (hα i) (hβ i))
      (fun i => by simpa using mul_le_mul_of_nonneg_left (hβ1 i) (hα i))
  have hβ2 : Summable fun i => α i * β i ^ 2 :=
    hαs.of_nonneg_of_le (fun i => mul_nonneg (hα i) (sq_nonneg _))
      (fun i => by
        have h2 : β i ^ 2 ≤ (1 : ℝ) := by nlinarith [hβ i, hβ1 i]
        simpa using mul_le_mul_of_nonneg_left h2 (hα i))
  have hnu : 0 ≤ ∑' i, α i := tsum_nonneg hα
  have hB : 0 ≤ ∑' i, α i * β i ^ 2 := tsum_nonneg fun i => mul_nonneg (hα i) (sq_nonneg _)
  have hstep : ∀ G : Finset ι, (∑ i ∈ G, α i * β i) ^ 2
      ≤ (∑' i, α i) * (∑' i, α i * β i ^ 2) := by
    intro G
    have hCS : (∑ i ∈ G, α i * β i) ^ 2
        ≤ (∑ i ∈ G, α i) * (∑ i ∈ G, α i * β i ^ 2) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq G (fun i => Real.sqrt (α i))
        (fun i => Real.sqrt (α i) * β i)
      have e1 : ∀ i, Real.sqrt (α i) * (Real.sqrt (α i) * β i) = α i * β i := by
        intro i
        have h1 : Real.sqrt (α i) * Real.sqrt (α i) = α i := by
          rw [← sq, Real.sq_sqrt (hα i)]
        rw [← mul_assoc, h1]
      have e2 : ∀ i, Real.sqrt (α i) ^ 2 = α i := fun i => Real.sq_sqrt (hα i)
      have e3 : ∀ i, (Real.sqrt (α i) * β i) ^ 2 = α i * β i ^ 2 := by
        intro i
        rw [mul_pow, Real.sq_sqrt (hα i)]
      simpa only [e1, e2, e3] using h
    have h1 : (∑ i ∈ G, α i) ≤ ∑' i, α i :=
      hαs.sum_le_tsum G fun i _ => hα i
    have h2 : (∑ i ∈ G, α i * β i ^ 2) ≤ ∑' i, α i * β i ^ 2 :=
      hβ2.sum_le_tsum G fun i _ => mul_nonneg (hα i) (sq_nonneg _)
    exact hCS.trans (mul_le_mul h1 h2 (Finset.sum_nonneg fun i _ => mul_nonneg (hα i) (sq_nonneg _))
      hnu)
  have hA : ∑' i, α i * β i ≤ Real.sqrt ((∑' i, α i) * (∑' i, α i * β i ^ 2)) :=
    Real.tsum_le_of_sum_le (fun i => mul_nonneg (hα i) (hβ i)) fun G =>
      Real.le_sqrt_of_sq_le (hstep G)
  calc (∑' i, α i * β i) ^ 2
      ≤ Real.sqrt ((∑' i, α i) * (∑' i, α i * β i ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (tsum_nonneg fun i => mul_nonneg (hα i) (hβ i)) hA 2
    _ = (∑' i, α i) * (∑' i, α i * β i ^ 2) := Real.sq_sqrt (mul_nonneg hnu hB)

/-- **Fubini for a finite sum against a `tsum`.**  For a finset `F` and a family `f` whose
`k`-fibers are summable,

    `∑_{m ∈ F} ∑'_k f m k ≤ ∑'_k ∑_{m ∈ F} f m k`.

Proof by induction on `F`, using `Summable.tsum_add` for the induction step (the sum of the two
fiber sums is summable by `summable_sum`). -/
private theorem finset_tsum_le {κ ι : Type*} [DecidableEq κ] {f : κ → ι → ℝ}
    (F : Finset κ) (hF : ∀ m ∈ F, Summable (f m)) :
    (∑ m ∈ F, ∑' k, f m k) ≤ ∑' k, ∑ m ∈ F, f m k := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hsa : Summable (f a) := hF a (Finset.mem_insert_self a s)
      have hs : Summable (fun k => ∑ m ∈ s, f m k) :=
        summable_sum fun m hm => hF m (Finset.mem_insert_of_mem hm)
      have ihs := ih (fun m hm => hF m (Finset.mem_insert_of_mem hm))
      calc (∑ m ∈ insert a s, ∑' k, f m k)
          = (∑' k, f a k) + ∑ m ∈ s, ∑' k, f m k := by rw [Finset.sum_insert ha]
        _ ≤ (∑' k, f a k) + ∑' k, ∑ m ∈ s, f m k := add_le_add (le_refl _) ihs
        _ = ∑' k, (f a k + ∑ m ∈ s, f m k) := (Summable.tsum_add hsa hs).symm
        _ = ∑' k, ∑ m ∈ insert a s, f m k := by
              refine tsum_congr fun k => ?_
              rw [Finset.sum_insert ha]

/-- The absolute mass of the high part of `F̂` is summable over the complement of the cube: `F̂ k`
is the finite combination `∑_i w i · χ̂(vec (k − K i))` of lattice shifts of the Schwartz
function `χ̂` (`Work.BoseRowQ2.chatTailEst.summable_chiHat_abs_shift`), and a finite sum of
summable functions is summable. -/
private theorem summable_abs_Fhat_compl (N : ℕ) (w : Lab N → ℝ) :
    Summable (fun k : {k : Z3 // k ∉ cube N} => |Fhat N w k.val|) := by
  have hmaj : Summable (fun k : {k : Z3 // k ∉ cube N} =>
      ∑ i : Lab N, |w i| * |chiHat (Work.BoseB4.vec (k.val - labVec N i))|) :=
    summable_sum fun i _ =>
      ((summable_chiHat_abs_shift (labVec N i)).subtype _).mul_left (|w i|)
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hmaj
  calc |Fhat N w k.val|
      = |∑ i : Lab N, w i * chiHat (Work.BoseB4.vec (k.val - labVec N i))| := rfl
    _ ≤ ∑ i : Lab N, |w i * chiHat (Work.BoseB4.vec (k.val - labVec N i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Lab N, |w i| * |chiHat (Work.BoseB4.vec (k.val - labVec N i))| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul]

/-- **Pointwise bound of the truncation error.**  `|highErr N w m| ≤ ∑'_{k ∉ cube} |F̂ k|·|χ̂(vec (m−k))|`:
the triangle inequality for `tsum` (`norm_tsum_le_tsum_norm`), the summand being absolutely
summable by `summable_abs_Fhat_compl` and `|χ̂| ≤ 1`. -/
private theorem abs_highErr_le (N : ℕ) (w : Lab N → ℝ) (m : Z3) :
    |highErr N w m| ≤ ∑' k : {k : Z3 // k ∉ cube N},
      |Fhat N w k.val| * |chiHat (Work.BoseB4.vec (m - k.val))| := by
  have hdef : highErr N w m = ∑' k : {k : Z3 // k ∉ cube N},
      Fhat N w k.val * chiHat (Work.BoseB4.vec (m - k.val)) := rfl
  have hcn : Summable (fun k : {k : Z3 // k ∉ cube N} =>
      ‖Fhat N w k.val * chiHat (Work.BoseB4.vec (m - k.val))‖) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (chiHat_abs_le_one _))
      (summable_abs_Fhat_compl N w)
  rw [hdef]
  calc |∑' k : {k : Z3 // k ∉ cube N}, Fhat N w k.val * chiHat (Work.BoseB4.vec (m - k.val))|
      = ‖∑' k : {k : Z3 // k ∉ cube N},
          Fhat N w k.val * chiHat (Work.BoseB4.vec (m - k.val))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : {k : Z3 // k ∉ cube N},
          ‖Fhat N w k.val * chiHat (Work.BoseB4.vec (m - k.val))‖ :=
        norm_tsum_le_tsum_norm hcn
    _ = ∑' k : {k : Z3 // k ∉ cube N},
          |Fhat N w k.val| * |chiHat (Work.BoseB4.vec (m - k.val))| := by
        refine tsum_congr fun k => ?_
        rw [Real.norm_eq_abs, abs_mul]

/-- **The `ℓ¹`-bound of the weighted mass on a finite set.**  For every finite set `F` of lattice
points outside the cube,

    `∑_{m ∈ F} ∑'_{k ∉ cube} |F̂ k| · χ̂(vec (m−k))² ≤ nu N w`.

The finite `m`-sum is moved inside the `k`-sum (`finset_tsum_le`, the `m`-fibers being dominated
by `|F̂|`), leaving `∑_{m ∈ F} χ̂(vec (m−k))²` for each `k`, which is at most `1` by
`Work.BoseRowQ2.chiHat_sq_cubeCompl_le_one`. -/
private theorem finset_tsum_mul_sq_le (N : ℕ) (w : Lab N → ℝ)
    (F : Finset {m : Z3 // m ∉ cube N}) :
    (∑ m ∈ F, ∑' k : {k : Z3 // k ∉ cube N},
        |Fhat N w k.val| * chiHat (Work.BoseB4.vec (m.val - k.val)) ^ 2) ≤ nu N w := by
  have hFhat : Summable (fun k : {k : Z3 // k ∉ cube N} => |Fhat N w k.val|) :=
    summable_abs_Fhat_compl N w
  have hsq1 : ∀ p : EuclideanSpace ℝ (Fin 3), chiHat p ^ 2 ≤ (1 : ℝ) := fun p => by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (chiHat_abs_le_one p)
  have hk : ∀ m : {m : Z3 // m ∉ cube N}, Summable (fun k : {k : Z3 // k ∉ cube N} =>
      |Fhat N w k.val| * chiHat (Work.BoseB4.vec (m.val - k.val)) ^ 2) := by
    intro m
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (fun k => mul_le_of_le_one_right (abs_nonneg _) (hsq1 _)) hFhat
  have hb1 : ∀ k : {k : Z3 // k ∉ cube N},
      (∑ m ∈ F, chiHat (Work.BoseB4.vec (m.val - k.val)) ^ 2) ≤ 1 := by
    intro k
    refine le_trans (Summable.sum_le_tsum F (fun m _ => sq_nonneg _)
      ((summable_chiHat_sq_shift (k.val)).subtype _)) ?_
    exact chiHat_sq_cubeCompl_le_one N k.val
  have hL : Summable (fun k : {k : Z3 // k ∉ cube N} =>
      |Fhat N w k.val| * (∑ m ∈ F, chiHat (Work.BoseB4.vec (m.val - k.val)) ^ 2)) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun m _ => sq_nonneg _))
      (fun k => mul_le_of_le_one_right (abs_nonneg _) (hb1 k)) hFhat
  refine (finset_tsum_le F fun m _ => hk m).trans ?_
  calc (∑' k : {k : Z3 // k ∉ cube N}, ∑ m ∈ F,
          |Fhat N w k.val| * chiHat (Work.BoseB4.vec (m.val - k.val)) ^ 2)
      = ∑' k : {k : Z3 // k ∉ cube N}, |Fhat N w k.val| *
          (∑ m ∈ F, chiHat (Work.BoseB4.vec (m.val - k.val)) ^ 2) :=
        tsum_congr fun k =>
          (Finset.mul_sum F (fun m => chiHat (Work.BoseB4.vec (m.val - k.val)) ^ 2)
            (|Fhat N w k.val|)).symm
    _ ≤ ∑' k : {k : Z3 // k ∉ cube N}, |Fhat N w k.val| := by
        refine Summable.tsum_le_tsum (fun k => ?_) hL hFhat
        simpa using mul_le_mul_of_nonneg_left (hb1 k) (abs_nonneg _)
    _ = nu N w := rfl

/-- **The `ℓ²`-bound of the truncation error by the `ℓ¹`-mass of the high part of `F̂`.**  With
`highErr N w m = ∑'_{k ∉ cube N} F̂(k) χ̂(vec (m−k))` and `nu N w = ∑'_{k ∉ cube N} |F̂(k)|`, one has

    `∑_{m ∉ cube N} highErr N w m ^ 2 ≤ (nu N w) ^ 2`.

Route (the coefficient-level Parseval identity, the same mechanism as
`chatTail_eq_highMode`): the left side is `≤ ∑'_m (∑'_{k ∉ cube} |F̂(k)| |χ̂(vec (m−k))|)²`; expanding
the square and interchanging the `m`-sum with the (absolutely convergent, dominated by the Schwartz
decay of `χ̂`) `k, k'`-sums gives `∑'_{k, k' ∉ cube} |F̂(k)| |F̂(k')| · (∑'_m χ̂(vec (m−k)) χ̂(vec (m−k')))`,
and the inner sum over *all* `m : ℤ³` is `χ̂²(vec (k−k'))` by `Work.BoseRowQ2.chiLatticeParseval`
(shifted form), whose absolute value is at most `1` (`Work.BoseRowQ2.chiHatSq_abs_le_one`).
**Caveat for the prover**: the Parseval evaluation is for the sum over all of `ℤ³`; the *restricted*
sum over `m ∉ cube N` must be compared with the full one by nonnegativity (indicator argument).
So the whole sum is at most `(∑'_{k ∉ cube} |F̂(k)|)² = nu ^ 2`. -/
theorem highErr_sq_sum_le_nu_sq (N : ℕ) (w : Work.BoseBoxFock.Lab N → ℝ) :
    (∑' m : {m : Fin 3 → ℤ // m ∉ Work.BoseRowQ2.cube N},
        Work.BoseRowQ2.highErr N w m.val ^ 2)
      ≤ Work.BoseRowQ2.nu N w ^ 2 := by
  have hnu : 0 ≤ nu N w := tsum_nonneg fun k => abs_nonneg _
  have hnu_eq : nu N w = ∑' k : {k : Z3 // k ∉ cube N}, |Fhat N w k.val| := rfl
  refine Real.tsum_le_of_sum_le (fun m => sq_nonneg _) fun F => ?_
  have hpt : ∀ m ∈ F, highErr N w m.val ^ 2 ≤ nu N w *
      (∑' k : {k : Z3 // k ∉ cube N},
        |Fhat N w k.val| * chiHat (Work.BoseB4.vec (m.val - k.val)) ^ 2) := by
    intro m _
    have hcs := sq_tsum_mul_le_tsum_mul_sq (fun k : {k : Z3 // k ∉ cube N} => |Fhat N w k.val|)
      (fun k : {k : Z3 // k ∉ cube N} => |chiHat (Work.BoseB4.vec (m.val - k.val))|)
      (fun k => abs_nonneg _) (fun k => abs_nonneg _) (fun k => chiHat_abs_le_one _)
      (summable_abs_Fhat_compl N w)
    calc highErr N w m.val ^ 2
        = |highErr N w m.val| ^ 2 := (sq_abs _).symm
      _ ≤ (∑' k : {k : Z3 // k ∉ cube N},
            |Fhat N w k.val| * |chiHat (Work.BoseB4.vec (m.val - k.val))|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_highErr_le N w m.val) 2
      _ ≤ (∑' k : {k : Z3 // k ∉ cube N}, |Fhat N w k.val|) *
            (∑' k : {k : Z3 // k ∉ cube N},
              |Fhat N w k.val| * |chiHat (Work.BoseB4.vec (m.val - k.val))| ^ 2) := hcs
      _ = nu N w * (∑' k : {k : Z3 // k ∉ cube N},
              |Fhat N w k.val| * chiHat (Work.BoseB4.vec (m.val - k.val)) ^ 2) := by
          rw [hnu_eq]
          refine congrArg (fun t => (∑' k : {k : Z3 // k ∉ cube N}, |Fhat N w k.val|) * t) ?_
          exact tsum_congr fun k =>
            congrArg (fun t => |Fhat N w k.val| * t) (sq_abs _)
  calc (∑ m ∈ F, highErr N w m.val ^ 2)
      ≤ ∑ m ∈ F, nu N w * (∑' k : {k : Z3 // k ∉ cube N},
          |Fhat N w k.val| * chiHat (Work.BoseB4.vec (m.val - k.val)) ^ 2) :=
        Finset.sum_le_sum hpt
    _ = nu N w * (∑ m ∈ F, ∑' k : {k : Z3 // k ∉ cube N},
          |Fhat N w k.val| * chiHat (Work.BoseB4.vec (m.val - k.val)) ^ 2) :=
        (Finset.mul_sum F _ (nu N w)).symm
    _ ≤ nu N w * nu N w := mul_le_mul_of_nonneg_left (finset_tsum_mul_sq_le N w F) hnu
    _ = nu N w ^ 2 := by ring

end Work.BoseRowQ2
