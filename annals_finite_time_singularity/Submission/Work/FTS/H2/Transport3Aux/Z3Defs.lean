/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `D_z`-pairing with the order-five *and* the mismatch summands removed

This file fixes the vocabulary used by the proof of
`Work.FTS.H2.Transport3Aux.good_pointwise_z3`, the pointwise bound of the "good" part of
the `D_z`-transport pairing

  `H4PairInt α (fun z θ => f z θ * D_z g z θ) g z θ - Badz2 α f g z θ`,
  `Badz2 = Badz + Mismatchz`,

by `C |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g`.

Expanding `H4PairInt` by the Leibniz rules `DzIter_mul_Dz_eq` (the `D_z`-slots) and
`mixed_mul_Dz_eq` (the mixed slots) shows that

  `H4PairInt α (fun z θ => f z θ * D_z g z θ) g z θ - Badz α f g z θ`
    `= easyZ α f g z θ + easyM α f g z θ`,

the finite sums of the Leibniz terms `TZ` (the `D_z`-slots) resp. `TM` (the mixed slots)
with the five "all derivatives on `g`" summands — `TZ 4 0` and `TM i j 0 0` for
`1 ≤ i`, `i + j = 4` — removed (`Badz_eq_sum`).  The remaining work is the *mismatch*
family: the mixed summands in which all the `θ`-derivatives fall on `f`, i.e. `a = i`, for
**every** `b ∈ [0,j]` (the index condition in `Transport3Aux/Defs.lean` is
`1 ≤ i ∧ i + j ≤ 4`, with no lower bound on `b`).  Those are exactly the summands
`TM α f g i j i b`, whose `g`-block `mixed (j-b+1) 0 g` carries no `θ`-derivative while the
pairing weight is `Wm² = w² sin(2θ)^{-γ}`: they must be removed by the `θ`-integration by
parts of `Transport3Aux/Defs.lean`'s `Mismatchz`, not estimated pointwise.  Here

* `MismatchPart α f g i j` collects the `b`-th mismatch summands of the slot `(i,j)`, and
  `Mismatchz_eq` identifies `Mismatchz` with their sum over `1 ≤ i`, `i + j ≤ 4`
  (in the `(i,j)`-indexing of the pairing);
* `Msurv` is the mixed slot sum with the mismatch family (`a = i`) removed as well, so that
  every remaining summand has `a < i`, hence two `γ`-weighted `HkIntegrand`-blocks of total
  order `≤ 4`.

The pointwise bound is then the term-by-term estimate of `easyZ` and `Msurv`.

(This is a self-contained copy of the relevant vocabulary: the sibling
`T2EasyPart.lean` contains the analogous definitions for a different decomposition of the
same pairing and is not imported here.)
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.Transport3Aux.Defs
import Submission.Work.FTS.H2.Whz_Wm_sq
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux
namespace Z3

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The Leibniz summands of the `D_z`-pairing -/

/-- The `(i,k)`-th `D_z`-slot Leibniz summand of `H4PairInt α (f · D_z g) g`:
`binom(i,k) · D_z^k f · D_z^{i+1-k} g · D_z^i g · Whz²`, in exactly the bracketing in which
the Leibniz expansion of `(D_z^i (f D_z g) · Whz) · (D_z^i g · Whz)` produces it. -/
def TZ (α : ℝ) (f g : ℝ → ℝ → ℝ) (i k : ℕ) (z θ : ℝ) : ℝ :=
  (((i.choose k : ℝ) * (Work.Spaces.DzIter k f z θ * Work.Spaces.DzIter (i + 1 - k) g z θ))
      * Whz z θ) * (Work.Spaces.DzIter i g z θ * Whz z θ)

/-- The `(i,j,a,b)`-th mixed-slot Leibniz summand of `H4PairInt α (f · D_z g) g`:
`binom(i,a) binom(j,b) · D_z^bD_θ^a f · D_z^{j-b+1}D_θ^{i-a} g · D_z^jD_θ^i g · Wm²`. -/
def TM (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) (z θ : ℝ) : ℝ :=
  ((((i.choose a : ℝ) * (j.choose b : ℝ))
      * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b + 1) (i - a) g z θ))
      * Wm α z θ) * (Work.Spaces.mixed j i g z θ * Wm α z θ)

/-- The `D_z`-slot part of the good expansion: all the Leibniz summands of the `D_z`-slots
except the order-five one `(i,k) = (4,0)`. -/
def easyZ (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1),
    (if i = 4 ∧ k = 0 then 0 else TZ α f g i k z θ)

/-- The mixed-slot part of the good expansion: all the Leibniz summands of the mixed slots
except the order-five ones (`a = b = 0` with `i + j = 4`). -/
def easyM (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
    (if 1 ≤ i ∧ i + j ≤ 4 then
      ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else TM α f g i j a b z θ)
    else 0)

/-- The mismatch summands of the mixed slot `(i,j)`: all the `θ`-derivatives fall on `f`
(`a = i`), for every `b ∈ [0,j]`.  This is the sum to which `Mismatchz` reduces after the
`(i,j)`-sums are pulled out. -/
def MismatchPart (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j : ℕ) (z θ : ℝ) : ℝ :=
  ∑ b ∈ Finset.range (j + 1), (((i.choose i : ℝ) * (j.choose b : ℝ))
      * (Work.Spaces.mixed b i f z θ * Work.Spaces.mixed (j - b + 1) 0 g z θ))
      * (Work.Spaces.mixed j i g z θ * (Wm α z θ) ^ 2)

/-- The mixed-slot part of the good expansion with the mismatch family removed as well:
the summands with `a < i`. -/
def Msurv (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
    (if 1 ≤ i ∧ i + j ≤ 4 then
      ∑ a ∈ Finset.range i, ∑ b ∈ Finset.range (j + 1),
        (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else TM α f g i j a b z θ)
    else 0)

/-! ## The Leibniz rules for the factor `D_z g` -/

/-- `D_z^n (D_z g) = D_z^{n+1} g`. -/
theorem DzIter_Dz (n : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter n (Work.Spaces.Dz g) = Work.Spaces.DzIter (n + 1) g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.DzIter_succ k (Work.Spaces.Dz g), ih, Work.Spaces.DzIter_succ (k + 1) g]

/-- `D_z^m D_θ^n (D_z g) = D_z^{m+1} D_θ^n g` on the closed quadrant, for smooth `g`. -/
theorem mixed_Dz_apply (m n : ℕ) (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.mixed m n (Work.Spaces.Dz g) z θ = Work.Spaces.mixed (m + 1) n g z θ := by
  intro z hz θ hθ
  have h := Work.Spaces.mixed_comm g hg m n 1 0 z θ hz hθ
  simpa [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ] using h

/-- The Leibniz expansion of `D_z^i (f · D_z g)`. -/
theorem DzIter_mul_Dz_eq (i : ℕ) (f g : ℝ → ℝ → ℝ) (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
        = ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ)
            * (Work.Spaces.DzIter k f z θ * Work.Spaces.DzIter (i + 1 - k) g z θ) := by
  intro z hz θ hθ
  have h1 : ContDiffOn ℝ ⊤ (fun z => f z θ) (Set.Ioi (-1)) :=
    Work.Spaces.hardyZ_contDiffOn_slice f hf hθ
  have h2 : ContDiffOn ℝ ⊤ (fun z => Work.Spaces.Dz g z θ) (Set.Ioi (-1)) :=
    Work.Spaces.hardyZ_contDiffOn_slice (Work.Spaces.Dz g) (Work.Spaces.SmoothNbhd.Dz hg) hθ
  rw [Work.Spaces.DzIter_mul i f (Work.Spaces.Dz g) hz h1 h2]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [DzIter_Dz (i - k) g, show i - k + 1 = i + 1 - k by omega]

/-- The Leibniz expansion of `D_z^j D_θ^i (f · D_z g)`. -/
theorem mixed_mul_Dz_eq (j i : ℕ) (f g : ℝ → ℝ → ℝ) (hf : Work.Spaces.SmoothNbhd f)
    (hg : Work.Spaces.SmoothNbhd g) : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f z θ
                  * Work.Spaces.mixed (j - b + 1) (i - a) g z θ) := by
  intro z hz θ hθ
  rw [Work.Spaces.mixed_mul_eq j i f (Work.Spaces.Dz g)
    (Work.Spaces.SmoothInt.of_SmoothNbhd hf)
    (Work.Spaces.SmoothInt.of_SmoothNbhd (Work.Spaces.SmoothNbhd.Dz hg)) z hz θ hθ]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  rw [mixed_Dz_apply (j - b) (i - a) g hg z hz θ hθ]

/-! ## The identification of the removed summands with `Badz` and `Mismatchz` -/

/-- The `(i,k) = (4,0)` `D_z`-slot summand is the first summand of `Badz`. -/
theorem TZ_four_zero (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    TZ α f g 4 0 z θ
      = f z θ * Work.Spaces.Dz (Work.Spaces.DzIter 4 g) z θ
          * Work.Spaces.DzIter 4 g z θ * Whz z θ ^ 2 := by
  rw [TZ]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.reduceSub,
    Work.Spaces.DzIter_zero, Work.Spaces.DzIter_succ]
  ring

/-- The `(a,b) = (0,0)` mixed-slot summand is the "all derivatives on `g`" summand of the
mixed part of `Badz`. -/
theorem TM_zero_zero (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j : ℕ) (z θ : ℝ) :
    TM α f g i j 0 0 z θ
      = f z θ * Work.Spaces.Dz (Work.Spaces.mixed j i g) z θ
          * Work.Spaces.mixed j i g z θ * Wm α z θ ^ 2 := by
  rw [TM]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
    Work.Spaces.mixed, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero,
    Work.Spaces.DzIter_succ]
  ring

/-- The `(a,b) = (i,b)` mixed-slot summand is the `b`-th mismatch summand of `Mismatchz`. -/
theorem TM_mismatch (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j b : ℕ) (z θ : ℝ) :
    TM α f g i j i b z θ
      = (((i.choose i : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b i f z θ * Work.Spaces.mixed (j - b + 1) 0 g z θ))
          * (Work.Spaces.mixed j i g z θ * Wm α z θ ^ 2) := by
  rw [TM, Nat.sub_self]
  ring

/-- `Mismatchz` is the sum of the mismatch parts `MismatchPart α f g i j` over the slots
`(i,j)` with `1 ≤ i` and `i + j ≤ 4` of the pairing. -/
theorem Mismatchz_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Mismatchz α f g z θ
      = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then MismatchPart α f g i j z θ else 0) := by
  unfold Mismatchz MismatchPart
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  by_cases h : 1 ≤ i ∧ i + j ≤ 4
  · rw [if_pos h]
    exact Finset.sum_congr rfl fun b hb => by rw [if_pos h]
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun b hb => by rw [if_neg h]

end Z3
end Work.FTS.H2.Transport3Aux
