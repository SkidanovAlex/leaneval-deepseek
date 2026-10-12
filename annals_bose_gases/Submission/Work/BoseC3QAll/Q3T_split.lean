import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Data.Real.Basic
import Submission.Work.BoseC3QAll.SubstHyp
import Submission.Work.BoseC3QAll.bCommutatorDag_swap_s
import Submission.Work.BoseC3QAll.bCommutator_swap_s
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseC3QAll.Q3T_split` — FS `lem:EstimatesOnQ3-js` in the θ-mode slot

FS §10 (`lem:EstimatesOnQ3-js`) rewrites the cubic word `Q3(z)` of
`eq:kroelleQ3z` in terms of the squeezed modes `b_k = a_k + α_k a_{-k}†`
(`eq:Defb_k`) and splits it into four pieces `Q3^(1) … Q3^(4)`.  This module
proves that splitting as an identity of operators on the `B7A` interface:

`T.Q3T E = T.Q3oneT E + T.Q3twoT E + T.Q3threeT E + T.Q3fourT E`

(`Work.BoseB7A.TildeData.Q3T`, `Q3oneT`, `Q3twoT`, `Q3threeT`, `Q3fourT` of
`Work.BoseB7AK.Defs`), under the algebra-only hypotheses `SubstHypG` of FS §10.
This is the `BoseB7A` (θ-mode slot `ã_s`) version of the retired `B7` chapter's
`Work.BoseB7.Q3_split`; only the `s`-slot operators differ (`T.taDag s`, `T.ta s`
instead of `F.aDag s`, `F.a s`), and the mode arithmetic of the two `k`-slots
(`k`, `s − k`) is identical, so the same computation applies verbatim.

## The computation

The substitution is FS's `eq:asInTermsOfbs` (`Work.BoseB7.a_eq`,
`Work.BoseB7.aDag_eq`, here in the `SubstHypG` form `a_eq_of_ne`, `aDag_eq_of_ne`)

`a_k = (1-α_k²)⁻¹ (b_k - α_k b_{-k}†)`,  `a_k† = (1-α_k²)⁻¹ (b_k† - α_k b_{-k})`,

applied **only** to the two `k`-modes `k` and `s - k` of the two cubic
monomials; the localised θ-mode is kept (`ã_s†`, `ã_s` are untouched), which is
exactly how the four pieces are written (the denominators `1-α_k²` are non-zero
on the pairs `(s,k)` that occur, i.e. `f_L(s) ≠ 0`, `k ∈ P_H`, by
`SubstHypG.denom_ne`).

Expanding `(b_{s-k} - α_{s-k}b_{k-s}†)(b_k - α_kb_{-k}†)` produces the `bb` and
`b†b†` pieces directly, but the two "cross" terms come out with the order of the
`b`'s reversed, so the computation needs the squeezed commutators

`[b_{s-k}, b_{-k}†] = [b_{-k}, b_{s-k}†] = (1-α_kα_{s-k})(χ̂²(s) - χ̂(k)χ̂(s-k)) • 1`

(`Work.BoseC3QAll.bCommutator_swap_s`, `Work.BoseC3QAll.bCommutatorDag_swap_s`: FS's
kernel computation, a real multiple of the identity).  Hence the leftover
`-α_k[b_{s-k},b_{-k}†]∘ã_s†` from the first monomial and its adjoint
`-α_k[b_{-k},b_{s-k}†]∘ã_s` from the second recombine into

`-α_k[b_{s-k},b_{-k}†]∘(ã_s† + ã_s)`,

which is exactly the `Q3^(4)` summand (FS's "commutator piece").  The equality
of the two commutators is where the kernel hypothesis `SubstHypG.hasKernel`
(FS `eq:Commutator_general`) and the parity of `χ̂`, `χ̂²`
(`SubstHypG.hatChi_even`, `SubstHypG.hatChiSq_even`) are used.

## Contents

* `a_eq_of_ne`, `aDag_eq_of_ne` — FS `eq:asInTermsOfbs` under just the
  non-vanishing of `1 - α_k²` and evenness of `α`.
* `qtermT_split_apply` — the `(s,k)` summand, pointwise.
* `qtermT_split` — the same, as operators on `F.H`.
* `Q3T_split` — the sum over the mode lattice, i.e. `lem:EstimatesOnQ3-js`.
-/

noncomputable section

open scoped BigOperators

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Work.BoseC3QAll

open Work.BoseB7

/-! ## 1. The substitution `a_k = (1-α_k²)⁻¹(b_k - α_k b_{-k}†)` under `SubstHypG`

`Work.BoseB7.a_eq`/`aDag_eq` take the bundled `EstHyp`; the substitution itself
only needs the non-vanishing of the denominator and the parity of `α`. -/

/-- FS `eq:asInTermsOfbs` (annihilation half), with the two hypotheses the
computation actually consumes: `α` even and `1 - α_i² ≠ 0`. -/
theorem a_eq_of_ne {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (i : Mode)
    (hα : E.alpha (-i) = E.alpha i) (hne : 1 - E.alpha i ^ 2 ≠ 0) :
    F.a i = (1 - E.alpha i ^ 2)⁻¹ • (F.bOp E.alpha i - (E.alpha i) • F.bOpDag E.alpha (-i)) := by
  ext φ
  simp only [FockData.bOp, FockData.bOpDag, hα, neg_neg, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.add_apply]
  set A := F.a i φ
  set C := F.aDag (-i) φ
  set a := E.alpha i
  -- the cancellation `(a + α a†) - α(a† + α a) = (1-α²) a`, pointwise
  have hinner : A + a • C - a • (C + a • A) = (1 - a ^ 2) • A := by
    rw [smul_add, smul_smul, sq, sub_smul, one_smul]
    abel
  rw [hinner, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- FS `eq:asInTermsOfbs` (creation half), with the two hypotheses the
computation actually consumes. -/
theorem aDag_eq_of_ne {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (i : Mode)
    (hα : E.alpha (-i) = E.alpha i) (hne : 1 - E.alpha i ^ 2 ≠ 0) :
    F.aDag i = (1 - E.alpha i ^ 2)⁻¹ • (F.bOpDag E.alpha i - (E.alpha i) • F.bOp E.alpha (-i)) := by
  have hkey : F.bOpDag E.alpha i - (E.alpha i) • F.bOp E.alpha (-i)
      = (1 - E.alpha i ^ 2) • F.aDag i := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
      FockData.bOp, FockData.bOpDag, hα, neg_neg]
    module
  rw [hkey, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-! ## 2. The splitting of one `(s,k)` summand -/

/-- **The `(s,k)` summand of FS `lem:EstimatesOnQ3-js`** (θ-mode slot): the two
cubic monomials `ã_s†a_{s-k}a_k + a_k†a_{s-k}†ã_s`, rewritten in the `b`'s.  This
is the algebraic heart of the four estimates: every piece of
`Q3^(1) … Q3^(4)` appears with its FS coefficient, and the fourth piece is
exactly the commutator term `-α_k[b_{s-k},b_{-k}†]∘(ã_s† + ã_s)`.

The denominators `1-α_k²`, `1-α_{s-k}²` are assumed non-zero (they are, on the
pairs that occur, by `SubstHypG.denom_ne`). -/
theorem qtermT_split_apply {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (h : SubstHypG F T E)
    (s k : Mode) (hk : 1 - E.alpha k ^ 2 ≠ 0) (hsk : 1 - E.alpha (s - k) ^ 2 ≠ 0)
    (hfL : E.fL s ≠ 0) (hkPH : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) (x : F.H) :
    (T.qtermT s k + T.qtermDagT s k) x
      = (E.q3Denom s k) •
        ( (T.taDag s ∘ₗ (F.bOp E.alpha (s - k) ∘ₗ F.bOp E.alpha k)
          + (E.alpha k * E.alpha (s - k)) • (T.taDag s ∘ₗ (F.bOpDag E.alpha (k - s) ∘ₗ F.bOpDag E.alpha (-k)))
          + F.bOpDag E.alpha k ∘ₗ (F.bOpDag E.alpha (s - k) ∘ₗ T.ta s)
          + (E.alpha k * E.alpha (s - k)) • (F.bOp E.alpha (-k) ∘ₗ (F.bOp E.alpha (k - s) ∘ₗ T.ta s))
          - (E.alpha k) • (T.taDag s ∘ₗ (F.bOpDag E.alpha (-k) ∘ₗ F.bOp E.alpha (s - k))
              + F.bOpDag E.alpha (s - k) ∘ₗ (F.bOp E.alpha (-k) ∘ₗ T.ta s))
          - (E.alpha (s - k)) • (T.taDag s ∘ₗ (F.bOpDag E.alpha (k - s) ∘ₗ F.bOp E.alpha k)
              + F.bOpDag E.alpha k ∘ₗ (F.bOp E.alpha (k - s) ∘ₗ T.ta s))
          - (E.alpha k) • (F.bCommutator E s k ∘ₗ (T.taDag s + T.ta s)) ) x) := by
  -- unfold the two cubic monomials and the four pieces
  simp only [Work.BoseB7A.TildeData.qtermT, Work.BoseB7A.TildeData.qtermDagT, FockData.bCommutator,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  -- substitute `a_k`, `a_k†`, `a_{s-k}`, `a_{s-k}†` (the θ-modes `ã_s`, `ã_s†` are kept)
  rw [a_eq_of_ne F E k (h.alpha_even k) hk, a_eq_of_ne F E (s - k) (h.alpha_even (s - k)) hsk,
    aDag_eq_of_ne F E k (h.alpha_even k) hk,
    aDag_eq_of_ne F E (s - k) (h.alpha_even (s - k)) hsk]
  -- expand all the linearity: turns into scalar multiples of the eight `b`-monomials
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_add, map_sub,
    map_smul, smul_add, smul_sub, smul_smul, neg_sub]
  -- the two cross terms: move `b_{-k}†` past `b_{s-k}` (resp. `b_{-k}` past `b_{s-k}†`)
  simp only [bCommutator_swap_s F E s k (h.kerA s k hfL hkPH hW) (h.kerB s k hfL hkPH hW)
      h.hatChi_even h.alpha_even,
    bCommutatorDag_swap_s F E s k (h.kerA' s k hfL hkPH hW) (h.kerB' s k hfL hkPH hW)
      h.hatChi_even h.alpha_even]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_add, map_sub, map_smul, smul_add,
    smul_sub, smul_smul]
  -- `q3Denom = (1-α_k²)⁻¹(1-α_{s-k}²)⁻¹`
  rw [show E.q3Denom s k = (1 - E.alpha k ^ 2)⁻¹ * (1 - E.alpha (s - k) ^ 2)⁻¹ from by
    simp only [Q3Env.q3Denom, one_div, mul_inv_rev]
    ring]
  module

/-- `qtermT_split_apply` as an identity of operators on one `(s,k)`. -/
theorem qtermT_split {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (h : SubstHypG F T E)
    (s k : Mode) (hk : 1 - E.alpha k ^ 2 ≠ 0) (hsk : 1 - E.alpha (s - k) ^ 2 ≠ 0)
    (hfL : E.fL s ≠ 0) (hkPH : k ∈ F.PHset E) (hW : E.W1 k ≠ 0) :
    T.qtermT s k + T.qtermDagT s k
      = (E.q3Denom s k) •
        ( T.taDag s ∘ₗ (F.bOp E.alpha (s - k) ∘ₗ F.bOp E.alpha k)
          + (E.alpha k * E.alpha (s - k)) • (T.taDag s ∘ₗ (F.bOpDag E.alpha (k - s) ∘ₗ F.bOpDag E.alpha (-k)))
          + F.bOpDag E.alpha k ∘ₗ (F.bOpDag E.alpha (s - k) ∘ₗ T.ta s)
          + (E.alpha k * E.alpha (s - k)) • (F.bOp E.alpha (-k) ∘ₗ (F.bOp E.alpha (k - s) ∘ₗ T.ta s))
          - (E.alpha k) • (T.taDag s ∘ₗ (F.bOpDag E.alpha (-k) ∘ₗ F.bOp E.alpha (s - k))
              + F.bOpDag E.alpha (s - k) ∘ₗ (F.bOp E.alpha (-k) ∘ₗ T.ta s))
          - (E.alpha (s - k)) • (T.taDag s ∘ₗ (F.bOpDag E.alpha (k - s) ∘ₗ F.bOp E.alpha k)
              + F.bOpDag E.alpha k ∘ₗ (F.bOp E.alpha (k - s) ∘ₗ T.ta s))
          - (E.alpha k) • (F.bCommutator E s k ∘ₗ (T.taDag s + T.ta s)) ) := by
  ext x
  rw [LinearMap.smul_apply]
  exact qtermT_split_apply F T E h s k hk hsk hfL hkPH hW x

/-! ## 3. Summing over the lattice: FS `lem:EstimatesOnQ3-js` -/

/-- **FS `lem:EstimatesOnQ3-js`**: the cubic word `Q3T` of `eq:kroelleQ3z` is
the sum of its four pieces `Q3oneT … Q3fourT`, obtained by the Bogoliubov
substitution `a_k = (1-α_k²)⁻¹(b_k - α_k b_{-k}†)` in the two `k`-modes.

Each `(s,k)` summand of `Q3T` carries the weight `f_L(s)Ŵ₁(k)`; multiplying
`qtermT_split` by it and regrouping the scalars gives exactly the summands of
`Q3oneT … Q3fourT`, so the double sums over `s` and `k ∈ P_H` can be added
summand by summand.  (The substitution denominators are non-zero on the pairs
occurring in the sum by `SubstHypG.denom_ne`; for `f_L(s) = 0` the summand
vanishes identically.) -/
theorem Q3T_split {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (h : Work.BoseC3QAll.SubstHypG F T E) :
    T.Q3T E = T.Q3oneT E + T.Q3twoT E + T.Q3threeT E + T.Q3fourT E := by
  -- the four summands of `Q3oneT … Q3fourT`, as functions of `(s,k)`
  let P1 : Mode → Mode → F.H →ₗ[ℝ] F.H := fun s k =>
    (E.fL s * E.W1 k * E.q3Denom s k) •
      (T.taDag s ∘ₗ (F.bOp E.alpha (s - k) ∘ₗ F.bOp E.alpha k)
        + (E.alpha k * E.alpha (s - k)) • (T.taDag s ∘ₗ (F.bOpDag E.alpha (k - s) ∘ₗ F.bOpDag E.alpha (-k)))
        + F.bOpDag E.alpha k ∘ₗ (F.bOpDag E.alpha (s - k) ∘ₗ T.ta s)
        + (E.alpha k * E.alpha (s - k)) • (F.bOp E.alpha (-k) ∘ₗ (F.bOp E.alpha (k - s) ∘ₗ T.ta s)))
  let P2 : Mode → Mode → F.H →ₗ[ℝ] F.H := fun s k =>
    (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)) •
      (T.taDag s ∘ₗ (F.bOpDag E.alpha (-k) ∘ₗ F.bOp E.alpha (s - k))
        + F.bOpDag E.alpha (s - k) ∘ₗ (F.bOp E.alpha (-k) ∘ₗ T.ta s))
  let P3 : Mode → Mode → F.H →ₗ[ℝ] F.H := fun s k =>
    (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k)) •
      (T.taDag s ∘ₗ (F.bOpDag E.alpha (k - s) ∘ₗ F.bOp E.alpha k)
        + F.bOpDag E.alpha k ∘ₗ (F.bOp E.alpha (k - s) ∘ₗ T.ta s))
  let P4 : Mode → Mode → F.H →ₗ[ℝ] F.H := fun s k =>
    (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)) •
      (F.bCommutator E s k ∘ₗ (T.taDag s + T.ta s))
  -- the weighted `(s,k)` summand splits into the four pieces
  have hpt : ∀ s ∈ excited Mode, ∀ k ∈ F.PHset E,
      (E.fL s * E.W1 k) • (T.qtermT s k + T.qtermDagT s k) = P1 s k + P2 s k + P3 s k + P4 s k := by
    intro s _ k hkPH
    by_cases hf : E.fL s = 0
    · -- the whole summand vanishes (`f_L(s) = 0`)
      dsimp only [P1, P2, P3, P4]
      simp only [hf, zero_mul, neg_zero, zero_smul, add_zero]
    by_cases hW : E.W1 k = 0
    · -- both sides vanish (`Ŵ₁(k) = 0`): the summand carries the factor `Ŵ₁ k`
      dsimp only [P1, P2, P3, P4]
      simp only [hW, mul_zero, zero_mul, neg_zero, zero_smul, add_zero]
    · obtain ⟨ha, hb⟩ := h.denom_ne s k hf hkPH hW
      dsimp only [P1, P2, P3, P4]
      rw [qtermT_split F T E h s k ha hb hf hkPH hW]
      module
  have hsum : (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, (E.fL s * E.W1 k) • (T.qtermT s k + T.qtermDagT s k))
      = (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, P1 s k)
        + (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, P2 s k)
        + (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, P3 s k)
        + (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, P4 s k) := by
    rw [Finset.sum_congr rfl (fun s hs => Finset.sum_congr rfl (fun k hk => hpt s hs k hk))]
    simp only [Finset.sum_add_distrib]
  rw [Work.BoseB7A.TildeData.Q3T, Work.BoseB7A.TildeData.Q3oneT, Work.BoseB7A.TildeData.Q3twoT, Work.BoseB7A.TildeData.Q3threeT, Work.BoseB7A.TildeData.Q3fourT]
  change (E.z / E.ell ^ 3) • (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
        (E.fL s * E.W1 k) • (T.qtermT s k + T.qtermDagT s k))
      = (E.z / E.ell ^ 3) • (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, P1 s k)
        + (E.z / E.ell ^ 3) • (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, P2 s k)
        + (E.z / E.ell ^ 3) • (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, P3 s k)
        + (E.z / E.ell ^ 3) • (∑ s ∈ excited Mode, ∑ k ∈ F.PHset E, P4 s k)
  rw [hsum, smul_add, smul_add, smul_add]

end Work.BoseC3QAll
