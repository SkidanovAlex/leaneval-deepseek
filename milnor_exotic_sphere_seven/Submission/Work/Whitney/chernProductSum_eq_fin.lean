import Mathlib
import Submission.Work.Whitney.ChernProduct

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# `chernProductSum` as a sum over `Fin (j+1)`

`Work.Whitney.chernProductSum Z₁ Z₂ j` is defined as the sum over `i ∈ Finset.range (j+1)` of the
degree bookkeeping `if i ≤ j` applied to `Work.Whitney.chernSummand Z₁ Z₂ i (j-i)`; the latter
is `Work.Whitney.cupChern i (j-i) (c_i Z₁) (c_{j-i} Z₂)`, i.e. the product `c_i Z₁ ⌣ c_{j-i} Z₂`
with the degree cast `2*i + 2*(j-i) = 2*(i + (j-i))` already applied.

Here we re-index the sum by `Fin (j+1)` and *inline* the graded product, so that each summand is
the plain cup product `cupH' ℤ (ssB B) (2*i) (2*(j-i)) (c_i Z₁) (c_{j-i} Z₂)` transported along
`2*i + 2*(j-i) = 2*j`.  The two degree casts differ (`2*(i+(j-i))` versus `2*i+2*(j-i)`) but the
proofs are compared by proof irrelevance, and `Work.Thom.cohTransport` depends on its equality
argument only through that proof, so the only real content is the unfolding of
`Work.Whitney.chernSummand`/`Work.Whitney.cupChern` and the transitivity of the transport
(`Work.Whitney.cohTransport_trans`).
-/

namespace Work.Whitney

/-- `Work.Whitney.chernProductSum Z₁ Z₂ j` re-indexed by `Fin (j+1)`, with the graded products
`Work.Whitney.cupChern` inlined as the transported cup products `Work.Cohomology.cupH'`. -/
theorem chernProductSum_eq_fin {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type}
    [Fintype ι₁] [Fintype ι₂] {m₁ m₂ : ℕ}
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂) (j : ℕ) :
    Work.Whitney.chernProductSum Z₁ Z₂ j
      = ∑ a : Fin (j + 1),
          Work.Thom.cohTransport (by have h := a.isLt; omega)
            ((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B)
              (2 * (a : ℕ)) (2 * (j - (a : ℕ))))
              (Work.Thom.chernClass m₁ (a : ℕ) Z₁)
              (Work.Thom.chernClass m₂ (j - (a : ℕ)) Z₂)) := by
  -- The auxiliary total function `F : ℕ → Coh ℤ (2*j) B` extending the `Fin (j+1)`-summand to
  -- all of `ℕ` (with value `0` outside the range, where it is never used).
  set F : ℕ → Work.Thom.Coh ℤ (2 * j) B := fun i =>
    if h : i ≤ j then
      Work.Thom.cohTransport (by omega : 2 * i + 2 * (j - i) = 2 * j)
        ((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (j - i)))
          (Work.Thom.chernClass m₁ i Z₁) (Work.Thom.chernClass m₂ (j - i) Z₂))
    else 0 with hF
  -- Unfolding `F` at an index in range, for an arbitrary proof of the transported degree equality
  -- (the proof is irrelevant for the value).
  have hF_apply : ∀ (i : ℕ) (h : i ≤ j) (q : 2 * i + 2 * (j - i) = 2 * j),
      F i = Work.Thom.cohTransport q
        ((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (j - i)))
          (Work.Thom.chernClass m₁ i Z₁) (Work.Thom.chernClass m₂ (j - i) Z₂)) := by
    intro i h q
    simp only [hF, dif_pos h]
  -- One summand of the left-hand side, inlined: the two consecutive degree casts compose.
  have step : ∀ (i : ℕ) (h : i ≤ j) (p : 2 * (i + (j - i)) = 2 * j)
      (q : 2 * i + 2 * (j - i) = 2 * j),
      Work.Thom.cohTransport p (Work.Whitney.chernSummand Z₁ Z₂ i (j - i))
        = Work.Thom.cohTransport q
          ((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (j - i)))
            (Work.Thom.chernClass m₁ i Z₁) (Work.Thom.chernClass m₂ (j - i) Z₂)) := by
    intro i h p q
    rw [Work.Whitney.chernSummand_def, Work.Whitney.cupChern_def,
      Work.Whitney.cohTransport_trans]
  -- Left-hand side: unroll the definition and drop the (vacuous) `if i ≤ j`.
  have hL : Work.Whitney.chernProductSum Z₁ Z₂ j
      = ∑ i ∈ Finset.range (j + 1), F i := by
    unfold Work.Whitney.chernProductSum
    refine Finset.sum_congr rfl fun i hi => ?_
    have hle : i ≤ j := by simp only [Finset.mem_range] at hi; omega
    rw [dif_pos hle, hF_apply i hle (by omega : 2 * i + 2 * (j - i) = 2 * j)]
    exact step i hle _ _
  -- Right-hand side: re-index the `Fin (j+1)`-sum by `Finset.range (j+1)`.
  have hR : (∑ a : Fin (j + 1),
        Work.Thom.cohTransport (by have h := a.isLt; omega)
          ((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B)
            (2 * (a : ℕ)) (2 * (j - (a : ℕ))))
            (Work.Thom.chernClass m₁ (a : ℕ) Z₁)
            (Work.Thom.chernClass m₂ (j - (a : ℕ)) Z₂)))
      = ∑ i ∈ Finset.range (j + 1), F i := by
    rw [← Fin.sum_univ_eq_sum_range F (j + 1)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hF_apply (a : ℕ) (by have h := a.isLt; omega)
      (by have h := a.isLt; omega : 2 * (a : ℕ) + 2 * (j - (a : ℕ)) = 2 * j)]
  rw [hL, hR]

end Work.Whitney
