import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

/-! ## Membership in the rectangular index block

`HkActivePairs k` is by definition the filter of the rectangle `range (k+1) × range (k+1)` by the
predicate `p.2 = 0 ∧ p.1 ≤ k ∨ 1 ≤ p.2 ∧ p.2 + p.1 ≤ k`.  On the rectangle the bound `p.1 ≤ k` of
the first disjunct is automatic, which is the content of the two membership lemmas below: the
first one records the rectangle membership (used on the definitional `.product` form), the second
its `×ˢ`-notation twin (used for `Finset.sum_product`). -/

/-- Membership in the index rectangle `range (k+1) × range (k+1)`, in the `.product` shape in
which `HkActivePairs` is defined. -/
theorem mem_range_prod_range (k : ℕ) (p : ℕ × ℕ) :
    p ∈ (Finset.range (k + 1)).product (Finset.range (k + 1)) ↔ p.1 ≤ k ∧ p.2 ≤ k := by
  constructor
  · intro hp
    change p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)) at hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    omega
  · rintro ⟨h1, h2⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩

/-- Membership in the index rectangle `range (k+1) × range (k+1)`, in the `×ˢ` shape that
`Finset.sum_product` produces. -/
theorem mem_range_sprod_range (k : ℕ) (p : ℕ × ℕ) :
    p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)) ↔ p.1 ≤ k ∧ p.2 ≤ k := by
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
  omega

/-- **The index set of the terms of `HkIntegrand`.**  `HkActivePairs k` consists exactly of the
pure pairs `(j, 0)` with `j ≤ k` and the mixed pairs `(j, i)` with `1 ≤ i` and `i + j ≤ k`. -/
theorem HkActivePairs_mem (k : ℕ) (p : ℕ × ℕ) :
    p ∈ HkActivePairs k ↔ p.2 = 0 ∧ p.1 ≤ k ∨ 1 ≤ p.2 ∧ p.2 + p.1 ≤ k := by
  rw [HkActivePairs, Finset.mem_filter, mem_range_prod_range]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro (h | h)
    · exact ⟨⟨by omega, by omega⟩, Or.inl h⟩
    · exact ⟨⟨by omega, by omega⟩, Or.inr h⟩

/-! ## The sum over `HkActivePairs k` -/

/-- **The sum over `HkActivePairs k` splits into its pure and mixed parts**: the pure terms
`(i, 0)`, `i ≤ k`, of the first sum of `HkIntegrand`, and the mixed terms `(j, i)`, `1 ≤ i`,
`i + j ≤ k`, of the double sum. -/
theorem HkActivePairs_sum (k : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ p ∈ HkActivePairs k, F p
      = (∑ i ∈ Finset.range (k + 1), F (i, 0))
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then F (j, i) else 0) := by
  -- rewrite the two disjuncts of the filter predicate separately, in the `×ˢ` shape
  have hfilter : HkActivePairs k
      = ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
          (fun p : ℕ × ℕ => p.2 = 0 ∨ (1 ≤ p.2 ∧ p.2 + p.1 ≤ k)) := by
    ext p
    rw [HkActivePairs, Finset.mem_filter, Finset.mem_filter, mem_range_prod_range,
      mem_range_sprod_range]
    tauto
  rw [hfilter, Finset.filter_or]
  have hdisj : Disjoint
      (((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
        (fun p : ℕ × ℕ => p.2 = 0))
      (((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
        (fun p : ℕ × ℕ => 1 ≤ p.2 ∧ p.2 + p.1 ≤ k)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_filter] at ha hb
    omega
  rw [Finset.sum_union hdisj, Finset.sum_filter, Finset.sum_filter]
  congr 1
  · -- the pure part: `∑ p, if p.2 = 0 then F p else 0 = ∑ i, F (i,0)`
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_ite_eq']
    simp
  · -- the mixed part: swap the two sums, using that the bound `p.1 ≤ k` is automatic
    rw [Finset.sum_product]
    conv_lhs => rw [Finset.sum_comm]

/-- **The index set of the terms of `HkIntegrand`.**  `HkActivePairs k` enumerates exactly the pairs `(j,i)` of `HkIntegrand α k`: the pure terms `(j,0)`, `j ≤ k`, of the first sum and the mixed terms `(j,i)`, `1 ≤ i`, `i + j ≤ k`, of the double sum (with `mixed j 0 = D_z^j` and the weight `termWeight α i` equal to `w/√sin^η` for `i = 0` and `Wt` for `i ≥ 1`). -/
theorem HkActivePairs_spec (k : ℕ) :
    (∀ p : ℕ × ℕ, p ∈ HkActivePairs k
        ↔ p.2 = 0 ∧ p.1 ≤ k ∨ 1 ≤ p.2 ∧ p.2 + p.1 ≤ k)
      ∧ (∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ),
          Work.Spaces.HkIntegrand α k f z θ
            = ∑ p ∈ HkActivePairs k,
                (Work.Spaces.mixed p.1 p.2 f z θ * termWeight α p.2 z θ) ^ 2) := by
  constructor
  · intro p
    exact HkActivePairs_mem k p
  · intro α f z θ
    -- expand the sum over `HkActivePairs` and compare the two halves with `HkIntegrand`
    rw [HkActivePairs_sum k
      (fun p => (Work.Spaces.mixed p.1 p.2 f z θ * termWeight α p.2 z θ) ^ 2)]
    rw [Work.Spaces.HkIntegrand]
    -- The pure radial halves are *definitionally* equal (`mixed i 0 = D_z^i` and
    -- `termWeight α 0 = w/√sin^η`), so `congr` discharges them and only the mixed comparison
    -- remains: `termWeight α i = Wt α` for `i ≥ 1`.
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left h, ite_eq_left h]
      simp only [termWeight, ite_eq_right (show ¬ i = 0 from by omega)]
    · rw [ite_eq_right h, ite_eq_right h]

end Work.FTS.PhiStar.Honesty.SlotsLimit
