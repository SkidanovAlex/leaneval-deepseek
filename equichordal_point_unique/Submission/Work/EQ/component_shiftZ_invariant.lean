import Mathlib
import Submission.Work.EQ.EndDefs
import Submission.Work.EQ.H0_invParam_ge

/-! # A compact cycle is invariant under the shift

`hcyc` says only that `σ^d` maps the component `S = connectedComponentIn (H0 a h) p` *into*
itself.  But `shiftZ a j` maps `H0` to `H0` for **every** `j : ℤ` (both directions, see
`mem_H0_shiftZ`), so the preimage of the component `S` under `σ^{-d}` is connected, meets `S`
(at `p`), and hence is contained in `S`.  Consequently every point of `S` has all its `d`-step
shifts inside `S`. -/

set_option linter.unusedVariables false

namespace Work.EQ

open Complex Filter _root_.Topology

section

variable {a : ℝ}

theorem eqLamC_ne_zero_of' (ha0 : 0 < a) (ha1 : a < 1) : ((eqLam a : ℝ) : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_zero, Ne, Complex.ofReal_inj]
  have : 0 < eqLam a := by rw [eqLam]; exact div_pos (by linarith) (by linarith)
  exact ne_of_gt this

/-- `hShift a` is `shiftZ a 1` on chain data. -/
theorem hShift_eq_shiftZ (a : ℝ) (p : ChainData) : hShift a p = shiftZ a 1 p := by
  simp only [hShift, shiftZ, zpow_one]

/-- Composing two integer shifts. -/
theorem shiftZ_shiftZ (ha0 : 0 < a) (ha1 : a < 1) (j k : ℤ) (p : ChainData) :
    shiftZ a j (shiftZ a k p) = shiftZ a (j + k) p := by
  have hne := eqLamC_ne_zero_of' (a := a) ha0 ha1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext n; simp only [shiftZ]; ring_nf
  · simp only [shiftZ, ← mul_assoc, ← zpow_add₀ hne]
  · simp only [shiftZ]
    rw [div_div, ← zpow_add₀ hne, add_comm]

/-- The integer shifts are mutually inverse. -/
theorem shiftZ_neg_apply (ha0 : 0 < a) (ha1 : a < 1) (j : ℤ) (p : ChainData) :
    shiftZ a j (shiftZ a (-j) p) = p ∧ shiftZ a (-j) (shiftZ a j p) = p := by
  have h1 := shiftZ_shiftZ ha0 ha1 j (-j) p
  have h2 := shiftZ_shiftZ ha0 ha1 (-j) j p
  rw [add_neg_cancel] at h1
  rw [neg_add_cancel] at h2
  refine ⟨?_, ?_⟩
  · rw [h1]; simp [shiftZ]
  · rw [h2]; simp [shiftZ]

/-- The `k`-fold iterate of the shift is `shiftZ a k`. -/
theorem hShift_iterate_eq_shiftZ (ha0 : 0 < a) (ha1 : a < 1) (k : ℕ) (p : ChainData) :
    (hShift a)^[k] p = shiftZ a (k : ℤ) p := by
  induction k with
  | zero => simp [shiftZ]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, hShift_eq_shiftZ, shiftZ_shiftZ ha0 ha1,
      show (1 : ℤ) + (k : ℤ) = ((k + 1 : ℕ) : ℤ) by push_cast; ring]

/-- The shift is continuous on chain data. -/
theorem continuous_shiftZ' (a : ℝ) (j : ℤ) : Continuous (shiftZ a j) := by
  unfold shiftZ
  fun_prop

/-- **A cycle is invariant under `σ^d`.**  If `σ^d` maps the component `S = connectedComponentIn
(H0 a h) p` into itself, then `shiftZ a (d * j)` maps `S` into itself for every `j : ℤ`. -/
theorem shiftZ_mem_component {h : ℂ → ℂ} {p : ChainData} {d : ℕ}
    (ha0 : 0 < a) (ha1 : a < 1) (hp : p ∈ H0 a h)
    (hcyc : ∀ q ∈ connectedComponentIn (H0 a h) p,
      (hShift a)^[d] q ∈ connectedComponentIn (H0 a h) p) :
    ∀ j : ℤ, ∀ q ∈ connectedComponentIn (H0 a h) p,
      shiftZ a ((d : ℤ) * j) q ∈ connectedComponentIn (H0 a h) p := by
  have hmem : p ∈ connectedComponentIn (H0 a h) p := mem_connectedComponentIn hp
  have hstep : ∀ q ∈ connectedComponentIn (H0 a h) p,
      shiftZ a (d : ℤ) q ∈ connectedComponentIn (H0 a h) p := by
    intro q hq
    have h1 := hcyc q hq
    rwa [hShift_iterate_eq_shiftZ ha0 ha1] at h1
  have hstepinv : ∀ q ∈ connectedComponentIn (H0 a h) p,
      shiftZ a (-(d : ℤ)) q ∈ connectedComponentIn (H0 a h) p := by
    intro q hq
    have hconn : IsPreconnected (shiftZ a (-(d : ℤ)) '' connectedComponentIn (H0 a h) p) :=
      (isPreconnected_connectedComponentIn).image _
        (continuous_shiftZ' a _).continuousOn
    have hsub : shiftZ a (-(d : ℤ)) '' connectedComponentIn (H0 a h) p ⊆ H0 a h := by
      rintro _ ⟨y, hy, rfl⟩
      exact mem_H0_shiftZ ha0 ha1 (connectedComponentIn_subset _ _ hy) _
    have hmem' : p ∈ shiftZ a (-(d : ℤ)) '' connectedComponentIn (H0 a h) p :=
      ⟨shiftZ a (d : ℤ) p, hstep p hmem, (shiftZ_neg_apply ha0 ha1 (d : ℤ) p).2⟩
    have hunion := IsPreconnected.union p hmem' hmem hconn isPreconnected_connectedComponentIn
    have hmain := hunion.subset_connectedComponentIn (Or.inr hmem)
      (by
        intro z hz
        rcases hz with hz | hz
        · exact hsub hz
        · exact connectedComponentIn_subset _ _ hz)
    exact hmain (Or.inl ⟨q, hq, rfl⟩)
  -- iterating the two steps
  have hkeypos : ∀ k : ℕ, ∀ q ∈ connectedComponentIn (H0 a h) p,
      shiftZ a (((d * k : ℕ)) : ℤ) q ∈ connectedComponentIn (H0 a h) p := by
    intro k
    induction k with
    | zero => intro q hq; simpa [shiftZ] using hq
    | succ k ih =>
      intro q hq
      have h1 : shiftZ a (d : ℤ) q ∈ connectedComponentIn (H0 a h) p := hstep q hq
      have h3 := ih (shiftZ a (d : ℤ) q) h1
      have h2 : ((d * k : ℕ) : ℤ) + (d : ℤ) = ((d * (k + 1) : ℕ) : ℤ) := by push_cast; ring
      rw [shiftZ_shiftZ ha0 ha1, h2] at h3
      exact h3
  have hkeyneg : ∀ k : ℕ, ∀ q ∈ connectedComponentIn (H0 a h) p,
      shiftZ a (-(((d * k : ℕ)) : ℤ)) q ∈ connectedComponentIn (H0 a h) p := by
    intro k
    induction k with
    | zero => intro q hq; simpa [shiftZ] using hq
    | succ k ih =>
      intro q hq
      have h1 : shiftZ a (-(d : ℤ)) q ∈ connectedComponentIn (H0 a h) p := hstepinv q hq
      have h3 := ih (shiftZ a (-(d : ℤ)) q) h1
      have h2 : -(((d * k : ℕ)) : ℤ) + -(d : ℤ) = -(((d * (k + 1) : ℕ)) : ℤ) := by push_cast; ring
      rw [shiftZ_shiftZ ha0 ha1, h2] at h3
      exact h3
  intro j
  by_cases hj : 0 ≤ j
  · have hdj : (d : ℤ) * j = ((d * j.toNat : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg hj]
    rw [hdj]
    exact hkeypos j.toNat
  · push_neg at hj
    have hj' : 0 ≤ -j := by omega
    have hdj : (d : ℤ) * j = -(((d * (-j).toNat : ℕ)) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg hj']
      ring
    rw [hdj]
    exact hkeyneg (-j).toNat

end

end Work.EQ
