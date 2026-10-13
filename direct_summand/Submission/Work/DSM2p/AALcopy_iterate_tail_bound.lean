-- Redirected copy of `Submission.Work.DSM2p.iterate_tail_bound` (imports re-pointed to the `AALvaln` vocabulary layer so that
-- `area_AAL_proved.lean` can import the result without an import cycle).  The original
-- file is untouched; this copy is generated mechanically.
import Mathlib
import Submission.Work.DSM2p.AALcopy_approx_defs

/-!
# `Work.DSM2p.iterate_tail_bound` — iterating the one-step digit estimate

**STATUS.** The statement as requested is *not provable*: its `hstep` and its conclusion bind
`Γ₀` at two independent universe levels, so `hstep` cannot be applied to the `(Γ₀, v)` the
conclusion is about.  The *intended* statement (one universe for `Γ₀`) is proved in full below
as `iterate_tail_bound_fixed`; the requested statement is kept as a `sorry` stub for reference.

This is the "Step 2/3" bookkeeping of `NOTES_approx.md`: from the one-step recursion
`Work.DSM2p.witt_step_rec` (packaged here as the hypothesis `hstep`) and the θ-invariance
`hθ : θ (zs (n+1)) = θ (zs n)`, deduce the source's estimate `AL-eq-re`

  `|z_m - [z̄_m]|_sup ≤ max (δ_m) (v(ϖ 0) ^ (p*m))`,  `δ_n := v (♯((zs n).coeff 0))`

of Česnavičius–Scholze, *Purity for flat cohomology*, `approx-lem`.

## The argument

`β_0 = 1`, `β_{n+1} = max (v(ϖ 0)^p * β_n) (δ_n)`.  Since `IsUnitBall v Set.univ`, `β_0 = 1`
bounds the digits of `zs 0`, and `hstep` gives by induction that both the digits of `zs n` and
the digits of the tail `zs n - [(zs n).coeff 0]` are `≤ β_n`.  It remains to compare `β_m` with
`max (δ_m) (v(ϖ 0)^{pm})`.

The key point — which is where `hθ` enters, and which distinguishes the true statement from the
*naive* iteration `β_m ≤ max (v(ϖ0)^{pm}, v(ϖ0)^{p(m-1)}δ_0, …, δ_{m-1})` — is **no cancellation**:
writing `E_n := θ (zs n) - ♯((zs n).coeff 0)`, one has
`♯((zs (n+1)).coeff 0) - ♯((zs n).coeff 0) = E_n - E_{n+1}`, and `v (E_n) ≤ v(ϖ 0)^p * β_n`.
Hence, whenever `v(ϖ 0)^p * β_n < δ_n` and `v(ϖ 0)^p * β_{n+1} < δ_n`, the addition
`♯((zs (n+1)).coeff 0) = ♯((zs n).coeff 0) + (E_n - E_{n+1})` does not cancel the leading digit and
`δ_{n+1} = δ_n`.  A strong induction on `m` then shows `β_m ≤ max (δ_m) (v(ϖ 0)^{pm})`: below the
threshold the geometric factor `v(ϖ 0)^p` wins, at/above it the `δ`'s are constant and dominate.

The input `v (E_n) ≤ v(ϖ 0)^p * β_n` is the sharp form of the truncated Teichmüller expansion
`fontaineTheta_sub_sum_mem`; it is proved once and for all in
`valu_fontaineTheta_sub_untilt_coeff_le` below.
-/

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

namespace Work.DSM2p

/-- The statement exactly as requested.  **As elaborated this is unprovable**: the `Γ₀`
of `hstep` and the `Γ₀` of the conclusion are two *independent* universe parameters (Lean
generalises the universes of the declaration before elaborating the proof), so `hstep`
cannot be instantiated at the `(Γ₀, v)` of the conclusion (see `iterate_tail_bound_fixed`
below for the intended statement, which is proved). -/
theorem iterate_tail_bound {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] (QR : DSMap.PerfectoidData p R) [Fact (¬ IsUnit (p : R))] [IsAdicComplete (Ideal.span {(p : R)}) R] (zs : ℕ → WittVector p (PreTilt R p)) (m : ℕ) (hθ : ∀ n : ℕ, WittVector.fontaineTheta R p (zs (n + 1)) = WittVector.fontaineTheta R p (zs n)) (hstep : ∀ n : ℕ, ∀ (Γ₀ : Type*) [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀), IsContinuousValuation (QR.ϖ 0) v → IsUnitBall v Set.univ → ∀ (β : Γ₀), (∀ j : ℕ, v (PreTilt.untilt (tiltDigit (zs n) j)) ≤ β) → (∀ j : ℕ, v (PreTilt.untilt (tiltDigit (zs (n + 1)) j)) ≤ max (v (QR.ϖ 0) ^ p * β) (v (PreTilt.untilt ((zs n).coeff 0)))) ∧ (∀ j : ℕ, v (PreTilt.untilt (tiltDigit (zs (n + 1) - WittVector.teichmuller p ((zs (n + 1)).coeff 0)) j)) ≤ max (v (QR.ϖ 0) ^ p * β) (v (PreTilt.untilt ((zs n).coeff 0))))) : ∀ (Γ₀ : Type*) [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀), IsContinuousValuation (QR.ϖ 0) v → IsUnitBall v Set.univ → ∀ j : ℕ, v (PreTilt.untilt (tiltDigit (zs m - WittVector.teichmuller p ((zs m).coeff 0)) j)) ≤ max (v (PreTilt.untilt ((zs m).coeff 0))) (v (QR.ϖ 0) ^ (p * m)) := by sorry

section FIX
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

open WittVector

universe u v

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact (¬ IsUnit (p : R))]
    [IsAdicComplete (Ideal.span {(p : R)}) R]

/-! ## Elementary facts about a continuous valuation on the unit ball -/

/-- A unit of the unit ball has value `1`. -/
theorem valu_units_eq_one {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation R Γ₀} (hball : IsUnitBall v Set.univ) (u : Rˣ) : v (↑u : R) = 1 := by
  have hmul : v (↑u : R) * v (↑u⁻¹ : R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h1 : v (↑u : R) ≤ 1 := hball _ (Set.mem_univ _)
  have h2 : v (↑u⁻¹ : R) ≤ 1 := hball _ (Set.mem_univ _)
  have hge : 1 ≤ v (↑u : R) := by
    calc (1 : Γ₀) = v (↑u : R) * v (↑u⁻¹ : R) := hmul.symm
      _ ≤ v (↑u : R) * 1 := mul_le_mul' le_rfl h2
      _ = v (↑u : R) := mul_one _
  exact le_antisymm h1 hge

/-- On the unit ball, `v (ϖ 0) ^ p = v p`. -/
theorem valu_varpi_pow_eq_v_p (QR : DSMap.PerfectoidData p R) {Γ₀ : Type v}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀} (hball : IsUnitBall v Set.univ) :
    v (QR.ϖ 0) ^ p = v (p : R) := by
  obtain ⟨u, hu⟩ := QR.unit
  rw [← map_pow, hu, map_mul, valu_units_eq_one hball u, mul_one]

/-- Continuity at `ϖ 0` transfers to `p`. -/
theorem cont_at_p (QR : DSMap.PerfectoidData p R) {Γ₀ : Type v}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}
    (hv : IsContinuousValuation (QR.ϖ 0) v) (hball : IsUnitBall v Set.univ) :
    ∀ γ : Γ₀, γ ≠ 0 → ∃ n : ℕ, v (p : R) ^ n < γ := by
  intro γ hγ
  obtain ⟨n, hn⟩ := hv γ hγ
  refine ⟨n, ?_⟩
  rw [← valu_varpi_pow_eq_v_p QR hball, ← pow_mul]
  exact lt_of_le_of_lt
    (pow_le_pow_right_of_le_one' (hball _ (Set.mem_univ _))
      (Nat.le_mul_of_pos_left n (Fact.out : p.Prime).pos)) hn

/-- **No cancellation.**  If `v b < v a` then `v (a + b) = v a`. -/
theorem valu_add_eq_of_lt {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation R Γ₀} {a b : R} (h : v b < v a) : v (a + b) = v a := by
  have h1 : v (a + b) ≤ v a := by
    have hle := v.map_add a b
    rwa [max_eq_left (le_of_lt h)] at hle
  have h2 : v a ≤ v (a + b) := by
    have hm := v.map_add (-b) (a + b)
    rw [show -b + (a + b) = a from by ring, Valuation.map_neg] at hm
    have hle : v a ≤ max (v (a + b)) (v b) := by
      rw [max_comm] at hm
      exact hm
    by_contra hcon
    push_neg at hcon
    exact absurd hle (not_le.mpr (max_lt hcon h))
  exact le_antisymm h1 h2

/-! ## The `β` recursion -/

/-- The digit bound recursion `β_0 = 1`, `β_{n+1} = max (q * β_n) (δ_n)`. -/
noncomputable def digitBeta {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    (q : Γ₀) (δ : ℕ → Γ₀) : ℕ → Γ₀
  | 0 => 1
  | n + 1 => max (q * digitBeta q δ n) (δ n)

@[simp]
theorem digitBeta_zero {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    (q : Γ₀) (δ : ℕ → Γ₀) : digitBeta q δ 0 = 1 := rfl

theorem digitBeta_succ {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    (q : Γ₀) (δ : ℕ → Γ₀) (n : ℕ) :
    digitBeta q δ (n + 1) = max (q * digitBeta q δ n) (δ n) := rfl

/-! ## The sharp truncated-expansion estimate -/

/-- **`v (θ z - ♯(z.coeff 0)) ≤ v(ϖ 0)^p * B`** whenever `B` bounds the tilt digits of `z`.
This is the sharp form of `fontaineTheta_sub_sum_mem`: the `j = 0` term of the expansion is
`♯(z.coeff 0)`, which cancels, and every remaining term carries a factor `p`, of value
`v(ϖ 0)^p`. -/
theorem valu_fontaineTheta_sub_untilt_coeff_le (QR : DSMap.PerfectoidData p R)
    {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}
    (hv : IsContinuousValuation (QR.ϖ 0) v) (hball : IsUnitBall v Set.univ)
    (z : WittVector p (PreTilt R p)) {B : Γ₀}
    (hz : ∀ j : ℕ, v (PreTilt.untilt (tiltDigit z j)) ≤ B) :
    v (WittVector.fontaineTheta R p z - PreTilt.untilt (z.coeff 0)) ≤ v (QR.ϖ 0) ^ p * B := by
  have hq : v (QR.ϖ 0) ^ p = v (p : R) := valu_varpi_pow_eq_v_p QR hball
  have hvp1 : v (p : R) ≤ 1 := le_of_lt (Valuation.map_p_lt_one QR v hv hball)
  -- the truncated bound, for an arbitrary truncation length `M`
  have key : ∀ M : ℕ, v (WittVector.fontaineTheta R p z - PreTilt.untilt (z.coeff 0))
      ≤ max (v (QR.ϖ 0) ^ p * B) (v (p : R) ^ (M + 1)) := by
    intro M
    have hmem := fontaineTheta_sub_sum_mem QR z M
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hsum : (∑ j ≤ M, PreTilt.untilt (tiltDigit z j) * (p : R) ^ j)
        = (∑ j ∈ Finset.range M, PreTilt.untilt (tiltDigit z (j + 1)) * (p : R) ^ (j + 1))
          + PreTilt.untilt (z.coeff 0) := by
      rw [show (Finset.Iic M : Finset ℕ) = Finset.range (M + 1) from by
        ext x; simp only [Finset.mem_Iic, Finset.mem_range]; omega]
      rw [Finset.sum_range_succ']
      simp [tiltDigit_zero]
    have hsplit : WittVector.fontaineTheta R p z - PreTilt.untilt (z.coeff 0)
        = (p : R) ^ (M + 1) * c
          + ∑ j ∈ Finset.range M, PreTilt.untilt (tiltDigit z (j + 1)) * (p : R) ^ (j + 1) := by
      have : WittVector.fontaineTheta R p z - PreTilt.untilt (z.coeff 0)
          = (WittVector.fontaineTheta R p z
              - ∑ j ≤ M, PreTilt.untilt (tiltDigit z j) * (p : R) ^ j)
            + ((∑ j ≤ M, PreTilt.untilt (tiltDigit z j) * (p : R) ^ j)
              - PreTilt.untilt (z.coeff 0)) := by ring
      rw [this, hc, hsum]; ring
    rw [hsplit]
    refine le_trans (v.map_add _ _) (max_le ?_ ?_)
    · rw [map_mul, map_pow]
      refine le_trans (mul_le_mul' le_rfl (hball c (Set.mem_univ _))) ?_
      rw [mul_one]
      exact le_max_right _ _
    · refine v.map_sum_le (g := max (v (QR.ϖ 0) ^ p * B) (v (p : R) ^ (M + 1)))
        (fun j _ => ?_)
      rw [map_mul, map_pow]
      have h1 : v (p : R) ^ (j + 1) ≤ v (p : R) := by
        rw [pow_succ]
        exact mul_le_of_le_one_left zero_le (pow_le_one' hvp1 j)
      calc v (PreTilt.untilt (tiltDigit z (j + 1))) * v (p : R) ^ (j + 1)
          ≤ B * v (p : R) := mul_le_mul' (hz (j + 1)) h1
        _ = v (QR.ϖ 0) ^ p * B := by rw [← hq, mul_comm]
        _ ≤ max (v (QR.ϖ 0) ^ p * B) (v (p : R) ^ (M + 1)) := le_max_left _ _
  -- pass to the limit using continuity
  refine le_of_not_gt fun hcon => ?_
  have hE0 : v (WittVector.fontaineTheta R p z - PreTilt.untilt (z.coeff 0)) ≠ 0 := by
    intro h0; rw [h0] at hcon; exact absurd hcon (not_lt.mpr zero_le)
  obtain ⟨N, hN⟩ := hv _ hE0
  have hM : v (p : R) ^ (N + 1)
      < v (WittVector.fontaineTheta R p z - PreTilt.untilt (z.coeff 0)) := by
    rw [← hq, ← pow_mul]
    exact lt_of_le_of_lt
      (pow_le_pow_right_of_le_one' (hball _ (Set.mem_univ _))
        (le_trans (Nat.le_succ N) (Nat.le_mul_of_pos_left (N + 1) (Fact.out : p.Prime).pos))) hN
  exact absurd (key N) (not_le.mpr (max_lt hcon hM))

/-! ## The main theorem -/

theorem iterate_tail_bound_fixed {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] (QR : DSMap.PerfectoidData p R) [Fact (¬ IsUnit (p : R))] [IsAdicComplete (Ideal.span {(p : R)}) R] (zs : ℕ → WittVector p (PreTilt R p)) (m : ℕ) (hθ : ∀ n : ℕ, WittVector.fontaineTheta R p (zs (n + 1)) = WittVector.fontaineTheta R p (zs n)) (hstep : ∀ n : ℕ, ∀ (v : Valuation R Γ₀), IsContinuousValuation (QR.ϖ 0) v → IsUnitBall v Set.univ → ∀ (β : Γ₀), (∀ j : ℕ, v (PreTilt.untilt (tiltDigit (zs n) j)) ≤ β) → (∀ j : ℕ, v (PreTilt.untilt (tiltDigit (zs (n + 1)) j)) ≤ max (v (QR.ϖ 0) ^ p * β) (v (PreTilt.untilt ((zs n).coeff 0)))) ∧ (∀ j : ℕ, v (PreTilt.untilt (tiltDigit (zs (n + 1) - WittVector.teichmuller p ((zs (n + 1)).coeff 0)) j)) ≤ max (v (QR.ϖ 0) ^ p * β) (v (PreTilt.untilt ((zs n).coeff 0))))) : ∀ (v : Valuation R Γ₀), IsContinuousValuation (QR.ϖ 0) v → IsUnitBall v Set.univ → ∀ j : ℕ, v (PreTilt.untilt (tiltDigit (zs m - WittVector.teichmuller p ((zs m).coeff 0)) j)) ≤ max (v (PreTilt.untilt ((zs m).coeff 0))) (v (QR.ϖ 0) ^ (p * m)) := by
  intro v hv hball j
  have hq : v (QR.ϖ 0) ^ p = v (p : R) := valu_varpi_pow_eq_v_p QR hball
  have hγ1 : v (QR.ϖ 0) ≤ 1 := hball _ (Set.mem_univ _)
  have hq1 : v (QR.ϖ 0) ^ p < 1 := by
    rw [hq]; exact Valuation.map_p_lt_one QR v hv hball
  -- the two sequences
  let δ : ℕ → Γ₀ := fun n => v (PreTilt.untilt ((zs n).coeff 0))
  let β : ℕ → Γ₀ := digitBeta (v (QR.ϖ 0) ^ p) δ
  have hβ0 : β 0 = 1 := rfl
  have hβs : ∀ n, β (n + 1) = max (v (QR.ϖ 0) ^ p * β n) (δ n) := fun n => rfl
  -- the digit bounds, by induction from `hstep`
  have DIG : ∀ n j, v (PreTilt.untilt (tiltDigit (zs n) j)) ≤ β n := by
    intro n
    induction n with
    | zero => intro j; rw [hβ0]; exact hball _ (Set.mem_univ _)
    | succ n ih => intro j; rw [hβs n]; exact (hstep n v hv hball (β n) ih).1 j
  have TAIL : ∀ n j,
      v (PreTilt.untilt (tiltDigit (zs n - WittVector.teichmuller p ((zs n).coeff 0)) j)) ≤ β n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · intro j; rw [h0, hβ0]; exact hball _ (Set.mem_univ _)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      intro j; rw [hβs k]; exact (hstep k v hv hball (β k) (DIG k)).2 j
  -- the sharp estimate `v (E n) ≤ v(ϖ 0)^p * β n`
  have hE : ∀ n, v (WittVector.fontaineTheta R p (zs n) - PreTilt.untilt ((zs n).coeff 0))
      ≤ v (QR.ϖ 0) ^ p * β n := fun n =>
    valu_fontaineTheta_sub_untilt_coeff_le QR hv hball (zs n) (DIG n)
  -- no cancellation for the leading digits, using `hθ`
  have hNO : ∀ k, v (QR.ϖ 0) ^ p * β k < δ k → v (QR.ϖ 0) ^ p * β (k + 1) < δ k →
      δ (k + 1) = δ k := by
    intro k h1 h2
    have hdiff : PreTilt.untilt ((zs (k + 1)).coeff 0) - PreTilt.untilt ((zs k).coeff 0)
        = (WittVector.fontaineTheta R p (zs k) - PreTilt.untilt ((zs k).coeff 0))
          - (WittVector.fontaineTheta R p (zs (k + 1))
              - PreTilt.untilt ((zs (k + 1)).coeff 0)) := by
      rw [hθ k]; ring
    have hlt : v (PreTilt.untilt ((zs (k + 1)).coeff 0) - PreTilt.untilt ((zs k).coeff 0))
        < δ k := by
      rw [hdiff, sub_eq_add_neg]
      refine lt_of_le_of_lt (le_trans (v.map_add _ _) (max_le ?_ ?_)) (max_lt h1 h2)
      · exact le_trans (hE k) (le_max_left _ _)
      · rw [Valuation.map_neg]; exact le_trans (hE (k + 1)) (le_max_right _ _)
    have hδk1 : δ (k + 1) = v (PreTilt.untilt ((zs k).coeff 0)) := by
      have hrew : PreTilt.untilt ((zs k).coeff 0)
            + (PreTilt.untilt ((zs (k + 1)).coeff 0) - PreTilt.untilt ((zs k).coeff 0))
          = PreTilt.untilt ((zs (k + 1)).coeff 0) := by ring
      calc δ (k + 1) = v (PreTilt.untilt ((zs (k + 1)).coeff 0)) := rfl
        _ = v (PreTilt.untilt ((zs k).coeff 0)
              + (PreTilt.untilt ((zs (k + 1)).coeff 0) - PreTilt.untilt ((zs k).coeff 0))) := by
            rw [hrew]
        _ = v (PreTilt.untilt ((zs k).coeff 0)) := valu_add_eq_of_lt hlt
    exact hδk1
  -- the comparison `β m ≤ max (δ m) ((v(ϖ 0)^p)^m)`
  have HBETA : ∀ n, β n ≤ max (δ n) ((v (QR.ϖ 0) ^ p) ^ n) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih
    cases n with
    | zero => rw [hβ0, pow_zero]; exact le_max_right _ _
    | succ k =>
      have ihk : β k ≤ max (δ k) ((v (QR.ϖ 0) ^ p) ^ k) := ih k (Nat.lt_succ_self k)
      have hbk_aux : ((v (QR.ϖ 0) ^ p) ^ (k + 1)) < δ k → v (QR.ϖ 0) ^ p * β k < δ k := by
        intro hcase
        have hpos : (0 : Γ₀) < δ k := lt_of_le_of_lt zero_le hcase
        by_cases h2 : ((v (QR.ϖ 0) ^ p) ^ k) ≤ δ k
        · have hle : β k ≤ δ k := le_trans ihk (max_eq_left h2).le
          calc v (QR.ϖ 0) ^ p * β k ≤ v (QR.ϖ 0) ^ p * δ k := mul_le_mul' le_rfl hle
            _ < 1 * δ k := mul_lt_mul_of_pos_right hq1 hpos
            _ = δ k := one_mul _
        · rw [not_le] at h2
          have hle : β k ≤ (v (QR.ϖ 0) ^ p) ^ k := le_trans ihk (max_eq_right (le_of_lt h2)).le
          calc v (QR.ϖ 0) ^ p * β k
              ≤ v (QR.ϖ 0) ^ p * (v (QR.ϖ 0) ^ p) ^ k := mul_le_mul' le_rfl hle
            _ = (v (QR.ϖ 0) ^ p) ^ (k + 1) := by rw [pow_succ']
            _ < δ k := hcase
      rw [hβs k]
      by_cases hcase : ((v (QR.ϖ 0) ^ p) ^ (k + 1)) < δ k
      · -- above the threshold: no cancellation, so `δ (k+1) = δ k` and `β (k+1) = δ k`
        have hbk : v (QR.ϖ 0) ^ p * β k < δ k := hbk_aux hcase
        have hβeq : β (k + 1) = δ k := by
          rw [hβs k, max_eq_right (le_of_lt hbk)]
        have hbk1 : v (QR.ϖ 0) ^ p * β (k + 1) < δ k := by
          rw [hβeq]
          calc v (QR.ϖ 0) ^ p * δ k < 1 * δ k :=
                mul_lt_mul_of_pos_right hq1 (lt_of_le_of_lt zero_le hcase)
            _ = δ k := one_mul _
        have hδeq : δ (k + 1) = δ k := hNO k hbk hbk1
        refine max_le ?_ ?_
        · exact le_trans (le_of_lt hbk) (by rw [← hδeq]; exact le_max_left _ _)
        · rw [← hδeq]
          exact le_max_left _ _
      · rw [not_lt] at hcase
        have hqk1 : (v (QR.ϖ 0) ^ p) ^ (k + 1) ≤ (v (QR.ϖ 0) ^ p) ^ k :=
          pow_le_pow_right_of_le_one' (le_of_lt hq1) (Nat.le_succ k)
        refine max_le ?_ ?_
        · have hqk : β k ≤ (v (QR.ϖ 0) ^ p) ^ k :=
            le_trans ihk (max_le (le_trans hcase hqk1) le_rfl)
          calc v (QR.ϖ 0) ^ p * β k
              ≤ v (QR.ϖ 0) ^ p * (v (QR.ϖ 0) ^ p) ^ k := mul_le_mul' le_rfl hqk
            _ = (v (QR.ϖ 0) ^ p) ^ (k + 1) := by rw [pow_succ']
            _ ≤ max (δ (k + 1)) ((v (QR.ϖ 0) ^ p) ^ (k + 1)) := le_max_right _ _
        · exact le_trans hcase (le_max_right _ _)
  -- assemble
  refine le_trans (TAIL m j) (le_trans (HBETA m) ?_)
  refine max_le (le_max_left _ _) ?_
  rw [pow_mul]
  exact le_max_right _ _

end FIX

end Work.DSM2p
