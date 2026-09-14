import Mathlib

import Submission.Vdw.LocalField.Completion
open scoped NumberField Valued WithZero
open Filter
open IsDedekindDomain
open IsLocalRing

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (stone 3, groundwork): the valuation ring of the completion
is adically complete

`Perfection.teichmuller` (the Teichmüller-lift input of the unramified-subfield
construction) needs `[IsAdicComplete 𝔪 (kpInt p P)]` at the valuation ring
`kpInt p P := (kprime p P).adicCompletionIntegers K` of the completion.  Mathlib
registers no such instance for `adicCompletionIntegers` (its
`IsNonarchimedeanLocalField`-based instance covers `Valued.integer` of local
fields, and `adicCompletionIntegers` is a different subtype).  This module
supplies it.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- In the normed field structure on the completion (which arises from its
rank-one valuation), norm ≤ 1 agrees with valuation ≤ 1. -/
lemma norm_le_one_iff_val (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (x : kpAdic p P) :
    ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff (L := kpAdic p P) (Γ₀ := ℤᵐ⁰) (x := x)

/-- norm < 1 agrees with valuation < 1. -/
lemma norm_lt_one_iff_val (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (x : kpAdic p P) :
    ‖x‖ < 1 ↔ Valued.v x < 1 :=
  Valued.toNormedField.norm_lt_one_iff (L := kpAdic p P) (Γ₀ := ℤᵐ⁰) (x := x)

/-- The elements of the valuation ring have norm ≤ 1. -/
lemma norm_le_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (x : kpInt p P) :
    ‖x‖ ≤ 1 := by
  exact (norm_le_one_iff_val p P (x : kpAdic p P)).mpr x.2

/-- The set of valuation-integral elements is the unit ball. -/
lemma val_le_one_set_eq_ball (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    ({x : kpAdic p P | Valued.v x ≤ 1} : Set (kpAdic p P)) = {x : kpAdic p P | ‖x‖ ≤ 1} := by
  ext x
  exact (norm_le_one_iff_val p P x).symm

/-- The valuation ring is a closed subset of the complete ambient field. -/
lemma isClosed_val_le_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    IsClosed ({x : kpAdic p P | Valued.v x ≤ 1} : Set (kpAdic p P)) := by
  rw [val_le_one_set_eq_ball]
  exact isClosed_le continuous_norm continuous_const

/-- **`CompleteSpace (kpInt p P)`**: the valuation ring of the complete field
`kpAdic p P` is complete (it is the closed unit ball). -/
theorem kpIntCompleteSpace (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    CompleteSpace (kpInt p P) := by
  classical
  apply (completeSpace_iff_isComplete_range (f := fun x : kpInt p P => (x : kpAdic p P)) ?_).mpr
  · have hset : Set.range (fun y : kpInt p P => (y : kpAdic p P)) =
        {x : kpAdic p P | Valued.v x ≤ 1} := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hset]
    exact (isClosed_val_le_one p P).isComplete
  · exact isUniformEmbedding_subtype_val.isUniformInducing

instance kpIntCompleteSpace_inst (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    CompleteSpace (kpInt p P) := kpIntCompleteSpace p P

/-- Membership in the maximal ideal of the valuation ring is `valuation < 1`. -/
lemma mem_maximalIdeal_iff_val_lt_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (x : kpInt p P) :
    x ∈ maximalIdeal (kpInt p P) ↔ Valued.v (x : kpAdic p P) < 1 := by
  change x ∈ maximalIdeal ((Valued.v : Valuation (kpAdic p P) ℤᵐ⁰).valuationSubring) ↔
    Valued.v (x : kpAdic p P) < 1
  exact Valuation.mem_maximalIdeal_iff (K := kpAdic p P) (v := (Valued.v : Valuation (kpAdic p P) ℤᵐ⁰))

/-- Membership in the maximal ideal is `norm < 1`. -/
lemma mem_maximalIdeal_iff_norm_lt_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (x : kpInt p P) :
    x ∈ maximalIdeal (kpInt p P) ↔ ‖x‖ < 1 := by
  rw [mem_maximalIdeal_iff_val_lt_one]
  exact (norm_lt_one_iff_val p P (x : kpAdic p P)).symm

/-- A chosen uniformizer of the DVR `kpInt p P`. -/
noncomputable def uniformizer (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] : kpInt p P :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible (kpInt p P))

/-- The chosen uniformizer is irreducible. -/
lemma uniformizer_irreducible (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Irreducible (uniformizer p P) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (kpInt p P))

/-- The maximal ideal is generated by the uniformizer. -/
lemma maximalIdeal_eq_span_uniformizer (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    maximalIdeal (kpInt p P) = Ideal.span {(uniformizer p P)} :=
  (uniformizer_irreducible p P).maximalIdeal_eq

/-- The uniformizer is nonzero. -/
lemma uniformizer_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    uniformizer p P ≠ 0 := (uniformizer_irreducible p P).ne_zero

/-- The uniformizer has norm strictly less than one. -/
lemma uniformizer_norm_lt_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    ‖uniformizer p P‖ < 1 := by
  have hmem : uniformizer p P ∈ maximalIdeal (kpInt p P) := by
    rw [maximalIdeal_eq_span_uniformizer]
    exact Submodule.mem_span_singleton_self _
  exact (mem_maximalIdeal_iff_norm_lt_one p P (uniformizer p P)).mp hmem

/-- The uniformizer has strictly positive norm. -/
lemma uniformizer_norm_pos (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    0 < ‖uniformizer p P‖ := by
  exact norm_pos_iff.mpr (uniformizer_ne_zero p P)

/-- A unit of the valuation ring has norm exactly one. -/
lemma norm_eq_one_of_unit (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (u : (kpInt p P)ˣ) :
    ‖(u : kpInt p P)‖ = 1 := by
  apply le_antisymm (norm_le_one p P (u : kpInt p P))
  have hle : (1 : ℝ) ≤ ‖(u : kpInt p P)‖ * ‖((u⁻¹ : (kpInt p P)ˣ) : kpInt p P)‖ := by
    calc
      (1 : ℝ) = ‖(1 : kpInt p P)‖ := by simp
      _ = ‖(u : kpInt p P) * ((u⁻¹ : (kpInt p P)ˣ) : kpInt p P)‖ := by
        congr 1
        rw [← Units.val_mul, mul_inv_cancel]
        simp
      _ ≤ ‖(u : kpInt p P)‖ * ‖((u⁻¹ : (kpInt p P)ˣ) : kpInt p P)‖ := norm_mul_le _ _
  have hle2 : (1 : ℝ) ≤ ‖(u : kpInt p P)‖ := by
    calc
      (1 : ℝ) ≤ ‖(u : kpInt p P)‖ * ‖((u⁻¹ : (kpInt p P)ˣ) : kpInt p P)‖ := hle
      _ ≤ ‖(u : kpInt p P)‖ * 1 := by
        exact mul_le_mul_of_nonneg_left (norm_le_one p P ((u⁻¹ : (kpInt p P)ˣ) : kpInt p P))
          (norm_nonneg _)
      _ = ‖(u : kpInt p P)‖ := by simp
  exact hle2

/-- norm of a power of the uniformizer. -/
lemma uniformizer_norm_pow (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (n : ℕ) :
    ‖uniformizer p P ^ n‖ = ‖uniformizer p P‖ ^ n := by
  rw [norm_pow]

/-- powers of the maximal ideal are the uniformizer powers. -/
lemma maximalIdeal_pow_eq_span (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (n : ℕ) :
    (maximalIdeal (kpInt p P)) ^ n = Ideal.span {uniformizer p P ^ n} := by
  rw [maximalIdeal_eq_span_uniformizer, Ideal.span_singleton_pow]

/-- **Norm ↔ maximal-ideal-power dictionary**: an element of the valuation ring
lies in `𝔪^n` iff its norm is at most `‖ϖ‖^n`. -/
theorem mem_maximalIdeal_pow_iff_norm_le (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (x : kpInt p P) (n : ℕ) :
    x ∈ (maximalIdeal (kpInt p P)) ^ n ↔ ‖x‖ ≤ ‖uniformizer p P‖ ^ n := by
  classical
  let ϖ : kpInt p P := uniformizer p P
  have hϖirr : Irreducible ϖ := by simpa [ϖ] using uniformizer_irreducible p P
  constructor
  · intro hx
    rw [maximalIdeal_pow_eq_span] at hx
    rcases (Ideal.mem_span_singleton.mp hx) with ⟨c, hc⟩
    calc
      ‖x‖ = ‖ϖ ^ n * c‖ := by rw [hc]
      _ ≤ ‖ϖ ^ n‖ * ‖c‖ := norm_mul_le _ _
      _ = ‖ϖ‖ ^ n * ‖c‖ := by rw [uniformizer_norm_pow]
      _ ≤ ‖ϖ‖ ^ n * 1 := by
        exact mul_le_mul_of_nonneg_left (norm_le_one p P c) (pow_nonneg (norm_nonneg _) n)
      _ = ‖ϖ‖ ^ n := by simp
  · intro hxnorm
    by_cases hx0 : x = 0
    · rw [hx0]
      simp
    · obtain ⟨m, u, hx⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (x := x) hx0 hϖirr
      have hxnorm_m : ‖x‖ = ‖ϖ‖ ^ m := by
        rw [hx]
        calc
          ‖(u : kpInt p P) * ϖ ^ m‖ = ‖(u : kpInt p P)‖ * ‖ϖ ^ m‖ := by rw [norm_mul]
          _ = 1 * ‖ϖ‖ ^ m := by rw [norm_eq_one_of_unit, uniformizer_norm_pow]
          _ = ‖ϖ‖ ^ m := by simp
      by_cases hn : n ≤ m
      · have hxmem : x ∈ (maximalIdeal (kpInt p P)) ^ m := by
          rw [maximalIdeal_pow_eq_span p P m]
          exact Ideal.mem_span_singleton.mpr ⟨(u : kpInt p P), by simpa [mul_comm] using hx⟩
        exact (Ideal.pow_le_pow_right hn) hxmem
      · have hmn : m < n := Nat.lt_of_not_ge hn
        have hnormlt : ‖ϖ‖ ^ n < ‖ϖ‖ ^ m :=
          pow_lt_pow_right_of_lt_one₀ (uniformizer_norm_pos p P) (uniformizer_norm_lt_one p P) hmn
        have hle : ‖ϖ‖ ^ m ≤ ‖ϖ‖ ^ n := by
          rw [← hxnorm_m]
          exact hxnorm
        exact False.elim ((lt_irrefl (‖ϖ‖ ^ m)) (lt_of_le_of_lt hle hnormlt))

/-- SModEq modulo powers of the maximal ideal is equivalent to a norm bound:
`a ≡ b [SMOD 𝔪^m] ⟺ ‖a - b‖ ≤ ‖ϖ‖^m`. -/
lemma smodEq_ideal_pow_iff_norm_le (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (a b : kpInt p P) (m : ℕ) :
    a ≡ b [SMOD ((maximalIdeal (kpInt p P)) ^ m • ⊤ : Submodule (kpInt p P) (kpInt p P))] ↔
      ‖a - b‖ ≤ ‖uniformizer p P‖ ^ m := by
  classical
  rw [SModEq.sub_mem]
  have h : a - b ∈ ((maximalIdeal (kpInt p P)) ^ m • ⊤ : Submodule (kpInt p P) (kpInt p P)) ↔
      a - b ∈ (maximalIdeal (kpInt p P)) ^ m := by
    simp
  rw [h]
  exact mem_maximalIdeal_pow_iff_norm_le p P (a - b) m

/-- `maximalIdeal (kpInt p P)` is nonzero (a uniformizer lies in it). -/
lemma maximalIdeal_ne_bot (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    maximalIdeal (kpInt p P) ≠ ⊥ := by
  intro h
  have hmem : uniformizer p P ∈ (⊥ : Ideal (kpInt p P)) := by
    rw [← h]
    exact (mem_maximalIdeal_iff_norm_lt_one p P (uniformizer p P)).mpr
      (uniformizer_norm_lt_one p P)
  exact (uniformizer_ne_zero p P) ((Ideal.mem_bot.mp hmem))

/-- **`IsAdicComplete 𝔪 (kpInt p P)`**: the valuation ring of the completion is
complete with respect to its maximal-ideal adic topology.  This is the missing
instance that the Teichmüller-lift step of the unramified-subfield construction
needs (`Perfection.teichmuller` requires `[IsAdicComplete 𝔪 R]`).  Proof: the
algebraic `𝔪`-adic Cauchy condition is, by the dictionary, a metric Cauchy
condition; the metric limit (completeness, `kpIntCompleteSpace`) is then the
algebraic limit by the ultrametric inequality. -/
instance kpIntIsAdicComplete (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    IsAdicComplete (maximalIdeal (kpInt p P)) (kpInt p P) where
  prec' x hx := by
    classical
    -- hx : ∀ {m n}, m ≤ n → x m ≡ x n [SMOD (𝔪^m • ⊤)]
    have hnorm (m n : ℕ) (hmn : m ≤ n) :
        ‖x m - x n‖ ≤ ‖uniformizer p P‖ ^ m := by
      exact (smodEq_ideal_pow_iff_norm_le p P (x m) (x n) m).mp (hx hmn)
    have hb (m n : ℕ) : ‖x m - x n‖ ≤ ‖uniformizer p P‖ ^ min m n := by
      rcases le_total m n with hmn | hnm
      · simpa [min_eq_left hmn] using hnorm m n hmn
      · have hs : ‖x m - x n‖ = ‖x n - x m‖ := by
          rw [← norm_neg]
          congr 1
          abel
        rw [hs]
        simpa [min_eq_right hnm] using hnorm n m hnm
    have hpow (N k : ℕ) (hNk : N ≤ k) : ‖uniformizer p P‖ ^ k ≤ ‖uniformizer p P‖ ^ N := by
      exact (pow_le_pow_iff_right_of_lt_one₀ (uniformizer_norm_pos p P)
        (uniformizer_norm_lt_one p P)).2 hNk
    -- metric Cauchy
    have hcauchy : CauchySeq x := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (uniformizer_norm_lt_one p P)
      refine ⟨N, fun m hm n hn => ?_⟩
      have hb' : ‖x m - x n‖ ≤ ‖uniformizer p P‖ ^ min m n := hb m n
      have hpow' : ‖uniformizer p P‖ ^ min m n ≤ ‖uniformizer p P‖ ^ N := by
        apply hpow
        exact le_min hm hn
      have hlt : ‖x m - x n‖ < ε := lt_of_le_of_lt (le_trans hb' hpow') hN
      simpa [dist_eq_norm] using hlt
    rcases cauchySeq_tendsto_of_complete hcauchy with ⟨L, hL⟩
    refine ⟨L, fun n => ?_⟩
    rw [smodEq_ideal_pow_iff_norm_le]
    have hlim (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k in atTop, ‖x k - L‖ < ε := by
      simpa [dist_eq_norm] using (Metric.tendsto_atTop.mp hL ε hε)
    have hEv : ∀ᶠ k in atTop, n ≤ k ∧ ‖x k - L‖ < ‖uniformizer p P‖ ^ (n + 1) := by
      exact (eventually_ge_atTop n).and (hlim (‖uniformizer p P‖ ^ (n + 1))
        (pow_pos (uniformizer_norm_pos p P) (n + 1)))
    obtain ⟨k, hkn, hkL⟩ := hEv.exists
    have hultra : ‖x n - L‖ ≤ max ‖x n - x k‖ ‖x k - L‖ := by
      have hd := dist_triangle_max (x n) (x k) L
      simpa [dist_eq_norm] using hd
    have hnk : ‖x n - x k‖ ≤ ‖uniformizer p P‖ ^ n := hnorm n k hkn
    have hpowdec : ‖uniformizer p P‖ ^ (n + 1) ≤ ‖uniformizer p P‖ ^ n := by
      exact hpow n (n + 1) (Nat.le_succ n)
    have hkLle : ‖x k - L‖ ≤ ‖uniformizer p P‖ ^ n := le_trans (le_of_lt hkL) hpowdec
    have hmax : max ‖x n - x k‖ ‖x k - L‖ ≤ ‖uniformizer p P‖ ^ n :=
      max_le hnk hkLle
    exact le_trans hultra hmax

end
end Submission.Vdw.LocalField