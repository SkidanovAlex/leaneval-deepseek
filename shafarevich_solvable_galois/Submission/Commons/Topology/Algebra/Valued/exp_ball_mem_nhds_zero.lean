import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Algebra.Valued.ValuationTopology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Filter Set
open scoped Topology
open WithZero

namespace expBallMemNhdsZero

/-- A subgroup-cut lemma for the integers used to prove that every `exp`-ball
`{x | v x < exp n}` (for `n : ℤ`) around zero in a `ℤᵐ⁰`-valued field is a
neighbourhood of zero.

Given a subset `S ⊆ ℤ` closed under addition, negation and containing `0`, for every
`n : ℤ` there is `m₀ ∈ S` such that every element of `S` strictly below `m₀` is
strictly below `n`.  (Intuitively: `m₀` is the least element of `S` which is `≥ n`,
or `n` itself when `n ∈ S`, or `0` when `S = {0}` and `n < 0`.) -/
lemma int_subgroup_cut {S : Set ℤ} (h0 : 0 ∈ S)
    (hadd : ∀ ⦃a b : ℤ⦄, a ∈ S → b ∈ S → a + b ∈ S)
    (hneg : ∀ ⦃a : ℤ⦄, a ∈ S → -a ∈ S) (n : ℤ) :
    ∃ m₀ ∈ S, ∀ m ∈ S, m < m₀ → m < n := by
  classical
  by_cases hn : n ∈ S
  · exact ⟨n, hn, fun m _ hmn => hmn⟩
  · by_cases hS : ∃ d ∈ S, d ≠ 0
    · rcases hS with ⟨d, hdS, hd0⟩
      let d' : ℤ := if 0 < d then d else -d
      have hd'pos : 0 < d' := by
        by_cases h : 0 < d
        · simp [d', h]
        · have hle : d ≤ 0 := not_lt.mp h
          have hlt : d < 0 := lt_of_le_of_ne hle hd0
          simp [d', h, hlt]
      have hd'S : d' ∈ S := by
        by_cases h : 0 < d
        · simp [d', h]; exact hdS
        · have hle : d ≤ 0 := not_lt.mp h
          have hlt : d < 0 := lt_of_le_of_ne hle hd0
          simpa [d', h] using hneg hdS
      have hmem_nsmul : ∀ k : ℕ, ((k : ℤ) * d') ∈ S := by
        intro k
        induction k with
        | zero => simpa using h0
        | succ k ih =>
            rw [Nat.cast_succ, add_mul, one_mul]
            exact hadd ih hd'S
      obtain ⟨k, hk⟩ := exists_nat_gt (R := ℤ) n
      have hkd' : ((k : ℤ) * d') ∈ S := hmem_nsmul k
      have hnlt : n < (k : ℤ) * d' := by
        have hk' : (k : ℤ) ≤ (k : ℤ) * d' := by
          have h1 : (1 : ℤ) ≤ d' := by omega
          have hk0 : (0 : ℤ) ≤ k := by exact_mod_cast Nat.zero_le k
          nlinarith
        exact lt_of_lt_of_le hk hk'
      let P : ℤ → Prop := fun m => m ∈ S ∧ n < m
      have hbdd : ∃ b : ℤ, ∀ z : ℤ, P z → b ≤ z := by
        refine ⟨n + 1, ?_⟩
        intro z hz
        omega
      have hinhab : ∃ z : ℤ, P z := ⟨(k : ℤ) * d', ⟨hkd', hnlt⟩⟩
      rcases Int.exists_least_of_bdd hbdd hinhab with ⟨m₀, hm₀P, hm₀min⟩
      refine ⟨m₀, hm₀P.1, ?_⟩
      intro m hm hm0
      by_contra hmn
      have hnm' : n ≤ m := le_of_not_gt hmn
      have hmn_ne : m ≠ n := by
        intro hmn_eq
        apply hn
        simpa [hmn_eq] using hm
      have hnltm : n < m := lt_of_le_of_ne hnm' (Ne.symm hmn_ne)
      have hPm : P m := ⟨hm, hnltm⟩
      have hmin := hm₀min m hPm
      exact (not_le_of_gt hm0) hmin
    · refine ⟨0, h0, ?_⟩
      intro m hm hm0
      have hmz : m = 0 := by
        by_contra hne
        exact hS ⟨m, hm, hne⟩
      omega

end expBallMemNhdsZero

namespace Commons.Topology.Algebra.Valued

/-- For any `n : ℤ`, the sublevel set `{x | v x < exp n}` of the valuation
`v : K → ℤᵐ⁰` of a valued field is a neighbourhood of zero (for the topology
induced by the valuation). -/
theorem exp_ball_mem_nhds_zero {K : Type*} [Field K] [vK : Valued K ℤᵐ⁰] (n : ℤ) :
    letI : UniformSpace K := vK.toUniformSpace
    letI : TopologicalSpace K := UniformSpace.toTopologicalSpace
    {x : K | Valued.v x < exp n} ∈ 𝓝 (0 : K) := by
  let v : Valuation K ℤᵐ⁰ := vK.v
  let S : Set ℤ := {m : ℤ | ∃ x : K, v x = exp m}
  have hS0 : (0 : ℤ) ∈ S := by
    refine ⟨(1 : K), ?_⟩
    simp
  have hSadd : ∀ ⦃a b : ℤ⦄, a ∈ S → b ∈ S → a + b ∈ S := by
    rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨x * y, ?_⟩
    rw [map_mul, hx, hy]
    rw [← WithZero.exp_add]
  have hSneg : ∀ ⦃a : ℤ⦄, a ∈ S → -a ∈ S := by
    rintro a ⟨x, hx⟩
    refine ⟨x⁻¹, ?_⟩
    rw [map_inv₀, hx]
    rw [← WithZero.exp_neg]
  obtain ⟨m₀, hm₀S, hcut⟩ := expBallMemNhdsZero.int_subgroup_cut hS0 hSadd hSneg n
  rcases hm₀S with ⟨a₀, ha₀⟩
  have ha₀ne : v a₀ ≠ 0 := by
    rw [ha₀]
    exact WithZero.exp_ne_zero
  let r : MonoidWithZeroHom.ValueGroup₀ (.ofClass v) := v.restrict a₀
  have hr_ne : r ≠ 0 := by
    intro hr
    have he := congrArg MonoidWithZeroHom.ValueGroup₀.embedding hr
    have : (MonoidWithZeroHom.ofClass v) a₀ = 0 := by
      simpa [Valuation.restrict_def, r] using he
    exact ha₀ne (by simpa [MonoidWithZeroHom.coe_ofClass] using this)
  let γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v))ˣ := Units.mk0 r hr_ne
  rw [Valued.mem_nhds_zero]
  refine ⟨γ, ?_⟩
  intro x hx
  have hx' : v x < exp m₀ := by
    have hvx : v x <
        MonoidWithZeroHom.ValueGroup₀.embedding
          (γ : MonoidWithZeroHom.ValueGroup₀ (.ofClass v)) := by
      exact (Valuation.restrict_lt_iff_lt_embedding v).mp hx
    have hem : MonoidWithZeroHom.ValueGroup₀.embedding
        (γ : MonoidWithZeroHom.ValueGroup₀ (.ofClass v)) = exp m₀ := by
      change MonoidWithZeroHom.ValueGroup₀.embedding (v.restrict a₀) = exp m₀
      rw [Valuation.restrict_def, MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
      simp [MonoidWithZeroHom.coe_ofClass, ha₀]
    rwa [hem] at hvx
  by_cases hx0 : x = 0
  · subst hx0
    simp
  · have hvx_ne : v x ≠ 0 := by
      intro h
      apply hx0
      exact (v.zero_iff).1 h
    let m : ℤ := log (v x)
    have hmS : m ∈ S := by
      refine ⟨x, ?_⟩
      exact (WithZero.exp_log hvx_ne).symm
    have hmm : m < m₀ := by
      have : exp m < exp m₀ := by
        simpa [m, WithZero.exp_log hvx_ne] using hx'
      exact (WithZero.exp_lt_exp).mp this
    have hmn : m < n := hcut m hmS hmm
    have : exp m < exp n := (WithZero.exp_lt_exp).mpr hmn
    simpa [m, WithZero.exp_log hvx_ne] using this

end Commons.Topology.Algebra.Valued