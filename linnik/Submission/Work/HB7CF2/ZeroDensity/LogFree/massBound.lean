import Mathlib
import Submission.Work.ZeroDensity.LogFree.RouteDefs
import Submission.Work.LinnikAreas.Density4.psiM_divisor_sum_zero
import Submission.Work.ZeroDensity.Jutila.bvDefs
import Submission.Work.HB7CF2.ZeroDensity.Jutila.LzSqIntGood
import Submission.Work.HB7CF2.ZeroDensity.Jutila.LzSqHard
import Submission.Work.ZeroDensity.LogFree.gfunWeightFacts

/-!
# `Work.ZeroDensity.LogFree.massBound`

Heath-Brown (1992) (11.14): the weighted second moment `Σ_{n ≤ N} Ψ(n)² n⁻¹ g(n)` of the
`ψ`-mollifier divisor sum is `O(1)`, uniformly in `q, T` and `N`.

The sharp input is Graham's estimate (HB (11.13)) for the truncated von Mangoldt sums, available
in the workspace for integer cutoffs in both ranges (`Jutila.LzSqIntGood` for `z² ≤ N`,
`Jutila.LzSqHard` for `z ≤ N < z²`) and extended here to real cutoffs by the affine
interpolation of `Jutila/LzSqUpper.lean`.  The passage to `massBound` uses the identity
`log(V/U)·Ψ_{U,V}(n) = Λ_V(n) − Λ_U(n)` (so that `Ψ`'s second moment is the second moment of the
difference of two truncated von Mangoldt sums) and a crude Abel summation, which needs only the
partial-sum bound `Σ_{n ≤ N} Ψ(n)² ≤ C N / log(V/U) + O(1)`.

The weight facts `gfunWeightFacts` (nonnegativity, monotonicity of `n ↦ gfun n / n`, and
`Σ_{n ≤ N} gfun n / n ≤ log(2X) + 2`) are proved in `LogFree/gfunWeightFacts.lean`.
-/

namespace Work.ZeroDensity.LogFree

open Finset
open scoped BigOperators

noncomputable section

lemma psiSum_mul_log (U V : ℝ) (hU : 0 < U) (hUV : U < V) (n : ℕ) :
    Real.log (V / U) * psiSum U V n
      = Work.ZeroDensity.Jutila.Lz V n - Work.ZeroDensity.Jutila.Lz U n := by
  have hV : 0 < V := lt_trans hU hUV
  have hlogpos : 0 < Real.log (V / U) := Real.log_pos (by rw [one_lt_div hU]; exact hUV)
  have hlogne : Real.log (V / U) ≠ 0 := ne_of_gt hlogpos
  rw [psiSum, Work.ZeroDensity.Jutila.Lz, Work.ZeroDensity.Jutila.Lz, Finset.mul_sum,
    Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have := Nat.pos_of_mem_divisors hd
    exact_mod_cast this
  rw [Work.LinnikAreas.Density4.psiM]
  by_cases h1 : (d : ℝ) ≤ U
  · rw [if_pos h1, if_pos (le_trans h1 hUV.le), if_pos h1]
    have hlogd : Real.log (V / U) = Real.log (V / (d : ℝ)) - Real.log (U / (d : ℝ)) := by
      rw [Real.log_div hV.ne' hU.ne', Real.log_div hV.ne' hd0.ne', Real.log_div hU.ne' hd0.ne']
      ring
    rw [hlogd]; ring
  · rw [if_neg h1]
    by_cases h2 : (d : ℝ) ≤ V
    · rw [if_pos h2, if_neg h1, if_pos h2]
      have hcancel : Real.log (V / U) * ((ArithmeticFunction.moebius d : ℝ)
          * Real.log (V / (d : ℝ)) / Real.log (V / U))
          = (ArithmeticFunction.moebius d : ℝ) * Real.log (V / (d : ℝ)) := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hlogne]
      rw [hcancel, sub_zero]
    · rw [if_neg h2, if_neg h1, if_neg h2]
      ring

private lemma sum_moebius_divisors_eq_zero_int (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply (f := ArithmeticFunction.moebius) (x := n),
    ArithmeticFunction.moebius_mul_coe_zeta]
  exact ArithmeticFunction.one_apply

private lemma sum_moebius_divisors_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) = 0 := by
  have h := sum_moebius_divisors_eq_zero_int n
  rw [if_neg (by omega : ¬ n = 1)] at h
  have hcast : ((∑ d ∈ n.divisors, ArithmeticFunction.moebius d : ℤ) : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) := by
    push_cast
    rfl
  rw [← hcast, h, Int.cast_zero]

lemma Lz_eq_sum_of_le {z : ℝ} {n : ℕ} (hz : (n : ℝ) ≤ z) :
    Work.ZeroDensity.Jutila.Lz z n
      = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * (Real.log z - Real.log d) := by
  have hf : ∀ d ∈ n.divisors, (d : ℝ) ≤ z := by
    intro d hd
    have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
      (Nat.dvd_of_mem_divisors hd)
    exact le_trans (by exact_mod_cast hdn) hz
  rw [Work.ZeroDensity.Jutila.Lz, Finset.filter_true_of_mem hf]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have := Nat.pos_of_mem_divisors hd
    exact_mod_cast this
  have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
    (Nat.dvd_of_mem_divisors hd)
  have hzpos : 0 < z := lt_of_lt_of_le hdpos (le_trans (by exact_mod_cast hdn) hz)
  rw [Real.log_div (ne_of_gt hzpos) (ne_of_gt hdpos)]

lemma Lz_eq_of_le {z z' : ℝ} {n : ℕ} (hn : 2 ≤ n) (hz : (n : ℝ) ≤ z) (hz' : (n : ℝ) ≤ z') :
    Work.ZeroDensity.Jutila.Lz z n = Work.ZeroDensity.Jutila.Lz z' n := by
  have h1 := Lz_eq_sum_of_le (z := z) hz
  have h2 := Lz_eq_sum_of_le (z := z') hz'
  have key : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * (Real.log z - Real.log d))
      = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * (Real.log z' - Real.log d) := by
    have hpt : ∀ d ∈ n.divisors,
        (ArithmeticFunction.moebius d : ℝ) * (Real.log z - Real.log d)
        = (ArithmeticFunction.moebius d : ℝ) * (Real.log z' - Real.log d)
          + (ArithmeticFunction.moebius d : ℝ) * (Real.log z - Real.log z') := by
      intro d hd; ring
    calc (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * (Real.log z - Real.log d))
        = ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℝ) * (Real.log z' - Real.log d)
            + (ArithmeticFunction.moebius d : ℝ) * (Real.log z - Real.log z')) :=
          Finset.sum_congr rfl hpt
      _ = (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * (Real.log z' - Real.log d))
            + (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) * (Real.log z - Real.log z') := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * (Real.log z' - Real.log d) := by
          rw [sum_moebius_divisors_eq_zero hn, zero_mul, add_zero]
  rw [h1, h2, key]

lemma Lz_one {z : ℝ} (hz : 1 ≤ z) : Work.ZeroDensity.Jutila.Lz z 1 = Real.log z := by
  have hz' : ((1 : ℕ) : ℝ) ≤ z := by exact_mod_cast hz
  rw [Lz_eq_sum_of_le hz', Nat.divisors_one, Finset.sum_singleton]
  simp


lemma Lz_int_eq_expl (z n : ℕ) :
    Work.ZeroDensity.Jutila.Lz (z : ℝ) n
      = ∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ z),
          (ArithmeticFunction.moebius d : ℝ) * Real.log ((z : ℝ) / (d : ℝ)) := by
  rw [Work.ZeroDensity.Jutila.Lz]
  refine Finset.sum_congr ?_ (fun d _ => rfl)
  ext d
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, Nat.cast_le.mp h.2⟩, fun h => ⟨h.1, Nat.cast_le.mpr h.2⟩⟩

lemma LzSqSharpInt :
    ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N →
      (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz (z : ℝ) n) ^ 2)
        ≤ (N : ℝ) * Real.log (z : ℝ) + C * (N : ℝ) := by
  obtain ⟨C₁, hC₁, h₁⟩ := Work.ZeroDensity.Jutila.LzSqIntGood
  obtain ⟨C₂, hC₂, h₂⟩ := Work.ZeroDensity.Jutila.LzSqHard
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro z N hz hzN
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rcases le_or_gt (z * z) N with h | h
  · refine (h₁ z N hz hzN h).trans ?_
    nlinarith [le_max_left C₁ C₂, hNnn]
  · have hconv : ∀ n : ℕ, (Work.ZeroDensity.Jutila.Lz (z : ℝ) n) ^ 2
        = (∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ z),
            (ArithmeticFunction.moebius d : ℝ) * Real.log ((z : ℝ) / (d : ℝ))) ^ 2 := by
      intro n; rw [Lz_int_eq_expl z n]
    rw [Finset.sum_congr rfl (fun n _ => hconv n)]
    refine (h₂ z N hz hzN h).trans ?_
    nlinarith [le_max_right C₁ C₂, hNnn]

private lemma Lz_eq_sum_shift {k : ℕ} {z : ℝ} (hz1 : (k : ℝ) ≤ z) (hz2 : z < ((k + 1 : ℕ) : ℝ))
    (n : ℕ) :
    Work.ZeroDensity.Jutila.Lz z n = ∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k),
      (ArithmeticFunction.moebius d : ℝ) * (Real.log z - Real.log d) := by
  rw [Work.ZeroDensity.Jutila.Lz]
  rw [Finset.filter_congr (p := fun d : ℕ => (d : ℝ) ≤ z) (q := fun d : ℕ => d ≤ k)]
  · refine Finset.sum_congr rfl (fun d hd => ?_)
    obtain ⟨hdmem, hdk⟩ := Finset.mem_filter.mp hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hdmem).1
    have hdne : d ≠ 0 := fun h =>
      (Nat.mem_divisors.mp hdmem).2 (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
    have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hdne
    have hzpos : 0 < z := by
      have h2 : (1 : ℝ) ≤ (k : ℝ) := by
        have : 1 ≤ k := le_trans hd1 hdk
        exact_mod_cast this
      linarith
    rw [Real.log_div (ne_of_gt hzpos) (by exact_mod_cast hdne)]
  · intro d _
    constructor
    · intro hd
      have h : (d : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_le_of_lt hd hz2
      have h' : d < k + 1 := by exact_mod_cast h
      omega
    · intro hd
      have h : (d : ℝ) ≤ (k : ℝ) := by exact_mod_cast hd
      linarith

private lemma sum_filter_succ_eq (k n : ℕ) (F : ℕ → ℝ) (hF : F (k + 1) = 0) :
    (∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k + 1), F d)
      = ∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k), F d := by
  have hsplit : (∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k + 1), F d)
      = (∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k), F d)
        + (∑ d ∈ n.divisors.filter (fun d : ℕ => d = k + 1), F d) := by
    rw [← Finset.sum_union (s₁ := n.divisors.filter (fun d : ℕ => d ≤ k))
          (s₂ := n.divisors.filter (fun d : ℕ => d = k + 1)) ?_]
    · congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hd, hle⟩
        rcases Nat.lt_or_ge d (k + 1) with h | h
        · exact Or.inl ⟨hd, by omega⟩
        · exact Or.inr ⟨hd, by omega⟩
      · rintro (⟨hd, hk⟩ | ⟨hd, hk⟩)
        · exact ⟨hd, by omega⟩
        · exact ⟨hd, by omega⟩
    · rw [Finset.disjoint_left]
      intro d hd1 hd2
      simp only [Finset.mem_filter] at hd1 hd2
      omega
  have hzero : (∑ d ∈ n.divisors.filter (fun d : ℕ => d = k + 1), F d) = 0 := by
    refine Finset.sum_eq_zero (fun d hd => ?_)
    obtain ⟨_, hd2⟩ := Finset.mem_filter.mp hd
    rw [hd2]; exact hF
  rw [hsplit, hzero, add_zero]

private lemma affine_comb_sums {ι : Type*} (s : Finset ι) (c L : ι → ℝ) {A B α : ℝ}
    (hAB : B - A ≠ 0) :
    (∑ d ∈ s, c d * (α - L d)) =
      ((B - α) / (B - A)) * (∑ d ∈ s, c d * (A - L d))
      + ((α - A) / (B - A)) * (∑ d ∈ s, c d * (B - L d)) := by
  have hsc : ∀ x : ℝ, ((B - α) / (B - A)) * (A - x) + ((α - A) / (B - A)) * (B - x) = α - x := by
    intro x; field_simp; ring
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun d _ => by rw [← hsc (L d)]; ring)

private lemma Lz_affine_interp (k : ℕ) (hk : 1 ≤ k) (z : ℝ) (hz1 : (k : ℝ) ≤ z)
    (hz2 : z < ((k + 1 : ℕ) : ℝ)) (n : ℕ) :
    Work.ZeroDensity.Jutila.Lz z n =
      ((Real.log ((k + 1 : ℕ) : ℝ) - Real.log z) / (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)))
        * Work.ZeroDensity.Jutila.Lz (k : ℝ) n
      + ((Real.log z - Real.log (k : ℝ)) / (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)))
        * Work.ZeroDensity.Jutila.Lz ((k + 1 : ℕ) : ℝ) n := by
  have hz : Work.ZeroDensity.Jutila.Lz z n = ∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k),
      (ArithmeticFunction.moebius d : ℝ) * (Real.log z - Real.log d) :=
    Lz_eq_sum_shift hz1 hz2 n
  have hk0 : Work.ZeroDensity.Jutila.Lz (k : ℝ) n
      = ∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k),
      (ArithmeticFunction.moebius d : ℝ) * (Real.log (k : ℝ) - Real.log d) :=
    Lz_eq_sum_shift (k := k) (z := (k : ℝ)) le_rfl (by push_cast; linarith) n
  have hk1 : Work.ZeroDensity.Jutila.Lz ((k + 1 : ℕ) : ℝ) n
      = ∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k),
      (ArithmeticFunction.moebius d : ℝ) * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log d) := by
    have hz2' : ((k + 1 : ℕ) : ℝ) < (((k + 1) + 1 : ℕ) : ℝ) := by push_cast; linarith
    rw [Lz_eq_sum_shift (k := k + 1) (z := ((k + 1 : ℕ) : ℝ)) le_rfl hz2']
    exact sum_filter_succ_eq k n _ (by
      show (ArithmeticFunction.moebius (k + 1) : ℝ) *
        (Real.log ((k + 1 : ℕ) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ)) = 0
      rw [sub_self, mul_zero])
  have hAB : Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) ≠ 0 := by
    have h : Real.log (k : ℝ) < Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_lt_log (by exact_mod_cast (by omega : 0 < k)) (by push_cast; linarith)
    linarith
  rw [hz, hk0, hk1]
  exact affine_comb_sums _ _ _ hAB

private lemma sq_le_convex_comb {θ ψ a b : ℝ} (h0 : 0 ≤ θ) (h1 : 0 ≤ ψ) (hs : θ + ψ = 1) :
    (θ * a + ψ * b) ^ 2 ≤ θ * a ^ 2 + ψ * b ^ 2 := by
  nlinarith [sq_nonneg (a - b), mul_nonneg h0 h1, hs]

lemma LzSqReal {C : ℝ} (hC : 0 < C)
    (hInt : ∀ (z N : ℕ), 2 ≤ z → z ≤ N →
      (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz (z : ℝ) n) ^ 2)
        ≤ (N : ℝ) * Real.log (z : ℝ) + C * (N : ℝ))
    (z : ℝ) (hz : 2 ≤ z) (N : ℕ) (hzN : z ≤ (N : ℝ)) :
    (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz z n) ^ 2)
      ≤ (N : ℝ) * Real.log z + C * (N : ℝ) := by
  set k := ⌊z⌋₊ with hkdef
  have hk2 : 2 ≤ k := Nat.le_floor (by exact_mod_cast hz)
  have hkz : (k : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hzk1 : z < ((k + 1 : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one z
    rw [← hkdef] at h
    push_cast
    linarith
  have hk1 : 1 ≤ k := by omega
  set A : ℝ := Real.log (k : ℝ) with hA
  set B : ℝ := Real.log ((k + 1 : ℕ) : ℝ) with hB
  set α : ℝ := Real.log z with hα
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hzpos : (0 : ℝ) < z := by linarith
  have hAα : A ≤ α := by rw [hA, hα]; exact Real.log_le_log hkpos hkz
  have hαB : α < B := by rw [hα, hB]; exact Real.log_lt_log hzpos hzk1
  have hAB : 0 < B - A := by linarith
  have hθ0 : 0 ≤ (B - α) / (B - A) := div_nonneg (by linarith) (le_of_lt hAB)
  have hψ0 : 0 ≤ (α - A) / (B - A) := div_nonneg (by linarith) (le_of_lt hAB)
  have hsumθ : (B - α) / (B - A) + (α - A) / (B - A) = 1 := by field_simp; ring
  have hcomb : ((B - α) / (B - A)) * A + ((α - A) / (B - A)) * B = α := by
    field_simp; ring
  have hterm : ∀ n : ℕ, (Work.ZeroDensity.Jutila.Lz z n) ^ 2 ≤
      ((B - α) / (B - A)) * (Work.ZeroDensity.Jutila.Lz (k : ℝ) n) ^ 2
        + ((α - A) / (B - A)) * (Work.ZeroDensity.Jutila.Lz ((k + 1 : ℕ) : ℝ) n) ^ 2 := by
    intro n
    have hinterp := Lz_affine_interp k hk1 z hkz hzk1 n
    rw [← hA, ← hB, ← hα] at hinterp
    rw [hinterp]
    exact sq_le_convex_comb hθ0 hψ0 hsumθ
  have hsumle : (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz z n) ^ 2) ≤
      ((B - α) / (B - A)) * (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz (k : ℝ) n) ^ 2)
        + ((α - A) / (B - A)) * (∑ n ∈ Finset.Icc 1 N,
            (Work.ZeroDensity.Jutila.Lz ((k + 1 : ℕ) : ℝ) n) ^ 2) := by
    calc (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz z n) ^ 2)
        ≤ ∑ n ∈ Finset.Icc 1 N, (((B - α) / (B - A)) * (Work.ZeroDensity.Jutila.Lz (k : ℝ) n) ^ 2
            + ((α - A) / (B - A)) * (Work.ZeroDensity.Jutila.Lz ((k + 1 : ℕ) : ℝ) n) ^ 2) :=
          Finset.sum_le_sum (fun n _ => hterm n)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rcases eq_or_lt_of_le hkz with hzk | hzk
  · have hkN : k ≤ N := by
      have h' : (k : ℝ) ≤ (N : ℝ) := by rw [hzk]; exact hzN
      exact_mod_cast h'
    have hkeq : (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz z n) ^ 2)
        = ∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz (k : ℝ) n) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hzk]
    rw [hkeq, hα, ← hzk]
    exact hInt k N hk2 hkN
  · have hkN : k ≤ N := by
      have h' : (k : ℝ) ≤ (N : ℝ) := le_trans (le_of_lt hzk) hzN
      exact_mod_cast h'
    have hk1N : k + 1 ≤ N := by
      have hlt : k < N := by
        have h' : (k : ℝ) < (N : ℝ) := lt_of_lt_of_le hzk hzN
        exact_mod_cast h'
      omega
    have hIntk := hInt k N hk2 hkN
    have hIntk1 := hInt (k + 1) N (by omega) hk1N
    have hb1 := mul_le_mul_of_nonneg_left hIntk hθ0
    have hb2 := mul_le_mul_of_nonneg_left hIntk1 hψ0
    have hcomb' : ((B - α) / (B - A)) * Real.log (k : ℝ)
        + ((α - A) / (B - A)) * Real.log ((k + 1 : ℕ) : ℝ) = Real.log z := by
      rw [← hA, ← hB, ← hα]
      exact hcomb
    have e : ((B - α) / (B - A)) * ((N : ℝ) * Real.log (k : ℝ) + C * (N : ℝ))
        + ((α - A) / (B - A)) * ((N : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) + C * (N : ℝ))
        = (N : ℝ) * Real.log z + C * (N : ℝ) := by
      linear_combination (N : ℝ) * hcomb' + (C * (N : ℝ)) * hsumθ
    nlinarith [hsumle, hb1, hb2, e]

private lemma sum_Icc_one_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, f n = f 1 + ∑ n ∈ Finset.Icc 2 N, f n := by
  have hset : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]

lemma Lz_sq_bound {C : ℝ} (hC : 0 < C)
    (hInt : ∀ (z N : ℕ), 2 ≤ z → z ≤ N →
      (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz (z : ℝ) n) ^ 2)
        ≤ (N : ℝ) * Real.log (z : ℝ) + C * (N : ℝ))
    (z : ℝ) (hz : 2 ≤ z) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz z n) ^ 2)
      ≤ (Real.log z) ^ 2 + (N : ℝ) * Real.log z + C * (N : ℝ) := by
  have hz0 : 0 < z := by linarith
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  by_cases hzN : z ≤ (N : ℝ)
  · have h := LzSqReal hC hInt z hz N hzN
    nlinarith [h, sq_nonneg (Real.log z)]
  · push_neg at hzN
    rcases Nat.lt_or_ge N 2 with hN | hN
    · have hsub : Finset.Icc 1 N ⊆ ({1} : Finset ℕ) := by
        intro n hn
        simp only [Finset.mem_Icc] at hn
        simp only [Finset.mem_singleton]
        omega
      have h1 : (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz z n) ^ 2)
          ≤ (Real.log z) ^ 2 := by
        refine (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_).trans ?_
        · intro n hn _
          rw [Finset.mem_singleton] at hn
          subst hn
          rw [Lz_one (by linarith : (1:ℝ) ≤ z)]
          positivity
        · rw [Finset.sum_singleton, Lz_one (by linarith : (1:ℝ) ≤ z)]
      have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith [h1, hlogz, hNnn, hC.le]
    · have hsplit := sum_Icc_one_split (fun n => (Work.ZeroDensity.Jutila.Lz z n) ^ 2)
        (by omega : 1 ≤ N)
      have hbridge : ∀ n ∈ Finset.Icc 2 N,
          (Work.ZeroDensity.Jutila.Lz z n) ^ 2
            = (Work.ZeroDensity.Jutila.Lz ((N : ℕ) : ℝ) n) ^ 2 := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        have hn2 : 2 ≤ n := hn.1
        have hnN : n ≤ N := hn.2
        have h2 : (n : ℝ) ≤ ((N : ℕ) : ℝ) := Nat.cast_le.mpr hnN
        have h1 : (n : ℝ) ≤ z := le_trans h2 hzN.le
        rw [Lz_eq_of_le (z := z) (z' := ((N:ℕ):ℝ)) (n := n) hn2 h1 h2]
      have hle : (∑ n ∈ Finset.Icc 2 N, (Work.ZeroDensity.Jutila.Lz ((N : ℕ) : ℝ) n) ^ 2)
          ≤ (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz ((N : ℕ) : ℝ) n) ^ 2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro n hn
          simp only [Finset.mem_Icc] at hn ⊢
          omega
        · intro n _ _
          positivity
      have hsharp := LzSqReal hC hInt (N : ℝ) (by exact_mod_cast hN) N le_rfl
      have hlogN : Real.log ((N : ℕ) : ℝ) ≤ Real.log z := Real.log_le_log (by positivity) hzN.le
      have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      rw [hsplit, Finset.sum_congr rfl hbridge, Lz_one (by linarith : (1:ℝ) ≤ z)]
      nlinarith [hle, hsharp, hlogN, hNnn]


private lemma sum_Icc_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 (N + 1), f n = (∑ n ∈ Finset.Icc 1 N, f n) + f (N + 1) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have hset : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), add_comm]

private lemma abel_id (b w : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, b n * w n)
      = (∑ n ∈ Finset.Icc 1 N, (∑ m ∈ Finset.Icc 1 n, b m) * (w n - w (n + 1)))
        + (∑ m ∈ Finset.Icc 1 N, b m) * w (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ (fun n => b n * w n) N, ih,
        sum_Icc_succ (fun n => (∑ m ∈ Finset.Icc 1 n, b m) * (w n - w (n + 1))) N,
        sum_Icc_succ (fun m => b m) N]
    ring

private lemma abel_telescope1 (w : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (w n - w (n + 1))) = w 1 - w (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_Icc_succ (fun n => w n - w (n + 1)) N, ih]; ring

private lemma abel_telescope2 (w : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ) * (w n - w (n + 1)))
      = (∑ n ∈ Finset.Icc 1 N, w n) - (N : ℝ) * w (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ (fun n => (n : ℝ) * (w n - w (n + 1))) N, ih, sum_Icc_succ w N]
    push_cast
    ring

private lemma abel_partial {b w : ℕ → ℝ} {K M : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hw : ∀ n : ℕ, 0 ≤ w n) (hwmono : ∀ n : ℕ, 1 ≤ n → w (n + 1) ≤ w n)
    (hA : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, b n ≤ K * (N : ℝ) + M) :
    ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, b n * w n
      ≤ K * (∑ n ∈ Finset.Icc 1 N, w n) + (K + M) * w 1 := by
  intro N
  rw [abel_id b w N]
  have hterm : ∀ n ∈ Finset.Icc 1 N, (∑ m ∈ Finset.Icc 1 n, b m) * (w n - w (n + 1))
      ≤ (K * (n : ℝ) + M) * (w n - w (n + 1)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hd : 0 ≤ w n - w (n + 1) := by linarith [hwmono n hn.1]
    exact mul_le_mul_of_nonneg_right (hA n) hd
  have hone : (∑ m ∈ Finset.Icc 1 N, b m) * w (N + 1) ≤ (K * (N : ℝ) + M) * w (N + 1) :=
    mul_le_mul_of_nonneg_right (hA N) (hw (N + 1))
  have hstep := add_le_add (Finset.sum_le_sum hterm) hone
  have hsum1 : (∑ n ∈ Finset.Icc 1 N, (K * (n : ℝ) + M) * (w n - w (n + 1)))
      = K * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) * (w n - w (n + 1)))
        + M * (∑ n ∈ Finset.Icc 1 N, (w n - w (n + 1))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [hsum1, abel_telescope1 w N, abel_telescope2 w N] at hstep
  have hNcast : ((N : ℕ) : ℝ) = (N : ℝ) := rfl
  nlinarith [hstep, hw 1, hw (N + 1), hK, hM]


/-! ## The main theorem -/

set_option maxHeartbeats 8000000 in
theorem massBoundCF (p : Work.ZeroDensity.LogFree.Params) : ∃ C_A : ℝ, 0 < C_A ∧ ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (q : ℕ), 2 ≤ q → ∀ [NeZero q] (T : ℝ), 1 ≤ T → D₀ ≤ Work.ZeroDensity.LogFree.scale q T →
    ∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N,
        (Work.ZeroDensity.LogFree.psiSum (Work.ZeroDensity.LogFree.Dpow q T p.u)
            (Work.ZeroDensity.LogFree.Dpow q T p.v) n) ^ 2 * ((n : ℝ))⁻¹
          * Work.ZeroDensity.LogFree.gfun (Work.ZeroDensity.LogFree.Dpow q T p.x)
              (Work.ZeroDensity.LogFree.Dpow q T p.u / (Work.ZeroDensity.LogFree.Lscale q T) ^ 2) n)
        ≤ C_A := by
  obtain ⟨C, hC, hInt⟩ := LzSqSharpInt
  have hpu : 0 < p.u := lt_trans p.hw p.hwu
  have huv : p.u < p.v := p.huv
  have hvx : p.v < p.x := p.hvx
  have hvu : 0 < p.v - p.u := by linarith
  have hxu : 0 < p.x - p.u := by linarith
  have hpx3 : 0 ≤ p.x + 3 := by linarith
  set K₁ : ℝ := 2 * (p.u + p.v) / (p.v - p.u) with hK₁def
  set K₂ : ℝ := 4 * C with hK₂def
  set K₃ : ℝ := 2 * (p.u ^ 2 + p.v ^ 2) / (p.v - p.u) ^ 2 with hK₃def
  set S : ℝ := max (max 1 (1 / (p.v - p.u))) (max (Real.log 2 / p.u) (16 / (p.x - p.u) ^ 2)) with hSdef
  have hK₁0 : 0 ≤ K₁ := by
    rw [hK₁def]
    exact div_nonneg (by nlinarith [hpu, huv]) (le_of_lt hvu)
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂def]; positivity
  have hK₃0 : 0 ≤ K₃ := by
    rw [hK₃def]
    exact div_nonneg (by nlinarith [hpu, huv]) (by positivity)
  have hA1 : 0 ≤ K₁ * (p.x + 3) / (p.v - p.u) :=
    div_nonneg (mul_nonneg hK₁0 hpx3) (le_of_lt hvu)
  have hA2 : 0 ≤ K₂ * (p.x + 3) / (p.v - p.u) ^ 2 :=
    div_nonneg (mul_nonneg hK₂0 hpx3) (by positivity)
  refine ⟨K₁ * (p.x + 3) / (p.v - p.u) + K₂ * (p.x + 3) / (p.v - p.u) ^ 2 + K₁ + K₂ + K₃ + 2,
    by linarith, Real.exp S, Real.exp_pos S, ?_⟩
  intro q hq _inst T hT hDthresh N
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hT3 : (3 : ℝ) ≤ T + 2 := by linarith
  have hD6 : 6 ≤ scale q T := by
    rw [scale]
    nlinarith
  have hDpos : 0 < scale q T := by linarith
  have hSle : S ≤ Real.log (scale q T) := by
    have h2 := Real.log_le_log (Real.exp_pos S) hDthresh
    rwa [Real.log_exp] at h2
  have hS1 : 1 ≤ S := by
    rw [hSdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hSvu : 1 / (p.v - p.u) ≤ S := by
    rw [hSdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hSlog : Real.log 2 / p.u ≤ S := by
    rw [hSdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hS16 : 16 / (p.x - p.u) ^ 2 ≤ S := by
    rw [hSdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  set L : ℝ := Lscale q T with hLdef
  set U : ℝ := Dpow q T p.u with hUdef
  set V : ℝ := Dpow q T p.v with hVdef
  set X : ℝ := Dpow q T p.x with hXdef
  set Up : ℝ := U / L ^ 2 with hUpdef
  have hLdef' : L = Real.log (scale q T) := by rw [hLdef, Lscale]
  have hL1 : 1 ≤ L := by rw [hLdef']; exact le_trans hS1 hSle
  have hLpos : 0 < L := by linarith
  have hUexp : U = Real.exp (p.u * L) := by
    have h1 : U = (scale q T) ^ p.u := by rw [hUdef, Dpow]
    rw [h1, Real.rpow_def_of_pos hDpos, hLdef']
    congr 1
    ring
  have hVexp : V = Real.exp (p.v * L) := by
    have h1 : V = (scale q T) ^ p.v := by rw [hVdef, Dpow]
    rw [h1, Real.rpow_def_of_pos hDpos, hLdef']
    congr 1
    ring
  have hXexp : X = Real.exp (p.x * L) := by
    have h1 : X = (scale q T) ^ p.x := by rw [hXdef, Dpow]
    rw [h1, Real.rpow_def_of_pos hDpos, hLdef']
    congr 1
    ring
  have hlogU : Real.log U = p.u * L := by rw [hUexp, Real.log_exp]
  have hlogV : Real.log V = p.v * L := by rw [hVexp, Real.log_exp]
  have hlogX : Real.log X = p.x * L := by rw [hXexp, Real.log_exp]
  have hUpos : 0 < U := by rw [hUexp]; positivity
  have hVpos : 0 < V := by rw [hVexp]; positivity
  have hXpos : 0 < X := by rw [hXexp]; positivity
  have hUV : U < V := by
    rw [hUexp, hVexp]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have hUppos : 0 < Up := by rw [hUpdef]; positivity
  have hlog2L : Real.log 2 ≤ p.u * L := by
    have h2 : Real.log 2 / p.u ≤ L := le_trans hSlog hSle
    calc Real.log 2 = (Real.log 2 / p.u) * p.u := by field_simp
      _ ≤ L * p.u := mul_le_mul_of_nonneg_right h2 (le_of_lt hpu)
      _ = p.u * L := by ring
  have hlog2Lv : Real.log 2 ≤ p.v * L := by nlinarith [hlog2L, hL1, hpu, huv]
  have hU2 : 2 ≤ U := by
    rw [hUexp]
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (p.u * L) := Real.exp_le_exp.mpr hlog2L
  have hV2 : 2 ≤ V := by
    rw [hVexp]
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (p.v * L) := Real.exp_le_exp.mpr hlog2Lv
  have hLamdef : Real.log (V / U) = (p.v - p.u) * L := by
    rw [Real.log_div (ne_of_gt hVpos) (ne_of_gt hUpos), hlogV, hlogU]
    ring
  have hLam1 : 1 ≤ Real.log (V / U) := by
    rw [hLamdef]
    have h2 : 1 / (p.v - p.u) ≤ L := le_trans hSvu hSle
    calc (1 : ℝ) = (1 / (p.v - p.u)) * (p.v - p.u) := by field_simp
      _ ≤ L * (p.v - p.u) := mul_le_mul_of_nonneg_right h2 (le_of_lt hvu)
      _ = (p.v - p.u) * L := by ring
  have hLampos : 0 < Real.log (V / U) := by linarith
  have hUpX : Up ≤ X := by
    have hlogL : Real.log L ≤ 2 * Real.sqrt L := by
      have h := Real.log_le_rpow_div (x := L) (ε := (1 : ℝ) / 2) (le_of_lt hLpos) (by norm_num)
      rw [← Real.sqrt_eq_rpow] at h
      have h' : Real.sqrt L / (1 / 2 : ℝ) = 2 * Real.sqrt L := by ring
      linarith
    have hLbig : 16 / (p.x - p.u) ^ 2 ≤ L := le_trans hS16 hSle
    have hsqrt : 4 / (p.x - p.u) ≤ Real.sqrt L := by
      have h4 : Real.sqrt (16 / (p.x - p.u) ^ 2) ≤ Real.sqrt L := Real.sqrt_le_sqrt hLbig
      have h5 : Real.sqrt (16 / (p.x - p.u) ^ 2) = 4 / (p.x - p.u) := by
        rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 16), Real.sqrt_sq (le_of_lt hxu)]
        norm_num
      rwa [h5] at h4
    have h6 : 4 * Real.sqrt L ≤ (p.x - p.u) * L := by
      have hsqrt4 : 4 ≤ (p.x - p.u) * Real.sqrt L := by
        have h7 := mul_le_mul_of_nonneg_right hsqrt (le_of_lt hxu)
        have h8 : (4 / (p.x - p.u)) * (p.x - p.u) = 4 := by field_simp
        linarith [h7, h8]
      have h9 := mul_le_mul_of_nonneg_right hsqrt4 (Real.sqrt_nonneg L)
      have h10 : Real.sqrt L * Real.sqrt L = L := by
        rw [← sq]
        exact Real.sq_sqrt (le_of_lt hLpos)
      nlinarith [h9, h10]
    have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
    have hlog : Real.log Up ≤ Real.log X := by
      rw [hUpdef, Real.log_div (ne_of_gt hUpos) (by positivity), hlogU, hlogX, Real.log_pow]
      push_cast
      have h99 : p.u * L ≤ p.x * L :=
        mul_le_mul_of_nonneg_right (le_of_lt (lt_trans huv hvx)) (le_of_lt hLpos)
      linarith [hlogL0, h99]
    exact (Real.log_le_log_iff hUppos hXpos).mp hlog
  have hX1 : 1 ≤ X := by
    rw [hXexp]
    exact Real.one_le_exp (by nlinarith [hvx, hpu, hL1])
  obtain ⟨hgf0, hgf1, hgf2⟩ := gfunWeightFacts X Up hUppos hX1 hUpX
  set b : ℕ → ℝ := fun n => (psiSum U V n) ^ 2 with hbdef
  set w : ℕ → ℝ := fun n => gfun X Up n / (n : ℝ) with hwdef
  have hrew : (∑ n ∈ Finset.Icc 1 N,
        (psiSum U V n) ^ 2 * ((n : ℝ))⁻¹ * gfun X Up n)
      = ∑ n ∈ Finset.Icc 1 N, b n * w n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [hbdef, hwdef]
    ring
  rw [hrew]
  have hA : ∀ n : ℕ, (∑ m ∈ Finset.Icc 1 n, b m)
      ≤ (K₁ / Real.log (V / U) + K₂ / (Real.log (V / U)) ^ 2) * (n : ℝ) + K₃ := by
    intro n
    have hident : ∀ m : ℕ, (Work.ZeroDensity.Jutila.Lz V m - Work.ZeroDensity.Jutila.Lz U m)
        = Real.log (V / U) * psiSum U V m := by
      intro m
      rw [psiSum_mul_log U V hUpos hUV m]
    have hstep : (∑ m ∈ Finset.Icc 1 n, b m)
        = (1 / (Real.log (V / U)) ^ 2)
          * (∑ m ∈ Finset.Icc 1 n,
              (Work.ZeroDensity.Jutila.Lz V m - Work.ZeroDensity.Jutila.Lz U m) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [hbdef, hident m]
      field_simp
    rw [hstep]
    have hsq : ∀ m : ℕ, (Work.ZeroDensity.Jutila.Lz V m - Work.ZeroDensity.Jutila.Lz U m) ^ 2
        ≤ 2 * (Work.ZeroDensity.Jutila.Lz V m) ^ 2 + 2 * (Work.ZeroDensity.Jutila.Lz U m) ^ 2 := by
      intro m
      nlinarith [sq_nonneg (Work.ZeroDensity.Jutila.Lz V m + Work.ZeroDensity.Jutila.Lz U m)]
    have hsumsq : (∑ m ∈ Finset.Icc 1 n,
          (Work.ZeroDensity.Jutila.Lz V m - Work.ZeroDensity.Jutila.Lz U m) ^ 2)
        ≤ 2 * (∑ m ∈ Finset.Icc 1 n, (Work.ZeroDensity.Jutila.Lz V m) ^ 2)
          + 2 * (∑ m ∈ Finset.Icc 1 n, (Work.ZeroDensity.Jutila.Lz U m) ^ 2) := by
      calc (∑ m ∈ Finset.Icc 1 n,
            (Work.ZeroDensity.Jutila.Lz V m - Work.ZeroDensity.Jutila.Lz U m) ^ 2)
          ≤ ∑ m ∈ Finset.Icc 1 n, (2 * (Work.ZeroDensity.Jutila.Lz V m) ^ 2
              + 2 * (Work.ZeroDensity.Jutila.Lz U m) ^ 2) := Finset.sum_le_sum (fun m _ => hsq m)
        _ = 2 * (∑ m ∈ Finset.Icc 1 n, (Work.ZeroDensity.Jutila.Lz V m) ^ 2)
              + 2 * (∑ m ∈ Finset.Icc 1 n, (Work.ZeroDensity.Jutila.Lz U m) ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    have hVb := Lz_sq_bound hC hInt V hV2 n
    have hUb := Lz_sq_bound hC hInt U hU2 n
    simp only [hlogV] at hVb
    simp only [hlogU] at hUb
    have hpos2 : 0 < (Real.log (V / U)) ^ 2 := by positivity
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hinner : (∑ m ∈ Finset.Icc 1 n,
          (Work.ZeroDensity.Jutila.Lz V m - Work.ZeroDensity.Jutila.Lz U m) ^ 2)
        ≤ 2 * ((p.v * L) ^ 2 + (n:ℝ) * (p.v * L) + C * (n:ℝ))
          + 2 * ((p.u * L) ^ 2 + (n:ℝ) * (p.u * L) + C * (n:ℝ)) := by
      linarith [hsumsq, hVb, hUb]
    have hmain : (1 / (Real.log (V / U)) ^ 2)
          * (2 * ((p.v * L) ^ 2 + (n:ℝ) * (p.v * L) + C * (n:ℝ))
            + 2 * ((p.u * L) ^ 2 + (n:ℝ) * (p.u * L) + C * (n:ℝ)))
        ≤ (K₁ / Real.log (V / U) + K₂ / (Real.log (V / U)) ^ 2) * (n : ℝ) + K₃ := by
      have h2 : 0 < (Real.log (V / U)) ^ 2 := by positivity
      have hid : 2 * ((p.v * L) ^ 2 + (n:ℝ) * (p.v * L) + C * (n:ℝ))
            + 2 * ((p.u * L) ^ 2 + (n:ℝ) * (p.u * L) + C * (n:ℝ))
          = (Real.log (V / U)) ^ 2
            * ((K₁ / Real.log (V / U) + K₂ / (Real.log (V / U)) ^ 2) * (n : ℝ) + K₃) := by
        rw [hK₁def, hK₂def, hK₃def, hLamdef]
        field_simp
        ring
      have hcancel : (1 / (Real.log (V / U)) ^ 2) * (Real.log (V / U)) ^ 2 = 1 := by
        field_simp
      rw [hid, ← mul_assoc, hcancel, one_mul]
    calc (1 / (Real.log (V / U)) ^ 2) * (∑ m ∈ Finset.Icc 1 n,
            (Work.ZeroDensity.Jutila.Lz V m - Work.ZeroDensity.Jutila.Lz U m) ^ 2)
        ≤ (1 / (Real.log (V / U)) ^ 2)
            * (2 * ((p.v * L) ^ 2 + (n:ℝ) * (p.v * L) + C * (n:ℝ))
              + 2 * ((p.u * L) ^ 2 + (n:ℝ) * (p.u * L) + C * (n:ℝ))) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ ≤ (K₁ / Real.log (V / U) + K₂ / (Real.log (V / U)) ^ 2) * (n : ℝ) + K₃ := hmain
  have hw0 : ∀ n : ℕ, 0 ≤ w n := by
    intro n
    rw [hwdef]
    have := hgf0 n
    positivity
  have hwmono : ∀ n : ℕ, 1 ≤ n → w (n + 1) ≤ w n := by
    intro n hn
    rw [hwdef]
    simpa only [Nat.cast_add, Nat.cast_one] using hgf1 n hn
  have hw1 : w 1 ≤ 1 := by
    have h1 : gfun X Up 1 ≤ 1 := by
      rw [gfun]
      show Real.exp (-(((1:ℕ):ℝ)/X)) - Real.exp (-(((1:ℕ):ℝ)/Up)) ≤ 1
      have hpos : (0:ℝ) ≤ Real.exp (-(((1:ℕ):ℝ)/Up)) := Real.exp_nonneg _
      have hle : Real.exp (-(((1:ℕ):ℝ)/X)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (le_of_lt (div_pos (by norm_num : (0:ℝ) < (((1:ℕ):ℝ))) hXpos))
      linarith [hpos, hle]
    rw [hwdef]
    simp only [Nat.cast_one, div_one]
    exact h1
  have habel := abel_partial (b := b) (w := w)
    (K := K₁ / Real.log (V / U) + K₂ / (Real.log (V / U)) ^ 2) (M := K₃)
    (by positivity) hK₃0 hw0 hwmono hA N
  have hlog2X : Real.log (2 * X) = Real.log 2 + p.x * L := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hXpos), hlogX]
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hsumw : (∑ n ∈ Finset.Icc 1 N, w n) ≤ (p.x + 3) * L := by
    have hsumw' : (∑ n ∈ Finset.Icc 1 N, w n) = ∑ n ∈ Finset.Icc 1 N, gfun X Up n / (n : ℝ) :=
      Finset.sum_congr rfl (fun n _ => by rw [hwdef])
    rw [hsumw']
    refine le_trans (hgf2 N) ?_
    rw [hlog2X]
    nlinarith [hL1, hlog2le, hvx, hpu]
  have hKb : K₁ / Real.log (V / U) + K₂ / (Real.log (V / U)) ^ 2 ≤ K₁ + K₂ := by
    have h1 : K₁ / Real.log (V / U) ≤ K₁ := by
      rw [div_le_iff₀ hLampos]; nlinarith [hK₁0, hLam1]
    have h2 : K₂ / (Real.log (V / U)) ^ 2 ≤ K₂ := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 ≤ (Real.log (V / U)) ^ 2 := by nlinarith [hLam1]
      nlinarith [hK₂0, this]
    linarith
  have hfinal : (K₁ / Real.log (V / U) + K₂ / (Real.log (V / U)) ^ 2)
        * (∑ n ∈ Finset.Icc 1 N, w n)
      + (K₁ / Real.log (V / U) + K₂ / (Real.log (V / U)) ^ 2 + K₃) * w 1
      ≤ K₁ * (p.x + 3) / (p.v - p.u) + K₂ * (p.x + 3) / (p.v - p.u) ^ 2 + K₁ + K₂ + K₃ + 2 := by
    have h1 : (K₁ / Real.log (V / U) + K₂ / (Real.log (V / U)) ^ 2)
          * (∑ n ∈ Finset.Icc 1 N, w n)
        ≤ (K₁ / Real.log (V / U) + K₂ / (Real.log (V / U)) ^ 2) * ((p.x + 3) * L) :=
      mul_le_mul_of_nonneg_left hsumw (by positivity)
    have h2 : (K₁ / Real.log (V / U) + K₂ / (Real.log (V / U)) ^ 2 + K₃) * w 1
        ≤ (K₁ + K₂ + K₃) := by
      have h3 : K₁ / Real.log (V / U) + K₂ / (Real.log (V / U)) ^ 2 + K₃ ≤ K₁ + K₂ + K₃ := by
        linarith [hKb]
      calc (K₁ / Real.log (V / U) + K₂ / (Real.log (V / U)) ^ 2 + K₃) * w 1
          ≤ (K₁ + K₂ + K₃) * w 1 := mul_le_mul_of_nonneg_right h3 (hw0 1)
        _ ≤ (K₁ + K₂ + K₃) * 1 := mul_le_mul_of_nonneg_left hw1 (by linarith [hK₁0, hK₂0, hK₃0])
        _ = K₁ + K₂ + K₃ := by ring
    have h3 : (K₁ / Real.log (V / U) + K₂ / (Real.log (V / U)) ^ 2) * ((p.x + 3) * L)
        ≤ K₁ * (p.x + 3) / (p.v - p.u) + K₂ * (p.x + 3) / (p.v - p.u) ^ 2 := by
      rw [add_mul]
      have e1 : K₁ / Real.log (V / U) * ((p.x + 3) * L) = K₁ * (p.x + 3) / (p.v - p.u) := by
        rw [hLamdef]
        field_simp
      have e2 : K₂ / (Real.log (V / U)) ^ 2 * ((p.x + 3) * L)
          ≤ K₂ * (p.x + 3) / (p.v - p.u) ^ 2 := by
        rw [hLamdef]
        have hden : 0 < (p.v - p.u) ^ 2 := by positivity
        calc K₂ / ((p.v - p.u) * L) ^ 2 * ((p.x + 3) * L)
            = K₂ * (p.x + 3) / ((p.v - p.u) ^ 2 * L) := by
              field_simp
          _ ≤ K₂ * (p.x + 3) / (p.v - p.u) ^ 2 :=
              div_le_div_of_nonneg_left (by positivity) hden (by nlinarith [hL1, hvu])
      linarith [e1, e2]
    linarith [h1, h2, h3]

  linarith [habel, hfinal]


end

end Work.ZeroDensity.LogFree
