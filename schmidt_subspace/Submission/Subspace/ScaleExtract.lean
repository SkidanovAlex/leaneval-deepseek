import Mathlib
import Submission.Subspace.GapPrinciple

/-!
# Extraction of the scales with gaps

The maximal-rank case of the subspace theorem (`Theorem C`) is proved by contradiction:
if there were "too many" hyperplanes `V(Q) = approxSpace L γ Q` (`Q` large), one extracts
scales `Q_0 > Q_1 > … > Q_{m-1}` with

* consecutive hyperplanes `V(Q_h)` **distinct**, and
* a *huge* multiplicative gap `Q_h ≥ Q_{h+1} ^ R`.

The gap comes from the gap principle `Submission.Subspace.approxSpace_le_of_gap`: if
`Q ≤ Q' ≤ Q ^ (1 + ε/2)` then `V(Q') ≤ V(Q)`, so distinct hyperplanes force
`Q' > Q ^ (1 + ε/2)` once one of them has dimension `N - 1`.

This file contains the purely order-theoretic part of that extraction.
-/

open scoped BigOperators

namespace Submission.Subspace

/-- Iterating a "shrinking" supermultiplicative condition: if `T (n+1) ^ c ≤ T n` for all `n`
with `c ≥ 1` and `T ≥ 1`, then `T (n+k) ^ (c^k) ≤ T n`. -/
lemma rpow_iter_le (T : ℕ → ℝ) (c : ℝ) (hc : 1 ≤ c) (hT : ∀ n, 1 ≤ T n)
    (hstep : ∀ n, (T (n + 1)) ^ c ≤ T n) : ∀ (n k : ℕ), (T (n + k)) ^ (c ^ k) ≤ T n := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hT0 : ∀ n, (0 : ℝ) < T n := fun n => lt_of_lt_of_le zero_lt_one (hT n)
  have key : ∀ k : ℕ, ∀ n : ℕ, (T (n + k)) ^ (c ^ k) ≤ T n := by
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      have h1 : (T (n + (k + 1))) ^ (c ^ (k + 1)) = ((T (n + (k + 1))) ^ (c ^ k)) ^ c := by
        rw [pow_succ, Real.rpow_mul (le_of_lt (hT0 _))]
      rw [h1]
      have h2 : (T (n + (k + 1))) ^ (c ^ k) ≤ T (n + 1) := by
        have h := ih (n + 1)
        rwa [show n + 1 + k = n + (k + 1) from by omega] at h
      exact le_trans (Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt (hT0 _)) _) h2 hc0)
        (hstep n)
  exact fun n k => key k n

/-- Sorting a finite set of reals: there is a strictly increasing enumeration of it. -/
lemma exists_strictMono_fin_finset (F : Finset ℝ) :
    ∃ g : Fin F.card → ℝ, StrictMono g ∧ ∀ j, g j ∈ F :=
  ⟨fun j => ((F.orderIsoOfFin rfl) j : ℝ),
    fun _ _ hij => (F.orderIsoOfFin rfl).strictMono hij,
    fun j => ((F.orderIsoOfFin rfl) j).2⟩

/-- The iteration of the gap step along a finite chain. -/
lemma fin_rpow_iter {Lc : ℕ} (f : Fin Lc → ℝ) (c : ℝ) (hc : 1 ≤ c) (hpos : ∀ j, 0 < f j)
    (hstep : ∀ a b : Fin Lc, a < b → (f a) ^ c ≤ f b) :
    ∀ (a k : ℕ) (ha : a + k < Lc), (f ⟨a, by omega⟩) ^ (c ^ k) ≤ f ⟨a + k, ha⟩ := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  intro a k
  induction k with
  | zero =>
    intro ha
    have heq : (⟨a, by omega⟩ : Fin Lc) = ⟨a + 0, ha⟩ := Fin.ext (by simp)
    rw [heq]
    simp
  | succ k ih =>
    intro ha
    have ha' : a + k < Lc := by omega
    have h1 : (f ⟨a + k, ha'⟩) ^ c ≤ f ⟨a + (k + 1), ha⟩ := by
      have hlt : (⟨a + k, ha'⟩ : Fin Lc) < ⟨a + (k + 1), ha⟩ := by
        rw [Fin.lt_def]; simp
      exact hstep _ _ hlt
    calc (f ⟨a, by omega⟩) ^ (c ^ (k + 1))
        = ((f ⟨a, by omega⟩) ^ (c ^ k)) ^ c := by
          rw [pow_succ, Real.rpow_mul (le_of_lt (hpos _))]
      _ ≤ (f ⟨a + k, ha'⟩) ^ c :=
          Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt (hpos _)) _) (ih ha') hc0
      _ ≤ f ⟨a + (k + 1), ha⟩ := h1

/-- **Extraction of the scales with gaps.**  Let `f` be a strictly increasing chain of `Lc`
scales whose hyperplanes `V(f j)` are pairwise distinct and have dimension `N - 1`, with
`Lc = 1 + (m-1)·t`.  Then one can pick `m` of them,
`Q h := f ((m-1-h)·t)`, with the multiplicative gaps
`(Q j) ^ ((1+ε/2) ^ (t·(j-i))) ≤ Q i` for `i ≤ j`. -/
theorem exists_gap_scales {N : ℕ} (hN : 2 ≤ N)
    (L : Matrix (Fin N) (Fin N) ℂ) (hL : L.det ≠ 0)
    (γ : Fin N → ℝ) (hγ1 : ∀ i, γ i ≤ 1) (ε : ℝ) (hε : 0 < ε) (hsum : ∑ i, γ i ≤ -ε)
    (Q₀ : ℝ) (hQ₀ : 1 ≤ Q₀)
    (hbig : (Nat.factorial N : ℝ) < ‖L.det‖ * Q₀ ^ (ε / 2))
    {m t Lc : ℕ} (hLc : Lc = 1 + (m - 1) * t) (f : Fin Lc → ℝ)
    (hf₀ : ∀ j, Q₀ ≤ f j) (hfmono : StrictMono f)
    (hfrank : ∀ j, Module.finrank ℚ (approxSpace L γ (f j)) = N - 1)
    (hfinj : ∀ j k, j ≠ k → approxSpace L γ (f j) ≠ approxSpace L γ (f k)) :
    ∃ Q : Fin m → ℝ, (∀ h, Q₀ ≤ Q h) ∧
      (∀ i j : Fin m, i ≤ j → (Q j) ^ ((1 + ε / 2) ^ (t * ((j : ℕ) - (i : ℕ)))) ≤ Q i) := by
  have hc1 : 1 ≤ 1 + ε / 2 := by linarith
  -- the elementary gap step: for `a < b` in the chain, `f a ^ (1+ε/2) ≤ f b`
  have hstep : ∀ a b : Fin Lc, a < b → (f a) ^ (1 + ε / 2) ≤ f b := by
    intro a b hab
    by_contra hcon
    push Not at hcon
    have hle : f a ≤ f b := le_of_lt (hfmono hab)
    have hbig' : (Nat.factorial N : ℝ) < ‖L.det‖ * (f a) ^ (ε / 2) := by
      have h1 : Q₀ ^ (ε / 2) ≤ (f a) ^ (ε / 2) :=
        Real.rpow_le_rpow (le_trans zero_le_one hQ₀) (hf₀ a) (by linarith)
      have h2 : (0 : ℝ) ≤ ‖L.det‖ := norm_nonneg _
      have := mul_le_mul_of_nonneg_left h1 h2
      linarith [hbig, this]
    have hle' : approxSpace L γ (f b) ≤ approxSpace L γ (f a) :=
      approxSpace_le_of_gap hN L hL γ hγ1 ε hε hsum (f a) (f b)
        (le_trans hQ₀ (hf₀ a)) hle (le_of_lt hcon) hbig' (hfrank a)
    have heq : approxSpace L γ (f b) = approxSpace L γ (f a) :=
      Submodule.eq_of_le_of_finrank_eq hle' (by rw [hfrank b, hfrank a])
    exact hfinj b a hab.ne' heq
  have hpos : ∀ j, 0 < f j := fun j => lt_of_lt_of_le zero_lt_one (le_trans hQ₀ (hf₀ j))
  refine ⟨fun h => f ⟨(m - 1 - (h : ℕ)) * t, ?_⟩, fun h => hf₀ _, ?_⟩
  · have h1 : (h : ℕ) ≤ m - 1 := by have := h.isLt; omega
    have h2 : (m - 1 - (h : ℕ)) * t ≤ (m - 1) * t := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega
  · intro i j hij
    have hij' : (i : ℕ) ≤ (j : ℕ) := hij
    have hsub : (m - 1 - (j : ℕ)) * t + t * ((j : ℕ) - (i : ℕ)) = (m - 1 - (i : ℕ)) * t := by
      have hkey : (m - 1 - (j : ℕ)) + ((j : ℕ) - (i : ℕ)) = (m - 1 - (i : ℕ)) := by
        have hj : (j : ℕ) ≤ m - 1 := by have := j.isLt; omega
        omega
      rw [Nat.mul_comm (m - 1 - (j : ℕ)) t, ← Nat.mul_add, hkey, Nat.mul_comm t]
    have hlt : (m - 1 - (j : ℕ)) * t + t * ((j : ℕ) - (i : ℕ)) < Lc := by
      rw [hsub]
      have hi : (i : ℕ) ≤ m - 1 := by have := i.isLt; omega
      have hle : (m - 1 - (i : ℕ)) * t ≤ (m - 1) * t := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      omega
    have hinst := fin_rpow_iter f (1 + ε / 2) hc1 hpos hstep ((m - 1 - (j : ℕ)) * t)
      (t * ((j : ℕ) - (i : ℕ))) hlt
    have hidx : f ⟨(m - 1 - (j : ℕ)) * t + t * ((j : ℕ) - (i : ℕ)), hlt⟩
        = f ⟨(m - 1 - (i : ℕ)) * t, by omega⟩ := by
      congr 1
      exact Fin.ext hsub
    rw [hidx] at hinst
    exact hinst

end Submission.Subspace
