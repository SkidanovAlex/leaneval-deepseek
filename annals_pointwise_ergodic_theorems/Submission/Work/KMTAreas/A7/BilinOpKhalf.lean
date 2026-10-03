/-
# The halved average as a bilinear convolution operator (`bilinOp_khalf`)

This module identifies the halved (upper half) bilinear average `Ã_m = Ahalf T_ℤ m X P`
with the bilinear convolution operator `bilinOp (khalf m P)` whose kernel is the *finite*
kernel `khalf m P` supported on the integer interval `(⌊m/2⌋, m] × {P(a)}`:

  `bilinOp_khalf : Ahalf T_ℤ m X P u v = bilinOp (khalf m P) u v`.

The statement `BilinOpKhalf` is the real-scale form `AhalfR T_ℤ N X P u v =
bilinOp (khalf ⌊N⌋ P) u v` used by the §7 small-scale analysis.

The proof is a computation: for each `a` the inner `tsum` over `b` collapses to the single
term `b = P.eval a` (`tsum_eq_single`), and the outer `tsum` over `a` is the finite sum over
the integers in `(⌊m/2⌋, m]`, which are exactly the casts of the naturals `n ∈ Ioc (m/2) m`
(`tsum_eq_sum` along the embedding `ℕ ↪ ℤ`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems

/-- The block sum of the upper half average for the integer shift `T_ℤ(n) = n - 1`:
`Ablock T_ℤ m P₁ P₂ f g x = ∑_{m/2 < n ≤ m} f (x - P₁(n)) * g (x - P₂(n))`. -/
lemma Ablock_TZ (m : ℕ) (P₁ P₂ : ℤ[X]) (f g : ℤ → ℂ) (x : ℤ) :
    Ablock TZ m P₁ P₂ f g x
      = ∑ n ∈ Finset.Ioc (m / 2) m, f (x - P₁.eval (n : ℤ)) * g (x - P₂.eval (n : ℤ)) := by
  rw [Ablock]
  exact Finset.sum_congr rfl (fun n _ => by rw [TZ_zpow, TZ_zpow])

/-- For fixed `a`, the inner sum over `b` in `bilinOp (khalf m P)` collapses to the single
term `b = P.eval a`. -/
lemma tsum_khalf_inner (m : ℕ) (P : ℤ[X]) (u v : ℤ → ℂ) (x a : ℤ) :
    (∑' b : ℤ, khalf m P a b * u (x - a) * v (x - b))
      = khalf m P a (P.eval a) * u (x - a) * v (x - P.eval a) := by
  rw [tsum_eq_single (P.eval a)]
  intro b hb
  simp [khalf, hb]

/-- The outer sum in `bilinOp (khalf m P)` is the finite sum over the integers `a` with
`m/2 < a ≤ m`, i.e. the casts of the naturals `n ∈ Ioc (m/2) m`. -/
lemma tsum_khalf_outer (m : ℕ) (P : ℤ[X]) (u v : ℤ → ℂ) (x : ℤ) :
    (∑' a : ℤ, khalf m P a (P.eval a) * u (x - a) * v (x - P.eval a))
      = ∑ n ∈ Finset.Ioc (m / 2) m,
          khalf m P (n : ℤ) (P.eval (n : ℤ)) * u (x - (n : ℤ)) * v (x - P.eval (n : ℤ)) := by
  rw [tsum_eq_sum (s := (Finset.Ioc (m / 2) m).map ⟨(↑· : ℕ → ℤ), Nat.cast_injective⟩)]
  · rw [Finset.sum_map]
    exact Finset.sum_congr rfl (fun n _ => rfl)
  · intro a ha
    by_cases h : (↑m : ℤ) / 2 < a ∧ a ≤ (↑m : ℤ)
    · exfalso
      apply ha
      refine Finset.mem_map.mpr ⟨a.toNat, ?_, ?_⟩
      · rw [Finset.mem_Ioc, Int.lt_toNat, Int.natCast_div, Int.toNat_le]
        exact h
      · have h0 : (0 : ℤ) ≤ a :=
          le_of_lt (lt_of_le_of_lt (Int.ediv_nonneg (Int.natCast_nonneg m) (by norm_num)) h.1)
        exact Int.toNat_of_nonneg h0
    · simp only [khalf]
      rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]
      ring

/-- The halved average at the integer scale `m` is the bilinear convolution operator with the
finite kernel `khalf m P`. -/
theorem bilinOp_khalf (m : ℕ) (P : ℤ[X]) (u v : ℤ → ℂ) :
    Ahalf TZ m X P u v = bilinOp (khalf m P) u v := by
  funext x
  have hcoef : (↑((m : ℝ)⁻¹) : ℂ) = ((m : ℂ))⁻¹ := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [bilinOp]
  simp_rw [tsum_khalf_inner]
  rw [tsum_khalf_outer, Ahalf, Ablock_TZ]
  simp only [Polynomial.eval_X]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn' : m / 2 < n ∧ n ≤ m := Finset.mem_Ioc.mp hn
  have hk : khalf m P (n : ℤ) (P.eval (n : ℤ)) = ((m : ℂ))⁻¹ := by
    have hc : (↑m : ℤ) / 2 < (↑n : ℤ) ∧ (↑n : ℤ) ≤ (↑m : ℤ)
        ∧ P.eval (↑n) = P.eval (↑n) := by
      refine ⟨?_, ?_, rfl⟩
      · have h1 : (↑m : ℤ) / 2 = ((m / 2 : ℕ) : ℤ) := by
          rw [eq_comm, Int.natCast_div]; norm_num
        rw [h1]; exact_mod_cast hn'.1
      · exact_mod_cast hn'.2
    rw [khalf, if_pos hc]
  rw [hcoef, hk]
  ring

/-- The real-scale form of `bilinOp_khalf`: the halved average at the real scale `N` is the
bilinear convolution operator with the finite kernel `khalf ⌊N⌋ P`. -/
theorem BilinOpKhalf (N : NNReal) (P : Polynomial ℤ) (u v : ℤ → ℂ) :
    Submission.PointwiseErgodicTheorems.AhalfR Submission.PointwiseErgodicTheorems.TZ N Polynomial.X P u v
      = Work.KMTAreas.A7.bilinOp (Work.KMTAreas.A7.khalf (Nat.floor N) P) u v := by
  exact bilinOp_khalf (Nat.floor N) P u v

end

end Work.KMTAreas.A7
