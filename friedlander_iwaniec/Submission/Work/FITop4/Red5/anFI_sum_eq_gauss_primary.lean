import Mathlib
import Submission.Work.FITop4.Red5.anFI_sum_eq_gauss
import Submission.Work.FITop4.Red5.primary_reduction

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `Work.FITop4.Red5.anFI_sum_eq_gauss_primary`

The primary form of the paper's (5.2): the weighted sum `∑_{1 ≤ n ≤ 2N, (m,n)=1} g(n) a_{mn}`
equals the Gaussian double sum over `|w|² = m` and over *primary* `z` with `1 ≤ |z|² ≤ 2N`:

  `∑_{1 ≤ n ≤ 2N, (m,n)=1} g(n) a_{mn}
     = ∑_{|w|² = m} ∑_{1 ≤ |z|² ≤ 2N, z primary, (m,|z|²)=1} g(|z|²) Z(Re wz)`

(the factor `1/4` of `anFI_sum_eq_gauss` cancels against the factor `4` of the primary
reduction `primary_reduction`).  The hypothesis `hodd` says `g` vanishes on the even integers,
which is what allows the reduction to be applied fibre by fibre (a primary element has odd norm).
-/

/-- A sum `∑ x ∈ s, (if P then a * h x else 0)` in which `P` and `a` do not depend on `x`. -/
lemma sum_ite_mul_const {ι : Type*} (s : Finset ι) (P : Prop) [Decidable P]
    (a : ℝ) (h : ι → ℝ) :
    (∑ x ∈ s, (if P then a * h x else 0)) = if P then a * ∑ x ∈ s, h x else 0 := by
  by_cases hP : P
  · simp only [if_pos hP]
    rw [Finset.mul_sum]
  · simp only [if_neg hP, Finset.sum_const_zero]

/-- The fibre over `|z|² = n` of the primary part of the annulus `1 ≤ |z|² ≤ R` is the primary
sphere `sphPrim n` (`1 ≤ n ≤ R`). -/
lemma filter_gnorm_eq_primary {R n : ℕ} (hn1 : 1 ≤ n) (hnR : n ≤ R) :
    ((((Work.FIPlan.gBox ((R : ℕ) : ℤ)).filter
        (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ R)).filter
        (fun z => Work.FIPlan.IsPrimary z)).filter
        (fun z => Work.FIPlan.gnorm z = n))
      = sphPrim n := by
  have h1 : ((((Work.FIPlan.gBox ((R : ℕ) : ℤ)).filter
        (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ R)).filter
        (fun z => Work.FIPlan.IsPrimary z)).filter
        (fun z => Work.FIPlan.gnorm z = n))
      = (((Work.FIPlan.gBox ((R : ℕ) : ℤ)).filter
        (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ R)).filter
        (fun z => Work.FIPlan.gnorm z = n)).filter (fun z => Work.FIPlan.IsPrimary z) :=
    Finset.filter_comm _ _ _
  have h2 : sphPrim n = (((Work.FIPlan.gBox ((R : ℕ) : ℤ)).filter
        (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ R)).filter
        (fun z => Work.FIPlan.gnorm z = n)).filter (fun z => Work.FIPlan.IsPrimary z) := by
    simp only [sphPrim, sph]
    rw [filter_gnorm_eq hn1 hnR]
  rw [h1, h2]

/-- **Fiber decomposition of the weighted primary `z`-sum** (primary analogue of `inner_sum_eq`):
collecting the primary Gaussian integers of the annulus `1 ≤ |z|² ≤ R` of the box `gBox R` by the
value `n = |z|²` turns the sum into the sum over `n ∈ [1, R]` of the sum over `sphPrim n`. -/
lemma inner_sum_eq_primary (m R : ℕ) (hR : 1 ≤ R) (g : ℕ → ℝ) (w : GaussianInt) :
    (∑ z ∈ (((Work.FIPlan.gBox ((R : ℕ) : ℤ)).filter
            (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ R)).filter
            (fun z => Work.FIPlan.IsPrimary z)),
        (if Nat.Coprime m (Work.FIPlan.gnorm z) then
          g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0))
      = ∑ n ∈ Finset.Icc 1 R,
          (if Nat.Coprime m n then g n *
            (∑ z ∈ sphPrim n, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) else 0) := by
  have hmap : ∀ z ∈ (((Work.FIPlan.gBox ((R : ℕ) : ℤ)).filter
        (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ R)).filter
        (fun z => Work.FIPlan.IsPrimary z)),
      Work.FIPlan.gnorm z ∈ Finset.Icc 1 R := by
    intro z hz
    simp only [Finset.mem_filter] at hz
    exact Finset.mem_Icc.mpr ⟨hz.1.2.1, hz.1.2.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun z => (if Nat.Coprime m (Work.FIPlan.gnorm z) then
      g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn1, hnR⟩ := Finset.mem_Icc.mp hn
  rw [filter_gnorm_eq_primary hn1 hnR]
  have h2 : ∀ z ∈ sphPrim n,
      (if Nat.Coprime m (Work.FIPlan.gnorm z) then
        g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0)
        = (if Nat.Coprime m n then
            g n * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0) := by
    intro z hz
    simp only [sphPrim, sph, Finset.mem_filter] at hz
    rw [hz.1.2]
  rw [Finset.sum_congr rfl h2]
  by_cases hc : Nat.Coprime m n
  · simp only [if_pos hc, Finset.mul_sum]
  · simp only [if_neg hc, Finset.sum_const_zero]

/-- The sphere sum is four times its primary part (the paper's primary reduction, with the
trivial coefficient `F ≡ 1`). -/
lemma sum_sph_eq_four_sphPrim (m n : ℕ) (hm : 1 ≤ m) (hn : Odd n) :
    (∑ w ∈ sph m, ∑ z ∈ sph n, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      = 4 * (∑ w ∈ sph m, ∑ z ∈ sphPrim n,
          (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) := by
  have h := primary_reduction m n (fun _ => 1) hm hn
  simpa only [sph, sphPrim, one_mul] using h

/-- The `n`-th contribution of the full double sum equals `4` times that of the primary double
sum: for odd `n` this is the primary reduction, and for even `n` both sides vanish because
`g n = 0`. -/
lemma term_eq (m n : ℕ) (g : ℕ → ℝ) (hm : 1 ≤ m) (hodd : ∀ n, ¬ Odd n → g n = 0) :
    (if Nat.Coprime m n then g n * (∑ w ∈ sph m, ∑ z ∈ sph n,
        (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) else 0)
      = 4 * (if Nat.Coprime m n then g n * (∑ w ∈ sph m, ∑ z ∈ sphPrim n,
        (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) else 0) := by
  by_cases hpar : Odd n
  · have h4 := sum_sph_eq_four_sphPrim m n hm hpar
    by_cases hc : Nat.Coprime m n
    · rw [if_pos hc, if_pos hc, h4]; ring
    · rw [if_neg hc, if_neg hc]; ring
  · have hgn : g n = 0 := hodd n hpar
    by_cases hc : Nat.Coprime m n <;> simp [hc, hgn]

/-- **The full double sum is four times the primary double sum.** -/
lemma full_eq_four_prim (m N : ℕ) (g : ℕ → ℝ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hodd : ∀ n, ¬ Odd n → g n = 0) :
    (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m),
        ∑ z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
            (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ 2 * N),
          (if Nat.Coprime m (Work.FIPlan.gnorm z) then
            g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0))
      = 4 * (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m),
          ∑ z ∈ ((Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
              (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ 2 * N)).filter
              (fun z => Work.FIPlan.IsPrimary z),
            (if Nat.Coprime m (Work.FIPlan.gnorm z) then
              g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0)) := by
  have hR : 1 ≤ 2 * N := by omega
  have key : (∑ w ∈ sph m, ∑ z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
            (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ 2 * N),
          (if Nat.Coprime m (Work.FIPlan.gnorm z) then
            g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0))
      = 4 * (∑ w ∈ sph m, ∑ z ∈ ((Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
              (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ 2 * N)).filter
              (fun z => Work.FIPlan.IsPrimary z),
          (if Nat.Coprime m (Work.FIPlan.gnorm z) then
            g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0)) := by
    calc
      (∑ w ∈ sph m, ∑ z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
            (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ 2 * N),
          (if Nat.Coprime m (Work.FIPlan.gnorm z) then
            g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0))
        = ∑ w ∈ sph m, ∑ n ∈ Finset.Icc 1 (2 * N),
            (if Nat.Coprime m n then g n *
              (∑ z ∈ sph n, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) else 0) := by
            apply Finset.sum_congr rfl
            intro w _
            exact inner_sum_eq m (2 * N) hR g w
      _ = ∑ n ∈ Finset.Icc 1 (2 * N), ∑ w ∈ sph m,
            (if Nat.Coprime m n then g n *
              (∑ z ∈ sph n, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) else 0) :=
            Finset.sum_comm
      _ = ∑ n ∈ Finset.Icc 1 (2 * N),
            (if Nat.Coprime m n then g n *
              (∑ w ∈ sph m, ∑ z ∈ sph n,
                (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) else 0) := by
            apply Finset.sum_congr rfl
            intro n _
            exact sum_ite_mul_const (sph m) (Nat.Coprime m n) (g n)
              (fun w => ∑ z ∈ sph n, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      _ = ∑ n ∈ Finset.Icc 1 (2 * N),
            4 * (if Nat.Coprime m n then g n *
              (∑ w ∈ sph m, ∑ z ∈ sphPrim n,
                (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) else 0) := by
            apply Finset.sum_congr rfl
            intro n _
            exact term_eq m n g hm hodd
      _ = 4 * (∑ n ∈ Finset.Icc 1 (2 * N),
            (if Nat.Coprime m n then g n *
              (∑ w ∈ sph m, ∑ z ∈ sphPrim n,
                (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) else 0)) := by
            rw [Finset.mul_sum]
      _ = 4 * (∑ w ∈ sph m, ∑ z ∈ ((Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
              (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ 2 * N)).filter
              (fun z => Work.FIPlan.IsPrimary z),
          (if Nat.Coprime m (Work.FIPlan.gnorm z) then
            g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0)) := by
            congr 1
            rw [show (∑ w ∈ sph m, ∑ z ∈ ((Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
                    (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ 2 * N)).filter
                    (fun z => Work.FIPlan.IsPrimary z),
                    (if Nat.Coprime m (Work.FIPlan.gnorm z) then
                      g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
                      else 0))
                = ∑ w ∈ sph m, ∑ n ∈ Finset.Icc 1 (2 * N),
                    (if Nat.Coprime m n then g n *
                      (∑ z ∈ sphPrim n,
                        (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) else 0) from by
                  apply Finset.sum_congr rfl
                  intro w _
                  exact inner_sum_eq_primary m (2 * N) hR g w]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro n _
            symm
            exact sum_ite_mul_const (sph m) (Nat.Coprime m n) (g n)
              (fun w => ∑ z ∈ sphPrim n, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
  simpa only [sph] using key

theorem anFI_sum_eq_gauss_primary (m N : ℕ) (g : ℕ → ℝ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hodd : ∀ n, ¬ Odd n → g n = 0) :
    (∑ n ∈ Finset.Icc 1 (2 * N),
        (if Nat.Coprime m n then g n * (Work.FIPlan.anFI (m * n) : ℝ) else 0))
      = ∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m),
          ∑ z ∈ ((Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
                  (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ 2 * N)).filter
                (fun z => Work.FIPlan.IsPrimary z),
            (if Nat.Coprime m (Work.FIPlan.gnorm z) then
              g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0) := by
  classical
  have hfull := full_eq_four_prim m N g hm hN hodd
  have hgauss := anFI_sum_eq_gauss m N hm hN g
  rw [hgauss, hfull]
  ring

end

end Work.FITop4.Red5
