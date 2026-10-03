import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop4.Red4.anFI_eq_four_gauss

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `Work.FITop4.Red5.anFI_sum_eq_gauss`

The paper's (5.2) summed against a weight `g` supported on the integers `n ≤ 2N` coprime to `m`:

  `∑_{1 ≤ n ≤ 2N, (m,n)=1} g(n) a_{mn} = ¼ ∑_{|w|² = m} ∑_{1 ≤ |z|² ≤ 2N, (m,|z|²)=1} g(|z|²) Z(Re wz)`,

which is the form of the Gaussian identity that the §5 bilinear forms consume.  It is a direct
consequence of `anFI_eq_four_gauss` (`a_{mn} = ¼ ∑_{|w|²=m} ∑_{|z|²=n} Z(Re wz)` for `(m,n)=1`)
after collecting the inner `z`-sum by the value of `|z|²`.

The only lattice input needed is that the box truncation `gBox (2N)` cuts out the same Gaussian
integers of norm `n` as `gBox n` does (`1 ≤ n ≤ 2N`).
-/

/-- `gnorm z = n` in coordinates. -/
lemma gnorm_eq_iff (z : GaussianInt) (n : ℕ) :
    Work.FIPlan.gnorm z = n ↔ z.re ^ 2 + z.im ^ 2 = (n : ℤ) := by
  rw [Work.FIPlan.gnorm]
  exact Commons.NumberTheory.GaussianInt.norm_natAbs_eq_iff z n

/-- Membership in the box `gBox R` is the coordinate-wise box condition. -/
lemma mem_gBox_iff {R : ℤ} {w : GaussianInt} :
    w ∈ Work.FIPlan.gBox R ↔ w.re ∈ Finset.Icc (-R) R ∧ w.im ∈ Finset.Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(w.re, w.im), Finset.mem_product.mpr ⟨h1, h2⟩, Zsqrtd.ext (by simp) (by simp)⟩

/-- The coordinates of `z` in terms of `gnorm`. -/
lemma natAbs_gnorm (z : GaussianInt) (n : ℕ) (hz : Work.FIPlan.gnorm z = n) :
    z.re.natAbs ^ 2 + z.im.natAbs ^ 2 = n := by
  have h1 : z.re ^ 2 + z.im ^ 2 = (n : ℤ) := (gnorm_eq_iff z n).mp hz
  have h2 : (z.re ^ 2 + z.im ^ 2).natAbs = n := by
    rw [h1]; simp
  rw [Int.natAbs_add_of_nonneg (by positivity) (by positivity), Int.natAbs_pow,
    Int.natAbs_pow] at h2
  exact h2

/-- Every Gaussian integer of norm `n` has coordinates bounded by `n` in absolute value. -/
lemma natAbs_coords_le_of_gnorm {z : GaussianInt} {n : ℕ}
    (hz : Work.FIPlan.gnorm z = n) : z.re.natAbs ≤ n ∧ z.im.natAbs ≤ n := by
  have hco : z.re.natAbs ^ 2 + z.im.natAbs ^ 2 = n := natAbs_gnorm z n hz
  rw [pow_two, pow_two] at hco
  have key : ∀ a : ℕ, a * a ≤ n → a ≤ n := fun a ha =>
    Nat.mul_self_le_mul_self_iff.mp (ha.trans (Nat.le_mul_self n))
  exact ⟨key _ (by omega), key _ (by omega)⟩

/-- For `1 ≤ n ≤ R` the box `gBox R` and the box `gBox n` cut out the *same* Gaussian integers
of norm `n` (the box condition follows from the norm condition, and conversely is weaker). -/
lemma gBox_filter_gnorm_eq {n R : ℕ} (_hn : 1 ≤ n) (hR : n ≤ R) :
    (Work.FIPlan.gBox ((R : ℕ) : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n)
      = (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n) := by
  ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨_, hgn⟩
    refine ⟨?_, hgn⟩
    obtain ⟨h1, h2⟩ := natAbs_coords_le_of_gnorm hgn
    rw [mem_gBox_iff]
    refine ⟨Finset.mem_Icc.mpr (abs_le.mp ?_), Finset.mem_Icc.mpr (abs_le.mp ?_)⟩
    · rw [Int.abs_eq_natAbs]; exact_mod_cast h1
    · rw [Int.abs_eq_natAbs]; exact_mod_cast h2
  · rintro ⟨hzn, hgn⟩
    refine ⟨?_, hgn⟩
    rw [mem_gBox_iff] at hzn
    obtain ⟨h1, h2⟩ := hzn
    rw [mem_gBox_iff]
    have hcast : ((n : ℕ) : ℤ) ≤ ((R : ℕ) : ℤ) := by exact_mod_cast hR
    refine ⟨Finset.mem_Icc.mpr (abs_le.mp ?_), Finset.mem_Icc.mpr (abs_le.mp ?_)⟩
    · exact le_trans (abs_le.mpr (Finset.mem_Icc.mp h1)) hcast
    · exact le_trans (abs_le.mpr (Finset.mem_Icc.mp h2)) hcast

/-- The annulus `1 ≤ |z|² ≤ R` inside `gBox R`, restricted to `|z|² = n`, is the set of Gaussian
integers of norm `n` inside `gBox n` (`1 ≤ n ≤ R`). -/
lemma filter_gnorm_eq {R n : ℕ} (hn1 : 1 ≤ n) (hnR : n ≤ R) :
    ((Work.FIPlan.gBox ((R : ℕ) : ℤ)).filter
        (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ R)).filter
        (fun z => Work.FIPlan.gnorm z = n)
      = (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n) := by
  rw [Finset.filter_filter]
  rw [show (Work.FIPlan.gBox ((R : ℕ) : ℤ)).filter
        (fun z => (1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ R) ∧ Work.FIPlan.gnorm z = n)
      = (Work.FIPlan.gBox ((R : ℕ) : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n) from by
    apply Finset.filter_congr
    intro z _
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨⟨by rw [h]; exact hn1, by rw [h]; exact hnR⟩, h⟩]
  exact gBox_filter_gnorm_eq hn1 hnR

/-- **Fiber decomposition of the weighted `z`-sum.**  Collecting the Gaussian integers of the
annulus `1 ≤ |z|² ≤ R` of the box `gBox R` by the value `n = |z|²` turns the sum into the sum over
`n ∈ [1, R]` of the sum over the Gaussian integers of norm `n` inside `gBox n`. -/
lemma inner_sum_eq (m R : ℕ) (_hR : 1 ≤ R) (g : ℕ → ℝ) (w : GaussianInt) :
    (∑ z ∈ (Work.FIPlan.gBox ((R : ℕ) : ℤ)).filter
            (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ R),
        (if Nat.Coprime m (Work.FIPlan.gnorm z) then
          g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0))
      = ∑ n ∈ Finset.Icc 1 R,
          (if Nat.Coprime m n then g n *
            (∑ z ∈ (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n),
              (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) else 0) := by
  have hmap : ∀ z ∈ (Work.FIPlan.gBox ((R : ℕ) : ℤ)).filter
        (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ R),
      Work.FIPlan.gnorm z ∈ Finset.Icc 1 R := by
    intro z hz
    rw [Finset.mem_filter] at hz
    exact Finset.mem_Icc.mpr ⟨hz.2.1, hz.2.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun z => (if Nat.Coprime m (Work.FIPlan.gnorm z) then
      g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn1, hnR⟩ := Finset.mem_Icc.mp hn
  rw [filter_gnorm_eq hn1 hnR]
  have h2 : ∀ z ∈ (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter
      (fun z => Work.FIPlan.gnorm z = n),
      (if Nat.Coprime m (Work.FIPlan.gnorm z) then
        g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0)
        = (if Nat.Coprime m n then
            g n * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0) := by
    intro z hz
    rw [(Finset.mem_filter.mp hz).2]
  rw [Finset.sum_congr rfl h2]
  by_cases hc : Nat.Coprime m n
  · simp only [if_pos hc, Finset.mul_sum]
  · simp only [if_neg hc, Finset.sum_const_zero]

theorem anFI_sum_eq_gauss (m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) (g : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 (2 * N),
        (if Nat.Coprime m n then g n * (Work.FIPlan.anFI (m * n) : ℝ) else 0))
      = (1 / 4) * ∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
            (fun w => Work.FIPlan.gnorm w = m),
          ∑ z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
              (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ 2 * N),
            (if Nat.Coprime m (Work.FIPlan.gnorm z) then
              g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0) := by
  classical
  have h2N : 1 ≤ 2 * N := by omega
  have hstep1 :
      (1 / 4) * (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
            (fun w => Work.FIPlan.gnorm w = m),
          ∑ z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
              (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ 2 * N),
            (if Nat.Coprime m (Work.FIPlan.gnorm z) then
              g (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) else 0))
        = (1 / 4) * (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
            (fun w => Work.FIPlan.gnorm w = m),
          ∑ n ∈ Finset.Icc 1 (2 * N),
            (if Nat.Coprime m n then g n *
              (∑ z ∈ (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter
                  (fun z => Work.FIPlan.gnorm z = n),
                (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) else 0)) := by
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    exact inner_sum_eq m (2 * N) h2N g w
  have hfinal :
      (∑ n ∈ Finset.Icc 1 (2 * N),
        (1 / 4) * (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
            (fun w => Work.FIPlan.gnorm w = m),
          (if Nat.Coprime m n then g n *
              (∑ z ∈ (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter
                  (fun z => Work.FIPlan.gnorm z = n),
                (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) else 0)))
        = ∑ n ∈ Finset.Icc 1 (2 * N),
            (if Nat.Coprime m n then g n * (Work.FIPlan.anFI (m * n) : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
    by_cases hc : Nat.Coprime m n
    · have hS :
          (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
              (fun w => Work.FIPlan.gnorm w = m),
            (∑ z ∈ (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter
                (fun z => Work.FIPlan.gnorm z = n),
              (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)))
          = 4 * (Work.FIPlan.anFI (m * n) : ℝ) := by
        rw [Work.FITop4.Red4.anFI_eq_four_gauss hm hn1 hc]
        ring
      have hsum :
          (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
              (fun w => Work.FIPlan.gnorm w = m),
            (if Nat.Coprime m n then g n *
                (∑ z ∈ (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter
                    (fun z => Work.FIPlan.gnorm z = n),
                  (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) else 0))
          = g n * (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
              (fun w => Work.FIPlan.gnorm w = m),
            (∑ z ∈ (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter
                (fun z => Work.FIPlan.gnorm z = n),
              (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))) := by
        simp only [if_pos hc, Finset.mul_sum]
      rw [hsum, hS, if_pos hc]
      ring
    · have hsum :
          (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
              (fun w => Work.FIPlan.gnorm w = m),
            (if Nat.Coprime m n then g n *
                (∑ z ∈ (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter
                    (fun z => Work.FIPlan.gnorm z = n),
                  (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) else 0)) = 0 := by
        simp only [if_neg hc, Finset.sum_const_zero]
      rw [hsum, if_neg hc]
      ring
  rw [hstep1, Finset.sum_comm, Finset.mul_sum, hfinal]

end

end Work.FITop4.Red5
