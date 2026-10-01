/-
# Auxiliary objects for `S3_eq_restricted`

Namespace `Work.LinnikAreas.Density4.BzS3`.

The quadruple form of `Σ_{n≤N} B_z(n)²` (`BzHard.S3_eq_quadruple`) is
`Σ_{q,r,t ≤ N} [r⊥t]μ(r)μ(t) · J(q,r,t)` with the inner `m`-sum
`J(q,r,t) = Σ_{m ≤ N} [m⊥rt][m squarefree][z<tm][z<rm][qrtm≤N]·log(tm/z)log(rm/z)`.

Here we collect the objects of the *restricted* form: the multiplier `muP`,
the inner sum `Jq`, the two differences of `s3G` (`Gd`), and the elementary
reindexing lemmas that convert `Jq` into a `s3G`-difference on the range
`q ≤ N/z`, `r,t ≤ N/(qz)`.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.LamRDefs
import Submission.Work.LinnikAreas.Density4.BzS3.S3InnerDefs

namespace Work.LinnikAreas.Density4.BzS3

open Finset

noncomputable section

/-- The Möbius multiplier `[r ⊥ t]·μ(r)·μ(t)` of the quadruple sum. -/
def muP (r t : ℕ) : ℝ :=
  if Nat.Coprime r t then
    (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ)
  else 0

/-- The inner `m`-sum of the quadruple form of `Σ_{n≤N} B_z(n)²`. -/
def Jq (z N q r t : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N,
    (if Nat.Coprime m (r * t) ∧ Squarefree m ∧ z < t * m ∧ z < r * m ∧ q * r * t * m ≤ N
     then Real.log (((t * m : ℕ) : ℝ) / (z : ℝ)) * Real.log (((r * m : ℕ) : ℝ) / (z : ℝ))
     else 0)

/-- The difference of the two `s3G` sums at the cut-offs `⌊N/(qrt)⌋` and `max ⌊z/t⌋ ⌊z/r⌋`. -/
def Gd (z N q r t : ℕ) : ℝ :=
  s3G (r * t) (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ))) (N / (q * r * t))
  - s3G (r * t) (Real.log ((z : ℝ) / (t : ℝ))) (Real.log ((z : ℝ) / (r : ℝ)))
      (max (z / t) (z / r))

/-- **Set identity for the inner `m`-sum.**  The `m` satisfying the five constraints of `Jq`
are exactly the squarefree `m` coprime to `rt` in the interval `(max ⌊z/t⌋ ⌊z/r⌋, ⌊N/(qrt)⌋]`. -/
lemma inner_filter_eq (z N q r t : ℕ) (hq : 0 < q) (hr : 0 < r) (ht : 0 < t) :
    (Finset.Icc 1 N).filter (fun m => Nat.Coprime m (r * t) ∧ Squarefree m ∧ z < t * m
        ∧ z < r * m ∧ q * r * t * m ≤ N)
      = (Finset.Icc (max (z / t) (z / r) + 1) (N / (q * r * t))).filter
        (fun m => Nat.Coprime m (r * t) ∧ Squarefree m) := by
  have hqrt : 0 < q * r * t := by positivity
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hm1, hmN⟩, hc, hs, hzt, hzr, hqr⟩
    have hL : z / t < m := (Nat.div_lt_iff_lt_mul ht).mpr (by rw [Nat.mul_comm]; exact hzt)
    have hR : z / r < m := (Nat.div_lt_iff_lt_mul hr).mpr (by rw [Nat.mul_comm]; exact hzr)
    have hX : m ≤ N / (q * r * t) :=
      (Nat.le_div_iff_mul_le hqrt).mpr (by rw [Nat.mul_comm]; exact hqr)
    refine ⟨⟨?_, hX⟩, hc, hs⟩
    exact Nat.lt_iff_add_one_le.mp (max_lt hL hR)
  · rintro ⟨⟨hm1, hm2⟩, hc, hs⟩
    have hmax : max (z / t) (z / r) < m := Nat.lt_of_succ_le hm1
    have hL : z / t < m := lt_of_le_of_lt (le_max_left _ _) hmax
    have hR : z / r < m := lt_of_le_of_lt (le_max_right _ _) hmax
    refine ⟨⟨?_, ?_⟩, hc, hs, ?_, ?_, ?_⟩
    · exact le_trans (Nat.le_add_left 1 _) hm1
    · exact le_trans hm2 (Nat.div_le_self _ _)
    · have := (Nat.div_lt_iff_lt_mul ht).mp hL
      rwa [Nat.mul_comm] at this
    · have := (Nat.div_lt_iff_lt_mul hr).mp hR
      rwa [Nat.mul_comm] at this
    · have := (Nat.le_div_iff_mul_le hqrt).mp hm2
      rwa [Nat.mul_comm] at this

/-- **Telescoping of `s3G`.**  For `Y ≤ X` the difference of the two `s3G`-sums is the sum over
the interval `(Y, X]` of the same filtered summand. -/
lemma sum_filter_Icc_sub_Icc (X Y : ℕ) (hYX : Y ≤ X) (p : ℕ → Prop) [DecidablePred p]
    (f : ℕ → ℝ) :
    (∑ m ∈ (Finset.Icc 1 X).filter p, f m) - (∑ m ∈ (Finset.Icc 1 Y).filter p, f m)
      = ∑ m ∈ (Finset.Icc (Y + 1) X).filter p, f m := by
  have hsub : (Finset.Icc 1 Y).filter p ⊆ (Finset.Icc 1 X).filter p := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    exact ⟨⟨hm.1.1, le_trans hm.1.2 hYX⟩, hm.2⟩
  have hsdiff : ((Finset.Icc 1 X).filter p) \ ((Finset.Icc 1 Y).filter p)
      = (Finset.Icc (Y + 1) X).filter p := by
    ext m
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hp⟩, hnot⟩
      have hYm : Y < m := by
        by_contra hc
        push_neg at hc
        exact hnot ⟨⟨h1, hc⟩, hp⟩
      exact ⟨⟨by omega, h2⟩, hp⟩
    · rintro ⟨⟨h1, h2⟩, hp⟩
      refine ⟨⟨⟨by omega, h2⟩, hp⟩, ?_⟩
      rintro ⟨⟨h3, h4⟩, -⟩
      omega
  have key := Finset.sum_sdiff hsub (f := f)
  rw [hsdiff] at key
  linarith

/-- **The `log` identity `log(tm/z) = log m − log(z/t)`.** -/
lemma log_mul_div_eq (z t m : ℕ) (hz : 0 < z) (ht : 0 < t) (hm : 0 < m) :
    Real.log (((t * m : ℕ) : ℝ) / (z : ℝ))
      = Real.log (m : ℝ) - Real.log ((z : ℝ) / (t : ℝ)) := by
  have hz' : (z : ℝ) ≠ 0 := by positivity
  have ht' : (t : ℝ) ≠ 0 := by positivity
  have hm' : (m : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_mul, Real.log_div (by positivity) hz', Real.log_mul ht' hm',
    Real.log_div hz' ht']
  ring

/-- **Pointwise identity on the restricted range.**  When `r,t ≤ ⌊N/(qz)⌋` the two cut-offs
satisfy `max ⌊z/t⌋ ⌊z/r⌋ ≤ ⌊N/(qrt)⌋`, so `Jq` telescopes into the difference `Gd` of the two
`s3G`-sums. -/
lemma Jq_eq_Gd (z N q r t : ℕ) (hz : 0 < z) (hq : 0 < q) (hr : 0 < r) (ht : 0 < t)
    (hrN : r ≤ N / (q * z)) (htN : t ≤ N / (q * z)) :
    Jq z N q r t = Gd z N q r t := by
  have hqz : 0 < q * z := by positivity
  have hqr : 0 < q * r := by positivity
  have hqt : 0 < q * t := by positivity
  have hYt : z / t ≤ N / (q * r * t) := by
    have h1 : z ≤ N / (q * r) := (Nat.le_div_iff_mul_le hqr).mpr (by
      have := (Nat.le_div_iff_mul_le hqz).mp hrN
      calc z * (q * r) = r * (q * z) := by ring
        _ ≤ N := this)
    calc z / t ≤ (N / (q * r)) / t := Nat.div_le_div_right h1
      _ = N / ((q * r) * t) := Nat.div_div_eq_div_mul N (q * r) t
      _ = N / (q * r * t) := rfl
  have hYr : z / r ≤ N / (q * r * t) := by
    have h1 : z ≤ N / (q * t) := (Nat.le_div_iff_mul_le hqt).mpr (by
      have := (Nat.le_div_iff_mul_le hqz).mp htN
      calc z * (q * t) = t * (q * z) := by ring
        _ ≤ N := this)
    calc z / r ≤ (N / (q * t)) / r := Nat.div_le_div_right h1
      _ = N / ((q * t) * r) := Nat.div_div_eq_div_mul N (q * t) r
      _ = N / (q * r * t) := by rw [show (q * t) * r = q * r * t by ring]
  have hYX : max (z / t) (z / r) ≤ N / (q * r * t) := max_le hYt hYr
  have hJ : Jq z N q r t
      = ∑ m ∈ (Finset.Icc (max (z / t) (z / r) + 1) (N / (q * r * t))).filter
          (fun m => Nat.Coprime m (r * t) ∧ Squarefree m),
          Real.log (((t * m : ℕ) : ℝ) / (z : ℝ)) * Real.log (((r * m : ℕ) : ℝ) / (z : ℝ)) := by
    unfold Jq
    rw [← Finset.sum_filter, inner_filter_eq z N q r t hq hr ht]
  have hG : Gd z N q r t
      = ∑ m ∈ (Finset.Icc (max (z / t) (z / r) + 1) (N / (q * r * t))).filter
          (fun m => Nat.Coprime m (r * t) ∧ Squarefree m),
          (Real.log (m : ℝ) - Real.log ((z : ℝ) / (t : ℝ)))
            * (Real.log (m : ℝ) - Real.log ((z : ℝ) / (r : ℝ))) := by
    unfold Gd s3G
    rw [sum_filter_Icc_sub_Icc (N / (q * r * t)) (max (z / t) (z / r)) hYX
        (fun m => Nat.Coprime m (r * t) ∧ Squarefree m)
        (fun m => (Real.log (m : ℝ) - Real.log ((z : ℝ) / (t : ℝ)))
          * (Real.log (m : ℝ) - Real.log ((z : ℝ) / (r : ℝ))))]
  rw [hJ, hG]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_Icc] at hm
  have hm0 : 0 < m := lt_of_lt_of_le (Nat.succ_pos _) hm.1.1
  rw [log_mul_div_eq z t m hz ht hm0, log_mul_div_eq z r m hz hr hm0]

/-- **Vanishing outside the restricted range.**  If any of `q > ⌊N/z⌋`, `r > ⌊N/(qz)⌋`,
`t > ⌊N/(qz)⌋` holds then no `m` satisfies the constraints of `Jq`, so `Jq = 0`. -/
lemma Jq_eq_zero (z N q r t : ℕ) (hz : 0 < z) (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 1 ≤ t)
    (h : N / z < q ∨ N / (q * z) < r ∨ N / (q * z) < t) :
    Jq z N q r t = 0 := by
  rw [Jq]
  apply Finset.sum_eq_zero
  intro m hm
  rw [if_neg]
  intro hc
  obtain ⟨hcop, hsq, hzt, hzr, hqrtm⟩ := hc
  have hqz : 0 < q * z := by positivity
  have hZTM : z ≤ t * m := le_of_lt hzt
  have hZRM : z ≤ r * m := le_of_lt hzr
  have key : N < q * r * t * m := by
    rcases h with h1 | h2 | h3
    · have h1' : N < q * z := (Nat.div_lt_iff_lt_mul hz).mp h1
      have hle : q * z ≤ q * r * t * m := by
        have hA : z ≤ r * (t * m) := le_trans hZTM (Nat.le_mul_of_pos_left (t * m) hr)
        calc q * z ≤ q * (r * (t * m)) := Nat.mul_le_mul_left q hA
          _ = q * r * t * m := by ring
      omega
    · have h2' : N < r * (q * z) := (Nat.div_lt_iff_lt_mul hqz).mp h2
      have hle : r * (q * z) ≤ q * r * t * m := by
        calc r * (q * z) = q * r * z := by ring
          _ ≤ q * r * (t * m) := Nat.mul_le_mul_left (q * r) hZTM
          _ = q * r * t * m := by ring
      omega
    · have h3' : N < t * (q * z) := (Nat.div_lt_iff_lt_mul hqz).mp h3
      have hle : t * (q * z) ≤ q * r * t * m := by
        calc t * (q * z) = q * t * z := by ring
          _ ≤ q * t * (r * m) := Nat.mul_le_mul_left (q * t) hZRM
          _ = q * r * t * m := by ring
      omega
  omega


end

end Work.LinnikAreas.Density4.BzS3
