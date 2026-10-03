import Mathlib
import Submission.Work.Peluse.MajorArc.Defs

namespace Work.Peluse.Fourier

open scoped BigOperators

/-- `ee ((k:ℝ) * x) = (ee x)^k`. -/
private lemma ee_nat_mul (x : ℝ) (k : ℕ) :
    Work.Peluse.ee ((k : ℝ) * x) = (Work.Peluse.ee x) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Work.Peluse.ee_add, ih, pow_succ]

/-- Orthogonality of the additive character on `ℤ/L`: the average of the `L`-th roots of unity is
`L` if `L ∣ m` and `0` otherwise. -/
private lemma dftTriple_orthogonality (L : ℕ) (hL : 1 ≤ L) (m : ℤ) :
    ∑ k ∈ Finset.range L, Work.Peluse.ee ((k : ℝ) * (m : ℝ) / (L : ℝ)) =
      if (L : ℤ) ∣ m then (L : ℂ) else 0 := by
  have hpow : ∀ k ∈ Finset.range L,
      Work.Peluse.ee ((k : ℝ) * (m : ℝ) / (L : ℝ)) =
        (Work.Peluse.ee ((m : ℝ) / (L : ℝ))) ^ k := by
    intro k _
    rw [mul_div_assoc]
    exact ee_nat_mul _ k
  rw [Finset.sum_congr rfl hpow]
  set ζ := Work.Peluse.ee ((m : ℝ) / (L : ℝ))
  have hζ : ζ = Work.Peluse.ee ((m : ℝ) / (L : ℝ)) := rfl
  have hζL : ζ ^ L = 1 := by
    rw [hζ, ← ee_nat_mul]
    rw [show (L : ℝ) * ((m : ℝ) / (L : ℝ)) = (m : ℝ) by field_simp]
    exact Work.Peluse.ee_int m
  have hiff : ζ = 1 ↔ (L : ℤ) ∣ m := by
    rw [hζ, Work.Peluse.ee_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hm : (m : ℝ) = (n : ℝ) * (L : ℝ) := by
        field_simp at hn
        linarith [hn]
      exact_mod_cast hm.trans (mul_comm (n : ℝ) (L : ℝ))
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [hc]
      push_cast
      field_simp
  by_cases h1 : ζ = 1
  · rw [if_pos (hiff.mp h1)]
    have : ∀ k ∈ Finset.range L, ζ ^ k = 1 := by intro k _; rw [h1, one_pow]
    rw [Finset.sum_congr rfl this]
    simp
  · rw [if_neg (fun h => h1 (hiff.mpr h))]
    have hsum : (∑ k ∈ Finset.range L, ζ ^ k) = 0 := by
      have hg := geom_sum_mul ζ L
      rw [hζL, sub_self] at hg
      exact (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr h1)
    rw [hsum]

theorem dftTriple (L K₁ K₂ K₃ : ℕ) (hL : 1 ≤ L) (hKL : K₁ + K₂ + K₃ < L)
    (A B C : ℤ → ℂ) (hB : ∀ v : ℤ, K₂ < v.natAbs → B v = 0) :
    (∑ k ∈ Finset.range L,
        (∑ u ∈ Finset.Icc (-(K₁ : ℤ)) (K₁ : ℤ),
            A u * Work.Peluse.ee (-((k : ℝ) * (u : ℝ)) / (L : ℝ))) *
        (∑ v ∈ Finset.Icc (-(K₂ : ℤ)) (K₂ : ℤ),
            B v * Work.Peluse.ee (((k : ℝ) * (v : ℝ)) / (L : ℝ))) *
        (∑ y ∈ Finset.Icc (-(K₃ : ℤ)) (K₃ : ℤ),
            C y * Work.Peluse.ee (-((k : ℝ) * (y : ℝ)) / (L : ℝ))))
      = (L : ℂ) * ∑ u ∈ Finset.Icc (-(K₁ : ℤ)) (K₁ : ℤ),
          ∑ y ∈ Finset.Icc (-(K₃ : ℤ)) (K₃ : ℤ), A u * C y * B (u + y) := by
  set I₁ : Finset ℤ := Finset.Icc (-(K₁ : ℤ)) (K₁ : ℤ) with hI₁
  set I₂ : Finset ℤ := Finset.Icc (-(K₂ : ℤ)) (K₂ : ℤ) with hI₂
  set I₃ : Finset ℤ := Finset.Icc (-(K₃ : ℤ)) (K₃ : ℤ) with hI₃
  have memAbs : ∀ {z : ℤ} {K : ℕ}, z ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) → |z| ≤ (K : ℤ) := by
    intro z K hz
    rw [Finset.mem_Icc] at hz
    exact abs_le.mpr hz
  have hBabs : ∀ v : ℤ, (K₂ : ℤ) < |v| → B v = 0 := by
    intro v hv
    apply hB
    have hcast : ((v.natAbs : ℕ) : ℤ) = |v| := Int.natCast_natAbs v
    have : (K₂ : ℤ) < ((v.natAbs : ℕ) : ℤ) := by rw [hcast]; exact hv
    exact_mod_cast this
  have hKLT : ((K₁ : ℤ) + (K₂ : ℤ) + (K₃ : ℤ)) < (L : ℤ) := by
    have h : ((K₁ + K₂ + K₃ : ℕ) : ℤ) < (L : ℤ) := by exact_mod_cast hKL
    push_cast at h
    linarith
  -- ## Step 1: expand the product of the three windowed Fourier transforms for fixed `k`
  have hExpand : ∀ k ∈ Finset.range L,
      (∑ u ∈ I₁, A u * Work.Peluse.ee (-((k : ℝ) * (u : ℝ)) / (L : ℝ))) *
      (∑ v ∈ I₂, B v * Work.Peluse.ee (((k : ℝ) * (v : ℝ)) / (L : ℝ))) *
      (∑ y ∈ I₃, C y * Work.Peluse.ee (-((k : ℝ) * (y : ℝ)) / (L : ℝ)))
      = ∑ u ∈ I₁, ∑ y ∈ I₃, ∑ v ∈ I₂,
          A u * B v * C y *
            Work.Peluse.ee ((k : ℝ) * ((v : ℝ) - (u : ℝ) - (y : ℝ)) / (L : ℝ)) := by
    intro k _
    rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have hcoeff : A u * Work.Peluse.ee (-((k : ℝ) * (u : ℝ)) / (L : ℝ)) *
        (B v * Work.Peluse.ee (((k : ℝ) * (v : ℝ)) / (L : ℝ)) *
          (C y * Work.Peluse.ee (-((k : ℝ) * (y : ℝ)) / (L : ℝ))))
        = A u * B v * C y *
          (Work.Peluse.ee (-((k : ℝ) * (u : ℝ)) / (L : ℝ)) *
            (Work.Peluse.ee (((k : ℝ) * (v : ℝ)) / (L : ℝ)) *
              Work.Peluse.ee (-((k : ℝ) * (y : ℝ)) / (L : ℝ)))) := by ring
    have hphase : Work.Peluse.ee (-((k : ℝ) * (u : ℝ)) / (L : ℝ)) *
          (Work.Peluse.ee (((k : ℝ) * (v : ℝ)) / (L : ℝ)) *
            Work.Peluse.ee (-((k : ℝ) * (y : ℝ)) / (L : ℝ)))
        = Work.Peluse.ee ((k : ℝ) * ((v : ℝ) - (u : ℝ) - (y : ℝ)) / (L : ℝ)) := by
      rw [← mul_assoc, ← Work.Peluse.ee_add, ← Work.Peluse.ee_add]
      congr 1
      ring
    rw [hcoeff, hphase]
  have hStep1 : (∑ k ∈ Finset.range L,
        (∑ u ∈ I₁, A u * Work.Peluse.ee (-((k : ℝ) * (u : ℝ)) / (L : ℝ))) *
        (∑ v ∈ I₂, B v * Work.Peluse.ee (((k : ℝ) * (v : ℝ)) / (L : ℝ))) *
        (∑ y ∈ I₃, C y * Work.Peluse.ee (-((k : ℝ) * (y : ℝ)) / (L : ℝ))))
      = ∑ k ∈ Finset.range L, ∑ u ∈ I₁, ∑ y ∈ I₃, ∑ v ∈ I₂,
          A u * B v * C y *
            Work.Peluse.ee ((k : ℝ) * ((v : ℝ) - (u : ℝ) - (y : ℝ)) / (L : ℝ)) :=
    Finset.sum_congr rfl hExpand
  -- ## Step 2: move the `k`-sum inside
  have hReord : (∑ k ∈ Finset.range L, ∑ u ∈ I₁, ∑ y ∈ I₃, ∑ v ∈ I₂,
          A u * B v * C y *
            Work.Peluse.ee ((k : ℝ) * ((v : ℝ) - (u : ℝ) - (y : ℝ)) / (L : ℝ)))
      = ∑ u ∈ I₁, ∑ y ∈ I₃, ∑ v ∈ I₂, ∑ k ∈ Finset.range L,
          A u * B v * C y *
            Work.Peluse.ee ((k : ℝ) * ((v : ℝ) - (u : ℝ) - (y : ℝ)) / (L : ℝ)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [Finset.sum_comm]
  -- ## Step 3: evaluate the `k`-sum by orthogonality
  have hKeval : (∑ u ∈ I₁, ∑ y ∈ I₃, ∑ v ∈ I₂, ∑ k ∈ Finset.range L,
          A u * B v * C y *
            Work.Peluse.ee ((k : ℝ) * ((v : ℝ) - (u : ℝ) - (y : ℝ)) / (L : ℝ)))
      = ∑ u ∈ I₁, ∑ y ∈ I₃, ∑ v ∈ I₂,
          A u * B v * C y * (if (L : ℤ) ∣ (v - u - y) then (L : ℂ) else 0) := by
    refine Finset.sum_congr rfl (fun u hu => ?_)
    refine Finset.sum_congr rfl (fun y hy => ?_)
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have hph : ((v : ℝ) - (u : ℝ) - (y : ℝ)) = ((v - u - y : ℤ) : ℝ) := by push_cast; ring
    rw [← Finset.mul_sum, hph, dftTriple_orthogonality L hL (v - u - y)]
  -- ## Step 4: collapse the `v`-sum
  have hvy : ∀ u y : ℤ, u ∈ I₁ → y ∈ I₃ →
      (∑ v ∈ I₂, A u * B v * C y * (if (L : ℤ) ∣ (v - u - y) then (L : ℂ) else 0))
        = (L : ℂ) * (A u * C y * B (u + y)) := by
    intro u y hu hy
    have hu' : |u| ≤ (K₁ : ℤ) := memAbs (hI₁ ▸ hu)
    have hy' : |y| ≤ (K₃ : ℤ) := memAbs (hI₃ ▸ hy)
    have hstep1 : (∑ v ∈ I₂,
          A u * B v * C y * (if (L : ℤ) ∣ (v - u - y) then (L : ℂ) else 0))
        = ∑ v ∈ I₂, A u * B v * C y * (if v = u + y then (L : ℂ) else 0) := by
      refine Finset.sum_congr rfl (fun v hv => ?_)
      have hv' : |v| ≤ (K₂ : ℤ) := memAbs (hI₂ ▸ hv)
      have hdv : ((L : ℤ) ∣ (v - u - y)) ↔ v = u + y := by
        constructor
        · intro hd
          have hb : |v - u - y| ≤ (K₁ : ℤ) + (K₂ : ℤ) + (K₃ : ℤ) := by
            have h1 : |v - u - y| ≤ |v| + |u| + |y| := by
              have h3 : |v - u| ≤ |v| + |u| := by
                rw [abs_sub_le_iff]
                constructor <;>
                  linarith [le_abs_self v, neg_le_abs v, le_abs_self u, neg_le_abs u]
              have h2 : |v - u - y| ≤ |v - u| + |y| := by
                rw [abs_sub_le_iff]
                constructor <;>
                  linarith [le_abs_self (v - u), neg_le_abs (v - u), le_abs_self y,
                    neg_le_abs y]
              linarith
            linarith [h1, hu', hv', hy']
          have hlt : |v - u - y| < (L : ℤ) := by linarith [hb, hKLT]
          have hz := Int.eq_zero_of_abs_lt_dvd hd hlt
          omega
        · intro h
          have h0 : v - u - y = 0 := by omega
          rw [h0]; exact dvd_zero _
      congr 1
      by_cases h : (L : ℤ) ∣ (v - u - y)
      · rw [if_pos h, if_pos (hdv.mp h)]
      · rw [if_neg h, if_neg (fun hh => h (hdv.mpr hh))]
    have hstep2 : (∑ v ∈ I₂, A u * B v * C y * (if v = u + y then (L : ℂ) else 0))
        = (L : ℂ) * (A u * C y * B (u + y)) := by
      have hterm : ∀ v : ℤ, A u * B v * C y * (if v = u + y then (L : ℂ) else 0)
          = (if v = u + y then A u * B v * C y * (L : ℂ) else 0) := by
        intro v
        by_cases h : v = u + y <;> simp [h]
      rw [Finset.sum_congr rfl (fun v hv => hterm v), Finset.sum_ite_eq']
      by_cases h : u + y ∈ I₂
      · rw [if_pos h]; ring
      · rw [if_neg h]
        have hB0 : B (u + y) = 0 := by
          apply hBabs
          have hnot : ¬ (-(K₂ : ℤ) ≤ u + y ∧ u + y ≤ (K₂ : ℤ)) := by
            intro hc
            exact h (by rw [hI₂, Finset.mem_Icc]; exact hc)
          rw [lt_abs]
          rcases (not_and_or.mp hnot) with h1 | h2
          · right; have := not_le.mp h1; linarith
          · left; exact not_le.mp h2
        rw [hB0]; ring
    rw [hstep1, hstep2]
  have hFinal : (∑ u ∈ I₁, ∑ y ∈ I₃, ∑ v ∈ I₂,
        A u * B v * C y * (if (L : ℤ) ∣ (v - u - y) then (L : ℂ) else 0))
      = (L : ℂ) * ∑ u ∈ I₁, ∑ y ∈ I₃, A u * C y * B (u + y) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    refine Finset.sum_congr rfl (fun y hy => ?_)
    exact hvy u y hu hy
  exact hStep1.trans (hReord.trans (hKeval.trans hFinal))

end Work.Peluse.Fourier
