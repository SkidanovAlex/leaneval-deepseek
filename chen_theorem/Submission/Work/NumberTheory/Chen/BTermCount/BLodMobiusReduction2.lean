import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodAssembly
import Submission.Work.NumberTheory.Chen.BTermCount.BLodConductorDecomp
import Submission.Work.NumberTheory.Chen.BTermCount.BLodMobiusBound
import Submission.Work.NumberTheory.Chen.BTermCount.sumThreePowInvTotientBound

namespace Work.NumberTheory.Chen.BTermCount

open Finset

attribute [local instance] Classical.propDecidable

/-!
# Möbius reduction for the `B̄`-twisted character sums (second form)

This module proves `BLodMobiusReduction2`: the odd-`d` weighted sum of the terms
`3^{ω d}/φ d · Σ_{c ∣ d, c ≥ 2} Σ*_{ψ mod c} ‖bProdCharSum d (changeLevel ψ)‖`
is bounded by `(log D)^3` times the double sum over `t, r` of
`(3^{ω t}/φ t)(3^{ω r}/φ r) · bProdCharSumDivSum t r`.

The route is the one described in `notes/BLOD_SESSION3_PLAN.md`:

* per `(d,c,ψ)`, the Möbius bound `BLodMobiusBound` turns the raised-level sum into
  `Σ_{t ∣ d/c} ‖bProdCharSumDiv c t ψ‖`;
* the weight `3^{ω d}/φ d` factors over the product `d = c·t·m` through
  super-multiplicativity of `Nat.totient`;
* the remaining coin count `Σ_{m ≤ D} 3^{ω m}/φ m ≤ C (log D)^3` is
  `sumThreePowInvTotientBound`.
-/

/-- The level weight `3^{ω n} / φ n`. -/
noncomputable def lvlW (n : ℕ) : ℝ := (3:ℝ)^(n.primeFactors.card) / (Nat.totient n : ℝ)

theorem lvlW_nonneg (n : ℕ) : 0 ≤ lvlW n := div_nonneg (by positivity) (by positivity)

/-- `ω` is subadditive for multiplication. -/
theorem primeFactors_card_mul_le (a b : ℕ) :
    (a*b).primeFactors.card ≤ a.primeFactors.card + b.primeFactors.card := by
  rcases eq_or_ne a 0 with h|h
  · subst h; simp
  rcases eq_or_ne b 0 with h₂|h₂
  · subst h₂; simp
  rw [Nat.primeFactors_mul h h₂]
  exact Finset.card_union_le _ _

/-- **Multiplicativity of the level weight.**  `lvlW (c t m) ≤ lvlW c · lvlW t · lvlW m`. -/
theorem lvlW_mul_le (c t m : ℕ) (hc : 1 ≤ c) (ht : 1 ≤ t) (hm : 1 ≤ m) :
    lvlW (c*t*m) ≤ lvlW c * lvlW t * lvlW m := by
  have hpc : (0:ℝ) < (Nat.totient c : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < c))
  have hω : (c*t*m).primeFactors.card
      ≤ c.primeFactors.card + t.primeFactors.card + m.primeFactors.card := by
    have h1 : (c*t*m).primeFactors.card ≤ (c*t).primeFactors.card + m.primeFactors.card := by
      rw [show c*t*m = (c*t)*m from by ring]
      exact primeFactors_card_mul_le (c*t) m
    have h2 : (c*t).primeFactors.card ≤ c.primeFactors.card + t.primeFactors.card :=
      primeFactors_card_mul_le c t
    omega
  have hφ : (Nat.totient c : ℝ) * (Nat.totient t : ℝ) * (Nat.totient m : ℝ)
      ≤ (Nat.totient (c*t*m) : ℝ) := by
    have h1 : (Nat.totient c : ℝ) * (Nat.totient (t*m) : ℝ) ≤ (Nat.totient (c*(t*m)) : ℝ) := by
      exact_mod_cast Nat.totient_super_multiplicative c (t*m)
    have h2 : (Nat.totient t : ℝ) * (Nat.totient m : ℝ) ≤ (Nat.totient (t*m) : ℝ) := by
      exact_mod_cast Nat.totient_super_multiplicative t m
    have h3 : c*(t*m) = c*t*m := by ring
    rw [h3] at h1
    have h4 : (Nat.totient c : ℝ) * ((Nat.totient t : ℝ) * (Nat.totient m : ℝ))
        ≤ (Nat.totient c : ℝ) * (Nat.totient (t*m) : ℝ) :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hpc)
    linarith
  rw [lvlW, lvlW, lvlW]
  have h3 : (3:ℝ)^((c*t*m).primeFactors.card)
      ≤ (3:ℝ)^(c.primeFactors.card) * (3:ℝ)^(t.primeFactors.card) * (3:ℝ)^(m.primeFactors.card) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hφpos : (0:ℝ) < (Nat.totient c : ℝ) * (Nat.totient t : ℝ) * (Nat.totient m : ℝ) := by positivity
  calc (3:ℝ)^((c*t*m).primeFactors.card) / (Nat.totient (c*t*m) : ℝ)
      ≤ ((3:ℝ)^(c.primeFactors.card) * (3:ℝ)^(t.primeFactors.card) * (3:ℝ)^(m.primeFactors.card))
          / (Nat.totient (c*t*m) : ℝ) := by
        apply div_le_div_of_nonneg_right h3 (by positivity)
    _ ≤ ((3:ℝ)^(c.primeFactors.card) * (3:ℝ)^(t.primeFactors.card) * (3:ℝ)^(m.primeFactors.card))
          / ((Nat.totient c : ℝ) * (Nat.totient t : ℝ) * (Nat.totient m : ℝ)) := by
        apply div_le_div_of_nonneg_left (by positivity) hφpos hφ
    _ = ((3:ℝ)^(c.primeFactors.card) / (Nat.totient c : ℝ))
          * ((3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ))
          * ((3:ℝ)^(m.primeFactors.card) / (Nat.totient m : ℝ)) := by
        field_simp

/-- A sum over the divisors of `n ≤ D` rewritten as a sum over `Icc 1 D` with an indicator. -/
theorem divisors_sum_eq_Icc_sum_ite (n D : ℕ) (f : ℕ → ℝ) (hn : 1 ≤ n) (hnD : n ≤ D) :
    ∑ t ∈ n.divisors, f t = ∑ t ∈ Finset.Icc 1 D, (if t ∣ n then f t else 0) := by
  have hI : Finset.Ico 1 (n+1) = Finset.Icc 1 n := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [Nat.divisors, hI, Finset.sum_filter]
  refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hnD) ?_
  intro t ht htn
  rw [Finset.mem_Icc] at ht
  have h : ¬ (t ∣ n) := by
    intro hdiv
    exact htn (Finset.mem_Icc.mpr ⟨ht.1, Nat.le_of_dvd (by omega) hdiv⟩)
  simp [h]

/-- The inner block of the `d`-term of the left hand side, as a double `Icc`-sum with indicator. -/
theorem block_eq (D d : ℕ) (Y : ℕ → ℕ → ℝ) (hd1 : 1 ≤ d) (hdD : d ≤ D) :
    (∑ c ∈ d.divisors.filter (fun c => 2 ≤ c), ∑ t ∈ (d / c).divisors, Y t c)
      = ∑ c ∈ Finset.Icc 1 D, ∑ t ∈ Finset.Icc 1 D,
          (if 2 ≤ c ∧ c * t ∣ d then Y t c else 0) := by
  have hd0 : d ≠ 0 := by omega
  have hstep1 : ∀ c ∈ d.divisors.filter (fun c => 2 ≤ c),
      (∑ t ∈ (d / c).divisors, Y t c)
        = ∑ t ∈ Finset.Icc 1 D, (if 2 ≤ c ∧ c * t ∣ d then Y t c else 0) := by
    intro c hc
    obtain ⟨hcdvd, hc2⟩ := Finset.mem_filter.mp hc
    have hcd : c ∣ d := (Nat.mem_divisors.mp hcdvd).1
    have hcpos : 1 ≤ c := by omega
    have hdc1 : 1 ≤ d / c := Nat.div_pos (Nat.le_of_dvd (by omega) hcd) (by omega)
    have hdcD : d / c ≤ D := le_trans (Nat.div_le_self d c) hdD
    rw [divisors_sum_eq_Icc_sum_ite (d / c) D (fun t => Y t c) hdc1 hdcD]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    by_cases h : t ∣ d / c
    · rw [if_pos h, if_pos ⟨hc2, (Nat.dvd_div_iff_mul_dvd hcd).mp h⟩]
    · rw [if_neg h, if_neg (fun hh => h ((Nat.dvd_div_iff_mul_dvd hcd).mpr hh.2))]
  rw [Finset.sum_congr rfl hstep1]
  refine Finset.sum_subset ?hsub ?hzero
  · intro c hc
    obtain ⟨hcdvd, hc2⟩ := Finset.mem_filter.mp hc
    have hcd : c ∣ d := (Nat.mem_divisors.mp hcdvd).1
    rw [Finset.mem_Icc]
    exact ⟨by omega, le_trans (Nat.le_of_dvd (by omega) hcd) hdD⟩
  · intro c hcI hcnot
    rw [Finset.sum_eq_zero]
    intro t ht
    rw [if_neg]
    rintro ⟨hc2, hctd⟩
    exact hcnot (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨(dvd_mul_right c t).trans hctd, hd0⟩, hc2⟩)

/-- **The reindexing / weight-swap bound.**  For nonnegative `w`, `Y` with `w` sub-multiplicative
on products, the odd-`d` weighted divisor sum is bounded by the `(log D)^3`-free double sum. -/
theorem reindex_bound (D : ℕ) (w : ℕ → ℝ) (Y : ℕ → ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (hY : ∀ t r, 0 ≤ Y t r)
    (hwmul : ∀ c t m, 1 ≤ c → 1 ≤ t → 1 ≤ m → w (c*t*m) ≤ w c * w t * w m) :
    (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
        w d * (∑ c ∈ d.divisors.filter (fun c => 2 ≤ c), ∑ t ∈ (d / c).divisors, Y t c))
      ≤ (∑ m ∈ Finset.Icc 1 D, w m) *
        (∑ t ∈ Finset.Icc 1 D, ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r), w t * (w r * Y t r)) := by
  classical
  have hA : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
        w d * (∑ c ∈ d.divisors.filter (fun c => 2 ≤ c), ∑ t ∈ (d / c).divisors, Y t c))
      = ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
          ∑ c ∈ Finset.Icc 1 D, ∑ t ∈ Finset.Icc 1 D,
            w d * (if 2 ≤ c ∧ c * t ∣ d then Y t c else 0) := by
    refine Finset.sum_congr rfl (fun d hd => ?_)
    obtain ⟨hdIcc, -⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hdIcc
    rw [block_eq D d Y hd1 hdD, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [Finset.mul_sum]
  have hB : ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
          ∑ c ∈ Finset.Icc 1 D, ∑ t ∈ Finset.Icc 1 D,
            w d * (if 2 ≤ c ∧ c * t ∣ d then Y t c else 0)
      ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
          ∑ c ∈ Finset.Icc 1 D, ∑ t ∈ Finset.Icc 1 D,
            (if 2 ≤ c ∧ c * t ∣ d then w c * w t * w (d / (c*t)) * Y t c else 0) := by
    refine Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun c hc => Finset.sum_le_sum (fun t ht => ?_)))
    obtain ⟨hdIcc, -⟩ := Finset.mem_filter.mp hd
    have hdd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
    by_cases hcond : 2 ≤ c ∧ c * t ∣ d
    · rw [if_pos hcond, if_pos hcond]
      have hc1 : 1 ≤ c := le_trans (by norm_num) hcond.1
      have hct1 : 1 ≤ c * t := Nat.pos_of_dvd_of_pos hcond.2 hdd1
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · subst h; simp at hct1
        · exact h
      have hm1 : 1 ≤ d / (c*t) := Nat.div_pos (Nat.le_of_dvd hdd1 hcond.2) (by omega)
      have hmul := hwmul c t (d / (c*t)) hc1 ht1 hm1
      have hdeq : c * t * (d / (c * t)) = d := Nat.mul_div_cancel' hcond.2
      calc w d * Y t c = w (c * t * (d / (c * t))) * Y t c := by rw [hdeq]
        _ ≤ (w c * w t * w (d / (c * t))) * Y t c :=
            mul_le_mul_of_nonneg_right hmul (hY t c)
    · rw [if_neg hcond]; simp [hcond]
  have hC : ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
          ∑ c ∈ Finset.Icc 1 D, ∑ t ∈ Finset.Icc 1 D,
            (if 2 ≤ c ∧ c * t ∣ d then w c * w t * w (d / (c*t)) * Y t c else 0)
      = ∑ c ∈ Finset.Icc 1 D, ∑ t ∈ Finset.Icc 1 D,
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
            (if 2 ≤ c ∧ c * t ∣ d then w c * w t * w (d / (c*t)) * Y t c else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [Finset.sum_comm]
  have hcoef : ∀ c t, (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
        (if 2 ≤ c ∧ c * t ∣ d then w c * w t * w (d / (c*t)) * Y t c else 0))
      ≤ (if 2 ≤ c then w c * w t * Y t c else 0) * (∑ m ∈ Finset.Icc 1 D, w m) := by
    intro c t
    by_cases hc2 : 2 ≤ c
    · rw [if_pos hc2]
      have hsimp : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
            (if 2 ≤ c ∧ c * t ∣ d then w c * w t * w (d / (c*t)) * Y t c else 0))
          = ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
              (if c * t ∣ d then (w c * w t * Y t c) * w (d / (c*t)) else 0) := by
        refine Finset.sum_congr rfl (fun d hd => ?_)
        by_cases h : c * t ∣ d
        · rw [if_pos ⟨hc2, h⟩, if_pos h]; ring
        · rw [if_neg (fun hh => h hh.2), if_neg h]
      rw [hsimp, ← Finset.sum_filter, ← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left
      · have hinj : Set.InjOn (fun d => d / (c*t))
            ↑(((Finset.Icc 1 D).filter (fun d => d % 2 = 1)).filter (fun d => c * t ∣ d)) := by
          intro d1 hd1 d2 hd2 heq
          have h1 : c*t ∣ d1 := (Finset.mem_filter.mp hd1).2
          have h2 : c*t ∣ d2 := (Finset.mem_filter.mp hd2).2
          have heq' : d1 / (c*t) = d2 / (c*t) := by simpa using heq
          rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq']
        have hLHS : (∑ d ∈ ((Finset.Icc 1 D).filter (fun d => d % 2 = 1)).filter (fun d => c * t ∣ d),
              w (d / (c*t)))
            = ∑ m ∈ Finset.image (fun d => d / (c*t))
                (((Finset.Icc 1 D).filter (fun d => d % 2 = 1)).filter (fun d => c * t ∣ d)), w m :=
          (Finset.sum_image (s := ((Finset.Icc 1 D).filter (fun d => d % 2 = 1)).filter (fun d => c * t ∣ d))
            (g := fun d => d / (c*t)) (f := w) hinj).symm
        rw [hLHS]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m hm hmt => hw m)
        intro m hm
        rw [Finset.mem_image] at hm
        obtain ⟨d, hdT, rfl⟩ := hm
        have hdvd : c*t ∣ d := (Finset.mem_filter.mp hdT).2
        have hdIcc : d ∈ Finset.Icc 1 D := (Finset.mem_filter.mp (Finset.mem_filter.mp hdT).1).1
        obtain ⟨hd1d, hdD⟩ := Finset.mem_Icc.mp hdIcc
        rw [Finset.mem_Icc]
        exact ⟨Nat.div_pos (Nat.le_of_dvd hd1d hdvd) (Nat.pos_of_dvd_of_pos hdvd hd1d),
               le_trans (Nat.div_le_self d (c*t)) hdD⟩
      · exact mul_nonneg (mul_nonneg (hw c) (hw t)) (hY t c)
    · rw [if_neg hc2]
      have hzero : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
            (if 2 ≤ c ∧ c * t ∣ d then w c * w t * w (d / (c*t)) * Y t c else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        exact if_neg (fun h => hc2 h.1)
      rw [hzero]; simp
  have hD' : ∑ c ∈ Finset.Icc 1 D, ∑ t ∈ Finset.Icc 1 D, (if 2 ≤ c then w c * w t * Y t c else 0)
      = ∑ t ∈ Finset.Icc 1 D, ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r), w t * (w r * Y t r) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    by_cases h : 2 ≤ r
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]
  calc (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
        w d * (∑ c ∈ d.divisors.filter (fun c => 2 ≤ c), ∑ t ∈ (d / c).divisors, Y t c))
      = ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
          ∑ c ∈ Finset.Icc 1 D, ∑ t ∈ Finset.Icc 1 D,
            w d * (if 2 ≤ c ∧ c * t ∣ d then Y t c else 0) := hA
    _ ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
          ∑ c ∈ Finset.Icc 1 D, ∑ t ∈ Finset.Icc 1 D,
            (if 2 ≤ c ∧ c * t ∣ d then w c * w t * w (d / (c*t)) * Y t c else 0) := hB
    _ = ∑ c ∈ Finset.Icc 1 D, ∑ t ∈ Finset.Icc 1 D,
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
            (if 2 ≤ c ∧ c * t ∣ d then w c * w t * w (d / (c*t)) * Y t c else 0) := hC
    _ ≤ ∑ c ∈ Finset.Icc 1 D, ∑ t ∈ Finset.Icc 1 D,
          (if 2 ≤ c then w c * w t * Y t c else 0) * (∑ m ∈ Finset.Icc 1 D, w m) :=
        Finset.sum_le_sum (fun c hc => Finset.sum_le_sum (fun t ht => hcoef c t))
    _ = (∑ c ∈ Finset.Icc 1 D, ∑ t ∈ Finset.Icc 1 D, (if 2 ≤ c then w c * w t * Y t c else 0))
          * (∑ m ∈ Finset.Icc 1 D, w m) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun c hc => ?_)
        rw [Finset.sum_mul]
    _ = (∑ m ∈ Finset.Icc 1 D, w m)
          * (∑ t ∈ Finset.Icc 1 D, ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r), w t * (w r * Y t r)) := by
        rw [hD']; exact mul_comm _ _

/-- **Möbius bound with an arbitrary divisibility proof.** -/
theorem moebius_bound_div (x M Y r d : ℕ) [NeZero d] (h : r ∣ d) (ψ : DirichletCharacter ℂ r) :
    ‖bProdCharSum x M Y d (DirichletCharacter.changeLevel h ψ)‖
      ≤ ∑ t ∈ (d / r).divisors, ‖bProdCharSumDiv x M Y r t ψ‖ := by
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      exact absurd (Nat.zero_dvd.mp h) (NeZero.ne d)
    · exact hpos
  obtain ⟨e, he⟩ := h
  subst he
  rw [Nat.mul_div_right e hr]
  exact BLodMobiusBound x M Y r e ψ

/-- Summing the Möbius bound over the primitive characters of level `r`. -/
theorem psi_sum_bound (x M Y d r : ℕ) [NeZero d] (hrd : r ∣ d) :
    (∑ ψ : {ψ' : DirichletCharacter ℂ r // ψ'.IsPrimitive},
        ‖bProdCharSum x M Y d (DirichletCharacter.changeLevel hrd ψ.1)‖)
      ≤ ∑ t ∈ (d / r).divisors, bProdCharSumDivSum x M Y t r := by
  calc (∑ ψ : {ψ' : DirichletCharacter ℂ r // ψ'.IsPrimitive},
        ‖bProdCharSum x M Y d (DirichletCharacter.changeLevel hrd ψ.1)‖)
      ≤ ∑ ψ : {ψ' : DirichletCharacter ℂ r // ψ'.IsPrimitive},
          ∑ t ∈ (d / r).divisors, ‖bProdCharSumDiv x M Y r t ψ.1‖ :=
        Finset.sum_le_sum (fun ψ _ => moebius_bound_div x M Y r d hrd ψ.1)
    _ = ∑ t ∈ (d / r).divisors, ∑ ψ : {ψ' : DirichletCharacter ℂ r // ψ'.IsPrimitive},
          ‖bProdCharSumDiv x M Y r t ψ.1‖ := Finset.sum_comm
    _ = ∑ t ∈ (d / r).divisors, bProdCharSumDivSum x M Y t r := by
        refine Finset.sum_congr rfl (fun t ht => ?_)
        rw [bProdCharSumDivSum]
        simp only [bProdCharSumDiv]
        exact (Finset.sum_subtype (Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive))
          (fun ψ => by simp) (fun ψ => ‖∑ n ∈ (bProdSet x M Y).filter (fun n => t ∣ n), ψ ((n:ℕ) : ZMod r)‖)).symm

/-- An `attach`-filtered sum is the corresponding filtered sum. -/
theorem attach_filter_sum_eq (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (G : ℕ → ℝ) :
    (∑ c ∈ s.attach.filter (fun c => p c.1), G c.1) = ∑ c ∈ s.filter p, G c := by
  conv_lhs => rw [Finset.sum_filter]
  change (∑ c ∈ s.attach, (fun n => if p n then G n else 0) c.1) = ∑ c ∈ s.filter p, G c
  rw [Finset.sum_attach (s := s) (f := fun n => if p n then G n else 0)]
  rw [← Finset.sum_filter]

attribute [local instance] Classical.propDecidable
theorem BLodMobiusReduction2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (x M Y D : ℕ), 2 ≤ D →
      (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
          ((3:ℝ)^(d.primeFactors.card) / (Nat.totient d : ℝ)) *
            (∑ c ∈ (d.divisors.attach.filter (fun c => 2 ≤ c.1)),
              ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
                ‖bProdCharSum x M Y d
                  (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖))
        ≤ C * (Real.log (D:ℝ))^3 *
          (∑ t ∈ Finset.Icc 1 D, ((3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ)) *
            ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r),
              ((3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) *
              bProdCharSumDivSum x M Y t r) := by
  obtain ⟨C1, hC1pos, hC1⟩ := sumThreePowInvTotientBound
  refine ⟨C1, hC1pos, fun x M Y D hD => ?_⟩
  change (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
        lvlW d * (∑ c ∈ (d.divisors.attach.filter (fun c => 2 ≤ c.1)),
              ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
                ‖bProdCharSum x M Y d
                  (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖))
        ≤ C1 * (Real.log (D:ℝ))^3 *
          (∑ t ∈ Finset.Icc 1 D, lvlW t *
            ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r),
              lvlW r * bProdCharSumDivSum x M Y t r)
  have hstep1 : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
        lvlW d * (∑ c ∈ (d.divisors.attach.filter (fun c => 2 ≤ c.1)),
              ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
                ‖bProdCharSum x M Y d
                  (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖))
      ≤ (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
        lvlW d * (∑ c ∈ d.divisors.filter (fun c => 2 ≤ c),
          ∑ t ∈ (d / c).divisors, bProdCharSumDivSum x M Y t c)) := by
    refine Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left ?_ (lvlW_nonneg d))
    obtain ⟨hdIcc, -⟩ := Finset.mem_filter.mp hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
    haveI : NeZero d := ⟨by omega⟩
    calc (∑ c ∈ (d.divisors.attach.filter (fun c => 2 ≤ c.1)),
          ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
            ‖bProdCharSum x M Y d (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖)
        ≤ ∑ c ∈ (d.divisors.attach.filter (fun c => 2 ≤ c.1)),
            ∑ t ∈ (d / c.1).divisors, bProdCharSumDivSum x M Y t c.1 :=
          Finset.sum_le_sum (fun c hc => psi_sum_bound x M Y d c.1 (Nat.mem_divisors.mp c.2).1)
      _ = ∑ c ∈ d.divisors.filter (fun c => 2 ≤ c),
            ∑ t ∈ (d / c).divisors, bProdCharSumDivSum x M Y t c :=
          attach_filter_sum_eq d.divisors (fun c => 2 ≤ c)
            (fun r => ∑ t ∈ (d / r).divisors, bProdCharSumDivSum x M Y t r)
  have hmain := reindex_bound D lvlW (fun t r => bProdCharSumDivSum x M Y t r)
    lvlW_nonneg (fun t r => bProdCharSumDivSum_nonneg x M Y t r) lvlW_mul_le
  have hRsum : (∑ t ∈ Finset.Icc 1 D, ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r),
        lvlW t * (lvlW r * bProdCharSumDivSum x M Y t r))
      = (∑ t ∈ Finset.Icc 1 D, lvlW t *
          ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r),
            lvlW r * bProdCharSumDivSum x M Y t r) := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.mul_sum]
  have hlog : (∑ m ∈ Finset.Icc 1 D, lvlW m) ≤ C1 * (Real.log (D:ℝ))^3 := by
    simpa only [lvlW] using hC1 D hD
  have hRnn : 0 ≤ (∑ t ∈ Finset.Icc 1 D, lvlW t *
      ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r),
        lvlW r * bProdCharSumDivSum x M Y t r) :=
    Finset.sum_nonneg (fun t ht => mul_nonneg (lvlW_nonneg t)
      (Finset.sum_nonneg (fun r hr => mul_nonneg (lvlW_nonneg r)
        (bProdCharSumDivSum_nonneg x M Y t r))))
  calc (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
        lvlW d * (∑ c ∈ (d.divisors.attach.filter (fun c => 2 ≤ c.1)),
              ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
                ‖bProdCharSum x M Y d
                  (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖))
      ≤ (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
        lvlW d * (∑ c ∈ d.divisors.filter (fun c => 2 ≤ c),
          ∑ t ∈ (d / c).divisors, bProdCharSumDivSum x M Y t c)) := hstep1
    _ ≤ (∑ m ∈ Finset.Icc 1 D, lvlW m) *
        (∑ t ∈ Finset.Icc 1 D, ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r),
          lvlW t * (lvlW r * bProdCharSumDivSum x M Y t r)) := hmain
    _ = (∑ m ∈ Finset.Icc 1 D, lvlW m) *
        (∑ t ∈ Finset.Icc 1 D, lvlW t *
          ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r),
            lvlW r * bProdCharSumDivSum x M Y t r) := by rw [hRsum]
    _ ≤ (C1 * (Real.log (D:ℝ))^3) *
        (∑ t ∈ Finset.Icc 1 D, lvlW t *
          ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r),
            lvlW r * bProdCharSumDivSum x M Y t r) :=
        mul_le_mul_of_nonneg_right hlog hRnn
    _ = C1 * (Real.log (D:ℝ))^3 *
        (∑ t ∈ Finset.Icc 1 D, lvlW t *
          ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r),
            lvlW r * bProdCharSumDivSum x M Y t r) := by ring

end Work.NumberTheory.Chen.BTermCount
