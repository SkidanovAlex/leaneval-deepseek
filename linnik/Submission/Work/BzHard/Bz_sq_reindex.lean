import Mathlib
import Submission.Work.LinnikAreas.Density4.LamRDefs
import Submission.Work.BzHard.moebius_param_mul
import Submission.Work.BzHard.moebius_param_vanish

namespace Work.BzHard

open Finset

noncomputable section

/-- **`Finset.sigma` associativity.**  A triple nested sum is a sum over the corresponding
doubly nested sigma set. -/
lemma sum_sigma_sigma {M : Type*} [AddCommMonoid M] {α : Type*} {β : α → Type*}
    {γ : (a : α) → β a → Type*} (s : Finset α) (t : ∀ a, Finset (β a))
    (u : ∀ a b, Finset (γ a b)) (f : ∀ a b, γ a b → M) :
    (∑ a ∈ s, ∑ b ∈ t a, ∑ c ∈ u a b, f a b c)
      = ∑ x ∈ s.sigma (fun a => (t a).sigma (fun b => u a b)), f x.1 x.2.1 x.2.2 := by
  have h1 : ∀ a, (∑ b ∈ t a, ∑ c ∈ u a b, f a b c)
      = ∑ y ∈ (t a).sigma (fun b => u a b), f a y.1 y.2 := fun a =>
    Finset.sum_sigma' (t a) (fun b => u a b) (fun b c => f a b c)
  calc (∑ a ∈ s, ∑ b ∈ t a, ∑ c ∈ u a b, f a b c)
      = ∑ a ∈ s, ∑ y ∈ (t a).sigma (fun b => u a b), f a y.1 y.2 :=
        Finset.sum_congr rfl (fun a _ => h1 a)
    _ = ∑ x ∈ s.sigma (fun a => (t a).sigma (fun b => u a b)), f x.1 x.2.1 x.2.2 :=
        Finset.sum_sigma' s (fun a => (t a).sigma (fun b => u a b)) (fun a y => f a y.1 y.2)

/-- The `B_z` square sum with the restricted index set, written as a flattened sigma sum. -/
lemma Bz_LHS_flat {M : Type*} [AddCommMonoid M] (z N : ℕ) (F : ℕ → ℕ → M) :
    (∑ n ∈ Finset.Icc 2 N, ∑ d ∈ (n.divisors.filter (fun d => z < d)),
        ∑ e ∈ ((n.divisors.filter (fun e => z < e)).filter
            (fun e => Nat.Coprime (Nat.gcd d e) ((e / Nat.gcd d e) * (d / Nat.gcd d e)))),
          F d e)
      = ∑ x ∈ ((Finset.Icc 2 N).sigma (fun n => (n.divisors.filter (fun d => z < d)).sigma
            (fun d => (n.divisors.filter (fun e => z < e)).filter
              (fun e => Nat.Coprime (Nat.gcd d e) ((e / Nat.gcd d e) * (d / Nat.gcd d e)))))),
          F x.2.1 x.2.2 :=
  sum_sigma_sigma _ _ _ _

/-- The reindexed right hand side, written as a flattened sigma sum. -/
lemma Bz_RHS_flat {M : Type*} [AddCommMonoid M] (z N : ℕ) (F : ℕ → ℕ → M) :
    (∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
        (if Nat.Coprime r t then
          ∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
              (fun m => Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r),
            F (m * t) (m * r)
        else 0))
      = ∑ x ∈ (Finset.Icc 1 N).sigma (fun q => (Finset.Icc 1 N).sigma (fun r =>
            ((Finset.Icc 1 N).filter (fun t => Nat.Coprime r t)).sigma (fun t =>
              (Finset.Icc 1 (N / (q * r * t))).filter
                (fun m => Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r)))),
          F (x.2.2.2 * x.2.2.1) (x.2.2.2 * x.2.1) := by
  have h1 : ∀ q ∈ Finset.Icc 1 N, ∀ r ∈ Finset.Icc 1 N,
      (∑ t ∈ Finset.Icc 1 N, (if Nat.Coprime r t then
          ∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
              (fun m => Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r),
            F (m * t) (m * r)
        else 0))
      = ∑ t ∈ (Finset.Icc 1 N).filter (fun t => Nat.Coprime r t),
          ∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
              (fun m => Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r),
            F (m * t) (m * r) := by
    intro q hq r hr
    exact (Finset.sum_filter (s := Finset.Icc 1 N) (p := fun t => Nat.Coprime r t)
      (f := fun t => ∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
              (fun m => Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r), F (m * t) (m * r))).symm
  rw [Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun r hr => h1 q hq r hr))]
  have h2 : ∀ q, (∑ r ∈ Finset.Icc 1 N,
        ∑ t ∈ (Finset.Icc 1 N).filter (fun t => Nat.Coprime r t),
          ∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
              (fun m => Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r),
            F (m * t) (m * r))
      = ∑ y ∈ (Finset.Icc 1 N).sigma (fun r =>
            ((Finset.Icc 1 N).filter (fun t => Nat.Coprime r t)).sigma (fun t =>
              (Finset.Icc 1 (N / (q * r * t))).filter
                (fun m => Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r))),
          F (y.2.2 * y.2.1) (y.2.2 * y.1) := fun q => sum_sigma_sigma _ _ _ _
  rw [Finset.sum_congr rfl (fun q _ => h2 q)]
  exact Finset.sum_sigma' _ _ _

/-- **The combinatorial reindexing.**  Summing an arbitrary function of the pair of divisors
`(d, e)` (with `e` restricted so that `gcd d e` is coprime to the cofactors) over `2 ≤ n ≤ N`
and `d, e ∣ n`, `z < d, z < e` is the same as summing over the parametrisation
`d = m·t`, `e = m·r` with `(r,t) = 1`, `(m, rt) = 1`. -/
lemma Bz_reindex_flat {M : Type*} [AddCommMonoid M] (z N : ℕ) (hz : 1 ≤ z) (F : ℕ → ℕ → M) :
    (∑ x ∈ ((Finset.Icc 2 N).sigma (fun n => (n.divisors.filter (fun d => z < d)).sigma
            (fun d => (n.divisors.filter (fun e => z < e)).filter
              (fun e => Nat.Coprime (Nat.gcd d e) ((e / Nat.gcd d e) * (d / Nat.gcd d e)))))),
          F x.2.1 x.2.2)
      = ∑ x ∈ (Finset.Icc 1 N).sigma (fun q => (Finset.Icc 1 N).sigma (fun r =>
            ((Finset.Icc 1 N).filter (fun t => Nat.Coprime r t)).sigma (fun t =>
              (Finset.Icc 1 (N / (q * r * t))).filter
                (fun m => Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r)))),
          F (x.2.2.2 * x.2.2.1) (x.2.2.2 * x.2.1) := by
  classical
  refine Finset.sum_bij'
    (fun x _ => ⟨x.1 / ((x.2.2 / Nat.gcd x.2.1 x.2.2) * (x.2.1 / Nat.gcd x.2.1 x.2.2) * Nat.gcd x.2.1 x.2.2),
        ⟨x.2.2 / Nat.gcd x.2.1 x.2.2, ⟨x.2.1 / Nat.gcd x.2.1 x.2.2, Nat.gcd x.2.1 x.2.2⟩⟩⟩)
    (fun y _ => ⟨y.1 * (y.2.1 * y.2.2.1) * y.2.2.2, ⟨y.2.2.2 * y.2.2.1, y.2.2.2 * y.2.1⟩⟩)
    ?_ ?_ ?_ ?_ ?_
  · -- the parametrisation of a divisor pair lands in the index set
    rintro ⟨n, d, e⟩ ha
    obtain ⟨hn, ha2⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hd, he⟩ := Finset.mem_sigma.mp ha2
    simp only [] at hn hd he
    obtain ⟨hddvd, hdz⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hddvd
    obtain ⟨heD, hcond⟩ := Finset.mem_filter.mp he
    obtain ⟨hevd, hez⟩ := Finset.mem_filter.mp heD
    obtain ⟨hedvd, _⟩ := Nat.mem_divisors.mp hevd
    obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hepar : 0 < e := Nat.pos_of_dvd_of_pos hedvd (by omega)
    have hgpos : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_right d hepar
    set m := Nat.gcd d e with hm
    set r := e / m with hr
    set t := d / m with ht
    have hmpos : 0 < m := by rw [hm]; exact hgpos
    have hmt : m * t = d := by rw [hm, ht]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
    have hmr : m * r = e := by rw [hm, hr]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
    have hcop : Nat.Coprime r t := by
      rw [hr, ht, hm]
      exact (Nat.coprime_div_gcd_div_gcd hgpos).symm
    have hlcm : Nat.lcm d e = r * t * m := by
      rw [← hmt, ← hmr, Nat.lcm_mul_left, hcop.symm.lcm_eq_mul]
      ring
    have hrtmdvd : r * t * m ∣ n := by
      have h1 : Nat.lcm d e ∣ n := Nat.lcm_dvd hdvd hedvd
      rwa [hlcm] at h1
    have hq : n / (r * t * m) * (r * t * m) = n := Nat.div_mul_cancel hrtmdvd
    have hrpos : 0 < r := by
      rw [hr, hm]
      exact Nat.div_pos (Nat.le_of_dvd hepar (Nat.gcd_dvd_right d e)) hgpos
    have htpos : 0 < t := by
      rw [ht, hm]
      exact Nat.div_pos (Nat.le_of_dvd hdpos (Nat.gcd_dvd_left d e)) hgpos
    have hqpos : 0 < n / (r * t * m) := Nat.pos_iff_ne_zero.mpr (by
      intro h0; rw [h0, zero_mul] at hq; omega)
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · exact Nat.one_le_iff_ne_zero.mpr hqpos.ne'
    · calc n / (r * t * m) ≤ n / (r * t * m) * (r * t * m) := Nat.le_mul_of_pos_right _ (by positivity)
        _ = n := hq
        _ ≤ N := hnN
    · exact Nat.one_le_iff_ne_zero.mpr hrpos.ne'
    · calc r ≤ r * m := Nat.le_mul_of_pos_right _ hmpos
        _ = m * r := by ring
        _ = e := hmr
        _ ≤ n := Nat.divisor_le hevd
        _ ≤ N := hnN
    · exact Nat.one_le_iff_ne_zero.mpr htpos.ne'
    · calc t ≤ t * m := Nat.le_mul_of_pos_right _ hmpos
        _ = m * t := by ring
        _ = d := hmt
        _ ≤ n := Nat.divisor_le hddvd
        _ ≤ N := hnN
    · exact hcop
    · exact hmpos
    · rw [Nat.le_div_iff_mul_le (by positivity : 0 < n / (r * t * m) * r * t)]
      have h1 : m * (n / (r * t * m) * r * t) = n := by
        calc m * (n / (r * t * m) * r * t) = n / (r * t * m) * (r * t * m) := by ring
          _ = n := hq
      rw [h1]
      exact hnN
    · exact hcond
    · rw [hmt]; exact hdz
    · rw [hmr]; exact hez
  · -- inverse map: the parametrised quadruple gives back a divisor pair
    rintro ⟨q, r, t, m⟩ hy
    obtain ⟨hq, hy2⟩ := Finset.mem_sigma.mp hy
    obtain ⟨hr, hy3⟩ := Finset.mem_sigma.mp hy2
    obtain ⟨ht, hm⟩ := Finset.mem_sigma.mp hy3
    simp only [] at hq hr ht hm
    obtain ⟨htIcc, hcoprt⟩ := Finset.mem_filter.mp ht
    obtain ⟨hmIcc, hmcond⟩ := Finset.mem_filter.mp hm
    obtain ⟨hq1, hqN⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hr1, hrN⟩ := Finset.mem_Icc.mp hr
    obtain ⟨ht1, htN⟩ := Finset.mem_Icc.mp htIcc
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hmIcc
    obtain ⟨hcm, hmtz, hmrz⟩ := hmcond
    have hq0 : 0 < q := by omega
    have hr0 : 0 < r := by omega
    have ht0 : 0 < t := by omega
    have hm0 : 0 < m := by omega
    have hst : 0 < q * r * t := by positivity
    have hg : Nat.gcd (m * t) (m * r) = m := by
      rw [Nat.gcd_mul_left, hcoprt.symm.gcd_eq_one, mul_one]
    have hdr : (m * r) / m = r := Nat.mul_div_right r hm0
    have hdt : (m * t) / m = t := Nat.mul_div_right t hm0
    have hmul : m * (q * r * t) ≤ N := (Nat.le_div_iff_mul_le hst).mp hmN
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · calc 2 ≤ m * t := by omega
        _ ≤ (q * r) * (m * t) := Nat.le_mul_of_pos_left _ (by positivity)
        _ = q * (r * t) * m := by ring
    · rw [show q * (r * t) * m = m * (q * r * t) by ring]; exact hmul
    · exact ⟨q * r, by ring⟩
    · positivity
    · exact hmtz
    · exact ⟨q * t, by ring⟩
    · positivity
    · exact hmrz
    · rw [hg, hdr, hdt]; exact hcm
  · -- the two maps are inverse on the left
    rintro ⟨n, d, e⟩ ha
    obtain ⟨hn, ha2⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hd, he⟩ := Finset.mem_sigma.mp ha2
    simp only [] at hn hd he
    obtain ⟨hddvd, _⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hddvd
    obtain ⟨heD, _⟩ := Finset.mem_filter.mp he
    obtain ⟨hevd, _⟩ := Finset.mem_filter.mp heD
    obtain ⟨hedvd, _⟩ := Nat.mem_divisors.mp hevd
    have hepar : 0 < e := Nat.pos_of_dvd_of_pos hedvd (by omega)
    have hgpos : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_right d hepar
    set m := Nat.gcd d e with hm
    set r := e / m with hr
    set t := d / m with ht
    have hmt : m * t = d := by rw [hm, ht]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
    have hmr : m * r = e := by rw [hm, hr]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
    have hcop : Nat.Coprime r t := by
      rw [hr, ht, hm]
      exact (Nat.coprime_div_gcd_div_gcd hgpos).symm
    have hlcm : Nat.lcm d e = r * t * m := by
      rw [← hmt, ← hmr, Nat.lcm_mul_left, hcop.symm.lcm_eq_mul]
      ring
    have hrtmdvd : r * t * m ∣ n := by
      have h1 : Nat.lcm d e ∣ n := Nat.lcm_dvd hdvd hedvd
      rwa [hlcm] at h1
    have hq : n / (r * t * m) * (r * t * m) = n := Nat.div_mul_cancel hrtmdvd
    simp only [Sigma.mk.injEq, heq_eq_eq]
    refine ⟨?_, hmt, hmr⟩
    rw [show n / (r * t * m) * (r * t) * m = n / (r * t * m) * (r * t * m) by ring]
    exact hq
  · -- the two maps are inverse on the right
    rintro ⟨q, r, t, m⟩ hy
    obtain ⟨hq, hy2⟩ := Finset.mem_sigma.mp hy
    obtain ⟨hr, hy3⟩ := Finset.mem_sigma.mp hy2
    obtain ⟨ht, hm⟩ := Finset.mem_sigma.mp hy3
    simp only [] at hq hr ht hm
    obtain ⟨htIcc, hcoprt⟩ := Finset.mem_filter.mp ht
    obtain ⟨hmIcc, hmcond⟩ := Finset.mem_filter.mp hm
    obtain ⟨hq1, hqN⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hr1, hrN⟩ := Finset.mem_Icc.mp hr
    obtain ⟨ht1, htN⟩ := Finset.mem_Icc.mp htIcc
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hmIcc
    have hq0 : 0 < q := by omega
    have hr0 : 0 < r := by omega
    have ht0 : 0 < t := by omega
    have hm0 : 0 < m := by omega
    have hst : 0 < r * t * m := by positivity
    have hg : Nat.gcd (m * t) (m * r) = m := by
      rw [Nat.gcd_mul_left, hcoprt.symm.gcd_eq_one, mul_one]
    have hdr : (m * r) / m = r := Nat.mul_div_right r hm0
    have hdt : (m * t) / m = t := Nat.mul_div_right t hm0
    have hqq : q * (r * t) * m / (r * t * m) = q := by
      rw [show q * (r * t) * m = (r * t * m) * q by ring, Nat.mul_div_right _ hst]
    rw [hg, hdr, hdt, hqq]
  · -- the summands agree: `d = m·t`, `e = m·r`
    rintro ⟨n, d, e⟩ ha
    obtain ⟨hn, ha2⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hd, _⟩ := Finset.mem_sigma.mp ha2
    simp only [] at hd
    obtain ⟨hddvd, _⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hddvd
    set m := Nat.gcd d e with hm
    set t := d / m with ht
    set r := e / m with hr
    have hmt : m * t = d := by rw [hm, ht]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
    have hmr : m * r = e := by rw [hm, hr]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
    rw [← hmt, ← hmr]

/-- **The reindexing identity** (nested form), for an arbitrary summand `F`. -/
lemma Bz_reindex_aux {M : Type*} [AddCommMonoid M] (z N : ℕ) (hz : 1 ≤ z) (F : ℕ → ℕ → M) :
    (∑ n ∈ Finset.Icc 2 N, ∑ d ∈ (n.divisors.filter (fun d => z < d)),
        ∑ e ∈ ((n.divisors.filter (fun e => z < e)).filter
            (fun e => Nat.Coprime (Nat.gcd d e) ((e / Nat.gcd d e) * (d / Nat.gcd d e)))),
          F d e)
      = ∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
          (if Nat.Coprime r t then
            ∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
                (fun m => Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r),
              F (m * t) (m * r)
          else 0) := by
  rw [Bz_LHS_flat z N F, Bz_reindex_flat z N hz F, ← Bz_RHS_flat z N F]

/-- Pointwise comparison of the two summands, using multiplicativity of `μ`. -/
lemma Bz_weight_pt {z m r t : ℕ} (hcop : Nat.Coprime m (r * t)) :
    ((ArithmeticFunction.moebius (m * t) : ℝ) * Real.log (((m * t : ℕ) : ℝ) / (z : ℝ))) *
        ((ArithmeticFunction.moebius (m * r) : ℝ) * Real.log (((m * r : ℕ) : ℝ) / (z : ℝ)))
      = (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
          (((ArithmeticFunction.moebius m : ℝ) ^ 2) *
            Real.log ((m : ℝ) * (t : ℝ) / (z : ℝ)) *
            Real.log ((m : ℝ) * (r : ℝ) / (z : ℝ))) := by
  have h1 := moebius_param_mul hcop
  have e1 : (((m * t : ℕ) : ℝ) / (z : ℝ)) = ((m : ℝ) * (t : ℝ) / (z : ℝ)) := by
    push_cast; ring
  have e2 : (((m * r : ℕ) : ℝ) / (z : ℝ)) = ((m : ℝ) * (r : ℝ) / (z : ℝ)) := by
    push_cast; ring
  rw [e1, e2]
  calc ((ArithmeticFunction.moebius (m * t) : ℝ) * Real.log ((m : ℝ) * (t : ℝ) / (z : ℝ))) *
        ((ArithmeticFunction.moebius (m * r) : ℝ) * Real.log ((m : ℝ) * (r : ℝ) / (z : ℝ)))
      = ((ArithmeticFunction.moebius (m * t) : ℝ) * (ArithmeticFunction.moebius (m * r) : ℝ)) *
          (Real.log ((m : ℝ) * (t : ℝ) / (z : ℝ)) *
            Real.log ((m : ℝ) * (r : ℝ) / (z : ℝ))) := by ring
    _ = ((ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
          (ArithmeticFunction.moebius m : ℝ) ^ 2) *
          (Real.log ((m : ℝ) * (t : ℝ) / (z : ℝ)) *
            Real.log ((m : ℝ) * (r : ℝ) / (z : ℝ))) := by rw [h1]
    _ = (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
          (((ArithmeticFunction.moebius m : ℝ) ^ 2) *
            Real.log ((m : ℝ) * (t : ℝ) / (z : ℝ)) *
            Real.log ((m : ℝ) * (r : ℝ) / (z : ℝ))) := by ring

/-- Expansion of the square of `B_z`. -/
lemma Bz_sq_expand (z N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, (Work.LinnikAreas.Density4.Bz z n) ^ 2)
      = ∑ n ∈ Finset.Icc 2 N, ∑ d ∈ (n.divisors.filter (fun d => z < d)),
          ∑ e ∈ (n.divisors.filter (fun e => z < e)),
            ((ArithmeticFunction.moebius d : ℝ) * Real.log ((d : ℝ) / (z : ℝ))) *
              ((ArithmeticFunction.moebius e : ℝ) * Real.log ((e : ℝ) / (z : ℝ))) := by
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [pow_two, Work.LinnikAreas.Density4.Bz, Finset.sum_mul_sum]

/-- The restriction `(gcd d e, cofactors) = 1` in the index set may be added: the terms
outside it vanish because the corresponding Möbius factor is zero. -/
lemma Bz_cond_expand (z N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, ∑ d ∈ (n.divisors.filter (fun d => z < d)),
        ∑ e ∈ ((n.divisors.filter (fun e => z < e)).filter
            (fun e => Nat.Coprime (Nat.gcd d e) ((e / Nat.gcd d e) * (d / Nat.gcd d e)))),
          ((ArithmeticFunction.moebius d : ℝ) * Real.log ((d : ℝ) / (z : ℝ))) *
            ((ArithmeticFunction.moebius e : ℝ) * Real.log ((e : ℝ) / (z : ℝ))))
      = ∑ n ∈ Finset.Icc 2 N, ∑ d ∈ (n.divisors.filter (fun d => z < d)),
          ∑ e ∈ (n.divisors.filter (fun e => z < e)),
            ((ArithmeticFunction.moebius d : ℝ) * Real.log ((d : ℝ) / (z : ℝ))) *
              ((ArithmeticFunction.moebius e : ℝ) * Real.log ((e : ℝ) / (z : ℝ))) := by
  refine Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun d hd => ?_))
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro e he hne
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hdvd : d ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
  have hevd : e ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos hevd (by omega)
  have hnc : ¬ Nat.Coprime (Nat.gcd d e) ((e / Nat.gcd d e) * (d / Nat.gcd d e)) := by
    intro hc
    exact hne (Finset.mem_filter.mpr ⟨he, hc⟩)
  rcases moebius_param_vanish hd1 he1 hnc with h0 | h0
  · rw [h0]; ring
  · rw [h0]; ring

/-- **Exact reindexing of the `B_z` square-sum.**  With `B_z(n) = ∑_{z < d ∣ n} μ d · log(d/z)`
(`LamRDefs`), and for `1 ≤ z`, any `N`:

`∑_{2 ≤ n ≤ N} B_z(n)² = ∑_{q,r,t ≤ N} [r ⟂ t] μ r · μ t · ∑_{m ≤ N/(qrt), m ⟂ rt, mt > z, mr > z} μ² m · log(mt/z) · log(mr/z)`.

Reason: expand the square over pairs of divisors `d, e > z` of `n`, and use the bijection
`d = t·m`, `e = r·m`, `n = q·r·t·m` (`q` free), coming from `q = gcd` of the complementary
divisors `n/d, n/e`: for `d,e | n` the complementary divisors are `n/d = q r`, `n/e = q t` with
`q = gcd(n/d, n/e)`, `(r,t) = 1` and `m = n/(qrt)`.  One checks `μ d · μ e = μ(r)μ(t)μ²(m)` exactly
when `(m, rt) = 1` (which holds automatically for non-zero terms), and `d > z ⟺ mt > z`,
`e > z ⟺ mr > z`.-/
theorem Bz_sq_reindex (z N : ℕ) (hz : 1 ≤ z) :
    (∑ n ∈ Finset.Icc 2 N, (Work.LinnikAreas.Density4.Bz z n) ^ 2)
      = ∑ q ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N, ∑ t ∈ Finset.Icc 1 N,
          (if Nat.Coprime r t then
            (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
              (∑ m ∈ (Finset.Icc 1 (N / (q * r * t))).filter
                  (fun m => Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r),
                ((ArithmeticFunction.moebius m : ℝ) ^ 2) *
                  Real.log ((m : ℝ) * (t : ℝ) / (z : ℝ)) *
                  Real.log ((m : ℝ) * (r : ℝ) / (z : ℝ)))
          else 0) := by
  rw [Bz_sq_expand, ← Bz_cond_expand]
  rw [Bz_reindex_aux z N hz
    (fun d e => ((ArithmeticFunction.moebius d : ℝ) * Real.log ((d : ℝ) / (z : ℝ))) *
      ((ArithmeticFunction.moebius e : ℝ) * Real.log ((e : ℝ) / (z : ℝ))))]
  refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun r _ =>
    Finset.sum_congr rfl (fun t _ => ?_)))
  by_cases h : Nat.Coprime r t
  · rw [if_pos h, if_pos h]
    rw [Finset.mul_sum (s := (Finset.Icc 1 (N / (q * r * t))).filter
            (fun m => Nat.Coprime m (r * t) ∧ z < m * t ∧ z < m * r))
          (f := fun m => ((ArithmeticFunction.moebius m : ℝ) ^ 2) *
                  Real.log ((m : ℝ) * (t : ℝ) / (z : ℝ)) *
                  Real.log ((m : ℝ) * (r : ℝ) / (z : ℝ)))]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    exact Bz_weight_pt (Finset.mem_filter.mp hm).2.1
  · rw [if_neg h, if_neg h]

end

end Work.BzHard
