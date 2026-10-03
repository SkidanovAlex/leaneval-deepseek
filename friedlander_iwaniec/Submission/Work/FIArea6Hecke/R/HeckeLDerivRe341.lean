/-
# `Submission.Work.FIArea6Hecke.R.HeckeLDerivRe341`

**The `(3,4,1)` inequality for the logarithmic derivative of the Hecke `L`-function of `ℚ(i)`.**

For every strict character `χ` mod `4d` (`d ≥ 1`), every weight `m : ℤ` and every `σ > 1`, `t : ℝ`,

  `3·Re(-L'/L)(σ, L(·,1)) + 4·Re(-L'/L)(σ+it, L(·,ψ)) + Re(-L'/L)(σ+2it, L(·,ψ²)) ≥ 0`,

where `L(·,1)` is the principal Hecke `L`-series `heckeLSeries (principalStrict d) 0`,
`L(·,ψ) = heckeLSeries χ m`, and `L(·,ψ²) = heckeLSeries (χ·χ) (2m)`.

This is the classical de la Vallée Poussin input to the zero-free region (16.20) of *FI*: it is
proved, exactly as in the paper, by the Euler product `L = ∏_p F_p` together with the elementary
inequality `3 + 4 cos θ + cos 2θ = 2(1+cos θ)² ≥ 0` applied term by term to `(log F_p)'`.

The proof is assembled from
* `HeckeLSeriesLogDerivEuler` — `(log L)' = Σ_p (log F_p)'` (the Euler product, differentiated),
* `LocalSplit341` / `LocalInert341` — the local per-prime `(3,4,1)` bound at split and inert primes,
* `LocalSplit341`'s helpers in `HeckeLDerivDefs` (`three_four_one_aux`, `local341_nonneg`).
-/
import Mathlib
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea6Hecke.R.HeckeLDerivDefs
import Submission.Work.FIArea6Hecke.R.LocalSplit341
import Submission.Work.FIArea6Hecke.R.LocalInert341
import Submission.Work.FIArea6Hecke.R.HeckeLSeriesLogDerivEuler
import Submission.Work.FIArea6Hecke.R.hecke_three_four_one
import Submission.Work.FIArea5.S16Hecke.splitPrimaryClass
import Submission.Work.FIArea5.S16Hecke.inertPrimaryClass

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open scoped BigOperators Topology

noncomputable section

/-! ## Elementary facts about conjugation, `ψ`, and the trivial local factors -/

lemma fourDZFR_star (d : ℕ) : star (fourDZFR d) = fourDZFR d := by
  rw [fourDZFR]; ext <;> simp

lemma gnorm_star_eq (z : GaussianInt) : Work.FIPlan.gnorm (star z) = Work.FIPlan.gnorm z := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_conj]

lemma isUnitMod4d_star_iff (d : ℕ) (z : GaussianInt) :
    Work.FIArea5.S16Hecke.IsUnitMod4d d (star z) ↔
      Work.FIArea5.S16Hecke.IsUnitMod4d d z := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨c, hc⟩ := hw
    refine ⟨star w, star c, ?_⟩
    have h2 : z * star w - 1 = star (star z * w - 1) := by
      rw [star_sub, star_mul, star_one, star_star]; ring
    rw [h2, hc, star_mul, fourDZFR_star]; ring
  · rintro ⟨w, hw⟩
    obtain ⟨c, hc⟩ := hw
    refine ⟨star w, star c, ?_⟩
    have h2 : star z * star w - 1 = star (z * w - 1) := by
      rw [star_sub, star_mul, star_one]; ring
    rw [h2, hc, star_mul, fourDZFR_star]; ring

/-- `ψ(χ·χ, 2m, z) = ψ(χ, m, z)²`. -/
lemma psi_sq (chi : GaussianInt → ℂ) (m : ℤ) (z : GaussianInt) :
    Work.FIArea5.S16Hecke.psi (fun w => chi w * chi w) (2 * m) z
      = Work.FIArea5.S16Hecke.psi chi m z * Work.FIArea5.S16Hecke.psi chi m z := by
  rw [Work.FIArea5.S16Hecke.psi, Work.FIArea5.S16Hecke.psi,
    show (2 : ℤ) * m = m * 2 from by ring, zpow_mul, zpow_two]
  ring

/-- If `λ(p^e) = 0` for all `e ≥ 1`, then the local Euler factor is identically `1`. -/
lemma heckeFp_eq_one (p : Nat.Primes) (chi : GaussianInt → ℂ) (k : ℤ) (h1 : chi 1 = 1)
    (hzero : ∀ e : ℕ, 1 ≤ e → Work.FIArea5.S16Hecke.heckeLam chi k ((p:ℕ)^e) = 0) :
    Work.FIArea5.S16Hecke.heckeFp chi k p = fun _ => (1 : ℂ) := by
  funext s
  rw [Work.FIArea5.S16Hecke.heckeFp_eq_tsum]
  rw [tsum_eq_single 0 (fun e he => by
    rw [hzero e (Nat.one_le_iff_ne_zero.mpr he)]
    ring)]
  rw [pow_zero, pow_zero, mul_one, Work.FIArea5.S16Hecke.heckeLam_one, h1]

/-- `Even (2^e)` for `e ≥ 1`. -/
lemma even_two_pow {e : ℕ} (he : 1 ≤ e) : Even (2^e) := by
  rw [show e = (e-1)+1 from by omega, pow_succ']
  exact even_two.mul_right _

/-- The split classification of the primary elements of norm `p^ν` in terms of `π` and `star π`. -/
lemma splitClass (p : Nat.Primes) (π : GaussianInt) (hπprim : Work.FIPlan.IsPrimary π)
    (hπgn : Work.FIPlan.gnorm π = (p:ℕ)) (hπirr : Irreducible π)
    (hnassoc : ¬ Associated π (star π)) :
    ∀ ν z, Work.FIPlan.IsPrimary z → Work.FIPlan.gnorm z = (p:ℕ)^ν →
      ∃! a, a ≤ ν ∧ z = π^a * (star π)^(ν-a) := by
  intro ν z hz hzgn
  obtain ⟨a, ha, haz⟩ :=
    Work.FIArea5.S16Hecke.primaryPowClassify (p:ℕ) π p.prop.pos hπprim hπgn hπirr ν z hz hzgn
  exact ⟨a, ⟨ha, haz⟩, fun b hb =>
    (Work.FIArea5.S16Hecke.powClassUnique π ν a b hπirr hnassoc ha hb.1 (haz.symm.trans hb.2)).symm⟩

/-- `geo 0 0 ν = 0` for `ν ≥ 1`. -/
lemma geo_zero_zero {ν : ℕ} (hν : 1 ≤ ν) : Work.FIArea5.S16Hecke.geo (0:ℂ) 0 ν = 0 := by
  unfold Work.FIArea5.S16Hecke.geo
  refine Finset.sum_eq_zero (fun a ha => ?_)
  rw [Finset.mem_range] at ha
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · rw [pow_zero, one_mul, zero_pow (by omega : ν - 0 ≠ 0)]
  · rw [zero_pow (by omega : a ≠ 0), zero_mul]

/-- `geoInert 0 ν = 0` for `ν ≥ 1`. -/
lemma geoInert_zero_zero {ν : ℕ} (hν : 1 ≤ ν) : Work.FIArea5.S16Hecke.geoInert (0:ℂ) ν = 0 := by
  unfold Work.FIArea5.S16Hecke.geoInert
  by_cases hev : Even ν
  · rw [if_pos hev]
    have h2ν : 2 ≤ ν := by obtain ⟨k, hk⟩ := hev; omega
    exact zero_pow (Nat.ne_of_gt (Nat.div_pos h2ν (by norm_num)))
  · rw [if_neg hev]

/-- `ψ(χ,0,z) = χ z`. -/
lemma psi_zero_eq (chi : GaussianInt → ℂ) (z : GaussianInt) :
    Work.FIArea5.S16Hecke.psi chi 0 z = chi z := by
  rw [Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one]

/-- The split local Euler factor as a product of two linear factors (as functions). -/
lemma heckeFp_split_model (p : Nat.Primes) {π : GaussianInt} (hπprim : Work.FIPlan.IsPrimary π)
    (hπgn : Work.FIPlan.gnorm π = (p:ℕ)) (hπirr : Irreducible π)
    (hnassoc : ¬ Associated π (star π))
    (chi : GaussianInt → ℂ) (k : ℤ) (h1 : chi 1 = 1)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hp4 : (p:ℕ) % 4 = 1) {s : ℂ} (hs : 1 < s.re) :
    Work.FIArea5.S16Hecke.heckeFp chi k p
      =ᶠ[𝓝 s] (fun z => (1 - Work.FIArea5.S16Hecke.psi chi k π * (((p:ℕ):ℂ) ^ (-z)))⁻¹
        * (1 - Work.FIArea5.S16Hecke.psi chi k (star π) * (((p:ℕ):ℂ) ^ (-z)))⁻¹) := by
  refine Filter.eventually_of_mem
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) (fun z hz => ?_)
  exact Work.FIArea6Hecke.R.heckeFp_split_eq (p:ℕ) p.prop hp4 chi k h1 hmul hb π (star π)
    hπprim (Work.FIArea5.S16Hecke.isPrimary_star hπprim) hπgn
    (by rw [gnorm_star_eq]; exact hπgn)
    (splitClass p π hπprim hπgn hπirr hnassoc) hz

/-- The inert local Euler factor as a single quadratic factor (as a function). -/
lemma heckeFp_inert_model (p : Nat.Primes) (hp3 : (p:ℕ) % 4 = 3)
    (chi : GaussianInt → ℂ) (k : ℤ) (h1 : chi 1 = 1)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Work.FIArea5.S16Hecke.heckeFp chi k p
      =ᶠ[𝓝 s] (fun z => (1 - Work.FIArea5.S16Hecke.psi chi k (-(p : GaussianInt))
        * ((((p:ℕ):ℂ) ^ (-z)))^2)⁻¹) := by
  refine Filter.eventually_of_mem
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) (fun z hz => ?_)
  exact Work.FIArea6Hecke.R.heckeFp_inert_eq (p:ℕ) p.prop hp3 chi k h1 hmul hb hz

/-! ## The per-prime `(3,4,1)` bound -/

lemma perPrime_bound (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (hd : 1 ≤ d)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) {σ t : ℝ} (hσ : 1 < σ)
    (p : Nat.Primes) :
    0 ≤ 3 * (-logDeriv (Work.FIArea5.S16Hecke.heckeFp (principalStrict d) 0 p)
              ((σ:ℂ))).re
      + 4 * (-logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p)
              ((σ:ℂ) + (t:ℂ) * Complex.I)).re
      + (-logDeriv (Work.FIArea5.S16Hecke.heckeFp (fun z => chi z * chi z) (2*m) p)
              ((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)).re := by
  obtain ⟨hchi1, hchimul, hchib, -, -⟩ := hchi.1
  have hchi0 := hchi.2
  have h1c : (fun z => chi z * chi z) 1 = 1 := by simp [hchi1]
  have hmulc : ∀ z w : GaussianInt,
      (fun z => chi z * chi z) (z * w) = (fun z => chi z * chi z) z * (fun z => chi z * chi z) w := by
    intro z w
    change chi (z * w) * chi (z * w) = (chi z * chi z) * (chi w * chi w)
    rw [hchimul z w]; ring
  have hbc : ∀ z : GaussianInt, ‖chi z * chi z‖ ≤ 1 := by
    intro z; rw [norm_mul]; exact mul_le_one₀ (hchib z) (norm_nonneg _) (hchib z)
  have h1a : (principalStrict d) 1 = 1 := principalStrict_one d
  -- the three base points
  have hσ' : (1 : ℝ) < ((σ:ℂ)).re := by simp; linarith
  have hσ2 : (1 : ℝ) < (((σ:ℂ) + (t:ℂ) * Complex.I)).re := by simp; linarith
  have hσ3 : (1 : ℝ) < (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)).re := by simp; linarith
  by_cases hp2 : (p:ℕ) = 2
  · -- p = 2: all local factors are `1`
    have hA : Work.FIArea5.S16Hecke.heckeFp (principalStrict d) 0 p = fun _ => (1:ℂ) :=
      heckeFp_eq_one p _ _ h1a (fun e he => by
        rw [hp2]; exact Work.FIArea5.S16Hecke.heckeLam_even _ _ (even_two_pow he))
    have hB : Work.FIArea5.S16Hecke.heckeFp chi m p = fun _ => (1:ℂ) :=
      heckeFp_eq_one p _ _ hchi1 (fun e he => by
        rw [hp2]; exact Work.FIArea5.S16Hecke.heckeLam_even _ _ (even_two_pow he))
    have hC : Work.FIArea5.S16Hecke.heckeFp (fun z => chi z * chi z) (2*m) p = fun _ => (1:ℂ) :=
      heckeFp_eq_one p _ _ h1c (fun e he => by
        rw [hp2]; exact Work.FIArea5.S16Hecke.heckeLam_even _ _ (even_two_pow he))
    rw [hA, hB, hC]
    simp only [logDeriv_apply, deriv_const, zero_div, neg_zero, Complex.zero_re]
    norm_num
  · have hpodd : Odd (p:ℕ) := p.prop.odd_of_ne_two hp2
    by_cases hp4 : (p:ℕ) % 4 = 1
    · -- split prime
      obtain ⟨π, hπprim, hπgn, hπirr, hnassoc⟩ :=
        Work.FIArea5.S16Hecke.existsPrimarySplit (p:ℕ) p.prop hp4
      by_cases hu : Work.FIArea5.S16Hecke.IsUnitMod4d d π
      · -- both Satake parameters of the principal character are `1`
        have hu' : Work.FIArea5.S16Hecke.IsUnitMod4d d (star π) :=
          (isUnitMod4d_star_iff d π).mpr hu
        have hP0π : Work.FIArea5.S16Hecke.psi (principalStrict d) 0 π = 1 := by
          rw [psi_zero_eq]
          exact principalStrict_of_unit hu
        have hP0π' : Work.FIArea5.S16Hecke.psi (principalStrict d) 0 (star π) = 1 := by
          rw [psi_zero_eq]
          exact principalStrict_of_unit hu'
        have hpsi_c : Work.FIArea5.S16Hecke.psi (fun z => chi z * chi z) (2*m) π
            = (Work.FIArea5.S16Hecke.psi chi m π)^2 := by
          rw [psi_sq, pow_two]
        have hpsi_c' : Work.FIArea5.S16Hecke.psi (fun z => chi z * chi z) (2*m) (star π)
            = (Work.FIArea5.S16Hecke.psi chi m (star π))^2 := by
          rw [psi_sq, pow_two]
        have hfA := heckeFp_split_model p hπprim hπgn hπirr hnassoc (principalStrict d) 0
          h1a (principalStrict_mul d) (norm_principalStrict_le_one d) hp4 hσ'
        have hfB := heckeFp_split_model p hπprim hπgn hπirr hnassoc chi m
          hchi1 hchimul hchib hp4 hσ2
        have hfC := heckeFp_split_model p hπprim hπgn hπirr hnassoc
          (fun z => chi z * chi z) (2*m) h1c hmulc hbc hp4 hσ3
        rw [(logDeriv_congr_nhds hfA).eq_of_nhds, (logDeriv_congr_nhds hfB).eq_of_nhds,
          (logDeriv_congr_nhds hfC).eq_of_nhds]
        simp only [hP0π, hP0π', hpsi_c, hpsi_c', one_mul]
        simpa only [one_mul] using LocalSplit341 p (t := t) hσ
          (Work.FIArea5.S16Hecke.norm_psi_le_one chi m hchib π)
          (Work.FIArea5.S16Hecke.norm_psi_le_one chi m hchib (star π))
      · -- `π` is not a unit mod `4d`: all local factors are `1`
        have h0π : Work.FIArea5.S16Hecke.psi (principalStrict d) 0 π = 0 := by
          rw [psi_zero_eq]; exact principalStrict_of_not_unit hu
        have h0π' : Work.FIArea5.S16Hecke.psi (principalStrict d) 0 (star π) = 0 := by
          rw [psi_zero_eq]
          exact principalStrict_of_not_unit (fun h => hu ((isUnitMod4d_star_iff d π).mp h))
        have h0cπ : Work.FIArea5.S16Hecke.psi chi m π = 0 := by
          rw [Work.FIArea5.S16Hecke.psi, hchi0 π hu]; ring
        have h0cπ' : Work.FIArea5.S16Hecke.psi chi m (star π) = 0 := by
          rw [Work.FIArea5.S16Hecke.psi, hchi0 (star π) (fun h => hu ((isUnitMod4d_star_iff d π).mp h))]
          ring
        have h0dπ : Work.FIArea5.S16Hecke.psi (fun z => chi z * chi z) (2*m) π = 0 := by
          rw [Work.FIArea5.S16Hecke.psi, hchi0 π hu]; ring
        have h0dπ' : Work.FIArea5.S16Hecke.psi (fun z => chi z * chi z) (2*m) (star π) = 0 := by
          rw [Work.FIArea5.S16Hecke.psi, hchi0 (star π) (fun h => hu ((isUnitMod4d_star_iff d π).mp h))]
          ring
        have hA : Work.FIArea5.S16Hecke.heckeFp (principalStrict d) 0 p = fun _ => (1:ℂ) :=
          heckeFp_eq_one p _ _ h1a (fun e he => by
            rw [Work.FIArea5.S16Hecke.heckeLam_splitSum (principalStrict d) 0 (p:ℕ) p.prop.pos
              (principalStrict_mul d) h1a π (star π) hπprim
              (Work.FIArea5.S16Hecke.isPrimary_star hπprim) hπgn
              (by rw [gnorm_star_eq]; exact hπgn)
              (splitClass p π hπprim hπgn hπirr hnassoc) e, h0π, h0π']
            exact geo_zero_zero he)
        have hB : Work.FIArea5.S16Hecke.heckeFp chi m p = fun _ => (1:ℂ) :=
          heckeFp_eq_one p _ _ hchi1 (fun e he => by
            rw [Work.FIArea5.S16Hecke.heckeLam_splitSum chi m (p:ℕ) p.prop.pos hchimul hchi1
              π (star π) hπprim (Work.FIArea5.S16Hecke.isPrimary_star hπprim) hπgn
              (by rw [gnorm_star_eq]; exact hπgn)
              (splitClass p π hπprim hπgn hπirr hnassoc) e, h0cπ, h0cπ']
            exact geo_zero_zero he)
        have hC : Work.FIArea5.S16Hecke.heckeFp (fun z => chi z * chi z) (2*m) p = fun _ => (1:ℂ) :=
          heckeFp_eq_one p _ _ h1c (fun e he => by
            rw [Work.FIArea5.S16Hecke.heckeLam_splitSum (fun z => chi z * chi z) (2*m) (p:ℕ)
              p.prop.pos hmulc h1c π (star π) hπprim
              (Work.FIArea5.S16Hecke.isPrimary_star hπprim) hπgn
              (by rw [gnorm_star_eq]; exact hπgn)
              (splitClass p π hπprim hπgn hπirr hnassoc) e, h0dπ, h0dπ']
            exact geo_zero_zero he)
        rw [hA, hB, hC]
        simp only [logDeriv_apply, deriv_const, zero_div, neg_zero, Complex.zero_re]
        norm_num
    · -- inert prime
      have hp3 : (p:ℕ) % 4 = 3 := by
        obtain ⟨k, hk⟩ := hpodd
        omega
      obtain ⟨hqp, -, hqgn, hclass⟩ :=
        Work.FIArea5.S16Hecke.inertPrimaryClass (p:ℕ) p.prop hp3
      by_cases hu : Work.FIArea5.S16Hecke.IsUnitMod4d d (-(p : GaussianInt))
      · have hP0q : Work.FIArea5.S16Hecke.psi (principalStrict d) 0 (-(p : GaussianInt)) = 1 := by
          rw [psi_zero_eq]; exact principalStrict_of_unit hu
        have hpsi_c : Work.FIArea5.S16Hecke.psi (fun z => chi z * chi z) (2*m) (-(p : GaussianInt))
            = (Work.FIArea5.S16Hecke.psi chi m (-(p : GaussianInt)))^2 := by
          rw [psi_sq, pow_two]
        have hfA := heckeFp_inert_model p hp3 (principalStrict d) 0 h1a (principalStrict_mul d)
          (norm_principalStrict_le_one d) hσ'
        have hfB := heckeFp_inert_model p hp3 chi m hchi1 hchimul hchib hσ2
        have hfC := heckeFp_inert_model p hp3 (fun z => chi z * chi z) (2*m) h1c hmulc hbc hσ3
        rw [(logDeriv_congr_nhds hfA).eq_of_nhds, (logDeriv_congr_nhds hfB).eq_of_nhds,
          (logDeriv_congr_nhds hfC).eq_of_nhds]
        simp only [hP0q, hpsi_c, one_mul]
        simpa only [one_mul] using
          LocalInert341 p (t := t) hσ (Work.FIArea5.S16Hecke.norm_psi_le_one chi m hchib (-(p : GaussianInt)))
      · have h0q : Work.FIArea5.S16Hecke.psi (principalStrict d) 0 (-(p : GaussianInt)) = 0 := by
          rw [psi_zero_eq]; exact principalStrict_of_not_unit hu
        have h0cq : Work.FIArea5.S16Hecke.psi chi m (-(p : GaussianInt)) = 0 := by
          rw [Work.FIArea5.S16Hecke.psi, hchi0 (-(p : GaussianInt)) hu]; ring
        have h0dq : Work.FIArea5.S16Hecke.psi (fun z => chi z * chi z) (2*m) (-(p : GaussianInt)) = 0 := by
          rw [Work.FIArea5.S16Hecke.psi, hchi0 (-(p : GaussianInt)) hu]; ring
        have hA : Work.FIArea5.S16Hecke.heckeFp (principalStrict d) 0 p = fun _ => (1:ℂ) :=
          heckeFp_eq_one p _ _ h1a (fun e he => by
            rw [Work.FIArea5.S16Hecke.heckeLam_inertSum (principalStrict d) 0 (p:ℕ) p.prop.pos
              (principalStrict_mul d) h1a (-(p : GaussianInt)) hqp hqgn hclass e, h0q]
            exact geoInert_zero_zero he)
        have hB : Work.FIArea5.S16Hecke.heckeFp chi m p = fun _ => (1:ℂ) :=
          heckeFp_eq_one p _ _ hchi1 (fun e he => by
            rw [Work.FIArea5.S16Hecke.heckeLam_inertSum chi m (p:ℕ) p.prop.pos hchimul hchi1
              (-(p : GaussianInt)) hqp hqgn hclass e, h0cq]
            exact geoInert_zero_zero he)
        have hC : Work.FIArea5.S16Hecke.heckeFp (fun z => chi z * chi z) (2*m) p = fun _ => (1:ℂ) :=
          heckeFp_eq_one p _ _ h1c (fun e he => by
            rw [Work.FIArea5.S16Hecke.heckeLam_inertSum (fun z => chi z * chi z) (2*m) (p:ℕ)
              p.prop.pos hmulc h1c (-(p : GaussianInt)) hqp hqgn hclass e, h0dq]
            exact geoInert_zero_zero he)
        rw [hA, hB, hC]
        simp only [logDeriv_apply, deriv_const, zero_div, neg_zero, Complex.zero_re]
        norm_num

/-! ## Assembly -/

theorem HeckeLDerivRe341 (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (hd : 1 ≤ d)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) {σ t : ℝ} (hσ : 1 < σ) :
    0 ≤ 3 * (-deriv (Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0)
              ((σ : ℂ)) / Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 ((σ : ℂ))).re
      + 4 * (-deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) (((σ : ℂ) + (t : ℂ) * Complex.I)) /
              Work.FIArea5.S16Hecke.heckeLSeries chi m (((σ : ℂ) + (t : ℂ) * Complex.I))).re
      + (-deriv (Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi z * chi z) (2 * m))
              (((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)) /
              Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi z * chi z) (2 * m)
              (((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I))).re := by
  obtain ⟨hchi1, hchimul, hchib, -, -⟩ := hchi.1
  have hs1 : (1 : ℝ) < ((σ:ℂ)).re := by simp; linarith
  have hs2 : (1 : ℝ) < (((σ:ℂ) + (t:ℂ) * Complex.I)).re := by simp; linarith
  have hs3 : (1 : ℝ) < (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)).re := by simp; linarith
  have h1a : (principalStrict d) 1 = 1 := principalStrict_one d
  have hmula : ∀ z w : GaussianInt,
      (principalStrict d) (z * w) = (principalStrict d) z * (principalStrict d) w :=
    principalStrict_mul d
  have hba : ∀ z : GaussianInt, ‖(principalStrict d) z‖ ≤ 1 := norm_principalStrict_le_one d
  have h1c : (fun z => chi z * chi z) 1 = 1 := by simp [hchi1]
  have hmulc : ∀ z w : GaussianInt,
      (fun z => chi z * chi z) (z * w) = (fun z => chi z * chi z) z * (fun z => chi z * chi z) w := by
    intro z w
    change chi (z * w) * chi (z * w) = (chi z * chi z) * (chi w * chi w)
    rw [hchimul z w]; ring
  have hbc : ∀ z : GaussianInt, ‖chi z * chi z‖ ≤ 1 := by
    intro z; rw [norm_mul]; exact mul_le_one₀ (hchib z) (norm_nonneg _) (hchib z)
  -- the log-derivative Euler product identities
  have eA : logDeriv (Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0) ((σ:ℂ))
      = ∑' p : Nat.Primes, logDeriv (Work.FIArea5.S16Hecke.heckeFp (principalStrict d) 0 p) ((σ:ℂ)) :=
    HeckeLSeriesLogDerivEuler (principalStrict d) 0 h1a hmula hba hs1
  have eB : logDeriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) (((σ:ℂ) + (t:ℂ) * Complex.I))
      = ∑' p : Nat.Primes, logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p)
          (((σ:ℂ) + (t:ℂ) * Complex.I)) :=
    HeckeLSeriesLogDerivEuler chi m hchi1 hchimul hchib hs2
  have eC : logDeriv (Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi z * chi z) (2*m))
        (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I))
      = ∑' p : Nat.Primes, logDeriv (Work.FIArea5.S16Hecke.heckeFp (fun z => chi z * chi z) (2*m) p)
          (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I)) :=
    HeckeLSeriesLogDerivEuler (fun z => chi z * chi z) (2*m) h1c hmulc hbc hs3
  -- summability of the three per-prime sequences
  obtain ⟨C2, hC2pos, hC2⟩ := heckeFp_logDeriv_bound
  have hsummP : ∀ (chi' : GaussianInt → ℂ) (k' : ℤ) (h1' : chi' 1 = 1)
      (hmul' : ∀ z w : GaussianInt, chi' (z * w) = chi' z * chi' w)
      (hb' : ∀ z : GaussianInt, ‖chi' z‖ ≤ 1) (s : ℂ) (hs : 1 < s.re),
      Summable (fun p : Nat.Primes => logDeriv (Work.FIArea5.S16Hecke.heckeFp chi' k' p) s) := by
    intro chi' k' h1' hmul' hb' s hs
    have hbnd : Summable (fun p : Nat.Primes =>
        C2 * Real.log ((p:ℕ):ℝ) * (((p:ℕ):ℝ)^(-s.re))) := by
      have h := (summable_primes_log_mul_rpow hs).mul_left C2
      exact h.congr (fun p => by ring)
    exact Summable.of_norm_bounded hbnd (fun p => hC2 chi' k' p s h1' hmul' hb' hs)
  have hsumA : Summable (fun p : Nat.Primes =>
      -logDeriv (Work.FIArea5.S16Hecke.heckeFp (principalStrict d) 0 p) ((σ:ℂ))) :=
    (hsummP _ _ h1a hmula hba _ hs1).neg
  have hsumB : Summable (fun p : Nat.Primes =>
      -logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) (((σ:ℂ) + (t:ℂ) * Complex.I))) :=
    (hsummP _ _ hchi1 hchimul hchib _ hs2).neg
  have hsumC : Summable (fun p : Nat.Primes =>
      -logDeriv (Work.FIArea5.S16Hecke.heckeFp (fun z => chi z * chi z) (2*m) p)
        (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I))) :=
    (hsummP _ _ h1c hmulc hbc _ hs3).neg
  -- the three `.re` identities
  have kA : (-logDeriv (Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0) ((σ:ℂ))).re
      = ∑' p : Nat.Primes,
          (-logDeriv (Work.FIArea5.S16Hecke.heckeFp (principalStrict d) 0 p) ((σ:ℂ))).re := by
    rw [eA, ← tsum_neg, Complex.re_tsum hsumA]
  have kB : (-logDeriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) (((σ:ℂ) + (t:ℂ) * Complex.I))).re
      = ∑' p : Nat.Primes,
          (-logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p)
            (((σ:ℂ) + (t:ℂ) * Complex.I))).re := by
    rw [eB, ← tsum_neg, Complex.re_tsum hsumB]
  have kC : (-logDeriv (Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi z * chi z) (2*m))
        (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I))).re
      = ∑' p : Nat.Primes,
          (-logDeriv (Work.FIArea5.S16Hecke.heckeFp (fun z => chi z * chi z) (2*m) p)
            (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I))).re := by
    rw [eC, ← tsum_neg, Complex.re_tsum hsumC]
  have hsumAr : Summable (fun p : Nat.Primes =>
      (-logDeriv (Work.FIArea5.S16Hecke.heckeFp (principalStrict d) 0 p) ((σ:ℂ))).re) := by
    simpa [Function.comp_def, Complex.reCLM_apply] using Complex.reCLM.summable hsumA
  have hsumBr : Summable (fun p : Nat.Primes =>
      (-logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) (((σ:ℂ) + (t:ℂ) * Complex.I))).re) := by
    simpa [Function.comp_def, Complex.reCLM_apply] using Complex.reCLM.summable hsumB
  have hsumCr : Summable (fun p : Nat.Primes =>
      (-logDeriv (Work.FIArea5.S16Hecke.heckeFp (fun z => chi z * chi z) (2*m) p)
        (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I))).re) := by
    simpa [Function.comp_def, Complex.reCLM_apply] using Complex.reCLM.summable hsumC
  -- assemble
  have key : 3 * (-logDeriv (Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0) ((σ:ℂ))).re
      + 4 * (-logDeriv (Work.FIArea5.S16Hecke.heckeLSeries chi m)
              (((σ:ℂ) + (t:ℂ) * Complex.I))).re
      + (-logDeriv (Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi z * chi z) (2*m))
              (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I))).re
      = ∑' p : Nat.Primes,
          (3 * (-logDeriv (Work.FIArea5.S16Hecke.heckeFp (principalStrict d) 0 p) ((σ:ℂ))).re
            + 4 * (-logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p)
                    (((σ:ℂ) + (t:ℂ) * Complex.I))).re
            + (-logDeriv (Work.FIArea5.S16Hecke.heckeFp (fun z => chi z * chi z) (2*m) p)
                    (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I))).re) := by
    rw [kA, kB, kC, ← tsum_mul_left, ← tsum_mul_left]
    rw [← (hsumAr.mul_left 3).tsum_add (hsumBr.mul_left 4)]
    rw [← ((hsumAr.mul_left 3).add (hsumBr.mul_left 4)).tsum_add hsumCr]
  have hLHS : 3 * (-deriv (Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0) ((σ:ℂ))
        / Work.FIArea5.S16Hecke.heckeLSeries (principalStrict d) 0 ((σ:ℂ))).re
      + 4 * (-deriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) (((σ:ℂ) + (t:ℂ) * Complex.I))
        / Work.FIArea5.S16Hecke.heckeLSeries chi m (((σ:ℂ) + (t:ℂ) * Complex.I))).re
      + (-deriv (Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi z * chi z) (2*m))
          (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I))
        / Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi z * chi z) (2*m)
          (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I))).re
      = ∑' p : Nat.Primes,
          (3 * (-logDeriv (Work.FIArea5.S16Hecke.heckeFp (principalStrict d) 0 p) ((σ:ℂ))).re
            + 4 * (-logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p)
                    (((σ:ℂ) + (t:ℂ) * Complex.I))).re
            + (-logDeriv (Work.FIArea5.S16Hecke.heckeFp (fun z => chi z * chi z) (2*m) p)
                    (((σ:ℂ) + ((2*t:ℝ):ℂ) * Complex.I))).re) := by
    rw [← key]
    simp only [logDeriv_apply, neg_div]
  rw [hLHS]
  exact tsum_nonneg (fun p => perPrime_bound d chi m hd hchi hσ p)

end

end Work.FIArea6Hecke.R
