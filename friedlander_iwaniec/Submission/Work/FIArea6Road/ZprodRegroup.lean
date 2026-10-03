import Mathlib
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs
import Submission.Work.FIArea6Road.EulerCore

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The Möbius-twisted Hecke coefficient `λ_m(n)·μ(n)·n^{-s}` -/

/-- The coefficient `λ_m(n)·μ(n)·n^{-s}` of the Möbius-twisted Hecke Dirichlet series. -/
def Aterm (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (n : ℕ) : ℂ :=
  Work.FIArea5.S16Hecke.heckeLam chi m n * (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)

lemma Aterm_mul {chi : GaussianInt → ℂ}
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (m : ℤ) (s : ℂ) {a b : ℕ} (hab : Nat.Coprime a b) :
    Aterm chi m s (a * b) = Aterm chi m s a * Aterm chi m s b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hb : b = 1 := (Nat.coprime_zero_left b).mp hab
    subst hb
    simp [Aterm, Work.FIArea5.S16Hecke.heckeLam_zero]
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    have ha1 : a = 1 := (Nat.coprime_zero_right a).mp hab
    subst ha1
    simp [Aterm, Work.FIArea5.S16Hecke.heckeLam_zero]
  rw [Aterm, Aterm, Aterm,
    Work.FIArea5.S16Hecke.heckeLam_mul chi m hchimul ha hb hab,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (Nat.coprime_iff_gcd_eq_one.mp hab),
    Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  push_cast
  ring

lemma Aterm_one {chi : GaussianInt → ℂ} (hchi1 : chi 1 = 1) (m : ℤ) (s : ℂ) :
    Aterm chi m s 1 = 1 := by
  simp [Aterm, Work.FIArea5.S16Hecke.heckeLam_one chi m, hchi1]

lemma Aterm_zero (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) : Aterm chi m s 0 = 0 := by
  simp [Aterm, Work.FIArea5.S16Hecke.heckeLam_zero]

lemma summable_norm_Aterm (chi : GaussianInt → ℂ) (m : ℤ)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖Aterm chi m s n‖) := by
  have hsre : s.re ≠ 0 := by linarith
  have hpt : ∀ n : ℕ, ‖Aterm chi m s n‖
      = ‖Work.FIArea5.S16Hecke.heckeLam chi m n
          * (ArithmeticFunction.moebius n : ℂ)‖ * (n : ℝ) ^ (-s.re) := by
    intro n
    rw [Aterm, norm_mul, Work.FIArea6Road.norm_natCast_cpow_neg n hsre]
  rw [funext hpt]
  exact summable_norm_lam_mu chi m hchibd hs

lemma Aterm_tsum_pow (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (hchi1 : chi 1 = 1)
    {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, Aterm chi m s (p ^ e)) = Work.FIArea6Road.locF chi m s p := by
  have hzero : ∀ e : ℕ, e ∉ Finset.range 2 → Aterm chi m s (p ^ e) = 0 := by
    intro e he
    rw [Finset.mem_range, not_lt] at he
    have hne1 : e ≠ 1 := by omega
    have hmu : ArithmeticFunction.moebius (p ^ e) = 0 := by
      rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
      simp [hne1]
    simp [Aterm, hmu]
  rw [tsum_eq_sum (s := Finset.range 2) hzero]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [Aterm, Work.FIArea6Road.locF, Work.FIArea5.S16Hecke.heckeLam_one chi m, hchi1,
    ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- **The Euler product of the Möbius-twisted Hecke series over all primes.**
`∏'_p (1 - λ_m(p)p^{-s})` is the `HasProd` value of the local factors. -/
theorem hasProd_locF_Mfac (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => Work.FIArea6Road.locF chi m s (p : ℕ))
      (Work.FIArea6.TauPieces.Mfac chi m s) := by
  have hf1 : Aterm chi m s 1 = 1 := Aterm_one hchi1 m s
  have hf0 : Aterm chi m s 0 = 0 := Aterm_zero chi m s
  have hmul : ∀ {a b : ℕ}, Nat.Coprime a b →
      Aterm chi m s (a * b) = Aterm chi m s a * Aterm chi m s b :=
    fun hab => Aterm_mul hchimul m s hab
  have hsum : Summable (fun n : ℕ => ‖Aterm chi m s n‖) := summable_norm_Aterm chi m hchibd hs
  have key := EulerProduct.eulerProduct_hasProd hf1 hmul hsum hf0
  have hloc : ∀ p : Nat.Primes, (∑' e : ℕ, Aterm chi m s ((p : ℕ) ^ e))
      = Work.FIArea6Road.locF chi m s (p : ℕ) :=
    fun p => Aterm_tsum_pow chi m s hchi1 p.2
  have key2 : HasProd (fun p : Nat.Primes => Work.FIArea6Road.locF chi m s (p : ℕ))
      (∑' n, Aterm chi m s n) := key.congr_fun (fun p => (hloc p).symm)
  have hval : (∑' n, Aterm chi m s n) = Work.FIArea6.TauPieces.Mfac chi m s := by
    rw [← key.tprod_eq, tprod_congr hloc, ← Work.FIArea6Road.Mfac_eq_tprod_locF]
  rw [hval] at key2
  exact key2

/-! ## The `Gser` Euler product -/

lemma Gterm_eq (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (Q n : ℕ) :
    Gterm Pa chi m s Q n = (if Nat.Coprime n Q then (1 : ℂ) else 0) * Aterm chi m s n := by
  simp only [Gterm, Aterm]
  ring

lemma Gterm_mul (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (Q : ℕ)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) {a b : ℕ}
    (hab : Nat.Coprime a b) :
    Gterm Pa chi m s Q (a * b) = Gterm Pa chi m s Q a * Gterm Pa chi m s Q b := by
  have hind : (if Nat.Coprime (a * b) Q then (1 : ℂ) else 0)
      = (if Nat.Coprime a Q then (1 : ℂ) else 0)
        * (if Nat.Coprime b Q then (1 : ℂ) else 0) := by
    by_cases ha : Nat.Coprime a Q
    · by_cases hb : Nat.Coprime b Q
      · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨ha, hb⟩), if_pos ha, if_pos hb, mul_one]
      · rw [if_neg (fun h => hb (Nat.coprime_mul_iff_left.mp h).2), if_pos ha, if_neg hb, mul_zero]
    · rw [if_neg (fun h => ha (Nat.coprime_mul_iff_left.mp h).1), if_neg ha, zero_mul]
  rw [Gterm_eq, Gterm_eq, Gterm_eq, hind, Aterm_mul hchimul m s hab]
  ring

lemma Gterm_one (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (Q : ℕ)
    (hchi1 : chi 1 = 1) : Gterm Pa chi m s Q 1 = 1 := by
  rw [Gterm_eq, Aterm_one hchi1 m s]
  simp

lemma Gterm_zero (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (Q : ℕ) :
    Gterm Pa chi m s Q 0 = 0 := by
  rw [Gterm_eq, Aterm_zero]
  ring

lemma summable_norm_Gterm (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) (Q : ℕ) :
    Summable (fun n : ℕ => ‖Gterm Pa chi m s Q n‖) := by
  have hsre : s.re ≠ 0 := by linarith
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_norm_lam_mu chi m hchibd hs)
  have h1 : ‖(if Nat.Coprime n Q then (1 : ℂ) else 0)‖ ≤ 1 := by split <;> simp
  calc ‖Gterm Pa chi m s Q n‖
      = ‖(if Nat.Coprime n Q then (1 : ℂ) else 0)‖ * ‖Aterm chi m s n‖ := by
        rw [Gterm_eq, norm_mul]
    _ = ‖(if Nat.Coprime n Q then (1 : ℂ) else 0)‖
          * (‖Work.FIArea5.S16Hecke.heckeLam chi m n * (ArithmeticFunction.moebius n : ℂ)‖
              * (n : ℝ) ^ (-s.re)) := by
        rw [Aterm, norm_mul, Work.FIArea6Road.norm_natCast_cpow_neg n hsre]
    _ ≤ 1 * (‖Work.FIArea5.S16Hecke.heckeLam chi m n * (ArithmeticFunction.moebius n : ℂ)‖
              * (n : ℝ) ^ (-s.re)) := by
        exact mul_le_mul_of_nonneg_right h1
          (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    _ = _ := by ring

lemma Gterm_tsum_pow (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ)
    (hchi1 : chi 1 = 1) {p : ℕ} (hp : p.Prime) (Q : ℕ) :
    (∑' e : ℕ, Gterm Pa chi m s Q (p ^ e))
      = if p ∣ Q then 1 else Work.FIArea6Road.locF chi m s p := by
  have hzero : ∀ e : ℕ, e ∉ Finset.range 2 → Gterm Pa chi m s Q (p ^ e) = 0 := by
    intro e he
    rw [Finset.mem_range, not_lt] at he
    have hne1 : e ≠ 1 := by omega
    have hmu : ArithmeticFunction.moebius (p ^ e) = 0 := by
      rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
      simp [hne1]
    simp [Gterm_eq, Aterm, hmu]
  rw [tsum_eq_sum (s := Finset.range 2) hzero]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [pow_zero, pow_one, Gterm_one Pa chi m s Q hchi1]
  simp only [Gterm_eq, Aterm]
  have hmu : ((ArithmeticFunction.moebius p : ℤ) : ℂ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]; norm_num
  rw [hmu]
  simp only [Nat.Prime.coprime_iff_not_dvd hp]
  by_cases hQ : p ∣ Q
  · rw [if_neg (not_not.mpr hQ), if_pos hQ]; ring
  · rw [if_pos hQ, if_neg hQ, Work.FIArea6Road.locF]; ring

theorem Gser_eq_tprod (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) (Q : ℕ) :
    Work.FIArea6Road.Gser Pa chi m s Q
      = ∏' p : Nat.Primes, (if (p : ℕ) ∣ Q then (1:ℂ) else Work.FIArea6Road.locF chi m s (p : ℕ)) := by
  have key := EulerProduct.eulerProduct_tprod (R := ℂ) (f := fun n => Gterm Pa chi m s Q n)
    (Gterm_one Pa chi m s Q hchi1) (fun {a b} hab => Gterm_mul Pa chi m s Q hchimul hab)
    (summable_norm_Gterm Pa chi m hchibd hs Q) (Gterm_zero Pa chi m s Q)
  rw [Gser_eq_tsum_Gterm, ← key]
  exact tprod_congr (fun p => Gterm_tsum_pow Pa chi m s hchi1 p.2 Q)

/-! ## Removing finitely many factors from an infinite product -/

lemma tprod_ite_one_mul {β : Type*} [DecidableEq β] (S : Finset β) (f : β → ℂ)
    (hf : HasProd f (∏' b, f b)) (hne : ∀ b ∈ S, f b ≠ 0) :
    ∏' b, (if b ∈ S then (1 : ℂ) else f b)
      = (∏' b, f b) * ∏' b, (if b ∈ S then (f b)⁻¹ else 1) := by
  have hk : HasProd (fun b : β => if b ∈ S then (f b)⁻¹ else 1)
      (∏' b, (if b ∈ S then (f b)⁻¹ else 1)) := by
    rw [tprod_eq_prod (s := S) (f := fun b : β => if b ∈ S then (f b)⁻¹ else 1)
      (fun b hb => by simp [hb])]
    exact hasProd_prod_of_ne_finset_one (s := S)
      (f := fun b : β => if b ∈ S then (f b)⁻¹ else 1) (fun b hb => by simp [hb])
  have hcongr : (fun b : β => if b ∈ S then (1 : ℂ) else f b)
      = fun b : β => f b * (if b ∈ S then (f b)⁻¹ else 1) := by
    funext b
    by_cases hb : b ∈ S
    · rw [if_pos hb, if_pos hb, mul_inv_cancel₀ (hne b hb)]
    · rw [if_neg hb, if_neg hb, mul_one]
  rw [hcongr]
  exact (hf.mul hk).tprod_eq

/-- The finite set of primes (as `Nat.Primes`) dividing `Q`. -/
def primesDiv (Q : ℕ) : Finset Nat.Primes :=
  Q.primeFactors.attach.image
    (fun x : {x // x ∈ Q.primeFactors} => (⟨x.1, Nat.prime_of_mem_primeFactors x.2⟩ : Nat.Primes))

lemma mem_primesDiv {Q : ℕ} (hQ : Q ≠ 0) {p : Nat.Primes} :
    p ∈ primesDiv Q ↔ (p : ℕ) ∣ Q := by
  rw [primesDiv, Finset.mem_image]
  constructor
  · rintro ⟨x, -, hx⟩
    have h : (p : ℕ) = x.1 := by rw [← hx]
    rw [h]
    exact (Nat.mem_primeFactors.mp x.2).2.1
  · intro hp
    exact ⟨⟨(p : ℕ), Nat.mem_primeFactors.mpr ⟨p.2, hp, hQ⟩⟩, Finset.mem_attach _ _, rfl⟩

lemma prod_primesDiv (Q : ℕ) (f : ℕ → ℂ) :
    ∏ p ∈ primesDiv Q, f (p : ℕ) = ∏ q ∈ Q.primeFactors, f q := by
  rw [primesDiv,
    Finset.prod_image (s := Q.primeFactors.attach)
      (f := fun p : Nat.Primes => f (p : ℕ))
      (g := fun x : {x // x ∈ Q.primeFactors} =>
        (⟨x.1, Nat.prime_of_mem_primeFactors x.2⟩ : Nat.Primes))
      (fun x _ y _ hxy => Subtype.ext (congrArg (fun p : Nat.Primes => (p : ℕ)) hxy)),
    Finset.prod_attach]

theorem TprodCorrection (chi : GaussianInt → ℂ) (m : ℤ) {s : ℂ}
    (hs : 1 < s.re) (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hM : HasProd (fun p : Nat.Primes => Work.FIArea6Road.locF chi m s (p : ℕ))
      (Work.FIArea6.TauPieces.Mfac chi m s))
    {Q : ℕ} (hQ : Q ≠ 0) :
    ∏' p : Nat.Primes, (if (p : ℕ) ∣ Q then (1:ℂ) else Work.FIArea6Road.locF chi m s (p : ℕ))
      = Work.FIArea6.TauPieces.Mfac chi m s
          * ∏ p ∈ Q.primeFactors, (Work.FIArea6Road.locF chi m s p)⁻¹ := by
  have hM' : HasProd (fun p : Nat.Primes => Work.FIArea6Road.locF chi m s (p : ℕ))
      (∏' p : Nat.Primes, Work.FIArea6Road.locF chi m s (p : ℕ)) := by
    rwa [← Work.FIArea6Road.Mfac_eq_tprod_locF]
  have hne : ∀ p ∈ primesDiv Q, Work.FIArea6Road.locF chi m s (p : ℕ) ≠ 0 :=
    fun p _ => Work.FIArea6Road.locF_ne_zero chi m hs hchibd p.2
  have hcongr : ∀ p : Nat.Primes, (if (p : ℕ) ∣ Q then (1:ℂ)
        else Work.FIArea6Road.locF chi m s (p : ℕ))
      = (if p ∈ primesDiv Q then (1:ℂ) else Work.FIArea6Road.locF chi m s (p : ℕ)) :=
    fun p => by simp only [mem_primesDiv hQ]
  rw [tprod_congr hcongr, tprod_ite_one_mul (primesDiv Q)
    (fun p : Nat.Primes => Work.FIArea6Road.locF chi m s (p : ℕ)) hM' hne,
    ← Work.FIArea6Road.Mfac_eq_tprod_locF]
  congr 1
  rw [tprod_eq_prod (s := primesDiv Q)
    (f := fun p : Nat.Primes => if p ∈ primesDiv Q then
      (Work.FIArea6Road.locF chi m s (p : ℕ))⁻¹ else 1) (fun p hp => by simp [hp])]
  rw [Finset.prod_congr rfl (fun p hp => by rw [if_pos hp])]
  exact prod_primesDiv Q (fun q => (Work.FIArea6Road.locF chi m s q)⁻¹)

/-! ## The weighted factor at `c·Π` -/

lemma PiPr_primeFactors (Pa : Work.FITop.Params) :
    (Work.FIArea6Road.PiPr Pa).primeFactors = Nat.primesBelow (Pa.Pz + 1) := by
  rw [Work.FIArea6Road.PiPr]
  exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primesBelow hp)

lemma Gser_mul_PiPr (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) {c : ℕ}
    (hcop : Nat.Coprime c (Work.FIArea6Road.PiPr Pa)) :
    Work.FIArea6Road.Gser Pa chi m s (c * Work.FIArea6Road.PiPr Pa)
      = Work.FIArea6.TauPieces.Mfac chi m s * Work.FIArea6.TauPieces.Pfac Pa chi m s
          * ∏ p ∈ c.primeFactors, (Work.FIArea6Road.locF chi m s p)⁻¹ := by
  have hPi0 : Work.FIArea6Road.PiPr Pa ≠ 0 := by
    have := Work.FIArea6Road.one_le_PiPr Pa; omega
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := (Nat.coprime_zero_left (Work.FIArea6Road.PiPr Pa)).mp hcop
    have h2 := Work.FIArea6Road.two_le_PiPr Pa
    omega
  have hdisj : Disjoint c.primeFactors (Work.FIArea6Road.PiPr Pa).primeFactors := by
    rw [Finset.disjoint_left]
    intro p hpc hpP
    have hp1 : p.Prime := Nat.prime_of_mem_primeFactors hpc
    have hpc' : p ∣ c := (Nat.mem_primeFactors.mp hpc).2.1
    have hpP' : p ∣ Work.FIArea6Road.PiPr Pa := (Nat.mem_primeFactors.mp hpP).2.1
    have hg : p ∣ Nat.gcd c (Work.FIArea6Road.PiPr Pa) := Nat.dvd_gcd hpc' hpP'
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hg
    exact hp1.ne_one (Nat.dvd_one.mp hg)
  rw [Gser_eq_tprod Pa chi m hchi1 hchimul hchibd hs (c * Work.FIArea6Road.PiPr Pa),
    TprodCorrection chi m hs hchibd
      (hasProd_locF_Mfac chi m hchi1 hchimul hchibd hs) (mul_ne_zero hc0 hPi0),
    Nat.primeFactors_mul hc0 hPi0, Finset.prod_union hdisj, PiPr_primeFactors Pa,
    Work.FIArea6Road.Pfac_eq_prod_inv Pa chi m s]
  ring

/-! ## The regrouping theorem *FI* (16.30)–(16.34) -/

theorem ZprodRegroup (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Work.FIArea6.TauPieces.Zsfun Pa chi m s
      = Work.FIArea6.TauPieces.Mfac chi m s * Work.FIArea6.TauPieces.Pfac Pa chi m s
          * Work.FIArea6.TauPieces.Qfac Pa chi m s := by
  have hQ : Work.FIArea6.TauPieces.Qfac Pa chi m s
      = ∑ c ∈ (sfin Pa).filter (fun c => Squarefree c ∧ Nat.Coprime c (PiPr Pa)),
          Work.FIArea5.S16Hecke.heckeLam chi m c * (c : ℂ) ^ (-s)
            * ∏ p ∈ c.primeFactors, (Work.FIArea6Road.locF chi m s p)⁻¹ := by
    rw [Work.FIArea6Road.Qfac_eq]
    rfl
  rw [Zsfun_regroup Pa chi m hs hchi1 hchimul hchibd, hQ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨-, hsf, hcop⟩ := Finset.mem_filter.mp hc
  rw [Gser_mul_PiPr Pa chi m hchi1 hchimul hchibd hs hcop]
  ring

end

end Work.FIArea6Road
