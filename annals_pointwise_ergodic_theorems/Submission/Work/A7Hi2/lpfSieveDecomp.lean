import Mathlib
import Submission.Work.A7Hi2.SieveDefs
import Submission.Work.KMTAreas.A7Hi2.chainLeFiniteIntegral
import Submission.Work.KMTAreas.A7.residueLp_fiberOp_le_of_projection
import Submission.Work.KMTAreas.A7Hi.kernelDecimation
import Submission.Work.KMTAreas.A7G.chainPartLowpass
import Submission.Work.KMTAreas.A7Lpd.bandSquareAll

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.A7Hi2

open scoped BigOperators

/-!
# The Möbius/Ramanujan (sieve) decomposition of the low-pass Ionescu–Wainger walk

This file proves `Work.A7Hi2.lpfSieveDecomp`: the low-pass Ionescu–Wainger family
`lpf ρ l₁ m₀ m = kmtProj ρ l₁ (-(m₀ + m))` is a finite combination of **decimated pure dilation
families**,

  `lpf ρ l₁ m₀ m f x = Σ_{d ∈ iwDivs ρ l₁} (d · sieveCoeff ρ l₁ d) · decimDilFam m₀ kmtPhiSch d f m x`,

with `iwDivs`/`sieveCoeff`/`decimDilFam` as in `Submission/Work/A7Hi2/SieveDefs.lean`.

The proof has two halves.

* *Arithmetic.*  The kernel of `kmtProj ρ l k` is `arithChar ρ l (-j) · cw (η_{≤k}) j`
  (`Work.KMTAreas.A7Hi.kmtKernel_eq_arithChar_cw`), so it suffices to expand the arithmetic
  character.  Writing `A_l = (ℚ/ℤ)_{≤l} = ⋃_{q ∈ P_{≤l}} {a/q : a < q}`, the union is the
  *disjoint* union of the primitive sets `{a/q : gcd(a,q) = 1}` over the divisor-closed set
  `P_{≤l}` (`torsionDecomp_local`), and the classical Ramanujan-sum identity
  `Σ_{(a,q)=1} e(a y/q) = Σ_{d | q} μ(q/d) d [d | y]` (`ramanujanSum_local`) turns the character
  sum into the sieve sum over the divisors (`sieveRHS_reindex_local`).
* *Analysis.*  The coefficient sequence of the rescaled cutoff is the dilate of the fixed profile
  `cw(η_{≤k}) (d m) = 2^k φ(2^k d m)` (`Work.KMTAreas.A7G.cw_etaCut_eq_dilateG` with
  `φ = Work.KMTAreas.A7Hi.kmtPhiSch`), which identifies the terms of the expansion with the
  decimated dilation family (`decimDilFam_eq_tsum_cw_aux`); the rearrangement of the `tsum` against
  the finite sieve sum is `tsum_of_dvd` together with the summability of the coefficients.
-/

/-! ## 0. Elementary summability helpers -/

/-- A summable family of `q`-th powers of a norm is bounded, `q > 0`. -/
lemma exists_norm_bound_of_summable_rpow {q : ℝ} (hq : 0 < q) {f : ℤ → ℂ}
    (hf : Summable (fun n : ℤ => ‖f n‖ ^ q)) : ∃ B : ℝ, ∀ n : ℤ, ‖f n‖ ≤ B := by
  refine ⟨(∑' n : ℤ, ‖f n‖ ^ q) ^ (1 / q), fun n => ?_⟩
  have hle : ‖f n‖ ^ q ≤ ∑' m : ℤ, ‖f m‖ ^ q :=
    Summable.le_tsum hf n (fun m _ => Real.rpow_nonneg (norm_nonneg _) q)
  have h1 : (‖f n‖ ^ q) ^ (1 / q) = ‖f n‖ := by
    rw [← Real.rpow_mul (norm_nonneg _), mul_one_div, div_self hq.ne', Real.rpow_one]
  rw [← h1]
  exact Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) q) hle (by positivity)

/-- The convolution of the coefficient sequence of the rescaled cutoff with a bounded function is
summable. -/
lemma summable_cw_mul_of_bdd {k : ℤ} {x : ℤ} {f : ℤ → ℂ} {B : ℝ}
    (hB : ∀ n : ℤ, ‖f n‖ ≤ B) :
    Summable (fun j : ℤ =>
      Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) j
        * f (x - j)) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hmaj : Summable (fun j : ℤ =>
      ‖Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) j‖
        * B) :=
    (Work.KMTAreas.A7.summable_cw_etaCut k).mul_right B
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le
    (f := fun j : ℤ => ‖Work.KMTAreas.A7.cw
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) j‖ * B)
    (g := fun j : ℤ => ‖Work.KMTAreas.A7.cw
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) j * f (x - j)‖)
    (fun j => norm_nonneg _) (fun j => ?_) hmaj
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB (x - j)) (norm_nonneg _)

/-! ## 1. `iwP ρ l` is closed under divisors -/

/-- **`P_{≤l}` is closed under divisors.**  For `l ≤ iwC0 ρ` this is `P_{≤l} = Icc 1 (2^l)`; in
the concrete regime one splits `d ∣ Q · w` (`Q ∣ Q₀ = (N₀!)^{D_ρ}`, `w ∈ W_{≤l}`) at the
threshold `N₀ = iwN0 ρ l` into its `N₀`-smooth and large-prime parts (`iwLow`, `iwHigh`). -/
theorem iwP_dvd_closed_aux (ρ : ℝ) (hρ1 : ρ ≤ 1) (l d q : ℕ)
    (hq : q ∈ Work.Analysis.IonescuWainger.iwP ρ l) (hd : d ∣ q) :
    d ∈ Work.Analysis.IonescuWainger.iwP ρ l := by
  rw [Work.Analysis.IonescuWainger.mem_iwP] at hq ⊢
  rcases hq with ⟨hle, h1, h2⟩ | ⟨hlt, hcon⟩
  · exact Or.inl ⟨hle, Nat.pos_of_dvd_of_pos hd h1, le_trans (Nat.le_of_dvd h1 hd) h2⟩
  · refine Or.inr ⟨hlt, ?_⟩
    rw [Work.Analysis.IonescuWainger.mem_iwPconcrete] at hcon ⊢
    obtain ⟨Q, hQ, w, hw, rfl⟩ := hcon
    obtain ⟨hQdvd, -⟩ := Nat.mem_divisors.mp hQ
    have hQ0 : Q ≠ 0 :=
      (Nat.pos_of_dvd_of_pos hQdvd
        (Nat.pos_of_ne_zero (Work.Analysis.IonescuWainger.iwQ0_ne_zero ρ l))).ne'
    have hw0 : w ≠ 0 := (Work.Analysis.IonescuWainger.pos_of_mem_iwW hw).ne'
    have hQw0 : Q * w ≠ 0 := mul_ne_zero hQ0 hw0
    have hd0 : d ≠ 0 := (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hQw0)).ne'
    have hle_d : ∀ p : ℕ, d.factorization p ≤ ((Q * w).factorization) p :=
      fun p => (Nat.factorization_le_iff_dvd hd0 hQw0).mpr hd p
    have hQp : ∀ p : ℕ, Work.Analysis.IonescuWainger.iwN0 ρ l < p → Q.factorization p = 0 := by
      intro p hp
      by_contra hne
      have hpprime : p.Prime := by
        have hmem : p ∈ (Q.factorization).support := Finsupp.mem_support_iff.mpr hne
        rw [Nat.support_factorization] at hmem
        exact (Nat.mem_primeFactors.mp hmem).1
      have hle := Work.Analysis.IonescuWainger.IwMono.factorization_le_of_dvd_iwQ0 hQdvd p
      rw [Work.Analysis.IonescuWainger.IwMono.factorial_factorization_eq_zero_of_lt hpprime hp,
        mul_zero] at hle
      exact hne (Nat.le_zero.mp hle)
    have hsplit := Work.Analysis.IonescuWainger.IwMono.iwLow_mul_iwHigh
      (m := Work.Analysis.IonescuWainger.iwN0 ρ l) hd0
    have hL0 : Work.Analysis.IonescuWainger.IwMono.iwLow
        (Work.Analysis.IonescuWainger.iwN0 ρ l) d ≠ 0 :=
      Work.Analysis.IonescuWainger.IwMono.iwLow_ne_zero _ _
    have hW0 : Work.Analysis.IonescuWainger.IwMono.iwHigh
        (Work.Analysis.IonescuWainger.iwN0 ρ l) d ≠ 0 :=
      Work.Analysis.IonescuWainger.IwMono.iwHigh_ne_zero _ _
    have hfacmul : ∀ p : ℕ, d.factorization p
        = (Work.Analysis.IonescuWainger.IwMono.iwLow
            (Work.Analysis.IonescuWainger.iwN0 ρ l) d).factorization p
          + (Work.Analysis.IonescuWainger.IwMono.iwHigh
            (Work.Analysis.IonescuWainger.iwN0 ρ l) d).factorization p := by
      intro p
      have h := congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_mul hL0 hW0)
      rw [hsplit] at h
      exact h
    have hhigh_dvd : Work.Analysis.IonescuWainger.IwMono.iwHigh
        (Work.Analysis.IonescuWainger.iwN0 ρ l) d ∣ w := by
      refine (Nat.factorization_le_iff_dvd
        (Work.Analysis.IonescuWainger.IwMono.iwHigh_ne_zero _ _) hw0).mp ?_
      rw [Finsupp.le_def]
      intro p
      rw [Work.Analysis.IonescuWainger.IwMono.iwHigh_factorization]
      by_cases hc : p ∈ d.factorization.support.filter
          (fun p => Work.Analysis.IonescuWainger.iwN0 ρ l < p)
      · rw [if_pos hc]
        have hgN : Work.Analysis.IonescuWainger.iwN0 ρ l < p := (Finset.mem_filter.mp hc).2
        have hle := hle_d p
        rw [Nat.factorization_mul hQ0 hw0, Finsupp.add_apply, hQp p hgN, Nat.zero_add] at hle
        exact hle
      · rw [if_neg hc]; exact Nat.zero_le _
    have hW : Work.Analysis.IonescuWainger.IwMono.iwHigh
        (Work.Analysis.IonescuWainger.iwN0 ρ l) d ∈ Work.Analysis.IonescuWainger.iwW ρ l := by
      refine Work.Analysis.IonescuWainger.mem_iwW.mpr
        ⟨hhigh_dvd.trans (Work.Analysis.IonescuWainger.mem_iwW.mp hw).1, ?_⟩
      have hsub := Finsupp.support_mono ((Nat.factorization_le_iff_dvd
        (Work.Analysis.IonescuWainger.IwMono.iwHigh_ne_zero _ _) hw0).mpr hhigh_dvd)
      exact le_trans (Finset.card_le_card hsub) (Work.Analysis.IonescuWainger.mem_iwW.mp hw).2
    have hlow_dvd : Work.Analysis.IonescuWainger.IwMono.iwLow
        (Work.Analysis.IonescuWainger.iwN0 ρ l) d ∣ Work.Analysis.IonescuWainger.iwQ0 ρ l := by
      refine (Nat.factorization_le_iff_dvd hL0
        (Work.Analysis.IonescuWainger.iwQ0_ne_zero ρ l)).mp ?_
      rw [Finsupp.le_def]
      intro p
      have hfac := hfacmul p
      have hLp_le : (Work.Analysis.IonescuWainger.IwMono.iwLow
          (Work.Analysis.IonescuWainger.iwN0 ρ l) d).factorization p ≤ d.factorization p := by
        rw [hfac]; exact Nat.le_add_right _ _
      by_cases hp : p ∈ Work.Analysis.IonescuWainger.iwPrimeRange ρ l
      · have hgt : Work.Analysis.IonescuWainger.iwN0 ρ l < p :=
          (Work.Analysis.IonescuWainger.IwMono.mem_iwPrimeRange_iff.mp hp).1
        by_cases hsupp : p ∈ d.factorization.support
        · have hwf : (Work.Analysis.IonescuWainger.IwMono.iwHigh
              (Work.Analysis.IonescuWainger.iwN0 ρ l) d).factorization p = d.factorization p := by
            rw [Work.Analysis.IonescuWainger.IwMono.iwHigh_factorization,
              if_pos (Finset.mem_filter.mpr ⟨hsupp, hgt⟩)]
          have hzero : (Work.Analysis.IonescuWainger.IwMono.iwLow
              (Work.Analysis.IonescuWainger.iwN0 ρ l) d).factorization p = 0 := by
            have h := hfac; rw [hwf] at h; omega
          rw [hzero]; exact Nat.zero_le _
        · have hdp : d.factorization p = 0 := by
            by_contra hne
            exact hsupp (Finsupp.mem_support_iff.mpr hne)
          have hze : (Work.Analysis.IonescuWainger.IwMono.iwLow
              (Work.Analysis.IonescuWainger.iwN0 ρ l) d).factorization p = 0 :=
            Nat.eq_zero_of_le_zero (by rw [hdp] at hLp_le; exact hLp_le)
          rw [hze]; exact Nat.zero_le _
      · have hwz : w.factorization p = 0 := by
          by_contra hne
          exact hp (Work.Analysis.IonescuWainger.IwMono.factorization_pos_mem_iwPrimeRange
            hw hne).1
        have hle := hle_d p
        rw [Nat.factorization_mul hQ0 hw0, Finsupp.add_apply, hwz, add_zero] at hle
        rw [Work.Analysis.IonescuWainger.IwMono.iwQ0_factorization]
        exact le_trans hLp_le
          (le_trans hle (Work.Analysis.IonescuWainger.IwMono.factorization_le_of_dvd_iwQ0 hQdvd p))
    exact ⟨Work.Analysis.IonescuWainger.IwMono.iwLow (Work.Analysis.IonescuWainger.iwN0 ρ l) d,
           Nat.mem_divisors.mpr ⟨hlow_dvd, Work.Analysis.IonescuWainger.iwQ0_ne_zero ρ l⟩,
           Work.Analysis.IonescuWainger.IwMono.iwHigh (Work.Analysis.IonescuWainger.iwN0 ρ l) d,
           hW, hsplit.symm⟩

/-! ## 2. The Ramanujan sum identity -/

/-- `Σ_{e | n} μ e = [n = 1]`. -/
lemma sum_moebius_divisors_eq (n : ℕ) :
    (∑ e ∈ n.divisors, ArithmeticFunction.moebius e) = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (R := ℤ) (f := ArithmeticFunction.moebius)
    (x := n)
  rw [ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply] at h
  exact h.symm

/-- The bijection `b ↦ e * b` from `range (q / e)` onto `{a < q : e ∣ a}`. -/
lemma sum_range_div_mul (q e : ℕ) (he : e ∣ q) (he0 : 0 < e) (F : ℕ → ℂ) :
    (∑ b ∈ Finset.range (q / e), F (e * b))
      = ∑ a ∈ (Finset.range q).filter (fun a => e ∣ a), F a := by
  refine Finset.sum_bij (fun b _ => e * b) ?_ ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ⟨b, rfl⟩⟩
    calc e * b < e * (q / e) := Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hb) he0
      _ = q := Nat.mul_div_cancel' he
  · intro b1 _ b2 _ h
    exact Nat.eq_of_mul_eq_mul_left he0 h
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨haq, ⟨b, rfl⟩⟩ := ha
    refine ⟨b, ?_, rfl⟩
    rw [Finset.mem_range]
    have h : e * (q / e) = q := Nat.mul_div_cancel' he
    exact Nat.lt_of_mul_lt_mul_left (by rw [h]; exact haq)
  · intro b _
    rfl

/-- `q / (q / e) = e` for `e ∣ q`, `q > 0`. -/
lemma div_div_self_eq (q e : ℕ) (hq : 0 < q) (he : e ∣ q) : q / (q / e) = e := by
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hq
  have hpos : 0 < q / e := Nat.div_pos (Nat.le_of_dvd hq he) hepos
  have h1 : (q / e) * (q / (q / e)) = q := by
    rw [mul_comm]
    exact Nat.div_mul_cancel ⟨e, (Nat.div_mul_cancel he).symm⟩
  have h2 : (q / e) * e = q := Nat.div_mul_cancel he
  exact Nat.mul_left_cancel hpos (by rw [h1, h2])

/-- The divisor sum is invariant under the involution `e ↦ q / e`. -/
lemma sum_divisors_div_swap' (q : ℕ) (hq : 0 < q) (F : ℕ → ℂ) :
    (∑ e ∈ q.divisors, F (q / e)) = ∑ d ∈ q.divisors, F d := by
  have hmem : ∀ e, e ∈ q.divisors → q / e ∈ q.divisors := fun e he =>
    Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp he).1, hq.ne'⟩
  refine Finset.sum_bij (fun e _ => q / e) ?_ ?_ ?_ ?_
  · intro e he
    exact hmem e he
  · intro e1 he1 e2 he2 h
    have h1 := div_div_self_eq q e1 hq (Nat.mem_divisors.mp he1).1
    have h2 := div_div_self_eq q e2 hq (Nat.mem_divisors.mp he2).1
    rw [← h1, ← h2, h]
  · intro k hk
    exact ⟨q / k, hmem k hk, div_div_self_eq q k hq (Nat.mem_divisors.mp hk).1⟩
  · intro e he
    rfl

/-- **The Ramanujan sum identity**: `Σ_{(a,q)=1, a<q} e(a y/q) = Σ_{d | q} μ(q/d) · d · [d | y]`. -/
lemma ramanujanSum_local (q : ℕ) (hq : 0 < q) (y : ℤ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        fourier (T := 1) y (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle))
      = ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) * (d : ℂ)
          * (if (d : ℤ) ∣ y then (1 : ℂ) else 0) := by
  have hdiv : ∀ a : ℕ, (Nat.gcd a q).divisors = q.divisors.filter (fun e => e ∣ a) := by
    intro a
    ext e
    simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hea, heq⟩, -⟩
      exact ⟨⟨heq, hq.ne'⟩, hea⟩
    · rintro ⟨⟨heq, -⟩, hea⟩
      exact ⟨⟨hea, heq⟩, (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right a q) hq).ne'⟩
  have hMb : ∀ a : ℕ, (if Nat.Coprime a q then (1 : ℂ) else 0)
      = ∑ e ∈ (Nat.gcd a q).divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) := by
    intro a
    have h := sum_moebius_divisors_eq (Nat.gcd a q)
    have hc : ((∑ e ∈ (Nat.gcd a q).divisors, ArithmeticFunction.moebius e : ℤ) : ℂ)
        = ∑ e ∈ (Nat.gcd a q).divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) := by
      push_cast
      rfl
    rw [← hc, h]
    by_cases hcop : Nat.Coprime a q
    · rw [if_pos hcop, if_pos (Nat.coprime_iff_gcd_eq_one.mp hcop)]
      norm_num
    · rw [if_neg hcop, if_neg (fun hg => hcop (Nat.coprime_iff_gcd_eq_one.mpr hg))]
      norm_num
  have hL : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        fourier (T := 1) y (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle))
      = ∑ e ∈ q.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ)
          * (if (((q / e : ℕ) : ℤ)) ∣ y then (((q / e : ℕ) : ℂ)) else 0) := by
    rw [Finset.sum_filter]
    calc (∑ a ∈ Finset.range q,
            (if Nat.Coprime a q then
              fourier (T := 1) y (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle)
              else 0))
        = ∑ a ∈ Finset.range q,
            (∑ e ∈ q.divisors.filter (fun e => e ∣ a),
                ((ArithmeticFunction.moebius e : ℤ) : ℂ))
              * fourier (T := 1) y
                  (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          have hstep : (if Nat.Coprime a q then fourier (T := 1) y
                (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle) else 0)
              = (if Nat.Coprime a q then (1 : ℂ) else 0)
                * fourier (T := 1) y
                    (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle) := by
            by_cases h : Nat.Coprime a q <;> simp [h]
          rw [hstep, hMb a, hdiv a]
      _ = ∑ a ∈ Finset.range q, ∑ e ∈ q.divisors,
            (if e ∣ a then ((ArithmeticFunction.moebius e : ℤ) : ℂ) else 0)
              * fourier (T := 1) y
                  (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_filter, Finset.sum_mul]
      _ = ∑ e ∈ q.divisors, ∑ a ∈ Finset.range q,
            (if e ∣ a then ((ArithmeticFunction.moebius e : ℤ) : ℂ) else 0)
              * fourier (T := 1) y
                  (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle) :=
          Finset.sum_comm
      _ = ∑ e ∈ q.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ)
            * (if (((q / e : ℕ) : ℤ)) ∣ y then (((q / e : ℕ) : ℂ)) else 0) := by
          refine Finset.sum_congr rfl fun e he => ?_
          have he_dvd : e ∣ q := (Nat.mem_divisors.mp he).1
          have he_pos : 0 < e := Nat.pos_of_dvd_of_pos he_dvd hq
          have h1 : (∑ a ∈ Finset.range q,
                (if e ∣ a then ((ArithmeticFunction.moebius e : ℤ) : ℂ) else 0)
                  * fourier (T := 1) y
                      (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle))
              = ∑ a ∈ (Finset.range q).filter (fun a => e ∣ a),
                  ((ArithmeticFunction.moebius e : ℤ) : ℂ)
                    * fourier (T := 1) y
                        (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun a _ => ?_
            by_cases h : e ∣ a <;> simp [h]
          rw [h1, ← Finset.mul_sum]
          congr 1
          rw [← sum_range_div_mul q e he_dvd he_pos
            (fun a => fourier (T := 1) y
              (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle))]
          have h2 : (∑ b ∈ Finset.range (q / e),
                fourier (T := 1) y ((((e * b : ℕ) : ℝ) / ((q : ℕ) : ℝ)) :
                  Work.Analysis.IonescuWainger.Circle))
              = ∑ b ∈ Finset.range (q / e),
                  fourier (T := 1) y ((((b : ℝ) / ((q / e : ℕ) : ℝ))) :
                    Work.Analysis.IonescuWainger.Circle) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            congr 1
            have hqR : ((q : ℕ) : ℝ) = (e : ℝ) * ((q / e : ℕ) : ℝ) := by
              calc ((q : ℕ) : ℝ) = (((e * (q / e) : ℕ)) : ℝ) := by
                    rw [Nat.mul_div_cancel' he_dvd]
                _ = (e : ℝ) * ((q / e : ℕ) : ℝ) := by push_cast; ring
            have heR : ((e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast he_pos.ne'
            have hqeR : (((q / e : ℕ)) : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.div_pos (Nat.le_of_dvd hq he_dvd) he_pos).ne'
            rw [hqR]
            push_cast
            field_simp
          rw [h2, Work.KMTAreas.A7.fourier_sum_range_div (q / e)
            (Nat.div_pos (Nat.le_of_dvd hq he_dvd) he_pos) y]
  have hR : (∑ d ∈ q.divisors, ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) * (d : ℂ)
        * (if (d : ℤ) ∣ y then (1 : ℂ) else 0))
      = ∑ e ∈ q.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ)
          * (if (((q / e : ℕ) : ℤ)) ∣ y then (((q / e : ℕ) : ℂ)) else 0) := by
    rw [← sum_divisors_div_swap' q hq (fun d => ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)
        * (d : ℂ) * (if (d : ℤ) ∣ y then (1 : ℂ) else 0))]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [div_div_self_eq q e hq (Nat.mem_divisors.mp he).1]
    by_cases h : (((q / e : ℕ) : ℤ)) ∣ y <;> simp [h]
  rw [hL, hR]

/-! ## 3. The torsion/primitive partition of `(ℚ/ℤ)_{≤l}` -/

/-- The torsion set `{a/q : a < q} ⊆ ℝ/ℤ`. -/
noncomputable def lpfTorsSet (q : ℕ) : Finset Work.Analysis.IonescuWainger.Circle :=
  (Finset.range q).image (fun a : ℕ =>
    (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle))

/-- The primitive set `{a/q : a < q, (a,q) = 1} ⊆ ℝ/ℤ`. -/
noncomputable def lpfPrimSet (q : ℕ) : Finset Work.Analysis.IonescuWainger.Circle :=
  ((Finset.range q).filter (fun a => Nat.Coprime a q)).image
    (fun a : ℕ => (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle))

/-- `a ↦ a/q` is injective on `{a < q}`. -/
lemma lpfDivCircle_inj' {q a b : ℕ} (hq : 0 < q) (ha : a < q) (hb : b < q)
    (h : (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle)
      = (((b : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle)) : a = b := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have haI : (a : ℝ) / (q : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    refine ⟨by positivity, ?_⟩
    rw [zero_add, div_lt_one hqR]
    exact_mod_cast ha
  have hbI : (b : ℝ) / (q : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    refine ⟨by positivity, ?_⟩
    rw [zero_add, div_lt_one hqR]
    exact_mod_cast hb
  have h2 : (a : ℝ) / (q : ℝ) = (b : ℝ) / (q : ℝ) :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp h
  have h3 : (a : ℝ) * (q : ℝ) = (b : ℝ) * (q : ℝ) :=
    (div_eq_div_iff hqR.ne' hqR.ne').mp h2
  have h4 : (a : ℝ) = (b : ℝ) := mul_right_cancel₀ hqR.ne' h3
  exact_mod_cast h4

/-- Two primitive sets with different moduli are disjoint. -/
lemma lpfPrimSet_disjoint {d d' : ℕ} (hd : d ≠ d') :
    Disjoint (lpfPrimSet d) (lpfPrimSet d') := by
  rw [Finset.disjoint_left]
  intro α hα hα'
  rw [lpfPrimSet, Finset.mem_image] at hα hα'
  obtain ⟨a, ha, rfl⟩ := hα
  obtain ⟨b, hb, hb_eq⟩ := hα'
  rw [Finset.mem_filter, Finset.mem_range] at ha hb
  have had : a < d := ha.1
  have hbd : b < d' := hb.1
  have hcop : Nat.Coprime a d := ha.2
  have hcop' : Nat.Coprime b d' := hb.2
  have hdd' : d ≠ 0 := by rintro rfl; exact absurd had (Nat.not_lt_zero a)
  have hdd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hdd'
  have hd'd : d' ≠ 0 := by rintro rfl; exact absurd hbd (Nat.not_lt_zero b)
  have hd'0 : (0 : ℝ) < (d' : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd'd
  have haI : (a : ℝ) / (d : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    refine ⟨by positivity, ?_⟩
    rw [zero_add, div_lt_one hdd0]
    exact_mod_cast had
  have hbI : (b : ℝ) / (d' : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    refine ⟨by positivity, ?_⟩
    rw [zero_add, div_lt_one hd'0]
    exact_mod_cast hbd
  have h2 : (a : ℝ) / (d : ℝ) = (b : ℝ) / (d' : ℝ) :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp hb_eq.symm
  have h3 : (a : ℝ) * (d' : ℝ) = (b : ℝ) * (d : ℝ) := (div_eq_div_iff hdd0.ne' hd'0.ne').mp h2
  have h3nat : a * d' = b * d := by exact_mod_cast h3
  have h1 : d ∣ d' := by
    refine (hcop.symm).dvd_of_dvd_mul_left ?_
    exact ⟨b, by rw [h3nat, mul_comm]⟩
  have h2' : d' ∣ d := by
    refine (hcop'.symm).dvd_of_dvd_mul_left ?_
    exact ⟨a, by rw [← h3nat, mul_comm]⟩
  exact hd (Nat.dvd_antisymm h1 h2')

/-- `(a · (q/d))/q = a/d` for `d ∣ q`. -/
lemma lpfDivMulDivEq (a q d : ℕ) (hq : 0 < q) (hd0 : 0 < d) (hd : d ∣ q) :
    (((a * (q / d) : ℕ) : ℝ) / ((q : ℕ) : ℝ)) = ((a : ℝ) / ((d : ℕ) : ℝ)) := by
  have hdq : ((q : ℕ) : ℝ) = (d : ℝ) * ((q / d : ℕ) : ℝ) := by
    calc ((q : ℕ) : ℝ) = (((d * (q / d) : ℕ)) : ℝ) := by rw [Nat.mul_div_cancel' hd]
      _ = (d : ℝ) * ((q / d : ℕ) : ℝ) := by push_cast; ring
  have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hd) hd0
  have hqe : ((q / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hqd.ne'
  rw [hdq]
  push_cast
  field_simp

/-- `{a/q : a < q} ⊆ ⋃_{d | q} {a/d : (a,d) = 1}`. -/
lemma lpfTorsSet_subset_biUnion_prim (q : ℕ) (hq : 0 < q) :
    lpfTorsSet q ⊆ q.divisors.biUnion lpfPrimSet := by
  intro α hα
  rw [lpfTorsSet, Finset.mem_image] at hα
  obtain ⟨a, ha, rfl⟩ := hα
  rw [Finset.mem_range] at ha
  set g := Nat.gcd a q with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right a hq
  have hgl : g ∣ a := Nat.gcd_dvd_left a q
  have hgr : g ∣ q := Nat.gcd_dvd_right a q
  refine Finset.mem_biUnion.mpr ⟨q / g, Nat.mem_divisors.mpr
    ⟨Nat.div_dvd_of_dvd hgr, hq.ne'⟩, ?_⟩
  rw [lpfPrimSet, Finset.mem_image]
  refine ⟨a / g, ?_, ?_⟩
  · rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.div_lt_div_of_lt_of_dvd hgr ha, Nat.coprime_div_gcd_div_gcd hgpos⟩
  · have h1 : ((a / g : ℕ) : ℝ) * (g : ℝ) = (a : ℝ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hgl]
    have h2 : ((q / g : ℕ) : ℝ) * (g : ℝ) = (q : ℝ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hgr]
    have hg0 : (g : ℝ) ≠ 0 := by positivity
    show (((a / g : ℕ) : ℝ) / ((q / g : ℕ) : ℝ) : Work.Analysis.IonescuWainger.Circle)
        = (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle)
    congr 1
    rw [← h1, ← h2]
    field_simp

/-- `{a/d : (a,d) = 1} ⊆ {b/q : b < q}` for `d ∣ q`. -/
lemma lpfPrimSet_subset_torsSet (q d : ℕ) (hq : 0 < q) (hd : d ∣ q) :
    lpfPrimSet d ⊆ lpfTorsSet q := by
  intro α hα
  rw [lpfPrimSet, Finset.mem_image] at hα
  obtain ⟨a, ha, rfl⟩ := hα
  rw [Finset.mem_filter, Finset.mem_range] at ha
  have had : a < d := ha.1
  rw [lpfTorsSet, Finset.mem_image]
  refine ⟨a * (q / d), ?_, ?_⟩
  · rw [Finset.mem_range]
    calc a * (q / d) < d * (q / d) :=
          Nat.mul_lt_mul_of_pos_right had
            (Nat.div_pos (Nat.le_of_dvd hq hd) (lt_of_le_of_lt (Nat.zero_le a) had))
      _ = q := Nat.mul_div_cancel' hd
  · show ((((a * (q / d) : ℕ) : ℝ) / ((q : ℕ) : ℝ)) :
        Work.Analysis.IonescuWainger.Circle)
        = (((a : ℝ) / ((d : ℕ) : ℝ)) : Work.Analysis.IonescuWainger.Circle)
    rw [lpfDivMulDivEq a q d hq (lt_of_le_of_lt (Nat.zero_le a) had) hd]

/-- The torsion set is the disjoint union of the primitive sets over the divisors. -/
lemma lpfTorsSet_eq_biUnion_prim (q : ℕ) (hq : 0 < q) :
    lpfTorsSet q = q.divisors.biUnion lpfPrimSet := by
  refine Finset.Subset.antisymm (lpfTorsSet_subset_biUnion_prim q hq) ?_
  intro α hα
  rw [Finset.mem_biUnion] at hα
  obtain ⟨d, hd, hαd⟩ := hα
  exact lpfPrimSet_subset_torsSet q d hq (Nat.mem_divisors.mp hd).1 hαd

/-- **The torsion/primitive decomposition of a divisor-closed union of torsion sets.**  For `S`
divisor-closed with positive elements, the character sum over `⋃_{q ∈ S} {a/q : a < q}` is the sum
of the primitive character sums. -/
theorem torsionDecomp_local (S : Finset ℕ) (hpos : ∀ q ∈ S, 0 < q)
    (hclosed : ∀ q ∈ S, ∀ d, d ∣ q → d ∈ S) (y : ℤ) :
    (∑ α ∈ S.biUnion lpfTorsSet, fourier (T := 1) y α)
      = ∑ q ∈ S, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          fourier (T := 1) y (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle) := by
  have hdisj : (↑S : Set ℕ).PairwiseDisjoint (fun q => lpfPrimSet q) := by
    intro q _ q' _ hne
    exact lpfPrimSet_disjoint hne
  have h1 : S.biUnion lpfTorsSet = S.biUnion (fun q => q.divisors.biUnion lpfPrimSet) :=
    Finset.biUnion_congr rfl (fun q hq => lpfTorsSet_eq_biUnion_prim q (hpos q hq))
  have h2 : S.biUnion (fun q => q.divisors.biUnion lpfPrimSet)
      = (S.biUnion (fun q => q.divisors)).biUnion lpfPrimSet := by
    ext α
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨q, hq, d, hd, hα⟩
      exact ⟨d, ⟨q, hq, hd⟩, hα⟩
    · rintro ⟨d, ⟨q, hq, hd⟩, hα⟩
      exact ⟨q, hq, d, hd, hα⟩
  have h3 : S.biUnion (fun q => q.divisors) = S := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro d hd
      rw [Finset.mem_biUnion] at hd
      obtain ⟨q, hq, hdq⟩ := hd
      exact hclosed q hq d (Nat.mem_divisors.mp hdq).1
    · intro q hq
      rw [Finset.mem_biUnion]
      exact ⟨q, hq, Nat.mem_divisors.mpr ⟨dvd_rfl, (hpos q hq).ne'⟩⟩
  have hunion : S.biUnion lpfTorsSet = S.biUnion lpfPrimSet := by rw [h1, h2, h3]
  have hstep : (∑ α ∈ S.biUnion lpfTorsSet, fourier (T := 1) y α)
      = ∑ α ∈ S.biUnion lpfPrimSet, fourier (T := 1) y α :=
    congrArg (fun z : Finset Work.Analysis.IonescuWainger.Circle =>
      ∑ α ∈ z, fourier (T := 1) y α) hunion
  have hsum : (∑ α ∈ S.biUnion lpfPrimSet, fourier (T := 1) y α)
      = ∑ q ∈ S, ∑ α ∈ lpfPrimSet q, fourier (T := 1) y α :=
    Finset.sum_biUnion (M := ℂ)
      (f := fun α : Work.Analysis.IonescuWainger.Circle => fourier (T := 1) y α)
      (s := S) (t := lpfPrimSet) hdisj
  refine hstep.trans (hsum.trans ?_)
  refine Finset.sum_congr rfl fun q hq => ?_
  show (∑ α ∈ (((Finset.range q).filter (fun a => Nat.Coprime a q)).image
      (fun a : ℕ => (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle))),
      fourier (T := 1) y α)
    = ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      fourier (T := 1) y (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle)
  exact Finset.sum_image
    (f := fun α : Work.Analysis.IonescuWainger.Circle => fourier (T := 1) y α)
    (g := fun a : ℕ => (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle))
    (s := (Finset.range q).filter (fun a => Nat.Coprime a q))
    (fun a ha b hb hab => lpfDivCircle_inj' (hpos q hq)
      (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab)

/-! ## 4. Reindexing the sieve expansion by the denominator -/

/-- **Reindexing the sieve expansion by the denominator `q ∈ iwP ρ l`** (the reverse of the
sieve/Möbius expansion of `sieveCoeff`). -/
lemma sieveRHS_reindex_local (ρ : ℝ) (l : ℕ) (y : ℤ) :
    (∑ d ∈ iwDivs ρ l, (((d : ℤ) : ℂ) * ((sieveCoeff ρ l d : ℤ) : ℂ))
        * (if (d : ℤ) ∣ y then (1 : ℂ) else 0))
      = ∑ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, ∑ d ∈ q.divisors,
          ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) * (d : ℂ)
            * (if (d : ℤ) ∣ y then (1 : ℂ) else 0) := by
  have hP0 : (∏ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, q) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact fun q hq => Work.Analysis.IonescuWainger.ne_zero_of_mem_iwP hq
  have hmemSS : ∀ d q : ℕ, q ∈ Work.Analysis.IonescuWainger.iwP ρ l → d ∣ q →
      d ∈ iwDivs ρ l := by
    intro d q hq hd
    rw [iwDivs, Nat.mem_divisors]
    exact ⟨hd.trans (Finset.dvd_prod_of_mem _ hq), hP0⟩
  have hcast : ∀ d : ℕ, ((sieveCoeff ρ l d : ℤ) : ℂ)
      = ∑ q ∈ (Work.Analysis.IonescuWainger.iwP ρ l).filter (fun q => d ∣ q),
          ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) := by
    intro d
    rw [sieveCoeff, Int.cast_sum]
  have hstep : ∀ d : ℕ, (∑ q ∈ (Work.Analysis.IonescuWainger.iwP ρ l).filter
        (fun q => d ∣ q), ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ))
      = ∑ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, if d ∣ q then
          ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) else 0 := by
    intro d
    rw [Finset.sum_filter]
  have hcomm : (∑ d ∈ iwDivs ρ l, ∑ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, ((d : ℤ) : ℂ)
        * (if d ∣ q then ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) else 0)
        * (if (d : ℤ) ∣ y then (1 : ℂ) else 0))
      = ∑ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, ∑ d ∈ iwDivs ρ l, ((d : ℤ) : ℂ)
        * (if d ∣ q then ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) else 0)
        * (if (d : ℤ) ∣ y then (1 : ℂ) else 0) := Finset.sum_comm
  calc (∑ d ∈ iwDivs ρ l, (((d : ℤ) : ℂ) * ((sieveCoeff ρ l d : ℤ) : ℂ))
        * (if (d : ℤ) ∣ y then (1 : ℂ) else 0))
      = ∑ d ∈ iwDivs ρ l, (((d : ℤ) : ℂ)
          * (∑ q ∈ (Work.Analysis.IonescuWainger.iwP ρ l).filter (fun q => d ∣ q),
              ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ)))
          * (if (d : ℤ) ∣ y then (1 : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hcast d]
    _ = ∑ d ∈ iwDivs ρ l, (((d : ℤ) : ℂ)
          * (∑ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, if d ∣ q then
              ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) else 0))
          * (if (d : ℤ) ∣ y then (1 : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hstep d]
    _ = ∑ d ∈ iwDivs ρ l, ∑ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, ((d : ℤ) : ℂ)
          * (if d ∣ q then ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) else 0)
          * (if (d : ℤ) ∣ y then (1 : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, ∑ d ∈ iwDivs ρ l, ((d : ℤ) : ℂ)
          * (if d ∣ q then ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) else 0)
          * (if (d : ℤ) ∣ y then (1 : ℂ) else 0) := hcomm
    _ = ∑ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, ∑ d ∈ q.divisors,
          ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) * (d : ℂ)
            * (if (d : ℤ) ∣ y then (1 : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        have hq0 : q ≠ 0 := Work.Analysis.IonescuWainger.ne_zero_of_mem_iwP hq
        have hsub : q.divisors ⊆ iwDivs ρ l := fun d hd =>
          hmemSS d q hq (Nat.mem_divisors.mp hd).1
        rw [← Finset.sum_subset hsub]
        · refine Finset.sum_congr rfl fun d hd => ?_
          rw [if_pos (Nat.mem_divisors.mp hd).1]
          push_cast
          ring
        · intro d hd hdnot
          have hnd : ¬ (d ∣ q) := fun hdq => hdnot (Nat.mem_divisors.mpr ⟨hdq, hq0⟩)
          simp [hnd]

/-! ## 5. The sieve decomposition of the arithmetic character -/

/-- **The sieve (Möbius) decomposition of the Ionescu–Wainger arithmetic character**:
`arithChar ρ l y = Σ_{d ∈ iwDivs ρ l} (d · sieveCoeff ρ l d) [d ∣ y]`. -/
theorem arithChar_sieve_local (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (y : ℤ) :
    Work.KMTAreas.A7.arithChar ρ l y
      = ∑ d ∈ iwDivs ρ l,
          (((d : ℤ) : ℂ) * ((sieveCoeff ρ l d : ℤ) : ℂ))
            * (if (d : ℤ) ∣ y then (1 : ℂ) else 0) := by
  have h1 : Work.KMTAreas.A7.arithChar ρ l y
      = ∑ q ∈ Work.Analysis.IonescuWainger.iwP ρ l,
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            fourier (T := 1) y (((a : ℝ) / (q : ℝ)) : Work.Analysis.IonescuWainger.Circle) := by
    rw [Work.KMTAreas.A7.arithChar]
    exact torsionDecomp_local (Work.Analysis.IonescuWainger.iwP ρ l)
      (fun q hq => Work.Analysis.IonescuWainger.pos_of_mem_iwP hq)
      (fun q hq d hd => iwP_dvd_closed_aux ρ hρ1 l d q hq hd) y
  rw [h1]
  refine (Finset.sum_congr rfl fun q hq =>
    ramanujanSum_local q (Work.Analysis.IonescuWainger.pos_of_mem_iwP hq) y).trans ?_
  exact (sieveRHS_reindex_local ρ l y).symm

/-! ## 6. The decimated dilation identity -/

/-- **The convolution kernel of `decimDilFam` is the dilate of the KMT profile**: the `d`-decimated
dilation family at scale `σ_m = lpfScale m₀ m` is the convolution with
`j ↦ cw (η_{≤k}) (d · j)`, `k = -(m₀ + m)`. -/
lemma decimDilFam_eq_tsum_cw_aux (m₀ m d : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    Work.A7Hi2.decimDilFam m₀ Work.KMTAreas.A7Hi.kmtPhiSch d f m x
      = ∑' j : ℤ,
          Work.KMTAreas.A7.cw
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                (-((m₀ : ℤ) + (m : ℤ)))) ((d : ℤ) * j)
            * f (x - (d : ℤ) * j) := by
  have hσR : (2 : ℝ) ^ (-((m₀ : ℤ) + (m : ℤ)))
      = ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ)⁻¹ := by
    rw [show -((m₀ : ℤ) + (m : ℤ)) = -(((m₀ + m : ℕ)) : ℤ) from by push_cast; ring]
    rw [zpow_neg, zpow_natCast, ← Work.KMTAreas.A7Hi.lpfScale_cast m₀ m]
  have hscal : (1 / (((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ) : ℂ))
      = (((2 : ℝ) ^ (-((m₀ : ℤ) + (m : ℤ))) : ℝ) : ℂ) := by
    rw [one_div, hσR]
    push_cast
    ring
  unfold Work.A7Hi2.decimDilFam
  refine tsum_congr fun j => ?_
  rw [Work.KMTAreas.A7G.cw_etaCut_eq_dilateG, Work.KMTAreas.A7Hi.kmtPhiSch_coe]
  have h2 : (2 : ℝ) ^ (-((m₀ : ℤ) + (m : ℤ))) * (((d : ℤ) * j : ℤ) : ℝ)
      = (((d : ℤ) * j : ℤ) : ℝ) / ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ) := by
    rw [hσR]; ring
  rw [hscal, h2]
  rw [show (((d : ℤ) : ℝ) * (j : ℝ)) = (((d : ℤ) * j : ℤ) : ℝ) from by push_cast; ring]

/-! ## 7. The sieve decomposition of the low-pass walk -/

/-- **The pointwise sieve (Möbius/decimated-dilation) decomposition of the Ionescu–Wainger
low-pass walk.**  See the module docstring. -/
theorem lpfSieveDecomp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p)
    (hptop : p < ⊤) (l₁ m₀ m : ℕ) (f : ℤ → ℂ)
    (hf : Summable (fun n : ℤ => ‖f n‖ ^ p.toReal)) (x : ℤ) :
    Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x
      = ∑ d ∈ Work.A7Hi2.iwDivs ρ l₁,
          (((d : ℤ) : ℂ) * ((Work.A7Hi2.sieveCoeff ρ l₁ d : ℤ) : ℂ))
            * Work.A7Hi2.decimDilFam m₀ Work.KMTAreas.A7Hi.kmtPhiSch d f m x := by
  obtain ⟨B, hB⟩ := exists_norm_bound_of_summable_rpow
    (ENNReal.toReal_pos (ne_of_gt (lt_trans one_pos hp)) (ne_of_lt hptop)) hf
  have hsum_g : Summable (fun j : ℤ =>
      Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
        (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j)) := summable_cw_mul_of_bdd hB
  have hL : Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x
      = ∑' j : ℤ, Work.KMTAreas.A7.arithChar ρ l₁ (-j)
          * Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
              (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j) := by
    rw [Work.KMTAreas.A7Hi.lpf, Work.KMTContract.kmtProj_apply]
    refine tsum_congr fun j => ?_
    rw [Work.KMTAreas.A7Hi.kmtKernel_eq_arithChar_cw]
  have hstep2 : ∀ j : ℤ, Work.KMTAreas.A7.arithChar ρ l₁ (-j)
        * Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j)
      = (∑ d ∈ iwDivs ρ l₁, (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))
            * (if (d : ℤ) ∣ j then (1 : ℂ) else 0))
        * Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j) := by
    intro j
    rw [arithChar_sieve_local ρ hρ hρ1 l₁ (-j)]
    have hs : (∑ d ∈ iwDivs ρ l₁, (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))
          * (if (d : ℤ) ∣ -j then (1 : ℂ) else 0))
        = ∑ d ∈ iwDivs ρ l₁, (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))
          * (if (d : ℤ) ∣ j then (1 : ℂ) else 0) := by
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [Int.dvd_neg]
    rw [hs]
  have hstep3 : ∀ j : ℤ, (∑ d ∈ iwDivs ρ l₁,
        (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))
            * (if (d : ℤ) ∣ j then (1 : ℂ) else 0))
        * Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j)
      = ∑ d ∈ iwDivs ρ l₁, (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))
          * ((if (d : ℤ) ∣ j then (1 : ℂ) else 0)
              * (Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                  (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j))) := by
    intro j
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have hstep4 : (∑' j : ℤ, ∑ d ∈ iwDivs ρ l₁,
        (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))
          * ((if (d : ℤ) ∣ j then (1 : ℂ) else 0)
              * (Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                  (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j))))
      = ∑ d ∈ iwDivs ρ l₁, (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))
          * ∑' j : ℤ, ((if (d : ℤ) ∣ j then (1 : ℂ) else 0)
              * (Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                  (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j))) := by
    refine (Summable.tsum_finsetSum (s := iwDivs ρ l₁)
      (f := fun (d : ℕ) (j : ℤ) => (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))
          * ((if (d : ℤ) ∣ j then (1 : ℂ) else 0)
              * (Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                  (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j)))) ?_).trans ?_
    · intro d _
      have hmaj : Summable (fun j : ℤ =>
          ‖(((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))‖ *
            (‖Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                (-((m₀ : ℤ) + (m : ℤ)))) j‖ * B)) :=
        (((Work.KMTAreas.A7.summable_cw_etaCut (-((m₀ : ℤ) + (m : ℤ)))).mul_right B).mul_left
          ‖(((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))‖)
      refine Summable.of_norm_bounded hmaj (fun j => ?_)
      simp only [norm_mul]
      have hI : ‖(if (d : ℤ) ∣ j then (1 : ℂ) else 0)‖ ≤ 1 := by
        by_cases h : (d : ℤ) ∣ j <;> simp [h]
      have hf1 : ‖f (x - j)‖ ≤ B := hB (x - j)
      have hstep : ‖(if (d : ℤ) ∣ j then (1 : ℂ) else 0)‖
            * (‖Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut
                Work.KMTContract.kmtEta (-((m₀ : ℤ) + (m : ℤ)))) j‖ * ‖f (x - j)‖)
          ≤ ‖Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut
                Work.KMTContract.kmtEta (-((m₀ : ℤ) + (m : ℤ)))) j‖ * B := by
        calc ‖(if (d : ℤ) ∣ j then (1 : ℂ) else 0)‖
              * (‖Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut
                  Work.KMTContract.kmtEta (-((m₀ : ℤ) + (m : ℤ)))) j‖ * ‖f (x - j)‖)
            ≤ 1 * (‖Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut
                  Work.KMTContract.kmtEta (-((m₀ : ℤ) + (m : ℤ)))) j‖ * ‖f (x - j)‖) :=
              mul_le_mul_of_nonneg_right hI (by positivity)
          _ = ‖Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut
                  Work.KMTContract.kmtEta (-((m₀ : ℤ) + (m : ℤ)))) j‖ * ‖f (x - j)‖ := one_mul _
          _ ≤ ‖Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut
                  Work.KMTContract.kmtEta (-((m₀ : ℤ) + (m : ℤ)))) j‖ * B :=
              mul_le_mul_of_nonneg_left hf1 (norm_nonneg _)
      have hA : 0 ≤ ‖(((d : ℤ) : ℂ))‖ * ‖((sieveCoeff ρ l₁ d : ℤ) : ℂ)‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left hstep hA
    · refine Finset.sum_congr rfl fun d _ => ?_
      rw [tsum_mul_left]
  have hstep5 : ∀ d ∈ iwDivs ρ l₁,
      (∑' j : ℤ, ((if (d : ℤ) ∣ j then (1 : ℂ) else 0)
              * (Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                  (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j))))
        = ∑' mm : ℤ, Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut
            Work.KMTContract.kmtEta (-((m₀ : ℤ) + (m : ℤ)))) ((d : ℤ) * mm)
              * f (x - (d : ℤ) * mm) := by
    intro d hd
    have hd0 : d ≠ 0 := by
      obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hd
      intro h
      rw [h] at hdvd
      exact hne (Nat.zero_dvd.mp hdvd)
    have h1 : (fun j : ℤ => (if (d : ℤ) ∣ j then (1 : ℂ) else 0)
          * (Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
              (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j)))
        = fun j : ℤ => (if (d : ℤ) ∣ j then
            (Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
              (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j)) else 0) := by
      funext j
      by_cases h : (d : ℤ) ∣ j <;> simp [h]
    rw [h1, Work.KMTAreas.A7Hi.tsum_of_dvd d hd0]
  calc Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x
      = ∑' j : ℤ, Work.KMTAreas.A7.arithChar ρ l₁ (-j)
          * Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
              (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j) := hL
    _ = ∑' j : ℤ, (∑ d ∈ iwDivs ρ l₁,
            (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))
            * (if (d : ℤ) ∣ j then (1 : ℂ) else 0))
        * Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j) := tsum_congr hstep2
    _ = ∑' j : ℤ, ∑ d ∈ iwDivs ρ l₁, (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))
          * ((if (d : ℤ) ∣ j then (1 : ℂ) else 0)
              * (Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                  (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j))) := tsum_congr hstep3
    _ = ∑ d ∈ iwDivs ρ l₁, (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))
          * ∑' j : ℤ, ((if (d : ℤ) ∣ j then (1 : ℂ) else 0)
              * (Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                  (-((m₀ : ℤ) + (m : ℤ)))) j * f (x - j))) := hstep4
    _ = ∑ d ∈ iwDivs ρ l₁, (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))
          * ∑' mm : ℤ, Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut
              Work.KMTContract.kmtEta (-((m₀ : ℤ) + (m : ℤ)))) ((d : ℤ) * mm)
                * f (x - (d : ℤ) * mm) :=
        Finset.sum_congr rfl fun d hd => by rw [hstep5 d hd]
    _ = ∑ d ∈ iwDivs ρ l₁, (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))
          * Work.A7Hi2.decimDilFam m₀ Work.KMTAreas.A7Hi.kmtPhiSch d f m x :=
        Finset.sum_congr rfl fun d _ => by rw [decimDilFam_eq_tsum_cw_aux]

end Work.A7Hi2
