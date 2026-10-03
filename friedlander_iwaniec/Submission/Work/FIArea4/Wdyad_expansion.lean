import Mathlib
import Submission.Work.FIArea4.WdyadSetup
import Submission.Work.FIArea4.WdyadPoisson
import Submission.Work.FIArea4.WdyadExpansionDefs
import Submission.Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators FourierTransform

noncomputable section

set_option linter.style.haveILetI false

/-! ## Step 1: the indicator is summable against a decaying function -/

lemma norm_cind_le_one (L : ℕ) (s : ℤ) (c : ℕ) : ‖cind L s c‖ ≤ 1 := by
  unfold cind; split <;> simp

/-! ## Step 2: rewriting the residue class sum as an arithmetic progression -/

/-- The integers congruent to `c` modulo `L` are exactly `c + m L`, `m : ℤ`. -/
def residueEquiv (L c : ℕ) [NeZero L] :
    ℤ ≃ {s : ℤ // (s : ZMod L) = (c : ZMod L)} where
  toFun m := ⟨(c : ℤ) + m * (L:ℤ), by
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero]⟩
  invFun s := (s.1 - (c:ℤ)) / (L:ℤ)
  left_inv m := by
    show ((c:ℤ) + m * (L:ℤ) - (c:ℤ)) / (L:ℤ) = m
    have hL0 : (L:ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
    rw [add_sub_cancel_left]
    exact Int.mul_ediv_cancel m hL0
  right_inv s := by
    apply Subtype.ext
    show (c:ℤ) + (s.1 - (c:ℤ)) / (L:ℤ) * (L:ℤ) = s.1
    have hdvd : (L:ℤ) ∣ s.1 - (c:ℤ) := by
      have h : (((s.1 - (c:ℤ)) : ℤ) : ZMod L) = 0 := by
        rw [Int.cast_sub, Int.cast_natCast, s.2, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp h
    rw [Int.ediv_mul_cancel hdvd, add_sub_cancel]

lemma tsum_cind_eq_tsum (F : ℝ → ℂ) {L : ℕ} [NeZero L] (c : ℕ) :
    (∑' s : ℤ, F (s:ℝ) * cind L s c)
      = ∑' m : ℤ, F (((c:ℤ) + m * (L:ℤ) : ℤ) : ℝ) := by
  have hfun : ∀ s : ℤ, F (s:ℝ) * cind L s c
      = Set.indicator {s : ℤ | (s : ZMod L) = (c : ZMod L)} (fun s => F (s:ℝ)) s := by
    intro s
    by_cases hs : (s : ZMod L) = (c : ZMod L)
    · rw [cind, if_pos hs, mul_one, Set.indicator_of_mem (show s ∈ _ from hs)]
    · rw [cind, if_neg hs, mul_zero, Set.indicator_of_notMem (show s ∉ _ from hs)]
  rw [tsum_congr hfun, ← _root_.tsum_subtype]
  exact (Equiv.tsum_eq (residueEquiv L c)
    (fun s : {s : ℤ // (s : ZMod L) = (c : ZMod L)} => F ((s:ℤ):ℝ))).symm

/-- Poisson summation over the residue class `s ≡ c (mod L)`. -/
lemma tsum_cind_poisson (F : ℝ → ℂ) (hc : Continuous F) {b : ℝ} (hb : 1 < b)
    (hF : F =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (hF' : (FourierTransform.fourier F) =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (L : ℕ) (hL : 0 < L) (c : ℕ) :
    (∑' s : ℤ, F (s:ℝ) * cind L s c)
      = (1/((L:ℕ):ℝ)) * ∑' k : ℤ, (FourierTransform.fourier F) ((k:ℝ)/(L:ℝ))
          * Complex.exp (2*Real.pi*Complex.I*(c:ℝ)*(k:ℝ)/(L:ℝ)) := by
  haveI : NeZero L := ⟨hL.ne'⟩
  have h1 : (∑' s : ℤ, F (s:ℝ) * cind L s c) = ∑' m : ℤ, F ((c:ℝ) + (m:ℝ)*(L:ℝ)) := by
    rw [tsum_cind_eq_tsum F c]
    refine tsum_congr (fun m => ?_)
    congr 1; push_cast; ring
  rw [h1]
  have h2 : (fun m : ℤ => F ((c:ℝ) + (m:ℝ)*(L:ℝ))) = (fun m : ℤ => F ((c:ℝ) + ↑(m * ↑L))) := by
    funext m; congr 1; push_cast; ring
  rw [h2, poisson_residue F hc hb hF hF' L hL (c:ℝ)]

/-- Poisson summation after summing a finite combination of residue classes. -/
theorem pair_tsum_poisson (F : ℝ → ℂ) (hc : Continuous F) {b : ℝ} (hb : 1 < b)
    (hF : F =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (hF' : (FourierTransform.fourier F) =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (L : ℕ) (hL : 0 < L) (r : ℕ) (g : ℕ → ℂ) :
    (∑' s : ℤ, F (s:ℝ) * (∑ a ∈ Finset.range L, g a * cind L s (r*a)))
      = (1/((L:ℕ):ℝ)) * ∑' k : ℤ, (FourierTransform.fourier F) ((k:ℝ)/(L:ℝ))
          * (∑ a ∈ Finset.range L, g a * Complex.exp (2*Real.pi*Complex.I*(r:ℝ)*(k:ℝ)*(a:ℝ)/(L:ℝ))) := by
  haveI : NeZero L := ⟨hL.ne'⟩
  have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast hL
  have hFsum : Summable fun s : ℤ => F (s:ℝ) := by
    have h := Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow (G := F) hb hF (d := 1) one_pos
    simpa using h
  have hcindsum : ∀ c : ℕ, Summable fun s : ℤ => F (s:ℝ) * cind L s c := by
    intro c
    refine (hFsum.norm).of_norm_bounded (fun s => ?_)
    rw [norm_mul]
    calc ‖F (s:ℝ)‖ * ‖cind L s c‖ ≤ ‖F (s:ℝ)‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_cind_le_one L s c) (norm_nonneg _)
      _ = ‖F (s:ℝ)‖ := mul_one _
  have hSsum : ∀ a ∈ Finset.range L, Summable fun s : ℤ => F (s:ℝ) * (g a * cind L s (r*a)) := by
    intro a _
    refine ((hFsum.norm).mul_left ‖g a‖).of_norm_bounded (fun s => ?_)
    rw [norm_mul, norm_mul]
    calc ‖F (s:ℝ)‖ * (‖g a‖ * ‖cind L s (r*a)‖) ≤ ‖F (s:ℝ)‖ * (‖g a‖ * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (norm_cind_le_one L s (r*a)) (norm_nonneg _)) (norm_nonneg _)
      _ = ‖g a‖ * ‖F (s:ℝ)‖ := by ring
  have hKsum : Summable fun k : ℤ => (FourierTransform.fourier F) ((k:ℝ)/(L:ℝ)) :=
    Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow (G := FourierTransform.fourier F) hb hF' hLpos
  have hksum : ∀ a ∈ Finset.range L, Summable fun k : ℤ =>
      (FourierTransform.fourier F) ((k:ℝ)/(L:ℝ))
        * (g a * Complex.exp (2*Real.pi*Complex.I*(r:ℝ)*(k:ℝ)*(a:ℝ)/(L:ℝ))) := by
    intro a _
    refine ((hKsum.norm).mul_left ‖g a‖).of_norm_bounded (fun k => ?_)
    rw [norm_mul, norm_mul]
    calc ‖(FourierTransform.fourier F) ((k:ℝ)/(L:ℝ))‖
            * (‖g a‖ * ‖Complex.exp (2*Real.pi*Complex.I*(r:ℝ)*(k:ℝ)*(a:ℝ)/(L:ℝ))‖)
          ≤ ‖(FourierTransform.fourier F) ((k:ℝ)/(L:ℝ))‖ * (‖g a‖ * 1) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (norm_nonneg _)
            rw [Complex.norm_exp]
            simp
      _ = ‖g a‖ * ‖(FourierTransform.fourier F) ((k:ℝ)/(L:ℝ))‖ := by ring
  rw [show (∑' s : ℤ, F (s:ℝ) * (∑ a ∈ Finset.range L, g a * cind L s (r*a)))
      = ∑' s : ℤ, ∑ a ∈ Finset.range L, F (s:ℝ) * (g a * cind L s (r*a)) from
        tsum_congr (fun s => Finset.mul_sum _ _ _)]
  rw [Summable.tsum_finsetSum hSsum]
  have hA : ∀ a : ℕ, (∑' s : ℤ, F (s:ℝ) * (g a * cind L s (r*a)))
      = (1/((L:ℕ):ℝ)) * ∑' k : ℤ, (FourierTransform.fourier F) ((k:ℝ)/(L:ℝ))
          * (g a * Complex.exp (2*Real.pi*Complex.I*(r:ℝ)*(k:ℝ)*(a:ℝ)/(L:ℝ))) := by
    intro a
    have h1 := tsum_cind_poisson F hc hb hF hF' L hL (r*a)
    have hstep1 : (∑' s : ℤ, F (s:ℝ) * (g a * cind L s (r*a)))
        = g a * ∑' s : ℤ, F (s:ℝ) * cind L s (r*a) := by
      rw [show (fun s : ℤ => F (s:ℝ) * (g a * cind L s (r*a)))
          = (fun s : ℤ => g a * (F (s:ℝ) * cind L s (r*a))) from by funext s; ring]
      rw [tsum_mul_left]
    rw [hstep1, h1]
    rw [show g a * ((1/((L:ℕ):ℝ)) * (∑' k : ℤ, (FourierTransform.fourier F) ((k:ℝ)/(L:ℝ))
          * Complex.exp (2*Real.pi*Complex.I*((r*a:ℕ):ℝ)*(k:ℝ)/(L:ℝ))))
        = (1/((L:ℕ):ℝ)) * (g a * (∑' k : ℤ, (FourierTransform.fourier F) ((k:ℝ)/(L:ℝ))
          * Complex.exp (2*Real.pi*Complex.I*((r*a:ℕ):ℝ)*(k:ℝ)/(L:ℝ)))) from by ring]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [show Complex.exp (2*Real.pi*Complex.I*((r*a:ℕ):ℝ)*(k:ℝ)/(L:ℝ))
        = Complex.exp (2*Real.pi*Complex.I*(r:ℝ)*(k:ℝ)*(a:ℝ)/(L:ℝ)) from by
          congr 1; push_cast; ring]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hA a)]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Summable.tsum_finsetSum hksum]
  apply tsum_congr
  intro k
  rw [Finset.mul_sum]

/-! ## Step 3: expanding `|TZ|²` into pairs of residue classes -/

lemma star_MentryZ (d a r : ℕ) (s : ℤ) :
    (starRingEnd ℂ) (MentryZ d a r s) = MentryZ d a r s := by
  unfold MentryZ
  split <;> simp

lemma MentryZ_eq_cind {d r : ℕ} (a : ℕ) (s : ℤ) (h : Nat.Coprime r d) :
    MentryZ d a r s = (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d) : ℂ) * cind d s (r*a) := by
  unfold MentryZ cind
  rw [show ((r * a : ℕ) : ZMod d) = (r : ZMod d) * (a : ZMod d) from Nat.cast_mul r a]
  by_cases hP : (s : ZMod d) = (r : ZMod d) * (a : ZMod d)
  · rw [if_pos ⟨h, hP⟩, if_pos hP, mul_one]
  · rw [if_neg (fun hc => hP hc.2), if_neg hP, mul_zero]

/-- The pair of residue-class `TZ` contributions with moduli `d₁, d₂` re-expressed on the single
modulus `[d₁, d₂]`. -/
def ATM (γ : ℕ → ℕ → ℂ) (r : ℕ) (d1 d2 : ℕ) (s : ℤ) : ℂ :=
  if Nat.Coprime r (d1*d2) then
    (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℂ) * (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℂ)
      * (∑ a ∈ Finset.range (Nat.lcm d1 d2),
          γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2)
            * cind (Nat.lcm d1 d2) s (r*a))
  else 0

lemma pair_expand {d1 d2 r : ℕ} [NeZero d1] [NeZero d2] [NeZero (Nat.lcm d1 d2)]
    (γ : ℕ → ℕ → ℂ) (s : ℤ) :
    (∑ a1 ∈ Finset.range d1, ∑ a2 ∈ Finset.range d2,
        (γ a1 d1 * MentryZ d1 a1 r s) * ((starRingEnd ℂ) (γ a2 d2) * MentryZ d2 a2 r s))
      = ATM γ r d1 d2 s := by
  unfold ATM
  by_cases hc : Nat.Coprime r (d1*d2)
  · rw [if_pos hc]
    have h1 : Nat.Coprime r d1 := hc.coprime_dvd_right (dvd_mul_right d1 d2)
    have h2 : Nat.Coprime r d2 := hc.coprime_dvd_right (dvd_mul_left d2 d1)
    have hkey : (∑ a1 ∈ Finset.range d1, ∑ a2 ∈ Finset.range d2,
        (γ a1 d1 * MentryZ d1 a1 r s) * ((starRingEnd ℂ) (γ a2 d2) * MentryZ d2 a2 r s))
        = (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℂ) * (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℂ)
          * (∑ a1 ∈ Finset.range d1, ∑ a2 ∈ Finset.range d2,
              (γ a1 d1 * (starRingEnd ℂ) (γ a2 d2)) * cind d1 s (r*a1) * cind d2 s (r*a2)) := by
      rw [show (∑ a1 ∈ Finset.range d1, ∑ a2 ∈ Finset.range d2,
          (γ a1 d1 * MentryZ d1 a1 r s) * ((starRingEnd ℂ) (γ a2 d2) * MentryZ d2 a2 r s))
          = ∑ a1 ∈ Finset.range d1, ∑ a2 ∈ Finset.range d2,
              ((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℂ) * (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℂ))
                * ((γ a1 d1 * (starRingEnd ℂ) (γ a2 d2)) * cind d1 s (r*a1) * cind d2 s (r*a2)) from by
            refine Finset.sum_congr rfl (fun a1 _ => Finset.sum_congr rfl (fun a2 _ => ?_))
            rw [MentryZ_eq_cind (h := h1) a1 s, MentryZ_eq_cind (h := h2) a2 s]
            ring]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a1 _ => ?_)
      rw [Finset.mul_sum]
    rw [hkey]
    rw [cind_double hc (fun a1 a2 => γ a1 d1 * (starRingEnd ℂ) (γ a2 d2)) s]
  · rw [if_neg hc]
    have hdisj : ¬ Nat.Coprime r d1 ∨ ¬ Nat.Coprime r d2 := by
      by_contra hcon
      rw [not_or] at hcon
      simp only [not_not] at hcon
      exact hc (hcon.1.mul_right hcon.2)
    rcases hdisj with h1 | h2
    · refine Finset.sum_eq_zero (fun a1 _ => Finset.sum_eq_zero (fun a2 _ => ?_))
      have hM : MentryZ d1 a1 r s = 0 := by
        unfold MentryZ; rw [if_neg (fun hc' => h1 hc'.1)]
      rw [hM]; simp
    · refine Finset.sum_eq_zero (fun a1 _ => Finset.sum_eq_zero (fun a2 _ => ?_))
      have hM : MentryZ d2 a2 r s = 0 := by
        unfold MentryZ; rw [if_neg (fun hc' => h2 hc'.1)]
      rw [hM]; simp

/-- Pointwise expansion of the squared modulus of the class sum. -/
lemma normSq_TZ_expand (D R S : ℕ) (hD : 1 ≤ D) (γ : ℕ → ℕ → ℂ) (r : ℕ) (s : ℤ) :
    ((Complex.normSq (TZ D R S γ r s) : ℝ) : ℂ)
      = ∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ Finset.Ioc D (2*D), ATM γ r d1 d2 s := by
  rw [← Complex.mul_conj]
  have hstar : (starRingEnd ℂ) (TZ D R S γ r s)
      = ∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
          (starRingEnd ℂ) (γ a d) * MentryZ d a r s := by
    unfold TZ
    rw [map_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_mul, star_MentryZ]
  rw [hstar]
  unfold TZ
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun d1 hd1 => Finset.sum_congr rfl (fun d2 hd2 => ?_))
  rw [Finset.sum_mul_sum]
  have hd1pos : 0 < d1 := by have h := (Finset.mem_Ioc.mp hd1).1; omega
  have hd2pos : 0 < d2 := by have h := (Finset.mem_Ioc.mp hd2).1; omega
  haveI : NeZero d1 := ⟨hd1pos.ne'⟩
  haveI : NeZero d2 := ⟨hd2pos.ne'⟩
  haveI : NeZero (Nat.lcm d1 d2) := ⟨(Nat.lcm_pos hd1pos hd2pos).ne'⟩
  exact pair_expand γ s

/-! ## Step 4: summability and the per-pair Poisson step -/

lemma norm_ATM_le (γ : ℕ → ℕ → ℂ) (r d1 d2 : ℕ) (s : ℤ) :
    ‖ATM γ r d1 d2 s‖ ≤ (∑ a ∈ Finset.range (Nat.lcm d1 d2), ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖)
        * (‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ)‖ * ‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ)‖) := by
  unfold ATM
  by_cases hc : Nat.Coprime r (d1*d2)
  · rw [if_pos hc]
    have h2 : ‖∑ a ∈ Finset.range (Nat.lcm d1 d2),
          γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * cind (Nat.lcm d1 d2) s (r*a)‖
        ≤ ∑ a ∈ Finset.range (Nat.lcm d1 d2), ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖ := by
      calc ‖∑ a ∈ Finset.range (Nat.lcm d1 d2),
            γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * cind (Nat.lcm d1 d2) s (r*a)‖
          ≤ ∑ a ∈ Finset.range (Nat.lcm d1 d2),
              ‖γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * cind (Nat.lcm d1 d2) s (r*a)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ a ∈ Finset.range (Nat.lcm d1 d2), ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖ := by
          refine Finset.sum_le_sum (fun a _ => ?_)
          calc ‖γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * cind (Nat.lcm d1 d2) s (r*a)‖
              = ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖ * ‖cind (Nat.lcm d1 d2) s (r*a)‖ := by
                rw [norm_mul, norm_mul, starRingEnd_apply, norm_star]
            _ ≤ ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖ * 1 :=
                mul_le_mul_of_nonneg_left (norm_cind_le_one _ _ _) (by positivity)
            _ = ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖ := by ring
    calc ‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ) * ((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ)
          * (∑ a ∈ Finset.range (Nat.lcm d1 d2), γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * cind (Nat.lcm d1 d2) s (r*a))‖
        = ‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ)‖ * ‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ)‖
          * ‖∑ a ∈ Finset.range (Nat.lcm d1 d2), γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * cind (Nat.lcm d1 d2) s (r*a)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ)‖ * ‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ)‖
          * (∑ a ∈ Finset.range (Nat.lcm d1 d2), ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (∑ a ∈ Finset.range (Nat.lcm d1 d2), ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖)
          * (‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ)‖ * ‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ)‖) := by ring
  · rw [if_neg hc, norm_zero]
    positivity

lemma summable_mul_ATM (F : ℝ → ℂ) (hFsum : Summable fun s : ℤ => F (s:ℝ))
    (γ : ℕ → ℕ → ℂ) (r d1 d2 : ℕ) :
    Summable fun s : ℤ => F (s:ℝ) * ATM γ r d1 d2 s := by
  refine ((hFsum.norm).mul_left ((∑ a ∈ Finset.range (Nat.lcm d1 d2), ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖)
      * (‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ)‖ * ‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ)‖))).of_norm_bounded (fun s => ?_)
  rw [norm_mul]
  calc ‖F (s:ℝ)‖ * ‖ATM γ r d1 d2 s‖
      ≤ ‖F (s:ℝ)‖ * ((∑ a ∈ Finset.range (Nat.lcm d1 d2), ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖)
          * (‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ)‖ * ‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ)‖)) :=
        mul_le_mul_of_nonneg_left (norm_ATM_le γ r d1 d2 s) (norm_nonneg _)
    _ = (∑ a ∈ Finset.range (Nat.lcm d1 d2), ‖γ (a % d1) d1‖ * ‖γ (a % d2) d2‖)
          * (‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ)‖ * ‖((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ)‖) * ‖F (s:ℝ)‖ := by ring

/-- The per-pair Poisson step. -/
lemma pair_value (F : ℝ → ℂ) (hc : Continuous F) {b : ℝ} (hb : 1 < b)
    (hF : F =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (hF' : (FourierTransform.fourier F) =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (γ : ℕ → ℕ → ℂ) (r : ℕ) {d1 d2 : ℕ} [NeZero d1] [NeZero d2] :
    (∑' s : ℤ, F (s:ℝ) * ATM γ r d1 d2 s)
      = (if Nat.Coprime r (d1*d2) then
            (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℂ) * (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℂ)
              * ((1/((Nat.lcm d1 d2 : ℕ) : ℝ)) * ∑' k : ℤ, (FourierTransform.fourier F) ((k:ℝ)/((Nat.lcm d1 d2 : ℕ):ℝ)) *
                  (∑ a ∈ Finset.range (Nat.lcm d1 d2),
                     γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
                       Complex.exp (2*Real.pi*Complex.I*(r:ℝ)*(k:ℝ)*(a:ℝ)/((Nat.lcm d1 d2 : ℕ):ℝ))))
           else 0) := by
  by_cases hc' : Nat.Coprime r (d1*d2)
  · rw [if_pos hc']
    have hLp : 0 < Nat.lcm d1 d2 := Nat.lcm_pos (NeZero.pos d1) (NeZero.pos d2)
    have hATM : ATM γ r d1 d2 = fun s : ℤ => (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℂ)
        * (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℂ)
        * (∑ a ∈ Finset.range (Nat.lcm d1 d2), γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2)
            * cind (Nat.lcm d1 d2) s (r*a)) := by
      funext s; unfold ATM; rw [if_pos hc']
    rw [hATM]
    have hstep : (∑' s : ℤ, F (s:ℝ) * ((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℂ)
          * (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℂ)
          * (∑ a ∈ Finset.range (Nat.lcm d1 d2), γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2)
              * cind (Nat.lcm d1 d2) s (r*a))))
        = ((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℂ) * (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℂ))
          * (∑' s : ℤ, F (s:ℝ) * (∑ a ∈ Finset.range (Nat.lcm d1 d2),
              (γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2)) * cind (Nat.lcm d1 d2) s (r*a))) := by
      rw [show (fun s : ℤ => F (s:ℝ) * ((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℂ)
            * (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℂ)
            * (∑ a ∈ Finset.range (Nat.lcm d1 d2), γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2)
                * cind (Nat.lcm d1 d2) s (r*a))))
          = (fun s : ℤ => ((jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℂ) * (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℂ))
              * (F (s:ℝ) * (∑ a ∈ Finset.range (Nat.lcm d1 d2),
                  (γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2)) * cind (Nat.lcm d1 d2) s (r*a)))) from by
            funext s; ring]
      rw [tsum_mul_left]
    rw [hstep, pair_tsum_poisson F hc hb hF hF'
      (Nat.lcm d1 d2) hLp r (fun a => γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2))]
  · rw [if_neg hc']
    rw [show (fun s : ℤ => F (s:ℝ) * ATM γ r d1 d2 s) = (fun _ : ℤ => 0) from by
      funext s; unfold ATM; rw [if_neg hc']; ring]
    simp

/-! ## Step 5: the theorem -/

theorem Wdyad_expansion (F : ℝ → ℂ) (hc : Continuous F) {b : ℝ} (hb : 1 < b)
    (hF : F =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (hF' : (FourierTransform.fourier F) =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (D R S : ℕ) (hD : 1 ≤ D) (γ : ℕ → ℕ → ℂ) (r : ℕ) :
    (∑' s : ℤ, F (s:ℝ) * ((Complex.normSq (TZ D R S γ r s) : ℝ) : ℂ))
      = ∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ Finset.Ioc D (2*D),
          (if Nat.Coprime r (d1*d2) then
            (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d1) : ℂ) * (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d2) : ℂ)
              * ((1/((Nat.lcm d1 d2 : ℕ) : ℝ)) * ∑' k : ℤ, (FourierTransform.fourier F) ((k:ℝ)/((Nat.lcm d1 d2 : ℕ):ℝ)) *
                  (∑ a ∈ Finset.range (Nat.lcm d1 d2),
                     γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
                       Complex.exp (2*Real.pi*Complex.I*(r:ℝ)*(k:ℝ)*(a:ℝ)/((Nat.lcm d1 d2 : ℕ):ℝ))))
           else 0) := by
  have hFsum : Summable fun s : ℤ => F (s:ℝ) := by
    have h := Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow (G := F) hb hF (d := 1) one_pos
    simpa using h
  have hpt : ∀ s : ℤ, F (s:ℝ) * ((Complex.normSq (TZ D R S γ r s) : ℝ) : ℂ)
      = ∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ Finset.Ioc D (2*D), F (s:ℝ) * ATM γ r d1 d2 s := by
    intro s
    rw [normSq_TZ_expand D R S hD γ r s]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d1 _ => ?_)
    rw [Finset.mul_sum]
  rw [show (∑' s : ℤ, F (s:ℝ) * ((Complex.normSq (TZ D R S γ r s) : ℝ) : ℂ))
      = ∑' s : ℤ, ∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ Finset.Ioc D (2*D), F (s:ℝ) * ATM γ r d1 d2 s
      from tsum_congr hpt]
  rw [Summable.tsum_finsetSum (s := Finset.Ioc D (2*D))
      (f := fun d1 (s : ℤ) => ∑ d2 ∈ Finset.Ioc D (2*D), F (s:ℝ) * ATM γ r d1 d2 s)
      (fun d1 _ => summable_sum (f := fun d2 (s : ℤ) => F (s:ℝ) * ATM γ r d1 d2 s)
        (fun d2 _ => summable_mul_ATM F hFsum γ r d1 d2))]
  trans ∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ Finset.Ioc D (2*D), ∑' s : ℤ, F (s:ℝ) * ATM γ r d1 d2 s
  · refine Finset.sum_congr rfl (fun d1 _ => ?_)
    exact Summable.tsum_finsetSum (s := Finset.Ioc D (2*D))
      (f := fun d2 (s : ℤ) => F (s:ℝ) * ATM γ r d1 d2 s) (fun d2 _ => summable_mul_ATM F hFsum γ r d1 d2)
  · refine Finset.sum_congr rfl (fun d1 hd1 => Finset.sum_congr rfl (fun d2 hd2 => ?_))
    have hd1pos : 0 < d1 := by have h := (Finset.mem_Ioc.mp hd1).1; omega
    have hd2pos : 0 < d2 := by have h := (Finset.mem_Ioc.mp hd2).1; omega
    haveI : NeZero d1 := ⟨hd1pos.ne'⟩
    haveI : NeZero d2 := ⟨hd2pos.ne'⟩
    exact pair_value F hc hb hF hF' γ r

end

end Work.FIArea4
