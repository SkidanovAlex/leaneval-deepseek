import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.farGadgets
import Submission.Work.FIArea4.Vflip.Vfd.coprimeSetup
import Submission.Work.FIArea4.Vflip.Vfd.coprime_pairR_oddPart_m
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs
import Submission.Work.FIArea4.Vflip.Vfd.farU_conjV_termwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary helpers -/

lemma fesc_sum_ite_const {M : Type*} [AddCommMonoid M] {ι : Type*} {p : Prop} [Decidable p]
    (s : Finset ι) (g : ι → M) :
    (∑ x ∈ s, (if p then g x else 0)) = if p then ∑ x ∈ s, g x else 0 := by
  by_cases h : p <;> simp [h]

lemma fesc_cR_le {c R : ℕ} (hc : 1 ≤ c) (hR : 1 ≤ R) : cR c R ≤ R := by
  rw [cR]
  rw [Nat.div_le_iff_le_mul_add_pred hc]
  have h : R ≤ c * R := by simpa using Nat.mul_le_mul_right R hc
  omega

lemma fesc_le_two_cR {c R ρ : ℕ} (hc : 1 ≤ c) (h : c * ρ ≤ 2 * R) : ρ ≤ 2 * cR c R := by
  have hRcR : R ≤ c * cR c R := le_mul_cR hc (R := R)
  have hdiv : (2 * R) / c ≤ 2 * cR c R := by
    apply Nat.div_le_of_le_mul
    calc (2:ℕ) * R ≤ 2 * (c * cR c R) := Nat.mul_le_mul_left 2 hRcR
      _ = c * (2 * cR c R) := by ring
  have h3 : ρ ≤ (2 * R) / c := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < c)]
    simpa [Nat.mul_comm] using h
  exact le_trans h3 hdiv

lemma fesc_pairAbs_mul_left {c ρ1 ρ2 s1 s2 : ℕ} (hc : 0 < c) (hcop : Nat.Coprime ρ1 ρ2) :
    Work.FIArea4.Vflip.pairAbs (c*ρ1) (c*ρ2) s1 s2 = Work.FIArea4.Vflip.pairAbs ρ1 ρ2 s1 s2 := by
  have h1 : Work.FIArea4.Vflip.pairR (c*ρ1) (c*ρ2) = ρ1 := by
    rw [Work.FIArea4.Vflip.pairR, Work.FIArea4.Vflip.pairC, Nat.gcd_mul_left,
      hcop.gcd_eq_one, mul_one]
    exact Nat.mul_div_cancel_left ρ1 hc
  have h2 : Work.FIArea4.Vflip.pairR (c*ρ2) (c*ρ1) = ρ2 := by
    rw [Work.FIArea4.Vflip.pairR, Work.FIArea4.Vflip.pairC, Nat.gcd_mul_left,
      hcop.symm.gcd_eq_one, mul_one]
    exact Nat.mul_div_cancel_left ρ2 hc
  have e1 : Work.FIArea4.Vflip.pairR ρ1 ρ2 = ρ1 := by
    rw [Work.FIArea4.Vflip.pairR, Work.FIArea4.Vflip.pairC, hcop.gcd_eq_one, Nat.div_one]
  have e2 : Work.FIArea4.Vflip.pairR ρ2 ρ1 = ρ2 := by
    rw [Work.FIArea4.Vflip.pairR, Work.FIArea4.Vflip.pairC, hcop.symm.gcd_eq_one, Nat.div_one]
  simp only [Work.FIArea4.Vflip.pairAbs, h1, h2, e1, e2]

/-! ## The summands -/

/-- The `μ`-free part of the summand of `farExpSum`, i.e. `farCoef` with the Möbius factor
removed, times the exponential and the `y^{it}` factor. -/
private def farX (D _m c : ℕ) (α : ℕ → ℕ → ℂ) (u t : ℝ) (i : FarIx) : ℂ :=
  ((jacobiSym (i.1.2.2 : ℤ) i.1.2.1 * jacobiSym (i.2.2 : ℤ) i.2.1 : ℤ) : ℂ) *
    (α (c * i.1.2.1) i.1.2.2 * star (α (c * i.2.1) i.2.2)) *
    ((jacobiSym (i.1.2.1 : ℤ) (Work.FIPlan.oddPart i.1.1) *
      jacobiSym (i.2.1 : ℤ) (Work.FIPlan.oddPart i.1.1) : ℤ) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (u * xOrig c i)) *
    (((ySep c D i : ℝ)) : ℂ) ^ (Complex.I * (t : ℂ))

/-- The summand of `pairSumCo` with `d` the (fixed) modulus, as a function of the reduced pair
`((ρ₁,s₁),(ρ₂,s₂))`. -/
private def pSC (d : ℕ) (u v : ℕ → ℕ → ℂ) (x : (ℕ×ℕ)×(ℕ×ℕ)) : ℂ :=
  if Nat.Coprime x.1.1 x.2.1 ∧ (((x.1.1 * x.2.2 : ℕ):ZMod d) = ((x.2.1 * x.1.2 : ℕ):ZMod d))
  then u x.1.1 x.1.2 * star (v x.2.1 x.2.2) *
    ((jacobiSym (x.1.1:ℤ) (Work.FIPlan.oddPart d) *
      jacobiSym (x.2.1:ℤ) (Work.FIPlan.oddPart d):ℤ):ℂ)
  else 0

/-! ## Alignment of the two conditions -/

lemma fesc_farCond_of {D R S m c q' : ℕ} {a b : ℝ} {ρ1 s1 ρ2 s2 : ℕ}
    (hc : 1 ≤ c) (hmc : m ∣ c)
    (hb1 : R < c*ρ1 ∧ c*ρ1 ≤ 2*R ∧ S < s1 ∧ s1 ≤ 2*S)
    (hb2 : R < c*ρ2 ∧ c*ρ2 ≤ 2*R ∧ S < s2 ∧ s2 ≤ 2*S)
    (hcop : Nat.Coprime ρ1 ρ2)
    (hcongr : ((ρ1*s2:ℕ):ZMod (m*q')) = ((ρ2*s1:ℕ):ZMod (m*q'))) :
    farCond D R S a b m c ((q',(ρ1,s1)),(ρ2,s2)) := by
  refine ⟨hc, hcop, hb1.1, hb1.2.1, hb2.1, hb2.2.1, hb1.2.2.1, hb1.2.2.2,
    hb2.2.2.1, hb2.2.2.2, hmc, ?_⟩
  have h2 := (Work.FIArea4.Vflip.Vfd.zmod_eq_pairAbs_iff ρ1 s1 ρ2 s2 (m*q')).mp hcongr
  simp only [Work.FIArea4.Vflip.pairC] at h2
  rw [hcop.gcd_eq_one, one_mul] at h2
  show m * q' ∣ Work.FIArea4.Vflip.pairAbs (c*ρ1) (c*ρ2) s1 s2
  rwa [fesc_pairAbs_mul_left (by omega) hcop]

lemma fesc_cond_of_farCond {D R S m c q' : ℕ} {a b : ℝ} {ρ1 s1 ρ2 s2 : ℕ}
    (hR : 1 ≤ R) (hS : 1 ≤ S) (hc : 1 ≤ c)
    (hfar : farCond D R S a b m c ((q',(ρ1,s1)),(ρ2,s2))) :
    ((ρ1,s1),(ρ2,s2)) ∈ (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) ×ˢ
      (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S))
    ∧ Nat.Coprime ρ1 ρ2
    ∧ ((ρ1*s2:ℕ):ZMod (m*q')) = ((ρ2*s1:ℕ):ZMod (m*q')) := by
  obtain ⟨h0c, hcop, ha1, ha2, hb1, hb2, hs1a, hs1b, hs2a, hs2b, hmc, hdiv⟩ := hfar
  dsimp only at ha1 ha2 hb1 hb2 hs1a hs1b hs2a hs2b hdiv
  have hρ1 : 1 ≤ ρ1 := by
    rcases Nat.eq_zero_or_pos ρ1 with h | h
    · rw [h, mul_zero] at ha1; omega
    · exact h
  have hρ2 : 1 ≤ ρ2 := by
    rcases Nat.eq_zero_or_pos ρ2 with h | h
    · rw [h, mul_zero] at hb1; omega
    · exact h
  have hle1 : ρ1 ≤ 2 * cR c R := fesc_le_two_cR hc ha2
  have hle2 : ρ2 ≤ 2 * cR c R := fesc_le_two_cR hc hb2
  refine ⟨?_, hcop, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨hρ1, hle1⟩, ⟨by omega, hs1b⟩⟩, ⟨⟨hρ2, hle2⟩, ⟨by omega, hs2b⟩⟩⟩
  · apply (Work.FIArea4.Vflip.Vfd.zmod_eq_pairAbs_iff ρ1 s1 ρ2 s2 (m*q')).mpr
    rw [show Work.FIArea4.Vflip.pairC ρ1 ρ2 = 1 from by
      rw [Work.FIArea4.Vflip.pairC, hcop.gcd_eq_one], one_mul]
    rwa [show iAbs c ((q',(ρ1,s1)),(ρ2,s2)) =
        Work.FIArea4.Vflip.pairAbs (c*ρ1) (c*ρ2) s1 s2 from rfl,
      fesc_pairAbs_mul_left (by omega) hcop] at hdiv

/-! ## Conversion of `pairSumCo` to a sum over the full box -/

lemma fesc_pairSumCo_eq_range (c R S d : ℕ) (u v : ℕ → ℕ → ℂ) (hc : 1 ≤ c) (hR : 1 ≤ R) :
    pairSumCo (cR c R) S d u v =
      ∑ w ∈ Finset.range (2*R+1) ×ˢ Finset.range (2*S+1),
        ∑ z ∈ Finset.range (2*R+1) ×ˢ Finset.range (2*S+1),
          (if (w,z) ∈ (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) ×ˢ
              (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S))
           then pSC d u v (w,z) else 0) := by
  have hsubA : Finset.Icc 1 (2*cR c R) ⊆ Finset.range (2*R+1) := by
    intro x hx; simp only [Finset.mem_Icc] at hx; simp only [Finset.mem_range]
    have := fesc_cR_le hc hR; omega
  have hsubB : Finset.Icc 1 (2*S) ⊆ Finset.range (2*S+1) := by
    intro x hx; simp only [Finset.mem_Icc] at hx; simp only [Finset.mem_range]; omega
  have hsubW : Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)
      ⊆ Finset.range (2*R+1) ×ˢ Finset.range (2*S+1) :=
    Finset.product_subset_product hsubA hsubB
  have hsubPP : (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) ×ˢ
      (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S))
      ⊆ (Finset.range (2*R+1) ×ˢ Finset.range (2*S+1)) ×ˢ
        (Finset.range (2*R+1) ×ˢ Finset.range (2*S+1)) :=
    Finset.product_subset_product hsubW hsubW
  rw [show pairSumCo (cR c R) S d u v
      = ∑ x ∈ (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) ×ˢ
            (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)), pSC d u v x from by
        simp only [pairSumCo, pSC, Finset.sum_product]]
  rw [show (∑ w ∈ Finset.range (2*R+1) ×ˢ Finset.range (2*S+1),
        ∑ z ∈ Finset.range (2*R+1) ×ˢ Finset.range (2*S+1),
          (if (w,z) ∈ (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) ×ˢ
              (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) then pSC d u v (w,z) else 0))
      = ∑ x ∈ (Finset.range (2*R+1) ×ˢ Finset.range (2*S+1)) ×ˢ
            (Finset.range (2*R+1) ×ˢ Finset.range (2*S+1)),
          (if x ∈ (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) ×ˢ
              (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) then pSC d u v x else 0) from by
        simp only [Finset.sum_product]]
  have hsum := Finset.sum_subset hsubPP
    (f := fun x => if x ∈ (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) ×ˢ
              (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) then pSC d u v x else 0)
    (by intro x _ hx; rw [if_neg hx])
  rw [← hsum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [if_pos hx]

/-! ## The termwise identity on the full box -/

private lemma fesc_perTuple {D R S m c q' : ℕ} {a b : ℝ} {α : ℕ → ℕ → ℂ} {u t : ℝ}
    {w z : ℕ × ℕ}
    (hR : 1 ≤ R) (hS : 1 ≤ S) (hc : 1 ≤ c) (hD : 1 ≤ D)
    (hmc : m ∣ c) (hq' : 1 ≤ q')
    (hcop : ∀ r s, α r s ≠ 0 → Nat.Coprime r (2*s))
    (hbox : ∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2*R ∧ S < s ∧ s ≤ 2*S) :
    (if farCond D R S a b m c ((q',w),z) then farX D m c α u t ((q',w),z) else 0)
      = (((c:ℕ):ℂ) / (((q'*D:ℕ)):ℂ))^(Complex.I*(t:ℂ)) *
        (if (w,z) ∈ (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) ×ˢ
            (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S))
         then pSC (m*q') (farU m c α u t) (farV m c α u t) (w,z) else 0) := by
  by_cases hα : α (c*w.1) w.2 * star (α (c*z.1) z.2) = 0
  · have hX : farX D m c α u t ((q',w),z) = 0 := by
      simp only [farX]; rw [hα]; ring
    have hU : farU m c α u t w.1 w.2 * star (farV m c α u t z.1 z.2) = 0 := by
      rcases mul_eq_zero.mp hα with h1 | h2
      · rw [show farU m c α u t w.1 w.2 = 0 from by simp only [farU, h1, zero_mul]]
        rw [zero_mul]
      · rw [show star (farV m c α u t z.1 z.2) = 0 from by
            simp only [farV, star_mul]; rw [h2]; ring]
        rw [mul_zero]
    have hpsc : pSC (m*q') (farU m c α u t) (farV m c α u t) (w,z) = 0 := by
      rw [pSC]
      by_cases hcc : Nat.Coprime w.1 z.1 ∧
          ((w.1*z.2:ℕ):ZMod (m*q')) = ((z.1*w.2:ℕ):ZMod (m*q'))
      · rw [if_pos hcc, hU]; ring
      · rw [if_neg hcc]
    rw [hpsc]
    by_cases hf : farCond D R S a b m c ((q',w),z)
    · rw [if_pos hf, hX]
      by_cases hm : (w,z) ∈ (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) ×ˢ
          (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) <;> simp [hm]
    · rw [if_neg hf]
      by_cases hm : (w,z) ∈ (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) ×ˢ
          (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) <;> simp [hm]
  · have hα1 : α (c*w.1) w.2 ≠ 0 := fun h => hα (by rw [h, zero_mul])
    have hα2 : α (c*z.1) z.2 ≠ 0 := fun h => hα (by rw [h]; simp)
    have hb1 := hbox (c*w.1) w.2 hα1
    have hb2 := hbox (c*z.1) z.2 hα2
    have hcop1 := hcop (c*w.1) w.2 hα1
    have hcop2 := hcop (c*z.1) z.2 hα2
    have hw1 : 0 < w.1 := by
      rcases Nat.eq_zero_or_pos w.1 with h | h
      · rw [h, mul_zero] at hb1; omega
      · exact h
    have hz1 : 0 < z.1 := by
      rcases Nat.eq_zero_or_pos z.1 with h | h
      · rw [h, mul_zero] at hb2; omega
      · exact h
    have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos hmc (by omega : 0 < c)
    by_cases hf : farCond D R S a b m c ((q',w),z)
    · obtain ⟨hmem, hcp, hcg⟩ := fesc_cond_of_farCond hR hS hc hf
      have hdiv : m*q' ∣ Work.FIArea4.Vflip.pairAbs (c*w.1) (c*z.1) w.2 z.2 := by
        have := hf.2.2.2.2.2.2.2.2.2.2.2
        dsimp only at this
        exact this
      have hterm := farU_conjV_termwise (c := c) (D := D) (m := m) (q' := q') (α := α)
        (u := u) (t := t) (ρ1 := w.1) (s1 := w.2) (ρ2 := z.1) (s2 := z.2)
        hc hm1 hD hq' hw1 hz1 hcop1 hcop2 hmc hcp hdiv
      rw [if_pos hf, if_pos hmem, pSC, if_pos ⟨hcp, hcg⟩]
      rw [show farX D m c α u t ((q',w),z) =
          ((jacobiSym (w.2:ℤ) w.1 * jacobiSym (z.2:ℤ) z.1 : ℤ):ℂ) *
            (α (c*w.1) w.2 * star (α (c*z.1) z.2)) *
            ((jacobiSym (w.1:ℤ) (Work.FIPlan.oddPart q') *
              jacobiSym (z.1:ℤ) (Work.FIPlan.oddPart q') : ℤ):ℂ) *
            Complex.exp (2*Real.pi*Complex.I*(u * xOrig c ((q',w),z))) *
            (((ySep c D ((q',w),z) : ℝ)):ℂ)^(Complex.I*(t:ℂ)) from rfl]
      rw [← hterm]
      ring
    · rw [if_neg hf]
      by_cases hmem : (w,z) ∈ (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S)) ×ˢ
          (Finset.Icc 1 (2*cR c R) ×ˢ Finset.Icc 1 (2*S))
      · rw [if_pos hmem]
        have hcc_false : ¬ (Nat.Coprime w.1 z.1 ∧
            ((w.1*z.2:ℕ):ZMod (m*q')) = ((z.1*w.2:ℕ):ZMod (m*q'))) :=
          fun hcc => hf (fesc_farCond_of hc hmc hb1 hb2 hcc.1 hcc.2)
        rw [pSC, if_neg hcc_false]; ring
      · rw [if_neg hmem]; ring

/-! ## The conversion of the far sum -/

private lemma fesc_farSet_range (D R S m c Q1 Q2 : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (u t : ℝ) :
    (∑ i ∈ farSet D R S a b m c Q1 Q2, farX D m c α u t i)
      = ∑ q' ∈ Finset.Ioc Q1 Q2,
          ∑ w ∈ Finset.range (2*R+1) ×ˢ Finset.range (2*S+1),
          ∑ z ∈ Finset.range (2*R+1) ×ˢ Finset.range (2*S+1),
            (if farCond D R S a b m c ((q',w),z) then farX D m c α u t ((q',w),z) else 0) := by
  rw [farSet, Finset.sum_filter]
  simp only [Finset.sum_product]
  refine Finset.sum_congr rfl (fun q' hq' =>
    Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun z _ => ?_)))
  have hq2 : q' ≤ Q2 := (Finset.mem_Ioc.mp hq').2
  by_cases hf : farCond D R S a b m c ((q',w),z) <;> simp [hq2, hf]

/-! ## The main theorem -/

theorem farExpSum_eq_pairSumCo {D R S m c Q1 Q2 : ℕ} {a b : ℝ} {α : ℕ → ℕ → ℂ}
    (hD : 0 < D) (hR : 1 ≤ R) (hS : 1 ≤ S) (hc : 1 ≤ c) (hmc : m ∣ c)
    (hcop : ∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s))
    (hbox : ∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S)
    (u t : ℝ) :
    farExpSum D R S a b α m c Q1 Q2 u t =
      (ArithmeticFunction.moebius m : ℂ) *
        ∑ q' ∈ Finset.Ioc Q1 Q2,
          (((c : ℕ) : ℂ) / (((q' * D : ℕ)) : ℂ)) ^ (Complex.I * (t : ℂ)) *
            pairSumCo (cR c R) S (m * q')
              (farU m c α u t) (farV m c α u t) := by
  have hD1 : 1 ≤ D := hD
  have hfar : farExpSum D R S a b α m c Q1 Q2 u t
      = (ArithmeticFunction.moebius m : ℂ) *
          ∑ i ∈ farSet D R S a b m c Q1 Q2, farX D m c α u t i := by
    rw [farExpSum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [farCoef, farX]; ring
  have hL := fesc_farSet_range D R S m c Q1 Q2 a b α u t
  have hR : (∑ q' ∈ Finset.Ioc Q1 Q2,
        (((c : ℕ) : ℂ) / (((q' * D : ℕ)) : ℂ)) ^ (Complex.I * (t : ℂ)) *
          pairSumCo (cR c R) S (m * q') (farU m c α u t) (farV m c α u t))
      = ∑ q' ∈ Finset.Ioc Q1 Q2,
          ∑ w ∈ Finset.range (2*R+1) ×ˢ Finset.range (2*S+1),
          ∑ z ∈ Finset.range (2*R+1) ×ˢ Finset.range (2*S+1),
            (if farCond D R S a b m c ((q',w),z) then farX D m c α u t ((q',w),z) else 0) := by
    refine Finset.sum_congr rfl (fun q' hq' => ?_)
    have hq1 : 1 ≤ q' := by have := (Finset.mem_Ioc.mp hq').1; omega
    rw [fesc_pairSumCo_eq_range (c := c) (R := R) (S := S) (d := m*q')
      (u := farU m c α u t) (v := farV m c α u t) hc hR]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    exact (fesc_perTuple hR hS hc hD1 hmc hq1 hcop hbox).symm
  rw [hfar, hL, hR]

end

end Work.FIArea4.Vflip.Vfd
