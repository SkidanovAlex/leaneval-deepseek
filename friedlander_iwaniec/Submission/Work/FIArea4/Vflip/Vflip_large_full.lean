import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.Evar_le_trivial
import Submission.Work.FIArea4.PairSumCommon
import Submission.Work.FIArea4.pair_sum_le_Evar
import Submission.Work.FIArea4.Vflip.vfm_plumbing
import Submission.Work.FIArea4.Vflip.Vflip_large_dyadic
import Submission.Work.FIArea4.Vflip.Vvar_strip_le
import Submission.Work.FIArea4.Vflip.Vvar_flip_mid
import Submission.Work.FIArea4.P13Scale
import Submission.Work.FIArea4.sum_rpow_two_pow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# FI Proposition 12.1 in the "large moduli" range `R*S < D*D` (full box)

This is the assembly of the (large-`D`) half of Friedlander--Iwaniec's Proposition 12.1, i.e. of
the "flipping of moduli" in the range `√(RS) < D ≤ RS`.  The purely combinatorial reduction of the
full box `[1,2R]×[1,2S]` of `Work.FIPlan.Vvar` to the (i) two boundary strips `r = 1`, `s = 1`,
(ii) the dyadic cells `(2^j, 2^{j+1}] × (2^k, 2^{k+1}]`, (iii) the crude small box `R*S < D` and
(iv) the small-`D` regime `D² ≤ R*S`, with the *weighted* Cauchy--Schwarz over the cells whose
weights are the brackets `p14T12 D (2^j) (2^k) ε`, is carried out in
`Submission.Work.FIArea4.Vflip.vfm_plumbing` (`vfm_large_full`).

The five inputs of that reduction are:

* `hcell` — the dyadic-box (interior) form of the estimate, `Submission.Work.FIArea4.Vflip.Vflip_large_dyadic`
  (FI §12 proper: the smooth near/far cutoff, the flip `d ↦ q = |Δ|/(dm)`, the Möbius reduction of
  `(r₁,r₂)` and the Fourier--Mellin separation, using the large sieve `h11`);
* `hstrip` — `Vvar_strip_le`;
* `hmed` — the range `R*S < D`, proved here (`vlf_Vvar_le_of_mul_lt_D`, constant `33`);
* `hsmall` — `Vvar_flip_small'`;
* `hdyad` — the summability of the bracket over the dyadic cells.
-/

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section


/-! ### Elementary facts -/

lemma vlf_jw_norm_le_one (d r : ℕ) : ‖jw d r‖ ≤ 1 := by
  rw [jw]
  rcases jacobiSym.trichotomy (r : ℤ) (Work.FIPlan.oddPart d) with h | h | h
  · rw [h]; norm_num
  · rw [h]; norm_num
  · rw [h]; norm_num

lemma vlf_cop_of_cop_two_mul {r s : ℕ} (h : Nat.Coprime r (2 * s)) : Nat.Coprime r s :=
  Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_left s 2) h

lemma vlf_eq_of_mul_eq_mul_of_coprime {r₁ s₁ r₂ s₂ : ℕ}
    (h₁ : Nat.Coprime r₁ s₁) (h₂ : Nat.Coprime r₂ s₂) (h : r₁ * s₂ = r₂ * s₁) :
    r₁ = r₂ ∧ s₁ = s₂ := by
  have d₁ : r₁ ∣ r₂ := h₁.dvd_of_dvd_mul_right ⟨s₂, h.symm⟩
  have d₂ : r₂ ∣ r₁ := h₂.dvd_of_dvd_mul_right ⟨s₁, h⟩
  have hr : r₁ = r₂ := Nat.dvd_antisymm d₁ d₂
  refine ⟨hr, ?_⟩
  rcases Nat.eq_zero_or_pos r₁ with h0 | hpos
  · rw [h0] at h₁ h
    have hs1 : s₁ = 1 := (Nat.coprime_zero_left s₁).mp h₁
    have hr2 : r₂ = 0 := by rw [hs1, Nat.zero_mul, Nat.mul_one] at h; exact h.symm
    have hs2 : s₂ = 1 := by rw [hr2] at h₂; exact (Nat.coprime_zero_left s₂).mp h₂
    rw [hs1, hs2]
  · have hpos' : 0 < r₂ := hr ▸ hpos
    rw [hr] at h
    exact (Nat.eq_of_mul_eq_mul_left hpos' h).symm

/-- Two pairs in the same residue class of `EvarCls` satisfy the determinant congruence. -/
lemma vlf_cls_congr_of_mem {R S d a : ℕ} (ha : a < d) {p q : ℕ × ℕ}
    (hp : p ∈ EvarCls R S d a) (hq : q ∈ EvarCls R S d a) :
    ((p.1 * q.2 : ℕ) : ZMod d) = ((q.1 * p.2 : ℕ) : ZMod d) :=
  (EvarCls_congr R S d a a ha ha hp hq).mpr rfl

/-- The products `EvarCls d a × EvarCls d a` are pairwise disjoint. -/
lemma vlf_cls_prod_pairwiseDisjoint (R S d : ℕ) (hd : 0 < d) :
    (↑(Finset.range d) : Set ℕ).PairwiseDisjoint
      (fun a => EvarCls R S d a ×ˢ EvarCls R S d a) := by
  intro a ha b hb hab
  show Disjoint (EvarCls R S d a ×ˢ EvarCls R S d a) (EvarCls R S d b ×ˢ EvarCls R S d b)
  have hdisj : Disjoint (EvarCls R S d a) (EvarCls R S d b) :=
    pairwiseDisjoint_EvarCls R S d hd ha hb hab
  rw [Finset.disjoint_left] at hdisj ⊢
  intro x hx hx'
  rw [Finset.mem_product] at hx hx'
  exact hdisj hx.1 hx'.1

/-- `Evar` is bounded by the sum over ordered pairs of pairs lying in one common class. -/
lemma vlf_Evar_le_classpair (R S d : ℕ) (hd : 0 < d) (β : ℕ → ℕ → ℂ) :
    Work.FIPlan.Evar R S d β ≤
      ∑ a ∈ Finset.range d, ∑ x ∈ EvarCls R S d a ×ˢ EvarCls R S d a,
        ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖ := by
  rw [Evar_eq_sum_normSq_clsSum]
  refine Finset.sum_le_sum (fun a _ => ?_)
  have hsum : ‖clsSum R S d β a‖ ≤ ∑ p ∈ EvarCls R S d a, ‖β p.1 p.2‖ := by
    rw [clsSum]
    calc ‖∑ p ∈ EvarCls R S d a, β p.1 p.2 * jw d p.1‖
        ≤ ∑ p ∈ EvarCls R S d a, ‖β p.1 p.2 * jw d p.1‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ EvarCls R S d a, ‖β p.1 p.2‖ := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) (vlf_jw_norm_le_one d p.1)
  calc Complex.normSq (clsSum R S d β a)
      = ‖clsSum R S d β a‖ ^ 2 := Complex.normSq_eq_norm_sq _
    _ ≤ (∑ p ∈ EvarCls R S d a, ‖β p.1 p.2‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hsum 2
    _ = ∑ p ∈ EvarCls R S d a, ∑ q ∈ EvarCls R S d a, ‖β p.1 p.2‖ * ‖β q.1 q.2‖ := by
        rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ x ∈ EvarCls R S d a ×ˢ EvarCls R S d a,
          ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖ := by
        rw [Finset.sum_product]

/-- The `d`-independent box of ordered pairs of pairs. -/
def vlf_pBox (R S : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S)) ×ˢ
    (Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S))

lemma vlf_card_Icc_two (M : ℕ) : (Finset.Icc 1 (2*M)).card = 2*M := by
  rw [Nat.card_Icc]; omega

lemma vlf_card_box (R S : ℕ) :
    ((Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S)) : Finset (ℕ × ℕ)).card = 4*R*S := by
  rw [Finset.card_product, vlf_card_Icc_two R, vlf_card_Icc_two S]; ring

lemma mem_U_subset_vlf_pBox {R S d : ℕ} {x : (ℕ × ℕ) × (ℕ × ℕ)}
    (hx : x ∈ (Finset.range d).biUnion
      (fun a => EvarCls R S d a ×ˢ EvarCls R S d a)) :
    x ∈ vlf_pBox R S := by
  rw [Finset.mem_biUnion] at hx
  obtain ⟨a, -, hx⟩ := hx
  rw [Finset.mem_product] at hx
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hr1, hs1, -⟩ := mem_EvarCls.mp hx1
  obtain ⟨hr2, hs2, -⟩ := mem_EvarCls.mp hx2
  have hr1' := (mem_EvarR.mp hr1).1
  have hr2' := (mem_EvarR.mp hr2).1
  simp only [vlf_pBox, Finset.mem_product]
  exact ⟨⟨hr1', hs1⟩, ⟨hr2', hs2⟩⟩

lemma vlf_p14L2_nonneg (R S : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ Work.FIArea4.p14L2 R S α := by
  rw [Work.FIArea4.p14L2]
  exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))

/-- The count of the moduli `d` for which a fixed ordered pair of pairs is in a common class. -/
lemma vlf_count_d_le_seven (D R S : ℕ) (β : ℕ → ℕ → ℂ) (hD : 1 ≤ D) (hRS : R * S < D)
    (hcop : ∀ r s, β r s ≠ 0 → Nat.Coprime r (2 * s))
    {x : (ℕ × ℕ) × (ℕ × ℕ)} (hx : x ∈ vlf_pBox R S)
    (hne : x.1 ≠ x.2) (hGnz : ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖ ≠ 0) :
    (((Finset.Ioc D (2*D)).filter (fun d => x ∈ (Finset.range d).biUnion
        (fun a => EvarCls R S d a ×ˢ EvarCls R S d a))).card : ℝ) ≤ 7 := by
  have hβ1 : β x.1.1 x.1.2 ≠ 0 := by
    intro h0; exact hGnz (by rw [h0, norm_zero, zero_mul])
  have hβ2 : β x.2.1 x.2.2 ≠ 0 := by
    intro h0; exact hGnz (by rw [h0, norm_zero, mul_zero])
  have hc1 : Nat.Coprime x.1.1 x.1.2 := vlf_cop_of_cop_two_mul (hcop _ _ hβ1)
  have hc2 : Nat.Coprime x.2.1 x.2.2 := vlf_cop_of_cop_two_mul (hcop _ _ hβ2)
  have hxbox : x ∈ (Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S)) ×ˢ
      (Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S)) := hx
  rw [Finset.mem_product] at hxbox
  obtain ⟨hb1, hb2⟩ := hxbox
  rw [Finset.mem_product] at hb1 hb2
  have hx11 : x.1.1 ≤ 2*R := (Finset.mem_Icc.mp hb1.1).2
  have hx12 : x.1.2 ≤ 2*S := (Finset.mem_Icc.mp hb1.2).2
  have hx21 : x.2.1 ≤ 2*R := (Finset.mem_Icc.mp hb2.1).2
  have hx22 : x.2.2 ≤ 2*S := (Finset.mem_Icc.mp hb2.2).2
  set A : ℕ := ((x.1.1 : ℤ) * (x.2.2 : ℤ) - (x.2.1 : ℤ) * (x.1.2 : ℤ)).natAbs with hA
  have hkey : ∀ d ∈ (Finset.Ioc D (2*D)).filter (fun d => x ∈ (Finset.range d).biUnion
      (fun a => EvarCls R S d a ×ˢ EvarCls R S d a)), d ∣ A ∧ 0 < A ∧ A < 8 * d := by
    intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨hdIoc, hdU⟩ := hd
    have hdpos : 0 < d := by have := (Finset.mem_Ioc.mp hdIoc).1; omega
    rw [Finset.mem_biUnion] at hdU
    obtain ⟨a, ha, hdU⟩ := hdU
    rw [Finset.mem_product] at hdU
    obtain ⟨h1, h2⟩ := hdU
    have ha' : a < d := Finset.mem_range.mp ha
    have hcong := vlf_cls_congr_of_mem ha' h1 h2
    have hdvd : d ∣ A := by
      have hz : (((x.1.1 : ℤ) * (x.2.2 : ℤ) - (x.2.1 : ℤ) * (x.1.2 : ℤ) : ℤ) : ZMod d) = 0 := by
        have e : (((x.1.1 : ℤ) * (x.2.2 : ℤ) - (x.2.1 : ℤ) * (x.1.2 : ℤ) : ℤ) : ZMod d)
            = ((x.1.1 * x.2.2 : ℕ) : ZMod d) - ((x.2.1 * x.1.2 : ℕ) : ZMod d) := by
          push_cast; ring
        rw [e, hcong, sub_self]
      have hz' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp hz
      have hzz := Int.natAbs_dvd_natAbs.mpr hz'
      simpa [hA] using hzz
    have hApos : 0 < A := by
      rw [hA]
      refine Int.natAbs_pos.mpr ?_
      intro hzero
      have hnat : x.1.1 * x.2.2 = x.2.1 * x.1.2 := by
        have : (x.1.1 : ℤ) * (x.2.2 : ℤ) = (x.2.1 : ℤ) * (x.1.2 : ℤ) := by
          have := sub_eq_zero.mp hzero; simpa using this
        exact_mod_cast this
      obtain ⟨h1', h2'⟩ := vlf_eq_of_mul_eq_mul_of_coprime hc1 hc2 hnat
      exact hne (Prod.ext h1' h2')
    have hAlt : A < 8 * d := by
      have h1 : A ≤ x.1.1 * x.2.2 + x.2.1 * x.1.2 := by
        rw [hA]
        have := Int.natAbs_sub_le ((x.1.1 : ℤ) * (x.2.2 : ℤ)) ((x.2.1 : ℤ) * (x.1.2 : ℤ))
        simpa [Int.natAbs_mul] using this
      have h2 : x.1.1 * x.2.2 + x.2.1 * x.1.2 ≤ 8 * (R * S) := by
        have e1 : x.1.1 * x.2.2 ≤ (2*R) * (2*S) := Nat.mul_le_mul hx11 hx22
        have e2 : x.2.1 * x.1.2 ≤ (2*R) * (2*S) := Nat.mul_le_mul hx21 hx12
        nlinarith
      have h3 : 8 * (R * S) < 8 * D := by omega
      have h4 : 8 * D ≤ 8 * d := by have := (Finset.mem_Ioc.mp hdIoc).1; omega
      omega
    exact ⟨hdvd, hApos, hAlt⟩
  have hc7 : ((Finset.Ioc D (2*D)).filter (fun d => x ∈ (Finset.range d).biUnion
      (fun a => EvarCls R S d a ×ˢ EvarCls R S d a))).card ≤ 7 := by
    set s := (Finset.Ioc D (2*D)).filter (fun d => x ∈ (Finset.range d).biUnion
      (fun a => EvarCls R S d a ×ˢ EvarCls R S d a)) with hs
    have hinj : Set.InjOn (fun d => A / d) ↑s := by
      intro d hd e he hde
      have hkd := hkey d (hs ▸ hd)
      have hke := hkey e (hs ▸ he)
      obtain ⟨hdvd, hApos, -⟩ := hkd
      obtain ⟨hevd, -, -⟩ := hke
      have h1 : d * (A / d) = A := Nat.mul_div_cancel' hdvd
      have h2 : e * (A / e) = A := Nat.mul_div_cancel' hevd
      have hk : A / d = A / e := hde
      have hd0 : 0 < d := by
        have hdIoc : d ∈ Finset.Ioc D (2*D) := (Finset.mem_filter.mp (hs ▸ hd)).1
        have := (Finset.mem_Ioc.mp hdIoc).1
        omega
      have h3 : d * (A / d) = e * (A / d) := by
        rw [h1, hk]
        exact h2.symm
      exact Nat.mul_right_cancel (Nat.div_pos (Nat.le_of_dvd hApos hdvd) hd0) h3
    have hmap : Set.MapsTo (fun d => A / d) ↑s ↑(Finset.Ico 1 8) := by
      intro d hd
      have hkd := hkey d (hs ▸ hd)
      obtain ⟨hdvd, hApos, hAlt⟩ := hkd
      rw [Finset.mem_coe, Finset.mem_Ico]
      refine ⟨Nat.div_pos (Nat.le_of_dvd hApos hdvd) (by omega), ?_⟩
      have h1 : d * (A / d) = A := Nat.mul_div_cancel' hdvd
      have h2 : d * (A / d) < d * 8 := by rw [h1]; omega
      exact Nat.lt_of_mul_lt_mul_left h2
    calc s.card = (s.image (fun d => A / d)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Ico 1 8).card := Finset.card_le_card (Finset.image_subset_iff.mpr hmap)
      _ = 7 := by simp [Nat.card_Ico]
  exact_mod_cast hc7

/-- **The range `R*S < D` of FI Proposition 12.1**: the variance is bounded by `33·D·L₂`. -/
theorem vlf_Vvar_le_of_mul_lt_D (D R S : ℕ) (β : ℕ → ℕ → ℂ) (hD : 1 ≤ D) (hR : 1 ≤ R)
    (hS : 1 ≤ S) (hRS : R * S < D)
    (hcop : ∀ r s, β r s ≠ 0 → Nat.Coprime r (2 * s)) :
    Work.FIPlan.Vvar R S D β ≤ 33 * (D : ℝ) * Work.FIArea4.p14L2 R S β := by
  let U : ℕ → Finset ((ℕ × ℕ) × (ℕ × ℕ)) := fun d =>
    (Finset.range d).biUnion (fun a => EvarCls R S d a ×ˢ EvarCls R S d a)
  have hstep1 : Work.FIPlan.Vvar R S D β ≤
      ∑ d ∈ Finset.Ioc D (2*D), ∑ x ∈ vlf_pBox R S,
        (if x ∈ U d then ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖ else 0) := by
    rw [Work.FIPlan.Vvar]
    refine Finset.sum_le_sum (fun d hd => ?_)
    have hd0 : 0 < d := by have := (Finset.mem_Ioc.mp hd).1; omega
    have h1 := vlf_Evar_le_classpair R S d hd0 β
    have hbu : (∑ a ∈ Finset.range d, ∑ x ∈ EvarCls R S d a ×ˢ EvarCls R S d a,
          ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖)
        = ∑ x ∈ (Finset.range d).biUnion (fun a => EvarCls R S d a ×ˢ EvarCls R S d a),
          ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖ :=
      (Finset.sum_biUnion (vlf_cls_prod_pairwiseDisjoint R S d hd0)).symm
    rw [hbu] at h1
    refine le_trans h1 ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_)
      (fun x _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [Finset.mem_filter]
    exact ⟨mem_U_subset_vlf_pBox hx, hx⟩
  have hswap : (∑ d ∈ Finset.Ioc D (2*D), ∑ x ∈ vlf_pBox R S,
        (if x ∈ U d then ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖ else 0))
      = ∑ x ∈ vlf_pBox R S, (‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖) *
          (((Finset.Ioc D (2*D)).filter (fun d => x ∈ U d)).card : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hN : ∀ x : (ℕ × ℕ) × (ℕ × ℕ), x ∈ vlf_pBox R S →
      (‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖) *
          (((Finset.Ioc D (2*D)).filter (fun d => x ∈ U d)).card : ℝ)
      ≤ (‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖) * (if x.1 = x.2 then (D:ℝ) else 7) := by
    intro x hx
    have hGnn : 0 ≤ ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    by_cases hG : ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖ = 0
    · rw [hG, zero_mul, zero_mul]
    · by_cases heq : x.1 = x.2
      · rw [if_pos heq]
        have hcard : (((Finset.Ioc D (2*D)).filter (fun d => x ∈ U d)).card : ℝ) ≤ (D:ℝ) := by
          have hle : ((Finset.Ioc D (2*D)).filter (fun d => x ∈ U d)).card
              ≤ (Finset.Ioc D (2*D)).card := Finset.card_le_card (Finset.filter_subset _ _)
          have h2 : (Finset.Ioc D (2*D)).card = D := by rw [Nat.card_Ioc]; omega
          rw [h2] at hle; exact_mod_cast hle
        exact mul_le_mul_of_nonneg_left hcard hGnn
      · rw [if_neg heq]
        have h7 : (((Finset.Ioc D (2*D)).filter (fun d => x ∈ U d)).card : ℝ) ≤ 7 :=
          vlf_count_d_le_seven D R S β hD hRS hcop hx heq hG
        exact mul_le_mul_of_nonneg_left h7 hGnn
  have hsplit : (∑ x ∈ vlf_pBox R S, (‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖) *
        (if x.1 = x.2 then (D:ℝ) else 7))
      = (∑ x ∈ (vlf_pBox R S).filter (fun x => x.1 = x.2),
            ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖) * (D:ℝ)
        + (∑ x ∈ (vlf_pBox R S).filter (fun x => ¬ (x.1 = x.2)),
            ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖) * 7 := by
    have hpt : ∀ x : (ℕ × ℕ) × (ℕ × ℕ), (‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖) *
        (if x.1 = x.2 then (D:ℝ) else 7)
        = (if x.1 = x.2 then (‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖) * D
            else (‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖) * 7) := by
      intro x
      by_cases h : x.1 = x.2 <;> simp [h]
    rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_ite]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hdiag : (∑ x ∈ (vlf_pBox R S).filter (fun x => x.1 = x.2),
        ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖) = Work.FIArea4.p14L2 R S β := by
    have hset : (vlf_pBox R S).filter (fun x => x.1 = x.2)
        = ((Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S)) : Finset (ℕ×ℕ)).image (fun p => (p, p)) := by
      ext x
      constructor
      · intro hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hxp, heq⟩ := hx
        rw [Finset.mem_image]
        refine ⟨x.2, ?_, Prod.ext heq.symm rfl⟩
        rw [vlf_pBox, Finset.mem_product] at hxp
        exact hxp.2
      · intro hx
        rw [Finset.mem_image] at hx
        obtain ⟨p, hp, hpx⟩ := hx
        rw [← hpx, Finset.mem_filter, vlf_pBox, Finset.mem_product]
        exact ⟨⟨hp, hp⟩, rfl⟩
    have hinj : ∀ p ∈ (Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S)),
        ∀ q ∈ (Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S)), (p, p) = (q, q) → p = q :=
      fun p _ q _ hpq => congrArg Prod.fst hpq
    rw [hset, Finset.sum_image hinj]
    rw [Work.FIArea4.p14L2, Finset.sum_product]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
    rw [Complex.normSq_eq_norm_sq]; ring
  have hL2 : (∑ p ∈ (Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S)), ‖β p.1 p.2‖ ^ 2)
      = Work.FIArea4.p14L2 R S β := by
    rw [Work.FIArea4.p14L2, Finset.sum_product]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
    rw [Complex.normSq_eq_norm_sq]
  have htot : (∑ x ∈ vlf_pBox R S, ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖)
      ≤ 4 * (D:ℝ) * Work.FIArea4.p14L2 R S β := by
    have hprod : (∑ x ∈ vlf_pBox R S, ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖)
        = (∑ p ∈ (Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S)), ‖β p.1 p.2‖) ^ 2 := by
      rw [vlf_pBox, Finset.sum_product, sq, Finset.sum_mul_sum]
    have hcard : (((Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S)) : Finset (ℕ×ℕ)).card : ℝ)
        ≤ 4 * (D:ℝ) := by
      rw [vlf_card_box]
      have h4 : 4 * R * S ≤ 4 * D := by
        have := Nat.mul_le_mul_left 4 (le_of_lt hRS)
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
      exact_mod_cast h4
    rw [hprod]
    calc (∑ p ∈ (Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S)), ‖β p.1 p.2‖) ^ 2
        ≤ (((Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S)) : Finset (ℕ×ℕ)).card : ℝ)
            * (∑ p ∈ (Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S)), ‖β p.1 p.2‖ ^ 2) :=
          sq_sum_le_card_mul_sum_sq
      _ = (((Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S)) : Finset (ℕ×ℕ)).card : ℝ)
            * Work.FIArea4.p14L2 R S β := by rw [hL2]
      _ ≤ 4 * (D:ℝ) * Work.FIArea4.p14L2 R S β :=
          mul_le_mul_of_nonneg_right hcard (vlf_p14L2_nonneg R S β)
  have hoff : (∑ x ∈ (vlf_pBox R S).filter (fun x => ¬ (x.1 = x.2)),
        ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖)
      ≤ 4 * (D:ℝ) * Work.FIArea4.p14L2 R S β :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))) htot
  have hL2nn : 0 ≤ Work.FIArea4.p14L2 R S β := vlf_p14L2_nonneg R S β
  have hDnn : (0:ℝ) ≤ (D:ℝ) := by positivity
  calc Work.FIPlan.Vvar R S D β
      ≤ ∑ x ∈ vlf_pBox R S, (‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖) *
          (((Finset.Ioc D (2*D)).filter (fun d => x ∈ U d)).card : ℝ) :=
        le_trans hstep1 (le_of_eq hswap)
    _ ≤ ∑ x ∈ vlf_pBox R S, (‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖) *
          (if x.1 = x.2 then (D:ℝ) else 7) := Finset.sum_le_sum hN
    _ = (∑ x ∈ (vlf_pBox R S).filter (fun x => x.1 = x.2),
            ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖) * (D:ℝ)
        + (∑ x ∈ (vlf_pBox R S).filter (fun x => ¬ (x.1 = x.2)),
            ‖β x.1.1 x.1.2‖ * ‖β x.2.1 x.2.2‖) * 7 := hsplit
    _ ≤ Work.FIArea4.p14L2 R S β * (D:ℝ) + (4 * (D:ℝ) * Work.FIArea4.p14L2 R S β) * 7 := by
        rw [hdiag]
        exact add_le_add (le_of_eq rfl) (mul_le_mul_of_nonneg_right hoff (by norm_num))
    _ ≤ 33 * (D:ℝ) * Work.FIArea4.p14L2 R S β := by
        nlinarith [hL2nn, hDnn]


end

end Work.FIArea4.Vflip
