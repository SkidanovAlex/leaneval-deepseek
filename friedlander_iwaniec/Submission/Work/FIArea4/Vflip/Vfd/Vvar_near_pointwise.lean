import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.NearKernelDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Pointwise near-diagonal bound for the variance

This file proves `Work.FIArea4.Vflip.Vfd.Vvar_near_pointwise`: the pointwise (per-pair) estimate
underlying the near-diagonal part of Friedlander--Iwaniec's Proposition 12.1.

For a pair `p = (r₁,s₁)`, `q = (r₂,s₂)` of the dyadic box `boxF R S = (R,2R] × (S,2S]` and the
separation parameters `H = (RS/D)^{1/3}`, `a = 2S/(HR)`, `b = 2S/R`, the cutoff factor
`(1 - nearCut a b (xPair p q))` vanishes exactly when the pair is *far*, and there the counting
kernel `nearKernel D R S H p q` is zero; on the complementary (near) set the whole weight is
dominated by `# {d ∈ (D/2,3D] : d ∣ Δ_{pq}}`, the `nearKernel`.

The two ingredients are:
* `‖pairWeight D p q‖ ≤ # {d ∈ (D/2,3D] : d ∣ Δ_{pq}}` (each `d` in the sum is either outside the
  support `(D/2,5D/2)` of `bump`, or divides `Δ_{pq}` and so is counted once, with `|jw| ≤ 1`);
* `1 - nearCut a b (xPair p q) ≠ 0 → |Δ_{pq}| H ≤ 8RS`, i.e. the "far" pairs have `nearCut = 1`.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset

/-- The Jacobi weight `(r | d')` has modulus at most one. -/
private lemma norm_jw_le_one (d r : ℕ) : ‖Work.FIArea4.jw d r‖ ≤ 1 := by
  unfold Work.FIArea4.jw
  rcases jacobiSym.trichotomy (r : ℤ) (Work.FIPlan.oddPart d) with h | h | h <;> rw [h] <;> norm_num

/-- If `a ≡ b (mod d)` then `d ∣ |b - a|`. -/
private lemma zmod_congr_dvd (d a b : ℕ) (h : ((a : ℕ) : ZMod d) = ((b : ℕ) : ZMod d)) :
    d ∣ ((b : ℤ) - (a : ℤ)).natAbs := by
  have h1 : a ≡ b [MOD d] := (ZMod.natCast_eq_natCast_iff a b d).mp h
  have h2 : (d : ℤ) ∣ (b : ℤ) - (a : ℤ) := (Nat.modEq_iff_dvd).mp h1
  have h3 : (d : ℤ).natAbs ∣ ((b : ℤ) - (a : ℤ)).natAbs := (Int.natAbs_dvd_natAbs).mpr h2
  rwa [Int.natAbs_natCast] at h3

theorem Vvar_near_pointwise :
    ∀ (D R S : ℕ) (H a b : ℝ) (α : ℕ → ℕ → ℂ) (p q : ℕ × ℕ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → D ≤ R * S → R * S < D * D →
      H = ((R : ℝ) * (S : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3) →
      a = 2 * (S : ℝ) / (H * (R : ℝ)) → b = 2 * (S : ℝ) / (R : ℝ) →
      p ∈ Work.FIArea4.Vflip.boxF R S → q ∈ Work.FIArea4.Vflip.boxF R S →
      ‖α p.1 p.2 * star (α q.1 q.2) *
          (((1 - Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.Vflip.xPair p q)) : ℝ) *
            Work.FIArea4.Vflip.pairWeight D p q)‖
        ≤ ‖α p.1 p.2‖ * ‖α q.1 q.2‖ * Work.FIArea4.Vflip.Vfd.nearKernel D R S H p q := by
  classical
  intro D R S H a b α p q hD hR hS hDRS hDsq hH ha hb hp hq
  -- ## unpackage the box and basic positivity
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hSpos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast (by omega : 0 < S)
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hpbox : p.1 ∈ Finset.Ioc R (2 * R) ∧ p.2 ∈ Finset.Ioc S (2 * S) := by
    rw [Work.FIArea4.Vflip.boxF, Finset.mem_product] at hp; exact hp
  have hqbox : q.1 ∈ Finset.Ioc R (2 * R) ∧ q.2 ∈ Finset.Ioc S (2 * S) := by
    rw [Work.FIArea4.Vflip.boxF, Finset.mem_product] at hq; exact hq
  have hpI : R < p.1 ∧ p.1 ≤ 2 * R := Finset.mem_Ioc.mp hpbox.1
  have hpJ : S < p.2 ∧ p.2 ≤ 2 * S := Finset.mem_Ioc.mp hpbox.2
  have hqI : R < q.1 ∧ q.1 ≤ 2 * R := Finset.mem_Ioc.mp hqbox.1
  have hqJ : S < q.2 ∧ q.2 ≤ 2 * S := Finset.mem_Ioc.mp hqbox.2
  have hp1pos : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast (by omega : 0 < p.1)
  have hq1pos : (0 : ℝ) < (q.1 : ℝ) := by exact_mod_cast (by omega : 0 < q.1)
  have hp2pos : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast (by omega : 0 < p.2)
  have hq2pos : (0 : ℝ) < (q.2 : ℝ) := by exact_mod_cast (by omega : 0 < q.2)
  have hp1le : (p.1 : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hpI.2
  have hq1le : (q.1 : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hqI.2
  have hprodpos : (0 : ℝ) < (p.1 : ℝ) * (q.1 : ℝ) := mul_pos hp1pos hq1pos
  have hprodle : (p.1 : ℝ) * (q.1 : ℝ) ≤ 4 * (R : ℝ) ^ 2 := by
    have h := mul_le_mul hp1le hq1le (le_of_lt hq1pos) (by positivity : (0 : ℝ) ≤ 2 * (R : ℝ))
    nlinarith [h]
  have hHpos : (0 : ℝ) < H := by
    rw [hH]
    exact Real.rpow_pos_of_pos (div_pos (mul_pos hRpos hSpos) hDpos) _
  have hapos : (0 : ℝ) < a := by
    rw [ha]
    exact div_pos (by linarith [hSpos]) (mul_pos hHpos hRpos)
  -- ## the difference ratio `xPair` and the integer difference
  have hxe : Work.FIArea4.Vflip.xPair p q
      = -(((nearDelta p q : ℤ)) : ℝ) / ((p.1 : ℝ) * (q.1 : ℝ)) := by
    have hp1n : (p.1 : ℝ) ≠ 0 := ne_of_gt hp1pos
    have hq1n : (q.1 : ℝ) ≠ 0 := ne_of_gt hq1pos
    unfold Work.FIArea4.Vflip.xPair nearDelta
    push_cast
    field_simp
    ring
  have hxabs : |Work.FIArea4.Vflip.xPair p q|
      = ((nearDelta p q).natAbs : ℝ) / ((p.1 : ℝ) * (q.1 : ℝ)) := by
    rw [hxe, abs_div, abs_neg]
    have hnum : |(((nearDelta p q) : ℤ) : ℝ)| = ((nearDelta p q).natAbs : ℝ) := by
      rw [show (((nearDelta p q).natAbs : ℕ) : ℝ) = ((|nearDelta p q| : ℤ) : ℝ) by
        rw [Int.abs_eq_natAbs]; norm_num]
      exact Int.cast_abs.symm
    rw [hnum, abs_of_pos hprodpos]
  -- ## the two ratio bounds, hence `|xPair| < b`
  have hs1 : (p.2 : ℝ) / (p.1 : ℝ) < 2 * (S : ℝ) / (R : ℝ) := by
    calc (p.2 : ℝ) / (p.1 : ℝ) ≤ (2 * (S : ℝ)) / (p.1 : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ (le_of_lt hp1pos)
          exact_mod_cast hpJ.2
      _ < (2 * (S : ℝ)) / (R : ℝ) :=
          div_lt_div_of_pos_left (by linarith [hSpos]) hRpos (by exact_mod_cast hpI.1)
  have hs2 : (q.2 : ℝ) / (q.1 : ℝ) < 2 * (S : ℝ) / (R : ℝ) := by
    calc (q.2 : ℝ) / (q.1 : ℝ) ≤ (2 * (S : ℝ)) / (q.1 : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ (le_of_lt hq1pos)
          exact_mod_cast hqJ.2
      _ < (2 * (S : ℝ)) / (R : ℝ) :=
          div_lt_div_of_pos_left (by linarith [hSpos]) hRpos (by exact_mod_cast hqI.1)
  have hxlt : |Work.FIArea4.Vflip.xPair p q| < b := by
    rw [hb, Work.FIArea4.Vflip.xPair, abs_lt]
    constructor <;> linarith [hs1, hs2, div_pos hq2pos hq1pos,
      div_pos hp2pos hp1pos]
  -- ## the lower bound `a < |xPair|` in the far case
  have hfar : ¬ ((nearDelta p q).natAbs : ℝ) * H ≤ 8 * (R : ℝ) * (S : ℝ) →
      a < |Work.FIArea4.Vflip.xPair p q| := by
    intro hcond
    have hcond' : 8 * (R : ℝ) * (S : ℝ) < ((nearDelta p q).natAbs : ℝ) * H := not_le.mp hcond
    have step1 : 2 * (S : ℝ) / (H * (R : ℝ))
        ≤ 8 * (R : ℝ) * (S : ℝ) / (H * ((p.1 : ℝ) * (q.1 : ℝ))) := by
      rw [div_le_div_iff₀ (mul_pos hHpos hRpos) (mul_pos hHpos hprodpos)]
      have h1 : H * ((p.1 : ℝ) * (q.1 : ℝ)) ≤ H * (4 * (R : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hprodle (le_of_lt hHpos)
      have h2 : 2 * (S : ℝ) * (H * ((p.1 : ℝ) * (q.1 : ℝ)))
          ≤ 2 * (S : ℝ) * (H * (4 * (R : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have heq : 2 * (S : ℝ) * (H * (4 * (R : ℝ) ^ 2))
          = 8 * (R : ℝ) * (S : ℝ) * (H * (R : ℝ)) := by ring
      rw [heq] at h2
      exact h2
    have step2 : 8 * (R : ℝ) * (S : ℝ) / (H * ((p.1 : ℝ) * (q.1 : ℝ)))
        < ((nearDelta p q).natAbs : ℝ) / ((p.1 : ℝ) * (q.1 : ℝ)) := by
      rw [div_lt_div_iff₀ (mul_pos hHpos hprodpos) hprodpos]
      have hmul := mul_lt_mul_of_pos_right hcond' hprodpos
      have heq : (((nearDelta p q).natAbs : ℝ) * H) * ((p.1 : ℝ) * (q.1 : ℝ))
          = ((nearDelta p q).natAbs : ℝ) * (H * ((p.1 : ℝ) * (q.1 : ℝ))) := by ring
      rw [heq] at hmul
      exact hmul
    rw [ha, hxabs]
    exact lt_of_le_of_lt step1 step2
  -- ## the pointwise `pairWeight` bound
  have hpw_bound : ‖Work.FIArea4.Vflip.pairWeight D p q‖
      ≤ (((Finset.Ioc (D / 2) (3 * D)).filter
            (fun d => d ∣ (nearDelta p q).natAbs)).card : ℝ) := by
    rw [Work.FIArea4.Vflip.pairWeight]
    refine (norm_sum_le (Finset.Icc 1 (3 * D)) _).trans ?_
    let T : Finset ℕ := (Finset.Ioc (D / 2) (3 * D)).filter (fun d => d ∣ (nearDelta p q).natAbs)
    have hterm : ∀ d ∈ Finset.Icc 1 (3 * D),
        ‖(Work.FIArea4.Vflip.bump ((d : ℝ) / D) : ℂ) *
          (if ((p.1 * q.2 : ℕ) : ZMod d) = ((q.1 * p.2 : ℕ) : ZMod d) then
            Work.FIArea4.jw d p.1 * Work.FIArea4.jw d q.1 else 0)‖
          ≤ (if d ∈ T then (1 : ℝ) else 0) := by
      intro d hd
      by_cases hmem : d ∈ T
      · rw [if_pos hmem, norm_mul]
        have hb1 : ‖(Work.FIArea4.Vflip.bump ((d : ℝ) / D) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [Work.FIArea4.Vflip.bump_nonneg ((d : ℝ) / D)],
            Work.FIArea4.Vflip.bump_le_one _⟩
        have hb2 : ‖(if ((p.1 * q.2 : ℕ) : ZMod d) = ((q.1 * p.2 : ℕ) : ZMod d) then
            Work.FIArea4.jw d p.1 * Work.FIArea4.jw d q.1 else 0)‖ ≤ 1 := by
          by_cases hc : ((p.1 * q.2 : ℕ) : ZMod d) = ((q.1 * p.2 : ℕ) : ZMod d)
          · rw [if_pos hc, norm_mul]
            nlinarith [norm_jw_le_one d p.1, norm_jw_le_one d q.1,
              norm_nonneg (Work.FIArea4.jw d p.1), norm_nonneg (Work.FIArea4.jw d q.1)]
          · rw [if_neg hc]; simp
        nlinarith [hb1, hb2, norm_nonneg (Work.FIArea4.Vflip.bump ((d : ℝ) / D) : ℂ)]
      · refine le_of_eq ?_
        rw [if_neg hmem]
        rw [norm_eq_zero]
        by_cases hc : ((p.1 * q.2 : ℕ) : ZMod d) = ((q.1 * p.2 : ℕ) : ZMod d)
        · rw [if_pos hc]
          have hdI := Finset.mem_Icc.mp hd
          have hdivd : d ∣ (nearDelta p q).natAbs := by
            have h := zmod_congr_dvd d (p.1 * q.2) (q.1 * p.2) hc
            have he : (((q.1 * p.2 : ℕ) : ℤ) - ((p.1 * q.2 : ℕ) : ℤ)) = - nearDelta p q := by
              unfold nearDelta; push_cast; ring
            rw [he, Int.natAbs_neg] at h
            exact h
          have hdle : d ≤ D / 2 := by
            by_contra hlt
            exact hmem (Finset.mem_filter.mpr
              ⟨Finset.mem_Ioc.mpr ⟨not_le.mp hlt, hdI.2⟩, hdivd⟩)
          have hbump0 : Work.FIArea4.Vflip.bump ((d : ℝ) / D) = 0 := by
            apply Work.FIArea4.Vflip.bump_eq_zero_of_le
            rw [div_le_iff₀ hDpos]
            have h2 : d * 2 ≤ D := (Nat.le_div_iff_mul_le (k := 2) (by norm_num)).mp hdle
            have h3 : (d : ℝ) * 2 ≤ (D : ℝ) := by exact_mod_cast h2
            linarith
          rw [hbump0]; simp
        · rw [if_neg hc, mul_zero]
    calc (∑ d ∈ Finset.Icc 1 (3 * D),
          ‖(Work.FIArea4.Vflip.bump ((d : ℝ) / D) : ℂ) *
            (if ((p.1 * q.2 : ℕ) : ZMod d) = ((q.1 * p.2 : ℕ) : ZMod d) then
              Work.FIArea4.jw d p.1 * Work.FIArea4.jw d q.1 else 0)‖)
        ≤ ∑ d ∈ Finset.Icc 1 (3 * D), (if d ∈ T then (1 : ℝ) else 0) :=
          Finset.sum_le_sum hterm
      _ = ((((Finset.Icc 1 (3 * D)).filter (fun d => d ∈ T)).card : ℕ) : ℝ) := by
          rw [Finset.card_filter]; push_cast; rfl
      _ ≤ (T.card : ℝ) := by
          have hsub : (Finset.Icc 1 (3 * D)).filter (fun d => d ∈ T) ⊆ T :=
            fun d hd => (Finset.mem_filter.mp hd).2
          exact_mod_cast Finset.card_le_card hsub
      _ = (((Finset.Ioc (D / 2) (3 * D)).filter
            (fun d => d ∣ (nearDelta p q).natAbs)).card : ℝ) := rfl
  -- ## the main pointwise factor
  have hmain : ‖(((1 - Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.Vflip.xPair p q)) : ℝ) : ℂ)
        * Work.FIArea4.Vflip.pairWeight D p q‖ ≤ Work.FIArea4.Vflip.Vfd.nearKernel D R S H p q := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hcond : ((nearDelta p q).natAbs : ℝ) * H ≤ 8 * (R : ℝ) * (S : ℝ)
    · have hK : Work.FIArea4.Vflip.Vfd.nearKernel D R S H p q
          = (((Finset.Ioc (D / 2) (3 * D)).filter
              (fun d => d ∣ (nearDelta p q).natAbs)).card : ℝ) := by
        unfold nearKernel
        rw [if_pos hcond]
      rw [hK]
      have hle1 := Work.FIArea4.Vflip.nearCut_le_one a b (Work.FIArea4.Vflip.xPair p q)
      have hge0 := Work.FIArea4.Vflip.nearCut_nonneg a b (Work.FIArea4.Vflip.xPair p q)
      calc |1 - Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.Vflip.xPair p q)|
              * ‖Work.FIArea4.Vflip.pairWeight D p q‖
          ≤ 1 * ‖Work.FIArea4.Vflip.pairWeight D p q‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            rw [abs_of_nonneg (by linarith)]
            linarith
        _ = ‖Work.FIArea4.Vflip.pairWeight D p q‖ := one_mul _
        _ ≤ _ := hpw_bound
    · have hnc1 : Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.Vflip.xPair p q) = 1 :=
        Work.FIArea4.Vflip.nearCut_eq_one hapos (le_of_lt (hfar hcond)) (le_of_lt hxlt)
      have hK0 : Work.FIArea4.Vflip.Vfd.nearKernel D R S H p q = 0 := by
        unfold nearKernel
        rw [if_neg hcond]
      rw [hnc1, hK0]; norm_num
  -- ## assemble
  have hstep : ‖α p.1 p.2 * star (α q.1 q.2) *
        (((1 - Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.Vflip.xPair p q)) : ℝ) *
          Work.FIArea4.Vflip.pairWeight D p q)‖
      = ‖α p.1 p.2‖ * ‖α q.1 q.2‖ *
          ‖(((1 - Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.Vflip.xPair p q)) : ℝ) : ℂ)
            * Work.FIArea4.Vflip.pairWeight D p q‖ := by
    rw [norm_mul, norm_mul, norm_star]
  rw [hstep]
  exact mul_le_mul_of_nonneg_left hmain (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end Work.FIArea4.Vflip.Vfd
