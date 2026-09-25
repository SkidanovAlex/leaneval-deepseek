import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_model_maximal_l2

namespace Work.BourgainPlan.Maximal

/-- **The non-monic major-arc model collapses to a single term on an arc.**  If some triple
`(q, a, l)` with `1 ≤ q ≤ ⌊N^{1/4}⌋`, `a < q`, `gcd a q = 1`, `l ∈ Icc (-1) P.leadingCoeff` satisfies
the arc condition `|c θ − a/q − l| ≤ N^{-(d−1/4)}`, then the model
`polyMajorArcModelPre P (1/4) N θ` equals the single term of that triple.

Proof route: verbatim adaptation of `Commons.Analysis.ExponentialSums.powMajorArcModel_eq_single`
(Submission/Commons/Analysis/ExponentialSums/pure_power_kernel_maximal_l2.lean, lines ~252–320), with
`powMajorArcBlock`/`powModelTerm` replaced by `polyMajorArcBlockPre`/`polyModelTermPre` and uniqueness
supplied by `Commons.Analysis.ExponentialSums.majorArc_term_unique` together with the separation
estimate `2 N^{-(d-1/4)} < (q q')^{-1}` (the same estimate as
`Work.BourgainPlan.Maximal.poly_arc_witness_unique`, proved here inline for self-containedness). -/
theorem polyMajorArcModelPre_eq_single (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    {N : ℕ} (hN : 3 ≤ N) (θ : ℝ)
    (h : ∃ x : ℕ × ℕ × ℤ, 1 ≤ x.1 ∧ x.1 ≤ Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) ∧
        x.2.1 < x.1 ∧ Nat.gcd x.2.1 x.1 = 1 ∧
        x.2.2 ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff ∧
        |(P.leadingCoeff : ℝ) * θ - (x.2.1 : ℝ) / (x.1 : ℝ) - (x.2.2 : ℝ)|
          ≤ (N : ℝ) ^ (-((P.natDegree : ℝ) - (1:ℝ)/4))) :
    Work.BourgainPlan.Maximal.polyMajorArcModelPre P ((1:ℝ)/4) N θ
      = Work.BourgainPlan.Maximal.polyModelTermPre P N h.choose.1 h.choose.2.1 h.choose.2.2 θ := by
  obtain ⟨hq1, hqfl, ha, hgcd, hl, hdist⟩ := h.choose_spec
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hd' : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  have hqpos : 0 < h.choose.1 := by omega
  have hqR : ((h.choose.1 : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/4) :=
    le_trans (by exact_mod_cast hqfl) (Nat.floor_le (Real.rpow_nonneg hNpos.le _))
  -- separation of two arcs of radius `N^{-(d-1/4)}` with denominators `≤ N^{1/4}`
  have hsep : ∀ {q q' : ℕ}, 0 < q → 0 < q' → (q : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/4) →
      (q' : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/4) →
      2 * (N : ℝ) ^ (-((P.natDegree : ℝ) - (1:ℝ)/4)) < ((q:ℝ)*(q':ℝ))⁻¹ := by
    intro q q' _ _ hq hq'
    have hprod : (q:ℝ)*(q':ℝ) ≤ (N:ℝ)^(1/2:ℝ) := by
      calc (q:ℝ)*(q':ℝ) ≤ (N:ℝ)^((1:ℝ)/4) * (N:ℝ)^((1:ℝ)/4) :=
            mul_le_mul hq hq' (by positivity) (by positivity)
        _ = (N:ℝ)^(1/2:ℝ) := by
            rw [← Real.rpow_add hNpos]
            norm_num
    have hpos : (0:ℝ) < (q:ℝ)*(q':ℝ) := by positivity
    have h1 : (N:ℝ)^(-((1:ℝ)/2)) ≤ ((q:ℝ)*(q':ℝ))⁻¹ := by
      have h1' : ((N:ℝ)^((1:ℝ)/2))⁻¹ ≤ ((q:ℝ)*(q':ℝ))⁻¹ :=
        (inv_le_inv₀ (Real.rpow_pos_of_pos hNpos _) hpos).mpr hprod
      rwa [← Real.rpow_neg hNpos.le ((1:ℝ)/2)] at h1'
    have h2 : 2 * (N:ℝ)^(-((P.natDegree : ℝ)-(1:ℝ)/4)) ≤ 2 * (N:ℝ)^(-(7/4:ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
      linarith
    have h3 : 2 * (N:ℝ)^(-((7:ℝ)/4)) < (N:ℝ)^(-((1:ℝ)/2)) := by
      have hN54 : (2:ℝ) < (N:ℝ)^((5:ℝ)/4) := by
        calc (2:ℝ) < 3 := by norm_num
          _ ≤ (N:ℝ) := by exact_mod_cast hN
          _ = (N:ℝ)^(1:ℝ) := (Real.rpow_one (N:ℝ)).symm
          _ ≤ (N:ℝ)^((5:ℝ)/4) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      have h4 : (N:ℝ)^(-((7:ℝ)/4)) = (N:ℝ)^(-((1:ℝ)/2)) * (N:ℝ)^(-((5:ℝ)/4)) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      have h5 : (N:ℝ)^(-((5:ℝ)/4)) = ((N:ℝ)^((5:ℝ)/4))⁻¹ :=
        Real.rpow_neg hNpos.le ((5:ℝ)/4)
      have h1' : 2 * (N:ℝ)^(-((5:ℝ)/4)) < 1 := by
        rw [h5, ← div_eq_mul_inv, div_lt_one (Real.rpow_pos_of_pos hNpos _)]
        exact hN54
      have h2' : (0:ℝ) < (N:ℝ)^(-((1:ℝ)/2)) := Real.rpow_pos_of_pos hNpos _
      rw [h4]
      calc 2 * ((N:ℝ)^(-((1:ℝ)/2)) * (N:ℝ)^(-((5:ℝ)/4)))
          = (N:ℝ)^(-((1:ℝ)/2)) * (2 * (N:ℝ)^(-((5:ℝ)/4))) := by ring
        _ < (N:ℝ)^(-((1:ℝ)/2)) * 1 := mul_lt_mul_of_pos_left h1' h2'
        _ = (N:ℝ)^(-((1:ℝ)/2)) := by ring
    exact lt_of_le_of_lt h2 (lt_of_lt_of_le h3 h1)
  -- uniqueness of the arc witness, in the form needed below
  have huniq : ∀ {q : ℕ} {a : ℕ} {l : ℤ}, 0 < q → (q : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/4) → a < q →
      Nat.gcd a q = 1 → l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff →
      |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ) - (l : ℝ)|
        ≤ (N : ℝ) ^ (-((P.natDegree : ℝ) - (1:ℝ)/4)) →
      q = h.choose.1 ∧ a = h.choose.2.1 ∧ l = h.choose.2.2 := by
    intro q a l hq0 hqR' ha' hg' _ hd'
    exact Commons.Analysis.ExponentialSums.majorArc_term_unique
      (θ := (P.leadingCoeff : ℝ) * θ)
      (r := (N : ℝ) ^ (-((P.natDegree : ℝ) - (1:ℝ)/4)))
      (q₁ := q) (q₂ := h.choose.1) (a₁ := a) (a₂ := h.choose.2.1)
      (l₁ := l) (l₂ := h.choose.2.2)
      hq0 hqpos ha' ha hg' hgcd hd' hdist (hsep hq0 hqpos hqR' hqR)
  have hblk : polyMajorArcBlockPre P ((1:ℝ)/4) N θ h.choose.1
      = polyModelTermPre P N h.choose.1 h.choose.2.1 h.choose.2.2 θ := by
    rw [polyMajorArcBlockPre]
    rw [Finset.sum_eq_single (s := Finset.range h.choose.1) (f := fun a =>
      (if Nat.gcd a h.choose.1 = 1 then
        ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
          if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(h.choose.1:ℝ) - (l:ℝ)|
              ≤ (N:ℝ)^(-((P.natDegree:ℝ)-(1:ℝ)/4))
          then polyModelTermPre P N h.choose.1 a l θ else 0
        else 0 : ℂ)) h.choose.2.1
      (fun a hamem hane => by
        by_cases hg : Nat.gcd a h.choose.1 = 1
        · rw [if_pos hg]
          refine Finset.sum_eq_zero (s := Finset.Icc (-1:ℤ) P.leadingCoeff) (f := fun l =>
            (if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(h.choose.1:ℝ) - (l:ℝ)|
                ≤ (N:ℝ)^(-((P.natDegree:ℝ)-(1:ℝ)/4))
              then polyModelTermPre P N h.choose.1 a l θ else 0 : ℂ)) (fun l hlmem => ?_)
          by_cases hc : |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(h.choose.1:ℝ) - (l:ℝ)|
              ≤ (N:ℝ)^(-((P.natDegree:ℝ)-(1:ℝ)/4))
          · rw [if_pos hc]
            exact absurd (huniq (q := h.choose.1) (a := a) (l := l) hqpos hqR
              (Finset.mem_range.mp hamem) hg hlmem hc).2.1 hane
          · rw [if_neg hc]
        · rw [if_neg hg])
      (fun hnot => absurd (Finset.mem_range.mpr ha) hnot)]
    rw [if_pos hgcd]
    rw [Finset.sum_eq_single (s := Finset.Icc (-1:ℤ) P.leadingCoeff) (f := fun l =>
      (if |(P.leadingCoeff:ℝ)*θ - (h.choose.2.1:ℝ)/(h.choose.1:ℝ) - (l:ℝ)|
          ≤ (N:ℝ)^(-((P.natDegree:ℝ)-(1:ℝ)/4))
        then polyModelTermPre P N h.choose.1 h.choose.2.1 l θ else 0 : ℂ)) h.choose.2.2
      (fun l hlmem hlne => by
        by_cases hc : |(P.leadingCoeff:ℝ)*θ - (h.choose.2.1:ℝ)/(h.choose.1:ℝ) - (l:ℝ)|
            ≤ (N:ℝ)^(-((P.natDegree:ℝ)-(1:ℝ)/4))
        · rw [if_pos hc]
          exact absurd (huniq (q := h.choose.1) (a := h.choose.2.1) (l := l) hqpos hqR ha hgcd
            hlmem hc).2.2 hlne
        · rw [if_neg hc])
      (fun hnot => absurd hl hnot)]
    rw [if_pos hdist]
  rw [polyMajorArcModelPre]
  rw [Finset.sum_eq_single (s := Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))))
    (f := polyMajorArcBlockPre P ((1:ℝ)/4) N θ) h.choose.1
    (fun q hqmem hqne => by
      rw [polyMajorArcBlockPre]
      refine Finset.sum_eq_zero (s := Finset.range q) (f := fun a =>
        (if Nat.gcd a q = 1 then
          ∑ l ∈ Finset.Icc (-1:ℤ) P.leadingCoeff,
            if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|
                ≤ (N:ℝ)^(-((P.natDegree:ℝ)-(1:ℝ)/4))
            then polyModelTermPre P N q a l θ else 0
          else 0 : ℂ)) (fun a hamem => ?_)
      by_cases hg : Nat.gcd a q = 1
      · rw [if_pos hg]
        refine Finset.sum_eq_zero (s := Finset.Icc (-1:ℤ) P.leadingCoeff) (f := fun l =>
          (if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|
              ≤ (N:ℝ)^(-((P.natDegree:ℝ)-(1:ℝ)/4))
            then polyModelTermPre P N q a l θ else 0 : ℂ)) (fun l hlmem => ?_)
        by_cases hc : |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|
            ≤ (N:ℝ)^(-((P.natDegree:ℝ)-(1:ℝ)/4))
        · rw [if_pos hc]
          exact absurd (huniq (q := q) (a := a) (l := l)
            (by have h1 := (Finset.mem_Icc.mp hqmem).1; omega)
            (le_trans (by exact_mod_cast (Finset.mem_Icc.mp hqmem).2)
              (Nat.floor_le (Real.rpow_nonneg hNpos.le _)))
            (Finset.mem_range.mp hamem) hg hlmem hc).1 hqne
        · rw [if_neg hc]
      · rw [if_neg hg])
    (fun hnot => absurd (Finset.mem_Icc.mpr ⟨hq1, hqfl⟩) hnot)]
  exact hblk

end Work.BourgainPlan.Maximal
