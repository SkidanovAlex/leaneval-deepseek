import Mathlib
import Submission.Work.TMC16Core.Core.geom
import Submission.Work.TMC16Core.Core.uni_nonres3_support
import Submission.Work.TMC16Core.Core.uni_nonres3_cosne
import Submission.Work.TMC16Core.Core.uni_nonres3_irr
import Submission.Work.TMC16Core.NrFinal.nruSep
import Submission.Work.TMC16Core.NrFinal.nruDenom
import Submission.Work.TMC16Core.NrFinal.arith
import Submission.Work.TMC16Core.NrFinal.sepB_bound
import Submission.Work.TMC16Core.Core.pdw_cosne
import Submission.Work.TMC16Core.Core.pdw_sum_up
import Submission.Work.Basic.UniNonres.Defs

/-!
# `nr_uniform`: the non-resonant uniformity estimate at the `Dnr` scale

Assembly of the AJ §9 non-resonant uniformity statement from the four pieces
`NrFinal.sep` (separation of the block-aligned window), `NrFinal.denom` (the two
denominator sums), `NrFinal.sepB_bound` (the separation/Stirling estimate) and
`NrFinal.arith` (the numerical bookkeeping), together with the two numerator
sums (`Core.pdw_sum_up`) and the distinctness of the cosines
(`Core.uni_nonres3_cosne`).
-/

namespace Work.TMC16Core.NrFinal

open Work.TMC16Core

noncomputable section


/-- Cardinality of the block-aligned index set. -/
theorem nr_card_Dnr {q : ℕ → ℕ} {n s a' b' : ℕ} {y : ℤ}
    (hab : a' + b' = s) (hs : 1 ≤ s) (hL : 1 ≤ q (n - 1))
    (hy : Work.TMC16Core.Core.Tnr q n s ≤ y) :
    (Work.TMC16Core.Core.Dnr q n s a' b' y).card = 2 * s * q (n - 1) := by
  have hdisj : Disjoint
      (Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ))) ((a' : ℤ) * (q (n - 1) : ℤ) - 1))
      (Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ)) (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_Icc] at hx1 hx2
    obtain ⟨h1, h2⟩ := hx1
    obtain ⟨h3, h4⟩ := hx2
    have habZ : ((a' : ℤ) + (b' : ℤ)) = (s : ℤ) := by exact_mod_cast hab
    have hsum : (a' : ℤ) * (q (n - 1) : ℤ) + (b' : ℤ) * (q (n - 1) : ℤ)
        = (s : ℤ) * (q (n - 1) : ℤ) := by rw [← add_mul, habZ]
    simp only [Work.TMC16Core.Core.Tnr] at hy
    nlinarith [h1, h2, h3, h4]
  rw [Work.TMC16Core.Core.Dnr, Finset.card_union_of_disjoint hdisj]
  have h1 : (Finset.Icc (-((a' : ℤ) * (q (n - 1) : ℤ)))
      ((a' : ℤ) * (q (n - 1) : ℤ) - 1)).card = 2 * a' * q (n - 1) := by
    rw [Int.card_Icc]
    have : (((a' : ℤ) * (q (n - 1) : ℤ) - 1) + 1 - (-((a' : ℤ) * (q (n - 1) : ℤ)))
        : ℤ) = ((2 * a' * q (n - 1) : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  have h2 : (Finset.Icc (y - (b' : ℤ) * (q (n - 1) : ℤ))
      (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1)).card = 2 * b' * q (n - 1) := by
    rw [Int.card_Icc]
    have : (y + (b' : ℤ) * (q (n - 1) : ℤ) - 1 + 1 - (y - (b' : ℤ) * (q (n - 1) : ℤ))
        : ℤ) = ((2 * b' * q (n - 1) : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [h1, h2]
  have hsum : 2 * a' * q (n - 1) + 2 * b' * q (n - 1) = 2 * s * q (n - 1) := by
    have hZ : ((2 * a' * q (n - 1) + 2 * b' * q (n - 1) : ℕ) : ℤ)
        = ((2 * s * q (n - 1) : ℕ) : ℤ) := by
      rw [← hab]
      push_cast
      ring
    exact_mod_cast hZ
  rw [hsum]


/-- **[DEV] the target, assembled from the four pieces.** -/
theorem nr_uniform_dnr {α θ c : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {n s a' b' m : ℕ} {y : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hn : 2 ≤ n) (hL : 1 ≤ q (n - 1)) (hs : 1 ≤ s) (hab : a' + b' = s)
    (hy1 : 1 ≤ y)
    (hyΔ : (y : ℝ) * Δ n ≤ 3 / 4)
    (hym : (m : ℤ) * (q n : ℤ) ≤ y) (hym' : y < ((m : ℤ) + 1) * (q n : ℤ))
    (hnres : ∀ ℓ : ℤ, (s : ℤ) * (q (n - 1) : ℤ) ≤ |y - (ℓ : ℤ) * (q n : ℤ)|)
    (hsL : (2 * (s : ℤ)) * (q (n - 1) : ℤ) < (q n : ℤ))
    (hblk : ∀ (p : ℤ) (ξ : ℝ) (k₀ : ℤ),
      k₀ ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (q (n - 1) : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((q (n - 1) : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (q (n - 1) : ℝ))
    (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (hθ : ∀ j : ℤ, |j| ≤ 2 * |y| + 6 * (s : ℤ) * (q (n - 1) : ℤ) + 4 →
      c ≤ Work.TMC16Core.fracDist (2 * θ + (j : ℝ) * α)) :
    Work.TMC16Core.Uniform
      (2 * Real.log ((q n : ℝ) / (s : ℝ)) / (q (n - 1) : ℝ)
        + 200 * Real.log ((q (n - 1) : ℝ)) / (q (n - 1) : ℝ)
        + 2 * Real.log (1 / c) / ((s : ℝ) * (q (n - 1) : ℝ))
        + 200 / (q (n - 1) : ℝ))
      (fun j : {j : ℤ // j ∈ Work.TMC16Core.Core.Dnr q n s a' b' y} =>
        θ + (j : ℝ) * α) := by
  classical
  have hTn : 2 * s * q (n - 1) ≤ q n := by
    have h : (2 * (s : ℤ)) * (q (n - 1) : ℤ) ≤ (q n : ℤ) := le_of_lt hsL
    exact_mod_cast h
  have hyT : Work.TMC16Core.Core.Tnr q n s ≤ y := by
    have h := hnres 0
    have h' : Work.TMC16Core.Core.Tnr q n s ≤ |y| := by
      simpa [Work.TMC16Core.Core.Tnr] using h
    rwa [abs_of_nonneg (by omega : (0 : ℤ) ≤ y)] at h'
  have hirr : ∀ k : ℤ, k ≠ 0 → Work.TMC16Core.fracDist ((k : ℝ) * α) ≠ 0 :=
    Work.TMC16Core.Core.uni_nonres3_irr hmono hΔpos hΔeq hΔup
  have hcard : Fintype.card {d : ℤ // d ∈ Work.TMC16Core.Core.Dnr q n s a' b' y}
      = 2 * s * q (n - 1) := by
    rw [Fintype.card_coe]
    exact nr_card_Dnr hab hs hL hyT
  have hcosne : ∀ i j : ℤ, i ∈ Work.TMC16Core.Core.Dnr q n s a' b' y →
      j ∈ Work.TMC16Core.Core.Dnr q n s a' b' y → i ≠ j →
      Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) ≠
        Real.cos (2 * Real.pi * (θ + (j : ℝ) * α)) :=
    fun i j hi hj hij =>
      Work.TMC16Core.Core.uni_nonres3_cosne hn hs hab hTn hyT hc hirr hθ hi hj hij
  have hδpos : (0 : ℝ) < 1 / (32 * (q n : ℝ)) := by
    have : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
    positivity
  have hδh : (1 : ℝ) / (32 * (q n : ℝ)) ≤ 1 / 2 := by
    have h1 : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqpos n
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hsep_all : ∀ d ∈ Work.TMC16Core.Core.Dnr q n s a' b' y,
      ∀ d' ∈ Work.TMC16Core.Core.Dnr q n s a' b' y,
      d ≠ d' → (1 / (32 * (q n : ℝ))) ≤
        Work.TMC16Core.fracDist (((d - d' : ℤ) : ℝ) * α) := by
    intro d hd d' hd' hne
    exact Work.TMC16Core.NrFinal.nru_sep hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hL hs hab hy1 hyΔ
      hym hym' hnres hsL hd' hd (fun h => hne h.symm)
  refine ⟨?_, ?_⟩
  · intro i j hij hcon
    exact hcosne i j i.2 j.2 (fun h => hij (Subtype.ext h)) hcon
  · intro k x hx
    have hprod : (∏ i ∈ Finset.univ.erase k,
        (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
          (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))))
        = ∏ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) := by
      refine Finset.prod_bij (fun (i : {d : ℤ // d ∈ Work.TMC16Core.Core.Dnr q n s a' b' y}) _ => (i : ℤ)) ?_ ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_erase] at hi ⊢
        exact ⟨fun hEq => hi.1 (Subtype.ext hEq), i.property⟩
      · intro i _ i' _ hEq
        exact Subtype.ext hEq
      · intro b hb
        rw [Finset.mem_erase] at hb
        refine ⟨⟨b, hb.2⟩, ?_, rfl⟩
        rw [Finset.mem_erase]
        exact ⟨fun hEq => hb.1 (congrArg Subtype.val hEq), Finset.mem_univ _⟩
      · intro i _
        rfl
    rw [hprod]
    have hexp : ((Fintype.card {d : ℤ // d ∈ Work.TMC16Core.Core.Dnr q n s a' b' y} : ℝ) - 1)
          * (2 * Real.log ((q n : ℝ) / (s : ℝ)) / (q (n - 1) : ℝ)
            + 200 * Real.log ((q (n - 1) : ℝ)) / (q (n - 1) : ℝ)
            + 2 * Real.log (1 / c) / ((s : ℝ) * (q (n - 1) : ℝ))
            + 200 / (q (n - 1) : ℝ))
        = (2 * (s : ℝ) * (q (n - 1) : ℝ) - 1)
          * (2 * Real.log ((q n : ℝ) / (s : ℝ)) / (q (n - 1) : ℝ)
            + 200 * Real.log ((q (n - 1) : ℝ)) / (q (n - 1) : ℝ)
            + 2 * Real.log (1 / c) / ((s : ℝ) * (q (n - 1) : ℝ))
            + 200 / (q (n - 1) : ℝ)) := by
      rw [hcard]
      push_cast
      ring
    rw [hexp]
    set a : ℝ := Real.arccos x / (2 * Real.pi) with ha
    have hxa : Real.cos (2 * Real.pi * a) = x := by
      have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      calc Real.cos (2 * Real.pi * a) = Real.cos (Real.arccos x) := by
            congr 1
            rw [ha]
            field_simp
        _ = x := Real.cos_arccos hx.1 hx.2
    have hfacN : ∀ i : ℤ, |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = 2 * |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))| *
            |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))| := by
      intro i
      rw [← hxa, Real.cos_sub_cos]
      rw [show (2 * Real.pi * a + 2 * Real.pi * (θ + (i : ℝ) * α)) / 2
            = Real.pi * (a + (θ + (i : ℝ) * α)) by ring,
          show (2 * Real.pi * a - 2 * Real.pi * (θ + (i : ℝ) * α)) / 2
            = Real.pi * (a - (θ + (i : ℝ) * α)) by ring]
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hfacD : ∀ i : ℤ,
        |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
        = 2 * |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))| *
            |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)| := by
      intro i
      rw [Real.cos_sub_cos]
      rw [show (2 * Real.pi * (θ + (k : ℝ) * α) + 2 * Real.pi * (θ + (i : ℝ) * α)) / 2
            = Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α) by push_cast; ring,
          show (2 * Real.pi * (θ + (k : ℝ) * α) - 2 * Real.pi * (θ + (i : ℝ) * α)) / 2
            = -(Real.pi * (((i - k : ℤ)) : ℝ) * α) by push_cast; ring,
          Real.sin_neg]
      rw [abs_mul, abs_mul, abs_neg, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    by_cases hzero : ∃ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
        x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) = 0
    · obtain ⟨i, hi, hiz⟩ := hzero
      have h1 : (∏ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
          (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
            (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))) = 0 :=
        Finset.prod_eq_zero hi (by rw [hiz, zero_div])
      rw [h1, abs_zero]
      exact Real.exp_pos _
    · push_neg at hzero
      have hnum_ne : ∀ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
          x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) ≠ 0 := fun i hi => hzero i hi
      have hden_ne : ∀ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
          Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)) ≠ 0 := by
        intro i hi
        rw [Finset.mem_erase] at hi
        exact sub_ne_zero.mpr (hcosne (k : ℤ) i k.2 hi.2 (fun h => hi.1 h.symm))
      have hsinN : ∀ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
          Real.sin (Real.pi * (a + (θ + (i : ℝ) * α))) ≠ 0 ∧
          Real.sin (Real.pi * (a - (θ + (i : ℝ) * α))) ≠ 0 := by
        intro i hi
        have h1 : 2 * |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))| *
            |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))| ≠ 0 := by
          rw [← hfacN i]
          exact (abs_pos.mpr (hnum_ne i hi)).ne'
        exact ⟨fun h0 => h1 (by rw [h0]; simp), fun h0 => h1 (by rw [h0]; simp)⟩
      have hsinDD : ∀ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
          Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α)) ≠ 0 ∧
          Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α) ≠ 0 := by
        intro i hi
        have h1 : 2 * |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))| *
            |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)| ≠ 0 := by
          rw [← hfacD i]
          exact (abs_pos.mpr (hden_ne i hi)).ne'
        exact ⟨fun h0 => h1 (by rw [h0]; simp), fun h0 => h1 (by rw [h0]; simp)⟩
      have hlog : Real.log |∏ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
            (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
              (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
          = (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
              Real.log |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|)
            - (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
                Real.log |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) := by
        rw [Finset.abs_prod]
        have h1 : ∏ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
              |(x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
                (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
            = (∏ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
                |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) /
              (∏ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
                |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) := by
          rw [Finset.prod_congr rfl (fun i hi => abs_div _ _), Finset.prod_div_distrib]
        have hN : (∏ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
            |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr (fun i hi => (abs_pos.mpr (hnum_ne i hi)).ne')
        have hD'' : (∏ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
            |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr (fun i hi => (abs_pos.mpr (hden_ne i hi)).ne')
        rw [h1, Real.log_div hN hD'',
          Real.log_prod (fun i hi => (abs_pos.mpr (hnum_ne i hi)).ne'),
          Real.log_prod (fun i hi => (abs_pos.mpr (hden_ne i hi)).ne')]
      have htermN : ∀ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
          Real.log |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
          = Real.log 2 + (Real.log |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))|
              + Real.log |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))|) := by
        intro i hi
        have hs0 := (hsinN i hi).1
        have ht0 := (hsinN i hi).2
        have h1 : |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
            = 2 * (|Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))| *
              |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))|) := by
          rw [hfacN i]; ring
        rw [h1, Real.log_mul (by norm_num) (mul_ne_zero (abs_ne_zero.mpr hs0) (abs_ne_zero.mpr ht0)),
          Real.log_mul (abs_ne_zero.mpr hs0) (abs_ne_zero.mpr ht0)]
      have htermD : ∀ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
          Real.log |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
          = Real.log 2 + (Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|
              + Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|) := by
        intro i hi
        have hs0 := (hsinDD i hi).1
        have ht0 := (hsinDD i hi).2
        have h1 : |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
            = 2 * (|Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))| *
              |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|) := by
          rw [hfacD i]; ring
        rw [h1, Real.log_mul (by norm_num) (mul_ne_zero (abs_ne_zero.mpr hs0) (abs_ne_zero.mpr ht0)),
          Real.log_mul (abs_ne_zero.mpr hs0) (abs_ne_zero.mpr ht0)]
      have hexpN : ∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
            Real.log |x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
          = ((((Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ)).card : ℝ) * Real.log 2)
            + ∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
                (Real.log |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))| +
                  Real.log |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))|) := by
        rw [Finset.sum_congr rfl htermN, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      have hexpD : ∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
            Real.log |Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))|
          = ((((Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ)).card : ℝ) * Real.log 2)
            + ∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
                (Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))| +
                  Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|) := by
        rw [Finset.sum_congr rfl htermD, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      have hS1 : ∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
              (Real.log |Real.sin (Real.pi * (a + (θ + (i : ℝ) * α)))| +
                Real.log |Real.sin (Real.pi * (a - (θ + (i : ℝ) * α)))|)
          = (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
              Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|)
            + (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
              Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · exact Finset.sum_congr rfl (fun i _ => by
            rw [show a + (θ + (i : ℝ) * α) = (a + θ) + (i : ℝ) * α by ring])
        · refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [show a - (θ + (i : ℝ) * α) = -((θ - a) + (i : ℝ) * α) by ring]
          rw [show Real.pi * -((θ - a) + (i : ℝ) * α) = -(Real.pi * ((θ - a) + (i : ℝ) * α)) by ring,
            Real.sin_neg, abs_neg]
      have hS2 : ∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
              (Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))| +
                Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|)
          = (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
              Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|)
            + (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
              Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|) :=
        Finset.sum_add_distrib
      have hmain : Real.log |∏ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
            (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
              (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
          = (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
              Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|)
            + (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
              Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|)
            - ((∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
                Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|)
              + (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
                Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|)) := by
        rw [hlog, hexpN, hS1, hexpD, hS2]
        ring
      have hUp1 : (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
            Real.log |Real.sin (Real.pi * ((a + θ) + (i : ℝ) * α))|)
          ≤ -((2 * (s : ℝ) * (q (n - 1) : ℝ) - 2 * (s : ℝ)) * Real.log 2)
            + 64 * (s : ℝ) * Real.log (q (n - 1) : ℝ) :=
        Work.TMC16Core.Core.pdw_sum_up (α := α) (ξ := a + θ) (q := q) (n := n)
          (s := s) (a' := a') (b' := b') (y := y) (k := (k : ℤ))
          (hL := hL) (hs := hs) (hab := hab) (hy := hyT) (hk := k.2) (hblk := hblk)
          (hnz := fun i hi => by
            have h1 := (hsinN i hi).1
            simpa only [show a + (θ + (i : ℝ) * α) = a + θ + (i : ℝ) * α by ring] using h1)
      have hUp2 : (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
            Real.log |Real.sin (Real.pi * ((θ - a) + (i : ℝ) * α))|)
          ≤ -((2 * (s : ℝ) * (q (n - 1) : ℝ) - 2 * (s : ℝ)) * Real.log 2)
            + 64 * (s : ℝ) * Real.log (q (n - 1) : ℝ) :=
        Work.TMC16Core.Core.pdw_sum_up (α := α) (ξ := θ - a) (q := q) (n := n)
          (s := s) (a' := a') (b' := b') (y := y) (k := (k : ℤ))
          (hL := hL) (hs := hs) (hab := hab) (hy := hyT) (hk := k.2) (hblk := hblk)
          (hnz := fun i hi => by
            have h1 := (hsinN i hi).2
            intro h0
            apply h1
            have harg : Real.pi * (a - (θ + (i : ℝ) * α)) = -(Real.pi * ((θ - a) + (i : ℝ) * α)) := by ring
            rw [harg, Real.sin_neg, h0, neg_zero])
      have hLo : (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
              Real.log |Real.sin (Real.pi * (2 * θ + (((i + k : ℤ)) : ℝ) * α))|)
            + (∑ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
              Real.log |Real.sin (Real.pi * (((i - k : ℤ)) : ℝ) * α)|)
          ≥ -((4 * (s : ℝ) * (q (n - 1) : ℝ) - 4 * (s : ℝ)) * Real.log 2)
            - 128 * (s : ℝ) * Real.log (q (n - 1) : ℝ)
            + Real.log (2 * c)
            - Work.Basic.UniNonres.sepB c (1 / (32 * (q n : ℝ))) (2 * s - 1)
            - Work.Basic.UniNonres.sepB (1 / (32 * (q n : ℝ))) (1 / (32 * (q n : ℝ))) (2 * s - 1) :=
        Work.TMC16Core.NrFinal.nru_denom (α := α) (θ := θ) (c := c) (q := q) (Δ := Δ) (n := n) (s := s)
          (a' := a') (b' := b') (m := m) (y := y) (k := (k : ℤ))
          hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hL hs hab hy1 hyΔ hym hym' hnres hsL
          hblk k.2 hc hc2 hθ hδpos hδh hsep_all
      have hbound : Real.log |∏ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
            (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
              (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
          ≤ 256 * (s : ℝ) * Real.log (q (n - 1) : ℝ) - Real.log (2 * c)
            + Work.Basic.UniNonres.sepB c (1 / (32 * (q n : ℝ))) (2 * s - 1)
            + Work.Basic.UniNonres.sepB (1 / (32 * (q n : ℝ))) (1 / (32 * (q n : ℝ))) (2 * s - 1) := by
        rw [hmain]
        linarith [hUp1, hUp2, hLo]
      have harith := Work.TMC16Core.NrFinal.arith (s := s) (L := q (n - 1)) (qn := q n) hs hL hTn hc hc2
        (le_refl (1 / (32 * (q n : ℝ))))
      have hkey : Real.log |∏ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
            (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
              (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
          < (2 * (s : ℝ) * (q (n - 1) : ℝ) - 1) *
            (2 * Real.log ((q n : ℝ) / (s : ℝ)) / (q (n - 1) : ℝ)
              + 200 * Real.log ((q (n - 1) : ℝ)) / (q (n - 1) : ℝ)
              + 2 * Real.log (1 / c) / ((s : ℝ) * (q (n - 1) : ℝ))
              + 200 / (q (n - 1) : ℝ)) := lt_of_le_of_lt hbound harith
      have hpos : 0 < |∏ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
            (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
              (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))| := by
        rw [Finset.abs_prod]
        refine Finset.prod_pos (fun i hi => ?_)
        rw [abs_div]
        exact div_pos (abs_pos.mpr (hnum_ne i hi)) (abs_pos.mpr (hden_ne i hi))
      calc |∏ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
            (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
              (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|
          = Real.exp (Real.log |∏ i ∈ (Work.TMC16Core.Core.Dnr q n s a' b' y).erase (k : ℤ),
            (x - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α))) /
              (Real.cos (2 * Real.pi * (θ + (k : ℝ) * α)) - Real.cos (2 * Real.pi * (θ + (i : ℝ) * α)))|) :=
            (Real.exp_log hpos).symm
        _ < Real.exp ((2 * (s : ℝ) * (q (n - 1) : ℝ) - 1) *
            (2 * Real.log ((q n : ℝ) / (s : ℝ)) / (q (n - 1) : ℝ)
              + 200 * Real.log ((q (n - 1) : ℝ)) / (q (n - 1) : ℝ)
              + 2 * Real.log (1 / c) / ((s : ℝ) * (q (n - 1) : ℝ))
              + 200 / (q (n - 1) : ℝ))) := Real.exp_lt_exp.mpr hkey

/-- **The target statement**, in the form of the required lemma: this is `nr_uniform_dnr`
transported along the shift `j ↦ j + T - 1` (`Core.uniform_nr_shift`), which identifies the
windows `I1nr ∪ I2nr` with the block-aligned index set `Dnr`. -/
theorem nr_uniform {α θ c : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    {n s a' b' m : ℕ} {y : ℤ}
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hblk : ∀ (p : ℤ) (ξ : ℝ) (k₀ : ℤ),
      k₀ ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (q (n - 1) : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((q (n - 1) : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (q (n - 1) : ℝ))
    (hn : 2 ≤ n) (hL : 1 ≤ q (n - 1)) (hs : 1 ≤ s) (hab : a' + b' = s)
    (hy1 : 1 ≤ y)
    (hyΔ : (y : ℝ) * Δ n ≤ 3 / 4)
    (hym : (m : ℤ) * (q n : ℤ) ≤ y) (hym' : y < ((m : ℤ) + 1) * (q n : ℤ))
    (hnres : ∀ ℓ : ℤ, (s : ℤ) * (q (n - 1) : ℤ) ≤ |y - (ℓ : ℤ) * (q n : ℤ)|)
    (hsL : (2 * (s : ℤ)) * (q (n - 1) : ℤ) < (q n : ℤ))
    (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (hθ : ∀ j : ℤ, |j| ≤ 2 * |y| + 6 * (s : ℤ) * (q (n - 1) : ℤ) + 4 →
      c ≤ Work.TMC16Core.fracDist (2 * θ + (j : ℝ) * α)) :
    Work.TMC16Core.Uniform
      (2 * Real.log ((q n : ℝ) / (s : ℝ)) / (q (n - 1) : ℝ)
        + 200 * Real.log (q (n - 1) : ℝ) / (q (n - 1) : ℝ)
        + 2 * Real.log (1 / c) / ((s : ℝ) * (q (n - 1) : ℝ))
        + 200 / (q (n - 1) : ℝ))
      (fun j : {j : ℤ // j ∈ Work.TMC16Core.Core.I1nr q n s a' ∪
          Work.TMC16Core.Core.I2nr q n s b' y} =>
        θ + (((j : ℤ) : ℝ) + (((Work.TMC16Core.Core.Knr q n s : ℕ) : ℝ) - 1) / 2) * α) := by
  rw [Work.TMC16Core.Core.uniform_nr_shift (q := q) (n := n) (s := s) (a' := a') (b' := b')
    (y := y) (θ := θ) hs hL]
  exact nr_uniform_dnr (α := α) (θ := θ) (c := c) (q := q) (Δ := Δ) (n := n) (s := s)
    (a' := a') (b' := b') (m := m) (y := y)
    (hqpos := hqpos) (hmono := hmono) (hΔpos := hΔpos) (hΔeq := hΔeq) (hΔup := hΔup)
    (hΔlo := hΔlo) (hbest := hbest) (hn := hn) (hL := hL) (hs := hs) (hab := hab)
    (hy1 := hy1) (hyΔ := hyΔ) (hym := hym) (hym' := hym') (hnres := hnres)
    (hsL := hsL) (hblk := hblk) (hc := hc) (hc2 := hc2) (hθ := hθ)

end

end Work.TMC16Core.NrFinal
