/-
# The two fibre identifications of the A6 loss-form route, with **ρ-dependent** thresholds

The A6 route as designed (`Submission/Work/KMTPlan/A6Clean/fiberOpSet_mdlSliceF_eq_fiberOp_of_large.lean`
and its `g`-twin, and the two consumers `mdlSliceNoGainF/G`) asks for a *single* threshold `B`,
independent of `ρ ∈ (0,1]`, above which the *cumulative*-height fibre

  `fiberOpSet (iwArithFreqs ρ l) m n₀ h`

coincides with the *exact*-height fibre `fiberOp ρ l m n₀ h`.  That statement is **false**: the
separation argument behind it needs `2^{-2·uScale ρ L} + γ < ‖α - β‖`, i.e. roughly
`uScale ρ L ≳ l`, whereas for `ρ → 0` and `L ~ 1/ρ` one has `uScale ρ L = 2` while `l` may be as
large as `L` (all the other hypotheses, including `mdlCore`, being satisfiable there — one may
take `C₀ = L`, `N = 2^L`, `l₁ = l₂ = L`, `k₁ = k₂ = 0`).  In that regime the window
`periodize (mStarF (uScale ρ L))` is much wider than the minimal frequency separation and the
window pieces at the cumulative-but-not-exact frequencies do not vanish.

What *is* true, and what the route actually needs (the final estimates of `MdlSliceNoGainAt`
admit constants depending on `ρ`), is the same identity with a threshold `B = B(ρ)` chosen after
`ρ` — that is the form proved here.  For `L ≥ B(ρ)` one has `uScale ρ L ≳ max (l, Cρ·2^{ρl})`,
so that the standard separation lemma (`sep_of_goodMajorArcs`) gives exactly the required gap.

The two statements below are therefore the ``vanishing'' inputs of the route, in the corrected
form: `∀ ρ, 0 < ρ → ρ ≤ 1 → ∃ B, ...` (compare the (false) `∃ B, ∀ ρ, ...` of the stubs).
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.mdlSliceNoGainAux
import Submission.Work.KMTPlan.A6Clean.mdlSliceF_fiberVarSampling
import Submission.Work.KMTPlan.A6Clean.mdlSliceG_fiberVarSampling
import Submission.Work.KMTPlan.A6Clean.Tle_mdlG_eq_Tex
import Submission.Work.KMTPlan.A6.Btwist_eq_BtwistEx_tm

set_option maxHeartbeats 1600000

namespace Work.KMTPlan.A6Clean

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTPlan.A6

noncomputable section

/-- **The `f`-side cumulative fibre is the exact-height fibre on the large scales**, with a
threshold depending on `ρ`. -/
theorem fiberOpSet_mdlSliceF_eq_fiberOp_of_largeRho (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ B : ℕ, ∀ (C₀ : ℕ) (a : ℕ → NNReal)
      (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ) (f : ℤ → ℂ),
      B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ → 1 ≤ l₁ →
      (∀ n : ℕ, 1 ≤ a n) → j₁ ∈ ({-1, 0, 1} : Finset ℤ) → (k₁ = 0 → j₁ ≠ -1) →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∀ (n : ℕ), Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → ∀ (n₀ : ℤ) (x : ℤ),
        Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) x
          = Work.KMTAreas.A7.fiberOp ρ l₁
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) x := by
  obtain ⟨Cna, hCnaPos, hCna⟩ :=
    Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing hρ
  obtain ⟨Bna, hBna⟩ :=
    Work.KMTPlan.A6Clean.goodMajorArcs_uScale_of_large ρ hρ Cna hCnaPos
  obtain ⟨Cρ, hCρpos, hCρsep⟩ := Work.KMTAreas.A7Hi.sep_of_goodMajorArcs ρ hρ hρ1
  obtain ⟨Bsep, hBsep⟩ :=
    Work.KMTPlan.A6Clean.goodMajorArcs_uScale_of_large ρ hρ Cρ hCρpos
  obtain ⟨Bfas, hBfas⟩ := Work.KMTAreas.A7.farey_and_strict_of_large_L ρ hρ hρ1
  refine ⟨Bna + Bsep + Bfas + 1, ?_⟩
  intro C₀ a l₁ l₂ k₁ k₂ j₁ t f hB hl₁ ha1 hj₁ hk₁ hf ht n hn n₀ x
  set L : ℕ := Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ with hLdef
  set U : ℕ := Work.KMTAreas.A7.uScale ρ L with hUdef
  set q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) with hqdef
  have hLeq : L = max (max l₁ l₂) (max k₁ k₂) := by rw [hLdef, Work.KMTPlan.A6.lcL]
  have hl₁L : l₁ ≤ L := by omega
  have hBnaL : Bna ≤ L := by omega
  have hBsepL : Bsep ≤ L := by omega
  have hBfasL : Bfas < L := by omega
  have hUeq : U = Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) := by
    rw [hUdef, hLeq]
  have hqeq : q = Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) := rfl
  -- the largeness consequences on the core
  have hsplit : Work.KMTAreas.A7.splitCut ρ L < Nat.floor (a n) :=
    ((Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hn).2.1
  have hsplit' : Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
      < Nat.floor (a n) := by rw [← hLeq]; exact hsplit
  have hN1 : 1 ≤ Nat.floor (a n) := (Nat.one_le_floor_iff (a n)).mpr (ha1 n)
  have hNpos : 0 < Nat.floor (a n) := hN1
  have hfs := hBfas l₁ l₂ k₁ k₂ (Nat.floor (a n)) hsplit' (by rw [← hLeq]; exact hBfasL)
  have hfarey : (2 : ℝ) ^ k₁ * (q : ℝ) * 8 ≤ (Nat.floor (a n) : ℝ) := hfs.1
  have hplat : k₁ + 2 * U + 1 ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat := hfs.2
  -- the packet radius
  set γ : ℝ := (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ))
    with hγdef
  have hγle : γ ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) := by
    rw [hγdef]
    exact (Work.KMTPlan.A6Clean.bandRadius_le k₁ U (Nat.floor (a n)) q hNpos hfarey hplat).1
  have hγpos : 0 < γ := by rw [hγdef]; positivity
  have ht_pos : 0 < (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) := zpow_pos (by norm_num) _
  -- `2 * 2^{-2U-1} = 2^{-2U}`
  have h2δ : 2 * (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) = (2 : ℝ) ^ (-(2 * (U : ℤ))) := by
    rw [show (-(2 * (U : ℤ))) = (-(2 * (U : ℤ)) - 1) + 1 by ring,
      zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  -- the window support
  have hmsupp : ∀ θ : ℝ, 2 * (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) < |θ| →
      Work.KMTAreas.A7.mStarF U θ = 0 := by
    intro θ hθ
    by_contra hne
    have h1 := Work.KMTPlan.A6.mStarF_ne_zero_abs_le U θ hne
    rw [h2δ] at hθ
    linarith
  -- the exact-height band of the packet
  have hband : ∃ hw : Memℓp (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) hw
        (⋃ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₁,
          Work.BourgainPlan.IonescuWainger.arcSet β γ) := by
    by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · obtain ⟨M, hM0, hMbd, hMper, hMarc⟩ :=
        Work.KMTPlan.A6.varphiNtjPeriodize_aux (Nat.floor (a n)) k₁ j₁ t hj₁ hk₁ hN1
      have hγsmall : γ ≤ (2 : ℝ) ^ (-(U : ℤ) - 1) :=
        le_trans hγle (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))
      have hΦ : Work.Analysis.IonescuWainger.SupportedInArc (-(U : ℤ) - 1)
          (Work.Analysis.IonescuWainger.periodize
            (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t)) :=
        supportedInArc_of_arcSet_le U _ γ hMarc hγsmall
      have hnA : Work.Analysis.IonescuWainger.NonAliasing (-(U : ℤ))
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) :=
        hCna l₁ (-(U : ℤ)) (hBna l₁ L hl₁L hBnaL).1
      have heq := mdlSliceF_eq_Tm ρ hρ hρ1 C₀ a l₁ l₂ k₁ k₂ j₁ t f n hj₁ hk₁ hc hf hnA hΦ
      rw [heq]
      obtain ⟨hw, hsup⟩ := Work.KMTPlan.A6Clean.tmBandOfArc ρ l₁
        (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t) γ hMper hMarc f
        (Work.KMTPlan.A6.memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hf)
      exact ⟨hw, hsup⟩
    · have hzero : Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n = 0 := by
        funext y
        simp only [Work.KMTPlan.A6.mdlSliceF, hc, if_false]
      rw [hzero]
      exact Work.KMTPlan.A6.zero_hasFreqSupport _
  obtain ⟨hh, hhE⟩ := hband
  -- the separation
  have hsep : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
      ∀ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, α ≠ β →
        2 * (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) + γ < ‖α - β‖ := by
    intro α hα β hβ hne
    have hgm : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(2 * (U : ℤ))) :=
      (hBsep l₁ L hl₁L hBsepL).2
    have h4 := hCρsep l₁ (-(2 * (U : ℤ))) (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
      hgm Finset.Subset.rfl α hα β (diffFreqs_subset_iwArithFreqs ρ l₁ hβ) hne
    have h4' : 8 * (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) ≤ ‖α - β‖ := by
      have h2δ' : (2 : ℝ) ^ (-(2 * (U : ℤ))) = 2 * (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) := h2δ.symm
      rw [h2δ'] at h4
      linarith
    linarith [hγle, h4', ht_pos]
  -- the abstract fibre identity
  have hkey := Work.KMTPlan.A6Clean.fiberOpSet_cumulative_eq_of_exact_band ρ hρ hρ1 l₁
    (Work.KMTAreas.A7.mStarF U) ((2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) γ ht_pos hγpos
    (Work.KMTPlan.A6.integrable_mStarF U) (Work.KMTPlan.A6.cw_mStarF_summable' U)
    hmsupp (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) hh hhE hsep n₀ x
  rw [hkey, Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew (by omega : l₁ ≠ 0)]
  rw [Work.KMTAreas.A7.fiberOp_eq_fiberOpSet_iwArithFreqsNew]

/-- **The `g`-side cumulative fibre is the exact-height fibre on the large scales**, with a
threshold depending on `ρ`. -/
theorem fiberOpPSet_mdlSliceG_eq_fiberOpP_of_largeRho (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ B : ℕ, ∀ (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
      (C₀ : ℕ) (a : ℕ → NNReal)
      (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (g : ℤ → ℂ),
      B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ → 1 ≤ l₂ →
      (∀ n : ℕ, 1 ≤ a n) → j₂ ∈ ({-1, 0, 1} : Finset ℤ) → (k₂ = 0 → j₂ ≠ -1) →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∀ (n : ℕ), Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → ∀ (n₀ : ℤ) (x : ℤ),
        Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
            (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x
          = Work.KMTAreas.A7.fiberOpP ρ P l₂
            (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x := by
  obtain ⟨Bna, hBna⟩ := Work.KMTAreas.A7.exists_nonAliasing_uScale ρ hρ hρ1
  obtain ⟨Cρ, hCρpos, hCρsep⟩ := Work.KMTAreas.A7Hi.sep_of_goodMajorArcs ρ hρ hρ1
  obtain ⟨Bsep, hBsep⟩ :=
    Work.KMTPlan.A6Clean.goodMajorArcs_uScale_of_large ρ hρ Cρ hCρpos
  obtain ⟨Bfas, hBfas⟩ := Work.KMTAreas.A7Hi.farey_and_strict_of_large_L_g ρ hρ hρ1
  refine ⟨Bna + Bsep + Bfas + 1, ?_⟩
  intro P hd C₀ a l₁ l₂ k₁ k₂ j₂ t g hB hl₂ ha1 hj₂ hk₂ hg ht n hn n₀ x
  set L : ℕ := Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ with hLdef
  set U : ℕ := Work.KMTAreas.A7.uScale ρ L with hUdef
  set q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) with hqdef
  have hLeq : L = max (max l₁ l₂) (max k₁ k₂) := by rw [hLdef, Work.KMTPlan.A6.lcL]
  have hl₂L : l₂ ≤ L := by omega
  have hBnaL : Bna ≤ L := by omega
  have hBsepL : Bsep ≤ L := by omega
  have hBfasL : Bfas < L := by omega
  have hUeq : U = Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) := by
    rw [hUdef, hLeq]
  have hl₂ne : l₂ ≠ 0 := by omega
  have hd2 : 2 ≤ P.natDegree := hd
  have hsplit : Work.KMTAreas.A7.splitCut ρ L < Nat.floor (a n) :=
    ((Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hn).2.1
  have hsplit' : Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
      < Nat.floor (a n) := by rw [← hLeq]; exact hsplit
  have hN1 : 1 ≤ Nat.floor (a n) := (Nat.one_le_floor_iff (a n)).mpr (ha1 n)
  have hfs := hBfas l₁ l₂ k₁ k₂ (Nat.floor (a n)) hsplit' (by rw [← hLeq]; exact hBfasL)
  have hstrict : (k₂ : ℤ) + 2 * (U : ℤ) + 1
      ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat := by
    have h2 : (k₂ : ℤ)
        + 2 * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ) + 1
        ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ) := by
      exact_mod_cast hfs.2
    simpa only [hUeq] using h2
  -- the non-singularity condition
  have hk : k₂ ≠ 0 ∨ 0 ≤ j₂ := by
    rcases (by simpa using hj₂ : j₂ = -1 ∨ j₂ = 0 ∨ j₂ = 1) with h | h | h
    · by_cases hk0 : k₂ = 0
      · exact absurd h (hk₂ hk0)
      · exact Or.inl hk0
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  -- the packet radius and the support of the modified bump
  set γ : ℝ := (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (U : ℤ))) - 1) with hγdef
  have hγpos : 0 < γ := zpow_pos (by norm_num) _
  have hsup : ∀ ξ : ℝ, Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ ≠ 0 →
      |ξ| ≤ γ := by
    intro ξ hξ
    rw [hγdef]
    exact (Work.KMTPlan.A6.varphitildeNtj_abs_le P (Nat.floor (a n)) k₂ j₂ t ξ hξ).trans
      (Work.KMTPlan.A6Clean.rpow_varphitildeNtj_le P (by omega) (Nat.floor (a n)) k₂ U j₂ t
        hstrict)
  -- `2 * 2^{-d·2U-1} = 2^{-d·2U}`
  have h2δ : 2 * (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (U : ℤ))) - 1)
      = (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (U : ℤ)))) := by
    rw [show (-((P.natDegree : ℤ) * (2 * (U : ℤ))))
        = (-((P.natDegree : ℤ) * (2 * (U : ℤ))) - 1) + 1 by ring,
      zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hmsupp : ∀ θ : ℝ, 2 * (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (U : ℤ))) - 1) < |θ| →
      Work.KMTAreas.A7.mStargF P.natDegree U θ = 0 := by
    intro θ hθ
    by_contra hne
    have h1 := Work.KMTPlan.A6.mStargF_ne_zero_abs_le P.natDegree U θ hne
    have h1' : |θ| ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (U : ℤ)))) := by
      simpa only [show (-((P.natDegree : ℤ) * 2 * (U : ℤ)))
        = -((P.natDegree : ℤ) * (2 * (U : ℤ))) by ring] using h1
    rw [h2δ] at hθ
    linarith
  -- the exact-height band of the packet
  have hband : ∃ hw : Memℓp (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) hw
        (⋃ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
          Work.BourgainPlan.IonescuWainger.arcSet β γ) := by
    by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · have hnA : Work.Analysis.IonescuWainger.NonAliasing
          (-((P.natDegree : ℤ) * (U : ℤ)))
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) :=
        Work.KMTAreas.A7Hi.nonAliasing_mono_scale
          (by have h0 : (0 : ℤ) ≤ (U : ℤ) := Int.natCast_nonneg U
              have h1 : (2 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd
              nlinarith)
          (hBna l₂ L hl₂L hBnaL)
      have hcollapse := Work.KMTPlan.A6Clean.Tle_mdlG_eq_Tex ρ hρ hρ1 P U l₂
        (Nat.floor (a n)) k₂ j₂ t g hl₂ne hk hg hnA hsup
      rw [show Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n
          = Work.KMTAreas.A7.Tex ρ l₂
              (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) g from by
        simp only [Work.KMTPlan.A6.mdlSliceG, hc, if_true]
        exact hcollapse]
      obtain ⟨hw, hsup'⟩ := Work.KMTAreas.A7.hasFreqSupport_Tex_of_memℓp ρ l₂
        (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) γ
        (Work.KMTPlan.A6.integrable_varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t hk)
        (Work.KMTPlan.A6.summable_cw_varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t hk)
        (fun θ hθ => Work.KMTAreas.A7.fiberOpTex_periodize_ne_zero_mem_arcSet hsup hθ)
        g (Work.KMTPlan.A6.memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hg)
      refine ⟨hw, ?_⟩
      simpa only [← Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl₂ne] using hsup'
    · have hzero : Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n = 0 := by
        funext y
        simp only [Work.KMTPlan.A6.mdlSliceG, hc, if_false]
      rw [hzero]
      exact Work.KMTPlan.A6.zero_hasFreqSupport _
  obtain ⟨hh, hhE⟩ := hband
  -- the separation
  have hsep : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
      ∀ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₂, α ≠ β →
        2 * (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (U : ℤ))) - 1) + γ < ‖α - β‖ := by
    intro α hα β hβ hne
    have hgm : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂
        (-((P.natDegree : ℤ) * (2 * (U : ℤ)))) := by
      have h2U : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂ (-(2 * (U : ℤ))) :=
        (hBsep l₂ L hl₂L hBsepL).2
      have hk : (-((P.natDegree : ℤ) * (2 * (U : ℤ)))) ≤ (-(2 * (U : ℤ))) := by
        have h0 : (0 : ℤ) ≤ (U : ℤ) := Int.natCast_nonneg U
        have h1 : (1 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast (by omega : 1 ≤ P.natDegree)
        nlinarith
      exact le_trans (by exact_mod_cast hk) h2U
    have h4 := hCρsep l₂ (-((P.natDegree : ℤ) * (2 * (U : ℤ))))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
      hgm Finset.Subset.rfl α hα β (diffFreqs_subset_iwArithFreqs ρ l₂ hβ) hne
    have h4' : 8 * (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (U : ℤ))) - 1) ≤ ‖α - β‖ := by
      have h2δ' : (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (U : ℤ))))
          = 2 * (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (U : ℤ))) - 1) := h2δ.symm
      rw [h2δ'] at h4
      linarith
    have h3 : 2 * (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (U : ℤ))) - 1) + γ
        = 3 * (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (U : ℤ))) - 1) := by
      rw [hγdef]; ring
    rw [h3]
    linarith [h4', zpow_pos (by norm_num : (0 : ℝ) < 2)
      (-((P.natDegree : ℤ) * (2 * (U : ℤ))) - 1)]
  -- the abstract fibre identity
  have hkey := Work.KMTPlan.A6Clean.fiberOpSet_cumulative_eq_of_exact_band ρ hρ hρ1 l₂
    (Work.KMTAreas.A7.mStargF P.natDegree U)
    ((2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (U : ℤ))) - 1)) γ
    (zpow_pos (by norm_num) _) hγpos
    (Work.KMTPlan.A6.integrable_mStargF P.natDegree U)
    (Work.KMTPlan.A6.cw_mStargF_summable' P.natDegree U)
    hmsupp (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) hh hhE hsep (P.eval n₀) x
  have hgoal : Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
        (Work.KMTAreas.A7.mStargF P.natDegree U) (P.eval n₀)
        (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x
      = Work.KMTAreas.A7.fiberOpSet
        (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂)
        (Work.KMTAreas.A7.mStargF P.natDegree U) (P.eval n₀)
        (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x := by
    rw [hkey, Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl₂ne]
  exact hgoal

end

end Work.KMTPlan.A6Clean
