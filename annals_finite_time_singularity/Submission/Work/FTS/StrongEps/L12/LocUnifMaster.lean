/-
# `L12_tendsto_locUnif` — the master bound

The single analytic inequality behind the convergence of `L₁₂(·)(z)`: for a datum `D` in `ℋ⁰` with
`HkSq α 0 D ≤ C`, and a box `[δ,R] × [ε,π/2-ε]` on which the weighted datum is small
(`|Gaz D s θ| ≤ η`), one has

`‖L₁₂ D z‖ ≤ BK √C √(δ³) + BK √C √(1/(1+R)) + √(angEnd ε) √W2 √C + η · angKSw · ∫_{[δ,R]} Wlam`.

The four terms are the near-zero piece, the far piece, the two angular end-pieces and the middle
piece (controlled by the box-uniform smallness of `Gaz`).  The proof splits the radial integral at
`(0,δ)`, `[δ,R]`, `(R,∞)` and uses the pointwise density bounds
`abs_L12dens_le_zero` (crude, from `HkMem α 0`) and `DensSplit` (fine, on the box), together with
the radial Cauchy–Schwarz `WlamCS` and the weight bounds `WlamSqIoo`, `WlamSqIoi`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.L12.LocUnifAux
import Submission.Work.FTS.StrongEps.L12.DensSplit
import Submission.Work.FTS.StrongEps.L12.WlamCS
import Submission.Work.FTS.StrongEps.L12.WlamSqIoo
import Submission.Work.FTS.StrongEps.L12.WlamSqIoi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The master bound -/

theorem L12_master_bound {α : ℝ} {D : ℝ → ℝ → ℝ} {C δ R ε η : ℝ}
    (hmem : Work.Spaces.HkMem α 0 D)
    (hbd : Work.Spaces.HkSq α 0 D ≤ C) (hC : 0 ≤ C)
    (hδ : 0 < δ) (hδR : δ ≤ R) (hε : 0 < ε) (hε4 : ε ≤ Real.pi / 4) (hη : 0 ≤ η)
    (hbox : ∀ s ∈ Set.Icc δ R, ∀ θ ∈ Set.Icc ε (Real.pi / 2 - ε),
      |Work.FTS.GalBasis.cc.Gaz D s θ| ≤ η)
    {z : ℝ} (hz : 0 ≤ z) :
    ‖Work.Construction.L12 D z‖
      ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (δ ^ 3)
        + Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (1 / (1 + R))
        + Real.sqrt (angEnd ε) * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C
        + η * angKSw * (∫ s in Set.Icc δ R, Work.FTS.GalBasis.cc.Wlam s) := by
  have hδ0 : 0 ≤ δ := hδ.le
  have hR0 : 0 ≤ R := le_trans hδ0 hδR
  have hRpos : 0 < R := lt_of_lt_of_le hδ hδR
  have hε' : ε < Real.pi / 2 := by linarith [hε4, Real.pi_pos]
  have hHnn : ∀ s, 0 ≤ radMarg α D s := radMarg_nonneg α D
  have hHint_Iz : MeasureTheory.IntegrableOn (radMarg α D) Work.Spaces.Iz := hmem.2
  have hHint : MeasureTheory.IntegrableOn (radMarg α D) (Set.Ioi 0) := by
    refine hHint_Iz.mono_set ?_
    intro x hx
    simp only [Work.Spaces.Iz, Set.mem_Ici] at hx ⊢
    exact le_of_lt hx
  have hmass : (∫ s in Set.Ioi 0, radMarg α D s) ≤ C := by
    have h1 : (∫ s in Set.Ioi 0, radMarg α D s) ≤ (∫ s in Work.Spaces.Iz, radMarg α D s) :=
      MeasureTheory.setIntegral_mono_set hHint_Iz (Filter.Eventually.of_forall hHnn)
        (Filter.Eventually.of_forall fun x hx => by
          simp only [Work.Spaces.Iz, Set.mem_Ici] at hx ⊢
          exact le_of_lt hx)
    have h2 : (∫ s in Work.Spaces.Iz, radMarg α D s) = Work.Spaces.HkSq α 0 D :=
      (HkSq_zero_eq α D).symm
    linarith
  have hslice : ∀ s ∈ Set.Ioi 0,
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 D s θ) Work.Spaces.Iθ :=
    fun s hs => hmem.1 s (by
      simp only [Work.Spaces.Iz, Set.mem_Ici]
      exact le_of_lt hs)
  -- the two majorants
  set Crude : ℝ → ℝ :=
    fun s => Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (radMarg α D s))
    with hCrude
  set Fine : ℝ → ℝ :=
    fun s => (η * angKSw) * Work.FTS.GalBasis.cc.Wlam s
      + Real.sqrt (angEnd ε) * (Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (radMarg α D s))
    with hFine
  set G : ℝ → ℝ := fun s => if s ∈ Set.Icc δ R then Fine s else Crude s with hG
  -- pointwise bounds on the density
  have hcrude_pt : ∀ s ∈ Set.Ioi 0, |Work.Construction.L12dens D s| ≤ Crude s := by
    intro s hs
    have hb := abs_L12dens_le_zero α D hs (hslice s hs)
    calc |Work.Construction.L12dens D s|
        ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * Real.sqrt (radMarg α D s)) := by
          simpa only [radMarg] using hb
      _ = Crude s := by rw [hCrude]; ring
  have hfine_pt : ∀ s ∈ Set.Icc δ R, |Work.Construction.L12dens D s| ≤ Fine s := by
    intro s hs
    have hs' : 0 < s := lt_of_lt_of_le hδ hs.1
    have hb := DensSplit (α := α) (h := D) (s := s) (ε := ε) (S := η) hs' hε hε'
      (hslice s hs') hη (fun θ hθ => hbox s hs θ hθ)
    calc |Work.Construction.L12dens D s|
        ≤ Work.FTS.GalBasis.cc.Wlam s *
            (η * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.FTS.GalBasis.cc.Sw θ)
              + Real.sqrt (angEnd ε) * Real.sqrt (radMarg α D s)) := by
          simpa only [angEnd, radMarg] using hb
      _ = Fine s := by rw [hFine]; simp only [angKSw]; ring
  -- integrability of the majorants
  have hCrude_int : MeasureTheory.IntegrableOn Crude (Set.Ioi 0) := by
    rw [hCrude]
    exact (integrableOn_Wlam_mul_sqrt hHnn hHint).const_mul _
  have hFine_int : MeasureTheory.IntegrableOn Fine (Set.Icc δ R) := by
    rw [hFine]
    have hsub : Set.Icc δ R ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le hδ hx.1
    have h1 : MeasureTheory.IntegrableOn
        (fun s => (η * angKSw) * Work.FTS.GalBasis.cc.Wlam s) (Set.Icc δ R) :=
      (ContinuousOn.integrableOn_compact isCompact_Icc (continuousOn_Wlam.mono hsub)).const_mul _
    have h2 : MeasureTheory.IntegrableOn
        (fun s => Real.sqrt (angEnd ε) * (Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (radMarg α D s)))
        (Set.Icc δ R) :=
      ((integrableOn_Wlam_mul_sqrt hHnn hHint).mono_set hsub).const_mul _
    exact h1.add h2
  -- the decomposition of `Ioi 0`
  have hdecomp : Set.Ioi (0 : ℝ) = (Set.Ioo 0 δ ∪ Set.Icc δ R) ∪ Set.Ioi R := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc, Set.mem_union]
    constructor
    · intro hx
      rcases lt_or_ge x δ with h | h
      · exact Or.inl (Or.inl ⟨hx, h⟩)
      · rcases le_or_gt x R with h' | h'
        · exact Or.inl (Or.inr ⟨h, h'⟩)
        · exact Or.inr h'
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | h3)
      · exact h1
      · exact lt_of_lt_of_le hδ h1
      · exact lt_trans hRpos h3

  have hG_int : MeasureTheory.IntegrableOn G (Set.Ioi 0) := by
    have hsub1 : Set.Ioo (0 : ℝ) δ ⊆ Set.Ioi 0 := fun x hx => hx.1
    have hsub3 : Set.Icc δ R ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le hδ hx.1
    have hsub4 : Set.Ioi R ⊆ Set.Ioi 0 := fun x hx => lt_trans hRpos hx
    have h1 : MeasureTheory.IntegrableOn G (Set.Ioo 0 δ) :=
      MeasureTheory.IntegrableOn.congr_fun (hCrude_int.mono_set hsub1)
        (fun s hs => by
          show Crude s = (if s ∈ Set.Icc δ R then Fine s else Crude s)
          rw [if_neg (fun hmem => absurd hmem.1 (not_le.mpr hs.2))])
        measurableSet_Ioo
    have h2 : MeasureTheory.IntegrableOn G (Set.Icc δ R) :=
      MeasureTheory.IntegrableOn.congr_fun hFine_int
        (fun s hs => by
          show Fine s = (if s ∈ Set.Icc δ R then Fine s else Crude s)
          rw [if_pos hs])
        measurableSet_Icc
    have h3 : MeasureTheory.IntegrableOn G (Set.Ioi R) :=
      MeasureTheory.IntegrableOn.congr_fun (hCrude_int.mono_set hsub4)
        (fun s hs => by
          show Crude s = (if s ∈ Set.Icc δ R then Fine s else Crude s)
          rw [if_neg (fun hmem => absurd hmem.2 (not_le.mpr hs))])
        measurableSet_Ioi
    have h123 : MeasureTheory.IntegrableOn G
        ((Set.Ioo (0 : ℝ) δ ∪ Set.Icc δ R) ∪ Set.Ioi R) := (h1.union h2).union h3
    rwa [← hdecomp] at h123
  -- the pointwise bound for `G`
  have hG_pt : ∀ s ∈ Set.Ioi 0, |Work.Construction.L12dens D s| ≤ G s := by
    intro s hs
    show |Work.Construction.L12dens D s|
      ≤ (if s ∈ Set.Icc δ R then Fine s else Crude s)
    by_cases h : s ∈ Set.Icc δ R
    · rw [if_pos h]
      exact hfine_pt s h
    · rw [if_neg h]
      exact hcrude_pt s hs
  have hGnn : ∀ s ∈ Set.Ioi 0, 0 ≤ G s := by
    intro s hs
    show 0 ≤ (if s ∈ Set.Icc δ R then Fine s else Crude s)
    have hWnn : 0 ≤ Work.FTS.GalBasis.cc.Wlam s :=
      Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt hs)
    by_cases h : s ∈ Set.Icc δ R
    · rw [if_pos h]
      show 0 ≤ Fine s
      rw [hFine]
      exact add_nonneg (mul_nonneg (mul_nonneg hη angKSw_nonneg) hWnn)
        (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hWnn (Real.sqrt_nonneg _)))
    · rw [if_neg h]
      show 0 ≤ Crude s
      rw [hCrude]
      exact mul_nonneg Work.FTS.GalBasis.cc.BK_nonneg
        (mul_nonneg hWnn (Real.sqrt_nonneg _))
  -- the three pieces
  have hmassIoo : (∫ s in Set.Ioo 0 δ, radMarg α D s) ≤ C :=
    le_trans (MeasureTheory.setIntegral_mono_set hHint (Filter.Eventually.of_forall hHnn)
      (Filter.Eventually.of_forall fun x hx => hx.1)) hmass
  have hmassIoiR : (∫ s in Set.Ioi R, radMarg α D s) ≤ C :=
    le_trans (MeasureTheory.setIntegral_mono_set hHint (Filter.Eventually.of_forall hHnn)
      (Filter.Eventually.of_forall fun x hx => lt_trans hRpos hx)) hmass
  have hmassIcc : (∫ s in Set.Icc δ R, radMarg α D s) ≤ C :=
    le_trans (MeasureTheory.setIntegral_mono_set hHint (Filter.Eventually.of_forall hHnn)
      (Filter.Eventually.of_forall fun x hx => lt_of_lt_of_le hδ hx.1)) hmass
  have hnear : (∫ s in Set.Ioo 0 δ, Crude s)
      ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (δ ^ 3) := by
    rw [hCrude]
    have hA : Set.Ioo (0 : ℝ) δ ⊆ Set.Ioi 0 := fun s hs => hs.1
    have h1 : (∫ s in Set.Ioo 0 δ, Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (radMarg α D s))
        ≤ Real.sqrt (δ ^ 3) * Real.sqrt C :=
      le_trans (WlamCS hA hHnn (hHint.mono_set hA))
        (mul_le_mul (Real.sqrt_le_sqrt (WlamSqIoo δ hδ0)) (Real.sqrt_le_sqrt hmassIoo)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc ∫ s in Set.Ioo 0 δ,
          Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (radMarg α D s))
        = Work.FTS.GalBasis.cc.BK * ∫ s in Set.Ioo 0 δ,
            Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (radMarg α D s) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Work.FTS.GalBasis.cc.BK * (Real.sqrt (δ ^ 3) * Real.sqrt C) :=
          mul_le_mul_of_nonneg_left h1 Work.FTS.GalBasis.cc.BK_nonneg
      _ = Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (δ ^ 3) := by ring
  have htail : (∫ s in Set.Ioi R, Crude s)
      ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (1 / (1 + R)) := by
    rw [hCrude]
    have hA : Set.Ioi R ⊆ Set.Ioi 0 := fun s hs => lt_trans hRpos hs
    have h1 : (∫ s in Set.Ioi R, Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (radMarg α D s))
        ≤ Real.sqrt (1 / (1 + R)) * Real.sqrt C :=
      le_trans (WlamCS hA hHnn (hHint.mono_set hA))
        (mul_le_mul (Real.sqrt_le_sqrt (WlamSqIoi R hR0)) (Real.sqrt_le_sqrt hmassIoiR)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc ∫ s in Set.Ioi R,
          Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (radMarg α D s))
        = Work.FTS.GalBasis.cc.BK * ∫ s in Set.Ioi R,
            Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (radMarg α D s) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Work.FTS.GalBasis.cc.BK * (Real.sqrt (1 / (1 + R)) * Real.sqrt C) :=
          mul_le_mul_of_nonneg_left h1 Work.FTS.GalBasis.cc.BK_nonneg
      _ = Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (1 / (1 + R)) := by ring
  have hmid : (∫ s in Set.Icc δ R, Fine s)
      ≤ η * angKSw * (∫ s in Set.Icc δ R, Work.FTS.GalBasis.cc.Wlam s)
        + Real.sqrt (angEnd ε) * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C := by
    rw [hFine]
    have hsub : Set.Icc δ R ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le hδ hx.1
    have hint1 : MeasureTheory.IntegrableOn
        (fun s => (η * angKSw) * Work.FTS.GalBasis.cc.Wlam s) (Set.Icc δ R) :=
      (ContinuousOn.integrableOn_compact isCompact_Icc (continuousOn_Wlam.mono hsub)).const_mul _
    have hint2 : MeasureTheory.IntegrableOn
        (fun s => Real.sqrt (angEnd ε) * (Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (radMarg α D s)))
        (Set.Icc δ R) :=
      ((integrableOn_Wlam_mul_sqrt hHnn hHint).mono_set hsub).const_mul _
    rw [MeasureTheory.integral_add hint1 hint2]
    have hfirst : ∫ s in Set.Icc δ R, (η * angKSw) * Work.FTS.GalBasis.cc.Wlam s
        = η * angKSw * (∫ s in Set.Icc δ R, Work.FTS.GalBasis.cc.Wlam s) :=
      MeasureTheory.integral_const_mul _ _
    have hsecond : ∫ s in Set.Icc δ R,
          Real.sqrt (angEnd ε) * (Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (radMarg α D s))
        ≤ Real.sqrt (angEnd ε) * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C := by
      rw [MeasureTheory.integral_const_mul]
      have h2 : (∫ s in Set.Icc δ R, Work.FTS.GalBasis.cc.Wlam s ^ 2)
          ≤ Work.FTS.GalBasis.cc.W2 := by
        simpa only [Work.FTS.GalBasis.cc.W2] using
          (MeasureTheory.setIntegral_mono_set integrableOn_Wlam_sq
            (Filter.Eventually.of_forall fun s => sq_nonneg _)
            (Filter.Eventually.of_forall fun x hx => hsub hx))
      have hinner : (∫ s in Set.Icc δ R, Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (radMarg α D s))
          ≤ Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C :=
        le_trans (WlamCS hsub hHnn (hHint.mono_set hsub))
          (mul_le_mul (Real.sqrt_le_sqrt h2) (Real.sqrt_le_sqrt hmassIcc)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      calc Real.sqrt (angEnd ε) * ∫ s in Set.Icc δ R,
            Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (radMarg α D s)
          ≤ Real.sqrt (angEnd ε) * (Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C) :=
            mul_le_mul_of_nonneg_left hinner (Real.sqrt_nonneg _)
        _ = Real.sqrt (angEnd ε) * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C := by ring
    linarith [hfirst, hsecond]
  have hdisj1 : Disjoint (Set.Ioo (0 : ℝ) δ) (Set.Icc δ R) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx'.1 (not_le.mpr hx.2)
  have hdisj2 : Disjoint (Set.Ioo (0 : ℝ) δ ∪ Set.Icc δ R) (Set.Ioi R) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases hx with h | h
    · exact absurd hx' (not_lt.mpr (le_trans (le_of_lt h.2) hδR))
    · exact absurd hx' (not_lt.mpr h.2)
  have hG_add : (∫ s in Set.Ioi 0, G s)
      = (∫ s in Set.Ioo 0 δ, G s) + (∫ s in Set.Icc δ R, G s) + (∫ s in Set.Ioi R, G s) := by
    have hsub1 : Set.Ioo (0 : ℝ) δ ⊆ Set.Ioi 0 := fun x hx => hx.1
    have hsub2 : Set.Ioo (0 : ℝ) δ ∪ Set.Icc δ R ⊆ Set.Ioi 0 := by
      intro x hx
      rcases hx with h | h
      · exact h.1
      · exact lt_of_lt_of_le hδ h.1
    have hsub3 : Set.Icc δ R ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le hδ hx.1
    have hsub4 : Set.Ioi R ⊆ Set.Ioi 0 := fun x hx => lt_trans hRpos hx
    rw [hdecomp,
      MeasureTheory.setIntegral_union hdisj2 measurableSet_Ioi
        (hG_int.mono_set hsub2) (hG_int.mono_set hsub4),
      MeasureTheory.setIntegral_union hdisj1 measurableSet_Icc
        (hG_int.mono_set hsub1) (hG_int.mono_set hsub3)]

  have hG_crude1 : (∫ s in Set.Ioo 0 δ, G s) = (∫ s in Set.Ioo 0 δ, Crude s) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    show (if s ∈ Set.Icc δ R then Fine s else Crude s) = Crude s
    rw [if_neg]
    intro hmem
    exact absurd hmem.1 (not_le.mpr hs.2)
  have hG_crude2 : (∫ s in Set.Ioi R, G s) = (∫ s in Set.Ioi R, Crude s) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    show (if s ∈ Set.Icc δ R then Fine s else Crude s) = Crude s
    rw [if_neg]
    intro hmem
    exact absurd hmem.2 (not_le.mpr hs)
  have hG_fine : (∫ s in Set.Icc δ R, G s) = (∫ s in Set.Icc δ R, Fine s) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    show (if s ∈ Set.Icc δ R then Fine s else Crude s) = Fine s
    rw [if_pos hs]
  have hstep1 : ‖Work.Construction.L12 D z‖
      ≤ (∫ s in Set.Ioi z, |Work.Construction.L12dens D s|) := by
    have h : Work.Construction.L12 D z
        = ∫ s in Set.Ioi z, Work.Construction.L12dens D s := rfl
    rw [h]
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi z))
        (f := fun s => Work.Construction.L12dens D s))
  have hstep2 : (∫ s in Set.Ioi z, |Work.Construction.L12dens D s|) ≤ (∫ s in Set.Ioi z, G s) := by
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (hG_int.mono_set (fun x hx => lt_of_le_of_lt hz hx)) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact hG_pt s (lt_of_le_of_lt hz hs)
  have hstep3 : (∫ s in Set.Ioi z, G s) ≤ (∫ s in Set.Ioi 0, G s) := by
    refine MeasureTheory.setIntegral_mono_set hG_int ?_ ?_
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with x hx
      exact hGnn x hx
    · filter_upwards with x hx
      exact lt_of_le_of_lt hz hx
  have hchain : ‖Work.Construction.L12 D z‖ ≤ (∫ s in Set.Ioi 0, G s) :=
    le_trans hstep1 (le_trans hstep2 hstep3)
  have hsplit : (∫ s in Set.Ioi 0, G s)
      = (∫ s in Set.Ioo 0 δ, Crude s) + (∫ s in Set.Icc δ R, Fine s)
        + (∫ s in Set.Ioi R, Crude s) := by
    rw [hG_add, hG_crude1, hG_crude2, hG_fine]
  have hpieces : (∫ s in Set.Ioo 0 δ, Crude s) + (∫ s in Set.Icc δ R, Fine s)
        + (∫ s in Set.Ioi R, Crude s)
      ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (δ ^ 3)
        + (η * angKSw * (∫ s in Set.Icc δ R, Work.FTS.GalBasis.cc.Wlam s)
            + Real.sqrt (angEnd ε) * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C)
        + Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (1 / (1 + R)) := by
    linarith [hnear, hmid, htail]
  calc ‖Work.Construction.L12 D z‖
      ≤ (∫ s in Set.Ioi 0, G s) := hchain
    _ = (∫ s in Set.Ioo 0 δ, Crude s) + (∫ s in Set.Icc δ R, Fine s)
        + (∫ s in Set.Ioi R, Crude s) := hsplit
    _ ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (δ ^ 3)
        + (η * angKSw * (∫ s in Set.Icc δ R, Work.FTS.GalBasis.cc.Wlam s)
            + Real.sqrt (angEnd ε) * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C)
        + Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (1 / (1 + R)) := hpieces
    _ = Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (δ ^ 3)
        + Work.FTS.GalBasis.cc.BK * Real.sqrt C * Real.sqrt (1 / (1 + R))
        + Real.sqrt (angEnd ε) * Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt C
        + η * angKSw * (∫ s in Set.Icc δ R, Work.FTS.GalBasis.cc.Wlam s) := by ring

end Work.FTS.StrongEps.L12
