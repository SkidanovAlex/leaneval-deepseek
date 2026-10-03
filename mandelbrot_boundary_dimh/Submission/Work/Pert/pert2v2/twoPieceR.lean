import Mathlib
import Submission.Work.Pert.pert2v2.glue_window_bool_wide
import Submission.Work.Pert.pert2v2.RBlockDefs
import Submission.Work.Pert.pert2v2.DRSub
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.Setup

/-!
# `Work.Pert.pert2v2.twoPieceR` — the two-piece return map `R̃_f`: charts, pieces, and the glue

`Submission/Work/Pert/NOTES_pert2v2_session30.md` §6.4.  The lifted return map of `PertData` is the
`T`-saturation of two pieces:

* **low** (heights `y₁' < |Im| < Hband`): the crux's formula
  `RlowPiece f Qp' τ Φp φ m dlow` (`pert2v2.Rlow_phi_pos` gives `φ (Rlow w + l) = f^l (φ w)`);
* **high** (heights `> Hband`): the level-shifted gate return map
  `Work.Pert.retP f Df τ ΨE (Qm Ξabs α ∩ Qp Ξabs α) α` (`pert2v2.retP_phi_shift`).

`glue_window_bool_wide` glues them (the charts have disjoint imaginary-part ranges, so the mixed
compatibility is vacuous and the same-chart one is `R (w+1) = R w + 1`), producing `R`, `DR` with
`DR` = the `ℤ`-saturation of the two charts, hence the three structural fields `DR_open`,
`IsTEquivariantOn R DR` and `DifferentiableOn ℂ R DR` of `PertData` for free.

This file only *performs the glue*; the four remaining fields (`DR_sub`, `R_close`, `R_upper`,
`orbit`) are produced by the pieces listed in §6.4 and are not restated here.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

/-- **The low chart** of the two-piece return map: the window `{|Re| < R1}`, inside the horn
domain and the maximal domain of `φ`, at band heights between `y₁'` and `Hband`. -/
def UlowSet (d : MandelDim.ParabData f₀ D₀) (Dφ : Set ℂ) (R1 y₁' Hband : ℝ) : Set ℂ :=
  {w : ℂ | |w.re| < R1 ∧ w ∈ d.DE ∧ w ∈ Dφ ∧ y₁' < |w.im| ∧ |w.im| < Hband}

/-- **The high chart**: the window `{|Re| < R1}` above `Hband`, restricted to the image of the waist
`Qm Ξabs α ∩ Qp Ξabs α` under the datum-level gate coordinate `ΨE`. -/
def UhighSet (ΨE : ℂ → ℂ) (Ξabs R1 Hband : ℝ) (α : ℂ) : Set ℂ :=
  {w : ℂ | |w.re| < R1 ∧ Hband < |w.im| ∧
    w ∈ ΨE '' (Work.Pert.Qm Ξabs α ∩ Work.Pert.Qp Ξabs α)}

/-- The low piece of the return map: the crux's formula with `k = 0` and the constant `dlow`
(`= cm - cp - 1/α`, the (A.4.2) constant). -/
def RlowOf (f : ℂ → ℂ) (Qp' : Set ℂ) (τ Φp φ : ℂ → ℂ) (m : ℕ) (dlow : ℂ) : ℂ → ℂ :=
  RlowPiece f Qp' τ Φp φ m dlow

/-- The high piece of the return map: the level-shifted gate return map. -/
def RhighOf (f : ℂ → ℂ) (Df : Set ℂ) (τ Φ : ℂ → ℂ) (Ξabs : ℝ) (α : ℂ) : ℂ → ℂ :=
  Work.Pert.retP f Df τ Φ (Work.Pert.Qm Ξabs α ∩ Work.Pert.Qp Ξabs α) α

/-- **The glue step of the two-piece R-block.**  With the two charts open, the two pieces
holomorphic on them and `+1`-equivariant where the step stays inside, the height-disjointness
(`|Im| < Hband` vs `Hband < |Im|`) makes the mixed compatibility vacuous and
`glue_window_bool_wide` produces `R`, `DR` with the three structural `PertData` fields. -/
theorem twoPieceR_exists (d : MandelDim.ParabData f₀ D₀) (Dφ : Set ℂ) {ΨE : ℂ → ℂ}
    {Ξabs R1 y₁' Hband : ℝ} (hR1lo : 1 / 2 < R1) (hR1hi : R1 ≤ 1)
    {α : ℂ} {f : ℂ → ℂ} {Df : Set ℂ} {Qp' : Set ℂ} {τ Φp φ : ℂ → ℂ} {m : ℕ} {dlow : ℂ}
    (hUlow : IsOpen (UlowSet d Dφ R1 y₁' Hband))
    (hRlow : DifferentiableOn ℂ (RlowOf f Qp' τ Φp φ m dlow) (UlowSet d Dφ R1 y₁' Hband))
    (hRlow1 : ∀ w : ℂ, w ∈ UlowSet d Dφ R1 y₁' Hband → w + 1 ∈ UlowSet d Dφ R1 y₁' Hband →
      RlowOf f Qp' τ Φp φ m dlow (w + 1) = RlowOf f Qp' τ Φp φ m dlow w + 1)
    (hUhigh : IsOpen (UhighSet ΨE Ξabs R1 Hband α))
    (hRhigh : DifferentiableOn ℂ (RhighOf f Df τ ΨE Ξabs α) (UhighSet ΨE Ξabs R1 Hband α))
    (hRhigh1 : ∀ w : ℂ, w ∈ UhighSet ΨE Ξabs R1 Hband α →
      w + 1 ∈ UhighSet ΨE Ξabs R1 Hband α →
      RhighOf f Df τ ΨE Ξabs α (w + 1) = RhighOf f Df τ ΨE Ξabs α w + 1) :
    ∃ R : ℂ → ℂ, ∃ DR : Set ℂ, IsOpen DR ∧ MandelDim.IsTEquivariantOn R DR ∧
      DifferentiableOn ℂ R DR ∧
      (∀ w : ℂ, w ∈ UlowSet d Dφ R1 y₁' Hband → R w = RlowOf f Qp' τ Φp φ m dlow w) ∧
      (∀ w : ℂ, w ∈ UhighSet ΨE Ξabs R1 Hband α → R w = RhighOf f Df τ ΨE Ξabs α w) ∧
      DR = ⋃ n : ℤ, (fun w : ℂ => w + (n : ℂ)) ''
        (UlowSet d Dφ R1 y₁' Hband ∪ UhighSet ΨE Ξabs R1 Hband α) :=
  glue_window_bool_wide (x₀ := 0) hR1lo hR1hi hUlow hRlow hRlow1 hUhigh hRhigh hRhigh1
    (fun w hw => ⟨by simpa using hw.1, hw.2.2.2.2⟩)
    (fun w hw => ⟨by simpa using hw.1, hw.2.1⟩)

/-- Monotonicity of the `ℤ`-saturation. -/
theorem iUnion_sat_mono {U V : Set ℂ} (h : U ⊆ V) :
    (⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' U) ⊆
      (⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' V) :=
by
  intro w hw
  simp only [Set.mem_iUnion] at hw ⊢
  obtain ⟨n, hn⟩ := hw
  exact ⟨n, Set.image_mono h hn⟩

-- WARNING (session 30 §9): the height-disjoint charts of `twoPieceR_exists` cannot actually
-- cover `PertData.DR_sub`'s band: an OPEN `Uhigh` inside `{|Im| ≥ Hband}` lies in `{|Im| > Hband}`,
-- so the line `{|Im| = Hband}` is in neither chart and `ℤ`-saturation preserves `|Im|`.  The two
-- charts must OVERLAP and be glued with `Work.Pert.tSat_glue` plus the cross compatibility
-- `pert2v2.Rlow_eq_retOf_level0` (lead's prescription, `NOTES_pert2v2_session30.md` §9.2).  The
-- lemma below is still true as stated, but its `hUhigh` cannot be discharged for an open `Uhigh`;
-- use it only with the overlapping charts of §9.2.
/-- **`DR_sub` for the two-piece return map (height-`≤` variant; see the warning above).**  The `K`-part lies in the low chart (`hK`); every
band point `y₁ ≤ |Im| ≤ Hband` of `d.DE` is a translate of the low chart
(`pert2v2.band_subset_saturation`, with the **closed** height bound so that the level
`|Im| = Hband` — which `glue_window_bool_wide`'s strict chart separation leaves to neither chart —
is covered); every point of the high band `Hband < |Im|` is a translate of the high chart
(`pert2v2.high_subset_saturation`, fed by the window coverage of `Work.Pert.waist_cover_pinned_v2`).
Since `DR` is by construction the saturation of the *union* of the charts, and saturation is
monotone, this gives `PertData.DR_sub`.  (The glue must be applied with threshold `Hband + 1`.) -/
theorem DR_sub_twoPiece {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {Ulow Uhigh DR K : Set ℂ} {Ψ : ℂ → ℂ} {Q : Set ℂ}
    {R1 y₁ y₁' Hband : ℝ}
    (hDR : DR = ⋃ n : ℤ, (fun u : ℂ => u + (n : ℂ)) '' (Ulow ∪ Uhigh))
    (hUhigh : Uhigh = {w : ℂ | |w.re| < 1 ∧ Hband ≤ |w.im| ∧ w ∈ Ψ '' Q})
    (hR1 : 1 / 2 < R1) (hy' : y₁' < y₁)
    (hUlow : ∀ w : ℂ, |w.re| < R1 → w ∈ d.DE → y₁' < |w.im| → |w.im| ≤ Hband → w ∈ Ulow)
    (hK : K ⊆ Ulow) (hKDE : K ∪ {w : ℂ | y₁ ≤ |w.im|} ⊆ d.DE)
    (hcov : ∀ w : ℂ, Hband ≤ |w.im| →
      ∃ n : ℤ, |(w + (n : ℂ)).re| < 1 ∧ w + (n : ℂ) ∈ Ψ '' Q) :
    K ∪ {w : ℂ | y₁ ≤ |w.im|} ⊆ DR := by
  intro w hw
  rcases hw with hwK | hwB
  · rw [hDR]
    simp only [Set.mem_iUnion]
    refine ⟨0, ?_⟩
    simp only [Set.mem_image]
    exact ⟨w, Or.inl (hK hwK), by simp⟩
  · rcases lt_or_ge |w.im| Hband with hlt | hge
    · -- `|Im| < Hband`: the low chart
      have h := band_subset_saturation d hd hR1 hy' hUlow (hKDE (Or.inr hwB)) hwB hlt.le
      simp only [Set.mem_iUnion] at h
      obtain ⟨n, hn⟩ := h
      rw [hDR]
      simp only [Set.mem_iUnion]
      exact ⟨n, Set.image_mono Set.subset_union_left hn⟩
    · -- `Hband ≤ |Im|`: the high chart (closed bound — tiles the band with the low chart)
      have h := high_subset_saturation (w := w) hUhigh (fun u hu => hcov u hu) hge
      simp only [Set.mem_iUnion] at h
      obtain ⟨n, hn⟩ := h
      rw [hDR]
      simp only [Set.mem_iUnion]
      exact ⟨n, Set.image_mono Set.subset_union_right hn⟩

end

end Work.Pert.pert2v2
