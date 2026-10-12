import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Sector.boxFormB_eq_zero_of_eq_zero_on_abox
import Submission.Work.BoseKinLoc.Sector.boxForm_fibre_sum_of_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.boxForm_fibreSumA_of_integrable`

**The sector (fibre) decomposition of the localised box form, translated support, equality form.**
For a smooth state `Ψ` supported in the *translated* box `c + abox N L`, with integrable
whole-space potential integrand, the anchored box form is the sum over the slot sets `S` of the
box-restricted forms of the fibre states, the outside configurations ranging over the translated
ambient box `c + acube (max L ℓ)`:

    `boxForm N v g ℓ μ d s εT b 0 Ψ = fibreSumA v g ℓ μ d s εT b (c + acube (max L ℓ)) Ψ`.

## Route

The proof **reduces the translated geometry to the anchored one** by enlarging the support box:
choose a box `L'` so large that it contains both the translated support box `c + acube L` and the
translated ambient box `c + acube (max L ℓ)` (e.g. `L' := 2‖c‖ + |max L ℓ| + |L| + 1`).  Then

* `tsupport Ψ ⊆ abox N L'` (the translated support box sits in the big cube), so the *proved*
  anchored decomposition `boxForm_fibre_sum_of_integrable` applies verbatim, with the outside
  region `acube (max L' ℓ) ∩ (acube ℓ)ᶜ`;
* the target's region `(c + acube (max L ℓ)) ∩ (acube ℓ)ᶜ` is contained in it, and the `S`-th
  outside integrand `y ↦ boxFormB |S| … (fibState S Ψ y)` vanishes off the target region: if some
  outside slot `y j` lies outside `c + acube (max L ℓ) ⊇ c + acube L`, then the fibre state
  `fibState S Ψ y` is identically zero (every reassembled configuration carries the coordinate
  `y j ∉ c + acube L`, where `Ψ` vanishes), and `boxFormB` of the zero state is `0`
  (`boxFormB_eq_zero_of_eq_zero_on_abox`).

Each summand is therefore the same integral over the two regions
(`setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`), and summing over `S` gives the claim.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

variable {N : ℕ}

/-! ## Elementary geometry of the translated boxes -/

/-- `acube L ⊆ acube (max L ℓ)`, for arbitrary signs (the two intervals only widen). -/
private lemma acube_subset_acube_max_gen (L ℓ : ℝ) :
    Submission.BoseGases.acube L ⊆ Submission.BoseGases.acube (max L ℓ) := by
  intro y hy m
  obtain ⟨h1, h2⟩ := Set.mem_Icc.mp ((Submission.BoseGases.mem_acube_iff L y).mp hy m)
  exact Set.mem_Icc.mpr
    ⟨by linarith [h1, le_max_left L ℓ], by linarith [h2, le_max_left L ℓ]⟩

/-- If `L'` dominates `2‖c‖ + |r|` then the translated cube `c + acube r` sits inside
`acube L'`. -/
private lemma image_acube_subset {c : ℝ³} {r L' : ℝ} (h : 2 * ‖c‖ + |r| ≤ L') :
    (fun z : ℝ³ => c + z) '' Submission.BoseGases.acube r ⊆ Submission.BoseGases.acube L' := by
  rintro y ⟨w, hw, rfl⟩
  rw [Submission.BoseGases.mem_acube_iff] at hw ⊢
  intro k
  obtain ⟨h1, h2⟩ := Set.mem_Icc.mp (hw k)
  have hcw : (c + w).ofLp k = c.ofLp k + w.ofLp k := by simp
  have hck : |c.ofLp k| ≤ ‖c‖ := by
    simpa using PiLp.norm_apply_le (p := (2 : ENNReal)) c k
  rw [Set.mem_Icc, hcw]
  constructor <;>
    linarith [abs_nonneg (c.ofLp k), neg_abs_le (c.ofLp k), le_abs_self (c.ofLp k), hck,
      neg_abs_le r, le_abs_self r, h1, h2, h]

/-- Membership in the diagonal translate of a configuration box: a configuration of `X N` lies in
the translate of `abox N L` iff each of its coordinates lies in the translate of `acube L`. -/
private lemma mem_image_abox_iff (c : ℝ³) (L : ℝ) (x : Submission.BoseGases.X N) :
    x ∈ (fun w : Submission.BoseGases.X N => fun i : Fin N => c + w i) ''
        Submission.BoseGases.abox N L
      ↔ ∀ i : Fin N, x i ∈ (fun z : ℝ³ => c + z) '' Submission.BoseGases.acube L := by
  constructor
  · rintro ⟨w, hw, rfl⟩ i
    exact ⟨w i, hw i, rfl⟩
  · intro h
    refine ⟨fun i => Classical.choose (h i), fun i => (Classical.choose_spec (h i)).1, ?_⟩
    funext i
    exact (Classical.choose_spec (h i)).2

/-! ## The theorem -/

theorem boxForm_fibreSumA_of_integrable {N : ℕ} {v g : ℝ³ → ℝ} {ℓ L μ d s εT b : ℝ}
    (hℓ : 0 < ℓ) {c : ℝ³} {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ (fun x : Submission.BoseGases.X N => fun i : Fin N => c + x i) ''
        Submission.BoseGases.abox N L)
    (hint : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N =>
      (Ψ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ (0 : ℝ³) x)) :
    Work.BoseKinLoc.boxForm N v g ℓ μ d s εT b 0 Ψ
      = Work.BoseKinLoc.Sector.fibreSumA v g ℓ μ d s εT b
          ((fun z : ℝ³ => c + z) '' Submission.BoseGases.acube (max L ℓ)) Ψ := by
  classical
  -- ## The big box `L'`
  set L' : ℝ := 2 * ‖c‖ + |max L ℓ| + |L| + 1 with hL'def
  have hL'0 : 0 ≤ L' := by
    rw [hL'def]
    linarith [norm_nonneg c, abs_nonneg (max L ℓ), abs_nonneg L]
  have hL'ge : L' ≤ max L' ℓ := le_max_left _ _
  -- the two translated cubes sit inside `acube L'`
  have hsub₁ : (fun z : ℝ³ => c + z) '' Submission.BoseGases.acube L
      ⊆ Submission.BoseGases.acube L' := by
    refine image_acube_subset ?_
    rw [hL'def]
    linarith [norm_nonneg c, abs_nonneg (max L ℓ)]
  have hsub₂ : (fun z : ℝ³ => c + z) '' Submission.BoseGases.acube (max L ℓ)
      ⊆ Submission.BoseGases.acube L' := by
    refine image_acube_subset ?_
    rw [hL'def]
    linarith [norm_nonneg c, abs_nonneg L]
  -- ## The support hypothesis for the big box
  have hsupp' : tsupport Ψ ⊆ Submission.BoseGases.abox N L' := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hsupp hx
    intro i
    exact hsub₁ ⟨w i, hw i, rfl⟩
  -- ## The anchored sector decomposition at the big box
  have hmain := boxForm_fibre_sum_of_integrable (N := N) (v := v) (g := g) (ℓ := ℓ) (L := L')
    (μ := μ) (d := d) (s := s) (εT := εT) (b := b) hℓ hΨ hsupp' hint
  -- ## `Ψ` vanishes off the translated support box
  have hPsi0 : ∀ w : Submission.BoseGases.X N,
      w ∉ (fun x : Submission.BoseGases.X N => fun i : Fin N => c + x i) ''
        Submission.BoseGases.abox N L → Ψ w = 0 := by
    intro w hw
    by_contra hne
    exact hw (hsupp (subset_tsupport Ψ (Function.mem_support.mpr hne)))
  -- ## The target region sits in the anchored one
  have hA : (fun z : ℝ³ => c + z) '' Submission.BoseGases.acube (max L ℓ)
      ⊆ Submission.BoseGases.acube (max L' ℓ) :=
    subset_trans hsub₂ (Submission.BoseGases.acube_mono hL'0 hL'ge)
  rw [hmain]
  simp only [fibreSum, fibreSumA, Work.PerSector.slotOutside]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero ?_ ?_ ?_
  · exact Work.PerSector.Work.PerSector.slotBox_measurable
      ((Submission.BoseGases.acube_measurable (max L' ℓ)).inter
        (Submission.BoseGases.acube_measurable ℓ).compl)
  · intro y hy
    rw [Work.PerSector.mem_slotBox_iff] at hy ⊢
    exact fun j => ⟨hA (hy j).1, (hy j).2⟩
  · -- the integrand vanishes on the part of the anchored region that the target region misses
    intro y hy
    obtain ⟨hyt, hys⟩ := hy
    rw [Work.PerSector.mem_slotBox_iff] at hyt
    have hnot : ∃ j : Work.PerSector.SlotOut N S,
        y j ∉ (fun z : ℝ³ => c + z) '' Submission.BoseGases.acube (max L ℓ) := by
      by_contra hcon
      refine hys ((Work.PerSector.mem_slotBox_iff).mpr (fun j => ⟨?_, (hyt j).2⟩))
      exact not_not.mp (not_exists.mp hcon j)
    obtain ⟨j, hj⟩ := hnot
    -- some outside coordinate of the fibre is outside the translated support box,
    -- hence the fibre state vanishes identically
    have hfib0 : fibState S Ψ y = 0 := by
      funext x
      rw [fibState_apply]
      refine hPsi0 _ ?_
      rw [mem_image_abox_iff]
      intro hmem
      have hcoord : (Work.PerSector.slotComb S
            (fun i : Work.PerSector.SlotIn N S => x (slotIso S i)) y) j.1 = y j := by
        rw [Work.PerSector.slotComb_apply, dif_neg j.2]
      have h1 : y j ∈ (fun z : ℝ³ => c + z) '' Submission.BoseGases.acube L := by
        rw [← hcoord]
        exact hmem j.1
      exact hj (Set.image_mono (acube_subset_acube_max_gen L ℓ) h1)
    -- and `boxFormB` of the zero state is zero
    exact boxFormB_eq_zero_of_eq_zero_on_abox (m := S.card) (v := v) (g := g) (ℓ := ℓ)
      (μ := μ) (d := d) (s := s) (εT := εT) (b := b) hℓ (fun x _ => congrFun hfib0 x)

end Work.BoseKinLoc.Sector
