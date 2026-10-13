/-
# `thMoll_deriv_le` — the `L¹`-bound for the angular mollification of the derivative kernel

The target statement bounds the derived angular mollification

  `∫_ℝ sKerd ε (θ - s) · Qext G w s ds`

of the (doubly odd extension of the) angular slice `G w ·` by `3 M ∫_{Iθ} |Qext G w s|`.

Mathematically: `sKerd ε` is supported in `(-ε, ε)` and bounded by `M`, while `Qext G w` is the
doubly odd extension of the slice.  Because `ε ≤ 1/2` and `-1/4 < θ < π/2 + 1/4`, the whole line
integral only sees arguments `θ - s ∈ (-π/2, π)` of the extension, where

  `Qext G w s = G w s` (for `s ∈ Iθ`), `= -G w (-s)` (for `s < 0`), `= -G w (π - s)` (for `s > π/2`).

The three pieces are moved to `Iθ` by the reflections `s ↦ -s` and `s ↦ π - s` (each preserving
Lebesgue measure); on the image of each piece the support hypothesis `hvan` confines the
integration to a subinterval of `Iθ` where the slice is controlled by `M`, giving one factor `M`
per piece and hence the constant `3`.

The two reflected pieces (the estimate `≤ M ∫_{Iθ} |g|` for the pieces `s < 0` and `s > π/2` after
reflecting them to `Iθ`) are proved as the independent library lemmas `piece_neg_le` and
`piece_pi_le`, imported here; this file contains the elementary facts about `sKerd` (continuity),
the cases of the doubly odd extension, the measure-preserving transports of the two reflected
pieces back to `Iθ`, the integrability bookkeeping and the assembly.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.piece_neg_le
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.piece_pi_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDzAux

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.deprecated false
set_option linter.unusedVariables false

open Work.FTS.EllSol.PkgK5.K5c (Qext Qext_of_mem)

/-! ## Elementary facts about the kernel and the doubly odd extension -/

/-- `sKerd ε = deriv (sKer ε)` is continuous, `sKer ε` being smooth. -/
theorem continuous_sKerd (ε : ℝ) : Continuous (sKerd ε) :=
  (contDiff_sKer ε (n := 2)).continuous_deriv (by norm_num)

/-- Left of the origin the doubly odd extension is the negated reflected datum. -/
theorem Qext_of_neg (G : ℝ → ℝ → ℝ) (w s : ℝ) (hs : s < 0) : Qext G w s = -G w (-s) := by
  rw [Qext, if_neg (fun h => absurd h.1 (not_le.mpr hs)), if_pos hs]

/-- Right of `π/2` the doubly odd extension is the negated reflected datum. -/
theorem Qext_of_pihalf_lt (G : ℝ → ℝ → ℝ) (w s : ℝ) (hs : Real.pi / 2 < s) :
    Qext G w s = -G w (Real.pi - s) := by
  rw [Qext, if_neg (fun h => absurd h.2 (not_le.mpr hs)), if_neg (by linarith [Real.pi_pos])]

/-- The reflection `t ↦ π - t` of the real line, as a homeomorphism. -/
private def piSubHomeo : ℝ ≃ₜ ℝ where
  toFun := fun t => Real.pi - t
  invFun := fun t => Real.pi - t
  left_inv := fun t => by ring
  right_inv := fun t => by ring
  continuous_toFun := continuous_const.sub continuous_id
  continuous_invFun := continuous_const.sub continuous_id

/-! ## The two reflected pieces

The two reflected pieces of the argument are proved as independent library lemmas about a bare
kernel `ρ` supported in `(-ε, ε)` and bounded by `M` (`piece_neg_le`, `piece_pi_le`); they are
imported above.  The remaining work here is the transport of the two reflected pieces back to
`Iθ` and the assembly.
-/

/-! ## The target estimate -/

theorem thMoll_deriv_le {G : ℝ → ℝ → ℝ} {w : ℝ}
    (hQ : ContinuousOn (fun s : ℝ => Work.FTS.EllSol.PkgK5.K5c.Qext G w s)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    {ε M θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hM0 : 0 ≤ M)
    (hM : ∀ x : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd ε x| ≤ M)
    (hvan : ∀ x : ℝ, ε < |x| → Work.FTS.EllSol.EllPkgAux.sKerd ε x = 0)
    (hθ : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4)) :
    |∫ s : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) * Work.FTS.EllSol.PkgK5.K5c.Qext G w s|
      ≤ 3 * M * ∫ s in Work.Spaces.Iθ, |Work.FTS.EllSol.PkgK5.K5c.Qext G w s| := by
  set ρ : ℝ → ℝ := Work.FTS.EllSol.EllPkgAux.sKerd ε with hρ
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun s : ℝ => G w s := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun s : ℝ => |ρ (θ - s)| * |Qext G w s| := ⟨_, rfl⟩
  have hρc : Continuous ρ := by rw [hρ]; exact continuous_sKerd ε
  -- the slice is continuous on `Iθ`
  have hIθ_sub : Work.Spaces.Iθ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩
  have hgB : ContinuousOn g Work.Spaces.Iθ := by
    rw [hg]
    exact (hQ.mono hIθ_sub).congr (fun s hs => (Qext_of_mem G w s hs).symm)
  have hgabsIθ : IntegrableOn (fun s : ℝ => |g s|) Work.Spaces.Iθ :=
    hgB.abs.integrableOn_compact isCompact_Icc
  have hMgabsIθ : IntegrableOn (fun s : ℝ => M * |g s|) Work.Spaces.Iθ :=
    hgabsIθ.const_mul M
  -- ## Step 1: the crude bound by the absolute value
  have hbase : |∫ s : ℝ, ρ (θ - s) * Qext G w s| ≤ ∫ s : ℝ, F s := by
    have h1 := abs_integral_le_integral_abs (μ := volume)
      (f := fun s : ℝ => ρ (θ - s) * Qext G w s)
    have h2 : (∫ s : ℝ, |ρ (θ - s) * Qext G w s|) = ∫ s : ℝ, F s := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
      simp only [hF, abs_mul]
    rwa [h2] at h1
  -- ## The pointwise identifications of `F` on the two reflected pieces
  have hcongrA : EqOn F (fun s : ℝ => |ρ (θ - s)| * |g (-s)|) (Set.Iio (0 : ℝ)) := by
    intro s hs
    have hs' : s < 0 := hs
    simp only [hF, Qext_of_neg G w s hs', abs_neg, hg]
  have hcongrC : EqOn F (fun s : ℝ => |ρ (θ - s)| * |g (Real.pi - s)|) (Set.Ioi (Real.pi / 2)) := by
    intro s hs
    have hs' : Real.pi / 2 < s := hs
    simp only [hF, Qext_of_pihalf_lt G w s hs', abs_neg, hg]
  -- ## Step 2: integrability of `F` on the three pieces
  have hFintB : IntegrableOn F Work.Spaces.Iθ := by
    have hcont1 : ContinuousOn (fun s : ℝ => |ρ (θ - s)| * |g s|) Work.Spaces.Iθ :=
      ((hρc.comp (continuous_const.sub continuous_id)).abs).continuousOn.mul hgB.abs
    have hint1 : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g s|) Work.Spaces.Iθ :=
      hcont1.integrableOn_compact isCompact_Icc
    refine hint1.congr_fun ?_ measurableSet_Icc
    intro s hs
    have h1 := (hF ▸ rfl : F s = |ρ (θ - s)| * |Qext G w s|)
    rw [h1, Qext_of_mem G w s hs, hg]
  have hFintA : IntegrableOn F (Set.Iio (0 : ℝ)) := by
    have hzero : ∀ s ∈ Set.Iic (-3 / 4 : ℝ), |ρ (θ - s)| * |g (-s)| = 0 := by
      intro s hs
      have hs' : s ≤ -3 / 4 := hs
      have hle : ε < |θ - s| := by
        have hpos : 0 < θ - s := by linarith [hθ.1, hs']
        rw [abs_of_pos hpos]
        linarith [hε1, hθ.1, hs']
      rw [hvan _ hle, abs_zero, zero_mul]
    have hInt1 : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g (-s)|) (Set.Iic (-3 / 4 : ℝ)) :=
      (MeasureTheory.integrableOn_zero (μ := (volume : Measure ℝ)) (s := Set.Iic (-3 / 4 : ℝ)) :
        IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Iic (-3 / 4 : ℝ)) volume).congr_fun
        (fun x hx => (hzero x hx).symm) measurableSet_Iic
    have hInt2 : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g (-s)|) (Set.Ioo (-3 / 4 : ℝ) 0) := by
      have hcont : ContinuousOn (fun s : ℝ => |ρ (θ - s)| * |g (-s)|) (Set.Icc (-3 / 4 : ℝ) 0) :=
        ((hρc.comp (continuous_const.sub continuous_id)).abs).continuousOn.mul
          (hgB.comp' continuous_neg.continuousOn
            (fun s hs => ⟨by linarith [hs.2],
              by linarith [hs.1, Real.pi_gt_three]⟩)).abs
      exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
    have hcov : Set.Iic (-3 / 4 : ℝ) ∪ Set.Ioo (-3 / 4 : ℝ) 0 = Set.Iio (0 : ℝ) := by
      ext x
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioo, Set.mem_Iio]
      constructor
      · rintro (h | h)
        · linarith
        · exact h.2
      · intro hx
        by_cases h : x ≤ -3 / 4
        · exact Or.inl h
        · push_neg at h
          exact Or.inr ⟨h, hx⟩
    have hInt : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g (-s)|) (Set.Iio (0 : ℝ)) := by
      rw [← hcov]
      exact hInt1.union hInt2
    exact hInt.congr_fun hcongrA.symm measurableSet_Iio
  have hFintC : IntegrableOn F (Set.Ioi (Real.pi / 2)) := by
    have hzero : ∀ s ∈ Set.Ici (Real.pi / 2 + 3 / 4 : ℝ),
        |ρ (θ - s)| * |g (Real.pi - s)| = 0 := by
      intro s hs
      have hs' : Real.pi / 2 + 3 / 4 ≤ s := hs
      have hle : ε < |θ - s| := by
        have hneg : θ - s < 0 := by linarith [hθ.2, hs']
        rw [abs_of_neg hneg]
        linarith [hε1, hθ.2, hs']
      rw [hvan _ hle, abs_zero, zero_mul]
    have hInt1 : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g (Real.pi - s)|)
        (Set.Ici (Real.pi / 2 + 3 / 4 : ℝ)) :=
      (MeasureTheory.integrableOn_zero (μ := (volume : Measure ℝ))
        (s := Set.Ici (Real.pi / 2 + 3 / 4 : ℝ)) :
        IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ici (Real.pi / 2 + 3 / 4 : ℝ)) volume).congr_fun
        (fun x hx => (hzero x hx).symm) measurableSet_Ici
    have hInt2 : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g (Real.pi - s)|)
        (Set.Ioo (Real.pi / 2 : ℝ) (Real.pi / 2 + 3 / 4)) := by
      have hcont : ContinuousOn (fun s : ℝ => |ρ (θ - s)| * |g (Real.pi - s)|)
          (Set.Icc (Real.pi / 2 : ℝ) (Real.pi / 2 + 3 / 4)) :=
        ((hρc.comp (continuous_const.sub continuous_id)).abs).continuousOn.mul
          (hgB.comp' ((continuous_const.sub continuous_id).continuousOn)
            (fun s hs => by
              show Real.pi - s ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
              refine ⟨?_, ?_⟩
              · have h1 : s ≤ Real.pi / 2 + 3 / 4 := hs.2
                have h2 : (3 / 4 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
                linarith
              · have h1 : Real.pi / 2 ≤ s := hs.1
                linarith)).abs
      exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
    have hcov : Set.Ioo (Real.pi / 2 : ℝ) (Real.pi / 2 + 3 / 4) ∪ Set.Ici (Real.pi / 2 + 3 / 4)
        = Set.Ioi (Real.pi / 2) := by
      ext x
      simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi]
      constructor
      · rintro (h | h)
        · exact h.1
        · linarith
      · intro hx
        rcases lt_or_ge x (Real.pi / 2 + 3 / 4) with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr h
    have hInt : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g (Real.pi - s)|)
        (Set.Ioi (Real.pi / 2)) := by
      rw [← hcov]
      exact hInt2.union hInt1
    exact hInt.congr_fun hcongrC.symm measurableSet_Ioi
  -- ## Step 3: the three bounds
  have hB : (∫ s in Work.Spaces.Iθ, F s) ≤ M * ∫ s in Work.Spaces.Iθ, |g s| := by
    have hcont1 : ContinuousOn (fun s : ℝ => |ρ (θ - s)| * |g s|) Work.Spaces.Iθ :=
      ((hρc.comp (continuous_const.sub continuous_id)).abs).continuousOn.mul hgB.abs
    have hint1 : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g s|) Work.Spaces.Iθ :=
      hcont1.integrableOn_compact isCompact_Icc
    have hcongr : EqOn (fun s : ℝ => |ρ (θ - s)| * |g s|) F Work.Spaces.Iθ := by
      intro s hs
      have h1 : F s = |ρ (θ - s)| * |Qext G w s| := hF ▸ rfl
      rw [h1, Qext_of_mem G w s hs, hg]
    have hle : ∀ s ∈ Work.Spaces.Iθ, F s ≤ M * |g s| := by
      intro s hs
      rw [← hcongr hs]
      exact mul_le_mul_of_nonneg_right (hM (θ - s)) (abs_nonneg _)
    calc (∫ s in Work.Spaces.Iθ, F s)
        ≤ ∫ s in Work.Spaces.Iθ, M * |g s| :=
          setIntegral_mono_on hFintB hMgabsIθ measurableSet_Icc hle
      _ = M * ∫ s in Work.Spaces.Iθ, |g s| := integral_const_mul M _
  have hA : (∫ s in Set.Iio (0 : ℝ), F s) ≤ M * ∫ s in Work.Spaces.Iθ, |g s| := by
    have hnegIoi : Neg.neg '' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by
      ext x
      simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]
      constructor
      · rintro ⟨t, ht, rfl⟩
        linarith
      · intro hx
        exact ⟨-x, by linarith, by ring⟩
    calc (∫ s in Set.Iio (0 : ℝ), F s)
        = ∫ s in Neg.neg '' Set.Ioi (0 : ℝ), F s := by rw [hnegIoi]
      _ = ∫ t in Set.Ioi (0 : ℝ), F (-t) :=
          (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_image_emb
            (Homeomorph.neg ℝ).measurableEmbedding F (Set.Ioi (0 : ℝ))
      _ = ∫ t in Set.Ioi (0 : ℝ), |ρ (θ + t)| * |g t| := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
          have ht' : (0 : ℝ) < t := ht
          have h1 : F (-t) = |ρ (θ - -t)| * |g (- -t)| :=
            hcongrA (show -t ∈ Set.Iio (0 : ℝ) from by simpa using neg_lt_zero.mpr ht')
          simpa using h1
      _ ≤ M * ∫ t in Work.Spaces.Iθ, |g t| :=
          piece_neg_le hρc hε0 hε1 hM0 hM hvan hgB hθ
  have hC : (∫ s in Set.Ioi (Real.pi / 2), F s) ≤ M * ∫ s in Work.Spaces.Iθ, |g s| := by
    have hpiIio : (fun t : ℝ => Real.pi - t) '' Set.Iio (Real.pi / 2) = Set.Ioi (Real.pi / 2) := by
      ext x
      simp only [Set.mem_image, Set.mem_Iio, Set.mem_Ioi]
      constructor
      · rintro ⟨t, ht, rfl⟩
        linarith
      · intro hx
        exact ⟨Real.pi - x, by linarith, by ring⟩
    calc (∫ s in Set.Ioi (Real.pi / 2), F s)
        = ∫ s in (fun t : ℝ => Real.pi - t) '' Set.Iio (Real.pi / 2), F s := by rw [hpiIio]
      _ = ∫ t in Set.Iio (Real.pi / 2), F (Real.pi - t) :=
          (Measure.measurePreserving_sub_left (volume : Measure ℝ) Real.pi).setIntegral_image_emb
            piSubHomeo.measurableEmbedding F (Set.Iio (Real.pi / 2))
      _ = ∫ t in Set.Iio (Real.pi / 2), |ρ (θ + t - Real.pi)| * |g t| := by
          refine setIntegral_congr_fun measurableSet_Iio (fun t ht => ?_)
          have ht' : t < Real.pi / 2 := ht
          have h1 : F (Real.pi - t) = |ρ (θ - (Real.pi - t))| * |g (Real.pi - (Real.pi - t))| :=
            hcongrC (show Real.pi - t ∈ Set.Ioi (Real.pi / 2) from by
              simp only [Set.mem_Ioi]; linarith [ht'])
          rw [show θ - (Real.pi - t) = θ + t - Real.pi by ring,
            show Real.pi - (Real.pi - t) = t by ring] at h1
          exact h1
      _ ≤ M * ∫ t in Work.Spaces.Iθ, |g t| :=
          piece_pi_le hρc hε0 hε1 hM0 hM hvan hgB hθ
  -- ## Step 4: the disjoint cover of `ℝ` and the splitting of the integral
  have hdisjAB : Disjoint (Set.Iio (0 : ℝ)) Work.Spaces.Iθ := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : x < 0 := hx1
    have h2 : (0 : ℝ) ≤ x := hx2.1
    linarith
  have hdisjABC : Disjoint (Set.Iio (0 : ℝ) ∪ Work.Spaces.Iθ) (Set.Ioi (Real.pi / 2)) := by
    rw [Set.disjoint_left]
    intro x hx hx3
    simp only [Set.mem_union, Set.mem_Iio] at hx
    have h3 : Real.pi / 2 < x := hx3
    rcases hx with hx | hx
    · linarith [Real.pi_pos]
    · linarith [hx.2]
  have hcover : Set.Iio (0 : ℝ) ∪ Work.Spaces.Iθ ∪ Set.Ioi (Real.pi / 2) = (Set.univ : Set ℝ) := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      rcases lt_or_ge x 0 with h | h
      · exact Or.inl (Or.inl h)
      · by_cases h2 : x ≤ Real.pi / 2
        · exact Or.inl (Or.inr ⟨h, h2⟩)
        · exact Or.inr (lt_of_not_ge h2)
  have hsplit : (∫ s : ℝ, F s)
      = (∫ s in Set.Iio (0 : ℝ), F s) + (∫ s in Work.Spaces.Iθ, F s)
        + ∫ s in Set.Ioi (Real.pi / 2), F s := by
    rw [← MeasureTheory.setIntegral_univ, ← hcover,
      MeasureTheory.setIntegral_union hdisjABC measurableSet_Ioi (hFintA.union hFintB) hFintC,
      MeasureTheory.setIntegral_union hdisjAB measurableSet_Icc hFintA hFintB]
  -- ## Step 5: assembly
  have hQeq : (∫ s in Work.Spaces.Iθ, |g s|)
      = ∫ s in Work.Spaces.Iθ, |Qext G w s| :=
    setIntegral_congr_fun measurableSet_Icc (fun s hs => by simp only [hg, Qext_of_mem G w s hs])
  calc |∫ s : ℝ, ρ (θ - s) * Qext G w s|
      ≤ ∫ s : ℝ, F s := hbase
    _ ≤ 3 * M * ∫ s in Work.Spaces.Iθ, |Qext G w s| := by
        rw [← hQeq]
        linarith [hsplit, hA, hB, hC]

end Work.FTS.EllSol.EllPkgAux.MollDzAux
