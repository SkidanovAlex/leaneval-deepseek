import Mathlib
import Submission.Work.Geo.DualStretch.Defs
import Submission.Work.Geo.DualStretch.Basic
import Submission.Work.Geo.DualStretch.massG_api
import Submission.Work.Geo.DualStretch.stretch_defs

/-!
A6 `Geo/DualStretch` — the bookkeeping facts behind the stretch.

`Work.Geo.DualStretch.stretch P hP β p α M` rescales the high part `B(x)` of a point `x ∈ P.space`
by the taper `taperM β p P hP α M x` and renormalises by `denOf β p P hP α M x`.  This file records
everything about the resulting *mass decomposition* that the inverse law and the relations of the
stretch use:

* the taper is positive, and `SOf` (the total high mass) lies in `[0,1]`;
* consequently the renormalisation factor `denOf` is positive;
* the level sets of positive mass `posCands P hP x` form a nonempty chain of faces of `P`, on which
  the rescaled weights `wtOf β p P hP α M x` are positive and sum to `1`;
* the stretched point is the corresponding convex combination of the barycentres of these level
  sets, hence lies in `P.space`.

The substance is the renormalisation identity `denOf = (1 - SOf) + taperM * SOf`, together with
`SOf = ∑_{high τ} massG τ` and `1 - SOf = ∑_{low τ} massG τ`; these convert the sum of the rescaled
weights `wtOf` into `denOf / denOf = 1`.
-/

open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

open _root_.PL (E Cx)

variable {n : ℕ}

theorem stretch_aux {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {β α M : ℝ} (hM : 0 < M) {p : ℕ}
    {x : PL.E n} (hx : x ∈ P.space) :
    (0 < Work.Geo.DualStretch.taperM β p P hP α M x) ∧
      (0 ≤ Work.Geo.DualStretch.SOf β p P hP x) ∧
      (Work.Geo.DualStretch.SOf β p P hP x ≤ 1) ∧
      (0 < Work.Geo.DualStretch.denOf β p P hP α M x) ∧
      (∀ τ ∈ Work.Geo.DualStretch.posCands P hP x, τ ∈ P.faces) ∧
      (Work.Geo.DualStretch.posCands P hP x).Nonempty ∧
      Work.Geo.DualStretch.IsChain (Work.Geo.DualStretch.posCands P hP x) ∧
      (∀ τ ∈ Work.Geo.DualStretch.posCands P hP x,
        0 < Work.Geo.DualStretch.wtOf β p P hP α M x τ) ∧
      (∑ τ ∈ Work.Geo.DualStretch.posCands P hP x,
        Work.Geo.DualStretch.wtOf β p P hP α M x τ = 1) ∧
      (Work.Geo.DualStretch.stretch P hP β p α M x ∈ P.space) ∧
      (Work.Geo.DualStretch.stretch P hP β p α M x =
        ∑ τ ∈ Work.Geo.DualStretch.posCands P hP x,
          Work.Geo.DualStretch.wtOf β p P hP α M x τ • Work.Geo.DualStretch.bary τ) := by
  classical
  obtain ⟨hnn, hsum, -, -, hchain, hfaces⟩ := massG_api P hP hx
  -- membership in `posCands`
  have hpos_mem : ∀ τ, τ ∈ posCands P hP x ↔ τ ∈ cands P hP ∧ 0 < massG P hP x τ := by
    intro τ; rw [posCands, Finset.mem_filter]
  have hsub : posCands P hP x ⊆ cands P hP := Finset.filter_subset _ _
  -- `SOf ∈ [0,1]`
  have hSOf_nonneg : 0 ≤ SOf β p P hP x := by
    rw [SOf]
    exact Finset.sum_nonneg (fun τ _ => by
      by_cases h : LowFace β p τ
      · simp [h]
      · simp only [h, ite_false]; rw [massG]; exact le_max_left _ _)
  have hSOf_le_one : SOf β p P hP x ≤ 1 := by
    rw [SOf]
    calc ∑ τ ∈ cands P hP, (if LowFace β p τ then 0 else massG P hP x τ)
        ≤ ∑ τ ∈ cands P hP, massG P hP x τ :=
          Finset.sum_le_sum (fun τ hτ => by
            by_cases h : LowFace β p τ
            · simp [h]; exact hnn τ hτ
            · simp [h])
      _ = 1 := hsum
  -- positivity of the renormalisation factor
  have hden_pos : 0 < denOf β p P hP α M x := by
    have htaper : 0 < taperM β p P hP α M x := taperM_pos hM p P hP x
    rw [denOf]
    by_cases h1M : 1 ≤ taperM β p P hP α M x
    · have hprod : 0 ≤ (taperM β p P hP α M x - 1) * SOf β p P hP x :=
        mul_nonneg (by linarith) hSOf_nonneg
      linarith
    · push Not at h1M
      have hle : taperM β p P hP α M x - 1 ≤ (taperM β p P hP α M x - 1) * SOf β p P hP x := by
        nlinarith [hSOf_nonneg, hSOf_le_one, h1M]
      linarith
  -- `posCands` is nonempty
  have hne_pos : (posCands P hP x).Nonempty := by
    have hex : ∃ τ ∈ cands P hP, 0 < massG P hP x τ := by
      by_contra hc
      push Not at hc
      have h0 : ∑ τ ∈ cands P hP, massG P hP x τ = 0 :=
        Finset.sum_eq_zero (fun τ hτ => le_antisymm (hc τ hτ) (hnn τ hτ))
      rw [h0] at hsum; norm_num at hsum
    obtain ⟨τ, hτ, hpos⟩ := hex
    exact ⟨τ, (hpos_mem τ).mpr ⟨hτ, hpos⟩⟩
  -- `posCands` is a chain of faces
  have hchain_pos : IsChain (posCands P hP x) := by
    intro σ hσ τ hτ
    exact hchain σ ((hpos_mem σ).mp hσ).1 τ ((hpos_mem τ).mp hτ).1
      ((hpos_mem σ).mp hσ).2 ((hpos_mem τ).mp hτ).2
  -- positivity of the rescaled weights
  have hwt_pos : ∀ τ ∈ posCands P hP x, 0 < wtOf β p P hP α M x τ := by
    intro τ hτ
    rw [wtOf]
    refine mul_pos ?_ ((hpos_mem τ).mp hτ).2
    by_cases h : LowFace β p τ
    · simp only [h, ite_true]; exact inv_pos.mpr hden_pos
    · simp only [h, ite_false]
      exact mul_pos (taperM_pos hM p P hP x) (inv_pos.mpr hden_pos)
  -- the two mass sums over `cands`
  have hhigh : (∑ τ ∈ cands P hP with ¬ LowFace β p τ, massG P hP x τ) = SOf β p P hP x := by
    rw [SOf, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    by_cases h : LowFace β p τ <;> simp [h]
  have hlowhigh : (∑ τ ∈ cands P hP with LowFace β p τ, massG P hP x τ)
      + (∑ τ ∈ cands P hP with ¬ LowFace β p τ, massG P hP x τ) = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not, hsum]
  have hlow : (∑ τ ∈ cands P hP with LowFace β p τ, massG P hP x τ) = 1 - SOf β p P hP x := by
    linarith
  -- the combined coefficient sum is `denOf`
  have hgd : (∑ τ ∈ cands P hP,
        (if LowFace β p τ then (1:ℝ) else taperM β p P hP α M x) * massG P hP x τ)
      = denOf β p P hP α M x := by
    have step1 : (∑ τ ∈ cands P hP,
          (if LowFace β p τ then (1:ℝ) else taperM β p P hP α M x) * massG P hP x τ)
        = ∑ τ ∈ cands P hP, (if LowFace β p τ then (1:ℝ) * massG P hP x τ
            else taperM β p P hP α M x * massG P hP x τ) := by
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      by_cases h : LowFace β p τ <;> simp [h]
    rw [step1, Finset.sum_ite]
    simp only [one_mul]
    rw [← Finset.mul_sum, hlow, hhigh, denOf]
    ring
  -- `wtOf` as `d⁻¹` times the combined coefficient
  have hwt_eq : ∀ τ, wtOf β p P hP α M x τ
      = (denOf β p P hP α M x)⁻¹ *
        ((if LowFace β p τ then (1:ℝ) else taperM β p P hP α M x) * massG P hP x τ) := by
    intro τ
    rw [wtOf]
    by_cases h : LowFace β p τ
    · simp only [h, ite_true]; ring
    · simp only [h, ite_false]; ring
  have hwt_zero : ∀ τ ∈ cands P hP, τ ∉ posCands P hP x → wtOf β p P hP α M x τ = 0 := by
    intro τ hτ hτnot
    have hz : massG P hP x τ = 0 :=
      le_antisymm (not_lt.mp (fun hp => hτnot (Finset.mem_filter.mpr ⟨hτ, hp⟩))) (hnn τ hτ)
    rw [wtOf, hz, mul_zero]
  -- the rescaled weights sum to `1`
  have hsum_wt : ∑ τ ∈ posCands P hP x, wtOf β p P hP α M x τ = 1 := by
    refine (Finset.sum_subset hsub hwt_zero).trans ?_
    rw [Finset.sum_congr rfl (fun τ (_ : τ ∈ cands P hP) => hwt_eq τ)]
    rw [← Finset.mul_sum, hgd, inv_mul_cancel₀ (ne_of_gt hden_pos)]
  -- the stretch is the corresponding convex combination
  have hrepr : stretch P hP β p α M x
      = ∑ τ ∈ posCands P hP x, wtOf β p P hP α M x τ • bary τ := by
    have hAB : AOf β p P hP x + taperM β p P hP α M x • BOf β p P hP x
        = ∑ τ ∈ cands P hP,
          ((if LowFace β p τ then (1:ℝ) else taperM β p P hP α M x) * massG P hP x τ) •
            bary τ := by
      have hBs : taperM β p P hP α M x • BOf β p P hP x
          = ∑ τ ∈ cands P hP,
            (if LowFace β p τ then (0 : PL.E n)
              else taperM β p P hP α M x • (massG P hP x τ • bary τ)) := by
        rw [BOf, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        by_cases h : LowFace β p τ <;> simp [h]
      rw [AOf, hBs, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      by_cases h : LowFace β p τ
      · simp only [h, ite_true]; rw [add_zero, one_mul]
      · simp only [h, ite_false]; rw [zero_add, smul_smul]
    rw [stretch_unfold P hP hx, hAB, Finset.smul_sum]
    have hstep : (∑ τ ∈ cands P hP,
          (denOf β p P hP α M x)⁻¹ •
            (((if LowFace β p τ then (1:ℝ) else taperM β p P hP α M x) * massG P hP x τ) •
              bary τ))
        = ∑ τ ∈ cands P hP, wtOf β p P hP α M x τ • bary τ :=
      Finset.sum_congr rfl (fun τ _ => by rw [smul_smul, hwt_eq τ])
    rw [hstep]
    exact (Finset.sum_subset hsub (fun τ hτ hτnot => by
      rw [hwt_zero τ hτ hτnot, zero_smul])).symm
  -- the stretched point lies in `P.space`
  have hmem : stretch P hP β p α M x ∈ P.space := by
    obtain ⟨τhi, hτhi, hmax⟩ :=
      Finset.exists_max_image (posCands P hP x) (fun τ => τ.card) hne_pos
    have hτhi_faces : τhi ∈ P.faces := hfaces τhi ((hpos_mem τhi).mp hτhi).2
    have hsubτ : ∀ τ ∈ posCands P hP x, τ ⊆ τhi := by
      intro τ hτ
      rcases hchain τ ((hpos_mem τ).mp hτ).1 τhi ((hpos_mem τhi).mp hτhi).1
        ((hpos_mem τ).mp hτ).2 ((hpos_mem τhi).mp hτhi).2 with h | h
      · exact h
      · have heq : τhi = τ := Finset.eq_of_subset_of_card_le h (hmax τ hτ)
        rw [heq]
    have hconv : Convex ℝ (PL.simp τhi) := by rw [PL.simp]; exact convex_convexHull ℝ _
    have hpt : (∑ τ ∈ posCands P hP x, wtOf β p P hP α M x τ • bary τ) ∈ PL.simp τhi :=
      Convex.sum_mem hconv (fun τ hτ => le_of_lt (hwt_pos τ hτ)) hsum_wt
        (fun τ hτ => simp_mono (hsubτ τ hτ)
          (bary_mem_simp (Geometry.SimplicialComplex.nonempty_of_mem_faces
            (hfaces τ ((hpos_mem τ).mp hτ).2))))
    rw [hrepr]
    exact Geometry.SimplicialComplex.convexHull_subset_space hτhi_faces hpt
  exact ⟨taperM_pos hM p P hP x, hSOf_nonneg, hSOf_le_one, hden_pos,
    (fun τ hτ => hfaces τ ((hpos_mem τ).mp hτ).2), hne_pos, hchain_pos, hwt_pos,
    hsum_wt, hmem, hrepr⟩

end Work.Geo.DualStretch
