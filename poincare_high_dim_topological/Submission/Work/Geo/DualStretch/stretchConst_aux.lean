import Mathlib
import Submission.Work.Geo.DualStretch.const_defs
import Submission.Work.Geo.DualStretch.stretch_defs
import Submission.Work.Geo.DualStretch.massG_api
import Submission.Work.Geo.DualStretch.Basic

/-!
A6 `Geo/DualStretch` — the bookkeeping facts behind the *constant factor* stretch.

This is the constant-`m` analogue of `stretch_aux`: for the stretch
`stretchM β p P hP (fun _ => m)` (rescaling the high mass by the constant `m > 0`) we record that

* the renormalisation factor `denC β p P hP m x` is positive;
* the level sets of positive mass `posCands P hP x` form a nonempty chain of faces of `P`, on which
  the rescaled weights `wtC β p P hP m x` are positive and sum to `1`;
* the stretched point is the corresponding convex combination of the barycentres of these level
  sets, hence lies in `P.space`.

The substance is, as in `stretch_aux`, the renormalisation identity
`denC = (1 - SOf) + m * SOf`, together with `SOf = ∑_{high τ} massG τ` and
`1 - SOf = ∑_{low τ} massG τ`.
-/

open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

open _root_.PL (E Cx)

variable {n : ℕ}

theorem stretchConst_aux {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {β : ℝ} {p : ℕ} {m : ℝ}
    (hm : 0 < m) {x : PL.E n} (hx : x ∈ P.space) {y : PL.E n}
    (hy : y = Work.Geo.DualStretch.stretchM β p P hP (fun _ => m) x) :
    0 < Work.Geo.DualStretch.denC β p P hP m x ∧
    (∀ τ ∈ Work.Geo.DualStretch.posCands P hP x, τ ∈ P.faces) ∧
    (Work.Geo.DualStretch.posCands P hP x).Nonempty ∧
    Work.Geo.DualStretch.IsChain (Work.Geo.DualStretch.posCands P hP x) ∧
    (∀ τ ∈ Work.Geo.DualStretch.posCands P hP x,
      0 < Work.Geo.DualStretch.wtC β p P hP m x τ) ∧
    (∑ τ ∈ Work.Geo.DualStretch.posCands P hP x, Work.Geo.DualStretch.wtC β p P hP m x τ = 1) ∧
    (y ∈ P.space) ∧
    (y = ∑ τ ∈ Work.Geo.DualStretch.posCands P hP x,
      Work.Geo.DualStretch.wtC β p P hP m x τ • Work.Geo.DualStretch.bary τ) := by
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
  -- positivity of the renormalisation factor `denC = (1 - SOf) + m * SOf`
  have hden_pos : 0 < denC β p P hP m x := by
    rw [denC]
    by_cases hm1 : 1 ≤ m
    · have hprod : 0 ≤ (m - 1) * SOf β p P hP x := mul_nonneg (by linarith) hSOf_nonneg
      linarith
    · push Not at hm1
      have hle : m - 1 ≤ (m - 1) * SOf β p P hP x := by
        simpa using mul_le_mul_of_nonpos_left hSOf_le_one (by linarith : m - 1 ≤ 0)
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
  -- `wtC` written in terms of the combined coefficient
  have hwt_eq : ∀ τ, wtC β p P hP m x τ
      = (1 + (m - 1) * SOf β p P hP x)⁻¹ *
        ((if LowFace β p τ then (1:ℝ) else m) * massG P hP x τ) := by
    intro τ
    rw [wtC, denC, div_eq_inv_mul]
  -- positivity of the rescaled weights
  have hwt_pos : ∀ τ ∈ posCands P hP x, 0 < wtC β p P hP m x τ := by
    intro τ hτ
    rw [hwt_eq τ]
    refine mul_pos (inv_pos.mpr hden_pos) (mul_pos ?_ ((hpos_mem τ).mp hτ).2)
    · by_cases h : LowFace β p τ
      · simp only [h, ite_true]; norm_num
      · simp only [h, ite_false]; exact hm
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
  -- the combined coefficient sum is `denC`
  have hgd : (∑ τ ∈ cands P hP,
        (if LowFace β p τ then (1:ℝ) else m) * massG P hP x τ)
      = denC β p P hP m x := by
    have step1 : (∑ τ ∈ cands P hP,
          (if LowFace β p τ then (1:ℝ) else m) * massG P hP x τ)
        = ∑ τ ∈ cands P hP, (if LowFace β p τ then (1:ℝ) * massG P hP x τ
            else m * massG P hP x τ) := by
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      by_cases h : LowFace β p τ <;> simp [h]
    rw [step1, Finset.sum_ite]
    simp only [one_mul]
    rw [← Finset.mul_sum, hlow, hhigh, denC]
    ring
  have hwt_zero : ∀ τ ∈ cands P hP, τ ∉ posCands P hP x → wtC β p P hP m x τ = 0 := by
    intro τ hτ hτnot
    have hz : massG P hP x τ = 0 :=
      le_antisymm (not_lt.mp (fun hp => hτnot (Finset.mem_filter.mpr ⟨hτ, hp⟩))) (hnn τ hτ)
    rw [wtC, hz, mul_zero, zero_div]
  -- the rescaled weights sum to `1`
  have hsum_wt : ∑ τ ∈ posCands P hP x, wtC β p P hP m x τ = 1 := by
    refine (Finset.sum_subset hsub hwt_zero).trans ?_
    rw [Finset.sum_congr rfl (fun τ (_ : τ ∈ cands P hP) => hwt_eq τ)]
    rw [← Finset.mul_sum, hgd]
    exact inv_mul_cancel₀ (ne_of_gt hden_pos)
  -- the stretch is the corresponding convex combination
  have hrepr : stretchM β p P hP (fun _ => m) x
      = ∑ τ ∈ posCands P hP x, wtC β p P hP m x τ • bary τ := by
    have hAB : AOf β p P hP x + m • BOf β p P hP x
        = ∑ τ ∈ cands P hP,
          ((if LowFace β p τ then (1:ℝ) else m) * massG P hP x τ) • bary τ := by
      have hBs : m • BOf β p P hP x
          = ∑ τ ∈ cands P hP,
            (if LowFace β p τ then (0 : PL.E n)
              else m • (massG P hP x τ • bary τ)) := by
        rw [BOf, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        by_cases h : LowFace β p τ <;> simp [h]
      rw [AOf, hBs, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      by_cases h : LowFace β p τ
      · simp only [h, ite_true]; rw [add_zero, one_mul]
      · simp only [h, ite_false]; rw [zero_add, smul_smul]
    rw [stretchM, ite_eq_left hx, hAB, Finset.smul_sum]
    have hstep : (∑ τ ∈ cands P hP,
          (1 + (m - 1) * SOf β p P hP x)⁻¹ •
            (((if LowFace β p τ then (1:ℝ) else m) * massG P hP x τ) • bary τ))
        = ∑ τ ∈ cands P hP, wtC β p P hP m x τ • bary τ :=
      Finset.sum_congr rfl (fun τ _ => by rw [smul_smul, hwt_eq τ])
    rw [hstep]
    exact (Finset.sum_subset hsub (fun τ hτ hτnot => by
      rw [hwt_zero τ hτ hτnot, zero_smul])).symm
  -- the stretched point lies in `P.space`
  have hmem : y ∈ P.space := by
    rw [hy, hrepr]
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
    have hpt : (∑ τ ∈ posCands P hP x, wtC β p P hP m x τ • bary τ) ∈ PL.simp τhi :=
      Convex.sum_mem hconv (fun τ hτ => le_of_lt (hwt_pos τ hτ)) hsum_wt
        (fun τ hτ => simp_mono (hsubτ τ hτ)
          (bary_mem_simp (Geometry.SimplicialComplex.nonempty_of_mem_faces
            (hfaces τ ((hpos_mem τ).mp hτ).2))))
    exact Geometry.SimplicialComplex.convexHull_subset_space hτhi_faces hpt
  exact ⟨hden_pos, (fun τ hτ => hfaces τ ((hpos_mem τ).mp hτ).2), hne_pos, hchain_pos,
    hwt_pos, hsum_wt, hmem, by rw [hy, hrepr]⟩

end Work.Geo.DualStretch
