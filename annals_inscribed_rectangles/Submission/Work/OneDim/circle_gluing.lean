import Mathlib
import Submission.Work.OneDim.Defs
import Submission.Work.OneDim.CirclePt
import Submission.Work.OneDim.CirclePtFacts
import Submission.Work.OneDim.SeamTools
import Submission.Work.OneDim.circle_gluing_prereq
import Submission.Work.OneDim.seam_chart_data
import Submission.Work.OneDim.tails_smooth

/-!
# Gluing `ℝ` into a circle: the dimension-one classification at a point

Let `C` be a Hausdorff smooth 1-manifold, `q : C`, and `φ : ℝ → C` an injective local
diffeomorphism whose range is `C \ {q}` and which tends to `q` at both ends.  Then `C` is
diffeomorphic to the circle.

The proof glues the two ends of `φ` at the seam `q`.  Two ingredients are used:

* a *reparametrisation* of `φ` which makes the seam standard: there is a diffeomorphism `Φ` of `ℝ`
  with `Φ t = 1 / κ (φ t)` for `t` in a neighbourhood of both ends, where `κ` is a local
  coordinate at `q` (`Work.OneDim.seam_chart_data`, `Work.OneDim.exists_diffeomorph_tails_smooth`);
* the stereographic parametrisation `spherePt` of the circle
  (`Work.OneDim.spherePt_stereographic`).

The map `G : C → Circle` sending `q` to the point at infinity and `φ t` to `spherePt (Φ t)` is then
a bijective local diffeomorphism, hence a diffeomorphism.
-/

open scoped Manifold ContDiff
open Topology Set Function Filter

namespace Work.OneDim

noncomputable section

/-! ## The inverse of `φ` is a local diffeomorphism away from the seam -/

theorem isLocalDiffeomorphAt_invFun_sd {C : Type*} [TopologicalSpace C]
    [ChartedSpace E1 C] [IsManifold I1 sm C]
    {q : C} {φ : ℝ → C}
    (hinj : Function.Injective φ)
    (hld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) I1 sm φ)
    (hrange : Set.range φ = Set.compl ({q} : Set C)) :
    ∀ y : C, y ≠ q →
      IsLocalDiffeomorphAt I1 (modelWithCornersSelf ℝ ℝ) sm (Function.invFun φ) y := by
  intro y hy
  have hyφ : y ∈ Set.range φ := by
    rw [hrange]
    exact fun hh => hy (Set.mem_singleton_iff.mp hh)
  obtain ⟨t, rfl⟩ := hyφ
  have hloc := (hld t).localInverse_isLocalDiffeomorphAt
  refine isLocalDiffeomorphAt_congr hloc ?_
  refine Filter.eventuallyEq_of_mem
    ((hld t).localInverse_open_source.mem_nhds (hld t).localInverse_mem_source) ?_
  intro y' hy'
  have h1 : φ ((hld t).localInverse y') = y' := (hld t).localInverse_right_inv hy'
  have h3 : φ (Function.invFun φ y') = y' :=
    Function.invFun_eq ⟨(hld t).localInverse y', h1⟩
  exact (hinj (h3.trans h1.symm)).symm

/-! ## The main theorem -/

theorem circle_gluing {C : Type*} [TopologicalSpace C] [ChartedSpace Work.OneDim.E1 C]
    [IsManifold Work.OneDim.I1 Work.OneDim.sm C] [T2Space C] [SecondCountableTopology C]
    {q : C} {φ : ℝ → C}
    (hinj : Function.Injective φ)
    (hld : IsLocalDiffeomorph (modelWithCornersSelf ℝ ℝ) Work.OneDim.I1 Work.OneDim.sm φ)
    (hrange : Set.range φ = Set.compl ({q} : Set C))
    (htop : Filter.Tendsto φ Filter.atTop (nhds q))
    (hbot : Filter.Tendsto φ Filter.atBot (nhds q)) :
    Nonempty (Diffeomorph Work.OneDim.I1 Work.OneDim.I1 Circle C Work.OneDim.sm) := by
  classical
  -- the stereographic facts about the circle
  obtain ⟨hsp_inj, -, hsp_inv, hsp_range, -, hsp_ld, hsp'_ld⟩ := spherePt_stereographic
  -- the seam data
  obtain ⟨κ, T₀, f, g, hκld, hκ0, hκpos, hκneg, hf_eq, hg_eq, hf_sm, hf_deriv, hf_top,
    hg_sm, hg_deriv, hg_bot⟩ := seam_chart_data (C := C) hinj hld hrange htop hbot
  -- the reparametrisation of `ℝ` that makes the seam standard
  obtain ⟨Φ, T, hT, hΦf, hΦg⟩ := exists_diffeomorph_tails_smooth hf_sm hg_sm hf_deriv hg_deriv hf_top hg_bot
  have hcont : Continuous φ := hld.contMDiff.continuous
  have hφ_ne : ∀ t : ℝ, φ t ≠ q := by
    intro t h
    have hmem : q ∈ Set.range φ := ⟨t, h⟩
    rw [hrange] at hmem
    exact hmem (by simp)
  -- ## The map
  set G : C → Circle := fun y => if y = q then Qm else spherePt (Φ (Function.invFun φ y))
    with hGdef
  have hGdef' : ∀ y : C, G y = if y = q then Qm else spherePt (Φ (Function.invFun φ y)) := by
    intro y
    rw [hGdef]
  have hGq : G q = Qm := by rw [hGdef']; simp
  have hGapply : ∀ t : ℝ, G (φ t) = spherePt (Φ t) := by
    intro t
    rw [hGdef', if_neg (hφ_ne t), Function.leftInverse_invFun hinj t]
  -- ## Bijectivity
  have hG_ne : ∀ y : C, y ≠ q → G y ≠ Qm := by
    intro y hy h
    have h2 : spherePt (Φ (Function.invFun φ y)) ∈ ({Qm} : Set Circle)ᶜ := by
      rw [← hsp_range]
      exact ⟨_, rfl⟩
    rw [hGdef', if_neg hy] at h
    exact h2 h
  have hG_inj : Function.Injective G := by
    intro y y' h
    by_cases hy : y = q
    · by_cases hy' : y' = q
      · rw [hy, hy']
      · have hGy : G y = Qm := by rw [hy]; exact hGq
        exact absurd (h.symm.trans hGy) (hG_ne y' hy')
    · by_cases hy' : y' = q
      · have hGy' : G y' = Qm := by rw [hy']; exact hGq
        exact absurd (h.trans hGy') (hG_ne y hy)
      · have h3 : Φ (Function.invFun φ y) = Φ (Function.invFun φ y') :=
          hsp_inj (by
            rw [hGdef', if_neg hy] at h
            rw [hGdef', if_neg hy'] at h
            exact h)
        have h4 : Function.invFun φ y = Function.invFun φ y' := Φ.injective h3
        have h5 : y ∈ Set.range φ := by
          rw [hrange]
          exact fun hh => hy (Set.mem_singleton_iff.mp hh)
        have h6 : y' ∈ Set.range φ := by
          rw [hrange]
          exact fun hh => hy' (Set.mem_singleton_iff.mp hh)
        rw [← Function.invFun_eq h5, ← Function.invFun_eq h6, h4]
  have hG_surj : Function.Surjective G := by
    intro z
    by_cases hz : z = Qm
    · exact ⟨q, by rw [hz]; exact hGq⟩
    · have hz' : z ∈ Set.range spherePt := by
        rw [hsp_range]
        exact fun hh => hz (Set.mem_singleton_iff.mp hh)
      obtain ⟨t, ht⟩ := hz'
      exact ⟨φ (Φ.symm t), by rw [hGapply, Φ.apply_symm_apply, ht]⟩
  -- ## Local diffeomorphism at the seam
  have hneigh : ({y : C | y ∉ φ '' Set.Icc (-T) T}) ∈ 𝓝 q := by
    have hc : IsCompact (φ '' Set.Icc (-T) T) :=
      isCompact_Icc.image_of_continuousOn hcont.continuousOn
    have hq : q ∈ (φ '' Set.Icc (-T) T)ᶜ := fun hmem => by
      obtain ⟨s, -, hs⟩ := hmem
      exact hφ_ne s hs
    exact hc.isClosed.isOpen_compl.mem_nhds hq
  have hG_ld_q : IsLocalDiffeomorphAt I1 I1 sm G q := by
    have hcomp : IsLocalDiffeomorphAt I1 I1 sm (fun y => spherePt' (κ y)) q :=
      IsLocalDiffeomorphAt.comp (K := I1) (P := Circle) hκld (hsp'_ld (κ q))
    refine isLocalDiffeomorphAt_congr hcomp ?_
    refine Filter.eventuallyEq_of_mem hneigh ?_
    intro y hy
    by_cases hyq : y = q
    · change spherePt' (κ y) = G y
      rw [hyq, hκ0, spherePt'_zero, hGq]
    · have hyr : y ∈ Set.range φ := by
        rw [hrange]
        exact fun hh => hyq (Set.mem_singleton_iff.mp hh)
      obtain ⟨t, ht⟩ := hyr
      have ht' : T < t ∨ t < -T := by
        by_contra hcon
        have h1 : t ≤ T := not_lt.mp (not_or.mp hcon).1
        have h2 : -T ≤ t := not_lt.mp (not_or.mp hcon).2
        exact hy ⟨t, Set.mem_Icc.mpr ⟨h2, h1⟩, ht⟩
      rw [← ht]
      change spherePt' (κ (φ t)) = G (φ t)
      rcases ht' with h | h
      · rw [hGapply, hΦf t (le_of_lt h), hf_eq t (le_of_lt (lt_of_le_of_lt hT h))]
        exact (hsp_inv (κ (φ t)) (ne_of_gt (hκpos t (le_of_lt (lt_of_le_of_lt hT h))))).symm
      · have ht₀ : t ≤ -T₀ := le_of_lt (lt_of_lt_of_le h (neg_le_neg hT))
        rw [hGapply, hΦg t (le_of_lt h), hg_eq t ht₀]
        exact (hsp_inv (κ (φ t)) (ne_of_lt (hκneg t ht₀))).symm
  -- ## Local diffeomorphism away from the seam
  have hG_ld_off : ∀ y : C, y ≠ q → IsLocalDiffeomorphAt I1 I1 sm G y := by
    intro y hy
    have hyr : y ∈ Set.range φ := by
      rw [hrange]
      exact fun hh => hy (Set.mem_singleton_iff.mp hh)
    obtain ⟨t, rfl⟩ := hyr
    have h1 : IsLocalDiffeomorphAt I1 (modelWithCornersSelf ℝ ℝ) sm
        (Function.invFun φ) (φ t) :=
      isLocalDiffeomorphAt_invFun_sd hinj hld hrange (φ t) (hφ_ne t)
    have h2 : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) sm
        Φ (Function.invFun φ (φ t)) := Φ.isLocalDiffeomorph (Function.invFun φ (φ t))
    have h3 : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ ℝ) I1 sm spherePt
        (Φ (Function.invFun φ (φ t))) := hsp_ld (Φ (Function.invFun φ (φ t)))
    have hcomp : IsLocalDiffeomorphAt I1 I1 sm
        (fun y => spherePt (Φ (Function.invFun φ y))) (φ t) :=
      IsLocalDiffeomorphAt.comp (K := I1) (P := Circle)
        (IsLocalDiffeomorphAt.comp (K := modelWithCornersSelf ℝ ℝ) (P := ℝ) h1 h2) h3
    refine isLocalDiffeomorphAt_congr hcomp ?_
    refine Filter.eventuallyEq_of_mem ((isOpen_compl_singleton (x := q)).mem_nhds ?_) ?_
    · exact fun hh => hφ_ne t (Set.mem_singleton_iff.mp hh)
    · intro y' hy'
      have hy'q : y' ≠ q := fun hh => hy' (Set.mem_singleton_iff.mpr hh)
      rw [hGdef', if_neg hy'q]
  have hG_ld : IsLocalDiffeomorph I1 I1 sm G := by
    intro y
    by_cases hy : y = q
    · rw [hy]
      exact hG_ld_q
    · exact hG_ld_off y hy
  exact ⟨(IsLocalDiffeomorph.diffeomorphOfBijective hG_ld ⟨hG_inj, hG_surj⟩).symm⟩

end

end Work.OneDim
