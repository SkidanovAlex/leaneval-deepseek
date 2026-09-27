import Mathlib
import Submission.Work.Mostow.geodSetup
import Submission.Work.Mostow.stab_eq_blk
import Submission.Work.Mostow.nearId_blk

/-!
# The Margulis region depends only on the normal coordinate `nrmC`

For an isometry `a` of `ℍ^{1+m}` which fixes the standard geodesic `stdTG 1 m` **pointwise**,
the near-identity property `NearIdAt a · η` at a point `u` depends only on the normal (last `m`)
coordinate `nrmC 1 m u` of `u`.  The reason is that each such `a` is a *block* isometry
`blk 1 m 1 R` (`Work.Mostow.stab_eq_blk`), acting on the Fermi coordinates `(v, W)` by
`(v, W) ↦ (v, R W)`, and that the distance from `fermiW 1 m v W` to the "foot-free" point
`fermiW 1 m v W'` is independent of the foot `v`.

Hence the Margulis region `Work.Mostow.margRegion m Λ η₁` is a union of level sets of `nrmC 1 m`,
which is the statement proved here.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

/-- `cosh (hdist v v) = 1`. -/
private lemma cosh_hdist_self_eq_one {n : ℕ} (v : Submission.Mostow.E n) :
    Real.cosh (Submission.Mostow.hdist v v) = 1 := by
  rw [nib_hdist_self, Real.cosh_zero]

/-- The distance between `fermiW 1 m v W` and `fermiW 1 m v W'` does not depend on the foot `v`. -/
lemma hdist_fermiW_foot_indep (m : ℕ) (v v' : Submission.Mostow.E 1)
    (W W' : Submission.Mostow.E m) :
    Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W)
        (Submission.Mostow.fermiW 1 m v W') =
      Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v' W)
        (Submission.Mostow.fermiW 1 m v' W') := by
  refine Real.cosh_injOn (nib_hdist_nonneg _ _) (nib_hdist_nonneg _ _) ?_
  rw [nib_cosh_hdist_fermiW, nib_cosh_hdist_fermiW, cosh_hdist_self_eq_one v,
    cosh_hdist_self_eq_one v', mul_one]

/-- The foot-free distance is a lower bound for the distance from any point with the same normal
coordinate: `hdist (fermiW v W) (fermiW v W') ≤ hdist (fermiW v W) (fermiW vp W')`. -/
lemma hdist_fermiW_le_foot (m : ℕ) (v vp : Submission.Mostow.E 1)
    (W Wp : Submission.Mostow.E m) :
    Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W)
        (Submission.Mostow.fermiW 1 m v Wp) ≤
      Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W)
        (Submission.Mostow.fermiW 1 m vp Wp) := by
  have hcosh : Real.cosh (Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W)
        (Submission.Mostow.fermiW 1 m v Wp)) ≤
      Real.cosh (Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W)
        (Submission.Mostow.fermiW 1 m vp Wp)) := by
    rw [nib_cosh_hdist_fermiW, nib_cosh_hdist_fermiW]
    have h2 : Real.sqrt (1 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖Wp‖ ^ 2)
          * Real.cosh (Submission.Mostow.hdist v v) ≤
        Real.sqrt (1 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖Wp‖ ^ 2)
          * Real.cosh (Submission.Mostow.hdist v vp) := by
      rw [cosh_hdist_self_eq_one v]
      exact mul_le_mul_of_nonneg_left (Real.one_le_cosh _) (by positivity)
    linarith
  rw [Real.cosh_le_cosh, abs_of_nonneg (nib_hdist_nonneg _ _),
    abs_of_nonneg (nib_hdist_nonneg _ _)] at hcosh
  exact hcosh

/-- The `cosh` of the displacement of a block rotation, in the foot-free coordinates. -/
lemma cosh_hdist_fermiW_rot (m : ℕ) (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (v : Submission.Mostow.E 1) (W : Submission.Mostow.E m) :
    Real.cosh (Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W)
        (Submission.Mostow.fermiW 1 m v (R W))) = 1 + ‖R W - W‖ ^ 2 / 2 := by
  rw [nib_cosh_hdist_fermiW, R.norm_map, cosh_hdist_self_eq_one, mul_one]
  have h1 : Real.sqrt (1 + ‖W‖ ^ 2) * Real.sqrt (1 + ‖W‖ ^ 2) = 1 + ‖W‖ ^ 2 := by
    rw [← sq, Real.sq_sqrt (by positivity)]
  rw [h1]
  have h2 : ‖R W - W‖ ^ 2 = 2 * ‖W‖ ^ 2 - 2 * inner ℝ W (R W) := by
    rw [norm_sub_sq_real, R.norm_map, real_inner_comm]
    ring
  rw [h2]
  ring

/-- A small displacement `< 2 sinh(η/2)` together with `η > 0` forces the block displacement at the
foot-free point to be `< η`. -/
lemma hdist_fermiW_rot_lt (m : ℕ) (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (v : Submission.Mostow.E 1) (W : Submission.Mostow.E m) {η : ℝ} (hη : 0 < η)
    (h : ‖R W - W‖ < 2 * Real.sinh (η / 2)) :
    Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W)
        (Submission.Mostow.fermiW 1 m v (R W)) < η := by
  have hcosh : Real.cosh (Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W)
        (Submission.Mostow.fermiW 1 m v (R W))) < Real.cosh η := by
    rw [cosh_hdist_fermiW_rot]
    have hc : Real.cosh η = 1 + 2 * Real.sinh (η / 2) ^ 2 := by
      have h2 := Real.cosh_two_mul (η / 2)
      rw [show (2 : ℝ) * (η / 2) = η by ring] at h2
      rw [h2, Real.cosh_sq]
      ring
    rw [hc]
    have hs : 0 ≤ Real.sinh (η / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
    have hD : 0 ≤ ‖R W - W‖ := norm_nonneg _
    nlinarith [h, hs, hD]
  rw [Real.cosh_lt_cosh, abs_of_nonneg (nib_hdist_nonneg _ _), abs_of_pos hη] at hcosh
  exact hcosh

/-- **Characterisation of `NearIdAt` for a block isometry.**  The property `NearIdAt (blk 1 m 1 R)`
at `fermiW 1 m v W` is equivalent to a condition on the normal coordinate alone: every `W'` whose
foot-free distance from `W` is at most `1` must be moved by `R` by less than `2 sinh(η/2)`.

The condition on `W'` (`hdist (fermiW 1 m v W) (fermiW 1 m v W') ≤ 1`) is itself free of the foot
`v` (`Work.Mostow.hdist_fermiW_foot_indep`), which is what makes the characterisation usable. -/
theorem nearIdAt_blk_spread_iff (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1) (hA : Submission.Mostow.POActionProp (1 + m))
    (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) (v : Submission.Mostow.E 1)
    (W : Submission.Mostow.E m) (η : ℝ) :
    Submission.Mostow.NearIdAt (Submission.Mostow.blk 1 m 1 R)
        (Submission.Mostow.fermiW 1 m v W) η ↔
      ∀ W' : Submission.Mostow.E m,
        Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W)
          (Submission.Mostow.fermiW 1 m v W') ≤ 1 →
        ‖R W' - W'‖ < 2 * Real.sinh (η / 2) := by
  constructor
  · intro hni W' hW'
    have hlt : Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W')
        (Submission.Mostow.blk 1 m 1 R • Submission.Mostow.fermiW 1 m v W') < η :=
      hni (Submission.Mostow.fermiW 1 m v W') hW'
    exact nib_disp_lt_of_hdist_lt m hA1 hI1 hA hI R v W' η hlt
  · intro hspread p hp
    set Wp : Submission.Mostow.E m := Submission.Mostow.nrmC 1 m p with hWp
    set vp : Submission.Mostow.E 1 :=
      (Real.sqrt (1 + ‖Submission.Mostow.nrmC 1 m p‖ ^ 2))⁻¹
        • Submission.Mostow.tanC 1 m p with hvp
    have hrec : Submission.Mostow.fermiW 1 m vp Wp = p := by
      rw [hvp, hWp]; exact nib_fermiW_surj m p
    have hηpos : 0 < η := by
      have h0 := hspread W (by rw [nib_hdist_self]; norm_num)
      have h2 : 0 < Real.sinh (η / 2) := by
        have hD : 0 ≤ ‖R W - W‖ := norm_nonneg _
        linarith
      have h3 : 0 < η / 2 := Real.sinh_pos_iff.mp h2
      linarith
    have hle : Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m v W)
        (Submission.Mostow.fermiW 1 m v Wp) ≤ 1 := by
      refine le_trans (hdist_fermiW_le_foot m v vp W Wp) ?_
      rw [hrec]
      exact hp
    have hdisp := hspread Wp hle
    rw [← hrec, nib_blk_smul_fermiW m hA1 hI1 hA hI R vp Wp]
    exact hdist_fermiW_rot_lt m R vp Wp hηpos hdisp

theorem margRegionNrmCSat (m : ℕ) (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) (η₁ : ℝ) :
    ∀ u u' : Submission.Mostow.E (1 + m), Submission.Mostow.nrmC 1 m u = Submission.Mostow.nrmC 1 m u' →
      u ∈ Work.Mostow.margRegion m Λ η₁ → u' ∈ Work.Mostow.margRegion m Λ η₁ := by
  intro u u' hW hu
  obtain ⟨a, haΛ, haStab, hares, hane, hni⟩ := hu
  -- every pointwise-fixing element of the stratum stabiliser is a block isometry
  have hab : a = Submission.Mostow.blk 1 m 1 (Submission.Mostow.nrmStd 1 m a) := by
    have h := stab_eq_blk 1 m hA1 hI1 hA hI a haStab
    rw [hares] at h
    exact h
  refine ⟨a, haΛ, haStab, hares, hane, ?_⟩
  rw [hab]
  have hni' : Submission.Mostow.NearIdAt
      (Submission.Mostow.blk 1 m 1 (Submission.Mostow.nrmStd 1 m a)) u η₁ := hab ▸ hni
  set R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m :=
    Submission.Mostow.nrmStd 1 m a with hR
  -- Fermi coordinates of `u` and `u'`
  set vu : Submission.Mostow.E 1 :=
    (Real.sqrt (1 + ‖Submission.Mostow.nrmC 1 m u‖ ^ 2))⁻¹ • Submission.Mostow.tanC 1 m u with hvu
  set vu' : Submission.Mostow.E 1 :=
    (Real.sqrt (1 + ‖Submission.Mostow.nrmC 1 m u'‖ ^ 2))⁻¹ • Submission.Mostow.tanC 1 m u'
    with hvu'
  have hurec : Submission.Mostow.fermiW 1 m vu (Submission.Mostow.nrmC 1 m u) = u := by
    rw [hvu]; exact nib_fermiW_surj m u
  have hurec' : Submission.Mostow.fermiW 1 m vu' (Submission.Mostow.nrmC 1 m u') = u' := by
    rw [hvu']; exact nib_fermiW_surj m u'
  -- the spread condition at `u`
  have hni_u : Submission.Mostow.NearIdAt (Submission.Mostow.blk 1 m 1 R)
      (Submission.Mostow.fermiW 1 m vu (Submission.Mostow.nrmC 1 m u)) η₁ := by
    rw [hurec]; exact hni'
  have hspread_u :=
    (nearIdAt_blk_spread_iff m hA1 hI1 hA hI R vu (Submission.Mostow.nrmC 1 m u) η₁).mp hni_u
  -- transport it to the foot of `u'`: the normal coordinate is the same and the test condition is
  -- foot-free
  have hspread_u' : ∀ W' : Submission.Mostow.E m,
      Submission.Mostow.hdist (Submission.Mostow.fermiW 1 m vu' (Submission.Mostow.nrmC 1 m u'))
        (Submission.Mostow.fermiW 1 m vu' W') ≤ 1 → ‖R W' - W'‖ < 2 * Real.sinh (η₁ / 2) := by
    intro W' h
    refine hspread_u W' ?_
    rw [hW]
    rw [hdist_fermiW_foot_indep m vu vu' (Submission.Mostow.nrmC 1 m u') W']
    exact h
  have hni_u' : Submission.Mostow.NearIdAt (Submission.Mostow.blk 1 m 1 R)
      (Submission.Mostow.fermiW 1 m vu' (Submission.Mostow.nrmC 1 m u')) η₁ :=
    (nearIdAt_blk_spread_iff m hA1 hI1 hA hI R vu' (Submission.Mostow.nrmC 1 m u') η₁).mpr
      hspread_u'
  rw [hurec'] at hni_u'
  exact hni_u'

end

end Work.Mostow
