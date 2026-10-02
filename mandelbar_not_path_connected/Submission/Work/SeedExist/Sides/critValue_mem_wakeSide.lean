/-
# `Work.SeedExist.Sides.critValue_mem_wakeSide`

The critical value `c = T_c 0` lies in the wake side `S₀` of the level-`0` α-pair of the root
portrait, i.e. in the far side of the co-landing pair `P₀ = (α₁, α₂)` at `z₁`.

## The argument

Write `T = T_c` (the antiholomorphic quadratic), `w = T⁴ z₁`, and let

* `P₄ = (652/2046, 1642/2046, w)` — the level-`4` α-pair: `T⁴ α₂ = 652/2046` and
  `T⁴ α₁ = 1642/2046`, both rays landing at `w`;
* `P₅ = (1675/2046, 2665/2046, -w)` — its antipode (the angles are those of `P₄` shifted by
  `1/2`), both rays landing at `−w`.

1. **The orbit of `z₁` closes up.**  `R(1642/2046) = R(T⁴α₁)` lands at `w`, so the antipodal
   ray `R(1675/2046) = R(652/2046 + 1/2)` lands at `−w`; as `T` maps landing points to landing
   points and `T (−w) = T w`, we get `T w = z₁`, i.e. `T⁵ z₁ = z₁`.  Hence `z₁ ≠ c` (otherwise
   `T w = c = T 0` forces `w = 0`) and the fiber of `T` over `z₁` is exactly `{w, −w}`.

2. **`0` lies on the near side of `P₄` and of `P₅`.**  By antipodal symmetry: if `0` were in
   the far side of `P₄`, then `−0 = 0` would lie in the antipodal far side, which is contained
   in `pairSide P₅`; and `pairSide P₅ ⊆ pairSideNear P₄` (the far arc of `P₅` lies in the near
   arc of `P₄`), contradicting the disjointness of the two sides of `P₄`.  Symmetrically for
   `P₅`.  Consequently `0` lies in the region of the ray polygon `[P₄, P₅]` at any level `R > 1`
   (the region is the intersection of the two near sides below the level, and `pot 0 = 0`).

3. **Transfer along `T`.**  The preimage of `curve P₀` under `T` is contained in
   `curve P₄ ∪ curve P₅`, so the region avoids `T⁻¹ (curve P₀)`.  The base point of the region
   is the ray point of angle `midNear [P₄, P₅] = 1642/2046 + (33/2046)/2 = 3317/4092` at level
   `√4`, and `T (3317/4092) = 775/2046 ∈ (α₁, α₂) = (371/1023, 404/1023)`, so its image lies in
   the far side `pairSide P₀`.  The region is preconnected and contains both `0` and the base
   point; hence `T` maps the component of `0` in `(T⁻¹ curve P₀)ᶜ` into a preconnected subset of
   `(curve P₀)ᶜ` meeting `pairSide P₀`, i.e. into `pairSide P₀` itself.  As `T 0 = c`, the
   critical value lies in `pairSide P₀`, which is `Work.SeedExist.wakeSide hN z₁ 0`.
-/
import Mathlib
import Submission.Work.SeedExist.Setup
import Submission.Work.SeedExist.Antipodal
import Submission.Work.SeedExist.Pairs
import Submission.Work.ELPull.preimage_paramRay
import Submission.Work.ELTop.RigInput
import Submission.Work.ELTop.tripodArms_disjoint
import Submission.Work.ELTop.pairSide_subset_pairSide
import Submission.Work.ELTop.pairSide_subset_pairSideNear
import Submission.Work.ELTop.polyRegion_eq_iInter_pairSideNear
import Submission.Work.ELTop.seed_mem_polyRegion

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedExist.Sides

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ}

/-! ## 1. The numerical data of the four preimage rays -/

theorem el_T_four_alpha1 : (Work.EL.T^[4]) Work.EL.alpha1 = 1642 / 2046 := by
  norm_num [Work.EL.T, Work.EL.alpha1, Int.fract, Function.iterate_succ_apply',
    Function.iterate_zero]

theorem el_T_four_alpha2 : (Work.EL.T^[4]) Work.EL.alpha2 = 652 / 2046 := by
  norm_num [Work.EL.T, Work.EL.alpha2, Int.fract, Function.iterate_succ_apply',
    Function.iterate_zero]

theorem el_T_1642 : Work.EL.T (1642 / 2046) = Work.EL.alpha2 := by
  norm_num [Work.EL.T, Work.EL.alpha2, Int.fract]

theorem el_T_652 : Work.EL.T (652 / 2046) = Work.EL.alpha1 := by
  norm_num [Work.EL.T, Work.EL.alpha1, Int.fract]

theorem el_T_1675 : Work.EL.T (1675 / 2046) = Work.EL.alpha1 := by
  norm_num [Work.EL.T, Work.EL.alpha1, Int.fract]

theorem el_T_2665 : Work.EL.T (2665 / 2046) = Work.EL.alpha2 := by
  norm_num [Work.EL.T, Work.EL.alpha2, Int.fract]

theorem el_fract_pre1 : Int.fract (-Work.EL.alpha1 / 2) = 1675 / 2046 := by
  norm_num [Work.EL.alpha1, Int.fract]

theorem el_fract_pre2 : Int.fract (-Work.EL.alpha1 / 2 + 1 / 2) = 652 / 2046 := by
  norm_num [Work.EL.alpha1, Int.fract]

theorem el_fract_pre3 : Int.fract (-Work.EL.alpha2 / 2) = 1642 / 2046 := by
  norm_num [Work.EL.alpha2, Int.fract]

theorem el_fract_pre4 : Int.fract (-Work.EL.alpha2 / 2 + 1 / 2) = 619 / 2046 := by
  norm_num [Work.EL.alpha2, Int.fract]

theorem el_T_midNear : Work.EL.T (3317 / 4092) = 775 / 2046 := by
  norm_num [Work.EL.T, Int.fract]

theorem el_InArc_mid : Work.EL.InArc (775 / 2046) Work.EL.alpha1 Work.EL.alpha2 :=
  Work.ELTop.InArc_of_mem_Ioo (by norm_num [Work.EL.alpha1]) (by norm_num [Work.EL.alpha2])
    (by norm_num [Work.EL.alpha2, Work.EL.alpha1])

theorem el_arcLen_45 : Work.EL.arcLen (652 / 2046) (1642 / 2046) = 990 / 2046 := by
  norm_num [Work.EL.arcLen, Int.fract]

theorem el_arcLen_55 : Work.EL.arcLen (1675 / 2046) (2665 / 2046) = 990 / 2046 := by
  norm_num [Work.EL.arcLen, Int.fract]

theorem el_arcLen_44 : Work.EL.arcLen (1642 / 2046) (1675 / 2046) = 33 / 2046 := by
  norm_num [Work.EL.arcLen, Int.fract]

theorem el_arcLen_45_ne : Work.EL.arcLen (652 / 2046) (1642 / 2046) ≠ 0 := by
  rw [el_arcLen_45]; norm_num

theorem el_arcLen_55_ne : Work.EL.arcLen (1675 / 2046) (2665 / 2046) ≠ 0 := by
  rw [el_arcLen_55]; norm_num

/-- The ray of angle `619/2046 = 2665/2046 - 1` is the ray of angle `2665/2046`. -/
theorem el_paramRay_619_mem {hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)} {z : ℂ}
    (h : z ∈ Work.Top.NakaneData.paramRay hN (619 / 2046)) :
    z ∈ Work.Top.NakaneData.paramRay hN (2665 / 2046) := by
  have h1 : Work.Top.NakaneData.paramRay hN ((619 : ℝ) / 2046 + ((1 : ℤ) : ℝ))
      = Work.Top.NakaneData.paramRay hN (619 / 2046) :=
    Work.ELTop.paramRay_add_int hN (619 / 2046) 1
  rw [show (2665 : ℝ) / 2046 = (619 : ℝ) / 2046 + ((1 : ℤ) : ℝ) by norm_num, h1]
  exact h

theorem el_Tantibar_neg (x : ℂ) : Tantibar c (-x) = Tantibar c x := by
  simp only [LeanEval.ComplexAnalysis.Tantibar, map_neg, neg_sq]

/-! ## 2. The three co-landing pairs -/

/-- The level-`0` α-pair: the two root rays `α₁`, `α₂` co-landing at `z₁`. -/
noncomputable def pairP0 (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) : Work.EL.CoPair hN where
  toRawPair := ⟨Work.EL.alpha1, Work.EL.alpha2, z₁⟩
  lands_a := (Work.ELTop.landsN_iff_landsAt hN
    (Work.ELPull.isDynBottcher_dynPhiOf_of_dynB' hN) Work.EL.alpha1 z₁).mpr h1
  lands_b := (Work.ELTop.landsN_iff_landsAt hN
    (Work.ELPull.isDynBottcher_dynPhiOf_of_dynB' hN) Work.EL.alpha2 z₁).mpr h2

/-- The level-`4` α-pair: the rays `T⁴α₂ = 652/2046`, `T⁴α₁ = 1642/2046` landing at `w = T⁴ z₁`. -/
noncomputable def pairP4 (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) : Work.EL.CoPair hN where
  toRawPair := ⟨652 / 2046, 1642 / 2046, (Tantibar c)^[4] z₁⟩
  lands_a := by
    have h := (Work.SeedExist.landsN_alphaPair hN h1 h2 4).2
    rwa [el_T_four_alpha2] at h
  lands_b := by
    have h := (Work.SeedExist.landsN_alphaPair hN h1 h2 4).1
    rwa [el_T_four_alpha1] at h

/-- The antipodal pair of `P₄`: the rays `1675/2046 = 652/2046 + 1/2`,
`2665/2046 = 1642/2046 + 1/2` landing at `−w`. -/
noncomputable def pairP5 (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) : Work.EL.CoPair hN where
  toRawPair := ⟨1675 / 2046, 2665 / 2046, -((Tantibar c)^[4] z₁)⟩
  lands_a := by
    have h := Work.SeedExist.landsN_add_half hN
      (θ := 652 / 2046) (y := (Tantibar c)^[4] z₁) (pairP4 hN h1 h2).lands_a
    rw [show (652 : ℝ) / 2046 + 1 / 2 = 1675 / 2046 by norm_num] at h
    exact h
  lands_b := by
    have h := Work.SeedExist.landsN_add_half hN
      (θ := 1642 / 2046) (y := (Tantibar c)^[4] z₁) (pairP4 hN h1 h2).lands_b
    rw [show (1642 : ℝ) / 2046 + 1 / 2 = 2665 / 2046 by norm_num] at h
    exact h

@[simp] theorem pairP0_a (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    (pairP0 hN h1 h2).a = Work.EL.alpha1 := rfl

@[simp] theorem pairP0_b (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    (pairP0 hN h1 h2).b = Work.EL.alpha2 := rfl

@[simp] theorem pairP0_y (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    (pairP0 hN h1 h2).y = z₁ := rfl

@[simp] theorem pairP4_a (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    (pairP4 hN h1 h2).a = 652 / 2046 := rfl

@[simp] theorem pairP4_b (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    (pairP4 hN h1 h2).b = 1642 / 2046 := rfl

@[simp] theorem pairP4_y (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    (pairP4 hN h1 h2).y = (Tantibar c)^[4] z₁ := rfl

@[simp] theorem pairP5_a (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    (pairP5 hN h1 h2).a = 1675 / 2046 := rfl

@[simp] theorem pairP5_b (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    (pairP5 hN h1 h2).b = 2665 / 2046 := rfl

@[simp] theorem pairP5_y (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    (pairP5 hN h1 h2).y = -((Tantibar c)^[4] z₁) := rfl

/-! ## 3. The orbit of `z₁` closes up -/

theorem el_T_five_z₁ (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    (Tantibar c)^[5] z₁ = z₁ := by
  have hφ := Work.ELPull.isDynBottcher_dynPhiOf_of_dynB' hN
  have hmap : Work.EL.LandsN hN Work.EL.alpha1 (Tantibar c ((Tantibar c)^[4] z₁)) := by
    have h := Work.ELTop.landsN_map hN hφ (pairP5 hN h1 h2).lands_a
    have h2' : Work.EL.LandsN hN (Work.EL.T (1675 / 2046))
        (Tantibar c (-((Tantibar c)^[4] z₁))) := h
    rw [el_T_1675, el_Tantibar_neg] at h2'
    exact h2'
  have hz : Work.EL.LandsN hN Work.EL.alpha1 z₁ :=
    (Work.ELTop.landsN_iff_landsAt hN hφ Work.EL.alpha1 z₁).mpr h1
  have huniq : Tantibar c ((Tantibar c)^[4] z₁) = z₁ := tendsto_nhds_unique hmap hz
  rw [show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply']
  exact huniq

/-- `T` applied at the fourth iterate of `z₁` gives back `z₁`. -/
theorem el_T_four_apply (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    Tantibar c ((Tantibar c)^[4] z₁) = z₁ := by
  have h := el_T_five_z₁ hN h1 h2
  rw [show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply'] at h
  exact h

theorem el_z1_ne_c (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (hzn : ∀ i : ℕ, i ≤ 4 → (Tantibar c)^[i] z₁ ≠ 0)
    (hzw : Tantibar c ((Tantibar c)^[4] z₁) = z₁) : z₁ ≠ c := by
  intro hzc
  have hTw : Tantibar c ((Tantibar c)^[4] z₁) = c := by rw [hzw, hzc]
  have h2 : (starRingEnd ℂ ((Tantibar c)^[4] z₁)) ^ 2 = 0 := by
    have h := hTw
    simp only [LeanEval.ComplexAnalysis.Tantibar] at h
    linear_combination h
  have h3 : (starRingEnd ℂ ((Tantibar c)^[4] z₁)) = 0 := sq_eq_zero_iff.mp h2
  have h4 : (Tantibar c)^[4] z₁ = 0 := by
    simpa using congrArg (starRingEnd ℂ) h3
  exact hzn 4 (by norm_num) h4

theorem el_fiber {z₁ : ℂ} (hzc : z₁ ≠ c) (hzw : Tantibar c ((Tantibar c)^[4] z₁) = z₁) :
    ∀ u : ℂ, Tantibar c u = z₁ →
      u = (Tantibar c)^[4] z₁ ∨ u = -((Tantibar c)^[4] z₁) := by
  obtain ⟨u₀, -, -, -, huniq⟩ := Work.ELPull.fiber_neg hzc
  intro u hu
  rcases huniq u hu with h | h
  · rcases huniq ((Tantibar c)^[4] z₁) hzw with h' | h'
    · exact Or.inl (by rw [h, h'])
    · exact Or.inr (by rw [h, h']; simp)
  · rcases huniq ((Tantibar c)^[4] z₁) hzw with h' | h'
    · exact Or.inr (by rw [h, h'])
    · exact Or.inl (by rw [h, h'])

/-! ## 4. The preimage of `curve P₀` is contained in `curve P₄ ∪ curve P₅` -/

theorem el_T_notMem_curveP0 (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁)
    (hfib : ∀ u : ℂ, Tantibar c u = z₁ →
      u = (Tantibar c)^[4] z₁ ∨ u = -((Tantibar c)^[4] z₁))
    {z : ℂ} (h4 : z ∉ Work.EL.pairCurve (pairP4 hN h1 h2))
    (h5 : z ∉ Work.EL.pairCurve (pairP5 hN h1 h2)) :
    Tantibar c z ∉ Work.EL.pairCurve (pairP0 hN h1 h2) := by
  have hφ := Work.ELPull.isDynBottcher_dynPhiOf_of_dynB' hN
  intro hz
  rw [Work.EL.mem_pairCurve_iff] at hz
  rcases hz with hz | hz | hz
  · have h := Work.ELPull.preimage_paramRay hN hφ Work.EL.alpha1 hz
    rw [el_fract_pre1, el_fract_pre2, Set.mem_union] at h
    rcases h with h | h
    · exact h5 (by rw [Work.EL.mem_pairCurve_iff]; exact Or.inl h)
    · exact h4 (by rw [Work.EL.mem_pairCurve_iff]; exact Or.inl h)
  · rcases hfib z hz with h | h
    · exact h4 (by rw [Work.EL.mem_pairCurve_iff]; exact Or.inr (Or.inl h))
    · exact h5 (by rw [Work.EL.mem_pairCurve_iff]; exact Or.inr (Or.inl h))
  · have h := Work.ELPull.preimage_paramRay hN hφ Work.EL.alpha2 hz
    rw [el_fract_pre3, el_fract_pre4, Set.mem_union] at h
    rcases h with h | h
    · exact h4 (by rw [Work.EL.mem_pairCurve_iff]; exact Or.inr (Or.inr h))
    · exact h5 (by rw [Work.EL.mem_pairCurve_iff]; exact Or.inr (Or.inr (el_paramRay_619_mem h)))

/-! ## 5. The arc inclusions of the two pairs -/

theorem el_InArc_shift (x : ℝ) (k : ℤ) (a b : ℝ) :
    Work.EL.InArc (x + (k : ℝ)) a b ↔ Work.EL.InArc x a b := by
  unfold Work.EL.InArc Work.EL.arcLen
  rw [show x + (k : ℝ) - a = (x - a) + (k : ℝ) by ring, Int.fract_add_intCast]

theorem el_harc45 {θ : ℝ} (h : Work.EL.InArc θ (652 / 2046) (1642 / 2046)) :
    Work.EL.InArc θ (2665 / 2046) (1675 / 2046 + 1) := by
  obtain ⟨m, hm1, hm2⟩ := Work.ELTop.InArc.exists_int_mem_Ioo (by norm_num) h
  have key := Work.ELTop.InArc_of_mem_Ioo (a := 2665 / 2046) (b := 1675 / 2046 + 1)
    (x := θ + ((m : ℤ) : ℝ) + 1) ?_ ?_ (by norm_num)
  · rw [show θ + ((m : ℤ) : ℝ) + 1 = θ + (((m + 1 : ℤ)) : ℝ) by push_cast; ring] at key
    exact (el_InArc_shift θ (m + 1) (2665 / 2046) (1675 / 2046 + 1)).mp key
  · push_cast; linarith
  · push_cast; linarith

theorem el_harc54 {θ : ℝ} (h : Work.EL.InArc θ (1675 / 2046) (2665 / 2046)) :
    Work.EL.InArc θ (1642 / 2046) (652 / 2046 + 1) := by
  obtain ⟨m, hm1, hm2⟩ := Work.ELTop.InArc.exists_int_mem_Ioo (by norm_num) h
  have key := Work.ELTop.InArc_of_mem_Ioo (a := 1642 / 2046) (b := 652 / 2046 + 1)
    (x := θ + ((m : ℤ) : ℝ)) ?_ ?_ (by norm_num)
  · exact (el_InArc_shift θ m (1642 / 2046) (652 / 2046 + 1)).mp key
  · linarith
  · linarith

/-! ## 6. The two pair curves are disjoint -/

theorem el_disjoint45 (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁)
    (hz4 : (Tantibar c)^[4] z₁ ≠ 0) :
    Disjoint (Work.EL.pairCurve (pairP4 hN h1 h2)) (Work.EL.pairCurve (pairP5 hN h1 h2)) := by
  have hwK : (Tantibar c)^[4] z₁ ∈ Work.EL.K c :=
    Work.ELTop.landsN_mem_K hN (pairP4 hN h1 h2).lands_a
  have hnegwK : -((Tantibar c)^[4] z₁) ∈ Work.EL.K c :=
    Work.ELTop.landsN_mem_K hN (pairP5 hN h1 h2).lands_a
  have hcurve5 : Work.EL.pairCurve (pairP5 hN h1 h2)
      = (Work.EL.paramRay hN (1675 / 2046) ∪ {-((Tantibar c)^[4] z₁)})
        ∪ Work.EL.paramRay hN (2665 / 2046) := rfl
  have h1a : Disjoint (Work.EL.paramRay hN (652 / 2046))
      (Work.EL.pairCurve (pairP5 hN h1 h2)) := by
    rw [hcurve5]
    refine Disjoint.union_right (Disjoint.union_right ?_ ?_) ?_
    · exact Work.ELTop.paramRay_disjoint hN (fun k =>
        Work.ELTop.unitIoo_ne_add_int (a := 652 / 2046) (y := 1675 / 2046)
          (by norm_num) (by norm_num) k)
    · rw [Set.disjoint_singleton_right]
      intro hmem
      exact (Work.EL.paramRay_subset_compl hN (652 / 2046)) hmem hnegwK
    · exact Work.ELTop.paramRay_disjoint hN (fun k =>
        Work.ELTop.unitIoo_ne_add_int (a := 652 / 2046) (y := 2665 / 2046)
          (by norm_num) (by norm_num) k)
  have h1b : Disjoint ({(Tantibar c)^[4] z₁} : Set ℂ) (Work.EL.pairCurve (pairP5 hN h1 h2)) := by
    rw [hcurve5, Set.disjoint_singleton_left]
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hmem
      exact (Work.EL.paramRay_subset_compl hN (1675 / 2046)) hmem hwK
    · intro h
      have h2' : (2 : ℂ) * (Tantibar c)^[4] z₁ = 0 := by linear_combination h
      exact hz4 ((mul_eq_zero.mp h2').resolve_left two_ne_zero)
    · intro hmem
      exact (Work.EL.paramRay_subset_compl hN (2665 / 2046)) hmem hwK
  have h1c : Disjoint (Work.EL.paramRay hN (1642 / 2046))
      (Work.EL.pairCurve (pairP5 hN h1 h2)) := by
    rw [hcurve5]
    refine Disjoint.union_right (Disjoint.union_right ?_ ?_) ?_
    · exact Work.ELTop.paramRay_disjoint hN (fun k =>
        Work.ELTop.unitIoo_ne_add_int (a := 1642 / 2046) (y := 1675 / 2046)
          (by norm_num) (by norm_num) k)
    · rw [Set.disjoint_singleton_right]
      intro hmem
      exact (Work.EL.paramRay_subset_compl hN (1642 / 2046)) hmem hnegwK
    · exact Work.ELTop.paramRay_disjoint hN (fun k =>
        Work.ELTop.unitIoo_ne_add_int (a := 1642 / 2046) (y := 2665 / 2046)
          (by norm_num) (by norm_num) k)
  rw [show Work.EL.pairCurve (pairP4 hN h1 h2)
      = (Work.EL.paramRay hN (652 / 2046) ∪ {(Tantibar c)^[4] z₁})
        ∪ Work.EL.paramRay hN (1642 / 2046) from rfl]
  exact (h1a.union_left h1b).union_left h1c

theorem el_neg_paramRay_45a {hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)} :
    (fun z : ℂ => -z) '' Work.EL.paramRay hN (652 / 2046)
      = Work.EL.paramRay hN (1675 / 2046) := by
  rw [show (1675 : ℝ) / 2046 = 652 / 2046 + 1 / 2 by norm_num]
  exact (Work.SeedExist.paramRay_add_half hN (652 / 2046)).symm

theorem el_neg_paramRay_45b {hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)} :
    (fun z : ℂ => -z) '' Work.EL.paramRay hN (1642 / 2046)
      = Work.EL.paramRay hN (2665 / 2046) := by
  rw [show (2665 : ℝ) / 2046 = 1642 / 2046 + 1 / 2 by norm_num]
  exact (Work.SeedExist.paramRay_add_half hN (1642 / 2046)).symm

theorem el_neg_paramRay_54a {hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)} :
    (fun z : ℂ => -z) '' Work.EL.paramRay hN (1675 / 2046)
      = Work.EL.paramRay hN (652 / 2046) := by
  rw [(Work.SeedExist.paramRay_add_half hN (1675 / 2046)).symm]
  rw [show (1675 : ℝ) / 2046 + 1 / 2 = (652 : ℝ) / 2046 + 1 by norm_num]
  exact Work.ELTop.paramRay_add_one_real hN (652 / 2046)

theorem el_neg_paramRay_54b {hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)} :
    (fun z : ℂ => -z) '' Work.EL.paramRay hN (2665 / 2046)
      = Work.EL.paramRay hN (1642 / 2046) := by
  rw [(Work.SeedExist.paramRay_add_half hN (2665 / 2046)).symm]
  rw [show (2665 : ℝ) / 2046 + 1 / 2 = (1642 : ℝ) / 2046 + 1 by norm_num]
  exact Work.ELTop.paramRay_add_one_real hN (1642 / 2046)

/-! ## 7. `0` lies on both near sides -/

theorem el_neg_subset_45 (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    (fun z : ℂ => -z) '' (Work.EL.pairSide (pairP4 hN h1 h2)) ⊆
      Work.EL.pairSide (pairP5 hN h1 h2) := by
  have hcurve : (fun z : ℂ => -z) '' Work.EL.pairCurve (pairP4 hN h1 h2)
      = Work.EL.pairCurve (pairP5 hN h1 h2) := by
    rw [show Work.EL.pairCurve (pairP4 hN h1 h2)
        = (Work.EL.paramRay hN (652 / 2046) ∪ {(Tantibar c)^[4] z₁})
          ∪ Work.EL.paramRay hN (1642 / 2046) from rfl,
      show Work.EL.pairCurve (pairP5 hN h1 h2)
        = (Work.EL.paramRay hN (1675 / 2046) ∪ {-((Tantibar c)^[4] z₁)})
          ∪ Work.EL.paramRay hN (2665 / 2046) from rfl,
      Set.image_union, Set.image_union, Set.image_singleton,
      el_neg_paramRay_45a (hN := hN), el_neg_paramRay_45b (hN := hN)]

  have hbase : (fun z : ℂ => -z) (Work.EL.rayPt hN ((pairP4 hN h1 h2).a
        + Work.EL.arcLen (pairP4 hN h1 h2).a (pairP4 hN h1 h2).b / 2) 2)
      = Work.EL.rayPt hN ((pairP5 hN h1 h2).a
        + Work.EL.arcLen (pairP5 hN h1 h2).a (pairP5 hN h1 h2).b / 2) 2 := by
    show -(Work.EL.rayPt hN (652 / 2046 + Work.EL.arcLen (652 / 2046) (1642 / 2046) / 2) 2)
      = Work.EL.rayPt hN (1675 / 2046 + Work.EL.arcLen (1675 / 2046) (2665 / 2046) / 2) 2
    rw [el_arcLen_45, el_arcLen_55,
      show (652 : ℝ) / 2046 + 990 / 2046 / 2 = 1147 / 2046 by norm_num,
      show (1675 : ℝ) / 2046 + 990 / 2046 / 2 = 2170 / 2046 by norm_num,
      ← Work.SeedExist.rayPt_add_half hN (1147 / 2046) 2]
    norm_num
  refine IsPreconnected.subset_connectedComponentIn ?_ ?_ ?_
  · exact isPreconnected_connectedComponentIn.image (fun z : ℂ => -z)
      continuous_neg.continuousOn
  · refine ⟨_, mem_connectedComponentIn (Work.ELTop.rayPt_farMid_notMem_pairCurve hN
      (pairP4 hN h1 h2)
      (by norm_num : (652 : ℝ) / 2046 < 1642 / 2046)
      (by norm_num : (1642 : ℝ) / 2046 < (652 : ℝ) / 2046 + 1)), hbase⟩
  · rintro w ⟨z, hz, rfl⟩ hw
    have hw' : (fun z : ℂ => -z) z ∈ Work.EL.pairCurve (pairP5 hN h1 h2) := hw
    rw [← hcurve] at hw'
    obtain ⟨y, hy, hyz⟩ := hw'
    have hyz' : y = z := neg_inj.mp hyz
    rw [hyz'] at hy
    exact (connectedComponentIn_subset _ _ hz) hy

theorem el_neg_subset_54 (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    (fun z : ℂ => -z) '' (Work.EL.pairSide (pairP5 hN h1 h2)) ⊆
      Work.EL.pairSide (pairP4 hN h1 h2) := by
  have hcurve : (fun z : ℂ => -z) '' Work.EL.pairCurve (pairP5 hN h1 h2)
      = Work.EL.pairCurve (pairP4 hN h1 h2) := by
    rw [show Work.EL.pairCurve (pairP5 hN h1 h2)
        = (Work.EL.paramRay hN (1675 / 2046) ∪ {-((Tantibar c)^[4] z₁)})
          ∪ Work.EL.paramRay hN (2665 / 2046) from rfl,
      show Work.EL.pairCurve (pairP4 hN h1 h2)
        = (Work.EL.paramRay hN (652 / 2046) ∪ {(Tantibar c)^[4] z₁})
          ∪ Work.EL.paramRay hN (1642 / 2046) from rfl,
      Set.image_union, Set.image_union, Set.image_singleton,
      el_neg_paramRay_54a (hN := hN), el_neg_paramRay_54b (hN := hN), neg_neg]

  have hbase : (fun z : ℂ => -z) (Work.EL.rayPt hN ((pairP5 hN h1 h2).a
        + Work.EL.arcLen (pairP5 hN h1 h2).a (pairP5 hN h1 h2).b / 2) 2)
      = Work.EL.rayPt hN ((pairP4 hN h1 h2).a
        + Work.EL.arcLen (pairP4 hN h1 h2).a (pairP4 hN h1 h2).b / 2) 2 := by
    show -(Work.EL.rayPt hN (1675 / 2046 + Work.EL.arcLen (1675 / 2046) (2665 / 2046) / 2) 2)
      = Work.EL.rayPt hN (652 / 2046 + Work.EL.arcLen (652 / 2046) (1642 / 2046) / 2) 2
    rw [el_arcLen_45, el_arcLen_55,
      show (1675 : ℝ) / 2046 + 990 / 2046 / 2 = 2170 / 2046 by norm_num,
      show (652 : ℝ) / 2046 + 990 / 2046 / 2 = 1147 / 2046 by norm_num,
      ← Work.SeedExist.rayPt_add_half hN (2170 / 2046) 2,
      show (2170 : ℝ) / 2046 + 1 / 2 = 1147 / 2046 + 1 by norm_num]
    exact Work.ELTop.rayPt_add_one hN (1147 / 2046) 2
  refine IsPreconnected.subset_connectedComponentIn ?_ ?_ ?_
  · exact isPreconnected_connectedComponentIn.image (fun z : ℂ => -z)
      continuous_neg.continuousOn
  · refine ⟨_, mem_connectedComponentIn (Work.ELTop.rayPt_farMid_notMem_pairCurve hN
      (pairP5 hN h1 h2)
      (by norm_num : (1675 : ℝ) / 2046 < 2665 / 2046)
      (by norm_num : (2665 : ℝ) / 2046 < (1675 : ℝ) / 2046 + 1)), hbase⟩
  · rintro w ⟨z, hz, rfl⟩ hw
    have hw' : (fun z : ℂ => -z) z ∈ Work.EL.pairCurve (pairP4 hN h1 h2) := hw
    rw [← hcurve] at hw'
    obtain ⟨y, hy, hyz⟩ := hw'
    have hyz' : y = z := neg_inj.mp hyz
    rw [hyz'] at hy
    exact (connectedComponentIn_subset _ _ hz) hy

theorem el_zero_mem_near_P4 (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁)
    (hJ : Work.Top.JordanForm) (h0K : (0 : ℂ) ∈ Work.EL.K c)
    (hz4 : (Tantibar c)^[4] z₁ ≠ 0) :
    (0 : ℂ) ∈ Work.EL.pairSideNear (pairP4 hN h1 h2) := by
  have h0c4 : (0 : ℂ) ∉ Work.EL.pairCurve (pairP4 hN h1 h2) := by
    rw [Work.EL.mem_pairCurve_iff]
    rintro (h | h | h)
    · exact (Work.EL.paramRay_subset_compl hN (652 / 2046)) h h0K
    · exact hz4 h.symm
    · exact (Work.EL.paramRay_subset_compl hN (1642 / 2046)) h h0K
  have hs4 := Work.ELTop.pairSides hN hJ (pairP4 hN h1 h2) el_arcLen_45_ne
  have hsub : Work.EL.pairSide (pairP5 hN h1 h2) ⊆ Work.EL.pairSideNear (pairP4 hN h1 h2) :=
    Work.ELTop.pairSide_subset_pairSideNear hN hJ (pairP5 hN h1 h2) (pairP4 hN h1 h2)
      (el_disjoint45 hN h1 h2 hz4).symm (fun _ hθ => el_harc54 hθ)
  have hneg := el_neg_subset_45 hN h1 h2
  rcases (show (0 : ℂ) ∈ Work.EL.pairSide (pairP4 hN h1 h2)
      ∪ Work.EL.pairSideNear (pairP4 hN h1 h2) from by
        rw [hs4.union_eq]; exact h0c4) with h | h
  · have h0' : (0 : ℂ) ∈ (fun z : ℂ => -z) '' Work.EL.pairSide (pairP4 hN h1 h2) :=
      ⟨0, h, by simp⟩
    exact absurd (hsub (hneg h0')) (Set.disjoint_left.mp hs4.disjoint h)
  · exact h

theorem el_zero_mem_near_P5 (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁)
    (hJ : Work.Top.JordanForm) (h0K : (0 : ℂ) ∈ Work.EL.K c)
    (hz4 : (Tantibar c)^[4] z₁ ≠ 0) :
    (0 : ℂ) ∈ Work.EL.pairSideNear (pairP5 hN h1 h2) := by
  have h0c5 : (0 : ℂ) ∉ Work.EL.pairCurve (pairP5 hN h1 h2) := by
    rw [Work.EL.mem_pairCurve_iff]
    rintro (h | h | h)
    · exact (Work.EL.paramRay_subset_compl hN (1675 / 2046)) h h0K
    · exact hz4 (neg_eq_zero.mp h.symm)
    · exact (Work.EL.paramRay_subset_compl hN (2665 / 2046)) h h0K
  have hs5 := Work.ELTop.pairSides hN hJ (pairP5 hN h1 h2) el_arcLen_55_ne
  have hsub : Work.EL.pairSide (pairP4 hN h1 h2) ⊆ Work.EL.pairSideNear (pairP5 hN h1 h2) :=
    Work.ELTop.pairSide_subset_pairSideNear hN hJ (pairP4 hN h1 h2) (pairP5 hN h1 h2)
      (el_disjoint45 hN h1 h2 hz4) (fun _ hθ => el_harc45 hθ)
  have hneg := el_neg_subset_54 hN h1 h2
  rcases (show (0 : ℂ) ∈ Work.EL.pairSide (pairP5 hN h1 h2)
      ∪ Work.EL.pairSideNear (pairP5 hN h1 h2) from by
        rw [hs5.union_eq]; exact h0c5) with h | h
  · have h0' : (0 : ℂ) ∈ (fun z : ℂ => -z) '' Work.EL.pairSide (pairP5 hN h1 h2) :=
      ⟨0, h, by simp⟩
    exact absurd (hsub (hneg h0')) (Set.disjoint_left.mp hs5.disjoint h)
  · exact h

/-! ## 8. The ray polygon `[P₄, P₅]` and its region -/

theorem el_polyAdmissible (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁)
    (hz4 : (Tantibar c)^[4] z₁ ≠ 0) :
    Work.EL.PolyAdmissible [pairP4 hN h1 h2, pairP5 hN h1 h2] := by
  refine ⟨by simp, ?_, ?_⟩
  · rw [Work.EL.CyclicStrict]
    refine ⟨by simp, ?_, ?_⟩
    · have hlist : [pairP4 hN h1 h2, pairP5 hN h1 h2].flatMap (fun P => [P.a, P.b])
          = [652 / 2046, 1642 / 2046, 1675 / 2046, 2665 / 2046] := rfl
      rw [hlist]
      refine List.pairwise_cons.mpr ⟨?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl <;> norm_num
      · refine List.pairwise_cons.mpr ⟨?_, ?_⟩
        · intro b hb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl <;> norm_num
        · refine List.pairwise_cons.mpr ⟨?_, ?_⟩
          · intro b hb
            simp only [List.mem_singleton] at hb
            subst hb
            norm_num
          · refine List.pairwise_cons.mpr ⟨?_, List.Pairwise.nil⟩
            intro b hb
            exact absurd hb (by simp)
    · intro x hx
      have hlist : [pairP4 hN h1 h2, pairP5 hN h1 h2].flatMap (fun P => [P.a, P.b])
          = [652 / 2046, 1642 / 2046, 1675 / 2046, 2665 / 2046] := rfl
      rw [hlist] at hx ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num [List.headD_cons]
  · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, List.Pairwise.nil⟩⟩
    · intro Q hQ
      simp only [List.mem_singleton] at hQ
      subst hQ
      intro h
      simp only [pairP4_y, pairP5_y] at h
      have h2' : (2 : ℂ) * (Tantibar c)^[4] z₁ = 0 := by linear_combination h
      exact hz4 ((mul_eq_zero.mp h2').resolve_left two_ne_zero)
    · intro b hb
      exact absurd hb (by simp)

theorem el_midNear45 (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    Work.EL.midNear [pairP4 hN h1 h2, pairP5 hN h1 h2] = 3317 / 4092 := by
  rw [Work.EL.midNear]
  norm_num [Int.fract]

theorem el_zero_mem_region (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁)
    (hJ : Work.Top.JordanForm) (h0K : (0 : ℂ) ∈ Work.EL.K c)
    (hz4 : (Tantibar c)^[4] z₁ ≠ 0) :
    (0 : ℂ) ∈ Work.EL.polyRegion [pairP4 hN h1 h2, pairP5 hN h1 h2] 4 := by
  have hR : (1 : ℝ) < 4 := by norm_num
  have hps := el_polyAdmissible hN h1 h2 hz4
  have hJc := Work.ELTop.polyCurve_isJordan hN _ hps hR
  rw [Work.ELTop.polyRegion_eq_iInter_pairSideNear hN hJ _ hps hR hJc]
  refine ⟨?_, ?_⟩
  · intro P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · exact el_zero_mem_near_P4 hN h1 h2 hJ h0K hz4
    · exact el_zero_mem_near_P5 hN h1 h2 hJ h0K hz4
  · show Work.EL.pot hN 0 < Real.log 4
    rw [Work.EL.pot_of_mem hN h0K]
    exact Real.log_pos hR

/-! ## 9. The critical value lies in the wake side -/

theorem wakeSide_eq_pairSide_P0 (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    Work.SeedExist.wakeSide hN z₁ 0 = Work.EL.pairSide (pairP0 hN h1 h2) := by
  have hα : Work.EL.alphaPairRaw c z₁ 0 = (pairP0 hN h1 h2).toRawPair := by
    rw [Work.EL.alphaPairRaw]
    simp only [Function.iterate_zero, id_eq]
    rw [min_eq_left (show Work.EL.alpha1 ≤ Work.EL.alpha2 by
        norm_num [Work.EL.alpha1, Work.EL.alpha2]),
      max_eq_right (show Work.EL.alpha1 ≤ Work.EL.alpha2 by
        norm_num [Work.EL.alpha1, Work.EL.alpha2])]
    rfl
  show Work.EL.RawPair.sideThrough hN (Work.EL.alphaPairRaw c z₁ 0)
      (Work.EL.wakeLo 0) (Work.EL.wakeHi 0)
    = Work.EL.RawPair.sideThrough hN (pairP0 hN h1 h2).toRawPair
      (pairP0 hN h1 h2).a (pairP0 hN h1 h2).b
  rw [hα]
  show Work.EL.RawPair.sideThrough hN (pairP0 hN h1 h2).toRawPair
      (Work.EL.wakeLo 0) (Work.EL.wakeHi 0)
    = Work.EL.RawPair.sideThrough hN (pairP0 hN h1 h2).toRawPair
      (Work.EL.alpha1) (Work.EL.alpha2)
  rfl

theorem critValue_mem_wakeSide {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c))
    (hJ : Work.Top.JordanForm) {z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁)
    (hzn : ∀ i : ℕ, i ≤ 4 → (LeanEval.ComplexAnalysis.Tantibar c)^[i] z₁ ≠ 0)
    (h0K : (0 : ℂ) ∈ Work.EL.K c) :
    c ∈ Work.SeedExist.wakeSide hN z₁ 0 := by
  have hφ := Work.ELPull.isDynBottcher_dynPhiOf_of_dynB' hN
  have hzw := el_T_four_apply hN h1 h2
  have hzc := el_z1_ne_c hN hzn hzw
  have hfib := el_fiber (c := c) hzc hzw
  have hz4 : (Tantibar c)^[4] z₁ ≠ 0 := fun h => hzn 4 (by norm_num) h
  have hz1 : z₁ ≠ 0 := by simpa using hzn 0 (by norm_num)
  -- `c ∈ K c`, hence the critical value is off the pair curve of `P₀`
  have hcK : c ∈ Work.EL.K c := by
    have hb : Work.ParamRays.BoundedOrbit c 0 := h0K
    have h1' := hb.shift 1
    rw [show Work.ParamRays.orbit c 0 1 = c from Work.ParamRays.critOrbit_one c] at h1'
    simpa [Work.EL.K, Work.ParamRays.filledJulia] using h1'
  have hc_curve : c ∉ Work.EL.pairCurve (pairP0 hN h1 h2) := by
    rw [Work.EL.mem_pairCurve_iff]
    rintro (h | h | h)
    · exact (Work.EL.paramRay_subset_compl hN Work.EL.alpha1) h hcK
    · exact hzc h.symm
    · exact (Work.EL.paramRay_subset_compl hN Work.EL.alpha2) h hcK
  -- the constants
  have hR : (1 : ℝ) < 4 := by norm_num
  have hps := el_polyAdmissible hN h1 h2 hz4
  have hJc := Work.ELTop.polyCurve_isJordan hN _ hps hR
  have hreg := Work.ELTop.polyRegion_eq_iInter_pairSideNear hN hJ _ hps hR hJc
  -- the base point of the region and its image
  have hyreg : Work.EL.rayPt hN (Work.EL.midNear [pairP4 hN h1 h2, pairP5 hN h1 h2])
      (Real.sqrt 4) ∈ Work.EL.polyRegion [pairP4 hN h1 h2, pairP5 hN h1 h2] 4 :=
    Work.ELTop.seed_mem_polyRegion hN _ hps hR
  have hs4 : (1 : ℝ) < Real.sqrt 4 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hTy : Tantibar c (Work.EL.rayPt hN (Work.EL.midNear [pairP4 hN h1 h2, pairP5 hN h1 h2])
      (Real.sqrt 4)) ∈ Work.EL.pairSide (pairP0 hN h1 h2) := by
    have hT := Work.ELTop.rayPt_T hN hφ
      (θ := Work.EL.midNear [pairP4 hN h1 h2, pairP5 hN h1 h2]) (s := Real.sqrt 4) hs4
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4)] at hT
    rw [← hT, el_midNear45 hN h1 h2, el_T_midNear]
    exact Work.ELTop.paramRay_subset_pairSide hN hJ (pairP0 hN h1 h2) el_InArc_mid
      (Work.EL.rayPt_mem_paramRay hN hR)
  -- the component of `0`
  have hreg_sub : Work.EL.polyRegion [pairP4 hN h1 h2, pairP5 hN h1 h2] 4 ⊆
      (Tantibar c ⁻¹' Work.EL.pairCurve (pairP0 hN h1 h2))ᶜ := by
    intro z hz hzT
    rw [hreg] at hz
    obtain ⟨hzside, -⟩ := hz
    have hz4' : z ∉ Work.EL.pairCurve (pairP4 hN h1 h2) :=
      fun hmem => (connectedComponentIn_subset _ _ (hzside _ (by simp))) hmem
    have hz5' : z ∉ Work.EL.pairCurve (pairP5 hN h1 h2) :=
      fun hmem => (connectedComponentIn_subset _ _ (hzside _ (by simp))) hmem
    exact el_T_notMem_curveP0 hN h1 h2 hfib hz4' hz5' hzT
  have hZmem : (0 : ℂ) ∈ (Tantibar c ⁻¹' Work.EL.pairCurve (pairP0 hN h1 h2))ᶜ := by
    show Tantibar c 0 ∉ Work.EL.pairCurve (pairP0 hN h1 h2)
    rw [show Tantibar c 0 = c by simp [LeanEval.ComplexAnalysis.Tantibar]]
    exact hc_curve
  have hZ : (0 : ℂ) ∈ connectedComponentIn
      (Tantibar c ⁻¹' Work.EL.pairCurve (pairP0 hN h1 h2))ᶜ 0 :=
    mem_connectedComponentIn hZmem
  have h0reg : (0 : ℂ) ∈ Work.EL.polyRegion [pairP4 hN h1 h2, pairP5 hN h1 h2] 4 :=
    el_zero_mem_region hN h1 h2 hJ h0K hz4
  have hZsub : Work.EL.polyRegion [pairP4 hN h1 h2, pairP5 hN h1 h2] 4 ⊆ connectedComponentIn
      (Tantibar c ⁻¹' Work.EL.pairCurve (pairP0 hN h1 h2))ᶜ 0 :=
    IsPreconnected.subset_connectedComponentIn (Work.EL.isPreconnected_polyRegion _ _) h0reg hreg_sub
  -- the image of the component
  have hTZpre : IsPreconnected (Tantibar c '' connectedComponentIn
      (Tantibar c ⁻¹' Work.EL.pairCurve (pairP0 hN h1 h2))ᶜ 0) :=
    isPreconnected_connectedComponentIn.image (Tantibar c) (by
      unfold LeanEval.ComplexAnalysis.Tantibar; fun_prop)
  have hTZsub : Tantibar c '' connectedComponentIn
      (Tantibar c ⁻¹' Work.EL.pairCurve (pairP0 hN h1 h2))ᶜ 0 ⊆
        (Work.EL.pairCurve (pairP0 hN h1 h2))ᶜ := by
    rintro w ⟨z, hz, rfl⟩ hmem
    exact (connectedComponentIn_subset _ _ hz) hmem
  have hmemT : Tantibar c (Work.EL.rayPt hN (Work.EL.midNear [pairP4 hN h1 h2, pairP5 hN h1 h2])
      (Real.sqrt 4)) ∈ Tantibar c '' connectedComponentIn
        (Tantibar c ⁻¹' Work.EL.pairCurve (pairP0 hN h1 h2))ᶜ 0 :=
    ⟨_, hZsub hyreg, rfl⟩
  have hmain : c ∈ Work.EL.pairSide (pairP0 hN h1 h2) := by
    have hTy' : Tantibar c (Work.EL.rayPt hN (Work.EL.midNear [pairP4 hN h1 h2, pairP5 hN h1 h2])
        (Real.sqrt 4)) ∈ connectedComponentIn (Work.EL.pairCurve (pairP0 hN h1 h2))ᶜ
          (Work.EL.rayPt hN ((pairP0 hN h1 h2).a
            + Work.EL.arcLen (pairP0 hN h1 h2).a (pairP0 hN h1 h2).b / 2) 2) := hTy
    have hsub := IsPreconnected.subset_connectedComponentIn hTZpre hmemT hTZsub
    rw [← connectedComponentIn_eq hTy'] at hsub
    exact hsub ⟨0, hZ, by simp [LeanEval.ComplexAnalysis.Tantibar]⟩
  rw [wakeSide_eq_pairSide_P0 hN h1 h2]
  exact hmain

end Work.SeedExist.Sides
