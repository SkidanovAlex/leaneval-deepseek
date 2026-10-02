import Mathlib
import Submission.Work.LandLeaves.All
import Submission.Work.LandLeaves.ccBet_angDouble_of_typeSet
import Submission.Work.LandLeaves.ccBet_v2_defs
import Submission.Work.LandLeaves.gmLocalOrder
import Submission.Work.LandLeaves.InArcHard.localCore
import Submission.Work.LandLeaves.InArcHard.sectorTransfer
import Submission.Work.LandLeaves.InArcHard.ccBet_angDouble_dichotomy
import Submission.Work.LandLeaves.InArcHard.BasicClean
import Submission.Work.ParamRays.isDynBottcher_unique
import Submission.Work.ELTop.All
import Submission.Work.LANDCL.Quarter.isParabolic_quarter_half

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Port of the Goldberg-Milnor Lemma 2.2 chain to the parabolic cusp `c = 1/4`, `z = 1/2`, `k = 1`

The whole chain proving the cyclic-order preservation of the `2k`-fold angle map at a *repelling*
periodic point is already on disk (`Work.LandLeaves.InArcHard`).  This file ports it to the
parabolic cusp, replacing every use of `Work.Landing.IsRepelling c k y` by the three explicit
inputs `hfix` (the fixed-point identity), `hlocal` (a local left inverse of the second return map)
and `hinj` (the injectivity of the angle map modulo `1` on the type).

Concretely, the uses of `hrep` in the chain are exactly

* `hrep.1.1 : 0 < k`,
* `tauC_fixed hrep : tauC c k y = y`,
* `exists_tauC_injOn hrep` (which only consumes the *left inverse* field `hgτ` of
  `exists_local_repelling_branch`, never the contraction),
* `rayAccum_angDouble_singleton' hφ hrep` (whose proof is `rayAccum_iterate` plus `tauC_fixed`),
* `eq_mod_one_of_rayAccum_of_angDouble_eq hφ hrep`,

and each of these is replaced below by the corresponding hypothesis.  All the *general* lemmas of
`Work.LandLeaves.InArcHard.Core` (the angular four-case tables, the Böttcher-level transfer, the
far-side dictionary, ...) are imported and used verbatim.

Every ported declaration is named `..._mndl` and lives in the same namespace as the original, so
that the copied proof scripts elaborate with exactly the same name resolution as the originals.
-/

/-- The second-return angle map `σ = (angDouble)^[2k]` sends the type of the fixed point `y` into
itself: the image of the ray of angle `θ` under `(Tantibar c)^[2k]` is the ray of angle `σθ`, and
`(Tantibar c)^[2k] y = y`.  (Port of `Work.LandLeaves.rayAccum_angDouble_singleton'`.) -/
theorem Work.LandLeaves.rayAccum_angDouble_singleton_mndl {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ)
    (hfix : (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] y = y)
    {θ : ℝ} (h : Work.Landing.rayAccum c φ θ = {y}) :
    Work.Landing.rayAccum c φ ((Work.Landing.angDouble)^[2 * k] θ) = {y} := by
  rw [Work.Landing.rayAccum_iterate hφ θ (2 * k), h, Set.image_singleton, hfix]

open Classical Filter Set
open LeanEval.ComplexAnalysis (Tantibar)
open scoped _root_.Topology

namespace Work.LandLeaves.InArcHard.Core

noncomputable section

/-- `τ` is injective on a small ball around the fixed point `y`, from a local left
inverse (`hlocal`); no contraction is used. -/
theorem exists_tauC_injOn_mndl {c : ℂ} {k : ℕ} {y : ℂ}
    (hfix : tauC c k y = y)
    (hlocal : ∃ (r r' : ℝ) (g : ℂ → ℂ), 0 < r ∧ 0 < r' ∧ ∀ z : ℂ,
      ‖z - y‖ ≤ r → ‖tauC c k z - y‖ ≤ r' → g (tauC c k z) = z) :
    ∃ r > 0, Set.InjOn (tauC c k) (Metric.ball y r) := by
  obtain ⟨r, r', g, hr, hr'pos, hgτ⟩ := hlocal
  have hcont : Continuous (tauC c k) := (differentiable_tauC c k).continuous
  have hmem : tauC c k ⁻¹' Metric.ball y r' ∈ 𝓝 y := by
    have h := hcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (tauC c k y) hr'pos)
    rwa [hfix] at h
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hmem
  have key : ∀ z ∈ Metric.ball y (min r δ), g (tauC c k z) = z := by
    intro z hz
    have hzr : z ∈ Metric.ball y r := Metric.ball_subset_ball (min_le_left r δ) hz
    have hzd : z ∈ Metric.ball y δ := Metric.ball_subset_ball (min_le_right r δ) hz
    have hzr' : tauC c k z ∈ Metric.ball y r' := hδ hzd
    refine hgτ z ?_ ?_
    · rw [Metric.mem_ball, dist_eq_norm] at hzr; exact le_of_lt hzr
    · rw [Metric.mem_ball, dist_eq_norm] at hzr'; exact le_of_lt hzr'
  refine ⟨min r δ, lt_min hr hδpos, fun z1 hz1 z2 hz2 heq => ?_⟩
  rw [← key z1 hz1, ← key z2 hz2, heq]

/-- Near the fixed point `y`, a point different from `y` is not mapped to `y` by `τ`. -/
theorem tauC_ne_y_near_mndl {c : ℂ} {k : ℕ} {y : ℂ}
    (hfix : tauC c k y = y)
    (hlocal : ∃ (r r' : ℝ) (g : ℂ → ℂ), 0 < r ∧ 0 < r' ∧ ∀ z : ℂ,
      ‖z - y‖ ≤ r → ‖tauC c k z - y‖ ≤ r' → g (tauC c k z) = z) :
    ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball y ε → z ≠ y → tauC c k z ≠ y := by
  obtain ⟨r, hr, hinj⟩ := exists_tauC_injOn_mndl hfix hlocal
  refine ⟨r, hr, fun z hz hzy hτ => hzy ?_⟩
  refine hinj hz (Metric.mem_ball.mpr (by simpa using hr)) ?_
  rw [hτ, hfix]

/-- **The side transfer near the landing point.**  With `P = (u,v,y)` and `P'` the pair of the
`4^k`-images, the far side of `P` is carried to the far side of `P'` on a punctured neighbourhood
of `y`: the local side correspondence at the ray points (the angular four-case table) together
with the local "no sibling ray" fact propagates along the preconnected punctured ball by a clopen
argument. -/
theorem cop_sides_gen_mndl {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hN : Work.EL.DynB c φ) (hk : 0 < k) (hfix : tauC c k y = y)
    (hlocal : ∃ (r r' : ℝ) (g : ℂ → ℂ), 0 < r ∧ 0 < r' ∧ ∀ z : ℂ,
      ‖z - y‖ ≤ r → ‖tauC c k z - y‖ ≤ r' → g (tauC c k z) = z)
    (P P' : Work.EL.CoPair hN) (hPy : P.y = y) (hP'y : P'.y = y)
    (hS : Work.EL.PairSides hN P) (hS' : Work.EL.PairSides hN P')
    (hnd' : Work.EL.arcLen P'.a P'.b ≠ 0)
    (hPTa : ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball y ε →
      tauC c k z ∈ Work.EL.paramRay hN P'.a → z ∈ Work.EL.paramRay hN P.a)
    (hPTb : ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball y ε →
      tauC c k z ∈ Work.EL.paramRay hN P'.b → z ∈ Work.EL.paramRay hN P.b)
    (hLA : ∀ p : ℂ, p ∈ Work.EL.paramRay hN P.a ∪ Work.EL.paramRay hN P.b → ∃ δ > 0,
      ∀ z : ℂ, z ∈ Metric.ball p δ → z ∉ Work.EL.pairCurve P →
        tauC c k z ∉ Work.EL.pairCurve P' ∧
        (z ∈ Work.EL.pairSide P ↔ tauC c k z ∈ Work.EL.pairSide P')) :
    ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball y ε → z ∉ Work.EL.pairCurve P →
      (z ∈ Work.EL.pairSide P ↔ tauC c k z ∈ Work.EL.pairSide P') := by
  obtain ⟨ε₀, hε₀pos, hFne⟩ := tauC_ne_y_near_mndl (c := c) (k := k) (y := y) hfix hlocal
  obtain ⟨εa, hεapos, hptia⟩ := hPTa
  obtain ⟨εb, hεbpos, hptib⟩ := hPTb
  set ε : ℝ := min ε₀ (min εa εb) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact lt_min hε₀pos (lt_min hεapos hεbpos)
  have hεε₀ : ε ≤ ε₀ := by rw [hεdef]; exact min_le_left _ _
  have hεεa : ε ≤ εa := by rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεεb : ε ≤ εb := by rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hball₀ : Metric.ball y ε ⊆ Metric.ball y ε₀ := Metric.ball_subset_ball hεε₀
  have hballa : Metric.ball y ε ⊆ Metric.ball y εa := Metric.ball_subset_ball hεεa
  have hballb : Metric.ball y ε ⊆ Metric.ball y εb := Metric.ball_subset_ball hεεb
  have hyK : y ∈ Work.EL.K c := hPy ▸ Work.ELTop.landsN_mem_K hN P.lands_a
  have hyX : y ∈ Work.EL.pairCurve P := by
    rw [Work.EL.mem_pairCurve_iff]; exact Or.inr (Or.inl hPy.symm)
  -- ## Step 1: `τ` creates no point of the curve of `P'`
  have step1 : ∀ z : ℂ, z ∈ Metric.ball y ε → z ∉ Work.EL.pairCurve P →
      tauC c k z ∉ Work.EL.pairCurve P' := by
    intro z hz hzX hFY
    have hzne : z ≠ y := fun h1 => hzX (h1.symm ▸ hyX)
    have hFne : tauC c k z ≠ y := hFne z (hball₀ hz) hzne
    rw [Work.EL.mem_pairCurve_iff] at hFY
    rcases hFY with h | h | h
    · exact hzX (by
        rw [Work.EL.mem_pairCurve_iff]
        exact Or.inl (hptia z (hballa hz) h))
    · exact hFne (h.trans hP'y)
    · exact hzX (by
        rw [Work.EL.mem_pairCurve_iff]
        exact Or.inr (Or.inr (hptib z (hballb hz) h)))
  -- ## Step 2: the good and the bad set
  set Good₀ : Set ℂ := {z : ℂ | z ∉ Work.EL.pairCurve P ∧
      ((z ∈ Work.EL.pairSide P ∧ tauC c k z ∈ Work.EL.pairSide P') ∨
       (z ∈ Work.EL.pairSideNear P ∧ tauC c k z ∈ Work.EL.pairSideNear P'))} with hGood₀
  set Bad : Set ℂ := {z : ℂ | z ∉ Work.EL.pairCurve P ∧
      ((z ∈ Work.EL.pairSide P ∧ tauC c k z ∈ Work.EL.pairSideNear P') ∨
       (z ∈ Work.EL.pairSideNear P ∧ tauC c k z ∈ Work.EL.pairSide P'))} with hBad
  set Ω : Set ℂ := Metric.ball y ε \ {y} with hΩ
  -- ## Step 3: the thickening of the curve of `P` given by the local angle lemma
  set TT : Set ℂ := {p : ℂ | p ∈ Metric.ball y ε \ {y} ∧
      (p ∈ Work.EL.paramRay hN P.a ∨ p ∈ Work.EL.paramRay hN P.b)} with hTT
  have hδexists : ∀ p : TT, ∃ δ > 0, ∀ z : ℂ, z ∈ Metric.ball p.1 δ →
      z ∉ Work.EL.pairCurve P →
      tauC c k z ∉ Work.EL.pairCurve P' ∧
      (z ∈ Work.EL.pairSide P ↔ tauC c k z ∈ Work.EL.pairSide P') :=
    fun p => hLA p.1 p.2.2
  set δ : TT → ℝ := fun p => Classical.choose (hδexists p) with hδdef
  have hδpos : ∀ p : TT, 0 < δ p := fun p => by
    rw [hδdef]; exact (Classical.choose_spec (hδexists p)).1
  have hδspec : ∀ p : TT, ∀ z : ℂ, z ∈ Metric.ball p.1 (δ p) →
      z ∉ Work.EL.pairCurve P →
      tauC c k z ∉ Work.EL.pairCurve P' ∧
      (z ∈ Work.EL.pairSide P ↔ tauC c k z ∈ Work.EL.pairSide P') := fun p => by
    rw [hδdef]; exact (Classical.choose_spec (hδexists p)).2
  set Good : Set ℂ := Good₀ ∪ ⋃ p : TT, Metric.ball p.1 (δ p) with hGood
  -- ## Openness
  have hcont_τ : Continuous (tauC c k) := (differentiable_tauC c k).continuous
  have hGood₀open : IsOpen Good₀ := by
    rw [hGood₀]
    have h1 : IsOpen {z : ℂ | z ∈ Work.EL.pairSide P ∧
        tauC c k z ∈ Work.EL.pairSide P'} :=
      hS.isOpen_far.inter (hS'.isOpen_far.preimage hcont_τ)
    have h2 : IsOpen {z : ℂ | z ∈ Work.EL.pairSideNear P ∧
        tauC c k z ∈ Work.EL.pairSideNear P'} :=
      hS.isOpen_near.inter (hS'.isOpen_near.preimage hcont_τ)
    have heq : {z : ℂ | z ∉ Work.EL.pairCurve P ∧
        ((z ∈ Work.EL.pairSide P ∧ tauC c k z ∈ Work.EL.pairSide P') ∨
         (z ∈ Work.EL.pairSideNear P ∧ tauC c k z ∈ Work.EL.pairSideNear P'))}
        = (Work.EL.pairCurve P)ᶜ ∩
          ({z : ℂ | z ∈ Work.EL.pairSide P ∧ tauC c k z ∈ Work.EL.pairSide P'} ∪
           {z : ℂ | z ∈ Work.EL.pairSideNear P ∧ tauC c k z ∈ Work.EL.pairSideNear P'}) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    rw [heq]
    exact (Work.ELTop.isClosed_pairCurve hN P).isOpen_compl.inter (h1.union h2)
  have hBadopen : IsOpen Bad := by
    rw [hBad]
    have h1 : IsOpen {z : ℂ | z ∈ Work.EL.pairSide P ∧
        tauC c k z ∈ Work.EL.pairSideNear P'} :=
      hS.isOpen_far.inter (hS'.isOpen_near.preimage hcont_τ)
    have h2 : IsOpen {z : ℂ | z ∈ Work.EL.pairSideNear P ∧
        tauC c k z ∈ Work.EL.pairSide P'} :=
      hS.isOpen_near.inter (hS'.isOpen_far.preimage hcont_τ)
    have heq : {z : ℂ | z ∉ Work.EL.pairCurve P ∧
        ((z ∈ Work.EL.pairSide P ∧ tauC c k z ∈ Work.EL.pairSideNear P') ∨
         (z ∈ Work.EL.pairSideNear P ∧ tauC c k z ∈ Work.EL.pairSide P'))}
        = (Work.EL.pairCurve P)ᶜ ∩
          ({z : ℂ | z ∈ Work.EL.pairSide P ∧ tauC c k z ∈ Work.EL.pairSideNear P'} ∪
           {z : ℂ | z ∈ Work.EL.pairSideNear P ∧ tauC c k z ∈ Work.EL.pairSide P'}) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    rw [heq]
    exact (Work.ELTop.isClosed_pairCurve hN P).isOpen_compl.inter (h1.union h2)
  have hGoodopen : IsOpen Good := by
    rw [hGood]
    exact hGood₀open.union (isOpen_iUnion fun p : TT => Metric.isOpen_ball)
  -- ## `Bad` and `Good` are disjoint
  have hdisj : Disjoint Bad Good := by
    rw [hGood, Set.disjoint_left]
    intro z hzB hzG
    rcases hzG with hzG₀ | hzU
    · rw [hBad] at hzB
      rw [hGood₀] at hzG₀
      obtain ⟨-, hBd⟩ := hzB
      obtain ⟨-, hGd⟩ := hzG₀
      rcases hBd with ⟨bP, bP'⟩ | ⟨bN, bN'⟩
      · rcases hGd with ⟨gP, gP'⟩ | ⟨gN, gN'⟩
        · exact hS'.disjoint.notMem_of_mem_left gP' bP'
        · exact hS.disjoint.notMem_of_mem_left bP gN
      · rcases hGd with ⟨gP, gP'⟩ | ⟨gN, gN'⟩
        · exact hS.disjoint.notMem_of_mem_left gP bN
        · exact hS'.disjoint.notMem_of_mem_left bN' gN'
    · rw [Set.mem_iUnion] at hzU
      obtain ⟨p, hzp⟩ := hzU
      rw [hBad] at hzB
      obtain ⟨hzX, hBd⟩ := hzB
      obtain ⟨hFzX, heq⟩ := hδspec p z hzp hzX
      rcases hBd with ⟨bP, bP'⟩ | ⟨bN, bN'⟩
      · exact hS'.disjoint.notMem_of_mem_left (heq.mp bP) bP'
      · exact hS.disjoint.notMem_of_mem_left (heq.mpr bN') bN
  -- ## Step 4: `Ω` is covered
  have hcover : Ω ⊆ Bad ∪ Good := by
    rw [hΩ, hGood]
    intro z hz
    obtain ⟨hzball, hzsing⟩ := hz
    by_cases hzX : z ∈ Work.EL.pairCurve P
    · right; right
      rw [Set.mem_iUnion]
      have hzTT : z ∈ TT := by
        rw [hTT]
        refine ⟨⟨hzball, hzsing⟩, ?_⟩
        rw [Work.EL.mem_pairCurve_iff] at hzX
        rcases hzX with h | h | h
        · exact Or.inl h
        · exact absurd (h.trans hPy) (fun h1 => hzsing (by simpa using h1))
        · exact Or.inr h
      exact ⟨⟨z, hzTT⟩, Metric.mem_ball_self (hδpos ⟨z, hzTT⟩)⟩
    · have hFzX : tauC c k z ∉ Work.EL.pairCurve P' := step1 z hzball hzX
      have hzAB : z ∈ Work.EL.pairSide P ∪ Work.EL.pairSideNear P := by
        rw [hS.union_eq]; exact hzX
      have hFAB : tauC c k z ∈ Work.EL.pairSide P' ∪ Work.EL.pairSideNear P' := by
        rw [hS'.union_eq]; exact hFzX
      rcases hzAB with hfar | hnear
      · rcases hFAB with hfar' | hnear'
        · right; left; rw [hGood₀]; exact ⟨hzX, Or.inl ⟨hfar, hfar'⟩⟩
        · left; rw [hBad]; exact ⟨hzX, Or.inl ⟨hfar, hnear'⟩⟩
      · rcases hFAB with hfar' | hnear'
        · left; rw [hBad]; exact ⟨hzX, Or.inr ⟨hnear, hfar'⟩⟩
        · right; left; rw [hGood₀]; exact ⟨hzX, Or.inr ⟨hnear, hnear'⟩⟩
  -- ## Step 5: the clopen argument
  have hpre : IsPreconnected Ω := by
    rw [hΩ]
    exact Work.SeedSimple2.COP.isPreconnected_ball_diff_singleton y ε
  have hor : Ω ⊆ Bad ∨ Ω ⊆ Good := hpre.subset_or_subset hBadopen hGoodopen hdisj hcover
  have hnotBad : ¬ Ω ⊆ Bad := by
    intro hsub
    obtain ⟨s₀, hs₀, hnear⟩ := exists_level_ball_of_landsN' hN P.lands_a hεpos
    set s : ℝ := (1 + s₀) / 2 with hsdef
    have hs1 : 1 < s := by rw [hsdef]; linarith
    have hss : s < s₀ := by rw [hsdef]; linarith
    have hzball : Work.EL.rayPt hN P.a s ∈ Metric.ball y ε := by
      rw [← hPy]; exact hnear s ⟨hs1, hss⟩
    have hzK : Work.EL.rayPt hN P.a s ∉ Work.EL.K c := Work.EL.rayPt_notMem_K hN hs1
    have hzne : Work.EL.rayPt hN P.a s ≠ y := fun h1 => hzK (h1.symm ▸ hyK)
    have hzΩ : Work.EL.rayPt hN P.a s ∈ Ω := by
      rw [hΩ]
      exact ⟨hzball, by simpa using hzne⟩
    have hzBad : Work.EL.rayPt hN P.a s ∈ Bad := hsub hzΩ
    rw [hBad] at hzBad
    exact hzBad.1 (by
      rw [Work.EL.mem_pairCurve_iff]
      exact Or.inl (Work.EL.rayPt_mem_paramRay hN hs1))
  have hΩG : Ω ⊆ Good := hor.resolve_left hnotBad
  -- ## The conclusion
  refine ⟨ε, hεpos, ?_⟩
  intro z hzball hzX
  have hzne : z ≠ y := fun h1 => hzX (h1.symm ▸ hyX)
  have hzΩ : z ∈ Ω := by
    rw [hΩ]
    exact ⟨hzball, by simpa using hzne⟩
  have hzGood : z ∈ Good := hΩG hzΩ
  rw [hGood] at hzGood
  rcases hzGood with hzG₀ | hzU
  · rw [hGood₀] at hzG₀
    obtain ⟨-, hGd⟩ := hzG₀
    constructor
    · intro hzA
      rcases hGd with ⟨-, gP'⟩ | ⟨gN, -⟩
      · exact gP'
      · exact absurd gN (hS.disjoint.notMem_of_mem_left hzA)
    · intro hzA'
      rcases hGd with ⟨gP, -⟩ | ⟨-, gN'⟩
      · exact gP
      · exact absurd gN' (hS'.disjoint.notMem_of_mem_left hzA')
  · rw [Set.mem_iUnion] at hzU
    obtain ⟨p, hzp⟩ := hzU
    exact (hδspec p z hzp hzX).2

/-- **The `2k`-fold angle map is injective modulo `1` on the type**, in the concrete form used
below. -/
theorem fract_sub_angDouble_ne_zero_mndl {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hk : 0 < k)
    (hinj : ∀ θ θ' : ℝ, Work.Landing.rayAccum c φ θ = {y} →
      Work.Landing.rayAccum c φ θ' = {y} →
      (∃ m : ℤ, (4 : ℝ) ^ k * θ = (4 : ℝ) ^ k * θ' + m) → ∃ mm : ℤ, θ = θ' + mm)
    {u w : ℝ} (hu : Work.Landing.rayAccum c φ u = {y})
    (hw : Work.Landing.rayAccum c φ w = {y}) (hne : Int.fract (w - u) ≠ 0) :
    Int.fract ((Work.Landing.angDouble)^[2 * k] w - (Work.Landing.angDouble)^[2 * k] u) ≠ 0 := by
  intro h0
  obtain ⟨m, hm⟩ := Int.fract_eq_zero_iff.mp h0
  have e1 := angDouble_iterate_two_mul hk w
  have e2 := angDouble_iterate_two_mul hk u
  rw [e1, e2] at hm
  have f1 : (4 : ℝ) ^ k * w - Int.fract ((4 : ℝ) ^ k * w) = (⌊(4 : ℝ) ^ k * w⌋ : ℝ) :=
    Int.self_sub_fract _
  have f2 : (4 : ℝ) ^ k * u - Int.fract ((4 : ℝ) ^ k * u) = (⌊(4 : ℝ) ^ k * u⌋ : ℝ) :=
    Int.self_sub_fract _
  have hkey : ∃ m' : ℤ, (4 : ℝ) ^ k * w = (4 : ℝ) ^ k * u + (m' : ℝ) := by
    refine ⟨m + ⌊(4 : ℝ) ^ k * w⌋ - ⌊(4 : ℝ) ^ k * u⌋, ?_⟩
    push_cast
    linarith
  obtain ⟨mm, hmm⟩ := hinj w u hw hu hkey
  refine hne ?_
  rw [hmm, show u + (mm : ℝ) - u = (mm : ℝ) by ring, Int.fract_intCast]

/-- **The local preimage identity at `y`**: near `y`, if `τ z` lies on the ray of an angle
congruent to `4^k u` modulo `1` and `R(u)` lands at `y`, then `z` itself lies on `R(u)`. -/
theorem tauC_preimage_tail_aux_mndl {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) {y : ℂ}
    (hfix : tauC c k y = y)
    (hlocal : ∃ (r r' : ℝ) (g : ℂ → ℂ), 0 < r ∧ 0 < r' ∧ ∀ z : ℂ,
      ‖z - y‖ ≤ r → ‖tauC c k z - y‖ ≤ r' → g (tauC c k z) = z) {u : ℝ}
    (hu : Work.Landing.rayAccum c φ u = {y}) :
    ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball y ε → ∀ θ' : ℝ,
      (∃ m : ℤ, θ' = (4 : ℝ) ^ k * u + m) →
      tauC c k z ∈ Work.EL.paramRay hN θ' → z ∈ Work.EL.paramRay hN u := by
  obtain ⟨ε₀, hε₀, hinj⟩ := exists_tauC_injOn_mndl hfix hlocal
  have hL : Work.EL.LandsN hN u y :=
    (Work.ELTop.landsN_iff_landsAt hN hφ u y).mpr (Work.LandLeaves.landsAt_of_rayAccum hφ hu)
  obtain ⟨s₀, hs₀, hnear⟩ := exists_level_ball_of_landsN' hN hL hε₀
  have hyK : y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN hL
  have hpot_y : Work.EL.pot hN y = 0 := Work.EL.pot_of_mem hN hyK
  have hτy : tauC c k y = y := hfix
  have hApos : 0 < (4 : ℝ) ^ k * Real.log s₀ :=
    mul_pos (by positivity) (Real.log_pos hs₀)
  have hcont : Continuous (fun z : ℂ => Work.EL.pot hN (tauC c k z)) :=
    hN.continuous_potential.comp (differentiable_tauC c k).continuous
  have hmem : {z : ℂ | Work.EL.pot hN (tauC c k z) < (4 : ℝ) ^ k * Real.log s₀} ∈ 𝓝 y :=
    (isOpen_lt hcont continuous_const).mem_nhds (by
      show Work.EL.pot hN (tauC c k y) < (4 : ℝ) ^ k * Real.log s₀
      rw [hτy, hpot_y]; exact hApos)
  obtain ⟨ε₁, hε₁, hbound⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
  intro z hz θ' hθ' hτz
  have hz₀ : z ∈ Metric.ball y ε₀ := Metric.ball_subset_ball (min_le_left _ _) hz
  have hz₁ : z ∈ Metric.ball y ε₁ := Metric.ball_subset_ball (min_le_right _ _) hz
  obtain ⟨m, hm⟩ := hθ'
  have hτz_top : tauC c k z ∈ Work.Top.NakaneData.paramRay hN θ' := hτz
  rw [Work.Top.NakaneData.paramRay_eq_range] at hτz_top
  obtain ⟨⟨t, ht⟩, ht_eq⟩ := hτz_top
  have htpos : 0 < t := lt_trans zero_lt_one ht
  obtain ⟨m', hm'⟩ := angDouble_it2m_add_int_aux u k
  have hray_eq : Work.EL.rayPt hN ((Work.Landing.angDouble)^[2 * k] u) t
      = Work.EL.rayPt hN θ' t := by
    rw [hm', hm, Work.ELTop.rayPt_add_int hN ((4 : ℝ) ^ k * u) t m',
      Work.ELTop.rayPt_add_int hN ((4 : ℝ) ^ k * u) t m]
  have ht_eq' : Work.EL.rayPt hN ((Work.Landing.angDouble)^[2 * k] u) t = tauC c k z :=
    hray_eq.trans ht_eq
  have hpotFz : Work.EL.pot hN (tauC c k z) = Real.log t := by
    rw [← ht_eq', Work.EL.pot_rayPt hN ht]
  have hlogt_lt : Real.log t < (4 : ℝ) ^ k * Real.log s₀ := by
    rw [← hpotFz]; exact hbound hz₁
  have hDpos : 0 < (4 : ℝ) ^ k := by positivity
  set s : ℝ := t ^ (((4 : ℝ) ^ k)⁻¹) with hsdef
  have hs1 : 1 < s := by
    rw [hsdef]; exact Real.one_lt_rpow ht (inv_pos.mpr hDpos)
  have hspow : s ^ (4 ^ k : ℕ) = t := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt htpos)]
    rw [show (((4 : ℕ) ^ k : ℕ) : ℝ) = (4 : ℝ) ^ k by push_cast; ring]
    rw [inv_mul_cancel₀ (ne_of_gt hDpos), Real.rpow_one]
  have hlog_s : Real.log s = ((4 : ℝ) ^ k)⁻¹ * Real.log t := by
    rw [hsdef, Real.log_rpow htpos]
  have hs_lt : s < s₀ := by
    refine (Real.log_lt_log_iff (Real.rpow_pos_of_pos htpos _)
      (lt_trans zero_lt_one hs₀)).mp ?_
    rw [hlog_s]
    calc ((4 : ℝ) ^ k)⁻¹ * Real.log t
        < ((4 : ℝ) ^ k)⁻¹ * ((4 : ℝ) ^ k * Real.log s₀) :=
          mul_lt_mul_of_pos_left hlogt_lt (inv_pos.mpr hDpos)
      _ = Real.log s₀ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hDpos), one_mul]
  have hrs : Work.EL.rayPt hN u s ∈ Metric.ball y ε₀ := hnear s ⟨hs1, hs_lt⟩
  have hF_ray : tauC c k (Work.EL.rayPt hN u s) = tauC c k z := by
    rw [show tauC c k (Work.EL.rayPt hN u s)
        = (Tantibar c)^[2 * k] (Work.EL.rayPt hN u s) from tauC_apply c k _,
      ← rayPt_iterate_angDouble hN hφ (θ := u) hs1, hspow]
    exact ht_eq'
  have hzeq : z = Work.EL.rayPt hN u s := hinj hz₀ hrs hF_ray.symm
  rw [hzeq]
  exact Work.EL.rayPt_mem_paramRay hN hs1

end

end Work.LandLeaves.InArcHard.Core

namespace Work.LandLeaves.InArcHard

noncomputable section

variable {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}

theorem sectorTransfer_mndl {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ)
    (hfix : (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] y = y) (hk : 0 < k)
    (hlocal : ∃ (r r' : ℝ) (g : ℂ → ℂ), 0 < r ∧ 0 < r' ∧ ∀ z : ℂ,
      ‖z - y‖ ≤ r → ‖Work.LandLeaves.InArcHard.Core.tauC c k z - y‖ ≤ r' → g (Work.LandLeaves.InArcHard.Core.tauC c k z) = z)
    (hinj : ∀ θ θ' : ℝ, Work.Landing.rayAccum c φ θ = {y} →
      Work.Landing.rayAccum c φ θ' = {y} →
      (∃ m : ℤ, (4 : ℝ) ^ k * θ = (4 : ℝ) ^ k * θ' + m) → ∃ mm : ℤ, θ = θ' + mm)
    {u v : ℝ} (hu : Work.Landing.rayAccum c φ u = {y}) (hv : Work.Landing.rayAccum c φ v = {y})
    (hnd : Int.fract (v - u) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ,
      z ∈ Work.EL.pairSide (Work.LandLeaves.mkPair (Work.LandLeaves.dynBNakane hφ)
            (Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ hu)
            (Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ hv)) →
      ‖z - y‖ < ε →
      (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] z ∈
        Work.EL.pairSide (Work.LandLeaves.mkPair (Work.LandLeaves.dynBNakane hφ)
          (Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ
            (Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix hu))
          (Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ
            (Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix hv))) := by
  classical
  let hN : Work.EL.DynB c φ := Work.LandLeaves.dynBNakane hφ
  -- ## The landing data of the shifted angles `fract u`, `fract v`
  have hacc_u' : Work.Landing.rayAccum c φ (Int.fract u) = {y} := by
    rw [← Work.FSeed.rayAccum_add_int c φ (Int.fract u) ⌊u⌋, Int.fract_add_floor u]
    exact hu
  have hacc_v' : Work.Landing.rayAccum c φ (Int.fract v) = {y} := by
    rw [← Work.FSeed.rayAccum_add_int c φ (Int.fract v) ⌊v⌋, Int.fract_add_floor v]
    exact hv
  have hL_u : Work.EL.LandsN hN u y :=
    Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ hu
  have hL_v : Work.EL.LandsN hN v y :=
    Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ hv
  have hL_u' : Work.EL.LandsN hN (Int.fract u) y :=
    (Work.ELTop.landsN_iff_landsAt hN hφ (Int.fract u) y).mpr
      (Work.LandLeaves.landsAt_of_rayAccum hφ hacc_u')
  have hL_v' : Work.EL.LandsN hN (Int.fract v) y :=
    (Work.ELTop.landsN_iff_landsAt hN hφ (Int.fract v) y).mpr
      (Work.LandLeaves.landsAt_of_rayAccum hφ hacc_v')
  -- ## The image angles and their landing points
  have hL_su : Work.EL.LandsN hN ((Work.Landing.angDouble)^[2 * k] u) y :=
    Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ
      (Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix hu)
  have hL_sv : Work.EL.LandsN hN ((Work.Landing.angDouble)^[2 * k] v) y :=
    Work.LandLeaves.InArcHard.landsN_of_rayAccum' hφ
      (Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix hv)
  -- ## The two pairs
  set P : Work.EL.CoPair hN := Work.LandLeaves.mkPair hN hL_u' hL_v' with hPdef
  set P' : Work.EL.CoPair hN := Work.LandLeaves.mkPair hN hL_su hL_sv with hP'def
  have hPa : P.a = Int.fract u := by rw [hPdef]; rfl
  have hPb : P.b = Int.fract v := by rw [hPdef]; rfl
  have hPa' : P'.a = (Work.Landing.angDouble)^[2 * k] u := by rw [hP'def]; rfl
  have hPb' : P'.b = (Work.Landing.angDouble)^[2 * k] v := by rw [hP'def]; rfl
  have hPy : P.y = y := by rw [hPdef]; rfl
  have hP'y : P'.y = y := by rw [hP'def]; rfl
  -- ## The far side of `P` is the far side of the given pair `(u,v)`
  have hside : Work.EL.pairSide P
      = Work.EL.pairSide (Work.LandLeaves.mkPair hN hL_u hL_v) := by
    rw [hPdef, Work.EL.pairSide_eq, Work.EL.pairSide_eq]
    show Work.EL.RawPair.side hN (⟨Int.fract u, Int.fract v, y⟩ : Work.EL.RawPair)
      = Work.EL.RawPair.side hN (⟨u, v, y⟩ : Work.EL.RawPair)
    have h1 : (⟨u, v, y⟩ : Work.EL.RawPair)
        = (⟨Int.fract u + (⌊u⌋ : ℝ), Int.fract v + (⌊v⌋ : ℝ), y⟩ : Work.EL.RawPair) := by
      rw [Int.fract_add_floor u, Int.fract_add_floor v]
    rw [h1]
    exact (Work.LandLeaves.InArcHard.Core.rawSide_add_int_aux hN (Int.fract u) (Int.fract v) y
      ⌊u⌋ ⌊v⌋).symm
  -- ## Non-degeneracy
  have hndP : Work.EL.arcLen P.a P.b ≠ 0 := by
    rw [hPa, hPb, Work.EL.arcLen, Work.LandLeaves.InArcHard.Core.fract_fract_sub_eq u v]
    exact hnd
  have hndP' : Work.EL.arcLen P'.a P'.b ≠ 0 := by
    rw [hPa', hPb']
    exact Work.LandLeaves.InArcHard.Core.fract_sub_angDouble_ne_zero_mndl hφ hk hinj hu hv hnd
  have hS : Work.EL.PairSides hN P :=
    Work.ELTop.pairSides hN Work.TopJordan.jordanForm P hndP
  have hS' : Work.EL.PairSides hN P' :=
    Work.ELTop.pairSides hN Work.TopJordan.jordanForm P' hndP'
  have hPab : P.a ≠ P.b := by
    rw [hPa, hPb]
    intro h
    refine hnd ?_
    rw [← Work.LandLeaves.InArcHard.Core.fract_fract_sub_eq u v, h]
    simp [Work.EL.arcLen]
  -- ## The witnesses for the `4^k`-congruence
  have hwit_u : ∃ m : ℤ, P'.a = (4 : ℝ) ^ k * P.a + m := by
    rw [hPa', hPa]
    refine ⟨(4 : ℤ) ^ k * ⌊u⌋ - ⌊(4 : ℝ) ^ k * u⌋, ?_⟩
    rw [Work.LandLeaves.angDouble_iterate_two_mul hk u]
    push_cast
    exact Work.LandLeaves.InArcHard.Core.fract_mul_eq ((4 : ℝ) ^ k) u
  have hwit_v : ∃ m : ℤ, P'.b = (4 : ℝ) ^ k * P.b + m := by
    rw [hPb', hPb]
    refine ⟨(4 : ℤ) ^ k * ⌊v⌋ - ⌊(4 : ℝ) ^ k * v⌋, ?_⟩
    rw [Work.LandLeaves.angDouble_iterate_two_mul hk v]
    push_cast
    exact Work.LandLeaves.InArcHard.Core.fract_mul_eq ((4 : ℝ) ^ k) v
  -- ## The local preimage identity at `y`
  have hPTa : ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball y ε →
      Work.LandLeaves.InArcHard.Core.tauC c k z ∈ Work.EL.paramRay hN P'.a →
      z ∈ Work.EL.paramRay hN P.a := by
    obtain ⟨ε, hε, h⟩ :=
      Work.LandLeaves.InArcHard.Core.tauC_preimage_tail_aux_mndl hN hφ hfix hlocal hacc_u'
    refine ⟨ε, hε, fun z hz hmem => h z hz P'.a ?_ hmem⟩
    rw [← hPa]
    exact hwit_u
  have hPTb : ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball y ε →
      Work.LandLeaves.InArcHard.Core.tauC c k z ∈ Work.EL.paramRay hN P'.b →
      z ∈ Work.EL.paramRay hN P.b := by
    obtain ⟨ε, hε, h⟩ :=
      Work.LandLeaves.InArcHard.Core.tauC_preimage_tail_aux_mndl hN hφ hfix hlocal hacc_v'
    refine ⟨ε, hε, fun z hz hmem => h z hz P'.b ?_ hmem⟩
    rw [← hPb]
    exact hwit_v
  -- ## The local angle transfer
  have hPaIco : P.a ∈ Set.Ico (0 : ℝ) 1 := by
    rw [hPa]
    exact ⟨Int.fract_nonneg u, Int.fract_lt_one u⟩
  have hPbIco : P.b ∈ Set.Ico (0 : ℝ) 1 := by
    rw [hPb]
    exact ⟨Int.fract_nonneg v, Int.fract_lt_one v⟩
  have hLA : ∀ p : ℂ, p ∈ Work.EL.paramRay hN P.a ∪ Work.EL.paramRay hN P.b → ∃ δ > 0,
      ∀ z : ℂ, z ∈ Metric.ball p δ → z ∉ Work.EL.pairCurve P →
        Work.LandLeaves.InArcHard.Core.tauC c k z ∉ Work.EL.pairCurve P' ∧
        (z ∈ Work.EL.pairSide P ↔
          Work.LandLeaves.InArcHard.Core.tauC c k z ∈ Work.EL.pairSide P') :=
    fun p hp =>
      Work.LandLeaves.InArcHard.Core.localAngleGen_lift hN hφ hk P P' hS hS'
        hPaIco hPbIco hPab hwit_u hwit_v hndP' hp
  -- ## The clopen argument
  obtain ⟨ε, hεpos, hε⟩ :=
    Work.LandLeaves.InArcHard.Core.cop_sides_gen_mndl hN hk hfix hlocal P P' hPy hP'y hS hS' hndP' hPTa hPTb hLA
  refine ⟨ε, hεpos, fun z hz hzb => ?_⟩
  have hzside : z ∈ Work.EL.pairSide P := by
    rw [hside]
    exact hz
  have hzmem : z ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hzb
  have hznot : z ∉ Work.EL.pairCurve P := by
    intro hc
    exact (connectedComponentIn_subset (Work.EL.pairCurve P)ᶜ
      (Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2) hzside) hc
  have hres : Work.LandLeaves.InArcHard.Core.tauC c k z ∈ Work.EL.pairSide P' :=
    ((hε z hzmem hznot).mp) hzside
  rw [Work.LandLeaves.InArcHard.Core.tauC_apply] at hres
  exact hres

/-- **The `2k`-fold angle map is injective modulo `1` on the type of `y`.**  If two angles `p`,
`q` whose rays both land at the repelling periodic point `y` are incongruent modulo `1`, then so
are their images. -/
theorem image_fract_ne_zero_mndl {p q : ℝ} (hφ : Work.ParamRays.IsDynBottcher c φ)
    (hk : 0 < k)
    (hinj : ∀ θ θ' : ℝ, Work.Landing.rayAccum c φ θ = {y} →
      Work.Landing.rayAccum c φ θ' = {y} →
      (∃ m : ℤ, (4 : ℝ) ^ k * θ = (4 : ℝ) ^ k * θ' + m) → ∃ mm : ℤ, θ = θ' + mm)
    (hp : Work.Landing.rayAccum c φ p = {y}) (hq : Work.Landing.rayAccum c φ q = {y})
    (hnd : Int.fract (q - p) ≠ 0) :
    Int.fract ((Work.Landing.angDouble)^[2 * k] q - (Work.Landing.angDouble)^[2 * k] p) ≠ 0 := by
  intro h0
  obtain ⟨m, hm⟩ := Int.fract_eq_zero_iff.mp h0
  have hkey : ∃ m' : ℤ, (4 : ℝ) ^ k * q = (4 : ℝ) ^ k * p + (m' : ℝ) := by
    refine ⟨m + ⌊(4 : ℝ) ^ k * q⌋ - ⌊(4 : ℝ) ^ k * p⌋, ?_⟩
    have f1 : (4 : ℝ) ^ k * p - Int.fract ((4 : ℝ) ^ k * p) = (⌊(4 : ℝ) ^ k * p⌋ : ℝ) :=
      Int.self_sub_fract _
    have f2 : (4 : ℝ) ^ k * q - Int.fract ((4 : ℝ) ^ k * q) = (⌊(4 : ℝ) ^ k * q⌋ : ℝ) :=
      Int.self_sub_fract _
    rw [← Work.LandLeaves.angDouble_iterate_two_mul hk q] at f2
    rw [← Work.LandLeaves.angDouble_iterate_two_mul hk p] at f1
    push_cast
    linarith
  obtain ⟨mm, hmm⟩ :=
    hinj q p hq hp hkey
  have hmm' : q - p = (mm : ℝ) := by linarith
  rw [hmm', Int.fract_intCast] at hnd
  exact hnd rfl

/-- **Cyclic-order preservation of the `2k`-fold angle map, given the sector transfer.**

If the second return map carries the far side of a co-landing pair near `y` into the far side of
the pair of the image angles (`Work.LandLeaves.InArcHard.sectorTransfer`), then the `2k`-fold
angle map preserves the cyclic betweenness on the type of `y`. -/
theorem ccBet_angDouble_of_sectorTransfer_mndl (hφ : Work.ParamRays.IsDynBottcher c φ)
    (hfix : (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] y = y) (hk : 0 < k)
    (hlocal : ∃ (r r' : ℝ) (g : ℂ → ℂ), 0 < r ∧ 0 < r' ∧ ∀ z : ℂ,
      ‖z - y‖ ≤ r → ‖Work.LandLeaves.InArcHard.Core.tauC c k z - y‖ ≤ r' → g (Work.LandLeaves.InArcHard.Core.tauC c k z) = z)
    (hinj : ∀ θ θ' : ℝ, Work.Landing.rayAccum c φ θ = {y} →
      Work.Landing.rayAccum c φ θ' = {y} →
      (∃ m : ℤ, (4 : ℝ) ^ k * θ = (4 : ℝ) ^ k * θ' + m) → ∃ mm : ℤ, θ = θ' + mm)
    {a b x : ℝ} (ha : Work.Landing.rayAccum c φ a = {y})
    (hb : Work.Landing.rayAccum c φ b = {y}) (hx : Work.Landing.rayAccum c φ x = {y})
    (hab : Work.LandLeaves.ccBet a b x) :
    Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b) ((Work.Landing.angDouble)^[2 * k] x) := by
  -- the non-degeneracies of the source triple
  have hp : 0 < Int.fract (b - a) := lt_trans hab.1 hab.2
  have hxapos : 0 < Int.fract (x - a) := hab.1
  have hxbpos : 0 < Int.fract (x - b) := by
    have h := Work.LandLeaves.fract_arc_eq a b x hab
    linarith [Int.fract_lt_one (b - a)]
  -- normalise the source pair
  set b' : ℝ := a + Int.fract (b - a) with hb'def
  have hb'eq : b = b' + (⌊b - a⌋ : ℝ) := by
    have h1 := Int.fract_add_floor (b - a); rw [hb'def]; linarith
  have hlt1 : a < b' := by rw [hb'def]; linarith
  have hlt2 : b' < a + 1 := by rw [hb'def]; linarith [Int.fract_lt_one (b - a)]
  have hnd : Int.fract (b' - a) ≠ 0 := by
    have h : b' - a = Int.fract (b - a) := by rw [hb'def]; ring
    rw [h, Int.fract_fract]; exact ne_of_gt hp
  have hacc_b' : Work.Landing.rayAccum c φ b' = {y} := by
    have hb'' : Work.Landing.rayAccum c φ (b' + (⌊b - a⌋ : ℝ)) = {y} := by
      rw [← hb'eq]; exact hb
    rwa [Work.FSeed.rayAccum_add_int c φ b' ⌊b - a⌋] at hb''
  have hcc : Work.LandLeaves.ccBet a b' x := by
    have h : Work.LandLeaves.ccBet a (b' + (⌊b - a⌋ : ℝ)) x := by rw [← hb'eq]; exact hab
    exact (ccBet_shift_mid a b' x ⌊b - a⌋).mp h
  -- the angle map is injective modulo `1` on the type
  have hσb_eq : (Work.Landing.angDouble)^[2 * k] b' = (Work.Landing.angDouble)^[2 * k] b := by
    have h : b' = b + ((-⌊b - a⌋ : ℤ) : ℝ) := by
      push_cast
      linarith [hb'eq]
    rw [h, angDouble_iterate_two_mul_add_int' hk b (-⌊b - a⌋)]
  have hnd_ab : Int.fract ((Work.Landing.angDouble)^[2 * k] b - (Work.Landing.angDouble)^[2 * k] a)
      ≠ 0 := image_fract_ne_zero_mndl hφ hk hinj ha hb (ne_of_gt hp)
  have hnd_ax : Int.fract ((Work.Landing.angDouble)^[2 * k] x - (Work.Landing.angDouble)^[2 * k] a)
      ≠ 0 := image_fract_ne_zero_mndl hφ hk hinj ha hx (ne_of_gt hxapos)
  have hnd_bx : Int.fract ((Work.Landing.angDouble)^[2 * k] x - (Work.Landing.angDouble)^[2 * k] b)
      ≠ 0 := image_fract_ne_zero_mndl hφ hk hinj hb hx (ne_of_gt hxbpos)
  have hnd_ax' : Int.fract ((Work.Landing.angDouble)^[2 * k] x
      - (Work.Landing.angDouble)^[2 * k] a) ≠ 0 := hnd_ax
  have hnd_bx' : Int.fract ((Work.Landing.angDouble)^[2 * k] x
      - (Work.Landing.angDouble)^[2 * k] b') ≠ 0 := by
    rw [hσb_eq]; exact hnd_bx
  have hnd_ab' : Int.fract ((Work.Landing.angDouble)^[2 * k] b'
      - (Work.Landing.angDouble)^[2 * k] a) ≠ 0 := by
    rw [hσb_eq]; exact hnd_ab
  -- the transfer
  set hN : Work.EL.DynB c φ := Work.LandLeaves.dynBNakane hφ with hNdef
  obtain ⟨ε, hεpos, htr⟩ := sectorTransfer_mndl hφ hfix hk hlocal hinj ha hacc_b' hnd
  -- the source ray lies in the far side of the source pair
  have hsub : Work.EL.paramRay hN x ⊆
      Work.EL.pairSide (Work.LandLeaves.mkPair hN (landsN_of_rayAccum'' hφ ha)
        (landsN_of_rayAccum'' hφ hacc_b')) :=
    Work.LandLeaves.paramRay_subset_pairSide_of_ccBet hN (landsN_of_rayAccum'' hφ ha)
      (landsN_of_rayAccum'' hφ hacc_b') hlt1 hlt2 hcc
  -- a point of the source ray close to `y`
  have hxN : Work.EL.LandsN hN x y := landsN_of_rayAccum'' hφ hx
  haveI : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hev : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Ioi 1), (1 < t) ∧ ‖Work.EL.rayPt hN x t - y‖ < ε := by
    filter_upwards [self_mem_nhdsWithin, hxN.eventually (Metric.ball_mem_nhds y hεpos)]
      with t ht hb
    exact ⟨ht, by simpa [Metric.mem_ball, dist_eq_norm] using hb⟩
  obtain ⟨t, ht1, htε⟩ := hev.exists
  have hzmem : Work.EL.rayPt hN x t ∈
      Work.EL.pairSide (Work.LandLeaves.mkPair hN (landsN_of_rayAccum'' hφ ha)
        (landsN_of_rayAccum'' hφ hacc_b')) :=
    hsub (Work.EL.rayPt_mem_paramRay hN ht1)
  have himg := htr (Work.EL.rayPt hN x t) hzmem htε
  rw [← Work.LandLeaves.rayPt_iterate_angDouble hN hφ ht1] at himg
  -- the image ray is disjoint from the image pair curve
  have hray_curve : Work.EL.paramRay hN ((Work.Landing.angDouble)^[2 * k] x) ⊆
      (Work.EL.pairCurve (Work.LandLeaves.mkPair hN
        (landsN_of_rayAccum'' hφ (Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix ha))
        (landsN_of_rayAccum'' hφ
          (Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix hacc_b'))))ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff, Work.EL.mem_pairCurve_iff]
    push_neg
    refine ⟨?_, ?_, ?_⟩
    · intro hza
      have hne : ∀ m : ℤ, (Work.Landing.angDouble)^[2 * k] a
          ≠ (Work.Landing.angDouble)^[2 * k] x + m := by
        intro m hm
        refine hnd_ax' ?_
        have hneg : (Work.Landing.angDouble)^[2 * k] x - (Work.Landing.angDouble)^[2 * k] a
            = ((-m : ℤ) : ℝ) := by push_cast; linarith
        rw [hneg, Int.fract_intCast]
      exact Set.disjoint_left.mp (Work.ELTop.paramRay_disjoint hN hne) hz hza
    · intro hzy
      have hyK : y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN hxN
      exact (Work.EL.paramRay_subset_compl hN _ hz) (by rw [hzy]; exact hyK)
    · intro hzb
      have hne : ∀ m : ℤ, (Work.Landing.angDouble)^[2 * k] b'
          ≠ (Work.Landing.angDouble)^[2 * k] x + m := by
        intro m hm
        refine hnd_bx' ?_
        have hneg : (Work.Landing.angDouble)^[2 * k] x - (Work.Landing.angDouble)^[2 * k] b'
            = ((-m : ℤ) : ℝ) := by push_cast; linarith
        rw [hneg, Int.fract_intCast]
      exact Set.disjoint_left.mp (Work.ELTop.paramRay_disjoint hN hne) hz hzb
  -- hence the whole image ray lies in the far side of the image pair
  have htpow : 1 < t ^ (4 ^ k : ℕ) := one_lt_pow₀ ht1 (by positivity)
  have hray : Work.EL.paramRay hN ((Work.Landing.angDouble)^[2 * k] x) ⊆
      Work.EL.pairSide (Work.LandLeaves.mkPair hN
        (landsN_of_rayAccum'' hφ (Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix ha))
        (landsN_of_rayAccum'' hφ
          (Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix hacc_b'))) := by
    have hside : Work.EL.pairSide (Work.LandLeaves.mkPair hN
          (landsN_of_rayAccum'' hφ (Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix ha))
          (landsN_of_rayAccum'' hφ
            (Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix hacc_b')))
        = connectedComponentIn (Work.EL.pairCurve (Work.LandLeaves.mkPair hN
            (landsN_of_rayAccum'' hφ (Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix ha))
            (landsN_of_rayAccum'' hφ
              (Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix hacc_b'))))ᶜ
          (Work.EL.rayPt hN ((Work.Landing.angDouble)^[2 * k] x) (t ^ (4 ^ k : ℕ))) :=
      connectedComponentIn_eq himg
    intro z hz
    rw [hside]
    exact IsPreconnected.subset_connectedComponentIn
      (Work.ELTop.isPreconnected_paramRay hN ((Work.Landing.angDouble)^[2 * k] x))
      (Work.EL.rayPt_mem_paramRay hN htpow) hray_curve hz
  -- normalise the image pair
  have himgpos : 0 < Int.fract ((Work.Landing.angDouble)^[2 * k] b'
      - (Work.Landing.angDouble)^[2 * k] a) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hnd_ab')
  set mb : ℤ := -⌊(Work.Landing.angDouble)^[2 * k] b' - (Work.Landing.angDouble)^[2 * k] a⌋ with hmb
  have hnorm1 : (Work.Landing.angDouble)^[2 * k] a
      < (Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ) := by
    have h := Int.fract_add_floor ((Work.Landing.angDouble)^[2 * k] b'
      - (Work.Landing.angDouble)^[2 * k] a)
    rw [hmb]; push_cast; linarith
  have hnorm2 : (Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ)
      < (Work.Landing.angDouble)^[2 * k] a + 1 := by
    have h := Int.fract_add_floor ((Work.Landing.angDouble)^[2 * k] b'
      - (Work.Landing.angDouble)^[2 * k] a)
    have hlt := Int.fract_lt_one ((Work.Landing.angDouble)^[2 * k] b'
      - (Work.Landing.angDouble)^[2 * k] a)
    rw [hmb]; push_cast; linarith
  -- the same far side, expressed with the shifted image angle
  have hray_raw : Work.EL.paramRay hN ((Work.Landing.angDouble)^[2 * k] x) ⊆
      Work.EL.RawPair.side hN (⟨(Work.Landing.angDouble)^[2 * k] a,
        (Work.Landing.angDouble)^[2 * k] b', y⟩ : Work.EL.RawPair) := by
    simpa [Work.EL.pairSide_eq, Work.LandLeaves.mkPair] using hray
  have hray_norm : Work.EL.paramRay hN ((Work.Landing.angDouble)^[2 * k] x) ⊆
      Work.EL.RawPair.side hN (⟨(Work.Landing.angDouble)^[2 * k] a,
        (Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ), y⟩ : Work.EL.RawPair) := by
    rw [side_add_int (y := y) hN ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b') mb]
    exact hray_raw
  -- the angle–side dictionary, converse direction, for the normalised image pair
  have hsgN : Work.EL.LandsN hN ((Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ)) y := by
    have hacc : Work.Landing.rayAccum c φ ((Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ))
        = {y} := by
      rw [Work.FSeed.rayAccum_add_int]
      exact Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix hacc_b'
    exact (Work.ELTop.landsN_iff_landsAt hN hφ _ y).mpr
      (Work.LandLeaves.landsAt_of_rayAccum hφ hacc)
  have hσaN : Work.EL.LandsN hN ((Work.Landing.angDouble)^[2 * k] a) y :=
    landsN_of_rayAccum'' hφ (Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix ha)
  have hσxN : Work.EL.LandsN hN ((Work.Landing.angDouble)^[2 * k] x) y :=
    landsN_of_rayAccum'' hφ (Work.LandLeaves.rayAccum_angDouble_singleton_mndl hφ hfix hx)
  have hnd_bx'' : Int.fract ((Work.Landing.angDouble)^[2 * k] x
      - ((Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ))) ≠ 0 := by
    rw [show (Work.Landing.angDouble)^[2 * k] x
          - ((Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ))
        = ((Work.Landing.angDouble)^[2 * k] x - (Work.Landing.angDouble)^[2 * k] b')
          + ((-mb : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast]
    exact hnd_bx'
  have hnd_ab'' : Int.fract (((Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ))
      - (Work.Landing.angDouble)^[2 * k] a) ≠ 0 := by
    rw [show ((Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ))
          - (Work.Landing.angDouble)^[2 * k] a
        = ((Work.Landing.angDouble)^[2 * k] b' - (Work.Landing.angDouble)^[2 * k] a)
          + (mb : ℝ) by ring, Int.fract_add_intCast]
    exact hnd_ab'
  have hcc' : Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ)) ((Work.Landing.angDouble)^[2 * k] x) :=
    Work.LandLeaves.ccBet_of_paramRay_subset_pairSide hN Work.TopJordan.jordanForm hσaN hsgN
      hσxN hnorm1 hnorm2 hnd_ax' hnd_bx'' hnd_ab''
      (by simpa [Work.EL.pairSide_eq, Work.LandLeaves.mkPair] using hray_norm)
  -- undo the two normalisations
  have hcc'' : Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b') ((Work.Landing.angDouble)^[2 * k] x) :=
    (ccBet_shift_mid ((Work.Landing.angDouble)^[2 * k] a) ((Work.Landing.angDouble)^[2 * k] b')
      ((Work.Landing.angDouble)^[2 * k] x) mb).mp hcc'
  rw [hσb_eq] at hcc''
  exact hcc''

/-! ## A self-contained port of the forward orientation -/

/-- **Cyclic-order preservation of the `2k`-fold angle map**, from the local hypotheses. -/
theorem ccBet_angDouble_of_typeSet_mndl {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ} {a b x : ℝ}
    (hφ : Work.ParamRays.IsDynBottcher c φ)
    (hfix : (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] y = y) (hk : 0 < k)
    (hlocal : ∃ (r r' : ℝ) (g : ℂ → ℂ), 0 < r ∧ 0 < r' ∧ ∀ z : ℂ,
      ‖z - y‖ ≤ r → ‖Work.LandLeaves.InArcHard.Core.tauC c k z - y‖ ≤ r' →
      g (Work.LandLeaves.InArcHard.Core.tauC c k z) = z)
    (hinj : ∀ θ θ' : ℝ, Work.Landing.rayAccum c φ θ = {y} →
      Work.Landing.rayAccum c φ θ' = {y} →
      (∃ m : ℤ, (4 : ℝ) ^ k * θ = (4 : ℝ) ^ k * θ' + m) → ∃ mm : ℤ, θ = θ' + mm)
    (ha : Work.Landing.rayAccum c φ a = {y}) (hb : Work.Landing.rayAccum c φ b = {y})
    (hx : Work.Landing.rayAccum c φ x = {y}) (hab : Work.LandLeaves.ccBet a b x) :
    Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b) ((Work.Landing.angDouble)^[2 * k] x) :=
  ccBet_angDouble_of_sectorTransfer_mndl hφ hfix hk hlocal hinj ha hb hx hab

end

end Work.LandLeaves.InArcHard

namespace Work.MandelFinal.Quarter

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-- `Tsq c = tauC c 1`: the second return map of `T_c` is the first iterate of the holomorphic
second return map `tauC c 1 = (Tantibar c)^[2]`. -/
theorem tsq_eq_tauC_one (c z : ℂ) :
    Work.Landing.Tsq c z = Work.LandLeaves.InArcHard.Core.tauC c 1 z := by
  have h := congrFun (Work.LandLeaves.Tsq_eq_iterate_two c) z
  rw [h]
  show (Tantibar c)^[2] z = (Tantibar c)^[2 * 1] z
  norm_num

/-- The local left-inverse hypothesis, transported from `Tsq (1/4)` to `tauC (1/4) 1`. -/
theorem localInverse_tauC_one
    (hlocal : ∃ (r r' : ℝ) (g : ℂ → ℂ), 0 < r ∧ 0 < r' ∧ ∀ z : ℂ,
      ‖z - (1 / 2 : ℂ)‖ ≤ r → ‖Work.Landing.Tsq (1 / 4 : ℂ) z - (1 / 2 : ℂ)‖ ≤ r' →
      g (Work.Landing.Tsq (1 / 4 : ℂ) z) = z) :
    ∃ (r r' : ℝ) (g : ℂ → ℂ), 0 < r ∧ 0 < r' ∧ ∀ z : ℂ,
      ‖z - (1 / 2 : ℂ)‖ ≤ r →
      ‖Work.LandLeaves.InArcHard.Core.tauC (1 / 4 : ℂ) 1 z - (1 / 2 : ℂ)‖ ≤ r' →
      g (Work.LandLeaves.InArcHard.Core.tauC (1 / 4 : ℂ) 1 z) = z := by
  obtain ⟨r, r', g, hr, hr', hg⟩ := hlocal
  refine ⟨r, r', g, hr, hr', fun z hz hz' => ?_⟩
  have h : g (Work.Landing.Tsq (1 / 4 : ℂ) z) = z :=
    hg z hz (by rwa [← tsq_eq_tauC_one] at hz')
  rwa [tsq_eq_tauC_one] at h

/-- The injectivity-modulo-`1` hypothesis, transported from `landsAt` to `rayAccum`. -/
theorem injMod_rayAccum_quarter
    (hinj : ∀ θ θ' : ℝ, Work.Landing.landsAt (1 / 4 : ℂ) θ (1 / 2) →
      Work.Landing.landsAt (1 / 4 : ℂ) θ' (1 / 2) →
      (∃ m : ℤ, (4 : ℝ) * θ = (4 : ℝ) * θ' + m) → ∃ mm : ℤ, θ = θ' + mm)
    {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher (1 / 4 : ℂ) φ) :
    ∀ θ θ' : ℝ, Work.Landing.rayAccum (1 / 4 : ℂ) φ θ = {1 / 2} →
      Work.Landing.rayAccum (1 / 4 : ℂ) φ θ' = {1 / 2} →
      (∃ m : ℤ, (4 : ℝ) ^ 1 * θ = (4 : ℝ) ^ 1 * θ' + m) → ∃ mm : ℤ, θ = θ' + mm := by
  intro θ θ' hθ hθ' hkey
  refine hinj θ θ' ⟨φ, hφ, hθ⟩ ⟨φ, hφ, hθ'⟩ ?_
  simpa using hkey

/-- Cyclic-order preservation at the parabolic cusp: Goldberg-Milnor II Lemma 2.2 at c = 1/4, z = 1/2, with the second return map Tsq (1/4), whose angle map is t -> Int.fract (4 t). This is the port of the proved Work.LandLeaves.ccBet_angDouble_of_typeSet chain from a repelling periodic point of odd period k to this parabolic point (k = 1). Full port instructions are in Submission/Work/MandelFinal/Quarter/NOTES_cop_quarter.md in this workspace. -/
theorem ccBet_angDouble_two_quarter
    (hfix : Work.Landing.Tsq (1 / 4 : ℂ) (1 / 2) = 1 / 2)
    (hlocal : ∃ (r r' : ℝ) (g : ℂ → ℂ), 0 < r ∧ 0 < r' ∧ ∀ z : ℂ,
      ‖z - (1 / 2 : ℂ)‖ ≤ r → ‖Work.Landing.Tsq (1 / 4 : ℂ) z - (1 / 2 : ℂ)‖ ≤ r' →
      g (Work.Landing.Tsq (1 / 4 : ℂ) z) = z)
    (hinj : ∀ θ θ' : ℝ, Work.Landing.landsAt (1 / 4 : ℂ) θ (1 / 2) →
      Work.Landing.landsAt (1 / 4 : ℂ) θ' (1 / 2) →
      (∃ m : ℤ, (4 : ℝ) * θ = (4 : ℝ) * θ' + m) → ∃ mm : ℤ, θ = θ' + mm)
    {a b x : ℝ} (ha : Work.Landing.landsAt (1 / 4 : ℂ) a (1 / 2))
    (hb : Work.Landing.landsAt (1 / 4 : ℂ) b (1 / 2))
    (hx : Work.Landing.landsAt (1 / 4 : ℂ) x (1 / 2))
    (habc : Work.LandLeaves.ccBet a b x) :
    Work.LandLeaves.ccBet (Int.fract (4 * a)) (Int.fract (4 * b)) (Int.fract (4 * x)) := by
  -- a Böttcher coordinate for the cusp, common to the three angles
  obtain ⟨φa, hφa, hacca⟩ := ha
  obtain ⟨φb, hφb, haccb⟩ := hb
  obtain ⟨φx, hφx, haccx⟩ := hx
  have hacc_b : Work.Landing.rayAccum (1 / 4 : ℂ) φa b = {1 / 2} := by
    rw [Work.Landing.rayAccum_congr
      (φ := φa) (ψ := φb) (fun w hw => Work.ParamRays.isDynBottcher_unique hφa hφb hw) b,
      haccb]
  have hacc_x : Work.Landing.rayAccum (1 / 4 : ℂ) φa x = {1 / 2} := by
    rw [Work.Landing.rayAccum_congr
      (φ := φa) (ψ := φx) (fun w hw => Work.ParamRays.isDynBottcher_unique hφa hφx hw) x,
      haccx]
  -- the fixed-point identity in `tauC` form, and `0 < 1`
  have hfixT : Work.LandLeaves.InArcHard.Core.tauC (1 / 4 : ℂ) 1 (1 / 2) = 1 / 2 := by
    rw [← tsq_eq_tauC_one]
    exact hfix
  have hfix2 : (Tantibar (1 / 4 : ℂ))^[2 * 1] (1 / 2) = 1 / 2 := by
    show (Tantibar (1 / 4 : ℂ))^[2] (1 / 2) = 1 / 2
    rw [← Work.LandLeaves.Tsq_eq_iterate_two]
    exact hfix
  -- the ported chain at `c = 1/4`, `y = 1/2`, `k = 1`
  have hres := Work.LandLeaves.InArcHard.ccBet_angDouble_of_typeSet_mndl
    (c := (1 / 4 : ℂ)) (k := 1) (y := (1 / 2 : ℂ)) hφa hfix2 (by norm_num)
    (localInverse_tauC_one hlocal) (injMod_rayAccum_quarter hinj hφa)
    hacca hacc_b hacc_x habc
  -- the angle map of the second return map is `θ ↦ Int.fract (4 θ)`
  rw [Work.LandLeaves.angDouble_iterate_two_mul (k := 1) (by norm_num) a,
    Work.LandLeaves.angDouble_iterate_two_mul (k := 1) (by norm_num) b,
    Work.LandLeaves.angDouble_iterate_two_mul (k := 1) (by norm_num) x] at hres
  simpa using hres

end

end Work.MandelFinal.Quarter
