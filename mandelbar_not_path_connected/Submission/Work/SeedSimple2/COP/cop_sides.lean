import Mathlib
import Submission.Work.SeedSimple2.Defs
import Submission.Work.SeedSimple2.COP.local_angle
import Submission.Work.SeedSimple2.COP.pti
import Submission.Work.SeedSimple2.COP.F_basics
import Submission.Work.SeedSimple2.COP.punctured_ball
import Submission.Work.ELTop.RigInput
import Submission.Work.ELTop.isClosed_pairCurve
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.paramRay_subset_pairSideNear

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.SeedSimple2.COP

/-- **`L6`: cyclic-order preservation, side form** (`NOTES_LEAD_mandelbar_rn0.md` §2, `L6`; the full design is in `Submission/Work/SeedSimple2/COP/NOTES_COP.md` §3 — read it first).

Near the parabolic point `z₁` and off the pair curve `P`, the second return map `F = (T_c)^10` maps the far side of `P` to the far side of the pair `P'` whose angles are the `F`-images of those of `P`, and the near side to the near side.

Proof design (clopen argument).
* `hS := Work.ELTop.pairSides d.hN hJ P hnd` and `hS' := Work.ELTop.pairSides d.hN hJ P' hnd'`, where `hnd : Work.EL.arcLen P.a P.b ≠ 0` comes from `hPa, hPb, hab` (`Work.ELTop.arcLen_ne_zero_of_lt` after normalizing `P.b` to `P.a + arcLen P.a P.b`).
* `ε := min ε₀ (min εa εb)` where `ε₀` is from `Work.SeedSimple2.COP.exists_injOn_F` (via `Work.SeedSimple2.COP.F_ne_z₁`) and `εa`, `εb` from `Work.SeedSimple2.COP.pti d P.lands_a` resp. `d P.lands_b` (rewrite `hPy`); set `Ω := Metric.ball d.z₁ ε \ {d.z₁}`, preconnected by `Work.SeedSimple2.COP.punctured_ball`.
* **Step 1.** For `z ∈ Ω` with `z ∉ Work.EL.pairCurve P`, also `Work.EL.F c z ∉ Work.EL.pairCurve P'`:  `Work.EL.F c z ≠ d.z₁` (`F_ne_z₁`), and `Work.EL.F c z ∈ Work.EL.paramRay d.hN P'.a` would give `Work.EL.F c z ∈ Work.EL.paramRay d.hN (1024 * P.a)` (`ha'` + `Work.ELTop.paramRay_add_int`), so `pti` forces `z ∈ Work.EL.paramRay d.hN P.a ⊆ Work.EL.pairCurve P` — contradiction (same for `P.b`).
* **Step 2.** `Good₀ := {z | z ∉ Work.EL.pairCurve P ∧ ((z ∈ Work.EL.pairSide P ∧ Work.EL.F c z ∈ Work.EL.pairSide P') ∨ (z ∈ Work.EL.pairSideNear P ∧ Work.EL.F c z ∈ Work.EL.pairSideNear P'))}` and `Bad := {z | z ∉ Work.EL.pairCurve P ∧ ((z ∈ Work.EL.pairSide P ∧ Work.EL.F c z ∈ Work.EL.pairSideNear P') ∨ (z ∈ Work.EL.pairSideNear P ∧ Work.EL.F c z ∈ Work.EL.pairSide P'))}` are open in `ℂ` (`Work.ELTop.isClosed_pairCurve`, `hS.isOpen_far`, `hS.isOpen_near`, `hS'.isOpen_far`, `hS'.isOpen_near`, continuity of `Work.EL.F c` = `Work.ELRig.differentiable_F`).
* **Step 3.** `Good := Good₀ ∪ ⋃ (p ∈ Ω ∩ Work.EL.pairCurve P), Metric.ball p (δ p)` with `δ p` from `Work.SeedSimple2.COP.local_angle d P P' hS hS' hPa hPb hab ha' hb' hnd'`; it is open, and `Disjoint Bad Good` (use `hS.disjoint`/`hS'.disjoint` and the equivalence of `local_angle`).
* **Step 4.** `Ω ⊆ Bad ∪ Good`: a point of `Ω ∩ Work.EL.pairCurve P` is not `d.z₁` (which lies on the curve), hence on `Work.EL.paramRay d.hN P.a ∪ Work.EL.paramRay d.hN P.b` (`Work.EL.mem_pairCurve_iff`, `hPy`), hence in its own ball; a point of `Ω ∖ Work.EL.pairCurve P` is in `Bad` or in `Good₀` by Step 1 and `hS.union_eq`/`hS'.union_eq`.
* **Step 5.** `Ω` preconnected plus open disjoint cover gives `Ω ⊆ Bad` or `Ω ⊆ Good` (e.g. `IsPreconnected.subset_or_subset_of_isOpen`, or the `subset_or_subset` version for closed sets applied to `isClopen`); and `Ω ⊄ Bad` because a ray point of level `s → 1⁺` on `Work.EL.paramRay d.hN P.a` lies in `Ω ∩ Work.EL.pairCurve P` (`P.lands_a`).  Hence `Bad ∩ Ω = ∅`, and for `z ∈ Metric.ball d.z₁ ε` with `z ∉ Work.EL.pairCurve P` (so `z ∈ Ω`, not in `Bad`, and by Step 1 `Work.EL.F c z ∉ Work.EL.pairCurve P'`) both points are in the same named side. -/
theorem cop_sides {c : ℂ} (d : Work.EL.RootParabolic c) (hJ : Work.Top.JordanForm)
    (P P' : Work.EL.CoPair d.hN) (hPy : P.y = d.z₁) (hP'y : P'.y = d.z₁)
    (hPa : P.a ∈ Set.Ioo (0:ℝ) 1) (hPb : P.b ∈ Set.Ioo (0:ℝ) 1) (hab : P.a ≠ P.b)
    (ha' : ∃ k : ℤ, P'.a = 1024 * P.a + k) (hb' : ∃ k : ℤ, P'.b = 1024 * P.b + k)
    (hnd' : Work.EL.arcLen P'.a P'.b ≠ 0) :
    ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball d.z₁ ε → z ∉ Work.EL.pairCurve P →
      (z ∈ Work.EL.pairSide P ↔ Work.EL.F c z ∈ Work.EL.pairSide P') := by
  -- ## Non-degeneracy and the two-sidedness of the two pairs
  have hnd : Work.EL.arcLen P.a P.b ≠ 0 := arcLen_ne_zero_of_mem_Ioo hPa hPb hab
  have hS : Work.EL.PairSides d.hN P := Work.ELTop.pairSides d.hN hJ P hnd
  have hS' : Work.EL.PairSides d.hN P' := Work.ELTop.pairSides d.hN hJ P' hnd'
  -- the two rays of `P` land at `z₁`
  have hland_a : Work.EL.LandsN d.hN P.a d.z₁ := by simpa [hPy] using P.lands_a
  have hland_b : Work.EL.LandsN d.hN P.b d.z₁ := by simpa [hPy] using P.lands_b
  -- ## The three radii
  obtain ⟨ε₀, hε₀pos, hFne_z₁⟩ := F_ne_z₁ d
  obtain ⟨εa, hεapos, hptia⟩ := pti d hland_a
  obtain ⟨εb, hεbpos, hptib⟩ := pti d hland_b
  set ε : ℝ := min ε₀ (min εa εb) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact lt_min hε₀pos (lt_min hεapos hεbpos)
  have hεε₀ : ε ≤ ε₀ := by rw [hεdef]; exact min_le_left _ _
  have hεεa : ε ≤ εa := by rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεεb : ε ≤ εb := by rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hball₀ : Metric.ball d.z₁ ε ⊆ Metric.ball d.z₁ ε₀ := Metric.ball_subset_ball hεε₀
  have hballa : Metric.ball d.z₁ ε ⊆ Metric.ball d.z₁ εa := Metric.ball_subset_ball hεεa
  have hballb : Metric.ball d.z₁ ε ⊆ Metric.ball d.z₁ εb := Metric.ball_subset_ball hεεb
  -- `z₁` lies on the pair curve of `P`
  have hz₁X : d.z₁ ∈ Work.EL.pairCurve P := by
    rw [Work.EL.mem_pairCurve_iff]
    exact Or.inr (Or.inl hPy.symm)
  -- ## Step 1: `F` creates no point of the curve of `P'`
  have step1 : ∀ z : ℂ, z ∈ Metric.ball d.z₁ ε → z ∉ Work.EL.pairCurve P →
      Work.EL.F c z ∉ Work.EL.pairCurve P' := by
    intro z hz hzX hFY
    have hzne : z ≠ d.z₁ := fun h1 => hzX (h1.symm ▸ hz₁X)
    have hFne : Work.EL.F c z ≠ d.z₁ := hFne_z₁ z (hball₀ hz) hzne
    rw [Work.EL.mem_pairCurve_iff] at hFY
    rcases hFY with h | h | h
    · obtain ⟨k, hk⟩ := ha'
      exact hzX (by
        rw [Work.EL.mem_pairCurve_iff]
        exact Or.inl (hptia z (hballa hz) P'.a ⟨k, hk⟩ h))
    · exact hFne (h.trans hP'y)
    · obtain ⟨k, hk⟩ := hb'
      exact hzX (by
        rw [Work.EL.mem_pairCurve_iff]
        exact Or.inr (Or.inr (hptib z (hballb hz) P'.b ⟨k, hk⟩ h)))
  -- ## Step 2: the good and the bad set
  set Good₀ : Set ℂ := {z : ℂ | z ∉ Work.EL.pairCurve P ∧
      ((z ∈ Work.EL.pairSide P ∧ Work.EL.F c z ∈ Work.EL.pairSide P') ∨
       (z ∈ Work.EL.pairSideNear P ∧ Work.EL.F c z ∈ Work.EL.pairSideNear P'))} with hGood₀
  set Bad : Set ℂ := {z : ℂ | z ∉ Work.EL.pairCurve P ∧
      ((z ∈ Work.EL.pairSide P ∧ Work.EL.F c z ∈ Work.EL.pairSideNear P') ∨
       (z ∈ Work.EL.pairSideNear P ∧ Work.EL.F c z ∈ Work.EL.pairSide P'))} with hBad
  set Ω : Set ℂ := Metric.ball d.z₁ ε \ {d.z₁} with hΩ
  -- ## Step 3: the thickening of the curve of `P` given by `local_angle`
  set TT : Set ℂ := {p : ℂ | p ∈ Metric.ball d.z₁ ε \ {d.z₁} ∧
      (p ∈ Work.EL.paramRay d.hN P.a ∨ p ∈ Work.EL.paramRay d.hN P.b)} with hTT
  have hδexists : ∀ p : TT, ∃ δ > 0, ∀ z : ℂ, z ∈ Metric.ball p.1 δ →
      z ∉ Work.EL.pairCurve P →
      Work.EL.F c z ∉ Work.EL.pairCurve P' ∧
      (z ∈ Work.EL.pairSide P ↔ Work.EL.F c z ∈ Work.EL.pairSide P') :=
    fun p => local_angle d P P' hS hS' hPa hPb hab ha' hb' hnd' p.2.2
  set δ : TT → ℝ := fun p => Classical.choose (hδexists p) with hδdef
  have hδpos : ∀ p : TT, 0 < δ p := fun p => by
    rw [hδdef]
    exact (Classical.choose_spec (hδexists p)).1
  have hδspec : ∀ p : TT, ∀ z : ℂ, z ∈ Metric.ball p.1 (δ p) →
      z ∉ Work.EL.pairCurve P →
      Work.EL.F c z ∉ Work.EL.pairCurve P' ∧
      (z ∈ Work.EL.pairSide P ↔ Work.EL.F c z ∈ Work.EL.pairSide P') := fun p => by
    rw [hδdef]
    exact (Classical.choose_spec (hδexists p)).2
  set Good : Set ℂ := Good₀ ∪ ⋃ p : TT, Metric.ball p.1 (δ p) with hGood
  -- ## Openness
  have hGood₀open : IsOpen Good₀ := by
    rw [hGood₀]
    have h1 : IsOpen {z : ℂ | z ∈ Work.EL.pairSide P ∧
        Work.EL.F c z ∈ Work.EL.pairSide P'} :=
      hS.isOpen_far.inter (hS'.isOpen_far.preimage (Work.ELRig.differentiable_F c).continuous)
    have h2 : IsOpen {z : ℂ | z ∈ Work.EL.pairSideNear P ∧
        Work.EL.F c z ∈ Work.EL.pairSideNear P'} :=
      hS.isOpen_near.inter (hS'.isOpen_near.preimage (Work.ELRig.differentiable_F c).continuous)
    have heq : {z : ℂ | z ∉ Work.EL.pairCurve P ∧
        ((z ∈ Work.EL.pairSide P ∧ Work.EL.F c z ∈ Work.EL.pairSide P') ∨
         (z ∈ Work.EL.pairSideNear P ∧ Work.EL.F c z ∈ Work.EL.pairSideNear P'))}
        = (Work.EL.pairCurve P)ᶜ ∩
          ({z : ℂ | z ∈ Work.EL.pairSide P ∧ Work.EL.F c z ∈ Work.EL.pairSide P'} ∪
           {z : ℂ | z ∈ Work.EL.pairSideNear P ∧ Work.EL.F c z ∈ Work.EL.pairSideNear P'}) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    rw [heq]
    exact (Work.ELTop.isClosed_pairCurve d.hN P).isOpen_compl.inter (h1.union h2)
  have hBadopen : IsOpen Bad := by
    rw [hBad]
    have h1 : IsOpen {z : ℂ | z ∈ Work.EL.pairSide P ∧
        Work.EL.F c z ∈ Work.EL.pairSideNear P'} :=
      hS.isOpen_far.inter (hS'.isOpen_near.preimage (Work.ELRig.differentiable_F c).continuous)
    have h2 : IsOpen {z : ℂ | z ∈ Work.EL.pairSideNear P ∧
        Work.EL.F c z ∈ Work.EL.pairSide P'} :=
      hS.isOpen_near.inter (hS'.isOpen_far.preimage (Work.ELRig.differentiable_F c).continuous)
    have heq : {z : ℂ | z ∉ Work.EL.pairCurve P ∧
        ((z ∈ Work.EL.pairSide P ∧ Work.EL.F c z ∈ Work.EL.pairSideNear P') ∨
         (z ∈ Work.EL.pairSideNear P ∧ Work.EL.F c z ∈ Work.EL.pairSide P'))}
        = (Work.EL.pairCurve P)ᶜ ∩
          ({z : ℂ | z ∈ Work.EL.pairSide P ∧ Work.EL.F c z ∈ Work.EL.pairSideNear P'} ∪
           {z : ℂ | z ∈ Work.EL.pairSideNear P ∧ Work.EL.F c z ∈ Work.EL.pairSide P'}) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    rw [heq]
    exact (Work.ELTop.isClosed_pairCurve d.hN P).isOpen_compl.inter (h1.union h2)
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
    · have hFzX : Work.EL.F c z ∉ Work.EL.pairCurve P' := step1 z hzball hzX
      have hzAB : z ∈ Work.EL.pairSide P ∪ Work.EL.pairSideNear P := by
        rw [hS.union_eq]; exact hzX
      have hFAB : Work.EL.F c z ∈ Work.EL.pairSide P' ∪ Work.EL.pairSideNear P' := by
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
    exact isPreconnected_ball_diff_singleton d.z₁ ε
  have hor : Ω ⊆ Bad ∨ Ω ⊆ Good := hpre.subset_or_subset hBadopen hGoodopen hdisj hcover
  have hnotBad : ¬ Ω ⊆ Bad := by
    intro hsub
    obtain ⟨s₀, hs₀, hnear⟩ := exists_level_ball_of_landsN d.hN hland_a hεpos
    set s : ℝ := (1 + s₀) / 2 with hsdef
    have hs1 : 1 < s := by rw [hsdef]; linarith
    have hss : s < s₀ := by rw [hsdef]; linarith
    have hzball : Work.EL.rayPt d.hN P.a s ∈ Metric.ball d.z₁ ε := hnear s ⟨hs1, hss⟩
    have hzK : Work.EL.rayPt d.hN P.a s ∉ Work.EL.K c := Work.EL.rayPt_notMem_K d.hN hs1
    have hz₁K : d.z₁ ∈ Work.EL.K c := Work.ELTop.landsN_mem_K d.hN hland_a
    have hzne : Work.EL.rayPt d.hN P.a s ≠ d.z₁ := fun h1 => hzK (h1.symm ▸ hz₁K)
    have hzΩ : Work.EL.rayPt d.hN P.a s ∈ Ω := by
      rw [hΩ]
      exact ⟨hzball, by simpa using hzne⟩
    have hzBad : Work.EL.rayPt d.hN P.a s ∈ Bad := hsub hzΩ
    rw [hBad] at hzBad
    exact hzBad.1 (by
      rw [Work.EL.mem_pairCurve_iff]
      exact Or.inl (Work.EL.rayPt_mem_paramRay d.hN hs1))
  have hΩG : Ω ⊆ Good := hor.resolve_left hnotBad
  -- ## The conclusion
  refine ⟨ε, hεpos, ?_⟩
  intro z hzball hzX
  have hzne : z ≠ d.z₁ := fun h1 => hzX (h1.symm ▸ hz₁X)
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

end Work.SeedSimple2.COP
