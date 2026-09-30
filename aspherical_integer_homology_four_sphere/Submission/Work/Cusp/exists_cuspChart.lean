import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.ThetaOuter_continuousOn
import Submission.Work.Cusp.ThetaOuter_injOn
import Submission.Work.Cusp.ThetaOuter_cuspInvOuter
import Submission.Work.Cusp.cuspInvOuter_ThetaOuter
import Submission.Work.Cusp.cuspInvOuter_continuousOn
import Submission.Work.Cusp.cuspInvOuter_mem_Sq
import Submission.Work.Cusp.cuspInvOuter_mem_cuspStratum
import Submission.Work.Cusp.isOpen_cuspBoxInterior
import Submission.Work.Cusp.isOpen_wedge
import Submission.Work.Cusp.collarHeight_mem
import Submission.Work.Cusp.collarHeight_strictAntiOn
import Submission.Work.Cusp.abs_le_nrm
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Real InnerProductSpace

namespace Work.Cusp

/-- **The layer parameter of a point of the box interior is in `(1/2, 1]`.**

If `Θ_v p y` lies in the open box `cuspBoxInterior v c δ`, then the layer parameter `‖p‖∞` lies in
`(1/2, 1]`.  Indeed the two height conditions of the box read
`s₁ < collarHeight ‖p‖∞ (β x) < s_J` with `x = cuspX v (u p) y`, while
`collarHeight (1/2) (β x) = s_J` and `collarHeight 1 (β x) = β x`; since `t ↦ collarHeight t (β x)`
is strictly decreasing (`β x < s_J`), the height being below `s_J` forces `‖p‖∞ > 1/2`, and the
box condition `β x < (Θ_v p y) 3 = collarHeight ‖p‖∞ (β x)` forces `‖p‖∞ < 1`. -/
private theorem boundsAux (v : Fin 5) (c : E3) (δ : ℝ) (p y : E2)
    (h : ThetaOuter v p y ∈ cuspBoxInterior v c δ) : (1/2 : ℝ) < nrm p ∧ nrm p ≤ 1 := by
  simp only [cuspBoxInterior, Set.mem_ofPred_eq] at h
  obtain ⟨-, -, hlt, -, -, hbeta⟩ := h
  have h3 : (ThetaOuter v p y) 3 = collarHeight (nrm p) (beta (cuspX v (u p) y)) := by
    simp [ThetaOuter, collarS]
  have hxOf : xOf (ThetaOuter v p y) = cuspX v (u p) y := by
    ext i; fin_cases i <;> simp [xOf, ThetaOuter]
  rw [h3] at hlt hbeta
  rw [hxOf] at hbeta
  set b : ℝ := beta (cuspX v (u p) y) with hb
  have hbpos : 0 < b := by rw [hb]; exact beta_pos _
  have hblt : b < sJ := lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  have hanti := collarHeight_strictAntiOn b hbpos hblt
  have hb_eq : collarHeight 1 b = b := by
    rw [collarHeight]
    have h : (2 * (1:ℝ) - 1) * Real.log b + (2 - 2 * (1:ℝ)) * Real.log sJ = Real.log b := by ring
    rw [h]; exact Real.exp_log hbpos
  have hhalf : collarHeight (1/2) b = sJ := by
    rw [collarHeight]
    have h : (2 * (1/2:ℝ) - 1) * Real.log b + (2 - 2 * (1/2:ℝ)) * Real.log sJ = Real.log sJ := by ring
    rw [h]; exact Real.exp_log (Real.exp_pos (1/2))
  constructor
  · have hlt' : collarHeight (nrm p) b < collarHeight (1/2) b := by rw [hhalf]; exact hlt
    exact (hanti.lt_iff_gt (Set.mem_univ (nrm p)) (Set.mem_univ (1/2))).mp hlt'
  · have hbeta' : collarHeight 1 b < collarHeight (nrm p) b := by rw [hb_eq]; exact hbeta
    have := (hanti.lt_iff_gt (Set.mem_univ (1:ℝ)) (Set.mem_univ (nrm p))).mp hbeta'
    linarith

/-- The open box interior is contained in the (closed at the ceiling) cusp source: the ceiling
condition `β x < s` of `cuspBoxInterior` is stronger than the condition `β x ≤ s` of `cuspSource`,
and the remaining conditions are the same (with `0 < outerU` replacing `0 ≤ outerU`). -/
private theorem cbiSubsetCs (v : Fin 5) (c : E3) (δ : ℝ) :
    cuspBoxInterior v c δ ⊆ cuspSource v c δ := by
  intro q hq
  simp only [cuspBoxInterior] at hq
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
  simp only [cuspSource, cuspBox]
  exact ⟨⟨h1, h2, h3, le_of_lt h4, h5⟩, le_of_lt h6⟩

/-- **Existence of the collar cusp chart.**  The chart `Φ` of the `v`-th cusp with box
`cuspBox v c δ` and wedge `k` is the restriction of the outer chart `ThetaOuter v` to the source
`{z | z.1 ∈ wedge k ∧ ThetaOuter v z.1 z.2 ∈ cuspBoxInterior v c δ}`, with inverse `cuspInvOuter v`
and target `cuspTargetI v c δ k`.

The two round trips are the content of the surrounding modules: `cuspInvOuter_ThetaOuter` (on the
collar, which is where the box interior lives by `boundsAux`) and `ThetaOuter_cuspInvOuter` (on the
cusp source, which contains the box interior by `cbiSubsetCs`).  Openness of the source and target
follows from `ThetaOuter_continuousOn_wedge` and `cuspInvOuter_continuousOn` together with the
openness of the wedge (`isOpen_wedge`) and of the box interior (`isOpen_cuspBoxInterior`). -/
theorem exists_cuspChart (v : Fin 5) (c : E3) (δ : ℝ) (k : Fin 4) :
    ∃ Φ : OpenPartialHomeomorph (E2 × E2) E4,
      Φ.source = {z | z.1 ∈ wedge k ∧ ThetaOuter v z.1 z.2 ∈ cuspBoxInterior v c δ} ∧
      Φ.target = cuspTargetI v c δ k ∧
        ∀ z, Φ z = ThetaOuter v z.1 z.2 := by
  set S : Set (E2 × E2) := {z | z.1 ∈ wedge k ∧ ThetaOuter v z.1 z.2 ∈ cuspBoxInterior v c δ} with hS
  set T : Set E4 := cuspTargetI v c δ k with hT
  have hbounds : ∀ z ∈ S, (1/2 : ℝ) < nrm z.1 ∧ nrm z.1 ≤ 1 := by
    intro z hz
    rw [hS] at hz
    exact boundsAux v c δ z.1 z.2 hz.2
  have hsq : ∀ z ∈ S, z.1 ∈ Sq := by
    intro z hz
    obtain ⟨h1, h2⟩ := hbounds z hz
    exact ⟨le_trans (abs_le_nrm _ 0) h2, le_trans (abs_le_nrm _ 1) h2⟩
  have hleft : ∀ z ∈ S, cuspInvOuter v (ThetaOuter v z.1 z.2) = z := by
    intro z hz
    obtain ⟨h1, h2⟩ := hbounds z hz
    exact cuspInvOuter_ThetaOuter v z.1 z.2 (hsq z hz) h1 h2
  have hright : ∀ q ∈ T, ThetaOuter v (cuspInvOuter v q).1 (cuspInvOuter v q).2 = q := by
    intro q hq
    rw [hT] at hq
    simp only [cuspTargetI, Set.mem_ofPred_eq] at hq
    exact ThetaOuter_cuspInvOuter v c δ q (cbiSubsetCs v c δ hq.1)
  refine ⟨{ toFun := fun z => ThetaOuter v z.1 z.2
            invFun := cuspInvOuter v
            source := S
            target := T
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            continuousOn_toFun := ?_
            continuousOn_invFun := ?_
            open_source := ?_
            open_target := ?_ }, ?_, ?_, ?_⟩
  · intro z hz
    rw [hT]
    simp only [cuspTargetI, Set.mem_ofPred_eq]
    rw [hS] at hz
    refine ⟨hz.2, ?_⟩
    rw [hleft z hz]
    exact hz.1
  · intro q hq
    rw [hT] at hq
    simp only [cuspTargetI, Set.mem_ofPred_eq] at hq
    rw [hS]
    refine ⟨hq.2, ?_⟩
    rw [hright q (by rw [hT]; exact hq)]
    exact hq.1
  · exact hleft
  · exact hright
  · exact (ThetaOuter_continuousOn_wedge v k).mono (fun z hz => by rw [hS] at hz; exact hz.1)
  · refine (cuspInvOuter_continuousOn v).mono ?_
    intro q hq
    rw [hT] at hq
    simp only [cuspTargetI, Set.mem_ofPred_eq] at hq
    simp only [cuspBoxInterior] at hq
    obtain ⟨-, hs1, -, -, -, -⟩ := hq.1
    exact lt_trans (by norm_num [s1] : (0:ℝ) < s1) hs1
  · rw [hS]
    have hs : IsOpen {z : E2 × E2 | z.1 ∈ wedge k} := (isOpen_wedge k).preimage continuous_fst
    have hcont : ContinuousOn (fun z : E2 × E2 => ThetaOuter v z.1 z.2) {z | z.1 ∈ wedge k} :=
      ThetaOuter_continuousOn_wedge v k
    have h := hcont.isOpen_inter_preimage hs (isOpen_cuspBoxInterior v c δ)
    convert h using 1
    ext z
    simp [Set.mem_preimage]
  · rw [hT]
    have hs : IsOpen {w : E2 × E2 | w.1 ∈ wedge k} := (isOpen_wedge k).preimage continuous_fst
    have hcont : ContinuousOn (cuspInvOuter v) (cuspBoxInterior v c δ) :=
      (cuspInvOuter_continuousOn v).mono (fun q hq => by
        simp only [cuspBoxInterior] at hq
        obtain ⟨-, hs1, -, -, -, -⟩ := hq
        exact lt_trans (by norm_num [s1] : (0:ℝ) < s1) hs1)
    have h := hcont.isOpen_inter_preimage (isOpen_cuspBoxInterior v c δ) hs
    convert h using 1
    ext q
    simp [cuspTargetI]
  · rfl
  · rfl
  · intro z; rfl

end Work.Cusp
