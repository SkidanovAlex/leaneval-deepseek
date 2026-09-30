import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.MChartAux
import Submission.Work.Cusp.exists_polarChartS
import Submission.Work.Cusp.isOpen_polarBox

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

open Set Topology
open Set.Notation

theorem isOpenEmbedding_cuspInvInner_polarBoxSect (v : Fin 5) (c : ℝ) (k : Fin 4) (W : Set E2)
    (hW : IsOpen W) :
    Topology.IsOpenEmbedding
      (fun q : {q : E4 // q ∈ polarBoxSect v c k W} => cuspInvInner v q.1) := by
  -- `Int.fract` is invariant under an integer translation of the argument
  have fract_fract_sub : ∀ (x d : ℝ), Int.fract (Int.fract x - d) = Int.fract (x - d) := by
    intro x d
    have h : x - d = (Int.fract x - d) + ((⌊x⌋ : ℤ) : ℝ) := by
      have h1 := Int.floor_add_fract x
      linarith
    rw [h, Int.fract_add_intCast]
  -- the open `w`-box `B` of the polar chart target
  set B : Set E4 := {q : E4 | q ∈ polarBox ∧ (!₂[q 2, q 3] : E2) ∈ W} with hBdef
  have hBopen : IsOpen B := by
    rw [hBdef]
    exact isOpen_polarBox.inter (hW.preimage (by fun_prop))
  have hBsub : B ⊆ polarBox := fun q hq => hq.1
  have hS : polarBoxSect v c k W = polarTargetS v c k B ∩ {q : E4 | q 0 < rJ} := by
    ext q
    simp only [polarBoxSect, polarTargetS, hBdef, Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  -- the (symmetric) polar chart as an open partial homeomorphism of the `(p,y)`-cover
  let e : OpenPartialHomeomorph E4 (E2 × E2) :=
    { toFun := cuspInvInner v
      invFun := fun z : E2 × E2 => ThetaPolarS v c z.1 z.2
      source := polarTargetS v c k B
      target := polarSourceS v c k B
      map_source' := by
        intro q hq
        obtain ⟨hqB, hqu, hqf⟩ := hq
        have hbox : q ∈ polarBox := hBsub hqB
        have hnrm := cuspInvInner_nrm_gt v q hbox
        refine ⟨?_, hnrm, ?_⟩
        · rw [wedgeS]
          refine ⟨lt_trans (by norm_num) hnrm, ?_⟩
          have hu : u (cuspInvInner v q).1 = Int.fract (uqOf v q) := cuspInvInner_uqOf v q hbox
          rw [hu, fract_fract_sub]
          exact hqf
        · rw [ThetaPolarS_cuspInvInner v c q hbox hqu]
          exact hqB
      map_target' := by
        intro z hz
        obtain ⟨hzw, hzn, hzB⟩ := hz
        refine ⟨hzB, ?_, ?_⟩
        · rw [uqOf_ThetaPolarS v c z.1 z.2]
          have h1 : uS c z.1 - c = Int.fract (u z.1 - c) := by rw [uS]; ring
          rw [h1, Set.mem_Ico]
          exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
        · rw [uqOf_ThetaPolarS v c z.1 z.2]
          have h1 : uS c z.1 - c = Int.fract (u z.1 - c) := by rw [uS]; ring
          have h2 : Int.fract (Int.fract (u z.1 - c)) = Int.fract (u z.1 - c) :=
            Int.fract_eq_self.mpr ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
          rw [h1, h2]
          exact hzw.2
      left_inv' := by
        intro q hq
        obtain ⟨hqB, hqu, _⟩ := hq
        exact ThetaPolarS_cuspInvInner v c q (hBsub hqB) hqu
      right_inv' := by
        intro z hz
        exact cuspInvInner_ThetaPolarS v c z.1 z.2
      continuousOn_toFun := (continuous_cuspInvInner v).continuousOn
      continuousOn_invFun := (ThetaPolarS_continuousOn v c k).mono (fun z hz => hz.1)
      open_source := isOpen_polarTargetS v c k B hBopen
      open_target := isOpen_polarSourceS v c k B hBopen }
  have hsub : polarBoxSect v c k W ⊆ e.source := by
    intro q hq
    rw [hS] at hq
    exact hq.1
  have hsOpen : IsOpen (e.source ↓∩ polarBoxSect v c k W) := by
    have hcont0 : Continuous (fun q : E4 => q 0) := PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0
    have hT : IsOpen {q : E4 | q 0 < rJ} := isOpen_Iio.preimage hcont0
    have heq : e.source ↓∩ polarBoxSect v c k W = e.source ↓∩ {q : E4 | q 0 < rJ} := by
      rw [hS]
      ext x
      constructor
      · intro hx
        exact hx.2
      · intro hx
        exact ⟨x.2, hx⟩
    rw [heq]
    exact hT.preimage continuous_subtype_val
  have hf : Topology.IsOpenEmbedding (e.source.domRestrict e) := e.isOpenEmbedding_restrict
  have h1 : Topology.IsOpenEmbedding (Set.inclusion hsub) :=
    Topology.IsOpenEmbedding.inclusion hsub hsOpen
  exact hf.comp h1

end Work.Cusp
