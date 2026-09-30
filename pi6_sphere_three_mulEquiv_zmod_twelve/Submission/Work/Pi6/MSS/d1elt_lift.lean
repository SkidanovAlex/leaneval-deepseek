import Mathlib
import Submission.Work.Pi6.MSS.e2FinalDefs
import Submission.Work.Pi6.MSS.evZ_d_transpose_vanishing
import Submission.Work.Pi6.MSS.E1D.exists_v_cycle
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The cycle of `F_s` attached to a cycle of the graded piece `gr_{s+1}` (transposed convention)

This is the degree-convention (`s + q`) transcription of `Work.Pi6.MSS.E1D.exists_v_cycle`: given a
cycle `w` of the graded piece `gr_{s+1} = F_{s+1}/F_s` in degree `(s+1) + q`, its lift
`grSecX 𝕜 p (s+1) ((s+1)+q) w` has a boundary lying in `F_s` (it is killed by the projection onto
the graded piece), so it is the image under the inclusion `F_s → F_{s+1}` of an element `v` of `F_s`
(unique, the inclusion being injective).  This `v` is a cycle, and so is its image in
`gr_s = F_s/F_{s-1}`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Pi6.MSS

noncomputable section

/-- Consecutive differentials of a chain complex of `𝕜`-modules kill every element. -/
private lemma d_comp_d_apply {𝕜 : Type} [Field 𝕜] (C : ChainComplex (ModuleCat 𝕜) ℕ) (i j k : ℕ)
    (x : ↥(C.X i)) :
    (ModuleCat.Hom.hom (C.d j k)) ((ModuleCat.Hom.hom (C.d i j)) x) = 0 := by
  have hdd := congrArg (fun (g : C.X i ⟶ C.X k) => g.hom x)
    (HomologicalComplex.d_comp_d C i j k)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using hdd

theorem d1elt_lift (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s q : ℕ)
    (w : ↥(Work.StemsB.fdZ 𝕜 (Work.Pi6.MSS.Kg 𝕜 p (s + 1)) ((s + 1) + q))) :
    ∃ v : ↥((Work.Pi6.MSS.Cc 𝕜 p (s + 1)).X (s + q)),
      (ModuleCat.Hom.hom ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)) s).f (s + q))) v
          = (ModuleCat.Hom.hom ((Work.Pi6.MSS.Cc 𝕜 p (s + 2)).d ((s + 1) + q) (s + q)))
              (Work.Pi6.MSS.grSecX 𝕜 p (s + 1) ((s + 1) + q)
                (w : (Work.Pi6.MSS.Kg 𝕜 p (s + 1)).X ((s + 1) + q))) ∧
      (ModuleCat.Hom.hom ((Work.Pi6.MSS.Cc 𝕜 p (s + 1)).d (s + q) ((s + q) - 1))) v = 0 ∧
      (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p s).d (s + q) ((s + q) - 1)))
          ((ModuleCat.Hom.hom ((Work.Pi6.MSS.Kgπ 𝕜 p s).f (s + q))) v) = 0 := by
  -- The boundary of the lift of `w` is killed by the projection onto the graded piece `gr_{s+1}`.
  have hb0 : (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kgπ 𝕜 p (s + 1)).f (s + q)))
      (ModuleCat.Hom.hom
        (((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj (s + 1)).d ((s + 1) + q) (s + q))
        ((Work.Pi6.MSS.grSecX 𝕜 p (s + 1) ((s + 1) + q))
          (w : (Work.Pi6.MSS.Kg 𝕜 p (s + 1)).X ((s + 1) + q)))) = 0 := by
    have hcomm := Work.SSSR.chainMap_comm_apply_elem (Work.Pi6.MSS.Kgπ 𝕜 p (s + 1))
      (i := (s + 1) + q) (j := s + q)
      ((Work.Pi6.MSS.grSecX 𝕜 p (s + 1) ((s + 1) + q))
        (w : (Work.Pi6.MSS.Kg 𝕜 p (s + 1)).X ((s + 1) + q)))
    rw [Work.Pi6.MSS.Kgπ_grSecX_apply 𝕜 p (s + 1) ((s + 1) + q)
      (w : (Work.Pi6.MSS.Kg 𝕜 p (s + 1)).X ((s + 1) + q))] at hcomm
    have hz0 : (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p (s + 1)).d ((s + 1) + q) (s + q)))
        (w : (Work.Pi6.MSS.Kg 𝕜 p (s + 1)).X ((s + 1) + q)) = 0 := by
      have hmem : (w : ↥((Work.Pi6.MSS.Kg 𝕜 p (s + 1)).X ((s + 1) + q)))
          ∈ LinearMap.ker (ModuleCat.Hom.hom
            ((Work.Pi6.MSS.Kg 𝕜 p (s + 1)).d ((s + 1) + q) (((s + 1) + q) - 1))) := w.2
      rw [show ((s + 1) + q) - 1 = s + q by omega] at hmem
      exact LinearMap.mem_ker.mp hmem
    exact hcomm.symm.trans hz0
  -- Hence it lies in `F_s`, so it has a preimage `v` under the inclusion `F_s → F_{s+1}`.
  have hmem : (ModuleCat.Hom.hom
        (((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj (s + 1)).d ((s + 1) + q) (s + q))
        ((Work.Pi6.MSS.grSecX 𝕜 p (s + 1) ((s + 1) + q))
          (w : (Work.Pi6.MSS.Kg 𝕜 p (s + 1)).X ((s + 1) + q))))
      ∈ LinearMap.range ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)) s).f
          (s + q)).hom := by
    apply Work.Pi6.MSS.ker_Kgπ_le_grIncl (𝕜 := 𝕜) p (s + 1) (s + q)
    exact LinearMap.mem_ker.mpr hb0
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hmem
  -- `v` is a cycle, since `d v` maps to `d (d (lift w)) = 0` under the injective inclusion.
  have hcyc : (ModuleCat.Hom.hom
      (((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj s).d (s + q)
        ((s + q) - 1))) v = 0 := by
    have h2 := Work.SSSR.chainMap_comm_apply_elem
      (Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)) s)
      (i := s + q) (j := (s + q) - 1) v
    rw [hv] at h2
    have hb0d : (ModuleCat.Hom.hom
        (((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj (s + 1)).d (s + q)
          ((s + q) - 1)))
        (ModuleCat.Hom.hom
          (((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj (s + 1)).d ((s + 1) + q) (s + q))
          ((Work.Pi6.MSS.grSecX 𝕜 p (s + 1) ((s + 1) + q))
            (w : (Work.Pi6.MSS.Kg 𝕜 p (s + 1)).X ((s + 1) + q)))) = 0 :=
      d_comp_d_apply ((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj (s + 1))
        ((s + 1) + q) (s + q) ((s + q) - 1)
        ((Work.Pi6.MSS.grSecX 𝕜 p (s + 1) ((s + 1) + q))
          (w : (Work.Pi6.MSS.Kg 𝕜 p (s + 1)).X ((s + 1) + q)))
    rw [hb0d] at h2
    have hmono : Mono ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)) s).f
        ((s + q) - 1)) := by
      have hmonoF : Mono (Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)) s) :=
        Work.SSSR.mono_serreChainFiltration_map 𝕜 (Work.Pi6.MSS.sF p)
          (Work.SSSR.natShift.map (homOfLE (Nat.le_succ s)))
      haveI := hmonoF
      infer_instance
    exact (ModuleCat.mono_iff_injective
      ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)) s).f
        ((s + q) - 1))).mp hmono (by rw [h2.symm, map_zero])
  -- The image of `v` in the graded piece `gr_s` is again a cycle, by the chain map property.
  have hkg : (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p s).d (s + q) ((s + q) - 1)))
      (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kgπ 𝕜 p s).f (s + q)) v) = 0 := by
    have h3 := Work.SSSR.chainMap_comm_apply_elem (Work.Pi6.MSS.Kgπ 𝕜 p s)
      (i := s + q) (j := (s + q) - 1) v
    rw [hcyc] at h3
    simpa using h3
  exact ⟨v, hv, hcyc, hkg⟩

end

end Work.Pi6.MSS
