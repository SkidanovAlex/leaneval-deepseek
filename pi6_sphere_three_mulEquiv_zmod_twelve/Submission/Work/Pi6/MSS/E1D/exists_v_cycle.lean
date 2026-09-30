import Mathlib
import Submission.Work.Pi6.MSS.e1DualFull
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The cycle of `F_s` attached to a cycle of the graded piece `gr_{s+1}`

Given a cycle `c` of the graded piece `gr_{s+1} = F_{s+1}/F_s` in degree `q + (s+1)`, its lift
`grSecX 𝕜 p (s+1) (q+(s+1)) (iCycles c)` has a boundary which lies in `F_s` (because `c` is a
cycle), so it is the image under the inclusion `F_s → F_{s+1}` of an element `v` of `F_s` (unique,
since the inclusion is injective).  This `v` is a cycle, and so is its image in `gr_s = F_s/F_{s-1}`.

This file records the existence of such a `v` with the three properties needed to apply the
elementwise description of the connecting map `d¹`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Pi6.MSS.E1D

noncomputable section

/-- Consecutive differentials of a chain complex of `𝕜`-modules kill every element. -/
private lemma d_comp_d_apply {𝕜 : Type} [Field 𝕜] (C : ChainComplex (ModuleCat 𝕜) ℕ) (i j k : ℕ)
    (x : ↥(C.X i)) :
    (ModuleCat.Hom.hom (C.d j k)) ((ModuleCat.Hom.hom (C.d i j)) x) = 0 := by
  have hdd := congrArg (fun (g : C.X i ⟶ C.X k) => g.hom x)
    (HomologicalComplex.d_comp_d C i j k)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using hdd

/-- **The existence of the cycle of `F_s` whose image under `F_s → F_{s+1}` is the boundary of a
lift of `c`.** -/
theorem exists_v_cycle {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (q s : ℕ)
    (c : ↥((Work.Pi6.MSS.Kg 𝕜 p (s+1)).cycles (q + (s+1)))) :
    ∃ v : ↥(((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj s).X (q + s)),
      (ModuleCat.Hom.hom
          ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)) s).f (q + s)) v
        = ModuleCat.Hom.hom
            (((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj (s+1)).d (q + (s+1)) (q + s))
            ((Work.Pi6.MSS.grSecX 𝕜 p (s+1) (q + (s+1)))
              (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p (s+1)).iCycles (q + (s+1))) c)))
      ∧ (ModuleCat.Hom.hom
            (((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj s).d (q + s)
              ((ComplexShape.down ℕ).next (q + s))) v = 0)
      ∧ (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p s).d (q + s)
            ((ComplexShape.down ℕ).next (q + s)))
            (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kgπ 𝕜 p s).f (q + s)) v) = 0) := by
  -- The boundary of the lift of `c` is killed by the projection onto the graded piece `gr_{s+1}`.
  have hb0 : (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kgπ 𝕜 p (s+1)).f (q + s)))
      (ModuleCat.Hom.hom
        (((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj (s+1)).d (q + (s+1)) (q + s))
        ((Work.Pi6.MSS.grSecX 𝕜 p (s+1) (q + (s+1)))
          (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p (s+1)).iCycles (q + (s+1))) c))) = 0 := by
    have hcomm := Work.SSSR.chainMap_comm_apply_elem (Work.Pi6.MSS.Kgπ 𝕜 p (s+1))
      (i := q + (s+1)) (j := q + s)
      ((Work.Pi6.MSS.grSecX 𝕜 p (s+1) (q + (s+1)))
        (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p (s+1)).iCycles (q + (s+1))) c))
    rw [Work.Pi6.MSS.Kgπ_grSecX_apply 𝕜 p (s+1) (q + (s+1))
      (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p (s+1)).iCycles (q + (s+1))) c)] at hcomm
    have hz0 : (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p (s+1)).d (q + (s+1)) (q + s)))
        (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p (s+1)).iCycles (q + (s+1))) c) = 0 := by
      have h := congrArg (fun (g : (Work.Pi6.MSS.Kg 𝕜 p (s+1)).cycles (q + (s+1)) ⟶
          (Work.Pi6.MSS.Kg 𝕜 p (s+1)).X (q + s)) => g.hom c)
        (HomologicalComplex.iCycles_d (Work.Pi6.MSS.Kg 𝕜 p (s+1)) (q + (s+1)) (q + s))
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using h
    exact hcomm.symm.trans hz0
  -- Hence it lies in `F_s`, so it has a preimage `v` under the inclusion `F_s → F_{s+1}`.
  have hmem : (ModuleCat.Hom.hom
        (((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj (s+1)).d (q + (s+1)) (q + s))
        ((Work.Pi6.MSS.grSecX 𝕜 p (s+1) (q + (s+1)))
          (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p (s+1)).iCycles (q + (s+1))) c)))
      ∈ LinearMap.range ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)) s).f
          (q + s)).hom := by
    apply Work.Pi6.MSS.ker_Kgπ_le_grIncl (𝕜 := 𝕜) p (s+1) (q + s)
    exact LinearMap.mem_ker.mpr hb0
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hmem
  -- `v` is a cycle, since `d v` maps to `d (d (lift c)) = 0` under the injective inclusion.
  have hcyc : (ModuleCat.Hom.hom
      (((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj s).d (q + s)
        ((ComplexShape.down ℕ).next (q + s)))) v = 0 := by
    have h2 := Work.SSSR.chainMap_comm_apply_elem
      (Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)) s)
      (i := q + s) (j := (ComplexShape.down ℕ).next (q + s)) v
    rw [hv] at h2
    have hb0d : (ModuleCat.Hom.hom
        (((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj (s+1)).d (q + s)
          ((ComplexShape.down ℕ).next (q + s))))
        (ModuleCat.Hom.hom
          (((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj (s+1)).d (q + (s+1)) (q + s))
          ((Work.Pi6.MSS.grSecX 𝕜 p (s+1) (q + (s+1)))
            (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p (s+1)).iCycles (q + (s+1))) c))) = 0 :=
      d_comp_d_apply ((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)).obj (s+1))
        (q + (s+1)) (q + s) ((ComplexShape.down ℕ).next (q + s))
        ((Work.Pi6.MSS.grSecX 𝕜 p (s+1) (q + (s+1)))
          (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p (s+1)).iCycles (q + (s+1))) c))
    rw [hb0d] at h2
    have hmono : Mono ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)) s).f
        ((ComplexShape.down ℕ).next (q + s))) := by
      have hmonoF : Mono (Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)) s) :=
        Work.SSSR.mono_serreChainFiltration_map 𝕜 (Work.Pi6.MSS.sF p)
          (Work.SSSR.natShift.map (homOfLE (Nat.le_succ s)))
      haveI := hmonoF
      infer_instance
    exact (ModuleCat.mono_iff_injective
      ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.sF p)) s).f
        ((ComplexShape.down ℕ).next (q + s)))).mp hmono (by rw [h2.symm, map_zero])
  -- The image of `v` in the graded piece `gr_s` is again a cycle, by the chain map property.
  have hkg : (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p s).d (q + s)
      ((ComplexShape.down ℕ).next (q + s))))
      (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kgπ 𝕜 p s).f (q + s)) v) = 0 := by
    have h3 := Work.SSSR.chainMap_comm_apply_elem (Work.Pi6.MSS.Kgπ 𝕜 p s)
      (i := q + s) (j := (ComplexShape.down ℕ).next (q + s)) v
    rw [hcyc] at h3
    simpa using h3
  exact ⟨v, hv, hcyc, hkg⟩

end

end Work.Pi6.MSS.E1D
