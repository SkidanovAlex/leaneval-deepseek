import Mathlib
import Submission.Work.SSS.FibreColDefs
import Submission.Work.SSS.FirstPage.HomElts
import Submission.Work.SSS.FirstPageCF.ZsqElts
import Submission.Work.SSS.FirstPageCF.exists_cycle_lift
import Submission.Work.SSS.FirstPageCF.mem_Bsq_of_sub_mem_range
import Submission.Work.SSS.FirstPageCF.sub_mem_range_of_jF_homologypi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SSS.FirstPageCF

/-- `Bsq` is the kernel of the class map followed by `d¹`: if the class of `z` in `E¹_{k+3,t}` lies
in the image of `d¹ : E¹_{k+3,t} → E¹_{k+2,t}`, then `z` lies in the model `Bsq`.

Roadmap.  Write `psi z = d¹ w` (from the hypothesis, using
`Work.SSS.E1Complex_d` to identify `((E1Complex ξ t).sc' (k+3) (k+2) (k+1)).f` with
`d1 ξ (k+2) t`), so `psi z = jF ξ (k+2) t (kF ξ (k+2) t w)`.  Since
`range (kF ξ (k+2) t) = ker (homologyMap (incF ξ.F (k+2)) ((k+2)+t))`
(`Work.SSS.range_kF_eq_ker_incF`), the class `kF ξ (k+2) t w` is represented by a cycle
`c ∈ F_{k+2}` whose image under `incF ξ.F (k+2)` is a boundary `∂e` in `F_{k+3}`
(`Work.SSS.d_eq_iCycles_iff_homologypi_eq_zero`).  On the other hand
`psi z = jF ξ (k+2) t (kF ξ (k+2) t w) = [projQ c]` (`Work.SSS.FirstPageCF.jF_apply_cyclesMk`), and
`psi z = [z]` (`Work.SSS.FirstPageCF.psi_apply_cyclesMk`), so `z - projQ c` is a boundary in `grF ξ.F (k+2)`:
`z - projQ c = ∂ṽ` (`Work.SSS.homologypi_eq_iff_sub_mem_range`).  Lift `ṽ` to `u ∈ F_{k+2}`
and set `x := c + ∂u ∈ F_{k+2}`; then `projQ x = z` and, with `e' := e + incF u`,
`∂e' = incF x`, so `z ∈ Bsq` by `Work.SSS.FirstPageCF.Bsq_mem_iff`.  The degree changed by the fact that the
short complex `(E1Complex ξ t).sc s` uses the index `(ComplexShape.down ℕ).next` while `Zsq` uses
`n - 1`: use `Work.SSS.eq_mp_of_eq_index` (a `Prop`-valued function of the degree) to transport
statements across equal indices. -/
lemma mem_Bsq_of_psi_mem_range {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C)
    (k t : ℕ) (z : ↥(Work.SSS.Zsq ξ (k+2) ((k+2)+t)))
    (hz : Work.SSS.FirstPageCF.psi ξ (k+2) t (by omega) z
      ∈ LinearMap.range (((Work.SSS.E1Complex ξ t).sc' (k+3) (k+2) (k+1)).f.hom)) :
    (z : (Work.SSS.grF ξ.F (k+2)).X ((k+2)+t)) ∈ Work.SSS.Bsq ξ (k+2) ((k+2)+t) := by
  -- Identify the differential of the short complex `sc' (k+3) (k+2) (k+1)` with `d¹`.
  have hSf : ((E1Complex ξ t).sc' (k+3) (k+2) (k+1)).f.hom = (d1 ξ (k+2) t).hom := by
    rw [show ((E1Complex ξ t).sc' (k+3) (k+2) (k+1)).f
        = (E1Complex ξ t).d (k+3) (k+2) from rfl]
    exact congrArg ModuleCat.Hom.hom (E1Complex_d ξ t (k+2))
  -- Re-type the element so that it lives in the `X₂` of the short complex.
  have hz1 : (psi ξ (k+2) t (by omega) z
      : ↥((E1Complex ξ t).sc' (k+3) (k+2) (k+1)).X₂)
      ∈ LinearMap.range (((E1Complex ξ t).sc' (k+3) (k+2) (k+1)).f.hom) := hz
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hz1
  -- `psi z = jF (kF w)`.
  have hw' : (jF ξ (k+2) t).hom ((kF ξ (k+2) t).hom w) = psi ξ (k+2) t (by omega) z := by
    have h1 : ((E1Complex ξ t).sc' (k+3) (k+2) (k+1)).f.hom w
        = (jF ξ (k+2) t).hom ((kF ξ (k+2) t).hom w) := by
      rw [hSf]; rfl
    rw [← h1]; exact hw
  -- `kF w` is killed by the map induced by `F_{k+2} ↪ F_{k+3}`.
  have hvker : (HomologicalComplex.homologyMap (incF ξ.F (k+2)) ((k+2)+t)).hom
      ((kF ξ (k+2) t).hom w) = 0 := by
    have hmem : (kF ξ (k+2) t).hom w ∈ (kF ξ (k+2) t).hom.range := ⟨w, rfl⟩
    rw [range_kF_eq_ker_incF ξ (k+2) t] at hmem
    exact hmem
  -- A cycle representative `x` of `kF w` whose image under `incF` is a boundary `e`.
  obtain ⟨x, hx, hcls, e, hee⟩ :=
    exists_cycle_lift ξ (k+2) t ((kF ξ (k+2) t).hom w) hvker
  -- Hence `psi z = jF ξ (k+2) t [x]`.
  have h33 : (jF ξ (k+2) t).hom ((HomologicalComplex.homologyπ (ξ.F.obj (k+2)) ((k+2)+t))
        ((ξ.F.obj (k+2)).cyclesMk x (((k+2)+t)-1) (next_down_eq_pred ((k+2)+t)) hx))
      = psi ξ (k+2) t (by omega) z := by
    rw [hcls]
    exact hw'
  -- The difference of the classes of `z` and of `projQ x` in `grF ξ.F (k+2)` is a boundary.
  have hsub := sub_mem_range_of_jF_homologypi ξ (k+2) t (by omega) z x hx h33
  exact mem_Bsq_of_sub_mem_range ξ (k+2) ((k+2)+t) (by omega) x e hee
    (z : (grF ξ.F (k+2)).X ((k+2)+t)) hsub

end Work.SSS.FirstPageCF
