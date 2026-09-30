import Mathlib
import Submission.Work.SSSR.Filtration
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits HomologicalComplex
/-- The value of the connecting map `kF ξ s t` on the homology class of a relative cycle,
computed by lifting along the quotient `F_{s+1} → F_{s+1}/F_s`.

If `z` is a cycle of `F_{s+1}/F_s` in degree `(s+1)+t` which is the image of `w : F_{s+1}` under the
quotient, and if `∂w` is the image in `F_{s+1}` of a cycle `v` of `F_s` in degree `s+t`, then
`kF ξ s t` sends the class of `z` (in `H_{(s+1)+t}(F_{s+1}/F_s)`) to the class of `v`
(in `H_{s+t}(F_s)`).  This is the elementwise description of the connecting homomorphism of the
short exact sequence `0 → F_s → F_{s+1} → F_{s+1}/F_s → 0`. -/
theorem kF_eq_of_lift {C : ChainComplex (ModuleCat R) ℕ} (ξ : Work.SSSR.Filtration R C) (s t : ℕ)
    (z : (Work.SSSR.grF ξ.F (s+1)).X ((s+1)+t))
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.grF ξ.F (s+1)).d ((s+1)+t)
        ((ComplexShape.down ℕ).next ((s+1)+t)))) z = 0)
    (w : (ξ.F.obj (s+1)).X ((s+1)+t))
    (hw : (ModuleCat.Hom.hom ((cokernel.π (Work.SSSR.incF ξ.F s)).f ((s+1)+t))) w = z)
    (v : (ξ.F.obj s).X (s+t))
    (hv : (ModuleCat.Hom.hom ((Work.SSSR.incF ξ.F s).f (s+t))) v
        = (ModuleCat.Hom.hom ((ξ.F.obj (s+1)).d ((s+1)+t) (s+t))) w)
    (hvcyc : (ModuleCat.Hom.hom ((ξ.F.obj s).d (s+t)
        ((ComplexShape.down ℕ).next (s+t)))) v = 0) :
    (ModuleCat.Hom.hom (Work.SSSR.kF ξ s t))
        ((ModuleCat.Hom.hom ((Work.SSSR.grF ξ.F (s+1)).homologyπ ((s+1)+t)))
          ((Work.SSSR.grF ξ.F (s+1)).cyclesMk z ((ComplexShape.down ℕ).next ((s+1)+t)) rfl hz))
      = (ModuleCat.Hom.hom ((ξ.F.obj s).homologyπ (s+t)))
          ((ξ.F.obj s).cyclesMk v ((ComplexShape.down ℕ).next (s+t)) rfl hvcyc) := by
  -- `kF ξ s t` is the connecting homomorphism `δ` of the short exact sequence
  -- `0 → F_s → F_{s+1} → F_{s+1}/F_s → 0`.
  have hij : (ComplexShape.down ℕ).Rel ((s+1)+t) (s+t) := by simp [ComplexShape.down]; omega
  have hkf : kF ξ s t = (sesF_shortExact ξ s).δ ((s+1)+t) (s+t) hij := rfl
  rw [hkf]
  -- Apply the elementwise description of `δ` supplied by Mathlib; the two `cyclesMk` entries in
  -- the goal are definitionally equal to the ones produced by `δ_apply` (the auxiliary index and
  -- the cycle-condition proof of `cyclesMk` are both proof-irrelevant).
  refine ShortComplex.ShortExact.δ_apply (sesF_shortExact ξ s) ((s+1)+t) (s+t) hij
    z ?_ w hw v hv ((ComplexShape.down ℕ).next (s+t)) rfl
  -- It remains to check that `z` is a cycle for the differential `d = F_{s+1}/F_s` in degree
  -- `(s+1)+t → s+t`; this is the hypothesis `hz` up to the identification `next ((s+1)+t) = s+t`.
  rw [← ComplexShape.next_eq' _ hij]
  exact hz

end Work.SSSR
