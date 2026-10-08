import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.M110.Reduce
import Submission.Work.DSTR.M110.fittingPi_centralizer_le_pslImage

namespace Work.DSTR

/-- **DS10a** (`Work.GW2.D110iiModelProp`, Bender 1981 1.10(ii) on the almost simple model): `Q` has a normal `L ≅ PSL(2,q)` (`q = p^k` odd `>= 5`) with `C_Q(L) = 1` and dihedral/cyclic Sylow 2-subgroups; then `F_{2'}(C_Q(t)) <= L` for every involution `t`.  Route (design3 §10): `Q` embeds in the semilinear group `PΓL(2,q)` (`AUTL2` A1–A3), so an odd-order element `x` of `F_{2'}(C_Q(t))` outside `L` would induce a field automorphism of odd order `r`; it acts nontrivially on the cyclic torus `T` of order `(q±1)/2` in `C_L(t)` (using `hl2cent`), so `1 ≠ [x,T] <= F_{2'}(C_Q(t)) ∩ T`, which contradicts the nilpotence of `F_{2'}(C_Q(t))` when `r ∤ |[x,T]|`, and is handled on the Sylow `r` of `T` otherwise. -/
theorem d110iiModel (hautL2 : Work.GW2.AutL2Prop)
    (hl2cent : Work.GW2.L2InvolutionCentralizerProp) (hl2ti : Work.GW2.L2TIProp)
    (hsub : Work.GW2.DihedralSubgroupProp) (h1 : Work.GW2.DihOrCycHeredProp) :
    Work.GW2.D110iiModelProp :=
  d110iiModel_of a6Prop (fun p k _ hp hq _ Q' hpsl hQ t' ht' =>
    Work.DSTR.M110.fittingPi_centralizer_le_pslImage p k hp hq Q' hpsl hQ t' ht')

end Work.DSTR
