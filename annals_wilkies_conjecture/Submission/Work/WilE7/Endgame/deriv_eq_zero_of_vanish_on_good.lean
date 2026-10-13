import Mathlib
import Submission.Work.WilE5.Flat.strictFDeriv_pi_eaEval
import Submission.Work.WilE7.Auxiliary.kerLeKerOfVanishLevelSet
import Submission.Work.WilE7.DimAPI.rankLocusAux
import Submission.Work.WilE7.DimAPI.jac_eq_fderiv
import Submission.Work.WilE7.coreLT_succ.SubStratum
import Submission.Work.WilE7.DimAPI.range_fderiv_good_eq_top
import Submission.Work.WilE7.DimAPI.ProjRankAux

namespace Work.WilE7.Endgame

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

theorem deriv_eq_zero_of_vanish_on_good {M K : ℕ} (W : WilkiesDesign.E.Stratum 0 M) (hW : W.Good)
    {z : Fin (0 + M) → ℝ} (hz : z ∈ W.X.set)
    (f : (Fin (0 + M) → ℝ) → (Fin K → ℝ)) (hf : HasFDerivAt f (fderiv ℝ f z) z)
    (hvan : ∀ᶠ y in 𝓝 z, y ∈ W.X.set → f y = f z)
    {v : Fin (0 + M) → ℝ} (hv : v ∈ LinearMap.ker (Work.WilE7.MainDesign.jac W z)) :
    fderiv ℝ f z v = 0 := by
  let g : (Fin (0 + M) → ℝ) → (Fin W.j → ℝ) := fun w a => WilkiesDesign.E.eaEval W.X.c (W.h a) w
  let L : (Fin (0 + M) → ℝ) →L[ℝ] (Fin W.j → ℝ) := fderiv ℝ g z
  -- `g` is strictly differentiable at `z`, and `W.Good` makes its derivative surjective.
  have hstrict : HasStrictFDerivAt g L z :=
    Work.WilE5.Flat.strictFDeriv_pi_eaEval W.X.c W.h z
  have hsurj : (L : (Fin (0 + M) → ℝ) →ₗ[ℝ] (Fin W.j → ℝ)).range = ⊤ :=
    Work.WilE7.DimAPI.range_fderiv_good_eq_top W hW hz
  -- The equations of `W` vanish at `z`.
  have hgz : g z = 0 := by
    funext a
    simpa [g] using (hW z hz).1 a
  -- Near `z` the zero set of the equations is contained in `W.X.set` (`Good`, third clause).
  have hgoodev : ∀ᶠ y in 𝓝 z, g y = 0 → y ∈ W.X.set := by
    filter_upwards [(hW z hz).2.2] with y hy hgy
    exact hy (funext fun i => i.elim0) (fun a => by
      have := congr_fun hgy a
      simpa [g] using this)
  -- Hence `f` is constant on the level set `{g = 0}` near `z`.
  have hvanlev : ∀ᶠ y in 𝓝 z, g y = 0 → f y = f z := by
    filter_upwards [hvan, hgoodev] with y hv1 hv2 hgy
    exact hv1 (hv2 hgy)
  -- `jac W z` is the underlying linear map of `L`, so `v ∈ L.ker`.
  have hvmem : v ∈ (L : (Fin (0 + M) → ℝ) →ₗ[ℝ] (Fin W.j → ℝ)).ker := by
    rw [LinearMap.mem_ker]
    have hjac := Work.WilE7.DimAPI.jac_eq_fderiv W z
    have hv0 : Work.WilE7.MainDesign.jac W z v = 0 := by simpa [LinearMap.mem_ker] using hv
    rw [← DFunLike.congr_fun hjac v]
    exact hv0
  -- Componentwise: the derivative of each coordinate of `f` vanishes on `ker L`.
  have main : ∀ i : Fin K, (fderiv ℝ f z v) i = 0 := by
    intro i
    let P : (Fin K → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    have hFi : HasFDerivAt (fun w => f w i) (P.comp (fderiv ℝ f z)) z :=
      P.hasFDerivAt.comp z hf
    have hvan_i : ∀ᶠ y in 𝓝 z, g y = 0 → (fun w => f w i) y = (fun w => f w i) z := by
      filter_upwards [hvanlev] with y hy hyg
      exact congr_fun (hy hyg) i
    have hsub := Work.WilE7.Auxiliary.kerLeKerOfVanishLevelSet g (fun w => f w i) z L
        (P.comp (fderiv ℝ f z)) hstrict hFi hsurj hgz hvan_i
    have hmem := hsub hvmem
    have : P (fderiv ℝ f z v) = 0 := hmem
    simpa [P, ContinuousLinearMap.proj_apply] using this
  funext i
  exact main i

end
