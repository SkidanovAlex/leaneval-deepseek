import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.GalFields.Norm.Xn_LGammaT_le
import Submission.Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
import Submission.Work.FTS.GalFields.RHS.L12f_eq_sub_add
import Submission.Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ
import Submission.Work.FTS.GalFields.RHS.Transport_L12_integrable
import Submission.Work.FTS.EllipticEst.TT.Slot11.ZsqAux
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `𝓛_Γ^T g − 𝓛_Γ^T g' = 𝓛_Γ^T (g − g')`, sharply

The linear part `𝓛_Γ^T` of the dynamic right-hand side of the Galerkin chapter is a **linear**
operator in the profile: on the open quadrant `(0,∞) × (0,π/2)`,

  `𝓛_Γ^T g − 𝓛_Γ^T g' = 𝓛_Γ^T (g − g')`      (`sharp_LGammaT_diff_eqOn`).

Everything in `𝓛_Γ^T` is transparently additive — the `𝓛`-part (`deriv`-linear on the open
quadrant, `SmoothOpen.DzIter_sub_open`) and the transport part — except the two *nonlocal*
`L₁₂`-terms, whose additivity needs the integrability of the angular slices **and** of the
`L₁₂`-densities of both summands (they are integrals over the unbounded region `(z,∞)`):

* the `z`-slot `L₁₂(f)(z)` is additive by `L12f_eq_sub_add`, with the integrability supplied by
  `SmoothOpen` + `HkMem α 4` (`GalBasis.cc.integrableOn_{slice,L12dens}_of_SmoothOpen_HkMem`);
* the projector slot `L₁₂(Transport f)(0)` — `Transport f = 3 sin(2θ)∂_θf/(1+z)` — needs the
  same integrability facts for the *transport* profile, which is `Transport_L12_integrable`;
  the pointwise comparison of `Transport f − Transport f'` with `Transport (f − f')` on the open
  quadrant then finishes with `L12f_congr_of_agreeOnQ`.

With the identity in hand, the sharp difference estimate reduces to the single profile bound
`Norm.Xn_LGammaT_le` applied to the difference `h`: the `SmoothOpen` and `HkMem` clauses
transport along the open-quadrant identity (`NonlinRows.smoothOpen_sub`, `HkMem_congr_Q0`), and
the norm clause through `HkSq_congr_open`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.GalFields.RHS

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The `L₁₂`-slot of the transport term -/

/-- **Additivity of the projector slot** `L₁₂(Transport ·)(0)`: for two `SmoothOpen` profiles
with `HkMem α 4`, the transport-`L₁₂`-difference is the transport-`L₁₂` of the difference. -/
theorem sharp_L12f_Transport_eq_sub_add {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f f' : Fn}
    (hSf : Work.FTS.EllipticEst.SmoothOpen f) (hSf' : Work.FTS.EllipticEst.SmoothOpen f')
    (hmf : Work.Spaces.HkMem α 4 f) (hmf' : Work.Spaces.HkMem α 4 f') :
    Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
      = Work.Coercivity.L12f (Work.Coercivity.Transport (fun z θ => f z θ - f' z θ)) 0
        + Work.Coercivity.L12f (Work.Coercivity.Transport f') 0 := by
  obtain ⟨hs1, hd1⟩ := Transport_L12_integrable hα hα1 hSf hmf
  obtain ⟨hs2, hd2⟩ := Transport_L12_integrable hα hα1 hSf' hmf'
  have h1 := L12f_eq_sub_add (a := Work.Coercivity.Transport f)
    (b := Work.Coercivity.Transport f') hs1 hs2 hd1 hd2
  have hcg : Work.Coercivity.L12f
        (fun z θ => Work.Coercivity.Transport f z θ - Work.Coercivity.Transport f' z θ) 0
      = Work.Coercivity.L12f (Work.Coercivity.Transport (fun z θ => f z θ - f' z θ)) 0 := by
    refine L12f_congr_of_agreeOnQ (le_refl 0) ?_
    intro z θ hz hθ0 hθ1
    have h := Work.FTS.EllipticEst.TTSlot11Aux.DthIter_sub_open hSf hSf' 1 z θ hz hθ0 hθ1
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] at h
    simp only [Work.Coercivity.Transport]
    rw [h]
    ring
  rw [hcg] at h1
  exact h1

/-! ## The identity on the open quadrant -/

/-- **`𝓛_Γ^T` is linear on the open quadrant**: for `SmoothOpen` profiles in `ℋ⁴_α`,
`𝓛_Γ^T f − 𝓛_Γ^T f'` agrees with `𝓛_Γ^T(f − f')` at every interior point of the quadrant.

The three components are additive there: `𝓛` and `Transport` through the `deriv`-linearity of
the iterated operators (`SmoothOpen.DzIter_sub_open`, `SmoothOpen.DthIter_sub_open`), and the
two `L₁₂`-slots through `L12f_eq_sub_add` (integrability from `SmoothOpen` + `HkMem α 4`) and
`sharp_L12f_Transport_eq_sub_add`. -/
theorem sharp_LGammaT_diff_eqOn {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f f' : Fn}
    (hSf : Work.FTS.EllipticEst.SmoothOpen f) (hSf' : Work.FTS.EllipticEst.SmoothOpen f')
    (hmf : Work.Spaces.HkMem α 4 f) (hmf' : Work.Spaces.HkMem α 4 f') :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Coercivity.LGammaT α f z θ - Work.Coercivity.LGammaT α f' z θ
        = Work.Coercivity.LGammaT α (fun z θ => f z θ - f' z θ) z θ := by
  intro z θ hz hθ0 hθ1
  -- the two `D`-operators are subtractive on the open quadrant
  have hDz : Work.Spaces.Dz f z θ
      = Work.Spaces.Dz (fun z θ => f z θ - f' z θ) z θ + Work.Spaces.Dz f' z θ := by
    have h := Work.FTS.EllipticEst.TTSlot11Aux.DzIter_sub_open hSf hSf' 1 z θ hz hθ0 hθ1
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] at h
    linarith
  have hDth : Work.Spaces.Dth f z θ
      = Work.Spaces.Dth (fun z θ => f z θ - f' z θ) z θ + Work.Spaces.Dth f' z θ := by
    have h := Work.FTS.EllipticEst.TTSlot11Aux.DthIter_sub_open hSf hSf' 1 z θ hz hθ0 hθ1
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] at h
    linarith
  -- hence for the transport term as well
  have hT : Work.Coercivity.Transport f z θ
      = Work.Coercivity.Transport (fun z θ => f z θ - f' z θ) z θ
        + Work.Coercivity.Transport f' z θ := by
    simp only [Work.Coercivity.Transport]
    rw [hDth]
    ring
  -- the integrability inputs of the `z`-slot at the base point `z`
  have hDa : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ := by
    intro s hs
    exact Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hSf hmf
      (lt_trans hz (Set.mem_Ioi.mp hs))
  have hDb : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * f' s θ / s) Work.Spaces.Iθ := by
    intro s hs
    exact Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hSf' hmf'
      (lt_trans hz (Set.mem_Ioi.mp hs))
  have hDca : MeasureTheory.IntegrableOn (Work.Construction.L12dens f) (Set.Ioi z) :=
    (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hSf hmf).mono_set
      (Set.Ioi_subset_Ioi hz.le)
  have hDcb : MeasureTheory.IntegrableOn (Work.Construction.L12dens f') (Set.Ioi z) :=
    (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hSf' hmf').mono_set
      (Set.Ioi_subset_Ioi hz.le)
  have hL12 : Work.Coercivity.L12f f z
      = Work.Coercivity.L12f (fun z θ => f z θ - f' z θ) z + Work.Coercivity.L12f f' z :=
    L12f_eq_sub_add hDa hDb hDca hDcb
  have hLT : Work.Coercivity.L12f (Work.Coercivity.Transport f) 0
      = Work.Coercivity.L12f (Work.Coercivity.Transport (fun z θ => f z θ - f' z θ)) 0
        + Work.Coercivity.L12f (Work.Coercivity.Transport f') 0 :=
    sharp_L12f_Transport_eq_sub_add hα hα1 hSf hSf' hmf hmf'
  simp only [Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.Proj,
    Work.Coercivity.L]
  rw [hDz, hT, hL12, hLT]
  ring

/-! ## Smoothness of `𝓛_Γ^T g` for `GalClass` data -/

/-- **`𝓛_Γ^T g` is `C^∞` on the open quadrant** for `GalClass α g` together with the elliptic
package of `g` (`EllPkgGo`): the two ingredients of `smoothOpen_LGammaT_of_L12` are `SmoothOpen`
of the datum and of the *radial* profile `z ↦ L₁₂(g)(z)`
(`NonlinRows.smoothOpen_L12_radial`, which spends the smoothness of the elliptic residual
`Vop(Φ̃_g)`; the zero mode `L₁₂(D_z^bD_θ^a g)(0) = 0` is *not* needed for this clause). -/
theorem sharp_smoothOpen_LGammaT_of_pkg {α Ce : ℝ} {g Φg : Fn} (hα : 0 < α)
    (hgal : Work.FTS.Nonlin.GalClass α g)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α g) :=
  smoothOpen_LGammaT_of_L12
    (Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1)
    (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hgal.reg.1)

/-! ## The target -/

theorem sharp_LGammaT_diff {α α₂ Ci Ct Ce Cs : ℝ}
    {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct)
    (hell : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hα : 0 < α) (hαα₂ : α ≤ α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ g g' h : Work.FTS.Galerkin.Fn,
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.GalClass α g' →
      Work.FTS.Nonlin.GalClass α h →
      (∀ z θ, h z θ = g z θ - g' z θ) → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
          Work.Coercivity.LGammaT α g z θ - Work.Coercivity.LGammaT α g' z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
          Work.Coercivity.LGammaT α g z θ - Work.Coercivity.LGammaT α g' z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Coercivity.LGammaT α g z θ - Work.Coercivity.LGammaT α g' z θ)
        ≤ K * Work.FTS.GalFields.Xn5 α h := by
  obtain ⟨K, hKpos, hKid⟩ :=
    Work.FTS.GalFields.Norm.Xn_LGammaT_le (Ce := Ce) (Cs := Cs) hN hE
  refine ⟨K, hKpos, ?_⟩
  intro g g' h hgal hgal' hgalh hdef hα1
  have hSg : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hgal.reg.1
  have hSg' : Work.FTS.EllipticEst.SmoothOpen g' :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hgal'.reg.1
  have hm4g : Work.Spaces.HkMem α 4 g :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hSg hgal.reg.2.1
  have hm4g' : Work.Spaces.HkMem α 4 g' :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hSg' hgal'.reg.2.1
  have hSOg : Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α g) :=
    sharp_smoothOpen_LGammaT_of_pkg hα hgal (hell g hgal)
  have hSOg' : Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α g') :=
    sharp_smoothOpen_LGammaT_of_pkg hα hgal' (hell g' hgal')
  -- the identity, rewritten in terms of the given difference `h`
  have hEq : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Coercivity.LGammaT α g z θ - Work.Coercivity.LGammaT α g' z θ
        = Work.Coercivity.LGammaT α h z θ := by
    intro z θ hz hθ0 hθ1
    rw [sharp_LGammaT_diff_eqOn hα hα1 hSg hSg' hm4g hm4g' z θ hz hθ0 hθ1]
    have hfun : (fun z θ => g z θ - g' z θ) = h := by
      funext z θ
      exact (hdef z θ).symm
    rw [hfun]
  refine ⟨Work.FTS.NonlinRows.smoothOpen_sub hSOg hSOg', ?_, ?_⟩
  · -- the `ℋ⁴`-honesty, transported along the open-quadrant identity
    exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
      (hKid (α := α) (g := h) hα hα1 hαα₂ hgalh).1
      (fun z hz θ hθ => (hEq z θ hz hθ.1 hθ.2).symm)
  · -- the sharp norm bound: the difference is `𝓛_Γ^T h`
    have hsq : Work.Spaces.HkSq α 4 (fun z θ =>
          Work.Coercivity.LGammaT α g z θ - Work.Coercivity.LGammaT α g' z θ)
        = Work.Spaces.HkSq α 4 (Work.Coercivity.LGammaT α h) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 4
        (fun z θ hz hθ0 hθ1 => hEq z θ hz hθ0 hθ1)
    have hbdh : Work.FTS.Nonlin.Xn α (Work.Coercivity.LGammaT α h)
        ≤ K * Work.FTS.GalFields.Xn5 α h :=
      (hKid (α := α) (g := h) hα hα1 hαα₂ hgalh).2
    have h1 : Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Coercivity.LGammaT α g z θ - Work.Coercivity.LGammaT α g' z θ)
        = Work.FTS.Nonlin.Xn α (Work.Coercivity.LGammaT α h) := by
      simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hsq]
    exact h1 ▸ hbdh

end Work.FTS.GalFields.RHS
