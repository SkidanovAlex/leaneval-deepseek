import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.PhiStar.EllExistHalf
import Submission.Work.FTS.GalBasis.FamEAux.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.bslOp_sub
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.PhiStar.Honesty.EllWeakAux.HkMem_sub_of_eqOn_Q0
import Submission.Work.FTS.PhiStar.Honesty.EllWeakAux.integrableOn_slice_mul_sinCos2
import Submission.Work.FTS.PhiStar.Honesty.EllWeakAux.Fstar_source_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.Honesty.ellWeakPos_sub` — the weak hypothesis class is closed under differences

`Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ` is the ten-conjunct hypothesis bundle of the
`ℋ^k` elliptic estimate (`prop:Hk` of Elgindi's Annals paper): the equation `bslOp α Ψ = F` on
the *open* quadrant, the two Dirichlet traces, the two angular moments (`F_*F = F_*Ψ = 0` for
`z > 0`), `C^∞`-smoothness of `Ψ` on the open quadrant, and the four `HkMem`-honesties of the
source and of the three second-order slots `z²∂_z²Ψ`, `∂_θ²Ψ`, `z∂_z∂_θ²Ψ`.

The statement proved here is that the class is closed under *differences*: if `(G,Ψ)` and
`(H,Φ)` are two data of the class then so is `(G - H, Ψ - Φ)`.  This is the linearity of the
whole package, and it is what allows one to compare two data of the class (in particular a
solution with a reference datum) inside all the estimates of the chapter.

The ten conjuncts and the point where each one is proved:

1. `bslOp α (Ψ - Φ) = G - H` on the open quadrant — the subtractivity of the elliptic operator
   (`Work.FTS.EllipticEst.bslOp_sub`), which needs only the `C²`-differentiability of the two
   data at the point, available from the open-quadrant smoothness;
2. `(Ψ - Φ) z 0 = 0` and 3. `(Ψ - Φ) z (π/2) = 0` — pointwise, from the two traces;
4. `F_*(G - H) z = 0` for `z > 0` — `EllWeakAux.Fstar_source_sub`: the angular profile
   `θ ↦ G z θ sinθcos²θ` of a source of the class is honest (`HkMem α k G` plus the equation
   give it integrability on the slice), so `F_*` subtracts;
5. `F_*(Ψ - Φ) z = 0` for `z > 0` — the same linearity for the *solutions*.  Here the
   integrability of the profile `θ ↦ Ψ z θ sinθcos²θ` is *not* a hypothesis of the class; it is
   forced by the honesty of `∂_θ²Ψ` (the weighted `L²` bound on the second derivative controls
   the first one by Cauchy–Schwarz/FTC on the open interval, hence the slice itself), which is
   `EllWeakAux.integrableOn_slice_mul_sinCos2`.  The linearity itself is
   `Fstar_sub_of_integrable_left` below, and it genuinely needs that integrability: the Bochner
   integral of a non-integrable function is `0`, so additivity for the *junk* values is false
   (`f` non-integrable and `g = f - v` with `v` integrable gives `F_*f = F_*g = 0` but
   `F_*(f - g) = F_*v ≠ 0` in general);
6. `C^∞` of `Ψ - Φ` on the open quadrant — `ContDiffOn.sub`;
7.–10. `HkMem α k (G - H)` and the three slot honesties of `Ψ - Φ` — the general closure
   statement `EllWeakAux.HkMem_sub_of_eqOn_Q0`: `HkIntegrand(·)` is local, so a datum which
   agrees with `u - v` on the open quadrant inherits the honesty of `u - v`, and the integrand
   of a difference is dominated by `2·HkIntegrand u + 2·HkIntegrand v`.  The open-quadrant
   identifications of the slots of a difference with the differences of the slots are
   `Work.FTS.GalBasis.pzIter_sub_eqOn` and `Work.FTS.GalBasis.pthIter_sub_eqOn` (for `z²∂_z²`
   resp. `∂_θ²`) and `pz_pthIter_two_sub` below (for `z∂_z∂_θ²`, which needs the locality of
   `∂_z` in addition to the `∂_θ²`-slot identity).

The two stream functions of the weak class are `C^∞` on the open quadrant (conjunct 6), and the
two *sources* are `C^∞` there as well because they agree with `bslOp` of a smooth function
(`smoothOpen_of_bslOp_eq`) — the latter is what makes the `HkIntegrand`-domination of conjunct 7
available.  Nothing is assumed outside the open quadrant, and the boundary lines `z = 0`,
`θ = 0`, `θ = π/2` cost nothing because the `ℋ`-weights vanish there.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-! ## Auxiliary lemmas for `ellWeakPos_sub` -/

/-- The partial `∂_z` depends only on a neighbourhood of the point. -/
private theorem pz_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) {z θ : ℝ} (hzθ : (z, θ) ∈ V) :
    Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (Continuous.prodMk_left θ).continuousAt.eventually (hV.mem_nhds hzθ)
  have hev : (fun z' => f z' θ) =ᶠ[𝓝 z] (fun z' => g z' θ) := by
    filter_upwards [hnb] with z' hz'
    exact h hz'
  simpa only [Work.Spaces.pz] using hev.deriv_eq

/-- **`Fstar` is additive on a difference as soon as one of the two integrands is honest.**

Without that hypothesis the statement is false: the Bochner integral of a non-integrable
function is `0`, so two non-integrable angular profiles with an *integrable* difference would
give a counterexample.  Here the integrability of `f`'s profile is what the weak class
supplies. -/
private theorem Fstar_sub_of_integrable_left {f g : ℝ → ℝ → ℝ} {z : ℝ}
    (hf : Work.Elliptic.Fstar f z = 0) (hg : Work.Elliptic.Fstar g z = 0)
    (hint : IntegrableOn (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    Work.Elliptic.Fstar (fun z θ => f z θ - g z θ) z = 0 := by
  set A : ℝ → ℝ := fun θ => f z θ * Work.Elliptic.sinCos2 θ with hAdef
  set B : ℝ → ℝ := fun θ => g z θ * Work.Elliptic.sinCos2 θ with hBdef
  have hA0 : (∫ θ in Work.Spaces.Iθ, A θ) = 0 := hf
  have hB0 : (∫ θ in Work.Spaces.Iθ, B θ) = 0 := hg
  have hAB : (A - fun θ => A θ - B θ) = B := by
    funext θ; simp only [Pi.sub_apply]; ring
  have hgoal : Work.Elliptic.Fstar (fun z θ => f z θ - g z θ) z
      = ∫ θ in Work.Spaces.Iθ, (A θ - B θ) := by
    rw [Work.Elliptic.Fstar]
    refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    simp only [hAdef, hBdef]
    ring
  have key : (∫ θ in Work.Spaces.Iθ, (A θ - B θ)) = 0 := by
    by_cases hB : Integrable B (volume.restrict Work.Spaces.Iθ)
    · rw [integral_sub hint hB, hA0, hB0, sub_zero]
    · rw [MeasureTheory.integral_undef]
      intro h
      exact hB ((hint.sub h).congr
        (Filter.Eventually.of_forall (fun x => congrFun hAB x)))
  rw [hgoal, key]

/-- The source `G` of a datum of the weak class is `C^∞` on the open quadrant: there it agrees
with `bslOp α Ψ`, which is `C^∞` because `Ψ` is. -/
private theorem smoothOpen_of_bslOp_eq {α : ℝ} {G Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (h : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = G z θ) :
    Work.FTS.EllipticEst.SmoothOpen G :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ)
    (fun z θ hz hθ hθ2 => h z hz θ hθ hθ2)

/-- The `∂_z∂_θθ`-slot of a difference is the difference of the slots, on the open quadrant. -/
private theorem pz_pthIter_two_sub {Ψ Φ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pz (Work.Spaces.pthIter 2 (fun z θ => Ψ z θ - Φ z θ)) z θ
        = Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
          - Work.Spaces.pz (Work.Spaces.pthIter 2 Φ) z θ := by
  intro z θ hz hθ0 hθ1
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ0, hθ1⟩
  have hcongr : Set.EqOn
      (Function.uncurry (Work.Spaces.pthIter 2 (fun z θ => Ψ z θ - Φ z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.pthIter 2 Ψ z θ
        - Work.Spaces.pthIter 2 Φ z θ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.GalBasis.pthIter_sub_eqOn (V := Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0 2 (hΨ.forall 3) (hΦ.forall 3)
  have hloc := pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hcongr hzθ
  have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.pthIter 2 Ψ z' θ) z :=
    (((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨ 2).hasDerivAt_slice
      ⟨hθ0, hθ1⟩ hz).differentiableAt)
  have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pthIter 2 Φ z' θ) z :=
    (((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΦ 2).hasDerivAt_slice
      ⟨hθ0, hθ1⟩ hz).differentiableAt)
  rw [hloc]
  simp only [Work.Spaces.pz]
  rw [show (fun z' : ℝ => Work.Spaces.pthIter 2 Ψ z' θ - Work.Spaces.pthIter 2 Φ z' θ)
      = (fun z' : ℝ => Work.Spaces.pthIter 2 Ψ z' θ)
        - (fun z' : ℝ => Work.Spaces.pthIter 2 Φ z' θ) from rfl]
  rw [deriv_sub hd1 hd2]

theorem ellWeakPos_sub (k : ℕ) {α : ℝ} {G H Ψ Φ : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.TT.EllWeakPos α k G Ψ)
    (hH : Work.FTS.EllipticEst.TT.EllWeakPos α k H Φ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α k (fun z θ => G z θ - H z θ)
      (fun z θ => Ψ z θ - Φ z θ) := by
  have hGc := hG
  have hHc := hH
  obtain ⟨hGeq, hG0, hGπ, hGFst, hGΨst, hGsm, hGFm, hGAm, hGBm, hGZm⟩ := hG
  obtain ⟨hHeq, hH0, hHπ, hHFst, hHΨst, hHsm, hHFm, hHAm, hHBm, hHZm⟩ := hH
  have hsmΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hGsm
  have hsmΦ : Work.FTS.EllipticEst.SmoothOpen Φ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hHsm
  have hsmG : Work.FTS.EllipticEst.SmoothOpen G := smoothOpen_of_bslOp_eq hsmΨ hGeq
  have hsmH : Work.FTS.EllipticEst.SmoothOpen H := smoothOpen_of_bslOp_eq hsmΦ hHeq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) the equation on the open quadrant
    intro z hz θ hθ0 hθ1
    have hc : Real.cos θ ≠ 0 := by
      refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;> linarith [Real.pi_pos]
    have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ0, hθ1⟩
    have hΨ2 : ContDiffAt ℝ 2 (Function.uncurry Ψ) (z, θ) :=
      (hsmΨ.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)
    have hΦ2 : ContDiffAt ℝ 2 (Function.uncurry Φ) (z, θ) :=
      (hsmΦ.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)
    rw [Work.FTS.EllipticEst.bslOp_sub α Ψ Φ z θ hc hΨ2 hΦ2,
      hGeq z hz θ hθ0 hθ1, hHeq z hz θ hθ0 hθ1]
  · -- (2) the Dirichlet trace at `θ = 0`
    intro z
    show Ψ z 0 - Φ z 0 = 0
    rw [hG0 z, hH0 z, sub_zero]
  · -- (3) the Dirichlet trace at `θ = π/2`
    intro z
    show Ψ z (Real.pi / 2) - Φ z (Real.pi / 2) = 0
    rw [hGπ z, hHπ z, sub_zero]
  · -- (4) the source's angular moment
    exact EllWeakAux.Fstar_source_sub k hGc hHc
  · -- (5) the solution's angular moment
    intro z hz
    exact Fstar_sub_of_integrable_left (f := Ψ) (g := Φ) (hGΨst z hz) (hHΨst z hz)
      (EllWeakAux.integrableOn_slice_mul_sinCos2 hsmΨ hGBm z hz)
  · -- (6) `C^∞` on the open quadrant
    intro n
    have hfun : Function.uncurry (fun z θ => Ψ z θ - Φ z θ)
        = fun p : ℝ × ℝ => Function.uncurry Ψ p - Function.uncurry Φ p := rfl
    rw [hfun]
    exact (hGsm n).sub (hHsm n)
  · -- (7) honesty of the source `G - H`
    exact EllWeakAux.HkMem_sub_of_eqOn_Q0 α k hsmG hsmH hGFm hHFm (fun _ _ _ _ _ => rfl)
  · -- (8) honesty of `z² ∂_z²(Ψ - Φ)`
    refine EllWeakAux.HkMem_sub_of_eqOn_Q0 α k ?_ ?_ hGAm hHAm ?_
    · exact Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
        Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
        (Work.FTS.EllipticEst.SmoothOpen.pzIter hsmΨ 2)
    · exact Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
        Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
        (Work.FTS.EllipticEst.SmoothOpen.pzIter hsmΦ 2)
    · intro z hz θ hθ0 hθ1
      have h2 : Work.Spaces.pzIter 2 (fun z θ => Ψ z θ - Φ z θ) z θ
          = Work.Spaces.pzIter 2 Ψ z θ - Work.Spaces.pzIter 2 Φ z θ :=
        Work.FTS.GalBasis.pzIter_sub_eqOn (V := Work.FTS.EllipticEst.Q0)
          Work.FTS.EllipticEst.isOpen_Q0 2 (hsmΨ.forall 3) (hsmΦ.forall 3)
          (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ0, hθ1⟩)
      rw [h2]
      ring
  · -- (9) honesty of `∂_θ²(Ψ - Φ)`
    refine EllWeakAux.HkMem_sub_of_eqOn_Q0 α k ?_ ?_ hGBm hHBm ?_
    · exact Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hsmΨ 2
    · exact Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hsmΦ 2
    · intro z hz θ hθ0 hθ1
      exact Work.FTS.GalBasis.pthIter_sub_eqOn (V := Work.FTS.EllipticEst.Q0)
        Work.FTS.EllipticEst.isOpen_Q0 2 (hsmΨ.forall 3) (hsmΦ.forall 3)
        (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ0, hθ1⟩)
  · -- (10) honesty of `z ∂_z∂_θ²(Ψ - Φ)`
    refine EllWeakAux.HkMem_sub_of_eqOn_Q0 α k ?_ ?_ hGZm hHZm ?_
    · exact Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
        Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
        (Work.FTS.EllipticEst.SmoothOpen.pz
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hsmΨ 2))
    · exact Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
        Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
        (Work.FTS.EllipticEst.SmoothOpen.pz
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hsmΦ 2))
    · intro z hz θ hθ0 hθ1
      rw [pz_pthIter_two_sub hsmΨ hsmΦ z θ hz hθ0 hθ1]
      ring

end Work.FTS.PhiStar.Honesty
