import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.PhiStar.EllExistHalf
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.ellWeakPos_sub =====
section

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
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OpenCoer.SlotWCommon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OpenCoer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Measurability and integrability of the datum -/

/-- An `SmoothOpen` datum is a.e. strongly measurable for the product of the two restricted
measures (the two differ from the open quadrant by a null set). -/
theorem aesm_f_open {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ hs.continuousOn



/-- `(f w)²` is jointly integrable, from the `D_z⁰`-certificate of `IntPkgO`. -/
theorem hfw_open {α : ℝ} {f : Fn} (hIP : IntPkgO α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine (hIP.sqDzOne 0 (by norm_num)).congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
  rintro ⟨z, θ⟩ _
  simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
  ring

/-- The `f²w²` form of the previous certificate, as used by `wip_G_bound`. -/
theorem hfw2_open {α : ℝ} {f : Fn} (hIP : IntPkgO α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine (hfw_open hIP).congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
  rintro ⟨z, θ⟩ _
  simp only [Function.uncurry_apply_pair]
  ring

/-! ## The two halves of the `L₁₂`-pairing, and the `L₁₂`-term -/

/-- The `K`-part of the `L₁₂`-pairing is jointly integrable (open class). -/
theorem intK_O (α : ℝ) (hα : 0 < α) {f : Fn} (hIP : IntPkgO α f)
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hHH : Work.Coercivity.HardyHyp f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.w z / z * Work.Coercivity.L12f f z
        * (Work.Spaces.K θ * f z θ))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
  Work.FTS.CoercivityFix.Coer1T.intMul_L12_Q hHH (hfw_open hIP) (aesm_f_open hs)
    Work.Spaces.K Work.Coercivity.integrableOn_Kθ_sq
    (Work.Coercivity.continuousOn_Kθ.aestronglyMeasurable measurableSet_Icc)

/-- The `(Γ/c - K)`-part of the `L₁₂`-pairing is jointly integrable (open class). -/
theorem intG_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn} (hIP : IntPkgO α f)
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hHH : Work.Coercivity.HardyHyp f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.w z / z * Work.Coercivity.L12f f z
        * ((Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) * f z θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
  Work.FTS.CoercivityFix.Coer1T.intMul_L12_Q hHH (hfw_open hIP) (aesm_f_open hs)
    (fun θ => Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ)
    (Work.Coercivity.integrableOn_GammaK_sq α hα hα1)
    (((Work.Coercivity.continuousOn_Gam α hα).div_const (Work.Spaces.c α)).sub
      Work.Coercivity.continuousOn_Kθ |>.aestronglyMeasurable measurableSet_Icc)

/-- The `L₁₂`-term of `𝓛_Γ` against `f w²` is jointly integrable (open class). -/
theorem intT1_w2_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn} (hIP : IntPkgO α f)
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hHH : Work.Coercivity.HardyHyp f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        (2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
          * Work.Coercivity.L12f f z * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hGam2 : MeasureTheory.Integrable
      (fun θ : ℝ => (2 * Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.of_bound ?_ 400 ?_
    · exact ((((Work.Coercivity.continuousOn_Gam α hα).const_mul
        (2 : ℝ)).div_const (Work.Spaces.c α)).pow 2).aestronglyMeasurable measurableSet_Icc
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 :=
        Work.Coercivity.Gam_div_c_bound hα hα1 hθ
      have h2 : |2 * Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 20 := by
        rw [show 2 * Work.Spaces.Gam α θ / Work.Spaces.c α
            = 2 * (Work.Spaces.Gam α θ / Work.Spaces.c α) by ring,
          abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith
      nlinarith [abs_nonneg (2 * Work.Spaces.Gam α θ / Work.Spaces.c α),
        sq_abs (2 * Work.Spaces.Gam α θ / Work.Spaces.c α)]
  have hcm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => 2 * Work.Spaces.Gam α θ / Work.Spaces.c α)
      (volume.restrict Work.Spaces.Iθ) :=
    (((Work.Coercivity.continuousOn_Gam α hα).const_mul (2 : ℝ)).div_const
      (Work.Spaces.c α)).aestronglyMeasurable measurableSet_Icc
  refine (Work.FTS.CoercivityFix.Coer1T.intMul_L12_Q hHH (hfw_open hIP) (aesm_f_open hs)
    (fun θ => 2 * Work.Spaces.Gam α θ / Work.Spaces.c α) hGam2 hcm).congr_fun ?_
    (measurableSet_Ici.prod measurableSet_Icc)
  rintro ⟨z, θ⟩ _
  simp only [Function.uncurry_apply_pair, Work.Spaces.w]
  rcases eq_or_ne z 0 with rfl | hz
  · norm_num
  · field_simp

/-- The `𝓛_Γ f · f w²` pairing is jointly integrable (open class): `𝓛_Γ = 𝓛 - (2zΓ/(c(1+z)²))L₁₂f`
and both halves are known to be integrable. -/
theorem intLG_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn} (hIP : IntPkgO α f)
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hHH : Work.Coercivity.HardyHyp f) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.LGamma α f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := hIP.intL_f_one.sub (intT1_w2_O α hα hα1 hIP hs hHH)
  rw [MeasureTheory.IntegrableOn] at h ⊢
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Pi.sub_apply, Work.Coercivity.LGamma]
  ring

/-! ## The `D_θ`-pairing and the projector kernel -/

/-- `(D_θ f)² w²` is jointly integrable (open class), from the `(i,j) = (1,0)` mixed certificate of
`IntPkgO` (`mixed 0 1 = D_θ`). -/
theorem intDth2_O {α : ℝ} {f : Fn} (hIP : IntPkgO α f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine (hIP.sqMixedOne 1 0 (by norm_num) (by norm_num)).congr_fun ?_
    (measurableSet_Ici.prod measurableSet_Icc)
  rintro ⟨z, θ⟩ _
  simp only [Function.uncurry_apply_pair, Work.Spaces.mixed, Work.Spaces.DzIter_zero,
    Work.Spaces.DthIter_zero, Work.Spaces.DthIter_succ]
  ring

/-- The a.e. strong measurability of `D_θ f · w` (open class). -/
theorem aesm_dth_mul_w_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (((hs.Dth).forall 0).continuousOn.mul Work.Coercivity.continuousOn_w_quad)

/-- **The bound `(C₀ f)² ≤ EDthW f` in the open class**: `L₁₂(Transport f)(0)` is a linear
functional of `D_θ f · w` whose kernel `3K(θ)z/(1+z)³` has `L²`-norm at most `1`. -/
theorem C0_sq_le_EDthW_O {α : ℝ} (hα : 0 < α) {f : Fn} (hIP : IntPkgO α f)
    (hs : Work.FTS.EllipticEst.SmoothOpen f) :
    (Work.Coercivity.C0 f) ^ 2 ≤ Work.Coercivity.EDthW f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Iz).prod
    (volume.restrict Work.Spaces.Iθ) with hP
  set u : ℝ × ℝ → ℝ :=
    fun p => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1 with hu
  set v : ℝ × ℝ → ℝ :=
    fun p => 3 * Work.Spaces.K p.2 * p.1 / (1 + p.1) ^ 3 with hv
  have hint := intDth2_O hIP
  have hu2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => u p ^ 2) P := by
    have h := Work.Coercivity.integrableOn_prod (g := fun z θ => Work.Spaces.Dth f z θ
      * Work.Spaces.Dth f z θ * Work.Spaces.w z ^ 2) hint
    exact h.congr (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩
      simp only [hu]
      ring)
  have hv2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => v p ^ 2) P := by
    have hran : MeasureTheory.Integrable (fun z : ℝ => 9 * (z ^ 2 / (1 + z) ^ 6))
        (volume.restrict Work.Spaces.Iz) :=
      Work.Coercivity.integrable_Iz_zsq_div_six.const_mul 9
    have hmul : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (9 * (p.1 ^ 2 / (1 + p.1) ^ 6)) * ((Work.Spaces.K p.2) ^ 2)) P :=
      hran.mul_prod Work.Coercivity.integrableOn_Kθ_sq
    refine hmul.congr ?_
    filter_upwards [Work.Coercivity.ae_prod_pos] with p hp
    have hp1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith [show (0 : ℝ) < p.1 from hp])
    simp only [hv]
    field_simp
    ring
  have huA : MeasureTheory.MemLp u 2 P :=
    (MeasureTheory.memLp_two_iff_integrable_sq (aesm_dth_mul_w_O hs)).2 hu2
  have hvA : MeasureTheory.MemLp v 2 P := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).2 hv2
    rw [hv]
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.K]
    fun_prop
  have hC0id : Work.Coercivity.C0 f = ∫ p, u p * v p ∂P := by
    have hdef : Work.Coercivity.C0 f = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s := by
      simp only [Work.Coercivity.C0, Work.Coercivity.L12f, Work.FM.L12, Work.FM.L12dens,
        Work.Spaces.Iθ]
    rw [hdef]
    have h1 : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s)
        = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ, u (s, θ) * v (s, θ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [hu, hv, Work.Coercivity.Transport, Work.Spaces.w]
      have hs0 : s ≠ 0 := ne_of_gt hs
      have hs1 : 1 + s ≠ 0 := ne_of_gt (by linarith [show (0 : ℝ) < s from hs])
      field_simp
    rw [h1]
    rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact (MeasureTheory.integral_prod (fun p : ℝ × ℝ => u p * v p)
      (huA.integrable_mul hvA)).symm
  have hunorm : ∫ p, u p ^ 2 ∂P = Work.Coercivity.EDthW f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDthW_eq_prod hint]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨z, θ⟩
    simp only [hu]
    ring
  have hsep : ∫ p, v p ^ 2 ∂P
      = (∫ z in Work.Spaces.Iz, 9 * (z ^ 2 / (1 + z) ^ 6))
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) := by
    have hcongr : (fun p : ℝ × ℝ => v p ^ 2)
        =ᵐ[P] fun p : ℝ × ℝ => (9 * (p.1 ^ 2 / (1 + p.1) ^ 6))
            * ((Work.Spaces.K p.2) ^ 2) := by
      filter_upwards [Work.Coercivity.ae_prod_pos] with p hp
      have hp1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith [show (0 : ℝ) < p.1 from hp])
      simp only [hv]; field_simp; ring
    rw [MeasureTheory.integral_congr_ae hcongr]
    have hran : MeasureTheory.Integrable (fun z : ℝ => 9 * (z ^ 2 / (1 + z) ^ 6))
        (volume.restrict Work.Spaces.Iz) :=
      Work.Coercivity.integrable_Iz_zsq_div_six.const_mul 9
    exact Work.Coercivity.integral_prod_sep _ _ hran Work.Coercivity.integrableOn_Kθ_sq
  have hvnorm : ∫ p, v p ^ 2 ∂P ≤ 1 := by
    rw [hsep]
    have h1 : (∫ z in Work.Spaces.Iz, 9 * (z ^ 2 / (1 + z) ^ 6)) = 3 / 10 := by
      rw [MeasureTheory.integral_const_mul, Work.Coercivity.integral_Iz_zsq_div_six]
      norm_num
    have h2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) ≤ 9 / 4 :=
      Work.Coercivity.integral_Iθ_Ksq_le
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2 :=
      integral_nonneg fun θ => sq_nonneg _
    rw [h1]
    nlinarith [h2, hnn]
  calc (Work.Coercivity.C0 f) ^ 2 = (∫ p, u p * v p ∂P) ^ 2 := by rw [hC0id]
    _ ≤ (∫ p, u p ^ 2 ∂P) * (∫ p, v p ^ 2 ∂P) :=
        Work.Coercivity.cs_integral_mul huA hvA
    _ ≤ Work.Coercivity.EDthW f * 1 := by
        rw [hunorm]
        exact mul_le_mul_of_nonneg_left hvnorm
          (by rw [← hunorm]; exact integral_nonneg fun p => sq_nonneg _)
    _ = Work.Coercivity.EDthW f := mul_one _

end Work.FTS.StrongEps.EpsE4Thr.OpenCoer
end
end
