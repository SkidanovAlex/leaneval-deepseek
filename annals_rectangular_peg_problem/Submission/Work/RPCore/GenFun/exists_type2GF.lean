import Mathlib
import Submission.Work.RPCore.Defs
import Submission.Work.RPCore.GenFun.Basic
import Submission.Work.RPCore.GenFun.rayPrimitive
import Submission.Work.RPCore.GenFun.slab_preconnected
import Submission.Work.RPCore.GenFun.invMap_spec
import Submission.Work.RPCore.GenFun.bvec_curl_free

set_option autoImplicit false

noncomputable section

open Work.RPV
open Real

namespace Work.RPCore.GenFun

/-! ## Auxiliary lemmas for the assembly of `exists_type2GF` -/

/-- The slab function `|q₁| + |p₁| + |p₂|` appearing in the hypotheses and conclusion. -/
def stuff (y : PS) : ℝ := |y.1.1| + |y.2.1| + |y.2.2|

theorem stuff_apply (y : PS) : stuff y = |y.1.1| + |y.2.1| + |y.2.2| := rfl

theorem continuous_stuff : Continuous stuff := by
  unfold stuff
  fun_prop

theorem dotL_zero : dotL (0 : PS) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  simp [dotL_apply, dot]

/-- A point far outside the slab `{|q₁| + |p₁| + |p₂| ≤ R}`. -/
def y0 (R : ℝ) : PS := ((|R| + 1, 0), (0, 0))

theorem lt_y0 (R : ℝ) : R < stuff (y0 R) := by
  have h : stuff (y0 R) = |R| + 1 := by
    simp [y0, stuff, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |R| + 1)]
  rw [h]
  linarith [le_abs_self R]

/-! ### The shift `Tk 1` -/

@[simp] theorem Tk_fst (k : ℤ) (x : PS) : (Tk k x).1 = (x.1.1, x.1.2 + 2 * π * k) := rfl

@[simp] theorem Tk_snd (k : ℤ) (x : PS) : (Tk k x).2 = x.2 := rfl

theorem Tk_one_eq (x : PS) : Tk 1 x = x + (((0 : ℝ), 2 * π), (0, 0)) := by
  simp [Tk, Prod.ext_iff]

theorem Tk_one_translate : (Tk 1 : PS → PS) = fun z : PS => z + (((0 : ℝ), 2 * π), (0, 0)) :=
  funext Tk_one_eq

theorem differentiable_Tk_one : Differentiable ℝ (Tk 1) := by
  rw [Tk_one_translate]
  exact differentiable_id.add_const _

theorem hasFDerivAt_Tk_one (y : PS) : HasFDerivAt (Tk 1) (1 : PS →L[ℝ] PS) y := by
  rw [Tk_one_translate]
  exact (hasFDerivAt_id y).add_const _

theorem fderiv_Tk_one (y : PS) : fderiv ℝ (Tk 1) y = 1 := (hasFDerivAt_Tk_one y).fderiv

theorem gproj_Tk {ψ : PS → PS} (hper : ∀ x, ψ (Tk 1 x) = Tk 1 (ψ x)) (x : PS) :
    gproj ψ (Tk 1 x) = Tk 1 (gproj ψ x) := by
  simp only [gproj_apply]
  rw [hper]
  ext <;> simp [Tk]

theorem invMap_Tk {ψ : PS → PS} (hper : ∀ x, ψ (Tk 1 x) = Tk 1 (ψ x))
    (hleft : ∀ x, invMap ψ (gproj ψ x) = x) (hright : ∀ y, gproj ψ (invMap ψ y) = y)
    (y : PS) : invMap ψ (Tk 1 y) = Tk 1 (invMap ψ y) := by
  have hinj : Function.Injective (gproj ψ) := fun a b h => by rw [← hleft a, h, hleft b]
  apply hinj
  rw [hright, gproj_Tk hper, hright]

theorem pfun_Tk {ψ : PS → PS} (hper : ∀ x, ψ (Tk 1 x) = Tk 1 (ψ x))
    (hleft : ∀ x, invMap ψ (gproj ψ x) = x) (hright : ∀ y, gproj ψ (invMap ψ y) = y)
    (y : PS) : pfun ψ (Tk 1 y) = pfun ψ y := by
  show (invMap ψ (Tk 1 y)).2 = (invMap ψ y).2
  rw [invMap_Tk hper hleft hright]
  exact Tk_snd 1 (invMap ψ y)

theorem Qfun_Tk {ψ : PS → PS} (hper : ∀ x, ψ (Tk 1 x) = Tk 1 (ψ x))
    (hleft : ∀ x, invMap ψ (gproj ψ x) = x) (hright : ∀ y, gproj ψ (invMap ψ y) = y)
    (y : PS) : Qfun ψ (Tk 1 y) = ((Qfun ψ y).1, (Qfun ψ y).2 + 2 * π) := by
  have h1 : invMap ψ (Tk 1 y) = Tk 1 (invMap ψ y) := invMap_Tk hper hleft hright y
  show (ψ (invMap ψ (Tk 1 y))).1 = ((Qfun ψ y).1, (Qfun ψ y).2 + 2 * π)
  rw [h1, hper]
  show ((ψ (invMap ψ y)).1.1, (ψ (invMap ψ y)).1.2 + 2 * π * (1 : ℤ)) = _
  rw [show ((1 : ℤ) : ℝ) = 1 by norm_num]
  rw [show Qfun ψ y = (ψ (invMap ψ y)).1 from rfl]
  ext <;> ring

theorem bvec_Tk {ψ : PS → PS} (hper : ∀ x, ψ (Tk 1 x) = Tk 1 (ψ x))
    (hleft : ∀ x, invMap ψ (gproj ψ x) = x) (hright : ∀ y, gproj ψ (invMap ψ y) = y)
    (y : PS) : bvec ψ (Tk 1 y) = bvec ψ y := by
  simp only [bvec, pfun_Tk hper hleft hright, Qfun_Tk hper hleft hright]
  ext <;> simp <;> ring

@[simp] theorem stuff_Tk (y : PS) : stuff (Tk 1 y) = stuff y := by
  simp [stuff, Tk]

/-! ### Smoothness and vanishing of `bvec` -/

theorem contDiff_bvec (ψ : PS → PS) (hψ : ContDiff ℝ 3 ψ)
    (hinv : ContDiff ℝ 3 (invMap ψ)) : ContDiff ℝ 3 (bvec ψ) := by
  have h : (bvec ψ) = fun y : PS =>
      ((invMap ψ y).2, (ψ (invMap ψ y)).1) - (y.2, y.1) := by
    funext y
    simp only [bvec, pfun, Qfun, Prod.mk_sub_mk]
  rw [h]
  exact (ContDiff.prodMk (contDiff_snd.comp hinv) (contDiff_fst.comp (hψ.comp hinv))).sub
    (ContDiff.prodMk contDiff_snd contDiff_fst)

theorem bvec_eq_zero (ψ : PS → PS) (R : ℝ)
    (hid : ∀ x, R ≤ stuff x → ψ x = x)
    (hleft : ∀ x, invMap ψ (gproj ψ x) = x) (y : PS) (hy : R ≤ stuff y) :
    bvec ψ y = 0 := by
  have hpsy : ψ y = y := hid y hy
  have hgy : gproj ψ y = y := by simp [gproj, hpsy]
  have him : invMap ψ y = y := by
    have h1 : invMap ψ (gproj ψ y) = y := hleft y
    rwa [hgy] at h1
  simp [bvec, pfun, Qfun, him, hpsy]

/-! ### From the derivative of `W` to `IsType2GF` -/

theorem dq_eq_of_fderiv {ψ : PS → PS} {W : PS → ℝ}
    (hW : ∀ y, fderiv ℝ W y = dotL (bvec ψ y)) (q P : ℝ × ℝ) :
    dq W q P = pfun ψ (q, P) - P := by
  have h : fderiv ℝ W (q, P) = dotL (bvec ψ (q, P)) := hW (q, P)
  show (fderiv ℝ W (q, P) ((1, 0), (0, 0)), fderiv ℝ W (q, P) ((0, 1), (0, 0))) = _
  rw [h]
  ext <;> simp [bvec, dot]

theorem dP_eq_of_fderiv {ψ : PS → PS} {W : PS → ℝ}
    (hW : ∀ y, fderiv ℝ W y = dotL (bvec ψ y)) (q P : ℝ × ℝ) :
    dP W q P = Qfun ψ (q, P) - q := by
  have h : fderiv ℝ W (q, P) = dotL (bvec ψ (q, P)) := hW (q, P)
  show (fderiv ℝ W (q, P) ((0, 0), (1, 0)), fderiv ℝ W (q, P) ((0, 0), (0, 1))) = _
  rw [h]
  ext <;> simp [bvec, dot]

theorem isType2GF_of_fderiv {ψ : PS → PS} {W : PS → ℝ}
    (hleft : ∀ x, invMap ψ (gproj ψ x) = x)
    (hright : ∀ y, gproj ψ (invMap ψ y) = y)
    (hW : ∀ y, fderiv ℝ W y = dotL (bvec ψ y)) : IsType2GF ψ W := by
  intro q p Q P
  rw [dq_eq_of_fderiv hW q P, dP_eq_of_fderiv hW q P]
  constructor
  · intro h
    have hg : gproj ψ (q, p) = (q, P) := by simp [gproj, h]
    have him : invMap ψ (q, P) = (q, p) := by rw [← hg]; exact hleft (q, p)
    have hp : pfun ψ (q, P) = p := by simp [pfun, him]
    have hQ : Qfun ψ (q, P) = Q := by simp [Qfun, him, h]
    constructor
    · rw [hp]; abel
    · rw [hQ]; abel
  · rintro ⟨h1, h2⟩
    have hp : p = pfun ψ (q, P) := by rw [h1]; abel
    have hQ : Q = Qfun ψ (q, P) := by rw [h2]; abel
    have hpsi := psi_invMap ψ (hright (q, P))
    rw [invMap_eq ψ (hright (q, P))] at hpsi
    rw [hp, hQ]
    simpa using hpsi

/-! ### Assembly from a primitive -/

theorem exists_type2GF_of_primitive (ψ : PS → PS) (W0 : PS → ℝ) (R : ℝ)
    (hW0 : ContDiff ℝ 3 W0)
    (hW0d : ∀ y, fderiv ℝ W0 y = dotL (bvec ψ y))
    (hleft : ∀ x, invMap ψ (gproj ψ x) = x)
    (hright : ∀ y, gproj ψ (invMap ψ y) = y)
    (hbvec0 : ∀ y, R ≤ stuff y → bvec ψ y = 0)
    (hbvecTk : ∀ y, bvec ψ (Tk 1 y) = bvec ψ y)
    (hpre : IsPreconnected {y : PS | R < stuff y}) :
    ∃ W : PS → ℝ, ContDiff ℝ 3 W ∧ IsType2GF ψ W ∧ (∀ x, W (Tk 1 x) = W x) ∧
      ∃ R' : ℝ, ∀ x, R' ≤ stuff x → W x = 0 := by
  have hopen : IsOpen {y : PS | R < stuff y} :=
    isOpen_lt continuous_const continuous_stuff
  have hdiff : DifferentiableOn ℝ W0 {y : PS | R < stuff y} :=
    (hW0.differentiable (by norm_num)).differentiableOn
  have hzero : Set.EqOn (fderiv ℝ W0) 0 {y : PS | R < stuff y} := by
    intro y hy
    rw [hW0d y, hbvec0 y (le_of_lt hy)]
    exact dotL_zero
  obtain ⟨c, hc⟩ := hopen.exists_is_const_of_fderiv_eq_zero hpre hdiff hzero
  let W : PS → ℝ := fun y => W0 y - c
  have hWd : ∀ y, fderiv ℝ W y = dotL (bvec ψ y) := by
    intro y
    show fderiv ℝ (fun y => W0 y - c) y = _
    rw [fderiv_sub_const]
    exact hW0d y
  have hWsmooth : ContDiff ℝ 3 W := by
    show ContDiff ℝ 3 (fun y => W0 y - c)
    exact hW0.sub contDiff_const
  have hWdiff : Differentiable ℝ W := hWsmooth.differentiable (by norm_num)
  have hfar : ∀ y : PS, R < stuff y → W (Tk 1 y) = W y := by
    intro y hy
    show W0 (Tk 1 y) - c = W0 y - c
    rw [hc (Tk 1 y) (by simpa using hy), hc y hy]
  have hcomp : ∀ z : PS,
      HasFDerivAt (fun z : PS => W (Tk 1 z)) (fderiv ℝ W (Tk 1 z)) z := by
    intro z
    have h4 : HasFDerivAt (fun z : PS => W (Tk 1 z))
        (fderiv ℝ W (Tk 1 z) ∘SL (1 : PS →L[ℝ] PS)) z :=
      (hWdiff (Tk 1 z)).hasFDerivAt.comp z (hasFDerivAt_Tk_one z)
    have h5 : (fderiv ℝ W (Tk 1 z) ∘SL (1 : PS →L[ℝ] PS)) = fderiv ℝ W (Tk 1 z) :=
      ContinuousLinearMap.comp_id _
    rw [h5] at h4
    exact h4
  have hDzero : ∀ z : PS, fderiv ℝ (fun z : PS => W (Tk 1 z) - W z) z = 0 := by
    intro z
    have hsub : HasFDerivAt (fun z : PS => W (Tk 1 z) - W z)
        (fderiv ℝ W (Tk 1 z) - fderiv ℝ W z) z :=
      (hcomp z).sub (hWdiff z).hasFDerivAt
    rw [hsub.fderiv, hWd (Tk 1 z), hWd z, hbvecTk z, sub_self]
  have hDdiff : DifferentiableOn ℝ (fun z : PS => W (Tk 1 z) - W z) Set.univ := by
    apply DifferentiableOn.sub
    · exact (hWdiff.comp differentiable_Tk_one).differentiableOn
    · exact hWdiff.differentiableOn
  have hDconst : ∀ a b : PS, W (Tk 1 a) - W a = W (Tk 1 b) - W b :=
    fun a b => isOpen_univ.is_const_of_fderiv_eq_zero isPreconnected_univ hDdiff
      (fun z _ => hDzero z) (Set.mem_univ a) (Set.mem_univ b)
  have hper : ∀ x, W (Tk 1 x) = W x := by
    intro x
    have hx := hDconst x (y0 R)
    have h2 : W (Tk 1 (y0 R)) - W (y0 R) = 0 := by rw [hfar (y0 R) (lt_y0 R), sub_self]
    have : W (Tk 1 x) - W x = 0 := by rw [hx, h2]
    exact sub_eq_zero.mp this
  refine ⟨W, hWsmooth, isType2GF_of_fderiv hleft hright hWd, hper, R + 1, ?_⟩
  intro x hx
  have hx' : R < stuff x := by linarith
  show W0 x - c = 0
  rw [hc x hx', sub_self]

end Work.RPCore.GenFun

namespace Work.RPCore.GenFun

theorem exists_type2GF (ψ : Work.RPV.PS → Work.RPV.PS) (hψ : ContDiff ℝ 3 ψ)
    (hsymp : ∀ x a b, Work.RPV.symp (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) = Work.RPV.symp a b)
    (hnear : ∀ x, ‖fderiv ℝ ψ x - ContinuousLinearMap.id ℝ Work.RPV.PS‖ ≤ 1 / 4)
    (hper : ∀ x, ψ (Work.RPV.Tk 1 x) = Work.RPV.Tk 1 (ψ x)) (R : ℝ)
    (hid : ∀ x, R ≤ |x.1.1| + |x.2.1| + |x.2.2| → ψ x = x) :
    ∃ W : Work.RPV.PS → ℝ, ContDiff ℝ 3 W ∧ Work.RPV.IsType2GF ψ W ∧ (∀ x, W (Work.RPV.Tk 1 x) = W x) ∧
      ∃ R' : ℝ, ∀ x, R' ≤ |x.1.1| + |x.2.1| + |x.2.2| → W x = 0 := by
  obtain ⟨hbij, hleft, hright, hinv_smooth, hderiv⟩ := invMap_spec ψ hψ hnear
  have hcurl : ∀ y u v, dot (fderiv ℝ (bvec ψ) y u) v = dot (fderiv ℝ (bvec ψ) y v) u :=
    bvec_curl_free ψ hψ hsymp hnear hderiv
  have hbs : ContDiff ℝ 3 (bvec ψ) := contDiff_bvec ψ hψ hinv_smooth
  obtain ⟨hW0s, hW0d⟩ := rayPrimitive (bvec ψ) hbs hcurl
  have hbvec0 : ∀ y, R ≤ stuff y → bvec ψ y = 0 :=
    fun y hy => bvec_eq_zero ψ R (fun x hx => hid x hx) hleft y hy
  have hbvecTk : ∀ y, bvec ψ (Tk 1 y) = bvec ψ y := bvec_Tk hper hleft hright
  obtain ⟨W, hWs, htype, hperW, hR⟩ :=
    exists_type2GF_of_primitive ψ (fun y : PS => ∫ t in (0 : ℝ)..1, dot (bvec ψ (t • y)) y) R
      hW0s hW0d hleft hright hbvec0 hbvecTk (slab_preconnected R)
  refine ⟨W, hWs, htype, hperW, ?_⟩
  obtain ⟨R', hR'⟩ := hR
  exact ⟨R', fun x hx => hR' x hx⟩

end Work.RPCore.GenFun
