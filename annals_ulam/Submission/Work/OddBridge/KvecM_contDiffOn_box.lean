import Mathlib
import Submission.Work.OddBridge.KernelDefs
import Submission.Work.OddVolterra.Existence.hquot_contDiff

/-!
# `C²` regularity of the manifest odd kernel `KvecM` on a box of slopes

This file proves `Work.OddBridge.KvecM_contDiffOn_box`: on a box of slopes
`(s,σ) ∈ [a,b]²` (`0 < a ≤ b ≤ 1`) the manifest representative
`Work.OddBridge.KvecM` of the paper's odd Abel kernel, evaluated at the two chord endpoints
`t = y σ`, `t = -x σ` together with the derivatives of the curve, is `C²` (in fact `C^∞`)
as a function of `(s,σ)`.

The ingredients are

* `Work.OddBridge.RR` (the Bell recursion) is `C^∞` in the triple `(s,σ,t)` whenever `h` is;
* the divided difference `hquot h` of `h` is `C^∞`;
* `Real.sqrt` is `C^∞` where its argument is non-zero, so `Kden = √((t+H)(L_σ+L_s))` is
  `C^∞` where it is positive (the standing hypothesis that the chord cuts the profile);
* `K₁ = J₁/Kden`, `K₂ = J₂/Kden` are quotients of `C^∞` functions;
* `x`, `y` are `C^∞` on the open set `(0,∞)`, hence so are `deriv x`, `deriv y`
  (`fderivWithin` of a smooth function is smooth).
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddBridge

open Work.OddVolterra

noncomputable section

/-! ## The first-coordinate directional derivative -/

/-- The directional derivative of `F : ℝ × ℝ × ℝ → ℝ` at `(s, σ, t)` in the direction of the
first coordinate equals the one-variable derivative of `u ↦ F (u, σ, t)` at `s`. -/
lemma fderiv_fst_eq_deriv_triple (F : ℝ × ℝ × ℝ → ℝ) (s σ t : ℝ)
    (hF : DifferentiableAt ℝ F (s, σ, t)) :
    (fderiv ℝ F (s, σ, t)) (1, 0, 0) = deriv (fun u : ℝ => F (u, σ, t)) s := by
  have hg : HasFDerivAt (fun u : ℝ => (u, σ, t))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ × ℝ)) s := by
    have h := (hasFDerivAt_id (𝕜 := ℝ) s).prodMk (hasFDerivAt_const (𝕜 := ℝ) (σ, t) s)
    simpa using h
  have hcomp : HasFDerivAt (fun u : ℝ => F (u, σ, t))
      ((fderiv ℝ F (s, σ, t)) ∘SL
        ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ × ℝ))) s := by
    simpa [Function.comp_def] using (hF.hasFDerivAt).comp s hg
  rw [← fderiv_apply_one_eq_deriv, hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rfl

/-- A `C^∞` function on `ℝ × ℝ × ℝ` has a `C^∞` directional derivative in the first
coordinate, as a function of the base point. -/
lemma contDiff_fderiv_fst_triple {F : ℝ × ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ × ℝ => (fderiv ℝ F p) (1, 0, 0) :=
  (hF.fderiv_right le_rfl).clm_apply contDiff_const

/-- For a `C^∞` function `F` on `ℝ × ℝ × ℝ`, the one-variable derivative of `u ↦ F (u,σ,t)`
is the first-coordinate directional derivative of `F`, as a function of `(s,σ,t)`. -/
lemma deriv_fst_eq_fderiv {F : ℝ × ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    (fun p : ℝ × ℝ × ℝ => deriv (fun u : ℝ => F (u, p.2.1, p.2.2)) p.1)
      = fun p : ℝ × ℝ × ℝ => (fderiv ℝ F p) (1, 0, 0) := by
  funext p
  exact (fderiv_fst_eq_deriv_triple F p.1 p.2.1 p.2.2
    (hF.differentiable (by simp) _)).symm

/-! ## The uncurried radicand -/

/-- The radicand `Zrad h` read as a function of the triple `(s,σ,t)`. -/
def Zr (h : ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ := Zrad h p.1 p.2.1 p.2.2

lemma contDiff_Zr {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (Zr h) := by
  unfold Zr Zrad line
  fun_prop

/-- The recursion's `∂_s Z`, read as a function of the triple. -/
lemma contDiff_Zs_triple {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ × ℝ => Zs h p.1 p.2.1 p.2.2 := by
  rw [show (fun p : ℝ × ℝ × ℝ => Zs h p.1 p.2.1 p.2.2)
      = fun p : ℝ × ℝ × ℝ => deriv (fun u : ℝ => Zr h (u, p.2.1, p.2.2)) p.1 from rfl]
  rw [deriv_fst_eq_fderiv (contDiff_Zr hh)]
  exact contDiff_fderiv_fst_triple (contDiff_Zr hh)

/-! ## Smoothness of the Bell recursion -/

/-- **The uncurried Bell recursion is `C^∞`.**  If `h` is `C^∞` and the uncurried
initial datum `initC` is `C^∞`, then `(s,σ,t) ↦ RR ν h initC m s σ t` is `C^∞`. -/
theorem contDiff_RR_triple (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {initC : ℝ → ℝ → ℝ → ℝ}
    (hinit : ContDiff ℝ ∞ fun p : ℝ × ℝ × ℝ => initC p.1 p.2.1 p.2.2) (m : ℕ) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ × ℝ => RR ν h initC m p.1 p.2.1 p.2.2 := by
  induction m with
  | zero => simpa only [RR] using hinit
  | succ m ih =>
    have hZr := contDiff_Zr hh
    have hZs := contDiff_Zs_triple hh
    have hdR : ContDiff ℝ ∞
        fun p : ℝ × ℝ × ℝ => deriv (fun u : ℝ => RR ν h initC m u p.2.1 p.2.2) p.1 := by
      rw [deriv_fst_eq_fderiv
        (F := fun p : ℝ × ℝ × ℝ => RR ν h initC m p.1 p.2.1 p.2.2) ih]
      exact contDiff_fderiv_fst_triple ih
    rw [show (fun p : ℝ × ℝ × ℝ => RR ν h initC (m + 1) p.1 p.2.1 p.2.2)
        = fun p : ℝ × ℝ × ℝ => Zr h p *
            deriv (fun u : ℝ => RR ν h initC m u p.2.1 p.2.2) p.1
          + (ν - (m : ℝ)) * Zs h p.1 p.2.1 p.2.2 * RR ν h initC m p.1 p.2.1 p.2.2
        from rfl]
    fun_prop


/-! ## Composition tools -/

/-- The derivative of a function that is `C^∞` on the open interval `(0,∞)` is again `C^∞`
there. -/
lemma contDiffOn_deriv_Ioi {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g (Set.Ioi 0)) :
    ContDiffOn ℝ ∞ (deriv g) (Set.Ioi 0) := by
  have hfd : ContDiffOn ℝ ∞ (fderivWithin ℝ g (Set.Ioi 0)) (Set.Ioi 0) :=
    hg.fderivWithin (uniqueDiffOn_Ioi 0) le_rfl
  have hfd2 : ContDiffOn ℝ ∞ (fun σ => (fderivWithin ℝ g (Set.Ioi 0) σ) (1 : ℝ))
      (Set.Ioi 0) :=
    hfd.clm_apply contDiffOn_const
  refine hfd2.congr (fun σ hσ => ?_)
  show deriv g σ = (fderivWithin ℝ g (Set.Ioi 0) σ) 1
  rw [fderivWithin_of_isOpen isOpen_Ioi hσ]
  rfl

/-- `Kden h s σ (t p)` is `C^∞` in `p` on `B`, as soon as the third coordinate `t` is and
`Kden` is positive on `B`. -/
lemma contDiffOn_Kden_comp {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {B : Set (ℝ × ℝ)} {t : ℝ × ℝ → ℝ} (ht : ContDiffOn ℝ ∞ t B)
    (htpos : ∀ p ∈ B, 0 < Kden h p.1 p.2 (t p)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Kden h p.1 p.2 (t p)) B := by
  have hquotB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => hquot h p.1 p.2) B :=
    (Work.OddVolterra.Existence.hquot_contDiff hh).contDiffOn
  have hhB1 : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => h p.1) B :=
    (hh.contDiffOn (s := Set.univ)).comp contDiffOn_fst (fun _ _ => trivial)
  have hhB2 : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => h p.2) B :=
    (hh.contDiffOn (s := Set.univ)).comp contDiffOn_snd (fun _ _ => trivial)
  have hrad : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      (t p + hquot h p.1 p.2) * ((p.2 * t p + h p.2) + (p.1 * t p + h p.1))) B :=
    (ht.add hquotB).mul (((contDiffOn_snd.mul ht).add hhB2).add
      ((contDiffOn_fst.mul ht).add hhB1))
  have hsqrt := hrad.sqrt (fun p hp => by
    have h := htpos p hp
    rw [Kden, Real.sqrt_pos, line, line] at h
    exact ne_of_gt h)
  simpa only [Kden, line] using hsqrt

/-! ## The manifest numerators and kernels -/

lemma contDiffOn_J1M_comp (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {B : Set (ℝ × ℝ)} {t : ℝ × ℝ → ℝ} (ht : ContDiffOn ℝ ∞ t B) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => J1M n h p.1 p.2 (t p)) B := by
  have hR : ContDiff ℝ ∞
      (fun q : ℝ × ℝ × ℝ =>
        RR ((n : ℝ) + 1 / 2) h (fun _ _ _ => (1 : ℝ)) (n + 1) q.1 q.2.1 q.2.2) :=
    contDiff_RR_triple ((n : ℝ) + 1 / 2) hh contDiff_const (n + 1)
  have hPhi : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (p.1, p.2, t p)) B :=
    contDiffOn_fst.prodMk (contDiffOn_snd.prodMk ht)
  have hcomp := (hR.contDiffOn (s := Set.univ)).comp hPhi (fun _ _ => trivial)
  simpa only [J1M, Function.comp_def] using hcomp

lemma contDiffOn_J2M_comp (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {B : Set (ℝ × ℝ)} {t : ℝ × ℝ → ℝ} (ht : ContDiffOn ℝ ∞ t B) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => J2M n h p.1 p.2 (t p)) B := by
  have hinit : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => lineSlope h q.1 q.2.2) := by
    unfold lineSlope
    fun_prop
  have hR : ContDiff ℝ ∞
      (fun q : ℝ × ℝ × ℝ =>
        RR ((n : ℝ) - 1 / 2) h (fun s _ t => lineSlope h s t) n q.1 q.2.1 q.2.2) :=
    contDiff_RR_triple ((n : ℝ) - 1 / 2) hh hinit n
  have hPhi : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (p.1, p.2, t p)) B :=
    contDiffOn_fst.prodMk (contDiffOn_snd.prodMk ht)
  have hcomp := (hR.contDiffOn (s := Set.univ)).comp hPhi (fun _ _ => trivial)
  simpa only [J2M, Function.comp_def] using hcomp

lemma contDiffOn_K1M_comp (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {B : Set (ℝ × ℝ)} {t : ℝ × ℝ → ℝ} (ht : ContDiffOn ℝ ∞ t B)
    (htpos : ∀ p ∈ B, 0 < Kden h p.1 p.2 (t p)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => K1M n h p.1 p.2 (t p)) B :=
  (contDiffOn_J1M_comp n hh ht).div (contDiffOn_Kden_comp hh ht htpos)
    (fun p hp => ne_of_gt (htpos p hp))

lemma contDiffOn_K2M_comp (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {B : Set (ℝ × ℝ)} {t : ℝ × ℝ → ℝ} (ht : ContDiffOn ℝ ∞ t B)
    (htpos : ∀ p ∈ B, 0 < Kden h p.1 p.2 (t p)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => K2M n h p.1 p.2 (t p)) B :=
  (contDiffOn_J2M_comp n hh ht).div (contDiffOn_Kden_comp hh ht htpos)
    (fun p hp => ne_of_gt (htpos p hp))

theorem KvecM_contDiffOn_box (n : ℕ) {h x y : ℝ → ℝ} {a b : ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x (Set.Ioi 0)) (hy : ContDiffOn ℝ (⊤ : ℕ∞) y (Set.Ioi 0))
    (ha : 0 < a) (hb : b ≤ 1)
    (hposy : ∀ s σ : ℝ, s ∈ Set.Icc a b → σ ∈ Set.Icc a b → 0 < Work.OddVolterra.Kden h s σ (y σ))
    (hposx : ∀ s σ : ℝ, s ∈ Set.Icc a b → σ ∈ Set.Icc a b → 0 < Work.OddVolterra.Kden h s σ (-(x σ))) :
    ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => Work.OddBridge.KvecM n h p.1 p.2 (x p.2) (y p.2) (deriv x p.2) (deriv y p.2))
      (Set.Icc a b ×ˢ Set.Icc a b) := by
  have hmaps : MapsTo (fun p : ℝ × ℝ => p.2) (Set.Icc a b ×ˢ Set.Icc a b) (Set.Ioi 0) :=
    fun p hp => lt_of_lt_of_le ha hp.2.1
  have hxB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => x p.2) (Set.Icc a b ×ˢ Set.Icc a b) :=
    hx.comp contDiffOn_snd hmaps
  have hyB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => y p.2) (Set.Icc a b ×ˢ Set.Icc a b) :=
    hy.comp contDiffOn_snd hmaps
  have hdxB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => deriv x p.2) (Set.Icc a b ×ˢ Set.Icc a b) :=
    (contDiffOn_deriv_Ioi hx).comp contDiffOn_snd hmaps
  have hdyB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => deriv y p.2) (Set.Icc a b ×ˢ Set.Icc a b) :=
    (contDiffOn_deriv_Ioi hy).comp contDiffOn_snd hmaps
  have hK1x : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => K1M n h p.1 p.2 (-(x p.2)))
      (Set.Icc a b ×ˢ Set.Icc a b) :=
    contDiffOn_K1M_comp n hh hxB.neg (fun p hp => hposx p.1 p.2 hp.1 hp.2)
  have hK1y : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => K1M n h p.1 p.2 (y p.2))
      (Set.Icc a b ×ˢ Set.Icc a b) :=
    contDiffOn_K1M_comp n hh hyB (fun p hp => hposy p.1 p.2 hp.1 hp.2)
  have hK2x : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => K2M n h p.1 p.2 (-(x p.2)))
      (Set.Icc a b ×ˢ Set.Icc a b) :=
    contDiffOn_K2M_comp n hh hxB.neg (fun p hp => hposx p.1 p.2 hp.1 hp.2)
  have hK2y : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => K2M n h p.1 p.2 (y p.2))
      (Set.Icc a b ×ˢ Set.Icc a b) :=
    contDiffOn_K2M_comp n hh hyB (fun p hp => hposy p.1 p.2 hp.1 hp.2)
  have hgoal : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => KvecM n h p.1 p.2
      (x p.2) (y p.2) (deriv x p.2) (deriv y p.2)) (Set.Icc a b ×ˢ Set.Icc a b) := by
    rw [contDiffOn_pi]
    intro i
    fin_cases i
    · simpa [KvecM] using ((hK1x.mul hdxB).add (hK1y.mul hdyB)).neg
    · simpa [KvecM] using ((hK2x.mul hdxB).add (hK2y.mul hdyB)).neg
  exact hgoal.of_le (WithTop.coe_le_coe.mpr le_top)

end

end Work.OddBridge
