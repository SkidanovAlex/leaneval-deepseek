import Mathlib
import Submission.Work.WilE3.Frame.CutSys
import Submission.Work.WilE3.Frame.CurveConst
import Submission.Work.WilE3.Frame.frame_line_deriv
import Submission.Work.WilE3.Frame.partial_curve_eq_Vword
import Submission.Work.WilE3.Frame.Vword_toC_eq_zero

namespace Work.WilE3.Frame

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

noncomputable section

variable {k r j : ℕ}

/-- The real direction `w : U k ι → ℝ`, extended by `0` off `Set.range ι`. -/
def wextR (ι : Fin j → Fin k) (w : U k ι → ℝ) : Fin k → ℝ :=
  fun l => if h : l ∈ Set.range ι then 0 else w ⟨l, h⟩

/-- The real direction `w : U k ι → ℝ` of the statement, extended by `0` off `Set.range ι` and
viewed as a complex vector. -/
def wextC (ι : Fin j → Fin k) (w : U k ι → ℝ) : Fin k → ℂ :=
  fun l => ((wextR ι w l : ℝ) : ℂ)

/-- On the tangential coordinates, `wextC ι w` agrees with `w`. -/
theorem wextC_apply (ι : Fin j → Fin k) (w : U k ι → ℝ) (i : U k ι) :
    wextC ι w i.1 = (w i : ℂ) := by
  simp [wextC, wextR, i.2]

/-- The `ιᶜ`-coordinates of `toC x + t • (wextC ι w)` are exactly
`uCoord k ι (toC x) + t • w`: `wextC ι w` transports `w` on the tangential coordinates and
vanishes on `Set.range ι`. -/
theorem uCoord_toC_add_smul_wextC (ι : Fin j → Fin k) (x : Fin k → ℝ)
    (w : U k ι → ℝ) (t : ℂ) :
    (fun i : U k ι => (toC x + t • wextC ι w) i.1)
      = uCoord k ι (toC x) + t • (fun i : U k ι => (w i : ℂ)) := by
  funext i
  simp [uCoord, toC, wextC, wextR, i.2]

/-- **Frame half, one-variable form.**  If every ordered reduced derivative
`opMono c h ι m f` of `f` at `x` of order `≤ Mv` with `m` supported off `Set.range ι` vanishes, then
for every real direction `w : U k ι → ℝ` all derivatives of order `≤ Mv` of the one-variable
function `t ↦ eaEvalC c f (Ψ (u₀ + t • w_ℂ, 0))` vanish at `0` (where `Ψ` straightens `{h = 0}` at
`x`, `u₀ = uCoord k ι (toC x)`, and `w_ℂ` is `w` viewed in `ℂ`).

Ingredients (each to be imported as needed):
* `Work.WilE3.Frame.partial_curve_eq_Vword` identifies the *ordered mixed partials* of
  `F : (Fin k → ℂ) → ℂ`, `F u = eaEvalC c f (Ψ (u|_ιᶜ, 0))`, with the frame words
  `Vword c h ι m (eaEvalC c f)` at `toC x` (for `m` supported off `ι`);
* `Work.WilE3.Frame.Vword_toC_eq_zero` makes those vanish under the hypothesis `hvan`;
* for `m` with some *positive* `ι`-exponent, `Work.WilE3.Frame.fold_finRange_eq_zero_of_constAlong`
  (in `Submission.Work.WilE3.Frame.FoldZero`) shows that the corresponding ordered partial is
  identically zero, because `Work.WilE3.Frame.constAlong_comp_subtype`
  (in `Submission.Work.WilE3.Frame.CurveConst`) says `F` is constant along every coordinate in
  `Set.range ι`;
* hence the hypothesis of `Work.WilE3.Frame.iteratedDeriv_line_eq_zero` (analyticity of `F` at
  `toC x` plus vanishing of all its ordered partials of order `≤ Mv`) holds, and it gives the
  vanishing of the `Mv`-th derivative (apply it to each `i ≤ Mv`) along the line
  `t ↦ toC x + t • w̃` where `w̃` is `w` extended by `0` off `Set.range ι`; the copy of that lemma
  used below is `Work.WilE3.Frame.frame_line_deriv` (`Submission.Work.WilE3.Frame.frame_line_deriv`),
  a module that does not import `IterLineAux` (the auxiliary module of
  `iteratedDeriv_line_eq_zero`), which declares `Work.WilE3.Frame.edir_congr` — the same name that
  `curve_chain_rule` (a dependency of `partial_curve_eq_Vword`) already declares — so that the two
  chains cannot be imported together;
* finally `F (toC x + t • w̃) = eaEvalC c f (Ψ (u₀ + t • w_ℂ, 0))` (both sides have the same
  `ιᶜ`-coordinates).

Note `Work.WilE3.Frame.partial_curve_eq_Vword` and `Work.WilE3.Frame.Vword_toC_eq_zero` are being
finished in parallel in this workspace; the modules are
`Submission.Work.WilE3.Frame.partial_curve_eq_Vword` and `Submission.Work.WilE3.Frame.Vword_toC_eq_zero`.
The file `Submission.Work.WilE3.Frame.Vdir_Vword` currently only defines bookkeeping for the fold and
is not needed here. -/
theorem frame_derivs_vanish {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (h : Fin j → WilkiesDesign.E.EAPoly k r) (ι : Fin j → Fin k)
    (f : WilkiesDesign.E.EAPoly k r) (x : Fin k → ℝ) (Mv : ℕ)
    (hvan : ∀ m : Fin k → ℕ, (∀ a, m (ι a) = 0) → (∑ l, m l) ≤ Mv →
      WilkiesDesign.E.eaEval c (WilkiesDesign.E.opMono c h ι m f) x = 0)
    (hd : Work.WilE3.Frame.jacValC c h ι (Work.WilE3.Frame.toC x) ≠ 0)
    (Ψ : ((Work.WilE3.Frame.U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ))
    (hΨ : Work.WilE3.Frame.IsStraightening c h ι x Ψ) (w : Work.WilE3.Frame.U k ι → ℝ) :
    ∀ i : ℕ, i ≤ Mv → iteratedDeriv i (fun t : ℂ =>
      Work.WilE3.eaEvalC c f (Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x) +
        t • (fun i => (w i : ℂ)), 0))) 0 = 0 := by
  classical
  intro i hi
  -- Unpack the straightening data.
  have hΨ0 : Ψ (uCoord k ι (toC x), 0) = toC x := hΨ.1
  have hΨan : AnalyticAt ℂ Ψ (uCoord k ι (toC x), 0) := hΨ.2.1
  have hΦΨ : ∀ᶠ z in 𝓝 (uCoord k ι (toC x), 0), PhiC c h ι (Ψ z) = z := hΨ.2.2.1
  -- The Jacobian does not vanish near the base point (it is analytic there and nonzero at `x`).
  have hΔ : ∀ᶠ z in 𝓝 (toC x), jacValC c h ι z ≠ 0 :=
    (Work.WilE3.API.eaEvalC_fderiv_analytic c (jacDet c h ι) (toC x)).2.continuousAt.eventually_ne hd
  -- The curve function `u ↦ f (Ψ (u|_ιᶜ, 0))`.
  set F : (Fin k → ℂ) → ℂ := fun u => eaEvalC c f (Ψ (fun l : U k ι => u l.1, 0)) with hF
  -- It is analytic at `toC x`.
  have hFan : AnalyticAt ℂ F (toC x) := by
    have hlin : AnalyticAt ℂ
        (fun u : Fin k → ℂ => (uCoord k ι u, (0 : Fin j → ℂ))) (toC x) := by
      let L : (Fin k → ℂ) →L[ℂ] ((U k ι → ℂ) × (Fin j → ℂ)) :=
        (ContinuousLinearMap.pi fun l : U k ι =>
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) l.1).prod 0
      have hL : (fun u : Fin k → ℂ => (uCoord k ι u, (0 : Fin j → ℂ))) = ⇑L := by
        funext u
        simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
          ContinuousLinearMap.proj_apply]
        rfl
      rw [hL]
      exact L.analyticAt (toC x)
    have hΨcomp : AnalyticAt ℂ (fun u : Fin k → ℂ => Ψ (fun l : U k ι => u l.1, 0)) (toC x) :=
      AnalyticAt.comp (g := Ψ)
        (f := fun u : Fin k → ℂ => (uCoord k ι u, (0 : Fin j → ℂ))) hΨan hlin
    have hout : AnalyticAt ℂ (fun z => eaEvalC c f z) (Ψ (uCoord k ι (toC x), 0)) :=
      (Work.WilE3.API.eaEvalC_fderiv_analytic c f _).1
    exact AnalyticAt.comp (g := fun z : Fin k → ℂ => eaEvalC c f z)
      (f := fun u : Fin k → ℂ => Ψ (uCoord k ι u, 0)) hout hΨcomp
  -- Vanishing of every ordered partial of order `≤ i`.
  have hpar : ∀ m : Fin k → ℕ, (∑ l, m l) ≤ i →
      ((List.finRange k).foldr (fun l G => (edir l)^[m l] G) F) (toC x) = 0 := by
    intro m hm
    rw [hF]
    by_cases hsupp : ∀ a : Fin j, m (ι a) = 0
    · -- supported off `Set.range ι`: the ordered partial is a frame word, killed by `hvan`.
      rw [partial_curve_eq_Vword c h ι f x Ψ hΦΨ hΨ0 hΨan hΔ m hsupp]
      exact Vword_toC_eq_zero c h ι f x Mv hvan hd m hsupp (le_trans hm hi)
    · -- some `ι`-exponent is positive: `F` is constant along that coordinate, so the word is `0`.
      obtain ⟨a, ha⟩ := not_forall.mp hsupp
      have hpos : 0 < m (ι a) := Nat.pos_of_ne_zero ha
      rw [fold_finRange_eq_zero_of_constAlong m F (ι a) hpos
        (constAlong_comp_subtype c f ι Ψ (ι a) ⟨a, rfl⟩)]
      rfl
  -- The line-derivative lemma applied to the direction `wextC ι w`.
  have hline : iteratedDeriv i (fun t : ℂ => F (toC x + t • wextC ι w)) 0 = 0 :=
    frame_line_deriv F (toC x) (wextC ι w) i hFan hpar
  -- Identification of the two one-variable functions.
  have hfun : (fun t : ℂ => F (toC x + t • wextC ι w)) =
      (fun t : ℂ => eaEvalC c f (Ψ (uCoord k ι (toC x) +
        t • (fun l : U k ι => (w l : ℂ)), 0))) := by
    funext t
    show eaEvalC c f (Ψ (fun l : U k ι => (toC x + t • wextC ι w) l.1, 0))
      = eaEvalC c f (Ψ (uCoord k ι (toC x) + t • (fun l : U k ι => (w l : ℂ)), 0))
    rw [uCoord_toC_add_smul_wextC ι x w t]
  rw [hfun] at hline
  exact hline

end

end Work.WilE3.Frame
