import Mathlib
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.Vcoef
import Submission.Work.WilE3.Frame.curve_analytic
import Submission.Work.WilE3.Frame.fderiv_cur_eq_VcoefC
import Submission.Work.WilE3.Frame.curve_chain_rule
import Submission.Work.WilE3.Frame.Vword_toC_eq_zero
import Submission.Work.WilE3.Frame.fderiv_curve_eq_VcoefC
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E
open Work.WilE3 (jacDet)

variable {k r j : ℕ}

/-! ## §4. The main theorem -/

/-- **Ordered derivatives along the curve `{h = 0}` are the frame words.**  With `Ψ` the analytic
local inverse of `Φ = (ι^c-coordinates, h)` and `V_l` the tangential frame field (`VcoefC`), the
mixed derivatives of `u ↦ f (Ψ (u|_ιᶜ, 0))`, taken in the same (increasing index) order as the fold
defining `Vword`/`opMono`, are the iterated frame derivatives of `f`.  This is the chain rule plus
the tangency of the curve (`fderiv_curve_eq_VcoefC`), applied `|m|` times.

Together with `Vword_toC_eq_zero` this gives the frame step of `E3_identity`: the ordered reduced
derivatives of `f` at `x` control every derivative of `f` along `{h = 0}`. -/
theorem partial_curve_eq_Vword {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (f : EAPoly k r) (x : Fin k → ℝ)
    (Ψ : ((Work.WilE3.Frame.U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ))
    (hΨ : ∀ᶠ w in 𝓝 (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x), 0),
      Work.WilE3.Frame.PhiC c h ι (Ψ w) = w)
    (hΨ0 : Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x), 0) =
      Work.WilE3.Frame.toC x)
    (hΨan : AnalyticAt ℂ Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x), 0))
    (hΔ : ∀ᶠ z in 𝓝 (Work.WilE3.Frame.toC x), Work.WilE3.Frame.jacValC c h ι z ≠ 0)
    (m : Fin k → ℕ) (hm : ∀ a : Fin j, m (ι a) = 0) :
    ((List.finRange k).foldr
        (fun l G => (Work.WilE3.Frame.edir l)^[m l] G)
        (fun u : Fin k → ℂ =>
          Work.WilE3.eaEvalC c f (Ψ (fun i : Work.WilE3.Frame.U k ι => u i.1, 0))))
      (Work.WilE3.Frame.toC x)
      = Work.WilE3.Frame.Vword c h ι m (fun z => Work.WilE3.eaEvalC c f z)
          (Work.WilE3.Frame.toC x) := by
  classical
  set z0 : Fin k → ℂ := toC x with hz0
  let cur : (Fin k → ℂ) → (Fin k → ℂ) := fun u => Ψ (uCoord k ι u, 0)
  let H : (Fin k → ℂ) → ℂ := fun z => eaEvalC c f z
  -- the tangent form of the curve, near `toC x`
  have hTanEv : ∀ᶠ u in 𝓝 z0, ∀ l : Fin k, l ∉ Set.range ι →
      fderiv ℂ cur u (Pi.single l 1) = VcoefC c h ι l (cur u) :=
    Filter.eventually_all.mpr fun l => by
      by_cases hl : l ∈ Set.range ι
      · filter_upwards with u
        exact fun h => absurd hl h
      · refine (fderiv_cur_eq_VcoefC c h ι x Ψ hΨ hΨ0 hΨan hΔ l hl).mono ?_
        intro u hu _
        exact hu
  -- analyticity and nonvanishing of the Jacobian near the curve
  have hpair : Continuous fun u : Fin k → ℂ => (uCoord k ι u, (0 : Fin j → ℂ)) :=
    (ContinuousLinearMap.prod (uCoordL k ι)
      (0 : (Fin k → ℂ) →L[ℂ] (Fin j → ℂ))).continuous
  have hAnEv : ∀ᶠ u in 𝓝 z0, AnalyticAt ℂ Ψ (uCoord k ι u, (0 : Fin j → ℂ)) :=
    (hpair.tendsto z0).eventually hΨan.eventually_analyticAt
  have hcurcont : ContinuousAt cur z0 := by
    have h := ContinuousAt.comp (x := z0)
      (f := fun u : Fin k → ℂ => (uCoord k ι u, (0 : Fin j → ℂ))) (g := Ψ)
      hΨan.continuousAt hpair.continuousAt
    simpa only [cur, Function.comp_def] using h
  have hcur_z0 : cur z0 = z0 := by
    show Ψ (uCoord k ι z0, 0) = z0
    exact hΨ0
  have hJacEv : ∀ᶠ u in 𝓝 z0, jacValC c h ι (cur u) ≠ 0 :=
    hcurcont.tendsto.eventually (by rw [hcur_z0]; exact hΔ)
  -- the good open set
  obtain ⟨U1, hU1o, hU1m, hU1⟩ := exists_isOpen_forall_of_eventually hAnEv
  obtain ⟨U2, hU2o, hU2m, hU2⟩ := exists_isOpen_forall_of_eventually hJacEv
  obtain ⟨U3, hU3o, hU3m, hU3⟩ := exists_isOpen_forall_of_eventually hTanEv
  set U : Set (Fin k → ℂ) := U1 ∩ U2 ∩ U3 with hUdef
  have hUo : IsOpen U := (hU1o.inter hU2o).inter hU3o
  have hUm : z0 ∈ U := ⟨⟨hU1m, hU2m⟩, hU3m⟩
  have hUan : ∀ u ∈ U, AnalyticAt ℂ Ψ (uCoord k ι u, (0 : Fin j → ℂ)) :=
    fun u hu => hU1 u hu.1.1
  have hUjac : ∀ u ∈ U, jacValC c h ι (cur u) ≠ 0 := fun u hu => hU2 u hu.1.2
  have hUtang : ∀ u ∈ U, ∀ l : Fin k, l ∉ Set.range ι →
      fderiv ℂ cur u (Pi.single l 1) = VcoefC c h ι l (cur u) := fun u hu => hU3 u hu.2
  have hUd : ∀ u ∈ U, HasFDerivAt cur (fderiv ℂ cur u) u := by
    intro u hu
    have hgd : HasFDerivAt (fun u' : Fin k → ℂ => (uCoord k ι u', (0 : Fin j → ℂ)))
        ((uCoordL k ι).prod 0) u :=
      (hasFDerivAt_uCoord k ι u).prodMk (hasFDerivAt_const (0 : Fin j → ℂ) u)
    have hdiff : DifferentiableAt ℂ Ψ (uCoord k ι u, (0 : Fin j → ℂ)) :=
      (hUan u hu).differentiableAt
    exact (hdiff.comp u hgd.differentiableAt).hasFDerivAt
  -- `H` is analytic everywhere
  have hHan : ∀ u ∈ U, AnalyticAt ℂ H (cur u) := by
    intro u _
    exact (Work.WilE3.API.eaEvalC_fderiv_analytic c f (cur u)).1
  -- the fold induction
  have key : ∀ (L : List (Fin k)), (∀ l ∈ L, m l ≠ 0 → l ∉ Set.range ι) →
      (∀ u ∈ U, AnalyticAt ℂ (L.foldr (fun i G => (Vdir c h ι i)^[m i] G) H) (cur u)) ∧
      (∀ u ∈ U, (L.foldr (fun i G => (edir i)^[m i] G) (fun u => H (cur u))) u
        = (L.foldr (fun i G => (Vdir c h ι i)^[m i] G) H) (cur u)) := by
    intro L
    induction L with
    | nil =>
        intro _
        exact ⟨hHan, fun u _ => rfl⟩
    | cons l L' ih =>
        intro hL
        have hL' : ∀ l' ∈ L', m l' ≠ 0 → l' ∉ Set.range ι :=
          fun l' hl' hne => hL l' (List.mem_cons_of_mem l hl') hne
        obtain ⟨ihAn, ihEq⟩ := ih hL'
        by_cases hl0 : m l = 0
        · constructor
          · intro u hu
            show AnalyticAt ℂ ((Vdir c h ι l)^[m l]
              (L'.foldr (fun i G => (Vdir c h ι i)^[m i] G) H)) (cur u)
            simp only [hl0, Function.iterate_zero_apply]
            exact ihAn u hu
          · intro u hu
            show ((edir l)^[m l]
                  (L'.foldr (fun i G => (edir i)^[m i] G) (fun u => H (cur u)))) u
                = ((Vdir c h ι l)^[m l]
                    (L'.foldr (fun i G => (Vdir c h ι i)^[m i] G) H)) (cur u)
            simp only [hl0, Function.iterate_zero_apply]
            exact ihEq u hu
        · have hl : l ∉ Set.range ι := hL l (List.mem_cons_self ..) hl0
          have hAnAll : ∀ u ∈ U, ∀ n : ℕ,
              AnalyticAt ℂ ((Vdir c h ι l)^[n]
                (L'.foldr (fun i G => (Vdir c h ι i)^[m i] G) H)) (cur u) := by
            intro u hu n
            induction n with
            | zero => exact ihAn u hu
            | succ n ihn =>
                rw [Function.iterate_succ_apply']
                exact analyticAt_Vdir_aux c h ι l _ (cur u) ihn (hUjac u hu)
          constructor
          · intro u hu
            exact hAnAll u hu (m l)
          · intro u hu
            have hstep1 : ((edir l)^[m l]
                (L'.foldr (fun i G => (edir i)^[m i] G) (fun u => H (cur u)))) u
                = ((edir l)^[m l]
                    (fun u' => (L'.foldr (fun i G => (Vdir c h ι i)^[m i] G) H) (cur u'))) u :=
              edir_iterate_congr_on l (m l) hUo ihEq u hu
            have hstep2 : ((edir l)^[m l]
                  (fun u' => (L'.foldr (fun i G => (Vdir c h ι i)^[m i] G) H) (cur u'))) u
                = ((Vdir c h ι l)^[m l]
                    (L'.foldr (fun i G => (Vdir c h ι i)^[m i] G) H)) (cur u) :=
              edir_iterate_comp_eq_Vdir_iterate c h ι l hl cur U hUo hUd
                (fun u hu => hUtang u hu l hl) _
                (fun n u hu => hAnAll u hu n) (m l) u hu
            show ((edir l)^[m l]
                  (L'.foldr (fun i G => (edir i)^[m i] G) (fun u => H (cur u)))) u
                = ((Vdir c h ι l)^[m l]
                    (L'.foldr (fun i G => (Vdir c h ι i)^[m i] G) H)) (cur u)
            exact hstep1.trans hstep2
  obtain ⟨-, hEq⟩ := key (List.finRange k) (by
    intro l _ hml hr
    obtain ⟨a, ha⟩ := hr
    exact hml (by rw [← ha]; exact hm a))
  have hmain := hEq z0 hUm
  rw [hcur_z0] at hmain
  show ((List.finRange k).foldr (fun i G => (edir i)^[m i] G) (fun u => H (cur u))) z0
      = ((List.finRange k).foldr (fun i G => (Vdir c h ι i)^[m i] G) H) z0
  exact hmain


end

end Work.WilE3.Frame
