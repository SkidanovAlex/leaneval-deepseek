import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kappa_tau0
import Submission.Work.RPB.B5.kappa_defect
import Submission.Work.RPB.B5.kappa_near_area
import Submission.Work.RPB.B5.kappa_shape_geom_small
import Submission.Work.RPB.B5.kA0_spec
import Submission.Work.RPV.levelPt_omega
import Submission.Work.RPB.B5.iteratedDeriv_comp_congr
import Submission.Work.RPB.B5.iteratedDeriv_eq_of_eqOn_Ioo_left
import Submission.Work.RPB.B5.chartJets_oneSided
import Submission.Work.RPB.B5.chartJets_levelPt_contDiff
import Submission.Work.RPB.B5.noL_defect_jets_ha
import Submission.Work.RPB.B5.uproj_chart_contDiffAt_kappa
import Submission.Work.RPB.B5.rho_range_kappa
import Submission.Work.RPB.B5.kappaSmallAux
import Submission.Work.RPB.B5.contDiffAt_signedArea_of_contDiffOn
import Submission.Work.RPB.B5.kappa_near_area_reg
import Submission.Work.RPB.B5.kshape_contDiffOn
import Submission.Work.RPB.B5.kshape_left_eq_chart
import Submission.Work.RPB.B5.collarPt_contDiffAt
import Submission.Work.RPB.B5.kac_left_agree

/-!
# B5: the `σ`-jets of the `κ`-parametrised collar at `σ = 0` (`kappa_collar_jets`)

The collar family `kgam`/`kac` of `Work.RPB.B5.collar_exists_kappa` is built so that on the left
of `σ = 0` its level point `levelPt (kgam τ σ t) σ (kac τ σ t)` agrees with the level family
`W τ t (ρh τ t σ)`, and so that both are `C⁸` at `σ = 0`.  Hence the one-sided `σ`-jets at `0`
agree, which is precisely the hypothesis (8) of `collar_exists_kappa` (the gluing condition at
the junction `x = -√2` of the Lagrangian family).

The three inputs are:

* on `σ ∈ (-δ, 0)` the glued shape `kshape` is the clamped chart family and, because
  `karS = signedArea (kshape)` equals `2π (1+σ)` there, the normalisation satisfies `kg = 1`;
  hence `kgam τ σ t = uproj (W τ t (ρh τ t σ))` (`kshape_left_eq_chart`,
  `kappa_near_area_reg`, `rho_range_kappa`);
* on `σ ∈ (-δ, 0)` the flux phase `kac` equals `kA0` plus the increment
  `(W τ t (ρh τ t σ)).1.2 - (W τ 0 (ρh τ 0 σ)).1.2`, by the Lagrangian identity
  `ω_ℂ(∂_σ U, ∂_t U) = ∂_t Q` (`kappa_defect`) and the fundamental theorem of calculus
  (`kac_left_agree`);
* the `σ`-jets of `kA0` at `0` are those of `σ ↦ (W τ 0 (ρh τ 0 σ)).1.2` (`kA0_jets`), so the
  two level parametrisations `σ ↦ levelPt (U σ) σ (Q σ + Δ σ)` and `σ ↦ levelPt (U σ) σ (Q σ)`
  have the same jets at `0` (Faà di Bruno: `iteratedDeriv_comp_congr`).

The point family of the collar is a *single* smooth formula in `σ`, so it is `C⁸` at `σ = 0`
(`collarPt_contDiffAt`); combining the left agreement with this smoothness gives the one-sided
jets.
-/

open Set Filter
open scoped Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.RPB.B5

/-! ## Plumbing: one-sided jets and jets of pairs -/

/-- For a function which is `C^n` at `x₀`, the one-sided iterated derivative at `x₀` (from the
right) is the ordinary iterated derivative. -/
private theorem kcj_iteratedDerivWithin_Ioi_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {x₀ : ℝ} {n : ℕ} (hf : ContDiffAt ℝ n f x₀)
    {j : ℕ} (hj : j ≤ n) : iteratedDerivWithin j f (Set.Ioi x₀) x₀ = iteratedDeriv j f x₀ := by
  have h1 : iteratedFDerivWithin ℝ j f (Set.Ici x₀) x₀
      = iteratedFDerivWithin ℝ j f (Set.Ioi x₀) x₀ := by
    rw [← Set.Ioi_insert]
    exact iteratedFDerivWithin_insert
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDeriv_eq_iteratedFDeriv, ← h1]
  exact congrArg (fun m : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℝ) E => m (fun _ => 1))
    (iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Ici x₀) (hf.of_le (by exact_mod_cast hj))
      (Set.mem_Ici.mpr le_rfl))

/-- The iterated derivative of a pair-valued function is the pair of the iterated derivatives. -/
private theorem kcj_iteratedDeriv_prod {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} {f : ℝ → E} {g : ℝ → F} {x : ℝ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    iteratedDeriv n (fun y : ℝ => (f y, g y)) x
      = (iteratedDeriv n f x, iteratedDeriv n g x) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_prodMk hf hg le_rfl,
    ContinuousMultilinearMap.prod_apply]

/-- The real-linear normalisation with factor `1` is the identity. -/
private theorem kcj_kdiagM_one (z : ℂ) : kdiagM 1 z = z := by
  rw [kdiagM, one_mul]
  exact Complex.re_add_im z

/-- A continuous function which agrees with another one eventually along a filter converging to
`x` agrees with it at `x`. -/
private theorem kcj_continuousAt_eq_of_eventuallyEq (f g : ℝ → ℝ) {x : ℝ} (l : Filter ℝ)
    [l.NeBot] (hl : l ≤ 𝓝 x) (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (h : f =ᶠ[l] g) : f x = g x :=
  tendsto_nhds_unique ((hf.tendsto.mono_left hl).congr' h) (hg.tendsto.mono_left hl)

/-! ## The integer at `τ = 0` -/

/-- The integer of the chord phase at `τ = 0` is the one appearing in the statement. -/
private theorem kcj_k_eq (a : ℝ → ℝ → ℝ → ℝ) (k k' : ℤ)
    (h : ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) Real.pi,
      a 0 t r = t + Real.pi / 2 + 2 * Real.pi * k)
    (h' : ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) Real.pi,
      a 0 t r = t + Real.pi / 2 + 2 * Real.pi * k') : k' = k := by
  have hmem : (Real.pi / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) Real.pi :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have h1 := h' 0 (Real.pi / 2) hmem
  have h2 := h 0 (Real.pi / 2) hmem
  have h3 : (2 * Real.pi) * ((k' : ℤ) : ℝ) = (2 * Real.pi) * ((k : ℤ) : ℝ) := by
    push_cast at h1 h2 ⊢
    linarith
  have h4 : ((k' : ℤ) : ℝ) = ((k : ℤ) : ℝ) :=
    mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0) h3
  exact_mod_cast h4

/-- The `σ`-jets at `0`, up to order `8`, of the chart phase at `t = 0` are those of the
constant `π/2 + 2πk`, as required by `kA0_jets`. -/
private theorem kcj_kcj_zero_eq (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) (k : ℤ)
    (hsmooth : ContDiffAt ℝ 8 (fun σ : ℝ => (W 0 0 (ρh 0 0 σ)).1.2) 0)
    (hflat : ∀ j : ℕ, j ≤ 8 →
      iteratedDeriv j (fun σ : ℝ => (W 0 0 (ρh 0 0 σ)).1.2
        - (0 + Real.pi / 2 + 2 * Real.pi * (k : ℝ))) 0 = 0) :
    ∀ j : ℕ, j ≤ 8 → kcj W ρh 0 j
      = iteratedDeriv j (fun _ : ℝ => Real.pi / 2 + 2 * Real.pi * k) 0 := by
  intro j hj
  let F : ℝ → ℝ := fun σ => (W 0 0 (ρh 0 0 σ)).1.2
  let Gc : ℝ → ℝ := fun _ => 0 + Real.pi / 2 + 2 * Real.pi * (k : ℝ)
  have hFcd : ContDiffAt ℝ j F 0 := hsmooth.of_le (by exact_mod_cast hj)
  have hGcd : ContDiffAt ℝ j Gc 0 := contDiffAt_const
  have hsub : iteratedDeriv j (F - Gc) 0 = iteratedDeriv j F 0 - iteratedDeriv j Gc 0 :=
    iteratedDeriv_sub hFcd hGcd
  have h0 : iteratedDeriv j (F - Gc) 0 = 0 := by
    show iteratedDeriv j (fun σ : ℝ => (W 0 0 (ρh 0 0 σ)).1.2
      - (0 + Real.pi / 2 + 2 * Real.pi * (k : ℝ))) 0 = 0
    exact hflat j hj
  rw [hsub] at h0
  have hkey : iteratedDeriv j F 0 = iteratedDeriv j Gc 0 := by linarith
  show iteratedDeriv j F 0 = iteratedDeriv j (fun _ : ℝ => Real.pi / 2 + 2 * Real.pi * k) 0
  rw [hkey]
  congr 1
  funext x
  show 0 + Real.pi / 2 + 2 * Real.pi * (k : ℝ) = Real.pi / 2 + 2 * Real.pi * k
  push_cast
  ring

/-! ## The equality of the `σ`-jets of the two level parametrisations -/

/-- **The Faà di Bruno comparison.**  Let `U σ = uproj (W τ t (ρh τ t σ))`,
`Q σ = (W τ t (ρh τ t σ)).1.2`, `Q₀ σ = (W τ 0 (ρh τ 0 σ)).1.2` and let `A0` be a function whose
`σ`-jets at `0` up to order `8` agree with those of `Q₀` (this is `kA0_jets`).  Then the two
parametrisations `σ ↦ levelPt (U σ) σ (Q σ + (A0 σ - Q₀ σ))` and `σ ↦ levelPt (U σ) σ (Q σ)`
have the same `σ`-jets at `0` up to order `8`; and the second is the level family
`σ ↦ W τ t (ρh τ t σ)` on `(-κ, κ)`. -/
private theorem kcj_jets_G_eq_level (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (k : ℤ) {κ : ℝ} (hκ : 0 < κ) {τ t : ℝ}
    (hU : ContDiffAt ℝ 8 (fun σ : ℝ => Work.RPV.uproj (W τ t (ρh τ t σ))) 0)
    (hQ : ContDiffAt ℝ 8 (fun σ : ℝ => (W τ t (ρh τ t σ)).1.2) 0)
    (hQ₀ : ContDiffAt ℝ 8 (fun σ : ℝ => (W τ 0 (ρh τ 0 σ)).1.2) 0)
    (hA0 : ContDiffAt ℝ 8 (fun σ : ℝ => kA0 W ρh δ k τ σ) 0)
    (hjet : ∀ j : ℕ, j ≤ 8 → iteratedDeriv j (fun σ : ℝ => kA0 W ρh δ k τ σ) 0
        = iteratedDeriv j (fun σ : ℝ => (W τ 0 (ρh τ 0 σ)).1.2) 0)
    (hAcd : ContDiffAt ℝ 8 (fun σ : ℝ => W τ t (ρh τ t σ)) 0)
    (hlev : ∀ σ ∈ Set.Ioo (-κ) κ, Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ) :
    ∀ j : ℕ, j ≤ 8 →
      iteratedDeriv j (fun σ : ℝ => Work.RPV.levelPt
          (Work.RPV.uproj (W τ t (ρh τ t σ))) σ
          ((W τ t (ρh τ t σ)).1.2 + (kA0 W ρh δ k τ σ - (W τ 0 (ρh τ 0 σ)).1.2))) 0
        = iteratedDeriv j (fun σ : ℝ => W τ t (ρh τ t σ)) 0 := by
  intro j hj
  let U : ℝ → ℂ := fun σ => Work.RPV.uproj (W τ t (ρh τ t σ))
  let Q : ℝ → ℝ := fun σ => (W τ t (ρh τ t σ)).1.2
  let Q₀ : ℝ → ℝ := fun σ => (W τ 0 (ρh τ 0 σ)).1.2
  let A₀ : ℝ → ℝ := fun σ => kA0 W ρh δ k τ σ
  let D : ℝ → ℝ := fun σ => A₀ σ - Q₀ σ
  have hUcd : ContDiffAt ℝ 8 U 0 := hU
  have hQcd : ContDiffAt ℝ 8 Q 0 := hQ
  have hQ₀cd : ContDiffAt ℝ 8 Q₀ 0 := hQ₀
  have hA₀cd : ContDiffAt ℝ 8 A₀ 0 := hA0
  have hDcd : ContDiffAt ℝ 8 D 0 := hA₀cd.sub hQ₀cd
  change iteratedDeriv j (fun σ : ℝ => Work.RPV.levelPt (U σ) σ (Q σ + D σ)) 0
      = iteratedDeriv j (fun σ : ℝ => W τ t (ρh τ t σ)) 0
  have hGcd : ContDiffAt ℝ 8 (fun σ : ℝ => Work.RPV.levelPt (U σ) σ (Q σ + D σ)) 0 :=
    (chartJets_levelPt_contDiff.contDiffAt).comp 0
      (hUcd.prodMk (contDiffAt_id.prodMk (hQcd.add hDcd)))
  have hG'cd : ContDiffAt ℝ 8 (fun σ : ℝ => Work.RPV.levelPt (U σ) σ (Q σ)) 0 :=
    (chartJets_levelPt_contDiff.contDiffAt).comp 0
      (hUcd.prodMk (contDiffAt_id.prodMk hQcd))
  have hstep1 : iteratedDeriv j (fun σ : ℝ => Work.RPV.levelPt (U σ) σ (Q σ + D σ)) 0
      = iteratedDeriv j (fun σ : ℝ => Work.RPV.levelPt (U σ) σ (Q σ)) 0 := by
    refine iteratedDeriv_comp_congr
      (F := fun p : ℂ × (ℝ × ℝ) => Work.RPV.levelPt p.1 p.2.1 p.2.2)
      (u := fun σ : ℝ => (U σ, (σ, Q σ + D σ)))
      (u' := fun σ : ℝ => (U σ, (σ, Q σ)))
      chartJets_levelPt_contDiff ?_ ?_ ?_ hj
    · exact hUcd.prodMk (contDiffAt_id.prodMk (hQcd.add hDcd))
    · exact hUcd.prodMk (contDiffAt_id.prodMk hQcd)
    · intro m hm
      have hm8 : ((m : ℕ) : ℕ∞ω) ≤ (8 : ℕ∞ω) := by exact_mod_cast hm
      have hUm : ContDiffAt ℝ (m : ℕ∞ω) U 0 := hUcd.of_le hm8
      have hQm : ContDiffAt ℝ (m : ℕ∞ω) Q 0 := hQcd.of_le hm8
      have hQ₀m : ContDiffAt ℝ (m : ℕ∞ω) Q₀ 0 := hQ₀cd.of_le hm8
      have hA₀m : ContDiffAt ℝ (m : ℕ∞ω) A₀ 0 := hA₀cd.of_le hm8
      have hDm : ContDiffAt ℝ (m : ℕ∞ω) D 0 := hA₀m.sub hQ₀m
      have hDjet : iteratedDeriv m D 0 = 0 := by
        have hsub2 : iteratedDeriv m (fun σ : ℝ => A₀ σ - Q₀ σ) 0
            = iteratedDeriv m A₀ 0 - iteratedDeriv m Q₀ 0 := iteratedDeriv_sub hA₀m hQ₀m
        have hjet' : iteratedDeriv m A₀ 0 = iteratedDeriv m Q₀ 0 := hjet m hm
        show iteratedDeriv m (fun σ : ℝ => A₀ σ - Q₀ σ) 0 = 0
        rw [hsub2, hjet', sub_self]
      have e1 : iteratedDeriv m (fun σ : ℝ => (U σ, (σ, Q σ + D σ))) 0
          = (iteratedDeriv m U 0, iteratedDeriv m (fun σ : ℝ => (σ, Q σ + D σ)) 0) :=
        kcj_iteratedDeriv_prod hUm (contDiffAt_id.prodMk (hQm.add hDm))
      have e2 : iteratedDeriv m (fun σ : ℝ => (U σ, (σ, Q σ))) 0
          = (iteratedDeriv m U 0, iteratedDeriv m (fun σ : ℝ => (σ, Q σ)) 0) :=
        kcj_iteratedDeriv_prod hUm (contDiffAt_id.prodMk hQm)
      have e3 : iteratedDeriv m (fun σ : ℝ => (σ, Q σ + D σ)) 0
          = (iteratedDeriv m (fun σ : ℝ => σ) 0,
              iteratedDeriv m (fun σ : ℝ => Q σ + D σ) 0) :=
        kcj_iteratedDeriv_prod contDiffAt_id (hQm.add hDm)
      have e4 : iteratedDeriv m (fun σ : ℝ => (σ, Q σ)) 0
          = (iteratedDeriv m (fun σ : ℝ => σ) 0, iteratedDeriv m (fun σ : ℝ => Q σ) 0) :=
        kcj_iteratedDeriv_prod contDiffAt_id hQm
      have e5 : iteratedDeriv m (fun σ : ℝ => Q σ + D σ) 0
          = iteratedDeriv m (fun σ : ℝ => Q σ) 0 + iteratedDeriv m D 0 :=
        iteratedDeriv_add hQm hDm
      rw [e1, e2, e3, e4, e5, hDjet, add_zero]
  have hstep2 : iteratedDeriv j (fun σ : ℝ => Work.RPV.levelPt (U σ) σ (Q σ)) 0
      = iteratedDeriv j (fun σ : ℝ => W τ t (ρh τ t σ)) 0 := by
    have hagree : ∀ x ∈ Set.Ioo (0 - κ) 0,
        (fun σ : ℝ => Work.RPV.levelPt (U σ) σ (Q σ)) x
          = (fun σ : ℝ => W τ t (ρh τ t σ)) x := by
      intro x hx
      rw [zero_sub] at hx
      have hxκ : x ∈ Set.Ioo (-κ) κ := ⟨hx.1, by linarith [hx.2, hκ]⟩
      exact levelPt_uproj_eq_self (W τ t (ρh τ t x)) x (hlev x hxκ)
    exact iteratedDeriv_eq_of_eqOn_Ioo_left hκ hG'cd hAcd hagree hj
  exact hstep1.trans hstep2

/-! ## The theorem -/

theorem kappa_collar_jets (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (k : ℤ) (hk : ∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) Real.pi,
        a 0 t r = t + Real.pi / 2 + 2 * Real.pi * k) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ κ ∧
      ∀ δ ∈ Set.Ioo (0 : ℝ) δ₀, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ j : ℕ, j ≤ 8 →
        iteratedDerivWithin j
            (fun σ : ℝ => Work.RPV.levelPt (Work.RPB.B5.kgam CI W ρh δ k τ σ t) σ
                (Work.RPB.B5.kac CI W ρh δ k τ σ t)) (Set.Ioi 0) 0
          = iteratedDeriv j (fun σ : ℝ => W τ t (ρh τ t σ)) 0 := by
  -- ## The local inputs
  obtain ⟨k', hk', δ₁, hδ₁pos, hδ₁κ, hcirc, -, hphase⟩ :=
    kappa_tau0 CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hρh hρh0 hρhv hρhl
  have hkk : k' = k := kcj_k_eq a k k' hk hk'
  obtain ⟨δ₂, hδ₂pos, hδ₂κ, hdefect, -⟩ :=
    kappa_defect CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hρh hρh0 hρhv hρhl
  obtain ⟨ε, hεpos, hεκ, hregε⟩ :=
    rho_range_kappa CI a ha ρ₀ hρ₀ W ρh hκ hW hWchord hρh hρh0 hρhv hρhl
  -- ## The scale
  have hmpos : 0 < min (min δ₁ (min δ₂ ε)) (min κ 1) :=
    lt_min (lt_min hδ₁pos (lt_min hδ₂pos hεpos)) (lt_min hκ one_pos)
  refine ⟨min (min δ₁ (min δ₂ ε)) (min κ 1) / 8, by positivity, ?_, ?_⟩
  · -- `δ₀ ≤ κ`
    have h1 : min (min δ₁ (min δ₂ ε)) (min κ 1) ≤ min δ₁ (min δ₂ ε) := min_le_left _ _
    have h2 : min δ₁ (min δ₂ ε) ≤ δ₁ := min_le_left _ _
    have h3 : δ₁ ≤ κ := hδ₁κ
    linarith [hmpos]
  · intro δ hδ τ hτ t j hj
    have hδpos : 0 < δ := hδ.1
    have hδA : δ < min δ₁ (min δ₂ ε) := by
      have h1 : min (min δ₁ (min δ₂ ε)) (min κ 1) ≤ min δ₁ (min δ₂ ε) := min_le_left _ _
      nlinarith [hδ.2, hmpos]
    have hδ₁ : δ < δ₁ := lt_of_lt_of_le hδA (min_le_left _ _)
    have hδ₂ : δ < δ₂ := lt_of_lt_of_le hδA (le_trans (min_le_right _ _) (min_le_left _ _))
    have hδε : δ < ε := lt_of_lt_of_le hδA (le_trans (min_le_right _ _) (min_le_right _ _))
    have hδκ : δ < κ := by
      have h1 : min (min δ₁ (min δ₂ ε)) (min κ 1) ≤ min κ 1 := min_le_right _ _
      have h2 : min κ 1 ≤ κ := min_le_left _ _
      nlinarith [hδ.2, hmpos]
    have hδ1 : δ < 1 := by
      have h1 : min (min δ₁ (min δ₂ ε)) (min κ 1) ≤ min κ 1 := min_le_right _ _
      have h2 : min κ 1 ≤ 1 := min_le_right _ _
      nlinarith [hδ.2, hmpos]
    -- ## The window `(-η, 0)`
    set η : ℝ := δ / 4 with hηdef
    have hηpos : 0 < η := by rw [hηdef]; linarith
    have hηδ : 4 * η ≤ δ := by rw [hηdef]; linarith
    have hη₁ : η < δ₁ := by rw [hηdef]; linarith
    have hη₂ : η < δ₂ := by rw [hηdef]; linarith
    have hηε : η < ε := by rw [hηdef]; linarith
    have hηκs : η < κ := by rw [hηdef]; linarith
    have hηκ : η ≤ κ := le_of_lt hηκs
    have hη1 : η < 1 := by rw [hηdef]; linarith
    -- ## The glued shape is the clamped chart family on `(-η, 0)`
    have hcircη : ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-η) 0,
        Work.RPV.uproj (W 0 t (ρh 0 t σ))
          = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (t * Complex.I) :=
      fun t σ hσ => (hcirc t σ ⟨by linarith [hσ.1, hη₁], hσ.2⟩).1
    have hkshape_left : ∀ σ ∈ Set.Ioo (-η) 0, ∀ u : ℝ,
        kshape CI W ρh δ k τ σ u = Work.RPV.uproj (W τ u (ρh τ u σ)) :=
      kshape_left_eq_chart CI W ρh hδpos hηδ k τ hcircη
    -- ## The area law on the left: `karS σ = 2π (1 + σ)`
    have harea : ∀ τ' ∈ Set.Icc (0 : ℝ) 1, ∀ σ ∈ Set.Icc (-η) 0,
        Work.RPB.signedArea (fun t : ℝ => Work.RPV.uproj (W τ' t (ρh τ' t σ)))
          = 2 * Real.pi * (1 + σ) :=
      kappa_near_area_reg CI a hρ₀ (hW.of_le (by norm_num)) hWchord hWper hκ
        (hρh.of_le (by norm_num)) hρh0 hρhv hρhl hρhper hηpos hηκs
        (fun τ' hτ' t σ hσ => hregε τ' hτ' t σ ⟨by linarith [hσ.1, hηε], hσ.2⟩)
    have hkshape_cd : ContDiffOn ℝ 12 (fun z : ℝ × ℝ => kshape CI W ρh δ k τ z.1 z.2)
        (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.univ) :=
      kshape_contDiffOn CI hW hκ hρh hρhv hδpos hδκ k hτ
    have hkshape_cd9 : ContDiffOn ℝ ((8 : ℕ∞ω) + 1)
        (fun z : ℝ × ℝ => kshape CI W ρh δ k τ z.1 z.2) (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.univ) :=
      hkshape_cd.of_le (by norm_num)
    have hkarS_cd : ContDiffAt ℝ 8 (fun σ : ℝ => karS CI W ρh δ k τ σ) 0 :=
      contDiffAt_signedArea_of_contDiffOn (fun σ t => kshape CI W ρh δ k τ σ t) 8 hkshape_cd9
    have hev_karS : (fun σ : ℝ => karS CI W ρh δ k τ σ) =ᶠ[𝓝[<] (0 : ℝ)]
        (fun σ : ℝ => 2 * Real.pi * (1 + σ)) := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds (show (-η : ℝ) < 0 from by linarith)).filter_mono
          (nhdsWithin_le_nhds (s := Set.Iio (0 : ℝ)))] with σ hσ hgt
      have hσI : σ ∈ Set.Ioo (-η) 0 := ⟨hgt, hσ⟩
      have h1 : karS CI W ρh δ k τ σ
          = Work.RPB.signedArea (fun t : ℝ => Work.RPV.uproj (W τ t (ρh τ t σ))) := by
        unfold karS
        congr 1
        funext u
        exact hkshape_left σ hσI u
      rw [h1]
      exact harea τ hτ σ ⟨le_of_lt hgt, le_of_lt hσ⟩
    have hkarS0 : karS CI W ρh δ k τ 0 = 2 * Real.pi := by
      have h := kcj_continuousAt_eq_of_eventuallyEq (fun σ : ℝ => karS CI W ρh δ k τ σ)
        (fun σ : ℝ => 2 * Real.pi * (1 + σ)) (𝓝[<] (0 : ℝ)) nhdsWithin_le_nhds
        hkarS_cd.continuousAt (by fun_prop) hev_karS
      simpa using h
    have hne : karS CI W ρh δ k τ 0 ≠ 0 := by rw [hkarS0]; positivity
    -- ## The normalisation is `1` and the phase increment is the level increment
    have hkg1 : ∀ σ ∈ Set.Ioo (-η) 0, kg CI W ρh δ k τ σ = 1 := by
      intro σ hσI
      have hkarSσ : karS CI W ρh δ k τ σ = 2 * Real.pi * (1 + σ) := by
        have h1 : karS CI W ρh δ k τ σ
            = Work.RPB.signedArea (fun t : ℝ => Work.RPV.uproj (W τ t (ρh τ t σ))) := by
          unfold karS
          congr 1
          funext u
          exact hkshape_left σ hσI u
        rw [h1]
        exact harea τ hτ σ ⟨le_of_lt hσI.1, le_of_lt hσI.2⟩
      have hpos : 0 < 1 + σ := by linarith [hσI.1, hη1]
      have h2 : 2 * Real.pi * (1 + σ) ≠ 0 := by positivity
      unfold kg
      rw [hkarSσ]
      exact div_self h2
    have hkgam_left : ∀ σ ∈ Set.Ioo (-η) 0, ∀ u : ℝ,
        kgam CI W ρh δ k τ σ u = Work.RPV.uproj (W τ u (ρh τ u σ)) := by
      intro σ hσI u
      have h1 : kg CI W ρh δ k τ σ = 1 := hkg1 σ hσI
      have h2 : kshape CI W ρh δ k τ σ u = Work.RPV.uproj (W τ u (ρh τ u σ)) :=
        hkshape_left σ hσI u
      unfold kgam
      rw [h1, h2, kcj_kdiagM_one]
    have hdefectη : ∀ σ ∈ Set.Ioo (-η) 0, ∀ u : ℝ,
        Work.RPV.ωC (deriv (fun s : ℝ => Work.RPV.uproj (W τ u (ρh τ u s))) σ)
            (deriv (fun s : ℝ => Work.RPV.uproj (W τ s (ρh τ s σ))) u)
          = deriv (fun s : ℝ => (W τ s (ρh τ s σ)).1.2) u :=
      fun σ hσI u => hdefect τ hτ σ ⟨by linarith [hσI.1, hη₂], hσI.2⟩ u
    have hkac_left : ∀ σ ∈ Set.Ioo (-η) 0, ∀ u : ℝ,
        kac CI W ρh δ k τ σ u = kA0 W ρh δ k τ σ
          + ((W τ u (ρh τ u σ)).1.2 - (W τ 0 (ρh τ 0 σ)).1.2) :=
      kac_left_agree CI hW hκ hρh hρhv hδpos hδκ k hτ hηpos hηκ hkgam_left hdefectη
    -- ## Smoothness of the two parametrisations at `σ = 0`
    have hσ0 : (0 : ℝ) ∈ Set.Ioo (-κ) κ := ⟨by linarith, hκ⟩
    have hslice := uproj_chart_contDiffAt_kappa (t := t) hW hκ hρh hρhv hτ hσ0
    have hpairt : ContDiffAt ℝ 8 (fun σ : ℝ => (σ, t)) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    have h8_12 : (8 : ℕ∞ω) ≤ (12 : ℕ∞ω) := by norm_num
    have hU8 : ContDiffAt ℝ 8 (fun σ : ℝ => Work.RPV.uproj (W τ t (ρh τ t σ))) 0 :=
      ContDiffAt.comp (x := (0 : ℝ)) (f := fun σ : ℝ => (σ, t))
        (g := fun p : ℝ × ℝ => Work.RPV.uproj (W τ p.2 (ρh τ p.2 p.1)))
        (hslice.1.of_le h8_12) hpairt
    have hQ8 : ContDiffAt ℝ 8 (fun σ : ℝ => (W τ t (ρh τ t σ)).1.2) 0 :=
      ContDiffAt.comp (x := (0 : ℝ)) (f := fun σ : ℝ => (σ, t))
        (g := fun p : ℝ × ℝ => (W τ p.2 (ρh τ p.2 p.1)).1.2)
        (hslice.2.of_le h8_12) hpairt
    have hsliceT0 := uproj_chart_contDiffAt_kappa (t := 0) hW hκ hρh hρhv hτ hσ0
    have hpair0 : ContDiffAt ℝ 8 (fun σ : ℝ => (σ, (0 : ℝ))) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    have hQ08 : ContDiffAt ℝ 8 (fun σ : ℝ => (W τ 0 (ρh τ 0 σ)).1.2) 0 :=
      ContDiffAt.comp (x := (0 : ℝ)) (f := fun σ : ℝ => (σ, (0 : ℝ)))
        (g := fun p : ℝ × ℝ => (W τ p.2 (ρh τ p.2 p.1)).1.2)
        (hsliceT0.2.of_le h8_12) hpair0
    have hA08 : ContDiffAt ℝ 8 (fun σ : ℝ => kA0 W ρh δ k τ σ) 0 := by
      unfold kA0 kjbump kphc kstp
      fun_prop
    have hGr : ContDiffAt ℝ 8 (fun σ : ℝ => Work.RPV.levelPt
        (Work.RPV.uproj (W τ t (ρh τ t σ))) σ ((W τ t (ρh τ t σ)).1.2)) 0 :=
      chartJets_levelPt_contDiff.contDiffAt.comp 0 (hU8.prodMk (contDiffAt_id.prodMk hQ8))
    have hAcd8 : ContDiffAt ℝ 8 (fun σ : ℝ => W τ t (ρh τ t σ)) 0 := by
      refine hGr.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hσ0] with σ hσ
      exact (levelPt_uproj_eq_self (W τ t (ρh τ t σ)) σ (hρhl τ hτ t σ hσ)).symm
    have hG_cd : ContDiffAt ℝ 8 (fun σ : ℝ => Work.RPV.levelPt
        (Work.RPV.uproj (W τ t (ρh τ t σ))) σ
        ((W τ t (ρh τ t σ)).1.2 + (kA0 W ρh δ k τ σ - (W τ 0 (ρh τ 0 σ)).1.2))) 0 :=
      chartJets_levelPt_contDiff.contDiffAt.comp 0
        (hU8.prodMk (contDiffAt_id.prodMk (hQ8.add (hA08.sub hQ08))))
    have hPcd : ContDiffAt ℝ 8 (fun σ : ℝ => Work.RPV.levelPt (kgam CI W ρh δ k τ σ t) σ
        (kac CI W ρh δ k τ σ t)) 0 :=
      collarPt_contDiffAt CI hW hκ hρh hρhv hδpos hδκ k hτ hkshape_cd hne t
    -- ## The equality of the jets of the two parametrisations on `(-η, 0)`
    have hP_eq_G : ∀ σ ∈ Set.Ioo (-η) 0,
        Work.RPV.levelPt (kgam CI W ρh δ k τ σ t) σ (kac CI W ρh δ k τ σ t)
          = Work.RPV.levelPt (Work.RPV.uproj (W τ t (ρh τ t σ))) σ
            ((W τ t (ρh τ t σ)).1.2 + (kA0 W ρh δ k τ σ - (W τ 0 (ρh τ 0 σ)).1.2)) := by
      intro σ hσI
      have h1 := hkgam_left σ hσI t
      have h2 := hkac_left σ hσI t
      have h3 : kA0 W ρh δ k τ σ + ((W τ t (ρh τ t σ)).1.2 - (W τ 0 (ρh τ 0 σ)).1.2)
          = (W τ t (ρh τ t σ)).1.2 + (kA0 W ρh δ k τ σ - (W τ 0 (ρh τ 0 σ)).1.2) := by ring
      rw [h1, h2, h3]
    -- ## The `kA0` jets
    have hphase0 : ∀ j : ℕ, j ≤ 8 →
        iteratedDeriv j (fun σ : ℝ => (W 0 0 (ρh 0 0 σ)).1.2
          - (0 + Real.pi / 2 + 2 * Real.pi * (k : ℝ))) 0 = 0 := by
      intro j hj
      have h := hphase 0 j hj
      rw [hkk] at h
      simpa using h
    have hslice00 := uproj_chart_contDiffAt_kappa (t := 0) hW hκ hρh hρhv
      (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩) hσ0
    have hpair00 : ContDiffAt ℝ 8 (fun σ : ℝ => (σ, (0 : ℝ))) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    have hQ000 : ContDiffAt ℝ 8 (fun σ : ℝ => (W 0 0 (ρh 0 0 σ)).1.2) 0 :=
      ContDiffAt.comp (x := (0 : ℝ)) (f := fun σ : ℝ => (σ, (0 : ℝ)))
        (g := fun p : ℝ × ℝ => (W 0 p.2 (ρh 0 p.2 p.1)).1.2)
        (hslice00.2.of_le h8_12) hpair00
    have h0 := kcj_kcj_zero_eq W ρh k hQ000 hphase0
    have hkA0 := kA0_jets W ρh δ hδpos k τ h0
    have hGjets := kcj_jets_G_eq_level W ρh δ hδpos k hκ hU8 hQ8 hQ08 hA08 hkA0 hAcd8
      (fun σ hσ => hρhl τ hτ t σ hσ)
    -- ## Assembly
    rw [kcj_iteratedDerivWithin_Ioi_eq hPcd hj]
    calc iteratedDeriv j (fun σ : ℝ => Work.RPV.levelPt (kgam CI W ρh δ k τ σ t) σ
            (kac CI W ρh δ k τ σ t)) 0
        = iteratedDeriv j (fun σ : ℝ => Work.RPV.levelPt (Work.RPV.uproj (W τ t (ρh τ t σ))) σ
            ((W τ t (ρh τ t σ)).1.2 + (kA0 W ρh δ k τ σ - (W τ 0 (ρh τ 0 σ)).1.2))) 0 :=
          iteratedDeriv_eq_of_eqOn_Ioo_left hηpos hPcd hG_cd
            (fun x hx => hP_eq_G x (by rwa [zero_sub] at hx)) hj
      _ = iteratedDeriv j (fun σ : ℝ => W τ t (ρh τ t σ)) 0 := hGjets j hj

end Work.RPB.B5
