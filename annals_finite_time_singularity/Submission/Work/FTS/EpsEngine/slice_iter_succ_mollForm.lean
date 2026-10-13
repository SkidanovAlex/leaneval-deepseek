/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/slice_iter_succ_mollForm.lean` — the per-iterate **mollified form**
# of the Picard iteration of the projected `ε`-scheme

The `(n+1)`-st Picard iterate of `Feps = Pz ∘ J_ε ∘ profRHS ∘ Pz ∘ J_ε` is, by definition,
`h₀ + ∫₀^τ Feps (slice (iter n) s) ds`.  The identity proved here is the **Fubini form** of that
increment: the time integral is pushed *inside* the mollifier,

    slice (iter (n+1)) τ  =  h₀ + J_ε (∫₀^τ profRHS (Pz (J_ε (slice (iter n) s))) ds)
                                  − (∫₀^τ c_s ds) · bump        on `Q0`,

`c_s := L12 (J_ε (profRHS (Pz (J_ε (slice (iter n) s))))) 0 / pzNorm` — exactly the shape consumed
by `SORuling.smoothOpen_of_mollForm` / `SORuling.smoothOpen_picard_slice`
(`EpsEngine/SmoothOpenIter.lean`) and by the `hlimP`/`hreg` chapters of `NOTES_LocalStep.md` (the
pass-to-the-limit arguments).  The two ingredients are

* the Fubini exchange of `∫₀^τ` with the compactly supported convolution `Jker ρ ε`
  (`SORuling.conv_intervalIntegral_swap`), plus the `s`-independence of `bump` — the private
  `intervalIntegral_Jeps_swap_aux` below (the Fubini/linearity step), and
* the joint continuity of `(s, x) ↦ logPull (profRHS (Pz (J_ε (slice (iter n) s)))) x`, which comes
  from the `XBall`-invariant `hP` through `profRHS_pre_sub_pt_le_Sq` +
  `SORuling.continuous_logPull_family`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convolution
import Submission.Work.FTS.EpsEngine.SmoothOpenIter
import Submission.Work.FTS.EpsEngine.LocalStepXBall

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Convolution
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Fubini for the projected mollified right-hand side.**  If the integrand has the (pointwise, on
the open quadrant) mollified form `F (slice W s) = J_ε (G s) − c s · bump` for `s ∈ [0,τ]`, and the
family `G` is jointly continuous in the log coordinates, then its time integral is

    ∫₀^τ F (slice W s) z θ  =  J_ε (∫₀^τ G s ds) z θ − (∫₀^τ c s ds) · bump z θ .

The `hG`-continuity makes `(s, x) ↦ Jker ρ ε x · logPull (G ⌊s⌋) (· − x)` product-integrable, which
is what `SORuling.conv_intervalIntegral_swap` needs. -/
private theorem intervalIntegral_Jeps_swap_aux {ρ : ℝ × ℝ → ℝ} {ε τ : ℝ}
    (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hτ : 0 ≤ τ)
    {F : Fn → Fn} {W : Fam} {G : ℝ → Fn} {c : ℝ → ℝ}
    (hF : ∀ s ∈ Set.Icc 0 τ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      F (slice W s) z θ = Jeps ρ ε (G s) z θ - c s * bump z θ)
    (hG : Continuous (fun q : ℝ × (ℝ × ℝ) => logPull (G q.1) q.2))
    (hFint : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      IntervalIntegrable (fun s => F (slice W s) z θ) volume 0 τ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ s in (0 : ℝ)..τ, F (slice W s) z θ)
      = Jeps ρ ε (fun z' θ' => ∫ s in (0 : ℝ)..τ, G s z' θ') z θ
        - (∫ s in (0 : ℝ)..τ, c s) * bump z θ := by
  set Ψ : Fn := fun z θ => ∫ s in (0 : ℝ)..τ, G s z θ with hΨdef
  have hlogΨ : logPull Ψ = fun x => ∫ s in (0 : ℝ)..τ, logPull (G s) x := rfl
  have hB := SORuling.conv_intervalIntegral_swap (k := Jker ρ ε)
    (contDiff_Jker ρ hρ ε 0).continuous (hasCompactSupport_Jker ρ hρ hε)
    (H := fun s => logPull (G s)) hG hτ (sOf z, zetaOf θ)
  have hJs : (fun s => Jeps ρ ε (G s) z θ) = fun s =>
      (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull (G s))
        (sOf z, zetaOf θ) :=
    funext fun s => Jeps_eq_conv ρ ε _ hz hθ
  have hJΨ : Jeps ρ ε Ψ z θ = (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun y => ∫ s in (0 : ℝ)..τ, logPull (G s) y)) (sOf z, zetaOf θ) := by
    rw [Jeps_eq_conv ρ ε Ψ hz hθ, hlogΨ]
  have hA : IntervalIntegrable (fun s => Jeps ρ ε (G s) z θ) volume 0 τ := by
    rw [hJs]; exact hB.1
  have hAint : ∫ s in (0 : ℝ)..τ, Jeps ρ ε (G s) z θ = Jeps ρ ε Ψ z θ := by
    rw [hJs, hB.2, hJΨ]
  have hFeq : ∀ s ∈ uIcc (0 : ℝ) τ,
      F (slice W s) z θ = Jeps ρ ε (G s) z θ - c s * bump z θ := by
    intro s hs
    rw [uIcc_of_le hτ] at hs
    exact hF s hs z θ hz hθ
  have hcb : ∫ s in (0 : ℝ)..τ, c s * bump z θ
      = ∫ s in (0 : ℝ)..τ, (Jeps ρ ε (G s) z θ - F (slice W s) z θ) := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    show c s * bump z θ = Jeps ρ ε (G s) z θ - F (slice W s) z θ
    rw [hFeq s hs]; ring
  have hsub := intervalIntegral.integral_sub hA (hFint z θ hz hθ)
  have hmc : ∫ s in (0 : ℝ)..τ, c s * bump z θ = (∫ s in (0 : ℝ)..τ, c s) * bump z θ :=
    intervalIntegral.integral_mul_const _ _
  show ∫ s in (0 : ℝ)..τ, F (slice W s) z θ = Jeps ρ ε Ψ z θ
    - (∫ s in (0 : ℝ)..τ, c s) * bump z θ
  linarith [hcb, hsub, hmc, hAint]

theorem slice_iter_succ_mollForm {α C₀ R Ce Cs Lw δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ} {h₀ : Work.FTS.Galerkin.Fn} (n : ℕ)
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (h0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hP : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₀
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s))
    (hEq : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ, Work.FTS.StrongEps.EpsSq α (fun z θ =>
      Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s z θ
        - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) t z θ) ≤ Lw * (s - t) ^ 2)
    (hFint : ∀ τ ∈ Set.Icc 0 δ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      IntervalIntegrable (fun s => Work.FTS.EpsEngine.Feps α ρ ε Φs E
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s) z θ) volume 0 τ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ (n + 1)) τ z θ
      = h₀ z θ
        + Work.FTS.StrongEps.Jeps ρ ε (fun z' θ' => ∫ s in (0 : ℝ)..τ,
            Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
              (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
                (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
                  (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s))) z' θ') z θ
        - (∫ s in (0 : ℝ)..τ, Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε
            (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
              (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
                (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.iter
                  (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ n) s))))) 0
            / Work.FTS.StrongEps.pzNorm) * Work.FTS.StrongEps.bump z θ := by
  have hτ0 : (0 : ℝ) ≤ τ := hτ.1
  -- the *unclamped* and *clamped* families of pre-mollified right-hand sides
  set Gr : ℝ → Fn := fun s => EpsLocalPStar.profRHS α Φs E
      (Pz (Jeps ρ ε (slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s))) with hGr
  set Gc : ℝ → Fn := fun s => Gr (Set.projIcc 0 τ hτ0 s : ℝ) with hGc
  have hGc_eq : ∀ s ∈ Set.Icc 0 τ, Gc s = Gr s := by
    intro s hs
    simp only [hGc]
    exact congrArg Gr (by rw [Set.projIcc_of_mem hτ0 hs])
  -- the iterate unfolds to `h₀ + ∫₀^τ Feps (slice (iter n) s) z θ`
  have hiter : slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ z θ
      = h₀ z θ + ∫ s in (0 : ℝ)..τ, Feps α ρ ε Φs E
          (slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s) z θ := by
    simp only [EpsLocalPStar.iter_succ, slice]
  -- `Gr` is continuous on the open quadrant and Lipschitz in the time parameter
  have hcont : ∀ s ∈ Set.Icc 0 τ, ContinuousOn (Function.uncurry (Gr s))
      Work.FTS.EllipticEst.Q0 := by
    intro s hs
    have hsδ : s ∈ Set.Icc 0 δ := ⟨hs.1, le_trans hs.2 hτ.2⟩
    exact ((smoothOpen_profRHS_of_classC (α := α) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E)
      hα hEll hstar (hP s hsδ).classC).forall 0).continuousOn
  obtain ⟨C, hCpos, hC⟩ := EpsLocalPStar.profRHS_pre_sub_pt_le_Sq (α := α) (C₀ := C₀) (Ce := Ce)
    (Cs := Cs) (R := R) (ρ := ρ) (Φs := Φs) (E := E)
    hα hρ hε hε1 hEll hstar hml hR
  set K : NNReal := ⟨C * Real.sqrt Lw, mul_nonneg hCpos.le (Real.sqrt_nonneg _)⟩ with hK
  have hlip : ∀ s ∈ Set.Icc 0 τ, ∀ t ∈ Set.Icc 0 τ, ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (Real.pi / 2) → |Gr s z θ - Gr t z θ| ≤ K * |s - t| := by
    intro s hs t ht z θ hz' hθ'
    have hsδ : s ∈ Set.Icc 0 δ := ⟨hs.1, le_trans hs.2 hτ.2⟩
    have htδ : t ∈ Set.Icc 0 δ := ⟨ht.1, le_trans ht.2 hτ.2⟩
    have hPs := hP s hsδ
    have hPt := hP t htδ
    have h1 := hC hPs.smoothOpen hPt.smoothOpen hPs.mem hPs.sq_le hPt.mem hPt.sq_le
      hPs.classC hPt.classC hPs.ball hPt.ball z θ hz' hθ'.1 hθ'.2
    have h2 : Real.sqrt (EpsSq α (fun z θ =>
          slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s z θ
            - slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) t z θ))
        ≤ Real.sqrt Lw * |s - t| := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hLw]
      exact Real.sqrt_le_sqrt (hEq s hsδ t htδ)
    calc |Gr s z θ - Gr t z θ|
        ≤ C * Real.sqrt (EpsSq α (fun z θ =>
            slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s z θ
              - slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) t z θ)) := h1
      _ ≤ C * (Real.sqrt Lw * |s - t|) := mul_le_mul_of_nonneg_left h2 hCpos.le
      _ = (K : ℝ) * |s - t| := by
          show C * (Real.sqrt Lw * |s - t|) = (C * Real.sqrt Lw) * |s - t|
          ring
  have hG : Continuous (fun q : ℝ × (ℝ × ℝ) => logPull (Gc q.1) q.2) :=
    SORuling.continuous_logPull_family hτ0 hcont hlip
  -- the pointwise mollified form of `Feps` at the iterated slices
  have hFpt : ∀ s ∈ Set.Icc 0 τ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Feps α ρ ε Φs E (slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s) z θ
        = Jeps ρ ε (Gc s) z θ
          - (Work.Construction.L12 (Jeps ρ ε (Gc s)) 0 / pzNorm) * bump z θ := by
    intro s hs z θ hz' hθ'
    show Pz (Jeps ρ ε (Gr s)) z θ = Jeps ρ ε (Gc s) z θ
      - (Work.Construction.L12 (Jeps ρ ε (Gc s)) 0 / pzNorm) * bump z θ
    rw [hGc_eq s hs, Pz_apply]
  -- Fubini
  have hswap := intervalIntegral_Jeps_swap_aux (ρ := ρ) (ε := ε) (τ := τ) hρ hε hτ0
    (F := Feps α ρ ε Φs E) (W := EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) (G := Gc)
    (c := fun s => Work.Construction.L12 (Jeps ρ ε (Gc s)) 0 / pzNorm) (z := z) (θ := θ)
    hFpt hG (fun z θ hz' hθ' => hFint τ hτ z θ hz' hθ') hz hθ
  -- remove the time clamping inside `J_ε` and inside the projection coefficient
  have hΨeq : (fun z' θ' => ∫ s in (0 : ℝ)..τ, Gc s z' θ')
      = fun z' θ' => ∫ s in (0 : ℝ)..τ, EpsLocalPStar.profRHS α Φs E
          (Pz (Jeps ρ ε (slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s))) z' θ' := by
    funext z' θ'
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le hτ0] at hs
    rw [hGc_eq s hs]
  have hceq : (∫ s in (0 : ℝ)..τ, Work.Construction.L12 (Jeps ρ ε (Gc s)) 0 / pzNorm)
      = ∫ s in (0 : ℝ)..τ, Work.Construction.L12 (Jeps ρ ε (EpsLocalPStar.profRHS α Φs E
          (Pz (Jeps ρ ε (slice (EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀ n) s))))) 0
          / pzNorm := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le hτ0] at hs
    rw [hGc_eq s hs]
  rw [hiter, hswap, hΨeq, hceq]
  ring

end Work.FTS.EpsEngine
