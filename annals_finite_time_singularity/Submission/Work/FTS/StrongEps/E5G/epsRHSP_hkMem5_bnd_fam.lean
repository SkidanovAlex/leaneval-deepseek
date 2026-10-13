import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E5G.epsWP_hkMem5_bnd_fam
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongEps.HkSq_Jeps_le
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.PZeroAux.PzJepsHkMem
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.PZeroAux.PzHkNormFour
import Submission.Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.OpenPkg.l12zero_field
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.EllipticEst.HkNorm_add_fts
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

/-! ## Auxiliary: the projection `P₀` and the composition `P₀ ∘ J_ε` are bounded on `ℋ⁵`

Both statements are the order-`5` instances of the level-`k` estimate
`PZeroAux.PzHkNormFour` / `PZeroAux.hkNorm_Pz_le` (proved) composed with the `E1` estimate
`HkSq_Jeps_le` (proved).  The only order-sensitive ingredient in the projection estimate is the
zero-mode bound `OpenPkg.l12zero_field`, `|L₁₂ f 0| ≤ C₁ ‖f‖_{ℋ⁴}`, which is an `ℋ⁴`-estimate and
hence also bounds `|L₁₂ f 0|` by `C₁ ‖f‖_{ℋ⁵}` via the monotonicity of the norm.  The
correction profile `bump` is `ℋ⁵`-bounded uniformly in `α` (`exists_HkNorm_bump_le`). -/

/-- **`P₀` is bounded on `ℋ⁵`, uniformly in `α ∈ (0,1]`.**

`P₀ f = f + (−c) • bump` with `c = L₁₂ f 0 / pzNorm`, so the subadditivity of the weighted norm
on the open quadrant (`HkNorm_add_fts`), its absolute homogeneity (`HkNorm_const_mul`), the
zero-mode bound `|L₁₂ f 0| ≤ C₁ ‖f‖_{ℋ⁴} ≤ C₁ ‖f‖_{ℋ⁵}` (from `OpenPkg.l12zero_field` plus the
monotonicity `HkNorm_mono_of_mem`) and the uniform bound `‖bump‖_{ℋ⁵} ≤ B` give the constant
`A = √2 (1 + C₁ B / pzNorm)`. -/
theorem hkNorm_Pz_le_five_local :
    ∃ A : ℝ, 0 < A ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 5 f →
        Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.Pz f)
          ≤ A * Work.Spaces.HkNorm α 5 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongEps.PZeroAux.exists_HkNorm_bump_le
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  have hC₁nn : 0 ≤ C₁ := hC₁pos.le
  refine ⟨Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm), ?_, ?_⟩
  · have h1 : 0 < C₁ * B / Work.FTS.StrongEps.pzNorm :=
      div_pos (mul_pos hC₁pos hBpos) hpzpos
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  · intro α hα f hfsm hm5
    have hα0 : 0 < α := hα.1
    have hα1 : α ≤ 1 := hα.2
    have hm4 : Work.Spaces.HkMem α 4 f :=
      Work.FTS.OpenPkg.HkMem_mono_open hfsm 4 (by norm_num) hm5
    have hl12 : |Work.Construction.L12 f 0| ≤ C₁ * Work.Spaces.HkNorm α 4 f := by
      simpa only [Work.FTS.Nonlin.Xn] using hC₁ α hα0 hα1 f ⟨hfsm, hm4⟩
    have hnorm45 : Work.Spaces.HkNorm α 4 f ≤ Work.Spaces.HkNorm α 5 f :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num) hm5
    have hcoefnn : 0 ≤ C₁ / Work.FTS.StrongEps.pzNorm := div_nonneg hC₁nn hpzpos.le
    have hc_bound : |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
        ≤ (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 5 f := by
      rw [abs_div, abs_of_pos hpzpos]
      calc |Work.Construction.L12 f 0| / Work.FTS.StrongEps.pzNorm
          ≤ (C₁ * Work.Spaces.HkNorm α 4 f) / Work.FTS.StrongEps.pzNorm :=
            div_le_div_of_nonneg_right hl12 hpzpos.le
        _ = (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 f := by ring
        _ ≤ (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 5 f :=
            mul_le_mul_of_nonneg_left hnorm45 hcoefnn
    have hbmem : Work.Spaces.HkMem α 5 Work.FTS.StrongEps.bump :=
      Work.FTS.StrongEps.PZeroAux.hkMem_bump α 5
    have hbnorm : Work.Spaces.HkNorm α 5 Work.FTS.StrongEps.bump ≤ B :=
      hB α hα 5 (by norm_num)
    have hgbump : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry Work.FTS.StrongEps.bump)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun n => Work.FTS.StrongEps.smoothOpen_bump.forall n
    have hgsm : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry (fun z θ => (-(Work.Construction.L12 f 0
          / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun n => (Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen
        (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
        Work.FTS.StrongEps.smoothOpen_bump).forall n
    have hgmem : Work.Spaces.HkMem α 5
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
      Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen _ hbmem
    have hPz : Work.FTS.StrongEps.Pz f
        = fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ := by
      funext z θ
      rw [Work.FTS.StrongEps.Pz_apply]
      ring
    rw [hPz]
    have hadd := Work.FTS.EllipticEst.HkNorm_add_fts α 5
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hfsm) hgsm hm5 hgmem
    have hcm : Work.Spaces.HkNorm α 5
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ)
        = |-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)|
          * Work.Spaces.HkNorm α 5 Work.FTS.StrongEps.bump :=
      Work.FTS.EllipticEst.HkNorm_const_mul α 5 _ hgbump
    rw [hcm, abs_neg] at hadd
    calc Work.Spaces.HkNorm α 5 (fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 5 f
            + |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
              * Work.Spaces.HkNorm α 5 Work.FTS.StrongEps.bump) := hadd
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 5 f
            + (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 5 f * B) := by
          refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (Real.sqrt_nonneg 2)
          exact mul_le_mul hc_bound hbnorm (Work.Spaces.HkNorm_nonneg _ _ _)
            (mul_nonneg hcoefnn (Work.Spaces.HkNorm_nonneg _ _ _))
      _ = Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.HkNorm α 5 f := by ring

/-- **`P₀ ∘ J_ε` is bounded on `ℋ⁵`, uniformly in `ε ∈ (0,1]`.**

The composition of the order-`5` projection bound above with the `E1` estimate
`HkSq α 5 (J_ε f) ≤ e^{Cε} HkSq α 5 f` (`HkSq_Jeps_le`): after taking square roots the factor is
`e^{Cε/2} ≤ e^{C/2}` for `ε ≤ 1`.  The membership `HkMem α 5 (J_ε f)` needed by `E1` is
`HkMem_Jeps`, and the smoothness of `J_ε f` is `smoothOpen_Jeps`. -/
theorem hkNorm_PzJeps_le_five_local {α : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ f : ℝ → ℝ → ℝ,
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) →
        Work.Spaces.HkMem α 5 f →
          Work.Spaces.HkNorm α 5
              (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
            ≤ A * Work.Spaces.HkNorm α 5 f := by
  obtain ⟨A₀, hA₀pos, hA₀⟩ := hkNorm_Pz_le_five_local
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.HkSq_Jeps_le ρ hρ.moll
  refine ⟨A₀ * Real.exp (C / 2), by positivity, ?_⟩
  intro ε hε hε1 f hsm hmem
  have hsmJ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsm
  have hmemJ : Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hsm hmem
  have h1 : Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
      ≤ A₀ * Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.Jeps ρ ε f) :=
    hA₀ α hα (Work.FTS.StrongEps.Jeps ρ ε f) hsmJ hmemJ
  have h2 : Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.Jeps ρ ε f)
      ≤ Real.exp (C / 2) * Work.Spaces.HkNorm α 5 f := by
    have hsq := hC α hα 5 ε hε hε1 f hsm hmem hmemJ
    have hE : (0 : ℝ) < Real.exp (C * ε) := Real.exp_pos _
    have hsqrt : Real.sqrt (Real.exp (C * ε)) = Real.exp (C * ε / 2) :=
      (Real.exp_half (C * ε)).symm
    calc Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.Jeps ρ ε f)
        = Real.sqrt (Work.Spaces.HkSq α 5 (Work.FTS.StrongEps.Jeps ρ ε f)) := rfl
      _ ≤ Real.sqrt (Real.exp (C * ε) * Work.Spaces.HkSq α 5 f) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (Real.exp (C * ε)) * Work.Spaces.HkNorm α 5 f := by
          rw [Real.sqrt_mul hE.le, Work.Spaces.HkNorm]
      _ = Real.exp (C * ε / 2) * Work.Spaces.HkNorm α 5 f := by rw [hsqrt]
      _ ≤ Real.exp (C / 2) * Work.Spaces.HkNorm α 5 f := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkNorm_nonneg α 5 f)
          exact Real.exp_le_exp.mpr (by nlinarith [hCpos, hε, hε1])
  calc Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
      ≤ A₀ * Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.Jeps ρ ε f) := h1
    _ ≤ A₀ * (Real.exp (C / 2) * Work.Spaces.HkNorm α 5 f) :=
        mul_le_mul_of_nonneg_left h2 hA₀pos.le
    _ = (A₀ * Real.exp (C / 2)) * Work.Spaces.HkNorm α 5 f := by ring

theorem epsRHSP_hkMem5_bnd_fam {α C₀ Ce Cs Cs6 T : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {G : ℕ → Work.FTS.Galerkin.Fam} {ε : ℕ → ℝ}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc (0 : ℝ) 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hb4 : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
        ≤ C₀ * α ^ 2)
    (hb6 : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
        ≤ Ce) :
    ∃ KW : ℝ, 0 < KW ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s) ∧
        Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s) ≤ KW := by
  -- ### the level-five bound on the pre-mollified right-hand side `epsWP`
  obtain ⟨Kw, hKw, hWP⟩ :=
    epsWP_hkMem5_bnd_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (Cs6 := Cs6) (T := T)
      (ρ := ρ) (Φs := Φs) (E := E) (G := G) (ε := ε)
      hα hρ hEll hstar hstar6 hml hC hb4 hb6
  -- ### the level-five bound on `P₀ ∘ J_ε`
  obtain ⟨A, hApos, hA⟩ := hkNorm_PzJeps_le_five_local (ρ := ρ) hρ hα
  refine ⟨A * Kw, mul_pos hApos hKw, fun n s hs => ?_⟩
  -- `epsWP` is `C^∞` on the open quadrant and honest in `ℋ⁵` at every fake time
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) :=
    smoothOpen_epsWP (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (T := T) (ρ := ρ) (Φs := Φs) (E := E)
      (g := G n) (ε := ε n) hα hEll hstar (fun s hs => hC n s hs) s hs
  have hsm' : ∀ k : ℕ, ContDiffOn ℝ (↑k)
      (Function.uncurry (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s))
      Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsm
  obtain ⟨hmem5, hnorm5⟩ := hWP n s hs
  refine ⟨?_, ?_⟩
  · -- membership: `P₀ J_ε` preserves `ℋ⁵`
    exact Work.FTS.StrongEps.PZeroAux.PzJepsHkMem 5 hρ hα (hε n).1 hsm' hmem5
  · -- the size bound
    calc Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s)
        = Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ (ε n)
            (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s))) := rfl
      _ ≤ A * Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s) :=
          hA (ε n) (hε n).1 (hε n).2 _ hsm' hmem5
      _ ≤ A * Kw := mul_le_mul_of_nonneg_left hnorm5 hApos.le

end Work.FTS.StrongEps.E5G
