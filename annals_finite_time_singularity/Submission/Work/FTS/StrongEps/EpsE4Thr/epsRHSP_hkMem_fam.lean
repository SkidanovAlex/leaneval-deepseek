import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPBdd
import Submission.Work.FTS.StrongEps.EpsE4Thr.HkNorm_epsRHSP_le
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The strengthened (level-six) form of the family estimate**: along a family `g` satisfying the
standing hypotheses of the projected scheme on `[0,T]`, the scheme's right-hand side
`epsRHSP α ρ ε Φs E g σ` is smooth on the open quadrant and honest in `ℋ⁶` at every fake time
`σ ∈ [0,T]`.

This is `EpsLocalPStar.EpsRHSPBdd` transported from a single profile to the family along
`StrongEps.epsRHSP_eq_slice`: `epsRHSP α ρ ε Φs E g σ = epsRHPSlice α ρ ε Φs E σ (slice g σ)`, and
the class-`C` small-ball data as well as the `ℋ⁶`-size bound required by `EpsRHSPBdd` are exactly
the hypotheses `hC`, `hball`, `hbd` evaluated at `slice g σ`.

`sorry`-free. -/
theorem epsRHSP_smoothOpen_hkMem6_fam {α C₀ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {ε T : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice g s))
    (hmem : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice g s))
    (hbd : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g s) ≤ B)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s))))
    (hball : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)))
        ≤ C₀ * α ^ 2) :
    ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ)
        ∧ Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) := by
  -- the slicewise class-`C` estimate of the scheme's right-hand side
  obtain ⟨_, _, hbdR⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPBdd (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (B := B) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hB
  intro σ hσ
  -- the right-hand side of the family at `σ` is the slicewise one at `slice g σ`
  rw [Work.FTS.StrongEps.epsRHSP_eq_slice]
  obtain ⟨hSmo, hMem6, -⟩ :=
    hbdR σ (slice g σ) (hsm σ hσ) (hmem σ hσ) (hbd σ hσ) (hC σ hσ) (hball σ hσ)
  exact ⟨hSmo, hMem6⟩

/-- **`ℋ⁴`-membership of the scheme's right-hand side along a family.**

This is the `ℋ⁴`-membership obligation of the level-four energy estimates of the local existence
scheme.  It is immediate from the stronger level-six form
`epsRHSP_smoothOpen_hkMem6_fam` together with the monotonicity of `HkMem` in the order
(`OpenPkg.HkMem_mono_open`, whose `SmoothOpen` input is the first conjunct of that same estimate):
the `ℋ⁴`-integrand is dominated, term by term, by the `ℋ⁶`-integrand.

`sorry`-free. -/
theorem epsRHSP_hkMem_fam {α C₀ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {ε T : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice g s))
    (hmem : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice g s))
    (hbd : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g s) ≤ B)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s))))
    (hball : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)))
        ≤ C₀ * α ^ 2) :
    ∀ σ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) := by
  intro σ hσ
  obtain ⟨hSmo, hMem6⟩ :=
    epsRHSP_smoothOpen_hkMem6_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (B := B)
      (ρ := ρ) (Φs := Φs) (E := E) (g := g) (ε := ε) (T := T)
      hα hρ hε hε1 hEll hstar hml hB hsm hmem hbd hC hball σ hσ
  -- honesty in `ℋ⁶` descends to `ℋ⁴`, the `ℋ⁴`-integrand being dominated by the `ℋ⁶`-one
  exact Work.FTS.OpenPkg.HkMem_mono_open hSmo 4 (by norm_num) hMem6

end Work.FTS.StrongEps.EpsE4Thr
