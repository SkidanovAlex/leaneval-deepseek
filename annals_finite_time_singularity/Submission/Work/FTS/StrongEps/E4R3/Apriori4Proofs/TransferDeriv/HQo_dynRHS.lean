import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.GalBasis.hk_sq_api
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_dth_dz
import Submission.Work.FTS.StrongEps.JfamP_norm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

/-!
# `HQo α 4 (dynRHS … τ)` — the transfer-derivative right-hand side

`HQo α 4 f = SmoothOpen f ∧ HkMem α 4 f`, and the nonlinear part of the scheme's right-hand side
is `dynRHS α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ`.

* `SmoothOpen`: `smoothOpen_dynRHS_of_classC` at the class-`C` slice `slice (JfamP ρ ε g) τ`
  (available since `τ ∈ Icc 0 τ` and `hτ : 0 < τ`).
* `HkMem α 4`: `epsWP α ρ ε Φs E g τ` unfolds definitionally to
  `dynLin α (JfamP ρ ε g) τ + dynRHS α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ`
  (`PZeroScheme.lean`), so `HkMem α 4 (dynRHS … τ)` follows from `ℋ⁴`-honesty of the two
  summands by `GalBasis.hkMem_sub_open` plus the pointwise identity
  `(dynLin + dynRHS) - dynLin = dynRHS` (`HkMem_congr_Q0`).
  * `HkMem α 4 (dynLin … τ)`: `EpsE4Thr.regQo_LGammaT` at `hw` gives `HkMem α 4 (𝓛_Γ^T _)`,
    transferred to `dynLin = -𝓛_Γ^T` by `GalBasis.hkMem_neg_open`.
  * `HkMem α 4 (epsWP … τ)`: `epsWP_hkMem4_bnd` at `T := τ`, `s := τ`.  That lemma states its
    `hEll`-packages and its `ℋ⁶`-size hypothesis with the *same* constant, whereas here `hEll`
    uses `Ce` and the `ℓ⁶`-bound uses `B`; both `EllPkgGo` and `EllPkgK` are monotone in the
    package constant (`EllPkgGo_mono_const` / `EllPkgK_mono_const` below), so instantiating at
    `max Ce B` reconciles the two.
-/

/-- `EllPkgGo` is monotone in its package constant: the four size fields have the shape
`… ≤ Ce * (nonnegative factor)`. -/
theorem EllPkgGo_mono_const {α Ce Ce' : ℝ} (hα : 0 ≤ α) {g Φg : Work.FTS.Galerkin.Fn}
    (h : Ce ≤ Ce') (hp : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    Work.FTS.VocabO.EllPkgGo α Ce' g Φg := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA : 0 ≤ α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg (Real.rpow_nonneg hα _) hX
  refine ⟨hp.sol, hp.smooth, ⟨hp.R.1, ?_⟩, ⟨hp.U.1, ?_⟩, ⟨hp.V.1, ?_⟩, hp.vanishU,
    ⟨hp.Vth.1, ?_⟩⟩
  · exact le_trans hp.R.2 (mul_le_mul_of_nonneg_right h hX)
  · exact le_trans hp.U.2 (mul_le_mul_of_nonneg_right h hX)
  · exact le_trans hp.V.2 (mul_le_mul_of_nonneg_right h hX)
  · refine le_trans hp.Vth.2 ?_
    calc Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g
        = Ce * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g) := mul_assoc _ _ _
      _ ≤ Ce' * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_right h hA
      _ = Ce' * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g := (mul_assoc _ _ _).symm

/-- `EllPkgK` is monotone in its package constant: the three size fields have the shape
`… ≤ Ce * HkNorm α k g`. -/
theorem EllPkgK_mono_const {α Ce Ce' : ℝ} {k : ℕ} {g Φg : Work.FTS.Galerkin.Fn}
    (h : Ce ≤ Ce') (hp : Work.FTS.ClassC.EllPkgK α k Ce g Φg) :
    Work.FTS.ClassC.EllPkgK α k Ce' g Φg := by
  have hX : 0 ≤ Work.Spaces.HkNorm α k g := Work.Spaces.HkNorm_nonneg α k g
  refine ⟨hp.sol, hp.smooth, ⟨hp.R.1, ?_⟩, ⟨hp.U.1, ?_⟩, ⟨hp.V.1, ?_⟩⟩
  · exact le_trans hp.R.2 (mul_le_mul_of_nonneg_right h hX)
  · exact le_trans hp.U.2 (mul_le_mul_of_nonneg_right h hX)
  · exact le_trans hp.V.2 (mul_le_mul_of_nonneg_right h hX)

theorem HQo_dynRHS {α C₀ B Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {ε τ : ℝ}
    (hτ : 0 < τ) (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hC : ∀ s ∈ Set.Icc 0 τ, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
    (hb4 : ∀ s ∈ Set.Icc 0 τ, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ C₀ * α ^ 2)
    (hb6 : ∀ s ∈ Set.Icc 0 τ, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ B) :
    Work.FTS.VocabO.HQo α 4 (Work.FTS.Galerkin.dynRHS α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
      (Work.FTS.StrongEps.JfamP ρ ε g) τ) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hτmem : τ ∈ Set.Icc (0 : ℝ) τ := ⟨hτ.le, le_rfl⟩
  have hw : Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) := hC τ hτmem
  have hell : Work.FTS.VocabO.EllPkgGo α Ce
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
      (E (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) := (hEll _ hw).1
  refine ⟨?_, ?_⟩
  · exact Work.FTS.StrongEps.smoothOpen_dynRHS_of_classC hα0 hα1 hw hell hstar
  · -- reconcile the two constants: packages at `Ce`, `ℋ⁶`-size at `B`
    have hCeB : Ce ≤ max Ce B := le_max_left _ _
    have hBle : B ≤ max Ce B := le_max_right _ _
    have hEllB : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α (max Ce B) u (E u) ∧
          Work.FTS.ClassC.EllPkgK α 6 (max Ce B) u (E u) :=
      fun u hu => ⟨EllPkgGo_mono_const hα0.le hCeB (hEll u hu).1,
        EllPkgK_mono_const hCeB (hEll u hu).2⟩
    have hb6B : ∀ s ∈ Set.Icc (0 : ℝ) τ, Work.FTS.StrongGlobal.Xn6 α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ max Ce B :=
      fun s hs => le_trans (hb6 s hs) hBle
    obtain ⟨KW, _hKW, hbnd⟩ :=
      Work.FTS.StrongEps.epsWP_hkMem4_bnd (α := α) (C₀ := C₀) (Ce := max Ce B) (Cs := Cs)
        (T := τ) (ρ := ρ) (Φs := Φs) (E := E) (g := g) (ε := ε)
        hα hEllB hstar hml hC hb4 hb6B
    -- the two summands, and `epsWP = dynLin + dynRHS` definitionally
    have hEpssmo : Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) :=
      Work.FTS.StrongEps.smoothOpen_epsWP (C₀ := C₀) (T := τ) hα hEllB hstar hC τ hτmem
    have hEpsmem : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) :=
      (hbnd τ hτmem).1
    have hLGT := Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT (α := α)
      (x := Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) hα hw
    have hlinsmo : Work.FTS.EllipticEst.SmoothOpen
        (Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.FTS.GalBasis.smoothOpen_neg hLGT.1
    have hlinmem : Work.Spaces.HkMem α 4
        (Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.FTS.GalBasis.hkMem_neg_open α 4 hLGT.2.1
    have hsub : Work.Spaces.HkMem α 4
        (fun z θ => Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ z θ
          - Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε g) τ z θ) :=
      Work.FTS.GalBasis.hkMem_sub_open α 4 hEpssmo hlinsmo hEpsmem hlinmem
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hsub
      (fun z _hz θ _hθ => ?_)
    show Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ z θ
        - Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε g) τ z θ
      = Work.FTS.Galerkin.dynRHS α
          (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
          (Work.FTS.StrongEps.JfamP ρ ε g) τ z θ
    simp only [Work.FTS.StrongEps.epsWP]
    ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
