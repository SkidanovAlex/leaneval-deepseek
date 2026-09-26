import Mathlib
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.LayerCont.LayerT2
import Submission.Work.LayerCont.FarTail.CuspFar
import Submission.Work.Residues.ResidueTheoremK
import Submission.Work.CKFinal.S2op_integral_eq_zero
import Submission.Work.CKFinal.S2op_Aexp_expand
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Kernels.KernelFacts.KPlus_T2

set_option linter.unusedVariables false

namespace Work.CKFinal

open MeasureTheory UpperHalfPlane ModularGroup

/-! ## Linearity of `S2op` in the function variable

`S2op k F = F|_k S(T-I)²` is a group-algebra slash, hence additive and `ℂ`-homogeneous in `F`
(`Work.Kernels.slash_add_F`, `Work.Kernels.slash_smul_F`).  These small restatements are what
allow the `S(T-I)²`-defect of the trunc integrand to be computed term by term. -/

/-- `S2op` is additive in the function variable. -/
private lemma S2op_add' (k : ℤ) (F G : UpperHalfPlane → ℂ) :
    Work.Asymptotics.S2op k (F + G) = Work.Asymptotics.S2op k F + Work.Asymptotics.S2op k G := by
  simp only [Work.Asymptotics.S2op]
  exact Work.Kernels.slash_add_F k _ F G

/-- `S2op` is `ℂ`-homogeneous in the function variable. -/
private lemma S2op_smul' (k : ℤ) (c : ℂ) (F : UpperHalfPlane → ℂ) :
    Work.Asymptotics.S2op k (c • F) = c • Work.Asymptotics.S2op k F := by
  simp only [Work.Asymptotics.S2op]
  exact Work.Kernels.slash_smul_F k _ c F

/-- `S2op` is additive for differences of functions. -/
private lemma S2op_sub' (k : ℤ) (F G : UpperHalfPlane → ℂ) :
    Work.Asymptotics.S2op k (F - G) = Work.Asymptotics.S2op k F - Work.Asymptotics.S2op k G := by
  ext τ
  simp only [Pi.sub_apply, Work.Asymptotics.S2op_apply_eq, Work.Kernels.slash_S_apply]
  ring

/-! ## The pointwise vanishing of the trunc-integrand defect -/

/-- The `S(T-I)²`-defect of the non-decaying part of the trunc integrand vanishes, because `Aexp`
is a `t`-linear, `σ`-constant combination of the four coefficient functions `Gcusp ℓ d i j` and
all four of those are killed.  This is `Work.CKFinal.S2op_Aexp_expand` followed by the hypothesis
`hG`. -/
private lemma S2op_Aexp_Gcusp_eq_zero' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (hG : ∀ i j : Fin 2,
      Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.Asymptotics.Gcusp ℓ d i j) = 0)
    (τ : UpperHalfPlane) (t : ℝ) :
    Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t) τ = 0 := by
  rw [S2op_Aexp_expand]
  simp only [hG 0 0, hG 0 1, hG 1 0, hG 1 1, Pi.zero_apply, mul_zero, add_zero]

/-- **Pointwise annihilation of the trunc-integrand defect.**  The `t`-integrand of
`layerTrunc` is the sum of the kernel part, killed by the kernel identity
`Work.Residues.Kaxis_Kfun_slash_S_T2`, and (minus) the non-decaying part `Aexp`, killed by `hG`;
the `σ`-constant Gaussian weight pulls straight out of `S2op`. -/
private lemma S2op_trunc_integrand_pointwise' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ)
    (hG : ∀ i j : Fin 2,
      Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.Asymptotics.Gcusp ℓ d i j) = 0)
    (τ : UpperHalfPlane) (t : ℝ) :
    Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane =>
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) τ = 0 := by
  have hK : Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t) = 0 := by
    simpa only [Work.Asymptotics.S2op] using Work.Residues.Kaxis_Kfun_slash_S_T2 ℓ d hd t
  have hA := S2op_Aexp_Gcusp_eq_zero' ℓ d hd hG τ t
  -- the difference of the function parts is killed
  have hsub : Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t) τ = 0 := by
    rw [show (fun σ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        = (fun σ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t)
          - (fun σ : UpperHalfPlane => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        from rfl]
    rw [S2op_sub']
    simp only [Pi.sub_apply, congrFun hK τ, hA, Pi.zero_apply, sub_zero]
  -- the Gaussian weight is `σ`-constant and pulls out
  rw [show (fun σ : UpperHalfPlane =>
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t)
      = Work.Asymptotics.gaussWeight r t • (fun σ : UpperHalfPlane =>
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t) from by
    funext σ
    simp only [Pi.smul_apply, smul_eq_mul]
    ring]
  rw [S2op_smul']
  simp only [Pi.smul_apply, hsub, smul_eq_mul, mul_zero]

/-! ## The main theorem -/

/-- **`S(T-I)²` annihilates the cusp-subtracted tail `layerTrunc` of the CKMRV layer**, for every
real `r`, whenever the three `S`-shifted contours `S•τ, S•(τ+1), S•(τ+2)` are clean on `(0,∞)` and
`S(T-I)²` kills the four cusp coefficient functions `Gcusp ℓ d i j` pointwise.

Route: `layerTrunc = sinSq r · ∫_{[1,∞)} (Kaxis (Kfun ℓ d) σ t - Aexp (Gcusp ℓ d) σ t) ·
gaussWeight r t dt`; the integrands are integrable (`Work.LayerCont.FarTail.tail_integrableOn_of_clean`)
and the `t`-integrand `S2op`-defect vanishes pointwise: `S2op` kills `Kaxis (Kfun ℓ d) · t`
(`Kaxis_Kfun_slash_S_T2`), while `S2op` of `σ ↦ Aexp G σ t` is `σ ↦ Aexp (fun i j => S2op k (G i j)) σ t`,
which is `0` because `Aexp` is a `t`-linear, `σ`-constant combination of the four `G i j τ` and all
four `S2op k (Gcusp ℓ d i j)` vanish. -/
theorem S2op_layerTrunc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ)
    (hG : ∀ i j : Fin 2, Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.Asymptotics.Gcusp ℓ d i j) = 0)
    {τ : UpperHalfPlane}
    (hclean : ∀ (σ : UpperHalfPlane),
      σ ∈ ({ModularGroup.S • τ, ModularGroup.S • ((1 : ℝ) +ᵥ τ),
        ModularGroup.S • ((2 : ℝ) +ᵥ τ)} : Set UpperHalfPlane) →
      ∀ (t : ℝ) (ht : 0 < t),
        Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane =>
        Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r) τ = 0 := by
  -- Integrability of the three shifted integrands on `[1,∞)`, from cleanliness.
  have hInt : ∀ σ ∈ ({ModularGroup.S • τ, ModularGroup.S • ((1 : ℝ) +ᵥ τ),
      ModularGroup.S • ((2 : ℝ) +ᵥ τ)} : Set UpperHalfPlane),
      IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) (Set.Ici (1 : ℝ)) :=
    fun σ hσ => Work.LayerCont.FarTail.tail_integrableOn_of_clean ℓ d hd (σ := σ) (r := r)
      (fun t ht => hclean σ hσ t ht)
  -- Linearity of `S2op` under the Bochner integral over `[1,∞)`.
  have hS : Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => ∫ t in Set.Ici (1 : ℝ),
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) τ = 0 := by
    refine S2op_integral_eq_zero (s := Set.Ici (1 : ℝ))
      (f := fun (σ : UpperHalfPlane) (t : ℝ) =>
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) ?_ ?_ ?_ ?_
    · exact hInt (ModularGroup.S • τ) (by simp)
    · exact hInt (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) (by simp)
    · exact hInt (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) (by simp)
    · intro t
      exact S2op_trunc_integrand_pointwise' ℓ d hd r hG τ t
  -- `layerTrunc` as the set integral over `[1,∞)`.
  have hfun : (fun σ : UpperHalfPlane =>
      Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r)
      = fun σ : UpperHalfPlane => Work.Asymptotics.sinSq r * ∫ t in Set.Ici (1 : ℝ),
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
          * Work.Asymptotics.gaussWeight r t := by
    funext σ
    rw [Work.Asymptotics.layerTrunc]
    simp only [Work.Asymptotics.gaussWeight]
  rw [hfun]
  -- The `τ`-independent factor `sinSq r` pulls out of `S2op`.
  have hsplit : Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Asymptotics.sinSq r * ∫ t in Set.Ici (1 : ℝ),
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
        * Work.Asymptotics.gaussWeight r t) τ
      = Work.Asymptotics.sinSq r * Work.Asymptotics.S2op ((d : ℤ) / 2)
        (fun σ : UpperHalfPlane => ∫ t in Set.Ici (1 : ℝ),
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
          * Work.Asymptotics.gaussWeight r t) τ := by
    rw [show (fun σ : UpperHalfPlane => Work.Asymptotics.sinSq r * ∫ t in Set.Ici (1 : ℝ),
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
          * Work.Asymptotics.gaussWeight r t)
        = Work.Asymptotics.sinSq r • (fun σ : UpperHalfPlane => ∫ t in Set.Ici (1 : ℝ),
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) σ t)
          * Work.Asymptotics.gaussWeight r t) from by
      funext σ; simp]
    rw [S2op_smul']
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsplit, hS, mul_zero]

end Work.CKFinal
