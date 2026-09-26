import Mathlib
import Submission.Work.LayerCont.LayerT2
import Submission.Work.Residues.ResidueTheoremK
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.LayerCont.FarTail.CuspFar
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.LayerCont.InteriorDD.Cleanliness
import Submission.Work.CKFinal.tendsto_S2op_sub_Aexp_zero
import Submission.Work.CKFinal.S2op_integral_eq_zero
import Submission.Work.CKFinal.S2op_Gcusp_of_tendsto
import Submission.Work.CKFinal.S2op_Gcusp_all_of_clean
import Submission.Work.CKFinal.S2op_layerLow
import Submission.Work.CKFinal.S2op_layerTrunc

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/CKFinal/DESIGN.md first (orchestrator design; your lemma is one node of its DAG; its §0 lists what is NOT actually proved and §5 what NOT to do). Clashes fixed by the lead (2026-09-25): Kaxis_bounded_compact's Pspace/Cseg/exists_local_bound_clean/… now carry a Kbc suffix; MiddleRange.Main's continuous_jInvariantFun is continuous_jInvariantFun_mr. Siblings run in parallel; import them when they land.

-/

namespace Work.CKFinal

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

/-! ## Elementary `j`-invariance and `S2op`-linearity

The three points `S•τ`, `S•(τ+1)`, `S•(τ+2)` of the `S(T-I)²`-defect all have the same modular
`j`-invariant as `τ`, so one cleanliness hypothesis at `τ` makes all three contours clean.  The
sub-lemmas below record that invariance and the linearity of `S2op` used to reassemble the layer
from its three pieces. -/

/-- `j` is invariant under translation by `2`. -/
lemma jInvariantFun_vadd_two_pl (τ : UpperHalfPlane) :
    Work.Kernels.jInvariantFun ((2 : ℝ) +ᵥ τ) = Work.Kernels.jInvariantFun τ := by
  rw [Work.Kernels.vadd_one_add_one, Work.Kernels.KernelFacts.jInvariantFun_vadd_one,
    Work.Kernels.KernelFacts.jInvariantFun_vadd_one]

/-- `S(T-I)²` is additive in the function variable. -/
lemma S2opPl_add (k : ℤ) (F G : UpperHalfPlane → ℂ) :
    Work.Asymptotics.S2op k (F + G) = Work.Asymptotics.S2op k F + Work.Asymptotics.S2op k G := by
  simp only [Work.Asymptotics.S2op]
  exact Work.Kernels.slash_add_F k _ F G

/-- `S(T-I)²` is `ℂ`-linear in the function variable, hence acts coefficientwise on a
four-term constant-coefficient combination. -/
lemma S2opPl_sum4 (k : ℤ) (c0 c1 c2 c3 : ℂ) (F0 F1 F2 F3 : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    Work.Asymptotics.S2op k (fun σ : UpperHalfPlane =>
        c0 * F0 σ + c1 * F1 σ + c2 * F2 σ + c3 * F3 σ) τ
      = c0 * Work.Asymptotics.S2op k F0 τ + c1 * Work.Asymptotics.S2op k F1 τ
        + c2 * Work.Asymptotics.S2op k F2 τ + c3 * Work.Asymptotics.S2op k F3 τ := by
  simp only [Work.Asymptotics.S2op_apply_eq, Work.Kernels.slash_S_apply]
  ring

/-- **The high part of the layer is annihilated by `S(T-I)²`**, as soon as `S(T-I)²` kills the
four cusp coefficient functions: the high part is a `τ`-constant-coefficient combination of the
four `Gcusp ℓ d i j`. -/
theorem S2op_highPart (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ)
    (hG : ∀ i j : Fin 2,
      Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.Asymptotics.Gcusp ℓ d i j) = 0) :
    Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) σ r) = 0 := by
  funext τ
  have hfun : (fun σ : UpperHalfPlane =>
        Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) σ r)
      = fun σ : UpperHalfPlane =>
          ((((Real.pi * r ^ 2 : ℝ) : ℂ) * (Work.Asymptotics.psi1 (Real.pi * r ^ 2) : ℂ)
                * Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ))) * Work.Asymptotics.Gcusp ℓ d 0 0 σ
            + Complex.I * (Work.Asymptotics.psi1 (Real.pi * r ^ 2) : ℂ)
                * ((((Real.pi * r ^ 2 : ℝ) : ℂ)) + 1)
                * Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ))) * Work.Asymptotics.Gcusp ℓ d 0 1 σ)
            + (((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)
                * (Work.Asymptotics.psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ)
                * Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)))
                * Work.Asymptotics.Gcusp ℓ d 1 0 σ)
            + Complex.I * (Work.Asymptotics.psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ)
                * ((((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)) + 1)
                * Complex.exp (-(((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)))
                * Work.Asymptotics.Gcusp ℓ d 1 1 σ) := by
    funext σ
    simp only [Work.Asymptotics.highPart]
  rw [hfun, S2opPl_sum4]
  simp only [hG 0 0, hG 0 1, hG 1 0, hG 1 1, Pi.zero_apply, mul_zero, add_zero]

/-- **Cleanliness transfers to the three `S`-shifted points**: if the `SL(2,ℤ)`-orbit of `τ`
misses the imaginary axis, then so do those of `S•τ`, `S•(τ+1)` and `S•(τ+2)`. -/
lemma clean_smul_S (τ : UpperHalfPlane)
    (hclean : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∀ (σ : UpperHalfPlane),
      σ ∈ ({ModularGroup.S • τ, ModularGroup.S • ((1 : ℝ) +ᵥ τ),
        ModularGroup.S • ((2 : ℝ) +ᵥ τ)} : Set UpperHalfPlane) →
      ∀ (t : ℝ) (ht : 0 < t),
        Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro σ hσ t ht
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
  rcases hσ with h | h | h
  · rw [h, Work.Kernels.KernelFacts.jInvariantFun_S_smul]; exact hclean t ht
  · rw [h, Work.Kernels.KernelFacts.jInvariantFun_S_smul,
      Work.Kernels.KernelFacts.jInvariantFun_vadd_one]; exact hclean t ht
  · rw [h, Work.Kernels.KernelFacts.jInvariantFun_S_smul, jInvariantFun_vadd_two_pl]
    exact hclean t ht

/-- `S(T-I)²` annihilates the layer, for every real `r`, at every point whose `SL(2,ℤ)`-orbit
misses the imaginary axis (the three points `S•τ`, `S•(τ+1)`, `S•(τ+2)` then have clean
contours, since `j` is `SL(2,ℤ)`-invariant). -/
theorem S2op_paperLayer (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : UpperHalfPlane)
    (hclean : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane =>
        Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r) τ = 0 := by
  -- `S(T-I)²` kills all four cusp coefficient functions: the limit of the `S(T-I)²`-defect of the
  -- cusp remainder at the clean point `τ` (via the cusp expansion of the kernel along the three
  -- shifted contours), then the identity theorem from the clean points to all of `ℍ`.
  have hGpt : ∀ (τ' : UpperHalfPlane) (i j : Fin 2),
      Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.Asymptotics.Gcusp ℓ d i j) τ' = 0 :=
    S2op_Gcusp_all_of_clean ℓ d hd (fun τ' i j hc =>
      S2op_Gcusp_of_tendsto ℓ d hd τ' (tendsto_S2op_sub_Aexp_zero ℓ d hd τ' hc) i j)
  have hG : ∀ i j : Fin 2,
      Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.Asymptotics.Gcusp ℓ d i j) = 0 :=
    fun i j => funext (fun τ' => hGpt τ' i j)
  -- the three `S`-shifted contours are clean
  have hclean3 := clean_smul_S τ hclean
  -- the three pieces of the layer
  have hlow : Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Asymptotics.layerLow ℓ d σ r) τ = 0 :=
    S2op_layerLow ℓ d hd r (fun σ hσ t ht _ => hclean3 σ hσ t ht)
  have htrunc : Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane =>
        Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r) τ = 0 :=
    S2op_layerTrunc ℓ d hd r hG hclean3
  have hhigh : Work.Asymptotics.S2op ((d : ℤ) / 2)
      (fun σ : UpperHalfPlane => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) σ r) = 0 :=
    S2op_highPart ℓ d hd r hG
  -- the layer is the sum of the three pieces
  have hfun : (fun σ : UpperHalfPlane =>
        Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r)
      = (fun σ : UpperHalfPlane => Work.Asymptotics.layerLow ℓ d σ r)
        + (fun σ : UpperHalfPlane =>
            Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d σ r)
        + (fun σ : UpperHalfPlane =>
            Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) σ r) := rfl
  rw [hfun, S2opPl_add, S2opPl_add]
  simp only [Pi.add_apply]
  rw [hlow, htrunc, congr_fun hhigh τ]
  simp

end Work.CKFinal
