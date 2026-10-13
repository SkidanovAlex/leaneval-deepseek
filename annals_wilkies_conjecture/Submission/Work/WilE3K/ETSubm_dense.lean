import Mathlib
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.ContAux
import Submission.Work.WilE9.EaD.eaEval_contDiff

namespace Work.WilE3K

set_option autoImplicit false

namespace ETData

variable {N rt n re : ℕ}

/-- Every coordinate of the system map of a lifted system is `C²`: an `arctan` row is
`Real.arctan ∘ proj - affine` and an exp-affine row is the EA evaluation of an EA polynomial along
the (analytic) chain of `E`. -/
theorem contDiff_map_apply (E : ETData N rt n re) (r : Fin (N + 1)) :
    ContDiff ℝ 2 (fun z : Fin (N + 1) → ℝ => E.map z r) := by
  by_cases hr : (r : ℕ) < rt
  · have hfun : (fun z : Fin (N + 1) → ℝ => E.map z r)
        = fun z => E.tanFun (E.tanIndex r hr) z := by
      funext z
      simp only [ETData.map]
      rw [dif_pos hr]
    rw [hfun]
    have htan : ContDiff ℝ 2 (fun z : Fin (N + 1) → ℝ =>
        Real.arctan (z (E.tanCoord (E.tanIndex r hr)))) :=
      (Real.contDiff_arctan (n := 2)).comp
        ((ContinuousLinearMap.proj (E.tanCoord (E.tanIndex r hr)) :
          (Fin (N + 1) → ℝ) →L[ℝ] ℝ).contDiff)
    have hlin : ContDiff ℝ 2 (fun z : Fin (N + 1) → ℝ => E.lin (E.tanIndex r hr) z) := by
      have hsum : ContDiff ℝ 2 (fun z : Fin (N + 1) → ℝ =>
          ∑ i : Fin n, E.lam (E.tanIndex r hr) i * z (E.freeCoord i)) := by
        refine ContDiff.sum (s := Finset.univ)
          (f := fun (i : Fin n) (z : Fin (N + 1) → ℝ) =>
            E.lam (E.tanIndex r hr) i * z (E.freeCoord i)) ?_
        intro i _
        exact ContDiff.mul (f := fun _ : Fin (N + 1) → ℝ => E.lam (E.tanIndex r hr) i)
          (g := fun z : Fin (N + 1) → ℝ => z (E.freeCoord i))
          contDiff_const
          ((ContinuousLinearMap.proj (E.freeCoord i) :
            (Fin (N + 1) → ℝ) →L[ℝ] ℝ).contDiff)
      have hconst : ContDiff ℝ 2 (fun _ : Fin (N + 1) → ℝ => E.mu (E.tanIndex r hr)) :=
        contDiff_const
      simpa only [ETData.lin] using hsum.add hconst
    simpa only [ETData.tanFun] using htan.sub hlin
  · have hfun : (fun z : Fin (N + 1) → ℝ => E.map z r)
        = fun z => E.evP (E.freeIndex r (not_lt.mp hr)) z := by
      funext z
      simp only [ETData.map]
      rw [dif_neg hr]
    rw [hfun]
    have key : ContDiff ℝ 2 (fun z : Fin (N + 1) → ℝ =>
        E.evalPoly (E.G (E.freeIndex r (not_lt.mp hr))) z) := by
      have h := Work.WilE9.EaD.eaEval_contDiff E.toChain (E.G (E.freeIndex r (not_lt.mp hr)))
      have h2 : (fun z : Fin (N + 1) → ℝ =>
            WilkiesDesign.E.eaEval E.toChain (E.G (E.freeIndex r (not_lt.mp hr))) z)
          = (fun z : Fin (N + 1) → ℝ =>
            E.evalPoly (E.G (E.freeIndex r (not_lt.mp hr))) z) := by
        funext z
        exact (E.evalPoly_eq_eaEval _ z).symm
      rw [h2] at h
      exact h.of_le le_top
    simpa only [ETData.evP] using key

/-- The remaining system `E.psiMap` of a lifted system is `C²`: it is a selection of coordinates of
the `C²` map `E.map`. -/
theorem contDiff_psiMap (E : ETData N (rt + 1) n re) : ContDiff ℝ 2 E.psiMap :=
  contDiff_pi.mpr fun i => contDiff_map_apply E (Fin.succAbove E.lastRow i)

end ETData

/-- Regular values of the remaining system are dense: this is the Sard hypothesis `hsard` of `ET_good_exists` instantiated at `G = E.psiMap` (an arbitrary `C²` map `ℝ^{N+1} → ℝ^N`), whose conclusion is exactly `E.ETSubmersion`. The only work is `ContDiff ℝ 2 E.psiMap`, from `Work.WilE3K.ContAux` (`E.evalPoly_eq_eaEval`) with `Work.WilE9.EaD.eaEval_contDiff` (the `tan` rows `Real.arctan ∘ proj - affine` are smooth). -/
theorem ETSubm_dense {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
    (hsard : ∀ (m : ℕ) (G : (Fin (m + 1) → ℝ) → (Fin m → ℝ)), ContDiff ℝ 2 G →
      ∀ (y₀ : Fin m → ℝ) (ε : ℝ), 0 < ε → ∃ y : Fin m → ℝ, dist y y₀ < ε ∧
        ∀ z, G z = y → LinearIndependent ℝ (fun a => fderiv ℝ (fun w => G w a) z)) :
    ∀ (y₀ : Fin N → ℝ) (ε : ℝ), 0 < ε → ∃ y : Fin N → ℝ, dist y y₀ < ε ∧ E.ETSubmersion y := by
  intro y₀ ε hε
  obtain ⟨y, hy, hreg⟩ := hsard N E.psiMap
    (ETData.contDiff_psiMap (N := N) (rt := rt) (n := n) (re := re) E) y₀ ε hε
  refine ⟨y, hy, ?_⟩
  intro z hz
  exact hreg z hz

end Work.WilE3K
