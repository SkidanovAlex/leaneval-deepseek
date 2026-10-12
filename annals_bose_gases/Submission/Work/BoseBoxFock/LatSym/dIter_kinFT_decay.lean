import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseBoxFock.kinFT_iteratedFDeriv_decay
import Submission.Work.BoseBoxFock.lap3_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Rapid decay of the iterated *directional* derivatives of the one-body kinetic Fourier transform

`Submission.BoseGases.kinFT β p = ∫_y e^{−i⟪p,y⟫}β(y)dy` is the `p`-convention Fourier transform
of `β`; for `β` smooth with compact support it is (the restriction of) an entire function, so that
every iterated derivative decays faster than any power of `‖p‖`
(`Work.BoseBoxFock.kinFT_iteratedFDeriv_decay`, which bounds the *operator norm*
`‖iteratedFDeriv ℝ k (kinFT β) p‖`).

The present module packages this in the form the lattice chapter consumes: the decay of the
iterated *directional* derivatives `Work.BoseBoxFock.dIter (kinFT β) L p` along an arbitrary list
`L` of directions, with the fixed weight `(1 + ‖p‖)^{-7}`:

`Work.BoseBoxFock.LatSym.dIter_kinFT_decay`.

The passage from the operator norm to a directional derivative is an evaluation bound: by
`Work.BoseBoxFock.dIter_eq_iteratedFDeriv`, `dIter f L p` is the multilinear map
`iteratedFDeriv ℝ L.length f p` evaluated on the tuple of directions `L.get`, so
`‖dIter f L p‖ ≤ (∏ i, ‖L.get i‖) · ‖iteratedFDeriv ℝ L.length f p‖`
(`norm_dIter_le_prod`). The product of the norms of the directions is a constant for the fixed
list `L`, and the decay of the operator norm with the exponent `7` is
`kinFT_iteratedFDeriv_decay` at `k = L.length`, `N = 7`.

The smoothness of `kinFT β` needed by `dIter_eq_iteratedFDeriv` is obtained from the Schwartz
picture: `β = ⇑F` for the Schwartz map `F = hβc.toSchwartzMap hβ`, the Fourier transform `𝓕 F` is
again Schwartz (hence smooth), and `kinFT β = (𝓕 F) ∘ ((2π)⁻¹ • ·)`.
-/

noncomputable section

open scoped ContDiff FourierTransform SchwartzMap

namespace Work.BoseBoxFock.LatSym

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Evaluation bound for the iterated directional derivative.** For smooth `f`, `dIter f L p`
is the `L.length`-th iterated derivative of `f` at `p` evaluated on the tuple `L.get`
(`Work.BoseBoxFock.dIter_eq_iteratedFDeriv`), hence bounded by the operator norm of that
multilinear map times the product of the norms of the directions. -/
lemma norm_dIter_le_prod {f : E3 → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (L : List E3) (p : E3) :
    ‖Work.BoseBoxFock.dIter f L p‖
      ≤ (∏ i : Fin L.length, ‖L.get i‖) * ‖iteratedFDeriv ℝ L.length f p‖ := by
  rw [Work.BoseBoxFock.dIter_eq_iteratedFDeriv f hf L p]
  calc ‖iteratedFDeriv ℝ L.length f p (fun i => L.get i)‖
      ≤ ‖iteratedFDeriv ℝ L.length f p‖ * ∏ i : Fin L.length, ‖L.get i‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = (∏ i : Fin L.length, ‖L.get i‖) * ‖iteratedFDeriv ℝ L.length f p‖ := mul_comm _ _

/-- The `p`-convention Fourier transform of a smooth compactly supported function is smooth:
`β = ⇑F` for a Schwartz map `F`, `𝓕 F` is again Schwartz, and `kinFT β = (𝓕 F) ∘ ((2π)⁻¹ • ·)`
(`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`). -/
lemma contDiff_kinFT_of_contDiff {β : E3 → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 => Submission.BoseGases.kinFT β p) := by
  set F : 𝓢(E3, ℂ) := hβc.toSchwartzMap hβ with hF
  have hFu : ⇑F = β := rfl
  have hfun : (fun p : E3 => Submission.BoseGases.kinFT β p)
      = fun p : E3 => (𝓕 F) (((2 * Real.pi)⁻¹ : ℝ) • p) := by
    funext p
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, ← hFu]
    exact congrFun (SchwartzMap.fourier_coe F).symm _
  rw [hfun]
  exact (SchwartzMap.smooth (𝓕 F) (⊤ : ℕ∞)).comp (contDiff_const_smul ((2 * Real.pi)⁻¹ : ℝ))

/-- **Rapid decay of the iterated directional derivatives of `kinFT β`.** For `β` smooth with
compact support and any list `L` of directions, `dIter (kinFT β) L ·` decays like
`(1 + ‖p‖)^{-7}`, with a constant depending on `β` and on the norms of the directions of `L`. -/
theorem dIter_kinFT_decay {β : EuclideanSpace ℝ (Fin 3) → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (L : List (EuclideanSpace ℝ (Fin 3))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseBoxFock.dIter (fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.kinFT β p) L p‖
        ≤ C * (1 + ‖p‖) ^ (-7 : ℝ) := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 => Submission.BoseGases.kinFT β p) :=
    contDiff_kinFT_of_contDiff hβ hβc
  obtain ⟨C', hC'0, hC'⟩ := Work.BoseBoxFock.kinFT_iteratedFDeriv_decay hβ hβc L.length 7
  refine ⟨max ((∏ i : Fin L.length, ‖L.get i‖) * C') 0, le_max_right _ _, fun p => ?_⟩
  have hP : 0 ≤ ∏ i : Fin L.length, ‖L.get i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hrp : (0 : ℝ) ≤ (1 + ‖p‖) ^ (-7 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hpow : (1 + ‖p‖) ^ (-7 : ℝ) = ((1 + ‖p‖) ^ 7 : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast (1 + ‖p‖) 7,
      ← Real.rpow_neg (x := 1 + ‖p‖) (by positivity) ((7 : ℕ) : ℝ)]
    norm_num
  have h1 : ‖Work.BoseBoxFock.dIter (fun p : E3 => Submission.BoseGases.kinFT β p) L p‖
      ≤ (∏ i : Fin L.length, ‖L.get i‖)
          * ‖iteratedFDeriv ℝ L.length (fun p : E3 => Submission.BoseGases.kinFT β p) p‖ :=
    norm_dIter_le_prod hcd L p
  have h2 : (∏ i : Fin L.length, ‖L.get i‖)
        * ‖iteratedFDeriv ℝ L.length (fun p : E3 => Submission.BoseGases.kinFT β p) p‖
      ≤ (∏ i : Fin L.length, ‖L.get i‖) * (C' / (1 + ‖p‖) ^ 7) :=
    mul_le_mul_of_nonneg_left (hC' p) hP
  have h3 : (∏ i : Fin L.length, ‖L.get i‖) * (C' / (1 + ‖p‖) ^ 7)
      = ((∏ i : Fin L.length, ‖L.get i‖) * C') * (1 + ‖p‖) ^ (-7 : ℝ) := by
    rw [hpow, div_eq_mul_inv]
    ring
  calc ‖Work.BoseBoxFock.dIter (fun p : E3 => Submission.BoseGases.kinFT β p) L p‖
      ≤ (∏ i : Fin L.length, ‖L.get i‖)
          * ‖iteratedFDeriv ℝ L.length (fun p : E3 => Submission.BoseGases.kinFT β p) p‖ := h1
    _ ≤ (∏ i : Fin L.length, ‖L.get i‖) * (C' / (1 + ‖p‖) ^ 7) := h2
    _ = ((∏ i : Fin L.length, ‖L.get i‖) * C') * (1 + ‖p‖) ^ (-7 : ℝ) := h3
    _ ≤ max ((∏ i : Fin L.length, ‖L.get i‖) * C') 0 * (1 + ‖p‖) ^ (-7 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hrp

end Work.BoseBoxFock.LatSym
