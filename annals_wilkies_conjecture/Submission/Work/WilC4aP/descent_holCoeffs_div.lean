import Mathlib
import Submission.Work.WilC4aP.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators

namespace Work.WilC4aP

open Polynomial

/-- The subring of `ℂ → ℂ` consisting of the functions analytic at `0`. -/
def holSub : Subring (ℂ → ℂ) where
  carrier := {f | AnalyticAt ℂ f 0}
  zero_mem' := by
    rw [show (0 : ℂ → ℂ) = (fun _ => (0 : ℂ)) from by funext x; rfl]
    exact analyticAt_const
  add_mem' := by
    intro a b ha hb
    exact ha.add hb
  neg_mem' := by
    intro a ha
    exact ha.neg
  one_mem' := by
    rw [show (1 : ℂ → ℂ) = (fun _ => (1 : ℂ)) from by funext x; rfl]
    exact analyticAt_const
  mul_mem' := by
    intro a b ha hb
    exact ha.mul hb

/-- Package a polynomial all of whose coefficients are analytic at `0` into `holSub[X]`. -/
def liftPoly (P : Polynomial (ℂ → ℂ)) (hP : HolCoeffs P 0) : Polynomial holSub :=
  ∑ i ∈ P.support, C (⟨P.coeff i, hP i⟩ : holSub) * X ^ i

/-- Mapping `liftPoly P` back down gives `P`. -/
lemma map_liftPoly (P : Polynomial (ℂ → ℂ)) (hP : HolCoeffs P 0) :
    (liftPoly P hP).map holSub.subtype = P := by
  unfold liftPoly
  rw [Polynomial.map_sum]
  trans ∑ i ∈ P.support, C (P.coeff i) * X ^ i
  · apply Finset.sum_congr rfl
    intro i _
    simp [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      Subring.subtype_apply]
  · conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq P]
    rw [Polynomial.sum_def]

/-- If `P = G * H` with `G` monic and the coefficients of `P` and of `G` holomorphic at `0`,
then the coefficients of `H` are holomorphic at `0`.

PROOF HINT: `H = P /ₘ G` (`Polynomial.div_modByMonic_unique`, since `P = G * H + 0` and
`degree 0 < degree G` for nonconstant `G`; if `G` is constant, divide directly).  For the
analyticity of the coefficients of `H` use the *subring* `S := {f : ℂ → ℂ // AnalyticAt ℂ f 0}`
of `(ℂ → ℂ)`: package the analytic coefficients of `P` and `G` into `P'`, `G' ∈ S[X]` (via
`Polynomial.sum_C_mul_X_pow_eq` and `Polynomial.C ⟨P.coeff i, hP i⟩ * X ^ i`), so that
`Polynomial.map S.subtype P' = P` and `Polynomial.map S.subtype G' = G` with `G'` monic;
`Polynomial.map_divByMonic` then gives `Polynomial.map S.subtype (P' /ₘ G') = P /ₘ G = H`,
so every `H.coeff i` is the image of an element of `S`, hence analytic at `0`.
(Equivalently: run the downward coefficient recurrence
`H_m = P_{m+d} − Σ_{i<d} G_i * H_{m+d−i}`.) -/
lemma descent_holCoeffs_div {P G H : Polynomial (ℂ → ℂ)} (hG : G.Monic) (hPeq : P = G * H)
    (hGhol : Work.WilC4aP.HolCoeffs G 0) (hP : Work.WilC4aP.HolCoeffs P 0) :
    Work.WilC4aP.HolCoeffs H 0 := by
  have hsubinj : Function.Injective holSub.subtype := holSub.subtype_injective
  have hPmap : (liftPoly P hP).map holSub.subtype = P := map_liftPoly P hP
  have hGmap : (liftPoly G hGhol).map holSub.subtype = G := map_liftPoly G hGhol
  have hG'monic : (liftPoly G hGhol).Monic := by
    have h := Polynomial.leadingCoeff_map_of_injective (f := holSub.subtype) hsubinj
      (liftPoly G hGhol)
    rw [hGmap] at h
    have h2 : holSub.subtype (liftPoly G hGhol).leadingCoeff = holSub.subtype (1 : holSub) := by
      rw [map_one, ← h, hG.leadingCoeff]
    exact hsubinj h2
  have hdiv : Polynomial.map holSub.subtype ((liftPoly P hP) /ₘ (liftPoly G hGhol)) = P /ₘ G := by
    rw [Polynomial.map_divByMonic holSub.subtype hG'monic, hPmap, hGmap]
  have hPG : P /ₘ G = H := by
    rw [hPeq, Polynomial.mul_divByMonic_cancel_left H hG]
  have hfinal : Polynomial.map holSub.subtype ((liftPoly P hP) /ₘ (liftPoly G hGhol)) = H := by
    rw [hdiv, hPG]
  intro i
  rw [← hfinal, Polynomial.coeff_map]
  exact (Polynomial.coeff ((liftPoly P hP) /ₘ (liftPoly G hGhol)) i).2

end Work.WilC4aP
