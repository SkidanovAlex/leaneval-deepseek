import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.Lat.detL_inf_latOrth
import Submission.Work.HP.GM.gcdMinors2_veronese_natAbs
import Submission.Work.HP.EEupper.gcdMinors_veronese
import Submission.Work.HP.Sig2.nu_indep

namespace Work.HP

/-! ## Independence helpers

`LinearIndependent ℤ ![x, y]` forces `x ≠ y` and `x ≠ -y` (the two obvious non-trivial
relations with coefficients `(1,-1)` and `(1,1)`). -/

private lemma ne_of_linInd' {ι : Type*} [Fintype ι] (x y : ι → ℤ)
    (h : LinearIndependent ℤ ![x, y]) : x ≠ y := by
  intro hxy
  have h2 := (Fintype.linearIndependent_iff.mp h) ![1, -1]
  have hsum : (∑ i, (![1, -1] : Fin 2 → ℤ) i • (![x, y] i)) = 0 := by
    simp [Fin.sum_univ_two, hxy]
  have := h2 hsum 0
  simp at this

private lemma ne_neg_of_linInd' {ι : Type*} [Fintype ι] (x y : ι → ℤ)
    (h : LinearIndependent ℤ ![x, y]) : x ≠ -y := by
  intro hxy
  have h2 := (Fintype.linearIndependent_iff.mp h) ![1, 1]
  have hsum : (∑ i, (![1, 1] : Fin 2 → ℤ) i • (![x, y] i)) = 0 := by
    simp [Fin.sum_univ_two, hxy]
  have := h2 hsum 0
  simp at this

/-- `Δ(x,y) · 𝓖(x,y) = ‖ν(x)‖‖ν(y)‖ / det Γ_{x,y}`.

Both sides equal `‖ν(x)‖‖ν(y)‖·𝓖(x,y)/𝔚(ν(x),ν(y))`, using
* `det Γ_{x,y} = 𝔚(ν(x),ν(y)) / 𝓖(x,y)` (`det_gam_gen` for the Veronese pair, plus Lemma G
  `EEupper.gcdMinors_veronese` to replace `𝓖(νx,νy)` by `𝓖(x,y)`). -/
theorem DeltaXY_gcd_detL (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : LinearIndependent ℤ ![x, y]) :
    DeltaXY d n x y * (gcdMinors2 x y : ℝ)
      = eNorm (veronese d n x) * eNorm (veronese d n y) / detL (Gam d n x y) := by
  have hd1 : 1 ≤ d := by omega
  -- Lemma G: the gcd of the minors is unchanged by the Veronese map
  have hgcast : (gcdMinors2 (veronese d n x) (veronese d n y) : ℝ) = (gcdMinors2 x y : ℝ) := by
    rw [EEupper.gcdMinors_veronese d n hd1 x y hx hy]
  -- independence of the Veronese images
  have hLIν : LinearIndependent ℤ ![veronese d n x, veronese d n y] :=
    Sig2.nu_indep d n hd x y hx hy (ne_of_linInd' x y hxy) (ne_neg_of_linInd' x y hxy)
  -- the determinant of `Γ_{x,y}` in terms of the wedge norm and the gcd of the minors
  have hdet : detL (Gam d n x y)
      = wedgeNorm (veronese d n x) (veronese d n y) / (gcdMinors2 x y : ℝ) := by
    rw [show Gam d n x y = latOrth (veronese d n x) ⊓ latOrth (veronese d n y) from rfl,
      (det_gam_gen (veronese d n x) (veronese d n y) hLIν).1, hgcast]
  rw [DeltaXY, hdet, div_div_eq_mul_div]
  ring

end Work.HP
