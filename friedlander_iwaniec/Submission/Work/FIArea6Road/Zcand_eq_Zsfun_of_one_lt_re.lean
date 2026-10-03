import Mathlib
import Submission.Work.FIArea6Road.ZcontExistsBoundUniform
import Submission.Work.FIArea6Road.ZcontAux
import Submission.Work.FIArea6Road.ZprodRegroup

namespace Work.FIArea6Road

theorem Zcand_eq_Zsfun_of_one_lt_re (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (d : ℕ) (Lam : ℂ → ℂ) (hd : 1 ≤ d) (hchi1 : chi 1 = 1)
    (hchimul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hchibd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hLam : AnalyticOn ℂ Lam Set.univ)
    (hag : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d m s * Work.FIArea5.S16Hecke.heckeLSeries chi m s)
    {s : ℂ} (hs : 1 < s.re) :
    Work.FIArea6.TauPieces.Zcand Pa chi m d Lam s = Work.FIArea6.TauPieces.Zsfun Pa chi m s := by
  -- On `re s > 1` the archimedean quotient `Lam/heckeArch` is the Hecke `L`-series `L(s,ψ)`.
  have hLval : Lam s / Work.FITop4.Bridge.heckeArch d m s
      = Work.FIArea5.S16Hecke.heckeLSeries chi m s :=
    zcontLval_eq hd chi m hchi1 hchimul hchibd hLam hag hs
  -- `Φ = M·L`.
  have hPhi := PhifacIdent chi m hchi1 hchimul hchibd hs
  -- `L(s,ψ)·L(s,ψ)⁻¹ = 1`.
  have hLmul := zcontLSeries_mul_inv (m := m) hchi1 hchimul hchibd hs
  -- `Z(s) = M(s)·P(s)·Q(s)`.
  have hRegroup := ZprodRegroup Pa chi m hchi1 hchimul hchibd hs
  rw [Work.FIArea6.TauPieces.Zcand_apply, hLval, hPhi]
  have hstep : (Work.FIArea6.TauPieces.Mfac chi m s
        * Work.FIArea5.S16Hecke.heckeLSeries chi m s)
        * (Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹
      = Work.FIArea6.TauPieces.Mfac chi m s := by
    rw [mul_assoc, hLmul, mul_one]
  rw [hstep, ← hRegroup]

end Work.FIArea6Road
