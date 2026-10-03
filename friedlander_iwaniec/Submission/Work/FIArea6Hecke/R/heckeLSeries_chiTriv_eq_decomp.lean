import Mathlib
import Submission.Work.FIArea6Hecke.R.PrincipalCharAux
import Submission.Work.FIArea6Hecke.R.logDerivBoundAux
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.zfrAux
import Submission.Work.FIArea6Hecke.R.LSeries_chi4fun_eulerProduct
import Submission.Work.FIArea6Hecke.R.hasProd_badCorr
import Submission.Work.FIArea6Hecke.R.localFactor_eq_decomp

namespace Work.FIArea6Hecke.R

open scoped BigOperators

theorem heckeLSeries_chiTriv_eq_decomp {d : ℕ} (hd : 1 ≤ d)
    (hloc : ∀ (p : ℕ), p.Prime → ∀ s : ℂ, 1 < s.re →
      (∑' e : ℕ, Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.R.chiTriv d) 0 (p ^ e)
          * (((p : ℂ) ^ (-s)) ^ e))
        = (if p ∣ 4 * d then 1 else
            ((1 - (p : ℂ) ^ (-s)) * (1 - Work.FIArea6Hecke.R.chi4fun p * (p : ℂ) ^ (-s)))⁻¹)) :
    ∀ s : ℂ, 1 < s.re →
      Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.R.chiTriv d) 0 s
        = riemannZeta s * LSeries Work.FIArea6Hecke.R.chi4fun s
          * Work.FIArea6Hecke.R.badPoly d s := by
  intro s hs
  -- The principal strict character `chiTriv d` is `principalChar d`; it is `1` at `1`,
  -- multiplicative, and bounded by `1`.
  have hchi1 : Work.FIArea6Hecke.R.chiTriv d (1 : GaussianInt) = 1 :=
    Work.FIArea5.S16Hecke.principalChar_one d
  have hchi : ∀ z w : GaussianInt,
      Work.FIArea6Hecke.R.chiTriv d (z * w)
        = Work.FIArea6Hecke.R.chiTriv d z * Work.FIArea6Hecke.R.chiTriv d w :=
    fun z w => Work.FIArea5.S16Hecke.principalChar_mul d z w
  have hchi_bd : ∀ z : GaussianInt, ‖Work.FIArea6Hecke.R.chiTriv d z‖ ≤ 1 :=
    fun z => Work.FIArea5.S16Hecke.norm_principalChar_le_one d z
  -- Euler product of the Hecke `L`-series.
  have hep := Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
      (Work.FIArea6Hecke.R.chiTriv d) 0 hchi1 hchi hchi_bd hs
  -- Euler products of the three pieces `ζ`, `L(·, χ₄)`, and the bad-prime correction `G_d`.
  have HA : HasProd (fun p : Nat.Primes => (1 - (((p : ℕ)) : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
    riemannZeta_eulerProduct_hasProd hs
  have HB := LSeries_chi4fun_eulerProduct (s := s) hs
  have HG := hasProd_badCorr d s
  have HABG : HasProd (fun p : Nat.Primes =>
        (1 - (((p : ℕ)) : ℂ) ^ (-s))⁻¹
          * (1 - Work.FIArea6Hecke.R.chi4fun (p : ℕ) * (((p : ℕ)) : ℂ) ^ (-s))⁻¹ *
          (if (p : ℕ) ∈ (4 * d).primeFactors then
            (1 - (((p : ℕ)) : ℂ) ^ (-s))
              * (1 - Work.FIArea6Hecke.R.chi4fun (p : ℕ) * (((p : ℕ)) : ℂ) ^ (-s)) else 1))
      (riemannZeta s * LSeries Work.FIArea6Hecke.R.chi4fun s * Work.FIArea6Hecke.R.badPoly d s) :=
    (HA.mul HB).mul HG
  rw [← hep]
  trans (∏' p : Nat.Primes,
        (1 - (((p : ℕ)) : ℂ) ^ (-s))⁻¹
          * (1 - Work.FIArea6Hecke.R.chi4fun (p : ℕ) * (((p : ℕ)) : ℂ) ^ (-s))⁻¹ *
          (if (p : ℕ) ∈ (4 * d).primeFactors then
            (1 - (((p : ℕ)) : ℂ) ^ (-s))
              * (1 - Work.FIArea6Hecke.R.chi4fun (p : ℕ) * (((p : ℕ)) : ℂ) ^ (-s)) else 1))
  · apply tprod_congr
    intro p
    -- Match the local factor of the Hecke Euler product with the local factor used in `hloc`.
    have hconv : (∑' e : ℕ, Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.R.chiTriv d) 0
          ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
        = (∑' e : ℕ, Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.R.chiTriv d) 0
          ((p : ℕ) ^ e) * ((((p : ℕ) : ℂ) ^ (-s)) ^ e)) := by
      refine tsum_congr fun e => ?_
      have h1 : ((((p : ℕ) : ℂ) ^ (-s)) ^ e)
          = ((((p : ℕ) : ℂ) ^ ((e : ℂ) * s))⁻¹) := by
        rw [← Complex.cpow_nat_mul (((p : ℕ) : ℂ)) e (-s)]
        rw [show ((e : ℂ) * (-s)) = -((e : ℂ) * s) by ring, Complex.cpow_neg]
      rw [h1, div_eq_mul_inv]
    rw [hconv, hloc (p : ℕ) p.2 s hs]
    exact localFactor_eq_decomp hd p.2 hs
  · exact HABG.tprod_eq

end Work.FIArea6Hecke.R
