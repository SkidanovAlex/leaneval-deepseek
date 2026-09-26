import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24E2Prime_work

set_option maxRecDepth 100000

/-!
# The truncation deviations `Kappa - khatDef`, `Rest - rhatDef`, and the remaining helpers
-/

namespace Work.Asymptotics.KhatE1Core

open Work.Asymptotics.KhatE1

noncomputable section

/-- `atomProd` extended by the untruncated atoms `E4,E6,E2,psi2,psi4`. -/
def atomProdND (ℓ : Work.Kernels.LogLambdaData) (c : ℂ)
    (nq nL nT nZ npi npi2 ns nC nA nB nE nP2 nP4 nE4 nE6 nE2 nP2ps nP4ps : ℕ)
    (τ z : UpperHalfPlane) : ℂ :=
  atomProd ℓ c nq nL nT nZ npi npi2 ns nC nA nB nE nP2 nP4 τ z
    * (Work.Kernels.E4Fun τ) ^ nE4 * (Work.Kernels.E6Fun τ) ^ nE6 * (Work.Kernels.E2Fun τ) ^ nE2
    * (Work.Kernels.psi2 ℓ τ) ^ nP2ps * (Work.Kernels.psi4 ℓ τ) ^ nP4ps

theorem boundPsi2 (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun τ _ => Work.Kernels.psi2 ℓ τ) 0 :=
  Bound.congr ((boundP20q ℓ).add (Bound.devPsi2 ℓ))
    (fun τ z => by simp only [devPsi2, P20q] <;> ring)

theorem boundPsi4 (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun τ _ => Work.Kernels.psi4 ℓ τ) 0 :=
  Bound.congr ((boundP40q ℓ).add (Bound.devPsi4 ℓ))
    (fun τ z => by simp only [devPsi4, P40q] <;> ring)

theorem bounded_atomProdND (ℓ : Work.Kernels.LogLambdaData) (c : ℂ)
    (nq nL nT nZ npi npi2 ns nC nA nB nE nP2 nP4 nE4 nE6 nE2 nP2ps nP4ps : ℕ) :
    Bound (atomProdND ℓ c nq nL nT nZ npi npi2 ns nC nA nB nE nP2 nP4 nE4 nE6 nE2 nP2ps nP4ps) 0 := by
  have h := ((((((bounded_atomProd ℓ c nq nL nT nZ npi npi2 ns nC nA nB nE nP2 nP4).mul (Bound.E4Fun.pow nE4)).mul (Bound.E6Fun.pow nE6)).mul (Bound.E2Fun.pow nE2)).mul ((boundPsi2 ℓ).pow nP2ps)).mul ((boundPsi4 ℓ).pow nP4ps))
  refine Bound.congr (Bound.mono (Nat.zero_le _) h) ?_
  intro τ z
  simp only [atomProdND, atomProd] <;> ring

/-- `atomProd` extended by the deviations. -/
def atomProdD (ℓ : Work.Kernels.LogLambdaData) (c : ℂ)
    (nq nL nT nZ npi npi2 ns nC nA nB nE nP2 nP4 nE4 nE6 nE2 nP2ps nP4ps
     ndA ndB ndE ndP2 ndP4 ndD : ℕ) (τ z : UpperHalfPlane) : ℂ :=
  atomProdND ℓ c nq nL nT nZ npi npi2 ns nC nA nB nE nP2 nP4 nE4 nE6 nE2 nP2ps nP4ps τ z
    * (devA τ) ^ ndA * (devB τ) ^ ndB * (devE τ) ^ ndE
    * (devPsi2 ℓ τ) ^ ndP2 * (devPsi4 ℓ τ) ^ ndP4 * (devD τ) ^ ndD

theorem bounded_atomProdD (ℓ : Work.Kernels.LogLambdaData) (c : ℂ)
    (nq nL nT nZ npi npi2 ns nC nA nB nE nP2 nP4 nE4 nE6 nE2 nP2ps nP4ps
     ndA ndB ndE ndP2 ndP4 ndD : ℕ)
    (h : 0 < ndA + ndB + ndE + ndP2 + ndP4 + ndD) :
    Bound (atomProdD ℓ c nq nL nT nZ npi npi2 ns nC nA nB nE nP2 nP4 nE4 nE6 nE2 nP2ps nP4ps
      ndA ndB ndE ndP2 ndP4 ndD) 2 := by
  have hdev : Bound (fun τ z => (devA τ) ^ ndA * (devB τ) ^ ndB * (devE τ) ^ ndE
      * (devPsi2 ℓ τ) ^ ndP2 * (devPsi4 ℓ τ) ^ ndP4 * (devD τ) ^ ndD)
      (2 * ndA + 2 * ndB + 2 * ndE + 2 * ndP2 + 2 * ndP4 + 2 * ndD) :=
    ((((((Bound.devA.pow ndA).mul (Bound.devB.pow ndB)).mul (Bound.devE.pow ndE)).mul ((Bound.devPsi2 ℓ).pow ndP2)).mul ((Bound.devPsi4 ℓ).pow ndP4)).mul (Bound.devD.pow ndD))
  have h2 := (bounded_atomProdND ℓ c nq nL nT nZ npi npi2 ns nC nA nB nE nP2 nP4 nE4 nE6 nE2 nP2ps nP4ps).mul hdev
  refine Bound.congr (Bound.mono ?_ h2) ?_
  · omega
  · intro τ z
    simp only [atomProdD, atomProdND, atomProd] <;> ring

theorem boundDevA1 : Bound (fun τ _ => devA1Fun τ) 2 := by
  have h2 : Bound (fun τ _ => (Work.Kernels.E4Fun τ) ^ 2 + Work.Kernels.E4Fun τ * A0q (Work.Kernels.qParamFun τ)
      + (A0q (Work.Kernels.qParamFun τ)) ^ 2) 0 :=
    (((Bound.E4Fun.pow 2)).add ((Bound.E4Fun).mul boundA0q)).add (boundA0q.pow 2)
  have h := (Bound.devA).mul h2
  refine Bound.congr h ?_
  intro τ z
  simp only [devA1Fun, devA, A0q, A1q] <;> ring

theorem boundInvPiZsq : Bound (fun _ z => (((Real.pi : ℂ) * (z : ℂ)) ^ 2)⁻¹) 0 := by
  refine ⟨1, 0, 0, one_pos, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hz3 : (3 : ℝ) ≤ ‖(z : ℂ)‖ := three_le_norm_coe_z hF ht hzim
  rw [Real.rpow_zero, Real.rpow_zero, pow_zero, mul_one, mul_one, mul_one]
  rw [norm_inv, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h9 : (9 : ℝ) ≤ Real.pi * ‖(z : ℂ)‖ := by nlinarith [Real.pi_gt_three]
  have hpos : (0 : ℝ) < Real.pi * ‖(z : ℂ)‖ := by positivity
  have : ((Real.pi * ‖(z : ℂ)‖) ^ 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    nlinarith
  linarith


theorem boundPoly2 (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun τ z => poly2Fun ℓ τ z) 0 := by
  have hsum := (((((bounded_atomProd ℓ ((3162:ℂ)) 0 0 0 2 1 0 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((33408:ℂ)) 0 0 0 2 1 0 0 1 0 0 0 0 0)).add ((bounded_atomProd ℓ ((7536:ℂ)) 0 0 0 4 3 0 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((-3240:ℂ) * Complex.I) 0 0 1 2 2 0 0 0 0 0 0 0 0))).add (((bounded_atomProd ℓ ((12000:ℂ)) 0 0 1 3 3 0 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((2256:ℂ) * Complex.I) 0 0 1 4 4 0 0 0 0 0 0 0 0)).add ((bounded_atomProd ℓ ((-2860254:ℂ)) 1 0 0 2 1 0 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((-44373636:ℂ)) 1 0 0 2 1 0 0 1 0 0 0 0 0)))).add ((((bounded_atomProd ℓ ((-646704:ℂ) * Complex.I) 1 0 0 3 2 0 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((-11880000:ℂ)) 1 0 0 4 3 0 0 0 0 0 0 0 0)).add ((bounded_atomProd ℓ ((-786348:ℂ) * Complex.I) 1 0 1 2 2 0 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((-12948696:ℂ)) 1 0 1 3 3 0 0 0 0 0 0 0 0))).add (((bounded_atomProd ℓ ((-2573664:ℂ) * Complex.I) 1 0 1 4 4 0 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((-17531004960:ℂ)) 2 0 0 2 1 0 0 0 0 0 0 0 0)).add ((bounded_atomProd ℓ ((-44720994240:ℂ)) 2 0 0 2 1 0 0 1 0 0 0 0 0).add ((bounded_atomProd ℓ ((-24572160:ℂ) * Complex.I) 2 0 0 3 2 0 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((-8660044800:ℂ)) 2 0 0 4 3 0 0 0 0 0 0 0 0)))))).add (((((bounded_atomProd ℓ ((17037412992:ℂ) * Complex.I) 2 0 1 2 2 0 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((-20133838656:ℂ)) 2 0 1 3 3 0 0 0 0 0 0 0 0)).add ((bounded_atomProd ℓ ((-3016915200:ℂ) * Complex.I) 2 0 1 4 4 0 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((-5396004864000:ℂ)) 3 0 0 2 1 0 0 0 0 0 0 0 0))).add (((bounded_atomProd ℓ ((-6816006144000:ℂ)) 3 0 0 2 1 0 0 1 0 0 0 0 0).add (bounded_atomProd ℓ ((-976748544000:ℂ)) 3 0 0 4 3 0 0 0 0 0 0 0 0)).add ((bounded_atomProd ℓ ((5525392942080:ℂ) * Complex.I) 3 0 1 2 2 0 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((-3878020592640:ℂ)) 3 0 1 3 3 0 0 0 0 0 0 0 0)))).add ((((bounded_atomProd ℓ ((-451798732800:ℂ) * Complex.I) 3 0 1 4 4 0 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((-326149079040000:ℂ)) 4 0 0 2 1 0 0 0 0 0 0 0 0)).add ((bounded_atomProd ℓ ((-256077987840000:ℂ)) 4 0 0 2 1 0 0 1 0 0 0 0 0).add (bounded_atomProd ℓ ((-25161891840000:ℂ)) 4 0 0 4 3 0 0 0 0 0 0 0 0))).add (((bounded_atomProd ℓ ((336341237760000:ℂ) * Complex.I) 4 0 1 2 2 0 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((-159252480000000:ℂ)) 4 0 1 3 3 0 0 0 0 0 0 0 0)).add ((bounded_atomProd ℓ ((-13557694464000:ℂ) * Complex.I) 4 0 1 4 4 0 0 0 0 0 0 0 0).add ((bounded_atomProd ℓ ((1528823808000000:ℂ)) 5 0 1 3 3 0 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((228049551360000:ℂ) * Complex.I) 5 0 1 4 4 0 0 0 0 0 0 0 0))))))
  refine Bound.congr hsum ?_
  intro τ z
  simp only [poly2Fun, Poly2, atomProd, ShZ, S0z] <;> ring_nf

theorem boundQ2Delta2 (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun τ z => (Work.Kernels.qParamFun τ) ^ 2 * delta2Fun ℓ τ z) 2 := by
  have h := ((Bound.qParamFun_pow 2).mul (boundPoly2 ℓ)).mul boundInvPiZsq
  refine Bound.congr h ?_
  intro τ z
  simp only [delta2Fun, Delta2, poly2Fun, div_eq_mul_inv] <;> ring


theorem kappaDevBound (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun τ z => Kappa ℓ τ z - khatDef ℓ τ z) 2 := by
  have hsum := ((((bounded_atomProdD ℓ (((1/3):ℂ)) 0 0 0 0 0 1 0 0 0 0 0 0 0 0 1 0 1 0 1 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((1/3):ℂ)) 0 0 0 0 0 1 0 0 1 0 0 0 0 0 0 0 1 0 0 1 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((1/3):ℂ)) 0 0 0 0 0 1 0 0 1 1 0 0 0 0 0 0 0 0 0 0 0 1 0 0 (by decide)))).add (((bounded_atomProdD ℓ (((1/3):ℂ)) 0 0 0 0 0 1 0 0 1 0 0 0 0 0 0 0 0 1 1 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((1/6):ℂ)) 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 1 2 0 0 0 0 0 (by decide))).add ((bounded_atomProdD ℓ (((1/6):ℂ)) 0 0 0 0 0 1 0 0 2 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 (by decide)).add (bounded_atomProdD ℓ (((1/36):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 0 0 0 0 0 0 1 2 0 0 1 0 0 0 0 0 (by decide))))).add (((bounded_atomProdD ℓ (((1/36):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 1 0 0 0 0 0 0 2 0 0 0 1 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((1/18):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 1 1 1 0 0 0 0 0 0 0 0 0 1 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((1/36):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 1 1 0 0 0 0 0 0 0 0 0 0 2 0 0 0 (by decide)))).add (((bounded_atomProdD ℓ (((1/6):ℂ)) 0 0 0 2 1 0 0 0 0 0 0 0 0 0 1 1 0 0 1 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((1/6):ℂ)) 0 0 0 2 1 0 0 0 1 0 0 0 0 0 0 1 0 0 0 1 0 0 0 0 (by decide))).add ((bounded_atomProdD ℓ (((1/6):ℂ)) 0 0 0 2 1 0 0 0 1 1 0 0 0 0 0 0 0 0 0 0 1 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((-1/6):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 2 0 0 0 0 0 0 1 0 0 1 0 0 0 0 0 (by decide)))))).add ((((bounded_atomProdD ℓ (((-1/6):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 1 0 0 0 0 0 0 1 0 0 2 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((-1/18):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 0 0 0 0 0 0 0 1 0 0 3 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((-1/18):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 3 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 (by decide)))).add (((bounded_atomProdD ℓ (((-1/2):ℂ)) 0 0 0 2 1 0 1 0 2 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((-1/2):ℂ)) 0 0 0 2 1 0 1 0 1 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 (by decide))).add ((bounded_atomProdD ℓ (((-1/6):ℂ)) 0 0 0 2 1 0 1 0 0 0 0 0 0 0 0 0 0 0 3 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((1/18):ℂ) * Complex.I) 0 0 1 2 2 0 2 0 1 0 0 0 0 0 1 0 0 0 1 0 0 0 0 0 (by decide))))).add ((((bounded_atomProdD ℓ (((1/36):ℂ) * Complex.I) 0 0 1 2 2 0 2 0 0 0 0 0 0 0 1 0 0 0 2 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((1/36):ℂ) * Complex.I) 0 0 1 2 2 0 2 0 2 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 (by decide))).add ((bounded_atomProdD ℓ ((-3:ℂ)) 0 0 0 0 0 1 0 1 2 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ ((-3:ℂ)) 0 0 0 0 0 1 0 1 1 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 (by decide)))).add (((bounded_atomProdD ℓ ((-1:ℂ)) 0 0 0 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 3 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ ((-3:ℂ) * Complex.I) 0 0 0 1 0 0 0 0 2 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 (by decide))).add ((bounded_atomProdD ℓ ((-3:ℂ) * Complex.I) 0 0 0 1 0 0 0 0 1 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ ((-1:ℂ) * Complex.I) 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3 0 0 0 0 0 (by decide))))))
  refine Bound.congr hsum ?_
  intro τ z
  simp only [Work.Asymptotics.KhatE1.Kappa, khatDef, KappaHat, RestHat, atomProdD, atomProdND, atomProd, devA, devB, devE, devD, devPsi2, devPsi4, A0q, B0q, E20q, P20q, P40q, ShZ, S0z]
  ring

theorem restDevBound (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun τ z => Rest ℓ τ z - rhatDef ℓ τ z) 2 := by
  have hsum := ((((((bounded_atomProdD ℓ ((9558:ℂ)) 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (by decide)).add (bounded_atomProdD ℓ ((-142236:ℂ)) 0 0 0 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (by decide))).add ((bounded_atomProdD ℓ (((-4719/32):ℂ)) 0 0 0 0 0 1 0 0 0 0 0 0 0 0 1 0 1 0 1 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((-4719/32):ℂ)) 0 0 0 0 0 1 0 0 1 0 0 0 0 0 0 0 1 0 0 1 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((-4719/32):ℂ)) 0 0 0 0 0 1 0 0 1 1 0 0 0 0 0 0 0 0 0 0 0 1 0 0 (by decide))))).add (((bounded_atomProdD ℓ (((-6417/16):ℂ)) 0 0 0 0 0 1 0 0 1 0 0 0 0 0 0 0 0 1 1 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((-6417/32):ℂ)) 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 1 2 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((-6417/32):ℂ)) 0 0 0 0 0 1 0 0 2 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 (by decide)))).add ((bounded_atomProdD ℓ ((-36:ℂ)) 0 0 0 0 0 1 0 0 2 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ ((-36:ℂ)) 0 0 0 0 0 1 0 0 1 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ ((-12:ℂ)) 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 3 0 0 0 0 0 (by decide)))))).add ((((bounded_atomProdD ℓ ((4392:ℂ)) 0 0 0 0 0 1 0 1 2 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ ((4392:ℂ)) 0 0 0 0 0 1 0 1 1 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ ((1464:ℂ)) 0 0 0 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 3 0 0 0 0 0 (by decide)))).add ((bounded_atomProdD ℓ ((-142236:ℂ) * Complex.I) 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (by decide)).add ((bounded_atomProdD ℓ ((4392:ℂ) * Complex.I) 0 0 0 1 0 0 0 0 2 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ ((4392:ℂ) * Complex.I) 0 0 0 1 0 0 0 0 1 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 (by decide))))).add (((bounded_atomProdD ℓ ((1464:ℂ) * Complex.I) 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((71/48):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 0 0 0 0 0 3 0 0 0 0 0 0 1 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((71/16):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 2 0 1 0 0 0 0 0 0 0 1 0 0 0 0 0 (by decide)))).add ((bounded_atomProdD ℓ (((71/16):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 1 0 1 0 0 0 0 0 0 0 2 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((71/48):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 0 0 1 0 0 0 0 0 0 0 3 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((213/16):ℂ)) 0 0 0 2 1 0 0 0 2 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 (by decide))))))).add (((((bounded_atomProdD ℓ (((213/16):ℂ)) 0 0 0 2 1 0 0 0 1 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((71/16):ℂ)) 0 0 0 2 1 0 0 0 0 0 0 0 0 0 0 0 0 0 3 0 0 0 0 0 (by decide))).add ((bounded_atomProdD ℓ (((-71/48):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 1 0 0 0 0 0 1 0 0 0 1 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((-71/96):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 0 0 0 0 0 0 1 0 0 0 2 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((-71/96):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 2 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 (by decide))))).add (((bounded_atomProdD ℓ (((-1351/96):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 0 0 0 0 0 0 1 2 0 0 1 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((-1351/96):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 1 0 0 0 0 0 0 2 0 0 0 1 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((-1351/48):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 1 1 1 0 0 0 0 0 0 0 0 0 1 0 0 0 (by decide)))).add ((bounded_atomProdD ℓ (((-1351/96):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 1 1 0 0 0 0 0 0 0 0 0 0 2 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((-1351/16):ℂ)) 0 0 0 2 1 0 0 0 0 0 0 0 0 0 1 1 0 0 1 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((-1351/16):ℂ)) 0 0 0 2 1 0 0 0 1 0 0 0 0 0 0 1 0 0 0 1 0 0 0 0 (by decide)))))).add ((((bounded_atomProdD ℓ (((-1351/16):ℂ)) 0 0 0 2 1 0 0 0 1 1 0 0 0 0 0 0 0 0 0 0 1 0 0 0 (by decide)).add ((bounded_atomProdD ℓ ((-1989:ℂ) * Complex.I) 0 0 1 2 2 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 1 (by decide)).add (bounded_atomProdD ℓ ((-1989:ℂ) * Complex.I) 1 0 1 2 2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 (by decide)))).add ((bounded_atomProdD ℓ ((-5967:ℂ)) 0 0 0 2 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (by decide)).add ((bounded_atomProdD ℓ ((4:ℂ) * Complex.I) 0 0 1 2 2 0 0 0 2 0 0 0 0 0 0 1 0 0 1 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ ((4:ℂ) * Complex.I) 0 0 1 2 2 0 0 0 1 0 0 0 0 0 0 1 0 0 2 0 0 0 0 0 (by decide))))).add (((bounded_atomProdD ℓ (((4/3):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 0 0 0 0 0 0 0 1 0 0 3 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((4/3):ℂ) * Complex.I) 0 0 1 2 2 0 0 0 3 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 (by decide)).add (bounded_atomProdD ℓ ((12:ℂ)) 0 0 0 2 1 0 0 0 2 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 (by decide)))).add ((bounded_atomProdD ℓ ((12:ℂ)) 0 0 0 2 1 0 0 0 1 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ ((4:ℂ)) 0 0 0 2 1 0 0 0 0 0 0 0 0 0 0 0 0 0 3 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((1/4):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 0 0 0 0 0 3 0 0 0 0 0 0 1 0 0 0 (by decide)))))))).add ((((((bounded_atomProdD ℓ (((3/4):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 2 0 1 0 0 0 0 0 0 0 1 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((3/4):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 1 0 1 0 0 0 0 0 0 0 2 0 0 0 0 0 (by decide))).add ((bounded_atomProdD ℓ (((1/4):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 0 0 1 0 0 0 0 0 0 0 3 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((9/4):ℂ)) 0 0 0 2 1 0 1 0 2 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((9/4):ℂ)) 0 0 0 2 1 0 1 0 1 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 (by decide))))).add (((bounded_atomProdD ℓ (((3/4):ℂ)) 0 0 0 2 1 0 1 0 0 0 0 0 0 0 0 0 0 0 3 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((-35/12):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 1 0 0 0 0 0 1 0 0 0 1 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((-35/24):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 0 0 0 0 0 0 1 0 0 0 2 0 0 0 0 0 (by decide)))).add ((bounded_atomProdD ℓ (((-35/24):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 2 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((-1/8):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 0 0 0 0 0 0 1 2 0 0 1 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((-1/8):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 1 0 0 0 0 0 0 2 0 0 0 1 0 0 0 0 (by decide)))))).add ((((bounded_atomProdD ℓ (((-1/4):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 1 1 1 0 0 0 0 0 0 0 0 0 1 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((-1/8):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 1 1 0 0 0 0 0 0 0 0 0 0 2 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((-3/4):ℂ)) 0 0 0 2 1 0 1 0 0 0 0 0 0 0 1 1 0 0 1 0 0 0 0 0 (by decide)))).add ((bounded_atomProdD ℓ (((-3/4):ℂ)) 0 0 0 2 1 0 1 0 1 0 0 0 0 0 0 1 0 0 0 1 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((-3/4):ℂ)) 0 0 0 2 1 0 1 0 1 1 0 0 0 0 0 0 0 0 0 0 1 0 0 0 (by decide)).add (bounded_atomProdD ℓ ((-8154:ℂ) * Complex.I) 0 0 1 2 2 0 1 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 1 (by decide))))).add (((bounded_atomProdD ℓ ((-8154:ℂ) * Complex.I) 1 0 1 2 2 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 (by decide)).add ((bounded_atomProdD ℓ ((-24462:ℂ)) 0 0 0 2 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (by decide)).add (bounded_atomProdD ℓ ((244:ℂ) * Complex.I) 0 0 1 2 2 0 1 0 2 0 0 0 0 0 0 1 0 0 1 0 0 0 0 0 (by decide)))).add ((bounded_atomProdD ℓ ((244:ℂ) * Complex.I) 0 0 1 2 2 0 1 0 1 0 0 0 0 0 0 1 0 0 2 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((244/3):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 0 0 0 0 0 0 0 1 0 0 3 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((244/3):ℂ) * Complex.I) 0 0 1 2 2 0 1 0 3 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 (by decide))))))).add (((((bounded_atomProdD ℓ ((732:ℂ)) 0 0 0 2 1 0 1 0 2 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ ((732:ℂ)) 0 0 0 2 1 0 1 0 1 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 (by decide))).add ((bounded_atomProdD ℓ ((244:ℂ)) 0 0 0 2 1 0 1 0 0 0 0 0 0 0 0 0 0 0 3 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((-1/16):ℂ) * Complex.I) 0 0 1 2 2 0 2 0 0 0 0 0 0 3 0 0 0 0 0 0 1 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((-3/16):ℂ) * Complex.I) 0 0 1 2 2 0 2 0 2 0 1 0 0 0 0 0 0 0 1 0 0 0 0 0 (by decide))))).add (((bounded_atomProdD ℓ (((-3/16):ℂ) * Complex.I) 0 0 1 2 2 0 2 0 1 0 1 0 0 0 0 0 0 0 2 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((-1/16):ℂ) * Complex.I) 0 0 1 2 2 0 2 0 0 0 1 0 0 0 0 0 0 0 3 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((-9/16):ℂ)) 0 0 0 2 1 0 2 0 2 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 (by decide)))).add ((bounded_atomProdD ℓ (((-9/16):ℂ)) 0 0 0 2 1 0 2 0 1 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((-3/16):ℂ)) 0 0 0 2 1 0 2 0 0 0 0 0 0 0 0 0 0 0 3 0 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((-639/16):ℂ) * Complex.I) 0 0 1 2 2 0 2 0 1 0 0 0 0 0 1 0 0 0 1 0 0 0 0 0 (by decide)))))).add ((((bounded_atomProdD ℓ (((-639/32):ℂ) * Complex.I) 0 0 1 2 2 0 2 0 0 0 0 0 0 0 1 0 0 0 2 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((-639/32):ℂ) * Complex.I) 0 0 1 2 2 0 2 0 2 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((1/32):ℂ) * Complex.I) 0 0 1 2 2 0 2 0 0 0 0 0 0 0 1 2 0 0 1 0 0 0 0 0 (by decide)))).add ((bounded_atomProdD ℓ (((1/32):ℂ) * Complex.I) 0 0 1 2 2 0 2 0 1 0 0 0 0 0 0 2 0 0 0 1 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((1/16):ℂ) * Complex.I) 0 0 1 2 2 0 2 0 1 1 1 0 0 0 0 0 0 0 0 0 1 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((1/32):ℂ) * Complex.I) 0 0 1 2 2 0 2 0 1 1 0 0 0 0 0 0 0 0 0 0 2 0 0 0 (by decide))))).add (((bounded_atomProdD ℓ (((3/16):ℂ)) 0 0 0 2 1 0 2 0 0 0 0 0 0 0 1 1 0 0 1 0 0 0 0 0 (by decide)).add ((bounded_atomProdD ℓ (((3/16):ℂ)) 0 0 0 2 1 0 2 0 1 0 0 0 0 0 0 1 0 0 0 1 0 0 0 0 (by decide)).add (bounded_atomProdD ℓ (((3/16):ℂ)) 0 0 0 2 1 0 2 0 1 1 0 0 0 0 0 0 0 0 0 0 1 0 0 0 (by decide)))).add ((bounded_atomProdD ℓ ((63:ℂ) * Complex.I) 0 0 1 2 2 0 2 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 1 (by decide)).add ((bounded_atomProdD ℓ ((63:ℂ) * Complex.I) 1 0 1 2 2 0 2 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 (by decide)).add (bounded_atomProdD ℓ ((189:ℂ)) 0 0 0 2 1 0 2 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 (by decide))))))))
  refine Bound.congr hsum ?_
  intro τ z
  simp only [Work.Asymptotics.KhatE1.Rest, rhatDef, KappaHat, RestHat, atomProdD, atomProdND, atomProd, devA, devB, devE, devD, devPsi2, devPsi4, A0q, B0q, E20q, P20q, P40q, ShZ, S0z]
  ring

end

end Work.Asymptotics.KhatE1Core
