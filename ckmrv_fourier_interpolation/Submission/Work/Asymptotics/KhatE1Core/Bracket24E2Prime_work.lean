import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24E2Prime_aux

namespace Work.Asymptotics.KhatE1Core

open Work.Asymptotics.KhatE1

noncomputable section

/-- A generic monomial in the bounded atoms. -/
def atomProd (ℓ : Work.Kernels.LogLambdaData) (c : ℂ)
    (nq nL nT nZ npi npi' ns nC nA nB nE nP2 nP4 : ℕ) (τ z : UpperHalfPlane) : ℂ :=
  c * (Work.Kernels.qParamFun τ) ^ nq * (cuspLin ℓ τ) ^ nL * ((τ : ℂ)) ^ nT
    * ((z : ℂ)) ^ nZ * ((Real.pi : ℂ)) ^ npi * (((Real.pi : ℂ))⁻¹) ^ npi'
    * (S0z z) ^ ns * (Work.Asymptotics.Compact.cuspC ℓ) ^ nC
    * (A0q (Work.Kernels.qParamFun τ)) ^ nA * (B0q (Work.Kernels.qParamFun τ)) ^ nB
    * (E20q (Work.Kernels.qParamFun τ)) ^ nE
    * (P20q (Work.Kernels.qParamFun τ) (cuspLin ℓ τ)) ^ nP2
    * (P40q (Work.Kernels.qParamFun τ) (cuspLin ℓ τ)) ^ nP4

theorem boundA0q : Bound (fun τ _ => A0q (Work.Kernels.qParamFun τ)) 0 := by
  refine Bound.congr (Bound.add Bound.one (((Bound.qParamFun).const_mul (240 : ℂ)))) ?_
  intro τ z
  simp only [A0q] <;> ring

theorem boundB0q : Bound (fun τ _ => B0q (Work.Kernels.qParamFun τ)) 0 := by
  refine Bound.congr (Bound.add Bound.one (((Bound.qParamFun).const_mul (-504 : ℂ)))) ?_
  intro τ z
  simp only [B0q] <;> ring

theorem boundE20q : Bound (fun τ _ => E20q (Work.Kernels.qParamFun τ)) 0 := by
  refine Bound.congr (Bound.add Bound.one (((Bound.qParamFun).const_mul (-24 : ℂ)))) ?_
  intro τ z
  simp only [E20q] <;> ring

theorem boundP20q (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun τ z => P20q (Work.Kernels.qParamFun τ) (cuspLin ℓ τ)) 0 := by
  have h : Bound (fun τ z => 2 * cuspLin ℓ τ
      + (48 * cuspLin ℓ τ + 408) * Work.Kernels.qParamFun τ) 0 :=
    ((Bound.cuspLin ℓ).const_mul (2 : ℂ)).add
      ((((Bound.cuspLin ℓ).const_mul (48 : ℂ)).add (Bound.const (408 : ℂ))).mul Bound.qParamFun)
  refine Bound.congr h ?_
  intro τ z
  simp only [P20q] <;> ring

theorem boundP40q (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun τ z => P40q (Work.Kernels.qParamFun τ) (cuspLin ℓ τ)) 0 := by
  have h : Bound (fun τ z => 2 * cuspLin ℓ τ
      - (288 * cuspLin ℓ τ + 744) * Work.Kernels.qParamFun τ) 0 :=
    ((Bound.cuspLin ℓ).const_mul (2 : ℂ)).add
      (((((Bound.cuspLin ℓ).const_mul (288 : ℂ)).add (Bound.const (744 : ℂ))).mul
        Bound.qParamFun).neg)
  refine Bound.congr h ?_
  intro τ z
  simp only [P40q] <;> ring

theorem bounded_atomProd (ℓ : Work.Kernels.LogLambdaData) (c : ℂ)
    (nq nL nT nZ npi npi' ns nC nA nB nE nP2 nP4 : ℕ) :
    Bound (atomProd ℓ c nq nL nT nZ npi npi' ns nC nA nB nE nP2 nP4) 0 := by
  have hm := Bound.monomial ℓ c nq nL nT nZ npi nC
  have h1 := hm.mul (Bound.piInvC_pow npi')
  have h2 := h1.mul ((Bound.S0z).pow ns)
  have h3 := h2.mul ((boundA0q).pow nA)
  have h4 := h3.mul ((boundB0q).pow nB)
  have h5 := h4.mul ((boundE20q).pow nE)
  have h6 := h5.mul ((boundP20q ℓ).pow nP2)
  have h7 := h6.mul ((boundP40q ℓ).pow nP4)
  refine Bound.congr (Bound.mono (Nat.zero_le _) h7) ?_
  intro τ z
  simp only [atomProd] <;> ring

theorem boundKhatDef (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun τ z => khatDef ℓ τ z) 0 := by
  have hsum : Bound (fun τ z =>
      atomProd ℓ ((1/3:ℂ)) 0 0 0 0 0 1 0 0 1 1 0 1 0 τ z +
      atomProd ℓ ((1/6:ℂ)) 0 0 0 0 0 1 0 0 2 0 0 0 1 τ z +
      atomProd ℓ ((1/36:ℂ)*Complex.I) 0 0 1 2 2 0 0 0 1 1 2 0 0 τ z +
      atomProd ℓ ((1/6:ℂ)) 0 0 0 2 1 0 0 0 1 1 1 0 0 τ z +
      atomProd ℓ ((-(1/18):ℂ)*Complex.I) 0 0 1 2 2 0 1 0 3 0 1 0 0 τ z +
      atomProd ℓ ((-(1/6):ℂ)) 0 0 0 2 1 0 1 0 3 0 0 0 0 τ z +
      atomProd ℓ ((1/36:ℂ)*Complex.I) 0 0 1 2 2 0 2 0 2 1 0 0 0 τ z +
      atomProd ℓ ((-1:ℂ)) 0 0 0 0 0 1 0 1 3 0 0 0 0 τ z +
      atomProd ℓ ((-Complex.I)) 0 0 0 1 0 0 0 0 3 0 0 0 0 τ z) 0 :=
    ((((((((      bounded_atomProd ℓ ((1/3:ℂ)) 0 0 0 0 0 1 0 0 1 1 0 1 0).add (bounded_atomProd ℓ ((1/6:ℂ)) 0 0 0 0 0 1 0 0 2 0 0 0 1)).add (bounded_atomProd ℓ ((1/36:ℂ)*Complex.I) 0 0 1 2 2 0 0 0 1 1 2 0 0)).add (bounded_atomProd ℓ ((1/6:ℂ)) 0 0 0 2 1 0 0 0 1 1 1 0 0)).add (bounded_atomProd ℓ ((-(1/18):ℂ)*Complex.I) 0 0 1 2 2 0 1 0 3 0 1 0 0)).add (bounded_atomProd ℓ ((-(1/6):ℂ)) 0 0 0 2 1 0 1 0 3 0 0 0 0)).add (bounded_atomProd ℓ ((1/36:ℂ)*Complex.I) 0 0 1 2 2 0 2 0 2 1 0 0 0)).add (bounded_atomProd ℓ ((-1:ℂ)) 0 0 0 0 0 1 0 1 3 0 0 0 0)).add (bounded_atomProd ℓ ((-Complex.I)) 0 0 0 1 0 0 0 0 3 0 0 0 0)
  refine Bound.congr hsum ?_
  intro τ z
  simp only [khatDef, KappaHat, atomProd, ShZ, S0z] <;> ring_nf

theorem boundRhatDef (ℓ : Work.Kernels.LogLambdaData) :
    Bound (fun τ z => rhatDef ℓ τ z) 0 := by
  have hsum : Bound (fun τ z =>
      atomProd ℓ ((9558:ℂ)) 1 0 0 0 0 1 0 0 0 0 0 0 0 τ z +
      atomProd ℓ ((-142236:ℂ)) 1 0 0 0 0 1 0 1 0 0 0 0 0 τ z +
      atomProd ℓ ((-(4719/32):ℂ)) 0 0 0 0 0 1 0 0 1 1 0 1 0 τ z +
      atomProd ℓ ((-(6417/32):ℂ)) 0 0 0 0 0 1 0 0 2 0 0 0 1 τ z +
      atomProd ℓ ((-12:ℂ)) 0 0 0 0 0 1 0 0 3 0 0 0 0 τ z +
      atomProd ℓ ((1464:ℂ)) 0 0 0 0 0 1 0 1 3 0 0 0 0 τ z +
      atomProd ℓ ((-142236:ℂ)*Complex.I) 1 0 0 1 0 0 0 0 0 0 0 0 0 τ z +
      atomProd ℓ ((1464:ℂ)*Complex.I) 0 0 0 1 0 0 0 0 3 0 0 0 0 τ z +
      atomProd ℓ ((71/48:ℂ)*Complex.I) 0 0 1 2 2 0 0 0 3 0 1 0 0 τ z +
      atomProd ℓ ((71/16:ℂ)) 0 0 0 2 1 0 0 0 3 0 0 0 0 τ z +
      atomProd ℓ ((-(71/96):ℂ)*Complex.I) 0 0 1 2 2 0 0 0 2 1 0 0 0 τ z +
      atomProd ℓ ((-(1351/96):ℂ)*Complex.I) 0 0 1 2 2 0 0 0 1 1 2 0 0 τ z +
      atomProd ℓ ((-(1351/16):ℂ)) 0 0 0 2 1 0 0 0 1 1 1 0 0 τ z +
      atomProd ℓ ((-1989:ℂ)*Complex.I) 1 0 1 2 2 0 0 0 0 0 1 0 0 τ z +
      atomProd ℓ ((-5967:ℂ)) 1 0 0 2 1 0 0 0 0 0 0 0 0 τ z +
      atomProd ℓ (((4/3:ℂ))*Complex.I) 0 0 1 2 2 0 0 0 3 0 1 0 0 τ z +
      atomProd ℓ ((4:ℂ)) 0 0 0 2 1 0 0 0 3 0 0 0 0 τ z +
      atomProd ℓ (((1/4:ℂ))*Complex.I) 0 0 1 2 2 0 1 0 3 0 1 0 0 τ z +
      atomProd ℓ ((3/4:ℂ)) 0 0 0 2 1 0 1 0 3 0 0 0 0 τ z +
      atomProd ℓ ((-(35/24):ℂ)*Complex.I) 0 0 1 2 2 0 1 0 2 1 0 0 0 τ z +
      atomProd ℓ ((-(1/8):ℂ)*Complex.I) 0 0 1 2 2 0 1 0 1 1 2 0 0 τ z +
      atomProd ℓ ((-(3/4):ℂ)) 0 0 0 2 1 0 1 0 1 1 1 0 0 τ z +
      atomProd ℓ ((-8154:ℂ)*Complex.I) 1 0 1 2 2 0 1 0 0 0 1 0 0 τ z +
      atomProd ℓ ((-24462:ℂ)) 1 0 0 2 1 0 1 0 0 0 0 0 0 τ z +
      atomProd ℓ (((244/3:ℂ))*Complex.I) 0 0 1 2 2 0 1 0 3 0 1 0 0 τ z +
      atomProd ℓ ((244:ℂ)) 0 0 0 2 1 0 1 0 3 0 0 0 0 τ z +
      atomProd ℓ ((-(1/16):ℂ)*Complex.I) 0 0 1 2 2 0 2 0 3 0 1 0 0 τ z +
      atomProd ℓ ((-(3/16):ℂ)) 0 0 0 2 1 0 2 0 3 0 0 0 0 τ z +
      atomProd ℓ ((-(639/32):ℂ)*Complex.I) 0 0 1 2 2 0 2 0 2 1 0 0 0 τ z +
      atomProd ℓ (((1/32:ℂ))*Complex.I) 0 0 1 2 2 0 2 0 1 1 2 0 0 τ z +
      atomProd ℓ ((3/16:ℂ)) 0 0 0 2 1 0 2 0 1 1 1 0 0 τ z +
      atomProd ℓ ((63:ℂ)*Complex.I) 1 0 1 2 2 0 2 0 0 0 1 0 0 τ z +
      atomProd ℓ ((189:ℂ)) 1 0 0 2 1 0 2 0 0 0 0 0 0 τ z) 0 :=
    ((((((((((((((((((((((((((((((((      bounded_atomProd ℓ ((9558:ℂ)) 1 0 0 0 0 1 0 0 0 0 0 0 0).add (bounded_atomProd ℓ ((-142236:ℂ)) 1 0 0 0 0 1 0 1 0 0 0 0 0)).add (bounded_atomProd ℓ ((-(4719/32):ℂ)) 0 0 0 0 0 1 0 0 1 1 0 1 0)).add (bounded_atomProd ℓ ((-(6417/32):ℂ)) 0 0 0 0 0 1 0 0 2 0 0 0 1)).add (bounded_atomProd ℓ ((-12:ℂ)) 0 0 0 0 0 1 0 0 3 0 0 0 0)).add (bounded_atomProd ℓ ((1464:ℂ)) 0 0 0 0 0 1 0 1 3 0 0 0 0)).add (bounded_atomProd ℓ ((-142236:ℂ)*Complex.I) 1 0 0 1 0 0 0 0 0 0 0 0 0)).add (bounded_atomProd ℓ ((1464:ℂ)*Complex.I) 0 0 0 1 0 0 0 0 3 0 0 0 0)).add (bounded_atomProd ℓ ((71/48:ℂ)*Complex.I) 0 0 1 2 2 0 0 0 3 0 1 0 0)).add (bounded_atomProd ℓ ((71/16:ℂ)) 0 0 0 2 1 0 0 0 3 0 0 0 0)).add (bounded_atomProd ℓ ((-(71/96):ℂ)*Complex.I) 0 0 1 2 2 0 0 0 2 1 0 0 0)).add (bounded_atomProd ℓ ((-(1351/96):ℂ)*Complex.I) 0 0 1 2 2 0 0 0 1 1 2 0 0)).add (bounded_atomProd ℓ ((-(1351/16):ℂ)) 0 0 0 2 1 0 0 0 1 1 1 0 0)).add (bounded_atomProd ℓ ((-1989:ℂ)*Complex.I) 1 0 1 2 2 0 0 0 0 0 1 0 0)).add (bounded_atomProd ℓ ((-5967:ℂ)) 1 0 0 2 1 0 0 0 0 0 0 0 0)).add (bounded_atomProd ℓ (((4/3:ℂ))*Complex.I) 0 0 1 2 2 0 0 0 3 0 1 0 0)).add (bounded_atomProd ℓ ((4:ℂ)) 0 0 0 2 1 0 0 0 3 0 0 0 0)).add (bounded_atomProd ℓ (((1/4:ℂ))*Complex.I) 0 0 1 2 2 0 1 0 3 0 1 0 0)).add (bounded_atomProd ℓ ((3/4:ℂ)) 0 0 0 2 1 0 1 0 3 0 0 0 0)).add (bounded_atomProd ℓ ((-(35/24):ℂ)*Complex.I) 0 0 1 2 2 0 1 0 2 1 0 0 0)).add (bounded_atomProd ℓ ((-(1/8):ℂ)*Complex.I) 0 0 1 2 2 0 1 0 1 1 2 0 0)).add (bounded_atomProd ℓ ((-(3/4):ℂ)) 0 0 0 2 1 0 1 0 1 1 1 0 0)).add (bounded_atomProd ℓ ((-8154:ℂ)*Complex.I) 1 0 1 2 2 0 1 0 0 0 1 0 0)).add (bounded_atomProd ℓ ((-24462:ℂ)) 1 0 0 2 1 0 1 0 0 0 0 0 0)).add (bounded_atomProd ℓ (((244/3:ℂ))*Complex.I) 0 0 1 2 2 0 1 0 3 0 1 0 0)).add (bounded_atomProd ℓ ((244:ℂ)) 0 0 0 2 1 0 1 0 3 0 0 0 0)).add (bounded_atomProd ℓ ((-(1/16):ℂ)*Complex.I) 0 0 1 2 2 0 2 0 3 0 1 0 0)).add (bounded_atomProd ℓ ((-(3/16):ℂ)) 0 0 0 2 1 0 2 0 3 0 0 0 0)).add (bounded_atomProd ℓ ((-(639/32):ℂ)*Complex.I) 0 0 1 2 2 0 2 0 2 1 0 0 0)).add (bounded_atomProd ℓ (((1/32:ℂ))*Complex.I) 0 0 1 2 2 0 2 0 1 1 2 0 0)).add (bounded_atomProd ℓ ((3/16:ℂ)) 0 0 0 2 1 0 2 0 1 1 1 0 0)).add (bounded_atomProd ℓ ((63:ℂ)*Complex.I) 1 0 1 2 2 0 2 0 0 0 1 0 0)).add (bounded_atomProd ℓ ((189:ℂ)) 1 0 0 2 1 0 2 0 0 0 0 0 0)
  refine Bound.congr hsum ?_
  intro τ z
  simp only [rhatDef, RestHat, atomProd, ShZ, S0z] <;> ring_nf
end

end Work.Asymptotics.KhatE1Core
