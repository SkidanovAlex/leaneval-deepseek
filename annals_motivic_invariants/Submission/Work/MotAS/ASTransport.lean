import Submission.Work.MotAS.ASEntries
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# AS (characteristic 5) Galois-coordinate transport identities

Part of the subproject `Submission/Work/MotAS` (`Work.MotAS`) for `MOTIVIC_KDATA_LEAD.md` §6.

The images of the split Klein--Fisher Pfaffians of `Work.MotK` under the Artin--Schreier
Galois-coordinate substitution `x_i = Σ_j y_j (w+i)^j` (`asM`), reduced modulo `w⁵ = w + g` and
`5 = 0`: hence `w`-free, i.e. `𝕜`-rational.  The certificates are `linear_combination` proofs over
`ℤ`.  The transported secant quintics `s`, `s'` (`asTransportS`, `asTransportSD`) and the bundle
`asTransportR` need a different reduction strategy (`Work.MotAS.ASRed`) and live in
`Submission/Work/MotAS/ASTransportSec.lean` / `ASTransportR.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS

variable {R : Type*} [CommRing R]


/-- `p_0(asM w · y) = Σ_j asN w 0 j · p^AS_j(y)`. -/
theorem asTransportP0 (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) (y : Fin 5 → R) :
    Work.MotK.kleinP a b (fun i => ∑ j, asM w i j * y j) 0 =
      ∑ j, asN w 0 j * kleinPAS a b g y j := by
  simp only [asM_0_0, asM_0_1, asM_0_2, asM_0_3, asM_0_4, asM_1_0, asM_1_1, asM_1_2, asM_1_3, asM_1_4, asM_2_0, asM_2_1, asM_2_2, asM_2_3, asM_2_4, asM_3_0, asM_3_1, asM_3_2, asM_3_3, asM_3_4, asM_4_0, asM_4_1, asM_4_2, asM_4_3, asM_4_4, asN_0_0, asN_0_1, asN_0_2, asN_0_3, asN_0_4, asN_1_0, asN_1_1, asN_1_2, asN_1_3, asN_1_4, asN_2_0, asN_2_1, asN_2_2, asN_2_3, asN_2_4, asN_3_0, asN_3_1, asN_3_2, asN_3_3, asN_3_4, asN_4_0, asN_4_1, asN_4_2, asN_4_3, asN_4_4, Fin.sum_univ_five,
    kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
    Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2, Work.MotK.kleinP3,
    Work.MotK.kleinP4, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  linear_combination (norm := refl_ring1 (mod := 5)) (a^ (2:ℕ)*w^ (3:ℕ)*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*w^ (2:ℕ)*y 3*y 4 + 20*a^ (2:ℕ)*w^ (2:ℕ)*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*w*y 2*y 4 + a^ (2:ℕ)*w*y 3^ (2:ℕ) + 35*a^ (2:ℕ)*w*y 3*y 4 + 174*a^ (2:ℕ)*w*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*y 1*y 4 + 2*a^ (2:ℕ)*y 2*y 3 + 30*a^ (2:ℕ)*y 2*y 4 + 15*a^ (2:ℕ)*y 3^ (2:ℕ) + 261*a^ (2:ℕ)*y 3*y 4 + 860*a^ (2:ℕ)*y 4^ (2:ℕ) - a*b*w^ (3:ℕ)*y 4^ (2:ℕ) - 2*a*b*w^ (2:ℕ)*y 3*y 4 - 2*a*b*w*y 2*y 4 - a*b*w*y 3^ (2:ℕ) - 2*a*b*y 1*y 4 - 2*a*b*y 2*y 3 - b^ (2:ℕ)*w^ (3:ℕ)*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*w^ (2:ℕ)*y 3*y 4 - 20*b^ (2:ℕ)*w^ (2:ℕ)*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*w*y 2*y 4 - b^ (2:ℕ)*w*y 3^ (2:ℕ) - 35*b^ (2:ℕ)*w*y 3*y 4 - 166*b^ (2:ℕ)*w*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*y 1*y 4 - 2*b^ (2:ℕ)*y 2*y 3 - 30*b^ (2:ℕ)*y 2*y 4 - 15*b^ (2:ℕ)*y 3^ (2:ℕ) - 249*b^ (2:ℕ)*y 3*y 4 - 740*b^ (2:ℕ)*y 4^ (2:ℕ)) * hw

/-- `p_1(asM w · y) = Σ_j asN w 1 j · p^AS_j(y)`. -/
theorem asTransportP1 (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) (y : Fin 5 → R) :
    Work.MotK.kleinP a b (fun i => ∑ j, asM w i j * y j) 1 =
      ∑ j, asN w 1 j * kleinPAS a b g y j := by
  simp only [asM_0_0, asM_0_1, asM_0_2, asM_0_3, asM_0_4, asM_1_0, asM_1_1, asM_1_2, asM_1_3, asM_1_4, asM_2_0, asM_2_1, asM_2_2, asM_2_3, asM_2_4, asM_3_0, asM_3_1, asM_3_2, asM_3_3, asM_3_4, asM_4_0, asM_4_1, asM_4_2, asM_4_3, asM_4_4, asN_0_0, asN_0_1, asN_0_2, asN_0_3, asN_0_4, asN_1_0, asN_1_1, asN_1_2, asN_1_3, asN_1_4, asN_2_0, asN_2_1, asN_2_2, asN_2_3, asN_2_4, asN_3_0, asN_3_1, asN_3_2, asN_3_3, asN_3_4, asN_4_0, asN_4_1, asN_4_2, asN_4_3, asN_4_4, Fin.sum_univ_five,
    kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
    Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2, Work.MotK.kleinP3,
    Work.MotK.kleinP4, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  linear_combination (norm := refl_ring1 (mod := 5)) (a^ (2:ℕ)*w^ (3:ℕ)*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*w^ (2:ℕ)*y 3*y 4 + 16*a^ (2:ℕ)*w^ (2:ℕ)*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*w*y 2*y 4 + a^ (2:ℕ)*w*y 3^ (2:ℕ) + 28*a^ (2:ℕ)*w*y 3*y 4 + 96*a^ (2:ℕ)*w*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*y 1*y 4 + 2*a^ (2:ℕ)*y 2*y 3 + 24*a^ (2:ℕ)*y 2*y 4 + 12*a^ (2:ℕ)*y 3^ (2:ℕ) + 144*a^ (2:ℕ)*y 3*y 4 + 256*a^ (2:ℕ)*y 4^ (2:ℕ) - a*b*w^ (3:ℕ)*y 4^ (2:ℕ) - 2*a*b*w^ (2:ℕ)*y 3*y 4 - 16*a*b*w^ (2:ℕ)*y 4^ (2:ℕ) - 2*a*b*w*y 2*y 4 - a*b*w*y 3^ (2:ℕ) - 28*a*b*w*y 3*y 4 - 112*a*b*w*y 4^ (2:ℕ) - 2*a*b*y 1*y 4 - 2*a*b*y 2*y 3 - 24*a*b*y 2*y 4 - 12*a*b*y 3^ (2:ℕ) - 168*a*b*y 3*y 4 - 448*a*b*y 4^ (2:ℕ) - b^ (2:ℕ)*w^ (3:ℕ)*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*w^ (2:ℕ)*y 3*y 4 - 16*b^ (2:ℕ)*w^ (2:ℕ)*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*w*y 2*y 4 - b^ (2:ℕ)*w*y 3^ (2:ℕ) - 28*b^ (2:ℕ)*w*y 3*y 4 - 108*b^ (2:ℕ)*w*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*y 1*y 4 - 2*b^ (2:ℕ)*y 2*y 3 - 24*b^ (2:ℕ)*y 2*y 4 - 12*b^ (2:ℕ)*y 3^ (2:ℕ) - 162*b^ (2:ℕ)*y 3*y 4 - 400*b^ (2:ℕ)*y 4^ (2:ℕ)) * hw

/-- `p_2(asM w · y) = Σ_j asN w 2 j · p^AS_j(y)`. -/
theorem asTransportP2 (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) (y : Fin 5 → R) :
    Work.MotK.kleinP a b (fun i => ∑ j, asM w i j * y j) 2 =
      ∑ j, asN w 2 j * kleinPAS a b g y j := by
  simp only [asM_0_0, asM_0_1, asM_0_2, asM_0_3, asM_0_4, asM_1_0, asM_1_1, asM_1_2, asM_1_3, asM_1_4, asM_2_0, asM_2_1, asM_2_2, asM_2_3, asM_2_4, asM_3_0, asM_3_1, asM_3_2, asM_3_3, asM_3_4, asM_4_0, asM_4_1, asM_4_2, asM_4_3, asM_4_4, asN_0_0, asN_0_1, asN_0_2, asN_0_3, asN_0_4, asN_1_0, asN_1_1, asN_1_2, asN_1_3, asN_1_4, asN_2_0, asN_2_1, asN_2_2, asN_2_3, asN_2_4, asN_3_0, asN_3_1, asN_3_2, asN_3_3, asN_3_4, asN_4_0, asN_4_1, asN_4_2, asN_4_3, asN_4_4, Fin.sum_univ_five,
    kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
    Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2, Work.MotK.kleinP3,
    Work.MotK.kleinP4, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  linear_combination (norm := refl_ring1 (mod := 5)) (a^ (2:ℕ)*w^ (3:ℕ)*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*w^ (2:ℕ)*y 3*y 4 + 12*a^ (2:ℕ)*w^ (2:ℕ)*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*w*y 2*y 4 + a^ (2:ℕ)*w*y 3^ (2:ℕ) + 21*a^ (2:ℕ)*w*y 3*y 4 + 62*a^ (2:ℕ)*w*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*y 1*y 4 + 2*a^ (2:ℕ)*y 2*y 3 + 18*a^ (2:ℕ)*y 2*y 4 + 9*a^ (2:ℕ)*y 3^ (2:ℕ) + 93*a^ (2:ℕ)*y 3*y 4 + 180*a^ (2:ℕ)*y 4^ (2:ℕ) - a*b*w^ (3:ℕ)*y 4^ (2:ℕ) - 2*a*b*w^ (2:ℕ)*y 3*y 4 - 32*a*b*w^ (2:ℕ)*y 4^ (2:ℕ) - 2*a*b*w*y 2*y 4 - a*b*w*y 3^ (2:ℕ) - 56*a*b*w*y 3*y 4 - 448*a*b*w*y 4^ (2:ℕ) - 2*a*b*y 1*y 4 - 2*a*b*y 2*y 3 - 48*a*b*y 2*y 4 - 24*a*b*y 3^ (2:ℕ) - 672*a*b*y 3*y 4 - 3584*a*b*y 4^ (2:ℕ) - b^ (2:ℕ)*w^ (3:ℕ)*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*w^ (2:ℕ)*y 3*y 4 - 12*b^ (2:ℕ)*w^ (2:ℕ)*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*w*y 2*y 4 - b^ (2:ℕ)*w*y 3^ (2:ℕ) - 21*b^ (2:ℕ)*w*y 3*y 4 - 54*b^ (2:ℕ)*w*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*y 1*y 4 - 2*b^ (2:ℕ)*y 2*y 3 - 18*b^ (2:ℕ)*y 2*y 4 - 9*b^ (2:ℕ)*y 3^ (2:ℕ) - 81*b^ (2:ℕ)*y 3*y 4 - 108*b^ (2:ℕ)*y 4^ (2:ℕ)) * hw

/-- `p_3(asM w · y) = Σ_j asN w 3 j · p^AS_j(y)`. -/
theorem asTransportP3 (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) (y : Fin 5 → R) :
    Work.MotK.kleinP a b (fun i => ∑ j, asM w i j * y j) 3 =
      ∑ j, asN w 3 j * kleinPAS a b g y j := by
  simp only [asM_0_0, asM_0_1, asM_0_2, asM_0_3, asM_0_4, asM_1_0, asM_1_1, asM_1_2, asM_1_3, asM_1_4, asM_2_0, asM_2_1, asM_2_2, asM_2_3, asM_2_4, asM_3_0, asM_3_1, asM_3_2, asM_3_3, asM_3_4, asM_4_0, asM_4_1, asM_4_2, asM_4_3, asM_4_4, asN_0_0, asN_0_1, asN_0_2, asN_0_3, asN_0_4, asN_1_0, asN_1_1, asN_1_2, asN_1_3, asN_1_4, asN_2_0, asN_2_1, asN_2_2, asN_2_3, asN_2_4, asN_3_0, asN_3_1, asN_3_2, asN_3_3, asN_3_4, asN_4_0, asN_4_1, asN_4_2, asN_4_3, asN_4_4, Fin.sum_univ_five,
    kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
    Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2, Work.MotK.kleinP3,
    Work.MotK.kleinP4, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  linear_combination (norm := refl_ring1 (mod := 5)) (a^ (2:ℕ)*w^ (3:ℕ)*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*w^ (2:ℕ)*y 3*y 4 + 28*a^ (2:ℕ)*w^ (2:ℕ)*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*w*y 2*y 4 + a^ (2:ℕ)*w*y 3^ (2:ℕ) + 49*a^ (2:ℕ)*w*y 3*y 4 + 342*a^ (2:ℕ)*w*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*y 1*y 4 + 2*a^ (2:ℕ)*y 2*y 3 + 42*a^ (2:ℕ)*y 2*y 4 + 21*a^ (2:ℕ)*y 3^ (2:ℕ) + 513*a^ (2:ℕ)*y 3*y 4 + 2380*a^ (2:ℕ)*y 4^ (2:ℕ) - a*b*w^ (3:ℕ)*y 4^ (2:ℕ) - 2*a*b*w^ (2:ℕ)*y 3*y 4 - 8*a*b*w^ (2:ℕ)*y 4^ (2:ℕ) - 2*a*b*w*y 2*y 4 - a*b*w*y 3^ (2:ℕ) - 14*a*b*w*y 3*y 4 - 28*a*b*w*y 4^ (2:ℕ) - 2*a*b*y 1*y 4 - 2*a*b*y 2*y 3 - 12*a*b*y 2*y 4 - 6*a*b*y 3^ (2:ℕ) - 42*a*b*y 3*y 4 - 56*a*b*y 4^ (2:ℕ) - b^ (2:ℕ)*w^ (3:ℕ)*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*w^ (2:ℕ)*y 3*y 4 - 8*b^ (2:ℕ)*w^ (2:ℕ)*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*w*y 2*y 4 - b^ (2:ℕ)*w*y 3^ (2:ℕ) - 14*b^ (2:ℕ)*w*y 3*y 4 - 24*b^ (2:ℕ)*w*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*y 1*y 4 - 2*b^ (2:ℕ)*y 2*y 3 - 12*b^ (2:ℕ)*y 2*y 4 - 6*b^ (2:ℕ)*y 3^ (2:ℕ) - 36*b^ (2:ℕ)*y 3*y 4 - 32*b^ (2:ℕ)*y 4^ (2:ℕ)) * hw

/-- `p_4(asM w · y) = Σ_j asN w 4 j · p^AS_j(y)`. -/
theorem asTransportP4 (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) (y : Fin 5 → R) :
    Work.MotK.kleinP a b (fun i => ∑ j, asM w i j * y j) 4 =
      ∑ j, asN w 4 j * kleinPAS a b g y j := by
  simp only [asM_0_0, asM_0_1, asM_0_2, asM_0_3, asM_0_4, asM_1_0, asM_1_1, asM_1_2, asM_1_3, asM_1_4, asM_2_0, asM_2_1, asM_2_2, asM_2_3, asM_2_4, asM_3_0, asM_3_1, asM_3_2, asM_3_3, asM_3_4, asM_4_0, asM_4_1, asM_4_2, asM_4_3, asM_4_4, asN_0_0, asN_0_1, asN_0_2, asN_0_3, asN_0_4, asN_1_0, asN_1_1, asN_1_2, asN_1_3, asN_1_4, asN_2_0, asN_2_1, asN_2_2, asN_2_3, asN_2_4, asN_3_0, asN_3_1, asN_3_2, asN_3_3, asN_3_4, asN_4_0, asN_4_1, asN_4_2, asN_4_3, asN_4_4, Fin.sum_univ_five,
    kleinPAS, kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
    Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2, Work.MotK.kleinP3,
    Work.MotK.kleinP4, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  linear_combination (norm := refl_ring1 (mod := 5)) (a^ (2:ℕ)*w^ (3:ℕ)*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*w^ (2:ℕ)*y 3*y 4 + 4*a^ (2:ℕ)*w^ (2:ℕ)*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*w*y 2*y 4 + a^ (2:ℕ)*w*y 3^ (2:ℕ) + 7*a^ (2:ℕ)*w*y 3*y 4 + 6*a^ (2:ℕ)*w*y 4^ (2:ℕ) + 2*a^ (2:ℕ)*y 1*y 4 + 2*a^ (2:ℕ)*y 2*y 3 + 6*a^ (2:ℕ)*y 2*y 4 + 3*a^ (2:ℕ)*y 3^ (2:ℕ) + 9*a^ (2:ℕ)*y 3*y 4 + 4*a^ (2:ℕ)*y 4^ (2:ℕ) - a*b*w^ (3:ℕ)*y 4^ (2:ℕ) - 2*a*b*w^ (2:ℕ)*y 3*y 4 - 24*a*b*w^ (2:ℕ)*y 4^ (2:ℕ) - 2*a*b*w*y 2*y 4 - a*b*w*y 3^ (2:ℕ) - 42*a*b*w*y 3*y 4 - 252*a*b*w*y 4^ (2:ℕ) - 2*a*b*y 1*y 4 - 2*a*b*y 2*y 3 - 36*a*b*y 2*y 4 - 18*a*b*y 3^ (2:ℕ) - 378*a*b*y 3*y 4 - 1512*a*b*y 4^ (2:ℕ) - b^ (2:ℕ)*w^ (3:ℕ)*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*w^ (2:ℕ)*y 3*y 4 - 24*b^ (2:ℕ)*w^ (2:ℕ)*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*w*y 2*y 4 - b^ (2:ℕ)*w*y 3^ (2:ℕ) - 42*b^ (2:ℕ)*w*y 3*y 4 - 248*b^ (2:ℕ)*w*y 4^ (2:ℕ) - 2*b^ (2:ℕ)*y 1*y 4 - 2*b^ (2:ℕ)*y 2*y 3 - 36*b^ (2:ℕ)*y 2*y 4 - 18*b^ (2:ℕ)*y 3^ (2:ℕ) - 372*b^ (2:ℕ)*y 3*y 4 - 1440*b^ (2:ℕ)*y 4^ (2:ℕ)) * hw

/-- `q(asM w · y) = q^AS(y)`. -/
theorem asTransportQ (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) (y : Fin 5 → R) :
    Work.MotK.kleinQ a b (fun i => ∑ j, asM w i j * y j) = kleinQAS a b y := by
  simp only [asM_0_0, asM_0_1, asM_0_2, asM_0_3, asM_0_4, asM_1_0, asM_1_1, asM_1_2, asM_1_3, asM_1_4, asM_2_0, asM_2_1, asM_2_2, asM_2_3, asM_2_4, asM_3_0, asM_3_1, asM_3_2, asM_3_3, asM_3_4, asM_4_0, asM_4_1, asM_4_2, asM_4_3, asM_4_4, asN_0_0, asN_0_1, asN_0_2, asN_0_3, asN_0_4, asN_1_0, asN_1_1, asN_1_2, asN_1_3, asN_1_4, asN_2_0, asN_2_1, asN_2_2, asN_2_3, asN_2_4, asN_3_0, asN_3_1, asN_3_2, asN_3_3, asN_3_4, asN_4_0, asN_4_1, asN_4_2, asN_4_3, asN_4_4, Fin.sum_univ_five, kleinQAS, Work.MotK.kleinQ,
    Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4,
    Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  linear_combination (norm := refl_ring1 (mod := 5)) (5*a^ (2:ℕ)*w^ (3:ℕ)*y 4^ (2:ℕ) + 10*a^ (2:ℕ)*w^ (2:ℕ)*y 3*y 4 + 80*a^ (2:ℕ)*w^ (2:ℕ)*y 4^ (2:ℕ) + 10*a^ (2:ℕ)*w*y 2*y 4 + 5*a^ (2:ℕ)*w*y 3^ (2:ℕ) + 140*a^ (2:ℕ)*w*y 3*y 4 + 680*a^ (2:ℕ)*w*y 4^ (2:ℕ) + 10*a^ (2:ℕ)*y 1*y 4 + 10*a^ (2:ℕ)*y 2*y 3 + 120*a^ (2:ℕ)*y 2*y 4 + 60*a^ (2:ℕ)*y 3^ (2:ℕ) + 1020*a^ (2:ℕ)*y 3*y 4 + 3680*a^ (2:ℕ)*y 4^ (2:ℕ) - 5*a*b*w^ (3:ℕ)*y 4^ (2:ℕ) - 10*a*b*w^ (2:ℕ)*y 3*y 4 - 80*a*b*w^ (2:ℕ)*y 4^ (2:ℕ) - 10*a*b*w*y 2*y 4 - 5*a*b*w*y 3^ (2:ℕ) - 140*a*b*w*y 3*y 4 - 840*a*b*w*y 4^ (2:ℕ) - 10*a*b*y 1*y 4 - 10*a*b*y 2*y 3 - 120*a*b*y 2*y 4 - 60*a*b*y 3^ (2:ℕ) - 1260*a*b*y 3*y 4 - 5600*a*b*y 4^ (2:ℕ) - 5*b^ (2:ℕ)*w^ (3:ℕ)*y 4^ (2:ℕ) - 10*b^ (2:ℕ)*w^ (2:ℕ)*y 3*y 4 - 80*b^ (2:ℕ)*w^ (2:ℕ)*y 4^ (2:ℕ) - 10*b^ (2:ℕ)*w*y 2*y 4 - 5*b^ (2:ℕ)*w*y 3^ (2:ℕ) - 140*b^ (2:ℕ)*w*y 3*y 4 - 600*b^ (2:ℕ)*w*y 4^ (2:ℕ) - 10*b^ (2:ℕ)*y 1*y 4 - 10*b^ (2:ℕ)*y 2*y 3 - 120*b^ (2:ℕ)*y 2*y 4 - 60*b^ (2:ℕ)*y 3^ (2:ℕ) - 900*b^ (2:ℕ)*y 3*y 4 - 2720*b^ (2:ℕ)*y 4^ (2:ℕ)) * hw

/-- Bundled transport of the Pfaffians: `p(asM w · y) = asN w · p^AS(y)`. -/
theorem asTransportP (a b g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) (y : Fin 5 → R) :
    Work.MotK.kleinP a b (fun i => ∑ j, asM w i j * y j) = (asN w).mulVec (kleinPAS a b g y) := by
  funext i
  fin_cases i
  · exact asTransportP0 a b g w h5 hw y
  · exact asTransportP1 a b g w h5 hw y
  · exact asTransportP2 a b g w h5 hw y
  · exact asTransportP3 a b g w h5 hw y
  · exact asTransportP4 a b g w h5 hw y

end Work.MotAS
