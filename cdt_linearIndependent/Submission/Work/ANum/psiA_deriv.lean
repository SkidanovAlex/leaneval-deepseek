import Mathlib
import Submission.CDTPlan.InterfacesA
import Submission.Work.APsi.defs
import Submission.Work.ANum.slit_deriv_zero
import Submission.Work.ANum.lune_deriv_zero

/-! # `deriv psiA 0` and its norm

The contour map `psiA = -(4/5)·lune(36/5, -w₄)` with `w₄` the four-slit composition.  By the chain
rule and the exact derivatives `slit r '(0) = 4r/(1+r)²`, `lune c '(0) = (c²-1)/(c²+1)`,

  `deriv psiA 0 = -(4/5)·((c²-1)/(c²+1))·rot(-1971/25000)·d₄·rot(453/12500)·d₃·rot(2927/25000)·d₂·
    rot(2033/25000)·d₁·(491/500)`,

with `dⱼ = 4rⱼ/(1+rⱼ)²`, and the norms `‖rot t‖ = 1` give the rational value of `‖deriv psiA 0‖`. -/

namespace Work.ANum

open Submission.CDTPlan Complex
open Work.APsi

noncomputable def sA0 (z : ℂ) : ℂ := (491 / 500 : ℂ) * z
noncomputable def sA1 (z : ℂ) : ℂ := slit (9 / 10) (sA0 z)
noncomputable def sA2 (z : ℂ) : ℂ := slit (379 / 625) (rot (2033 / 25000) * sA1 z)
noncomputable def sA3 (z : ℂ) : ℂ := slit (673 / 1250) (rot (2927 / 25000) * sA2 z)
noncomputable def sA4 (z : ℂ) : ℂ := slit (7487 / 10000) (rot (453 / 12500) * sA3 z)
noncomputable def slitsA' (z : ℂ) : ℂ := rot (-1971 / 25000) * sA4 z

theorem slitsA'_eq : slitsA' = slitsA := rfl

/-- The real slope `4r/(1+r)²` of the slit map, as a complex number. -/
theorem slit_deriv_zero' (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (slit r) ((4 * r / (1 + r) ^ 2 : ℝ) : ℂ) 0 := by
  have h := slit_deriv_zero r hr hr1
  have hv : 4 * (r : ℂ) / (1 + (r : ℂ)) ^ 2 = ((4 * r / (1 + r) ^ 2 : ℝ) : ℂ) := by
    rw [show ((r:ℂ)) = ((r:ℝ):ℂ) from rfl,
      show (4 * ((r:ℝ):ℂ)) = (((4*r:ℝ)):ℂ) by push_cast; ring,
      show (1 + ((r:ℝ):ℂ)) = (((1+r:ℝ)):ℂ) by push_cast; ring,
      show (((1+r:ℝ):ℂ))^2 = ((((1+r)^2:ℝ)):ℂ) by push_cast; ring]
    rw [← Complex.ofReal_div]
  rw [hv] at h
  exact h

/-- The real slope `(c²-1)/(c²+1)` of the lune map, as a complex number. -/
theorem lune_deriv_zero' (c : ℝ) (hc : 1 < c) :
    HasDerivAt (lune c) (((c ^ 2 - 1) / (c ^ 2 + 1) : ℝ) : ℂ) 0 := by
  have h := lune_deriv_zero c hc
  have hv : (((c : ℂ) ^ 2 - 1) / ((c : ℂ) ^ 2 + 1)) = (((c ^ 2 - 1) / (c ^ 2 + 1) : ℝ) : ℂ) := by
    rw [show ((c : ℂ) ^ 2 - 1) = (((c ^ 2 - 1 : ℝ)) : ℂ) by push_cast; ring,
      show ((c : ℂ) ^ 2 + 1) = (((c ^ 2 + 1 : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_div]
  rw [hv] at h
  exact h



/-! ## The chain rule along the contour -/

/-- The `j`-th slit slope `4r/(1+r)²`, as a complex number. -/
noncomputable def Ds (r : ℝ) : ℂ := ((4 * r / (1 + r) ^ 2 : ℝ) : ℂ)

theorem sA0_deriv : HasDerivAt sA0 (491 / 500 : ℂ) 0 := by
  have h : HasDerivAt (fun z : ℂ => (491 / 500 : ℂ) * z) (491 / 500 : ℂ) 0 := by
    have h0 := (hasDerivAt_id' (0 : ℂ)).const_mul (491 / 500 : ℂ)
    have hv : (491 / 500 : ℂ) * 1 = 491 / 500 := by ring
    exact h0.congr_deriv hv
  rw [show sA0 = fun z : ℂ => (491 / 500 : ℂ) * z from rfl]
  exact h

theorem sA1_zero : sA1 0 = 0 := by simp [sA1, sA0, slit_zero]

theorem sA1_deriv : HasDerivAt sA1 (Ds (9 / 10) * (491 / 500)) 0 := by
  have h : HasDerivAt (fun z : ℂ => slit (9 / 10) (sA0 z)) (Ds (9 / 10) * (491 / 500)) 0 := by
    have hs : HasDerivAt (slit (9 / 10)) (Ds (9 / 10)) (sA0 0) := by
      rw [show sA0 0 = 0 by simp [sA0]]
      exact slit_deriv_zero' (9 / 10) (by norm_num) (by norm_num)
    exact hs.comp 0 sA0_deriv
  rw [show sA1 = fun z : ℂ => slit (9 / 10) (sA0 z) from rfl]
  exact h

theorem sA2_zero : sA2 0 = 0 := by simp [sA2, sA1, sA0, slit_zero]

theorem sA2_deriv : HasDerivAt sA2
    (Ds (379 / 625) * (rot (2033 / 25000) * (Ds (9 / 10) * (491 / 500)))) 0 := by
  have hinner : HasDerivAt (fun z : ℂ => rot (2033 / 25000) * sA1 z)
      (rot (2033 / 25000) * (Ds (9 / 10) * (491 / 500))) 0 := by
    have h := sA1_deriv.const_mul (rot (2033 / 25000))
    rw [show (fun z : ℂ => rot (2033 / 25000) * sA1 z)
        = fun z : ℂ => rot (2033 / 25000) * sA1 z from rfl] at h
    exact h
  have hs : HasDerivAt (slit (379 / 625)) (Ds (379 / 625))
      ((fun z : ℂ => rot (2033 / 25000) * sA1 z) 0) := by
    rw [show (fun z : ℂ => rot (2033 / 25000) * sA1 z) 0 = 0 by simp [sA1_zero]]
    exact slit_deriv_zero' (379 / 625) (by norm_num) (by norm_num)
  have h := hs.comp 0 hinner
  rw [show sA2 = (fun z : ℂ => slit (379 / 625) (rot (2033 / 25000) * sA1 z)) from rfl]
  exact h

theorem sA3_zero : sA3 0 = 0 := by simp [sA3, sA2, sA1, sA0, slit_zero]

theorem sA3_deriv : HasDerivAt sA3
    (Ds (673 / 1250) * (rot (2927 / 25000) *
      (Ds (379 / 625) * (rot (2033 / 25000) * (Ds (9 / 10) * (491 / 500)))))) 0 := by
  have hinner : HasDerivAt (fun z : ℂ => rot (2927 / 25000) * sA2 z)
      (rot (2927 / 25000) *
        (Ds (379 / 625) * (rot (2033 / 25000) * (Ds (9 / 10) * (491 / 500))))) 0 :=
    sA2_deriv.const_mul (rot (2927 / 25000))
  have hs : HasDerivAt (slit (673 / 1250)) (Ds (673 / 1250))
      ((fun z : ℂ => rot (2927 / 25000) * sA2 z) 0) := by
    rw [show (fun z : ℂ => rot (2927 / 25000) * sA2 z) 0 = 0 by simp [sA2_zero]]
    exact slit_deriv_zero' (673 / 1250) (by norm_num) (by norm_num)
  have h := hs.comp 0 hinner
  rw [show sA3 = (fun z : ℂ => slit (673 / 1250) (rot (2927 / 25000) * sA2 z)) from rfl]
  exact h

theorem sA4_zero : sA4 0 = 0 := by simp [sA4, sA3, sA2, sA1, sA0, slit_zero]

theorem sA4_deriv : HasDerivAt sA4
    (Ds (7487 / 10000) * (rot (453 / 12500) *
      (Ds (673 / 1250) * (rot (2927 / 25000) *
        (Ds (379 / 625) * (rot (2033 / 25000) * (Ds (9 / 10) * (491 / 500)))))))) 0 := by
  have hinner : HasDerivAt (fun z : ℂ => rot (453 / 12500) * sA3 z)
      (rot (453 / 12500) *
        (Ds (673 / 1250) * (rot (2927 / 25000) *
          (Ds (379 / 625) * (rot (2033 / 25000) * (Ds (9 / 10) * (491 / 500))))))) 0 :=
    sA3_deriv.const_mul (rot (453 / 12500))
  have hs : HasDerivAt (slit (7487 / 10000)) (Ds (7487 / 10000))
      ((fun z : ℂ => rot (453 / 12500) * sA3 z) 0) := by
    rw [show (fun z : ℂ => rot (453 / 12500) * sA3 z) 0 = 0 by simp [sA3_zero]]
    exact slit_deriv_zero' (7487 / 10000) (by norm_num) (by norm_num)
  have h := hs.comp 0 hinner
  rw [show sA4 = (fun z : ℂ => slit (7487 / 10000) (rot (453 / 12500) * sA3 z)) from rfl]
  exact h

theorem slitsA'_zero : slitsA' 0 = 0 := by simp [slitsA', sA4_zero]

/-- The derivative of the four-slit composition at `0`. -/
noncomputable def W : ℂ := rot (-1971 / 25000) * (Ds (7487 / 10000) * (rot (453 / 12500) *
  (Ds (673 / 1250) * (rot (2927 / 25000) *
    (Ds (379 / 625) * (rot (2033 / 25000) * (Ds (9 / 10) * (491 / 500))))))))

theorem slitsA'_deriv : HasDerivAt slitsA' W 0 := by
  have h := sA4_deriv.const_mul (rot (-1971 / 25000))
  rw [show slitsA' = (fun z : ℂ => rot (-1971 / 25000) * sA4 z) from rfl]
  exact h

/-- The lune slope `(c²-1)/(c²+1)` for `c = 36/5`, as a real number. -/
noncomputable def Lune : ℝ := ((36 / 5 : ℝ) ^ 2 - 1) / ((36 / 5 : ℝ) ^ 2 + 1)

theorem lune_deriv_36 : HasDerivAt (lune (36 / 5)) ((Lune : ℝ) : ℂ) 0 := by
  have h := lune_deriv_zero' (36 / 5) (by norm_num)
  rw [show ((36 / 5 : ℝ) ^ 2 - 1) / ((36 / 5 : ℝ) ^ 2 + 1) = Lune by rfl] at h
  exact h

theorem psiA_deriv_value : deriv psiA 0 = (((4 / 5 : ℝ) * Lune : ℝ) : ℂ) * W := by
  have hneg : HasDerivAt (fun z : ℂ => -slitsA' z) (-1 * W) 0 := by
    have hh : HasDerivAt (fun z : ℂ => -z) (-1) (slitsA' 0) := by
      rw [show slitsA' 0 = 0 by exact slitsA'_zero]
      exact hasDerivAt_neg' 0
    exact HasDerivAt.comp 0 hh slitsA'_deriv
  have hlune : HasDerivAt (lune (36 / 5)) ((Lune : ℝ) : ℂ)
      ((fun z : ℂ => -slitsA' z) 0) := by
    rw [show (fun z : ℂ => -slitsA' z) 0 = 0 by simp [slitsA'_zero]]
    exact lune_deriv_36
  have h1 : HasDerivAt (fun z : ℂ => lune (36 / 5) (-slitsA' z))
      (((Lune : ℝ) : ℂ) * (-1 * W)) 0 := by
    change HasDerivAt ((fun w : ℂ => lune (36 / 5) w) ∘ (fun z : ℂ => -slitsA' z))
      (((Lune : ℝ) : ℂ) * (-1 * W)) 0
    exact HasDerivAt.comp 0 hlune hneg
  have h2 : HasDerivAt (fun z : ℂ => -(4 / 5) * lune (36 / 5) (-slitsA' z))
      (-(4 / 5) * (((Lune : ℝ) : ℂ) * (-1 * W))) 0 := h1.const_mul (-(4 / 5))
  have h3 : HasDerivAt psiA (-(4 / 5) * (((Lune : ℝ) : ℂ) * (-1 * W))) 0 := by
    rw [show psiA = (fun z : ℂ => -(4 / 5) * lune (36 / 5) (-slitsA' z)) from by
      funext z; simp only [psiA, slitsA'_eq]]
    exact h2
  rw [h3.deriv]
  push_cast
  ring

theorem psiA_deriv_norm :
    ‖deriv psiA 0‖ = 2383521894760738000000000 / 3774888615849058882987209 := by
  rw [psiA_deriv_value]
  simp only [W, Ds, Lune, norm_mul, norm_rot]
  simp
  norm_num

end Work.ANum
