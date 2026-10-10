/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.KleinTwData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Homogeneity of the ruling data of the T-twisted Crauder–Katz link

The ruling vectors `kleinTwRuleA`, `kleinTwRuleB` of the T-twisted link are quadratic in the
coordinate vector, and the twisted inverse sextic evaluated on the ruling line `A + τ·B` is
homogeneous of degree six.  This file records those homogeneity statements, together with the
`λ²`-homogeneity of the rule vectors in their argument.

The proofs are structural: `kleinTwRuleA/B` are the polarisations of the quadratic Pfaffian map
`kleinTwP` along the tangent vector `kleinTwTan`, which is built from the polar form
`kleinTwBilin` of the T-invariant quadric `kleinTwQ = kleinTwP0`.  Each of these pieces is first
put into an explicit shape (`*_eq`), after which the degree bookkeeping is a chain of
`IsHomogeneous.add/sub/neg/mul/pow` applications with literal degrees; the degrees produced are
definitionally equal to the numerals in the statements.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.MotK.TwRuling

open MvPolynomial

section Homog

variable {A : Type*} [CommRing A]

/-! ### Component (`rfl`) lemmas for the twisted Pfaffian vector -/

private theorem kleinTwP_apply_zero (a b h : A) (y : Fin 5 → A) :
    kleinTwP a b h y 0 = kleinTwP0 a b h y := rfl

private theorem kleinTwP_apply_one (a b h : A) (y : Fin 5 → A) :
    kleinTwP a b h y 1 = kleinTwP1 a b h y := rfl

private theorem kleinTwP_apply_two (a b h : A) (y : Fin 5 → A) :
    kleinTwP a b h y 2 = kleinTwP2 a b h y := rfl

private theorem kleinTwP_apply_three (a b h : A) (y : Fin 5 → A) :
    kleinTwP a b h y 3 = kleinTwP3 a b h y := rfl

private theorem kleinTwP_apply_four (a b h : A) (y : Fin 5 → A) :
    kleinTwP a b h y 4 = kleinTwP4 a b h y := rfl

/-! ### Explicit shapes of the twisted Pfaffians and of the inverse sextic -/

private theorem kleinTwP0_eq (a b h : A) (y : Fin 5 → MvPolynomial (Fin 5) A) :
    kleinTwP0 (C a) (C b) (C h) y
      = (-(C a * C b)) * ((y 0) ^ 2) + ((C a ^ 2) * (C h)) * (y 2 * y 3)
        - ((C b ^ 2) * (C h)) * (y 1 * y 4) := by
  simp only [kleinTwP0]
  first | refl_ring1 | ring

private theorem kleinTwP1_eq (a b h : A) (y : Fin 5 → MvPolynomial (Fin 5) A) :
    kleinTwP1 (C a) (C b) (C h) y
      = (-(C a * C b)) * ((y 2) ^ 2) + (C a ^ 2) * (y 0 * y 4)
        - (C b ^ 2) * (y 1 * y 3) := by
  simp only [kleinTwP1]
  first | refl_ring1 | ring

private theorem kleinTwP2_eq (a b h : A) (y : Fin 5 → MvPolynomial (Fin 5) A) :
    kleinTwP2 (C a) (C b) (C h) y
      = (-((C a * C b) * C h)) * ((y 4) ^ 2) + (C a ^ 2) * (y 1 * y 2)
        - (C b ^ 2) * (y 0 * y 3) := by
  simp only [kleinTwP2]
  first | refl_ring1 | ring

private theorem kleinTwP3_eq (a b h : A) (y : Fin 5 → MvPolynomial (Fin 5) A) :
    kleinTwP3 (C a) (C b) (C h) y
      = (-(C a * C b)) * ((y 1) ^ 2) + ((C a ^ 2) * (C h)) * (y 3 * y 4)
        - (C b ^ 2) * (y 0 * y 2) := by
  simp only [kleinTwP3]
  first | refl_ring1 | ring

private theorem kleinTwP4_eq (a b h : A) (y : Fin 5 → MvPolynomial (Fin 5) A) :
    kleinTwP4 (C a) (C b) (C h) y
      = (-((C a * C b) * C h)) * ((y 3) ^ 2) + (C a ^ 2) * (y 0 * y 1)
        - ((C b ^ 2) * C h) * (y 2 * y 4) := by
  simp only [kleinTwP4]
  first | refl_ring1 | ring

private theorem kleinTwR0_eq (a b h : A) (y : Fin 5 → MvPolynomial (Fin 5) A) :
    kleinTwR0 (C a) (C b) (C h) y
      = (-((C a * C b ^ 3) * C h)) * (((y 3) ^ 2) * y 4)
        - ((C a * C b ^ 3) * (C h ^ 2)) * (y 1 * ((y 2) ^ 2))
        + ((C a ^ 2) * (C b ^ 2)) * ((y 0) ^ 3)
        + (((C a ^ 3) * C b) * C h) * (y 2 * ((y 4) ^ 2))
        + (((C a ^ 3) * C b) * (C h ^ 2)) * (((y 1) ^ 2) * y 3)
        - ((C a ^ 4) * C h) * ((y 0 * y 1) * y 4)
        - ((C b ^ 4) * C h) * ((y 0 * y 2) * y 3) := by
  simp only [kleinTwR0]
  first | refl_ring1 | ring

/-! ### Homogeneity of the twisted Pfaffians and of the inverse sextic -/

private theorem kleinTwP0_isHomogeneous (a b h : A) (y : Fin 5 → MvPolynomial (Fin 5) A)
    (hy : ∀ j, (y j).IsHomogeneous 1) :
    (kleinTwP0 (C a) (C b) (C h) y).IsHomogeneous 2 := by
  have h0 := hy 0; have h1 := hy 1; have h2 := hy 2; have h3 := hy 3; have h4 := hy 4
  rw [kleinTwP0_eq]
  exact IsHomogeneous.sub
    (IsHomogeneous.add
      (((isHomogeneous_C (Fin 5) a).mul (isHomogeneous_C (Fin 5) b)).neg.mul (h0.pow 2))
      ((((isHomogeneous_C (Fin 5) a).pow 2).mul
        (isHomogeneous_C (Fin 5) h)).mul (h2.mul h3)))
    ((((isHomogeneous_C (Fin 5) b).pow 2).mul
      (isHomogeneous_C (Fin 5) h)).mul (h1.mul h4))

private theorem kleinTwP1_isHomogeneous (a b h : A) (y : Fin 5 → MvPolynomial (Fin 5) A)
    (hy : ∀ j, (y j).IsHomogeneous 1) :
    (kleinTwP1 (C a) (C b) (C h) y).IsHomogeneous 2 := by
  have h0 := hy 0; have h1 := hy 1; have h2 := hy 2; have h3 := hy 3; have h4 := hy 4
  rw [kleinTwP1_eq]
  exact IsHomogeneous.sub
    (IsHomogeneous.add
      (((isHomogeneous_C (Fin 5) a).mul (isHomogeneous_C (Fin 5) b)).neg.mul (h2.pow 2))
      (((isHomogeneous_C (Fin 5) a).pow 2).mul (h0.mul h4)))
    (((isHomogeneous_C (Fin 5) b).pow 2).mul (h1.mul h3))

private theorem kleinTwP2_isHomogeneous (a b h : A) (y : Fin 5 → MvPolynomial (Fin 5) A)
    (hy : ∀ j, (y j).IsHomogeneous 1) :
    (kleinTwP2 (C a) (C b) (C h) y).IsHomogeneous 2 := by
  have h0 := hy 0; have h1 := hy 1; have h2 := hy 2; have h3 := hy 3; have h4 := hy 4
  rw [kleinTwP2_eq]
  exact IsHomogeneous.sub
    (IsHomogeneous.add
      ((((isHomogeneous_C (Fin 5) a).mul (isHomogeneous_C (Fin 5) b)).mul
        (isHomogeneous_C (Fin 5) h)).neg.mul (h4.pow 2))
      (((isHomogeneous_C (Fin 5) a).pow 2).mul (h1.mul h2)))
    (((isHomogeneous_C (Fin 5) b).pow 2).mul (h0.mul h3))

private theorem kleinTwP3_isHomogeneous (a b h : A) (y : Fin 5 → MvPolynomial (Fin 5) A)
    (hy : ∀ j, (y j).IsHomogeneous 1) :
    (kleinTwP3 (C a) (C b) (C h) y).IsHomogeneous 2 := by
  have h0 := hy 0; have h1 := hy 1; have h2 := hy 2; have h3 := hy 3; have h4 := hy 4
  rw [kleinTwP3_eq]
  exact IsHomogeneous.sub
    (IsHomogeneous.add
      (((isHomogeneous_C (Fin 5) a).mul (isHomogeneous_C (Fin 5) b)).neg.mul (h1.pow 2))
      ((((isHomogeneous_C (Fin 5) a).pow 2).mul
        (isHomogeneous_C (Fin 5) h)).mul (h3.mul h4)))
    (((isHomogeneous_C (Fin 5) b).pow 2).mul (h0.mul h2))

private theorem kleinTwP4_isHomogeneous (a b h : A) (y : Fin 5 → MvPolynomial (Fin 5) A)
    (hy : ∀ j, (y j).IsHomogeneous 1) :
    (kleinTwP4 (C a) (C b) (C h) y).IsHomogeneous 2 := by
  have h0 := hy 0; have h1 := hy 1; have h2 := hy 2; have h3 := hy 3; have h4 := hy 4
  rw [kleinTwP4_eq]
  exact IsHomogeneous.sub
    (IsHomogeneous.add
      ((((isHomogeneous_C (Fin 5) a).mul (isHomogeneous_C (Fin 5) b)).mul
        (isHomogeneous_C (Fin 5) h)).neg.mul (h3.pow 2))
      (((isHomogeneous_C (Fin 5) a).pow 2).mul (h0.mul h1)))
    ((((isHomogeneous_C (Fin 5) b).pow 2).mul
      (isHomogeneous_C (Fin 5) h)).mul (h2.mul h4))

private theorem kleinTwR0_isHomogeneous (a b h : A) (y : Fin 5 → MvPolynomial (Fin 5) A)
    (hy : ∀ j, (y j).IsHomogeneous 2) :
    (kleinTwR0 (C a) (C b) (C h) y).IsHomogeneous 6 := by
  have h0 := hy 0; have h1 := hy 1; have h2 := hy 2; have h3 := hy 3; have h4 := hy 4
  rw [kleinTwR0_eq]
  exact IsHomogeneous.sub
    (IsHomogeneous.sub
      (IsHomogeneous.add
        (IsHomogeneous.add
          (IsHomogeneous.add
            (IsHomogeneous.sub
              ((((isHomogeneous_C (Fin 5) a).mul
                ((isHomogeneous_C (Fin 5) b).pow 3)).mul
                  (isHomogeneous_C (Fin 5) h)).neg.mul ((h3.pow 2).mul h4))
              ((((isHomogeneous_C (Fin 5) a).mul
                ((isHomogeneous_C (Fin 5) b).pow 3)).mul
                  ((isHomogeneous_C (Fin 5) h).pow 2)).mul (h1.mul (h2.pow 2))))
            ((((isHomogeneous_C (Fin 5) a).pow 2).mul
              ((isHomogeneous_C (Fin 5) b).pow 2)).mul (h0.pow 3)))
          (((((isHomogeneous_C (Fin 5) a).pow 3).mul
            (isHomogeneous_C (Fin 5) b)).mul (isHomogeneous_C (Fin 5) h)).mul
              (h2.mul (h4.pow 2))))
        (((((isHomogeneous_C (Fin 5) a).pow 3).mul
          (isHomogeneous_C (Fin 5) b)).mul ((isHomogeneous_C (Fin 5) h).pow 2)).mul
            ((h1.pow 2).mul h3)))
      ((((isHomogeneous_C (Fin 5) a).pow 4).mul
        (isHomogeneous_C (Fin 5) h)).mul ((h0.mul h1).mul h4)))
    ((((isHomogeneous_C (Fin 5) b).pow 4).mul
      (isHomogeneous_C (Fin 5) h)).mul ((h0.mul h2).mul h3))

/-! ### The polar form of the T-invariant quadric -/

/-- Explicit shape of the polar form `kleinTwBilin` of the T-invariant quadric
`q = kleinTwP0 = kleinTwQ`.  The factor `-2·C a·C b` of `q` is written as `-ab - ab`, so that no
numeral appears. -/
private theorem kleinTwBilin_eq (a b h : A) (u v : Fin 5 → MvPolynomial (Fin 5) A) :
    kleinTwBilin (C a) (C b) (C h) u v
      = ((-(C a * C b)) - (C a * C b)) * (u 0 * v 0)
        + ((C a ^ 2) * (C h)) * (u 2 * v 3 + u 3 * v 2)
        - ((C b ^ 2) * (C h)) * (u 1 * v 4 + u 4 * v 1) := by
  simp only [kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply]
  first | refl_ring1 | ring

private theorem kleinTwBilin_isHomogeneous (a b h : A) (u v : Fin 5 → MvPolynomial (Fin 5) A)
    (hu : ∀ j, (u j).IsHomogeneous 1) (hv : ∀ j, (v j).IsHomogeneous 0) :
    (kleinTwBilin (C a) (C b) (C h) u v).IsHomogeneous 1 := by
  have h0 := hu 0; have h1 := hu 1; have h2 := hu 2; have h3 := hu 3; have h4 := hu 4
  have k0 := hv 0; have k1 := hv 1; have k2 := hv 2; have k3 := hv 3; have k4 := hv 4
  rw [kleinTwBilin_eq]
  exact IsHomogeneous.sub
    (IsHomogeneous.add
      ((((isHomogeneous_C (Fin 5) a).mul (isHomogeneous_C (Fin 5) b)).neg.sub
        ((isHomogeneous_C (Fin 5) a).mul (isHomogeneous_C (Fin 5) b))).mul (h0.mul k0))
      ((((isHomogeneous_C (Fin 5) a).pow 2).mul
        (isHomogeneous_C (Fin 5) h)).mul
          (IsHomogeneous.add (h2.mul k3) (h3.mul k2))))
    ((((isHomogeneous_C (Fin 5) b).pow 2).mul
      (isHomogeneous_C (Fin 5) h)).mul
        (IsHomogeneous.add (h1.mul k4) (h4.mul k1)))

/-! ### The tangent vector of the T-invariant quadric -/

/-- The components of the standard basis vectors `kleinE k` are constants. -/
private theorem kleinE_isHomogeneous (k j : Fin 5) :
    ((kleinE k : Fin 5 → MvPolynomial (Fin 5) A) j).IsHomogeneous 0 := by
  have hval : (kleinE k : Fin 5 → MvPolynomial (Fin 5) A) j
      = (if j = k then (1 : MvPolynomial (Fin 5) A) else 0) :=
    Pi.single_apply k (1 : MvPolynomial (Fin 5) A) j
  rw [hval]
  by_cases h : j = k
  · rw [if_pos h]; exact isHomogeneous_one (Fin 5) A
  · rw [if_neg h]; exact isHomogeneous_zero (Fin 5) A 0

private theorem kleinTwTan_isHomogeneous (a b h : A) (c : Fin 5 → MvPolynomial (Fin 5) A)
    (hc : ∀ j, (c j).IsHomogeneous 1) (k i : Fin 5) :
    (kleinTwTan (C a) (C b) (C h) c k i).IsHomogeneous 1 := by
  have hk : (kleinTwBilin (C a) (C b) (C h) c (kleinE k)).IsHomogeneous 1 :=
    kleinTwBilin_isHomogeneous a b h c (kleinE k) hc (fun j => kleinE_isHomogeneous k j)
  have h0 : (kleinTwBilin (C a) (C b) (C h) c (kleinE 0)).IsHomogeneous 1 :=
    kleinTwBilin_isHomogeneous a b h c (kleinE 0) hc (fun j => kleinE_isHomogeneous 0 j)
  have e0i : ((kleinE (0 : Fin 5) : Fin 5 → MvPolynomial (Fin 5) A) i).IsHomogeneous 0 :=
    kleinE_isHomogeneous 0 i
  have eki : ((kleinE k : Fin 5 → MvPolynomial (Fin 5) A) i).IsHomogeneous 0 :=
    kleinE_isHomogeneous k i
  exact (hk.mul e0i).sub (h0.mul eki)

/-! ### The ruling vectors -/

private theorem kleinTwP_isHomogeneous (a b h : A) (y : Fin 5 → MvPolynomial (Fin 5) A)
    (hy : ∀ j, (y j).IsHomogeneous 1) (i : Fin 5) :
    (kleinTwP (C a) (C b) (C h) y i).IsHomogeneous 2 := by
  fin_cases i
  · exact kleinTwP0_isHomogeneous a b h y hy
  · exact kleinTwP1_isHomogeneous a b h y hy
  · exact kleinTwP2_isHomogeneous a b h y hy
  · exact kleinTwP3_isHomogeneous a b h y hy
  · exact kleinTwP4_isHomogeneous a b h y hy

private theorem kleinTwPolarP_isHomogeneous (a b h : A) (c u : Fin 5 → MvPolynomial (Fin 5) A)
    (hc : ∀ j, (c j).IsHomogeneous 1) (hu : ∀ j, (u j).IsHomogeneous 1) (i : Fin 5) :
    (kleinTwPolarP (C a) (C b) (C h) c u i).IsHomogeneous 2 := by
  have hcu : ∀ j : Fin 5, ((c + u) j).IsHomogeneous 1 := by
    intro j
    rw [Pi.add_apply]
    exact (hc j).add (hu j)
  exact ((kleinTwP_isHomogeneous a b h (c + u) hcu i).sub
    (kleinTwP_isHomogeneous a b h c hc i)).sub (kleinTwP_isHomogeneous a b h u hu i)

private theorem kleinTwRuleA_isHomogeneous (a b h : A) (i : Fin 5) :
    (kleinTwRuleA (C a) (C b) (C h) (fun j => X j) i).IsHomogeneous 2 := by
  have hX : ∀ j : Fin 5,
      (((fun j => X j) : Fin 5 → MvPolynomial (Fin 5) A) j).IsHomogeneous 1 :=
    fun j => isHomogeneous_X A j
  have htan : ∀ j : Fin 5,
      (kleinTwTan (C a) (C b) (C h) (fun j => X j) 1 j).IsHomogeneous 1 :=
    fun j => kleinTwTan_isHomogeneous a b h (fun j => X j) hX 1 j
  exact kleinTwPolarP_isHomogeneous a b h (fun j => X j)
    (kleinTwTan (C a) (C b) (C h) (fun j => X j) 1) hX htan i

private theorem kleinTwRuleB_isHomogeneous (a b h : A) (i : Fin 5) :
    (kleinTwRuleB (C a) (C b) (C h) (fun j => X j) i).IsHomogeneous 2 := by
  have hX : ∀ j : Fin 5,
      (((fun j => X j) : Fin 5 → MvPolynomial (Fin 5) A) j).IsHomogeneous 1 :=
    fun j => isHomogeneous_X A j
  have htan : ∀ j : Fin 5,
      (kleinTwTan (C a) (C b) (C h) (fun j => X j) 2 j).IsHomogeneous 1 :=
    fun j => kleinTwTan_isHomogeneous a b h (fun j => X j) hX 2 j
  exact kleinTwPolarP_isHomogeneous a b h (fun j => X j)
    (kleinTwTan (C a) (C b) (C h) (fun j => X j) 2) hX htan i

/-! ### `λ²`-homogeneity of the data in the coordinate vector -/

private theorem kleinTwP0_smul (a b h lam : A) (y : Fin 5 → A) :
    kleinTwP0 a b h (fun i => lam * y i) = lam ^ 2 * kleinTwP0 a b h y := by
  simp only [kleinTwP0]
  first | refl_ring1 | ring

private theorem kleinTwP1_smul (a b h lam : A) (y : Fin 5 → A) :
    kleinTwP1 a b h (fun i => lam * y i) = lam ^ 2 * kleinTwP1 a b h y := by
  simp only [kleinTwP1]
  first | refl_ring1 | ring

private theorem kleinTwP2_smul (a b h lam : A) (y : Fin 5 → A) :
    kleinTwP2 a b h (fun i => lam * y i) = lam ^ 2 * kleinTwP2 a b h y := by
  simp only [kleinTwP2]
  first | refl_ring1 | ring

private theorem kleinTwP3_smul (a b h lam : A) (y : Fin 5 → A) :
    kleinTwP3 a b h (fun i => lam * y i) = lam ^ 2 * kleinTwP3 a b h y := by
  simp only [kleinTwP3]
  first | refl_ring1 | ring

private theorem kleinTwP4_smul (a b h lam : A) (y : Fin 5 → A) :
    kleinTwP4 a b h (fun i => lam * y i) = lam ^ 2 * kleinTwP4 a b h y := by
  simp only [kleinTwP4]
  first | refl_ring1 | ring

private theorem kleinTwP_smul_zero (a b h lam : A) (y : Fin 5 → A) :
    kleinTwP a b h (fun i => lam * y i) 0 = lam ^ 2 * kleinTwP a b h y 0 := by
  simp only [kleinTwP_apply_zero]
  exact kleinTwP0_smul a b h lam y

private theorem kleinTwP_smul_one (a b h lam : A) (y : Fin 5 → A) :
    kleinTwP a b h (fun i => lam * y i) 1 = lam ^ 2 * kleinTwP a b h y 1 := by
  simp only [kleinTwP_apply_one]
  exact kleinTwP1_smul a b h lam y

private theorem kleinTwP_smul_two (a b h lam : A) (y : Fin 5 → A) :
    kleinTwP a b h (fun i => lam * y i) 2 = lam ^ 2 * kleinTwP a b h y 2 := by
  simp only [kleinTwP_apply_two]
  exact kleinTwP2_smul a b h lam y

private theorem kleinTwP_smul_three (a b h lam : A) (y : Fin 5 → A) :
    kleinTwP a b h (fun i => lam * y i) 3 = lam ^ 2 * kleinTwP a b h y 3 := by
  simp only [kleinTwP_apply_three]
  exact kleinTwP3_smul a b h lam y

private theorem kleinTwP_smul_four (a b h lam : A) (y : Fin 5 → A) :
    kleinTwP a b h (fun i => lam * y i) 4 = lam ^ 2 * kleinTwP a b h y 4 := by
  simp only [kleinTwP_apply_four]
  exact kleinTwP4_smul a b h lam y

private theorem kleinTwP_smul (a b h lam : A) (y : Fin 5 → A) :
    kleinTwP a b h (fun i => lam * y i) = fun i => lam ^ 2 * kleinTwP a b h y i := by
  funext i
  fin_cases i
  · exact kleinTwP_smul_zero a b h lam y
  · exact kleinTwP_smul_one a b h lam y
  · exact kleinTwP_smul_two a b h lam y
  · exact kleinTwP_smul_three a b h lam y
  · exact kleinTwP_smul_four a b h lam y

private theorem kleinTwBilin_smul_left (a b h lam : A) (u v : Fin 5 → A) :
    kleinTwBilin a b h (fun i => lam * u i) v = lam * kleinTwBilin a b h u v := by
  simp only [kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply]
  first | refl_ring1 | ring

private theorem kleinTwTan_smul (a b h lam : A) (c : Fin 5 → A) (k : Fin 5) :
    kleinTwTan a b h (fun i => lam * c i) k = fun i => lam * kleinTwTan a b h c k i := by
  funext i
  simp only [kleinTwTan, kleinTwBilin_smul_left]
  first | refl_ring1 | ring

private theorem kleinTwPolarP_smul (a b h lam : A) (c u : Fin 5 → A) :
    kleinTwPolarP a b h (fun i => lam * c i) (fun i => lam * u i)
      = fun i => lam ^ 2 * kleinTwPolarP a b h c u i := by
  have h1 : (fun i => lam * c i) + (fun i => lam * u i) = fun i => lam * (c + u) i := by
    funext j
    simp only [Pi.add_apply]
    first | refl_ring1 | ring
  funext i
  simp only [kleinTwPolarP, h1, kleinTwP_smul]
  first | refl_ring1 | ring

private theorem kleinTwRuleA_smul (a b h lam : A) (c : Fin 5 → A) :
    kleinTwRuleA a b h (fun i => lam * c i) = fun i => lam ^ 2 * kleinTwRuleA a b h c i := by
  funext i
  simp only [kleinTwRuleA, kleinTwTan_smul, kleinTwPolarP_smul]

private theorem kleinTwRuleB_smul (a b h lam : A) (c : Fin 5 → A) :
    kleinTwRuleB a b h (fun i => lam * c i) = fun i => lam ^ 2 * kleinTwRuleB a b h c i := by
  funext i
  simp only [kleinTwRuleB, kleinTwTan_smul, kleinTwPolarP_smul]

end Homog

theorem SdSextHomog {R : Type*} [CommRing R] (a b h τ : R) :
    (∀ i : Fin 5, (Work.MotK.kleinTwRuleA (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun j => MvPolynomial.X j) i).IsHomogeneous 2) ∧
    (∀ i : Fin 5, (Work.MotK.kleinTwRuleB (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun j => MvPolynomial.X j) i).IsHomogeneous 2) ∧
    (Work.MotK.kleinTwR0 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1)
      (fun i => Work.MotK.kleinTwRuleA (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1)
          (fun j => MvPolynomial.X j) i
        + MvPolynomial.C τ * Work.MotK.kleinTwRuleB (MvPolynomial.C a) (MvPolynomial.C b)
          (MvPolynomial.C 1) (fun j => MvPolynomial.X j) i)).IsHomogeneous 6 ∧
    (∀ (c : Fin 5 → R) (lam : R), Work.MotK.kleinTwRuleA a b h (fun i => lam * c i)
        = fun i => lam ^ 2 * Work.MotK.kleinTwRuleA a b h c i) ∧
    (∀ (c : Fin 5 → R) (lam : R), Work.MotK.kleinTwRuleB a b h (fun i => lam * c i)
        = fun i => lam ^ 2 * Work.MotK.kleinTwRuleB a b h c i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact kleinTwRuleA_isHomogeneous a b h i
  · intro i
    exact kleinTwRuleB_isHomogeneous a b h i
  · have hy : ∀ i : Fin 5,
        (Work.MotK.kleinTwRuleA (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C 1)
            (fun j => MvPolynomial.X j) i
          + MvPolynomial.C τ * Work.MotK.kleinTwRuleB (MvPolynomial.C a) (MvPolynomial.C b)
            (MvPolynomial.C 1) (fun j => MvPolynomial.X j) i).IsHomogeneous 2 :=
      fun i => (kleinTwRuleA_isHomogeneous a b 1 i).add
        ((isHomogeneous_C (Fin 5) τ).mul (kleinTwRuleB_isHomogeneous a b 1 i))
    exact kleinTwR0_isHomogeneous a b 1 _ hy
  · intro c lam
    exact kleinTwRuleA_smul a b h lam c
  · intro c lam
    exact kleinTwRuleB_smul a b h lam c

end Work.MotK.TwRuling
