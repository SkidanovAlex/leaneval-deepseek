/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.ChartDefs
import Submission.Work.MotK.TGen.KleinTwRChart0
import Submission.Work.MotK.TGen.KleinTwFhomPi

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Phi0GambT` — the dehomogenised *inverse* unit condition of the affine T-twisted link

`Phi0 a b h : K[x₀,x₁,x₂] →ₐ[K] R[1/Gdiv]` is the pullback of the inverse link map `χ = π_p ∘ R`
on the affine chart, i.e. `MvPolynomial.aeval (psiG a b h)` where `psiG` are the chart coordinates
`(0, ǧ₁/ǧ₄, ǧ₂/ǧ₄, ǧ₃/ǧ₄, 1) = (1/ǧ₄)·ǧ`.

The target evaluates `Phi0` on the source equation `GambT = F_hom(p, ·)|_{chart}` and identifies the
result:

  `Phi0 GambT = (1/ǧ₄)^11 · ( -b(p, ǧ)^5 · s'(chart)^2 · FambT )`,

where `ǧ = bwVec`, `FambT = G_hom(p, ·)|_{chart}`, and `1/ǧ₄ = invG4`.

The proof is the chain

* `Phi0 GambT = kleinTwFhom p (x ↦ invG4 · ǧ(x))` — the chart substitution `x ↦ psiG` is the
  vector `invG4 · ǧ`, and `aeval` commutes with the polynomial expression `kleinTwFhom`;
* homogeneity of `kleinTwFhom` in its vector argument (`kleinTwFhom_smul`) pulls out
  `invG4^11`;
* `ǧ = π_p (R chart)` and `π_p` does not change `kleinTwFhom` on the quadric
  (`KleinTwFhomPi`), nor the polar form `b(p, ·)` (`kleinTwBilin_pi_eq`);
* the second unit condition `FambT_unit` (`kleinTwFhom_kleinTwR`) rewrites
  `kleinTwFhom p (R chart)` as `-b(p,R chart)^5 · s'(chart)^2 · FambT`.

The two auxiliary lemmas below record that `kleinTwFhom` is a polynomial expression (integer
coefficients, no division) in its arguments, hence commutes with `aeval` and with any ring
homomorphism.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

/-- `MvPolynomial.aeval` commutes with the source equation `kleinTwFhom` of the T-twist: the
latter is a polynomial expression in its arguments, so it is respected by evaluation. -/
lemma aeval_kleinTwFhom_g {σ K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (a b h : MvPolynomial σ K) (p v : Fin 5 → MvPolynomial σ K) (y : σ → A) :
    MvPolynomial.aeval y (Work.MotK.kleinTwFhom a b h p v)
      = Work.MotK.kleinTwFhom (MvPolynomial.aeval y a) (MvPolynomial.aeval y b)
          (MvPolynomial.aeval y h) (fun i => MvPolynomial.aeval y (p i))
          (fun i => MvPolynomial.aeval y (v i)) := by
  simp only [Work.MotK.kleinTwFhom, Work.MotK.kleinTwBilin, Work.MotK.kleinTwQ,
    Work.MotK.kleinTwP0, Work.MotK.kleinTwStereo, Work.MotK.kleinTwS, Pi.add_apply, Pi.sub_apply]
  simp

/-- Any ring homomorphism commutes with the polynomial expression `kleinTwFhom`. -/
lemma map_kleinTwFhom_g {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b h : R) (p v : Fin 5 → R) :
    Work.MotK.kleinTwFhom (f a) (f b) (f h) (fun i => f (p i)) (fun i => f (v i))
      = f (Work.MotK.kleinTwFhom a b h p v) := by
  simp only [Work.MotK.kleinTwFhom, Work.MotK.kleinTwBilin, Work.MotK.kleinTwQ,
    Work.MotK.kleinTwP0, Work.MotK.kleinTwStereo, Work.MotK.kleinTwS, Pi.add_apply,
    Pi.sub_apply, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]

theorem Phi0GambT {K : Type} [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Phi0 a b h (GambT a b h)
      = invG4 a b h ^ 11 *
          algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
            (-(kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h)
                  (bwVec a b h)) ^ 5 *
              kleinTwSDualV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (chart3 K) ^ 2 *
              FambT a b h) := by
  -- `aeval (psiG) (C c) = algebraMap R[1/Gdiv] (C c)`
  have hAa : ∀ c : K, MvPolynomial.aeval (psiG a b h) (MvPolynomial.C c)
      = algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h)) (MvPolynomial.C c) := by
    intro c
    rw [MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq]
    exact IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K)
      (Localization.Away (Gdiv a b h)) c
  have hpR : (fun i : Fin 5 => MvPolynomial.aeval (psiG a b h) (pRa a b h i))
      = fun i => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
          (pRa a b h i) := by
    funext i
    rw [pRa_apply]
    exact hAa _
  -- the chart substitution `x ↦ psiG` is the vector `invG4 · ǧ`
  have hchart : (fun i : Fin 5 => MvPolynomial.aeval (psiG a b h) (chart3 K i))
      = fun i => invG4 a b h *
          algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h)) (bwVec a b h i) := by
    funext i
    fin_cases i <;> simp [chart3, psiG, bwVec_zero a b h, invG4_mul_bwVec4 a b h]
  -- the chart-level unit condition, before the identification of `ǧ` with `R chart`
  have hA : Phi0 a b h (GambT a b h)
      = invG4 a b h ^ 11 *
          algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
            (Work.MotK.kleinTwFhom (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
              (pRa a b h) (bwVec a b h)) := by
    have hstep1 : Phi0 a b h (GambT a b h)
        = Work.MotK.kleinTwFhom
            (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
              (MvPolynomial.C a))
            (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
              (MvPolynomial.C b))
            (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
              (MvPolynomial.C h))
            (fun i => algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
              (pRa a b h i))
            (fun i => invG4 a b h * algebraMap (MvPolynomial (Fin 3) K)
              (Localization.Away (Gdiv a b h)) (bwVec a b h i)) := by
      rw [Phi0, GambT,
        aeval_kleinTwFhom_g (a := MvPolynomial.C a) (b := MvPolynomial.C b)
          (h := MvPolynomial.C h) (p := pRa a b h) (v := chart3 K) (y := psiG a b h)]
      rw [hAa a, hAa b, hAa h, hpR, hchart]
    rw [hstep1, Work.MotK.kleinTwFhom_smul,
      ← map_kleinTwFhom_g (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h)))
        (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (pRa a b h) (bwVec a b h)]
  -- identify `kleinTwFhom p ǧ` with the target equation via the inverse unit condition
  have hF : algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
        (Work.MotK.kleinTwFhom (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (pRa a b h) (bwVec a b h))
      = algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
          (-(Work.MotK.kleinTwBilin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
                (pRa a b h) (bwVec a b h)) ^ 5 *
            Work.MotK.kleinTwSDualV (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
              (chart3 K) ^ 2 *
            FambT a b h) := by
    rw [show bwVec a b h = Work.MotK.kleinTwPi (pRa a b h)
          (Work.MotK.kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (chart3 K)) from rfl,
      KleinTwFhomPi _ _ _ _ _ (Work.MotK.kleinTwQ_pRa a b h ha hh),
      Work.MotK.FambT_unit a b h (KleinTwRChart0 a b h ha hb hh),
      ← Work.MotK.kleinTwBilin_pi_eq _ _ _ _ _ (Work.MotK.kleinTwQ_pRa a b h ha hh),
      show Work.MotK.kleinTwPi (pRa a b h)
          (Work.MotK.kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (chart3 K)) = bwVec a b h from rfl]
  rw [hA, hF]

end Work.MotK.TGen
