import Mathlib
import Submission.Work.ZassenhausSuzuki.exists_k_center
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.szTilde_conj
import Submission.Work.ZassenhausSuzuki.canon_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Vocabulary for the `∼`-product formula `tilde_tilde_center_zs`

This module only fixes the definitions used by the proof of
`Work.ZassenhausSuzuki.tilde_tilde_center_zs` (the `∼`-product formula, BG 5.12 replacement),
on top of the conjugation/`lamOf` machinery of `Work.ZassenhausSuzuki.exists_k_center`:

* `conjQ hsplit d x` — the conjugation `d · x · d⁻¹` of `x ∈ Q` by `d ∈ D = twoPoint H t`
  (from `exists_k_center`);
* `mulD hsplit htorus d = λ_d · θλ_d` where `λ_d = lamOf hsplit htorus d` is the torus
  parameter by which `d ∈ D` acts on `Q`.  This is the *multiplier* of `d` on the centre
  `Z(Q)`: `d · z_b · d⁻¹ = z_{mulD d · b}` where `z_b = zc e b`, and `mulD` is multiplicative.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## Elementary properties of `conjQ` -/

theorem conjQ_one (hsplit : IsSplitRankOne H Q t) (d : twoPoint H t) :
    conjQ hsplit d (1 : Q) = 1 := by
  apply Subtype.ext
  simp [conjQ_coe]

theorem conjQ_inv (hsplit : IsSplitRankOne H Q t) (d : twoPoint H t) (x : Q) :
    conjQ hsplit d x⁻¹ = (conjQ hsplit d x)⁻¹ := by
  apply Subtype.ext
  simp only [conjQ_coe, Subgroup.coe_inv]
  group

theorem conjQ_conjQ_inv (hsplit : IsSplitRankOne H Q t) (d : twoPoint H t) (x : Q) :
    conjQ hsplit d⁻¹ (conjQ hsplit d x) = x := by
  apply Subtype.ext
  simp only [conjQ_coe, Subgroup.coe_inv]
  group

variable {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m}
  {e : Q ≃* SzA (GaloisField 2 m) θ}

/-- The *multiplier* of `d ∈ D` on the centre of the root group: `d · z_b · d⁻¹ = z_{mulD d · b}`
for `z_b = zc e b`. -/
noncomputable def mulD (hsplit : IsSplitRankOne H Q t)
    (htorus : ∀ d : G, d ∈ twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = SzA.hLam θ (lam : GaloisField 2 m) (e x))
    (d : twoPoint H t) : GaloisField 2 m :=
  (lamOf hsplit htorus d : GaloisField 2 m) * θ (lamOf hsplit htorus d : GaloisField 2 m)

theorem mulD_ne_zero (hsplit : IsSplitRankOne H Q t)
    (htorus : ∀ d : G, d ∈ twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = SzA.hLam θ (lam : GaloisField 2 m) (e x))
    (d : twoPoint H t) : mulD hsplit htorus d ≠ 0 := by
  unfold mulD
  exact mul_ne_zero (Units.ne_zero _)
    (θ.map_ne_zero_iff.mpr (Units.ne_zero _))

/-- `mulD` is multiplicative. -/
theorem mulD_mul (hsplit : IsSplitRankOne H Q t)
    (htorus : ∀ d : G, d ∈ twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = SzA.hLam θ (lam : GaloisField 2 m) (e x))
    (d₁ d₂ : twoPoint H t) :
    mulD hsplit htorus (d₁ * d₂) = mulD hsplit htorus d₁ * mulD hsplit htorus d₂ := by
  unfold mulD
  rw [lamOf_mul hsplit htorus d₁ d₂, Units.val_mul, map_mul]
  ring

theorem mulD_one (hsplit : IsSplitRankOne H Q t)
    (htorus : ∀ d : G, d ∈ twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = SzA.hLam θ (lam : GaloisField 2 m) (e x)) :
    mulD hsplit htorus (1 : twoPoint H t) = 1 := by
  unfold mulD
  rw [lamOf_one hsplit htorus]
  simp

theorem mulD_inv (hsplit : IsSplitRankOne H Q t)
    (htorus : ∀ d : G, d ∈ twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = SzA.hLam θ (lam : GaloisField 2 m) (e x))
    (d : twoPoint H t) :
    mulD hsplit htorus d⁻¹ = (mulD hsplit htorus d)⁻¹ := by
  have h := mulD_mul hsplit htorus d d⁻¹
  rw [mul_inv_cancel, mulD_one hsplit htorus] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

/-- **The multiplier acts on the centre by multiplication of the index**: for every `d ∈ D` and
every `w`, `d · z_w · d⁻¹ = z_{mulD d · w}`. -/
theorem conjQ_zc (hsplit : IsSplitRankOne H Q t)
    (htorus : ∀ d : G, d ∈ twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = SzA.hLam θ (lam : GaloisField 2 m) (e x))
    (d : twoPoint H t) (w : GaloisField 2 m) :
    conjQ hsplit d (zc e w) = zc e (mulD hsplit htorus d * w) := by
  have h := conjQ_center_spec hsplit htorus d (z := zc e w) (c := w) (zc_coe e w)
  apply e.injective
  rw [h, zc_coe]
  rfl

/-- **Equivariance of the reflection `∼` under `D`, in index form.** -/
theorem conjQ_szTilde_zc (hsplit : IsSplitRankOne H Q t)
    (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (htorus : ∀ d : G, d ∈ twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = SzA.hLam θ (lam : GaloisField 2 m) (e x))
    (d : twoPoint H t) (w : GaloisField 2 m) :
    conjQ hsplit d (szTilde hsplit (zc e w))
      = szTilde hsplit (zc e (mulD hsplit htorus d * w)) := by
  refine Subtype.ext ?_
  rw [← conjQ_zc hsplit htorus d w, conjQ_coe]
  exact (szTilde_conj hsplit hzass h2 d.2 (conjQ_coe hsplit d (zc e w))).symm

/-! ## The Moufang involution `μ_x = t·h(x)` acting on the root group -/

/-- The conjugate `h(x)·y·h(x)⁻¹ ∈ Q` (the local copy of `TitsDesign.conjH`, so that the
`μ_x`-identity can be stated without importing the `unproved`-carrying design file). -/
noncomputable def conjHQ (hsplit : IsSplitRankOne H Q t)
    (C : Work.ZassenhausPSL2.Canon H Q t) (x y : Q) : Q :=
  ⟨hG C x * (y : G) * (hG C x)⁻¹, canon_D_conj_Q_mem hsplit (C.h x) y⟩

/-- The point action of the Moufang involution `μ_x = t·h(x)`: `μ_x y = g(h(x)·y·h(x)⁻¹)`
(this is definitionally `TitsDesign.muPt`). -/
noncomputable def muPtQ (hsplit : IsSplitRankOne H Q t)
    (C : Work.ZassenhausPSL2.Canon H Q t) (x y : Q) : Q :=
  C.g (conjHQ hsplit C x y)

@[simp] theorem conjHQ_coe (hsplit : IsSplitRankOne H Q t)
    (C : Work.ZassenhausPSL2.Canon H Q t) (x y : Q) :
    ((conjHQ hsplit C x y : Q) : G) = hG C x * (y : G) * (hG C x)⁻¹ := rfl


/-! ## The centre of the root group in `e`-coordinates -/

theorem zc_add (e : Q ≃* SzA (GaloisField 2 m) θ) (a b : GaloisField 2 m) :
    zc e a * zc e b = zc e (a + b) := by
  apply e.injective
  rw [map_mul, zc_coe, zc_coe, zc_coe]
  ext <;> simp [SzA.mul_a, SzA.mul_b]

theorem zc_mul_self' (e : Q ≃* SzA (GaloisField 2 m) θ) (a : GaloisField 2 m) :
    zc e a * zc e a = 1 := zc_mul_self e a


end Work.ZassenhausSuzuki
