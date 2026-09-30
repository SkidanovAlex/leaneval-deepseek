import Mathlib
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Filtered cochain complexes with a compatible product (vocabulary for area MSS)

A `CohFilt 𝕜` is a cochain complex of `𝕜`-modules together with a decreasing filtration by
subcomplexes `F^s` (`F^0 = C`, `F^{n+1}C^n = 0`) and a product which respects the filtration and
satisfies the Leibniz rule.  This is the input of the construction of the cohomological Serre
spectral sequence over a field; the concrete instantiation for a Serre fibration is the Serre
cochain filtration `Work.Pi6.MSS.coFilt` of `Submission/Work/Pi6/MSS/Defs.lean`.

The Leibniz sign is the one of `Work.Pi6.CohSS`: for `x` in degree `n`, the second term acquires
the sign `(-1)^n`.  The degrees of the two terms on the right are `(n+1)+m` and `n+(m+1)`, which
are equal to `n+m+1` only up to a propositional equality; the corresponding transports
(`Work.Pi6.MSS.CohFilt.xcast`) appear explicitly.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- A **filtered cochain complex with a compatible product**.  `F s n` is the `s`-th filtration
step in cohomological degree `n`; `mul n m` is the product `C^n × C^m → C^{n+m}`. -/
structure CohFilt (𝕜 : Type) [CommRing 𝕜] where
  /-- the ambient cochain complex -/
  C : CochainComplex (ModuleCat 𝕜) ℕ
  /-- the filtration -/
  F : ℕ → ∀ n : ℕ, Submodule 𝕜 (C.X n)
  /-- the filtration is decreasing -/
  F_mono : ∀ s n : ℕ, F (s+1) n ≤ F s n
  /-- `F^0 = C` -/
  F_zero : ∀ n : ℕ, F 0 n = ⊤
  /-- the top of the filtration vanishes: `F^{n+1} C^n = 0` -/
  F_top : ∀ n : ℕ, F (n+1) n = ⊥
  /-- the filtration is by subcomplexes -/
  F_leib : ∀ (s n : ℕ) (x : C.X n), x ∈ F s n → (C.d n (n+1)).hom x ∈ F s (n+1)
  /-- the product -/
  mul : ∀ n m : ℕ, C.X n →ₗ[𝕜] C.X m →ₗ[𝕜] C.X (n + m)
  /-- the product respects the filtration -/
  mul_filt : ∀ (s s' n m : ℕ) (x : C.X n) (y : C.X m), x ∈ F s n → y ∈ F s' m →
    mul n m x y ∈ F (s + s') (n + m)
  /-- the Leibniz rule, with the sign of the cochain complex -/
  mul_leib : ∀ (n m : ℕ) (e₁ : (n+1) + m = n + m + 1) (e₂ : n + (m+1) = n + m + 1)
    (x : C.X n) (y : C.X m),
    (C.d (n+m) (n+m+1)).hom (mul n m x y) =
      (eqToHom (congrArg C.X e₁)).hom (mul (n+1) m ((C.d n (n+1)).hom x) y)
        + (-1 : 𝕜) ^ n •
          (eqToHom (congrArg C.X e₂)).hom (mul n (m+1) x ((C.d m (m+1)).hom y))

namespace CohFilt

variable {𝕜 : Type} [CommRing 𝕜] (W : CohFilt 𝕜)

/-- The differential `C^n → C^{n+1}` as a linear map. -/
def d (n : ℕ) : W.C.X n →ₗ[𝕜] W.C.X (n+1) := (W.C.d n (n+1)).hom

/-- The differential `C^{n-1} → C^n` as a linear map. -/
def dPrev (n : ℕ) : W.C.X (n-1) →ₗ[𝕜] W.C.X n := (W.C.d (n-1) n).hom

/-- Transport of an element of `C^a` to `C^b` along an equality of degrees. -/
def xcast {a b : ℕ} (h : a = b) : W.C.X a →ₗ[𝕜] W.C.X b :=
  (eqToHom (congrArg W.C.X h)).hom

@[simp] theorem xcast_rfl {a : ℕ} : (W.xcast (rfl : a = a)) = LinearMap.id := by
  ext x; rfl

theorem xcast_trans {a b c : ℕ} (h : a = b) (h' : b = c) :
    (W.xcast h').comp (W.xcast h) = W.xcast (h.trans h') := by
  subst h h'; simp

/-- The Leibniz rule, in the form used in the construction of the pages. -/
theorem mul_leib' (n m : ℕ) (x : W.C.X n) (y : W.C.X m) :
    W.d (n+m) (W.mul n m x y) =
      W.xcast (by omega) (W.mul (n+1) m (W.d n x) y)
        + (-1 : 𝕜) ^ n • W.xcast (by omega) (W.mul n (m+1) x (W.d m y)) :=
  W.mul_leib n m (by omega) (by omega) x y

end CohFilt

end

end Work.Pi6.MSS
