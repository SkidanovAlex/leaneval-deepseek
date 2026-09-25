import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Core.dbar_sq_zero
import Submission.Work.NN.Final.Transport

namespace Work.NN.Final

open LeanEval.Geometry.NewlanderNirenberg
open Set
open scoped ContDiff

/-!
# `proj02_integrable_flat`: integrability `∂̄² = 0` transported to the flat model `ℂⁿ`

This file proves `Work.NN.Final.proj02_integrable_flat`, the identity that (in the flat model
`ℂⁿ = Fin n → ℂ`, with the structure `Jtr J T` obtained from an almost complex structure `J` on
`U ⊆ ℝ^{2n}` by transport along `tupleDeriv T`) reads: *the `(0,2)`-part of `d(∂̄ v)` vanishes for
an integrable `J`, i.e. `∂̄² = 0`.*

The proof does not recompute the classical identity; it **transports** the already proved
statement `Work.NN.Core.dbar_sq_zero` from `ℝ^{2n}` to `ℂⁿ` along the linear isomorphism
`tupleDeriv T`.  The only content is therefore the compatibility of the two objects appearing in
the statement with the transport:

* the exterior derivative `dOne` of a `1`-form commutes with precomposition by a linear
  equivalence (`dExteriorG_precomp`), while `dOne` and `Work.AlmostComplex.Types.dExterior` are the
  same formula (`dExteriorG`);
* the `(0,2)`-projection `proj02` is transported by a linear equivalence intertwining the two
  complex structures (`proj02P_eqv`).

Both inputs are already available: `Work.NN.Final.dbar_comp_tupleDeriv` identifies
`Submission.dbar J (v ∘ tupleDeriv T)` with `dbarCn (Jtr J T) v` composed with `tupleDeriv T`, and
`Work.NN.Core.dbarSq_eq_proj02` identifies `dbarSq` with the projection of the exterior derivative.
-/

/-- The exterior derivative of a `1`-form on an arbitrary real normed space, evaluated on two
vectors: `dθ_x(u,w) = D_u(θ(·)(w))(x) - D_w(θ(·)(u))(x)`.  This is the common unfolding of
`Work.NN.Final.dOne` (on `ℂⁿ`) and `Work.AlmostComplex.Types.dExterior` (on `ℝ^{2n}`). -/
noncomputable def dExteriorG {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (θ : G → G →L[ℝ] ℂ) (x X Y : G) : ℂ :=
  fderiv ℝ (fun y => θ y Y) x X - fderiv ℝ (fun y => θ y X) x Y

/-- `Work.NN.Final.dOne` is the generic `dExteriorG`. -/
lemma dOne_eq_dExteriorG {n : ℕ} (α : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ)
    (z V W : Work.NN.Core.Cn n) : dOne α z V W = dExteriorG α z V W := rfl

/-- `Work.AlmostComplex.Types.dExterior` is the generic `dExteriorG`. -/
lemma dExterior_eq_dExteriorG {n : ℕ} (θ : E n → E n →L[ℝ] ℂ) (x X Y : E n) :
    Work.AlmostComplex.Types.dExterior θ x X Y = dExteriorG θ x X Y := rfl

/-- **The exterior derivative commutes with precomposition by a linear equivalence.**  For a `1`-form
`θ` on `G` and a continuous linear equivalence `L : E n ≃L[ℝ] G`, the exterior derivative of the
pulled-back form `x ↦ θ (L x) ∘ L` at `y`, on `A, B`, is the exterior derivative of `θ` at `L y` on
`L A, L B`. -/
lemma dExteriorG_precomp {n : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E n ≃L[ℝ] G) (θ : G → G →L[ℝ] ℂ) (y : E n) (A B : E n) :
    dExteriorG (fun x => (θ (L x)).comp (L : E n →L[ℝ] G)) y A B
      = dExteriorG θ (L y) (L A) (L B) := by
  have eB : (fun x : E n => ((θ (L x)).comp (L : E n →L[ℝ] G)) B)
      = fun x => θ (L x) (L B) := rfl
  have eA : (fun x : E n => ((θ (L x)).comp (L : E n →L[ℝ] G)) A)
      = fun x => θ (L x) (L A) := rfl
  simp only [dExteriorG, eB, eA]
  have h1 := ContinuousLinearEquiv.comp_right_fderiv (iso := L)
    (f := fun w : G => θ w (L B)) (x := y)
  have h2 := ContinuousLinearEquiv.comp_right_fderiv (iso := L)
    (f := fun w : G => θ w (L A)) (x := y)
  rw [show ((fun w : G => θ w (L B)) ∘ ⇑L) = fun x : E n => θ (L x) (L B)
        from by funext x; rfl] at h1
  rw [show ((fun w : G => θ w (L A)) ∘ ⇑L) = fun x : E n => θ (L x) (L A)
        from by funext x; rfl] at h2
  rw [h1, h2]
  simp [ContinuousLinearMap.comp_apply]

/-- The pointwise `(0,2)`-projection formula, on a fixed structure `J₁` on `ℂⁿ` and a fixed
`2`-form `β`: `(1/4)·(β(V,W) + iβ(JV,W) + iβ(V,JW) - β(JV,JW))`. -/
noncomputable def proj02P {n : ℕ} (J₁ : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (β : Work.NN.Core.Cn n → Work.NN.Core.Cn n → ℂ) (V W : Work.NN.Core.Cn n) : ℂ :=
  (1 / 4 : ℂ) * (β V W + Complex.I * β (J₁ V) W + Complex.I * β V (J₁ W) - β (J₁ V) (J₁ W))

/-- `Work.NN.Final.proj02` is the pointwise `proj02P`. -/
lemma proj02_eq_proj02P {n : ℕ}
    (J : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (Ω : Work.NN.Core.Cn n → Work.NN.Core.Cn n → Work.NN.Core.Cn n → ℂ)
    (z V W : Work.NN.Core.Cn n) :
    proj02 J Ω z V W = proj02P (J z) (Ω z) V W := rfl

/-- **The `(0,2)`-projection is compatible with a linear equivalence intertwining the structures.**
If `L : E n ≃L[ℝ] ℂⁿ` interwines `J₀` (on `ℝ^{2n}`) with `J₁` (on `ℂⁿ`), i.e. `J₁ ∘ L = L ∘ J₀`,
and the `2`-forms `α`, `β` satisfy `α A B = β (L A) (L B)`, then the projection of `β` at `V, W`
equals the projection of `α` at `L.symm V, L.symm W`. -/
lemma proj02P_eqv {n : ℕ} (L : E n ≃L[ℝ] Work.NN.Core.Cn n)
    (J₀ : E n →L[ℝ] E n) (J₁ : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (hJ : ∀ u, J₁ (L u) = L (J₀ u))
    (α : E n → E n → ℂ) (β : Work.NN.Core.Cn n → Work.NN.Core.Cn n → ℂ)
    (hαβ : ∀ A B, α A B = β (L A) (L B)) (V W : Work.NN.Core.Cn n) :
    proj02P J₁ β V W = Work.AlmostComplex.Types.proj02 J₀ α (L.symm V) (L.symm W) := by
  simp only [proj02P, Work.AlmostComplex.Types.proj02]
  have hV : L (J₀ (L.symm V)) = J₁ V := by
    rw [← hJ (L.symm V), ContinuousLinearEquiv.apply_symm_apply]
  have hW : L (J₀ (L.symm W)) = J₁ W := by
    rw [← hJ (L.symm W), ContinuousLinearEquiv.apply_symm_apply]
  simp only [hαβ, ContinuousLinearEquiv.apply_symm_apply, hV, hW]

/-- The linear equivalence `E n ≃L[ℝ] ℂⁿ` given by `tupleDeriv T`, with inverse
`tupleDerivInv T`.  Its coercions to `E n →L[ℝ] ℂⁿ` and `ℂⁿ →L[ℝ] E n` are *definitionally*
`tupleDeriv T` resp. `tupleDerivInv T`. -/
noncomputable def tupleDerivEquiv' {n : ℕ} (T : E n ≃L[ℝ] Submission.F n) :
    E n ≃L[ℝ] Work.NN.Core.Cn n :=
  ContinuousLinearEquiv.equivOfInverse (Work.NN.Core.tupleDeriv T) (Work.NN.Core.tupleDerivInv T)
    (fun x => Work.NN.Final.tupleDerivInv_tupleDeriv T x)
    (fun y => Work.NN.Core.tupleDeriv_tupleDerivInv T y)

theorem proj02_integrable_flat {n : ℕ} {U : Set (LeanEval.Geometry.NewlanderNirenberg.E n)} (hU : IsOpen U) {J : LeanEval.Geometry.NewlanderNirenberg.E n → LeanEval.Geometry.NewlanderNirenberg.E n →L[ℝ] LeanEval.Geometry.NewlanderNirenberg.E n} (hJ : LeanEval.Geometry.NewlanderNirenberg.IsAlmostComplexOn J U) (hN : LeanEval.Geometry.NewlanderNirenberg.NijenhuisVanishesOn J U) (T : LeanEval.Geometry.NewlanderNirenberg.E n ≃L[ℝ] Submission.F n) {v : Work.NN.Core.Cn n → ℂ} (hv : ∀ k : ℕ, ContDiff ℝ k v) {z : Work.NN.Core.Cn n} (hz : Work.NN.Core.tupleDerivInv T z ∈ U) (V W : Work.NN.Core.Cn n) : Work.NN.Final.proj02 (Work.NN.Final.Jtr J T) (fun z' A B => Work.NN.Final.dOne (fun z'' => Work.NN.Core.dbarCn (Work.NN.Final.Jtr J T) v z'') z' A B) z V W = 0 := by
  -- `v` is smooth, hence so is its transport `y ↦ v (tupleDeriv T y)`.
  have hvtop : ContDiff ℝ ∞ v :=
    (contDiff_iff_forall_nat_le (𝕜 := ℝ) (f := v) (n := (⊤ : ℕ∞))).2 (fun m _ => hv m)
  let L : E n ≃L[ℝ] Work.NN.Core.Cn n := tupleDerivEquiv' T
  have hLx : L (Work.NN.Core.tupleDerivInv T z) = z := by
    rw [show L (Work.NN.Core.tupleDerivInv T z)
        = Work.NN.Core.tupleDeriv T (Work.NN.Core.tupleDerivInv T z) from rfl]
    rw [Work.NN.Core.tupleDeriv_tupleDerivInv]
  -- `Jtr J T z` is `J (tupleDerivInv T z)` transported along `L`.
  have hJ' : ∀ u : E n,
      Work.NN.Final.Jtr J T z (L u) = L (J (Work.NN.Core.tupleDerivInv T z) u) := by
    intro u
    rw [Work.NN.Final.Jtr_apply]
    have h1 : Work.NN.Core.tupleDerivInv T (L u) = u := by
      show Work.NN.Core.tupleDerivInv T (Work.NN.Core.tupleDeriv T u) = u
      rw [Work.NN.Final.tupleDerivInv_tupleDeriv]
    rw [h1]
    rfl
  have hsm : ContDiff ℝ ∞ (fun y : E n => v (Work.NN.Core.tupleDeriv T y)) := by
    have h := hvtop.comp L.contDiff
    exact h
  -- Integrability on `ℝ^{2n}`: `∂̄² = 0` for the transported function.
  have hsq : Work.NN.Core.dbarSq J (fun y : E n => v (Work.NN.Core.tupleDeriv T y))
      (Work.NN.Core.tupleDerivInv T z) (L.symm V) (L.symm W) = 0 :=
    Work.NN.Core.dbar_sq_zero hU hJ hN hsm (L.symm V) (L.symm W) hz
  have hproj : Work.AlmostComplex.Types.proj02 (J (Work.NN.Core.tupleDerivInv T z))
      (fun A B => Work.AlmostComplex.Types.dExterior
        (Submission.dbar J (fun y : E n => v (Work.NN.Core.tupleDeriv T y)))
        (Work.NN.Core.tupleDerivInv T z) A B) (L.symm V) (L.symm W) = 0 := by
    rw [← Work.NN.Core.dbarSq_eq_proj02]
    exact hsq
  -- The transport identity for the exterior derivative of `∂̄ v`.
  have hβ : ∀ A B : E n,
      dExteriorG (Submission.dbar J (fun y : E n => v (Work.NN.Core.tupleDeriv T y)))
          (Work.NN.Core.tupleDerivInv T z) A B
        = dExteriorG (fun w => Work.NN.Core.dbarCn (Work.NN.Final.Jtr J T) v w) z (L A) (L B) := by
    intro A B
    rw [show Submission.dbar J (fun y : E n => v (Work.NN.Core.tupleDeriv T y))
          = fun y : E n => ((fun w => Work.NN.Core.dbarCn (Work.NN.Final.Jtr J T) v w) (L y)).comp
              (L : E n →L[ℝ] Work.NN.Core.Cn n)
        from by funext y; exact Work.NN.Final.dbar_comp_tupleDeriv J T v y]
    rw [dExteriorG_precomp (L := L)
      (θ := fun w => Work.NN.Core.dbarCn (Work.NN.Final.Jtr J T) v w)
      (y := Work.NN.Core.tupleDerivInv T z) (A := A) (B := B)]
    rw [hLx]
  have htrans : proj02P (Work.NN.Final.Jtr J T z)
      (fun A B => dExteriorG (fun w => Work.NN.Core.dbarCn (Work.NN.Final.Jtr J T) v w) z A B) V W
      = Work.AlmostComplex.Types.proj02 (J (Work.NN.Core.tupleDerivInv T z))
          (fun A B => dExteriorG (Submission.dbar J (fun y : E n => v (Work.NN.Core.tupleDeriv T y)))
            (Work.NN.Core.tupleDerivInv T z) A B) (L.symm V) (L.symm W) :=
    proj02P_eqv L (J (Work.NN.Core.tupleDerivInv T z)) (Work.NN.Final.Jtr J T z) hJ'
      (fun A B => dExteriorG (Submission.dbar J (fun y : E n => v (Work.NN.Core.tupleDeriv T y)))
        (Work.NN.Core.tupleDerivInv T z) A B)
      (fun A B => dExteriorG (fun w => Work.NN.Core.dbarCn (Work.NN.Final.Jtr J T) v w) z A B)
      hβ V W
  change proj02P (Work.NN.Final.Jtr J T z)
      (fun A B => dExteriorG (fun w => Work.NN.Core.dbarCn (Work.NN.Final.Jtr J T) v w) z A B) V W = 0
  rw [htrans]
  exact hproj

end Work.NN.Final
