import Mathlib
import Submission.Work.KT.Fund.AssemblyDefs
import Submission.Work.KT.r_gamma_mvn2x2
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.Fund.hopf_trace_det
import Submission.Work.KT.Fund.twoByTwo_idem_of_trace_det

/-!
# `Work.KT.Fund.r_gamma` — the Hopf class restricts to the trivial class at the base point

`r = (X × {pt})^*` is restriction of `K₀`-classes on `X × S²` to the base point and
`γ = snd^*(cls hopfIdem)` is the Hopf class on `X × S²`.  As `pt = up 0` is a point of the
upper hemisphere, the Hopf line bundle is trivial there, i.e. `hopfIdem` evaluates to a rank-one
projection of the base field.  This is the statement `r γ = 1` used by the assembly of
`Work.KT.fund_product`.

The proof decomposes as follows.

* `r_gamma_hopf_eval` (the mathematical content): for **every** point `x₀ : S²`, evaluation of
  functions at `x₀` sends the Hopf class to `cls (Mat.one ℂ 1)`.  The matrix
  `P = hopfIdem(x₀)` is a `2 × 2` idempotent over `ℂ` of trace one (and vanishing determinant),
  hence Murray–von Neumann equivalent to the `1 × 1` identity (`r_gamma_mvn2x2`, pure algebra).
* `r_gamma_mapA_one`: `K0.mapA` along `ℂ → R` sends `cls (Mat.one ℂ 1)` to `cls (Mat.one R 1)`.
* `r_gamma_pullAlg_comp`: `snd^* ∘ bp^* = (snd ∘ bp)^* = (pt)^*`, the pull-back along the
  constant map, which factors through evaluation at `pt`.
-/

namespace Work.KT.Fund


noncomputable section

/-- Functoriality of `K0.mapA` along a composition of algebra homomorphisms. -/
lemma r_gamma_mapA_comp {A B C : Type} [Ring A] [Ring B] [Ring C]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C] (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) (x : K0 A) :
    K0.mapA ψ (K0.mapA φ x) = K0.mapA (ψ.comp φ) x := by
  have h : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom := by ext a; rfl
  show K0.map ψ.toRingHom (K0.map φ.toRingHom x) = K0.map (ψ.comp φ).toRingHom x
  rw [h, K0.map_comp_apply]

/-- The matrix underlying the Hopf idempotent, with its size made explicit. -/
def r_gamma_hopfMat : Matrix (Fin 2) (Fin 2) C(S2, ℂ) := hopfIdem.2

lemma r_gamma_hopfMat_trace : r_gamma_hopfMat 0 0 + r_gamma_hopfMat 1 1 = 1 := by
  simpa [r_gamma_hopfMat] using hopf_trace_det.1

lemma r_gamma_hopfMat_det :
    r_gamma_hopfMat 0 0 * r_gamma_hopfMat 1 1 = r_gamma_hopfMat 0 1 * r_gamma_hopfMat 1 0 := by
  simpa [r_gamma_hopfMat] using hopf_trace_det.2

lemma r_gamma_hopfIdem_isIdem : Mat.IsIdem hopfIdem :=
  twoByTwo_idem_of_trace_det hopfIdem.2 hopf_trace_det.1 hopf_trace_det.2

/-- The Hopf class evaluated at a point of `S²` is the class of the trivial line bundle. -/
lemma r_gamma_hopf_eval (x0 : S2) :
    K0.mapA (evalC x0) (cls hopfIdem) = cls (Mat.one ℂ 1) := by
  have hIdem : Mat.IsIdem hopfIdem := r_gamma_hopfIdem_isIdem
  rw [K0.map_cls (evalC x0).toRingHom hIdem]
  set P : Matrix (Fin 2) (Fin 2) ℂ := r_gamma_hopfMat.map (evalC x0).toRingHom with hP
  have hmap : Mat.map (evalC x0).toRingHom hopfIdem = (⟨2, P⟩ : Mat ℂ) := rfl
  rw [hmap]
  have htr : P 0 0 + P 1 1 = 1 := by
    rw [hP, Matrix.map_apply, Matrix.map_apply]
    have h := congrArg (fun f : C(S2, ℂ) => f x0) r_gamma_hopfMat_trace
    simpa using h
  have hdet : P 0 0 * P 1 1 = P 0 1 * P 1 0 := by
    rw [hP, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
    have h := congrArg (fun f : C(S2, ℂ) => f x0) r_gamma_hopfMat_det
    simpa using h
  exact cls_eq_of_mvn (twoByTwo_idem_of_trace_det P htr hdet) (Mat.one_isIdem ℂ 1)
    (r_gamma_mvn2x2 P htr hdet)

/-- Along `ℂ → R`, the class of the trivial line bundle over `ℂ` is the class of the trivial
line bundle over `R`. -/
lemma r_gamma_mapA_one (R : Type) [CommRing R] [Algebra ℂ R] :
    K0.mapA (Algebra.ofId ℂ R) (cls (Mat.one ℂ 1)) = cls (Mat.one R 1) := by
  have hmat : Mat.map (Algebra.ofId ℂ R).toRingHom (Mat.one ℂ 1) = Mat.one R 1 := by
    show (⟨1, (1 : Matrix (Fin 1) (Fin 1) ℂ).map (Algebra.ofId ℂ R).toRingHom⟩ : Mat R)
        = ⟨1, (1 : Matrix (Fin 1) (Fin 1) R)⟩
    congr 1
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.map_apply]
  rw [K0.map_cls (Algebra.ofId ℂ R).toRingHom (Mat.one_isIdem ℂ 1), hmat]

/-- Pulling back functions along `snd ∘ bp` is evaluation at the base point of `S²`. -/
lemma r_gamma_pullAlg_comp (X : Type) [TopologicalSpace X] :
    (pullAlg (bp X)).comp (pullAlg (ContinuousMap.snd : C(X × S2, S2)))
      = (Algebra.ofId ℂ C(X, ℂ)).comp (evalC pt) := by
  ext f x
  simp [pullAlg, Algebra.ofId_apply, bp]

theorem r_gamma (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    Work.KT.Fund.r X (Work.KT.Fund.gamma X)
      = Work.KT.cls (Work.KT.Mat.one C(X, ℂ) 1) := by
  show K0.mapA (pullAlg (bp X))
      (K0.mapA (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (cls hopfIdem))
    = cls (Mat.one C(X, ℂ) 1)
  rw [r_gamma_mapA_comp (pullAlg (ContinuousMap.snd : C(X × S2, S2))) (pullAlg (bp X))
    (cls hopfIdem)]
  rw [r_gamma_pullAlg_comp X]
  rw [← r_gamma_mapA_comp (evalC pt) (Algebra.ofId ℂ C(X, ℂ)) (cls hopfIdem)]
  rw [r_gamma_hopf_eval pt]
  exact r_gamma_mapA_one C(X, ℂ)

end

end Work.KT.Fund
