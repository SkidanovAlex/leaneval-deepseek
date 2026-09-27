import Mathlib
import Submission.Work.KT.Defs

/-!
# `Work.KT.mvLin`: the linear map `v ↦ M *ᵥ v`

`Work.KT.FiberProd` (and hence `Work.KT.TwoDisk V`) carries only a `Ring` instance — the
project's convention is to pass commutativity as an explicit hypothesis rather than to ask for a
`CommRing` instance on a subring.  Consequently Mathlib's `Matrix.mulVecLin` (which needs
`CommSemiring`) is not available for these rings, and we provide here the replacement

`mvLin hcomm M : (Fin n → R) →ₗ[R] (Fin m → R)`, `v ↦ M *ᵥ v`,

where `hcomm` is an explicit commutativity hypothesis on `R`.
-/

namespace Work.KT

open Matrix

noncomputable section

variable {R : Type} [Ring R]

/-- Matrix–vector multiplication as an `R`-linear map, for a ring `R` with an explicit
commutativity hypothesis. -/
def mvLin (hcomm : ∀ x y : R, x * y = y * x) {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) :
    (Fin n → R) →ₗ[R] (Fin m → R) where
  toFun := M.mulVec
  map_add' := fun x y => Matrix.mulVec_add M x y
  map_smul' := fun c v => by
    letI : SMulCommClass R R R :=
      ⟨fun a b x => by
        show a * (b * x) = b * (a * x)
        rw [← mul_assoc, hcomm a b, mul_assoc]⟩
    exact Matrix.mulVec_smul M c v

@[simp] theorem mvLin_apply (hcomm : ∀ x y : R, x * y = y * x) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) R) (v : Fin n → R) : mvLin hcomm M v = M.mulVec v := rfl

theorem mvLin_mul (hcomm : ∀ x y : R, x * y = y * x) {l m n : ℕ}
    (M : Matrix (Fin l) (Fin m) R) (N : Matrix (Fin m) (Fin n) R) :
    mvLin hcomm (M * N) = (mvLin hcomm M).comp (mvLin hcomm N) := by
  apply LinearMap.ext
  intro v
  funext i
  show (M * N).mulVec v i = (M.mulVec (N.mulVec v)) i
  rw [Matrix.mulVec_mulVec]

theorem mvLin_one (hcomm : ∀ x y : R, x * y = y * x) {n : ℕ} :
    mvLin hcomm (1 : Matrix (Fin n) (Fin n) R) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  funext i
  show (1 : Matrix (Fin n) (Fin n) R).mulVec v i = v i
  rw [Matrix.one_mulVec]

theorem mvLin_add (hcomm : ∀ x y : R, x * y = y * x) {m n : ℕ}
    (M N : Matrix (Fin m) (Fin n) R) :
    mvLin hcomm (M + N) = mvLin hcomm M + mvLin hcomm N := by
  apply LinearMap.ext
  intro v
  funext i
  show ((M + N).mulVec v) i = (M.mulVec v + N.mulVec v) i
  rw [Matrix.add_mulVec]

theorem mvLin_zero (hcomm : ∀ x y : R, x * y = y * x) {m n : ℕ} :
    mvLin hcomm (0 : Matrix (Fin m) (Fin n) R) = 0 := by
  apply LinearMap.ext
  intro v
  funext i
  show ((0 : Matrix (Fin m) (Fin n) R).mulVec v) i = (0 : Fin m → R) i
  rw [Matrix.zero_mulVec]

theorem mem_range_mvLin {hcomm : ∀ x y : R, x * y = y * x} {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) R) (v : Fin m → R) :
    v ∈ (mvLin hcomm M).range ↔ ∃ w, M.mulVec w = v := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, by rwa [mvLin_apply] at hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, by rwa [mvLin_apply]⟩

theorem range_mvLin_eq_top_iff {hcomm : ∀ x y : R, x * y = y * x} {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) R) :
    (mvLin hcomm M).range = ⊤ ↔ Function.Surjective M.mulVec := by
  rw [LinearMap.range_eq_top]
  constructor
  · intro h v
    obtain ⟨w, hw⟩ := h v
    exact ⟨w, by rwa [mvLin_apply] at hw⟩
  · intro h v
    obtain ⟨w, hw⟩ := h v
    exact ⟨w, by rwa [mvLin_apply]⟩

end

end Work.KT
