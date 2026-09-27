import Mathlib
import Submission.Work.KT.Fund.kbi_defs

/-!
# `Work.KT.Fund.kbi_hopfsq`

The two rank-one projections

* `h1m = c • [[1, ζ̄], [ζ, ζζ̄]]` — the projection onto the line spanned by `(1, ζ)`,
* `h2m = c • [[ζζ̄, ζ̄], [ζ, 1]]` — the projection onto the line spanned by `(ζ̄, 1)`,

where `ζ` is the coordinate of the disc, `ζ̄` its conjugate and `c = (1 + ζζ̄)⁻¹` the
normalising factor, are idempotent, and they agree on the boundary circle `|ζ| = 1`
(where `c = 1/2` and `ζ̄ = ζ⁻¹`).

The computation is performed once, for a general commutative ring: the *shape* of the two
matrices is isolated as `KBIM1 c u ub` and `KBIM2 c u ub`, which are definitionally equal to
`h1m X` / `h2m X` at `c = zcn X`, `u = zc X`, `ub = zcb X`.  Idempotence then only uses the
single scalar relation `c * (1 + u * ub) = 1` (`= KBI.zcn_mul_one_add X`), and the boundary
equality only uses `g u * g ub = 1` for the ring homomorphism `g = bdryRestrict X`
(`= Units.mul_inv (zUnit X)`, since on the circle `ζ · ζ⁻¹ = 1`).
-/

namespace Work.KT.Fund

open _root_.Matrix

noncomputable section

/-! ## The two generic matrix shapes -/

/-- The generic shape of the projection onto the line spanned by `(1, u)`,
namely `c • [[1, ub], [u, u·ub]]`.  `KBIM1 (zcn X) (zc X) (zcb X)` is definitionally
`KBI.h1m X`. -/
def KBIM1 {R : Type*} [Mul R] (c u ub : R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of fun i j =>
    if i = 0 then (if j = 0 then c else c * ub) else (if j = 0 then c * u else c * (u * ub))

/-- The generic shape of the projection onto the line spanned by `(ub, 1)`,
namely `c • [[u·ub, ub], [u, 1]]`.  `KBIM2 (zcn X) (zc X) (zcb X)` is definitionally
`KBI.h2m X`. -/
def KBIM2 {R : Type*} [Mul R] (c u ub : R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of fun i j =>
    if i = 0 then (if j = 0 then c * (u * ub) else c * ub) else (if j = 0 then c * u else c)

/-- `h1m` is the generic first shape. -/
lemma kbi_h1m_eq_KBIM1 (X : Type) [TopologicalSpace X] :
    KBI.h1m X = KBIM1 (KBI.zcn X) (KBI.zc X) (KBI.zcb X) := rfl

/-- `h2m` is the generic second shape. -/
lemma kbi_h2m_eq_KBIM2 (X : Type) [TopologicalSpace X] :
    KBI.h2m X = KBIM2 (KBI.zcn X) (KBI.zc X) (KBI.zcb X) := rfl

/-! ## Idempotence -/

/-- `KBIM1 c u ub` is idempotent as soon as `c * (1 + u * ub) = 1`. -/
lemma KBIM1_mul_self {R : Type*} [CommRing R] (c u ub : R) (h : c * (1 + u * ub) = 1) :
    KBIM1 c u ub * KBIM1 c u ub = KBIM1 c u ub := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KBIM1, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination c * h
  · linear_combination (c * ub) * h
  · linear_combination (c * u) * h
  · linear_combination (c * (u * ub)) * h

/-- `KBIM2 c u ub` is idempotent as soon as `c * (1 + u * ub) = 1`. -/
lemma KBIM2_mul_self {R : Type*} [CommRing R] (c u ub : R) (h : c * (1 + u * ub) = 1) :
    KBIM2 c u ub * KBIM2 c u ub = KBIM2 c u ub := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KBIM2, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (c * (u * ub)) * h
  · linear_combination (c * ub) * h
  · linear_combination (c * u) * h
  · linear_combination c * h

/-- The two generic shapes agree after applying a ring homomorphism `g` along which `u·ub ↦ 1`
(in particular on the boundary circle, where `ζ · ζ⁻¹ = 1`). -/
lemma map_KBIM1_eq_map_KBIM2 {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (c u ub : R) (h : g u * g ub = 1) :
    (KBIM1 c u ub).map g = (KBIM2 c u ub).map g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KBIM1, KBIM2, Matrix.map_apply, map_mul, h]

/-! ## The target -/

theorem kbi_hopfsq (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    Work.KT.Fund.KBI.h1m X * Work.KT.Fund.KBI.h1m X = Work.KT.Fund.KBI.h1m X ∧
      Work.KT.Fund.KBI.h2m X * Work.KT.Fund.KBI.h2m X = Work.KT.Fund.KBI.h2m X ∧
      (Work.KT.Fund.KBI.h1m X).map (fun f => Work.KT.Fund.bdryRestrict X f) =
        (Work.KT.Fund.KBI.h2m X).map (fun f => Work.KT.Fund.bdryRestrict X f) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [kbi_h1m_eq_KBIM1]
    exact KBIM1_mul_self _ _ _ (KBI.zcn_mul_one_add X)
  · rw [kbi_h2m_eq_KBIM2]
    exact KBIM2_mul_self _ _ _ (KBI.zcn_mul_one_add X)
  · have hz : bdryRestrict X (KBI.zc X) * bdryRestrict X (KBI.zcb X) = 1 := by
      rw [KBI.bdryRestrict_zc, KBI.bdryRestrict_zcb]
      exact Units.mul_inv (zUnit X)
    rw [kbi_h1m_eq_KBIM1, kbi_h2m_eq_KBIM2]
    exact map_KBIM1_eq_map_KBIM2 (bdryRestrict X) _ _ _ hz

end

end Work.KT.Fund
