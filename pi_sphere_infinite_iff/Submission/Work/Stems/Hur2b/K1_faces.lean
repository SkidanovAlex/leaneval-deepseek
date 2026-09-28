import Mathlib
import Submission.Work.Stems.Hur2.Kfill

/-!
# The faces of `K₁ e` as cubical chains

`K₁ e` is the square filling the edge `e` (`Submission/Work/Stems/Hur2/Kfill.lean`).  This file
records its four faces as *cubes* — i.e. as elements of `C(IC 1, X)` — and the resulting
chain-level identity

`cubD 1 X (single (K₁ e) 1) = single x₀ - single (K₀ (e 0)) - single e + single (K₀ (e 1))`,

which is the degree-one instance of Hutchings' chain homotopy identity
`∂ K(σ) = σ - K(∂σ)` (`Submission/Work/Stems/Hur2/PLAN.md`, item 6 / `(2.3)`).  The faces are
the degenerate/constant cubes together with the two `K₀`-paths of the endpoints of `e`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.Stems.Hur2b

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- A path, read as a `1`-cube. -/
def pathCube {x y : X} (γ : Path x y) : ContinuousMap (IC 1) X :=
  γ.toContinuousMap.comp ⟨fun t : IC 1 => t 0, by continuity⟩

theorem pathCube_apply {x y : X} (γ : Path x y) (t : IC 1) : pathCube γ t = γ (t 0) := rfl

/-- The `(0,0)`-face of `K₁ e` (the degenerate face `x₀`). -/
theorem faceCube_K1_fst_zero (x₀ : X) [SimplyConnectedSpace X] (e : ContinuousMap (IC 1) X) :
    faceCube (0 : Fin 2) (0 : unitInterval) (Work.Stems.Hur2.K₁ x₀ e) =
      ContinuousMap.const (IC 1) x₀ := by
  ext t
  exact Work.Stems.Hur2.K₁_face_00 x₀ e t

/-- The `(1,0)`-face of `K₁ e` (the `K₀`-path of `e 0`). -/
theorem faceCube_K1_snd_zero (x₀ : X) [SimplyConnectedSpace X] (e : ContinuousMap (IC 1) X) :
    faceCube (1 : Fin 2) (0 : unitInterval) (Work.Stems.Hur2.K₁ x₀ e) =
      pathCube (Work.Stems.Hur2.K₀ x₀ (e 0)) := by
  ext t
  exact Work.Stems.Hur2.K₁_face_10 x₀ e t

/-- The `(0,1)`-face of `K₁ e` (the edge `e` itself). -/
theorem faceCube_K1_fst_one (x₀ : X) [SimplyConnectedSpace X] (e : ContinuousMap (IC 1) X) :
    faceCube (0 : Fin 2) (1 : unitInterval) (Work.Stems.Hur2.K₁ x₀ e) = e := by
  ext t
  exact Work.Stems.Hur2.K₁_face_01 x₀ e t

/-- The `(1,1)`-face of `K₁ e` (the `K₀`-path of `e 1`). -/
theorem faceCube_K1_snd_one (x₀ : X) [SimplyConnectedSpace X] (e : ContinuousMap (IC 1) X) :
    faceCube (1 : Fin 2) (1 : unitInterval) (Work.Stems.Hur2.K₁ x₀ e) =
      pathCube (Work.Stems.Hur2.K₀ x₀ (e 1)) := by
  ext t
  exact Work.Stems.Hur2.K₁_face_11 x₀ e t

/-- **The degree-one instance of `∂ K(σ) = σ - K(∂σ)`.** -/
theorem cubD_single_K1 (x₀ : X) [SimplyConnectedSpace X] (e : ContinuousMap (IC 1) X) :
    cubD 1 X (Finsupp.single (Work.Stems.Hur2.K₁ x₀ e) 1) =
      Finsupp.single (ContinuousMap.const (IC 1) x₀) 1
        - Finsupp.single (pathCube (Work.Stems.Hur2.K₀ x₀ (e 0))) 1
        - Finsupp.single e 1
        + Finsupp.single (pathCube (Work.Stems.Hur2.K₀ x₀ (e 1))) 1 := by
  rw [cubD_single, Fin.sum_univ_two]
  rw [faceCube_K1_fst_zero x₀ e, faceCube_K1_snd_zero x₀ e,
    faceCube_K1_fst_one x₀ e, faceCube_K1_snd_one x₀ e]
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.mod_succ, Int.reduceNeg,
    pow_zero, pow_one, one_smul, neg_smul, sub_eq_add_neg]
  abel

end

end Work.Stems.Hur2b
