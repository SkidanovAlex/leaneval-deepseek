import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Matrix

open Module LinearMap

/-- **Dimension of the image of a submodule under a linear map.**

For a linear map `g : W →ₗ[K] U` and a submodule `R ≤ W`, the dimension of the image
`g(R)` together with the dimension of `R ⊓ ker g` fills up the dimension of `R`:
$\dim g(R) + \dim (R \cap \ker g) = \dim R.$

This is rank–nullity applied to `g` restricted to `R`. -/
theorem finrank_map_add_finrank_inf_ker {K : Type*} [Field K] {W U : Type*}
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    [FiniteDimensional K W]
    (g : W →ₗ[K] U) (R : Submodule K W) :
    finrank K (Submodule.map g R) + finrank K ↥(R ⊓ LinearMap.ker g) = finrank K ↥R := by
  have hmap2 : Submodule.map g R = LinearMap.range (g.comp R.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [hmap2]
  have hker : (g.comp R.subtype).ker = Submodule.comap R.subtype g.ker := by
    ext x
    simp [LinearMap.mem_ker]
  have hmap : Submodule.map R.subtype (g.comp R.subtype).ker = R ⊓ g.ker := by
    rw [hker, Submodule.map_comap_eq, Submodule.range_subtype]
  have hfr : finrank K ↥(R ⊓ g.ker) = finrank K ↥((g.comp R.subtype).ker) := by
    rw [← hmap, Submodule.finrank_map_subtype_eq]
  have h := LinearMap.finrank_range_add_finrank_ker (g.comp R.subtype)
  rw [hfr]
  exact h

/-- **Rank–nullity for a triple of composable linear maps.**

Let `A : W →ₗ U`, `B : V →ₗ W`, `C : U' →ₗ V` satisfy
`ker A ≤ range B` and `ker (A ∘ B) ≤ range C`.  Then
$\dim \operatorname{im}(A \circ B \circ C)
  = \dim \operatorname{im} B - \bigl(\dim \ker A
      + (\dim V - \dim \operatorname{im} C)\bigr).$

This is the linear-algebra content of the "rank sandwich" identity: `ker A` is
absorbed by `range B`, and the kernel of `A ∘ B` lies inside `range C`. -/
theorem finrank_range_comp_comp_eq {K : Type*} [Field K] {V W U U' : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup U] [Module K U] [AddCommGroup U'] [Module K U']
    [FiniteDimensional K V] [FiniteDimensional K W]
    (A : W →ₗ[K] U) (B : V →ₗ[K] W) (C : U' →ₗ[K] V)
    (h1 : LinearMap.ker A ≤ LinearMap.range B)
    (h2 : LinearMap.ker (A.comp B) ≤ LinearMap.range C) :
    finrank K (LinearMap.range (A.comp (B.comp C))) =
      finrank K (LinearMap.range B) -
        (finrank K ↥(LinearMap.ker A) + (finrank K V - finrank K ↥(LinearMap.range C))) := by
  classical
  set T : V →ₗ[K] U := A.comp B with hT
  have hkerT_le : LinearMap.ker T ≤ LinearMap.range C := by
    intro v hv
    exact h2 (by rw [hT]; exact hv)
  have e1 : finrank K (LinearMap.range (A.comp (B.comp C))) + finrank K ↥(LinearMap.ker T) =
      finrank K ↥(LinearMap.range C) := by
    have hcomp : A.comp (B.comp C) = T.comp C := by
      rw [hT, LinearMap.comp_assoc]
    rw [hcomp, LinearMap.range_comp]
    have hkey := finrank_map_add_finrank_inf_ker T (LinearMap.range C)
    have hinf : (LinearMap.range C ⊓ LinearMap.ker T) = LinearMap.ker T :=
      inf_eq_right.mpr hkerT_le
    rw [hinf] at hkey
    exact hkey
  have e2 : finrank K (LinearMap.range T) + finrank K ↥(LinearMap.ker T) = finrank K V :=
    LinearMap.finrank_range_add_finrank_ker T
  have e3 : finrank K (LinearMap.range T) + finrank K ↥(LinearMap.ker A) =
      finrank K ↥(LinearMap.range B) := by
    have hmapA : Submodule.map A (LinearMap.range B) = LinearMap.range T := by
      rw [← LinearMap.range_comp, ← hT]
    have hinfA : (LinearMap.range B ⊓ LinearMap.ker A) = LinearMap.ker A :=
      inf_eq_right.mpr h1
    have hkey := finrank_map_add_finrank_inf_ker A (LinearMap.range B)
    rw [hmapA, hinfA] at hkey
    exact hkey
  have e4 : finrank K ↥(LinearMap.range C) ≤ finrank K V := Submodule.finrank_le _
  omega

theorem rank_sandwich_eq {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (ι : Matrix (Fin m) (Fin m') (ZMod 2)) (X : Matrix (Fin n) (Fin m) (ZMod 2))
    (h1 : LinearMap.ker Q.mulVecLin ≤ LinearMap.range X.mulVecLin)
    (h2 : ∀ w : Fin m → ZMod 2, X.mulVec w ∈ LinearMap.ker Q.mulVecLin →
      w ∈ LinearMap.range ι.mulVecLin) :
    (Q * X * ι).rank =
      X.rank - (Module.finrank (ZMod 2) ↥(LinearMap.ker Q.mulVecLin) +
        (m - Module.finrank (ZMod 2) ↥(LinearMap.range ι.mulVecLin))) := by
  have h2le : LinearMap.ker (Q.mulVecLin.comp X.mulVecLin) ≤ LinearMap.range ι.mulVecLin := by
    intro w hw
    apply h2 w
    simpa [LinearMap.mem_ker, LinearMap.comp_apply, Matrix.mulVecLin_apply] using hw
  have hmain := finrank_range_comp_comp_eq Q.mulVecLin X.mulVecLin ι.mulVecLin h1 h2le
  have hrange_eq : LinearMap.range (Q * X * ι).mulVecLin =
      LinearMap.range (Q.mulVecLin.comp (X.mulVecLin.comp ι.mulVecLin)) := by
    simp only [Matrix.mulVecLin_mul, LinearMap.comp_assoc]
  have hrank : (Q * X * ι).rank =
      finrank (ZMod 2) (LinearMap.range (Q.mulVecLin.comp (X.mulVecLin.comp ι.mulVecLin))) := by
    rw [Matrix.rank, hrange_eq]
  rw [hrank, hmain, Module.finrank_fin_fun]
  rfl

end Commons.LinearAlgebra.Matrix