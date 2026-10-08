import Mathlib
import Submission.Work.L2F.Props.OddSubDefs

/-!
# `comap` to `PGL(2,F)` of an odd-order subgroup is finite

Let `K ≤ PGL(2,F)` be a subgroup of odd order.  In the Gorenstein–Walter proof one needs that
the full preimage `K.comap (SL(2,F) → PGL(2,F))` is a *finite* group, so that counting arguments
(Sylow theory, `Nat.card` identities) can be applied to it.

The point is that `SL(2,F) → PGL(2,F)` has finite kernel, namely the centre of `SL(2,F)`, which is
contained in `{1, -1}` (a matrix in the centre of `SL(2,F)` is scalar with scalar entry `u`
satisfying `u² = 1`, hence `u = ±1`).  A finite kernel combined with a finite target subgroup
gives a finite preimage, which is the abstract lemma `finite_comap_of_finite_ker` below.

Note that `Odd (Nat.card K)` already forces `K` to be finite, since `Nat.card` of an infinite type
is `0`, which is not odd.
-/

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.oddsub

/-- An abstract form of the counting step: the preimage of a finite subgroup under a homomorphism
with finite kernel is finite.

Indeed, the preimage is the disjoint union, over `x` in the (finite) image `f '' (S.comap f)`, of
the fibres `f ⁻¹' {x}`; each nonempty fibre is a coset of `f.ker` (finite by hypothesis). -/
lemma finite_comap_of_finite_ker {G H : Type*} [Group G] [Group H]
    (f : G →* H) (S : Subgroup H) (hker : (f.ker : Set G).Finite)
    (hS : (S : Set H).Finite) : (S.comap f : Set G).Finite := by
  refine Set.Finite.of_finite_fibers f ?_ ?_
  · refine hS.subset ?_
    rintro y ⟨x, hx, rfl⟩
    exact hx
  · rintro y ⟨x, hx, rfl⟩
    refine (hker.image (fun w => w * x)).subset ?_
    rintro z ⟨hz1, hz2⟩
    have hzy : f z = f x := by simpa using hz2
    refine ⟨z * x⁻¹, ?_, by group⟩
    show f (z * x⁻¹) = 1
    rw [map_mul, map_inv, hzy, mul_inv_cancel]

/-- The kernel of `SL(2,F) → PGL(2,F)` is the centre of `SL(2,F)`, which is contained in
`{1, -1}`: a central element is a scalar matrix with scalar entry `u` and determinant `u² = 1`,
so `u = ±1` (in a field, `(u - 1) * (u + 1) = 0`).  In particular the kernel is finite. -/
lemma toPGL_ker_finite (F : Type*) [Field F] :
    ((Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).ker :
      Set (Matrix.SpecialLinearGroup (Fin 2) F)).Finite := by
  rw [Matrix.SpecialLinearGroup.toPGL_ker]
  have h1 : ({g : Matrix.SpecialLinearGroup (Fin 2) F |
      Matrix.SpecialLinearGroup.toGL g = 1} : Set _).Finite :=
    Set.Subsingleton.finite fun a ha b hb =>
      Matrix.SpecialLinearGroup.toGL_injective (ha.trans hb.symm)
  have h2 : ({g : Matrix.SpecialLinearGroup (Fin 2) F |
      Matrix.SpecialLinearGroup.toGL g = -1} : Set _).Finite :=
    Set.Subsingleton.finite fun a ha b hb =>
      Matrix.SpecialLinearGroup.toGL_injective (ha.trans hb.symm)
  refine (h1.union h2).subset ?_
  intro g hg
  have hgGL : Matrix.SpecialLinearGroup.toGL g ∈ Subgroup.center (GL (Fin 2) F) :=
    (Matrix.SpecialLinearGroup.toGL_mem_center_iff g).mpr hg
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range] at hgGL
  obtain ⟨u, hu⟩ := hgGL
  have hu2 : u ^ 2 = 1 := by
    have h : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL g) = 1 :=
      Matrix.SpecialLinearGroup.coeToGL_det g
    rw [← hu, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h
    exact h
  have hprod : ((u : F) - 1) * ((u : F) + 1) = 0 := by
    have hv : (u : F) ^ 2 = 1 := by
      have := congrArg (fun x : Fˣ => (x : F)) hu2
      simpa using this
    have : ((u : F) - 1) * ((u : F) + 1) = (u : F) ^ 2 - 1 := by ring
    rw [this, hv]; ring
  rcases mul_eq_zero.mp hprod with h | h
  · left
    have hu1 : u = 1 := by
      refine Units.ext ?_
      have h' : (u : F) = 1 := sub_eq_zero.mp h
      simpa using h'
    change Matrix.SpecialLinearGroup.toGL g = 1
    rw [← hu, hu1]
    exact map_one (Matrix.GeneralLinearGroup.scalar (Fin 2))
  · right
    have hum1 : u = -1 := by
      refine Units.ext ?_
      have h' : (u : F) = -1 := by linear_combination h
      simpa using h'
    change Matrix.SpecialLinearGroup.toGL g = -1
    rw [← hu, hum1]
    ext i j
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    by_cases hij : i = j <;> simp [Matrix.scalar, hij]

theorem finite_comap_toPGL (F : Type*) [Field F]
    (K : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) (hodd : Odd (Nat.card K)) :
    Finite (Subgroup.comap Matrix.SpecialLinearGroup.toPGL K) := by
  have hK : Finite K := Nat.finite_of_card_ne_zero (by
    intro h0
    obtain ⟨k, hk⟩ := hodd
    omega)
  exact Set.finite_coe_iff.mpr
    (finite_comap_of_finite_ker Matrix.SpecialLinearGroup.toPGL K
      (toPGL_ker_finite F) (Set.finite_coe_iff.mp hK))

end Work.L2F.Props.oddsub
