import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Grading

open scoped TensorProduct

open Work.ORTorsion

open Work.ORTorsion.LaurentBase

/-- The `K`-linear action of a basis element `single h 1` of `K[H]` on `V ⊗[K] R` is the
diagonal action `diagElem` of `h`. -/
theorem single_smul_diagElem {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (h : H) (w : V ⊗[K] ↥Lb.R) :
    (MonoidAlgebra.single h (1 : K) : MonoidAlgebra K H) • w
      = diagElem (K := K) (V := V) H.subtype Lb.genR h w := by
  change (diagRingHom (K := K) (V := V) H.subtype Lb.genR
    (MonoidAlgebra.single h (1 : K))) w = _
  rw [diagRingHom_single]
  rfl

/-- The `K`-linear action of a basis element `single n 1` of `K[N]` on `V ⊗[K] D(N)` is the
diagonal action `diagElem` of `n`. -/
theorem single_smul_diagElem_N {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (n : ↥Lb.N) (z : V ⊗[K] ↥(L.D Lb.N)) :
    (MonoidAlgebra.single n (1 : K) : MonoidAlgebra K ↥Lb.N) • z
      = diagElem (K := K) (V := V) Lb.N.subtype (L.genD Lb.N) n z := by
  change (diagRingHom (K := K) (V := V) Lb.N.subtype (L.genD Lb.N)
    (MonoidAlgebra.single n (1 : K))) z = _
  rw [diagRingHom_single]
  rfl

/-- The degree-`0` coordinate of an element of `D(N)` sitting in `R` in degree `0` is itself. -/
theorem coord_zero_of_DN {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {H : Subgroup G} {φ : H →* Multiplicative ℤ}
    (Lb : LaurentBase K U G L.gen L.D H φ) (e : ↥(L.D Lb.N)) :
    Lb.coord 0 (⟨(e : U), Lb.DN_le_R e.2⟩ : ↥Lb.R) = e := by
  have h0 : (⟨(e : U), Lb.DN_le_R e.2⟩ : ↥Lb.R)
      = Lb.rightMulU 0 ⟨(e : U), Lb.DN_le_R e.2⟩ := by
    apply Subtype.ext
    rw [Lb.rightMulU_coe]
    simp
  rw [h0, Lb.coord_base 0 0 e, if_pos rfl]

theorem Mk_zero_single {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (n : ↥Lb.N) (z : V ⊗[K] ↥(L.D Lb.N)) :
    Mk Lb 0 ((MonoidAlgebra.single (⟨(n : G), LaurentBase.N_le_H Lb n.2⟩ : H) (1 : K) :
        MonoidAlgebra K H) • (inclDN Lb z))
      = (MonoidAlgebra.single n (1 : K) : MonoidAlgebra K ↥Lb.N) • z := by
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul v d =>
      rw [single_smul_diagElem L Lb, single_smul_diagElem_N L Lb, inclDN_tmul,
        diagElem_apply_tmul, diagElem_apply_tmul, Mk_tmul]
      have hgenR : Lb.genR (⟨(n : G), LaurentBase.N_le_H Lb n.2⟩ : H)
          = (⟨((L.genD Lb.N n : U)), Lb.DN_le_R (L.genD Lb.N n).2⟩ : ↥Lb.R) := by
        ext; rfl
      have hprod : (⟨((L.genD Lb.N n : U)), Lb.DN_le_R (L.genD Lb.N n).2⟩ : ↥Lb.R)
            * ⟨(d : U), Lb.DN_le_R d.2⟩
          = ⟨(((L.genD Lb.N n * d : ↥(L.D Lb.N)) : U)),
              Lb.DN_le_R (L.genD Lb.N n * d).2⟩ := by
        ext; rfl
      have hc : Lb.coord 0 (Lb.genR (⟨(n : G), LaurentBase.N_le_H Lb n.2⟩ : H)
          * ⟨(d : U), Lb.DN_le_R d.2⟩) = L.genD Lb.N n * d := by
        rw [hgenR, hprod]
        exact coord_zero_of_DN L Lb (L.genD Lb.N n * d)
      rw [hc]
      rfl
  | add z w hz hw =>
      simp only [map_add, smul_add, hz, hw]

end Work.ORTorsion.Grading
