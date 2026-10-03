import Mathlib
import Submission.Work.ORTorsion.Defs

/-- v4.35 port: `TensorProduct.induction_on` lost `@[elab_as_elim]` when deprecated. -/
@[elab_as_elim] private theorem tpInductionOn' {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] {motive : TensorProduct R M N → Prop}
    (z : TensorProduct R M N) (zero : motive 0) (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z zero tmul add


namespace Work.ORTorsion.Grading

open scoped TensorProduct

open Work.ORTorsion

open Work.ORTorsion.LaurentBase

/-- The diagonal action of a single group element `h : H` on `V ⊗[K] ↥Lb.R` commutes with the
right multiplication `Tm Lb i` by the power `u ^ i` in the Laurent algebra `R`.  Both sides are
`TensorProduct.map`s, and the assertion reduces to associativity in the ring `↥Lb.R`:
`a * (y * u ^ i) = (a * y) * u ^ i`. -/
lemma diagElem_Tm_comm {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (h : H) (i : ℤ) :
    ((diagElem (K := K) (V := V) H.subtype Lb.genR h).comp (Tm Lb i)) =
      ((Tm Lb i).comp (diagElem (K := K) (V := V) H.subtype Lb.genR h)) := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  refine tpInductionOn' z ?_ ?_ ?_
  · simp
  · intro v y
    rw [Tm_tmul, diagElem_apply_tmul, diagElem_apply_tmul, Tm_tmul]
    congr 1
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, LaurentBase.rightMulU_coe]
    rw [mul_assoc]
  · intro x y hx hy
    simp only [map_add, hx, hy]

/-- The diagonal algebra map `diagRingHom` is `K`-linear: it is the `RingHom` underlying the
`K`-algebra homomorphism `MonoidAlgebra.lift K _ H (diagGroupHom jG jM)`. -/
lemma diagRingHom_smul {K : Type*} [Field K] {G : Type*} [Group G] {M : Type*} [Ring M]
    [Algebra K M] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H' : Type*} [Group H'] (jG : H' →* G) (jM : H' →* M) (r : K)
    (x : MonoidAlgebra K H') :
    diagRingHom (K := K) (V := V) jG jM (r • x) =
      r • diagRingHom (K := K) (V := V) jG jM x := by
  show (MonoidAlgebra.lift K (Module.End K (V ⊗[K] M)) H' (diagGroupHom jG jM)) (r • x)
      = r • (MonoidAlgebra.lift K (Module.End K (V ⊗[K] M)) H' (diagGroupHom jG jM)) x
  exact map_smul _ r x

theorem commute_Tm {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]
    (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (x : MonoidAlgebra K H) (i : ℤ) (z : V ⊗[K] ↥Lb.R) :
    x • (Tm Lb i z) = Tm Lb i (x • z) := by
  revert z
  refine MonoidAlgebra.induction_on (motive := fun x => ∀ z : V ⊗[K] ↥Lb.R,
      x • (Tm Lb i z) = Tm Lb i (x • z)) x ?_ ?_ ?_
  · intro h z
    change (diagRingHom (K := K) (V := V) H.subtype Lb.genR (MonoidAlgebra.of K H h))
        (Tm Lb i z)
      = Tm Lb i ((diagRingHom (K := K) (V := V) H.subtype Lb.genR
          (MonoidAlgebra.of K H h)) z)
    rw [MonoidAlgebra.of_apply, diagRingHom_single]
    exact LinearMap.congr_fun (diagElem_Tm_comm (K := K) L Lb h i) z
  · intro x y hx hy z
    simp only [add_smul, map_add, hx, hy]
  · intro r x hx z
    change (diagRingHom (K := K) (V := V) H.subtype Lb.genR (r • x)) (Tm Lb i z)
      = Tm Lb i ((diagRingHom (K := K) (V := V) H.subtype Lb.genR (r • x)) z)
    rw [diagRingHom_smul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    congr 1
    exact hx z

end Work.ORTorsion.Grading
