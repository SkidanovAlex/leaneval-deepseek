import Mathlib
import Submission.Work.ORTorsion.Defs

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.ORTorsion.Grading

open scoped TensorProduct

open Work.ORTorsion

open Work.ORTorsion.LaurentBase

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]

/-- The degree-`0` coordinate of an element of `D(N)` sitting inside `R` is the element itself. -/
private theorem coord_zero_DN (L : TorsionData K G U) {H : Subgroup G}
    {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (d : ↥(L.D Lb.N)) :
    Lb.coord 0 ⟨(d : U), Lb.DN_le_R d.2⟩ = d := by
  have h0 : (⟨(d : U), Lb.DN_le_R d.2⟩ : ↥Lb.R)
      = Lb.rightMulU 0 ⟨(d : U), Lb.DN_le_R d.2⟩ := by
    apply Subtype.ext
    rw [Lb.rightMulU_coe]
    simp
  rw [h0, Lb.coord_base 0 0 d]
  simp

/-- `mapSubAlg` of a monomial with arbitrary coefficient. -/
private theorem mapSubAlg_single' {H H' : Subgroup G} (h : H ≤ H') (k : H) (c : K) :
    mapSubAlg h (MonoidAlgebra.single k c : MonoidAlgebra K H)
      = (MonoidAlgebra.single ⟨(k : G), h k.2⟩ c : MonoidAlgebra K H') := by
  rw [mapSubAlg, MonoidAlgebra.lift_single]
  change c • (MonoidAlgebra.single ⟨(k : G), h k.2⟩ (1 : K) : MonoidAlgebra K H') = _
  rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- `diagRingHom` is the algebra lift of `diagGroupHom`. -/
private theorem diagRingHom_apply {M : Type*} [Ring M] [Algebra K M] {V : Type*} [AddCommGroup V]
    [Module K V] [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Type*} [Group H] (jG : H →* G) (jM : H →* M) (x : MonoidAlgebra K H) :
    diagRingHom (K := K) (V := V) jG jM x
      = (MonoidAlgebra.lift K (Module.End K (V ⊗[K] M)) H
          (diagGroupHom (K := K) (V := V) jG jM)) x := rfl

/-- `diagGroupHom` evaluated at a point is `diagElem`. -/
private theorem diagGroupHom_apply {M : Type*} [Ring M] [Algebra K M] {V : Type*} [AddCommGroup V]
    [Module K V] [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Type*} [Group H] (jG : H →* G) (jM : H →* M) (h : H) :
    diagGroupHom (K := K) (V := V) jG jM h = diagElem (K := K) (V := V) jG jM h := rfl

/-- The diagonal `K[H]`-action on `V ⊗[K] R` is the action through `diagRingHom`. -/
private theorem smul_diagR (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (a : MonoidAlgebra K H) (w : V ⊗[K] ↥Lb.R) :
    a • w = (diagRingHom (K := K) (V := V) H.subtype Lb.genR a) w := rfl

/-- The diagonal `K[N]`-action on `V ⊗[K] D(N)` is the action through `diagRingHom`. -/
private theorem smul_diagDN (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (g : MonoidAlgebra K ↥Lb.N) (z : V ⊗[K] ↥(L.D Lb.N)) :
    g • z = (diagRingHom (K := K) (V := V) Lb.N.subtype (L.genD Lb.N) g) z := rfl

/-- The degree-`0` coordinate of `gen n · d` in `R`, for `n ∈ N` and `d ∈ D(N)`. -/
private theorem coord_genR_mul (L : TorsionData K G U) {H : Subgroup G}
    {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (n : ↥Lb.N) (d : ↥(L.D Lb.N)) :
    Lb.coord 0 (Lb.genR ⟨(n : G), LaurentBase.N_le_H Lb n.2⟩
        * (⟨(d : U), Lb.DN_le_R d.2⟩ : ↥Lb.R)) = L.genD Lb.N n * d := by
  have hgen : (Lb.genR ⟨(n : G), LaurentBase.N_le_H Lb n.2⟩ : ↥Lb.R)
      = ⟨((L.genD Lb.N n : ↥(L.D Lb.N)) : U), Lb.DN_le_R (L.gen_mem Lb.N n)⟩ := by
    apply Subtype.ext; rfl
  have hmul : (Lb.genR ⟨(n : G), LaurentBase.N_le_H Lb n.2⟩
      * (⟨(d : U), Lb.DN_le_R d.2⟩ : ↥Lb.R) : ↥Lb.R)
      = ⟨((L.genD Lb.N n * d : ↥(L.D Lb.N)) : U),
          Lb.DN_le_R (mul_mem (L.gen_mem Lb.N n) d.2)⟩ := by
    rw [hgen]; apply Subtype.ext; rfl
  rw [hmul]
  exact coord_zero_DN L Lb (L.genD Lb.N n * d)

/-- The lemma in the monomial case: a single `K[N]`-monomial acting on `V ⊗[K] D(N)` agrees with
its image in `K[H]` acting on `V ⊗[K] R`, followed by the degree-`0` coordinate. -/
private theorem mono_c (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (n : ↥Lb.N) (c : K) (z : V ⊗[K] ↥(L.D Lb.N)) :
    Mk Lb 0 ((MonoidAlgebra.single (⟨(n : G), LaurentBase.N_le_H Lb n.2⟩ : H) c :
        MonoidAlgebra K H) • (inclDN Lb z))
      = (MonoidAlgebra.single n c : MonoidAlgebra K ↥Lb.N) • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v d =>
      rw [inclDN_tmul, smul_diagR L Lb, diagRingHom_apply, MonoidAlgebra.lift_single,
        LinearMap.smul_apply, diagGroupHom_apply, diagElem_apply_tmul, LinearMap.map_smul, Mk_tmul,
        coord_genR_mul L Lb n d, smul_diagDN L Lb, diagRingHom_apply, MonoidAlgebra.lift_single,
        LinearMap.smul_apply, diagGroupHom_apply, diagElem_apply_tmul]
      rfl
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

theorem Mk_zero_mul_N {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (g : MonoidAlgebra K ↥Lb.N) (z : V ⊗[K] ↥(L.D Lb.N)) :
    Mk Lb 0 ((mapSubAlg (LaurentBase.N_le_H Lb) g : MonoidAlgebra K H) • (inclDN Lb z))
      = g • z := by
  induction g using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, add_smul, hx, hy]
  | single n c =>
      rw [mapSubAlg_single']
      exact mono_c L Lb n c z

end Work.ORTorsion.Grading
