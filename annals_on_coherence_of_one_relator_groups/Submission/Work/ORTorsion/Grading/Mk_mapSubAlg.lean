import Mathlib
import Submission.Work.ORTorsion.Defs
import Submission.Work.ORTorsion.Grading.Mk_Tm
import Submission.Work.ORTorsion.Grading.Mk_inclDN
import Submission.Work.ORTorsion.Grading.Mk_zero_mul_N
import Submission.Work.ORTorsion.Grading.Mk_zero_single
import Submission.Work.ORTorsion.Grading.commute_Tm
import Submission.Work.ORTorsion.Grading.expansion
import Submission.Work.ORTorsion.Grading.exists_single_smul_mem_range

set_option maxHeartbeats 1000000

namespace Work.ORTorsion.Grading

open scoped TensorProduct

open Work.ORTorsion

open Work.ORTorsion.LaurentBase

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]
  {gen : G →* Uˣ} {D : Subgroup G → Subalgebra K U} {H : Subgroup G} {φ : H →* Multiplicative ℤ}

/-! ## `diagRingHom` as the underlying algebra lift -/

private theorem diagRingHom_apply' {K : Type*} [Field K] {G : Type*} [Group G] {M : Type*}
    [Ring M] [Algebra K M] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {G' : Type*} [Group G'] (jG : G' →* G) (jM : G' →* M) (x : MonoidAlgebra K G') :
    diagRingHom (K := K) (V := V) jG jM x
      = (MonoidAlgebra.lift K (Module.End K (V ⊗[K] M)) G'
          (diagGroupHom (K := K) (V := V) jG jM)) x := rfl

/-! ## Multiplication by an element of `D(N)` commutes with the coordinates -/

/-- In `R`, `inc d · (c · u ^ i) = inc (d * c) · u ^ i`. -/
private theorem mul_inclusion_rightMulU (Lb : LaurentBase K U G gen D H φ)
    (d c : ↥(D Lb.N)) (i : ℤ) :
    Subalgebra.inclusion Lb.DN_le_R d * Lb.rightMulU i ⟨(c : U), Lb.DN_le_R c.2⟩
      = Lb.rightMulU i (Subalgebra.inclusion Lb.DN_le_R (d * c)) := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Lb.rightMulU_coe, Subalgebra.coe_inclusion, mul_assoc]

/-- The `coord_base` rule phrased with `Subalgebra.inclusion`. -/
private theorem coord_inclusion_inc (Lb : LaurentBase K U G gen D H φ) (j : ℤ)
    (d : ↥(D Lb.N)) :
    Lb.coord j (Subalgebra.inclusion Lb.DN_le_R d) = if j = 0 then d else 0 :=
  coord_inclusion Lb j d

/-- **The grading is `D(N)`-linear.**  For `d ∈ D(N)`, `y ∈ R` and `j ∈ ℤ`,
`coord j (d · y) = d · coord j y`. -/
private theorem coord_inclusion_mul (Lb : LaurentBase K U G gen D H φ)
    (d : ↥(D Lb.N)) (y : ↥Lb.R) (j : ℤ) :
    Lb.coord j (Subalgebra.inclusion Lb.DN_le_R d * y) = d * Lb.coord j y := by
  obtain ⟨S, hS⟩ := Lb.coord_expand y
  have hmem : ∀ i, i ∉ S → Lb.coord i y = 0 := by
    intro i hi
    have h1 : Lb.coord i y
        = ∑ k ∈ S, (if i = k then Lb.coord k y else 0) := by
      conv_lhs => rw [← hS]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Lb.coord_shift i k, coord_inclusion]
      simp only [sub_eq_zero]
    rw [h1, Finset.sum_ite_eq, if_neg hi]
  have key : Subalgebra.inclusion Lb.DN_le_R d * y
      = ∑ i ∈ S, Lb.rightMulU i (Subalgebra.inclusion Lb.DN_le_R (d * Lb.coord i y)) := by
    conv_lhs => rw [← hS]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_inclusion_rightMulU Lb d (Lb.coord i y) i]
  have hterm : ∀ i, Lb.coord j
        (Lb.rightMulU i (Subalgebra.inclusion Lb.DN_le_R (d * Lb.coord i y)))
      = (if j = i then d * Lb.coord i y else 0) := by
    intro i
    rw [Lb.coord_shift j i, coord_inclusion_inc]
    simp only [sub_eq_zero]
  rw [key, map_sum, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq]
  by_cases hj : j ∈ S
  · rw [if_pos hj]
  · rw [if_neg hj, hmem j hj, mul_zero]

/-! ## The tensor-level statements -/

/-- The diagonal `K[H]`-action of the monomial `single ⟨n⟩ c` on `V ⊗[K] R`. -/
private theorem single_smul_coe_H {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (L : TorsionData K G U) {H : Subgroup G} {φ : H →* Multiplicative ℤ}
    (Lb : LaurentBase K U G L.gen L.D H φ) (n : ↥Lb.N) (c : K) (w : V ⊗[K] ↥Lb.R) :
    (MonoidAlgebra.single ⟨(n : G), LaurentBase.N_le_H Lb n.2⟩ c : MonoidAlgebra K H) • w
      = c • (diagElem (K := K) (V := V) H.subtype Lb.genR
          ⟨(n : G), LaurentBase.N_le_H Lb n.2⟩ w) := by
  change (diagRingHom (K := K) (V := V) H.subtype Lb.genR
      (MonoidAlgebra.single ⟨(n : G), LaurentBase.N_le_H Lb n.2⟩ c)) w = _
  rw [diagRingHom_apply', MonoidAlgebra.lift_single, LinearMap.smul_apply]
  rfl

/-- The diagonal `K[N]`-action of the monomial `single n c` on `V ⊗[K] D(N)`. -/
private theorem single_smul_coe_N {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (L : TorsionData K G U) {H : Subgroup G} {φ : H →* Multiplicative ℤ}
    (Lb : LaurentBase K U G L.gen L.D H φ) (n : ↥Lb.N) (c : K)
    (z : V ⊗[K] ↥(L.D Lb.N)) :
    (MonoidAlgebra.single n c : MonoidAlgebra K ↥Lb.N) • z
      = c • (diagElem (K := K) (V := V) Lb.N.subtype (L.genD Lb.N) n z) := by
  change (diagRingHom (K := K) (V := V) Lb.N.subtype (L.genD Lb.N)
      (MonoidAlgebra.single n c)) z = _
  rw [diagRingHom_apply', MonoidAlgebra.lift_single, LinearMap.smul_apply]
  rfl

/-- The degree-`j` coordinate of the diagonal action of `n ∈ N` on `V ⊗[K] R` equals the
diagonal action of `n` on the degree-`j` coordinate. -/
private theorem Mk_diagElem {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (L : TorsionData K G U) {H : Subgroup G} {φ : H →* Multiplicative ℤ}
    (Lb : LaurentBase K U G L.gen L.D H φ) (n : ↥Lb.N) (j : ℤ)
    (w : V ⊗[K] ↥Lb.R) :
    Mk Lb j (diagElem (K := K) (V := V) H.subtype Lb.genR
        ⟨(n : G), LaurentBase.N_le_H Lb n.2⟩ w)
      = diagElem (K := K) (V := V) Lb.N.subtype (L.genD Lb.N) n (Mk Lb j w) := by
  have hgen : Lb.genR ⟨(n : G), LaurentBase.N_le_H Lb n.2⟩
      = Subalgebra.inclusion Lb.DN_le_R (L.genD Lb.N n) := Subtype.ext rfl
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v y =>
      rw [diagElem_apply_tmul, Mk_tmul, Mk_tmul, diagElem_apply_tmul, hgen,
        coord_inclusion_mul Lb (L.genD Lb.N n) y j]
      rfl
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-! ## `mapSubAlg` on monomials -/

private theorem mapSubAlg_single' {H H' : Subgroup G} (h : H ≤ H') (k : H) (c : K) :
    mapSubAlg h (MonoidAlgebra.single k c : MonoidAlgebra K H)
      = (MonoidAlgebra.single ⟨(k : G), h k.2⟩ c : MonoidAlgebra K H') := by
  rw [mapSubAlg, MonoidAlgebra.lift_single]
  change c • (MonoidAlgebra.single ⟨(k : G), h k.2⟩ (1 : K) : MonoidAlgebra K H') = _
  rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-! ## The target theorem -/

/-- **The degree-`j` coordinate map is `K[N]`-linear.** -/
theorem Mk_mapSubAlg {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (g : MonoidAlgebra K ↥Lb.N) (j : ℤ) (w : TensorProduct K V ↥Lb.R) :
    LaurentBase.Mk Lb j ((mapSubAlg (LaurentBase.N_le_H Lb) g : MonoidAlgebra K H) • w)
      = g • (LaurentBase.Mk Lb j w) := by
  induction g using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, add_smul, map_add, hx, hy]
  | single n c =>
      rw [mapSubAlg_single']
      rw [single_smul_coe_H L Lb n c w, single_smul_coe_N L Lb n c, map_smul,
        Mk_diagElem L Lb n j]

end Work.ORTorsion.Grading
