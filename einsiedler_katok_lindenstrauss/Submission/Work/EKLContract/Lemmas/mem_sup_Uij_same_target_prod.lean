import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.isHoro_Uij

/-!
# `U_ij ⊔ U_kj` is the set of products `u_ij(s) · u_kj(t)`

For two root subgroups `U_ij`, `U_kj` with the *same target* `j` and distinct sources
`i ≠ k`, the join `U_ij ⊔ U_kj` consists exactly of the elements `u_ij(s) * u_kj(t)`.

The mathematical content is that `u_ij(s) = 1 + s E_ij` and `u_kj(t) = 1 + t E_kj` commute
(the products `E_ij E_kj = δ_{jk} E_ij` and `E_kj E_ij = δ_{ji} E_kj` both vanish because
`j ∉ {i,k}`), so that the set of products is stable under multiplication and inversion and
hence is a subgroup; it contains both generators, so it is the join.

The products are computed with `Matrix.single_mul_single_of_ne`; `Subgroup.mem_sup` itself
only applies in *commutative* groups, which `SL₃(ℝ)` is not, hence the explicit subgroup.
-/

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLContract.Lemmas

open Work.EKLContract

/-- The matrix of the product of two transvections with the same target: it is the identity
except for the entries `(i,j)` and `(k,j)`, where it carries `s` and `t`. -/
theorem toMat_uij_mul_same_target {i j k : Fin 3} (hij : i ≠ j) (hkj : k ≠ j) (s t : ℝ) :
    toMat (uij hij s * uij hkj t) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j s + Matrix.single k j t := by
  have hAB : Matrix.single i j s * Matrix.single k j t = (0 : Matrix (Fin 3) (Fin 3) ℝ) :=
    Matrix.single_mul_single_of_ne s i j k hkj.symm t
  rw [toMat_mul, horoUij_toMat hij, horoUij_toMat hkj]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hAB, add_zero]

/-- Two transvections with the same target commute. -/
theorem uij_mul_comm_same_target {i j k : Fin 3} (hij : i ≠ j) (hkj : k ≠ j) (s t : ℝ) :
    uij hij s * uij hkj t = uij hkj t * uij hij s := by
  apply ext_toMat
  rw [toMat_uij_mul_same_target hij hkj s t, toMat_uij_mul_same_target hkj hij t s]
  abel

/-- `u_ij(a + c) = u_ij(a) * u_ij(c)`. -/
theorem uij_add' {i j : Fin 3} (hij : i ≠ j) (a c : ℝ) :
    uij hij (a + c) = uij hij a * uij hij c :=
  Matrix.SpecialLinearGroup.transvection_add hij a c

/-- `u_ij(s)⁻¹ = u_ij(-s)`. -/
theorem uij_inv' {i j : Fin 3} (hij : i ≠ j) (s : ℝ) : (uij hij s)⁻¹ = uij hij (-s) :=
  Matrix.SpecialLinearGroup.transvection_inv hij s

/-- The product formula for the set `{u_ij(s) · u_kj(t)}`: it is stable under multiplication. -/
theorem uij_mul_prod {i j k : Fin 3} (hij : i ≠ j) (hkj : k ≠ j) (a b c d : ℝ) :
    uij hij (a + c) * uij hkj (b + d) =
      (uij hij a * uij hkj b) * (uij hij c * uij hkj d) := by
  rw [uij_add' hij a c, uij_add' hkj b d,
      mul_assoc (uij hij a) (uij hij c) (uij hkj b * uij hkj d),
      ← mul_assoc (uij hij c) (uij hkj b) (uij hkj d),
      uij_mul_comm_same_target hij hkj c b,
      mul_assoc (uij hkj b) (uij hij c) (uij hkj d),
      ← mul_assoc (uij hij a) (uij hkj b) (uij hij c * uij hkj d)]

/-- The set of products `{u_ij(s) · u_kj(t)}`, as a subgroup of `SL₃(ℝ)`. -/
def supUijSameTarget {i j k : Fin 3} (hij : i ≠ j) (hkj : k ≠ j) : Subgroup SL3 where
  carrier := Set.range (fun p : ℝ × ℝ => uij hij p.1 * uij hkj p.2)
  one_mem' := ⟨(0, 0), by simp only [horoUij_zero hij, horoUij_zero hkj, mul_one]⟩
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨(p.1 + q.1, p.2 + q.2), uij_mul_prod hij hkj p.1 p.2 q.1 q.2⟩
  inv_mem' := by
    rintro _ ⟨p, rfl⟩
    refine ⟨(-p.1, -p.2), ?_⟩
    rw [mul_inv_rev, uij_inv' hkj p.2, uij_inv' hij p.1]
    exact uij_mul_comm_same_target hij hkj (-p.1) (-p.2)

theorem mem_sup_Uij_same_target_prod {i j k : Fin 3} (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k)
    (g : Work.EKLContract.SL3) :
    g ∈ Work.EKLContract.Uij hij ⊔ Work.EKLContract.Uij hkj ↔
      ∃ s t : ℝ, Work.EKLContract.uij hij s * Work.EKLContract.uij hkj t = g := by
  constructor
  · intro hg
    have hle : Uij hij ⊔ Uij hkj ≤ supUijSameTarget hij hkj := by
      refine sup_le ?_ ?_
      · intro u hu
        obtain ⟨s, rfl⟩ := (horoUij_mem_iff hij u).mp hu
        exact ⟨(s, 0), by simp only [horoUij_zero hkj, mul_one]⟩
      · intro u hu
        obtain ⟨t, rfl⟩ := (horoUij_mem_iff hkj u).mp hu
        exact ⟨(0, t), by simp only [horoUij_zero hij, one_mul]⟩
    obtain ⟨p, hp⟩ := hle hg
    exact ⟨p.1, p.2, hp⟩
  · rintro ⟨s, t, rfl⟩
    exact Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨s, rfl⟩)
      (Subgroup.subset_closure ⟨t, rfl⟩)

end Work.EKLContract.Lemmas
