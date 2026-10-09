import Mathlib
import Submission.Work.SSGRoute.CC.MagFourDefs
import Submission.Work.SSGRoute.magLead_inv_cube_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CC

open Work.SSGRoute.prop5

open scoped commutatorElement

/-!
# The Magnus leading term of the "inverted commutator" `u⁻¹ v⁻¹ u v`

For `u`, `v` in the second term `γ₂ = ⁅⊤,⊤⁆` of the lower central series of a free group
(Mathlib indexing: `lowerCentralSeries 1`) we compute the degree-`≤4` Magnus leading term of the
group commutator `u⁻¹ v⁻¹ u v = ⁅u⁻¹, v⁻¹⁆` at truncation `5`:

`magLead 5 (u⁻¹ * v⁻¹ * u * v) = magLead 5 u * magLead 5 v - magLead 5 v * magLead 5 u`.

The point is that although `magLead 5 (u⁻¹) ≠ - magLead 5 u` in general (the truncation `5` is too
small for the strict inverse formula, which would need `5 ≤ 2·2`), the corrections `a²`, `b²`
(`a = magLead 5 u`, `b = magLead 5 v`) only contribute terms of degree `≥ 6`, which already vanish
modulo `fil X 5`.
-/

/-- A product of two elements of the truncation `FreeAssoc X ⧸ fil X 5` of degrees `i` and `j` with
`i + j ≥ 5` vanishes. -/
lemma filq_five_mul_eq_zero {X : Type} {i j : ℕ} (h : 5 ≤ i + j)
    {x y : FreeAssoc X ⧸ fil X 5} (hx : x ∈ filq X 5 i) (hy : y ∈ filq X 5 j) :
    x * y = 0 :=
  mem_filq_self_eq_zero' (filq_antitone X 5 h (mul_mem_filq X 5 i j hx hy))

/-- The square of an element of the degree-`≥2` part of the truncation at `5` has degree `≥ 4`. -/
lemma sq_mem_filq_two {X : Type} {x : FreeAssoc X ⧸ fil X 5} (hx : x ∈ filq X 5 2) :
    x ^ 2 ∈ filq X 5 4 := by
  rw [pow_two]
  exact mul_mem_filq X 5 2 2 hx hx

/-- The cube of an element of the degree-`≥2` part vanishes in the truncation at `5`. -/
lemma cube_eq_zero_of_mem_filq_two {X : Type} {x : FreeAssoc X ⧸ fil X 5}
    (hx : x ∈ filq X 5 2) : x ^ 3 = 0 := by
  have h2 : x ^ 2 ∈ filq X 5 4 := sq_mem_filq_two hx
  have h3 : x ^ 3 = x ^ 2 * x := by noncomm_ring
  rw [h3]
  exact filq_five_mul_eq_zero (i := 4) (j := 2) (by norm_num) h2 hx

/-- **The algebraic core.** In the truncation at `5`, if `a` and `b` both have degree `≥ 2` then
the "inverse corrections" `-a + a²` and `-b + b²` have the same ring commutator as `a` and `b`:
all the extra terms have degree `≥ 6` and vanish. -/
lemma commutator_inv_form {X : Type} {a b : FreeAssoc X ⧸ fil X 5}
    (ha : a ∈ filq X 5 2) (hb : b ∈ filq X 5 2) :
    (-a + a ^ 2) * (-b + b ^ 2) - (-b + b ^ 2) * (-a + a ^ 2) = a * b - b * a := by
  have ha2 : a ^ 2 ∈ filq X 5 4 := sq_mem_filq_two ha
  have hb2 : b ^ 2 ∈ filq X 5 4 := sq_mem_filq_two hb
  have hab2 : a * b ^ 2 = 0 := filq_five_mul_eq_zero (i := 2) (j := 4) (by norm_num) ha hb2
  have ha2b : a ^ 2 * b = 0 := filq_five_mul_eq_zero (i := 4) (j := 2) (by norm_num) ha2 hb
  have ha2b2 : a ^ 2 * b ^ 2 = 0 := filq_five_mul_eq_zero (i := 4) (j := 4) (by norm_num) ha2 hb2
  have hba2 : b * a ^ 2 = 0 := filq_five_mul_eq_zero (i := 2) (j := 4) (by norm_num) hb ha2
  have hb2a : b ^ 2 * a = 0 := filq_five_mul_eq_zero (i := 4) (j := 2) (by norm_num) hb2 ha
  have hb2a2 : b ^ 2 * a ^ 2 = 0 := filq_five_mul_eq_zero (i := 4) (j := 4) (by norm_num) hb2 ha2
  have e1 : (-a + a ^ 2) * (-b + b ^ 2) = a * b := by
    rw [show (-a + a ^ 2) * (-b + b ^ 2)
          = a * b - a * b ^ 2 - a ^ 2 * b + a ^ 2 * b ^ 2 from by noncomm_ring,
      hab2, ha2b, ha2b2]
    simp
  have e2 : (-b + b ^ 2) * (-a + a ^ 2) = b * a := by
    rw [show (-b + b ^ 2) * (-a + a ^ 2)
          = b * a - b * a ^ 2 - b ^ 2 * a + b ^ 2 * a ^ 2 from by noncomm_ring,
      hba2, hb2a, hb2a2]
    simp
  rw [e1, e2]

theorem magLead_commutator_inv_pair {X : Type} (u v : FreeGroup X)
    (hu : u ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 1)
    (hv : v ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries 1) :
    Work.SSGRoute.prop5.magLead 5 (u⁻¹ * v⁻¹ * u * v) =
      Work.SSGRoute.prop5.magLead 5 u * Work.SSGRoute.prop5.magLead 5 v -
        Work.SSGRoute.prop5.magLead 5 v * Work.SSGRoute.prop5.magLead 5 u := by
  -- The bracket lemma at `N = 5`, `p = q = 2` gives the commutator identity modulo `filq X 5 5 = ⊥`.
  have hcom := magLead_commutator (X := X) 5 2 2 (by norm_num) (by norm_num) (by norm_num)
    (Subgroup.inv_mem _ hu) (Subgroup.inv_mem _ hv)
  have hkey : magLead 5 ⁅u⁻¹, v⁻¹⁆
      = magLead 5 u⁻¹ * magLead 5 v⁻¹ - magLead 5 v⁻¹ * magLead 5 u⁻¹ :=
    sub_eq_zero.mp (mem_filq_self_eq_zero' (filq_antitone X 5 (show 5 ≤ 2 + 2 + 1 by norm_num) hcom))
  -- The degree-`2` part of the leading terms.
  have hu2 : magLead 5 u ∈ filq X 5 2 := magLead_mem_filq 5 2 (by norm_num) (by norm_num) hu
  have hv2 : magLead 5 v ∈ filq X 5 2 := magLead_mem_filq 5 2 (by norm_num) (by norm_num) hv
  -- The inverses, via the cube-zero formula.
  have hinvu : magLead 5 u⁻¹ = -magLead 5 u + (magLead 5 u) ^ 2 :=
    magLead_inv_cube_zero 5 u (cube_eq_zero_of_mem_filq_two hu2)
  have hinvv : magLead 5 v⁻¹ = -magLead 5 v + (magLead 5 v) ^ 2 :=
    magLead_inv_cube_zero 5 v (cube_eq_zero_of_mem_filq_two hv2)
  have harg : u⁻¹ * v⁻¹ * u * v = ⁅u⁻¹, v⁻¹⁆ := by
    simp [commutatorElement_def]
  rw [harg, hkey, hinvu, hinvv]
  exact commutator_inv_form hu2 hv2

end Work.SSGRoute.CC
