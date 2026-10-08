import Mathlib
import Submission.Work.Models.PSL2.Defs
import Submission.Work.Models.PSL2.D_facts
import Submission.Work.Models.PSL2.U_facts
import Submission.Work.Models.PSL2.B_facts
import Submission.Work.Models.PSL2.B_stronglyEmbedded

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.PSL2.B_split_setup` — the matrix shape of an involution outside the Borel

Let `F` be a field of characteristic `2`, `G = SL(2,F)`, `B` the standard Borel (the upper
triangular matrices) and `U` its unipotent radical (`U = {1 + t E₀₁ | t ∈ F}`, the standard
maximal unipotent subgroup).  This file collects the *matrix* facts used in the proof that
`B` splits over `U` along any involution `t ∉ B`:

write `t = !![a, b; c, d]` for the matrix of `t`.  Since `t` is an involution (`t^2 = 1`) and
`t ∉ B` (so `c ≠ 0`),

* `t 1 1 = t 0 0` (`t_mat_11_eq_00`) — the `(1,0)`-entry of `t² = 1` gives `c (t₀₀ + t₁₁) = 0`;
* `t 0 0 ^ 2 + t 0 1 * t 1 0 = 1` (`t_mat_key`) — the `(0,0)`-entry of `t² = 1`;
* for `x ∈ B` (so `x 1 0 = 0`), the `(1,0)`-entry of `t x t` is
  `c (a (x₀₀ + x₁₁) + c x₀₁)` (`t_conj_entry`).

Consequently `x ∈ B ⊓ B^t` if and only if `x ∈ B` and `a (x₀₀ + x₁₁) + c x₀₁ = 0`
(`mem_twoPoint_iff`).  The set of such `x` is exactly the "conjugated diagonal torus"
`{ !![u, s (u + u⁻¹); 0, u⁻¹] | u ∈ Fˣ }` with `s = a / c` (`torusConj`, and
`torusConj_mem_twoPoint` for the membership); this is the complement of `U` in `B`.

Finally `isCyclic_map_conj` records that a conjugate of a cyclic subgroup is cyclic.
-/

namespace Work.Models.PSL2

open Matrix

variable {F : Type*} [Field F] [CharP F 2]

/-- An element of order `2` is its own inverse. -/
lemma mul_self_of_orderOf_two {t : SL2 F} (ht : orderOf t = 2) : t * t = 1 := by
  have h : t ^ 2 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, ht]
  simpa [pow_two] using h

/-- The underlying matrix of an involution of `SL(2,F)` has square `1`. -/
lemma t_mul_self_coe {t : SL2 F} (ht : orderOf t = 2) :
    (t : Matrix (Fin 2) (Fin 2) F) * (t : Matrix (Fin 2) (Fin 2) F) = 1 := by
  have h := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F)) (mul_self_of_orderOf_two ht)
  rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h

/-- An element of `SL(2,F)` outside the Borel has non-zero `(1,0)`-entry. -/
lemma t_mat_10_ne {t : SL2 F} (htB : t ∉ B (F := F)) :
    (t : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := fun h => htB (mem_B_iff'.mpr h)

/-- **An involution outside `B` has equal diagonal entries.**  The `(1,0)`-entry of `t * t = 1`
reads `c (t₀₀ + t₁₁) = 0`, and `c ≠ 0`. -/
lemma t_mat_11_eq_00 {t : SL2 F} (ht : orderOf t = 2) (htB : t ∉ B (F := F)) :
    (t : Matrix (Fin 2) (Fin 2) F) 1 1 = (t : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  have h : (t : Matrix (Fin 2) (Fin 2) F) 1 0 * (t : Matrix (Fin 2) (Fin 2) F) 0 0
      + (t : Matrix (Fin 2) (Fin 2) F) 1 1 * (t : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) (t_mul_self_coe ht)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at hh
    simpa using hh
  have h2 : (t : Matrix (Fin 2) (Fin 2) F) 1 0 *
      ((t : Matrix (Fin 2) (Fin 2) F) 0 0 + (t : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
    rw [mul_add,
      mul_comm ((t : Matrix (Fin 2) (Fin 2) F) 1 0) ((t : Matrix (Fin 2) (Fin 2) F) 1 1)]
    exact h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (t_mat_10_ne htB)
  · rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h3
    exact h3.symm

/-- **The defining relation of an involution of `SL(2,F)`**: the `(0,0)`-entry of `t * t = 1`. -/
lemma t_mat_key {t : SL2 F} (ht : orderOf t = 2) :
    (t : Matrix (Fin 2) (Fin 2) F) 0 0 * (t : Matrix (Fin 2) (Fin 2) F) 0 0
      + (t : Matrix (Fin 2) (Fin 2) F) 0 1 * (t : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) (t_mul_self_coe ht)
  simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh

/-- **The `(1,0)`-entry of `t x t` for `x ∈ B`.**  With `t = !![a,b;c,a]` (`a = t₀₀ = t₁₁`,
`c = t₁₀ ≠ 0`) and `x = !![p,q;0,r]` upper triangular, the `(1,0)`-entry of `t x t` is
`c (a (p + r) + c q)`. -/
lemma t_conj_entry {t x : SL2 F} (ht : orderOf t = 2) (htB : t ∉ B (F := F))
    (hx : x ∈ B (F := F)) :
    ((t * x * t : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0
      = (t : Matrix (Fin 2) (Fin 2) F) 1 0
        * ((t : Matrix (Fin 2) (Fin 2) F) 0 0
            * ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1)
          + (t : Matrix (Fin 2) (Fin 2) F) 1 0 * (x : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have h10 : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hx
  have hd : (t : Matrix (Fin 2) (Fin 2) F) 1 1 = (t : Matrix (Fin 2) (Fin 2) F) 0 0 :=
    t_mat_11_eq_00 ht htB
  have hcoe : ((t * x * t : SL2 F) : Matrix (Fin 2) (Fin 2) F)
      = (t : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F)
        * (t : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rw [hcoe]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  rw [h10, hd]
  ring

/-- An involution is its own inverse. -/
lemma inv_eq_self_of_orderOf_two {t : SL2 F} (ht : orderOf t = 2) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (mul_self_of_orderOf_two ht)

/-- Conjugating twice by an involution is the identity. -/
lemma conj_conj_eq {t y : SL2 F} (ht : orderOf t = 2) : t * (t * y * t⁻¹) * t⁻¹ = y := by
  have h1 : t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t⁻¹ * t⁻¹) := by group
  rw [h1, mul_self_of_orderOf_two ht, one_mul, inv_eq_self_of_orderOf_two ht,
    mul_self_of_orderOf_two ht, mul_one]

/-- Membership in `B^t = t B t⁻¹` for `t` an involution. -/
lemma mem_conj_B_iff {t : SL2 F} (ht : orderOf t = 2) (y : SL2 F) :
    y ∈ Submission.Blueprint.conj t (B (F := F)) ↔ t * y * t⁻¹ ∈ B (F := F) := by
  rw [Submission.Blueprint.conj, Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, hby⟩
    have hby' : t * b * t⁻¹ = y := by simpa [MulAut.conj_apply] using hby
    rw [← hby', conj_conj_eq ht]
    exact hb
  · intro hy
    exact ⟨t * y * t⁻¹, hy, by
      change t * (t * y * t⁻¹) * t⁻¹ = y
      exact conj_conj_eq ht⟩

/-- **The two-point stabiliser `B ⊓ B^t` in coordinates.**  For `t` an involution outside `B`
and an arbitrary `x : SL(2,F)`,

`x ∈ B ⊓ B^t  ↔  x₁₀ = 0  and  a (x₀₀ + x₁₁) + c x₀₁ = 0`,

where `a = t₀₀ = t₁₁` and `c = t₁₀ ≠ 0`. -/
lemma mem_twoPoint_iff {t : SL2 F} (ht : orderOf t = 2) (htB : t ∉ B (F := F)) (x : SL2 F) :
    x ∈ Submission.Blueprint.twoPoint (B (F := F)) t ↔
      (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
        (t : Matrix (Fin 2) (Fin 2) F) 0 0
          * ((x : Matrix (Fin 2) (Fin 2) F) 0 0 + (x : Matrix (Fin 2) (Fin 2) F) 1 1)
        + (t : Matrix (Fin 2) (Fin 2) F) 1 0 * (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
  have hcne : (t : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := t_mat_10_ne htB
  have htinv : t⁻¹ = t := inv_eq_self_of_orderOf_two ht
  rw [Submission.Blueprint.twoPoint, Subgroup.mem_inf, mem_B_iff', mem_conj_B_iff ht, htinv]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : ((t * x * t : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := h2
    rw [t_conj_entry ht htB h1] at h3
    exact ⟨h1, (mul_eq_zero.mp h3).resolve_left hcne⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, mem_B_iff'.mpr ?_⟩
    rw [t_conj_entry ht htB h1, h2, mul_zero]

/-- **The inverse of a `2 × 2` special linear matrix** in characteristic `2`: it is obtained by
swapping the two diagonal entries (and keeping the off-diagonal ones, `-x = x`). -/
lemma inv_coe (y : SL2 F) : ((y⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F)
    = !![(y : Matrix (Fin 2) (Fin 2) F) 1 1, (y : Matrix (Fin 2) (Fin 2) F) 0 1;
        (y : Matrix (Fin 2) (Fin 2) F) 1 0, (y : Matrix (Fin 2) (Fin 2) F) 0 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]

/-- The matrices `!![u, s (u + u⁻¹); 0, u⁻¹]` (`u ∈ Fˣ`): a `B`-conjugate of the diagonal
torus, lying in the coset of the two-point stabiliser of any involution `t ∉ B` whose
`(0,0)`-entry is `a` and whose `(1,0)`-entry is `c`, for `s = a / c`. -/
def torusConj (s : F) (u : Fˣ) : SL2 F :=
  ⟨!![(u : F), s * ((u : F) + ((u⁻¹ : Fˣ) : F)); 0, ((u⁻¹ : Fˣ) : F)], by
    rw [Matrix.det_fin_two_of]
    simp⟩

/-- The matrix form of `torusConj`. -/
lemma torusConj_coe (s : F) (u : Fˣ) :
    (torusConj s u : Matrix (Fin 2) (Fin 2) F)
      = !![(u : F), s * ((u : F) + ((u⁻¹ : Fˣ) : F)); 0, ((u⁻¹ : Fˣ) : F)] := rfl

lemma torusConj_coe_00 (s : F) (u : Fˣ) :
    (torusConj s u : Matrix (Fin 2) (Fin 2) F) 0 0 = (u : F) := rfl

lemma torusConj_coe_01 (s : F) (u : Fˣ) :
    (torusConj s u : Matrix (Fin 2) (Fin 2) F) 0 1
      = s * ((u : F) + ((u⁻¹ : Fˣ) : F)) := rfl

lemma torusConj_coe_10 (s : F) (u : Fˣ) :
    (torusConj s u : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := rfl

lemma torusConj_coe_11 (s : F) (u : Fˣ) :
    (torusConj s u : Matrix (Fin 2) (Fin 2) F) 1 1 = ((u⁻¹ : Fˣ) : F) := rfl

/-- `torusConj s u` lies in the Borel (it is upper triangular). -/
lemma torusConj_mem_B (s : F) (u : Fˣ) : torusConj s u ∈ B (F := F) :=
  mem_B_iff'.mpr (torusConj_coe_10 s u)

/-- `torusConj s u` is a conjugate of a diagonal matrix: it follows from the matrix identity
`unip s * diag(u,u⁻¹) * unip s = !![u, s (u + u⁻¹); 0, u⁻¹]` in characteristic `2`. -/
lemma torusConj_eq_conj_unip (s : F) (u : Fˣ) :
    torusConj s u = unip s * diagUnit (F := F) u * (unip s)⁻¹ := by
  have hinv : (unip s)⁻¹ = unip s :=
    inv_eq_of_mul_eq_one_right (unip_mul_self s)
  have hcoe : ((unip s * diagUnit (F := F) u * (unip s)⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F)
      = (unip s : Matrix (Fin 2) (Fin 2) F) * (diagUnit (F := F) u : Matrix (Fin 2) (Fin 2) F)
        * (unip s : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv]
  refine Subtype.ext ?_
  rw [hcoe, torusConj_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, unip_coe, diagUnit, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Fin.isValue, Fin.reduceFinMk, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
      Units.val_inv_eq_inv_val]
  · ring

/-- **The membership of the conjugated torus in the two-point stabiliser.**  With
`s = a / c` (`a = t₀₀`, `c = t₁₀ ≠ 0`), every `torusConj s u` (`u ∈ Fˣ`) lies in `B ⊓ B^t`. -/
lemma torusConj_mem_twoPoint {t : SL2 F} (ht : orderOf t = 2) (htB : t ∉ B (F := F))
    (u : Fˣ) :
    torusConj ((t : Matrix (Fin 2) (Fin 2) F) 0 0 * ((t : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹) u
      ∈ Submission.Blueprint.twoPoint (B (F := F)) t := by
  have hcne : (t : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := t_mat_10_ne htB
  rw [mem_twoPoint_iff ht htB]
  constructor
  · rfl
  · have hmul : (t : Matrix (Fin 2) (Fin 2) F) 1 0
        * ((t : Matrix (Fin 2) (Fin 2) F) 0 0 * ((t : Matrix (Fin 2) (Fin 2) F) 1 0)⁻¹)
        = (t : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      rw [← mul_assoc, mul_comm ((t : Matrix (Fin 2) (Fin 2) F) 1 0)
        ((t : Matrix (Fin 2) (Fin 2) F) 0 0), mul_assoc, mul_inv_cancel₀ hcne, mul_one]
    simp only [torusConj_coe_00, torusConj_coe_01, torusConj_coe_11]
    rw [← mul_assoc, hmul, CharTwo.add_self_eq_zero]

/-- **A conjugate of a cyclic subgroup is cyclic** (the image of a cyclic group under a suitable
injective homomorphism is cyclic). -/
lemma isCyclic_map_conj {G : Type*} [Group G] (b : G) (H : Subgroup G) [IsCyclic ↥H] :
    IsCyclic ↥(H.map (MulAut.conj b).toMonoidHom) := by
  let φ : ↥H →* ↥(H.map (MulAut.conj b).toMonoidHom) :=
    { toFun := fun x => ⟨MulAut.conj b x, Subgroup.mem_map.mpr ⟨(x : G), x.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp only [MulAut.conj_apply, Subgroup.coe_mul]; group }
  refine isCyclic_of_surjective φ ?_
  rintro ⟨y, hy⟩
  obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨w, hw⟩, Subtype.ext hwy⟩

end Work.Models.PSL2
