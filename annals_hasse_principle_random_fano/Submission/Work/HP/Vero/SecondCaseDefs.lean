import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero.SigmaDefs

/-!
# Definitions and glue for the second case of §3.3 (Browning–Le Boudec–Sawin)

The type `ι → ℝ` of real vectors carries the sup norm, so `Metric.infDist` is *not* the Euclidean
distance used by the paper.  We therefore define our own Euclidean distance `eucDist v S` to a set.

`rowVecR n i c` is the row map `rᵢ` of the paper acting on real coefficient vectors of quadratic
forms:  it is `rowVec n i` extended to real coefficients.  The main pairing identity is
`dot_sigma_rowVecR`:  `⟨c, σ(eᵢ,v)⟩ = ⟨rᵢ(c), v⟩`.
-/

/-!
## Route notes for `Work.HP.Vero.second_case_witness` (and the second case of §3.3)

Let `A` be the symmetric `(n+1) × (n+1)` matrix `A i j = a (pairMon n i j)`.  Two identities make the
witness lemma elementary (no dimension count needed):

* `∑ m, a m * σ(u,v) m = ∑ i, ∑ j, A i j * u i * v j`, i.e. `σ` is the polarisation of the quadratic
  form `f_a(z) = ∑ m, a m * ν₂(z)_m`:  indeed `σ(u,v)(pairMon i j) = u i * v j + u j * v i` for
  `i ≠ j` and `σ(u,u)(pairMon i i) = u i * u i`; equivalently `f_a(z+z') - f_a(z) - f_a(z') =
  2 * ∑ m, a m * σ(z,z')_m`, so `f_a(z) = ∑ i, ∑ j, A i j * z i * z j`.
* `∑ m, a m * σ(e_i, v)_m = ∑ j, A i j * v j` (this is `dot_sigma_rowVecR` in this file, combined
  with `σ(e_i,v)(pairMon i j) = v j` and `σ(e_i,v)(pairMon t j) = 0` for `t ≠ i`).

Consequently the hypothesis `∀ i v, v ⊥ x, v ⊥ y → ∑ m, a m * σ(e_i,v)_m = 0` says that each *row*
of `A` is orthogonal to every vector of `span_ℝ{x,y}^⊥`; since the integer vectors orthogonal to
`x` and `y` span `span_ℝ{x,y}^⊥` (`span_realify_latOrth_inf`), every row of `A` lies in
`span_ℝ{x,y}` — this is the `dual_orthogonal_span_pair` + `LinearMap.BilinForm.orthogonal_orthogonal`
step with `dualDotForm`.  So `A = C xᵀ + D yᵀ` for vectors `C, D` of `ℝ^{n+1}`.

Symmetry of `A` (`pairMon_comm`) then gives, for `v ⊥ x, v ⊥ y`,
`0 = vᵀ A u = ⟨v,C⟩⟨u,x⟩ + ⟨v,D⟩⟨u,y⟩` for all `u`; as `x, y` are linearly independent the pairs
`(⟨u,x⟩,⟨u,y⟩)` fill `ℝ²`, so `⟨v,C⟩ = ⟨v,D⟩ = 0`, whence `C, D ∈ span_ℝ{x,y}`.  Writing
`C = α x + β y`, `D = δ x + ε y` and using symmetry once more (`β = δ`) gives
`A i j = α xᵢxⱼ + β(xᵢyⱼ + xⱼyᵢ) + ε yᵢyⱼ`.

Finally, comparing values on `pairMon n i j`,
`a = (α - β) ν₂x + (ε - β) ν₂y + β ν₂(x+y)`  (note: **not** with `σ(x,y)`; the diagonal entries of
`σ(x,x)`/`σ(x,y)` are not the doubled ones, so `σ(x,y)` has to be replaced by
`ν₂(x+y) - ν₂x - ν₂y` and the coefficients adjusted).  Hence `a ∈ span_ℝ{ν₂x, ν₂y, ν₂(x+y)}`,
contradicting `ha`.  This proves the contrapositive of the witness lemma.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Vero

open Work.HP

/-! ## Euclidean distance -/

/-- The Euclidean distance from a real vector to a set of real vectors, with the Euclidean norm
`rNorm` (the function type `ι → ℝ` has no `InnerProductSpace` instance, so `Metric.infDist` would
use the sup norm). -/
def eucDist {ι : Type*} [Fintype ι] (v : ι → ℝ) (S : Set (ι → ℝ)) : ℝ :=
  sInf ((fun z => rNorm (v - z)) '' S)

variable {ι : Type*} [Fintype ι]

lemma eucDist_le (v : ι → ℝ) (S : Set (ι → ℝ)) {z : ι → ℝ} (hz : z ∈ S) :
    eucDist v S ≤ rNorm (v - z) :=
  csInf_le ⟨0, by rintro r ⟨y, -, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨z, hz, rfl⟩

lemma eucDist_nonneg (v : ι → ℝ) (S : Set (ι → ℝ)) : 0 ≤ eucDist v S := by
  rcases S.eq_empty_or_nonempty with h | h
  · rw [eucDist, h, Set.image_empty, Real.sInf_empty]
  · exact le_csInf (h.image _) (by rintro r ⟨y, -, rfl⟩; exact Real.sqrt_nonneg _)

variable {n : ℕ}

/-! ## The row map on real coefficient vectors -/

/-- The row map `rᵢ` of the paper on real coefficient vectors: `rowVecR n i c j = c (XᵢXⱼ)`. -/
def rowVecR (n : ℕ) (i : Fin (n + 1)) (c : Mon 2 n → ℝ) : Fin (n + 1) → ℝ :=
  fun j => c (pairMon n i j)

@[simp] lemma rowVecR_apply (n : ℕ) (i : Fin (n + 1)) (c : Mon 2 n → ℝ) (j : Fin (n + 1)) :
    rowVecR n i c j = c (pairMon n i j) := rfl

lemma rowVecR_add (n : ℕ) (i : Fin (n + 1)) (c d : Mon 2 n → ℝ) :
    rowVecR n i (c + d) = rowVecR n i c + rowVecR n i d := by
  ext j; simp [rowVecR]

lemma rowVecR_sub (n : ℕ) (i : Fin (n + 1)) (c d : Mon 2 n → ℝ) :
    rowVecR n i (c - d) = rowVecR n i c - rowVecR n i d := by
  ext j; simp [rowVecR]

lemma rowVecR_smul (n : ℕ) (i : Fin (n + 1)) (a : ℝ) (c : Mon 2 n → ℝ) :
    rowVecR n i (a • c) = a • rowVecR n i c := by
  ext j; simp [rowVecR]

/-- `rᵢ` of an integer coefficient vector is the cast of `rowVec n i`. -/
lemma rowVecR_toR (n : ℕ) (i : Fin (n + 1)) (c : Mon 2 n → ℤ) :
    rowVecR n i (toR c) = toR (rowVec n i c) := rfl

/-- `rᵢ` of the Veronese vector `ν₂(x)` is `xᵢ • x`. -/
lemma rowVecR_veronese (n : ℕ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℤ) :
    rowVecR n i (toR (veronese 2 n x)) = (x i : ℝ) • toR x := by
  ext j
  rw [rowVecR_apply, Pi.smul_apply, smul_eq_mul]
  show ((veronese 2 n x) (pairMon n i j) : ℝ) = (x i : ℝ) * (x j : ℝ)
  rw [veronese_pairMon]
  push_cast
  ring

/-! ## The pairing identity `⟨c, σ(eᵢ,v)⟩ = ⟨rᵢ(c), v⟩` -/

/-- The pairing of `σ(eᵢ,v)` against a real coefficient vector `c` is the pairing of the row
vector `rᵢ(c)` with `v`. -/
theorem dot_sigma_rowVecR (n : ℕ) (i : Fin (n + 1)) (v : Fin (n + 1) → ℤ) (c : Mon 2 n → ℝ) :
    (∑ m : Mon 2 n, c m * (sigma n (Pi.single i 1) v m : ℝ))
      = ∑ j, rowVecR n i c j * (v j : ℝ) := by
  classical
  have hsig : ∀ m : Mon 2 n, ((sigma n (Pi.single i 1) v m : ℤ) : ℝ)
      = ∑ q, (if m = pairMon n i q then (v q : ℝ) else 0) := by
    intro m
    have h1 : sigma n (Pi.single i 1) v m = ∑ q, (if m = pairMon n i q then v q else 0) := by
      rw [sigma]
      rw [Finset.sum_eq_single i]
      · refine Finset.sum_congr rfl fun q _ => ?_
        by_cases h : m = pairMon n i q
        · rw [if_pos h, if_pos h, Pi.single_eq_same, one_mul]
        · rw [if_neg h, if_neg h]
      · intro b _ hb
        refine Finset.sum_eq_zero fun q _ => ?_
        rw [Pi.single_eq_of_ne hb]; simp
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [h1, Int.cast_sum]
    exact Finset.sum_congr rfl (fun q _ => by by_cases h : m = pairMon n i q <;> simp [h])
  have h : ∀ m : Mon 2 n, c m * (sigma n (Pi.single i 1) v m : ℝ)
      = ∑ q, (if m = pairMon n i q then c m * (v q : ℝ) else 0) := by
    intro m
    rw [hsig m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : m = pairMon n i q <;> simp [h]
  rw [Finset.sum_congr rfl (fun m _ => h m), Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (pairMon n i q) (fun m => c m * (v q : ℝ))]
  simp [rowVecR]

/-! ## Norm bounds and injectivity of `j ↦ XᵢXⱼ` -/

/-- `XᵢXⱼ = XᵢXⱼ'` implies `j = j'`. -/
lemma pairMon_right_injective (n : ℕ) (i : Fin (n + 1)) :
    Function.Injective (fun j : Fin (n + 1) => pairMon n i j) := by
  intro j j' h
  have hh : (pairMon n i j : Fin (n + 1) → Fin 3) = (pairMon n i j') := congrArg Subtype.val h
  have h2 : ((pairMon n i j).1 j : ℕ) = ((pairMon n i j').1 j : ℕ) :=
    congrArg (fun m : Fin (n + 1) → Fin 3 => (m j : ℕ)) hh
  by_contra hne
  rw [show ((pairMon n i j).1 j : ℕ) = (if j = i then 1 else 0) + 1 from by
        simp [pairMon, Work.HP.NA.monDij],
      show ((pairMon n i j').1 j : ℕ) = (if j = i then 1 else 0) + 0 from by
        simp [pairMon, Work.HP.NA.monDij, hne]] at h2
  split_ifs at h2 <;> omega

/-- The Euclidean norm of a row vector is at most the Euclidean norm of the whole coefficient
vector (a row is a sub-collection of coordinates). -/
lemma rNorm_rowVecR_le (n : ℕ) (i : Fin (n + 1)) (c : Mon 2 n → ℝ) :
    rNorm (rowVecR n i c) ≤ rNorm c := by
  rw [rNorm, rNorm, Real.sqrt_le_sqrt_iff (Finset.sum_nonneg (fun m _ => sq_nonneg (c m)))]
  have hinj := pairMon_right_injective n i
  have h2 : (∑ j : Fin (n + 1), (c (pairMon n i j)) ^ 2) ≤ ∑ m : Mon 2 n, c m ^ 2 := by
    have h3 := Finset.sum_le_sum_of_subset_of_nonneg (s := Finset.univ.image (fun j : Fin (n+1) =>
        pairMon n i j)) (t := (Finset.univ : Finset (Mon 2 n))) (f := fun m => c m ^ 2)
      (Finset.subset_univ _) (fun m _ _ => sq_nonneg _)
    rwa [Finset.sum_image (fun a _ b _ hab => hinj hab)] at h3
  calc ∑ j : Fin (n + 1), (rowVecR n i c j) ^ 2
      = ∑ j : Fin (n + 1), (c (pairMon n i j)) ^ 2 := rfl
    _ ≤ ∑ m : Mon 2 n, c m ^ 2 := h2

/-! ## Integer vectors orthogonal to `x` and `y` -/

/-- A real vector in `span{x,y}` pairs to zero with every integer vector orthogonal to `x` and
`y`. -/
lemma sum_mul_eq_zero_of_mem_span {n : ℕ} {x y v : Fin (n + 1) → ℤ}
    (hvx : ∑ j, v j * x j = 0) (hvy : ∑ j, v j * y j = 0) {z : Fin (n + 1) → ℝ}
    (hz : z ∈ Submodule.span ℝ ({toR x, toR y} : Set (Fin (n + 1) → ℝ))) :
    ∑ j, z j * (v j : ℝ) = 0 := by
  refine Submodule.span_induction (p := fun z _ => ∑ j, z j * (v j : ℝ) = 0) ?_ ?_ ?_ ?_ hz
  · rintro z (rfl | rfl)
    · show ∑ j, ((x j : ℤ) : ℝ) * ((v j : ℤ) : ℝ) = 0
      rw [show (∑ j, ((x j : ℤ) : ℝ) * ((v j : ℤ) : ℝ)) = ((∑ j, v j * x j : ℤ) : ℝ) from by
        push_cast
        exact Finset.sum_congr rfl (fun j _ => by ring)]
      rw [hvx, Int.cast_zero]
    · show ∑ j, ((y j : ℤ) : ℝ) * ((v j : ℤ) : ℝ) = 0
      rw [show (∑ j, ((y j : ℤ) : ℝ) * ((v j : ℤ) : ℝ)) = ((∑ j, v j * y j : ℤ) : ℝ) from by
        push_cast
        exact Finset.sum_congr rfl (fun j _ => by ring)]
      rw [hvy, Int.cast_zero]
  · simp
  · intro a b _ _ ha hb
    rw [Finset.sum_congr rfl (fun j _ => by rw [Pi.add_apply, add_mul]), Finset.sum_add_distrib,
      ha, hb, add_zero]
  · intro c b _ hb
    have hterm : ∀ j, (c • b) j * (v j : ℝ) = c * (b j * (v j : ℝ)) := fun j => by
      rw [Pi.smul_apply, smul_eq_mul]; ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, hb, mul_zero]

end Work.HP.Vero
