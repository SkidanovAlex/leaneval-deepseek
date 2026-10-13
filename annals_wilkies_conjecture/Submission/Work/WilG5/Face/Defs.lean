/-
  WilG5 / Face — the boundary (face) part of the algebraic lemma.

  For `n ≥ 1` and `i : Fin n` we build the *coordinate-deleting* injection
  `delSplit i : Fin (n-1) → Fin n` (the increasing injection skipping `i`) together with the
  *coordinate-inserting* map `insCoord i c : (Fin (n-1) → ℝ) → (Fin n → ℝ)`, which takes the
  value `c` at `i` and reads the other coordinates off `v`.  Both are written directly on
  `Fin n` / `Fin (n-1)`; this is deliberate, since `Fin.succAbove`/`Fin.insertNth` live on
  `Fin ((n-1)+1)` and would force a transport along `(n-1)+1 = n` through the whole development.

  The face of `X ⊆ ℝⁿ` at coordinate `i` with value `c` is
  `faceProj i c X = coordImage (delSplit i) (X ∩ {x | x i = c})`, and `insCoord_mem_faceProj`
  states the expected round trip `insCoord i c y ∈ X ↔ y ∈ faceProj i c X`.

  `projCoord h` (keep the first `μ'` coordinates of `ℝ^μ`) and `extHalf` (fill the remaining
  coordinates with `1/2`) move a chart of `ℝ^{μ'}` to one of `ℝ^μ` (`μ' ≤ μ`), which is what
  lets the face recursion run with source dimension `min μ (n-1)` and still produce charts of
  the required shape `(Fin μ → ℝ) → ℝⁿ`.

  `dfs n` / `ffs F n` are the degree and format shifts incurred by cutting out one face
  (hyperplane + `coordImage`, see `Work.WilG5.Reindex3.coordImage_mem`); they are *constants*
  in `D` — `D' = D + dfs n` — which is what makes the counting addition uniform over the faces.
-/
import Mathlib
import Submission.Work.WilG5.Defs
import Submission.Work.WilG5.Reindex3

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG5.Face

open WilkiesDesign WilkiesConjecture
open Work.WilG5

variable {n : ℕ}

/-! ## 1. Splitting off one coordinate -/

/-- The index of `j ≠ i` in the enumeration of the complement of `i`, realised on `Fin (n-1)`.
It is the inverse of `delSplit i` at points `j ≠ i`. -/
def splitIdx {n : ℕ} (i j : Fin n) (h : j ≠ i) : Fin (n - 1) :=
  ⟨if j.val < i.val then j.val else j.val - 1, by
    have hne : j.val ≠ i.val := fun hv => h (Fin.ext hv)
    split_ifs with hlt
    · have h1 := i.isLt; omega
    · have h1 := j.isLt; omega⟩

/-- The increasing injection `Fin (n-1) → Fin n` skipping `i`. -/
def delSplit {n : ℕ} (i : Fin n) : Fin (n - 1) → Fin n :=
  fun j => ⟨if j.val < i.val then j.val else j.val + 1, by
    split_ifs with h
    · have h1 := j.isLt; have h2 := i.isLt; omega
    · have h1 := j.isLt; omega⟩

theorem delSplit_ne {n : ℕ} (i : Fin n) (j : Fin (n - 1)) : delSplit i j ≠ i := by
  intro h
  have h' : (delSplit i j).val = i.val := congrArg Fin.val h
  simp only [delSplit, Fin.val_mk] at h'
  split_ifs at h' <;> omega

theorem delSplit_injective {n : ℕ} (i : Fin n) : Function.Injective (delSplit i) := by
  intro j k h
  apply Fin.ext
  have h' : (delSplit i j).val = (delSplit i k).val := congrArg Fin.val h
  simp only [delSplit, Fin.val_mk] at h'
  split_ifs at h' <;> omega

theorem splitIdx_delSplit {n : ℕ} (i : Fin n) (j : Fin (n - 1)) :
    splitIdx i (delSplit i j) (delSplit_ne i j) = j := by
  apply Fin.ext
  simp only [splitIdx, delSplit, Fin.val_mk]
  split_ifs <;> omega

theorem delSplit_splitIdx {n : ℕ} (i j : Fin n) (hj : j ≠ i) :
    delSplit i (splitIdx i j hj) = j := by
  apply Fin.ext
  have hne : j.val ≠ i.val := fun h => hj (Fin.ext h)
  simp only [splitIdx, delSplit, Fin.val_mk]
  split_ifs <;> omega

theorem exists_delSplit_eq {n : ℕ} (i j : Fin n) (hj : j ≠ i) :
    ∃ k : Fin (n - 1), delSplit i k = j :=
  ⟨splitIdx i j hj, delSplit_splitIdx i j hj⟩

/-! ## 2. Inserting a coordinate -/

/-- `v` with the value `c` inserted at position `i`. -/
def insCoord {n : ℕ} (i : Fin n) (c : ℝ) (v : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  fun j => if h : j = i then c else v (splitIdx i j h)

@[simp] theorem insCoord_self {n : ℕ} (i : Fin n) (c : ℝ) (v : Fin (n - 1) → ℝ) :
    insCoord i c v i = c := by
  simp [insCoord]

theorem insCoord_of_ne {n : ℕ} (i j : Fin n) (c : ℝ) (v : Fin (n - 1) → ℝ) (hj : j ≠ i) :
    insCoord i c v j = v (splitIdx i j hj) := by
  simp only [insCoord]
  rw [dite_eq_right hj]

theorem insCoord_delSplit {n : ℕ} (i : Fin n) (c : ℝ) (v : Fin (n - 1) → ℝ)
    (j : Fin (n - 1)) : insCoord i c v (delSplit i j) = v j := by
  rw [insCoord_of_ne i _ c v (delSplit_ne i j), splitIdx_delSplit]

/-- `insCoord i c` is the inverse of "restrict to the complement of `i`" on the points `x`
with `x i = c`. -/
theorem eq_insCoord_of {n : ℕ} (i : Fin n) (c : ℝ) (x : Fin n → ℝ) (hx : x i = c) :
    x = insCoord i c (fun j => x (delSplit i j)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [insCoord_self, hx]
  · rw [insCoord_of_ne i j c _ hj, delSplit_splitIdx i j hj]

/-! ## 3. The linear part of `insCoord` -/

/-- The linear part of `insCoord`: insert `0` at coordinate `i`. -/
def insLM {n : ℕ} (i : Fin n) : (Fin (n - 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := insCoord i 0
  map_add' := by
    intro v w
    funext j
    by_cases hj : j = i
    · subst hj; simp [insCoord]
    · rw [insCoord_of_ne i j 0 (v + w) hj]
      simp only [Pi.add_apply]
      rw [insCoord_of_ne i j 0 v hj, insCoord_of_ne i j 0 w hj]
  map_smul' := by
    intro a v
    funext j
    by_cases hj : j = i
    · subst hj; simp [insCoord]
    · rw [insCoord_of_ne i j 0 (a • v) hj]
      simp only [Pi.smul_apply, RingHom.id_apply]
      rw [insCoord_of_ne i j 0 v hj]

/-- `insLM i` as a continuous linear map (continuity is automatic in finite dimension). -/
noncomputable def insCLM {n : ℕ} (i : Fin n) : (Fin (n - 1) → ℝ) →L[ℝ] (Fin n → ℝ) where
  toLinearMap := insLM i
  cont := LinearMap.continuous_of_finiteDimensional _

@[simp] theorem insCLM_apply {n : ℕ} (i : Fin n) (v : Fin (n - 1) → ℝ) :
    insCLM i v = insCoord i 0 v := rfl

/-- `insCoord i c` is the linear map `insCLM i` shifted by the constant `Pi.single i c`. -/
theorem insCoord_eq_insCLM_add {n : ℕ} (i : Fin n) (c : ℝ) (v : Fin (n - 1) → ℝ) :
    insCoord i c v = insCLM i v + Pi.single i c := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [insCoord_self]
    simp [insCLM, insLM, Pi.single_eq_same]
  · rw [insCoord_of_ne i j c v hj]
    simp only [Pi.add_apply]
    rw [insCLM_apply, insCoord_of_ne i j 0 v hj, Pi.single_eq_of_ne hj]
    simp

/-- `insCLM i` is norm non-increasing for the sup norms. -/
theorem norm_insCLM_le_one {n : ℕ} (i : Fin n) : ‖insCLM i‖ ≤ 1 := by
  rcases n with _ | m
  · exact Fin.elim0 i
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul, insCLM_apply]
    rw [pi_norm_le_iff_of_nonempty]
    intro j
    by_cases hj : j = i
    · subst hj
      rw [insCoord_self]
      simp
    · rw [insCoord_of_ne i j 0 v hj]
      exact norm_le_pi_norm v (splitIdx i j hj)

/-! ## 4. The face of a set -/

/-- The face of `X` at coordinate `i` and value `c`, read on the remaining coordinates. -/
def faceProj {n : ℕ} (i : Fin n) (c : ℝ) (X : Set (Fin n → ℝ)) : Set (Fin (n - 1) → ℝ) :=
  coordImage (delSplit i) (X ∩ {x | x i = c})

theorem insCoord_mem_faceProj {n : ℕ} (i : Fin n) (c : ℝ) (X : Set (Fin n → ℝ))
    (y : Fin (n - 1) → ℝ) : insCoord i c y ∈ X ↔ y ∈ faceProj i c X := by
  constructor
  · intro h
    exact ⟨insCoord i c y, ⟨h, insCoord_self i c y⟩,
      funext fun j => insCoord_delSplit i c y j⟩
  · rintro ⟨x, ⟨hx, hxi⟩, hxy⟩
    have key : insCoord i c (x ∘ delSplit i) = x := (eq_insCoord_of i c x hxi).symm
    rw [← hxy, key]
    exact hx

theorem faceProj_subset_cube01 {n : ℕ} {X : Set (Fin n → ℝ)} (hX : X ⊆ cube01 n)
    (i : Fin n) (c : ℝ) : faceProj i c X ⊆ cube01 (n - 1) := by
  rintro y ⟨x, ⟨hx, -⟩, hxy⟩ j
  have : y j = x (delSplit i j) := by rw [← hxy]; rfl
  rw [this]
  exact hX hx (delSplit i j)

/-! ## 5. Changing the source dimension of a chart -/

/-- The first `μ'` coordinates of `t : ℝ^μ`. -/
def projCoord {μ μ' : ℕ} (h : μ' ≤ μ) (t : Fin μ → ℝ) : Fin μ' → ℝ :=
  fun j => t (Fin.castLE h j)

/-- `s : ℝ^{μ'}` extended to `ℝ^μ` by filling the remaining coordinates with `1/2`. -/
def extHalf {μ μ' : ℕ} (s : Fin μ' → ℝ) : Fin μ → ℝ :=
  fun j => if h : j.val < μ' then s ⟨j.val, h⟩ else 1 / 2

theorem projCoord_extHalf {μ μ' : ℕ} (h : μ' ≤ μ) (s : Fin μ' → ℝ) :
    projCoord h (extHalf (μ := μ) s) = s := by
  funext j
  show extHalf (μ := μ) s (Fin.castLE h j) = s j
  unfold extHalf
  rw [dite_eq_left (show (Fin.castLE h j).val < μ' by rw [Fin.val_castLE]; exact j.isLt)]
  exact congrArg s (Fin.ext (by rw [Fin.val_castLE]))

theorem projCoord_mem_openCube {μ μ' : ℕ} (h : μ' ≤ μ) {t : Fin μ → ℝ}
    (ht : t ∈ openCube μ) : projCoord h t ∈ openCube μ' := fun j => ht (Fin.castLE h j)

theorem extHalf_mem_openCube {μ μ' : ℕ} {s : Fin μ' → ℝ} (hs : s ∈ openCube μ') :
    extHalf (μ := μ) s ∈ openCube μ := by
  intro j
  by_cases hj : j.val < μ'
  · rw [extHalf, dite_eq_left hj]
    exact hs ⟨j.val, hj⟩
  · rw [extHalf, dite_eq_right hj]
    norm_num

/-! ## 6. The shifts of format and degree caused by one face -/

/-- Degree shift: hyperplane (1) + `coordImage` (`32 * (n + (n-1)) + 32`). -/
def dfs (n : ℕ) : ℕ := 1 + 32 * (n + (n - 1)) + 32

/-- Format shift: hyperplane (1) + `coordImage` (`64 * (n + (n-1)) + 64`). -/
def ffs (F n : ℕ) : ℕ := max F n + 1 + 64 * (n + (n - 1)) + 64

/-- The coordinate hyperplane `{x | x i = c}` is an `Ω`-set of format `n` and degree `1`. -/
theorem coordEq_mem {S : SOMin} {n : ℕ} (i : Fin n) (c : ℝ) :
    {x : Fin n → ℝ | x i = c} ∈ S.Ω n 1 n := by
  have hdeg : ((MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin n) ℝ)).totalDegree ≤ 1 :=
    le_trans (td_sub_le _ _) (max_le (td_X_le i) (le_trans (td_C_le c) (Nat.zero_le 1)))
  have heq : {x : Fin n → ℝ | x i = c} = {x : Fin n → ℝ |
      MvPolynomial.eval x (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin n) ℝ) = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact mem_mono (S.hyp n (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin n) ℝ)) n 1
    (le_refl _) hdeg

end Work.WilG5.Face
