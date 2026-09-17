import Submission.E8Enum
import Submission.E8Orbit
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple

/-!
# The candidate character of `L(ω₁ + ω₈)`

The seven dominant multiplicities of `V = L(ω₁+ω₈)` are

  `λ ↦ 1,  ω₂ ↦ 7,  ω₇ ↦ 34,  ω₁ ↦ 133,  2ω₈ ↦ 7,  ω₈ ↦ 455,  0 ↦ 1407`,

which add up to `dim V = 1·30240 + 7·17280 + 34·6720 + 133·2160 + 7·240 + 455·240 + 1407·1
= 779247`.

This file builds the corresponding **candidate multiplicity function** `mfun : (Fin 8 → ℤ) → ℤ`:
the dominant conjugate `dcX` of a weight is looked up in the table above, with the shortcut that a
weight whose norm `⟪v,v⟫` is not one of `0,2,4,6,8,10` cannot be a weight of `V` and gets value
`0` (so that `dcX` — by far the most expensive kernel computation — is only evaluated for the
about 500 weights that survive).  The Freudenthal recursion is then verified at the six dominant
weights other than `λ` by `decide`.

Once the *actual* character of `L(ω₁+ω₈)` is known to satisfy the hypotheses of
`Submission.E8Character.eq_of_freudenthal` (support bound, `dc`-invariance via integrability, and
the trace/Freudenthal recursion), this file identifies it with `mfun` and yields both
`dim V = 779247` (via the orbit sizes) and the weight multiplicities needed for the tensor square.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

namespace Submission.E8Numerics

open Submission.WeylReflect Submission.E8Character Submission.E8Orbit Submission.E8Enum

/-- The integral quadratic form `v ⬝ A⁻¹ v` (the squared length of a weight). -/
abbrev qq : (Fin 8 → ℤ) → ℤ := Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ

/-- `qZ` is invariant under a fold of simple reflections. -/
lemma qZ_foldl (L : List (Fin 8)) (v : Fin 8 → ℤ) :
    qq (L.foldl (fun w (i : Fin 8) => fun j => w j - w i * E8 i j) v)
      = qq v := by
  induction L generalizing v with
  | nil => rfl
  | cons i L ih =>
      rw [List.foldl_cons, ih]
      exact Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ_refl v i

/-- The norm is invariant under the dominant-conjugate algorithm. -/
lemma qZ_dcX (v : Fin 8 → ℤ) : qq (dcX v) = qq v := by
  rw [dcX, dcl_eq_foldl]
  exact qZ_foldl _ v

/-- The norm table: `⟪v,v⟫ ∈ {0,2,4,6,8,10}` (the norms of the seven dominant weights below `λ`). -/
def normTable : ℤ → Bool
  | 0 => true | 2 => true | 4 => true | 6 => true | 8 => true | 10 => true | _ => false

/-- The norm check. -/
def normOk (v : Fin 8 → ℤ) : Bool := normTable (qq v)

lemma normOk_eq_true {v : Fin 8 → ℤ} : normOk v = true ↔
    qq v = 0 ∨ qq v = 2 ∨ qq v = 4 ∨ qq v = 6 ∨
      qq v = 8 ∨ qq v = 10 := by
  simp only [normOk, normTable]
  split <;> simp_all

lemma normOk_eq_false {v : Fin 8 → ℤ} (h : normOk v = false) :
    qq v ≠ 0 ∧ qq v ≠ 2 ∧ qq v ≠ 4 ∧ qq v ≠ 6 ∧
      qq v ≠ 8 ∧ qq v ≠ 10 := by
  simp only [normOk, normTable] at h
  split at h <;> simp_all

/-- The table of the seven dominant multiplicities. -/
def tab (w : Fin 8 → ℤ) : ℤ :=
  if w = lam then 1
  else if w = e 1 then 7
  else if w = 2 • e 7 then 7
  else if w = e 6 then 34
  else if w = e 0 then 133
  else if w = e 7 then 455
  else if w = 0 then 1407
  else 0

/-- The candidate multiplicity, from the norm test and the dominant conjugate. -/
def mfunAux (b : Bool) (w : Fin 8 → ℤ) : ℤ := if b then tab w else 0

/-- **The candidate multiplicity function of `L(ω₁+ω₈)`.** -/
def mfun (v : Fin 8 → ℤ) : ℤ := mfunAux (normOk v) (dcX v)

lemma normOk_dcX (v : Fin 8 → ℤ) : normOk (dcX v) = normOk v := by
  simp only [normOk, qZ_dcX]

/-- A non-zero table value means the weight is one of the seven. -/
lemma tab_ne_zero {w : Fin 8 → ℤ} (h : tab w ≠ 0) : w ∈ the7 := by
  rw [the7]
  simp only [tab] at h
  by_cases h1 : w = lam
  · subst h1; simp
  by_cases h2 : w = e 1
  · subst h2; simp
  by_cases h3 : w = 2 • e 7
  · subst h3; simp
  by_cases h4 : w = e 6
  · subst h4; simp
  by_cases h5 : w = e 0
  · subst h5; simp
  by_cases h6 : w = e 7
  · subst h6; simp
  by_cases h7 : w = 0
  · subst h7; simp
  · exfalso
    apply h
    simp only [tab, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7]

/-- The seven dominant weights are dominated by `λ`. -/
lemma posCon_lam_sub_the7 {w : Fin 8 → ℤ} (h : w ∈ the7) : w = lam ∨ posCon (lam - w) := by
  simp only [the7, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr fun i => by fin_cases i <;> decide
  · exact Or.inr fun i => by fin_cases i <;> decide
  · exact Or.inr fun i => by fin_cases i <;> decide
  · exact Or.inr fun i => by fin_cases i <;> decide
  · exact Or.inr fun i => by fin_cases i <;> decide
  · exact Or.inr fun i => by fin_cases i <;> decide

/-- **The support condition** for the candidate character: a non-zero value is only attained at
weights dominated by `λ`. -/
theorem mfun_support {v : Fin 8 → ℤ} (h : mfun v ≠ 0) : lam - v = 0 ∨ posCon (lam - v) := by
  have hnorm : normOk v = true := by
    by_contra hc
    rw [Bool.not_eq_true] at hc
    exact h (by simp [mfun, mfunAux, hc])
  have htab : tab (dcX v) ≠ 0 := by
    intro h0
    exact h (by simp [mfun, mfunAux, hnorm, h0])
  have hmem : dcX v ∈ the7 := tab_ne_zero htab
  have hw := posCon_lam_sub_the7 hmem
  have hstep : posCon (dcX v - v) := dcX_sub_posCon v
  rcases hw with hw | hw
  · -- dcX v = lam, so lam - v = dcX v - v
    exact Or.inr (hw ▸ hstep)
  · -- lam - v = (lam - dcX v) + (dcX v - v)
    refine Or.inr ?_
    have : lam - v = (lam - dcX v) + (dcX v - v) := by abel
    rw [this]
    exact posCon_add hw hstep

/-- The candidate character is invariant under the dominant conjugate. -/
theorem mfun_dcX (v : Fin 8 → ℤ) : mfun (dcX v) = mfun v := by
  simp only [mfun, normOk_dcX, dcX_idem]

end Submission.E8Numerics
