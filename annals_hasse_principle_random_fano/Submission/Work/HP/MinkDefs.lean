import Mathlib
import Submission.Work.HP.Defs

set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators

namespace Work.HP

variable {ι : Type*} [Fintype ι]

/-- Integer dot product of two integer vectors. -/
def dotZ (x b : ι → ℤ) : ℤ := ∑ i, x i * b i

lemma dotZ_apply (x b : ι → ℤ) : dotZ x b = ∑ i, x i * b i := rfl

lemma dotZ_comm (x b : ι → ℤ) : dotZ x b = dotZ b x := by
  simp only [dotZ_apply]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma dotZ_add (x y b : ι → ℤ) : dotZ (x + y) b = dotZ x b + dotZ y b := by
  simp only [dotZ_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dotZ_smul (m : ℤ) (x b : ι → ℤ) : dotZ (m • x) b = m * dotZ x b := by
  simp only [dotZ_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `projScale b` is `‖b‖²` times the orthogonal projection onto `b^⊥`; it is `ℤ`-linear and is
the "scaled projection" used in the inductive proof of Minkowski's second theorem. -/
def projScale (b : ι → ℤ) : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) where
  toFun x := (dotZ b b) • x - (dotZ x b) • b
  map_add' x y := by
    simp only [dotZ_add]
    module
  map_smul' m x := by
    simp only [dotZ_smul]
    module

@[simp] lemma projScale_apply (b x : ι → ℤ) :
    projScale b x = (dotZ b b) • x - (dotZ x b) • b := rfl

/-- The Gram matrix of a finite family of integer vectors (for the standard Euclidean structure). -/
def gramM {κ : Type*} (c : κ → ι → ℤ) : Matrix κ κ ℝ :=
  Matrix.of fun i j => ∑ k, ((c i k : ℝ)) * ((c j k : ℝ))

lemma gramM_apply {κ : Type*} (c : κ → ι → ℤ) (i j : κ) :
    gramM c i j = ∑ k, ((c i k : ℝ)) * ((c j k : ℝ)) := rfl

/-- The Gram determinant of a finite family of integer vectors. -/
def gramDet {κ : Type*} [Fintype κ] [DecidableEq κ] (c : κ → ι → ℤ) : ℝ := (gramM c).det

/-- Squared Euclidean norm as an integer dot product. -/
lemma eNorm_sq_eq (v : ι → ℤ) : eNorm v ^ 2 = ((dotZ v v : ℤ) : ℝ) := by
  rw [eNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  push_cast [dotZ_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma dotZ_self_nonneg (v : ι → ℤ) : 0 ≤ dotZ v v := by
  rw [dotZ_apply]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

lemma eNorm_nonneg (v : ι → ℤ) : 0 ≤ eNorm v := Real.sqrt_nonneg _

lemma eNorm_pos_iff {v : ι → ℤ} : 0 < eNorm v ↔ v ≠ 0 := by
  rw [eNorm, Real.sqrt_pos]
  have hnr : (0:ℝ) ≤ ∑ i, ((v i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hiff : (∑ i, ((v i : ℤ) : ℝ) ^ 2) = 0 ↔ v = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ((v i : ℤ) : ℝ))]
    constructor
    · intro h
      funext i
      have h2 : ((v i : ℤ) : ℝ) ^ 2 = 0 := h i (Finset.mem_univ i)
      have h3 : ((v i : ℤ) : ℝ) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      exact_mod_cast h3
    · rintro rfl i _
      simp
  constructor
  · intro h hv; rw [hv] at h; simp at h
  · intro hv
    rcases lt_trichotomy (∑ i, ((v i : ℤ) : ℝ) ^ 2) 0 with h | h | h
    · exact absurd h (not_lt.mpr hnr)
    · exact absurd (hiff.mp h) hv
    · exact h

lemma eNorm_pos_of_ne_zero {v : ι → ℤ} (hv : v ≠ 0) : 0 < eNorm v := eNorm_pos_iff.mpr hv

section LamAux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- There are `i` linearly independent vectors in `L` when `i ≤ rk L`. -/
lemma exists_linIndep_card (L : Submodule ℤ (ι → ℤ)) {i : ℕ} (hi : i ≤ rk L) :
    ∃ f : Fin i → (ι → ℤ), (∀ j, f j ∈ L) ∧ LinearIndependent ℤ f := by
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L
  have hn : n = rk L := by
    show n = Module.finrank ℤ ↥L
    rw [Module.finrank_eq_card_basis b]
    simp
  subst hn
  refine ⟨fun j => (b (Fin.castLE hi j) : ι → ℤ), fun j => (b _).2, ?_⟩
  exact (b.linearIndependent.comp (Fin.castLE hi) (Fin.castLE_injective hi)).map' L.subtype
    (Submodule.ker_subtype L)

/-- `lam` is a lower bound of its defining set, hence nonnegative. -/
lemma lam_nonneg (L : Submodule ℤ (ι → ℤ)) (i : ℕ) : 0 ≤ lam L i := by
  have hdef : lam L i = sInf (setOf fun r : ℝ => 0 ≤ r ∧ ∃ f : Fin i → (ι → ℤ),
      (∀ j, f j ∈ L) ∧ LinearIndependent ℤ f ∧ ∀ j, eNorm (f j) ≤ r) := rfl
  rw [hdef]
  by_cases h : (setOf fun r : ℝ => 0 ≤ r ∧ ∃ f : Fin i → (ι → ℤ),
      (∀ j, f j ∈ L) ∧ LinearIndependent ℤ f ∧ ∀ j, eNorm (f j) ≤ r).Nonempty
  · exact le_csInf h fun x hx => hx.1
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

/-- Any `ρ > lam L i` admits `i` linearly independent vectors of `L` of norm at most `ρ`. -/
lemma lam_witness (L : Submodule ℤ (ι → ℤ)) {i : ℕ} (hi : i ≤ rk L) {ρ : ℝ}
    (hρ : lam L i < ρ) :
    ∃ f : Fin i → (ι → ℤ), (∀ j, f j ∈ L) ∧ LinearIndependent ℤ f ∧ ∀ j, eNorm (f j) ≤ ρ := by
  obtain ⟨g, hgL, hli⟩ := exists_linIndep_card L hi
  have hdef : lam L i = sInf (setOf fun r : ℝ => 0 ≤ r ∧ ∃ f : Fin i → (ι → ℤ),
      (∀ j, f j ∈ L) ∧ LinearIndependent ℤ f ∧ ∀ j, eNorm (f j) ≤ r) := rfl
  have hne : (setOf fun r : ℝ => 0 ≤ r ∧ ∃ f : Fin i → (ι → ℤ), (∀ j, f j ∈ L) ∧
      LinearIndependent ℤ f ∧ ∀ j, eNorm (f j) ≤ r).Nonempty := by
    refine ⟨∑ j : Fin i, eNorm (g j), Finset.sum_nonneg fun j _ => eNorm_nonneg (g j), g, hgL, hli, ?_⟩
    intro j
    exact Finset.single_le_sum (fun j _ => eNorm_nonneg (g j)) (Finset.mem_univ j)
  obtain ⟨s, ⟨-, f, hfL, hli', hfs⟩, hsρ⟩ := exists_lt_of_csInf_lt hne (hdef ▸ hρ)
  exact ⟨f, hfL, hli', fun j => (hfs j).trans hsρ.le⟩

lemma detL_nonneg (L : Submodule ℤ (ι → ℤ)) : 0 ≤ detL L := Real.sqrt_nonneg _

end LamAux
