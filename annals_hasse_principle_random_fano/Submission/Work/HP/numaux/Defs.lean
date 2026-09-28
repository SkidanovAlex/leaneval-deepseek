import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux

/-!
# Auxiliary lattice notions for `Work.HP.num_lattices`

This file collects the notions (and the cheap lemmas) that the counting argument for
`Work.HP.num_lattices` needs:

* `dotI a x = ∑ i, a i * x i` — the standard bilinear pairing on `ℤ^ι`;
* `orthLat Λ` — the primitive lattice of integer vectors orthogonal to `Λ`;
* `satLat Λ` — the saturation (pure hull) of `Λ`, i.e. the set of `x` with `m • x ∈ Λ`
  for some `m ≠ 0`.

Only elementary facts are proved here; the substantial inputs (Minkowski's second theorem,
the determinant of the orthogonal lattice, the rank formula, the realisers of the successive
minima, the double orthogonal complement, the rank of the saturation) are delegated and live
in sibling files in this directory.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard bilinear pairing `⟨a,x⟩ = ∑ᵢ aᵢ xᵢ` on `ℤ^ι`. -/
def dotI (a x : ι → ℤ) : ℤ := ∑ i, a i * x i

lemma dotI_comm (a x : ι → ℤ) : dotI a x = dotI x a := by
  simp only [dotI]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma dotI_add_left (a b x : ι → ℤ) : dotI (a + b) x = dotI a x + dotI b x := by
  simp only [dotI, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dotI_add_right (a x y : ι → ℤ) : dotI a (x + y) = dotI a x + dotI a y := by
  simp only [dotI, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dotI_smul_left (c : ℤ) (a x : ι → ℤ) : dotI (c • a) x = c * dotI a x := by
  simp only [dotI, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dotI_smul_right (c : ℤ) (a x : ι → ℤ) : dotI a (c • x) = c * dotI a x := by
  simp only [dotI, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `a` is orthogonal to the lattice `Λ` when `⟨a,x⟩ = 0` for all `x ∈ Λ`. -/
def orthLat (Λ : Submodule ℤ (ι → ℤ)) : Submodule ℤ (ι → ℤ) where
  carrier := {a | ∀ x ∈ Λ, dotI a x = 0}
  zero_mem' := by
    intro x _
    simp [dotI]
  add_mem' := by
    intro a b ha hb x hx
    show dotI (a + b) x = 0
    rw [dotI_add_left, ha x hx, hb x hx, add_zero]
  smul_mem' := by
    intro c a ha x hx
    show dotI (c • a) x = 0
    rw [dotI_smul_left, ha x hx, mul_zero]

@[simp] lemma mem_orthLat {Λ : Submodule ℤ (ι → ℤ)} {a : ι → ℤ} :
    a ∈ orthLat Λ ↔ ∀ x ∈ Λ, dotI a x = 0 := Iff.rfl

lemma orthLat_le_iff {Λ M : Submodule ℤ (ι → ℤ)} :
    orthLat Λ ≤ M ↔ ∀ a, (∀ x ∈ Λ, dotI a x = 0) → a ∈ M := Iff.rfl

lemma le_orthLat_iff {Λ M : Submodule ℤ (ι → ℤ)} :
    Λ ≤ orthLat M ↔ ∀ x ∈ Λ, ∀ a ∈ M, dotI x a = 0 := by
  constructor
  · intro h x hx a ha
    exact (mem_orthLat.mp (h hx)) a ha
  · intro h x hx
    rw [mem_orthLat]
    intro a ha
    exact h x hx a ha

lemma orthLat_antitone {Λ M : Submodule ℤ (ι → ℤ)} (h : Λ ≤ M) : orthLat M ≤ orthLat Λ := by
  intro a ha x hx
  exact ha x (h hx)

/-- The saturation (pure hull) of an integral lattice: the set of `x` with `m • x ∈ Λ`
for some non-zero `m`. -/
def satLat (Λ : Submodule ℤ (ι → ℤ)) : Submodule ℤ (ι → ℤ) where
  carrier := {x | ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ Λ}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    intro x y hx hy
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n, hn, hny⟩ := hy
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have h : (m * n) • (x + y) = n • (m • x) + m • (n • y) := by
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    rw [h]
    exact Submodule.add_mem _ (Submodule.smul_mem _ n hmx) (Submodule.smul_mem _ m hny)
  smul_mem' := by
    intro c x hx
    obtain ⟨m, hm, hmx⟩ := hx
    refine ⟨m, hm, ?_⟩
    have h : m • (c • x) = c • (m • x) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [h]
    exact Submodule.smul_mem _ c hmx

@[simp] lemma mem_satLat {Λ : Submodule ℤ (ι → ℤ)} {x : ι → ℤ} :
    x ∈ satLat Λ ↔ ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ Λ := Iff.rfl

lemma le_satLat (Λ : Submodule ℤ (ι → ℤ)) : Λ ≤ satLat Λ := by
  intro x hx
  exact ⟨1, one_ne_zero, by simpa using hx⟩

/-- The saturation of a primitive lattice is itself. -/
lemma satLat_eq_of_isPrimLat {Λ : Submodule ℤ (ι → ℤ)} (h : IsPrimLat Λ) :
    satLat Λ = Λ := by
  refine le_antisymm ?_ (le_satLat Λ)
  intro x hx
  obtain ⟨m, hm, hmx⟩ := hx
  exact h x m hm hmx

lemma satLat_mono {Λ M : Submodule ℤ (ι → ℤ)} (h : Λ ≤ M) : satLat Λ ≤ satLat M := by
  intro x hx
  obtain ⟨m, hm, hmx⟩ := hx
  exact ⟨m, hm, h hmx⟩

/-- The saturation is primitive (pure). -/
lemma isPrimLat_satLat (Λ : Submodule ℤ (ι → ℤ)) : IsPrimLat (satLat Λ) := by
  intro x m hm hmx
  obtain ⟨k, hk, hkx⟩ := hmx
  refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
  have h : (k * m) • x = k • (m • x) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  exact hkx

/-- Cauchy–Schwarz for the explicit Euclidean norm and the standard pairing. -/
lemma abs_dotI_le (a x : ι → ℤ) :
    |((dotI a x : ℤ) : ℝ)| ≤ eNorm a * eNorm x := by
  have h : ((dotI a x : ℤ) : ℝ) = ∑ i, ((a i : ℝ) * (x i : ℝ)) := by
    simp only [dotI, Int.cast_sum, Int.cast_mul]
  rw [h, eNorm, eNorm]
  have hs : (∑ i, |(a i : ℝ)| * |(x i : ℝ)|) ≤
      Real.sqrt (∑ i, ((a i : ℝ)) ^ 2) * Real.sqrt (∑ i, ((x i : ℝ)) ^ 2) := by
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun i => |(a i : ℝ)|) (fun i => |(x i : ℝ)|)
    rw [Finset.sum_congr rfl (fun i _ => sq_abs ((a i : ℝ))),
      Finset.sum_congr rfl (fun i _ => sq_abs ((x i : ℝ)))] at hsq
    have h' : Real.sqrt ((∑ i, |(a i : ℝ)| * |(x i : ℝ)|) ^ 2) ≤
        Real.sqrt ((∑ i, ((a i : ℝ)) ^ 2) * (∑ i, ((x i : ℝ)) ^ 2)) :=
      Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)),
      Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h'
    exact h'
  calc |∑ i, ((a i : ℝ) * (x i : ℝ))| ≤ ∑ i, |(a i : ℝ) * (x i : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |(a i : ℝ)| * |(x i : ℝ)| := Finset.sum_congr rfl fun i _ => abs_mul _ _
    _ ≤ _ := hs


lemma dotI_sub_left (a b x : ι → ℤ) : dotI (a - b) x = dotI a x - dotI b x := by
  rw [sub_eq_add_neg, dotI_add_left]
  have h : -b = (-1 : ℤ) • b := by simp
  rw [h, dotI_smul_left]
  ring

lemma dotI_sub_right (a x y : ι → ℤ) : dotI a (x - y) = dotI a x - dotI a y := by
  rw [sub_eq_add_neg, dotI_add_right]
  have h : -y = (-1 : ℤ) • y := by simp
  rw [h, dotI_smul_right]
  ring

end Work.HP
