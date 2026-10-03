/-
# Area A8 — the `V^r`-valued trilinear interpolation (algebraic part)

This module sets up the *linearisation* of the clamped variational norm as a trilinear pairing,
and proves the algebraic identities (bilinearity of the pairing, expansion of the bilinear
operator over the finite supports of its arguments) that the three-lines argument needs.

Vocabulary (from `Submission.Work.KMTAreas.A8Defs`): `pair a l = ∑ₙ aₙlₙ` for a finitely
supported `l`.
-/
import Mathlib
import Submission.Work.KMTAreas.A8Defs
import Submission.Work.Analysis.Interpolation.analyticFamily_boundary
import Submission.Work.Analysis.Interpolation.eLpNorm_eq_iSup_simpleFunc_integral
import Submission.Work.Analysis.Interpolation.riesz_thorin_linear
import Submission.Work.Analysis.Interpolation.stein_trilinear

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.InverseTheory (FinSupp)

/-- The delta mass at `x : ℤ`. -/
noncomputable def delta (x : ℤ) : ℤ → ℂ := Pi.single x 1

lemma finSupp_delta (x : ℤ) : FinSupp (delta x) := by
  refine ⟨{x}, ?_⟩
  intro y hy
  rw [delta, Pi.single_eq_of_ne]
  simpa using hy

lemma finSupp_zero' : FinSupp (0 : ℤ → ℂ) := ⟨∅, fun x _ => rfl⟩

lemma finSupp_sum {ι : Type*} (s : Finset ι) {f : ι → ℤ → ℂ}
    (hf : ∀ i ∈ s, FinSupp (f i)) : FinSupp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, fun x _ => by simp⟩
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- `pair` is additive in its first argument. -/
lemma pair_add (a b : ℕ → ℂ) (l : ℕ →₀ ℂ) : pair (a + b) l = pair a l + pair b l := by
  classical
  rw [pair, pair, pair, ← Finsupp.sum_add]
  exact Finsupp.sum_congr fun n c => by simp [Pi.add_apply, add_mul]

/-- `pair` is homogeneous in its first argument. -/
lemma pair_smul (c : ℂ) (a : ℕ → ℂ) (l : ℕ →₀ ℂ) : pair (c • a) l = c * pair a l := by
  classical
  simp only [pair, Finsupp.sum, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

section Operator

variable {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ}

/-- `T` vanishes when its first argument is `0`. -/
lemma T_zero_left
    (hlin : ∀ f f' g (c : ℂ), FinSupp f → FinSupp f' → FinSupp g →
      T (f + c • f') g = T f g + c • T f' g) (g : ℤ → ℂ) (hg : FinSupp g) :
    T 0 g = 0 := by
  have h := hlin 0 0 g 1 finSupp_zero' finSupp_zero' hg
  simp only [Pi.zero_apply, one_smul, add_zero] at h
  have h' : T 0 g + 0 = T 0 g + T 0 g := by simpa using h
  exact (add_left_cancel h').symm

/-- `T` vanishes when its second argument is `0`. -/
lemma T_zero_right
    (hlin : ∀ f g g' (c : ℂ), FinSupp f → FinSupp g → FinSupp g' →
      T f (g + c • g') = T f g + c • T f g') (f : ℤ → ℂ) (hf : FinSupp f) :
    T f 0 = 0 := by
  have h := hlin f 0 0 1 hf finSupp_zero' finSupp_zero'
  simp only [Pi.zero_apply, one_smul, add_zero] at h
  have h' : T f 0 + 0 = T f 0 + T f 0 := by simpa using h
  exact (add_left_cancel h').symm

/-- `T` is additive in its first argument. -/
lemma T_add_left
    (hlin : ∀ f f' g (c : ℂ), FinSupp f → FinSupp f' → FinSupp g →
      T (f + c • f') g = T f g + c • T f' g)
    {f f' g : ℤ → ℂ} (hf : FinSupp f) (hf' : FinSupp f') (hg : FinSupp g) :
    T (f + f') g = T f g + T f' g := by
  have h := hlin f f' g 1 hf hf' hg
  simpa using h

/-- `T` is additive in its second argument. -/
lemma T_add_right
    (hlin : ∀ f g g' (c : ℂ), FinSupp f → FinSupp g → FinSupp g' →
      T f (g + c • g') = T f g + c • T f g')
    {f g g' : ℤ → ℂ} (hf : FinSupp f) (hg : FinSupp g) (hg' : FinSupp g') :
    T f (g + g') = T f g + T f g' := by
  have h := hlin f g g' 1 hf hg hg'
  simpa using h

/-- `T` is homogeneous in its first argument. -/
lemma T_smul_left
    (hlin : ∀ f f' g (c : ℂ), FinSupp f → FinSupp f' → FinSupp g →
      T (f + c • f') g = T f g + c • T f' g)
    (f g : ℤ → ℂ) (c : ℂ) (hf : FinSupp f) (hg : FinSupp g) :
    T (c • f) g = c • T f g := by
  have h := hlin 0 f g c finSupp_zero' hf hg
  rw [zero_add, T_zero_left hlin g hg, zero_add] at h
  exact h

/-- `T` is homogeneous in its second argument. -/
lemma T_smul_right
    (hlin : ∀ f g g' (c : ℂ), FinSupp f → FinSupp g → FinSupp g' →
      T f (g + c • g') = T f g + c • T f g')
    (f g : ℤ → ℂ) (c : ℂ) (hf : FinSupp f) (hg : FinSupp g) :
    T f (c • g) = c • T f g := by
  have h := hlin f 0 g c hf finSupp_zero' hg
  rw [zero_add, T_zero_right hlin f hf, zero_add] at h
  exact h

/-- `T` applied to a finite linear combination of finitely supported functions, in its first
argument. -/
lemma T_sum_left
    (hlin : ∀ f f' g (c : ℂ), FinSupp f → FinSupp f' → FinSupp g →
      T (f + c • f') g = T f g + c • T f' g)
    {ι : Type*} (s : Finset ι) (f : ι → ℤ → ℂ) (c : ι → ℂ) (g : ℤ → ℂ)
    (hf : ∀ i ∈ s, FinSupp (f i)) (hg : FinSupp g) :
    T (∑ i ∈ s, c i • f i) g = ∑ i ∈ s, c i • T (f i) g := by
  classical
  induction s using Finset.induction with
  | empty => simpa using T_zero_left hlin g hg
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hfa : FinSupp (f a) := hf a (Finset.mem_insert_self a s)
      have hfs : FinSupp (∑ i ∈ s, c i • f i) :=
        finSupp_sum s fun i hi => (hf i (Finset.mem_insert_of_mem hi)).smul (c i)
      rw [T_add_left hlin (hfa.smul (c a)) hfs hg,
        T_smul_left hlin (f a) g (c a) hfa hg,
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- `T` applied to a finite linear combination of finitely supported functions, in its second
argument. -/
lemma T_sum_right
    (hlin : ∀ f g g' (c : ℂ), FinSupp f → FinSupp g → FinSupp g' →
      T f (g + c • g') = T f g + c • T f g')
    {ι : Type*} (s : Finset ι) (g : ι → ℤ → ℂ) (c : ι → ℂ) (f : ℤ → ℂ)
    (hg : ∀ i ∈ s, FinSupp (g i)) (hf : FinSupp f) :
    T f (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • T f (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using T_zero_right hlin f hf
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hga : FinSupp (g a) := hg a (Finset.mem_insert_self a s)
      have hgs : FinSupp (∑ i ∈ s, c i • g i) :=
        finSupp_sum s fun i hi => (hg i (Finset.mem_insert_of_mem hi)).smul (c i)
      rw [T_add_right hlin hf (hga.smul (c a)) hgs,
        T_smul_right hlin f (g a) (c a) hf hga,
        ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

/-- **The expansion of a bilinear operator over the finite supports of its arguments.**  If
`s`, `t` are finite sets containing the supports of `f` and `g` (given by the "off the set"
conditions below), then `T f g` is the finite sum of `(f x)(g y) T δ_x δ_y`. -/
lemma T_eq_sum_delta
    (hlin₁ : ∀ f f' g (c : ℂ), FinSupp f → FinSupp f' → FinSupp g →
      T (f + c • f') g = T f g + c • T f' g)
    (hlin₂ : ∀ f g g' (c : ℂ), FinSupp f → FinSupp g → FinSupp g' →
      T f (g + c • g') = T f g + c • T f g')
    (f g : ℤ → ℂ) (s t : Finset ℤ)
    (hs : ∀ x ∉ s, f x = 0) (ht : ∀ y ∉ t, g y = 0) :
    T f g = ∑ x ∈ s, ∑ y ∈ t, (f x * g y) • T (delta x) (delta y) := by
  classical
  set F : ℤ → ℂ := ∑ x ∈ s, (f x) • delta x with hF
  set G : ℤ → ℂ := ∑ y ∈ t, (g y) • delta y with hG
  have hFfin : FinSupp F := finSupp_sum s fun x _ => (finSupp_delta x).smul (f x)
  have hGfin : FinSupp G := finSupp_sum t fun y _ => (finSupp_delta y).smul (g y)
  have hf_exp : f = F := by
    funext y
    rw [hF, Finset.sum_apply]
    rw [Finset.sum_eq_single y]
    · simp [delta]
    · intro x _ hxy
      simp [delta, Pi.single_eq_of_ne (Ne.symm hxy)]
    · intro hy
      simp [hs y hy]
  have hg_exp : g = G := by
    funext y
    rw [hG, Finset.sum_apply]
    rw [Finset.sum_eq_single y]
    · simp [delta]
    · intro x _ hxy
      simp [delta, Pi.single_eq_of_ne (Ne.symm hxy)]
    · intro hy
      simp [ht y hy]
  calc T f g = T F G := by
        rw [hf_exp, hg_exp]
    _ = ∑ x ∈ s, (f x) • T (delta x) G :=
        T_sum_left hlin₁ s (fun x => delta x) f G (fun x _ => finSupp_delta x) hGfin
    _ = ∑ x ∈ s, (f x) • (∑ y ∈ t, (g y) • T (delta x) (delta y)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [T_sum_right hlin₂ t (fun y => delta y) g (delta x) (fun y _ => finSupp_delta y)
          (finSupp_delta x)]
    _ = ∑ x ∈ s, ∑ y ∈ t, (f x * g y) • T (delta x) (delta y) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [smul_smul]

/-- **The trilinear form of area A8.**  Given the bilinear operator `T` and a finitely supported
test object `ψ x` for each `x : ℤ`, `lam T ψ u v h` is `∑' x, ⟨T u v (·) x, ψ x⟩ h x` when all
three of `u`, `v`, `h` are finitely supported, and `0` otherwise. -/
noncomputable def lam (T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ) (psi : ℤ → (ℕ →₀ ℂ))
    (u v h : ℤ → ℂ) : ℂ := by
  classical
  exact if FinSupp u ∧ FinSupp v ∧ FinSupp h then
    ∑' x : ℤ, pair (fun n => T u v n x) (psi x) * h x
  else 0

lemma lam_of_finSupp {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ} {psi : ℤ → (ℕ →₀ ℂ)}
    {u v h : ℤ → ℂ} (hu : FinSupp u) (hv : FinSupp v) (hh : FinSupp h) :
    lam T psi u v h = ∑' x : ℤ, pair (fun n => T u v n x) (psi x) * h x := by
  rw [lam, if_pos ⟨hu, hv, hh⟩]

lemma lam_of_not_finSupp {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ} {psi : ℤ → (ℕ →₀ ℂ)}
    {u v h : ℤ → ℂ} (hu : ¬(FinSupp u ∧ FinSupp v ∧ FinSupp h)) : lam T psi u v h = 0 := by
  rw [lam, if_neg hu]

end Operator

end Work.KMTAreas
