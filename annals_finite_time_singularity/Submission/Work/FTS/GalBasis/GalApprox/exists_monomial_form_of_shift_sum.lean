import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.NatInt
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.RingNF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Monomial form of a sum of shifted powers

The main result of this file, `Work.FTS.GalBasis.GalApprox.exists_monomial_form_of_shift_sum`,
says that a finite sum `∑ i, c i * (z - A) ^ (p i) * (θ - C) ^ (q i)` of translated
monomials is again a finite sum `∑ k, c' k * z ^ (p' k) * θ ^ (q' k)` of monomials in the
*untranslated* variables `z, θ`.  (The number of monomials may grow; repetitions are
allowed on the right-hand side.)

The proof never expands any binomial: it uses only that the class of functions of the form
`∑ k, c' k * z ^ (p' k) * θ ^ (q' k)` is a `ℝ`-submodule of `ℝ → ℝ → ℝ` closed under
multiplication by `z` and by `θ`, together with the two identities

* `c * (z - A) ^ (p+1) * (θ - C) ^ q = (z - A) * (c * (z - A) ^ p * (θ - C) ^ q)`,
* `c * (z - A) ^ p * (θ - C) ^ (q+1) = (θ - C) * (c * (z - A) ^ p * (θ - C) ^ q)`

which make the induction on `(p, q)` immediate.  Closures are recorded as the lemmas
`isMonoSum_add`, `isMonoSum_smul`, `isMonoSum_mul_z`, `isMonoSum_mul_theta`, the finite
sum statement is `isMonoSum_finset_sum`, and the inductive construction of a translated
monomial is `isMonoSum_shift_pow`.
-/

namespace Work.FTS.GalBasis.GalApprox

open scoped BigOperators

/-- A function of two real variables which is a finite sum of two-variable monomials
`c * z ^ a * θ ^ b`. -/
def IsMonoSum (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ (m : ℕ) (a b : Fin m → ℕ) (c : Fin m → ℝ),
    ∀ z θ, f z θ = ∑ k, c k * z ^ (a k) * θ ^ (b k)

theorem isMonoSum_congr {f g : ℝ → ℝ → ℝ} (hfg : ∀ z θ, f z θ = g z θ)
    (hg : IsMonoSum g) : IsMonoSum f := by
  obtain ⟨m, a, b, c, hc⟩ := hg
  exact ⟨m, a, b, c, fun z θ => (hfg z θ).trans (hc z θ)⟩

theorem isMonoSum_zero : IsMonoSum (0 : ℝ → ℝ → ℝ) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun z θ => ?_⟩
  simp

theorem isMonoSum_const (r : ℝ) : IsMonoSum (fun _ _ : ℝ => r) := by
  refine ⟨1, fun _ => 0, fun _ => 0, fun _ => r, fun z θ => ?_⟩
  simp

theorem isMonoSum_add {f g : ℝ → ℝ → ℝ} (hf : IsMonoSum f) (hg : IsMonoSum g) :
    IsMonoSum (fun z θ => f z θ + g z θ) := by
  obtain ⟨m₁, a₁, b₁, c₁, h₁⟩ := hf
  obtain ⟨m₂, a₂, b₂, c₂, h₂⟩ := hg
  refine ⟨m₁ + m₂, Fin.append a₁ a₂, Fin.append b₁ b₂, Fin.append c₁ c₂, fun z θ => ?_⟩
  change f z θ + g z θ =
    ∑ k, Fin.append c₁ c₂ k * z ^ (Fin.append a₁ a₂ k) * θ ^ (Fin.append b₁ b₂ k)
  rw [h₁ z θ, h₂ z θ, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem isMonoSum_smul (r : ℝ) {f : ℝ → ℝ → ℝ} (hf : IsMonoSum f) :
    IsMonoSum (fun z θ => r * f z θ) := by
  obtain ⟨m, a, b, c, hc⟩ := hf
  refine ⟨m, a, b, fun k => r * c k, fun z θ => ?_⟩
  change r * f z θ = ∑ k, (r * c k) * z ^ (a k) * θ ^ (b k)
  rw [hc z θ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem isMonoSum_mul_z {f : ℝ → ℝ → ℝ} (hf : IsMonoSum f) :
    IsMonoSum (fun z θ => z * f z θ) := by
  obtain ⟨m, a, b, c, hc⟩ := hf
  refine ⟨m, fun k => a k + 1, b, c, fun z θ => ?_⟩
  change z * f z θ = ∑ k, c k * z ^ (a k + 1) * θ ^ (b k)
  rw [hc z θ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ']
  ring

theorem isMonoSum_mul_theta {f : ℝ → ℝ → ℝ} (hf : IsMonoSum f) :
    IsMonoSum (fun z θ => θ * f z θ) := by
  obtain ⟨m, a, b, c, hc⟩ := hf
  refine ⟨m, a, fun k => b k + 1, c, fun z θ => ?_⟩
  change θ * f z θ = ∑ k, c k * z ^ (a k) * θ ^ (b k + 1)
  rw [hc z θ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ']
  ring

theorem isMonoSum_mul_sub_z (A : ℝ) {f : ℝ → ℝ → ℝ} (hf : IsMonoSum f) :
    IsMonoSum (fun z θ => (z - A) * f z θ) := by
  have h := isMonoSum_add (isMonoSum_mul_z hf) (isMonoSum_smul (-A) hf)
  exact isMonoSum_congr (fun z θ => by ring) h

theorem isMonoSum_mul_sub_theta (C : ℝ) {f : ℝ → ℝ → ℝ} (hf : IsMonoSum f) :
    IsMonoSum (fun z θ => (θ - C) * f z θ) := by
  have h := isMonoSum_add (isMonoSum_mul_theta hf) (isMonoSum_smul (-C) hf)
  exact isMonoSum_congr (fun z θ => by ring) h

theorem isMonoSum_theta_shift (C : ℝ) :
    ∀ (q : ℕ) (c : ℝ), IsMonoSum (fun _ θ => c * (θ - C) ^ q) := by
  intro q
  induction q with
  | zero =>
      intro c
      exact isMonoSum_congr (fun z θ => by simp) (isMonoSum_const c)
  | succ n ih =>
      intro c
      have h := isMonoSum_mul_sub_theta C (ih c)
      exact isMonoSum_congr (fun z θ => by rw [pow_succ]; ring) h

theorem isMonoSum_shift_pow (A C : ℝ) :
    ∀ (p : ℕ) (q : ℕ) (c : ℝ), IsMonoSum (fun z θ => c * (z - A) ^ p * (θ - C) ^ q) := by
  intro p
  induction p with
  | zero =>
      intro q c
      refine isMonoSum_congr (fun z θ => ?_) (isMonoSum_theta_shift C q c)
      simp
  | succ n ih =>
      intro q c
      have h := isMonoSum_mul_sub_z A (ih q c)
      exact isMonoSum_congr (fun z θ => by rw [pow_succ]; ring) h

theorem isMonoSum_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ → ℝ)
    (h : ∀ i ∈ s, IsMonoSum (f i)) :
    IsMonoSum (∑ i ∈ s, f i) :=
  Finset.sum_induction f IsMonoSum (fun _ _ ha hb => isMonoSum_add ha hb) isMonoSum_zero h

theorem exists_monomial_form_of_shift_sum {A C : ℝ} {ι : Type*} [Fintype ι] (p q : ι → ℕ) (c : ι → ℝ) :
    ∃ (m : ℕ) (p' q' : Fin m → ℕ) (c' : Fin m → ℝ),
      ∀ z θ : ℝ, (∑ i, c i * (z - A) ^ (p i) * (θ - C) ^ (q i))
        = ∑ k, c' k * z ^ (p' k) * θ ^ (q' k) := by
  have hterm : ∀ i : ι, IsMonoSum (fun z θ => c i * (z - A) ^ (p i) * (θ - C) ^ (q i)) :=
    fun i => isMonoSum_shift_pow A C (p i) (q i) (c i)
  have hsum : IsMonoSum (fun z θ => ∑ i, c i * (z - A) ^ (p i) * (θ - C) ^ (q i)) := by
    have h := isMonoSum_finset_sum (Finset.univ : Finset ι)
      (fun i z θ => c i * (z - A) ^ (p i) * (θ - C) ^ (q i)) (fun i _ => hterm i)
    refine isMonoSum_congr (fun z θ => ?_) h
    simp only [Finset.sum_apply]
  exact hsum

end Work.FTS.GalBasis.GalApprox
