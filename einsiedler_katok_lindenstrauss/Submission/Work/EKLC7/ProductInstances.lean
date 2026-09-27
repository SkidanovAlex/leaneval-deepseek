import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLContract.Lemmas.isHoro_sup_same_source
import Submission.Work.EKLContract.Lemmas.isHoro_sup_same_target

/-!
# C7: the four product instances of the commutator computation

For pairwise distinct indices `i, j, k : Fin 3` this proves the four existentials of the C7
commutator computation: for each of the four ways of choosing which root group is *centralised*
by `aDiag t` and which root group(s) are *contracted* by it, there is a vector `t : Fin 3 → ℝ`.

Concretely:
* `aDiag t` centralises `U_ab` (i.e. `aDiag t * g = g * aDiag t` for all `g ∈ U_ab`) exactly when
  `t a = t b`, and `aDiag t` contracts `U_ab` (all conjugates `aDiag t ^ n * g * (aDiag t ^ n)⁻¹`
  tend to `1`) exactly when `t a < t b` (the `n`-fold conjugate of `u_ab(s)` is
  `u_ab(e^{n (t a - t b)} s)`).
* The joins `VjkIk = U_jk ⊔ U_ik` (common target `k`) and `VijIk = U_ij ⊔ U_ik` (common source
  `i`) are contracted as soon as both of their root groups are contracted.

The four instances therefore just need a `t` satisfying the corresponding (in)equalities, which
always exists by the choice `t = 0` resp. `1` in the relevant slots.
-/

namespace Work.EKLC7

open Filter Topology
open Work.EKLContract

/-- `aDiag t` commutes with every element of `U_ij` when `t i = t j`: conjugating a transvection
by `aDiag t` rescales its parameter by `exp (t i - t j) = 1`. -/
theorem aDiag_centralizes_uij {i j : Fin 3} (h : i ≠ j) (t : Fin 3 → ℝ) (ht : t i = t j)
    (g : SL3) (hg : g ∈ Uij h) : aDiag t * g = g * aDiag t := by
  obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff h g).mp hg
  rw [Work.EKLContract.Lemmas.horoUij_aDiag_mul t h s, ht, sub_self, Real.exp_zero, one_mul]

/-- **First product instance.**  `aDiag t` centralises `U_ij` and contracts
`VjkIk = U_jk ⊔ U_ik` (the join of the two root groups with common target `k`).
The vector `t = (0, 0, 1)` (value `1` at the slot `k`, `0` elsewhere) has `t i = t j = 0` and
`t j, t i < t k = 1`. -/
theorem prodConj1 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (∃ t : Fin 3 → ℝ,
      (∀ g ∈ Work.EKLContract.Uij hij, Work.EKLContract.aDiag t * g = g *
        Work.EKLContract.aDiag t) ∧
      (∀ u ∈ Work.EKLC7.VjkIk hjk hik,
        Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u
          * (Work.EKLContract.aDiag t ^ n)⁻¹) Filter.atTop (nhds 1))) := by
  refine ⟨fun c => if c = k then 1 else 0, ?_, ?_⟩
  · intro g hg
    refine aDiag_centralizes_uij hij _ ?_ g hg
    show (if i = k then 1 else 0) = (if j = k then 1 else 0)
    rw [if_neg hik, if_neg hjk]
  · intro u hu
    change u ∈ Uij hjk ⊔ Uij hik at hu
    refine Work.EKLContract.Lemmas.st_contraction hjk hik hij.symm _ ?_ ?_ u hu
    · show (if j = k then 1 else 0) < (if k = k then 1 else 0)
      rw [if_neg hjk, if_pos rfl]; norm_num
    · show (if i = k then 1 else 0) < (if k = k then 1 else 0)
      rw [if_neg hik, if_pos rfl]; norm_num

/-- **Second product instance.**  `aDiag t` centralises `U_jk` and contracts
`VijIk = U_ij ⊔ U_ik` (the join of the two root groups with common source `i`).
The vector `srcU_exp i j k` (`0` at `i`, `1` at `j` and `k`) has `t j = t k = 1` and
`t i = 0 < 1`. -/
theorem prodConj2 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (∃ t : Fin 3 → ℝ,
      (∀ g ∈ Work.EKLContract.Uij hjk, Work.EKLContract.aDiag t * g = g *
        Work.EKLContract.aDiag t) ∧
      (∀ u ∈ Work.EKLC7.VijIk hij hik,
        Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u
          * (Work.EKLContract.aDiag t ^ n)⁻¹) Filter.atTop (nhds 1))) := by
  refine ⟨Work.EKLContract.Lemmas.srcU_exp i j k, ?_, ?_⟩
  · intro g hg
    refine aDiag_centralizes_uij hjk _ ?_ g hg
    rw [Work.EKLContract.Lemmas.srcU_exp_j, Work.EKLContract.Lemmas.srcU_exp_k hjk]
  · intro u hu
    change u ∈ Uij hij ⊔ Uij hik at hu
    rw [Work.EKLContract.Lemmas.srcU_sup_eq_sub hij hik] at hu
    rw [Work.EKLContract.Lemmas.srcU_mem_sub] at hu
    obtain ⟨s, t', rfl⟩ := hu
    exact Work.EKLContract.Lemmas.srcU_contraction hij hik hjk s t'

/-- **Third product instance.**  `aDiag t` centralises `U_jk` and contracts the single root
group `U_ik`.  The vector `srcU_exp i j k` has `t j = t k = 1` and `t i = 0 < t k = 1`. -/
theorem prodConj3 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (∃ t : Fin 3 → ℝ,
      (∀ g ∈ Work.EKLContract.Uij hjk, Work.EKLContract.aDiag t * g = g *
        Work.EKLContract.aDiag t) ∧
      (∀ u ∈ Work.EKLContract.Uij hik,
        Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u
          * (Work.EKLContract.aDiag t ^ n)⁻¹) Filter.atTop (nhds 1))) := by
  refine ⟨Work.EKLContract.Lemmas.srcU_exp i j k, ?_, ?_⟩
  · intro g hg
    refine aDiag_centralizes_uij hjk _ ?_ g hg
    rw [Work.EKLContract.Lemmas.srcU_exp_j, Work.EKLContract.Lemmas.srcU_exp_k hjk]
  · intro u hu
    obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hik u).mp hu
    refine Work.EKLContract.Lemmas.horoUij_tendsto_conj
      (Work.EKLContract.Lemmas.srcU_exp i j k) hik ?_ s
    show Work.EKLContract.Lemmas.srcU_exp i j k i < Work.EKLContract.Lemmas.srcU_exp i j k k
    rw [Work.EKLContract.Lemmas.srcU_exp_i hij hik, Work.EKLContract.Lemmas.srcU_exp_k hjk]
    norm_num

/-- **Fourth product instance.**  `aDiag t` centralises `U_ij` and contracts the single root
group `U_ik`.  The vector `t = (0, 0, 1)` has `t i = t j = 0` and `t i = 0 < t k = 1`. -/
theorem prodConj4 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (∃ t : Fin 3 → ℝ,
      (∀ g ∈ Work.EKLContract.Uij hij, Work.EKLContract.aDiag t * g = g *
        Work.EKLContract.aDiag t) ∧
      (∀ u ∈ Work.EKLContract.Uij hik,
        Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u
          * (Work.EKLContract.aDiag t ^ n)⁻¹) Filter.atTop (nhds 1))) := by
  refine ⟨fun c => if c = k then 1 else 0, ?_, ?_⟩
  · intro g hg
    refine aDiag_centralizes_uij hij _ ?_ g hg
    show (if i = k then 1 else 0) = (if j = k then 1 else 0)
    rw [if_neg hik, if_neg hjk]
  · intro u hu
    obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff hik u).mp hu
    refine Work.EKLContract.Lemmas.horoUij_tendsto_conj (fun c => if c = k then 1 else 0) hik ?_ s
    show (if i = k then 1 else 0) < (if k = k then 1 else 0)
    rw [if_neg hik, if_pos rfl]; norm_num

theorem ProductInstances : ∀ {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
    (∃ t : Fin 3 → ℝ, (∀ g ∈ Work.EKLContract.Uij hij, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t) ∧
      (∀ u ∈ Work.EKLC7.VjkIk hjk hik,
        Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u
          * (Work.EKLContract.aDiag t ^ n)⁻¹) Filter.atTop (nhds 1)))
    ∧ (∃ t : Fin 3 → ℝ, (∀ g ∈ Work.EKLContract.Uij hjk, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t) ∧
      (∀ u ∈ Work.EKLC7.VijIk hij hik,
        Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u
          * (Work.EKLContract.aDiag t ^ n)⁻¹) Filter.atTop (nhds 1)))
    ∧ (∃ t : Fin 3 → ℝ, (∀ g ∈ Work.EKLContract.Uij hjk, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t) ∧
      (∀ u ∈ Work.EKLContract.Uij hik,
        Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u
          * (Work.EKLContract.aDiag t ^ n)⁻¹) Filter.atTop (nhds 1)))
    ∧ (∃ t : Fin 3 → ℝ, (∀ g ∈ Work.EKLContract.Uij hij, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t) ∧
      (∀ u ∈ Work.EKLContract.Uij hik,
        Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u
          * (Work.EKLContract.aDiag t ^ n)⁻¹) Filter.atTop (nhds 1))) := by
  intro i j k hij hjk hik
  exact ⟨prodConj1 hij hjk hik, prodConj2 hij hjk hik,
    prodConj3 hij hjk hik, prodConj4 hij hjk hik⟩

end Work.EKLC7
