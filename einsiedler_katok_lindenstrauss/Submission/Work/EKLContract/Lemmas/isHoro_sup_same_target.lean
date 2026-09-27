import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLContract.Lemmas.mem_sup_Uij_same_target_prod
import Submission.Work.EKLContract.Lemmas.uij_same_target_prod_of_offdiag
import Submission.Work.EKLContract.Lemmas.uij_same_target_tendsto

/-!
# Joins of root groups with the same target are admissible

`Work.EKLContract.IsHoro U` is the frozen contract that a subgroup `U ≤ SL₃(ℝ)` be closed,
normalised by the diagonal group `A = {aDiag t}` and contracted by some `aDiag t`
(`isHoro_Uij.lean` verifies it for the individual root groups `U_ij = {u_ij(s) = 1 + s E_ij}`,
`isHoro_Upar.lean` for the three-dimensional horospherical subgroups, and
`isHoro_sup_same_source.lean` for joins `U_ij ⊔ U_ik` with a *common source*).

This file verifies it for the join of two root groups with a **common target**,

`U_ij ⊔ U_kj`,  `i ≠ j`, `k ≠ j`,

which (for `i ≠ k`) is the two-dimensional *abelian* group of unitriangular matrices
`1 + s E_ij + t E_kj` — the diagonal-opposite companion of the same-source case: here the two
roots are `e_i - e_j` and `e_k - e_j`, whose sum is not a root, so the commutator
`[E_ij, E_kj] = δ_{jk} E_ij = 0` vanishes instead of producing a third root group.

The mathematics (explicit `3 × 3` matrix bookkeeping on top of `horoUij_*`):

* `E_ij E_kj = δ_{jk} E_ij = 0` and `E_kj E_ij = δ_{ji} E_kj = 0`, so the two root groups
  commute and `(s,t) ↦ u_ij(s) u_kj(t)` is a homomorphism `(ℝ²,+) → SL₃(ℝ)`; the join is
  exactly its range (`mem_sup_Uij_same_target_prod`) and every element of the join is
  `1 + s E_ij + t E_kj` (`st_toMat_mul`, `st_mem_sup_iff_entries`);
* conversely any element of `SL₃(ℝ)` agreeing with `1` outside the two slots `(i,j)`, `(k,j)`
  is such a product (`uij_same_target_prod_of_offdiag`), which exhibits the join as a finite
  intersection of closed entry conditions (`st_isClosed`);
* `aDiag τ · u_ij(s) u_kj(t) · (aDiag τ)⁻¹ = u_ij(e^{τ_i - τ_j} s) u_kj(e^{τ_k - τ_j} t)`
  (`st_conj_mem`), so the diagonal group normalises the join;
* for `t` with `t j = 1`, `t i = t k = 0` both exponents are negative and the conjugates tend
  to `1` as `n → ∞` (`st_contraction`).

The degenerate case `i = k` (the two root groups are the same subgroup, so the join is `U_ij`)
reduces to `isHoro_Uij` by proof irrelevance.
-/

open MeasureTheory Filter Topology
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLContract.Lemmas

open Work.EKLContract

/-! ## The underlying matrix of a product `u_ij(s) · u_kj(t)` -/

/-- The underlying matrix of `u_ij(s) u_kj(t)` is `1 + s E_ij + t E_kj`: the cross term
`E_ij E_kj = δ_{jk} E_ij` vanishes because `k ≠ j`, so the two root groups commute. -/
theorem st_toMat_mul {i j k : Fin 3} (hij : i ≠ j) (hkj : k ≠ j) (s t : ℝ) :
    toMat (uij hij s * uij hkj t) = (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j s
      + Matrix.single k j t := by
  rw [toMat_mul, horoUij_toMat hij, horoUij_toMat hkj]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.single_mul_single_of_ne (c := s) (i := i) (j := j) (k := k) hkj.symm (d := t)]
  abel

/-- Entries of an element of `SL₃(ℝ)` are continuous functions of the element. -/
theorem st_cont_entry (a b : Fin 3) : Continuous fun g : SL3 => toMat g a b :=
  (continuous_apply b).comp (Matrix.SpecialLinearGroup.continuous_apply _ continuous_id a)

/-! ## Closedness: the carrier is described by finitely many entry conditions -/

/-- Membership in `U_ij ⊔ U_kj` described by entries: everything agrees with `1` outside the
two slots `(i,j)`, `(k,j)`.  (For `i ≠ k` the first implication direction is
`st_toMat_mul`, the second is `uij_same_target_prod_of_offdiag`.) -/
theorem st_mem_sup_iff_entries {i j k : Fin 3} (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k)
    (g : SL3) :
    g ∈ Uij hij ⊔ Uij hkj ↔
      ∀ a b : Fin 3, ¬((a = i ∧ b = j) ∨ (a = k ∧ b = j)) →
        toMat g a b = (1 : Matrix (Fin 3) (Fin 3) ℝ) a b := by
  constructor
  · intro hg
    obtain ⟨s, t, rfl⟩ := (mem_sup_Uij_same_target_prod hij hkj hik g).mp hg
    rw [st_toMat_mul hij hkj s t]
    intro a b hab
    have h1 : ¬(i = a ∧ j = b) := fun h => hab (Or.inl ⟨h.1.symm, h.2.symm⟩)
    have h2 : ¬(k = a ∧ j = b) := fun h => hab (Or.inr ⟨h.1.symm, h.2.symm⟩)
    simp only [Matrix.add_apply, Matrix.single_apply, if_neg h1, if_neg h2, add_zero]
  · intro H
    rw [mem_sup_Uij_same_target_prod hij hkj hik]
    exact ⟨toMat g i j, toMat g k j, uij_same_target_prod_of_offdiag hij hkj hik g
      (fun a b h1 h2 => H a b (fun h => h.elim h1 h2))⟩

/-- `U_ij ⊔ U_kj` is closed in `SL₃(ℝ)`: its carrier is the intersection of the finitely many
closed conditions "entry `(a,b)` equals the identity's entry" for `(a,b)` outside the two slots. -/
theorem st_isClosed {i j k : Fin 3} (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k) :
    IsClosed ((Uij hij ⊔ Uij hkj : Subgroup SL3) : Set SL3) := by
  have hchar : ((Uij hij ⊔ Uij hkj : Subgroup SL3) : Set SL3) =
      {g : SL3 | ∀ a b : Fin 3, ¬((a = i ∧ b = j) ∨ (a = k ∧ b = j)) →
        toMat g a b = (1 : Matrix (Fin 3) (Fin 3) ℝ) a b} :=
    Set.ext fun g => st_mem_sup_iff_entries hij hkj hik g
  rw [hchar]
  have hset : {g : SL3 | ∀ a b : Fin 3, ¬((a = i ∧ b = j) ∨ (a = k ∧ b = j)) →
        toMat g a b = (1 : Matrix (Fin 3) (Fin 3) ℝ) a b} =
      ⋂ (p : {p : Fin 3 × Fin 3 // ¬((p.1 = i ∧ p.2 = j) ∨ (p.1 = k ∧ p.2 = j))}),
        {g : SL3 | toMat g p.1.1 p.1.2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1.1 p.1.2} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Subtype.forall]
    exact ⟨fun H p hp => H p.1 p.2 hp, fun H a b hab => H (a, b) hab⟩
  rw [hset]
  exact isClosed_iInter fun p => isClosed_eq (st_cont_entry p.1.1 p.1.2) continuous_const

/-! ## Normalisation by the diagonal group -/

/-- Conjugation by `aDiag τ` rescales the two slots independently:
`aDiag τ · u_ij(s) u_kj(t) · (aDiag τ)⁻¹ = u_ij(e^{τ_i - τ_j} s) u_kj(e^{τ_k - τ_j} t)`. -/
theorem st_conj_mem {i j k : Fin 3} (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k)
    (t : Fin 3 → ℝ) (u : SL3) (hu : u ∈ Uij hij ⊔ Uij hkj) :
    aDiag t * u * (aDiag t)⁻¹ ∈ Uij hij ⊔ Uij hkj := by
  rw [mem_sup_Uij_same_target_prod hij hkj hik] at hu
  obtain ⟨s, s', rfl⟩ := hu
  rw [mem_sup_Uij_same_target_prod hij hkj hik]
  exact ⟨Real.exp (t i - t j) * s, Real.exp (t k - t j) * s',
    (by rw [show aDiag t * (uij hij s * uij hkj s') * (aDiag t)⁻¹ =
        (aDiag t * uij hij s * (aDiag t)⁻¹) * (aDiag t * uij hkj s' * (aDiag t)⁻¹) from by group,
      horoUij_aDiag_conj, horoUij_aDiag_conj])⟩

/-! ## Contraction -/

/-- The join is contracted by `aDiag t` for any `t` with `t i < t j` and `t k < t j`: every
element of the join is a two-factor product, and both factors are contracted. -/
theorem st_contraction {i j k : Fin 3} (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k)
    (t : Fin 3 → ℝ) (hti : t i < t j) (htk : t k < t j) :
    ∀ u ∈ Uij hij ⊔ Uij hkj,
      Tendsto (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (𝓝 1) := by
  intro u hu
  rw [mem_sup_Uij_same_target_prod hij hkj hik] at hu
  obtain ⟨s, s', rfl⟩ := hu
  exact uij_same_target_tendsto hij hkj t hti htk s s'

/-! ## The target -/

theorem isHoro_sup_same_target {i j k : Fin 3} (hij : i ≠ j) (hkj : k ≠ j) : Work.EKLContract.IsHoro (Work.EKLContract.Uij hij ⊔ Work.EKLContract.Uij hkj) := by
  by_cases hik : i = k
  · -- the two root groups coincide: the join is `U_ij` itself
    subst hik
    have hU : Uij hij = Uij hkj := congrArg Uij (Subsingleton.elim hij hkj)
    simpa [hU] using isHoro_Uij hij
  · refine ⟨st_isClosed hij hkj hik, ?_, ?_⟩
    · intro t u hu
      exact st_conj_mem hij hkj hik t u hu
    · -- contract by `t = (0, 1, 0)`-shaped: `t j` maximal, `t i = t k = 0`
      refine ⟨fun a : Fin 3 => if a = j then 1 else 0, ?_⟩
      intro u hu
      refine st_contraction hij hkj hik _ ?_ ?_ u hu
      · show (if i = j then 1 else 0) < (if j = j then 1 else 0)
        rw [if_neg hij, if_pos rfl]
        norm_num
      · show (if k = j then 1 else 0) < (if j = j then 1 else 0)
        rw [if_neg hkj, if_pos rfl]
        norm_num

end Work.EKLContract.Lemmas
