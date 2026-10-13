/-
  A **singleton good stratum** at the absolute split `Stratum 0 M`.

  Given any point `P` of the closed cube `cubeC (0 + M)`, there is a *good* fibrewise
  stratum `W : Stratum 0 M` whose underlying semi-Pfaffian set is exactly `{P}` and whose
  number of equations is the maximal `j = M`.

  The construction is the crudest possible: the chain is empty (`r = 0`, so the set is
  genuinely semialgebraic), the basic set cuts out `P` by the `M` coordinate equations
  `xᵢ = Pᵢ`, and the `M` equations `h_a = x_a - P_a` have the identity as Jacobian w.r.t.
  the fibre coordinates (which are *all* coordinates, since `p = 0`), hence rank `M`, with
  zero set exactly `{P}`, so the local containment clause of `Good` holds trivially.

  Everything is bookkept through `Fin.natAdd 0 : Fin M → Fin (0 + M)`, the canonical
  identification of `Fin M` with `Fin (0 + M)`.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.GermDefs

set_option autoImplicit false
noncomputable section

open WilkiesDesign WilkiesDesign.E

namespace Work.CoreStep

/-- The basic set `{x | ∀ i, x i = P i}` (as a DNF-`basic` with no strict inequalities) holds
exactly at `P`. -/
private lemma holds_iff {M : ℕ} (P : Fin (0 + M) → ℝ) (x : Fin (0 + M) → ℝ) :
    Basic.holds (EAChain.nil (0 + M))
      (⟨List.ofFn (fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.C (P i)), []⟩ : Basic (0 + M) 0) x
      ↔ x = P := by
  constructor
  · intro hx
    funext i
    have h1 : eaEval (EAChain.nil (0 + M))
        (MvPolynomial.X (Sum.inl i) - MvPolynomial.C (P i)) x = 0 := by
      apply hx.1
      rw [List.mem_ofFn]
      exact ⟨i, rfl⟩
    have h2 : x i - P i = 0 := by simpa [eaEval] using h1
    linarith
  · intro hx
    rw [hx]
    refine ⟨?_, by simp⟩
    intro f hf
    rw [List.mem_ofFn] at hf
    obtain ⟨i, rfl⟩ := hf
    simp [eaEval]

/-- `Fin.natAdd 0 : Fin M → Fin (0 + M)` is surjective (it is the canonical identification). -/
private lemma natAdd_zero_surjective {M : ℕ} :
    Function.Surjective (Fin.natAdd 0 : Fin M → Fin (0 + M)) := by
  intro i
  refine ⟨Fin.cast (Nat.zero_add M) i, ?_⟩
  apply Fin.ext
  simp [Fin.natAdd]

/-- The `(a,l)`-entry of the Jacobian of `x ↦ (x_a - P_a)` w.r.t. the fibre coordinates: the
Kronecker delta `δ_{l,a}`. -/
private lemma entry_eq {M : ℕ} (P : Fin (0 + M) → ℝ) (a l : Fin M) :
    eaEval (EAChain.nil (0 + M))
      (eaD (EAChain.nil (0 + M)) (Fin.natAdd 0 l)
        (MvPolynomial.X (Sum.inl (Fin.natAdd 0 a)) - MvPolynomial.C (P (Fin.natAdd 0 a))))
      P = if l = a then 1 else 0 := by
  simp only [eaD, EAChain.nil, Finset.univ_eq_empty, Finset.sum_empty, add_zero, eaEval,
    map_sub, MvPolynomial.pderiv_C, sub_zero, MvPolynomial.pderiv_X, Pi.single_apply]
  by_cases h : l = a
  · subst h
    simp [map_one]
  · have hc : ¬ (Sum.inl (Fin.natAdd 0 a) = (Sum.inl (Fin.natAdd 0 l) : Fin (0 + M) ⊕ Fin 0)) := by
      intro hh
      exact h (Fin.natAdd_injective M 0 (Sum.inl_injective.eq_iff.mp hh)).symm
    rw [ite_eq_right hc, ite_eq_right h]
    simp [map_zero]

/-- That Jacobian matrix is the identity, hence has rank `M`. -/
private lemma matrix_eq {M : ℕ} (P : Fin (0 + M) → ℝ) :
    (Matrix.of fun (a : Fin M) (l : Fin M) =>
      eaEval (EAChain.nil (0 + M))
        (eaD (EAChain.nil (0 + M)) (Fin.natAdd 0 l)
          (MvPolynomial.X (Sum.inl (Fin.natAdd 0 a)) - MvPolynomial.C (P (Fin.natAdd 0 a))))
        P) = 1 := by
  ext a l
  rw [Matrix.of_apply, entry_eq P a l, Matrix.one_apply]
  by_cases h : l = a
  · subst h; simp
  · have h' : ¬ a = l := fun hh => h hh.symm
    rw [ite_eq_right h, ite_eq_right h']

theorem exists_good_singleton_stratum {M : ℕ} (P : Fin (0 + M) → ℝ)
    (hP : P ∈ WilkiesDesign.E.cubeC (0 + M)) :
    ∃ W : WilkiesDesign.E.Stratum 0 M, W.Good ∧ W.j = M ∧ W.X.set = {P} := by
  let B : Basic (0 + M) 0 :=
    ⟨List.ofFn (fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.C (P i)), []⟩
  let X : SemiPf (0 + M) := ⟨0, EAChain.nil (0 + M), [B]⟩
  let h : Fin M → EAPoly (0 + M) 0 :=
    fun a => MvPolynomial.X (Sum.inl (Fin.natAdd 0 a)) - MvPolynomial.C (P (Fin.natAdd 0 a))
  have hset : X.set = {P} := by
    dsimp only [X, B]
    ext x
    simp only [SemiPf.set, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, B', hB', hBx⟩
      rw [List.mem_singleton] at hB'
      subst hB'
      exact (holds_iff P x).mp hBx
    · intro hx
      rw [hx]
      exact ⟨hP, _, List.mem_singleton.mpr rfl, (holds_iff P P).mpr rfl⟩
  refine ⟨⟨X, M, h⟩, ?_, rfl, hset⟩
  intro z hz
  have hzP : z = P := by
    have h1 : z ∈ ({P} : Set (Fin (0 + M) → ℝ)) := hset ▸ hz
    simpa using h1
  subst z
  refine ⟨?_, ?_, ?_⟩
  · -- the equations vanish at `P`
    intro a
    simp [h, eaEval]
  · -- the Jacobian has rank `M`
    have hm : (Matrix.of fun (a : Fin M) (l : Fin M) =>
        eaEval (X.c) (eaD (X.c) (Fin.natAdd 0 l) (h a)) P).rank = M := by
      have hh : (Matrix.of fun (a : Fin M) (l : Fin M) =>
          eaEval (X.c) (eaD (X.c) (Fin.natAdd 0 l) (h a)) P)
          = (Matrix.of fun (a : Fin M) (l : Fin M) =>
            eaEval (EAChain.nil (0 + M))
              (eaD (EAChain.nil (0 + M)) (Fin.natAdd 0 l)
                (MvPolynomial.X (Sum.inl (Fin.natAdd 0 a)) - MvPolynomial.C (P (Fin.natAdd 0 a))))
              P) := by
        rfl
      rw [hh, matrix_eq P]
      simp
    exact hm
  · -- locally, the zero set of the equations is contained in `X.set`
    refine Filter.Eventually.of_forall (fun z' _ hzero => ?_)
    have hz' : z' = P := by
      funext i
      obtain ⟨a, ha⟩ := natAdd_zero_surjective (M := M) i
      rw [← ha]
      have hh : z' (Fin.natAdd 0 a) - P (Fin.natAdd 0 a) = 0 := by
        simpa [h, eaEval] using hzero a
      linarith
    rw [hset, hz']
    exact Set.mem_singleton P

end Work.CoreStep
