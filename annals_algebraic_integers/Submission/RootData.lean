import Mathlib

/-!
# Root enumeration for separable integer polynomials (over ℂ)
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace Submission.RootData

/-- The complexification of `Q`. -/
noncomputable def Qc (Q : Polynomial ℤ) : Polynomial ℂ := Q.map (algebraMap ℤ ℂ)

/-- Full root data of a separable integer polynomial of degree `n ≥ 1`: an
injective enumeration `α` of all `n` complex roots together with the
factorization `Qc Q = C(lc)·∏ᵢ (X − C(α i))`. -/
def RootDataOf (Q : Polynomial ℤ) (n : ℕ) : Prop :=
  ∃ α : Fin n → ℂ,
    Function.Injective α ∧
      Qc Q = Polynomial.C ((Q.leadingCoeff : ℂ)) *
        ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))

/-- The complexification map ℤ → ℂ is injective. -/
lemma algebraMap_int_complex_injective : Function.Injective (algebraMap ℤ ℂ) := by
  exact Int.cast_injective

/-- The complexification of a nonzero polynomial is nonzero. -/
lemma Qc_ne_zero_of_ne_zero {Q : Polynomial ℤ} (hQ0 : Q ≠ 0) : Qc Q ≠ 0 := by
  intro hz
  apply hQ0
  exact (Polynomial.map_eq_zero_iff algebraMap_int_complex_injective).mp hz

/-- The leading coefficient of the complexification is the complexified leading
coefficient. -/
lemma Qc_leadingCoeff {Q : Polynomial ℤ} : (Qc Q).leadingCoeff = (Q.leadingCoeff : ℂ) := by
  unfold Qc
  exact leadingCoeff_map_of_injective algebraMap_int_complex_injective Q

/-- The complexification preserves the degree of a polynomial. -/
lemma Qc_natDegree {Q : Polynomial ℤ} : (Qc Q).natDegree = Q.natDegree := by
  unfold Qc
  exact natDegree_map_eq_of_injective algebraMap_int_complex_injective Q

/-- MAIN RESULT: a separable complexification gives full root data. -/
theorem root_data_of_separable {n : ℕ} (hn : 1 ≤ n) (Q : Polynomial ℤ) (hQ0 : Q ≠ 0)
    (hQn : Q.natDegree = n)
    (hsep : (Qc Q).Separable) : RootDataOf Q n := by
  classical
  have _hn : 1 ≤ n := hn
  have _hQ0 : Q ≠ 0 := hQ0
  let f : Polynomial ℂ := Qc Q
  have hfsep : f.Separable := by simpa [f, Qc] using hsep
  have hsplit : f.Splits := IsAlgClosed.splits f
  have hnod : f.roots.Nodup := nodup_roots hfsep
  have hrootsCard : f.roots.card = n := by
    calc
      f.roots.card = f.natDegree := splits_iff_card_roots.mp hsplit
      _ = Q.natDegree := Qc_natDegree
      _ = n := hQn
  let S : Finset ℂ := f.roots.toFinset
  have hScard : S.card = n := by
    dsimp [S]
    calc
      f.roots.toFinset.card = f.roots.card := Multiset.toFinset_card_of_nodup hnod
      _ = n := hrootsCard
  let e : S ≃ Fin n := Finset.equivFinOfCardEq hScard
  let α : Fin n → ℂ := fun i => (e.symm i : ℂ)
  refine ⟨α, ?_, ?_⟩
  · have hval : Function.Injective (fun x : S => (x : ℂ)) := Subtype.coe_injective
    dsimp [α]
    exact hval.comp (Equiv.injective e.symm)
  · -- factorization
    have hlc : f.leadingCoeff = (Q.leadingCoeff : ℂ) := by
      simpa [f] using (Qc_leadingCoeff (Q := Q))
    calc
      Qc Q = f := rfl
      _ = C f.leadingCoeff * (f.roots.map (fun a => X - C a)).prod := hsplit.eq_prod_roots
      _ = C (Q.leadingCoeff : ℂ) * (f.roots.map (fun a => X - C a)).prod := by rw [hlc]
      _ = C (Q.leadingCoeff : ℂ) * (S.prod (fun a => X - C a)) := by
        congr 1
        dsimp [S]
        change (f.roots.map (fun a : ℂ => X - C a)).prod =
          (f.roots.toFinset.1.map (fun a : ℂ => X - C a)).prod
        rw [show f.roots.toFinset.1 = f.roots by
          rw [Multiset.toFinset]
          exact Multiset.dedup_eq_self.mpr hnod]
      _ = C (Q.leadingCoeff : ℂ) * (∏ x : S, (X - C (x : ℂ))) := by
        congr 1
        simp
        exact (Finset.prod_attach S (fun a : ℂ => X - C a)).symm
      _ = C (Q.leadingCoeff : ℂ) * (∏ i : Fin n, (X - C (α i))) := by
        congr 1
        dsimp [α]
        exact (Equiv.prod_comp (e.symm) (fun x : S => X - C (x : ℂ))).symm

end Submission.RootData
