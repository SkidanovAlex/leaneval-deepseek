import ChallengeDeps
import Submission.Commons.LorentzianPolynomials.L_subset_closure
import Submission.Commons.LorentzianPolynomials.closure_subset_L

open LorentzianPolynomials
open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
set_option autoImplicit false

namespace Submission.Lorentzian

noncomputable section

-- membership bridges
lemma Ŀ_mem_iff : ∀ (n : ℕ) (d : ℕ) (f : LorentzianPolynomials.H n d),
    f ∈ LorentzianPolynomials.Ŀ n d ↔ (f : Commons.LorentzianPolynomials.H n d) ∈ Commons.LorentzianPolynomials.Ŀ n d
  | n, 0 => by intro f; change (f ∈ LorentzianPolynomials.P n 0) ↔ (f : Commons.LorentzianPolynomials.H n 0) ∈ Commons.LorentzianPolynomials.P n 0; rfl
  | n, 1 => by intro f; rfl
  | n, 2 => by intro f; rfl
  | n, d+3 => by
      intro f
      change (((∀ m : Fin n →₀ ℕ, weight 1 m = d+3 → 0 < f.1.coeff m) ∧
          ∀ i : Fin n, ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ Ŀ n (d+2)) ↔
        ((∀ m : Fin n →₀ ℕ, weight 1 m = d+3 → 0 < (f : Commons.LorentzianPolynomials.H n (d+3)).1.coeff m) ∧
          ∀ i : Fin n, (⟨f.1.pderiv i, f.2.pderiv⟩ : Commons.LorentzianPolynomials.H n (d+2)) ∈ Commons.LorentzianPolynomials.Ŀ n (d+2)))
      constructor
      · intro h
        exact ⟨h.1, fun i => by
          have heq := Ŀ_mem_iff n (d+2) ⟨f.1.pderiv i, f.2.pderiv⟩
          exact heq.mp (h.2 i)⟩
      · intro h
        exact ⟨h.1, fun i => by
          have heq := Ŀ_mem_iff n (d+2) ⟨f.1.pderiv i, f.2.pderiv⟩
          exact heq.mpr (h.2 i)⟩

lemma L_mem_iff : ∀ (n : ℕ) (d : ℕ) (f : LorentzianPolynomials.H n d),
    f ∈ LorentzianPolynomials.L n d ↔ (f : Commons.LorentzianPolynomials.H n d) ∈ Commons.LorentzianPolynomials.L n d
  | n, 0 => by intro f; rfl
  | n, 1 => by intro f; rfl
  | n, 2 => by intro f; rfl
  | n, d+3 => by
      intro f
      have hul : f ∈ LorentzianPolynomials.L n (d+3) ↔
          ((LorentzianPolynomials.IsMConvex (f.1.support : Set (Fin n →₀ ℕ)) ∧
              ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m) ∧
            ∀ i : Fin n, ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ LorentzianPolynomials.L n (d+2)) := by rfl
      have hur : (f : Commons.LorentzianPolynomials.H n (d+3)) ∈ Commons.LorentzianPolynomials.L n (d+3) ↔
          ((Commons.LorentzianPolynomials.IsMConvex (f.1.support : Set (Fin n →₀ ℕ)) ∧
              ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m) ∧
            ∀ i : Fin n, (⟨f.1.pderiv i, f.2.pderiv⟩ : Commons.LorentzianPolynomials.H n (d+2)) ∈ Commons.LorentzianPolynomials.L n (d+2)) := by rfl
      rw [hul, hur]
      constructor
      · intro h
        exact ⟨h.1, fun i => by
          have heq := L_mem_iff n (d+2) ⟨f.1.pderiv i, f.2.pderiv⟩
          exact heq.mp (h.2 i)⟩
      · intro h
        exact ⟨h.1, fun i => by
          have heq := L_mem_iff n (d+2) ⟨f.1.pderiv i, f.2.pderiv⟩
          exact heq.mpr (h.2 i)⟩

lemma hH (n d : ℕ) : LorentzianPolynomials.H n d = Commons.LorentzianPolynomials.H n d := by rfl

lemma Ŀ_eq_cast (n d : ℕ) :
    LorentzianPolynomials.Ŀ n d = (hH n d).symm ▸ (Commons.LorentzianPolynomials.Ŀ n d : Set (Commons.LorentzianPolynomials.H n d)) := by
  ext f
  change f ∈ LorentzianPolynomials.Ŀ n d ↔
    (f : Commons.LorentzianPolynomials.H n d) ∈ Commons.LorentzianPolynomials.Ŀ n d
  exact Ŀ_mem_iff n d f

lemma L_eq_cast (n d : ℕ) :
    LorentzianPolynomials.L n d = (hH n d).symm ▸ (Commons.LorentzianPolynomials.L n d : Set (Commons.LorentzianPolynomials.H n d)) := by
  ext f
  change f ∈ LorentzianPolynomials.L n d ↔
    (f : Commons.LorentzianPolynomials.H n d) ∈ Commons.LorentzianPolynomials.L n d
  exact L_mem_iff n d f

lemma mem_closure_cast_iff (n d : ℕ) (f : LorentzianPolynomials.H n d) :
    (f ∈ closure ((hH n d).symm ▸ (Commons.LorentzianPolynomials.Ŀ n d : Set (Commons.LorentzianPolynomials.H n d)))) ↔
      (f : Commons.LorentzianPolynomials.H n d) ∈ closure (Commons.LorentzianPolynomials.Ŀ n d) := by
  rfl

lemma mem_L_cast_iff (n d : ℕ) (f : LorentzianPolynomials.H n d) :
    (f ∈ ((hH n d).symm ▸ (Commons.LorentzianPolynomials.L n d : Set (Commons.LorentzianPolynomials.H n d)))) ↔
      (f : Commons.LorentzianPolynomials.H n d) ∈ Commons.LorentzianPolynomials.L n d := by
  rfl

theorem theorem_2_25 (n d : ℕ) (hn : 0 < n) : closure (Ŀ n d) = L n d := by
  classical
  have hclĿ : closure (Ŀ n d) =
      closure ((hH n d).symm ▸ (Commons.LorentzianPolynomials.Ŀ n d : Set (Commons.LorentzianPolynomials.H n d))) := by
    rw [Ŀ_eq_cast]
  rw [hclĿ, L_eq_cast]
  apply le_antisymm
  · intro f hf
    have hfC : (f : Commons.LorentzianPolynomials.H n d) ∈
        closure (Commons.LorentzianPolynomials.Ŀ n d) := (mem_closure_cast_iff n d f).mp hf
    have hfL : (f : Commons.LorentzianPolynomials.H n d) ∈ Commons.LorentzianPolynomials.L n d :=
      Commons.LorentzianPolynomials.closure_subset_L n d hn hfC
    exact (mem_L_cast_iff n d f).mpr hfL
  · intro f hf
    have hfL : (f : Commons.LorentzianPolynomials.H n d) ∈ Commons.LorentzianPolynomials.L n d :=
      (mem_L_cast_iff n d f).mp hf
    have hfC : (f : Commons.LorentzianPolynomials.H n d) ∈
        closure (Commons.LorentzianPolynomials.Ŀ n d) :=
      Commons.LorentzianPolynomials.L_subset_closure n d hn hfL
    exact (mem_closure_cast_iff n d f).mpr hfC

end

end Submission.Lorentzian
