import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic

namespace Commons.Algebra.MvPolynomial

theorem card_support_block_le {m N : ℕ} (P : MvPolynomial (Fin m × Fin N) ℂ) (d : Fin m → ℕ)
    (hdeg : ∀ J ∈ P.support, ∀ h : Fin m, ∑ k : Fin N, J (h, k) ≤ d h) :
    P.support.card ≤ ∏ h : Fin m, (d h + 1) ^ N := by
  classical
  have hcard : (Fintype.piFinset (fun h : Fin m =>
        Fintype.piFinset (fun _ : Fin N => Finset.range (d h + 1)))).card
      = ∏ h : Fin m, (d h + 1) ^ N := by
    rw [Fintype.card_piFinset]
    refine Finset.prod_congr rfl (fun h _ => ?_)
    rw [Fintype.card_piFinset]
    simp [Finset.prod_const, Fintype.card_fin]
  have hsub : P.support.image (fun J : Fin m × Fin N →₀ ℕ => fun h k => J (h, k)) ⊆
      Fintype.piFinset (fun h : Fin m => Fintype.piFinset (fun _ : Fin N => Finset.range (d h + 1))) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨J, hJ, rfl⟩ := hx
    rw [Fintype.mem_piFinset]
    intro h
    rw [Fintype.mem_piFinset]
    intro k
    rw [Finset.mem_range]
    have hle : J (h, k) ≤ ∑ k : Fin N, J (h, k) :=
      Finset.single_le_sum (f := fun k => J (h, k)) (fun i _ => Nat.zero_le _) (Finset.mem_univ k)
    exact Nat.lt_succ_of_le (le_trans hle (hdeg J hJ h))
  have hinj : Function.Injective (fun J : Fin m × Fin N →₀ ℕ => fun h k => J (h, k)) := by
    intro J₁ J₂ h
    ext x
    have h2 := congr_fun (congr_fun h x.1) x.2
    simpa [Prod.mk.eta] using h2
  calc P.support.card
      = (P.support.image (fun J : Fin m × Fin N →₀ ℕ => fun h k => J (h, k))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (Fintype.piFinset (fun h : Fin m =>
          Fintype.piFinset (fun _ : Fin N => Finset.range (d h + 1)))).card :=
        Finset.card_le_card hsub
    _ = ∏ h : Fin m, (d h + 1) ^ N := hcard

end Commons.Algebra.MvPolynomial