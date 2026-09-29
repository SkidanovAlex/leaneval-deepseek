import Mathlib
import Submission.Work.Holonomy3.siegelDefs

namespace Work.Holonomy3

open Submission.CDTPlan Submission.CDT.Discrepancy
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The coefficient of `mkQ y i` at the exponent `Finsupp.equivFunOnFinite.symm k.1` attached to a
low-discrepancy exponent vector `k ∈ lowSet d D ε` is the corresponding entry `y (i,k)`. -/
lemma coeff_mkQ_symm {m d : ℕ} {D : ℕ} {ε : ℝ} (y : ColIdx d D ε m → ℤ)
    {i : Fin d → Fin m} (hi : i ∈ balSet d m) (k : lowSet d D ε) :
    ((mkQ y i).coeff (Finsupp.equivFunOnFinite.symm k.1) : ℚ)
      = (y ⟨(i, k.1), hi, k.2⟩ : ℚ) := by
  rw [coeff_mkQ y hi, dif_pos (by rw [Finsupp.equivFunOnFinite.apply_symm_apply]; exact k.2)]
  exact congrArg (fun p => (y p : ℚ)) (Subtype.ext (by simp))

/-- **Support of the auxiliary template.** A sum over the support of `mkQ y i` of the coefficient
times a weight `B` of the exponent vector equals the corresponding sum over the low-discrepancy
exponents `k ∈ P_ε^d ∩ [0,D]^d`, pairing each `k` with its entry `y (i,k)` in the integer vector.
(Entries where `y` vanishes contribute `0` on both sides, which is why the support can be smaller
than `lowSet d D ε`.) -/
theorem sum_support_mkQ {m d : ℕ} {D : ℕ} {ε : ℝ} (y : Work.Holonomy3.ColIdx d D ε m → ℤ)
    (i : Fin d → Fin m) (hi : i ∈ Work.Holonomy3.balSet d m) (B : (Fin d → ℕ) → ℚ) :
    ∑ k ∈ (Work.Holonomy3.mkQ y i).support,
        ((Work.Holonomy3.mkQ y i).coeff k : ℚ) * B (Finsupp.equivFunOnFinite k) =
      ∑ k ∈ (Work.Holonomy3.lowSet d D ε).attach,
        (y ⟨(i, k.1), hi, k.2⟩ : ℚ) * B k.1 := by
  classical
  have hsub : (mkQ y i).support ⊆ (lowSet d D ε).attach.image
      (fun x : {k // k ∈ lowSet d D ε} => Finsupp.equivFunOnFinite.symm x.1) := by
    intro k hk
    refine Finset.mem_image.mpr ⟨⟨Finsupp.equivFunOnFinite k, supported_mkQ y i k hk⟩, ?_, ?_⟩
    · exact Finset.mem_attach _ _
    · exact Finsupp.equivFunOnFinite.symm_apply_apply k
  have hinj : Set.InjOn (fun x : {k // k ∈ lowSet d D ε} => Finsupp.equivFunOnFinite.symm x.1)
      ↑(lowSet d D ε).attach := fun x _ y _ hxy =>
    Subtype.ext (Finsupp.equivFunOnFinite.symm.injective hxy)
  calc ∑ k ∈ (mkQ y i).support,
        ((mkQ y i).coeff k : ℚ) * B (Finsupp.equivFunOnFinite k)
      = ∑ k ∈ (lowSet d D ε).attach.image
          (fun x : {k // k ∈ lowSet d D ε} => Finsupp.equivFunOnFinite.symm x.1),
          ((mkQ y i).coeff k : ℚ) * B (Finsupp.equivFunOnFinite k) :=
        Finset.sum_subset hsub (fun k _ hk => by
          have hk0 : (mkQ y i).coeff k = 0 := by
            by_contra hc
            exact hk (MvPolynomial.mem_support_iff.mpr hc)
          rw [hk0, zero_mul])
    _ = ∑ x ∈ (lowSet d D ε).attach,
          ((mkQ y i).coeff (Finsupp.equivFunOnFinite.symm x.1) : ℚ)
            * B (Finsupp.equivFunOnFinite (Finsupp.equivFunOnFinite.symm x.1)) :=
        Finset.sum_image hinj
    _ = ∑ k ∈ (lowSet d D ε).attach, (y ⟨(i, k.1), hi, k.2⟩ : ℚ) * B k.1 := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [coeff_mkQ_symm y hi x, Finsupp.equivFunOnFinite.apply_symm_apply]

end Work.Holonomy3
