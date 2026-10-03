import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs

namespace Work.ORLyndon.CLDirect

/-- Splitting `f` along the Cohen--Lyndon section, and conjugating. Sketch: `q := QuotientGroup.mk f`, `m := ⟨f * (D.s q)⁻¹, _⟩`; membership from `D.mk_s q` via `QuotientGroup.eq` and normality of `M` (`f * ((D.s q)⁻¹ * f) * f⁻¹ = f * (D.s q)⁻¹`). Second conjunct: push the coercion (`Subgroup.coe_mul`, `coe_pow`, `coe_inv`), rewrite with `D.e_of`, conclude with `conj_pow`/`group`. -/
theorem conj_pow_eq {X : Type*} {u : FreeGroup X} (D : Work.ORLyndon.CLDirect.CLData u)
    (f : FreeGroup X) (l : ℕ) :
    ∃ m : ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X))),
      (m : FreeGroup X) * D.s (QuotientGroup.mk f) = f ∧
      f * u ^ l * f⁻¹ =
        ((m * (D.e (FreeGroup.of (QuotientGroup.mk f))) ^ l * m⁻¹ :
          ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) : FreeGroup X) := by
  -- Write `q` for the coset of `f` and `m = f * s q⁻¹`.
  set q := QuotientGroup.mk f with hq
  -- `m` lies in `M = ⟪u⟫`: from `mk (s q) = q = mk f` we get `(s q)⁻¹ * f ∈ M`,
  -- and conjugating by `f` (normality) turns it into `f * (s q)⁻¹`.
  have hmem : f * (D.s q)⁻¹ ∈ Subgroup.normalClosure ({u} : Set (FreeGroup X)) := by
    have h2 : (D.s q)⁻¹ * f ∈ Subgroup.normalClosure ({u} : Set (FreeGroup X)) :=
      QuotientGroup.eq.mp (by rw [D.mk_s q, hq])
    have h3 := Subgroup.normalClosure_normal.conj_mem ((D.s q)⁻¹ * f) h2 f
    convert h3 using 1
    group
  refine ⟨⟨f * (D.s q)⁻¹, hmem⟩, ?_, ?_⟩
  · -- `m * s q = f` by cancellation.
    show f * (D.s q)⁻¹ * D.s q = f
    group
  · -- Push the subgroup coercion, use `D.e_of` on the basis element, then `conj_pow`.
    have hcoe : ((⟨f * (D.s q)⁻¹, hmem⟩ * (D.e (FreeGroup.of q)) ^ l *
        ⟨f * (D.s q)⁻¹, hmem⟩⁻¹ :
        ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) : FreeGroup X) = f * u ^ l * f⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, D.e_of q, conj_pow]
      group
    exact hcoe.symm

end Work.ORLyndon.CLDirect
