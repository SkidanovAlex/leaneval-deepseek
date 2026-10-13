import Mathlib
import Submission.Work.DSG4a.FreePres
import Submission.Work.DSG4a.one_mem_map_splitIdeal_of_isUnimodular_tmul
import Submission.Work.DSG4a.LocalGlobal
import Submission.Work.DSG4a.Split

namespace Work.DSG4a

-- `letI` is genuinely needed in the proof below: the chosen algebra structure `ψ.toAlgebra`
-- must be available to instance resolution for the base-change lemma.
set_option linter.style.haveILetI false

universe u

theorem isUnimodular_of_forall_maximal {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M]
    [Module A M] (P : Work.DSG4a.FreePres A M) (e : M)
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ (A' : Type u) (_ : CommRing A') (_ : IsLocalRing A')
      (ψ : A →+* A'), ψ.Flat ∧ (IsLocalRing.maximalIdeal A').comap ψ = 𝔪 ∧
      (letI : Algebra A A' := ψ.toAlgebra
       Module.IsUnimodular A' (TensorProduct.mk A A' M (1 : A') e))) :
    Module.IsUnimodular A e := by
  -- Unimodularity of `e` is the statement `1 ∈ splitIdeal A e`, so it suffices to run the
  -- ideal-theoretic local-to-global argument on the splitting ideal.
  rw [← one_mem_splitIdeal_iff]
  refine one_mem_ideal_of_forall_maximal (splitIdeal A e) ?_
  intro 𝔪 h𝔪
  -- For each maximal `𝔪` choose the flat local `A`-algebra `A'` supplied by the hypothesis.
  obtain ⟨A', _, _, ψ, hflat, hcomap, huni⟩ := h 𝔪 h𝔪
  refine ⟨A', _, _, ψ, hflat, hcomap, ?_⟩
  -- Read `A'` as an `A`-algebra through `ψ`; then `algebraMap A A' = ψ` definitionally and
  -- `ψ.Flat` unfolds to `Module.Flat A A'`.
  letI : Algebra A A' := ψ.toAlgebra
  have key := one_mem_map_splitIdeal_of_isUnimodular_tmul (A := A) (A' := A') P e hflat huni
  rwa [show (algebraMap A A' : A →+* A') = ψ from rfl] at key

end Work.DSG4a
