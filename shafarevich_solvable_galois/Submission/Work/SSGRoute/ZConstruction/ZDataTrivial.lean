import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.Reduction
import Submission.Work.SSGRoute.ZConstruction.ZDataGlue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Two elementary reductions for the `z`-data of Schmidt--Wingberg §4

`Work.SSGRoute.HasZData` (`Submission/Work/SSGRoute/ZConstruction/ZDataGlue.lean`) mentions the datum
`y` in **one** clause only: the agreement clause

  `∀ B, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) → ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B →
    z σ = y σ`,

i.e. `z` is tested against `y` only on the decomposition groups of the places *conjugate into `S`*
(`cs(S)`).  Two consequences are recorded here.

* `Work.SSGRoute.hasZData_congr_cs`: the `z`-data of `y` and of `y'` are equivalent as soon as
  `y` and `y'` agree on the decomposition groups of `cs(S)`.  Hence the *only* datum of `y` that the
  `z`-data sees is its restriction to `⋃_{B ∈ cs(S)} (decomp k B ⊓ K.fixingSubgroup)`; in particular
  the problem `z_data_general` may be replaced by the same problem for the projection of `y` onto the
  span of that local data (Schmidt--Wingberg reduce the coefficient module to the `cs(S)`-data).

* `Work.SSGRoute.z_data_general_of_cs_trivial`: if `y` already *vanishes* on those decomposition
  groups, then `z := 0` witnesses the whole `z`-data (the sharpened condition (b) is vacuous because
  `z` is unramified everywhere).  This is the trivial case of `z_data_general`; the genuine content
  of the theorem therefore lies in the places of `cs(S)` that are **split in `K` and prime to `p`**
  (by `hyT`/`hy0` at every other place of `cs(S)` the datum is already zero there), where `y` may be
  non-trivial on the *unramified part* of the local group.
-/

namespace Work.SSGRoute

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
  {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [Normal k K]
  {E : Type} [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]

/-- The `z`-data of `y` depends on `y` only through its values on the decomposition groups of the
places conjugate into `S`: if `y` and `y'` agree there, `z` is a witness for one if and only if it
is a witness for the other. -/
theorem hasZData_congr_cs {S : Finset (ValuationSubring Ω)} {y y' : (Ω ≃ₐ[k] Ω) → E}
    {z : (Ω ≃ₐ[k] Ω) → E}
    (h : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y' σ = y σ)
    (hz : HasZData K Λ S y z) : HasZData K Λ S y' z := by
  obtain ⟨ha, hl, hg, hi, hs, hb⟩ := hz
  exact ⟨ha, hl, fun B hB hc σ hσK hσd => by rw [h B hB hc σ hσK hσd, hg B hB hc σ hσK hσd],
    hi, hs, hb⟩

/-- **The trivial case of the `z`-data.**  If the datum `y` vanishes on the decomposition groups of
all the places conjugate into `S`, then `z := 0` satisfies the whole `z`-data for `y` (all the
clauses except the agreement clause do not mention `y`, and the agreement clause is exactly the
hypothesis; the sharpened condition (b) is vacuous since `z` is unramified everywhere). -/
theorem z_data_general_of_cs_trivial {S : Finset (ValuationSubring Ω)}
    {y : (Ω ≃ₐ[k] Ω) → E}
    (hytriv : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z := by
  refine ⟨fun _ => 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g _ h _; simp
  · exact ⟨⊤, isOpen_univ, fun _ _ _ _ _ => rfl⟩
  · intro B hB hc σ hσK hσd
    exact (hytriv B hB hc σ hσK hσd).symm
  · intro c _ _; rfl
  · intro B _ _ _ σ _ _; rfl
  · intro B _ _ _ htrig
    obtain ⟨σ, hσI, hσK, hσne⟩ := htrig
    exact absurd rfl hσne

end Work.SSGRoute
