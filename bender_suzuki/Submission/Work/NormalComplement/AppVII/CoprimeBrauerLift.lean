import Mathlib
import Submission.Work.CharCore.Main
import Submission.Work.Hering.AppVII.brauer_setup
import Submission.Work.Hering.AppVII.brauer_lift_aux
import Submission.Work.NormalComplement.AppVII.ToKProps
import Submission.Work.NormalComplement.AppVII.TildeEProps
import Submission.Work.NormalComplement.AppVII.LiftExistsUniqueToK
import Submission.Work.NormalComplement.AppVII.BrauerSumZero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Coprime Brauer lifting (Huppert V.12.9) in the form used by Peterfalvi's Appendix VII

Let `A` be a finite group, `r` a prime with `r ∤ |A|`, `k = F̄_r` and `V` a simple `k[A]`-module.
The "Brauer character" of `V` — obtained by lifting the eigenvalues of every `ρ a` (roots of
unity of order dividing `|A|`) to `ℂ` — is an irreducible *ordinary* character `χ` of `A` with
the same kernel and the same restriction behaviour: for a subgroup `C ≤ A`, the multiplicity of
the trivial character of `C` in `Res_C χ` equals `dim_k V^C`.

Here this is assembled from the four ingredients (all in this directory):
`TildeEProps` / `LiftSumTildeE` (the `tildeE`-identities), `ToKProps` (the reduced central
idempotents `toK χ` are central, idempotent, orthogonal, sum to `1`, and kill the elements in the
kernel of `χ`), `LiftExistsUniqueToK` (each simple module lies in exactly one block of `k[A]`)
and `BrauerSumZero` (the restriction to a subgroup with `V^C = 0` misses the trivial character).

The statement records the two consequences needed for `SimpleFixedPoint`.
-/

noncomputable section

open Classical

namespace Work.NormalComplement.AppVII

/-- **Coprime Brauer lifting**, in the two-consequence form needed for Appendix VII. -/
theorem coprime_brauer_lift {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A))
    {V : Type*} [AddCommGroup V] [Module (Work.Hering.AppVII.BrauerField r) V]
    [Module.Finite (Work.Hering.AppVII.BrauerField r) V]
    (ρ : Representation (Work.Hering.AppVII.BrauerField r) A V) [ρ.IsIrreducible]
    (P Z : Subgroup A) [Fintype ↥P]
    (hP : ∀ v : V, (∀ c ∈ P, ρ c v = v) → v = 0)
    (hZ : ¬ Z ≤ ρ.ker) :
    ∃ χ : A → ℂ, χ ∈ Work.CharCore.Irr A ∧ (∃ z ∈ Z, χ z ≠ χ 1) ∧
      (∑ s : ↥P, χ (s : A)) = 0 := by
  have hprops := ToKProps hcop (TildeEProps (A := A))
  obtain ⟨χ₀, hblock, -⟩ := LiftExistsUniqueToK hcop ρ (inferInstance)
  refine ⟨χ₀.1, χ₀.2, ?_, ?_⟩
  · -- the `Z`-part: a non-trivial element of `Z` is not in the kernel of `ρ`, hence not in that
    -- of `χ` either (the kernel of `χ` acts trivially on `V`)
    obtain ⟨z, hzZ, hzker⟩ : ∃ z ∈ Z, ρ z ≠ 1 := by
      by_contra h
      push_neg at h
      exact hZ fun z hz => by rw [MonoidHom.mem_ker]; exact h z hz
    refine ⟨z, hzZ, fun hχz => hzker ?_⟩
    have hkey := hprops.2.2.2.2 χ₀.1 χ₀.2 z hχz
    have h1 := congrArg (fun e => ρ.asAlgebraHom e) hkey
    rw [map_mul, hblock, Representation.asAlgebraHom_single_one, one_mul] at h1
    exact h1
  · -- the `P`-part: no `P`-fixed vector means the trivial character of `P` does not occur
    exact BrauerSumZero hcop hprops ρ (inferInstance) P hP χ₀.1 χ₀.2 hblock

end Work.NormalComplement.AppVII
