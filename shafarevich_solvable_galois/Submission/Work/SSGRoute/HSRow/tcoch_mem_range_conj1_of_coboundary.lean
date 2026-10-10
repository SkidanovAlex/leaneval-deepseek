import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.HSConj
import Submission.Work.SSGRoute.HSRow.TransgressionDefs
import Submission.Work.SSGRoute.HSRow.sub_primitive_mem_lcCocycles
import Submission.Work.SSGRoute.HSRow.tcoch_sub_conj_coboundary_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.HSRow

open scoped Pointwise
open Classical

set_option linter.unusedVariables false

/-- **(Q1) The transgression vanishes on coboundaries** (normalised case, `σ ∈ D`).  If the
locally constant `2`-cocycle `c` on `D` is a coboundary on `D` (`c = d¹E` on `D × D`, with
`σ ∈ D` so that the values `c σ ·`, `c · σ⁻¹` are covered) and `c 1 1 = 0`, then for *any* locally
constant primitive `β` of `c|_{I × I}` the class of `tcoch I σ c β` lies in `range (conj₁ - 1)`.
Indeed `φ := β - E|_I ∈ Z¹(I,M)`, `tcoch I σ c β - tcoch I σ c E|_I = conj₁ φ - φ`, and
`tcoch I σ c E|_I = d⁰ (E σ - E 1)` with `E 1 = c 1 1 = 0`. -/
theorem tcoch_mem_range_conj1_of_coboundary
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (D I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hσ : σ ∈ D) (hI : I ≤ D)
    (hnorm1 : ∀ n ∈ I, σ * n * σ⁻¹ ∈ I) (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hc : c ∈ Work.SSGRoute.lcCocycles2 p k Ω K M D)
    (hcob : c ∈ Work.SSGRoute.coboundaries2 p k Ω K M D)
    (hc11 : c 1 1 = 0)
    (β : (Ω ≃ₐ[k] Ω) → M) (hβlc : SSGRoute.IsLocConstOn I β)
    (hβ : ∀ n ∈ I, ∀ m ∈ I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m)
    (htcoch : tcoch p k Ω K M I σ c β ∈ Work.SSGRoute.lcCocycles p k Ω K M I) :
    Work.SSGRoute.toClass p k Ω K M I (tcoch p k Ω K M I σ c β) ∈
      LinearMap.range (Work.SSGRoute.conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id) := by
  classical
  -- `c` is the coboundary on `D` of a locally constant `1`-cochain `b`.
  obtain ⟨b, hblc, hbcob⟩ := hcob
  -- The difference `φ = β - b` of the two primitives of `c|_I`: a locally constant `1`-cocycle.
  let Φ : (Ω ≃ₐ[k] Ω) → M := fun x => β x - b x
  have hΦmem : Φ ∈ Work.SSGRoute.lcCocycles p k Ω K M I :=
    sub_primitive_mem_lcCocycles p k Ω K M D I hI c b β hbcob hblc hβlc hβ
  -- The `σ`-conjugate of `Φ`, again a locally constant `1`-cocycle on `I`.
  have hGmem : Work.SSGRoute.h1locConjShift p k Ω K M σ Φ ∈ Work.SSGRoute.lcCocycles p k Ω K M I :=
    Work.SSGRoute.h1locConjShift_mem_lcCocycles p k Ω K M I σ hnorm2 hΦmem
  have hDmem : (Work.SSGRoute.h1locConjShift p k Ω K M σ Φ - Φ)
      ∈ Work.SSGRoute.lcCocycles p k Ω K M I := Submodule.sub_mem _ hGmem hΦmem
  -- `tcoch I σ c β - (conj₁ Φ - Φ)` is the coboundary of `b σ` on `I` (the `β`-terms cancel).
  have hcobI : (tcoch p k Ω K M I σ c β - (Work.SSGRoute.h1locConjShift p k Ω K M σ Φ - Φ))
      ∈ Work.SSGRoute.coboundaries p k Ω K M I := by
    refine ⟨b σ, fun n hn => ?_⟩
    have hp : (SSGRoute.res k K σ • β (σ⁻¹ * n * σ) - c σ (σ⁻¹ * n * σ)
          + SSGRoute.res k K n • c σ σ⁻¹ - c (n * σ) σ⁻¹ + c 1 1 - β n)
        - (SSGRoute.res k K σ • (β (σ⁻¹ * n * σ) - b (σ⁻¹ * n * σ)) - (β n - b n))
      = SSGRoute.res k K n • b σ - b σ :=
      tcoch_sub_conj_coboundary_general (SSGRoute.res k K) D I σ hσ hI hnorm2 c b β hbcob hc11 n hn
    -- unfold `tcoch`, `tprim` and the conjugation shift to reach the algebraic identity `hp`
    have hgoal : (tcoch p k Ω K M I σ c β
        - (Work.SSGRoute.h1locConjShift p k Ω K M σ Φ - Φ)) n
        = (SSGRoute.res k K σ • β (σ⁻¹ * n * σ) - c σ (σ⁻¹ * n * σ)
            + SSGRoute.res k K n • c σ σ⁻¹ - c (n * σ) σ⁻¹ + c 1 1 - β n)
          - (SSGRoute.res k K σ • (β (σ⁻¹ * n * σ) - b (σ⁻¹ * n * σ)) - (β n - b n)) := by
      simp only [Pi.sub_apply]
      rw [tcoch_apply_of_mem p k Ω K M I σ c β hn, tprim_apply]
      rfl
    rw [hgoal]
    exact hp
  -- Hence `tcoch I σ c β` and `conj₁ Φ - Φ` have the same class.
  have hdiff : Work.SSGRoute.toClass p k Ω K M I (tcoch p k Ω K M I σ c β)
      = Work.SSGRoute.toClass p k Ω K M I (Work.SSGRoute.h1locConjShift p k Ω K M σ Φ - Φ) := by
    rw [Work.SSGRoute.toClass, dif_pos htcoch, Work.SSGRoute.toClass,
      dif_pos hDmem, Submodule.mkQ_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq _).mpr (by
      rw [Submodule.mem_comap]
      exact hcobI)
  -- and split the class of that difference.
  have hadd : Work.SSGRoute.toClass p k Ω K M I (Work.SSGRoute.h1locConjShift p k Ω K M σ Φ)
      = Work.SSGRoute.toClass p k Ω K M I (Work.SSGRoute.h1locConjShift p k Ω K M σ Φ - Φ)
        + Work.SSGRoute.toClass p k Ω K M I Φ := by
    rw [← Work.SSGRoute.toClass_add p k Ω K M I hDmem hΦmem]
    congr 1
    ext n
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  -- `conj₁` acts on classes by the conjugation shift.
  have hconj : (Work.SSGRoute.conj1 p k Ω K M I σ hnorm1 hnorm2)
      (Work.SSGRoute.toClass p k Ω K M I Φ)
      = Work.SSGRoute.toClass p k Ω K M I (Work.SSGRoute.h1locConjShift p k Ω K M σ Φ) := by
    rw [Work.SSGRoute.conj1_spec p k Ω K M I σ hnorm1 hnorm2 Φ hΦmem]
    rfl
  refine LinearMap.mem_range.mpr ⟨Work.SSGRoute.toClass p k Ω K M I Φ, ?_⟩
  rw [LinearMap.sub_apply, LinearMap.id_apply, hconj, hadd, hdiff]
  abel

end Work.SSGRoute.HSRow
