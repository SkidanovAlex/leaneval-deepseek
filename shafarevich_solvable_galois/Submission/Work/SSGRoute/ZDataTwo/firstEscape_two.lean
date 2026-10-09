import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.ZDataTwo.mu2EscapeRealisationH
import Submission.Work.SSGRoute.ZDataTwo.mu2EscapeRealisationHKfresh
import Submission.Work.SSGRoute.H9.swHistKExists_proved
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The first escape step of the `p = 2` §4 recursion (Schmidt–Wingberg, Stage 1)

This is the *first stage* of the recursion by which Schmidt–Wingberg's §4 constructs the class `z` of
`Work.SSGRoute.shafarevich_z_data_two_kummerCore` in the exceptional case `p = 2`: apply the proved
`p = 2` escape oracle `Work.SSGRoute.ZDataTwo.mu2EscapeRealisationH` to the datum `y` itself, on the
place set `T₀` of one representative per `G_K`-class of the places of `cs(S)`.

The oracle needs

* the place set `T₀` to be finite, pairwise non-`G_K`-conjugate and to cover the places over `2` and
  the places ramified in `Λ` up to `G_K`-conjugacy (`hSram`), and
* the datum `g + h A` at the blocks of `T₀` to kill the inertia there (`hyT`) and to be compatible
  outside (`hgram`, which is `hyS`), and to kill the involutions (`hyinf`).

Its conclusion is exactly what is recorded below: a class `b₁ ∈ Kˣ` and a new place `Q₁`, finite and
completely split in `Λ`, outside the `G_K`-classes of `T₀`, such that `χ_{b₁}` agrees with `y` on the
local groups of the `cs(S)`-blocks, kills the involutions of `G_K`, and kills the inertia at every
finite place outside `cs(S)` that is not `G_K`-conjugate to `Q₁`.

The two difficult technical steps of the proof are the *representative set* `T = krep K (kleadReps K S)`
(`Work.SSGRoute.H9.krep`, which is pairwise non-`G_K`-conjugate: `kleadReps` alone is not, because a
place of `cs(S)` may well have a nontrivial decomposition group in `Gal(K|k)`), and the transport of
the oracle's agreement clause from the `T`-blocks to all the `k`-conjugates of `S`
(`Work.SSGRoute.ZDataMup.clause_one_of_covering`, which needs `Work.SSGRoute.ZDataMup.kleadReps_covers`
to turn `k`-conjugacy into `G_K`-conjugacy). -/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute

set_option linter.unusedVariables false

/-- **The global Kummer cochain of `b` is invariant under `G_K`-conjugation.**  Both spellings of the
cocycle are additive on `G_K` and `ZMod 2` has characteristic `2`, so `χ_b(μσμ⁻¹) = χ_b σ`. -/
lemma nodeKummerCochar_conj_two (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (b : (↥K)ˣ)
    {μ : Ω ≃ₐ[k] Ω} (hμ : μ ∈ K.fixingSubgroup)
    {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) :
    nodeKummerCochar K ζ hζK hζ b (μ * σ * μ⁻¹) = nodeKummerCochar K ζ hζK hζ b σ := by
  have hadd := nodeKummerCochar_add K ζ hζK hζ b
  have hμi : μ⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hμ
  have h1 : nodeKummerCochar K ζ hζK hζ b (μ * σ * μ⁻¹)
      = nodeKummerCochar K ζ hζK hζ b μ +
        (nodeKummerCochar K ζ hζK hζ b σ + nodeKummerCochar K ζ hζK hζ b μ⁻¹) := by
    rw [mul_assoc, hadd μ hμ (σ * μ⁻¹) (K.fixingSubgroup.mul_mem hσ hμi),
      hadd σ hσ μ⁻¹ hμi]
  have hμinv : nodeKummerCochar K ζ hζK hζ b μ +
      nodeKummerCochar K ζ hζK hζ b μ⁻¹ = 0 := by
    have h0 : nodeKummerCochar K ζ hζK hζ b 1 = 0 := by
      have h2 := hadd 1 K.fixingSubgroup.one_mem 1 K.fixingSubgroup.one_mem
      rw [one_mul] at h2
      exact add_left_cancel (by rw [add_zero]; exact h2.symm)
    have h := hadd μ hμ μ⁻¹ hμi
    rw [mul_inv_cancel, h0] at h
    exact h.symm
  rw [h1]
  have hneg : nodeKummerCochar K ζ hζK hζ b μ =
      - nodeKummerCochar K ζ hζK hζ b μ⁻¹ :=
    eq_neg_of_add_eq_zero_left hμinv
  rw [hneg]
  ring

/-- **The first escape step of the `p = 2` §4 recursion.**  There are `b ∈ Kˣ` and a finite place `Q`
of `Ω` over `k`, completely split in `Λ`, outside the `G_K`-classes of the places of `S`, such that
`χ_b` agrees with `y` on the local groups of all the places of `cs(S)`, kills the involutions of
`G_K`, and kills the inertia of every finite place outside `cs(S)` that is not `G_K`-conjugate to
`Q`. -/
theorem firstEscape_two (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ (b : (↥K)ˣ) (Q : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k Λ Q ∧
      (∀ A ∈ S, ¬ Work.SSGRoute.gesKConj K A Q) ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A Q) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          nodeKummerCochar K ζ hζK hζ b σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → nodeKummerCochar K ζ hζK hζ b c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        (¬ Work.SSGRoute.gesKConj K Q B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          nodeKummerCochar K ζ hζK hζ b σ = 0) := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  set T : Finset (ValuationSubring Ω) :=
    Work.SSGRoute.H9.krep K (Work.SSGRoute.ZDataMup.kleadReps K S) with hTdef
  -- ## the oracle hypotheses for `T = krep K (kleadReps K S)`, `g = y`, `h = 0`
  have hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B :=
    fun A hA B hB h => Work.SSGRoute.H9.krep_disj K _ A hA B hB h
  have hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (2 : Ω) < 1 ∨
        ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ Λ.fixingSubgroup) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B := by
    intro B hB hcond
    have hram : SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1 := by
      rcases hcond with h | ⟨σ, -, hσI, hσΛ⟩
      · exact Or.inr h
      · exact Or.inl ⟨σ, hσI, hσΛ⟩
    obtain ⟨A₀, hA₀, hA₀B⟩ := hSram B hB hram
    obtain ⟨A', hA', hA'B⟩ := Work.SSGRoute.ZDataMup.kleadReps_covers K S hA₀ hA₀B
    obtain ⟨A'', hA'', hA''A'⟩ := Work.SSGRoute.H9.krep_covers K _ A' hA'
    exact ⟨A'', hA'', Work.SSGRoute.H9.swGesKConj_trans hA''A' hA'B⟩
  have hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A := by
    intro A hA
    obtain ⟨A', hA', hA'A⟩ := Work.SSGRoute.H9.krep_mem_classes K _ A hA
    obtain ⟨τ, hτK, hτA⟩ := hA'A
    have hA'fin : SSGRoute.IsFinPlace k A' := by
      obtain ⟨A₀, hA₀, hA₀A'⟩ :=
        Work.SSGRoute.ZDataMup.kleadReps_mem_conjPlace (p := 2) K hA'
      obtain ⟨ρ, hρ⟩ := hA₀A'
      rw [← hρ]
      exact (SSGRoute.isFinPlace_smul_iff A₀ ρ).mpr (hSfin A₀ hA₀)
    rw [← hτA] at hA'fin
    exact (SSGRoute.isFinPlace_smul_iff A τ).mp hA'fin
  -- every element of `T` is `k`-conjugate to an element of `S`
  have hTS : ∀ A ∈ T, ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A := by
    intro A hA
    obtain ⟨A', hA', hA'A⟩ := Work.SSGRoute.H9.krep_mem_classes K _ A hA
    obtain ⟨A₀, hA₀, hA₀A'⟩ :=
      Work.SSGRoute.ZDataMup.kleadReps_mem_conjPlace (p := 2) K hA'
    obtain ⟨τ, hτK, hτA⟩ := hA'A
    obtain ⟨ρ, hρ⟩ := hA₀A'
    exact ⟨A₀, hA₀, τ⁻¹ * ρ, by rw [mul_smul, hρ, ← hτA, inv_smul_smul]⟩
  have hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0 := by
    intro B hB hBT hnsplit σ hσK hσI
    refine hyS B hB (fun A₀ hA₀ hconj => ?_) hnsplit σ hσK hσI
    obtain ⟨A', hA', hA'B⟩ := Work.SSGRoute.ZDataMup.kleadReps_covers K S hA₀ hconj
    obtain ⟨A'', hA'', hA''A'⟩ := Work.SSGRoute.H9.krep_covers K _ A' hA'
    exact hBT A'' hA'' (Work.SSGRoute.H9.swGesKConj_trans hA''A' hA'B)
  -- ## the oracle
  obtain ⟨b, Q, hQfin, hQsplit, hQnotT, hQnotTk, hagree, hinv, hunr⟩ :=
    Work.SSGRoute.ZDataTwo.mu2EscapeRealisationHKfresh k Ω K Λ hKΛ ζ hζ hζK T hTfin hTdisj hTcov
      y hy hyc hgram (fun _ _ => 0)
      (fun _ _ _ _ => by simp)
      (fun _ _ => ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩)
      (fun _ _ => Or.inl (fun _ _ => rfl))
      (fun A hA σ hσK hσI => by
        simpa using hyT A (hTfin A hA) (hTS A hA) σ hσK hσI)
      (fun c hc hc2 => hyinf c hc hc2)
      (fun _ _ _ _ _ => rfl)
  refine ⟨b, Q, hQfin, hQsplit, ?_, ?_, ?_, ?_, ?_⟩
  · -- every element of `S` is `K`-conjugate to an element of `T`, and `T` avoids `Q`
    intro A hA hconj
    obtain ⟨τ, hτK, hτA⟩ := hconj
    obtain ⟨A', hA', hA'Q⟩ := Work.SSGRoute.ZDataMup.kleadReps_covers K S hA ⟨τ, hτA⟩
    obtain ⟨A'', hA'', hA''A'⟩ := Work.SSGRoute.H9.krep_covers K _ A' hA'
    exact hQnotT A'' hA'' (Work.SSGRoute.H9.swGesKConj_trans hA''A' hA'Q)
  · -- the strengthened, `k`-level exclusion at the places of `S`
    intro A hA hconj
    have hmem : Work.SSGRoute.ZDataMup.galLift K (1 : K ≃ₐ[k] K) • A ∈
        Work.SSGRoute.ZDataMup.kleadReps K S :=
      Finset.mem_image.mpr ⟨(A, 1), Finset.mem_product.mpr ⟨hA, Finset.mem_univ 1⟩, rfl⟩
    obtain ⟨A', hA', hA'A⟩ := Work.SSGRoute.H9.krep_covers K _ _ hmem
    obtain ⟨τ, hτK, hτA⟩ := hA'A
    have hconjA' : SSGRoute.IsConjPlace k A' A :=
      ⟨(Work.SSGRoute.ZDataMup.galLift K (1 : K ≃ₐ[k] K))⁻¹ * τ, by
        rw [mul_smul, hτA, inv_smul_smul]⟩
    exact hQnotTk A' hA' (SSGRoute.isConjPlace_trans hconjA' hconj)
  · -- the agreement, transported from the `T`-blocks to all the `k`-conjugates of `S`
    intro B hB hSconj σ hσ
    obtain ⟨hσd, hσK⟩ := Subgroup.mem_inf.mp hσ
    obtain ⟨A₀, hA₀, hA₀B⟩ := hSconj
    obtain ⟨A', hA', hA'B⟩ := Work.SSGRoute.ZDataMup.kleadReps_covers K S hA₀ hA₀B
    obtain ⟨A'', hA'', hA''A'⟩ := Work.SSGRoute.H9.krep_covers K _ A' hA'
    obtain ⟨υ, hυK, hυ⟩ := hA''A'
    obtain ⟨τ, hτK, hτ⟩ := hA'B
    -- `B = (τ * υ) • A''`
    have hμ : τ * υ ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hτK hυK
    have hμi : (τ * υ)⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hμ
    have hBμ : (τ * υ) • A'' = B := by rw [mul_smul, hυ, hτ]
    -- the conjugate `σ' = (τυ)⁻¹ σ (τυ)` lies in the local group of `A''`
    set σ' : Ω ≃ₐ[k] Ω := (τ * υ)⁻¹ * σ * (τ * υ) with hσ'def
    have hσ'K : σ' ∈ K.fixingSubgroup :=
      K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem hμi hσK) hμ
    have hσ'A : σ' ∈ SSGRoute.decomp k A'' := by
      show σ' • A'' = A''
      rw [hσ'def, mul_smul, mul_smul, hBμ, hσd, ← hBμ, inv_smul_smul]
    have horacle : nodeKummerCochar K ζ hζK hζ b σ' = y σ' := by
      simpa using hagree A'' hA'' σ' (Subgroup.mem_inf.mpr ⟨hσ'A, hσ'K⟩)
    -- `χ_b σ = χ_b σ'` and `y σ = y σ'` by `G_K`-conjugation invariance
    have hχ : nodeKummerCochar K ζ hζK hζ b σ = nodeKummerCochar K ζ hζK hζ b σ' := by
      have h := nodeKummerCochar_conj_two k Ω K ζ hζ hζK b hμi hσK
      simp only [inv_inv] at h
      rw [hσ'def]
      exact h.symm
    have hyc' : y σ = y σ' := by
      have h := Work.SSGRoute.ZDataMup.additive_conj_invariant K y hy hμi hσK
      simp only [inv_inv] at h
      rw [hσ'def]
      exact h.symm
    rw [hχ, horacle, hyc']
  · exact hinv
  · -- the confinement, transported from `T` to `S`
    intro B hB hSconj hQconj σ hσK hσI
    refine hunr B hB (fun A hA hconj => ?_) hQconj σ hσK hσI
    obtain ⟨A₀, hA₀, hA₀A⟩ := hTS A hA
    obtain ⟨ρ, hρ⟩ := hA₀A
    obtain ⟨τ, hτK, hτB⟩ := hconj
    exact hSconj A₀ hA₀ ⟨τ * ρ, by rw [mul_smul, hρ, hτB]⟩

end Work.SSGRoute.ZDataTwo
