import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.HSRow.TransgressionDefs
import Submission.Work.SSGRoute.HSTwoRow.exists_lcCocycleOn_zpowers_gen_eq
import Submission.Work.SSGRoute.HSTwoRow.procyclic_hypotheses
import Submission.Work.SSGRoute.PT.isCoboundary2On_of_proCyclic_growth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.HSRow

set_option linter.style.haveILetI false

/-- A locally constant `c`-twisted crossed homomorphism `χ` on `C = closure (zpowers σ)` with
prescribed value `-m` at `σ`.  Construction: `χ := a - χ₀` where `χ₀ : ↥C → M` is a locally
constant primitive of the restriction of `c` to `C × C` (exists because `H²(C, ·) = 0` for procyclic
`C`, i.e. `Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth` with the growth hypotheses of
`Work.SSGRoute.HSTwoRow.procyclic_hypotheses`) and `a` is a locally constant `1`-cocycle on `C` with
`a σ = χ₀ σ - m` (`Work.SSGRoute.HSTwoRow.exists_lcCocycleOn_zpowers_gen_eq` with the stable
submodule `⊤`; it exists for *every* value because `p • (norm of a finite order generator) = 0`).
Then `χ (γ * δ) = χ γ + ρ(γ) • χ δ + c γ δ` and `χ σ = -m`. -/
theorem exists_chi
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (σ : Ω ≃ₐ[k] Ω)
    (hZ : ∀ n : ℕ, 0 < n → ∃ f : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) →*
        Multiplicative (ZMod n), Function.Surjective f)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hcC : SSGRoute.IsCocycle2
      ((SSGRoute.res k K).comp (Subgroup.subtype (Subgroup.topologicalClosure (Subgroup.zpowers σ))))
      (fun γ δ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) => c γ δ))
    (hlcC : SSGRoute.IsLocConst2
      (fun γ δ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) => c γ δ))
    (m : M) :
    ∃ χ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) → M,
      SSGRoute.IsLocConstOn ⊤ χ ∧
      (∀ γ δ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)),
        χ (γ * δ) = χ γ + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • χ δ
          + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω)) ∧
      χ ⟨σ, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)⟩ = -m := by
  classical
  -- The procyclic group `C = closure (zpowers σ)`.
  set C : Subgroup (Ω ≃ₐ[k] Ω) := Subgroup.topologicalClosure (Subgroup.zpowers σ) with hCdef
  have hσC : σ ∈ C := Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)
  haveI hcompC : CompactSpace ↥C :=
    isCompact_iff_compactSpace.mp
      (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers σ)).isCompact
  -- Procyclicity and the `p`-adic growth of `C` (`hZ`).
  obtain ⟨hprocyc, hbig⟩ := Work.SSGRoute.HSTwoRow.procyclic_hypotheses p k Ω σ hZ
  -- The action `act = res k K ∘ subtype C` of `C` on `M`.
  let act : ↥C →* (K ≃ₐ[k] K) := (SSGRoute.res k K).comp (Subgroup.subtype C)
  have hcont : Continuous (fun g : ↥C => SSGRoute.res k K (g : Ω ≃ₐ[k] Ω)) :=
    (InfiniteGalois.restrictNormalHom_continuous K).comp continuous_subtype_val
  -- The action is trivial on some open subgroup (the kernel of the restriction), because
  -- `res k K` is continuous and `K ≃ₐ[k] K` is discrete.
  have hker : ∃ U₀ : Subgroup ↥C, IsOpen (U₀ : Set ↥C) ∧ ∀ g ∈ U₀, ∀ n : M, act g • n = n := by
    refine ⟨act.ker, ?_, ?_⟩
    · have h1 : (act.ker : Set ↥C) = act ⁻¹' ({1} : Set (K ≃ₐ[k] K)) := rfl
      rw [h1]
      exact (isOpen_discrete ({1} : Set (K ≃ₐ[k] K))).preimage hcont
    · intro g hg n
      have hg1 : act g = 1 := hg
      rw [hg1, one_smul]
  -- `H²(C, M) = 0`: a locally constant primitive `χ₀` of `c|_C`.
  obtain ⟨χ₀, hχ₀lc, hχ₀eq⟩ :=
    Work.SSGRoute.PT.isCoboundary2On_of_proCyclic_growth (p := p) (Γ := ↥C)
      (G := K ≃ₐ[k] K) (N := M) act hker hprocyc hbig (fun γ δ : ↥C => c γ δ) hcC hlcC
  -- A locally constant `1`-cocycle `a` on `C` with `a σ = χ₀ σ - m`.
  obtain ⟨a, hacoc, halc, haσ, -⟩ :=
    Work.SSGRoute.HSTwoRow.exists_lcCocycleOn_zpowers_gen_eq p k Ω K M σ hZ ⊤
      (fun γ _ w _ => Submodule.mem_top) (χ₀ ⟨σ, hσC⟩ - m) Submodule.mem_top
  -- `χ := a - χ₀` is the required twisted crossed homomorphism.
  refine ⟨fun γ : ↥C => a (γ : Ω ≃ₐ[k] Ω) - χ₀ γ, ?_, ?_, ?_⟩
  · -- local constancy on `⊤`: intersect a subgroup where `a` is constant with one where `χ₀` is.
    obtain ⟨U, hUo, hUinv⟩ := halc
    obtain ⟨U₀, hU₀o, hU₀inv⟩ := hχ₀lc
    refine ⟨U₀ ⊓ U.comap (Subgroup.subtype C), ?_, ?_⟩
    · rw [Subgroup.coe_inf]
      refine hU₀o.inter ?_
      have h : (U.comap (Subgroup.subtype C) : Set ↥C)
          = Subtype.val ⁻¹' (U : Set (Ω ≃ₐ[k] Ω)) := rfl
      rw [h]
      exact hUo.preimage continuous_subtype_val
    · intro g hg u hu huTop
      obtain ⟨hu₀, huU⟩ := Subgroup.mem_inf.mp hu
      show a ((g * u : ↥C) : Ω ≃ₐ[k] Ω) - χ₀ (g * u) = a (g : Ω ≃ₐ[k] Ω) - χ₀ g
      have huC : (u : Ω ≃ₐ[k] Ω) ∈ C := u.2
      have h1 : a ((g * u : ↥C) : Ω ≃ₐ[k] Ω) = a (g : Ω ≃ₐ[k] Ω) := by
        have hh := hUinv (g : Ω ≃ₐ[k] Ω) g.2 (u : Ω ≃ₐ[k] Ω) (Subgroup.mem_comap.mp huU) huC
        simpa using hh
      have h2 : χ₀ (g * u) = χ₀ g := hU₀inv g (Subgroup.mem_top g) u hu₀ (Subgroup.mem_top u)
      rw [h1, h2]
  · -- the twisted crossed homomorphism identity
    intro γ δ
    have hcoc := hacoc (γ : Ω ≃ₐ[k] Ω) γ.2 (δ : Ω ≃ₐ[k] Ω) δ.2
    have hprim := hχ₀eq γ (Subgroup.mem_top γ) δ (Subgroup.mem_top δ)
    beta_reduce at hprim
    simp only [act, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype] at hprim
    show a ((γ * δ : ↥C) : Ω ≃ₐ[k] Ω) - χ₀ (γ * δ)
      = (a (γ : Ω ≃ₐ[k] Ω) - χ₀ γ)
        + SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • (a (δ : Ω ≃ₐ[k] Ω) - χ₀ δ)
        + c (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω)
    simp only [Subgroup.coe_mul] at hcoc ⊢
    rw [hcoc, hprim, smul_sub]
    abel
  · -- the prescribed value at `σ`
    show a ((⟨σ, hσC⟩ : ↥C) : Ω ≃ₐ[k] Ω) - χ₀ ⟨σ, hσC⟩ = -m
    have haσ' : a ((⟨σ, hσC⟩ : ↥C) : Ω ≃ₐ[k] Ω) = χ₀ ⟨σ, hσC⟩ - m := haσ
    rw [haσ']
    abel

end Work.SSGRoute.HSRow
