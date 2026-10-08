import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.CharBridge
import Submission.Work.BG.Lambda
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.lambda_mul_mem
import Submission.Work.BG.lemma17_ii_aux
import Submission.OddOrder.GroupTheory.RepresentationTheory.CharacterCompleteness
import Submission.OddOrder.GroupTheory.RepresentationTheory.CharacterProduct

/-!
# Area BG: Bender–Glauberman 1981, Lemma 1.7(ii)

The `Λ`-orbit decomposition of the restriction to `H₀` of a virtual character of `G`:

`χ|_{H₀} = Σ_{ν ∈ Irr(H₀)} (a_ν − a_{ρν})·ν  +  Σ_{μ ∈ rep} a_μ · r(Λμ)`,

where `rep` is a transversal of the `Λ`-orbits of `Irr(H₀)`, `ρ` selects the representative of
the orbit of `ν`, `a_ν = (χ|_{H₀}, ν)_{H₀}`, and `r(Λμ)` is the (normalised) orbit sum.

The proof is the one given by the paper: Fourier inversion writes `χ|_{H₀} = Σ_ν a_ν ν`, and the
two orbit-summed pieces cancel because the parameterisation `(β, μ) ↦ Inf(β)·μ` is a bijection
`(H₀/U)^* × rep → Irr(H₀)` (here the freeness hypothesis on the stabilisers is what makes the
orbit sum a sum over the orbit *with each element once*, matching `lambdaOrbitSum`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- **The orbit parameterisation is a bijection.**  Under the freeness, disjointness and
covering hypotheses, `(β, μ) ↦ Inf(β)·μ` is a bijection
`(H₀/U)^* × rep ≃ Irr(H₀)`. -/
theorem orbitMap_bijective (P : Hyp12 G) [(P.U.subgroupOf P.H0).Normal]
    [Fintype ↥P.H0] [Invertible (Nat.card ↥P.H0 : ℂ)]
    [Fintype (quotGroup P →* ℂˣ)]
    [Fintype (IrreducibleCharacter ↥P.H0)]
    (rep : Finset (ClassFunction ↥P.H0 ℂ))
    (hirr : ∀ μ ∈ rep, IsIrreducibleCharacter μ)
    (hfree : ∀ μ ∈ rep, Function.Injective (fun β : quotGroup P →* ℂˣ =>
      lambdaInf P β * μ))
    (hdisj : ∀ μ ∈ rep, ∀ ν ∈ rep, μ ≠ ν → ¬ ∃ lam ∈ Lambda P, lam * μ = ν)
    (hov : ∀ ν : IrreducibleCharacter ↥P.H0,
      ∃ μ ∈ rep, ((ν : ClassFunction ↥P.H0 ℂ) = μ) ∨
        ∃ lam ∈ Lambda P, (ν : ClassFunction ↥P.H0 ℂ) = lam * μ) :
    Function.Bijective (orbitMap P rep hirr) := by
  constructor
  · rintro ⟨β₁, μ₁⟩ ⟨β₂, μ₂⟩ h
    have hcf : lambdaInf P β₁ * (μ₁ : ClassFunction ↥P.H0 ℂ) =
        lambdaInf P β₂ * (μ₂ : ClassFunction ↥P.H0 ℂ) := by
      have h' := Subtype.ext_iff.mp h
      simpa only [orbitMap_apply] using h'
    have h2 : (μ₁ : ClassFunction ↥P.H0 ℂ) =
        lambdaInf P (β₁⁻¹ * β₂) * (μ₂ : ClassFunction ↥P.H0 ℂ) := by
      have hstep := congrArg (fun z => lambdaInf P β₁⁻¹ * z) hcf
      rw [← mul_assoc_cf, ← mul_assoc_cf, lambdaInf_inv_mul, one_mul_cf, lambdaInf_mul]
        at hstep
      exact hstep
    by_cases hμ : (μ₁ : ClassFunction ↥P.H0 ℂ) = (μ₂ : ClassFunction ↥P.H0 ℂ)
    · have hfr : lambdaInf P β₁ * (μ₁ : ClassFunction ↥P.H0 ℂ) =
          lambdaInf P β₂ * (μ₁ : ClassFunction ↥P.H0 ℂ) := by
        rw [hcf, ← hμ]
      have hβ : β₁ = β₂ := hfree μ₁ μ₁.2 hfr
      have hμ' : μ₁ = μ₂ := Subtype.ext hμ
      rw [hβ, hμ']
    · have hEx : ∃ lam ∈ Lambda P,
          lam * (μ₂ : ClassFunction ↥P.H0 ℂ) = (μ₁ : ClassFunction ↥P.H0 ℂ) :=
        ⟨lambdaInf P (β₁⁻¹ * β₂), lambdaInf_mem P _, h2.symm⟩
      exact absurd hEx (hdisj μ₂ μ₂.2 μ₁ μ₁.2 (fun hh => hμ hh.symm))
  · rintro ν
    obtain ⟨μ, hμ, hcases⟩ := hov ν
    rcases hcases with h | ⟨lam, hlam, hν⟩
    · refine ⟨(1, ⟨μ, hμ⟩), ?_⟩
      apply Subtype.ext
      show (orbitMap P rep hirr (1, ⟨μ, hμ⟩) : ClassFunction ↥P.H0 ℂ) =
        (ν : ClassFunction ↥P.H0 ℂ)
      rw [orbitMap_apply, lambdaInf_one, one_mul_cf]
      simpa using h.symm
    · obtain ⟨β, hβ⟩ := (mem_Lambda_iff P).mp hlam
      refine ⟨(β, ⟨μ, hμ⟩), ?_⟩
      apply Subtype.ext
      show (orbitMap P rep hirr (β, ⟨μ, hμ⟩) : ClassFunction ↥P.H0 ℂ) =
        (ν : ClassFunction ↥P.H0 ℂ)
      rw [orbitMap_apply, hβ]
      simpa using hν.symm

/-- **`ρ` selects the representative of the orbit of `Inf(β)·μ`.** -/
theorem orbitMap_rho (P : Hyp12 G) [(P.U.subgroupOf P.H0).Normal]
    [Fintype ↥P.H0] [Invertible (Nat.card ↥P.H0 : ℂ)]
    [Fintype (quotGroup P →* ℂˣ)]
    [Fintype (IrreducibleCharacter ↥P.H0)]
    (rep : Finset (ClassFunction ↥P.H0 ℂ))
    (hirr : ∀ μ ∈ rep, IsIrreducibleCharacter μ)
    (hdisj : ∀ μ ∈ rep, ∀ ν ∈ rep, μ ≠ ν → ¬ ∃ lam ∈ Lambda P, lam * μ = ν)
    (ρ : IrreducibleCharacter ↥P.H0 → ClassFunction ↥P.H0 ℂ)
    (hρmem : ∀ ν : IrreducibleCharacter ↥P.H0, ρ ν ∈ rep)
    (hρorb : ∀ ν : IrreducibleCharacter ↥P.H0,
      ((ν : ClassFunction ↥P.H0 ℂ) = ρ ν) ∨
      ∃ lam ∈ Lambda P, (ν : ClassFunction ↥P.H0 ℂ) = lam * ρ ν) :
    ∀ x : (quotGroup P →* ℂˣ) × ↥rep,
      ρ (orbitMap P rep hirr x) = (x.2 : ClassFunction ↥P.H0 ℂ) := by
  rintro ⟨β, μ⟩
  have hν : (orbitMap P rep hirr (β, μ) : ClassFunction ↥P.H0 ℂ) =
      lambdaInf P β * (μ : ClassFunction ↥P.H0 ℂ) := orbitMap_apply P rep hirr (β, μ)
  rcases hρorb (orbitMap P rep hirr (β, μ)) with hA | hB
  · have hEx : ∃ lam ∈ Lambda P,
        lam * (μ : ClassFunction ↥P.H0 ℂ) = ρ (orbitMap P rep hirr (β, μ)) :=
      ⟨lambdaInf P β, lambdaInf_mem P β, hν.symm.trans hA⟩
    by_contra hne
    exact (hdisj μ μ.2 (ρ (orbitMap P rep hirr (β, μ))) (hρmem _))
      (fun hh => hne hh.symm) hEx
  · obtain ⟨lam, hlam, hνlam⟩ := hB
    obtain ⟨β', hβ'⟩ := (mem_Lambda_iff P).mp hlam
    have hkey : (μ : ClassFunction ↥P.H0 ℂ) =
        lambdaInf P (β⁻¹ * β') * ρ (orbitMap P rep hirr (β, μ)) := by
      have hcf : lambdaInf P β * (μ : ClassFunction ↥P.H0 ℂ) =
          lambdaInf P β' * ρ (orbitMap P rep hirr (β, μ)) := by
        rw [← hν, hνlam, hβ']
      have hstep := congrArg (fun z => lambdaInf P β⁻¹ * z) hcf
      rw [← mul_assoc_cf, ← mul_assoc_cf, lambdaInf_inv_mul, one_mul_cf, lambdaInf_mul]
        at hstep
      exact hstep
    have hEx : ∃ lam ∈ Lambda P,
        lam * ρ (orbitMap P rep hirr (β, μ)) = (μ : ClassFunction ↥P.H0 ℂ) :=
      ⟨lambdaInf P (β⁻¹ * β'), lambdaInf_mem P _, hkey.symm⟩
    by_contra hne
    exact (hdisj (ρ (orbitMap P rep hirr (β, μ))) (hρmem _) μ μ.2) hne hEx

theorem lemma17_ii {G : Type} [Group G] [Finite G] (P : Work.BG.Hyp12 G)
    [(P.U.subgroupOf P.H0).Normal] [Fintype ↥P.H0] [Invertible (Nat.card ↥P.H0 : ℂ)]
    [Invertible (Nat.card G : ℂ)] [Fintype G] [Fintype (Work.BG.quotGroup P →* ℂˣ)]
    [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter ↥P.H0)]
    (rep : Finset (OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ))
    (hirr : ∀ μ ∈ rep, OddOrder.RepresentationTheory.IsIrreducibleCharacter μ)
    (hfree : ∀ μ ∈ rep, Function.Injective (fun β : Work.BG.quotGroup P →* ℂˣ =>
      OddOrder.RepresentationTheory.ClassFunction.compHom (Work.BG.quotMk P)
        (OddOrder.RepresentationTheory.linearClassFunction β) * μ))
    (hdisj : ∀ μ ∈ rep, ∀ ν ∈ rep, μ ≠ ν → ¬ ∃ lam ∈ Work.BG.Lambda P, lam * μ = ν)
    (hov : ∀ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥P.H0,
      ∃ μ ∈ rep, ((ν : OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ) = μ) ∨
        ∃ lam ∈ Work.BG.Lambda P,
          (ν : OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ) = lam * μ)
    (ρ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥P.H0 →
      OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ)
    (hρmem : ∀ (ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥P.H0), ρ ν ∈ rep)
    (hρorb : ∀ (ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥P.H0),
      ((ν : OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ) =
        (ρ ν : OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ)) ∨
      ∃ lam ∈ Work.BG.Lambda P,
        (ν : OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ) =
          lam * (ρ ν : OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ))
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hχ : χ ∈ OddOrder.RepresentationTheory.ZIrr G) :
    OddOrder.RepresentationTheory.ClassFunction.restrict P.H0 χ
      = (∑ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥P.H0,
          ((OddOrder.RepresentationTheory.ClassFunction.inner
              (OddOrder.RepresentationTheory.ClassFunction.restrict P.H0 χ)
              (ν : OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ)) -
            (OddOrder.RepresentationTheory.ClassFunction.inner
              (OddOrder.RepresentationTheory.ClassFunction.restrict P.H0 χ) (ρ ν))) •
              (ν : OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ))
        + ∑ μ ∈ rep,
            (OddOrder.RepresentationTheory.ClassFunction.inner
              (OddOrder.RepresentationTheory.ClassFunction.restrict P.H0 χ) μ) •
              Work.BG.lambdaOrbitSum P μ := by
  classical
  haveI : Fintype ↥rep := rep.fintypeCoeSort
  let a : ClassFunction ↥P.H0 ℂ → ℂ :=
    fun μ => ClassFunction.inner (ClassFunction.restrict P.H0 χ) μ
  change ClassFunction.restrict P.H0 χ
      = (∑ ν : IrreducibleCharacter ↥P.H0, (a ν - a (ρ ν)) •
            (ν : ClassFunction ↥P.H0 ℂ))
        + ∑ μ ∈ rep, a μ • lambdaOrbitSum P μ
  -- (1) Fourier inversion
  have hFourier : ClassFunction.restrict P.H0 χ
      = ∑ ν : IrreducibleCharacter ↥P.H0, a ν • (ν : ClassFunction ↥P.H0 ℂ) :=
    (sum_inner_irreducibleCharacter_smul (ClassFunction.restrict P.H0 χ)).symm
  -- (3) the reindexing of the orbit sums
  have hReindex : (∑ ν : IrreducibleCharacter ↥P.H0, a (ρ ν) •
        (ν : ClassFunction ↥P.H0 ℂ))
      = ∑ μ ∈ rep, a μ • lambdaOrbitSum P μ := by
    have hbij := orbitMap_bijective P rep hirr hfree hdisj hov
    let e : ((quotGroup P →* ℂˣ) × ↥rep) ≃ IrreducibleCharacter ↥P.H0 :=
      Equiv.ofBijective _ hbij
    have hrho : ∀ x : (quotGroup P →* ℂˣ) × ↥rep,
        ρ (orbitMap P rep hirr x) = (x.2 : ClassFunction ↥P.H0 ℂ) :=
      orbitMap_rho P rep hirr hdisj ρ hρmem hρorb
    calc (∑ ν : IrreducibleCharacter ↥P.H0, a (ρ ν) •
            (ν : ClassFunction ↥P.H0 ℂ))
        = ∑ x : (quotGroup P →* ℂˣ) × ↥rep, a (ρ (orbitMap P rep hirr x)) •
            (orbitMap P rep hirr x : ClassFunction ↥P.H0 ℂ) :=
          (Fintype.sum_equiv e
            (fun x : (quotGroup P →* ℂˣ) × ↥rep => a (ρ (orbitMap P rep hirr x)) •
              (orbitMap P rep hirr x : ClassFunction ↥P.H0 ℂ))
            (fun ν : IrreducibleCharacter ↥P.H0 => a (ρ ν) •
              (ν : ClassFunction ↥P.H0 ℂ))
            (fun x => rfl)).symm
      _ = ∑ x : (quotGroup P →* ℂˣ) × ↥rep, a (x.2 : ClassFunction ↥P.H0 ℂ) •
            (lambdaInf P x.1 * (x.2 : ClassFunction ↥P.H0 ℂ)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hrho x, orbitMap_apply]
      _ = ∑ β : quotGroup P →* ℂˣ, ∑ μ : ↥rep,
            a (μ : ClassFunction ↥P.H0 ℂ) •
              (lambdaInf P β * (μ : ClassFunction ↥P.H0 ℂ)) :=
          Fintype.sum_prod_type _
      _ = ∑ μ : ↥rep, ∑ β : quotGroup P →* ℂˣ,
            a (μ : ClassFunction ↥P.H0 ℂ) •
              (lambdaInf P β * (μ : ClassFunction ↥P.H0 ℂ)) := by
          rw [Finset.sum_comm]
      _ = ∑ μ : ↥rep, a (μ : ClassFunction ↥P.H0 ℂ) •
            lambdaOrbitSum P (μ : ClassFunction ↥P.H0 ℂ) := by
          refine Finset.sum_congr rfl fun μ _ => ?_
          rw [lambdaOrbitSum_eq_sum, Finset.smul_sum]
      _ = ∑ μ ∈ rep, a μ • lambdaOrbitSum P μ :=
          (Finset.sum_subtype rep (fun x => Iff.rfl)
            (fun μ => a μ • lambdaOrbitSum P μ)).symm
  -- (2) the splitting of the Fourier coefficients
  have hAlg : (∑ ν : IrreducibleCharacter ↥P.H0, a ν •
        (ν : ClassFunction ↥P.H0 ℂ))
      = (∑ ν : IrreducibleCharacter ↥P.H0, (a ν - a (ρ ν)) •
            (ν : ClassFunction ↥P.H0 ℂ))
        + ∑ ν : IrreducibleCharacter ↥P.H0, a (ρ ν) •
            (ν : ClassFunction ↥P.H0 ℂ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ν _ => by
      rw [sub_smul, sub_add_cancel]
  rw [hFourier, ← hReindex, ← hAlg]

end Work.BG
