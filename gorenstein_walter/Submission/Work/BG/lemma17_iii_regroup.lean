import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.Lambda
import Submission.Work.BG.lemma17_ii
import Submission.Work.BG.lemma17_ii_aux

/-!
# Area BG: regrouping of `χ|_{H₀}` along the `Λ`-orbits (Bender–Glauberman 1981, Lemma 1.7)

For a Hypothesis-1.2 configuration with `|H₀ : U| = 2` (so that `Λ = {1, λ₂}`), a transversal
`rep` of the `Λ`-orbits of `Irr(H₀)` satisfying the freeness/disjointness/covering hypotheses of
`Work.BG.lemma17_ii`, and *any* class function `χ` of `G`, the value of `χ` at `g ∈ H₀` can be
written as a sum over `rep` in which each `Λ`-orbit `{μ, λ₂μ}` contributes its two terms:

`χ(g) = Σ_{μ ∈ rep} ( ⟨χ|_{H₀}, μ⟩·μ(g) + ⟨χ|_{H₀}, λ₂μ⟩·(λ₂μ)(g) )`.

This is the regrouping used by part (iii) of Lemma 1.7: it is (ii) with the orbit sums `r(Λν)`
counted once per element (which the freeness hypothesis `hfree` guarantees) and the two members
of each orbit `{μ, λ₂μ}` written out separately.

The mathematical content is

* Fourier inversion on `H₀` (`sum_inner_irreducibleCharacter_smul`), which expresses `χ|_{H₀}`
  as `Σ_{ν ∈ Irr(H₀)} ⟨χ|_{H₀}, ν⟩·ν` — this uses the *arbitrary* class function form of the
  inversion, no virtual-characterness of `χ` is required;
* the `Λ`-orbit parameterisation `(β, μ) ↦ Inf(β)·μ : (H₀/U)^* × rep ≃ Irr(H₀)` of
  `Work.BG.orbitMap_bijective`, together with the fact that a group of order two has a two-element
  dual (`sum_monoidHom_dual_eq_of_natCard_two`), which splits the `(H₀/U)^*` sum into the two
  terms `β = 1` and `β = λ₂`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **The dual of a group of order two.**  If `A` is a group with `Nat.card A = 2` and
`lam2 ≠ 1` is a homomorphism `A →* ℂˣ`, then the only homomorphisms `A →* ℂˣ` are `1` and
`lam2`; consequently any sum over the dual reduces to its two terms. -/
theorem sum_monoidHom_dual_eq_of_natCard_two {A : Type} [Group A] (h2 : Nat.card A = 2)
    {lam2 : A →* ℂˣ} (hlam2 : lam2 ≠ 1) (H : (A →* ℂˣ) → ℂ) [Fintype (A →* ℂˣ)] :
    ∑ β : A →* ℂˣ, H β = H 1 + H lam2 := by
  classical
  -- A group of order two has a (unique) non-identity element `c` which generates it, so that
  -- every homomorphism is determined by its value at `c`.
  have key : ∀ (c : A), c ≠ 1 → (∀ z : A, z = 1 ∨ z = c) →
      ∀ β : A →* ℂˣ, β = 1 ∨ β = lam2 := by
    intro c hc hgen β
    have hdet : ∀ {γ δ : A →* ℂˣ}, γ c = δ c → γ = δ := by
      intro γ δ h
      ext z
      rcases hgen z with hz | hz
      · rw [hz, map_one, map_one]
      · rw [hz, h]
    have hc2 : c * c = 1 := by
      rcases hgen (c * c) with h | h
      · exact h
      · exact absurd (mul_left_cancel (show c * c = c * 1 by rw [h, mul_one])) hc
    have hval : ∀ (γ : A →* ℂˣ), γ c = 1 ∨ γ c = -1 := by
      intro γ
      have hsq : (γ c) ^ 2 = 1 := by rw [sq, ← map_mul, hc2, map_one]
      have h2c : (((γ c : ℂˣ)) : ℂ) ^ 2 = 1 := by
        have := congrArg (fun u : ℂˣ => (u : ℂ)) hsq
        simpa [Units.val_pow_eq_pow_val] using this
      have hfac : ((((γ c : ℂˣ)) : ℂ) - 1) * ((((γ c : ℂˣ)) : ℂ) + 1) = 0 := by
        linear_combination h2c
      rcases mul_eq_zero.mp hfac with h | h
      · left; exact Units.ext (by simpa using sub_eq_zero.mp h)
      · right; exact Units.ext (by simpa using add_eq_zero_iff_eq_neg.mp h)
    have hlam2c : lam2 c = -1 := by
      rcases hval lam2 with h | h
      · exfalso
        refine hlam2 (hdet ?_)
        rw [h]; simp
      · exact h
    rcases hval β with h | h
    · left; refine hdet ?_; rw [h]; simp
    · right; refine hdet ?_; rw [h, hlam2c]
  -- `A` has exactly two elements, one of which is `1`.
  obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.mp h2
  have hcover : ∀ z : A, z = x ∨ z = y := fun z => by
    have hz : z ∈ ({x, y} : Set A) := by rw [hset]; trivial
    simpa [Set.mem_insert_iff] using hz
  have hdual : ∀ β : A →* ℂˣ, β = 1 ∨ β = lam2 := by
    rcases hcover 1 with h1x | h1y
    · refine key y (fun h => hxy (h1x.symm.trans h.symm)) (fun z => ?_)
      rcases hcover z with h | h
      · exact Or.inl (h.trans h1x.symm)
      · exact Or.inr h
    · refine key x (fun h => hxy (h.trans h1y)) (fun z => ?_)
      rcases hcover z with h | h
      · exact Or.inr h
      · exact Or.inl (h.trans h1y.symm)
  have huniv : (Finset.univ : Finset (A →* ℂˣ)) = {1, lam2} :=
    Finset.Subset.antisymm
      (fun x _ => by rcases hdual x with h | h <;> simp [h])
      (fun x _ => Finset.mem_univ x)
  rw [huniv, Finset.sum_pair (f := H) hlam2.symm]

/-- **Regrouping the Fourier expansion of a class function of `H₀` along the `Λ`-orbits.**

Under the hypotheses of `Work.BG.lemma17_ii` (a transversal `rep` of the `Λ`-orbits of
`Irr(H₀)` with free, pairwise disjoint, covering orbits) and `Nat.card (H₀/U) = 2`, the
Fourier expansion `Σ_{ν ∈ Irr(H₀)} ⟨ψ, ν⟩·ν(g)` of an arbitrary class function `ψ` of `H₀`
splits into the two members of every orbit:

`Σ_{ν} ⟨ψ, ν⟩·ν(g) = Σ_{μ ∈ rep} ( ⟨ψ, μ⟩·μ(g) + ⟨ψ, λ₂μ⟩·(λ₂μ)(g) )`. -/
theorem fourier_eq_sum_rep {G : Type} [Group G] [Finite G] (P : Hyp12 G)
    [(P.U.subgroupOf P.H0).Normal] [Fintype ↥P.H0] [Invertible (Nat.card ↥P.H0 : ℂ)]
    [Fintype (quotGroup P →* ℂˣ)] [Fintype (IrreducibleCharacter ↥P.H0)]
    (h2 : Nat.card (quotGroup P) = 2) {lam2 : quotGroup P →* ℂˣ} (hlam2 : lam2 ≠ 1)
    (rep : Finset (ClassFunction ↥P.H0 ℂ))
    (hirr : ∀ μ ∈ rep, IsIrreducibleCharacter μ)
    (hfree : ∀ μ ∈ rep, Function.Injective (fun β : quotGroup P →* ℂˣ =>
      ClassFunction.compHom (quotMk P) (linearClassFunction β) * μ))
    (hdisj : ∀ μ ∈ rep, ∀ ν ∈ rep, μ ≠ ν →
      ¬ ∃ lam ∈ Lambda P, lam * μ = ν)
    (hov : ∀ ν : IrreducibleCharacter ↥P.H0,
      ∃ μ ∈ rep, ((ν : ClassFunction ↥P.H0 ℂ) = μ) ∨
        ∃ lam ∈ Lambda P, (ν : ClassFunction ↥P.H0 ℂ) = lam * μ)
    (ψ : ClassFunction ↥P.H0 ℂ) (g : ↥P.H0) :
    (∑ ν : IrreducibleCharacter ↥P.H0,
        ClassFunction.inner ψ (ν : ClassFunction ↥P.H0 ℂ) *
          ((ν : ClassFunction ↥P.H0 ℂ) g))
      = ∑ μ ∈ rep, (ClassFunction.inner ψ μ * μ g
          + ClassFunction.inner ψ (ClassFunction.compHom (quotMk P)
              (linearClassFunction lam2) * μ)
            * (ClassFunction.compHom (quotMk P) (linearClassFunction lam2) * μ) g) := by
  classical
  haveI : Fintype ↥rep := rep.fintypeCoeSort
  -- The `Λ`-orbit parameterisation `(β, μ) ↦ Inf(β)·μ`.
  let e : ((quotGroup P →* ℂˣ) × ↥rep) ≃ IrreducibleCharacter ↥P.H0 :=
    Equiv.ofBijective (orbitMap P rep hirr)
      (orbitMap_bijective P rep hirr hfree hdisj hov)
  have hcf : ∀ (β : quotGroup P →* ℂˣ) (μ : ↥rep),
      (e (β, μ) : ClassFunction ↥P.H0 ℂ) = lambdaInf P β * (μ : ClassFunction ↥P.H0 ℂ) := by
    intro β μ
    rw [Equiv.ofBijective_apply, orbitMap_apply]
  -- Reindex `Irr(H₀)` by `(H₀/U)^* × rep`.
  have step1 : (∑ ν : IrreducibleCharacter ↥P.H0,
        ClassFunction.inner ψ (ν : ClassFunction ↥P.H0 ℂ) *
          ((ν : ClassFunction ↥P.H0 ℂ) g))
      = ∑ x : (quotGroup P →* ℂˣ) × ↥rep,
          ClassFunction.inner ψ (e x : ClassFunction ↥P.H0 ℂ) *
            ((e x : ClassFunction ↥P.H0 ℂ) g) :=
    (Fintype.sum_equiv e (fun x => ClassFunction.inner ψ (e x : ClassFunction ↥P.H0 ℂ) *
        ((e x : ClassFunction ↥P.H0 ℂ) g))
      (fun ν => ClassFunction.inner ψ (ν : ClassFunction ↥P.H0 ℂ) *
        ((ν : ClassFunction ↥P.H0 ℂ) g)) (fun x => rfl)).symm
  rw [step1, Fintype.sum_prod_type]
  simp only [hcf]
  -- Interchange the two sums and split the `(H₀/U)^*`-sum into `β = 1` and `β = λ₂`.
  rw [Finset.sum_comm]
  have hsplit : ∀ μ : ↥rep,
      (∑ β : quotGroup P →* ℂˣ,
        ClassFunction.inner ψ (lambdaInf P β * (μ : ClassFunction ↥P.H0 ℂ)) *
          ((lambdaInf P β * (μ : ClassFunction ↥P.H0 ℂ)) g))
      = ClassFunction.inner ψ (μ : ClassFunction ↥P.H0 ℂ) * ((μ : ClassFunction ↥P.H0 ℂ) g)
        + ClassFunction.inner ψ (lambdaInf P lam2 * (μ : ClassFunction ↥P.H0 ℂ)) *
          ((lambdaInf P lam2 * (μ : ClassFunction ↥P.H0 ℂ)) g) := by
    intro μ
    rw [sum_monoidHom_dual_eq_of_natCard_two (A := quotGroup P) h2 hlam2
      (fun β => ClassFunction.inner ψ (lambdaInf P β * (μ : ClassFunction ↥P.H0 ℂ)) *
          ((lambdaInf P β * (μ : ClassFunction ↥P.H0 ℂ)) g)),
      lambdaInf_one, one_mul_cf]
  rw [Finset.sum_congr rfl (fun μ _ => hsplit μ)]
  simp only [lambdaInf]
  exact (Finset.sum_subtype rep (fun x => Iff.rfl) (fun μ => ClassFunction.inner ψ μ * μ g
        + ClassFunction.inner ψ (ClassFunction.compHom (quotMk P)
            (linearClassFunction lam2) * μ)
          * (ClassFunction.compHom (quotMk P)
            (linearClassFunction lam2) * μ) g)).symm

theorem lemma17_iii_regroup {G : Type} [Group G] [Finite G] (P : Work.BG.Hyp12 G)
    [(P.U.subgroupOf P.H0).Normal] [Fintype ↥P.H0] [Invertible (Nat.card ↥P.H0 : ℂ)]
    [Fintype (Work.BG.quotGroup P →* ℂˣ)]
    [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter ↥P.H0)]
    (h2 : Nat.card (Work.BG.quotGroup P) = 2) {lam2 : Work.BG.quotGroup P →* ℂˣ}
    (hlam2 : lam2 ≠ 1)
    (rep : Finset (OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ))
    (hirr : ∀ μ ∈ rep, OddOrder.RepresentationTheory.IsIrreducibleCharacter μ)
    (hfree : ∀ μ ∈ rep, Function.Injective (fun β : Work.BG.quotGroup P →* ℂˣ =>
      OddOrder.RepresentationTheory.ClassFunction.compHom (Work.BG.quotMk P)
        (OddOrder.RepresentationTheory.linearClassFunction β) * μ))
    (hdisj : ∀ μ ∈ rep, ∀ ν ∈ rep, μ ≠ ν →
      ¬ ∃ lam ∈ Work.BG.Lambda P, lam * μ = ν)
    (hov : ∀ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥P.H0,
      ∃ μ ∈ rep, ((ν : OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ) = μ) ∨
        ∃ lam ∈ Work.BG.Lambda P,
          (ν : OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ) = lam * μ)
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) (g : ↥P.H0) :
    χ (g : G) = ∑ μ ∈ rep,
      (OddOrder.RepresentationTheory.ClassFunction.inner
          (OddOrder.RepresentationTheory.ClassFunction.restrict P.H0 χ) μ * μ g
        + OddOrder.RepresentationTheory.ClassFunction.inner
            (OddOrder.RepresentationTheory.ClassFunction.restrict P.H0 χ)
            (OddOrder.RepresentationTheory.ClassFunction.compHom (Work.BG.quotMk P)
              (OddOrder.RepresentationTheory.linearClassFunction lam2) * μ)
          * (OddOrder.RepresentationTheory.ClassFunction.compHom (Work.BG.quotMk P)
              (OddOrder.RepresentationTheory.linearClassFunction lam2) * μ) g) := by
  -- Fourier inversion on `H₀`: `χ|_{H₀} = Σ_{ν ∈ Irr(H₀)} ⟨χ|_{H₀}, ν⟩·ν`.
  have hFourier := sum_inner_irreducibleCharacter_smul (G := ↥P.H0)
    (ClassFunction.restrict P.H0 χ)
  have hval : χ (g : G) = ∑ ν : IrreducibleCharacter ↥P.H0,
      ClassFunction.inner (ClassFunction.restrict P.H0 χ) (ν : ClassFunction ↥P.H0 ℂ) *
        ((ν : ClassFunction ↥P.H0 ℂ) g) := by
    have h := congrArg (fun (φ : ClassFunction ↥P.H0 ℂ) => φ g) hFourier
    rw [ClassFunction.sum_apply] at h
    rw [← ClassFunction.restrict_apply P.H0 χ g]
    simpa [ClassFunction.smul_apply] using h.symm
  rw [hval]
  exact fourier_eq_sum_rep P h2 hlam2 rep hirr hfree hdisj hov
    (ClassFunction.restrict P.H0 χ) g

end Work.BG
