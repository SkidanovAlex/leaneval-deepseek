import Mathlib
import Submission.Work.ArtinInduction.LatticeModp.Infra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.ArtinInduction.LatticeModp

/-! ## Auxiliary lemmas for `coprime_reduce` -/

/-- An additive invariant `ρ` on finite `𝔽_p[G]`-modules takes the same value on two modules
related by a `G`-equivariant `ZMod p`-linear isomorphism: apply additivity to the short exact
sequence `N₁ --e--> N₂ --0--> PUnit` and use `rho_subsingleton` on `PUnit`. -/
lemma rho_iso {p : ℕ} [NeZero p] {G : Type} [Group G] (ρ : Inv p G) (hadd : IsAddInv ρ)
    {N₁ : Type} [AddCommGroup N₁] [Module (ZMod p) N₁] [DistribMulAction G N₁]
    [SMulCommClass G (ZMod p) N₁] [Finite N₁]
    {N₂ : Type} [AddCommGroup N₂] [Module (ZMod p) N₂] [DistribMulAction G N₂]
    [SMulCommClass G (ZMod p) N₂] [Finite N₂]
    (e : N₁ ≃ₗ[ZMod p] N₂) (he : ∀ (g : G) (x : N₁), e (g • x) = g • e x) :
    ρ N₂ = ρ N₁ := by
  have h0 : ρ (PUnit : Type) = 0 := rho_subsingleton ρ hadd
  have hker : LinearMap.ker (0 : N₂ →ₗ[ZMod p] PUnit)
      = LinearMap.range (e : N₁ →ₗ[ZMod p] N₂) := by
    rw [LinearMap.ker_zero, LinearMap.range_eq_top.mpr e.surjective]
  have h := hadd N₁ N₂ PUnit (e : N₁ →ₗ[ZMod p] N₂) (0 : N₂ →ₗ[ZMod p] PUnit)
    e.injective (fun y => ⟨0, Subsingleton.elim _ _⟩) hker he (fun g n => by simp)
  rwa [h0, add_zero] at h

/-- The `G`-action on a quotient is compatible with `Submodule.Quotient.mk`: this is
`quotDMA_mk` with the domain element written as a `Submodule.Quotient.mk`. -/
lemma quotDMA_mk_apply {G : Type} [Group G] {X : Type} [AddCommGroup X] [DistribMulAction G X]
    (S : Submodule ℤ X) (hS : ∀ (g : G) (x : X), x ∈ S → g • x ∈ S) (g : G) (x : X) :
    (letI : DistribMulAction G (X ⧸ S) := quotDMA S hS
     g • (Submodule.Quotient.mk (p := S) x : X ⧸ S))
      = Submodule.Quotient.mk (p := S) (g • x) :=
  qDMAA_mk S.toAddSubgroup hS g x

/-- `p` acts injectively on a finite module all of whose elements are `p`-divisible. -/
lemma pSmul_injective_of_finite_of_pdiv {p : ℕ} {Q : Type} [AddCommGroup Q] [Finite Q]
    (hdiv : pSmulSub p Q = ⊤) : Function.Injective (fun x : Q => (p : ℤ) • x) := by
  have hsurj : Function.Surjective (fun x : Q => (p : ℤ) • x) := fun x =>
    mem_pSmulSub_iff.mp (hdiv ▸ Submodule.mem_top)
  exact Finite.injective_iff_surjective.mpr hsurj

/-- The "prime-to-`p`" decomposition `R = A + pR`: if `R/A` is `p`-divisible then every `r ∈ R`
is of the form `a + p·y` with `a ∈ A` and `y ∈ R`. -/
lemma exists_eq_add_pSmul_of_pdiv {M : Type} [AddCommGroup M] (p : ℕ) (A R : Submodule ℤ M)
    (hAR : A ≤ R) (hdiv : pSmulSub p (↥R ⧸ Submodule.comap R.subtype A) = ⊤) (r : ↥R) :
    ∃ a : ↥A, ∃ y : ↥R, (r : M) = (a : M) + (p : ℤ) • (y : M) := by
  set A' : Submodule ℤ ↥R := Submodule.comap R.subtype A with hA'def
  have key : ∀ x : ↥R ⧸ A', ∃ y : ↥R ⧸ A', (p : ℤ) • y = x := fun x =>
    mem_pSmulSub_iff.mp (hdiv ▸ Submodule.mem_top)
  obtain ⟨y, hy⟩ := key (Submodule.Quotient.mk (p := A') r)
  obtain ⟨y₀, hy₀⟩ := Submodule.Quotient.mk_surjective A' y
  have h1 : Submodule.Quotient.mk (p := A') ((p : ℤ) • y₀) = Submodule.Quotient.mk (p := A') r := by
    rw [Submodule.Quotient.mk_smul, hy₀, hy]
  have h2 : ((p : ℤ) • y₀ - r) ∈ A' := (Submodule.Quotient.eq A').mp h1
  have h3 : ((p : ℤ) • (y₀ : M) - (r : M)) ∈ A := Submodule.mem_comap.mp h2
  refine ⟨⟨(r : M) - (p : ℤ) • (y₀ : M), ?_⟩, y₀, ?_⟩
  · simpa using A.neg_mem h3
  · simp

/-- `A ∩ pR ⊆ pA`: the inclusion `A/pA → R/pR` is injective. -/
lemma mem_pSmulSub_of_coe_mem_pSmulSub {M : Type} [AddCommGroup M] (p : ℕ) (A R : Submodule ℤ M)
    (hAR : A ≤ R) (hfin : Finite (↥R ⧸ Submodule.comap R.subtype A))
    (hdiv : pSmulSub p (↥R ⧸ Submodule.comap R.subtype A) = ⊤)
    (a : ↥A) (ha : (⟨a.1, hAR a.2⟩ : ↥R) ∈ pSmulSub p ↥R) :
    a ∈ pSmulSub p ↥A := by
  set A' : Submodule ℤ ↥R := Submodule.comap R.subtype A with hA'def
  haveI : Finite (↥R ⧸ A') := hfin
  have hinj : Function.Injective (fun x : ↥R ⧸ A' => (p : ℤ) • x) :=
    pSmul_injective_of_finite_of_pdiv hdiv
  obtain ⟨y, hy⟩ := mem_pSmulSub_iff.mp ha
  have hyA' : y ∈ A' := by
    have hzero : (p : ℤ) • (Submodule.Quotient.mk (p := A') y)
        = (p : ℤ) • (0 : ↥R ⧸ A') := by
      rw [smul_zero]
      have h2 : Submodule.Quotient.mk (p := A') ((p : ℤ) • y) = (0 : ↥R ⧸ A') := by
        rw [hy, Submodule.Quotient.mk_eq_zero]
        exact a.2
      rwa [Submodule.Quotient.mk_smul] at h2
    exact (Submodule.Quotient.mk_eq_zero A').mp (hinj hzero)
  have hyA : (y : M) ∈ A := Submodule.mem_comap.mp hyA'
  refine mem_pSmulSub_iff.mpr ⟨⟨(y : M), hyA⟩, ?_⟩
  apply Subtype.ext
  have hy' : ((p : ℤ) • (y : M)) = (a : M) := by
    have := congrArg (Subtype.val) hy
    simpa using this
  simpa using hy'

/-! ## The prime-to-`p` reduction -/

/-- The "prime-to-`p`" step: for `G`-stable `ℤ`-sublattices `A ≤ R` with `R/A` finite and
`p`-divisible (`p·(R/A) = ⊤`, equivalently `p ∤ [R:A]`), the invariants of `R/pR` and `A/pA`
agree.  Route: `R = A + pR` gives `R/(A+pR) = 0`, `A ∩ pR = pA`, so `A/pA ≅ R/pR` via the
inclusion and additivity of `ρ` plus `rho_subsingleton` (in `LatticeModp/Infra.lean`) finishes. -/
theorem coprime_reduce {p : ℕ} [NeZero p] {G : Type} [Group G] (ρ : Inv p G)
    (hadd : IsAddInv ρ) {M : Type} [AddCommGroup M] [DistribMulAction G M]
    (A R : Submodule ℤ M) (hAR : A ≤ R)
    (hAG : ∀ (g : G) (m : M), m ∈ A → g • m ∈ A)
    (hRG : ∀ (g : G) (m : M), m ∈ R → g • m ∈ R)
    (hfgA : Module.Finite ℤ ↥A) (hfgR : Module.Finite ℤ ↥R)
    (hfin : Finite (↥R ⧸ Submodule.comap R.subtype A))
    (hdiv : pSmulSub p (↥R ⧸ Submodule.comap R.subtype A) = ⊤) :
    redRho (G := G) ρ M R hRG hfgR = redRho (G := G) ρ M A hAG hfgA := by
  -- the instance packages for the two quotients
  letI hA_dma : DistribMulAction G ↥A := subDMA (G := G) A hAG
  letI hR_dma : DistribMulAction G ↥R := subDMA (G := G) R hRG
  letI hA_mod : Module (ZMod p) (↥A ⧸ pSmulSub p ↥A) :=
    quotZMod p (pSmulSub p ↥A) (fun x => nsmul_mem_pSmulSub x)
  letI hA_qdma : DistribMulAction G (↥A ⧸ pSmulSub p ↥A) :=
    quotDMA (pSmulSub p ↥A) (fun g m hm => pSmulSub_smul_mem hm g)
  letI hA_scc : SMulCommClass G (ZMod p) (↥A ⧸ pSmulSub p ↥A) :=
    quotSCC p (pSmulSub p ↥A) (fun g m hm => pSmulSub_smul_mem hm g)
      (fun x => nsmul_mem_pSmulSub x)
  letI hA_fin : Finite (↥A ⧸ pSmulSub p ↥A) :=
    finite_quot_pSmulSub_of_moduleFinite p (NeZero.ne p)
  letI hR_mod : Module (ZMod p) (↥R ⧸ pSmulSub p ↥R) :=
    quotZMod p (pSmulSub p ↥R) (fun x => nsmul_mem_pSmulSub x)
  letI hR_qdma : DistribMulAction G (↥R ⧸ pSmulSub p ↥R) :=
    quotDMA (pSmulSub p ↥R) (fun g m hm => pSmulSub_smul_mem hm g)
  letI hR_scc : SMulCommClass G (ZMod p) (↥R ⧸ pSmulSub p ↥R) :=
    quotSCC p (pSmulSub p ↥R) (fun g m hm => pSmulSub_smul_mem hm g)
      (fun x => nsmul_mem_pSmulSub x)
  letI hR_fin : Finite (↥R ⧸ pSmulSub p ↥R) :=
    finite_quot_pSmulSub_of_moduleFinite p (NeZero.ne p)
  -- the inclusion `A ↪ R` induces `A/pA → R/pR`
  have hle : pSmulSub p ↥A ≤ Submodule.comap (Submodule.inclusion hAR) (pSmulSub p ↥R) := by
    intro x hx
    rw [Submodule.mem_comap]
    obtain ⟨a, rfl⟩ := mem_pSmulSub_iff.mp hx
    rw [map_zsmul, Submodule.inclusion_apply]
    exact mem_pSmulSub_iff.mpr ⟨⟨a.1, hAR a.2⟩, rfl⟩
  let g : (↥A ⧸ pSmulSub p ↥A) →ₗ[ℤ] (↥R ⧸ pSmulSub p ↥R) :=
    Submodule.mapQ (pSmulSub p ↥A) (pSmulSub p ↥R) (Submodule.inclusion hAR) hle
  have hg_apply : ∀ a : ↥A, g (Submodule.Quotient.mk (p := pSmulSub p ↥A) a)
      = Submodule.Quotient.mk (p := pSmulSub p ↥R) (⟨a.1, hAR a.2⟩ : ↥R) := by
    intro a
    simp only [g, Submodule.mapQ_apply, Submodule.inclusion_apply]
  have hg_surj : Function.Surjective g := by
    intro y
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (pSmulSub p ↥R) y
    obtain ⟨a, y₀, hry⟩ := exists_eq_add_pSmul_of_pdiv p A R hAR hdiv r
    refine ⟨Submodule.Quotient.mk (p := pSmulSub p ↥A) a, ?_⟩
    rw [hg_apply, Submodule.Quotient.eq]
    refine mem_pSmulSub_iff.mpr ⟨-y₀, ?_⟩
    apply Subtype.ext
    show (p : ℤ) • (-(y₀ : M)) = (a : M) - (r : M)
    rw [smul_neg, hry]
    abel
  have hg_inj : Function.Injective g := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (pSmulSub p ↥A) x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective (pSmulSub p ↥A) y
    rw [hg_apply, hg_apply, Submodule.Quotient.eq] at hxy
    rw [Submodule.Quotient.eq]
    have hz : Submodule.inclusion hAR (a - b) ∈ pSmulSub p ↥R := by
      rw [map_sub, Submodule.inclusion_apply, Submodule.inclusion_apply]
      exact hxy
    have hz' : (⟨(a - b).1, hAR (a - b).2⟩ : ↥R) ∈ pSmulSub p ↥R := by
      simpa [Submodule.inclusion_apply] using hz
    exact mem_pSmulSub_of_coe_mem_pSmulSub p A R hAR hfin hdiv (a - b) hz'
  let e : (↥A ⧸ pSmulSub p ↥A) ≃ₗ[ZMod p] (↥R ⧸ pSmulSub p ↥R) :=
    LinearEquiv.ofBijective ((g.toAddMonoidHom).toZModLinearMap p) ⟨hg_inj, hg_surj⟩
  have he : ∀ (γ : G) (x : ↥A ⧸ pSmulSub p ↥A), e (γ • x) = γ • e x := by
    intro γ x
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (pSmulSub p ↥A) x
    change g (γ • Submodule.Quotient.mk (p := pSmulSub p ↥A) a)
      = γ • g (Submodule.Quotient.mk (p := pSmulSub p ↥A) a)
    rw [quotDMA_mk_apply (pSmulSub p ↥A) (fun g m hm => pSmulSub_smul_mem hm g) γ a,
      hg_apply (γ • a), hg_apply a,
      quotDMA_mk_apply (pSmulSub p ↥R) (fun g m hm => pSmulSub_smul_mem hm g) γ
        (⟨a.1, hAR a.2⟩ : ↥R)]
    exact congrArg (Submodule.Quotient.mk (p := pSmulSub p ↥R)) (Subtype.ext rfl)
  have hR : redRho (G := G) ρ M R hRG hfgR = ρ (↥R ⧸ pSmulSub p ↥R) := by
    unfold redRho
    rfl
  have hA : redRho (G := G) ρ M A hAG hfgA = ρ (↥A ⧸ pSmulSub p ↥A) := by
    unfold redRho
    rfl
  rw [hR, hA]
  exact rho_iso ρ hadd e he

end Work.ArtinInduction.LatticeModp
