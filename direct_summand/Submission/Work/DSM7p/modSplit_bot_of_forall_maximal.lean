import Mathlib
import Submission.Work.DSM7p.Basic
import Submission.Work.DSM7p.Alg.smul_top_prod
import Submission.Work.DSM7p.Free.exists_comp_eq_of_surjective_of_free
import Submission.Work.DSM7p.Free.mem_smul_top_of_forall_apply_mem
import Submission.Work.DSM7p.Krull.mem_of_forall_mem_sup_smul_pow

/-!
# DSM7p — from splittings modulo every power of the maximal ideal to an honest splitting

The `lim¹`/Krull step at the end of Bhatt's §4 proof of the direct summand theorem
(`α₀ / p^m = 0` for all `m` implies `α₀ = 0`), in the model-theoretic form used by `DSM7p`.

Let `A` be a Noetherian local ring with maximal ideal `m`, `P` a bounded-above complex of finite
free `A`-modules and `ε : A → P⁰` a coaugmentation.  Assume that for every `k` the unit splits
modulo `m ^ k` with value `1`; the goal is the honest splitting
`ModSplit P ε (RingHom.id A) ⊥ 1`.

In the `A`-linear (adjoint) form `DSAM3.ModSplitA`, the hypothesis gives for every `k` a functional
`t_k : P⁰ →ₗ[A] A ⧸ m ^ k` killing `d⁻¹ : P⁻¹ → P⁰` and sending `ε 1` to `1`.  Since `P⁰` is free,
each `t_k` lifts to an honest functional `g_k : P⁰ →ₗ[A] A` whose restriction to `im d⁻¹` takes
values in `m ^ k` and whose value at `ε 1` is `1` modulo `m ^ k`
(`exists_functional_forall_mem_maximalIdeal` below).

Consider the linear map `Φ : Hom_A(P⁰, A) → Hom_A(P⁻¹, A) × A`, `u ↦ (u ∘ d⁻¹, u (ε 1))`.  Its
image is the set of pairs arising from functionals; a functional killing `d⁻¹` with value `1` at
`ε 1` is exactly a preimage of the fixed point `x₀ := (0, 1)`.  Each `g_k` exhibits
`x₀ - Φ(g_k) = (-(g_k ∘ d⁻¹), 1 - g_k(ε 1)) ∈ m ^ k • ⊤`, so `x₀ ∈ range Φ ⊔ m ^ k • ⊤` for every
`k`; the two components lie in `m ^ k • ⊤` because `P⁻¹` is finite free
(`Work.DSM7p.Free.mem_smul_top_of_forall_apply_mem`) and because `m ^ k • ⊤` of a product is the
product of the `m ^ k • ⊤`'s (`Work.DSM7p.Alg.smul_top_prod`).  The target
`Hom_A(P⁻¹, A) × A` is finitely generated, so Krull's intersection theorem for finitely generated
modules over a Noetherian local ring — `Work.DSM7p.Krull.mem_of_forall_mem_sup_smul_pow`, from
`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` — yields `x₀ ∈ range Φ`, i.e. the desired functional.
No completeness of `A` is used, only Krull.
-/

set_option linter.style.haveILetI false
set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct

namespace Work.DSM7p

universe a

/-- **Unpacking the hypothesis `mod m ^ k`.**  For every `k`, a splitting of the coaugmentation
modulo `m ^ k` with value `1` lifts, along the (free) module `P⁰`, to an honest functional
`g : P⁰ →ₗ[A] A` whose restriction to `im d⁻¹` takes values in `m ^ k` and whose value at `ε 1`
is `1` modulo `m ^ k`. -/
theorem exists_functional_forall_mem_maximalIdeal {A : Type a} [CommRing A] [IsLocalRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : DSMap.Mix.IsBddFinFree P)
    (h : ∀ k : ℕ, DSMap.Mix.ModSplit P ε (RingHom.id A) ((IsLocalRing.maximalIdeal A) ^ k) 1)
    (k : ℕ) :
    ∃ g : P.X 0 →ₗ[A] A,
      (∀ x : P.X (-1), g ((P.d (-1) 0).hom x) ∈ (IsLocalRing.maximalIdeal A) ^ k) ∧
      (1 - g (ε.hom 1) ∈ (IsLocalRing.maximalIdeal A) ^ k) := by
  haveI : Module.Free A (P.X 0) := (hP.1 0).1
  -- the `A`-linear form of the hypothesis: a functional `t` into `A ⧸ m ^ k`
  obtain ⟨t, ht1, ht2⟩ :=
    (DSAM3.modSplit_iff_ModSplitA P ε (RingHom.id A) ((IsLocalRing.maximalIdeal A) ^ k) 1).mp
      (h k)
  let p : Submodule A A := (((IsLocalRing.maximalIdeal A) ^ k : Ideal A) : Submodule A A)
  -- lift `t` to an honest functional along the surjection `A → A ⧸ m ^ k` (`P⁰` is free)
  obtain ⟨g, hg⟩ := Work.DSM7p.Free.exists_comp_eq_of_surjective_of_free
    (p := Submodule.mkQ p) (Submodule.mkQ_surjective p) t
  refine ⟨g, ?_, ?_⟩
  · intro x
    have h0 : t ((P.d (-1) 0).hom x) = 0 := by
      have := LinearMap.congr_fun ht1 x
      simpa using this
    have hz : p.mkQ (g ((P.d (-1) 0).hom x)) = 0 := by
      rw [← LinearMap.comp_apply, hg, h0]
    exact (Submodule.Quotient.mk_eq_zero p).mp (by simpa [Submodule.mkQ_apply] using hz)
  · have ht2' : t (ε.hom 1) = p.mkQ (1 : A) := by
      rw [ht2, Submodule.mkQ_apply]
      rfl
    have hz : p.mkQ (g (ε.hom 1)) = p.mkQ (1 : A) := by
      rw [← LinearMap.comp_apply, hg, ht2']
    have hmem := (Submodule.Quotient.eq p).mp
      (by simpa only [Submodule.mkQ_apply] using hz)
    simpa using neg_mem hmem

/-- **Lifting from `mod m^k` to the honest splitting.**  Let `A` be a Noetherian local ring, `P` a bounded-above complex of finite free `A`-modules with coaugmentation `ε : A → P⁰`.  If the coaugmentation splits modulo every power of the maximal ideal (with value `1`), then it splits honestly (`ModSplit P ε (RingHom.id A) ⊥ 1`).

Mathematically this is the `lim¹`/Krull step at the end of Bhatt's §4 proof (`α₀/p^m = 0` for all `m` implies `α₀ = 0`).  Formally: the set of functionals `t : P⁰ →ₗ[A] A` killing `d⁻¹` with `t (ε 1) = 1` is the fibre of the linear map `Φ : Hom_A(P⁰,A) → Hom_A(P⁻¹,A) × A`, `t ↦ (t ∘ d⁻¹, t (ε 1))` over `(0,1)`; the hypothesis gives, for every `k`, a point mapping into `m^k • ⊤` of `(0,1)`, so the image of `(0,1)` in the finitely generated module `(Hom_A(P⁻¹,A) × A)/range Φ` lies in `⋂_k m^k • ⊤ = ⊥` by Krull's intersection result for finitely generated modules over a Noetherian local ring (`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`).  No completeness of `A` is used, only Krull. -/
theorem modSplit_bot_of_forall_maximal {A : Type a} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : DSMap.Mix.IsBddFinFree P)
    (h : ∀ k : ℕ, DSMap.Mix.ModSplit P ε (RingHom.id A) ((IsLocalRing.maximalIdeal A) ^ k) 1) :
    DSMap.Mix.ModSplit P ε (RingHom.id A) ⊥ 1 := by
  haveI : Module.Free A (P.X (-1)) := (hP.1 (-1)).1
  haveI : Module.Finite A (P.X (-1)) := (hP.1 (-1)).2
  haveI : Module.Finite A ((P.X (-1) →ₗ[A] A) × A) := inferInstance
  -- the map whose fibre over `(0,1)` is the set of splitting functionals
  let Φ : (P.X 0 →ₗ[A] A) →ₗ[A] (P.X (-1) →ₗ[A] A) × A :=
    LinearMap.prod (LinearMap.lcomp A A (P.d (-1) 0).hom) (LinearMap.applyₗ (ε.hom 1))
  have hΦ : ∀ u : P.X 0 →ₗ[A] A, Φ u = (u.comp (P.d (-1) 0).hom, u (ε.hom 1)) := fun _ => rfl
  -- `(0,1)` lies in `range Φ ⊔ m ^ k • ⊤` for every `k`, by the `mod m ^ k` hypothesis
  have hmem : ((0 : P.X (-1) →ₗ[A] A), (1 : A)) ∈ LinearMap.range Φ := by
    refine Work.DSM7p.Krull.mem_of_forall_mem_sup_smul_pow (LinearMap.range Φ) (fun k => ?_)
    obtain ⟨g, hg1, hg2⟩ := exists_functional_forall_mem_maximalIdeal P ε hP h k
    -- the two components of `(0,1) - Φ g` are divisible by `m ^ k`
    have hfst : (-(g.comp (P.d (-1) 0).hom)) ∈ ((IsLocalRing.maximalIdeal A) ^ k • ⊤ :
        Submodule A (P.X (-1) →ₗ[A] A)) := by
      refine Work.DSM7p.Free.mem_smul_top_of_forall_apply_mem ((IsLocalRing.maximalIdeal A) ^ k)
        (-(g.comp (P.d (-1) 0).hom)) (fun x => ?_)
      simp only [LinearMap.neg_apply, LinearMap.comp_apply]
      exact neg_mem (hg1 x)
    have hsnd : (1 - g (ε.hom 1)) ∈
        ((IsLocalRing.maximalIdeal A) ^ k • ⊤ : Submodule A A) := by
      have := Submodule.smul_mem_smul hg2 (Submodule.mem_top : (1 : A) ∈ (⊤ : Submodule A A))
      simpa [smul_eq_mul] using this
    have hsub : ((0 : P.X (-1) →ₗ[A] A), (1 : A)) - Φ g ∈
        ((IsLocalRing.maximalIdeal A) ^ k • ⊤ :
          Submodule A ((P.X (-1) →ₗ[A] A) × A)) := by
      rw [hΦ g, Work.DSM7p.Alg.smul_top_prod]
      exact Submodule.mem_prod.mpr ⟨by simpa using hfst, by simpa using hsnd⟩
    exact Submodule.mem_sup.mpr ⟨Φ g, LinearMap.mem_range_self Φ g,
      ((0 : P.X (-1) →ₗ[A] A), (1 : A)) - Φ g, hsub, by abel⟩
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hmem
  -- `u` kills `d⁻¹` and sends `ε 1` to `1`
  have hu1 : u.comp (P.d (-1) 0).hom = 0 := by
    have := congrArg Prod.fst hu
    simpa [hΦ u] using this
  have hu2 : u (ε.hom 1) = 1 := by
    have := congrArg Prod.snd hu
    simpa [hΦ u] using this
  -- assemble the `A`-linear splitting modulo `⊥`
  rw [DSAM3.modSplit_iff_ModSplitA]
  refine ⟨(Submodule.mkQ (⊥ : Submodule A A)).comp u, ?_, ?_⟩
  · rw [LinearMap.comp_assoc, hu1, LinearMap.comp_zero]
  · rw [LinearMap.comp_apply, hu2]
    rfl

end Work.DSM7p
