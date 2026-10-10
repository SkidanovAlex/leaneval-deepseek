import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.isLocConstOn_corestriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Building the corestriction `Cor : H¹(G_K, E) → H¹(G_k, E)` on the level of cocycles

We construct, for a crossed homomorphism `y` on `G_K = K.fixingSubgroup` and a section `sec` of
`res k K`, an explicit `1`-cocycle `x` on all of `G_k` whose restriction to `G_K` is the formal
corestriction `X δ = ∑_{s : Gal(K/k)} s • y(sec(s)⁻¹ δ sec(s))`.

The formula (as in the classical transfer / corestriction) is

  `x σ = ∑_{s : Gal(K/k)} s • y(sec(s)⁻¹ · σ · sec((res k K σ)⁻¹ · s))`.

The argument of `y` is always in `G_K` because its `res k K`-image is
`s⁻¹ (res k K σ) ((res k K σ)⁻¹ s) = 1`.  The cocycle identity is the associativity
`sec(s)⁻¹ στ sec(...) = (sec(s)⁻¹ σ sec(...)) · (sec(...)⁻¹ τ sec(...))` together with
additivity of `y` on `G_K`; the extra reindexing `s ↦ (res k K σ) · s` inside the second sum is
`sum_mulLeft_smul`. -/

/-- Reindexing a finite sum over a finite group along left multiplication. -/
lemma sum_mulLeft_smul {G : Type*} [Group G] [Fintype G] {M : Type*} [AddCommMonoid M]
    [DistribSMul G M] (a : G) (f : G → M) :
    ∑ s, (a * s) • f s = ∑ t, t • f (a⁻¹ * t) := by
  have h := Equiv.sum_comp (Equiv.mulLeft a) (fun t : G => t • f (a⁻¹ * t))
  simpa [Equiv.mulLeft, inv_mul_cancel_left] using h

section Setup

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]

/-- The explicit corestriction cocycle
`x σ = ∑_{s : Gal(K/k)} s • y(sec(s)⁻¹ · σ · sec((res k K σ)⁻¹ · s))`. -/
noncomputable def corCocycle (y : (Ω ≃ₐ[k] Ω) → E)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) : (Ω ≃ₐ[k] Ω) → E :=
  fun σ => ∑ s : K ≃ₐ[k] K, s • y ((sec s)⁻¹ * σ * sec ((res k K σ)⁻¹ * s))

/-- `K.fixingSubgroup` is the kernel of `res k K`. -/
lemma mem_fixingSubgroup_iff_res_eq_one (u : Ω ≃ₐ[k] Ω) :
    res k K u = 1 ↔ u ∈ K.fixingSubgroup := by
  rw [show res k K u = u.restrictNormal K from rfl, AlgEquiv.restrictNormal_eq_one_iff,
    IntermediateField.mem_fixingSubgroup_iff]

/-- The `y`-argument of `corCocycle` lies in `K.fixingSubgroup`. -/
lemma corCocycle_arg_mem (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω))
    (hsec : ∀ s, res k K (sec s) = s) (σ : Ω ≃ₐ[k] Ω) (s : K ≃ₐ[k] K) :
    (sec s)⁻¹ * σ * sec ((res k K σ)⁻¹ * s) ∈ K.fixingSubgroup := by
  rw [← mem_fixingSubgroup_iff_res_eq_one, map_mul, map_mul, map_inv, hsec, hsec]
  group

/-- `corCocycle` is a `1`-cocycle for the action of `Gal(K/k)` on `E` pulled back along
`res k K`. -/
lemma corCocycle_isCocycle (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, res k K (sec s) = s) :
    IsCocycleOn (res k K) ⊤ (corCocycle k Ω K E y sec) := by
  intro σ _ τ _
  show corCocycle k Ω K E y sec (σ * τ)
      = corCocycle k Ω K E y sec σ + res k K σ • corCocycle k Ω K E y sec τ
  simp only [corCocycle]
  have hstep : ∀ s : K ≃ₐ[k] K,
      y ((sec s)⁻¹ * (σ * τ) * sec ((res k K (σ * τ))⁻¹ * s))
      = y ((sec s)⁻¹ * σ * sec ((res k K σ)⁻¹ * s))
        + y ((sec ((res k K σ)⁻¹ * s))⁻¹ * τ
            * sec ((res k K τ)⁻¹ * ((res k K σ)⁻¹ * s))) := by
    intro s
    have hr : (res k K (σ * τ))⁻¹ * s = (res k K τ)⁻¹ * ((res k K σ)⁻¹ * s) := by
      rw [map_mul, mul_inv_rev, mul_assoc]
    have hmul : (sec s)⁻¹ * (σ * τ) * sec ((res k K (σ * τ))⁻¹ * s)
        = ((sec s)⁻¹ * σ * sec ((res k K σ)⁻¹ * s))
          * ((sec ((res k K σ)⁻¹ * s))⁻¹ * τ
             * sec ((res k K τ)⁻¹ * ((res k K σ)⁻¹ * s))) := by
      rw [hr]; group
    rw [hmul]
    exact hy _ (corCocycle_arg_mem k Ω K sec hsec σ s) _
      (corCocycle_arg_mem k Ω K sec hsec τ _)
  have hkey : (∑ s : K ≃ₐ[k] K, s • y ((sec s)⁻¹ * (σ * τ)
        * sec ((res k K (σ * τ))⁻¹ * s)))
      = ∑ s : K ≃ₐ[k] K, s • (y ((sec s)⁻¹ * σ * sec ((res k K σ)⁻¹ * s))
          + y ((sec ((res k K σ)⁻¹ * s))⁻¹ * τ
              * sec ((res k K τ)⁻¹ * ((res k K σ)⁻¹ * s)))) :=
    Finset.sum_congr rfl (fun s _ => by rw [hstep s])
  rw [hkey]
  simp only [smul_add]
  rw [Finset.sum_add_distrib]
  have hgoal : (∑ s : K ≃ₐ[k] K, s • y ((sec ((res k K σ)⁻¹ * s))⁻¹ * τ
        * sec ((res k K τ)⁻¹ * ((res k K σ)⁻¹ * s))))
      = (res k K σ) • (∑ t : K ≃ₐ[k] K, t • y ((sec t)⁻¹ * τ
          * sec ((res k K τ)⁻¹ * t))) := by
    rw [Finset.smul_sum]
    rw [← sum_mulLeft_smul (res k K σ)
      (fun t : K ≃ₐ[k] K => y ((sec t)⁻¹ * τ * sec ((res k K τ)⁻¹ * t)))]
    exact Finset.sum_congr rfl (fun s _ => by rw [mul_smul])
  rw [hgoal]

/-- `corCocycle` is locally constant on all of `G_k`. -/
lemma corCocycle_isLocConstOn (y : (Ω ≃ₐ[k] Ω) → E)
    (hyc : IsLocConstOn K.fixingSubgroup y)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, res k K (sec s) = s) :
    IsLocConstOn ⊤ (corCocycle k Ω K E y sec) := by
  obtain ⟨U₀, hU₀open, hU₀prop⟩ := hyc
  refine ⟨K.fixingSubgroup ⊓ (⨅ t : K ≃ₐ[k] K, conjSubgroup (sec t) U₀), ?_, ?_⟩
  · rw [Subgroup.coe_inf]
    refine IsOpen.inter (IntermediateField.fixingSubgroup_isOpen K) ?_
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite (fun t => isOpen_conjSubgroup (sec t) U₀ hU₀open)
  · intro σ _ u hu _
    show corCocycle k Ω K E y sec (σ * u) = corCocycle k Ω K E y sec σ
    simp only [corCocycle]
    have huH : u ∈ K.fixingSubgroup := hu.1
    have huconj : ∀ t : K ≃ₐ[k] K, (sec t)⁻¹ * u * sec t ∈ U₀ := by
      intro t
      exact mem_conjSubgroup.mp (Subgroup.mem_iInf.mp hu.2 t)
    have hru : res k K u = 1 := (mem_fixingSubgroup_iff_res_eq_one k Ω K u).mpr huH
    have hterm : ∀ s : K ≃ₐ[k] K,
        y ((sec s)⁻¹ * (σ * u) * sec ((res k K (σ * u))⁻¹ * s))
        = y ((sec s)⁻¹ * σ * sec ((res k K σ)⁻¹ * s)) := by
      intro s
      rw [map_mul, hru, mul_one]
      have hmul : (sec s)⁻¹ * (σ * u) * sec ((res k K σ)⁻¹ * s)
          = ((sec s)⁻¹ * σ * sec ((res k K σ)⁻¹ * s))
            * ((sec ((res k K σ)⁻¹ * s))⁻¹ * u * sec ((res k K σ)⁻¹ * s)) := by
        group
      rw [hmul]
      have hA : (sec s)⁻¹ * σ * sec ((res k K σ)⁻¹ * s) ∈ K.fixingSubgroup :=
        corCocycle_arg_mem k Ω K sec hsec σ s
      have hz : (sec ((res k K σ)⁻¹ * s))⁻¹ * u * sec ((res k K σ)⁻¹ * s)
          ∈ K.fixingSubgroup := by
        rw [← mem_fixingSubgroup_iff_res_eq_one, map_mul, map_mul, map_inv, hsec, hru]
        group
      exact hU₀prop _ hA _ (huconj ((res k K σ)⁻¹ * s)) hz
    exact Finset.sum_congr rfl (fun s _ => by rw [hterm s])

/-- On `G_K = K.fixingSubgroup`, `corCocycle` is the formal corestriction
`X δ = ∑_{s : Gal(K/k)} s • y(sec(s)⁻¹ δ sec(s))`. -/
lemma corCocycle_restrict (y : (Ω ≃ₐ[k] Ω) → E)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) :
    ∀ δ ∈ K.fixingSubgroup, corCocycle k Ω K E y sec δ
      = ∑ s : K ≃ₐ[k] K, s • y ((sec s)⁻¹ * δ * sec s) := by
  intro δ hδ
  have h1 : res k K δ = 1 := (mem_fixingSubgroup_iff_res_eq_one k Ω K δ).mpr hδ
  simp only [corCocycle]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [h1, inv_one, one_mul]

end Setup

/-- **Corestriction of a `1`-cocycle along `G_K ◁ G_k`.**

Given a crossed homomorphism `y` on `G_K = K.fixingSubgroup` (`hy`; the action of `G_K` on `E` is
the restriction of the action of `Gal(K/k)`, so `G_K` acts trivially and `y` is additive there)
which is locally constant (`hyc`), and a section `sec` of `res k K`, there is a continuous crossed
homomorphism `x` on all of `G_k` whose restriction to `G_K` is the formal corestriction
`X δ = ∑_{s : Gal(K/k)} s • y(sec(s)⁻¹ * δ * sec(s))`.

This is the classical corestriction `Cor : H¹(G_K, E) → H¹(G_k, E)`.  A concrete cocycle is
`x δ = ∑_{i} g_i • y(g_{τ(i)}⁻¹ * δ * g_i)`, where `g_i = sec i` runs over the left cosets of
`G_K` and `g_{τ(i)} = sec ((res k K δ)⁻¹ * i)`, so that `g_{τ(i)} G_K = (res k K δ)⁻¹ (g_i G_K)` and hence
`g_{τ(i)}⁻¹ * δ * g_i ∈ G_K` (its `res k K`-image is
`((resδ)⁻¹ i)⁻¹ (resδ) i = 1`).  Note: the *other* pairing,
`g_{σ(i)} = sec ((res k K δ) * i)`, is **not** a cocycle.  For `δ ∈ G_K` the permutation `τ` is the
identity and this is `X δ` (because `g_i • e = (res k K g_i) • e = i • e`). -/
theorem exists_corestriction (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : IsLocConstOn K.fixingSubgroup y)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, res k K (sec s) = s) :
    ∃ x : (Ω ≃ₐ[k] Ω) → E,
      IsCocycleOn (res k K) ⊤ x ∧ IsLocConstOn ⊤ x ∧
      ∀ δ ∈ K.fixingSubgroup, x δ = ∑ s : K ≃ₐ[k] K, s • y ((sec s)⁻¹ * δ * sec s) :=
  ⟨corCocycle k Ω K E y sec,
    corCocycle_isCocycle k Ω K E y hy sec hsec,
    corCocycle_isLocConstOn k Ω K E y hyc sec hsec,
    corCocycle_restrict k Ω K E y sec⟩

end Work.SSGRoute
