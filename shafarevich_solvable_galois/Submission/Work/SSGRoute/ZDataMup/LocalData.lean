import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZDataMup.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-`K` local-data spaces of the realisation gate, and the linear algebra of maximality

Companion of `Submission/Work/SSGRoute/ZDataMup/tatePoitou_h1_realisation.lean`, holding the
*sorry-free* layer of the lane that proves the Tate--Poitou degree-`1` realisation gate.

## What is here

* the formal preliminaries the gate consumes: `res` is trivial on `G_K`, so the `1`-coboundaries on
  a level-`K` local group `H ≤ G_K` are exactly the zero function
  (`isCoboundaryOn_iff_eqOn_zero`) and the gate's third clause is pointwise agreement
  (`exists_realisation_iff_pointwise`); the local pairings depend only on the restrictions of the
  cocycles (`pair_congr_of_eqOn_left/right`) and are non-degenerate on the locally constant
  cocycles by `perfect` (`pair_nondegenerate_of_perfect`);
* the **spaces of the lane**: the locally constant `H`-cocycles `localCocycle`, the level-`K`
  Selmer space `selmerSpace T` (locally constant cocycles on `G_K` vanishing on the inertia of the
  finite places outside the conjugates of `T`), the local-data space `localDataSpace T` (tuples of
  locally constant cocycles on the groups `decomp k A ⊓ G_K`), the localisation
  `localisationMap` and its image `localImage` (the `W_T` of the gate);
* the **easy half of maximality**: `sum_pair_selmer_eq_zero` -- for a pairing satisfying the product
  formula, two classes of the Selmer space pair trivially at `T` (`W_T ⊆ W_T^⊥`);
* the **linear algebra of the other half**: `orthogonal_eq_of_ker_eq_bot_of_isotropic_of_finrank_le`
  -- for a bilinear form whose left radical is trivial, an isotropic subspace `W` with
  `finrank V ≤ 2 * finrank W` equals its orthogonal complement.  So *everything* that is missing for
  the gate is the arithmetic *counting* input `finrank V ≤ 2 * finrank W_T` (the Euler
  characteristic / counting identity of the level-`K` localisation,
  `ZSplit/levelK_counting_identity`, `PT.pt_selmer_counting_identity`), plus the identification of
  the left radical with `⊥` from `perfect` in the product form
  (`Work.SSGRoute.ZDataMup.sum_pair_eq_zero_imp_eqOn_localGroups`, filed).

## Two corrections found while stating the lane (important for the next stretch)

* **The radical of the sum pairing is not `⊥`.**  The pairings are blind to the values *outside* the
  local groups, so the radical of the sum pairing on `localDataSpace K T` contains every tuple
  vanishing on the local groups; the correct statement is that the radical is *contained* in
  `productVanish K T ⊓ localDataSpace K T` (`Work.SSGRoute.ZDataMup.sum_pair_eq_zero_impEqZero`),
  and the counting has to be taken on the *quotient* `localDataSpace K T ⧸ localVanish K T`, which
  is the product of the local `H¹`s `H¹(decomp k A ⊓ G_K, ZMod p)`.  The quotient step is the
  general bilinear-form statement `Work.SSGRoute.ZDataMup.orthogonal_le_sup_of_ker_le`.
* **Chirality of `horth`.**  `IsOrthogonalToDual` pairs `f A` in the *first* argument, while
  `LinearMap.BilinForm.orthogonal` is the *right* annihilator.  The assembly therefore runs the
  quotient step on the *transposed* form `B.flip` (equivalently: `horth` places the datum in the
  left annihilator of `W_T`, which is `(B.flip).orthogonal W_T`), using the two radical facts
  `B.ker ≤ localVanish`, `localVanish ≤ B.orthogonal ⊤` and their transposes.

## The exact remaining rungs of the lane

1. `sum_pair_eq_zero_impEqZero` (non-degeneracy of the sum pairing on `localDataSpace T`, from
   `perfect`; the product version of `pair_nondegenerate_of_perfect`);
2. the *counting identity* for the level-`K` localisation: `finrank (localDataSpace T)` and
   `finrank (localImage T)` satisfy `finrank (localDataSpace T) ≤ 2 * finrank (localImage T)`
   (arithmetic; the local-duality/Poitou--Tate lane);
3. the assembly: `horth` puts the local datum into the orthogonal complement of `localImage T`,
   so 1 + 2 + `orthogonal_eq_of_ker_eq_bot_of_isotropic_of_finrank_le` give `z` (mine to write).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataMup

/-- The restriction `G_k →* Gal(K/k)` (`SSGRoute.res k K`) is trivial on `G_K = K.fixingSubgroup`:
the fixing subgroup of `K` is exactly the kernel of the restriction. -/
theorem res_eq_one_of_mem_fixingSubgroup {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K] {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) :
    SSGRoute.res k K σ = 1 := by
  show (AlgEquiv.restrictNormalHom K) σ = 1
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
  exact hσ

/-- **A `1`-coboundary on a level-`K` local group is the zero function.**  For `H ≤ G_K` the
coboundary `g ↦ res g • m - m` is constantly `m - m = 0`, because `res` is trivial on `G_K`; hence
a function on `H` is a coboundary precisely when it vanishes on `H`.  In particular the local
cohomology of `H` is the space of locally constant `H`-cocycles itself (no quotient by
coboundaries). -/
theorem isCoboundaryOn_iff_eqOn_zero {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    {H : Subgroup (Ω ≃ₐ[k] Ω)} (hH : H ≤ K.fixingSubgroup) (f : (Ω ≃ₐ[k] Ω) → ZMod p) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H f ↔ ∀ g ∈ H, f g = 0 := by
  constructor
  · rintro ⟨m, hm⟩ g hg
    have hres : SSGRoute.res k K g = 1 := res_eq_one_of_mem_fixingSubgroup (hH hg)
    rw [hm g hg, hres, one_smul, sub_self]
  · intro h
    exact ⟨0, fun g hg => by rw [h g hg]; simp⟩

/-- The third clause of the conclusion of the realisation, rewritten: `z - f` is a coboundary on a
level-`K` local group `H` if and only if `z` and `f` agree pointwise on `H`. -/
theorem sub_isCoboundaryOn_iff_eqOn {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    {H : Subgroup (Ω ≃ₐ[k] Ω)} (hH : H ≤ K.fixingSubgroup) (z f : (Ω ≃ₐ[k] Ω) → ZMod p) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H (fun σ => z σ - f σ) ↔
      ∀ g ∈ H, z g = f g := by
  rw [isCoboundaryOn_iff_eqOn_zero (p := p) hH]
  exact ⟨fun h g hg => sub_eq_zero.mp (h g hg), fun h g hg => sub_eq_zero.mpr (h g hg)⟩

open _root_.SSGRoute

/-- The difference of two locally constant `H`-cocycles is a locally constant `H`-cocycle. -/
theorem isCocycleOn_sub {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    {H : Subgroup (Ω ≃ₐ[k] Ω)} {b b' : (Ω ≃ₐ[k] Ω) → ZMod p}
    (hb : IsCocycleOn (res k K) H b ∧ IsLocConstOn H b)
    (hb' : IsCocycleOn (res k K) H b' ∧ IsLocConstOn H b') :
    IsCocycleOn (res k K) H (fun g => b g - b' g) ∧
      IsLocConstOn H (fun g => b g - b' g) := by
  obtain ⟨U, hU, hUc⟩ := hb.2
  obtain ⟨U', hU', hU'c⟩ := hb'.2
  refine ⟨?_, ⟨U ⊓ U', ?_, ?_⟩⟩
  · intro g hg h hh
    have h1 := hb.1 g hg h hh
    have h2 := hb'.1 g hg h hh
    show b (g * h) - b' (g * h) = (b g - b' g) + res k K g • (b h - b' h)
    rw [h1, h2, smul_sub]
    abel
  · simpa [Subgroup.coe_inf] using hU.inter hU'
  · intro g hg u hu hmem
    have hgu : u ∈ U := (Subgroup.mem_inf.mp hu).1
    have hgu' : u ∈ U' := (Subgroup.mem_inf.mp hu).2
    show b (g * u) - b' (g * u) = b g - b' g
    rw [hUc g hg u hgu hmem, hU'c g hg u hgu' hmem]

/-- **The local pairings depend only on the restrictions of the cocycles to the local group.**  If
`b` and `b'` are locally constant `H`-cocycles agreeing on `H`, then `b - b'` is a coboundary on
`H`, so by additivity and vanishing on coboundaries the pairing is unchanged in the second
variable.  Hence `horth` is a statement about *localised* data. -/
theorem pair_congr_of_eqOn_right {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p}
    (hpair : IsLocalTateSystem p k Ω K pair) {H : Subgroup (Ω ≃ₐ[k] Ω)}
    (hH : ∃ A : ValuationSubring Ω, IsFinPlace k A ∧ H = decomp k A ⊓ K.fixingSubgroup)
    {a b b' : (Ω ≃ₐ[k] Ω) → ZMod p}
    (ha : IsCocycleOn (res k K) H a ∧ IsLocConstOn H a)
    (hb : IsCocycleOn (res k K) H b ∧ IsLocConstOn H b)
    (hb' : IsCocycleOn (res k K) H b' ∧ IsLocConstOn H b')
    (hbb' : ∀ g ∈ H, b g = b' g) : pair H a b = pair H a b' := by
  have hle : H ≤ K.fixingSubgroup := by
    obtain ⟨A, -, rfl⟩ := hH
    exact inf_le_right
  have hsub := isCocycleOn_sub (p := p) hb hb'
  have hzero : ∀ g ∈ H, (fun g => b g - b' g) g = 0 := fun g hg => sub_eq_zero.mpr (hbb' g hg)
  have hcob : IsCoboundaryOn (res k K) H (fun g => b g - b' g) :=
    (isCoboundaryOn_iff_eqOn_zero (p := p) hle _).mpr hzero
  have hvan : pair H a (fun g => b g - b' g) = 0 :=
    hpair.vanishes_coboundary H hH a _ ha hsub (Or.inr hcob)
  have hadd : pair H a ((fun g => b g - b' g) + b') =
      pair H a (fun g => b g - b' g) + pair H a b' :=
    hpair.additive_right H hH a _ _ ha hsub hb'
  have hfun : (fun g => b g - b' g) + b' = b := by
    funext g; simp [Pi.add_apply, sub_add_cancel]
  rw [← hfun, hadd, hvan, zero_add]

/-- The first-variable version of `pair_congr_of_eqOn_right`. -/
theorem pair_congr_of_eqOn_left {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p}
    (hpair : IsLocalTateSystem p k Ω K pair) {H : Subgroup (Ω ≃ₐ[k] Ω)}
    (hH : ∃ A : ValuationSubring Ω, IsFinPlace k A ∧ H = decomp k A ⊓ K.fixingSubgroup)
    {a a' b : (Ω ≃ₐ[k] Ω) → ZMod p}
    (ha : IsCocycleOn (res k K) H a ∧ IsLocConstOn H a)
    (ha' : IsCocycleOn (res k K) H a' ∧ IsLocConstOn H a')
    (hb : IsCocycleOn (res k K) H b ∧ IsLocConstOn H b)
    (haa' : ∀ g ∈ H, a g = a' g) : pair H a b = pair H a' b := by
  have hle : H ≤ K.fixingSubgroup := by
    obtain ⟨A, -, rfl⟩ := hH
    exact inf_le_right
  have hsub := isCocycleOn_sub (p := p) ha ha'
  have hzero : ∀ g ∈ H, (fun g => a g - a' g) g = 0 := fun g hg => sub_eq_zero.mpr (haa' g hg)
  have hcob : IsCoboundaryOn (res k K) H (fun g => a g - a' g) :=
    (isCoboundaryOn_iff_eqOn_zero (p := p) hle _).mpr hzero
  have hvan : pair H (fun g => a g - a' g) b = 0 :=
    hpair.vanishes_coboundary H hH _ b hsub hb (Or.inl hcob)
  have hadd : pair H ((fun g => a g - a' g) + a') b =
      pair H (fun g => a g - a' g) b + pair H a' b :=
    hpair.additive_left H hH _ _ b hsub ha' hb
  have hfun : (fun g => a g - a' g) + a' = a := by
    funext g; simp [Pi.add_apply, sub_add_cancel]
  rw [← hfun, hadd, hvan, zero_add]

/-- **The locally constant `H`-cocycles form a `ZMod p`-submodule** of the space of all functions
`G_k → ZMod p`: the cocycle condition is linear, and local constancy is preserved by sums, scalar
multiples and `0`.  (The scalar branch uses the `SMulCommClass` hypothesis: the action of `G_k` is
`ZMod p`-linear.)  This is the closure data that packages the local cocycle spaces on which the
local pairings of `IsLocalTateSystem` live, and in particular it is what an argument by linear
algebra (bilinearity, non-degeneracy, the annihilator of the localisation image) consumes. -/
theorem localCocycle_submodule {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] (H : Subgroup (Ω ≃ₐ[k] Ω))
    (hH : H ≤ K.fixingSubgroup) :
    (∀ a b : (Ω ≃ₐ[k] Ω) → ZMod p,
        IsCocycleOn (res k K) H a → IsLocConstOn H a →
        IsCocycleOn (res k K) H b → IsLocConstOn H b →
        IsCocycleOn (res k K) H (a + b) ∧ IsLocConstOn H (a + b)) ∧
      (∀ (c : ZMod p) (a : (Ω ≃ₐ[k] Ω) → ZMod p),
        IsCocycleOn (res k K) H a → IsLocConstOn H a →
        IsCocycleOn (res k K) H (fun g => c • a g) ∧
          IsLocConstOn H (fun g => c • a g)) ∧
      IsCocycleOn (res k K) H (0 : (Ω ≃ₐ[k] Ω) → ZMod p) ∧
        IsLocConstOn H (0 : (Ω ≃ₐ[k] Ω) → ZMod p) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b ha1 ha2 hb1 hb2
    obtain ⟨U, hU, hUc⟩ := ha2
    obtain ⟨U', hU', hU'c⟩ := hb2
    refine ⟨?_, ⟨U ⊓ U', ?_, ?_⟩⟩
    · intro g hg h hh
      show a (g * h) + b (g * h) = (a g + b g) + res k K g • (a h + b h)
      rw [ha1 g hg h hh, hb1 g hg h hh, smul_add]
      abel
    · simpa [Subgroup.coe_inf] using hU.inter hU'
    · intro g hg u hu hmem
      have hgu : u ∈ U := (Subgroup.mem_inf.mp hu).1
      have hgu' : u ∈ U' := (Subgroup.mem_inf.mp hu).2
      show a (g * u) + b (g * u) = a g + b g
      rw [hUc g hg u hgu hmem, hU'c g hg u hgu' hmem]
  · intro c a ha1 ha2
    obtain ⟨U, hU, hUc⟩ := ha2
    refine ⟨?_, ⟨U, hU, ?_⟩⟩
    · intro g hg h hh
      show c • a (g * h) = c • a g + res k K g • (c • a h)
      rw [ha1 g hg h hh, smul_add, SMulCommClass.smul_comm (res k K g) c (a h)]
    · intro g hg u hu hmem
      show c • a (g * u) = c • a g
      rw [hUc g hg u hu hmem]
  · exact fun g hg h hh => by simp
  · exact ⟨⊤, isOpen_univ, fun g hg u hu hmem => rfl⟩

/-- **The local pairings are non-degenerate on the locally constant cocycles.**  This is the
`perfect` field of `IsLocalTateSystem` in the form in which the reduction of the realisation gate
consumes it: a locally constant `H`-cocycle (`H = decomp k A ⊓ G_K` a level-`K` local group) that
pairs trivially against *every* locally constant `H`-cocycle is a coboundary on `H`, and since a
coboundary on a subgroup of `G_K` is the zero function
(`isCoboundaryOn_iff_eqOn_zero`), it *vanishes* on `H`.  Consequently the pairing only depends on
the localised data and its radical on the local cocycle space is trivial. -/
theorem pair_nondegenerate_of_perfect {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p}
    (hpair : IsLocalTateSystem p k Ω K pair) {H : Subgroup (Ω ≃ₐ[k] Ω)}
    (hH : ∃ A : ValuationSubring Ω, IsFinPlace k A ∧ H = decomp k A ⊓ K.fixingSubgroup)
    {a : (Ω ≃ₐ[k] Ω) → ZMod p}
    (ha : IsCocycleOn (res k K) H a ∧ IsLocConstOn H a)
    (horth : ∀ b : (Ω ≃ₐ[k] Ω) → ZMod p,
      IsCocycleOn (res k K) H b → IsLocConstOn H b → pair H a b = 0) :
    ∀ g ∈ H, a g = 0 := by
  have hcob : IsCoboundaryOn (res k K) H a :=
    hpair.perfect H hH a ha (fun b hb => horth b hb.1 hb.2)
  have hle : H ≤ K.fixingSubgroup := by
    obtain ⟨A, -, rfl⟩ := hH
    exact inf_le_right
  exact (isCoboundaryOn_iff_eqOn_zero (p := p) hle a).mp hcob

/-- **The realisation gate, in pointwise form.**  The conclusion of
`Work.SSGRoute.ZDataMup.tatePoitou_h1_realisation` is *equivalent* to the existence of a global
cocycle `z` on `G_K` which is locally constant, agrees pointwise with the local datum `f A` on every
level-`K` local group `decomp k A ⊓ K.fixingSubgroup` (`A ∈ T`), and vanishes on the inertia of
every finite place outside the conjugates of `T`.  This is the form in which the arithmetic input
(the exactness of the level-`K` localisation: the local data must *glue*) is consumed. -/
theorem exists_realisation_iff_pointwise {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (T : Finset (ValuationSubring Ω))
    (f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p) :
    (∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
        IsCocycleOn (res k K) K.fixingSubgroup z ∧
        IsLocConstOn K.fixingSubgroup z ∧
        (∀ A ∈ T, IsCoboundaryOn (res k K) (decomp k A ⊓ K.fixingSubgroup)
          (fun σ => z σ - f A σ)) ∧
        (∀ B : ValuationSubring Ω, IsFinPlace k B →
          (∀ A ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
          ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → z σ = 0)) ↔
    (∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
        IsCocycleOn (res k K) K.fixingSubgroup z ∧
        IsLocConstOn K.fixingSubgroup z ∧
        (∀ A ∈ T, ∀ g ∈ decomp k A ⊓ K.fixingSubgroup, z g = f A g) ∧
        (∀ B : ValuationSubring Ω, IsFinPlace k B →
          (∀ A ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
          ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → z σ = 0)) := by
  have key : ∀ z : (Ω ≃ₐ[k] Ω) → ZMod p,
      ((∀ A ∈ T, IsCoboundaryOn (res k K) (decomp k A ⊓ K.fixingSubgroup)
          (fun σ => z σ - f A σ)) ↔
       (∀ A ∈ T, ∀ g ∈ decomp k A ⊓ K.fixingSubgroup, z g = f A g)) := by
    intro z
    constructor
    · intro h A hA
      exact (sub_isCoboundaryOn_iff_eqOn (p := p) inf_le_right z (f A)).mp (h A hA)
    · intro h A hA
      exact (sub_isCoboundaryOn_iff_eqOn (p := p) inf_le_right z (f A)).mpr (h A hA)
  constructor
  · rintro ⟨z, h1, h2, h3, h4⟩
    exact ⟨z, h1, h2, (key z).mp h3, h4⟩
  · rintro ⟨z, h1, h2, h3, h4⟩
    exact ⟨z, h1, h2, (key z).mpr h3, h4⟩


section Lane

open _root_.SSGRoute

/-- The `1`-cocycle condition restricts to subgroups. -/
theorem isCocycleOn_of_le {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    {H H' : Subgroup (Ω ≃ₐ[k] Ω)} (h : H ≤ H') {b : (Ω ≃ₐ[k] Ω) → ZMod p}
    (hb : IsCocycleOn (res k K) H' b) : IsCocycleOn (res k K) H b :=
  fun g hg h' hh => hb g (h hg) h' (h hh)

/-- Local constancy restricts to subgroups. -/
theorem isLocConstOn_of_le {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {H H' : Subgroup (Ω ≃ₐ[k] Ω)} (h : H ≤ H') {b : (Ω ≃ₐ[k] Ω) → ZMod p}
    (hb : IsLocConstOn H' b) : IsLocConstOn H b := by
  obtain ⟨U, hU, hUc⟩ := hb
  exact ⟨U, hU, fun g hg u hu huH => hUc g (h hg) u hu (h huH)⟩

/-- The sum of two locally constant `H`-cocycles is one. -/
theorem isCocycleOn_add {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] {H : Subgroup (Ω ≃ₐ[k] Ω)}
    {a b : (Ω ≃ₐ[k] Ω) → ZMod p} (ha : IsCocycleOn (res k K) H a)
    (hb : IsCocycleOn (res k K) H b) : IsCocycleOn (res k K) H (a + b) := by
  intro g hg h hh
  show a (g * h) + b (g * h) = (a g + b g) + res k K g • (a h + b h)
  rw [ha g hg h hh, hb g hg h hh, smul_add]
  abel

/-- The sum of two locally constant functions is locally constant. -/
theorem isLocConstOn_add {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {H : Subgroup (Ω ≃ₐ[k] Ω)} {a b : (Ω ≃ₐ[k] Ω) → ZMod p}
    (ha : IsLocConstOn H a) (hb : IsLocConstOn H b) : IsLocConstOn H (a + b) := by
  obtain ⟨U, hU, hUc⟩ := ha
  obtain ⟨U', hU', hU'c⟩ := hb
  refine ⟨U ⊓ U', ?_, ?_⟩
  · simpa [Subgroup.coe_inf] using hU.inter hU'
  · intro g hg u hu hmem
    have hgu : u ∈ U := (Subgroup.mem_inf.mp hu).1
    have hgu' : u ∈ U' := (Subgroup.mem_inf.mp hu).2
    show a (g * u) + b (g * u) = a g + b g
    rw [hUc g hg u hgu hmem, hU'c g hg u hgu' hmem]

/-- A `ZMod p`-multiple of a locally constant `H`-cocycle is one (the action of `G_k` is
`ZMod p`-linear, i.e. `SMulCommClass`). -/
theorem isCocycleOn_smul {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] {H : Subgroup (Ω ≃ₐ[k] Ω)}
    (c : ZMod p) {a : (Ω ≃ₐ[k] Ω) → ZMod p} (ha : IsCocycleOn (res k K) H a) :
    IsCocycleOn (res k K) H (fun g => c • a g) := by
  intro g hg h hh
  show c • a (g * h) = c • a g + res k K g • (c • a h)
  rw [ha g hg h hh, smul_add, SMulCommClass.smul_comm (res k K g) c (a h)]

/-- A scalar multiple of a locally constant function is locally constant. -/
theorem isLocConstOn_smul {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {H : Subgroup (Ω ≃ₐ[k] Ω)} (c : ZMod p) {a : (Ω ≃ₐ[k] Ω) → ZMod p}
    (ha : IsLocConstOn H a) : IsLocConstOn H (fun g => c • a g) := by
  obtain ⟨U, hU, hUc⟩ := ha
  exact ⟨U, hU, fun g hg u hu hmem => by
    show c • a (g * u) = c • a g
    rw [hUc g hg u hu hmem]⟩

/-- The zero function is an `H`-cocycle. -/
theorem isCocycleOn_zero {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) : IsCocycleOn (res k K) H (0 : (Ω ≃ₐ[k] Ω) → ZMod p) :=
  fun g hg h hh => by simp

/-- The zero function is locally constant. -/
theorem isLocConstOn_zero {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) : IsLocConstOn H (0 : (Ω ≃ₐ[k] Ω) → ZMod p) :=
  ⟨⊤, isOpen_univ, fun g hg u hu hmem => rfl⟩

/-- **The locally constant `H`-cocycles form a `ZMod p`-submodule.**  This is the space on which the
local pairings of `IsLocalTateSystem` live: its `additive_left`/`additive_right` fields are stated
exactly for these elements. -/
def localCocycle {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → ZMod p) where
  carrier := {a | IsCocycleOn (res k K) H a ∧ IsLocConstOn H a}
  zero_mem' := ⟨isCocycleOn_zero H, isLocConstOn_zero H⟩
  add_mem' := fun {a b} ha hb => ⟨isCocycleOn_add ha.1 hb.1, isLocConstOn_add ha.2 hb.2⟩
  smul_mem' := fun c {a} ha => ⟨isCocycleOn_smul c ha.1, isLocConstOn_smul c ha.2⟩

/-- **The level-`K` Selmer space `V_T`.**  Locally constant `1`-cocycles on `G_K = K.fixingSubgroup`
vanishing on the inertia subgroup of every finite place outside the conjugates of `T` (i.e.
unramified outside the conjugates of `T`).  The vanishing is imposed on the *full* inertia subgroups
of `G_k`, which is what the product formula `IsProductFormula` consumes. -/
def selmerSpace {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] (T : Finset (ValuationSubring Ω)) :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → ZMod p) where
  carrier := {b | IsCocycleOn (res k K) K.fixingSubgroup b ∧
    IsLocConstOn K.fixingSubgroup b ∧
    ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup,
        ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
      ∀ σ : Ω ≃ₐ[k] Ω, IsInertia k B σ → b σ = 0}
  zero_mem' := ⟨isCocycleOn_zero _, isLocConstOn_zero _, fun B hB hnot σ hσI => rfl⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨isCocycleOn_add ha.1 hb.1, isLocConstOn_add ha.2.1 hb.2.1, ?_⟩
    intro B hB hnot σ hσI
    rw [Pi.add_apply, ha.2.2 B hB hnot σ hσI, hb.2.2 B hB hnot σ hσI, add_zero]
  smul_mem' := by
    intro c a ha
    refine ⟨isCocycleOn_smul c ha.1, isLocConstOn_smul c ha.2.1, ?_⟩
    intro B hB hnot σ hσI
    rw [Pi.smul_apply, ha.2.2 B hB hnot σ hσI, smul_zero]

/-- **The space of local data at `T`**: tuples of locally constant `1`-cocycles on the level-`K`
local groups `decomp k A ⊓ G_K`, one for each `A ∈ T`. -/
def localDataSpace {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] (T : Finset (ValuationSubring Ω)) :
    Submodule (ZMod p) ({A : ValuationSubring Ω // A ∈ T} → (Ω ≃ₐ[k] Ω) → ZMod p) where
  carrier := {a | ∀ A : {A : ValuationSubring Ω // A ∈ T},
    IsCocycleOn (res k K) (decomp k A.1 ⊓ K.fixingSubgroup) (a A) ∧
      IsLocConstOn (decomp k A.1 ⊓ K.fixingSubgroup) (a A)}
  zero_mem' := fun A => ⟨isCocycleOn_zero _, isLocConstOn_zero _⟩
  add_mem' := by
    intro a b ha hb A
    exact ⟨isCocycleOn_add (ha A).1 (hb A).1, isLocConstOn_add (ha A).2 (hb A).2⟩
  smul_mem' := by
    intro c a ha A
    exact ⟨isCocycleOn_smul c (ha A).1, isLocConstOn_smul c (ha A).2⟩

/-- **The localisation of the level-`K` Selmer space at the places of `T`**: restrict a globally
defined locally constant cocycle to each local group `decomp k A ⊓ G_K`. -/
noncomputable def localisationMap {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] (T : Finset (ValuationSubring Ω)) :
    selmerSpace (p := p) K T →ₗ[ZMod p] localDataSpace (p := p) K T where
  toFun := fun b => ⟨fun A => b.1, fun A => ⟨isCocycleOn_of_le inf_le_right b.2.1,
    isLocConstOn_of_le inf_le_right b.2.2.1⟩⟩
  map_add' := by
    intro b b'
    apply Subtype.ext
    funext A
    rfl
  map_smul' := by
    intro c b
    apply Subtype.ext
    funext A
    rfl

/-- **The localisation image `W_T`**: the local data at `T` realised by a level-`K` class which is
unramified outside the conjugates of `T`. -/
noncomputable def localImage {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] (T : Finset (ValuationSubring Ω)) :
    Submodule (ZMod p) ({A : ValuationSubring Ω // A ∈ T} → (Ω ≃ₐ[k] Ω) → ZMod p) :=
  ((localisationMap (p := p) K T).range).map (Submodule.subtype (localDataSpace (p := p) K T))

/-- **The easy half of maximality** (`W_T ⊆ W_T^⊥`): by the product formula, two level-`K` classes
unramified outside the conjugates of `T` pair trivially at `T`.  This is `IsProductFormula`
evaluated at `T' = T`. -/
theorem sum_pair_selmer_eq_zero {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p}
    (hrec : IsProductFormula p k Ω K pair) {T : Finset (ValuationSubring Ω)}
    (hTfin : ∀ A ∈ T, IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    {b b' : (Ω ≃ₐ[k] Ω) → ZMod p} (hb : b ∈ selmerSpace (p := p) K T)
    (hb' : b' ∈ selmerSpace (p := p) K T) :
    ∑ A ∈ T, pair (decomp k A ⊓ K.fixingSubgroup) b b' = 0 :=
  hrec b b' hb.1 hb.2.1 hb'.1 hb'.2.1 T hTfin hTdisj
    (fun B hB hnot σ hσI => ⟨hb.2.2 B hB hnot σ hσI, hb'.2.2 B hB hnot σ hσI⟩)

end Lane


section Vanish

open _root_.SSGRoute

/-- The submodule of functions on `G_k` vanishing on a subgroup `H`: the kernel of the restriction
of scalar-valued functions to `H`.  For a level-`K` local group this is what the local pairings are
blind to, so the local cohomology `H¹(H, ZMod p)` of such an `H` is
`localCocycle K H ⧸ (localCocycle K H ⊓ vanishOn H)`, and a `LinearMap.BilinForm` on the cocycle
space descends to it. -/
def vanishOn {p : ℕ} {G : Type} [Group G] (H : Subgroup G) : Submodule (ZMod p) (G → ZMod p) where
  carrier := {f | ∀ g ∈ H, f g = 0}
  zero_mem' := fun g hg => rfl
  add_mem' := fun {f f'} hf hf' => fun g hg => by
    rw [Pi.add_apply, hf g hg, hf' g hg, add_zero]
  smul_mem' := fun c {f} hf => fun g hg => by
    rw [Pi.smul_apply, hf g hg, smul_zero]

/-- The local-data tuples all of whose components vanish on the corresponding level-`K` local group.
The quotient of `localDataSpace K T` by this submodule is the product of the local `H¹`s
`H¹(decomp k A ⊓ G_K, ZMod p)` for `A ∈ T`. -/
def productVanish {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (T : Finset (ValuationSubring Ω)) :
    Submodule (ZMod p) ({A : ValuationSubring Ω // A ∈ T} → (Ω ≃ₐ[k] Ω) → ZMod p) where
  carrier := {a | ∀ A : {A : ValuationSubring Ω // A ∈ T},
    ∀ g ∈ decomp k A.1 ⊓ K.fixingSubgroup, a A g = 0}
  zero_mem' := fun A g hg => rfl
  add_mem' := fun {a b} ha hb => fun A g hg => by
    simp [Pi.add_apply, ha A g hg, hb A g hg]
  smul_mem' := fun c {a} ha => fun A g hg => by
    simp [Pi.smul_apply, ha A g hg]

/-- The vanishing submodule *inside* the local-data space: `localDataSpace K T ⊓ productVanish`.
This is the `V₀` of the quotient step `orthogonal_le_sup_of_ker_le`; the localisation image modulo
`V₀` is the image of `V_T` in the product of the local `H¹`s. -/
def localVanish {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] (T : Finset (ValuationSubring Ω)) :
    Submodule (ZMod p) ↥(localDataSpace (p := p) K T) :=
  (productVanish (p := p) K T).comap (localDataSpace (p := p) K T).subtype

/-- The localisation image, as a submodule of the local-data space itself (rather than of the
ambient function space): this is the `W_T` on which the counting identity is stated. -/
noncomputable def localImageIn {p : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] (T : Finset (ValuationSubring Ω)) :
    Submodule (ZMod p) ↥(localDataSpace (p := p) K T) :=
  (localisationMap (p := p) K T).range

end Vanish

section LinearAlgebra

/-- **Maximality of an isotropic subspace from a counting inequality.**  If the left radical of a
bilinear form on a finite-dimensional space is trivial (`ker B = ⊥`), if `W` is isotropic
(`W ≤ W^⊥`) and if the counting input `finrank V ≤ 2 * finrank W` holds, then `W` is *maximally*
isotropic: `W^⊥ = W`.  In the realisation lane the counting input is the counting identity of the
level-`K` localisation (`finrank` of the local-data space versus `finrank` of `W_T`), i.e. the
Euler characteristic -- the one remaining arithmetic rung. -/
theorem orthogonal_eq_of_ker_eq_bot_of_isotropic_of_finrank_le
    {K' V : Type} [Field K'] [AddCommGroup V] [Module K' V] [FiniteDimensional K' V]
    (B : LinearMap.BilinForm K' V) (hker : B.ker = ⊥) (W : Submodule K' V)
    (hiso : W ≤ B.orthogonal W) (hfin : Module.finrank K' V ≤ 2 * Module.finrank K' W) :
    B.orthogonal W = W := by
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) W
  rw [hker, inf_bot_eq, finrank_bot, add_zero] at h1
  have h2 : Module.finrank K' ↥(B.orthogonal W) ≤ Module.finrank K' W := by omega
  exact (Submodule.eq_of_le_of_finrank_le hiso h2).symm

end LinearAlgebra

end Work.SSGRoute.ZDataMup
