import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.akH2_restriction_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


/-! ## The group restriction on the continuous second cohomology, as a named map

Session 1 of this node proved the *existence* of the group restriction on the continuous model
`AbsoluteKummer.H2` together with its two computation rules
(`Submission/Work/SSGRoute/akH2_restriction_natural.lean`, `akH2_restriction_natural`).  The
localisation square of the E1a lane needs it as a *named* map, so here it is extracted once and
for all, with the two rules specialised. -/

namespace Work.AbsoluteKummer

section AkRes

variable {G : Type} [TopologicalSpace G] [Group G]

/-- **The group restriction on the continuous second cohomology** `H²(G,M) →+ H²(H,M)`. -/
noncomputable def akRes (H : Subgroup G) (M : Type) [AddCommGroup M] [DistribMulAction G M] :
    Work.AbsoluteKummer.H2 G M →+ Work.AbsoluteKummer.H2 ↥H M :=
  Classical.choose (akH2_restriction_natural H M)

/-- The computation rule of `akRes` on classes of locally constant cocycles. -/
theorem akRes_H2π (H : Subgroup G) (M : Type) [AddCommGroup M] [DistribMulAction G M]
    (c : G × G → M) (hc : c ∈ Work.AbsoluteKummer.Z2 G M) :
    akRes H M (Work.AbsoluteKummer.H2π G M ⟨c, hc⟩) =
      Work.AbsoluteKummer.H2π ↥H M
        ⟨fun q : ↥H × ↥H => c (q.1, q.2), akRes_locallyConstant H M c hc⟩ :=
  (Classical.choose_spec (akH2_restriction_natural H M)).1 c hc

/-- **Naturality of `akRes` with the forgetful map `akToGCH2` into the abstract model.** -/
theorem akToGCH2_akRes (H : Subgroup G) (M : Type) [AddCommGroup M] [DistribMulAction G M]
    (x : Work.AbsoluteKummer.H2 G M) :
    Work.SSGRoute.PT.akToGCH2 ↥H M (akRes H M x) =
      Work.GroupCohomology.resH2 G H (Work.SSGRoute.PT.akToGCH2 G M x) :=
  (Classical.choose_spec (akH2_restriction_natural H M)).2 x


/-- **Group restriction commutes with a change of coefficients.**  For a `Γ`-equivariant additive
map `f : M →+ N` of discrete `Γ`-modules and a subgroup `H ≤ Γ`, the map `H²(Γ,M) → H²(Γ,N)`
induced by `f` commutes with the group restriction `akRes`.

This is the coefficient naturality of the E1a chain: it lets the restriction of
`e1aCoeffH2 (δ (ζ z))` to a decomposition group be computed by the restricted coefficient map, one
of the two remaining inputs of the localisation square of the E1a lane. -/
theorem akRes_mapH2 {G : Type} [TopologicalSpace G] [Group G] (H : Subgroup G)
    {M N : Type} [AddCommGroup M] [AddCommGroup N] [DistribMulAction G M] [DistribMulAction G N]
    (f : M →+ N) (hf : Work.GroupCohomology.IsEquivariant G f)
    (x : Work.AbsoluteKummer.H2 G M) :
    akRes H N (Work.AbsoluteKummer.mapH2 f hf x) =
      Work.AbsoluteKummer.mapH2 f (fun (h : ↥H) (m : M) => hf (h : G) m)
        (akRes H M x) := by
  classical
  let hf' : Work.GroupCohomology.IsEquivariant ↥H f := fun h m => hf (h : G) m
  have h1 : ∀ z : Work.AbsoluteKummer.Z2 ↥H M,
      Work.AbsoluteKummer.mapH2 f hf' (Work.AbsoluteKummer.H2π ↥H M z) =
        Work.AbsoluteKummer.H2π ↥H N (Work.AbsoluteKummer.mapZ2 f hf' z) :=
    fun z => Work.AbsoluteKummer.mapH2_H2π f hf' z
  refine QuotientAddGroup.induction_on x ?_
  intro z
  change akRes H N (Work.AbsoluteKummer.mapH2 f hf (Work.AbsoluteKummer.H2π G M z)) =
    Work.AbsoluteKummer.mapH2 f hf' (akRes H M (Work.AbsoluteKummer.H2π G M z))
  rw [Work.AbsoluteKummer.mapH2_H2π, akRes_H2π, akRes_H2π, h1]
  apply congrArg (Work.AbsoluteKummer.H2π ↥H N)
  apply Subtype.ext
  funext q
  show f ((z : G × G → M) (q.1, q.2)) = f ((z : G × G → M) (q.1, q.2))
  rfl

/-- **The hypothesis of the target, in the continuous model.**  The abstract restriction of
`akToGCH2 x` vanishes exactly when the continuous restriction of `x` has vanishing image under
`akToGCH2`. -/
theorem resH2_akToGCH2_eq_zero_iff_akRes {G : Type} [TopologicalSpace G] [Group G]
    (H : Subgroup G) (M : Type) [AddCommGroup M] [DistribMulAction G M]
    (x : Work.AbsoluteKummer.H2 G M) :
    Work.GroupCohomology.resH2 G H (Work.SSGRoute.PT.akToGCH2 G M x) = 0 ↔
      Work.SSGRoute.PT.akToGCH2 ↥H M (akRes H M x) = 0 :=
  iff_of_eq (congrArg (fun z => z = 0) (akToGCH2_akRes H M x).symm)

/-- **The target's hypothesis implies the continuous vanishing, given the injectivity of
`akToGCH2`.**

This is the generic form of the passage from the *abstract* formulation of a localisation clause
(`resH2_D (akToGCH2 x) = 0`) to the *continuous* one (`akRes_D x = 0`) that the local dictionary of
the E1a lane is stated with.  It isolates the one input which is not formal: the injectivity of the
forgetful map `akToGCH2 : H²_c(D,E) → H²_abs(D,E)`, i.e. `Z²_c ∩ B²_abs = B²_c` at `D` (see
`PT/NOTE_e1aBetaCan_localDictionary_fin_compat.md` § 3). -/
theorem akRes_eq_zero_of_resH2_eq_zero {G : Type} [TopologicalSpace G] [Group G]
    (H : Subgroup G) (M : Type) [AddCommGroup M] [DistribMulAction G M]
    (hgap : ∀ z : Work.AbsoluteKummer.H2 ↥H M,
      Work.SSGRoute.PT.akToGCH2 ↥H M z = 0 → z = 0)
    (x : Work.AbsoluteKummer.H2 G M) :
    Work.GroupCohomology.resH2 G H (Work.SSGRoute.PT.akToGCH2 G M x) = 0 →
      akRes H M x = 0 :=
  fun h => hgap _ ((resH2_akToGCH2_eq_zero_iff_akRes H M x).mp h)


/-- **Group restriction commutes with the connecting map of a short exact sequence** (cocycle
level).

For a short exact sequence `S : 0 → M → N → P → 0` of discrete `Γ`-modules, a subgroup `H ≤ Γ` and
the *restricted* sequence `SH` (same modules and same maps, with the `↥H`-action), the connecting
cocycle of a locally constant `1`-cocycle commutes with the group restriction `akRes`.

The two lifts `S.liftCochainC c|_H` and `SH.liftCochainC cH` of the same cocycle on `↥H` differ by
an `N`-valued cochain with values in `ker π = range ι`; pulling the difference back along `ι` (which
is additive and locally constant as a pullback) exhibits the difference of the connecting cocycles
as a coboundary, hence the two classes agree.

This is the "tail" naturality of the E1a chain: with `akRes_mapH2` it computes the restriction of
`e1aCoeffH2 (e1aDelta (ζ z))` by the restricted dualised resolution, which is what the localisation
square of the E1a lane needs. -/
theorem akRes_deltaH2 {Γ : Type} [TopologicalSpace Γ] [Group Γ] [IsTopologicalGroup Γ]
    (H : Subgroup Γ) [IsTopologicalGroup ↥H]
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction Γ M] [DistribMulAction Γ N] [DistribMulAction Γ P]
    (S : ShortExactSeq Γ M N P) (SH : ShortExactSeq ↥H M N P)
    (hiota : ∀ m : M, SH.iota m = S.iota m) (hpi : ∀ n : N, SH.pi n = S.pi n)
    (c : ↥(Work.AbsoluteKummer.Z1 Γ P)) (cH : ↥(Work.AbsoluteKummer.Z1 ↥H P))
    (hcH : ∀ h : ↥H, (cH : ↥H → P) h = (c : Γ → P) h) :
    akRes H M (Work.AbsoluteKummer.H2π Γ M (S.deltaCocycleC c)) =
      Work.AbsoluteKummer.H2π ↥H M (SH.deltaCocycleC cH) := by
  classical
  rw [akRes_H2π, Work.AbsoluteKummer.H2π_eq_iff, Work.AbsoluteKummer.mem_B2_iff]
  -- the two lifts of the common cocycle on `↥H`
  set b : ↥H → N := fun h => S.liftCochainC (c : Γ → P) (h : Γ) with hb
  set b' : ↥H → N := SH.liftCochainC (cH : ↥H → P) with hb'
  -- their difference has values in `ker π = range ι`
  have hker : ∀ h : ↥H, b h - b' h ∈ SH.pi.ker := by
    intro h
    have e1 : SH.pi (b h) = (cH : ↥H → P) h := by
      rw [hb, hpi, S.pi_liftCochainC]
      exact (hcH h).symm
    have e2 : SH.pi (b' h) = (cH : ↥H → P) h := by
      rw [hb', SH.pi_liftCochainC]
    rw [AddMonoidHom.mem_ker, map_sub, e1, e2, sub_self]
  set w : ↥H → M := fun h => SH.iotaInv (b h - b' h) with hw
  have hwi : ∀ h : ↥H, SH.iota (w h) = b h - b' h := by
    intro h
    rw [hw]
    exact SH.iota_iotaInv (SH.mem_range_of_mem_ker (hker h))
  have hbl : Work.AbsoluteKummer.IsLocallyConstant b :=
    (ShortExactSeq.isLocallyConstant_liftCochainC S (isLocallyConstant_of_mem_Z1 c.2)).comp
      continuous_subtype_val
  have hb'l : Work.AbsoluteKummer.IsLocallyConstant b' :=
    ShortExactSeq.isLocallyConstant_liftCochainC SH (isLocallyConstant_of_mem_Z1 cH.2)
  have hwl : Work.AbsoluteKummer.IsLocallyConstant w := by
    rw [hw]
    exact Work.AbsoluteKummer.IsLocallyConstant.map SH.iotaInv (hbl.sub hb'l)
  refine ⟨w, hwl, ?_⟩
  funext q
  obtain ⟨g, h⟩ := q
  apply SH.iota_injective
  have h1 : SH.iota (S.iotaInv (Work.GroupCohomology.d1 Γ N (S.liftCochainC (c : Γ → P))
        ((g : Γ), (h : Γ))))
      = Work.GroupCohomology.d1 Γ N (S.liftCochainC (c : Γ → P)) ((g : Γ), (h : Γ)) := by
    rw [hiota]
    exact S.iota_iotaInv (S.mem_range_of_mem_ker (S.pi_d1_liftCochainC c (g : Γ) (h : Γ)))
  have h2 : SH.iota (SH.iotaInv (Work.GroupCohomology.d1 ↥H N (SH.liftCochainC (cH : ↥H → P))
        (g, h)))
      = Work.GroupCohomology.d1 ↥H N (SH.liftCochainC (cH : ↥H → P)) (g, h) :=
    SH.iota_iotaInv (SH.mem_range_of_mem_ker (SH.pi_d1_liftCochainC cH g h))
  have h3 : SH.iota (Work.GroupCohomology.d1 ↥H M w (g, h))
      = Work.GroupCohomology.d1 ↥H N b (g, h) - Work.GroupCohomology.d1 ↥H N b' (g, h) := by
    have hA : Work.GroupCohomology.d1 ↥H N b (g, h) - Work.GroupCohomology.d1 ↥H N b' (g, h)
        = Work.GroupCohomology.d1 ↥H N (b - b') (g, h) := by
      simp only [Work.GroupCohomology.d1_apply, Pi.sub_apply, smul_sub]
      abel
    have hB : Work.GroupCohomology.d1 ↥H N (b - b') (g, h)
        = SH.iota (Work.GroupCohomology.d1 ↥H M w (g, h)) := by
      have hfun : b - b' = fun h : ↥H => SH.iota (w h) := by
        funext h; exact (hwi h).symm
      rw [hfun, Work.GroupCohomology.d1_apply, Work.GroupCohomology.d1_apply]
      rw [map_add, map_sub, SH.iota_equivariant]
    exact (hA.trans hB).symm
  simp only [AddSubgroup.coe_sub, Pi.sub_apply, ShortExactSeq.deltaCocycleC_apply,
    ShortExactSeq.liftCochainC_apply]
  rw [map_sub, h1, h2, h3, hb, hb']
  try rfl
end AkRes

end Work.AbsoluteKummer

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

/-- **THE GAP: injectivity of `akToGCH2` at the finite place `A`.**

The target's hypothesis is stated in the *abstract* model (`resH2` of `akToGCH2`), while the whole
E1a chain and the local dictionary live in the *continuous* model; passing between them needs the
forgetful map `akToGCH2 : H²_c(D_A,E) → H²_abs(D_A,E)` to lose nothing.  Equivalently, in cocycle
terms (`akToGCH2_H2π` + `H2π_eq_zero_iff`), this is

  **`Z²_c ∩ B²_abs = B²_c` at `D_A = decomp k A`**.

**Status: a genuine arithmetic statement, not a formal one** (this is the corrected version of the
node's earlier assessment; see `PT/NOTE_e1aBetaCan_localDictionary_fin_compat.md` § 11).

* `H²_c(D_A,E) = H²(D_A/U₀,E)` with `U₀ = ker(D_A → Aut E)` open normal (as `E` is finite and the
  action continuous), and with this identification `akToGCH2` is the inflation
  `H²(D_A/U₀,E) → H²_abs(D_A,E)` along the finite quotient `D_A ↠ D_A/U₀`.
* In cocycle form the statement is: every locally constant `2`-cocycle `c` on `D_A` which is an
  abstract coboundary `c = d¹b` is a coboundary of a locally constant cochain.  Writing
  `Φ(x,v) := b(xv) - b(x) = x·Φ(v)` for `v` in an open normal `V` through which `c` factors
  (uniform local constancy), one needs a *derivation* `Ψ : D_A → E` restricting to `Φ`; then
  `b - Ψ` is right-`V`-invariant, hence locally constant.  **The existence of `Ψ` is not formal**:
  for `G = ℤ/4`, `V = 2ℤ/4 ≅ ℤ/2`, `E = 𝔽₂` trivial and `Φ(2) = 1`, no homomorphism
  `Ψ : ℤ/4 → 𝔽₂` restricts to `Φ` (as `Ψ(2) = 2·Ψ(1) = 0`).  Equivalently, the statement is the
  vanishing of the transgression `H¹(U₀,E)^{D_A/U₀} → H²(D_A/U₀,E)` (Hochschild–Serre five-term
  sequence), i.e. the local Tate duality input in degree two —
  `H²_abs(D_A,E) ≅ H⁰(D_A,E^∨(1))^∨` with `inf` dual to
  `(E^∨(1))^{D_A} ⊆ (E^∨(1))^{D_A/U₀}`.
* The analogous statement for an *arbitrary* profinite group is **FALSE**: the delegated prover
  supplied the counterexample `G = ℤ/4 × ℤ₂`, `U = 2ℤ/4 × {0} ≅ ℤ/2`, `E = 𝔽₂` trivial, where
  `res : H¹(G,𝔽₂) → H¹(U,𝔽₂)` vanishes (every hom `G → 𝔽₂` kills `2·(1,0)`), so the transgression
  has zero kernel and the nontrivial `G/U`-invariant class of `H¹(U,𝔽₂)` gives a nonzero element of
  `Z²_c ∩ B²_abs` which is not in `B²_c` (as `U` is the only open normal subgroup of `G` contained
  in `U`).  Hence the statement below is *specific* to `D_A = Gal(Ω_v/k_v)` and is the single
  arithmetic input isolated by `akRes_eq_zero_of_resH2_eq_zero`. -/
theorem akToGCH2_injective_decompFin
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (Ω ≃ₐ[k] Ω) E]
    [Finite E] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Function.Injective (Work.SSGRoute.PT.akToGCH2 ↥(SSGRoute.decomp k A) E) := by
  sorry


/-! ## Bricks for the local dictionary at a finite place

The target `e1aBetaCan_localDictionary_fin_compat` is the (conditional) compatibility of the
degree-two local dictionary: from the vanishing of `res_{D_A}(akToGCH2 (e1aChainC y))` in
`H²(D_A,E)` it concludes `extLoc_q (extToIdeles y) = 0`.

The first two lemmas below *identify the hypothesis* in cocycle terms, which is the form any
proof of the compatibility has to start from: the restriction of the class is the class of the
restricted locally constant `2`-cocycle, and its vanishing is equivalent to that restricted
cocycle being a coboundary of an (arbitrary, a priori non-continuous) `1`-cochain. -/

section Restrict

variable {G : Type} [TopologicalSpace G] [Group G] (H : Subgroup G)
variable (M : Type) [AddCommGroup M] [DistribMulAction G M]

/-- **The computation rule of the abstract restriction of the forgetful image.**  For a locally
constant `2`-cocycle `c` on `G`, the restriction to `H ≤ G` of the abstract class
`akToGCH2 (H2π c)` is the class of the restricted cocycle (with the abstract (non-continuous)
coboundaries): both sides are `H2π` of the function restriction of `c`.

This is the general form of the computation performed inside
`Work.SSGRoute.PT.sha2ToH2AK_restrict_decomp_eq_zero`. -/
theorem resH2_akToGCH2_H2π (c : ↥(Work.AbsoluteKummer.Z2 G M)) :
    Work.GroupCohomology.resH2 G H (akToGCH2 G M (Work.AbsoluteKummer.H2π G M c)) =
      Work.GroupCohomology.H2π ↥H M
        (Work.GroupCohomology.resZ2 G H (akZ2ToGCZ2 G M c)) := by
  rw [akToGCH2_H2π, Work.GroupCohomology.resH2_H2π]

/-- **The hypothesis of the local dictionary in cocycle form.**  For a locally constant `2`-cocycle
`c` on `G = Ω ≃ₐ[k] Ω`, the vanishing of `resH2 H (akToGCH2 (H2π c))` is exactly the statement that
the *restriction* of `c` to `H × H` is the coboundary of some cochain `H → M` — a priori an
arbitrary (non-continuous, non-locally-constant) cochain.

The difference with the *locally constant* coboundary condition used by `Z2loc`
(`SSGRoute.IsCoboundary2On`) is the abstract-vs-continuous gap; see the note
`NOTE_e1aBetaCan_localDictionary_fin_compat.md`. -/
theorem resH2_akToGCH2_H2π_eq_zero_iff (c : ↥(Work.AbsoluteKummer.Z2 G M)) :
    Work.GroupCohomology.resH2 G H (akToGCH2 G M (Work.AbsoluteKummer.H2π G M c)) = 0 ↔
      ∃ b : ↥H → M,
        Work.GroupCohomology.d1 ↥H M b
          = (Work.GroupCohomology.resZ2 G H (akZ2ToGCZ2 G M c) : ↥H × ↥H → M) := by
  rw [resH2_akToGCH2_H2π, Work.GroupCohomology.H2pi_eq_zero_iff, Work.GroupCohomology.mem_B2_iff]

end Restrict

/-! ## The two hypothesis forms

The sibling node `PT/e1aChainC_localComparison` uses the *continuous* hypothesis: the chain class
has a representative `c` which is a coboundary of a **locally constant** cochain on `D_A`
(`SSGRoute.IsCoboundary2On`).  The target of this file uses the *abstract* form (`resH2` of
`akToGCH2`, i.e. a coboundary of an *arbitrary* cochain, see `resH2_akToGCH2_H2π_eq_zero_iff`).
The lemma below records the easy direction: the continuous condition *implies* the abstract one.
(The converse would require `Z²_cont ∩ B²_abs = B²_cont` at `D_A`, i.e. injectivity of the
abstract-vs-continuous comparison; that is the delicate point of the note's §3.)

Consequently the target is *weaker in hypothesis* — hence *stronger as a statement* — than the
sibling node, and the consumer `PT.e1aBetaCan_le_ker` can supply the *continuous* hypothesis
directly for `y = β b` from the proof of `PT.e1aBetaCan_aux.sha2_to_H2AK_restrict_decomp_eq_zero`
(which produces a locally constant primitive, `x.2.2.2.1 A hA`). -/

section HypForms

variable {Γ : Type} [TopologicalSpace Γ] [Group Γ] {G : Type} [Group G]
variable {M : Type} [AddCommGroup M] [DistribMulAction Γ M] [DistribMulAction G M]

/-- **The locally-constant coboundary condition implies the abstract one**: a cocycle which is a
coboundary of a locally constant cochain on `H ≤ Γ` lies in the abstract coboundaries `B²` of
`↥H`, via the same cochain.  (`hact` records that the `↥H`-action is the `Γ`-action through the
coercion, which holds definitionally in the application.) -/
theorem resZ2_mem_B2_of_isCoboundary2On (act : Γ →* G)
    (hact : ∀ (γ : Γ) (m : M), γ • m = act γ • m) (H : Subgroup Γ) (c : Γ → Γ → M)
    (hcob : SSGRoute.IsCoboundary2On act H c) :
    (fun q : ↥H × ↥H => c (q.1 : Γ) (q.2 : Γ)) ∈ Work.GroupCohomology.B2 ↥H M := by
  obtain ⟨b, _hb, hbc⟩ := hcob
  refine ⟨fun h : ↥H => b (h : Γ), ?_⟩
  funext q
  obtain ⟨g, h⟩ := q
  have hsmul : g • b (h : Γ) = (g : Γ) • b (h : Γ) := rfl
  rw [Work.GroupCohomology.d1_apply, hsmul, hact (g : Γ) (b (h : Γ))]
  simpa using (hbc (g : Γ) g.2 (h : Γ) h.2).symm

end HypForms

/-! ## The reduction of the target to the local dictionary

The target is the `Λ`-free (conditional) form of the compatibility of the degree-two local
dictionary.  It follows from the *existential* form in which the requester stated it
(`PT/e1aBetaCan_localDictionary_fin_inj`): if `Λ` is injective and the compatibility clause holds,
then `Λ (extLoc …) = 0` and injectivity kill `extLoc …`.  The lemma below records that reduction,
so that the target is a corollary of the existential form as soon as the latter lands. -/

section Reduction

open scoped TensorProduct

/-- **The target follows from the local dictionary with an injective `Λ`.** -/
theorem e1aBetaCan_localDictionary_fin_compat_of_fin_inj
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (hΛ : ∃ Λ : CategoryTheory.Abelian.Ext.{0}
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)) 2 →+
      @Work.GroupCohomology.H2 (SSGRoute.decomp k A) E _ _
        (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
          (DistribMulAction.compHom E (SSGRoute.res k K)) (SSGRoute.decomp k A)),
      Function.Injective Λ ∧
      ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
        @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) E _ _
          (DistribMulAction.compHom E (SSGRoute.res k K))
          (SSGRoute.decomp k A)
          (@Work.SSGRoute.PT.akToGCH2 (Ω ≃ₐ[k] Ω) _ _ E _
            (DistribMulAction.compHom E (SSGRoute.res k K))
            (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)) = 0 →
        Λ (SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
            (SSGRoute.PTExt.extToIdeles (k := k) y)) = 0) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) E _ _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (SSGRoute.decomp k A)
        (@Work.SSGRoute.PT.akToGCH2 (Ω ≃ₐ[k] Ω) _ _ E _
          (DistribMulAction.compHom E (SSGRoute.res k K))
          (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)) = 0 →
      SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
        (SSGRoute.PTExt.extToIdeles (k := k) y) = 0 := by
  intro y hy
  obtain ⟨Λ, hΛinj, hΛcompat⟩ := hΛ
  exact hΛinj (by rw [hΛcompat y hy, map_zero])

end Reduction

/-! ## The target (the statement requested by the colleague; untouched) -/

theorem e1aBetaCan_localDictionary_fin_compat
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) E _ _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (SSGRoute.decomp k A)
        (@Work.SSGRoute.PT.akToGCH2 (Ω ≃ₐ[k] Ω) _ _ E _
          (DistribMulAction.compHom E (SSGRoute.res k K))
          (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)) = 0 →
      SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
        (SSGRoute.PTExt.extToIdeles (k := k) y) = 0 := by sorry

end Work.SSGRoute.PT
