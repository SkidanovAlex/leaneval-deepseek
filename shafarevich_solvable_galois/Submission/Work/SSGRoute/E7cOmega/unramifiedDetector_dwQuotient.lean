import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.e7comega_defs
import Submission.Work.SSGRoute.eCoh_map
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7cOmega

open SSGRoute.PTExt CategoryTheory
open NK.GlobalCFT (Idele Place IdeleClassGroup)

/-! ## Group-cohomology layer of the detector (helper lemmas)

The detecting classes in `unramifiedDetector_dwQuotient` are built from `1`-cocycles `z : G → A`
whose class is `eCoh 1 G A ((groupCohomology.H1π A).hom z)`.  The group-cohomology layer below
provides `eCoh_one_comp_mk0` (coefficient change: postcomposition with `mk₀ φ` is the class of the
coefficientwise image cocycle) and `extHRestrict_eCoh_one` (restriction to a subgroup is the class
of the naively restricted cocycle), with `extHMap_id_apply_aux` as the local ingredient of the
first.  Together they turn `π_*(res_{D'} h) ≠ 0` for a cocycle-built class into a statement about
cocycle *values*. -/

/-- Local copy of `Work.SSGRoute.extHMap_id_apply` (avoiding the heavy import of
`bridgeE_map_coeff`): changing coefficients along `φ` at the identity of the group is
postcomposition with `mk₀ φ`. -/
theorem extHMap_id_apply_aux {G : Type} [Group G] {A B : Rep Coeff G} (φ : A ⟶ B) {n : ℕ}
    (y : extH A n) : extHMap (MonoidHom.id G) φ y = y.comp (Abelian.Ext.mk₀ φ) (add_zero n) := by
  unfold extHMap extRes
  rw [show y.mapExactFunctor (Rep.resFunctor (MonoidHom.id G)) = y from
        Work.SSGRoute.mapExactFunctor_id y,
      show unitRes (MonoidHom.id G) = 𝟙 (unitRep G) from rfl]
  exact Abelian.Ext.mk₀_id_comp _

/-- **Naturality of the `E0b` bridge in the coefficient morphism.**  Postcomposition with `mk₀ φ`
of the class of a `1`-cocycle `z` of `A` is the class of the coefficientwise image cocycle.  This is
what turns a non-vanishing statement `π_*(res h) ≠ 0` about a class built from a cocycle into a
statement about the values of the cocycle. -/
theorem eCoh_one_comp_mk0 (G : Type) [Group G] (A B : Rep Coeff G)
    (φ : A ⟶ B) (z : ↥(groupCohomology.cocycles₁ A)) (z' : ↥(groupCohomology.cocycles₁ B))
    (hz : ∀ g : G, (z' : G → ↥B) g = φ.hom ((z : G → ↥A) g)) :
    (eCoh 1 G A ((groupCohomology.H1π A).hom z)).comp
        (Abelian.Ext.mk₀ φ) (add_zero 1) =
      eCoh 1 G B ((groupCohomology.H1π B).hom z') := by
  have hzz : groupCohomology.mapCocycles₁ (MonoidHom.id G) φ z = z' := by
    apply Subtype.ext
    funext g
    first
      | (rw [groupCohomology.coe_mapCocycles₁]; exact (hz g).symm)
      | (show (groupCohomology.cochainsMap₁ (MonoidHom.id G) φ (z : G → ↥A)) g
            = (z' : G → ↥B) g
         exact (hz g).symm)
      | exact (hz g).symm
  rw [← extHMap_id_apply_aux φ (eCoh 1 G A ((groupCohomology.H1π A).hom z)),
    ← Work.SSGRoute.eCoh_map 1 G G (MonoidHom.id G) A B φ ((groupCohomology.H1π A).hom z),
    groupCohomology.H1π_comp_map_apply, hzz]

/-- **Restriction of a class given by a cocycle.**  The restriction to `D ≤ G` of the class of a
`1`-cocycle of `A` is the class of the naively restricted cocycle.  This is the half of
`Work.SSGRoute.e9_caseB_cocycle` that does not mention vanishing; together with `eCoh_one_comp_mk0`
it lets one compute `π_*(res_{D'} h)` for a class `h` built from a cocycle, which is what both
constructions in the target's header need. -/
theorem extHRestrict_eCoh_one (G : Type) [Group G] (A : Rep Coeff G) (D : Subgroup G)
    (z : ↥(groupCohomology.cocycles₁ A)) :
    extHRestrict D (eCoh 1 G A ((groupCohomology.H1π A).hom z)) =
      eCoh 1 ↥D (Rep.res D.subtype A)
        ((groupCohomology.H1π (Rep.res D.subtype A)).hom
          (groupCohomology.mapCocycles₁ D.subtype
            (CategoryTheory.CategoryStruct.id (Rep.res D.subtype A)) z)) := by
  rw [extHRestrict]
  rw [← Work.SSGRoute.eCoh_map 1 G ↥D D.subtype A (Rep.res D.subtype A)
    (CategoryTheory.CategoryStruct.id (Rep.res D.subtype A)) ((groupCohomology.H1π A).hom z)]
  rw [groupCohomology.H1π_comp_map_apply]

/-! ## Delegated pieces of the node

Both surviving branches of the target's case analysis are now fired as separate lemmas (each
reviewed by two critics before being handed out):

* `Work.SSGRoute.E7cOmega.unramifiedDetector_dwQuotientInvariant` — the **invariant construction**
  (`∃ m ∈ M^Γ, π m ≠ 0`), from the on-disk `Sha2Lib.exists_unramified_character_with_p_dvd_residueDeg`
  and `Sha2Lib.extH_class_of_character`; the three lemmas above give its cocycle computation.
* `Work.SSGRoute.E7cOmega.unramifiedDetector_dwQuotientTransfer` — the **transfer construction**
  (`h = Cor_N^Γ ψ`), with hypotheses
  `hp : ¬ p ∣ |D_w|` (so that the transfer value `|D_w| · m₀` is non-zero in `𝔽_p`),
  `hI₁ : I' ∩ N = 1` (whence the class is unramified at `q'`),
  `hsup : D' ⊔ N = ⊤` (equivalently `D_w = Gal(K/k)`, i.e. a single Mackey double coset), and a
  detection input `m₀ = ψ (n^j)` with `n ∈ D' ∩ N` and `π m₀ ≠ 0`. -/

namespace Work.SSGRoute.E7cOmega

/-!
# `unramifiedDetector_dwQuotient`: mathematical map of the node (session notes)

**State of the statement.**  The statement is *true* (no counterexample was found, and every
concrete configuration that was computed by hand satisfies it), but it is a *research-level*
node: its proof needs one of

* a level `L ⊇ K` together with a *non-abelian* realisation of the local datum at `q` (the
  split embedding problem `Gal(L/k) = M ⋊ G` with prescribed local behaviour), i.e. exactly the
  Grünwald–Wang/Shafarevich existence machinery that this project is building — this is what the
  lane's own note (`NOTE_assemblies_H7_L2960.md` §4) flags as "the truth genuinely rests on the
  solvability of embedding problems"; or
* a substantial group-cohomology development (Shapiro + corestriction/Mackey + transfer duality)
  *plus* a Grünwald–Wang input realising the local group structure used by the transfer.

**What is on disk and provable now (the route).**  Write `Γ = Gal(L/k)`, `N = Gal(L/K)` and
`D' = D_{q'} = decompK q'`, `W = D' ∩ N`, `I' = inertia of q'`.  Since `e(q'|K) = 1` one has
`I' ∩ N = 1`, so `W ↪ D'/I'` is *cyclic*; and `π_*(res_{D'} ·)` lands in
`H¹(D', 𝔽_p) = Hom(D', 𝔽_p)`, which is nonzero precisely when `p ∣ |D'|`.

Two constructions can give a detecting class `h ∈ H¹(Γ, res M)` with `h|_I' = 0` and
`π_*(res_{D'} h) ≠ 0`.  (A third one that *looks* available — the "character-line case" — is
impossible, for the structural reason recorded after them.)

1. *(invariant case)* if some `m` is fixed by `Γ` and `π m ≠ 0`, take the cocycle
   `σ ↦ f(σ) • m`, where `f` is the global additive character of a level supplied by
   `Work.SSGRoute.Sha2Lib.exists_unramified_character_with_p_dvd_residueDeg` (proved on disk: it
   gives `e(q'|K) = 1` and a character killing the inertia of `q'` and non-trivial on `D_{q'}`);
   this is immediate from `Work.SSGRoute.Sha2Lib.extH_class_of_character` (proved) and the cocycle
   API (`groupCohomology.cocycles₁`, `Work.SSGRoute.eCoh`, `Work.SSGRoute.e9_caseB_cocycle`).
   Delegated as `Work.SSGRoute.E7cOmega.unramifiedDetector_dwQuotientInvariant`.
2. *(corestriction/transfer case)* take `h = Cor_N^Γ(ψ)` for a homomorphism `ψ : N → M`
   (`N` acts trivially on `M` — the `Γ`-action on `M` factors through `galRes` — and `Cor` is on disk
   via `Submission/Work/SSGRoute/ext_corestriction.lean`).  The Mackey formula for corestriction is the
   *double-coset* sum (`res_H ∘ Cor_K = Σ_{g ∈ H\Γ/K} Cor_{H ∩ gKg⁻¹} ∘ conj_g ∘ res`), **not**
   `res ∘ Cor = index` — the latter is false (checked on `ℤ/4 ⊇ ℤ/2`: `res_N Cor_N^Γ x = 2x`).  With a
   *single* double coset (`D' ⊔ N = ⊤`, equivalently `D_w = Gal(K/k)`) one gets
   `res_{D'} h = Cor_W^{D'}(ψ|_W)`, whence `π_*(res_{D'} h) = (π ∘ ψ|_W) ∘ V_{D',W}`: the class detects
   `π` as soon as `V(D') ⊄ W^p`, and `V|_W : w ↦ w^{|D_w|}`.  Since `W ≅ ℤ/n` with `p ∣ |W|`, this
   holds whenever `p ∤ |D_w|`; the on-disk level
   `Work.SSGRoute.E7cC.exists_level_unramified_p_dvd_inertiaDeg` (`e(q'|K) = 1`, `p ∣ |W| = f(q'|K)`)
   supplies exactly such a level.  Fired as
   `Work.SSGRoute.E7cOmega.unramifiedDetector_dwQuotientTransfer`, with hypotheses
   `hp : ¬ p ∣ |D_w|` (the transfer value is `|D_w| · m₀`), `hI₁ : I' ∩ N = 1` (unramifiedness: the
   inertia lies in no Mackey term) and `hsup : D' ⊔ N = ⊤` (single double coset), plus a detection
   input `m₀ = ψ (n^j)` with `n ∈ D' ∩ N` and `π m₀ ≠ 0`.  (Note: `hsup` forces `Gal(K/k) ≅ D'/W` to
   be a quotient of a decomposition group, hence solvable — harmless for this project, but a real
   constraint worth remembering.)

*(There is no "character-line case".)*  Suppose `χ₀ : G → 𝔽_p^×` and `φ : 𝔽_p →⁺ M` satisfy the twist
relation `M.ρ σ (φ x) = φ (χ₀(σ)·x)`, and `π ∘ φ` is injective on non-zero arguments.  Then for
`σ ∈ D_w` and any `x`, `π (φ (χ₀(σ)·x)) = π (M.ρ σ (φ x)) = π (φ x)`, so `χ₀(σ)·x = x` for
`x ≠ 0`, i.e. `χ₀|_{D_w} = 1`.  Since `π` takes values in the **trivial** module, every
one-dimensional submodule on which `π` is non-zero is automatically `D_w`-trivial — exactly the
condition under which the twisted cocycle `σ ↦ φ (χ₀(σ) - 1)` restricts to `0` on `D'` and detects
nothing.  (Confirmed independently by two referees when this route was submitted for review.)

**The gap.**  Branch 2 covers exactly `p ∤ |D_w|` (with `hsup` that is the regime
`p ∤ |Gal(K/k)|`).  In the remaining configurations (`M^Γ ⊆ ker π`, `p ∣ |D_w|`) the transfer is
*always* inside `W^p` (e.g. `D_w = I_w = ℤ/p`: then `|D'| = p|W|` and `D' = W × I'` are forced, so
`V(D') = V(W) = W^p`), so branch 2 gives nothing and branch 1 is excluded by hypothesis.  What remains
is a class in `H¹(Γ, M)` whose restriction to `N` is a prescribed `ψ ∈ Hom(N, M)` with vanishing
transgression — a *non-abelian* realisation problem (`Gal(L/k) = M ⋊ G` with the module action,
prescribing also the local structure at `q`), i.e. Shafarevich-type input.

**Imports a continuation needs** (add when the pieces below are available):
`Submission.Work.SSGRoute.Sha2Lib.exists_unramified_character_with_p_dvd_residueDeg`,
`Submission.Work.SSGRoute.Sha2Lib.extH_class_of_character`,
`Submission.Work.SSGRoute.ext_corestriction`,
`Submission.Work.SSGRoute.GrunwaldWang.grunwaldWang_corrected`.
-/

theorem unramifiedDetector_dwQuotient (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (π : Rep.res (decompK (k := k) (K := K) w).subtype M ⟶
      Rep.trivial Coeff (decompK (k := k) (K := K) w) (ZMod p))
    (hπ : Function.Surjective π.hom) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (h : extH (Rep.res (galRes k K ↥L) M) 1),
      IsUnramifiedClassAt q' h ∧
      q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
      (extHRestrict (decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h).comp
        (Abelian.Ext.mk₀ (Rep.resMap (decompKRestrict k K ↥L w
          (NK.GlobalCFT.Place.ofFinite q') hq') π)) (add_zero 1) ≠ 0 := by
  sorry

end Work.SSGRoute.E7cOmega
