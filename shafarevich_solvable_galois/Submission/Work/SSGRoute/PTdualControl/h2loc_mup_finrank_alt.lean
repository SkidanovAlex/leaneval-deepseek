import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.AbsoluteKummer.Kummer.kummerSES
import Submission.Work.AbsoluteKummer.SES.exists_connecting_exact_H2
import Submission.Work.AbsoluteKummer.Hilbert90.H1_eq_zero
import Submission.Work.SSGRoute.kummerBase_euler_h2transport
import Submission.Work.SSGRoute.PTembedding.KummerMuDefs
import Submission.Work.SSGRoute.PTCore.RootsOfUnityInstances
import Submission.Work.SSGRoute.PTCore.H2_level_defs
import Submission.Work.SSGRoute.PTCore.level_units_H2_cyclic
import Submission.Work.SSGRoute.PTCore.local_exists_degree_p_level
import Submission.Work.SSGRoute.PTCore.card_eq_prime_of_pairwise_dependent
import Submission.Work.SSGRoute.PTCore.zmultiples_pTorsion_int_dependent
import Submission.Work.SSGRoute.PTCore.h2loc_equiv_localGal_mup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p`-torsion of the local Brauer group: `H²(D_A, μ_p)` is one-dimensional

The target of this file is `Work.SSGRoute.PTCore.h2loc_mup_finrank`: for a finite place `A` of an
algebraic closure `Ω` of a number field `k`, a prime `p` and `μ_p = DualMod p T` (the cyclotomic
dual of a rank-one module `T`, `ζ_p ∈ K`),

  `dim_{𝔽_p} H²(D_A, μ_p) = 1`,   `D_A = SSGRoute.decomp k A`,

classically `H²(F, μ_p) ≅ Br(F)[p] ≅ ℤ/p` for the local field `F` at `A` (Kummer sequence, Hilbert
90, and `Br(F) ≅ ℚ/ℤ`); it holds for every prime `p`, including `p = 2`.

## What is proved here (sorry-free)

* `range_mapH2_eq_ker_mapH2` — exactness of the `H²`-row `H²(G,M) → H²(G,N) → H²(G,P)` of a short
  exact sequence of discrete `G`-modules in the continuous-cohomology model
  `Work.AbsoluteKummer`.  The workspace's `Work.AbsoluteKummer.SES` chapter supplies the
  connecting map `δ : H¹(G,P) → H²(G,M)` and the exactness `range δ = ker H²(ι)`
  (`range_deltaH2_eq_ker_mapH2`); the missing *other* half is proved here by the standard cocycle
  argument (lift the coboundary `π ∘ c` through a fixed section of `π`, and pull back along `ι`).

* `H2_rootsOfUnity_equiv_ptorsion_units` — the **Kummer identification**
  `H²(G_k, μ_p) ≅ H²(G_k, k̄ˣ)[p]` for any field `k` with algebraic closure: the Kummer short exact
  sequence `1 → μ_p → k̄ˣ --p--> k̄ˣ → 1` together with `H¹(G_k, k̄ˣ) = 0`
  (`Work.AbsoluteKummer.Hilbert90.H1_eq_zero`, Hilbert 90) gives the isomorphism.

## The route to the target, and the missing pieces

Every ingredient of the target that is *not* an instance of local class field theory is reduced
in the workspace; what is missing is the arithmetic of `Br(F) ≅ ℚ/ℤ`.  The route used below is
*not* the one recorded in `Submission/NK/LocalCFT/Brauer/Basic.lean` (which reduces the local
Brauer input to the trivial-coefficient statement `H²(G_κ, ℤ/p) ≠ 0` and, correctly, warns that
"the naive candidate — the fundamental class of a degree-`p` cyclic level — does not survive";
that warning applies to the *trivial*-coefficient finite-level statements, whose inflation maps
have the transgression in their kernel).  With **units** coefficients the corresponding
inflation maps are injective, because their kernel is a transgression out of `H¹(N, A)` with
`A = F̄ˣ`, which vanishes by Hilbert 90.  Concretely:

1. **Model bridge** (available): `Work.SSGRoute.H2loc … M (decomp k A) ≃+ H²_cont(D_A, M)`
   (`Work.SSGRoute.LTDDefs.H2locAddEquivH2`, `Work.SSGRoute.PT.H2locEquivH2_decomp`).

2. **Transfer to the completion** (missing, but glue rather than arithmetic).  Write
   `F = k_𝔭` for the completion of `k` at the prime below `A`.  Then `D_A ≅ Gal(Ω_A/F)` where
   `Ω_A` is the completion of `Ω` at `A`.  What is needed is the *level-wise* statement: for every
   finite normal `L/k` with `K ≤ L`,
   `D_A/(D_A ∩ Gal(Ω/L)) ≅ Gal(L_w/k_p)`  with `L_w = L ⊗ k_p`,
   compatibly with the action on `μ_p`.  Both halves are in the workspace
   (`map_restrictNormalHom_decomp_eq`, and `decompositionSubgroup_placeOf_mulEquiv_localGalois`
   in `Submission/NeukirchUchida/Local/PlaceFromValuation.lean`); what remains is (a) the module
   compatibility and (b) the two colimit descriptions (continuous `H²` with a *finite* coefficient
   module is the filtered colimit of `H²(G/U, M)` over the open normal `U` acting trivially on
   `M`; every class comes from a finite level because a locally constant cocycle factors through
   an open subgroup, and conversely a locally constant primitive has finite image, hence values in
   a finite level).  Cofinality of the levels `L_w` among the finite extensions of `F` is
   `Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional`.

3. **Kummer** (`H2_rootsOfUnity_equiv_ptorsion_units`, proved here): `H²(F, μ_p) ≅ Br(F)[p]`,
   where `Br(F) := H²_cont(G_F, F̄ˣ)`.

4. **`Br(F)[p] ≅ ℤ/p`** (the arithmetic core, reduced here to statements that are in the tree):
   * the canonical map `colim_E H²(Gal(E/F), Eˣ) → Br(F)` (over the finite Galois levels `E/F`)
     is bijective — surjective because a locally constant `2`-cocycle has finite image and
     factors through an open subgroup, injective because a locally constant primitive of a level
     cocycle has finite image and hence lives at a finite level;
   * at every finite Galois level `E/F` the group `H²(Gal(E/F), Eˣ)` is cyclic of order `[E : F]`:
     `Nat.card` is
     `Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_local_eq_finrank`,
     and a generator of order `[E : F]` is
     `Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units_adicCompletion`;
   * **upper bound** `dim Br(F)[p] ≤ 1`: given `x, y ∈ Br(F)[p]`, lift them to a common level `E`
     (the inflation maps are transitive); then `x, y` lie in `im(infl_E)[p]`, and since
     `im(infl_E)` is a quotient of the *cyclic* group `H²(Gal(E/F), Eˣ)`, its `p`-torsion is
     `0` or `ℤ/p` — no injectivity of inflation is needed for this half;
   * **lower bound** `Br(F)[p] ≠ 0`: take a level `E/F` of degree divisible by `p` (an unramified
     degree-`p` extension, or any cyclic level; note `p | [E:F]` for `E = F(μ_{p²})`).  The
     fundamental classes `u_E ∈ H²(Gal(E/F), Eˣ)` of the levels of `F^{ab}` form a *compatible*
     family with `levelInfHom L E h (u L) = [E:L] • u E`
     (`NK.NUV2.RouteE.exists_compatible_fundamentalClasses`, proved), so the image of
     `([E:F]/p) • u_E` in `Br(F)` is non-zero: an element of a directed colimit of groups is zero
     iff it becomes zero at some larger level, and every inflation of `u_E` is a non-zero multiple
     of a fundamental class.

5. **Assembly**: `dim H²_cont(D_A, μ_p) = dim Br(F)[p] = 1`, transported back along (1)–(2),
   using `Module.finrank` of an `AddEquiv`-image.

-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace Work.SSGRoute.PTdualControl

open Work.AbsoluteKummer

/-- The level structure of `H²(G_F, F̄ˣ)`: a compatible system of inflation maps from the finite
Galois levels, injective, with nested ranges and covering the colimit.  This is *verbatim* the
content of `Work.SSGRoute.PTCore.H2_units_level_structure` (`Submission/Work/SSGRoute/PTCore/
H2_units_level_structure.lean`), whose proof is the current target of the `PTCore` lane
(`H2_level_pieces.lean` proves its ingredients): this file consumes it as a hypothesis, so that
the reduction below is axiom-clean and can be applied the moment that node lands. -/
def H2LevelStructure (F : Type) [Field F] [IsGalois F (AlgebraicClosure F)] : Prop :=
  ∃ φ : ∀ L : FiniteGaloisIntermediateField F (AlgebraicClosure F),
      groupCohomology (Rep.ofAlgebraAutOnUnits F ↥L) 2 →+
        Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G F) (Additive (AlgebraicClosure F)ˣ),
    (∀ L : FiniteGaloisIntermediateField F (AlgebraicClosure F),
        Function.Injective (φ L)) ∧
    (∀ (L L' : FiniteGaloisIntermediateField F (AlgebraicClosure F)),
        (L : IntermediateField F (AlgebraicClosure F)) ≤ L' →
        Set.range (φ L) ⊆ Set.range (φ L')) ∧
    (∀ x : Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G F)
        (Additive (AlgebraicClosure F)ˣ),
      ∃ L : FiniteGaloisIntermediateField F (AlgebraicClosure F), x ∈ Set.range (φ L))

/- **Instance priorities.**  In this file's import closure a competing `Module`/`DistribMulAction`
instance for `Additive (rootsOfUnity p K)` shadows the pair whose `SMulCommClass` companion is
available, so that typeclass search fails on
`SMulCommClass (K ≃ₐ[k] K) (ZMod p) (Additive (rootsOfUnity p K))`.  Raising the priorities of the
three matching instances (the `Ω`-free ones of `PTCore/RootsOfUnityInstances.lean` and the Galois
action of `PTembedding/mup_kummer_defs.lean`) lets search find a consistent triple. -/
attribute [local instance 10000] Work.SSGRoute.PTCore.instModuleAddRootsOfUnityOfField
attribute [local instance 10000] Work.SSGRoute.PTCore.instSMulCommClassAddRootsOfUnityOfField
attribute [local instance 10000] Work.SSGRoute.PTembedding.MupKummer.instDistribMulActionAddRootsOfUnityOfField

universe u

section Exactness2

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]


/-! The `Ω`-free instances `instModuleAddRootsOfUnityOfField` and
`instSMulCommClassAddRootsOfUnityOfField` for the coefficient module `μ_p` live in
`Submission.Work.SSGRoute.PTCore.RootsOfUnityInstances` (imported above), so that statements
mentioning `μ_p` elaborate without explicit instance arguments. -/

/-- **Exactness of the `H²`-row of a short exact sequence of discrete `G`-modules.**

For `0 → M --ι--> N --π--> P → 0`, the induced sequence
`H²(G,M) --H²(ι)--> H²(G,N) --H²(π)--> H²(G,P)` is exact at `H²(G,N)`.

This is the degree-`2` piece of the long exact sequence that the workspace's
`Work.AbsoluteKummer.SES` chapter proves only up to the connecting map `δ : H¹(G,P) → H²(G,M)`
(`Work.AbsoluteKummer.SES.range_deltaH2_eq_ker_mapH2`); the piece proved here is the *other*
exactness, which turns the Kummer sequence into the identification
`H²(G,μ_p) ≅ H²(G,k̄ˣ)[p]`.

The proof is the standard cocycle computation: given a continuous `2`-cocycle `c` with values in
`N` whose image `π ∘ c` in `P` is a coboundary `d¹f`, lift `f` to a locally constant cochain `g`
with values in `N` (a fixed set-theoretic section of `π` composed with `f`), so that
`c' := c - d¹g` is a continuous `2`-cocycle with `π ∘ c' = 0`; `c'` therefore takes values in
`ker π = im ι`, and pulling back along the injective `ι` produces a continuous `2`-cocycle `c''`
with values in `M` whose image under `H²(ι)` is the class of `c`. -/
theorem range_mapH2_eq_ker_mapH2 (S : ShortExactSeq G M N P) :
    (mapH2 S.iota S.iota_equivariant).range = (mapH2 S.pi S.pi_equivariant).ker := by
  classical
  have hker : ∀ m : M, S.pi (S.iota m) = 0 := by
    intro m
    have hmem : S.iota m ∈ S.pi.ker := by
      rw [← S.range_iota_eq_ker_pi]
      exact AddMonoidHom.mem_range.mpr ⟨m, rfl⟩
    exact AddMonoidHom.mem_ker.mp hmem
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker]
    induction y using Work.AbsoluteKummer.SES.H2_induction_on with
    | h c =>
      rw [mapH2_H2π, mapH2_H2π, H2π_eq_zero_iff, mem_B2_iff]
      refine ⟨0, isLocallyConstant_const 0, ?_⟩
      funext p
      obtain ⟨a, b⟩ := p
      have h0 : Work.GroupCohomology.d1 G P (0 : G → P) = 0 := map_zero _
      rw [h0, mapZ2_apply]
      simp only [Pi.zero_apply]
      exact (hker ((c : G × G → M) (a, b))).symm
  · intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    induction x using Work.AbsoluteKummer.SES.H2_induction_on with
    | h c =>
      rw [mapH2_H2π, H2π_eq_zero_iff, mem_B2_iff] at hx
      obtain ⟨f, hfC, hfd⟩ := hx
      let liftP : P → N := fun q => Classical.choose (S.pi_surjective q)
      have hliftP_spec : ∀ q : P, S.pi (liftP q) = q :=
        fun q => Classical.choose_spec (S.pi_surjective q)
      let g : G → N := fun γ => liftP (f γ)
      have hgC : g ∈ C1c G N := by
        show AbsoluteKummer.IsLocallyConstant (fun γ => liftP (f γ))
        exact AbsoluteKummer.IsLocallyConstant.map liftP hfC
      have hgpi : ∀ γ : G, S.pi (g γ) = f γ := fun γ => hliftP_spec (f γ)
      have hd1gZ : Work.GroupCohomology.d1 G N g ∈ Z2 G N :=
        B2_le_Z2 S.isDiscreteN (by rw [mem_B2_iff]; exact ⟨g, hgC, rfl⟩)
      have hc'Z : (fun p : G × G => (c : G × G → N) p
          - Work.GroupCohomology.d1 G N g p) ∈ Z2 G N :=
        sub_mem c.2 hd1gZ
      have hc'pi : ∀ p : G × G,
          S.pi ((c : G × G → N) p - Work.GroupCohomology.d1 G N g p) = 0 := by
        intro p
        have h1 : S.pi (Work.GroupCohomology.d1 G N g p)
            = Work.GroupCohomology.d1 G P (fun γ => S.pi (g γ)) p :=
          congrFun (Work.GroupCohomology.mapCochain2_d1 G S.pi S.pi_equivariant g) p
        rw [map_sub, h1, show (fun γ => S.pi (g γ)) = f from funext hgpi]
        have h3 : Work.GroupCohomology.d1 G P f p = S.pi ((c : G × G → N) p) :=
          congrFun hfd p
        rw [h3, sub_self]
      have hc'inrange : ∀ p : G × G,
          ((c : G × G → N) p - Work.GroupCohomology.d1 G N g p) ∈ S.iota.range := by
        intro p
        rw [S.range_iota_eq_ker_pi]
        exact AddMonoidHom.mem_ker.mpr (hc'pi p)
      let iotaInv : N → M := fun n => if h : n ∈ S.iota.range then
        Classical.choose ((AddMonoidHom.mem_range).mp h) else 0
      have hiotaInv_spec : ∀ n : N, n ∈ S.iota.range → S.iota (iotaInv n) = n := by
        intro n hn
        have h1 : iotaInv n = Classical.choose ((AddMonoidHom.mem_range).mp hn) := by
          dsimp only [iotaInv]
          rw [dif_pos hn]
        rw [h1]
        exact Classical.choose_spec ((AddMonoidHom.mem_range).mp hn)
      have hc''spec : ∀ p : G × G, S.iota (iotaInv ((c : G × G → N) p
          - Work.GroupCohomology.d1 G N g p))
          = (c : G × G → N) p - Work.GroupCohomology.d1 G N g p :=
        fun p => hiotaInv_spec _ (hc'inrange p)
      have hc''Z : (fun p : G × G => iotaInv ((c : G × G → N) p
          - Work.GroupCohomology.d1 G N g p)) ∈ Z2 G M := by
        rw [mem_Z2_iff]
        refine ⟨?_, ?_⟩
        · intro a b d
          have hc'id := ((mem_Z2_iff (fun p : G × G => (c : G × G → N) p
            - Work.GroupCohomology.d1 G N g p)).mp hc'Z).1 a b d
          apply S.iota_injective
          have hstep : S.iota (a • (fun p : G × G => iotaInv ((c : G × G → N) p
              - Work.GroupCohomology.d1 G N g p)) (b, d))
              = a • ((c : G × G → N) (b, d)
                - Work.GroupCohomology.d1 G N g (b, d)) := by
            rw [S.iota_equivariant a, hc''spec (b, d)]
          rw [map_add, map_add, hstep, hc''spec (a * b, d), hc''spec (a, b),
            hc''spec (a, b * d)]
          exact hc'id
        · exact AbsoluteKummer.IsLocallyConstant.map iotaInv
            (((mem_Z2_iff (fun p : G × G => (c : G × G → N) p
              - Work.GroupCohomology.d1 G N g p)).mp hc'Z).2)
      refine ⟨H2π G M ⟨_, hc''Z⟩, ?_⟩
      rw [mapH2_H2π]
      have h2 : mapZ2 S.iota S.iota_equivariant (⟨_, hc''Z⟩ : Z2 G M)
          = (⟨fun p : G × G => (c : G × G → N) p - Work.GroupCohomology.d1 G N g p,
              hc'Z⟩ : Z2 G N) := by
        refine Subtype.ext ?_
        funext p
        rw [mapZ2_apply]
        exact hc''spec p
      rw [h2, H2π_eq_iff, mem_B2_iff]
      refine ⟨-g, neg_mem hgC, ?_⟩
      funext p
      obtain ⟨a, b⟩ := p
      simp only [AddSubgroup.coe_sub, Pi.sub_apply, Pi.neg_apply,
        Work.GroupCohomology.d1_apply, smul_neg]
      abel

end Exactness2

section Kummer

/-- **Kummer theory: `H²(G_k, μ_p)` is the `p`-torsion of `H²(G_k, k̄ˣ)`.**

The Kummer sequence `1 → μ_p → k̄ˣ → k̄ˣ → 1` (the `p`-th power map on the units of an
algebraically closed field) gives an exact sequence
`H²(G_k, μ_p) → H²(G_k, k̄ˣ) --p--> H²(G_k, k̄ˣ)`, and `H¹(G_k, k̄ˣ) = 0` (Hilbert 90) makes the
first map injective.  Hence `H²(G_k, μ_p)` is the `p`-torsion of `H²(G_k, k̄ˣ)` — the
`p`-torsion of the Brauer group `Br(k)` in the case of a local field `k`. -/
theorem H2_rootsOfUnity_equiv_ptorsion_units (k : Type*) [Field k]
    [IsGalois k (AlgebraicClosure k)] (p : ℕ) [Fact p.Prime] :
    Nonempty (H2 (G k) (Additive (rootsOfUnity p (AlgebraicClosure k))) ≃+
      ↥(mapH2 (Kummer.kummerPi (k := k) p) (Kummer.kummerPi_equivariant (k := k) p)).ker) := by
  classical
  let S : ShortExactSeq (G k) (Additive (rootsOfUnity p (AlgebraicClosure k)))
      (Additive (AlgebraicClosure k)ˣ) (Additive (AlgebraicClosure k)ˣ) :=
    { iota := Kummer.kummerIota (k := k) p
      pi := Kummer.kummerPi (k := k) p
      iota_equivariant := Kummer.kummerIota_equivariant (k := k) p
      pi_equivariant := Kummer.kummerPi_equivariant (k := k) p
      iota_injective := Kummer.kummerIota_injective (k := k) p
      pi_surjective := Kummer.kummerPi_surjective (k := k) p
      range_iota_eq_ker_pi := Kummer.kummerIota_range_eq_ker_pi (k := k) p
      isDiscreteM := isDiscreteModule_addRootsOfUnity k p
      isDiscreteN := isDiscreteModule_addUnits k
      isDiscreteP := isDiscreteModule_addUnits k }
  have h1zero : Subsingleton (H1 (G k) (Additive (AlgebraicClosure k)ˣ)) :=
    ⟨fun a b => by rw [Hilbert90.H1_eq_zero (k := k) a, Hilbert90.H1_eq_zero (k := k) b]⟩
  have hdelta : S.deltaH2 = 0 :=
    AddMonoidHom.ext (fun y => by
      have hy : y = 0 := Subsingleton.elim y 0
      rw [hy, map_zero, AddMonoidHom.zero_apply])
  have hker : (mapH2 S.iota S.iota_equivariant).ker = ⊥ := by
    rw [← SES.range_deltaH2_eq_ker_mapH2 S, hdelta, AddMonoidHom.range_zero]
  have hrange : (mapH2 S.iota S.iota_equivariant).range
      = (mapH2 S.pi S.pi_equivariant).ker := range_mapH2_eq_ker_mapH2 S
  have hinj : Function.Injective (mapH2 S.iota S.iota_equivariant) := by
    intro x y hxy
    have h : x - y = 0 := by
      have hm : x - y ∈ (mapH2 S.iota S.iota_equivariant).ker := by
        rw [AddMonoidHom.mem_ker, map_sub, hxy, sub_self]
      rw [hker] at hm
      simpa using hm
    exact sub_eq_zero.mp h
  refine ⟨AddEquiv.ofBijective
    ({ toFun := fun x => ⟨mapH2 S.iota S.iota_equivariant x, by
          rw [← hrange]
          exact ⟨x, rfl⟩⟩
       map_zero' := Subtype.ext (map_zero _)
       map_add' := fun x y => Subtype.ext (map_add _ _ _) }
      : H2 (G k) (Additive (rootsOfUnity p (AlgebraicClosure k))) →+
        ↥(mapH2 S.pi S.pi_equivariant).ker)
    ⟨fun x y hxy => hinj (Subtype.ext_iff.mp hxy), fun y => ?_⟩⟩
  have hy' : y.1 ∈ (mapH2 S.iota S.iota_equivariant).range := by
    rw [hrange]
    exact y.2
  obtain ⟨x, hx⟩ := hy'
  exact ⟨x, Subtype.ext hx⟩

end Kummer


section CoeffTransfer

/-- **The coefficient identification: the local `H²` with coefficients `DualMod p T` is the local
`H²` with coefficients in the `p`-th roots of unity `μ_p ⊆ K`.**

For `T` a cyclotomic dual, `DualMod p T ≅ μ_p` as `𝔽_p[Gal(K/k)]`-modules through the equivariant
linear isomorphism `Work.SSGRoute.PTembedding.MupCard.dualModEquivMu` (`dualModEquivMu_smul`), and pushing
locally constant `2`-cocycles along an equivariant linear isomorphism of coefficient modules
(`Work.SSGRoute.H2locPush`) gives an additive equivalence of the local `H²`-groups.  This is the
reduction that lets the target be stated with `μ_p`, for which the Kummer sequence (and hence the
Kummer identification `H2_rootsOfUnity_equiv_ptorsion_units`) is available. -/
theorem h2loc_addEquiv_dualMod_mu
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Nonempty (Work.SSGRoute.H2loc p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A) ≃+
      Work.SSGRoute.H2loc p k Ω K (Additive (rootsOfUnity p K)) (SSGRoute.decomp k A)) := by
  classical
  let e : Work.SSGRoute.DualMod p T ≃ₗ[ZMod p] Additive (rootsOfUnity p K) :=
    Work.SSGRoute.PTembedding.MupCard.dualModEquivMu hT hζ hζK
  have hev : ∀ (g : K ≃ₐ[k] K) (m : Work.SSGRoute.DualMod p T), e (g • m) = g • e m :=
    fun g m => Work.SSGRoute.PTembedding.MupCard.dualModEquivMu_smul hT hζ hζK g m
  have hsym : ∀ (g : K ≃ₐ[k] K) (m : Additive (rootsOfUnity p K)),
      e.symm (g • m) = g • e.symm m :=
    Work.SSGRoute.linearEquiv_symm_equivariant2 e hev
  have key : ∀ z : Work.SSGRoute.H2loc p k Ω K (Work.SSGRoute.DualMod p T)
        (SSGRoute.decomp k A),
      Work.SSGRoute.H2locPush (H := SSGRoute.decomp k A) e.symm.toLinearMap hsym
        (Work.SSGRoute.H2locPush (H := SSGRoute.decomp k A) e.toLinearMap hev z) = z := by
    intro z
    refine Submodule.Quotient.induction_on _ z (fun c => ?_)
    rw [Work.SSGRoute.H2locPush_mk, Work.SSGRoute.H2locPush_mk, Submodule.Quotient.eq]
    have h0 : Work.SSGRoute.pushCocycles2 (H := SSGRoute.decomp k A) e.symm.toLinearMap hsym
        (Work.SSGRoute.pushCocycles2 (H := SSGRoute.decomp k A) e.toLinearMap hev c) = c := by
      apply Subtype.ext
      ext g h
      simp
    rw [h0, sub_self]
    exact Submodule.zero_mem _
  have key' : ∀ z : Work.SSGRoute.H2loc p k Ω K (Additive (rootsOfUnity p K))
        (SSGRoute.decomp k A),
      Work.SSGRoute.H2locPush (H := SSGRoute.decomp k A) e.toLinearMap hev
        (Work.SSGRoute.H2locPush (H := SSGRoute.decomp k A) e.symm.toLinearMap hsym z) = z := by
    intro z
    refine Submodule.Quotient.induction_on _ z (fun c => ?_)
    rw [Work.SSGRoute.H2locPush_mk, Work.SSGRoute.H2locPush_mk, Submodule.Quotient.eq]
    have h0 : Work.SSGRoute.pushCocycles2 (H := SSGRoute.decomp k A) e.toLinearMap hev
        (Work.SSGRoute.pushCocycles2 (H := SSGRoute.decomp k A) e.symm.toLinearMap hsym c) = c := by
      apply Subtype.ext
      ext g h
      simp
    rw [h0, sub_self]
    exact Submodule.zero_mem _
  refine ⟨AddEquiv.ofBijective
    (Work.SSGRoute.H2locPush (H := SSGRoute.decomp k A) e.toLinearMap hev) ⟨?_, ?_⟩⟩
  · intro x y hxy
    rw [← key x, ← key y, hxy]
  · intro y
    exact ⟨Work.SSGRoute.H2locPush (H := SSGRoute.decomp k A) e.symm.toLinearMap hsym y, key' y⟩

end CoeffTransfer


section LocalArithmetic

open Work.AbsoluteKummer

/-- The `p`-th power map on the units `k̄ˣ` is multiplication by `p`. -/
theorem kummerPi_apply_eq_nsmul (k : Type*) [Field k] (p : ℕ)
    (a : Additive (AlgebraicClosure k)ˣ) :
    Kummer.kummerPi (k := k) p a = p • a := by
  rw [Kummer.kummerPi_apply]
  exact (Work.SSGRoute.PTembedding.MupCard.ofMul_nsmul p (Additive.toMul a)).symm

/-- **The map induced by the `p`-th power map on the units is multiplication by `p`.** -/
theorem mapH2_kummerPi_eq_nsmul (k : Type*) [Field k] [IsGalois k (AlgebraicClosure k)]
    (p : ℕ) :
    ∀ x : Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G k) (Additive (AlgebraicClosure k)ˣ),
      Work.AbsoluteKummer.mapH2 (Kummer.kummerPi (k := k) p)
        (Kummer.kummerPi_equivariant (k := k) p) x = p • x := by
  intro x
  induction x using Work.AbsoluteKummer.SES.H2_induction_on with
  | h c =>
  rw [Work.AbsoluteKummer.mapH2_H2π]
  have hcoe : ((Work.AbsoluteKummer.mapZ2 (Kummer.kummerPi (k := k) p)
        (Kummer.kummerPi_equivariant (k := k) p) c :
      Work.AbsoluteKummer.Z2 (Work.AbsoluteKummer.G k) (Additive (AlgebraicClosure k)ˣ)) :
      (Work.AbsoluteKummer.G k) × (Work.AbsoluteKummer.G k) → Additive (AlgebraicClosure k)ˣ)
      = p • ((c : Work.AbsoluteKummer.Z2 (Work.AbsoluteKummer.G k)
        (Additive (AlgebraicClosure k)ˣ)) :
        (Work.AbsoluteKummer.G k) × (Work.AbsoluteKummer.G k) → Additive (AlgebraicClosure k)ˣ) := by
    funext q
    rw [Pi.smul_apply, Work.AbsoluteKummer.mapZ2_apply]
    exact kummerPi_apply_eq_nsmul k p (c.1 q)
  rw [show Work.AbsoluteKummer.mapZ2 (Kummer.kummerPi (k := k) p)
        (Kummer.kummerPi_equivariant (k := k) p) c = p • c from Subtype.ext hcoe,
      map_nsmul]

/-- **The `p`-torsion of the local Brauer group of a `p`-adic field has `p` elements.** -/
theorem natCard_H2_rootsOfUnity_adicCompletion (p : ℕ) [Fact p.Prime] {K : Type} [Field K]
    [NumberField K] (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hstruct : H2LevelStructure (Q.adicCompletion K)) :
    Nat.card (Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G (Q.adicCompletion K))
      (Additive (rootsOfUnity p (AlgebraicClosure (Q.adicCompletion K))))) = p := by
  classical
  haveI hgal : IsGalois (Q.adicCompletion K) (AlgebraicClosure (Q.adicCompletion K)) :=
    inferInstance
  obtain ⟨eK⟩ := H2_rootsOfUnity_equiv_ptorsion_units (k := Q.adicCompletion K) p
  obtain ⟨φ, hφinj, hφmono, hφcov⟩ := hstruct
  set W := Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G (Q.adicCompletion K))
    (Additive (AlgebraicClosure (Q.adicCompletion K))ˣ) with hW
  set T : AddSubgroup W :=
    (Work.AbsoluteKummer.mapH2 (Kummer.kummerPi (k := Q.adicCompletion K) p)
      (Kummer.kummerPi_equivariant (k := Q.adicCompletion K) p)).ker with hT
  have hTmem : ∀ x : W, x ∈ T ↔ p • x = 0 := by
    intro x
    rw [hT, AddMonoidHom.mem_ker, mapH2_kummerPi_eq_nsmul (Q.adicCompletion K) p x]
  haveI : Module (ZMod p) ↥T := AddCommGroup.zmodModule (n := p) (G := ↥T) (fun x : ↥T => by
    refine Subtype.ext ?_
    simpa using (hTmem x.1).mp x.2)
  have hcyc : ∀ L : FiniteGaloisIntermediateField (Q.adicCompletion K)
      (AlgebraicClosure (Q.adicCompletion K)), ∃ w : W, Set.range (φ L) ⊆ AddSubgroup.zmultiples w := by
    intro L
    obtain ⟨u, hgen, -⟩ := Work.SSGRoute.PTCore.level_units_H2_cyclic (K := K) Q
      (L : IntermediateField (Q.adicCompletion K) (AlgebraicClosure (Q.adicCompletion K)))
    refine ⟨φ L u, ?_⟩
    rintro _ ⟨y, hy⟩
    have hy' : y ∈ AddSubgroup.zmultiples u := by rw [hgen]; trivial
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hy'
    exact ⟨m, by rw [← hy, ← hm, map_zsmul]⟩
  have hdep : ∀ x y : ↥T, ∃ c d : ZMod p, (c, d) ≠ 0 ∧ c • x + d • y = 0 := by
    intro x y
    have hpx : p • (x : W) = 0 := (hTmem x.1).mp x.2
    have hpy : p • (y : W) = 0 := (hTmem y.1).mp y.2
    obtain ⟨Lx, hLx⟩ := hφcov x.1
    obtain ⟨Ly, hLy⟩ := hφcov y.1
    have hxr : x.1 ∈ Set.range (φ (Lx ⊔ Ly)) := by
      refine hφmono Lx (Lx ⊔ Ly) ?_ hLx
      exact le_sup_left
    have hyr : y.1 ∈ Set.range (φ (Lx ⊔ Ly)) := by
      refine hφmono Ly (Lx ⊔ Ly) ?_ hLy
      exact le_sup_right
    obtain ⟨w, hw⟩ := hcyc (Lx ⊔ Ly)
    obtain ⟨m, n, hmn, hsum⟩ :=
      Work.SSGRoute.PTCore.zmultiples_pTorsion_int_dependent p w x.1 y.1 (hw hxr) (hw hyr) hpx hpy
    refine ⟨(m : ZMod p), (n : ZMod p), ?_, ?_⟩
    · intro h0
      exact hmn ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd m p).mp (congrArg Prod.fst h0),
        (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp (congrArg Prod.snd h0)⟩
    · refine Subtype.ext ?_
      rw [Int.cast_smul_eq_zsmul (ZMod p) m x, Int.cast_smul_eq_zsmul (ZMod p) n y]
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_zero, AddSubgroup.coe_zsmul]
      exact hsum
  have hne : ∃ z : ↥T, z ≠ 0 := by
    obtain ⟨L, hfd, hLgal, hdvd⟩ := Work.SSGRoute.PTCore.local_exists_degree_p_level (K := K) p Q
    haveI := hfd
    haveI := hLgal
    let Lfg : FiniteGaloisIntermediateField (Q.adicCompletion K)
        (AlgebraicClosure (Q.adicCompletion K)) :=
      { toIntermediateField := L, finiteDimensional := hfd, isGalois := hLgal }
    obtain ⟨u, hgen, hord⟩ := Work.SSGRoute.PTCore.level_units_H2_cyclic (K := K) Q L
    have hn0 : Module.finrank (Q.adicCompletion K) ↥L ≠ 0 :=
      ne_of_gt ((Module.finrank_pos_iff_of_free (Q.adicCompletion K) ↥L).mpr inferInstance)
    obtain ⟨m, hm⟩ := hdvd
    have hpu : p • (m • u) = 0 := by
      rw [← mul_nsmul' u p m, ← hm, ← hord]
      exact addOrderOf_nsmul_eq_zero u
    have hne0 : m • u ≠ 0 := by
      intro h0
      have hd : Module.finrank (Q.adicCompletion K) ↥L ∣ m := by
        rw [← hord, addOrderOf_dvd_iff_nsmul_eq_zero]
        exact h0
      have hmp : m ≠ 0 := by
        intro h0'
        apply hn0
        calc Module.finrank (Q.adicCompletion K) ↥L = p * m := hm
          _ = 0 := by rw [h0', mul_zero]
      have hmlt : m < Module.finrank (Q.adicCompletion K) ↥L := by
        rw [hm]
        simpa using Nat.mul_lt_mul_of_pos_right (Fact.out : p.Prime).one_lt
          (Nat.pos_of_ne_zero hmp)
      have hm0 : m = 0 := Nat.eq_zero_of_dvd_of_lt hd hmlt
      apply hn0
      calc Module.finrank (Q.adicCompletion K) ↥L = p * m := hm
        _ = 0 := by rw [hm0, mul_zero]
    refine ⟨⟨φ Lfg (m • u), ?_⟩, ?_⟩
    · rw [hTmem, ← map_nsmul, hpu, map_zero]
    · intro hz
      have h1 : φ Lfg (m • u) = 0 := congrArg Subtype.val hz
      exact hne0 (hφinj Lfg (by rw [h1, map_zero]))
  have hTcard : Nat.card ↥T = p := Work.SSGRoute.PTCore.card_eq_prime_of_pairwise_dependent p hdep hne
  exact (Nat.card_congr eK.toEquiv).trans hTcard

end LocalArithmetic

/-- **The `p`-torsion of the local Brauer group: `H²(D_A, μ_p)` is one-dimensional.**

For a finite place `A` of `Ω` over `k` and `μ_p = DualMod p T` (the cyclotomic dual of `T`), the
second local cohomology of the decomposition group with coefficients in `μ_p` is one-dimensional
over `𝔽_p`: classically `H²(F, μ_p) ≅ Br(F)[p] ≅ ℤ/p` for the local field `F` at `A` (Kummer
sequence plus `Br(F) ≅ ℚ/ℤ`), for every prime `p` including `p = 2`.

This is the base case of `Work.SSGRoute.local_tate_duality_02` at `M = μ_p` (there the two sides
are `1` and `dim H⁰(D_A, DualMod p T^∨(1)) = 1`), and one of the two arithmetic inputs of the
residue-characteristic case of the local Euler characteristic
(`Work.SSGRoute.local_tate_duality_euler`), the `E7` node of `DESIGN_PT.md`. -/
theorem h2loc_mup_finrank_alt
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hstruct : H2LevelStructure ((Submission.NeukirchUchida.primeOf A hA).adicCompletion k)) :
    Module.finrank (ZMod p)
      (Work.SSGRoute.H2loc p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A)) = 1 := by
  classical
  obtain ⟨e1⟩ := h2loc_addEquiv_dualMod_mu p k Ω K ζ hζ hζK T hT A hA
  obtain ⟨e2⟩ := Work.SSGRoute.PTCore.h2loc_equiv_localGal_mup p k Ω K ζ hζ hζK A hA
  have harith : Nat.card (Work.AbsoluteKummer.H2
      (Work.AbsoluteKummer.G (Work.SSGRoute.PTembedding.localFieldOf k A hA))
      (Additive (rootsOfUnity p
        (AlgebraicClosure (Work.SSGRoute.PTembedding.localFieldOf k A hA))))) = p :=
    natCard_H2_rootsOfUnity_adicCompletion p (Submission.NeukirchUchida.primeOf A hA) hstruct
  set V := Work.SSGRoute.H2loc p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A) with hV
  have hcard : Nat.card V = p := (Nat.card_congr (e1.trans e2).toEquiv).trans harith
  haveI : Finite V :=
    (Nat.card_ne_zero.mp (by rw [hcard]; exact (Fact.out : p.Prime).ne_zero)).2
  haveI : Fintype V := Fintype.ofFinite V
  have hcard2 : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    rw [Nat.card_eq_fintype_card]
    rw [@Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hkey : p ^ (1 : ℕ) = p ^ Module.finrank (ZMod p) V := by
    rw [pow_one]
    exact hcard.symm.trans hcard2
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le hkey).symm

end Work.SSGRoute.PTdualControl
