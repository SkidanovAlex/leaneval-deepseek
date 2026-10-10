import Mathlib.FieldTheory.KrullTopology
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.range_deltaH3_eq_ker_mapH3
import Submission.Work.SSGRoute.range_mapH2_eq_ker_deltaH3
import Submission.Work.SSGRoute.sha2_transport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTembedding

open Work.AbsoluteKummer

/-! ## Functoriality of `H³` is injective when the coefficient map has a left inverse -/

/-- If an equivariant additive map `φ : M →+ N` has an equivariant additive left inverse `ψ`,
then the induced map `H³(G,M) →+ H³(G,N)` is injective. -/
lemma mapH3_injective_of_leftInverse {G : Type*} [TopologicalSpace G] [Group G]
    {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    {N : Type*} [AddCommGroup N] [DistribMulAction G N]
    (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (ψ : N →+ M) (hψ : Work.GroupCohomology.IsEquivariant G ψ)
    (hleft : ∀ m : M, ψ (φ m) = m) :
    Function.Injective (Work.SSGRoute.H3Map.mapH3 φ hφ) := by
  rw [← AddMonoidHom.ker_eq_bot_iff]
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx
  rw [AddSubgroup.mem_bot]
  refine (Work.SSGRoute.H3Map.H3_induction_on x
    (C := fun z => Work.SSGRoute.H3Map.mapH3 φ hφ z = 0 → z = 0) ?_) hx
  intro c hc
  rw [Work.SSGRoute.H3Map.mapH3_H3π, Work.SSGRoute.H3π_eq_zero_iff,
    Work.SSGRoute.mem_B3_iff] at hc
  obtain ⟨b, hblc, hb⟩ := hc
  rw [Work.SSGRoute.H3π_eq_zero_iff, Work.SSGRoute.mem_B3_iff]
  refine ⟨Work.GroupCohomology.mapCochain2 G ψ b,
    Work.AbsoluteKummer.IsLocallyConstant.map ψ hblc, ?_⟩
  have hgoal : Work.GroupCohomology.mapCochain3 G ψ
      ((Work.SSGRoute.H3Map.mapZ3 φ hφ c : G × G × G → N)) = (c : G × G × G → M) := by
    funext q
    rw [Work.GroupCohomology.mapCochain3_apply]
    show ψ (φ ((c : G × G × G → M) q)) = (c : G × G × G → M) q
    rw [hleft]
  rw [← Work.GroupCohomology.mapCochain3_d2 G ψ hψ b, hb]
  exact hgoal

/-! ## `H³(k, μ_p) = 0` when `H³(k, k̄ˣ) = 0` and `H²(k, k̄ˣ)` is `p`-divisible -/

/-- **The main reduction.**  For a field `k` containing a primitive `p`-th root of unity `ζ`, if
`H³(G_k, k̄ˣ) = 0` and `H²(G_k, k̄ˣ)` is `p`-divisible, then `H³(G_k, 𝔽_p) = 0`.

The proof runs the Kummer short exact sequence `0 → μ_p → k̄ˣ →^p k̄ˣ → 0` through the
`2 → 3` segment of the long exact sequence:

* `H²(G_k, k̄ˣ) →^{π} H²(G_k, k̄ˣ)` is multiplication by `p` (because `π = (· ^ p)`), hence
  surjective by the divisibility hypothesis;
* exactness at `H²(G_k, k̄ˣ)` gives `ker δ³ = range H²(π) = ⊤`, i.e. `δ³ = 0`;
* exactness at `H³(G_k, μ_p)` gives `ker H³(ι) = range δ³ = ⊥`, so `H³(ι)` is injective;
* as `H³(G_k, k̄ˣ) = 0` and `H³(ι) : H³(G_k, μ_p) → H³(G_k, k̄ˣ)` is injective, `H³(G_k, μ_p) = 0`;
* transporting along the equivariant isomorphism `𝔽_p ≅ μ_p`, also `H³(G_k, 𝔽_p) = 0`. -/
theorem h3_mup_subsingleton_of_units_divisible (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (hμ : ∃ ζ : k, IsPrimitiveRoot ζ p)
    (hunits : Subsingleton
      (Work.SSGRoute.H3 (M := Additive (AlgebraicClosure k)ˣ) (Work.AbsoluteKummer.G k)))
    (hdiv : ∀ x : Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G k)
      (Additive (AlgebraicClosure k)ˣ), ∃ y, p • y = x) :
    Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p)
      (Work.AbsoluteKummer.G k)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- the Kummer short exact sequence `0 → μ_p → k̄ˣ →^p k̄ˣ → 0`
  let S : Work.AbsoluteKummer.ShortExactSeq (Work.AbsoluteKummer.G k)
      (Additive (rootsOfUnity p (AlgebraicClosure k)))
      (Additive (AlgebraicClosure k)ˣ) (Additive (AlgebraicClosure k)ˣ) :=
    { iota := Work.AbsoluteKummer.Kummer.kummerIota (k := k) p
      pi := Work.AbsoluteKummer.Kummer.kummerPi (k := k) p
      iota_equivariant := Work.AbsoluteKummer.Kummer.kummerIota_equivariant (k := k) p
      pi_equivariant := Work.AbsoluteKummer.Kummer.kummerPi_equivariant (k := k) p
      iota_injective := Work.AbsoluteKummer.Kummer.kummerIota_injective (k := k) p
      pi_surjective := Work.AbsoluteKummer.Kummer.kummerPi_surjective (k := k) p
      range_iota_eq_ker_pi := Work.AbsoluteKummer.Kummer.kummerIota_range_eq_ker_pi (k := k) p
      isDiscreteM := Work.AbsoluteKummer.isDiscreteModule_addRootsOfUnity k p
      isDiscreteN := Work.AbsoluteKummer.isDiscreteModule_addUnits k
      isDiscreteP := Work.AbsoluteKummer.isDiscreteModule_addUnits k }
  -- `π` is multiplication by `p` on the units
  have hpow : ∀ x : Additive (AlgebraicClosure k)ˣ,
      Work.AbsoluteKummer.Kummer.kummerPi (k := k) p x = p • x := by
    intro x
    apply Additive.toMul.injective
    rw [Work.AbsoluteKummer.Kummer.kummerPi_apply, toMul_ofMul, toMul_nsmul]
  -- hence `H²(π)` is multiplication by `p`, which is surjective by hypothesis
  have hsurj : Function.Surjective
      (Work.AbsoluteKummer.mapH2 S.pi S.pi_equivariant) := by
    intro y
    obtain ⟨z, hz⟩ := hdiv y
    obtain ⟨c, hc⟩ :=
      (QuotientAddGroup.mk'_surjective
        ((Work.AbsoluteKummer.B2 (Work.AbsoluteKummer.G k)
          (Additive (AlgebraicClosure k)ˣ)).comap
          (Work.AbsoluteKummer.Z2 (Work.AbsoluteKummer.G k)
            (Additive (AlgebraicClosure k)ˣ)).subtype)) z
    rw [← hc] at hz
    refine ⟨Work.AbsoluteKummer.H2π (Work.AbsoluteKummer.G k)
      (Additive (AlgebraicClosure k)ˣ) c, ?_⟩
    have hmapZ : Work.AbsoluteKummer.mapZ2 S.pi S.pi_equivariant c = p • c := by
      apply Subtype.ext
      funext q
      rw [Work.AbsoluteKummer.mapZ2_apply]
      exact hpow _
    rw [Work.AbsoluteKummer.mapH2_H2π, hmapZ, map_nsmul]
    simpa only [Work.AbsoluteKummer.H2π] using hz
  -- exactness at `H²(G, k̄ˣ)` forces `δ³ = 0`
  have hker : S.deltaH3.ker = ⊤ := by
    rw [← Work.SSGRoute.range_mapH2_eq_ker_deltaH3 S]
    exact AddMonoidHom.range_eq_top.mpr hsurj
  have hzero : S.deltaH3 = 0 := (AddMonoidHom.ker_eq_top_iff).mp hker
  -- exactness at `H³(G, μ_p)` then forces `H³(ι)` to be injective
  have hker2 : (Work.SSGRoute.H3Map.mapH3 S.iota S.iota_equivariant).ker = ⊥ := by
    rw [← Work.SSGRoute.range_deltaH3_eq_ker_mapH3 S, hzero]
    simp
  have hinj : Function.Injective (Work.SSGRoute.H3Map.mapH3 S.iota S.iota_equivariant) :=
    (AddMonoidHom.ker_eq_bot_iff _).mp hker2
  haveI hB : Subsingleton
      (Work.SSGRoute.H3 (M := Additive (AlgebraicClosure k)ˣ) (Work.AbsoluteKummer.G k)) :=
    hunits
  haveI : Subsingleton
      (Work.SSGRoute.H3 (M := Additive (rootsOfUnity p (AlgebraicClosure k)))
        (Work.AbsoluteKummer.G k)) :=
    ⟨fun a b => hinj (Subsingleton.elim _ _)⟩
  -- transport along the equivariant isomorphism `𝔽_p ≅ μ_p`
  let φ : Work.SSGRoute.Triv p →+ Additive (rootsOfUnity p (AlgebraicClosure k)) :=
    Work.SSGRoute.muAddEquiv k p hμ
  let ψ : Additive (rootsOfUnity p (AlgebraicClosure k)) →+ Work.SSGRoute.Triv p :=
    (Work.SSGRoute.muAddEquiv k p hμ).symm
  have hφe : Work.GroupCohomology.IsEquivariant (Work.AbsoluteKummer.G k) φ :=
    Work.SSGRoute.muAddEquiv_equivariant k p hμ
  have hψe : Work.GroupCohomology.IsEquivariant (Work.AbsoluteKummer.G k) ψ :=
    Work.SSGRoute.muAddEquiv_symm_equivariant k p hμ
  have hinjφ : Function.Injective (Work.SSGRoute.H3Map.mapH3 φ hφe) :=
    mapH3_injective_of_leftInverse φ hφe ψ hψe (fun m => by simp [φ, ψ])
  exact ⟨fun a b => hinjφ (Subsingleton.elim _ _)⟩

theorem h3_triv_subsingleton_of_units_divisible (p : ℕ) [Fact p.Prime] {K : Type} [Field K]
    [NumberField K] (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hunits : Subsingleton (Work.SSGRoute.H3
      (M := Additive (Units (AlgebraicClosure (Q.adicCompletion K))))
      (Work.AbsoluteKummer.G (Q.adicCompletion K))))
    (hdiv : ∀ x : Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G (Q.adicCompletion K))
      (Additive (Units (AlgebraicClosure (Q.adicCompletion K)))), ∃ y, p • y = x)
    (ζ : Q.adicCompletion K) (hζ : IsPrimitiveRoot ζ p) :
    Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p)
      (Work.AbsoluteKummer.G (Q.adicCompletion K))) :=
  h3_mup_subsingleton_of_units_divisible p (Q.adicCompletion K) ⟨ζ, hζ⟩ hunits hdiv

end Work.SSGRoute.PTembedding
