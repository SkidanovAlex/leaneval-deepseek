import Mathlib
import Submission.NK.NUV2.LCLeaves
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.step0_inf_open
import Submission.NK.NUV2.LC.RouteB.lies_in_stabSubgroup
import Submission.NK.NUV2.LC.finite_support_loc_odd_of_twist
import Submission.NK.LocalDecomposition.Basic
import Submission.NK.Mine.LocalGaloisInfiniteDischarge

/-! Guidance from the project lead (the requester):

# Guidance: DecompContainment by the NON-CIRCULAR route (orchestrator's design; replaces the old producer architecture)
RULE: no licensed inputs; build what is missing; declare_false only with a counterexample.
WHY THE OLD ROUTE WAS CIRCULAR: SurjTwo/UniqLocal/HasseTwo/Guarded were statements about the closed H itself — each is
"H sits at one place" in disguise. Here ABHN is applied ONLY to Br(F)[p] at OPEN levels U = G_F (F number field ⊆ K'^H),
with an ODD prime p and ζ_p ∈ F (so F is totally complex; no finite-level Sha² issues — the ℚ(√−65) refutation was at
finite level Gal(L/K) with ℤ/2); passing to H uses only continuity, compactness and counting. The old files under
`Submission/Work/NUV2/{LC,ABHN}/` (conjTransport, h2CardTransport, cardGlobalTwo_of_hkc, local_brauer_*, order_statement,
eq_of_nontrivial_of_surjective_prod, decompContainment_of_inputs) are reusable.
Notation: `H2P p V := NK.BrauerHasse.H2Profinite p V`, maps `loc`, `res` (`LocalDecomposition/Localisation.lean`, `loc_eq_res`).
A place A is V-live if Nontrivial (H2P p (V ⊓ stabSubgroup A)).
LEMMAS (each TRUE, none mentions a local-type H; delegate each):
(L1) continuity, (L5) orbit separation, (H) Hasse at open levels, (FS) finite support at open levels,
(R2) two-place realisation, (P) cyclic periodicity compatible with localisation, (L0) local cardinality,
(L3') liveness to open subgroups; also a p-general ConjTransport and additive structure on H2P.
PROOF: Step 0: replace H by the open normal H₁ = H ∩ G_{K(ζ_p)} ∩ e⁻¹(G_{κ(ζ_p)}); Claim U, Claim E, final argument.
-/

namespace NK.NUV2.LC.RouteB

open IsDedekindDomain
open scoped Pointwise

/-- **The final argument of Route B** (see `RouteB/NOTES_assembly_design.md`): a closed subgroup `V`
of `Gal(K'/K)` of *local type* — fixing a primitive `p`-th root `ζ`, continuously isomorphic to
`Gal(κ'/M)` for a finite Galois `M/κ` containing a primitive `p`-th root, `κ = 𝔮.adicCompletion L` —
lies in the decomposition group of some place over a finite prime of `K`.

This is `NK.NUV2.LC.RouteB.lies_in_stabSubgroup`, restated in the `ValuationSubring` form used by
`NK.NUV2.DecompContainment`.  It consumes the input `hFC` (Hasse's fundamental class, through the
two-place realisation) and the local computation `card_open_local`. -/
theorem lies_in_decompositionGroup (hFC : NK.GlobalCFTdeep.FundamentalClassElement) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ζ : K') (hζ : IsPrimitiveRoot ζ p) {L : Type} [Field L]
    [NumberField L] (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (M : FiniteGaloisIntermediateField (𝔮.adicCompletion L)
      (SeparableClosure (𝔮.adicCompletion L)))
    (hζM : ∃ ζ' : ↥M, IsPrimitiveRoot ζ' p) (V : Subgroup Gal(K'/K))
    (hVcl : IsClosed (V : Set Gal(K'/K)))
    (hVζ : V ≤ rootFix (K := K) (K' := K') ζ)
    (e : ↥V ≃ₜ* ↥(M.fixingSubgroup)) :
    ∃ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ ∧
      V ≤ NK.BrauerHasse.stabSubgroup A := by
  obtain ⟨A, hA⟩ := lies_in_stabSubgroup (K := K) (K' := K') hFC p hp hp2 ζ hζ 𝔮 M hζM V hVcl hVζ e
  exact ⟨A.1, A.2, hA⟩

/-- A subgroup `H₁ = H ⊓ N₀` with `N₀` **open** has finite index in `H`: `N₀` contains an open
normal subgroup of `Gal(K'/K)` (Krull topology), hence has finite index, and finite index passes to
`H₁` in `H` (`Subgroup.inf_relIndex_left`; note that this does *not* follow from closedness of `H`,
which would be the false Nikolov–Segal statement). -/
theorem relIndex_inf_open_pos {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {H N : Subgroup Gal(K'/K)} (hN : IsOpen (N : Set Gal(K'/K))) :
    0 < (H ⊓ N).relIndex H := by
  haveI : N.FiniteIndex := by
    obtain ⟨N₀, hN₀⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (G := Gal(K'/K)) hN N.one_mem
    haveI : (N₀.toSubgroup).FiniteIndex := N₀.finiteIndex_of_finite_quotient
    exact Subgroup.finiteIndex_of_le hN₀
  rw [Subgroup.inf_relIndex_left]
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have h1 : (N.subgroupOf H).index ≠ 0 := Subgroup.finiteIndex_iff.mp inferInstance
  exact h1 (by simpa only [Subgroup.relIndex] using h0)

/-- **`NK.NUV2.DecompContainment` by the non-circular Route B.**

A closed subgroup `H ≤ Gal(K'/K)` of the absolute Galois group of a number field which is
topologically isomorphic to the absolute Galois group of a `p`-adic field (a completion `κ` of a
number field at a finite prime) lies in the decomposition group of a place of `K'` over a finite
prime of `K` (Neukirch, Invent. Math. **6** (1969), Theorem 1; NSW (12.1.9) "if").

Proof (Route B): at an **odd** prime `p` and a primitive `p`-th root `ζ_p ∈ K'`,

* **Step 0** (`RouteB/step0_inf_open`): replace `H` by the open normal subgroup `H₁ = H ⊓ N₀`
  (with `N₀` open) of local type `≅ Gal(κ'/M)`, `M/κ` finite Galois containing `ζ_p`, with
  `H₁ ≤ rootFix ζ_p` and `H₁` closed;
* **the core** (`RouteB/lies_in_stabSubgroup`, the "final argument", which consumes `hFC` through
  the two-place realisation and the local computation `card_open_local`): `H₁ ≤ D_A` for some place
  `A` over a finite prime;
* **Ivanov's `lm:finindexlm`** (`NK.LocalDecomposition.le_stabSubgroup_of_openSubgroup_le`,
  Neukirch's argument): an open subgroup of `H` inside a decomposition group pulls `H` into it;
  the hypothesis `Nat.card ↥H = 0` (H infinite) comes from `H ≅ Gal(κ'/κ)` and the infinitude of
  the absolute Galois group of a `p`-adic field
  (`NK.Mine.localGaloisInfinite_adicCompletion`). -/
theorem decompContainment_B (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    (hKC : NK.NUV2.KCAll) : NK.NUV2.DecompContainment := by
  intro K K' _ _ _ _ _ H hHclosed hlab
  obtain ⟨L, hLf, hLnf, 𝔮, he⟩ := hlab
  letI : Field L := hLf
  letI : NumberField L := hLnf
  obtain ⟨e⟩ := he
  -- a primitive cube root of unity in `K'`
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : NeZero (3 : K') := ⟨Nat.cast_ne_zero.mpr (by norm_num)⟩
  obtain ⟨ζ, hζ⟩ :=
    NK.NUV2.LC.OddTwist.exists_isPrimitiveRoot_of_isSepClosure (K := K) (K' := K') 3
      (by norm_num)
  -- Step 0
  obtain ⟨H₁, N₀, M, e₁, hH₁le, -, hN₀open, hH₁eq, hH₁ζ, hζM⟩ :=
    step0_inf_open (K := K) (K' := K') 3 (by norm_num) (by norm_num) ζ hζ 𝔮 H hHclosed e
  have hH₁cl : IsClosed (H₁ : Set Gal(K'/K)) := by
    rw [hH₁eq]
    exact hHclosed.inter (Subgroup.isClosed_of_isOpen N₀ hN₀open)
  -- the core: the containment for the local-type subgroup `H₁`
  obtain ⟨A, hAne, hAle⟩ :=
    lies_in_decompositionGroup (K := K) (K' := K') hFC 3 (by norm_num) (by norm_num) ζ hζ 𝔮 M hζM
      H₁ hH₁cl hH₁ζ e₁
  -- Ivanov's `lm:finindexlm`: pass from the open subgroup `H₁` to `H`
  have hH₁fin : 0 < H₁.relIndex H := by
    rw [hH₁eq]
    exact relIndex_inf_open_pos (K := K) (K' := K') (H := H) hN₀open
  have hHinf : Nat.card ↥H = 0 := by
    haveI : Infinite (Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) :=
      NK.Mine.localGaloisInfinite_adicCompletion 𝔮 _
    rw [Nat.card_congr e.toMulEquiv.toEquiv]
    exact Nat.card_eq_zero_of_infinite
  exact ⟨A, hAne, NK.LocalDecomposition.le_stabSubgroup_of_openSubgroup_le A hAne H H₁ hH₁le
    hH₁fin hHinf hAle⟩

end NK.NUV2.LC.RouteB
