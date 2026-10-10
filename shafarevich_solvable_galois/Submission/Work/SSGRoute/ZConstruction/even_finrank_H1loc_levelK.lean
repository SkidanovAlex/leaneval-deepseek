import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.LocallyConstant.Basic
import Submission.NK.GlobalCFTdeep.SecondInequality.localIndex_finite_mem
import Submission.NK.GlobalCFTdeep.SecondInequality.localIndex_finite_notMem
import Submission.Work.SSGRoute.LTDRefs.levelK_finite
import Submission.Work.SSGRoute.PTembedding.lcHoms_localUnits
import Submission.Work.SSGRoute.ZConstruction.even_localDegree_levelK_residueChar
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxHeartbeats 400000

/-!
# The level-`K` local `H¹` with trivial coefficients has even dimension

For a number field `k`, an algebraic closure `Ω`, a finite Galois subextension `K/k`, a place `A`
of `Ω` over a finite place of `k` and an odd prime `p` with `ζ_p ∈ K`, the locally constant local
`H¹` of the *level-`K`* decomposition group `H = decomp k A ⊓ K.fixingSubgroup` with coefficients
in `𝔽_p` is an `𝔽_p`-vector space of *even* dimension.

## The proof

On `H` the coefficient action is trivial (`H ≤ K.fixingSubgroup = ker (res k K)`), so the local
`H¹` is the group of locally constant characters `H → 𝔽_p^*` (`H1locEquivH1`, the fact that the
crossed homomorphisms for the trivial action are the additive maps, and the vanishing of the
coboundaries), and hence its cardinality is a power of `p` with the exponent

  `dim H¹(H, 𝔽_p) = log_p #(lcHoms H)`.

The chain of cardinalities

  `H1loc(H, 𝔽_p) → lcHoms(H) → lcHoms(decomp_A) → lcHoms(Gal(κ̄/κ)) → κˣ ⧸ (κˣ)^p`

(for `κ = K_𝔓` the completion of `K` at the place `𝔓` below `A`, the last step being local Kummer
reciprocity) reduces the parity to the local count

  `#(κˣ ⧸ (κˣ)^p) = p ^ ([κ : ℚ_p] + 2)`  if `p` is the residue characteristic of `A`,
  `#(κˣ ⧸ (κˣ)^p) = p ^ 2`               otherwise,

which is `NK.GlobalCFTdeep.SecondInequality.localIndex_finite_mem` resp. `..._notMem`.  In the
first case the parity is that of `[κ : ℚ_p]`, which is even because `ζ_p ∈ K ⊆ κ` forces
`p - 1 ∣ [κ : ℚ_p]` (`even_localDegree_levelK_residueChar`); in the second case the exponent is
`2`.
-/

namespace Work.SSGRoute.ZConstruction

open scoped Pointwise

/-! ## Three formal bridges -/

/-- Local constancy in the sense of `Work.AbsoluteKummer` is Mathlib's local constancy. -/
private lemma absLoc_iff {X M : Type*} [TopologicalSpace X] (f : X → M) :
    Work.AbsoluteKummer.IsLocallyConstant f ↔ _root_.IsLocallyConstant f := by
  rw [_root_.IsLocallyConstant.iff_exists_open]
  rfl

section Trivial

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable (p : ℕ) [Fact p.Prime] [DistribMulAction Γ (ZMod p)]

/-- A locally constant additive `1`-cocycle for the trivial action, read as a character. -/
private noncomputable def z1ToLc
    (hsmul : ∀ (g : Γ) (m : ZMod p), g • m = m)
    (f : ↥(Work.AbsoluteKummer.Z1 Γ (ZMod p))) : ↥(Work.SSGRoute.lcHoms p Γ) :=
  ⟨{ toFun := fun g => Multiplicative.ofAdd (f.1 g)
     map_one' := by
       rw [ofAdd_eq_one]
       have hh := f.2.1 1 1
       rw [one_mul] at hh
       rw [hsmul 1 (f.1 1)] at hh
       have h1 : f.1 1 + 0 = f.1 1 + f.1 1 := by rw [add_zero, ← hh]
       exact (add_left_cancel h1).symm
     map_mul' := by
       intro g h
       have hh := f.2.1 g h
       rw [hsmul g (f.1 h)] at hh
       rw [hh, ofAdd_add]
       exact mul_comm _ _ },
   (absLoc_iff f.1).mp f.2.2 |>.comp Multiplicative.ofAdd⟩

/-- A locally constant character is a locally constant additive `1`-cocycle for the trivial
action. -/
private noncomputable def lcToZ1
    (hsmul : ∀ (g : Γ) (m : ZMod p), g • m = m)
    (χ : ↥(Work.SSGRoute.lcHoms p Γ)) : ↥(Work.AbsoluteKummer.Z1 Γ (ZMod p)) :=
  ⟨fun g => (χ.1 g).toAdd, by
    rw [Work.AbsoluteKummer.mem_Z1_iff]
    refine ⟨?_, ?_⟩
    · intro g h
      change (χ.1 (g * h)).toAdd = g • (χ.1 h).toAdd + (χ.1 g).toAdd
      rw [hsmul g (χ.1 h).toAdd, map_mul, toAdd_mul]
      exact add_comm _ _
    · exact (absLoc_iff (fun g => (χ.1 g).toAdd)).mpr (χ.2.comp Multiplicative.toAdd)⟩

/-- For the trivial action, `Z¹(Γ, 𝔽_p)` is the group of locally constant characters. -/
private theorem card_Z1_eq_card_lcHoms
    (hsmul : ∀ (g : Γ) (m : ZMod p), g • m = m) :
    Nat.card ↥(Work.AbsoluteKummer.Z1 Γ (ZMod p)) = Nat.card ↥(Work.SSGRoute.lcHoms p Γ) :=
  Nat.card_congr
    { toFun := z1ToLc p hsmul, invFun := lcToZ1 p hsmul
      left_inv := fun χ => Subtype.ext (funext fun g => rfl)
      right_inv := fun f => Subtype.ext (MonoidHom.ext fun g => rfl) }

/-- For the trivial action, `H¹(Γ, 𝔽_p) = Z¹(Γ, 𝔽_p)`: the coboundaries vanish. -/
private theorem card_H1_eq_card_Z1
    (hsmul : ∀ (g : Γ) (m : ZMod p), g • m = m) :
    Nat.card (Work.AbsoluteKummer.H1 Γ (ZMod p)) =
      Nat.card ↥(Work.AbsoluteKummer.Z1 Γ (ZMod p)) := by
  have hB1 : Work.AbsoluteKummer.B1 Γ (ZMod p) = ⊥ := by
    rw [Work.AbsoluteKummer.B1, AddMonoidHom.range_eq_bot_iff]
    ext a g
    show Work.GroupCohomology.d0 Γ (ZMod p) a g = 0
    rw [Work.GroupCohomology.d0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hsmul g a, sub_self]
  have hbot : ((Work.AbsoluteKummer.B1 Γ (ZMod p)).comap
      (Work.AbsoluteKummer.Z1 Γ (ZMod p)).subtype) =
      (⊥ : AddSubgroup ↥(Work.AbsoluteKummer.Z1 Γ (ZMod p))) := by
    rw [hB1]
    ext x
    simp [AddSubgroup.mem_comap]
  have hH : Work.AbsoluteKummer.H1 Γ (ZMod p) = (↥(Work.AbsoluteKummer.Z1 Γ (ZMod p)) ⧸ (⊥ : AddSubgroup ↥(Work.AbsoluteKummer.Z1 Γ (ZMod p)))) := by
    unfold Work.AbsoluteKummer.H1
    rw [hbot]
  rw [hH]
  exact Nat.card_congr (QuotientAddGroup.quotientBot (G := ↥(Work.AbsoluteKummer.Z1 Γ (ZMod p)))).toEquiv

end Trivial

/-- A homeomorphic group isomorphism induces a bijection of the locally constant
characters. -/
private theorem card_lcHoms_of_homeomorph' (p : ℕ) [Fact p.Prime] {G H : Type} [Group G]
    [TopologicalSpace G] [Group H] [TopologicalSpace H] (e : G ≃* H)
    (he : IsHomeomorph (e : G → H)) :
    Nat.card ↥(Work.SSGRoute.lcHoms p G) = Nat.card ↥(Work.SSGRoute.lcHoms p H) := by
  have hsymm : Continuous (e.symm : H → G) := by
    rw [continuous_def]
    intro U hU
    have h : (e.symm : H → G) ⁻¹' U = e '' U := by
      ext y
      constructor
      · intro hy
        exact ⟨e.symm y, hy, by simp⟩
      · rintro ⟨g, hg, rfl⟩
        simpa using hg
    rw [h]
    exact he.isOpenMap U hU
  refine Nat.card_congr
    { toFun := fun χ => ⟨χ.1.comp e.symm.toMonoidHom, ?_⟩
      invFun := fun χ => ⟨χ.1.comp e.toMonoidHom, ?_⟩
      left_inv := fun χ => Subtype.ext (MonoidHom.ext (fun g => by simp))
      right_inv := fun χ => Subtype.ext (MonoidHom.ext (fun h => by simp)) }
  · show IsLocallyConstant (fun h : H => χ.1 (e.symm h))
    exact χ.2.comp_continuous hsymm
  · show IsLocallyConstant (fun g : G => χ.1 (e g))
    exact χ.2.comp_continuous he.continuous

/-- The locally constant characters of the decomposition group at a finite place are those of the
absolute Galois group of the completion. -/
private theorem lcHoms_card_decomp_eq_localGal' (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    Nat.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp k A))
      = Nat.card ↥(Work.SSGRoute.lcHoms p (Work.SSGRoute.PTembedding.localGalOf k A hA)) := by
  classical
  let 𝔭 := Submission.NeukirchUchida.primeOf A hA
  have h𝔭 := Submission.NeukirchUchida.primeOf_spec A hA
  letI : Algebra (𝔭.adicCompletion k) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A h𝔭).toAlgebra
  have halg : ∀ z : 𝔭.adicCompletion k,
      (algebraMap (𝔭.adicCompletion k) (NK.NeukirchUchida.placeCompletion A)) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A h𝔭 z := fun z => rfl
  have hW :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers 𝔭 A h𝔭
  haveI : IsSepClosure (𝔭.adicCompletion k)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion 𝔭 A h𝔭 halg
  haveI : IsGalois (𝔭.adicCompletion k) ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A) :=
    IsSepClosure.isGalois
  let e : ↥(SSGRoute.decomp k A) ≃*
      Gal(SeparableClosure (𝔭.adicCompletion k)/(𝔭.adicCompletion k)) :=
    NK.Mine.localGaloisEquiv 𝔭 A h𝔭 halg hW
  have he : IsHomeomorph (e : ↥(SSGRoute.decomp k A) →
      Gal(SeparableClosure (𝔭.adicCompletion k)/(𝔭.adicCompletion k))) :=
    NK.Mine.isHomeomorph_trans (NK.Mine.adjoinLocalEquiv 𝔭 A h𝔭 halg hW)
      (AlgEquiv.autCongr (NK.Mine.adjoinSepEquiv 𝔭 A h𝔭 halg))
      (NK.Mine.isHomeomorph_adjoinLocalEquiv 𝔭 A h𝔭 halg hW)
      (NK.Mine.isHomeomorph_autCongr (NK.Mine.adjoinSepEquiv 𝔭 A h𝔭 halg))
  exact card_lcHoms_of_homeomorph' p e he

/-! ## The target -/

theorem even_finrank_H1loc_levelK (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Even (Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup))) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- ### the level-`K` local group
  set H : Subgroup (Ω ≃ₐ[k] Ω) := SSGRoute.decomp k A ⊓ K.fixingSubgroup with hHdef
  have hHle : H ≤ K.fixingSubgroup := inf_le_right
  -- ### the action of `↥H` on the coefficients, through `res`
  letI : DistribMulAction ↥H (ZMod p) :=
    { smul := fun h m => SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m
      one_smul := fun m => by
        change SSGRoute.res k K ((1 : ↥H) : Ω ≃ₐ[k] Ω) • m = m
        rw [Subgroup.coe_one, map_one, one_smul]
      mul_smul := fun h₁ h₂ m => by
        change SSGRoute.res k K (((h₁ * h₂ : ↥H)) : Ω ≃ₐ[k] Ω) • m
          = SSGRoute.res k K ((h₁ : ↥H) : Ω ≃ₐ[k] Ω) •
            (SSGRoute.res k K ((h₂ : ↥H) : Ω ≃ₐ[k] Ω) • m)
        rw [Subgroup.coe_mul, map_mul, mul_smul]
      smul_zero := fun h => by
        change SSGRoute.res k K ((h : ↥H) : Ω ≃ₐ[k] Ω) • (0 : ZMod p) = 0
        rw [smul_zero]
      smul_add := fun h m₁ m₂ => by
        change SSGRoute.res k K ((h : ↥H) : Ω ≃ₐ[k] Ω) • (m₁ + m₂)
          = SSGRoute.res k K ((h : ↥H) : Ω ≃ₐ[k] Ω) • m₁
            + SSGRoute.res k K ((h : ↥H) : Ω ≃ₐ[k] Ω) • m₂
        rw [smul_add] }
  have hsmulH : ∀ (h : ↥H) (m : ZMod p), h • m = m := by
    intro h m
    have h1 : SSGRoute.res k K ((h : ↥H) : Ω ≃ₐ[k] Ω) = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker K]
      exact hHle h.2
    change SSGRoute.res k K ((h : ↥H) : Ω ≃ₐ[k] Ω) • m = m
    rw [h1, one_smul]
  -- ### finiteness of the local `H¹`
  haveI hFin : Finite (Work.SSGRoute.H1loc p k Ω K (ZMod p) H) :=
    Work.SSGRoute.LTDRefs.levelK_finite p k Ω K A hA (ZMod p)
  haveI hFintype : Fintype (Work.SSGRoute.H1loc p k Ω K (ZMod p) H) := Fintype.ofFinite _
  -- ### the base change of the field data to `K`
  haveI hNF : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) K
  haveI hAC : IsAlgClosure ↥K Ω :=
    ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  have hAK : SSGRoute.IsFinPlace ↥K A := by
    intro hK
    apply hA
    rw [eq_top_iff]
    intro q _
    rw [ValuationSubring.mem_comap]
    have hmem : algebraMap ↥K Ω (algebraMap k ↥K q) ∈ A := by
      have : algebraMap k ↥K q ∈ A.comap (algebraMap ↥K Ω) := by rw [hK]; trivial
      rwa [ValuationSubring.mem_comap] at this
    rwa [IsScalarTower.algebraMap_apply k ↥K Ω]
  -- ### a primitive `p`-th root of unity in the completion at the prime below `A`
  have hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) (by simpa using hζ)
      (RingHom.injective _)
  have hζκ : ∃ ζ' : (Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K,
      IsPrimitiveRoot ζ' p :=
    ⟨algebraMap ↥K ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K) ⟨ζ, hζK⟩,
      hζK'.map_of_injective
        (f := algebraMap ↥K ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K))
        (RingHom.injective _)⟩
  -- ### the chain of cardinalities
  have hchain : Nat.card (Work.SSGRoute.H1loc p k Ω K (ZMod p) H)
      = Nat.card (((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ ⧸
          (powMonoidHom p : ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ →*
            ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ).range) := by
    calc Nat.card (Work.SSGRoute.H1loc p k Ω K (ZMod p) H)
        = Nat.card (Work.AbsoluteKummer.H1 ↥H (ZMod p)) :=
          Nat.card_congr (Work.SSGRoute.H1locEquivH1 p k Ω K (ZMod p) H
            (fun _ _ => rfl)).toEquiv
      _ = Nat.card ↥(Work.AbsoluteKummer.Z1 ↥H (ZMod p)) := card_H1_eq_card_Z1 p hsmulH
      _ = Nat.card ↥(Work.SSGRoute.lcHoms p ↥H) := card_Z1_eq_card_lcHoms p hsmulH
      _ = Nat.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp ↥K A)) :=
          card_lcHoms_of_homeomorph' p (Work.SSGRoute.decompEquiv_fok k Ω K A)
            (Work.SSGRoute.isHomeomorph_decompEquiv_fok k Ω K A)
      _ = Nat.card ↥(Work.SSGRoute.lcHoms p
            (Work.SSGRoute.PTembedding.localGalOf ↥K A hAK)) :=
          lcHoms_card_decomp_eq_localGal' p ↥K Ω A hAK
      _ = Nat.card (((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ ⧸
            (powMonoidHom p : ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ →*
              ((Submission.NeukirchUchida.primeOf A hAK).adicCompletion ↥K)ˣ).range) :=
          Work.SSGRoute.PTembedding.lcHoms_localUnits p ↥K Ω A hAK
  -- ### the two cases of the local count
  have hcard : ∃ N : ℕ, Nat.card (Work.SSGRoute.H1loc p k Ω K (ZMod p) H) = p ^ N ∧ Even N := by
    by_cases hmem : (p : NumberField.RingOfIntegers ↥K) ∈
        (Submission.NeukirchUchida.primeOf A hAK).asIdeal
    · refine ⟨NK.LocalInputs.localDegree ↥K (Submission.NeukirchUchida.primeOf A hAK) + 2, ?_, ?_⟩
      · rw [hchain]
        exact NK.GlobalCFTdeep.SecondInequality.localIndex_finite_mem
          (Submission.NeukirchUchida.primeOf A hAK) Fact.out hmem hζκ
      · exact (even_localDegree_levelK_residueChar
          (Submission.NeukirchUchida.primeOf A hAK) Fact.out hp hmem hζκ).add even_two
    · refine ⟨2, ?_, even_two⟩
      · rw [hchain]
        exact NK.GlobalCFTdeep.SecondInequality.localIndex_finite_notMem
          (Submission.NeukirchUchida.primeOf A hAK) Fact.out hmem hζκ
  obtain ⟨N, hNcard, hNeven⟩ := hcard
  -- ### cardinality to dimension
  have hcarddim : Nat.card (Work.SSGRoute.H1loc p k Ω K (ZMod p) H)
      = p ^ Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K (ZMod p) H) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hpow : p ^ Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K (ZMod p) H) = p ^ N := by
    rw [← hcarddim]
    exact hNcard
  have hfin_eq : Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K (ZMod p) H) = N :=
    Nat.pow_right_injective (Fact.out : p.Prime).two_le hpow
  rw [hfin_eq]
  exact hNeven

end Work.SSGRoute.ZConstruction
