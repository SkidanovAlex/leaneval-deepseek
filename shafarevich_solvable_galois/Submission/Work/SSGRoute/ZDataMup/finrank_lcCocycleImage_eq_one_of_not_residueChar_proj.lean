import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.LocallyConstant.Basic
import Submission.NK.GlobalCFTdeep.SecondInequality.localIndex_finite_notMem
import Submission.Work.SSGRoute.LTDDefs.H1loc_iso_H1cont
import Submission.Work.SSGRoute.ZConstruction.natCard_lcHoms_levelK_localGroup
import Submission.Work.SSGRoute.ZDataMup.finite_lcCocycleImage
import Submission.Work.SSGRoute.ZDataMup.finrank_lcCocycleImage_eq_H1loc
import Submission.Work.SSGRoute.isUnit_natCast_iff_not_dvd_resCharAt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

/-!
**Restatement, in the target file's own vocabulary, of the level-`K` local one-dimensionality.**

`Work.SSGRoute.ZDataMup.finrank_H1loc_triv_eq_one_of_not_residueChar` proves this for the canonical
`Triv`-coefficient vocabulary, but its module imports `sha2_defs`, whose global direct `SMul`
instances shadow the projection-shaped ones and make *every* declaration of
`ZDataMup/tatePoitou_h1_realisation.lean` fail to elaborate.  Hence the target file cannot import it,
and the statement below must be proved in a module that does **not** (transitively) import
`Submission.Work.SSGRoute.sha2_defs` or `Submission.Work.SSGRoute.mup_local_defs` (so: import only
the modules listed in `depends_on`, plus `Submission.NK.GlobalCFTdeep.SecondInequality.localIndex_finite_notMem`
for the arithmetic `|K_𝔮ˣ/(K_𝔮ˣ)^p| = p`; none of those imports `sha2_defs`).

## The route

`finrank_lcCocycleImage_eq_H1loc` already reduces the target to the local `H¹`; here we instead
count the `𝔽_p`-module `↥(lcCocycleImage K H)` of locally constant `1`-cocycles on
`H = decomp k A ⊓ K.fixingSubgroup` *restricted to* `H` directly.  Because `res k K` is trivial on
`H ≤ G_K`, such a restricted cocycle is nothing but a locally constant *additive* character of `H`,
i.e. a locally constant monoid homomorphism `↥H →* Multiplicative (𝔽_p)`; conversely every such
character extends to a locally constant `1`-cocycle on `G_k` (extend by `0` off `H`,
`Work.SSGRoute.extendCocycle`).  This gives the two inequalities

  `|↥(lcCocycleImage K H)| = |lcHoms p ↥H| = |lcHoms p ↥(decomp (k := ↥K) A)|`

(`lcCocycleImage_hom`, `isOpen_ker_iff_isLocallyConstant`, and the homeomorphism
`decompEquiv_fok`), and the right-hand side is `|κˣ ⧸ (κˣ)^p|` for `κ = K_𝔮`
(`natCard_lcHoms_levelK_localGroup`).  For `p` a unit of `𝒪_κ` and `ζ_p ∉ κ` the classical
structure of `κˣ` gives `|κˣ ⧸ (κˣ)^p| = p`, and `p ^ finrank = |·|` upgrades the count to the
`𝔽_p`-dimension.
-/

open scoped Pointwise
open Classical

noncomputable section

/-! ## Two generalities about local constancy -/

/-- **Open kernel ⟺ local constancy** for a homomorphism into the discrete group `𝔽_pˣ`. -/
theorem isOpen_ker_iff_isLocallyConstant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {n : ℕ} (χ : G →* Multiplicative (ZMod n)) :
    IsOpen (χ.ker : Set G) ↔ _root_.IsLocallyConstant χ := by
  refine ⟨fun h => Work.SSGRoute.PTembedding.isLocallyConstant_of_isOpen_ker χ h, fun h => ?_⟩
  have h1 : IsOpen (χ ⁻¹' {(1 : Multiplicative (ZMod n))}) := h.isOpen_fiber 1
  have h2 : (χ ⁻¹' {(1 : Multiplicative (ZMod n))} : Set G) = (χ.ker : Set G) := by
    ext x
    simp [MonoidHom.mem_ker]
  rwa [h2] at h1

/-- The local constancy convention of `Work.AbsoluteKummer` is Mathlib's `IsLocallyConstant`. -/
theorem absLoc_iff {X M : Type*} [TopologicalSpace X] (f : X → M) :
    Work.AbsoluteKummer.IsLocallyConstant f ↔ _root_.IsLocallyConstant f := by
  rw [_root_.IsLocallyConstant.iff_exists_open]
  rfl

/-! ## The level-`K` local cocycles versus the locally constant characters -/

section Main

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω}
  [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **Every locally constant character of the level-`K` local group extends to a locally constant
`1`-cocycle on `G_k`.**  The cocycle is obtained from the additive character
`h ↦ (χ (decompEquiv_fok h)).toAdd` by extension by `0` off `H`
(`Work.SSGRoute.extendCocycle`); the crossed-homomorphism condition is additivity, because `res k K`
is trivial on `H`, and local constancy is transport of the local constancy of `χ` along the
homeomorphism `decompEquiv_fok`. -/
theorem exists_cocycle_of_lcHoms_finrank (A : ValuationSubring Ω)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    ∃ f ∈ localCocycle (p := p) K (SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      ∀ h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        f (h : Ω ≃ₐ[k] Ω) = (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A h)).toAdd := by
  classical
  let H : Subgroup (Ω ≃ₐ[k] Ω) := SSGRoute.decomp k A ⊓ K.fixingSubgroup
  have hH : H ≤ K.fixingSubgroup := inf_le_right
  letI : DistribMulAction ↥H (ZMod p) :=
    { smul := fun h m => SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m
      one_smul := fun m => by
        show SSGRoute.res k K (((1 : ↥H) : Ω ≃ₐ[k] Ω)) • m = m
        rw [Subgroup.coe_one, map_one, one_smul]
      mul_smul := fun h₁ h₂ m => by
        show SSGRoute.res k K (((h₁ * h₂ : ↥H) : Ω ≃ₐ[k] Ω)) • m
          = SSGRoute.res k K ((h₁ : Ω ≃ₐ[k] Ω)) • (SSGRoute.res k K ((h₂ : Ω ≃ₐ[k] Ω)) • m)
        rw [Subgroup.coe_mul, map_mul, mul_smul]
      smul_zero := fun h => smul_zero (SSGRoute.res k K (h : Ω ≃ₐ[k] Ω))
      smul_add := fun h m n => smul_add (SSGRoute.res k K (h : Ω ≃ₐ[k] Ω)) m n }
  have hcompat : ∀ (h : ↥H) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m := fun _ _ => rfl
  let c : ↥H → ZMod p := fun h => (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A h)).toAdd
  have hc : c ∈ Work.AbsoluteKummer.Z1 ↥H (ZMod p) := by
    rw [Work.AbsoluteKummer.mem_Z1_iff]
    refine ⟨?_, ?_⟩
    · intro g h
      show c (g * h) = g • c h + c g
      have h1 : c (g * h) = c g + c h := by
        show (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A (g * h))).toAdd
          = (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A g)).toAdd
            + (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A h)).toAdd
        rw [map_mul (Work.SSGRoute.decompEquiv_fok k Ω K A) g h,
          map_mul χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A g)
            (Work.SSGRoute.decompEquiv_fok k Ω K A h),
          toAdd_mul]
      rw [h1, show g • c h = c h from by
        change SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • c h = c h
        rw [res_eq_one_of_mem_fixingSubgroup (hH g.2), one_smul]]
      exact add_comm _ _
    · show Work.AbsoluteKummer.IsLocallyConstant c
      rw [absLoc_iff]
      have h1 : _root_.IsLocallyConstant
          (fun h : ↥H => χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A h)) :=
        χ.2.comp_continuous (Work.SSGRoute.isHomeomorph_decompEquiv_fok k Ω K A).continuous
      rw [_root_.IsLocallyConstant.iff_exists_open] at h1 ⊢
      intro x
      obtain ⟨U, hUo, hxU, hU⟩ := h1 x
      exact ⟨U, hUo, hxU, fun y hy => by
        show (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A y)).toAdd
          = (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A x)).toAdd
        rw [hU y hy]⟩
  refine ⟨(Work.SSGRoute.extendCocycle p k Ω K (ZMod p) H hcompat ⟨c, hc⟩).1, ?_, ?_⟩
  · exact (Work.SSGRoute.extendCocycle p k Ω K (ZMod p) H hcompat ⟨c, hc⟩).2
  · intro h
    change (if hh : (h : Ω ≃ₐ[k] Ω) ∈ H then c ⟨(h : Ω ≃ₐ[k] Ω), hh⟩ else 0)
      = (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A h)).toAdd
    rw [dif_pos h.2]

/-- **Lower bound**: the locally constant characters of the level-`K` local group inject into the
level-`K` local cocycle image (via the extension `exists_cocycle_of_lcHoms_finrank` restricted to `H`). -/
theorem lcHoms_card_le_lcCocycleImage (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Nat.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) ≤
      Nat.card ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) := by
  classical
  let H : Subgroup (Ω ≃ₐ[k] Ω) := SSGRoute.decomp k A ⊓ K.fixingSubgroup
  haveI hfin : Finite ↥(lcCocycleImage (p := p) K H) :=
    finite_lcCocycleImage (p := p) (K := K) hA
  let Ξ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) →
      ↥(lcCocycleImage (p := p) K H) := fun χ =>
    let f := Classical.choose (exists_cocycle_of_lcHoms_finrank (p := p) (K := K) A χ)
    ⟨restrictToSub H f,
      Submodule.mem_map.mpr
        ⟨f, (Classical.choose_spec (exists_cocycle_of_lcHoms_finrank (p := p) (K := K) A χ)).1, rfl⟩⟩
  refine Nat.card_le_card_of_injective Ξ ?_
  intro χ χ' hχeq
  have hv : ∀ h : ↥H, (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A h)).toAdd
      = (χ'.1 (Work.SSGRoute.decompEquiv_fok k Ω K A h)).toAdd := by
    intro h
    have h1 := (Classical.choose_spec (exists_cocycle_of_lcHoms_finrank (p := p) (K := K) A χ)).2 h
    have h2 := (Classical.choose_spec (exists_cocycle_of_lcHoms_finrank (p := p) (K := K) A χ')).2 h
    rw [← h1, ← h2]
    exact congrFun (congrArg Subtype.val hχeq) h
  apply Subtype.ext
  ext y
  obtain ⟨h, rfl⟩ := (Work.SSGRoute.decompEquiv_fok k Ω K A).surjective y
  simpa using congrArg Multiplicative.ofAdd (hv h)

/-- **Upper bound**: the locally constant cocycle image embeds into the open-kernel (equivalently
locally constant) characters of the level-`K` local group. -/
theorem lcCocycleImage_card_le_lcHoms (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Nat.card ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) ≤
      Nat.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) := by
  classical
  let H : Subgroup (Ω ≃ₐ[k] Ω) := SSGRoute.decomp k A ⊓ K.fixingSubgroup
  have hH : H ≤ K.fixingSubgroup := inf_le_right
  haveI hfin : Finite {χ : ↥H →* Multiplicative (ZMod p) // IsOpen (χ.ker : Set ↥H)} :=
    finite_openKernel_homs_decomp_kernel p k Ω K A hA (ZMod p)
  have himg : Nat.card ↥(lcCocycleImage (p := p) K H)
      ≤ Nat.card {χ : ↥H →* Multiplicative (ZMod p) // IsOpen (χ.ker : Set ↥H)} := by
    let Θ : ↥(lcCocycleImage (p := p) K H) →
        {χ : ↥H →* Multiplicative (ZMod p) // IsOpen (χ.ker : Set ↥H)} := fun x =>
      ⟨Classical.choose (lcCocycleImage_hom hH x),
        (Classical.choose_spec (lcCocycleImage_hom hH x)).2⟩
    refine Nat.card_le_card_of_injective Θ ?_
    intro x y hxy
    apply Subtype.ext
    funext g
    have h1 : (Θ x).1 g = (Θ y).1 g :=
      congrArg (fun z => z.1 g) hxy
    have h2 : (Θ x).1 g = x.1 g :=
      congrFun (Classical.choose_spec (lcCocycleImage_hom hH x)).1 g
    have h3 : (Θ y).1 g = y.1 g :=
      congrFun (Classical.choose_spec (lcCocycleImage_hom hH y)).1 g
    rw [h2, h3] at h1
    exact h1
  calc Nat.card ↥(lcCocycleImage (p := p) K H)
      ≤ Nat.card {χ : ↥H →* Multiplicative (ZMod p) // IsOpen (χ.ker : Set ↥H)} := himg
    _ = Nat.card ↥(Work.SSGRoute.lcHoms p ↥H) :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun χ => isOpen_ker_iff_isLocallyConstant χ))

end Main

/-! ## The arithmetic input: `|κˣ ⧸ (κˣ)^p| = p` when `p ∤ #κ̄ˣ` -/

open IsDedekindDomain in
/-- The self-`LiesOver` instance for a prime ideal (not a Mathlib instance). -/
theorem liesOver_self_primeIdeal {L : Type} [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    𝔮.asIdeal.LiesOver 𝔮.asIdeal :=
  Ideal.LiesOver.mk (by ext x; simp [Ideal.under])

/-- **The local Kummer count with `p` prime to the residue characteristic and `ζ_p` absent.**  For a
number field `L`, a finite prime `𝔮` of `L` and a prime `p` which is a unit at `𝔮` and such that the
completion `L_𝔮` contains no primitive `p`-th root of unity, the `p`-power class group
`L_𝔮ˣ ⧸ (L_𝔮ˣ)^p` has order `p`. -/
theorem localKummerQuot_card_eq_prime_of_notMem_notExists {L : Type} [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {q : ℕ} (hq : q.Prime)
    (hnot : (q : NumberField.RingOfIntegers L) ∉ 𝔮.asIdeal)
    (hζ : ¬ ∃ ζ : 𝔮.adicCompletion L, IsPrimitiveRoot ζ q) :
    Nat.card ((𝔮.adicCompletion L)ˣ ⧸
      (powMonoidHom q : (𝔮.adicCompletion L)ˣ →* (𝔮.adicCompletion L)ˣ).range) = q := by
  classical
  have hunit : IsUnit (q : 𝔮.adicCompletionIntegers L) :=
    NK.GlobalCFTdeep.SecondInequality.isUnit_natCast_adicCompletionIntegers_of_notMem 𝔮 hnot
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI hfinRes : Finite (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers L)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion L 𝔮
  haveI : Fintype (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers L)) := Fintype.ofFinite _
  haveI : IsCyclic (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers L))ˣ := inferInstance
  have hres : Nat.card ((IsLocalRing.ResidueField (𝔮.adicCompletionIntegers L))ˣ ⧸
      (powMonoidHom q : (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers L))ˣ →*
        (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers L))ˣ).range) = 1 := by
    rw [Commons.GroupTheory.SpecificGroups.Cyclic.card_quotient_powMonoidHom
      (G := (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers L))ˣ) q,
      ← Nat.card_eq_fintype_card, Nat.card_units]
    have hndvd : ¬ q ∣ Nat.card (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers L)) - 1 := by
      intro hdvd
      exact hζ (NK.TameStructureDeep.Degree.exists_isPrimitiveRoot_adicCompletion_of_dvd
        𝔮 𝔮 (liesOver_self_primeIdeal 𝔮) hq.ne_zero hdvd)
    exact Nat.coprime_iff_gcd_eq_one.mp ((hq.coprime_iff_not_dvd).mpr hndvd)
  rw [NK.GlobalCFTdeep.SecondInequality.natCard_kummerQuot_eq_mul_units 𝔮 hq,
    NK.GlobalCFTdeep.SecondInequality.natCard_units_quot_eq_residueUnits 𝔮 hq hunit, hres,
    mul_one]

/-- **The target.**  See the module docstring for the route. -/
theorem finrank_lcCocycleImage_eq_one_of_not_residueChar_proj (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hAp : ¬ A.valuation ((p : ℚ) : Ω) < 1)
    (hK : SSGRoute.IsFinPlace ↥K A)
    (hζ : ¬ ∃ ζ : Work.SSGRoute.PTembedding.localFieldOf ↥K A hK, IsPrimitiveRoot ζ p) :
    Module.finrank (ZMod p) ↥(Work.SSGRoute.ZDataMup.lcCocycleImage (p := p) K
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) = 1 := by
  classical
  haveI : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) K
  haveI : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- `p` is a unit at the prime `𝔮 = primeOf A hK` of `↥K`
  have hnot : (p : NumberField.RingOfIntegers ↥K) ∉
      (Submission.NeukirchUchida.primeOf A hK).asIdeal := by
    rw [← Work.SSGRoute.resCharAt_valuation_lt_one_iff_mem ↥K Ω A hK
      (p : NumberField.RingOfIntegers ↥K)]
    simpa using hAp
  -- the count of locally constant characters of the level-`K` local group is `p`
  have hcardH : Nat.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) = p := by
    rw [Work.SSGRoute.ZConstruction.natCard_lcHoms_levelK_localGroup p k Ω K A hA hK hK]
    exact localKummerQuot_card_eq_prime_of_notMem_notExists
      (Submission.NeukirchUchida.primeOf A hK) (Fact.out : p.Prime) hnot hζ
  -- the character counts transport along the homeomorphism `decompEquiv_fok`
  have htrans : Nat.card ↥(Work.SSGRoute.lcHoms p
        ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup))
      = Nat.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) := by
    have he := Work.SSGRoute.isHomeomorph_decompEquiv_fok k Ω K A
    have hsymm : Continuous ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm :
        ↥(SSGRoute.decomp (k := ↥K) A) → ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :=
      (Work.SSGRoute.decompEquiv_fok k Ω K A).toEquiv.continuous_symm_iff.2 he.isOpenMap
    exact Work.SSGRoute.ZConstruction.natCard_lcHoms_congr p
      (Work.SSGRoute.decompEquiv_fok k Ω K A) he.continuous hsymm
  -- the cardinality of the cocycle image
  have hcard : Nat.card ↥(lcCocycleImage (p := p) K
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) = p := by
    refine le_antisymm ?_ ?_
    · calc Nat.card ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A ⊓ K.fixingSubgroup))
          ≤ Nat.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :=
            lcCocycleImage_card_le_lcHoms (p := p) (K := K) A hA
        _ = Nat.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) := htrans
        _ = p := hcardH
    · calc p = Nat.card ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
            hcardH.symm
        _ ≤ Nat.card ↥(lcCocycleImage (p := p) K
              (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :=
            lcHoms_card_le_lcCocycleImage (p := p) (K := K) A hA
  -- finiteness and the `𝔽_p`-dimension
  haveI hfin : Finite ↥(lcCocycleImage (p := p) K
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :=
    finite_lcCocycleImage (p := p) (K := K) hA
  haveI hft : Fintype ↥(lcCocycleImage (p := p) K
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) := Fintype.ofFinite _
  have hpown : Nat.card ↥(lcCocycleImage (p := p) K
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup))
      = p ^ Module.finrank (ZMod p) ↥(lcCocycleImage (p := p) K
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hpow : p ^ Module.finrank (ZMod p) ↥(lcCocycleImage (p := p) K
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) = p ^ 1 := by
    rw [← hpown, hcard, pow_one]
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hpow

end

end Work.SSGRoute.ZDataMup
