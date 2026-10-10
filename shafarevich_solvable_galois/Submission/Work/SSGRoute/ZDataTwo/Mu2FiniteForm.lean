import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.ZDataTwo.ArchKummer
import Submission.Work.SSGRoute.ZDataTwo.exists_kummerChar_agreeing_on_decomp
import Submission.Work.SSGRoute.ZDataTwo.exists_localPowClass_eq
import Submission.Work.SSGRoute.ZDataTwo.normGroup_quadLevel_adicCompletion_ne_top
import Submission.Work.ZDataTwo.kummerChar_eq_zero_iff_isSquare_completion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The finite-place half of the `μ₂` local Tate pairing

For a finite place `A` of `Ω` (i.e. `IsFinPlace k A`), this file constructs the local `p = 2` Tate
pairing on the local cohomology `H1loc 2 k Ω K (ZMod 2) (decomp k A)`:

  `finForm A x y := ⟪αₓ, α_y⟫_{Q}`,

where `Q` is the prime of `k` below `A`, `⟪·,·⟫_Q` is the local Hilbert symbol at the completion
`k_Q`, and `αₓ ∈ kˣ` is a *global* Kummer element of the local class `x` (produced by the local
Kummer surjectivity, `exists_kummerChar_agreeing_on_decomp`).

Well-definedness of the *value* is the local Kummer dictionary
(`Work.ZDataTwo.kummerChar_eq_zero_iff_isSquare_completion`): two global Kummer elements of the same
local class differ by a local square, and the Hilbert symbol is insensitive to squares.
-/

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute
open scoped IntermediateField Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod 2)] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) (ZMod 2)]

/-- `x + x = 0` in a module over `ZMod 2`. -/
lemma add_self_eq_zero_zmodTwo {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  have h : (2 : ZMod 2) • x = 0 := by
    rw [show (2 : ZMod 2) = 0 from by decide, zero_smul]
  have h2 : (2 : ZMod 2) • x = x + x := by
    rw [show (2 : ZMod 2) = 1 + 1 from by decide, add_smul, one_smul]
  rwa [h2] at h

/-- In a commutative group, `a * a' = d * d` exhibits `a` as `a'` times a square. -/
lemma eq_mul_sq_of_mul_eq_sq {G : Type*} [CommGroup G] {a a' d : G} (h : a * a' = d * d) :
    a = a' * ((d * a'⁻¹) * (d * a'⁻¹)) := by
  have h1 : a * a'⁻¹ = d * d * (a'⁻¹ * a'⁻¹) := by
    have h2 : a * a' * (a'⁻¹ * a'⁻¹) = d * d * (a'⁻¹ * a'⁻¹) := by rw [h]
    have h3 : a * a' * (a'⁻¹ * a'⁻¹) = a * a'⁻¹ := by group
    rw [h3] at h2; exact h2
  have h4 : a = (a * a'⁻¹) * a' := by group
  rw [h4, h1]
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- `toAdd` converts the product in `Multiplicative (ZMod 2)` into a sum. -/
lemma toAdd_mul_zmodTwo (u v : Multiplicative (ZMod 2)) :
    Multiplicative.toAdd (u * v) = Multiplicative.toAdd u + Multiplicative.toAdd v := rfl

/-- The Kummer field `k(√α)` of `α ∈ kˣ`, inside `Ω`. -/
noncomputable def kummerField (α : kˣ) : IntermediateField k Ω :=
  k⟮((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω)⟯

instance finiteDimensional_kummerField (α : kˣ) : FiniteDimensional k (kummerField k Ω α) :=
  IntermediateField.adjoin.finiteDimensional
    (x := ((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω))
    (IsIntegral.of_pow (n := 2) (by norm_num) (by
      rw [← Units.val_pow_eq_pow_val, Work.SSGRoute.kummerSqrt_pow, Units.coe_map]
      exact isIntegral_algebraMap))

/-- **The Kummer class** of `α ∈ kˣ` in the local cohomology of a subgroup `H ≤ G_k`. -/
noncomputable def kummerClass (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (H : Subgroup (Ω ≃ₐ[k] Ω))
    (α : kˣ) : H1loc 2 k Ω K (ZMod 2) H :=
  toClass 2 k Ω K (ZMod 2) H (Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α)

/-- **Cochains agreeing on `H` have the same class.**  For locally constant `1`-cocycles `f`, `g`
on `H` that agree pointwise on `H`, the difference `f - g` is a coboundary (the action is trivial),
whence `toClass f = toClass g`. -/
lemma toClass_eq_toClass_of_eq_on {H : Subgroup (Ω ≃ₐ[k] Ω)} {f g : (Ω ≃ₐ[k] Ω) → ZMod 2}
    (hf : f ∈ lcCocycles 2 k Ω K (ZMod 2) H) (hg : g ∈ lcCocycles 2 k Ω K (ZMod 2) H)
    (h : ∀ σ ∈ H, f σ = g σ) :
    toClass 2 k Ω K (ZMod 2) H f = toClass 2 k Ω K (ZMod 2) H g := by
  have hsub : f - g ∈ lcCocycles 2 k Ω K (ZMod 2) H := Submodule.sub_mem _ hf hg
  have hcob : f - g ∈ coboundaries 2 k Ω K (ZMod 2) H :=
    (mem_coboundaries 2 k Ω K (ZMod 2) H (f - g)).mpr
      ((isCoboundaryOn_iff_eq_zero k Ω K H (f - g)).mpr (fun σ hσ => by
        simp only [Pi.sub_apply, Pi.zero_apply, h σ hσ, sub_self]))
  have hzero : toClass 2 k Ω K (ZMod 2) H (f - g) = 0 :=
    (toClass_eq_zero_iff 2 k Ω K (ZMod 2) H hsub).mpr hcob
  have hdecomp : f = g + (f - g) := by funext σ; simp [Pi.add_apply]
  rw [hdecomp, toClass_add 2 k Ω K (ZMod 2) H hg hsub, hzero, add_zero]

/-- The Kummer character of `α` vanishes on the fixing subgroup of `k(√α)`. -/
lemma kummerChar_eq_zero_of_mem_fixingSubgroup (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (α : kˣ)
    {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ (kummerField k Ω α).fixingSubgroup) :
    Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α σ = 0 := by
  rw [Work.SSGRoute.kummerChar_eq_zero_iff_apply_sqrt]
  exact (IntermediateField.mem_fixingSubgroup_iff (kummerField k Ω α) σ).mp hσ _
    (IntermediateField.mem_adjoin_simple_self k _)

/-- **The Kummer character is a locally constant cocycle on every subgroup.** -/
lemma kummerChar_mem_lcCocycles (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (H : Subgroup (Ω ≃ₐ[k] Ω))
    (α : kˣ) :
    Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α ∈ lcCocycles 2 k Ω K (ZMod 2) H := by
  rw [mem_lcCocycles]
  refine ⟨?_, ?_⟩
  · intro g _ h _
    rw [Work.SSGRoute.kummerChar_mul_apply, smul_zmodTwo_eq_self]
  · refine ⟨(kummerField k Ω α).fixingSubgroup, ?_, ?_⟩
    · exact IntermediateField.fixingSubgroup_isOpen (kummerField k Ω α)
    · intro g _ u hu _
      have hadd := Work.SSGRoute.kummerChar_mul_apply (K := k) (Ω := Ω) ζ hζ α g u
      rw [hadd, kummerChar_eq_zero_of_mem_fixingSubgroup k Ω ζ hζ α hu, add_zero]

/-- **Additivity of the Kummer class.** -/
lemma kummerClass_mul (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (H : Subgroup (Ω ≃ₐ[k] Ω))
    (α β : kˣ) :
    kummerClass k Ω K ζ hζ H (α * β) =
      kummerClass k Ω K ζ hζ H α + kummerClass k Ω K ζ hζ H β := by
  unfold kummerClass
  rw [Work.SSGRoute.kummerChar_mul (K := k) (Ω := Ω) ζ hζ α β]
  exact toClass_add 2 k Ω K (ZMod 2) H (kummerChar_mem_lcCocycles k Ω K ζ hζ H α)
    (kummerChar_mem_lcCocycles k Ω K ζ hζ H β)

/-- **Surjectivity of the Kummer class map on a decomposition group.**  Every local class of
`decomp k A` is the class of the global Kummer character of some `α ∈ kˣ`. -/
theorem kummerClass_surjective (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (A : ValuationSubring Ω)
    (hA : IsFinPlace k A) :
    Function.Surjective (kummerClass k Ω K ζ hζ (decomp k A)) := by
  intro x
  obtain ⟨g, hg, hgx⟩ := toClass_surjective 2 k Ω K (ZMod 2) (decomp k A) x
  obtain ⟨b, hb⟩ := exists_kummerChar_agreeing_on_decomp (k := k) (Ω := Ω) ζ hζ A hA g
    ((isCocycleOn_iff_add k Ω K (decomp k A) g).mp hg.1) hg.2
  rw [← hgx]
  refine ⟨b, ?_⟩
  show toClass 2 k Ω K (ZMod 2) (decomp k A) (Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ b)
    = toClass 2 k Ω K (ZMod 2) (decomp k A) g
  exact toClass_eq_toClass_of_eq_on k Ω K (kummerChar_mem_lcCocycles k Ω K ζ hζ _ b) hg
    (fun σ hσ => (hb σ hσ).symm)

/-! ## The local Hilbert pairing of two Kummer classes -/

/-- The prime of `k` below a finite place `A` of `Ω`. -/
noncomputable def primeBelow (A : ValuationSubring Ω) (hA : IsFinPlace k A) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
  (Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
    (A.comap (algebraMap k Ω)) hA
    (fun x => Commons.NumberTheory.NumberField.ringOfIntegers_le_of_valuationSubring
      (A.comap (algebraMap k Ω)) x)).choose

lemma primeBelow_spec (A : ValuationSubring Ω) (hA : IsFinPlace k A) :
    A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k (primeBelow k Ω A hA) :=
  (Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
    (A.comap (algebraMap k Ω)) hA
    (fun x => Commons.NumberTheory.NumberField.ringOfIntegers_le_of_valuationSubring
      (A.comap (algebraMap k Ω)) x)).choose_spec

/-- The local reciprocity datum at a completion of `k`. -/
noncomputable def adicReciprocity (Q : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers k)) :
    NK.LocalArtin.ReciprocityMap (Q.adicCompletion k)
      (SeparableClosure (Q.adicCompletion k)) :=
  (Classical.choice (NK.NUV2.ARL.HR.artinReciprocity_adicCompletion (K := k) Q)).toReciprocityMap

/-- The image of a global unit `α ∈ kˣ` in the completion `k_Qˣ`. -/
noncomputable def localImage (Q : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers k)) (α : kˣ) : (Q.adicCompletion k)ˣ :=
  Units.map (algebraMap k (Q.adicCompletion k)).toMonoidHom α

lemma localImage_mul (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (α β : kˣ) : localImage k Q (α * β) = localImage k Q α * localImage k Q β :=
  map_mul _ α β

/-- **The local Hilbert pairing of two global units** at the prime `Q`: `toAdd` of `⟪ᾱ,β̄⟫_Q`. -/
noncomputable def finPair (Q : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers k)) (α β : kˣ) : ZMod 2 :=
  Multiplicative.toAdd
    (NK.NUV2.LC.hilbertSymbol (adicReciprocity k Q) (localImage k Q α) (localImage k Q β))

/-- The Hilbert symbol is a square in the first variable: it is unchanged when the first argument
is multiplied by a square. -/
lemma hilbertSymbol_mul_sq_left (Q : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers k)) (a c b : (Q.adicCompletion k)ˣ) :
    NK.NUV2.LC.hilbertSymbol (adicReciprocity k Q) (a * (c * c)) b =
      NK.NUV2.LC.hilbertSymbol (adicReciprocity k Q) a b := by
  rw [Work.HilbertSymbolGeneral.canonicalAPI.hilbertSymbol_mul_left,
    Work.HilbertSymbolGeneral.canonicalAPI.hilbertSymbol_sq_left, mul_one]

/-- The Hilbert symbol is a square in the second variable. -/
lemma hilbertSymbol_mul_sq_right (Q : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers k)) (a b c : (Q.adicCompletion k)ˣ) :
    NK.NUV2.LC.hilbertSymbol (adicReciprocity k Q) a (b * (c * c)) =
      NK.NUV2.LC.hilbertSymbol (adicReciprocity k Q) a b := by
  rw [Work.HilbertSymbolGeneral.canonicalAPI.hilbertSymbol_mul_right,
    Work.HilbertSymbolGeneral.canonicalAPI.hilbertSymbol_sq_right, mul_one]

/-- The Kummer character of `α * α'` vanishes on `decomp k A` when `κ α = κ α'`. -/
lemma kummerChar_mul_vanish_of_class_eq (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (A : ValuationSubring Ω) {α α' : kˣ}
    (h : kummerClass k Ω K ζ hζ (decomp k A) α = kummerClass k Ω K ζ hζ (decomp k A) α') :
    ∀ σ ∈ decomp k A, Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ (α * α') σ = 0 := by
  have hsum : kummerClass k Ω K ζ hζ (decomp k A) (α * α') = 0 := by
    rw [kummerClass_mul, h, add_self_eq_zero_zmodTwo]
  have hmem : Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ (α * α')
      ∈ lcCocycles 2 k Ω K (ZMod 2) (decomp k A) :=
    kummerChar_mem_lcCocycles k Ω K ζ hζ _ _
  have hzero : toClass 2 k Ω K (ZMod 2) (decomp k A)
      (Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ (α * α')) = 0 := by
    rw [kummerClass] at hsum
    exact hsum
  intro σ hσ
  exact (isCoboundaryOn_iff_eq_zero k Ω K (decomp k A) _).mp
    ((mem_coboundaries 2 k Ω K (ZMod 2) (decomp k A) _).mp
      ((toClass_eq_zero_iff 2 k Ω K (ZMod 2) (decomp k A) hmem).mp hzero)) σ hσ

/-- **Well-definedness of the finite pairing in the first variable.**  If two global Kummer
elements define the same local class, the local Hilbert symbol against any fixed `β` is unchanged:
the two differ by a local square, and the symbol is insensitive to squares. -/
theorem finPair_congr_left (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (A : ValuationSubring Ω)
    (hA : IsFinPlace k A) (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hQ : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k Q)
    {α α' β : kˣ}
    (h : kummerClass k Ω K ζ hζ (decomp k A) α = kummerClass k Ω K ζ hζ (decomp k A) α') :
    finPair k Q α β = finPair k Q α' β := by
  have hvan := kummerChar_mul_vanish_of_class_eq k Ω K ζ hζ A h
  obtain ⟨d, hd⟩ := (Work.ZDataTwo.kummerChar_eq_zero_iff_isSquare_completion (k := k) (Ω := Ω)
    ζ hζ A hA Q hQ (α * α')).mp hvan
  have hda : localImage k Q α * localImage k Q α' = d * d := by
    have h1 : ((localImage k Q (α * α') : (Q.adicCompletion k)ˣ) : Q.adicCompletion k)
        = (d * d : (Q.adicCompletion k)ˣ) := by
      rw [localImage, Units.coe_map]
      exact hd
    rw [localImage_mul] at h1
    exact Units.ext h1
  rw [finPair, finPair]
  set a := localImage k Q α with ha
  set a' := localImage k Q α' with ha'
  set b := localImage k Q β with hb
  have hfac : a = a' * ((d * a'⁻¹) * (d * a'⁻¹)) := eq_mul_sq_of_mul_eq_sq hda
  rw [hfac, hilbertSymbol_mul_sq_left]

/-- **Well-definedness of the finite pairing in the second variable.** -/
theorem finPair_congr_right (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (A : ValuationSubring Ω)
    (hA : IsFinPlace k A) (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hQ : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k Q)
    {β β' α : kˣ}
    (h : kummerClass k Ω K ζ hζ (decomp k A) β = kummerClass k Ω K ζ hζ (decomp k A) β') :
    finPair k Q α β = finPair k Q α β' := by
  have hvan := kummerChar_mul_vanish_of_class_eq k Ω K ζ hζ A h
  obtain ⟨d, hd⟩ := (Work.ZDataTwo.kummerChar_eq_zero_iff_isSquare_completion (k := k) (Ω := Ω)
    ζ hζ A hA Q hQ (β * β')).mp hvan
  have hdb : localImage k Q β * localImage k Q β' = d * d := by
    have h1 : ((localImage k Q (β * β') : (Q.adicCompletion k)ˣ) : Q.adicCompletion k)
        = (d * d : (Q.adicCompletion k)ˣ) := by
      rw [localImage, Units.coe_map]
      exact hd
    rw [localImage_mul] at h1
    exact Units.ext h1
  rw [finPair, finPair]
  set a := localImage k Q α with ha
  set b := localImage k Q β with hb
  set b' := localImage k Q β' with hb'
  have hfac : b = b' * ((d * b'⁻¹) * (d * b'⁻¹)) := eq_mul_sq_of_mul_eq_sq hdb
  rw [hfac, hilbertSymbol_mul_sq_right]

/-- **Multiplicativity of the finite pairing in the first variable.** -/
lemma finPair_mul_left (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (α α' β : kˣ) :
    finPair k Q (α * α') β = finPair k Q α β + finPair k Q α' β := by
  rw [finPair, finPair, finPair, localImage_mul,
    Work.HilbertSymbolGeneral.canonicalAPI.hilbertSymbol_mul_left, toAdd_mul_zmodTwo]

/-- **Multiplicativity of the finite pairing in the second variable.** -/
lemma finPair_mul_right (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (α β β' : kˣ) :
    finPair k Q α (β * β') = finPair k Q α β + finPair k Q α β' := by
  rw [finPair, finPair, finPair, localImage_mul,
    Work.HilbertSymbolGeneral.canonicalAPI.hilbertSymbol_mul_right, toAdd_mul_zmodTwo]

/-- Symmetry of the finite pairing. -/
lemma finPair_comm (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (α β : kˣ) : finPair k Q α β = finPair k Q β α := by
  rw [finPair, finPair, Work.HilbertSymbolGeneral.hilbertSymbol_comm]


/-- The trivial Kummer class: the Kummer character of `1` is zero. -/
lemma kummerChar_one_apply (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (σ : Ω ≃ₐ[k] Ω) :
    Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ (1 : kˣ) σ = 0 :=
  (Work.SSGRoute.kummerChar_eq_zero_iff_exists_sqrt_fixed (K := k) (Ω := Ω) ζ hζ (1 : kˣ) σ).mpr
    ⟨1, by simp, by simp⟩

lemma kummerClass_one (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    kummerClass k Ω K ζ hζ H (1 : kˣ) = 0 := by
  unfold kummerClass
  rw [toClass_eq_zero_iff 2 k Ω K (ZMod 2) H (kummerChar_mem_lcCocycles k Ω K ζ hζ H 1),
    mem_coboundaries]
  exact (isCoboundaryOn_iff_eq_zero k Ω K H _).mpr (fun σ _ => kummerChar_one_apply k Ω ζ hζ σ)

lemma finPair_one_left (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (α : kˣ) : finPair k Q 1 α = 0 := by
  rw [finPair]
  simp [localImage]

lemma finPair_one_right (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (α : kˣ) : finPair k Q α 1 = 0 := by
  rw [finPair]
  simp [localImage]

/-- A chosen right inverse of the Kummer class map on `decomp k A`. -/
noncomputable def kummerRep (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (A : ValuationSubring Ω)
    (hA : IsFinPlace k A) : H1loc 2 k Ω K (ZMod 2) (decomp k A) → kˣ :=
  Function.surjInv (kummerClass_surjective k Ω K ζ hζ A hA)

lemma kummerClass_kummerRep (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (A : ValuationSubring Ω)
    (hA : IsFinPlace k A) (x : H1loc 2 k Ω K (ZMod 2) (decomp k A)) :
    kummerClass k Ω K ζ hζ (decomp k A) (kummerRep k Ω K ζ hζ A hA x) = x :=
  Function.surjInv_eq _ x

/-- **The finite-place local Tate pairing** at the place `A`: the local Hilbert symbol of global
Kummer representatives of the two local classes. -/
noncomputable def finForm (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (A : ValuationSubring Ω)
    (hA : IsFinPlace k A) :
    H1loc 2 k Ω K (ZMod 2) (decomp k A) →ₗ[ZMod 2]
      (H1loc 2 k Ω K (ZMod 2) (decomp k A) →ₗ[ZMod 2] ZMod 2) :=
  AddMonoidHom.toZModLinearMap 2
  { toFun := fun x => AddMonoidHom.toZModLinearMap 2
      { toFun := fun y => finPair k (primeBelow k Ω A hA)
          (kummerRep k Ω K ζ hζ A hA x) (kummerRep k Ω K ζ hζ A hA y)
        map_zero' := by
          have hκ : kummerClass k Ω K ζ hζ (decomp k A) (kummerRep k Ω K ζ hζ A hA 0)
              = kummerClass k Ω K ζ hζ (decomp k A) 1 := by
            rw [kummerClass_kummerRep, kummerClass_one]
          rw [finPair_congr_right k Ω K ζ hζ A hA (primeBelow k Ω A hA) (primeBelow_spec k Ω A hA)
            (α := kummerRep k Ω K ζ hζ A hA x) hκ]
          exact finPair_one_right k (primeBelow k Ω A hA) _
        map_add' := fun y y' => by
          have hκ : kummerClass k Ω K ζ hζ (decomp k A)
                (kummerRep k Ω K ζ hζ A hA y * kummerRep k Ω K ζ hζ A hA y')
              = kummerClass k Ω K ζ hζ (decomp k A)
                (kummerRep k Ω K ζ hζ A hA (y + y')) := by
            rw [kummerClass_mul, kummerClass_kummerRep, kummerClass_kummerRep,
              kummerClass_kummerRep]
          rw [finPair_congr_right k Ω K ζ hζ A hA (primeBelow k Ω A hA) (primeBelow_spec k Ω A hA)
            (α := kummerRep k Ω K ζ hζ A hA x) hκ.symm]
          exact finPair_mul_right k (primeBelow k Ω A hA) _ _ _ },
    map_zero' := by
      refine LinearMap.ext (fun y => ?_)
      show finPair k (primeBelow k Ω A hA) (kummerRep k Ω K ζ hζ A hA 0)
        (kummerRep k Ω K ζ hζ A hA y) = 0
      have hκ : kummerClass k Ω K ζ hζ (decomp k A) (kummerRep k Ω K ζ hζ A hA 0)
          = kummerClass k Ω K ζ hζ (decomp k A) 1 := by
        rw [kummerClass_kummerRep, kummerClass_one]
      rw [finPair_congr_left k Ω K ζ hζ A hA (primeBelow k Ω A hA) (primeBelow_spec k Ω A hA)
        (β := kummerRep k Ω K ζ hζ A hA y) hκ]
      exact finPair_one_left k (primeBelow k Ω A hA) _
    map_add' := fun x x' => by
      refine LinearMap.ext (fun y => ?_)
      show finPair k (primeBelow k Ω A hA) (kummerRep k Ω K ζ hζ A hA (x + x'))
        (kummerRep k Ω K ζ hζ A hA y) =
        finPair k (primeBelow k Ω A hA) (kummerRep k Ω K ζ hζ A hA x)
          (kummerRep k Ω K ζ hζ A hA y) +
        finPair k (primeBelow k Ω A hA) (kummerRep k Ω K ζ hζ A hA x')
          (kummerRep k Ω K ζ hζ A hA y)
      have hκ : kummerClass k Ω K ζ hζ (decomp k A)
            (kummerRep k Ω K ζ hζ A hA x * kummerRep k Ω K ζ hζ A hA x')
          = kummerClass k Ω K ζ hζ (decomp k A) (kummerRep k Ω K ζ hζ A hA (x + x')) := by
        rw [kummerClass_mul, kummerClass_kummerRep, kummerClass_kummerRep, kummerClass_kummerRep]
      rw [finPair_congr_left k Ω K ζ hζ A hA (primeBelow k Ω A hA) (primeBelow_spec k Ω A hA)
        (β := kummerRep k Ω K ζ hζ A hA y) hκ.symm]
      exact finPair_mul_left k (primeBelow k Ω A hA) _ _ _ }

lemma finForm_apply (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (A : ValuationSubring Ω)
    (hA : IsFinPlace k A) (x y : H1loc 2 k Ω K (ZMod 2) (decomp k A)) :
    finForm k Ω K ζ hζ A hA x y = finPair k (primeBelow k Ω A hA)
      (kummerRep k Ω K ζ hζ A hA x) (kummerRep k Ω K ζ hζ A hA y) := rfl

/-- **The value of the finite-place pairing on the classes of global Kummer characters.** -/
theorem finForm_kummerClass (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (A : ValuationSubring Ω)
    (hA : IsFinPlace k A) (α β : kˣ) :
    finForm k Ω K ζ hζ A hA (kummerClass k Ω K ζ hζ (decomp k A) α)
        (kummerClass k Ω K ζ hζ (decomp k A) β)
      = finPair k (primeBelow k Ω A hA) α β := by
  rw [finForm_apply]
  have hα : kummerClass k Ω K ζ hζ (decomp k A) (kummerRep k Ω K ζ hζ A hA
      (kummerClass k Ω K ζ hζ (decomp k A) α)) = kummerClass k Ω K ζ hζ (decomp k A) α :=
    kummerClass_kummerRep k Ω K ζ hζ A hA _
  have hβ : kummerClass k Ω K ζ hζ (decomp k A) (kummerRep k Ω K ζ hζ A hA
      (kummerClass k Ω K ζ hζ (decomp k A) β)) = kummerClass k Ω K ζ hζ (decomp k A) β :=
    kummerClass_kummerRep k Ω K ζ hζ A hA _
  rw [finPair_congr_left k Ω K ζ hζ A hA (primeBelow k Ω A hA) (primeBelow_spec k Ω A hA)
      (β := kummerRep k Ω K ζ hζ A hA (kummerClass k Ω K ζ hζ (decomp k A) β)) hα,
    finPair_congr_right k Ω K ζ hζ A hA (primeBelow k Ω A hA) (primeBelow_spec k Ω A hA)
      (α := α) hβ]

end Work.SSGRoute.ZDataTwo
