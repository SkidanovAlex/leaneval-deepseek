import Submission.Work.SSGRoute.ZDataTwo.Mu2FiniteForm
import Submission.Work.HilbertSymbolGeneral.hilbertSymbol_comm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Non-degeneracy of the finite-place `μ₂` Tate pairing

The pairing `finPair k Q α β = ⟪ᾱ, β̄⟫_Q` of two global units is non-degenerate modulo the local
Kummer classes: if `⟪ᾱ, β̄⟫_Q = 1` for *every* `β ∈ kˣ`, then `α` is a local square at `Q`, i.e. its
Kummer class vanishes on `decomp k A`.

The proof is the standard one: if `ᾱ` is not a local square then `k_Q(√ᾱ)/k_Q` is a genuine
quadratic extension, whose norm group is proper (`normGroup_quadLevel_adicCompletion_ne_top`); a
non-norm `u` is realised as `β̄` up to a square by weak approximation
(`exists_localPowClass_eq`), and the norm criterion (`hilbertSymbol_eq_one_iff_normGroup` together
with the explicit norm-form description `mem_normGroup_quadLevel_iff`) then makes `⟪ᾱ, β̄⟫_Q ≠ 1`.
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

lemma toAdd_eq_zero_iff (x : Multiplicative (ZMod 2)) : Multiplicative.toAdd x = 0 ↔ x = 1 := by
  fin_cases x <;> decide

/-- **Non-degeneracy of the finite pairing in the first variable.** -/
theorem finPair_nondegenerate_left (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (A : ValuationSubring Ω) (hA : IsFinPlace k A)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hQ : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k Q)
    (α : kˣ) (h : ∀ β : kˣ, finPair k Q α β = 0) :
    kummerClass k Ω K ζ hζ (decomp k A) α = 0 := by
  by_contra hne
  have hnv : ¬ ∀ σ ∈ decomp k A, Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α σ = 0 := by
    intro hv
    refine hne ?_
    unfold kummerClass
    rw [toClass_eq_zero_iff 2 k Ω K (ZMod 2) (decomp k A)
      (kummerChar_mem_lcCocycles k Ω K ζ hζ (decomp k A) α), mem_coboundaries]
    exact (isCoboundaryOn_iff_eq_zero k Ω K (decomp k A) _).mpr hv
  have hnsq : ¬ ∃ d : (Q.adicCompletion k)ˣ, localImage k Q α = d * d := by
    rintro ⟨d, hd⟩
    refine hnv ((Work.ZDataTwo.kummerChar_eq_zero_iff_isSquare_completion (k := k) (Ω := Ω) ζ hζ
      A hA Q hQ α).mpr ⟨d, ?_⟩)
    have hd' := congrArg (fun u : (Q.adicCompletion k)ˣ => (u : Q.adicCompletion k)) hd
    simpa [localImage, Units.val_mul] using hd'
  set a : (Q.adicCompletion k)ˣ := localImage k Q α with ha
  have hnsq' : ¬ ∃ d : (Q.adicCompletion k)ˣ, a = d * d := by
    rintro ⟨d, hd⟩
    exact hnsq ⟨d, by rw [ha]; exact hd⟩
  have hy' : NK.NUV2.LC.sqroot (F := Q.adicCompletion k)
      (F' := SeparableClosure (Q.adicCompletion k)) a *
      NK.NUV2.LC.sqroot (F := Q.adicCompletion k)
      (F' := SeparableClosure (Q.adicCompletion k)) a =
      algebraMap (Q.adicCompletion k) (SeparableClosure (Q.adicCompletion k))
        (a : Q.adicCompletion k) :=
    NK.NUV2.LC.sqroot_mul_self (F := Q.adicCompletion k)
      (F' := SeparableClosure (Q.adicCompletion k)) a
  have hyn : NK.NUV2.LC.sqroot (F := Q.adicCompletion k)
      (F' := SeparableClosure (Q.adicCompletion k)) a
      ∉ Set.range (algebraMap (Q.adicCompletion k) (SeparableClosure (Q.adicCompletion k))) := by
    rintro ⟨c, hc⟩
    have hcc : c * c = (a : Q.adicCompletion k) :=
      (algebraMap (Q.adicCompletion k) (SeparableClosure (Q.adicCompletion k))).injective
        (by rw [map_mul, hc, hy'])
    have hc0 : c ≠ 0 := fun h0 => a.ne_zero (by rw [← hcc, h0, mul_zero])
    exact hnsq' ⟨Units.mk0 c hc0, by
      refine Units.ext ?_
      show (a : Q.adicCompletion k) = c * c
      exact hcc.symm⟩
  have hNnt : NK.LocalReciprocity.normGroup (Q.adicCompletion k)
      ↥(NK.NUV2.LC.quadLevel (NK.NUV2.LC.sqroot (F := Q.adicCompletion k)
          (F' := SeparableClosure (Q.adicCompletion k)) a)
        (a : Q.adicCompletion k) hy') ≠ ⊤ :=
    normGroup_quadLevel_adicCompletion_ne_top Q (a : Q.adicCompletion k) _ hy' hyn
  obtain ⟨u, -, hu⟩ := SetLike.not_le_iff_exists.mp (show ¬ (⊤ : Subgroup (Q.adicCompletion k)ˣ) ≤
      NK.LocalReciprocity.normGroup (Q.adicCompletion k)
        ↥(NK.NUV2.LC.quadLevel (NK.NUV2.LC.sqroot (F := Q.adicCompletion k)
            (F' := SeparableClosure (Q.adicCompletion k)) a)
          (a : Q.adicCompletion k) hy') from fun hle => hNnt (top_le_iff.mp hle))
  obtain ⟨b, c, hc, hbc⟩ := exists_localPowClass_eq (k := k) Q u
  have hcb : localImage k Q b = u * c := hbc
  have hne1 : NK.NUV2.LC.hilbertSymbol (adicReciprocity k Q) a (localImage k Q b) ≠ 1 := by
    rw [hcb, Work.HilbertSymbolGeneral.canonicalAPI.hilbertSymbol_mul_right]
    obtain ⟨d, hd⟩ := hc
    have hd2 : d ^ 2 = c := by simpa [powMonoidHom_apply] using hd
    have hc2 : c = d * d := by rw [← hd2, pow_two]
    rw [hc2, Work.HilbertSymbolGeneral.canonicalAPI.hilbertSymbol_sq_right, mul_one,
      Work.HilbertSymbolGeneral.hilbertSymbol_comm]
    intro h1
    obtain ⟨y2, hy2, hmem⟩ :=
      (NK.NUV2.LC.hilbertSymbol_eq_one_iff_normGroup (adicReciprocity k Q) u a).mp h1
    exact hu ((Work.HilbertSymbolGeneral.mem_normGroup_quadLevel_iff _ (a : Q.adicCompletion k)
      a.ne_zero hy' u).mpr ((Work.HilbertSymbolGeneral.mem_normGroup_quadLevel_iff y2
      (a : Q.adicCompletion k) a.ne_zero hy2 u).mp hmem))
  refine hne1 ?_
  have h0' : Multiplicative.toAdd
      (NK.NUV2.LC.hilbertSymbol (adicReciprocity k Q) a (localImage k Q b)) = 0 := by
    have he : finPair k Q α b = Multiplicative.toAdd
        (NK.NUV2.LC.hilbertSymbol (adicReciprocity k Q) a (localImage k Q b)) := by
      rw [finPair, ← ha]
    rw [← he]
    exact h b
  exact (toAdd_eq_zero_iff _).mp h0'

/-- **Non-degeneracy of the finite pairing in the second variable.** -/
theorem finPair_nondegenerate_right (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (A : ValuationSubring Ω) (hA : IsFinPlace k A)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hQ : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k Q)
    (β : kˣ) (h : ∀ α : kˣ, finPair k Q α β = 0) :
    kummerClass k Ω K ζ hζ (decomp k A) β = 0 := by
  refine finPair_nondegenerate_left k Ω K ζ hζ A hA Q hQ β ?_
  intro γ
  rw [finPair_comm k Q β γ]
  exact h γ

/-- **Non-degeneracy of the finite-place local Tate pairing** on the local cohomology. -/
theorem finForm_nondegenerate (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (A : ValuationSubring Ω)
    (hA : IsFinPlace k A) :
    (∀ x : H1loc 2 k Ω K (ZMod 2) (decomp k A),
        (∀ y, finForm k Ω K ζ hζ A hA x y = 0) → x = 0) ∧
      (∀ y : H1loc 2 k Ω K (ZMod 2) (decomp k A),
        (∀ x, finForm k Ω K ζ hζ A hA x y = 0) → y = 0) := by
  constructor
  · intro x hx
    have hrep := kummerClass_kummerRep k Ω K ζ hζ A hA x
    rw [← hrep]
    refine finPair_nondegenerate_left k Ω K ζ hζ A hA (primeBelow k Ω A hA)
      (primeBelow_spec k Ω A hA) _ ?_
    intro β
    rw [← finForm_kummerClass k Ω K ζ hζ A hA (kummerRep k Ω K ζ hζ A hA x) β, hrep]
    exact hx _
  · intro y hy
    have hrep := kummerClass_kummerRep k Ω K ζ hζ A hA y
    rw [← hrep]
    refine finPair_nondegenerate_right k Ω K ζ hζ A hA (primeBelow k Ω A hA)
      (primeBelow_spec k Ω A hA) _ ?_
    intro α
    rw [← finForm_kummerClass k Ω K ζ hζ A hA α (kummerRep k Ω K ζ hζ A hA y), hrep]
    exact hy _

end Work.SSGRoute.ZDataTwo
