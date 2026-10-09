import Mathlib
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.exists_split_place_avoiding
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Grünwald escape "correction" step

`Work.SSGRoute.GrunwaldEscapeCore.grunwald_escape_correction` is the *correction* step of the
Grünwald-with-escape node `Work.SSGRoute.grunwald_escape_relative` (node N2 of
`_NOTE_STEP4_DESIGN.md`): given a global class `a ∈ Kˣ` whose Kummer character realises the local
datum `g + h A` on the decomposition groups of the places of `T` (`ha`), one must find a *new*
class `b ∈ Kˣ` with the same local data at `T` but whose ramification outside `T` sits over one
single, completely split, place `Q`.

## Mathematical route (Schmidt–Wingberg §4, classical CFT form)

Write `↥K` for the level field, and let `𝔭_A` denote the prime of `K` below `A ∈ T` (the `A` are
pairwise non-`K`-conjugate by `hTdisj`, so this is one prime per class).

1. Choose a modulus `𝔪` of `↥K` supported exactly on the `𝔭_A` (`A ∈ T`) with exponents `N` so large
   that `1 + 𝔭_A^N ⊆ (K_{𝔭_A}^×)^p`, and such that `𝔪` also contains the conductor of `(L₁ ⊔ L₂)/K`.
2. Let `𝔡 ∈ I(𝔪)` be the `T`-free part of the divisor of `a` (an ideal coprime to `𝔪`).
3. `NK.NUV2.RouteB.RayModulus.exists_prime_mem_rayClass` (delegated): there is a prime `𝔮 ∤ 𝔪` whose
   ray class mod `𝔪` is the inverse of the class of `𝔡`.  Equivalently (`classOfIdeal` +
   `CongSubgroup`), there is `γ ∈ Kˣ` with
     `(γ) = 𝔡·𝔮`  and  `γ ≡ 1 (mod 𝔪)`.
   (This is Čebotarev in the ray class field of `𝔪`; the Chebotarev step is the only place where the
   *escape* is used: `𝔮` is chosen after `a`.)
4. Set `b := a / γ`.  Then `div(b) = (div(a)·𝔡^{-1})·𝔮^{-1}` is supported on the `𝔭_A` and `𝔮`, so
   `v_𝔠(b) = 0` for every prime `𝔠 ∉ {𝔭_A} ∪ {𝔮}`; and `[b]_{𝔭_A} = [a]_{𝔭_A}` because `γ` is a
   local `p`-th power there.
5. Kummer dictionary (`Work.SSGRoute.local_kummer_dictionary`,
   `Work.SSGRoute.ZConstruction.kummerCharZMod_fixingSubgroup_mul_pow`): `b/a = γ^{-1}` is a local
   `p`-th power at each `𝔭_A`, hence `kummerCharZMod b = kummerCharZMod a` on every decomposition
   group of `T` — clause (a) of the conclusion.
6. Inertia criterion (`Work.SSGRoute.kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd`): at a
   place `B` whose prime is not among the `𝔭_A` and not `𝔮`, `b` is a unit, so the Kummer character
   of `b` kills the inertia of `B` (clause (b)), provided `B` is not `K`-conjugate to `Q`.
7. The place `Q`: every place above `𝔮` has the same `k`-prime below it, so it remains to choose
   `𝔮` in step 3 with its prime below `k` completely split in `L₁ ⊔ L₂` — this is the
   *orthogonality* condition of the design (`horth₁`, `horth₂`, `hgram`, `hTcov`, `ha`), which makes
   the prescribed Frobenius in the ray class field compatible with the splitting condition in the
   compositum, and is again Čebotarev.  In the degenerate case `L₁ = L₂ = K` the splitting condition
   is automatic and no orthogonality is needed.

Steps 1–4 (the arithmetic core) and step 7 (the orthogonality pairing computation, which uses the
global reciprocity law for the local Kummer pairing) are the two genuinely arithmetic inputs; the
remaining steps are the Kummer/place translation, which is what the lemmas below prepare.

## Status of the ingredients

Proved in this file:

* `smul_eq_of_coe_eq`: `↥K`- and `k`-automorphisms of `Ω` with the same underlying function act
  in the same way on `ValuationSubring Ω` (the transport used throughout);
* `exists_split_place_not_gesKConj`: step 7's *existence* statement for `Q`, i.e. a finite place
  split in `L₁ ⊔ L₂` over `k` and not `K`-conjugate to any element of `T` (Čebotarev, from
  `Work.SSGRoute.exists_split_place_avoiding`);
* `kummerChar_eq_zero_on_decomp_of_localPow`: steps 5–6 at one place (the local dictionary
  `Work.SSGRoute.local_kummer_dictionary` in the direction used above).

Delegated / available elsewhere:

* `Work.SSGRoute.GrunwaldEscapeCore.exists_prime_mem_rayClass` (delegated): every ray class
  modulo `𝔪` contains a prime ideal coprime to `𝔪` — this is the Čebotarev input of step 3;
* `Work.SSGRoute.GrunwaldEscapeCore.exists_pow_eq_of_isCongAt` (proved): `1 + 𝔭^N ⊆ (K_𝔭ˣ)^p` for
  `N` large — the local analysis of steps 1/4;
* `Work.SSGRoute.kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd`: the inertia criterion of
  step 6 (a unit at `B` has Kummer character killing the inertia of `B`).

Still missing (the two items that make this lemma deep):

* **(the reading-off / correction construction)** assembling steps 1–4 into: for the datum of `a`
  there are a prime `𝔮` of `↥K` (coprime to `𝔪`) and `γ ∈ Kˣ` with `(γ) = 𝔡·𝔮`, `γ ≡ 1 (mod 𝔪)`
  — using `exists_prime_mem_rayClass` and `exists_pow_eq_of_isCongAt`;
* **(the orthogonality / step 7)** proving from `hgram`, `horth₁`, `horth₂`, `hTcov`, `ha` and
  `hKimag` that the prescribed ray class is compatible with complete splitting in `L₁ ⊔ L₂`.  The
  shape of the argument: decompose a character `χ` of `Gal(M/K)` killing
  `(L₁ ⊔ L₂).fixingSubgroup` as `χ₁ + χ₂` with `χ₁` killing `L₁.fixingSubgroup` and `χ₂` killing
  `L₂.fixingSubgroup` (the dual of the injection `G/(H₁ ∩ H₂) → G/H₁ × G/H₂`), and compute the
  pairing `⟨χ, Art(𝔡)⟩ = Σ_{𝔭 ∈ T}(a, χ)_𝔭` with the global reciprocity law (product formula) for
  the local Kummer pairing; `hgram` and `hTcov` kill the `g`-part at `L₁`-split places, `horth₁`
  the `h A`-part, `horth₂` the whole datum at the `L₂` stage, and `hKimag` makes the archimedean
  places contribute `1`.
-/

namespace Work.SSGRoute.GrunwaldEscapeCore

open scoped Pointwise

/-! ## The auxiliary place `Q`

The existence of a finite place `Q`, split in `L₁ ⊔ L₂` over `k` and not `K`-conjugate to any
element of `T`, is Čebotarev's density theorem in the form
`Work.SSGRoute.exists_split_place_avoiding`.  This is the place of the escape clause of the
conclusion: the only property of `Q` used there is that its `k`-prime is completely split in
`L₁ ⊔ L₂`. -/
theorem exists_split_place_not_gesKConj (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (K L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂]
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A) :
    ∃ Q : ValuationSubring Ω, SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k (L₁ ⊔ L₂) Q ∧
      ∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q := by
  obtain ⟨Q, hQfin, hQsplit, hQavoid⟩ := exists_split_place_avoiding k Ω (L₁ ⊔ L₂) T hTfin
  refine ⟨Q, hQfin, hQsplit, fun A hA hconj => hQavoid A hA ?_⟩
  obtain ⟨τ, -, hτ⟩ := hconj
  exact ⟨τ, hτ⟩

/-! ## Two `Ω`-automorphisms with the same underlying function act in the same way on places

The pointwise action of `Ω ≃ₐ[k] Ω` and of `Ω ≃ₐ[↥K] Ω` on `ValuationSubring Ω` is the action by
the underlying function, so an `↥K`-automorphism and a `k`-automorphism with the same underlying
function act identically. -/
theorem smul_eq_of_coe_eq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) {φ : Ω ≃ₐ[↥K] Ω} {ψ : Ω ≃ₐ[k] Ω} (h : ⇑φ = ⇑ψ)
    (A : ValuationSubring Ω) : φ • A = ψ • A := by
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, h]⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, h]⟩

/-! ## The local Kummer dictionary at a point of `T`
If `x` is a local `p`-th power at the prime `𝔭` of `↥K` below a finite place `A` of `Ω`, then the
Kummer character of `x` kills the whole decomposition group of `A` inside `G_K`.  This is
`Work.SSGRoute.local_kummer_dictionary` (in the direction "local `p`-th power ⟹ trivial local
class"), transported along the identification of `decomp k A ⊓ K.fixingSubgroup` with
`decomp ↥K A` given by `Work.SSGRoute.gesLocalToGalK`. -/
theorem kummerChar_eq_zero_on_decomp_of_localPow (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (p : ℕ) [Fact p.Prime] (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (x : (↥K)ˣ) (hx : NK.UchidaKummer.localPowClass ↥K p 𝔭 x = 1)
    (σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
    Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ x
      (Work.SSGRoute.gesLocalToGalK K σ) = 0 := by
  have hmem : Work.SSGRoute.gesLocalToGalK K σ ∈ SSGRoute.decomp (k := ↥K) A := by
    rw [MulAction.mem_stabilizer_iff]
    have hσ : (σ : Ω ≃ₐ[k] Ω) • A = A := (Subgroup.mem_inf.mp σ.2).1
    rw [smul_eq_of_coe_eq K (show ⇑(Work.SSGRoute.gesLocalToGalK K σ)
      = ⇑(σ : Ω ≃ₐ[k] Ω) from rfl)]
    exact hσ
  exact (Work.SSGRoute.local_kummer_dictionary (p := p) K ζ hζ A hA 𝔭 h𝔭 x).mpr hx _
    hmem

theorem grunwald_escape_correction (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₁.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₂.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k L₁ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (horth₂ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, g σ + h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → g σ + h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ)) :
    ∃ (Q : ValuationSubring Ω) (b : (↥K)ˣ),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k (L₁ ⊔ L₂) Q ∧
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
      (∀ A ∈ T, ∀ σ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b
            (Work.SSGRoute.gesLocalToGalK K σ) =
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
            (Work.SSGRoute.gesLocalToGalK K σ)) ∧
      (∀ (B : ValuationSubring Ω), SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ Work.SSGRoute.gesKConj K Q B →
        ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup), SSGRoute.IsInertia k B σ →
          Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ b
            (Work.SSGRoute.gesGalKOfFixing K σ hσ) = 0) := by sorry

end Work.SSGRoute.GrunwaldEscapeCore
