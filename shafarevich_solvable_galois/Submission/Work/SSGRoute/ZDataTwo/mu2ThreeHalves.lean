import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NodeS37.claimOfPreTwo
import Submission.Work.SSGRoute.NodeS37.goodClassOfHistory
import Submission.Work.SSGRoute.NodeS37.twoRecExists
import Submission.Work.SSGRoute.ZDataTwo.mu2EscapeRealisationH
import Submission.Work.SSGRoute.ZDataTwo.mu2PinnedValueDiagonal
import Submission.Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo

/-- **A `Λ`-split place is not `K`-conjugate to itself over a different `K`-orbit.**  If `Q` is a
finite place whose decomposition group is contained in `Gal(Ω/Λ)` (i.e. `Q` splits completely in
`Λ`), then for every `σ ∉ K.fixingSubgroup` the place `σ • Q` and `Q` do **not** have the same prime
of `↥K` below them.

Equivalently (by `Work.SSGRoute.exists_mem_fixingSubgroup_smul_eq_of_comap_eq`): no lift of a
non-trivial element of `Gal(K|k)` lies in the decomposition group of a `Λ`-split place `Q`.
Consequently the decomposition group of the `k`-prime below a `Λ`-split place is *involution-free*
inside `Gal(K|k)` — which is what makes the paper's `G₁`-case `(z_i)^{σQ} = 0` consistent with the
escape normalisation `Odd (count_𝔮 b)`; without the `Λ`-splitness of `Q` the two would clash. -/
lemma comap_smul_ne_comap_of_isSplitIn
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] (hKΛ : K ≤ Λ)
    (Q : ValuationSubring Ω) (hQ : SSGRoute.IsFinPlace k Q)
    (hQsplit : SSGRoute.IsSplitIn k Λ Q)
    {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∉ K.fixingSubgroup) :
    (σ • Q).comap (algebraMap ↥K Ω) ≠ Q.comap (algebraMap ↥K Ω) := by
  classical
  have hne (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B) :
      B.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    intro htop
    apply hB
    refine le_antisymm le_top ?_
    intro x _
    have h1 : algebraMap ↥K Ω (algebraMap k ↥K x) ∈ B := by
      rw [← ValuationSubring.mem_comap, htop]
      exact trivial
    rwa [← IsScalarTower.algebraMap_apply k ↥K Ω] at h1
  intro h
  obtain ⟨τ, hτ, hτQ⟩ :=
    Work.SSGRoute.exists_mem_fixingSubgroup_smul_eq_of_comap_eq K
      (hne (σ • Q) ((SSGRoute.isFinPlace_smul_iff Q σ).mpr hQ)) h
  have hfix : (τ * σ) • Q = Q := by rw [mul_smul, hτQ]
  have hdecomp : τ * σ ∈ SSGRoute.decomp k Q := by
    rw [SSGRoute.decomp, MulAction.mem_stabilizer_iff]
    exact hfix
  have hΛ : τ * σ ∈ Λ.fixingSubgroup := hQsplit hdecomp
  have hK : τ * σ ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hΛ ⊢
    intro x hx
    exact hΛ x (hKΛ hx)
  exact hσ (by
    have hmem := K.fixingSubgroup.mul_mem (K.fixingSubgroup.inv_mem hτ) hK
    simpa [inv_mul_cancel_left] using hmem)

/-! ## The algebraic heart of the reduction to one good class

The target asks for three halves.  If `b ∈ Kˣ` is a global Kummer element of `y` (which exists by
`ZSplit.exists_kummerCocharZMod_of_additive_locConst`) and `B ∈ Kˣ` is any class with the
companion-controlled ramification, then the three halves `b, b, b⁻¹b⁻¹B` have the *same* local
data as `B`: each of them agrees with `y` on the `cs(S)`-blocks, each kills the involutions, and
their product is `B`, so the sum's cochain is `χ_B`.  The two identities below are exactly that
computation; they are the reason the target is equivalent to the existence of a single good class.
-/

/-- The Kummer cochain of a product is the sum of the cochains. -/
lemma nodeKummerCochar_mul_local (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (a d : (↥K)ˣ) :
    Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (a * d) =
      Work.SSGRoute.nodeKummerCochar K ζ hζK hζ a +
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ d :=
  kummerCochar_mul K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) a d

/-- A square is invisible to the Kummer cochain. -/
lemma nodeKummerCochar_sq_local (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (c : (↥K)ˣ) :
    Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (c ^ 2) = 0 :=
  kummerCochar_sq K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) c

/-- **The third half has the local data of `B`.**  `χ_{b⁻¹b⁻¹B} = χ_B`: the two `b⁻¹`-factors
contribute `χ_{b⁻¹} + χ_{b⁻¹} = χ_{(b⁻¹)²} = 0` in `𝔽₂`. -/
lemma nodeKummerCochar_inv_inv_mul (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b B : (↥K)ˣ) :
    Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (b⁻¹ * b⁻¹ * B) =
      Work.SSGRoute.nodeKummerCochar K ζ hζK hζ B := by
  rw [nodeKummerCochar_mul_local k Ω K ζ hζ hζK (b⁻¹ * b⁻¹) B,
    show b⁻¹ * b⁻¹ = (b⁻¹) ^ 2 from (pow_two b⁻¹).symm,
    nodeKummerCochar_sq_local k Ω K ζ hζ hζK b⁻¹, zero_add]

/-- **The three halves `b, b, b⁻¹b⁻¹B` multiply to `B`,** so the three-term sum of the `z`-data has
the Kummer cochain of `B`. -/
lemma threeHalves_mul (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b B : (↥K)ˣ) :
    b * b * (b⁻¹ * b⁻¹ * B) = B := by
  group

theorem mu2ThreeHalves (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (oracle : ∀ (T : Finset (ValuationSubring Ω)),
      (∀ A ∈ T, SSGRoute.IsFinPlace k A) →
      (∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (B.valuation (2 : Ω) < 1 ∨
          ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ Λ.fixingSubgroup) →
        ∃ A ∈ T, Work.SSGRoute.gesKConj K A B) →
      ∀ (g : (Ω ≃ₐ[k] Ω) → ZMod 2),
        (∀ x ∈ K.fixingSubgroup, ∀ z ∈ K.fixingSubgroup, g (x * z) = g x + g z) →
        SSGRoute.IsLocConstOn K.fixingSubgroup g →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ SSGRoute.IsSplitIn k Λ B →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0) →
        ∀ (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod 2),
          (∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
            ∀ z ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * z) = h A x + h A z) →
          (∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
            ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0) →
          (∀ A ∈ T, (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
            SSGRoute.IsSplitIn k Λ A) →
          (∀ A ∈ T, ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
            g σ + h A σ = 0) →
          (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → g c = 0) →
          (∀ A ∈ T, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → h A c = 0) →
          ∃ (b : (↥K)ˣ) (Q : ValuationSubring Ω),
            SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k Λ Q ∧
            (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A Q) ∧
            (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
              Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = g σ + h A σ) ∧
            (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
              Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b c = 0) ∧
            (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
              (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) →
              (¬ Work.SSGRoute.gesKConj K Q B) →
              ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
                Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b σ = 0)) :
    ∃ (Pset : Finset (ValuationSubring Ω)) (b : Fin 3 → (↥K)ˣ),
      (∀ P ∈ Pset, SSGRoute.IsFinPlace k P) ∧
      (∀ P ∈ Pset, SSGRoute.IsSplitIn k Λ P) ∧
      (∀ P ∈ Pset, ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A P) ∧
      (∀ i : Fin 3, ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (b i) σ = y σ) ∧
      (∀ i : Fin 3, ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 →
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (b i) c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        (∀ P ∈ Pset, ∀ τ : Ω ≃ₐ[k] Ω, τ ∈ K.fixingSubgroup → τ • P ≠ B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (b 0 * b 1 * b 2) σ = 0) ∧
      (∀ P ∈ Pset, ∀ B : ValuationSubring Ω, SSGRoute.IsConjPlace k P B →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • P = B) →
        ∀ u ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (b 0 * b 1 * b 2) u = 0) := by
  classical
  haveI hsepK : IsSepClosure ↥K Ω := ⟨IsSepClosure.sep_closed Ω, inferInstance⟩
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- the recursion of Schmidt--Wingberg's §4 (`p = 2`): escape primes `Q_m` with classes `b_m`
  obtain ⟨s, hs⟩ :=
    Work.SSGRoute.NodeS37.twoRecExists (K := K) (Λ := Λ) hKΛ ζ hζ hζK S hSfin hSram
      y hy hyc hyS hyT hyinf
  -- the paper's Claim (`χ_{b_m}` kills the local group of the `σ`-siblings of `Q_l`), in its
  -- three cases: `m < l` (the crossed two-place chain), `m = l` (the p. 16 computation) and
  -- `l < m` (the prescription of the rule).
  have hclaim : ∀ m l : ℕ, ∀ σ : Ω ≃ₐ[k] Ω, σ ∉ K.fixingSubgroup →
      (SSGRoute.res k K σ) ^ 2 = 1 →
      ∀ u ∈ SSGRoute.decomp k (σ • (s.f l).1) ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ (s.f m).2 u = 0 := by
    intro m l σ hσK hσ2 u hu
    rcases lt_trichotomy m l with hlt | heq | hgt
    · exact Work.SSGRoute.NodeS37.claimOfPreTwo_lt (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y hy hyT
        s hs m l hlt σ hσK hσ2 u hu
    · subst heq
      exact Work.SSGRoute.P2Close.claimOfPinnedZero (K := K) ζ hζ hζK (s.f m).2 (s.f m).1
        ((hs (m + 1)).1 m (Nat.lt_succ_self m))
        (Work.SSGRoute.NodeS35.isSplitIn_of_le (K := K) (N := Λ) hKΛ
          ((hs (m + 1)).2.1 m (Nat.lt_succ_self m)))
        (fun B hB hconj σ' hσ'K hσ'I =>
          Work.SSGRoute.NodeS37.claimOfPreTwoConfined.claimOfPreTwoConfined (K := K) (Λ := Λ)
            hKΛ ζ hζ hζK S y hy hyT s hs m B hB hconj σ' hσ'K hσ'I)
        (fun ρ hρ1 hρ2 =>
          Work.SSGRoute.ZDataTwo.mu2PinnedValueDiagonal (K := K) (Λ := Λ) hKΛ ζ hζ hζK S hSfin
            hSdisj hSram y hy hyc hyS hyT hy0 hyinf s hs m ρ hρ1 hρ2)
        σ hσK hσ2 u hu
    · exact Work.SSGRoute.NodeS37.claimOfPreTwo_gt (K := K) (Λ := Λ) hKΛ ζ hζ hζK S y s hs
        m l hgt σ hσK hσ2 u hu
  -- the verification: the minimal shoe-box triple and the two-place identities produce one good
  -- class `B = b_i b_j b_N`
  obtain ⟨Pset, B, hPfin, hPsplit, hPnotS, h1, h2, h3, h4⟩ :=
    Work.SSGRoute.NodeS37.goodClassOfHistory (K := K) (Λ := Λ) hKΛ ζ hζ hζK S hSfin hSdisj
      hSram y hy hyc hyS hyT hy0 hyinf s hs hclaim
  -- the global Kummer element of `y` (Kummer duality), and the three halves
  obtain ⟨b, hb⟩ :=
    Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst 2 k Ω K ζ hζK hζ y hy hyc
  refine Work.SSGRoute.NodeS37.threeHalvesConcl_of_goodClass K Λ ζ hζK hζ S Pset hPfin hPsplit
    hPnotS y hyinf b B ?_ h1 h2 h3 h4
  intro σ hσ
  rw [Work.SSGRoute.H9.CV2.nodeKummerCochar_eq_nodeKummerCocharZMod_two (K := K) ζ hζ hζK b σ]
  exact (hb σ hσ).symm

end Work.SSGRoute.ZDataTwo
