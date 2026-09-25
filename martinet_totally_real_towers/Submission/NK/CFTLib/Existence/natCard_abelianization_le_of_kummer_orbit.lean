import Mathlib
import Submission.NK.CFTLib.Existence.KummerCountNotes
import Submission.NK.CFTLib.Existence.natCard_kummerFixed_le_prime

set_option linter.style.haveILetI false

open scoped IsMulCommutative

namespace NK.CFTLib.Existence

/-- If a `K'`-algebra automorphism `u` of `N` commutes with `σN` and fixes `β₀`, then it
fixes every element of the `K'`-orbit of `β₀` under `σN`, hence — if that orbit generates
`N` over `K'` — it is the identity. -/
theorem eq_one_of_fixes_kummer_orbit
    {K K' N : Type*} [Field K] [Field K'] [Field N]
    [Algebra K K'] [Algebra K' N] [Algebra K N] [IsScalarTower K K' N]
    (σN : N ≃ₐ[K] N) (β₀ : N)
    (hgen : IntermediateField.adjoin K' (Set.range fun i : ℕ => ((σN : N → N)^[i]) β₀) = ⊤)
    (u : N ≃ₐ[K'] N) (hcomm : ∀ x, u (σN x) = σN (u x)) (hb : u β₀ = β₀) :
    u = 1 := by
  have horbit : ∀ i : ℕ, u (((σN : N → N)^[i]) β₀) = ((σN : N → N)^[i]) β₀ := by
    intro i
    induction i with
    | zero => simpa using hb
    | succ i ih => rw [Function.iterate_succ_apply', hcomm, ih]
  have htop : (⊤ : IntermediateField K' N) ≤ IntermediateField.fixedField (Subgroup.zpowers u) := by
    rw [← hgen, IntermediateField.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    show ((σN : N → N)^[i]) β₀ ∈ IntermediateField.fixedField (Subgroup.zpowers u)
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have hstab : Subgroup.zpowers u ≤
        MulAction.stabilizer (N ≃ₐ[K'] N) (((σN : N → N)^[i]) β₀) :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (horbit i))
    exact MulAction.mem_stabilizer_iff.mp (hstab hf)
  have h : Subgroup.zpowers u ≤ (⊥ : Subgroup (N ≃ₐ[K'] N)) := by
    have := (IntermediateField.le_iff_le (Subgroup.zpowers u) ⊤).mp htop
    rwa [IntermediateField.fixingSubgroup_top] at this
  simpa using h (Subgroup.mem_zpowers u)

/-- Group-theoretic assembly: if `H ≤ G` with `[G,G] ≤ H`, `[G:H] = d`, and `H` admits an
endomorphism `δ` with range inside `[G,G]` and kernel of cardinality at most `p`, then the
abelianisation of `G` has at most `p * d` elements. -/
theorem natCard_abelianization_le_of_index_range
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) (p d : ℕ)
    (hH : commutator G ≤ H) (hidx : H.index = d)
    (hδ : ∃ δ : ↥H →* ↥H, Subgroup.map H.subtype δ.range ≤ commutator G ∧
      Nat.card ↥δ.ker ≤ p) :
    Nat.card (Abelianization G) ≤ p * d := by
  obtain ⟨δ, hrange, hker⟩ := hδ
  haveI : Finite ↥H := Finite.of_injective H.subtype Subtype.coe_injective
  haveI : δ.range.FiniteIndex := inferInstance
  haveI : δ.ker.FiniteIndex := inferInstance
  have hle : δ.range ≤ (commutator G).subgroupOf H := (Subgroup.map_le_iff_le_comap).mp hrange
  have hmain : (commutator G).relIndex H ≤ p :=
    calc (commutator G).relIndex H = ((commutator G).subgroupOf H).index := rfl
      _ ≤ δ.range.index := Subgroup.index_antitone hle
      _ = Nat.card ↥δ.ker := Subgroup.index_range
      _ ≤ p := hker
  calc Nat.card (Abelianization G) = (commutator G).index := rfl
    _ = (commutator G).relIndex H * H.index := (Subgroup.relIndex_mul_index hH).symm
    _ = (commutator G).relIndex H * d := by rw [hidx]
    _ ≤ p * d := Nat.mul_le_mul_right d hmain

theorem natCard_abelianization_le_of_kummer_orbit
    {K K' N : Type*} [Field K] [Field K'] [Field N]
    [Algebra K K'] [Algebra K' N] [Algebra K N] [IsScalarTower K K' N]
    [FiniteDimensional K K'] [FiniteDimensional K N] [FiniteDimensional K' N]
    [IsGalois K K'] [IsGalois K N] [IsGalois K' N]
    [IsMulCommutative (K' ≃ₐ[K] K')] [IsMulCommutative (N ≃ₐ[K'] N)]
    (p : ℕ) [Fact p.Prime] {ζ : K'} (hζ : IsPrimitiveRoot ζ p)
    (σ : K' ≃ₐ[K] K') (hσ : ∀ τ : K' ≃ₐ[K] K', ∃ n : ℕ, τ = σ ^ n)
    (σN : N ≃ₐ[K] N) (hσN : ∀ x : K', σN (algebraMap K' N x) = algebraMap K' N (σ x))
    (a : K'ˣ) (β₀ : N) (hβ₀ : β₀ ^ p = algebraMap K' N (a : K'))
    (hgen : IntermediateField.adjoin K' (Set.range fun i : ℕ => ((σN : N → N)^[i]) β₀) = ⊤) :
    Nat.card (Abelianization (N ≃ₐ[K] N)) ≤ p * Module.finrank K K' := by
  haveI : Normal K K' := IsGalois.to_normal
  haveI : Finite (N ≃ₐ[K] N) := by
    have h : Nat.card (N ≃ₐ[K] N) ≠ 0 := by
      rw [IsGalois.card_aut_eq_finrank K N]
      exact (Module.finrank_pos (R := K) (M := N)).ne'
    exact (Nat.card_ne_zero.mp h).2
  let ρ : (N ≃ₐ[K] N) →* (K' ≃ₐ[K] K') := AlgEquiv.restrictNormalHom (F := K) (K₁ := N) K'
  -- the commutator subgroup is contained in `ker ρ`, since `Gal(K'/K)` is commutative
  have hC_le_H : commutator (N ≃ₐ[K] N) ≤ ρ.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro x ⟨g, h, rfl⟩
    refine MonoidHom.mem_ker.mpr ?_
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (‹IsMulCommutative (K' ≃ₐ[K] K')›).is_comm.comm (ρ g) (ρ h)
  -- membership in `ker ρ` means fixing `K'` pointwise
  have hmem_iff : ∀ g : N ≃ₐ[K] N, g ∈ ρ.ker ↔
      ∀ c : K', g (algebraMap K' N c) = algebraMap K' N c := by
    intro g
    have hg : ρ g = g.restrictNormal K' := rfl
    rw [MonoidHom.mem_ker, hg]
    constructor
    · intro h c
      have hc : (g.restrictNormal K') c = c := by rw [h]; rfl
      have h2 := AlgEquiv.restrictNormal_commutes (F := K) (K₁ := N) (K₂ := N) g K' c
      rw [hc] at h2
      exact h2.symm
    · intro h
      ext c
      have h2 := AlgEquiv.restrictNormal_commutes (F := K) (K₁ := N) (K₂ := N) g K' c
      rw [h c] at h2
      exact (algebraMap K' N).injective h2
  -- `ker ρ` is the range of the restriction-of-scalars map, hence commutative
  have hker : ρ.ker = (AlgEquiv.restrictScalarsHom K (S := K') (A := N)).range := by
    ext σ
    constructor
    · intro hσ
      rw [MonoidHom.mem_range]
      refine ⟨{ σ with commutes' := ?_ }, ?_⟩
      · intro c; exact (hmem_iff σ).mp hσ c
      · ext x; rfl
    · intro hσ
      rw [hmem_iff]
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hσ
      intro c
      show g (algebraMap K' N c) = algebraMap K' N c
      exact g.commutes c
  have hHcomm : ∀ a b : ↥ρ.ker, a * b = b * a := fun a b => by
    have ha : (a : N ≃ₐ[K] N) ∈ (AlgEquiv.restrictScalarsHom K (S := K') (A := N)).range := by
      rw [← hker]; exact a.2
    have hb : (b : N ≃ₐ[K] N) ∈ (AlgEquiv.restrictScalarsHom K (S := K') (A := N)).range := by
      rw [← hker]; exact b.2
    obtain ⟨a', ha'⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨b', hb'⟩ := MonoidHom.mem_range.mp hb
    refine Subtype.ext ?_
    show (a : N ≃ₐ[K] N) * (b : N ≃ₐ[K] N) = (b : N ≃ₐ[K] N) * (a : N ≃ₐ[K] N)
    rw [← ha', ← hb', ← map_mul, ← map_mul]
    exact congrArg _ ((‹IsMulCommutative (N ≃ₐ[K'] N)›).is_comm.comm a' b')
  haveI : IsMulCommutative ↥ρ.ker := isMulCommutative_iff.mpr hHcomm
  -- the index of the kernel
  have hHidx : ρ.ker.index = Module.finrank K K' := by
    rw [Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := K') N),
      Subgroup.card_top, IsGalois.card_aut_eq_finrank]
  -- conjugation by `σN` preserves `ker ρ`, and `δ := g ↦ σN g σN⁻¹ g⁻¹` is an endomorphism
  have hconj_mem : ∀ g : ↥ρ.ker, σN * (g : N ≃ₐ[K] N) * σN⁻¹ ∈ ρ.ker :=
    fun g => (MonoidHom.normal_ker ρ).conj_mem (g : N ≃ₐ[K] N) g.2 σN
  let conjH : ↥ρ.ker →* ↥ρ.ker :=
    ((MulAut.conj σN : (N ≃ₐ[K] N) →* (N ≃ₐ[K] N)).comp ρ.ker.subtype).codRestrict ρ.ker hconj_mem
  have hconjH_coe : ∀ y : ↥ρ.ker,
      ((conjH y : ↥ρ.ker) : N ≃ₐ[K] N) = σN * (y : N ≃ₐ[K] N) * σN⁻¹ := by
    intro y
    change (MulAut.conj σN) ((y : ↥ρ.ker) : N ≃ₐ[K] N) = σN * (y : N ≃ₐ[K] N) * σN⁻¹
    rw [MulAut.conj_apply]
  let δ : ↥ρ.ker →* ↥ρ.ker := MonoidHom.mk' (fun y => conjH y * y⁻¹) (by
    intro a b
    show conjH (a * b) * (a * b)⁻¹ = (conjH a * a⁻¹) * (conjH b * b⁻¹)
    rw [map_mul, mul_inv_rev]
    ac_rfl)
  have hδco : ∀ y : ↥ρ.ker, ((δ y : ↥ρ.ker) : N ≃ₐ[K] N) =
      σN * (y : N ≃ₐ[K] N) * σN⁻¹ * (y : N ≃ₐ[K] N)⁻¹ := by
    intro y
    simp [δ, MonoidHom.mk'_apply, hconjH_coe]
  have hker_iff : ∀ y : ↥ρ.ker, y ∈ δ.ker ↔
      σN * (y : N ≃ₐ[K] N) * σN⁻¹ = (y : N ≃ₐ[K] N) := by
    intro y
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h2 : conjH y = y := by
        have h3 := congrArg (fun z : ↥ρ.ker => z * y) h
        simpa [δ, MonoidHom.mk'_apply, mul_assoc] using h3
      have h4 := congrArg (fun z : ↥ρ.ker => (z : N ≃ₐ[K] N)) h2
      rwa [hconjH_coe y] at h4
    · intro h
      have h2 : conjH y = y := by
        refine Subtype.ext ?_
        rw [hconjH_coe y, h]
      have h3 : conjH y * y⁻¹ = 1 := by rw [h2, mul_inv_cancel]
      simpa [δ, MonoidHom.mk'_apply] using h3
  have hδmem : ∀ g : ↥ρ.ker,
      ((δ g : ↥ρ.ker) : N ≃ₐ[K] N) ∈ commutator (N ≃ₐ[K] N) := by
    intro g
    rw [hδco g, commutator_eq_closure]
    exact Subgroup.subset_closure (commutator_mem_commutatorSet σN (g : N ≃ₐ[K] N))
  have hrange : Subgroup.map ρ.ker.subtype δ.range ≤ commutator (N ≃ₐ[K] N) := by
    apply (Subgroup.map_le_iff_le_comap).mpr
    rintro y ⟨g, rfl⟩
    exact hδmem g
  -- the kernel of `δ` is the Kummer fixed set, of cardinality at most `p`
  have hcard : Nat.card ↥δ.ker ≤ p := by
    rw [Nat.card_congr (show ↥δ.ker ≃ {g : N ≃ₐ[K] N //
        (∀ c : K', g (algebraMap K' N c) = algebraMap K' N c) ∧ σN * g * σN⁻¹ = g} from
      { toFun := fun y => ⟨(y : ↥ρ.ker), (hmem_iff _).mp (y : ↥ρ.ker).2,
          (hker_iff (y : ↥ρ.ker)).mp y.2⟩
        invFun := fun x => ⟨⟨x.1, (hmem_iff x.1).mpr x.2.1⟩, (hker_iff _).mpr x.2.2⟩
        left_inv := fun y => by ext; rfl
        right_inv := fun x => by ext; rfl })]
    exact natCard_kummerFixed_le_prime p σN β₀ a hβ₀ hgen
  exact natCard_abelianization_le_of_index_range ρ.ker p (Module.finrank K K') hC_le_H hHidx
    ⟨δ, hrange, hcard⟩

end NK.CFTLib.Existence
