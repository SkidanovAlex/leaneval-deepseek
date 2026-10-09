import Mathlib
import Submission.Work.SSGRoute.PTembedding.kummer_ses_decomp
import Submission.Work.SSGRoute.PTembedding.hilbert90_decomp
import Submission.Work.AbsoluteKummer.SES.ker_mapH2_le_range_deltaH2
import Submission.Work.SSGRoute.range_mapH2_eq_ker_mapH2
import Submission.Work.SSGRoute.PT.AlphaTwoKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer step of the base case of local Tate duality

Milne, *Arithmetic Duality Theorems*, I.2.3 at `r = 0`, in the case `M = μ_p` (the "cyclotomic"
base case) asserts

  `Hom_{D_A}(μ_p, μ_p) = 𝔽_p ≅ H²(D_A, μ_p)^∨`,

i.e. `H²(D_A, μ_p) ≅ 𝔽_p` — the statement that the `p`-torsion of the local Brauer group `Br(k_v)`
is one-dimensional.  The *formal* half of it is the Kummer sequence

  `0 → μ_p → Ωˣ →^{p} Ωˣ → 0`

over `D_A = decomp k A` (`PTembedding.kummer_ses_decomp`) together with Hilbert 90
(`PTembedding.hilbert90_decompH1`): the connecting map `H¹(D_A, Ωˣ) → H²(D_A, μ_p)` is then zero,
so `H²(D_A, μ_p) → H²(D_A, Ωˣ)` is **injective**, and (by exactness at the middle) its image is the
kernel of multiplication by `p` on `H²(D_A, Ωˣ)`.  This file records the injectivity, which reduces
the base case to the arithmetic statement `H²(D_A, Ωˣ)[p] ≅ 𝔽_p`.

The general form below (`h2_map_iota_injective_of_subsingleton_H1`) is the standard consequence of
the exactness at `H²(M)` of the long exact sequence of a short exact sequence of discrete
`G`-modules: `ker (mapH2 ι) ≤ range (deltaH2)`, and `deltaH2` has subsingleton domain.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute.Nakayama

open Work.AbsoluteKummer

/-- **Injectivity of `H²(M) → H²(N)` in a short exact sequence `0 → M → N → P → 0` whose third
term has `H¹(G,P) = 0`.**  Then the connecting map `H¹(G,P) → H²(G,M)` vanishes, so by exactness at
`H²(G,M)` the map induced by the inclusion is injective (its image is the kernel of the map to
`H²(G,P)`, whence the Kummer identification `H²(G,M) ≅ ker (H²(G,N) → H²(G,P))`). -/
theorem h2_map_iota_injective_of_subsingleton_H1 {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : ShortExactSeq G M N P) (hP : Subsingleton (H1 G P)) :
    Function.Injective (mapH2 S.iota S.iota_equivariant) := by
  rw [← AddMonoidHom.ker_eq_bot_iff]
  refine le_antisymm ?_ bot_le
  refine le_trans (SES.ker_mapH2_le_range_deltaH2 S) ?_
  have hdelta : S.deltaH2 = 0 := by
    apply AddMonoidHom.ext
    intro x
    rw [hP.elim x 0]
    simp
  rw [hdelta, AddMonoidHom.range_zero]

/-- **The Kummer step of the base case of local Tate duality.**  There is a short exact sequence
`0 → μ_p → Ωˣ →^{p} Ωˣ → 0` over the decomposition group `D_A` of a finite place `A` (the Kummer
sequence) for which the map `H²(D_A, μ_p) → H²(D_A, Ωˣ)` is injective; by exactness this identifies
`H²(D_A, μ_p)` with the kernel of multiplication by `p` on `H²(D_A, Ωˣ)` (the `p`-torsion of the
local Brauer group). -/
theorem kummer_h2_muAdd_injective
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    ∃ S : ShortExactSeq ↥(SSGRoute.decomp k A) (PTembedding.MupCard.MuAdd p K)
        (Additive (Units Ω)) (Additive (Units Ω)),
      (∀ x : PTembedding.MupCard.MuAdd p K,
          S.iota x = PTembedding.MupCard.muIota (p := p) (K := K) x) ∧
      (∀ u : Additive (Units Ω), S.pi u = PTembedding.MupCard.powPi (p := p) (Ω := Ω) u) ∧
      Function.Injective (mapH2 S.iota S.iota_equivariant) := by
  obtain ⟨S, hiota, hpi⟩ :=
    PTembedding.MupCard.exists_kummerSES_decomp (p := p) (k := k) (Ω := Ω) (K := K) ζ hζ hζK A hA
  have hP : Subsingleton (H1 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) :=
    -- Hilbert 90 at the closed subgroup `D_A` (class-formation axiom 1.1a)
    ⟨fun a b => by
      rw [PTembedding.MupCard.hilbert90_decompH1 k Ω A hA a,
        PTembedding.MupCard.hilbert90_decompH1 k Ω A hA b]⟩
  exact ⟨S, hiota, hpi, h2_map_iota_injective_of_subsingleton_H1 S hP⟩

/-- **The Kummer reduction of the cyclotomic base case of local Tate duality.**  For the Kummer
sequence `0 → μ_p → Ωˣ →^{p} Ωˣ → 0` over `D_A`, the group `H²(D_A, μ_p)` is the kernel of the map
`H²(D_A, Ωˣ) → H²(D_A, Ωˣ)` induced by the `p`-th power map, i.e. the `p`-torsion of the local
Brauer group `Br(k_v) = H²(D_A, Ωˣ)`.  This reduces the base case `H²(D_A, μ_p) ≅ 𝔽_p` of local
Tate duality to the arithmetic statement `{x : H²(D_A, Ωˣ) // p • x = 0} ≅ 𝔽_p`. -/
theorem kummer_h2_muAdd_ker
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    ∃ S : ShortExactSeq ↥(SSGRoute.decomp k A) (PTembedding.MupCard.MuAdd p K)
        (Additive (Units Ω)) (Additive (Units Ω)),
      (∀ x : PTembedding.MupCard.MuAdd p K,
          S.iota x = PTembedding.MupCard.muIota (p := p) (K := K) x) ∧
      (∀ u : Additive (Units Ω), S.pi u = PTembedding.MupCard.powPi (p := p) (Ω := Ω) u) ∧
      Nonempty (H2 ↥(SSGRoute.decomp k A) (PTembedding.MupCard.MuAdd p K) ≃+
        (mapH2 S.pi S.pi_equivariant).ker) := by
  obtain ⟨S, hiota, hpi⟩ :=
    PTembedding.MupCard.exists_kummerSES_decomp (p := p) (k := k) (Ω := Ω) (K := K) ζ hζ hζK A hA
  have hP : Subsingleton (H1 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) :=
    ⟨fun a b => by
      rw [PTembedding.MupCard.hilbert90_decompH1 k Ω A hA a,
        PTembedding.MupCard.hilbert90_decompH1 k Ω A hA b]⟩
  have hinj := h2_map_iota_injective_of_subsingleton_H1 S hP
  have hrange : (mapH2 S.iota S.iota_equivariant).range =
      (mapH2 S.pi S.pi_equivariant).ker := Work.SSGRoute.range_mapH2_eq_ker_mapH2 S
  refine ⟨S, hiota, hpi, ?_⟩
  let F : H2 ↥(SSGRoute.decomp k A) (PTembedding.MupCard.MuAdd p K) →+
      ↥(mapH2 S.pi S.pi_equivariant).ker :=
    { toFun := fun x => ⟨mapH2 S.iota S.iota_equivariant x, by
        rw [← hrange]; exact AddMonoidHom.mem_range.mpr ⟨x, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  refine ⟨AddEquiv.ofBijective F ?_⟩
  refine ⟨fun x y hxy => hinj (Subtype.ext_iff.mp hxy), fun y => ?_⟩
  obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp (by rw [hrange]; exact y.2)
  exact ⟨x, Subtype.ext hx⟩

/-- **The Kummer step of the cyclotomic base case of local Tate duality, in final form.**
For the Kummer sequence `0 → μ_p → Ωˣ →^{p} Ωˣ → 0` over the decomposition group `D_A` of a finite
place, the group `H²(D_A, μ_p)` is the `p`-torsion subgroup of `H²(D_A, Ωˣ)` — the `p`-torsion of
the local Brauer group `Br(k_v) = ℚ/ℤ`:

  `H²(D_A, μ_p) ≅ (H²(D_A, Ωˣ))[p] = Work.SSGRoute.PT.PTor p (H²(D_A, Ωˣ))`.

The two inputs are Hilbert 90 at the closed subgroup `D_A`
(`PTembedding.MupCard.hilbert90_decompH1`, which makes the connecting map
`H¹(D_A, Ωˣ) → H²(D_A, μ_p)` vanish, hence `H²(D_A, μ_p) → H²(D_A, Ωˣ)` injective — the
`H²`-Hilbert 90 of `Work.SSGRoute.PT.ker_mapH2_eq_bot_of_subsingleton`) and the identification of
the image with the kernel of multiplication by `p`
(`Work.SSGRoute.PT.range_mapH2_eq_ker_nsmul`).  With the arithmetic statement
`Work.SSGRoute.Nakayama.br_pTorsion` (`Nat.card (H²(D_A,Ωˣ))[p] = p`) this yields
`H²(D_A, μ_p) ≅ 𝔽_p`, i.e. the `M = μ_p` instance of local Tate duality
`Hom_{D_A}(μ_p, μ_p) ≅ H²(D_A, μ_p)^∨`. -/
theorem kummer_h2_muAdd_pTorsion
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    ∃ S : ShortExactSeq ↥(SSGRoute.decomp k A) (PTembedding.MupCard.MuAdd p K)
        (Additive (Units Ω)) (Additive (Units Ω)),
      (∀ x : PTembedding.MupCard.MuAdd p K,
          S.iota x = PTembedding.MupCard.muIota (p := p) (K := K) x) ∧
      (∀ u : Additive (Units Ω), S.pi u = PTembedding.MupCard.powPi (p := p) (Ω := Ω) u) ∧
      Nonempty (H2 ↥(SSGRoute.decomp k A) (PTembedding.MupCard.MuAdd p K) ≃+
        Work.SSGRoute.PT.PTor p (H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))) := by
  obtain ⟨S, hiota, hpi⟩ :=
    PTembedding.MupCard.exists_kummerSES_decomp (p := p) (k := k) (Ω := Ω) (K := K) ζ hζ hζK A hA
  have hPi : ∀ u : Additive (Units Ω), S.pi u = p • u := by
    intro u
    rw [hpi u]
    exact PTembedding.MupCard.powPi_eq_nsmul u
  have hP : Subsingleton (H1 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) :=
    ⟨fun a b => by
      rw [PTembedding.MupCard.hilbert90_decompH1 k Ω A hA a,
        PTembedding.MupCard.hilbert90_decompH1 k Ω A hA b]⟩
  have hrange : (mapH2 S.iota S.iota_equivariant).range =
      (Work.SSGRoute.PT.nsmulHom p (H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))).ker :=
    Work.SSGRoute.PT.range_mapH2_eq_ker_nsmul p S hPi
  have hker : (mapH2 S.iota S.iota_equivariant).ker = ⊥ :=
    Work.SSGRoute.PT.ker_mapH2_eq_bot_of_subsingleton p S hP
  have hinj : Function.Injective (mapH2 S.iota S.iota_equivariant) := by
    rw [← AddMonoidHom.ker_eq_bot_iff]; exact hker
  refine ⟨S, hiota, hpi, ?_⟩
  let F : H2 ↥(SSGRoute.decomp k A) (PTembedding.MupCard.MuAdd p K) →+
      Work.SSGRoute.PT.PTor p (H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) :=
    { toFun := fun x => ⟨mapH2 S.iota S.iota_equivariant x, by
        have hmem : mapH2 S.iota S.iota_equivariant x ∈
            (Work.SSGRoute.PT.nsmulHom p (H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))).ker := by
          rw [← hrange]
          exact AddMonoidHom.mem_range.mpr ⟨x, rfl⟩
        simpa [AddMonoidHom.mem_ker] using hmem⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  refine ⟨AddEquiv.ofBijective F ?_⟩
  refine ⟨fun x y hxy => hinj (Subtype.ext_iff.mp hxy), fun y => ?_⟩
  have hy : y.1 ∈ (mapH2 S.iota S.iota_equivariant).range := by
    rw [hrange, AddMonoidHom.mem_ker, Work.SSGRoute.PT.nsmulHom_apply]
    exact (Work.SSGRoute.PT.mem_PTor).mp y.2
  obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp hy
  exact ⟨x, Subtype.ext hx⟩

end Work.SSGRoute.Nakayama
