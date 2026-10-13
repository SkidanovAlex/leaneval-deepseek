import Mathlib
import Submission.Work.DSM5b.HCF.Complex
import Submission.Work.DSM5b.HCF.sizeExact

namespace Work.DSM5b

universe u

namespace CoeffSys.Hom

variable {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]

/-- A morphism of coefficient systems that is termwise injective induces an injective map on the
sorted (increasing tuple) complexes.  Everything is termwise: the `τ`-component of `stcMap φ m z`
is `φ.φ (tupRng τ.1) (z τ)`. -/
lemma stcMap_injective {𝒜 ℬ : CoeffSys R ι} (φ : CoeffSys.Hom 𝒜 ℬ)
    (hφ : ∀ S, Function.Injective (φ.φ S)) (m : ℕ) :
    Function.Injective (stcMap φ m) := by
  intro z z' h
  funext τ
  exact hφ _ (congr_fun h τ)

/-- A morphism of coefficient systems that is termwise surjective induces a surjective map on the
sorted complexes (a preimage is built pointwise by choice). -/
lemma stcMap_surjective {𝒜 ℬ : CoeffSys R ι} (φ : CoeffSys.Hom 𝒜 ℬ)
    (hφ : ∀ S, Function.Surjective (φ.φ S)) (m : ℕ) :
    Function.Surjective (stcMap φ m) := by
  intro x
  choose y hy using fun τ => hφ (tupRng τ.1) (x τ)
  exact ⟨y, funext hy⟩

/-- If two composable morphisms of coefficient systems are termwise exact
(`ker (ψ.φ S) = range (φ.φ S)` for every `S`), then they are exact on the sorted complexes. -/
lemma stcMap_ker_range {𝒜 ℬ 𝒞 : CoeffSys R ι} (φ : CoeffSys.Hom 𝒜 ℬ) (ψ : CoeffSys.Hom ℬ 𝒞)
    (h : ∀ S, LinearMap.ker (ψ.φ S) = LinearMap.range (φ.φ S)) (m : ℕ) :
    LinearMap.ker (stcMap ψ m) = LinearMap.range (stcMap φ m) := by
  ext z
  constructor
  · intro hz
    rw [LinearMap.mem_ker] at hz
    rw [LinearMap.mem_range]
    have hmem : ∀ τ : IncrTuple m, ∃ y, φ.φ (tupRng τ.1) y = z τ := by
      intro τ
      have hzτ : ψ.φ (tupRng τ.1) (z τ) = 0 := congr_fun hz τ
      have : z τ ∈ LinearMap.ker (ψ.φ (tupRng τ.1)) := LinearMap.mem_ker.mpr hzτ
      rw [h (tupRng τ.1)] at this
      exact LinearMap.mem_range.mp this
    choose y hy using hmem
    exact ⟨y, funext hy⟩
  · intro hz
    rw [LinearMap.mem_range] at hz
    obtain ⟨w, rfl⟩ := hz
    rw [LinearMap.mem_ker]
    funext τ
    have : φ.φ (tupRng τ.1) (w τ) ∈ LinearMap.range (φ.φ (tupRng τ.1)) :=
      LinearMap.mem_range.mpr ⟨w τ, rfl⟩
    rw [← h (tupRng τ.1)] at this
    exact LinearMap.mem_ker.mp this

end CoeffSys.Hom

end Work.DSM5b

namespace Work.DSM5b.HCF

universe u

/-- **Exactness of the size filtration on the sorted complex.**  For a coefficient system `𝒜` over a
commutative ring `R`, a linearly ordered index type `ι`, and `k m : ℕ`, the maps induced by the
inclusion and the quotient map of the size filtration on the sorted (increasing tuple) complex
form the exact sequence

  `0 → Stc (𝒜_{≥k+1}) m → Stc (𝒜_{≥k}) m → Stc (𝒜_{=k}) m → 0`:

`stcMap (subInclHom 𝒜 k) m` is injective, `stcMap (subQuotHom 𝒜 k) m` is surjective, and the kernel
of the latter is the range of the former.  All three statements are termwise over the increasing
tuples `τ`, reducing to the termwise exactness of `0 → ↥(N_{k+1} S) → ↥(N_k S) → ↥(N_k S)/image → 0`
(`Submodule.inclusion_injective`, `Submodule.mkQ_surjective`, `Submodule.ker_mkQ`). -/
theorem stcExact {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    (𝒜 : Work.DSM5b.CoeffSys R ι) (k m : ℕ) :
    Function.Injective (Work.DSM5b.CoeffSys.Hom.stcMap (Work.DSM5b.CoeffSys.subInclHom 𝒜 k) m) ∧
      Function.Surjective (Work.DSM5b.CoeffSys.Hom.stcMap (Work.DSM5b.CoeffSys.subQuotHom 𝒜 k) m) ∧
      LinearMap.ker (Work.DSM5b.CoeffSys.Hom.stcMap (Work.DSM5b.CoeffSys.subQuotHom 𝒜 k) m) =
        LinearMap.range (Work.DSM5b.CoeffSys.Hom.stcMap (Work.DSM5b.CoeffSys.subInclHom 𝒜 k) m) := by
  refine ⟨Work.DSM5b.CoeffSys.Hom.stcMap_injective (Work.DSM5b.CoeffSys.subInclHom 𝒜 k)
            (fun S => Submodule.inclusion_injective
              (Work.DSM5b.CoeffSys.sizeSubSys_mono 𝒜 k S)) m,
          Work.DSM5b.CoeffSys.Hom.stcMap_surjective (Work.DSM5b.CoeffSys.subQuotHom 𝒜 k)
            (fun S => Submodule.mkQ_surjective _) m, ?_⟩
  exact Work.DSM5b.CoeffSys.Hom.stcMap_ker_range (Work.DSM5b.CoeffSys.subInclHom 𝒜 k)
    (Work.DSM5b.CoeffSys.subQuotHom 𝒜 k) (fun S => Submodule.ker_mkQ _) m

end Work.DSM5b.HCF
