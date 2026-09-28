import Mathlib
import Submission.Work.Cohomology.pd_hatcher_data

/-!
# The Hatcher decomposition, in the form used by the crux square

`Work.Cohomology.pd_hatcher_data` produces a cycle `w` representing `c` whose underlying chain is
a sum `a + b + d + j` of chains supported in `U∖L`, `U∩V`, `V∖K` and `(K∪L)ᶜ`.  For the crux
square (Hatcher's Lemma 3.36) one needs the decomposition in the form `α = α₁ + α₂ + α₃` together
with the *support of the boundaries*:

`dα₁` is supported in `Lᶜ` and `dα₃` is supported in `Kᶜ`.

Since the `j`-part lies in `(K∪L)ᶜ ⊆ Kᶜ`, one takes `α₁ := a`, `α₂ := b`, `α₃ := d + j`; then
`α₁ + α₂ + α₃ = a + b + d + j` is the cycle `w`, `dα₁ = da` is supported in `U∖L ⊆ Lᶜ`, and
`dα₃ = dd + dj` is supported in `(V∖K) ∪ (K∪L)ᶜ ⊆ Kᶜ`.

The only structural inputs are that `inclChains X S` is a chain map (so the boundary of a chain
supported in `S` is again supported in `S`) and that `inclChains X S` factors through
`inclChains X T` whenever `S ⊆ T`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **Monotonicity of the support of a chain in a subset**: a chain lying in the image of
`C_*(S) ⟶ C_*(M)` also lies in the image of `C_*(T) ⟶ C_*(M)` when `S ⊆ T`. -/
theorem mem_range_inclChains_of_subset {M : TopCat} {S T : Set M} (h : S ⊆ T) {n : ℕ}
    {x : (singularChains ℤ M).X n}
    (hx : x ∈ LinearMap.range ((inclChains M S).f n).hom) :
    x ∈ LinearMap.range ((inclChains M T).f n).hom := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(inclChainsSub M S T h).f n y, ?_⟩
  have hcomp : ((inclChainsSub M S T h).f n ≫ (inclChains M T).f n)
      = (inclChains M S).f n := by
    have h1 := congrArg (fun (φ : singularChains ℤ (TopCat.of S) ⟶ singularChains ℤ M) => φ.f n)
      (inclChainsSub_comp M S T h)
    rwa [HomologicalComplex.comp_f] at h1
  rw [← hcomp]
  rfl

/-- **The boundary of a chain supported in `S` is supported in `S`**: this is naturality of the
chain map `inclChains M S`. -/
theorem d_mem_range_inclChains {M : TopCat} {S : Set M} {n : ℕ} {x : (singularChains ℤ M).X n}
    (hx : x ∈ LinearMap.range ((inclChains M S).f n).hom) :
    (singularChains ℤ M).d n (n - 1) x ∈ LinearMap.range ((inclChains M S).f (n - 1)).hom := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(singularChains ℤ (TopCat.of S)).d n (n - 1) y, ?_⟩
  have h := congrArg
    (fun (g : (singularChains ℤ (TopCat.of S)).X n ⟶ (singularChains ℤ M).X (n - 1)) =>
      (ModuleCat.Hom.hom g) y) ((inclChains M S).comm n (n - 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-- **The Hatcher decomposition with the support of the boundaries.** -/
theorem pd_hatcher_decomp {M : TopCat} [T2Space M] {N : ℕ}
    (c : (singularChains ℤ M).homology N) {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    {K L : Set M} (hKc : IsCompact K) (hLc : IsCompact L) (hKU : K ⊆ U) (hLV : L ⊆ V) :
    ∃ (α : (singularChains ℤ M).cycles N) (α₁ α₂ α₃ : (singularChains ℤ M).X N),
      (HomologicalComplex.homologyπ (singularChains ℤ M) N α = c) ∧
      (singularChains ℤ M).iCycles N α = α₁ + α₂ + α₃ ∧
      (∃ a', (inclChains M (U \ L)).f N a' = α₁) ∧
      (∃ b', (inclChains M (U ∩ V)).f N b' = α₂) ∧
      (∃ e', (inclChains M Lᶜ).f (N - 1) e' = (singularChains ℤ M).d N (N - 1) α₁) ∧
      (∃ f', (inclChains M Kᶜ).f (N - 1) f' = (singularChains ℤ M).d N (N - 1) α₃) := by
  obtain ⟨w, hw, a, b, d, j, hsum, ⟨a', ha'⟩, ⟨b', hb'⟩, ⟨d', hd'⟩, ⟨j', hj'⟩⟩ :=
    pd_hatcher_data c hU hV hKc hLc hKU hLV
  refine ⟨w, a, b, d + j, hw, ?_, ⟨a', ha'⟩, ⟨b', hb'⟩, ?_, ?_⟩
  · rw [hsum]; ac_rfl
  · have ha : a ∈ LinearMap.range ((inclChains M (U \ L)).f N).hom := ⟨a', ha'⟩
    obtain ⟨e', he'⟩ := mem_range_inclChains_of_subset (M := M) (S := U \ L) (T := Lᶜ)
      (fun x hx => hx.2) (d_mem_range_inclChains ha)
    exact ⟨e', he'⟩
  · have hd1 : d ∈ LinearMap.range ((inclChains M (V \ K)).f N).hom := ⟨d', hd'⟩
    have hj1 : j ∈ LinearMap.range ((inclChains M ((K ∪ L)ᶜ)).f N).hom := ⟨j', hj'⟩
    have hdv : (singularChains ℤ M).d N (N - 1) d ∈
        LinearMap.range ((inclChains M Kᶜ).f (N - 1)).hom :=
      mem_range_inclChains_of_subset (fun x hx => hx.2) (d_mem_range_inclChains hd1)
    have hjk : (singularChains ℤ M).d N (N - 1) j ∈
        LinearMap.range ((inclChains M Kᶜ).f (N - 1)).hom :=
      mem_range_inclChains_of_subset (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_union] at hx ⊢
        exact fun h => hx (Or.inl h)) (d_mem_range_inclChains hj1)
    rw [map_add]
    exact add_mem hdv hjk

end

end Work.Cohomology
