import Mathlib
import Submission.Work.ORP311.LuckDim
import Submission.Work.ORP311.mem_ell2Sub_iff

namespace Work.ORP311

/-- **The window subspaces form a meet-semilattice of `ℓ²(HSum n)`.**

`ell2Sub n Z` is the closed span of the Hilbert-basis vectors `e_i ⊗ δ_g` with `g ∈ Z`, and
`Work.ORP311.mem_ell2Sub_iff` identifies its elements as those vectors all of whose `δ_g`-components
with `g ∉ Z` vanish.  Consequently membership in `ell2Sub n Z ⊓ ell2Sub n W` says exactly that
the `δ_g`-components vanish for `g ∉ Z` *and* for `g ∉ W`, and since `g ∉ Z ∩ W` is equivalent to
`g ∉ Z ∨ g ∉ W`, this is membership in `ell2Sub n (Z ∩ W)`. -/
theorem ell2Sub_inf {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (Z W : Set G) : Work.ORP311.ell2Sub (G := G) n Z ⊓ Work.ORP311.ell2Sub (G := G) n W = Work.ORP311.ell2Sub (G := G) n (Z ∩ W) := by
  ext x
  rw [Submodule.mem_inf, mem_ell2Sub_iff, mem_ell2Sub_iff, mem_ell2Sub_iff]
  constructor
  · rintro ⟨hZ, hW⟩ g hg i
    by_cases h : g ∈ Z
    · exact hW g (fun hW' => hg ⟨h, hW'⟩) i
    · exact hZ g h i
  · rintro h
    exact ⟨fun g hg i => h g (fun hZW => hg hZW.1) i,
      fun g hg i => h g (fun hZW => hg hZW.2) i⟩

end Work.ORP311
