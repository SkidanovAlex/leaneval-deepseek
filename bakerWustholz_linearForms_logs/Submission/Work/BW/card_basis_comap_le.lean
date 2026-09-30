import Mathlib
import Submission.Work.BW.coordVecLin_defs
import Submission.Work.BW.finrank_ker_mulVecLin_fin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `ℤ`-rank of the pullback of the kernel lattice

Let `F` be a number field, `d = [F : ℚ]`, and let `a : Fin M → Fin N → F` be a matrix with
`F`-linearly independent rows.  The kernel lattice `kerLattice a` lives in the mixed coordinate
space `CoordSpace F N = ℝ^{d·N}`, and its pullback along the coordinate map
`coordVecLin : (Fin N → 𝓞 F) →ₗ[ℤ] CoordSpace F N` -- which is, as a set, the set
`kerVecs a` of integral kernel vectors of `a` (see `mem_comap_coordVecLin_iff`) -- is a free
`ℤ`-module whose rank is at most `d · (N - M)`.

Indeed, the spanning set `b` of the pullback gives, via the pointwise coercion to `F`, a family of
`ℚ`-linearly independent vectors of `F^N` (a `ℤ`-basis is `ℤ`-independent, and linear independence
over `ℤ` implies linear independence over `ℚ` by `LinearIndependent.iff_fractionRing`) which lies in
the `F`-kernel `ker (a ·)` of `a`, of `ℚ`-dimension `d · (N - M)` by rank-nullity
(`finrank_ker_mulVecLin_fin` and `Module.finrank_mul_finrank`).

Consequently any `ℤ`-basis of the pullback -- for instance the one produced by
`exists_zbasis_kerLattice` -- has at most `d · (N - M)` elements.
-/

namespace Work.BW

open NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- The pointwise `ℤ`-linear map `x ↦ (fun j => (x j : F))` from integral vectors to `F`-vectors. -/
noncomputable def toF {N : ℕ} : (Fin N → RingOfIntegers F) →ₗ[ℤ] (Fin N → F) where
  toFun x := fun j => (x j : F)
  map_add' x y := by funext j; simp
  map_smul' n x := by funext j; simp

omit [NumberField F] in
lemma toF_injective {N : ℕ} : Function.Injective (toF (F := F) (N := N)) := by
  intro x y h
  funext j
  exact Subtype.ext (congrFun h j)

/-- The pullback `(kerLattice a).comap coordVecLin` is a free `ℤ`-module of rank at most
`[F : ℚ] · (N - M)`: any of its `ℤ`-bases has at most `[F : ℚ] · (N - M)` elements. -/
theorem card_basis_comap_le {F : Type*} [Field F] [NumberField F] {M N k : ℕ}
    (a : Fin M → Fin N → F) (hind : LinearIndependent F a)
    (b : Module.Basis (Fin k) ℤ ↥((Work.BW.kerLattice (F := F) a).comap
      (Work.BW.coordVecLin (F := F)))) :
    k ≤ Module.finrank ℚ F * (N - M) := by
  classical
  set Lp := (kerLattice (F := F) a).comap (coordVecLin (F := F)) with hLp
  -- The family `ψ ∘ b` of `F`-vectors underlying the basis.
  let ψ : ↥Lp →ₗ[ℤ] (Fin N → F) := (toF (F := F) (N := N)).comp (Submodule.subtype Lp)
  have hψinj : Function.Injective ψ := by
    intro x y h
    exact Subtype.ext (toF_injective h)
  -- A `ℤ`-basis is `ℤ`-independent, and `ℤ`-independence over a `ℚ`-module is `ℚ`-independence.
  have hZ : LinearIndependent ℤ (ψ ∘ ⇑b) :=
    b.linearIndependent.map' ψ (LinearMap.ker_eq_bot.mpr hψinj)
  have hQ : LinearIndependent ℚ (ψ ∘ ⇑b) :=
    (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).mp hZ
  -- The `F`-kernel of `a`.
  set K : Submodule F (Fin N → F) := LinearMap.ker ((Matrix.of a).mulVecLin) with hK
  -- Its elements are kernel vectors of `a`.
  have hmem : ∀ i, (ψ ∘ ⇑b) i ∈ K.restrictScalars ℚ := by
    intro i
    have hx : ((b i : ↥Lp) : Fin N → RingOfIntegers F) ∈ kerVecs (F := F) a :=
      (mem_comap_coordVecLin_iff (F := F) a _).mp (b i).2
    have hy : ∀ i', ∑ j, a i' j * ((ψ ∘ ⇑b) i) j = 0 := by
      intro i'
      simpa [ψ, toF, LinearMap.comp_apply] using hx i'
    show (Matrix.of a).mulVecLin ((ψ ∘ ⇑b) i) = 0
    funext i'
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.of_apply, Pi.zero_apply, dotProduct]
    rw [hy i']
  -- The `ℚ`-span of the family lies in the kernel, and has exactly `k` dimensions.
  have hspan_le : Submodule.span ℚ (Set.range (ψ ∘ ⇑b)) ≤ K.restrictScalars ℚ :=
    Submodule.span_le.mpr (fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      exact hmem i)
  have hcard : Module.finrank ℚ ↥(Submodule.span ℚ (Set.range (ψ ∘ ⇑b))) = k := by
    rw [finrank_span_eq_card hQ, Fintype.card_fin]
  have hfinK : Module.Finite ℚ ↥(K.restrictScalars ℚ) :=
    FiniteDimensional.finiteDimensional_submodule (K.restrictScalars ℚ)
  have hmono : Module.finrank ℚ ↥(Submodule.span ℚ (Set.range (ψ ∘ ⇑b))) ≤
      Module.finrank ℚ ↥(K.restrictScalars ℚ) := Submodule.finrank_mono hspan_le
  -- Rank-nullity over `F`, then base change to `ℚ`.
  have hKdim : Module.finrank ℚ ↥(K.restrictScalars ℚ) = Module.finrank ℚ F * (N - M) := by
    have hfin : Module.finrank F ↥K = N - M := by
      rw [hK]; exact finrank_ker_mulVecLin_fin a hind
    have h := Module.finrank_mul_finrank ℚ F ↥K
    rw [hfin] at h
    exact h.symm
  exact le_trans (le_of_eq hcard.symm) (le_trans hmono (le_of_eq hKdim))

end Work.BW
