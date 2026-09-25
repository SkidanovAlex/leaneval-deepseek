import Mathlib
import Submission.CFTLib.NKProps
import Submission.Work.CFT.ClassFormation.Defs
import Submission.Work.CFTLib.ClassGroupTransport.exists_classGroup_mulEquiv

/-!
# Vocabulary for the relative Shafarevich bound

The relative Shafarevich bound compares the inflation image
`H²(Gal(K/F), 𝔽_p) → H²(Gal(K'/F), 𝔽_p)` with `dim H¹(Gal(K'/F), 𝔽_p)` and `ρ = r₁+r₂−1+δ_p(F)`,
for `K ⊆ K'` finite Galois unramified `p`-extensions of `F` with `K'` containing every unramified
abelian `p`-extension of `K`.

The two invariant spaces that occur are

* `Work.CFTLib.clInvariantChar F K p` — the `G`-invariant characters `Cl(𝓞 K) → ℤ/p`,
  `G = Gal(K/F)`: their dimension is the `c` of the guidance.  The action of `G` on `Cl(𝓞 K)` is
  the canonical one induced by `NumberField.RingOfIntegers.mapAlgEquiv g` (`clEquiv`).
* `Work.CFTLib.invCharSubmodule p N` — the `G'`-invariant additive characters `N → 𝔽_p` of a
  normal subgroup `N ◁ G'` (with `G'` acting by conjugation).  Its dimension is
  `dim H¹(N, 𝔽_p)^{G'}`.
-/

open scoped Classical
open NumberField

noncomputable section

namespace Work.CFTLib

/-- The automorphism `Cl(𝓞 K) ≃* Cl(𝓞 K)` induced by `g : K ≃ₐ[F] K`.  This is the canonical
action of `Gal(K/F)` on the class group of `K`. -/
noncomputable def clEquiv (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (g : K ≃ₐ[F] K) : ClassGroup (𝓞 K) ≃* ClassGroup (𝓞 K) :=
  ClassGroup.mulEquiv (NumberField.RingOfIntegers.mapAlgEquiv g).toRingEquiv

/-- **The `G`-invariant characters of the class group.**  For `G = Gal(K/F)`, this is the
`𝔽_p`-subspace of `Hom(Cl(𝓞 K), ℤ/p)` consisting of the characters fixed by the canonical
`G`-action `clEquiv`.  Its dimension is the `c` of the relative Shafarevich bound. -/
noncomputable def clInvariantChar (F K : Type) [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] (p : ℕ) :
    Submodule (ZMod p) (AddMonoidHom (Additive (ClassGroup (𝓞 K))) (ZMod p)) where
  carrier := {χ | ∀ (g : K ≃ₐ[F] K) (c : ClassGroup (𝓞 K)),
    χ (Additive.ofMul (clEquiv F K g c)) = χ (Additive.ofMul c)}
  zero_mem' := by intro g c; simp
  add_mem' := by
    intro χ ψ hχ hψ g c
    simp only [Set.mem_ofPred_eq] at hχ hψ ⊢
    rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, hχ g c, hψ g c]
  smul_mem' := by
    intro a χ hχ g c
    simp only [Set.mem_ofPred_eq] at hχ ⊢
    rw [AddMonoidHom.smul_apply, AddMonoidHom.smul_apply, hχ g c]

/-- **The `G'`-invariant additive characters of a normal subgroup `N ◁ G'`**, with `G'` acting
on `N` by conjugation.  Its dimension is `dim H¹(N, 𝔽_p)^{G'}`. -/
noncomputable def invCharSubmodule (p : ℕ) {G' : Type*} [Group G'] (N : Subgroup G')
    [N.Normal] :
    Submodule (ZMod p) (AddMonoidHom (Additive N) (ZMod p)) where
  carrier := {χ | ∀ (g : G') (n : N),
    χ (Additive.ofMul (⟨g⁻¹ * n.1 * g, Subgroup.Normal.conj_mem' ‹N.Normal› n.1 n.2 g⟩ : N))
      = χ (Additive.ofMul n)}
  zero_mem' := by intro g n; simp
  add_mem' := by
    intro χ ψ hχ hψ g n
    simp only [Set.mem_ofPred_eq] at hχ hψ ⊢
    rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, hχ g n, hψ g n]
  smul_mem' := by
    intro a χ hχ g n
    simp only [Set.mem_ofPred_eq] at hχ ⊢
    rw [AddMonoidHom.smul_apply, AddMonoidHom.smul_apply, hχ g n]

end Work.CFTLib
