/-
# The flatness theorem of Jaikin-Zapirain--Linton, Theorem 5.6 (single two-cell case)

Abstract form of the crux of the proof of JL, Theorem 5.6, in the single two-cell case
(their §5.3, the "Magnus subgroup" form).  The data are:
* a short exact sequence `0 → A → B → C → 0` of right `K[G]`-modules — this is their
  Claim 5.10, the two-term Lyndon sequence;
* for every right `K[G]`-module `L`, the test module `S ⊗[K] L` (the diagonal module of
  `Submission.Work.ORFlatness.Diagonal`, playing the role of `D_{K[G]} ⊗_K L*`), with
  `Tor₁^{K[G]}(B, S ⊗ L) = 0` (their Claim 5.8, flatness of the Magnus part) and
  `A ⊗ (S ⊗ L) → B ⊗ (S ⊗ L)` injective (their Lemma 5.1, i.e. the torsion-freeness
  coming from Claim 5.9 = Weinbaum, together with `char K ∤ l`);
* the duality of `Tor₁` for the diagonal module (their Lemma 5.2).

`tor1Vanishes_diagonal_jl` is verbatim the intermediate conclusion of their proof;
`leftFlat_diagonal_jl` is the final flatness statement, obtained from it by the flatness
criterion `Work.ORFlatness.leftFlat_iff_forall_tor1Vanishes` (which is their Lemma 5.2
turned into a criterion, in the strengthened form where the test modules are all right
`K[G]`-modules).
-/
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.FlatCrit
import Submission.Work.ORFlatness.Diagonal
import Submission.Work.ORFlatness.tor1Vanishes_of_shortExact

set_option autoImplicit false

open TensorProduct MulOpposite

universe u

namespace Work.ORFlatness

variable (K : Type u) [CommRing K] (G : Type u) [Group G]
variable (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)

/-- **Jaikin-Zapirain--Linton, Theorem 5.6 (single two-cell case), intermediate step.**
For every right `K[G]`-module `L`: if `Tor₁^{K[G]}(B, S ⊗[K] L) = 0` (Claim 5.8) and the
map `A ⊗ (S ⊗[K] L) → B ⊗ (S ⊗[K] L)` is injective (Lemma 5.1 + Claim 5.9 + `char K ∤ l`),
then `Tor₁^{K[G]}(C, S ⊗[K] L) = 0`.  This is the dimension-shifting step of their proof
of Theorem 5.6. -/
theorem tor1Vanishes_diagonal_jl
    {A B C : Type u} [AddCommGroup A] [Module (MonoidAlgebra K G)ᵐᵒᵖ A]
    [AddCommGroup B] [Module (MonoidAlgebra K G)ᵐᵒᵖ B]
    [AddCommGroup C] [Module (MonoidAlgebra K G)ᵐᵒᵖ C]
    (f : A →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] B) (g : B →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] C)
    (hg : Function.Surjective g) (hfg : f.range = g.ker)
    (L : Type u) [AddCommGroup L] [Module K L] [Module (MonoidAlgebra K G)ᵐᵒᵖ L]
    [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ L]
    [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ L]
    (hB : letI := diagModule K G S φ L
      Tor1Vanishes (MonoidAlgebra K G) B (S ⊗[K] L))
    (hA : letI := diagModule K G S φ L
      Function.Injective (BalTensor.map (MonoidAlgebra K G) f
        (LinearMap.id : (S ⊗[K] L) →ₗ[MonoidAlgebra K G] (S ⊗[K] L)))) :
    letI := diagModule K G S φ L
    Tor1Vanishes (MonoidAlgebra K G) C (S ⊗[K] L) := by
  letI := diagModule K G S φ L
  exact tor1Vanishes_of_shortExact f g hg hfg (S ⊗[K] L) hB hA

/-- **Jaikin-Zapirain--Linton, Theorem 5.6 (single two-cell case), flatness form.**
If in addition
* the duality of `Tor₁` (their Lemma 5.2) holds in the form
  `Tor₁^{K[G]}(L, S ⊗[K] C) = 0 ↔ Tor₁^{K[G]}(C, S ⊗[K] L) = 0` for every `L`, and
* flatness of a left `K[G]`-module may be tested against right `K[G]`-modules carrying a
  compatible `K`-module structure (the standard reduction, valid because every right
  `K[G]`-module is a quotient of a free one, and the syzygy of a free presentation of a
  right `K[G]`-module is again a `K`-module),
then the left `K[G]`-module `S ⊗[K] C` — i.e. `D_{K[G]} ⊗_K (I_{K[G]}/I^G_{K[H]})` in the
notation of Jaikin-Zapirain--Linton — is flat. -/
theorem leftFlat_diagonal_jl
    {A B C : Type u} [AddCommGroup A] [Module (MonoidAlgebra K G)ᵐᵒᵖ A]
    [AddCommGroup B] [Module (MonoidAlgebra K G)ᵐᵒᵖ B]
    [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G)ᵐᵒᵖ C]
    [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ C]
    [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ C]
    (f : A →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] B) (g : B →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] C)
    (hg : Function.Surjective g) (hfg : f.range = g.ker)
    (hB : ∀ (L : Type u) [AddCommGroup L] [Module K L] [Module (MonoidAlgebra K G)ᵐᵒᵖ L]
      [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ L]
      [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ L],
      letI := diagModule K G S φ L
      Tor1Vanishes (MonoidAlgebra K G) B (S ⊗[K] L))
    (hA : ∀ (L : Type u) [AddCommGroup L] [Module K L] [Module (MonoidAlgebra K G)ᵐᵒᵖ L]
      [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ L]
      [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ L],
      letI := diagModule K G S φ L
      Function.Injective (BalTensor.map (MonoidAlgebra K G) f
        (LinearMap.id : (S ⊗[K] L) →ₗ[MonoidAlgebra K G] (S ⊗[K] L))))
    (hswap : ∀ (L : Type u) [AddCommGroup L] [Module K L] [Module (MonoidAlgebra K G)ᵐᵒᵖ L]
      [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ L]
      [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ L],
      letI := diagModule K G S φ L
      letI := diagModule K G S φ C
      (Tor1Vanishes (MonoidAlgebra K G) L (S ⊗[K] C) ↔
        Tor1Vanishes (MonoidAlgebra K G) C (S ⊗[K] L)))
    (hred : ∀ (M : Type u) [AddCommGroup M] [Module (MonoidAlgebra K G) M],
      (∀ (X : Type u) [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G)ᵐᵒᵖ X]
        [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ X]
        [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ X],
        Tor1Vanishes (MonoidAlgebra K G) X M) → LeftFlat (MonoidAlgebra K G) M) :
    letI := diagModule K G S φ C
    LeftFlat (MonoidAlgebra K G) (S ⊗[K] C) := by
  letI := diagModule K G S φ C
  apply hred (S ⊗[K] C)
  intro X _ _ _ _ _
  haveI := diagModule K G S φ X
  rw [hswap X]
  exact tor1Vanishes_diagonal_jl K G S φ f g hg hfg X (hB X) (hA X)

end Work.ORFlatness
