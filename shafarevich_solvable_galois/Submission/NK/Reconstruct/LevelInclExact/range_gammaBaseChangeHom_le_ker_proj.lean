import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.Reconstruct.LevelInclExact.ellIncl_range_eq_ker_ellRestrict
import Submission.NK.Reconstruct.gammaBaseChange
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The base-change map `π_{L/K}` kills the fibre over the trivial level-`L` element

`NK.Reconstruct.gammaBaseChangeHom ℓ L : Γ_L →* Γ_K` is Shimizu's canonical map
`π_{L/K}` (`gammaBaseChange.lean`); it is characterised by the projection formula

  `Γ.proj N (π_{L/K} f) = ellRestrict ℓ N (N ⊔ L) _ (ellIncl ℓ L (N ⊔ L) _ (Γ.proj _ f))`.

Evaluating that formula at the level `N = L` leaves the *composite* of the level inclusion and
the level restriction at the single level `L ⊔ L`:

  `Γ.proj L (π_{L/K} f) = ellRestrict ℓ L (L ⊔ L) _ (ellIncl ℓ L (L ⊔ L) _ (Γ.proj _ f))`,

and this composite is trivial because the level inclusion `ellIncl` has range the kernel of the
level restriction `ellRestrict` (`LevelInclExact.ellIncl_range_eq_ker_ellRestrict`, i.e.
`1 → Gal(M/L) → Gal(M/K) → Gal(L/K) → 1` abelianised and restricted to ℓ-primary parts).

Hence `π_{L/K}` lands in the kernel of the projection `Γ_K → Γ_L`:

  `(π_{L/K}).range ≤ (Γ.proj L).ker`.

The two occurrences of the proof `L ≤ L ⊔ L` (one as `le_sup_left`, one as `le_sup_right` at
`N = L`) carry no information — the relation is a proposition — so the composite has the same
shape as the one covered by the exactness lemma.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

namespace NK.Reconstruct.LevelInclExact

theorem range_gammaBaseChangeHom_le_ker_proj {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) (L : FrobLevel K K') :
    (gammaBaseChangeHom ℓ L).range ≤ (Gamma.proj (K := K) (K' := K') (ℓ := ℓ) L).ker := by
  -- the projection of `π_{L/K} f` to the level `L`
  rintro g ⟨f, rfl⟩
  rw [MonoidHom.mem_ker]
  show ellRestrict ℓ L (L.sup L) (FrobLevel.le_sup_right L L)
      (ellIncl ℓ L (L.sup L) (FrobLevel.le_sup_left L L)
        (Gamma.proj (K := ↥L.L) (K' := K') (ℓ := ℓ)
          (levelExtend L (L.sup L) (FrobLevel.le_sup_left L L)) f)) = 1
  -- the two proofs `L ≤ L ⊔ L` agree, so this is the composite of the level inclusion with the
  -- level restriction at `L ⊔ L`
  rw [show FrobLevel.le_sup_right L L = FrobLevel.le_sup_left L L from
    Subsingleton.elim _ _]
  -- the level inclusion has range the kernel of the level restriction
  rw [← MonoidHom.mem_ker]
  exact le_of_eq (ellIncl_range_eq_ker_ellRestrict ℓ L (L.sup L)
      (FrobLevel.le_sup_left L L)) (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

end NK.Reconstruct.LevelInclExact
