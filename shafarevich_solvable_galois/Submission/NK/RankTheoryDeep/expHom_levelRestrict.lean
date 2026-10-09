import Mathlib
import Submission.NK.RankTheoryDeep.TowerArc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the cyclotomic exponent map

The exponent maps `NK.RankTheoryDeep.expHom Ω N : Gal(ℚ(ζ_{towerMod N})/ℚ) →* (ℤ/towerMod N)^×`
of `Submission/Work/RankTheoryDeep/TowerArc.lean` are the first coordinates of the cyclotomic
character of `Γ_ℚ`, and they are the input of the surjection
`Γ_ℚ ↠ ∏_n ℤ/2^n` used in `Submission/Work/RankTheoryDeep/gamma_surjection_ellTower.lean`
(the refutation of `NK.ShimizuRank.GammaTFRankFinite`).

For that construction one needs the maps to be **compatible with the tower**, i.e. the square

```
Gal(ℚ(ζ_{towerMod N})/ℚ) --expHom N--> (ℤ/towerMod N)^×
          |                                        |
   levelRestrictHom (n ≤ N)                    unitRed (n ≤ N)
          v                                        v
Gal(ℚ(ζ_{towerMod n})/ℚ) --expHom n--> (ℤ/towerMod n)^×
```

must commute for `n ≤ N`.  That is the statement proved here:

* `NK.RankTheoryDeep.expHom_levelRestrict` — **the naturality of the cyclotomic exponent**:
  the exponent of the restriction of an automorphism is the reduction of the exponent.

## Proof

The one non-formal point is that the chosen primitive roots `towerZeta Ω n` and `towerZeta Ω N`
are *independent* choices: `cycLevel_mono` only knows that `towerZeta Ω n` is *some* power of
`towerZeta Ω N`.  Everything else is the bookkeeping of the two coercions involved:

* `NK.RankTheoryDeep.levelRestrictHom_apply_coe` — restricting an automorphism of the level `M`
  to a level `L ⊆ M` and then viewing the result inside `M` is applying the automorphism: the
  restriction maps of `NK.Reconstruct.levelRestrictHom` (a conjugation by `levelToEquiv`) fix the
  subfield pointwise in the correct sense.
* `IsPrimitiveRoot.eq_pow_of_pow_eq_one` writes `towerZeta Ω n` (viewed in the level `N`) as
  `towerZeta Ω N ^ i` with `i < towerMod N`; the automorphism then acts on both sides by the single
  exponent `expHom Ω N σ`, and both the exponent `expHom Ω n` of the restriction and the reduced
  exponent `unitRed h (expHom Ω N σ)` are pinned down by `IsPrimitiveRoot.pow_inj`.
-/

namespace NK.RankTheoryDeep

/-- **The restriction maps of the projective system act by applying the automorphism.**
For a level `L` inside a larger level `M` (both finite normal levels of `K'/K`), the restriction of
`σ : Gal(M/K)` to `L` is `σ` itself, read through the identification `levelToEquiv` of
`↥(levelTo L M h)` with `↥L.L`: the coercion of `levelRestrictHom L M h σ x` back into `K'` is the
coercion of `σ` applied to `x`. -/
theorem levelRestrictHom_apply_coe {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    [IsGalois K K'] (L M : NK.Reconstruct.FrobLevel K K') (h : L.L ≤ M.L) (σ : Gal(↥M.L/K))
    (x : ↥L.L) :
    (NK.Reconstruct.levelRestrictHom L M h σ x : K') =
      (σ (IntermediateField.inclusion h x) : K') := by
  have := NK.Reconstruct.normal_levelTo L M h
  unfold NK.Reconstruct.levelRestrictHom
  simp only [MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
    NK.Reconstruct.algEquivConjHom, AlgEquiv.trans_apply]
  rw [show ((NK.Reconstruct.levelToEquiv L M h)
        (AlgEquiv.restrictNormalHom ↥(NK.Reconstruct.levelTo L M h) σ
          ((NK.Reconstruct.levelToEquiv L M h).symm x)) : K')
      = ((AlgEquiv.restrictNormalHom ↥(NK.Reconstruct.levelTo L M h) σ
          ((NK.Reconstruct.levelToEquiv L M h).symm x)) : ↥M.L) from rfl]
  rw [AlgEquiv.restrictNormalHom_apply]
  have hx : (((NK.Reconstruct.levelToEquiv L M h).symm x) : ↥M.L)
      = IntermediateField.inclusion h x := by
    apply Subtype.ext
    rfl
  rw [hx]

/-- **Naturality of the cyclotomic exponent map**: restricting an automorphism of the `N`-th
cyclotomic level of `Ω` to the `n`-th level (`n ≤ N`) reduces its cyclotomic exponent mod
`towerMod n`. -/
theorem expHom_levelRestrict (Ω : Type*) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    {n N : ℕ} (h : n ≤ N) :
    (NK.RankTheoryDeep.expHom Ω n).comp
        (NK.Reconstruct.levelRestrictHom (NK.RankTheoryDeep.cycLevel Ω n)
          (NK.RankTheoryDeep.cycLevel Ω N) (NK.RankTheoryDeep.cycLevel_mono Ω h)) =
      (NK.RankTheoryDeep.unitRed h).comp (NK.RankTheoryDeep.expHom Ω N) := by
  have hne : NeZero (towerMod n) := ⟨towerMod_ne_zero n⟩
  have hNe : NeZero (towerMod N) := ⟨towerMod_ne_zero N⟩
  ext σ
  simp only [MonoidHom.comp_apply]
  -- abbreviations for the objects of the statement
  set hm : (cycLevel Ω n).L ≤ (cycLevel Ω N).L := cycLevel_mono Ω h with hmdef
  set ζn : ↥(cycLevel Ω n).L := towerZetaL Ω n with hζndef
  set ζN : ↥(cycLevel Ω N).L := towerZetaL Ω N with hζNdef
  set a : (ZMod (towerMod N))ˣ := expHom Ω N σ with hadef
  set j : ℕ := (((unitRed h a) : (ZMod (towerMod n))ˣ) : ZMod (towerMod n)).val with hjdef
  have hζn : IsPrimitiveRoot ζn (towerMod n) := towerZetaL_isPrimitiveRoot Ω n
  have hζN : IsPrimitiveRoot ζN (towerMod N) := towerZetaL_isPrimitiveRoot Ω N
  -- `towerZeta Ω n`, viewed in the larger level, is a `towerMod n`-th root of unity
  have hβ : (IntermediateField.inclusion hm ζn) ^ (towerMod n) = 1 := by
    rw [← map_pow (IntermediateField.inclusion hm) ζn (towerMod n), hζn.pow_eq_one, map_one]
  have hβN : (IntermediateField.inclusion hm ζn) ^ (towerMod N) = 1 := by
    obtain ⟨k, hk⟩ := towerMod_dvd_of_le h
    rw [hk, pow_mul, hβ, one_pow]
  -- hence it is a power of the chosen primitive `towerMod N`-th root
  obtain ⟨i, -, hi⟩ := hζN.eq_pow_of_pow_eq_one hβN
  -- the restriction of `σ` to the small level is `σ` itself, evaluated in the big level
  have h1 : IntermediateField.inclusion hm
        ((NK.Reconstruct.levelRestrictHom (cycLevel Ω n) (cycLevel Ω N) hm σ) ζn)
      = σ (IntermediateField.inclusion hm ζn) := by
    apply Subtype.ext
    exact levelRestrictHom_apply_coe (cycLevel Ω n) (cycLevel Ω N) hm σ ζn
  -- `σ` acts on the powers of `towerZeta Ω N` with the exponent `expHom Ω N σ`
  have hσspec := expHom_spec Ω N σ
  rw [← hadef, ← hζNdef] at hσspec
  have key1 : σ (IntermediateField.inclusion hm ζn)
      = (IntermediateField.inclusion hm ζn) ^ (a : ZMod (towerMod N)).val := by
    rw [← hi, map_pow, ← hσspec, ← pow_mul, ← pow_mul, mul_comm]
  -- the reduced exponent is the exponent `a` of the big level, modulo `towerMod n`
  have haval : ((unitRed h a : (ZMod (towerMod n))ˣ) : ZMod (towerMod n))
      = ((a : ZMod (towerMod N)).val : ZMod (towerMod n)) := by
    rw [NK.RankTheoryDeep.unitRed]
    show (Units.map ((ZMod.castHom (towerMod_dvd_of_le h) (ZMod (towerMod n))).toMonoidHom) a
        : ZMod (towerMod n)) = _
    rw [Units.coe_map]
    show (ZMod.castHom (towerMod_dvd_of_le h) (ZMod (towerMod n)))
        (a : ZMod (towerMod N))
      = ((a : ZMod (towerMod N)).val : ZMod (towerMod n))
    calc (ZMod.castHom (towerMod_dvd_of_le h) (ZMod (towerMod n))) (a : ZMod (towerMod N))
        = (ZMod.castHom (towerMod_dvd_of_le h) (ZMod (towerMod n)))
            (((a : ZMod (towerMod N)).val : ZMod (towerMod N))) := by
          rw [ZMod.natCast_zmod_val]
      _ = ((a : ZMod (towerMod N)).val : ZMod (towerMod n)) := map_natCast _ _
  have hmod : (a : ZMod (towerMod N)).val ≡ j [MOD towerMod n] := by
    have h1 : (((unitRed h a) : (ZMod (towerMod n))ˣ) : ZMod (towerMod n)).val
        = (a : ZMod (towerMod N)).val % towerMod n := by
      rw [haval, ZMod.val_natCast]
    rw [hjdef, h1]
    exact (Nat.mod_modEq _ _).symm
  have key2 : (IntermediateField.inclusion hm ζn) ^ (a : ZMod (towerMod N)).val
      = (IntermediateField.inclusion hm ζn) ^ j :=
    pow_eq_pow_of_modEq hmod hβ
  -- the defining identity of `expHom Ω n` on the restriction
  have key : (NK.Reconstruct.levelRestrictHom (cycLevel Ω n) (cycLevel Ω N) hm σ) ζn
      = ζn ^ j := by
    have hinj : Function.Injective (IntermediateField.inclusion hm :
        ↥(cycLevel Ω n).L → ↥(cycLevel Ω N).L) := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : ↥(cycLevel Ω N).L => (z : Ω)) hxy
    apply hinj
    rw [map_pow, h1, key1, key2]
  have hpow : ζn ^ ((expHom Ω n ((NK.Reconstruct.levelRestrictHom (cycLevel Ω n)
        (cycLevel Ω N) hm σ))) : ZMod (towerMod n)).val = ζn ^ j := by
    have hs := expHom_spec Ω n (NK.Reconstruct.levelRestrictHom (cycLevel Ω n)
      (cycLevel Ω N) hm σ)
    rw [← hζndef] at hs
    rw [hs]
    exact key
  have hval : ((expHom Ω n ((NK.Reconstruct.levelRestrictHom (cycLevel Ω n)
        (cycLevel Ω N) hm σ))) : ZMod (towerMod n)).val = j :=
    hζn.pow_inj (ZMod.val_lt _) (by rw [hjdef]; exact ZMod.val_lt _) hpow
  exact ZMod.val_injective (towerMod n) hval

end NK.RankTheoryDeep
