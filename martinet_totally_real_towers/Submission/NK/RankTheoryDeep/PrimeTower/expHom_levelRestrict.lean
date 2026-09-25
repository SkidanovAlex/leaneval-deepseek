import Mathlib
import Submission.NK.RankTheoryDeep.PrimeTower.Defs
import Submission.NK.RankTheoryDeep.expHom_levelRestrict

namespace NK.RankTheoryDeep.PrimeTower

/-- The restriction maps of the projective system act by applying the automorphism: this is
`NK.RankTheoryDeep.levelRestrictHom_apply_coe`, restated in the `PrimeTower` namespace so that
the proof below can refer to it by a short name. -/
theorem levelRestrictHom_apply_coe_gen {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    [IsGalois K K'] (L M : NK.Reconstruct.FrobLevel K K') (h : L.L ≤ M.L)
    (σ : Gal(↥M.L/K)) (x : ↥L.L) :
    (NK.Reconstruct.levelRestrictHom L M h σ x : K') =
      (σ (IntermediateField.inclusion h x) : K') :=
  NK.RankTheoryDeep.levelRestrictHom_apply_coe L M h σ x

-- expHom ℓ Ω N : Gal(ℚ(ζ_{towerMod ℓ N})/ℚ) →* (ZMod (towerMod ℓ N))ˣ, unitRed ℓ h the reduction (ZMod (towerMod ℓ N))ˣ → (ZMod (towerMod ℓ n))ˣ for n ≤ N, cycLevel ℓ Ω N the level ℚ(ζ_{towerMod ℓ N}) of Ω, all in Submission/Work/RankTheoryDeep/PrimeTower/Defs.lean.  ℓ = 2 analogue: Submission/Work/RankTheoryDeep/expHom_levelRestrict.lean
theorem expHom_levelRestrict (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type*) [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] {n N : ℕ} (h : n ≤ N) :
    (expHom ℓ Ω n).comp
        (NK.Reconstruct.levelRestrictHom (cycLevel ℓ Ω n) (cycLevel ℓ Ω N)
          (cycLevel_mono ℓ Ω h)) =
      (unitRed ℓ h).comp (expHom ℓ Ω N) := by
  have hne : NeZero (towerMod ℓ n) := ⟨towerMod_ne_zero ℓ n⟩
  have hNe : NeZero (towerMod ℓ N) := ⟨towerMod_ne_zero ℓ N⟩
  ext σ
  simp only [MonoidHom.comp_apply]
  set hm : (cycLevel ℓ Ω n).L ≤ (cycLevel ℓ Ω N).L := cycLevel_mono ℓ Ω h with hmdef
  set ζn : ↥(cycLevel ℓ Ω n).L := towerZetaL ℓ Ω n with hζndef
  set ζN : ↥(cycLevel ℓ Ω N).L := towerZetaL ℓ Ω N with hζNdef
  set a : (ZMod (towerMod ℓ N))ˣ := expHom ℓ Ω N σ with hadef
  set j : ℕ := (((unitRed ℓ h a) : (ZMod (towerMod ℓ n))ˣ) : ZMod (towerMod ℓ n)).val with hjdef
  have hζn : IsPrimitiveRoot ζn (towerMod ℓ n) := towerZetaL_isPrimitiveRoot ℓ Ω n
  have hζN : IsPrimitiveRoot ζN (towerMod ℓ N) := towerZetaL_isPrimitiveRoot ℓ Ω N
  -- `towerZeta ℓ Ω n`, viewed in the larger level, is a `towerMod ℓ n`-th root of unity
  have hβ : (IntermediateField.inclusion hm ζn) ^ (towerMod ℓ n) = 1 := by
    rw [← map_pow (IntermediateField.inclusion hm) ζn (towerMod ℓ n), hζn.pow_eq_one, map_one]
  have hβN : (IntermediateField.inclusion hm ζn) ^ (towerMod ℓ N) = 1 := by
    obtain ⟨k, hk⟩ := towerMod_dvd_of_le ℓ h
    rw [hk, pow_mul, hβ, one_pow]
  -- hence it is a power of the chosen primitive `towerMod ℓ N`-th root
  obtain ⟨i, -, hi⟩ := hζN.eq_pow_of_pow_eq_one hβN
  -- the restriction of `σ` to the small level is `σ` itself, evaluated in the big level
  have h1 : IntermediateField.inclusion hm
        ((NK.Reconstruct.levelRestrictHom (cycLevel ℓ Ω n) (cycLevel ℓ Ω N) hm σ) ζn)
      = σ (IntermediateField.inclusion hm ζn) := by
    apply Subtype.ext
    exact levelRestrictHom_apply_coe_gen (cycLevel ℓ Ω n) (cycLevel ℓ Ω N) hm σ ζn
  -- `σ` acts on the powers of `towerZeta ℓ Ω N` with the exponent `expHom ℓ Ω N σ`
  have hσspec := expHom_spec ℓ Ω N σ
  rw [← hadef, ← hζNdef] at hσspec
  have key1 : σ (IntermediateField.inclusion hm ζn)
      = (IntermediateField.inclusion hm ζn) ^ (a : ZMod (towerMod ℓ N)).val := by
    rw [← hi, map_pow, ← hσspec, ← pow_mul, ← pow_mul, mul_comm]
  -- the reduced exponent is the exponent `a` of the big level, modulo `towerMod ℓ n`
  have haval : ((unitRed ℓ h a : (ZMod (towerMod ℓ n))ˣ) : ZMod (towerMod ℓ n))
      = ((a : ZMod (towerMod ℓ N)).val : ZMod (towerMod ℓ n)) := by
    rw [unitRed]
    show (Units.map ((ZMod.castHom (towerMod_dvd_of_le ℓ h) (ZMod (towerMod ℓ n))).toMonoidHom) a
        : ZMod (towerMod ℓ n)) = _
    rw [Units.coe_map]
    show (ZMod.castHom (towerMod_dvd_of_le ℓ h) (ZMod (towerMod ℓ n)))
        (a : ZMod (towerMod ℓ N))
      = ((a : ZMod (towerMod ℓ N)).val : ZMod (towerMod ℓ n))
    calc (ZMod.castHom (towerMod_dvd_of_le ℓ h) (ZMod (towerMod ℓ n))) (a : ZMod (towerMod ℓ N))
        = (ZMod.castHom (towerMod_dvd_of_le ℓ h) (ZMod (towerMod ℓ n)))
            (((a : ZMod (towerMod ℓ N)).val : ZMod (towerMod ℓ N))) := by
          rw [ZMod.natCast_zmod_val]
      _ = ((a : ZMod (towerMod ℓ N)).val : ZMod (towerMod ℓ n)) := map_natCast _ _
  have hmod : (a : ZMod (towerMod ℓ N)).val ≡ j [MOD towerMod ℓ n] := by
    have h1 : (((unitRed ℓ h a) : (ZMod (towerMod ℓ n))ˣ) : ZMod (towerMod ℓ n)).val
        = (a : ZMod (towerMod ℓ N)).val % towerMod ℓ n := by
      rw [haval, ZMod.val_natCast]
    rw [hjdef, h1]
    exact (Nat.mod_modEq _ _).symm
  have key2 : (IntermediateField.inclusion hm ζn) ^ (a : ZMod (towerMod ℓ N)).val
      = (IntermediateField.inclusion hm ζn) ^ j :=
    pow_eq_pow_of_modEq hmod hβ
  -- the defining identity of `expHom ℓ Ω n` on the restriction
  have key : (NK.Reconstruct.levelRestrictHom (cycLevel ℓ Ω n) (cycLevel ℓ Ω N) hm σ) ζn
      = ζn ^ j := by
    have hinj : Function.Injective (IntermediateField.inclusion hm :
        ↥(cycLevel ℓ Ω n).L → ↥(cycLevel ℓ Ω N).L) := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : ↥(cycLevel ℓ Ω N).L => (z : Ω)) hxy
    apply hinj
    rw [map_pow, h1, key1, key2]
  have hpow : ζn ^ ((expHom ℓ Ω n ((NK.Reconstruct.levelRestrictHom (cycLevel ℓ Ω n)
        (cycLevel ℓ Ω N) hm σ))) : ZMod (towerMod ℓ n)).val = ζn ^ j := by
    have hs := expHom_spec ℓ Ω n (NK.Reconstruct.levelRestrictHom (cycLevel ℓ Ω n)
      (cycLevel ℓ Ω N) hm σ)
    rw [← hζndef] at hs
    rw [hs]
    exact key
  have hval : ((expHom ℓ Ω n ((NK.Reconstruct.levelRestrictHom (cycLevel ℓ Ω n)
        (cycLevel ℓ Ω N) hm σ))) : ZMod (towerMod ℓ n)).val = j :=
    hζn.pow_inj (ZMod.val_lt _) (by rw [hjdef]; exact ZMod.val_lt _) hpow
  exact ZMod.val_injective (towerMod ℓ n) hval

end NK.RankTheoryDeep.PrimeTower
