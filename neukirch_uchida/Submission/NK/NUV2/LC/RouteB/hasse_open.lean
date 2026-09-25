import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.NUV2.LC.RouteB.hasse_twist_open
import Submission.NK.NUV2.LC.RouteB.locLevel_levelCompareOfTop

namespace NK.NUV2.LC.RouteB

/-- **`IsMuOpen` gives the pointwise triviality of the action on the `p`-th roots of unity**: a
subgroup fixing a primitive `p`-th root `ζ ∈ K'` fixes every `p`-th root of unity, since those are
the powers of `ζ`. -/
lemma rootsOfUnity_smul_eq_self_of_isMuOpen {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (hp : p.Prime) {ζ : K'}
    (hζ : IsPrimitiveRoot ζ p) {V : Subgroup Gal(K'/K)}
    (hV : IsMuOpen (K := K) (K' := K') ζ V) :
    ∀ σ : Gal(K'/K), σ ∈ V → ∀ y : rootsOfUnity p K', σ • y = y := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro σ hσV y
  have hfix : (σ : K' ≃ₐ[K] K') ζ = ζ := by
    have h1 : σ ∈ IntermediateField.fixingSubgroup (IntermediateField.adjoin K ({ζ} : Set K')) :=
      hV.2 hσV
    exact (IntermediateField.mem_fixingSubgroup_iff
      (IntermediateField.adjoin K ({ζ} : Set K')) σ).mp h1 ζ
      (IntermediateField.subset_adjoin K {ζ} (Set.mem_singleton ζ))
  have hy : (((y : (K')ˣ) : K')) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity p (y : (K')ˣ)).mp y.2, Units.val_one]
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hy
  apply Subtype.ext
  apply Units.ext
  rw [show (((σ • y : rootsOfUnity p K') : (K')ˣ) : K')
      = (σ : K' ≃ₐ[K] K') • (((y : (K')ˣ) : K')) from rfl]
  rw [← hi]
  change (σ : K' ≃ₐ[K] K') (ζ ^ i) = ζ ^ i
  rw [map_pow, hfix]

/-- **Route B, lemma (H): the Hasse principle (ABHN, injectivity half) at an open level.**

Let `p ≠ 2` be a prime, `ζ` a primitive `p`-th root of unity in `K'` and `V ≤ Gal(K'/K)` open with
`V ≤ rootFix ζ` (equivalently, the fixed field `F = K'^V` contains `ζ`, so that on the levels of `V`
the trivial coefficients `Z/p` agree with `μ_p` and `H²(V, Z/p) = Br(F)[p]`).  If the localisation of
`x ∈ H²(V, Z/p)` vanishes at every finite place, then `x = 0` — i.e. `Br(F)[p] → ∏_v Br(F_v)[p]` is
injective (Hasse–Brauer–Noether; `p ≠ 2` because the archimedean places contribute nothing for odd
`p`).

This is `NK.NUV2.LC.hasse_open_level` with the fixing hypothesis spelled out; see
`Submission/Work/NUV2/LC/NOTES_hasse_open_level.md` for the proved reduction
(`hasse_open_level_of_fixingMu_crux`, reducing to `V ≤ NK.NUV2.LC.OddTwist.fixingMu p`) and for
the remaining level-bookkeeping gap `(G1)`/`(G2)`, whose solution uses `NK.GlobalCFTdeep.hbnUnits`
(Milne CFT VII.7.1, on disk) at a finite level. -/
theorem hasse_open (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {K K' : Type} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (hV : IsMuOpen (K := K) (K' := K') ζ V)
    (x : NK.BrauerHasse.H2Profinite p V)
    (h : ∀ A : NK.BrauerHasse.OverFinitePrime K K', NK.BrauerHasse.H2Profinite.loc p V x A = 0) :
    x = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have htriv := rootsOfUnity_smul_eq_self_of_isMuOpen p hp hζ hV
  -- represent `x` at a level containing `ζ`
  obtain ⟨L₀, a₀, ha₀⟩ := NK.BrauerHasse.H2Profinite.ofLevel_surjective x
  let Lζ : FiniteGaloisIntermediateField K K' :=
    FiniteGaloisIntermediateField.adjoin K ({ζ} : Set K')
  let L : FiniteGaloisIntermediateField K K' := Lζ ⊔ L₀
  have hL₀L : L₀ ≤ L := le_sup_right
  have hLζL : Lζ ≤ L := le_sup_left
  have ha : (NK.BrauerHasse.levelMap p (U := V) hL₀L) a₀ = (NK.BrauerHasse.levelMap p (U := V) hL₀L) a₀ := rfl
  -- the level class representing `x`
  set a : NK.BrauerHasse.LevelH2 p V L :=
    (NK.BrauerHasse.levelMap p (U := V) hL₀L) a₀ with ha_def
  have hza : NK.BrauerHasse.H2Profinite.ofLevel L a = x := by
    rw [ha_def]
    exact (NK.BrauerHasse.H2Profinite.ofLevel_levelMap (p := p) (U := V) hL₀L a₀).trans ha₀
  -- `muLevel p L = ⊤`
  have hmuL : NK.BrauerTwist.muLevel p L = ⊤ := by
    refine NK.NUV2.LC.OddTwist.muLevel_eq_top_of_forall_mem p (L := L) ?_
    intro y
    have hy : (((y : (K')ˣ) : K')) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity p (y : (K')ˣ)).mp y.2, Units.val_one]
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hy
    rw [← hi]
    refine pow_mem ?_ i
    exact hLζL (FiniteGaloisIntermediateField.subset_adjoin K {ζ} (Set.mem_singleton ζ))
  -- the twisted shadow of `x`
  have hloc : ∀ A : NK.BrauerTwist.OverFinitePrime K K',
      NK.BrauerTwist.H2Twist.loc p V
        (NK.BrauerTwist.H2Twist.ofLevel p V L
          ((NK.NUV2.LC.OddTwist.levelCompareOfTop p ζ hζ V htriv L hmuL).symm a)) A = 0 := by
    intro A
    let Ah : NK.BrauerHasse.OverFinitePrime K K' := ⟨A.1, A.2⟩
    have hAh : Ah.1 = A.1 := rfl
    rw [NK.HasseTwist.loc_ofLevel_eq_zero_iff]
    -- the trivial picture: a level killing the level localisation
    have hA : NK.BrauerHasse.LocalH2.ofLevel p V A.1 L
        ((NK.BrauerHasse.locLevel p V A.1 L) a) = 0 := by
      have hx1 : NK.BrauerHasse.H2Profinite.loc p V
          (NK.BrauerHasse.H2Profinite.ofLevel L a) Ah = 0 := by
        rw [hza]
        exact h Ah
      rwa [NK.BrauerHasse.H2Profinite.loc_ofLevel_apply] at hx1
    obtain ⟨M, hLM, h2, hM⟩ :=
      (NK.BrauerHasse.local_ofLevel_eq_iff p
        (a := (NK.BrauerHasse.locLevel p V A.1 L) a)
        (b := (0 : NK.BrauerHasse.LocalLevelH2 p V A.1 ⊥))).mp hA
    rw [map_zero] at hM
    have hM' : (NK.BrauerHasse.locLevel p V A.1 M)
        ((NK.BrauerHasse.levelMap p (U := V) hLM) a) = 0 := by
      rw [NK.BrauerHasse.levelMap_locLevel_apply]
      exact hM
    have hmuM : NK.BrauerTwist.muLevel p M = ⊤ :=
      NK.NUV2.LC.OddTwist.muLevel_eq_top_of_mono p hmuL hLM
    have htwM : (NK.BrauerTwist.locLevel p V A.1 M)
        ((NK.NUV2.LC.OddTwist.levelCompareOfTop p ζ hζ V htriv M hmuM).symm
          ((NK.BrauerHasse.levelMap p (U := V) hLM) a)) = 0 :=
      (NK.NUV2.LC.RouteB.locLevel_levelCompareOfTop p ζ hζ V htriv M hmuM A.1
        ((NK.BrauerHasse.levelMap p (U := V) hLM) a)).mpr hM'
    refine ⟨M, hLM, ?_⟩
    rw [← NK.BrauerTwist.levelMap_locLevel_apply]
    rw [NK.NUV2.LC.OddTwist.levelCompareOfTop_inv_levelMap p ζ hζ V htriv hLM hmuL hmuM a]
    exact htwM
  -- the twisted Hasse principle at the open level
  have hs0 : NK.BrauerTwist.H2Twist.ofLevel p V L
      ((NK.NUV2.LC.OddTwist.levelCompareOfTop p ζ hζ V htriv L hmuL).symm a) = 0 :=
    -- the twisted Hasse principle at the open level (`hasse_twist_open`, sorry-free), applied to
    -- the twisted shadow of `x` whose localisations vanish by `hloc`
    hasse_twist_open p hp hp2 ζ hζ V hV _ hloc
  -- back to the trivial picture
  rw [← hza]
  refine (NK.NUV2.LC.OddTwist.H2Profinite_ofLevel_eq_zero_iff (p := p) (U := V) a).mpr ?_
  obtain ⟨N, hLN, hN⟩ :=
    (NK.NUV2.LC.OddTwist.H2Twist_ofLevel_eq_zero_iff p (U := V)
      (a := (NK.NUV2.LC.OddTwist.levelCompareOfTop p ζ hζ V htriv L hmuL).symm a)).mp hs0
  have hmuN : NK.BrauerTwist.muLevel p N = ⊤ :=
    NK.NUV2.LC.OddTwist.muLevel_eq_top_of_mono p hmuL hLN
  have key : (NK.BrauerHasse.levelMap p (U := V) hLN) a = 0 := by
    have h1 := NK.NUV2.LC.OddTwist.levelCompareOfTop_levelMap p ζ hζ V htriv hLN hmuL hmuN
      ((NK.NUV2.LC.OddTwist.levelCompareOfTop p ζ hζ V htriv L hmuL).symm a)
    rw [Equiv.apply_symm_apply] at h1
    rw [hN] at h1
    rw [NK.NUV2.LC.OddTwist.levelCompareOfTop_zero p ζ hζ V htriv N hmuN] at h1
    exact h1.symm
  exact ⟨N, hLN, key⟩

end NK.NUV2.LC.RouteB
