import Mathlib
import Submission.NK.NUV2.TowerRank.towerIso
import Submission.NK.NUV2.ArtinBridge.levelPairIso
import Submission.NK.NUV2.ArtinBridge.canonicalArtinDatum_of_levelPairIso
import Submission.NK.NUV2.ArtinBridge.isPGroup_sup_of_isPGroup
import Submission.NK.NUV2.ArtinBridge.exists_ellPowerLevel_normClassSubgroup_le
import Submission.NK.NUV2.TowerRank.exists_abelian_level
import Submission.NK.NUV2.TowerRank.le_dualRank_gamma_of_nested_levels
import Submission.NK.NUV2.TowerRank.exists_nested_subgroups_of_le_dualRank

/-!
# `r ≤ dualRank Γ_K 2` from `r ≤ dualRank C_K 2` and the level-pair correspondence

This file proves `NK.NUV2.TowerRank.le_dualRank_gamma_of_levelPairIso`, i.e. **half (B)** of the
rank form of `2`-adic Artin reciprocity (see `Submission/Work/NUV2/TowerRank/NOTES.md` §3 and §8),
now from the *pair* input `NK.NUV2.ArtinBridge.LevelPairIso K Ω 2` rather than from a nested tower
of levels: the pair condition (the levelwise norm-group/Galois-subgroup correspondence) produces the
*coherent* Artin system (`NK.NUV2.ArtinBridge.canonicalArtinDatum_of_levelPairIso`), and the
coherence is exactly what is needed to transport a tower of quotients of `C_K` to a tower of
quotients of `Γ_K`.

## The argument

* from `r ≤ dualRank C_K 2` the workspace produces a **nested tower of open subgroups**
  `U 0 ⊇ U 1 ⊇ ⋯` of `C_K` with `C_K ⧸ U n ≅ (ℤ/2^n)^r`
  (`NK.NUV2.TowerRank.exists_nested_subgroups_of_le_dualRank`);
* the existence theorem (in the form `NK.NUV2.TowerRank.exists_abelian_level`, which is derived
  from `hEx` and the norm limitation theorem) realises each `U n` as a norm group
  `N_{L n/K} C_{L n}` of an abelian — hence `2`-power — level `L n`; the `L n` need *not* be nested,
  and the composita `M n := L 0 ⊔ ⋯ ⊔ L n` are used instead: they *are* nested, they are `2`-levels,
  and `N_{M n/K} C_{M n} ≤ U n`;
* the coherent Artin system `art L : C_K ↠ Γ_{L,2}` (from `hPair`) identifies
  `C_K ⧸ N_{M n/K} C_{M n}` with `Γ_{M n, 2}` **coherently in `n`** and the corrected isomorphisms
  `φ n : C_K ⧸ U n ≅ (ℤ/2^n)^r` supplied by `TowerCompatible r` (the crux of §2 of the NOTES) are
  compatible with the transition maps; composing with the projections `Γ_K ↠ Γ_{M n,2}` produces
  *compatible* surjections `θ n : Γ_K ↠ (ℤ/2^n)^r`;
* a compatible family of level surjections of a profinite group yields `r` independent continuous
  characters of `Γ_K` (the finite-intersection argument of
  `NK.NUV2.TowerRank.le_dualRank_gamma_of_nested_levels`), i.e. `r ≤ dualRank Γ_K 2`.
-/

namespace NK.NUV2.TowerRank

open scoped IsMulCommutative

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## The compositum of the levels of a tower -/

/-- **The running compositum of the levels of a tower**: `supRange L n = L 0 ⊔ L 1 ⊔ ⋯ ⊔ L n`. -/
noncomputable def supRange {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] (L : ℕ → NK.Reconstruct.FrobLevel K Ω) :
    ℕ → NK.Reconstruct.FrobLevel K Ω
  | 0 => L 0
  | (n + 1) => (supRange L n).sup (L (n + 1))

/-- Each level of the tower is contained in its running compositum. -/
lemma le_supRange {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] (L : ℕ → NK.Reconstruct.FrobLevel K Ω) :
    ∀ n, (L n).L ≤ (supRange L n).L := by
  intro n
  cases n with
  | zero => exact le_rfl
  | succ k => exact NK.Reconstruct.FrobLevel.le_sup_right (supRange L k) (L (k + 1))

/-- The running composita are nested. -/
lemma supRange_le_succ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] (L : ℕ → NK.Reconstruct.FrobLevel K Ω) :
    ∀ n, (supRange L n).L ≤ (supRange L (n + 1)).L := by
  intro n
  exact NK.Reconstruct.FrobLevel.le_sup_left (supRange L n) (L (n + 1))

/-- The running composita of `ℓ`-levels are `ℓ`-levels. -/
lemma isPGroup_supRange {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] (L : ℕ → NK.Reconstruct.FrobLevel K Ω) (ℓ : ℕ)
    (hL : ∀ n, IsPGroup ℓ (↥(L n).L ≃ₐ[K] ↥(L n).L)) :
    ∀ n, IsPGroup ℓ (↥(supRange L n).L ≃ₐ[K] ↥(supRange L n).L) := by
  intro n
  induction n with
  | zero => exact hL 0
  | succ k ih =>
      exact NK.NUV2.ArtinBridge.isPGroup_sup_of_isPGroup ℓ (supRange L k) (L (k + 1)) ih (hL (k + 1))

/-! ## Cardinality of the standard level `(ℤ/2^n)^r` -/

/-- The multiplicative group `Multiplicative ((ℤ/2^n)^r)` has cardinality `2 ^ (r * n)`. -/
lemma card_multiplicative_fin_zmod (r n : ℕ) :
    Nat.card (Multiplicative (Fin r → ZMod (2 ^ n))) = 2 ^ (r * n) := by
  rw [show Nat.card (Multiplicative (Fin r → ZMod (2 ^ n)))
      = Nat.card (Fin r → ZMod (2 ^ n)) from Nat.card_congr (Equiv.refl _)]
  rw [Nat.card_pi]
  simp only [Nat.card_zmod]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

/-- **An abelian level whose norm group has `2`-power index is a `2`-level.** -/
lemma isPGroup_two_gal_of_normClassSubgroup_eq {K : Type} [Field K] [NumberField K]
    {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] [Algebra K Ω]
    [IsGalois K Ω] (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    (r n : ℕ) (F : NK.Reconstruct.FrobLevel K Ω)
    (habel : IsMulCommutative (↥F.L ≃ₐ[K] ↥F.L))
    (U : Subgroup (NK.GlobalCFT.IdeleClassGroup K))
    (hN : NK.GlobalCFT.Idele.normClassSubgroup K ↥F.L = U)
    (e : NK.GlobalCFT.IdeleClassGroup K ⧸ U ≃* Multiplicative (Fin r → ZMod (2 ^ n))) :
    IsPGroup 2 (↥F.L ≃ₐ[K] ↥F.L) := by
  haveI hsolv : Group.IsSolvable (↥F.L ≃ₐ[K] ↥F.L) :=
    Group.isSolvable_of_comm (fun a b => mul_comm' a b)
  have hrec := NK.GlobalCFTdeep.galoisReciprocity_of_fundamentalClassElement hFC
    (K := K) (L := ↥F.L)
  have e1 : (↥F.L ≃ₐ[K] ↥F.L) ≃* Multiplicative (Fin r → ZMod (2 ^ n)) :=
    (Abelianization.equivOfComm (H := ↥F.L ≃ₐ[K] ↥F.L)).trans
      (hrec.iso.symm.trans ((QuotientGroup.quotientMulEquivOfEq hN).trans e))
  have hcard : Nat.card (↥F.L ≃ₐ[K] ↥F.L) = 2 ^ (r * n) := by
    rw [Nat.card_congr e1.toEquiv]
    exact card_multiplicative_fin_zmod r n
  exact IsPGroup.of_card hcard

/-! ## A compatible family of level surjections of `Γ_K` bounds its rank

This is the second half of `NK.NUV2.TowerRank.le_dualRank_gamma_of_nested_levels`, isolated in
the form in which the main theorem produces it (a compatible family of surjections
`Γ_K ↠ (ℤ/2^n)^r`, rather than one obtained from a nested tower of levels). -/
theorem le_dualRank_gamma_of_compatible_levelHom (r : ℕ)
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsGalois K Ω]
    (F : ∀ n, NK.Reconstruct.Gamma K Ω 2 →* Multiplicative (Fin r → ZMod (2 ^ n)))
    (hFc : ∀ n, Continuous ⇑(F n))
    (hFs : ∀ n, Function.Surjective (F n))
    (hstep : ∀ (n : ℕ) (x : NK.Reconstruct.Gamma K Ω 2),
      (F n x).toAdd = coordRed r n (n + 1) ((F (n + 1) x).toAdd)) :
    (r : Cardinal) ≤ NK.RankTheoryDeep.dualRank (NK.Reconstruct.Gamma K Ω 2) 2 := by
  classical
  have hcompat : ∀ (m n : ℕ) (hmn : m ≤ n) (x : NK.Reconstruct.Gamma K Ω 2),
      (F m x).toAdd = coordRed r m n ((F n x).toAdd) := by
    intro m n hmn x
    have key : ∀ k (hmk : m ≤ k), (F m x).toAdd = coordRed r m k ((F k x).toAdd) := by
      intro k hmk
      induction k, hmk using Nat.le_induction with
      | base => rw [coordRed_self]
      | succ j hmj ih =>
          rw [ih, hstep j x]
          exact coordRed_comp r m j (j + 1) hmj (Nat.le_succ j) ((F (j + 1) x).toAdd)
    exact key n hmn
  let Fi : ∀ (i : Fin r) (n : ℕ),
      Additive (NK.Reconstruct.Gamma K Ω 2) →+ ZMod (2 ^ n) :=
    fun i n => (Pi.evalAddMonoidHom (fun _ : Fin r => ZMod (2 ^ n)) i).comp
      (MonoidHom.toAdditive (F n))
  have hFi_apply : ∀ (i : Fin r) (n : ℕ) (x : Additive (NK.Reconstruct.Gamma K Ω 2)),
      Fi i n x = (F n (Additive.toMul x)).toAdd i := fun i n x => rfl
  have hcompatFi : ∀ (i : Fin r) (m n : ℕ) (hmn : m ≤ n)
      (x : Additive (NK.Reconstruct.Gamma K Ω 2)),
      Fi i m x = redAdd m n (Fi i n x) := by
    intro i m n hmn x
    show (F m (Additive.toMul x)).toAdd i = redAdd m n ((F n (Additive.toMul x)).toAdd i)
    have h := congrFun (hcompat m n hmn (Additive.toMul x)) i
    rwa [coordRed_apply] at h
  have hcompatFi_cast : ∀ (i : Fin r) (m n : ℕ) (hmn : m ≤ n)
      (x : Additive (NK.Reconstruct.Gamma K Ω 2)),
      Fi i m x = ZMod.castHom (pow_dvd_pow 2 hmn) (ZMod (2 ^ m)) (Fi i n x) := by
    intro i m n hmn x
    rw [hcompatFi i m n hmn x, redAdd_of_le hmn]
  have hcontFi : ∀ (i : Fin r) (n : ℕ), Continuous ⇑(Fi i n) := by
    intro i n
    have h1 : Continuous (fun x : Additive (NK.Reconstruct.Gamma K Ω 2) =>
        F n (Additive.toMul x)) :=
      (hFc n).comp
        (continuous_id : Continuous (Additive.toMul : Additive (NK.Reconstruct.Gamma K Ω 2) →
          NK.Reconstruct.Gamma K Ω 2))
    have h2 : Continuous (fun y : Multiplicative (Fin r → ZMod (2 ^ n)) => y.toAdd i) :=
      continuous_of_discreteTopology
    exact h2.comp h1
  have hlift : ∀ i : Fin r, ∃ g : Additive (NK.Reconstruct.Gamma K Ω 2) →+ PadicInt 2,
      ∀ (n : ℕ) (x : Additive (NK.Reconstruct.Gamma K Ω 2)),
        PadicInt.toZModPow n (g x) = Fi i n x :=
    fun i => NK.RankTheoryDeep.exists_addHom_padicInt_lift (Fi i) (hcompatFi_cast i)
  choose χhom hχhom using hlift
  have hcontχ : ∀ i : Fin r, Continuous ⇑(χhom i) := fun i =>
    NK.RankTheoryDeep.continuous_of_toZModPow_comp (χhom i) (Fi i)
      (fun n => hcontFi i n) (fun n x => hχhom i n x)
  let χ : Fin r → NK.Reconstruct.Dual (NK.Reconstruct.Gamma K Ω 2) 2 :=
    fun i => ⟨χhom i, hcontχ i⟩
  refine NK.NUV2.TowerRank.le_dualRank_of_surjective χ (fun y => ?_)
  let S : ℕ → Set (NK.Reconstruct.Gamma K Ω 2) := fun n =>
    {x | ∀ i : Fin r, Fi i n (Additive.ofMul x) = PadicInt.toZModPow n (y i)}
  have hclosed : ∀ n, IsClosed (S n) := by
    intro n
    have hset : S n = ⋂ i : Fin r,
        {x : NK.Reconstruct.Gamma K Ω 2 |
          Fi i n (Additive.ofMul x) = PadicInt.toZModPow n (y i)} := by
      ext x
      simp only [S, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hset]
    refine isClosed_iInter (fun i => isClosed_eq ?_ continuous_const)
    exact (hcontFi i n).comp
      (continuous_id : Continuous (Additive.ofMul : NK.Reconstruct.Gamma K Ω 2 →
        Additive (NK.Reconstruct.Gamma K Ω 2)))
  have hnonempty : ∀ n, (S n).Nonempty := by
    intro n
    obtain ⟨g, hg⟩ := hFs n (Multiplicative.ofAdd (fun i : Fin r => PadicInt.toZModPow n (y i)))
    refine ⟨g, ?_⟩
    intro i
    have hgi := congrFun (congrArg (fun w : Multiplicative (Fin r → ZMod (2 ^ n)) =>
      w.toAdd) hg) i
    show Fi i n (Additive.ofMul g) = PadicInt.toZModPow n (y i)
    rw [hFi_apply, toMul_ofMul]
    simpa using hgi
  have hanti : ∀ {m n : ℕ}, m ≤ n → S n ⊆ S m := by
    intro m n hmn x hx i
    have h1 : Fi i m (Additive.ofMul x) = redAdd m n (Fi i n (Additive.ofMul x)) :=
      hcompatFi i m n hmn (Additive.ofMul x)
    have h2 : redAdd m n (Fi i n (Additive.ofMul x))
        = ZMod.castHom (pow_dvd_pow 2 hmn) (ZMod (2 ^ m)) (Fi i n (Additive.ofMul x)) :=
      redAdd_of_le hmn _
    rw [h1, h2, hx i]
    exact congrFun (congrArg (fun f : ℤ_[2] →+* ZMod (2 ^ m) => ⇑f)
      (PadicInt.zmod_cast_comp_toZModPow m n hmn)) (y i)
  have hInter : (⋂ n, S n).Nonempty := by
    by_contra hne
    have hempty : (Set.univ ∩ ⋂ n, S n) = ∅ := by
      rw [Set.univ_inter]
      exact Set.not_nonempty_iff_eq_empty.mp hne
    obtain ⟨u, hu⟩ := isCompact_univ.elim_finite_subfamily_closed S hclosed
      (Set.disjoint_iff_inter_eq_empty.mpr hempty)
    obtain ⟨x, hx⟩ := hnonempty (u.sup id)
    have hx' : x ∈ Set.univ ∩ ⋂ n ∈ u, S n := by
      refine ⟨Set.mem_univ x, ?_⟩
      rw [Set.mem_iInter₂]
      intro n hn
      exact (hanti (Finset.le_sup hn)) hx
    exact Set.disjoint_left.mp hu hx'.1 hx'.2
  obtain ⟨x, hx⟩ := hInter
  refine ⟨x, ?_⟩
  funext i
  refine PadicInt.ext_of_toZModPow.mp (fun n => ?_)
  exact (hχhom i n (Additive.ofMul x)).trans (Set.mem_iInter.mp hx n i)

/-! ## The main theorem -/

theorem le_dualRank_gamma_of_levelPairIso (r : ℕ) (hTower : NK.NUV2.TowerRank.TowerCompatible r)
    (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    (hEx : ∀ (K : Type) [Field K] [NumberField K], NK.GlobalCFT.ExistenceTheorem K)
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsGalois K Ω]
    (hPair : NK.NUV2.ArtinBridge.LevelPairIso K Ω 2)
    (h : (r : Cardinal) ≤ NK.RankTheoryDeep.dualRank (NK.GlobalCFT.IdeleClassGroup K) 2) :
    (r : Cardinal) ≤ NK.RankTheoryDeep.dualRank (NK.Reconstruct.Gamma K Ω 2) 2 := by
  classical
  haveI hsepK : IsSepClosure K Ω := ⟨IsSepClosure.sep_closed ℚ, inferInstance⟩
  -- ## Step 1: the nested tower of open subgroups of `C_K`
  obtain ⟨U, hUanti, hUopen, hUlev⟩ := exists_nested_subgroups_of_le_dualRank (K := K) r h
  have hUfin : ∀ n, (U n).FiniteIndex := fun n => by
    haveI : Finite (NK.GlobalCFT.IdeleClassGroup K ⧸ U n) :=
      Finite.of_equiv (Multiplicative (Fin r → ZMod (2 ^ n))) (hUlev n).some.symm.toEquiv
    exact Subgroup.finiteIndex_iff.mpr (Subgroup.index_ne_zero_of_finite (H := U n))
  -- ## Step 2: the abelian class fields `L n` of the `U n`
  have hLexists : ∀ n, ∃ F : NK.Reconstruct.FrobLevel K Ω,
      IsMulCommutative (↥F.L ≃ₐ[K] ↥F.L) ∧
        NK.GlobalCFT.Idele.normClassSubgroup K ↥F.L = U n :=
    fun n => exists_abelian_level hFC hEx (U n) (hUfin n) (hUopen n)
  choose L hLab hLN using hLexists
  have hLp : ∀ n, IsPGroup 2 (↥(L n).L ≃ₐ[K] ↥(L n).L) := fun n =>
    isPGroup_two_gal_of_normClassSubgroup_eq (K := K) (Ω := Ω) hFC r n (L n) (hLab n) (U n)
      (hLN n) (hUlev n).some
  -- ## Step 3: the nested composita `M n = L 0 ⊔ ⋯ ⊔ L n` and their norm groups
  let M : ℕ → NK.Reconstruct.FrobLevel K Ω := supRange L
  have hMp : ∀ n, IsPGroup 2 (↥(M n).L ≃ₐ[K] ↥(M n).L) := isPGroup_supRange L 2 hLp
  have hMle : ∀ n, (M n).L ≤ (M (n + 1)).L := supRange_le_succ L
  have hLleM : ∀ n, (L n).L ≤ (M n).L := le_supRange L
  have hnorm : ∀ n,
      NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L ≤ U n := fun n =>
    (NK.NUV2.ArtinBridge.normClassSubgroup_le_of_le (L n).L (M n).L (hLleM n)).trans
      (le_of_eq (hLN n))
  -- ## Step 4: the coherent Artin system
  obtain ⟨art, hcoh, hker, hsurj⟩ :=
    NK.NUV2.ArtinBridge.canonicalArtinDatum_of_levelPairIso 2 hPair
  -- ## Step 5: the isomorphisms `C_K ⧸ N_{M n} ≅ Γ_{M n, 2}`
  haveI hNormN : ∀ n, (NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L).Normal := fun n =>
    Subgroup.normal_of_isMulCommutative _
  haveI hNormU : ∀ n, (U n).Normal := fun n => Subgroup.normal_of_isMulCommutative _
  let α' : ∀ n, NK.GlobalCFT.IdeleClassGroup K ⧸
        NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L →*
        ↥(NK.Reconstruct.LevelEllPart (M n).L 2) := fun n =>
    QuotientGroup.lift (NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L)
      (art (M n) (hMp n)) (le_of_eq (hker (M n) (hMp n)).symm)
  have hα'ker : ∀ n, (α' n).ker = ⊥ := fun n => by
    change (QuotientGroup.lift (NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L)
      (art (M n) (hMp n)) (le_of_eq (hker (M n) (hMp n)).symm)).ker = ⊥
    rw [QuotientGroup.ker_lift, hker (M n) (hMp n), Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
  have hα'inj : ∀ n, Function.Injective (α' n) := fun n =>
    (MonoidHom.ker_eq_bot_iff (α' n)).mp (hα'ker n)
  have hα'surj : ∀ n, Function.Surjective (α' n) := fun n y => by
    obtain ⟨c, hc⟩ := hsurj (M n) (hMp n) y
    refine ⟨QuotientGroup.mk' _ c, ?_⟩
    change (QuotientGroup.lift (NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L)
      (art (M n) (hMp n)) (le_of_eq (hker (M n) (hMp n)).symm))
      (QuotientGroup.mk' _ c) = y
    have hcomp := congrFun (congrArg (fun f : NK.GlobalCFT.IdeleClassGroup K →*
        ↥(NK.Reconstruct.LevelEllPart (M n).L 2) => ⇑f)
      (QuotientGroup.lift_comp_mk' (NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L)
        (art (M n) (hMp n)) (le_of_eq (hker (M n) (hMp n)).symm))) c
    exact hcomp.trans hc
  let α : ∀ n, (NK.GlobalCFT.IdeleClassGroup K ⧸
        NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L) ≃*
        ↥(NK.Reconstruct.LevelEllPart (M n).L 2) := fun n =>
    MulEquiv.ofBijective (α' n) ⟨hα'inj n, hα'surj n⟩
  have hα_apply : ∀ (n : ℕ) (c : NK.GlobalCFT.IdeleClassGroup K),
      (α n) (QuotientGroup.mk' _ c) = art (M n) (hMp n) c := by
    intro n c
    change (α' n) (QuotientGroup.mk' _ c) = art (M n) (hMp n) c
    have hcomp := congrFun (congrArg (fun f : NK.GlobalCFT.IdeleClassGroup K →*
        ↥(NK.Reconstruct.LevelEllPart (M n).L 2) => ⇑f)
      (QuotientGroup.lift_comp_mk' (NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L)
        (art (M n) (hMp n)) (le_of_eq (hker (M n) (hMp n)).symm))) c
    exact hcomp
  -- ## Step 6: the quotient maps
  let qN : ∀ n, (NK.GlobalCFT.IdeleClassGroup K ⧸
        NK.GlobalCFT.Idele.normClassSubgroup K ↥(M (n + 1)).L) →*
        (NK.GlobalCFT.IdeleClassGroup K ⧸
        NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L) := fun n =>
    QuotientGroup.map (NK.GlobalCFT.Idele.normClassSubgroup K ↥(M (n + 1)).L)
      (NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L)
      (MonoidHom.id (NK.GlobalCFT.IdeleClassGroup K))
      (by
        have hmono : NK.GlobalCFT.Idele.normClassSubgroup K ↥(M (n + 1)).L ≤
            NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L :=
          NK.NUV2.ArtinBridge.normClassSubgroup_le_of_le (M n).L (M (n + 1)).L (hMle n)
        simpa using hmono)
  have hqN_mk' : ∀ (n : ℕ) (c : NK.GlobalCFT.IdeleClassGroup K),
      qN n (QuotientGroup.mk' _ c) = QuotientGroup.mk' _ c := by
    intro n c
    change (QuotientGroup.map (NK.GlobalCFT.Idele.normClassSubgroup K ↥(M (n + 1)).L)
        (NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L)
        (MonoidHom.id (NK.GlobalCFT.IdeleClassGroup K)) _)
        (QuotientGroup.mk' _ c) = QuotientGroup.mk' _ c
    rw [QuotientGroup.map_mk', QuotientGroup.mk'_apply]
    exact (QuotientGroup.mk'_apply _ c).symm
  let ρ : ∀ n, (NK.GlobalCFT.IdeleClassGroup K ⧸
        NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L) →*
        (NK.GlobalCFT.IdeleClassGroup K ⧸ U n) := fun n =>
    QuotientGroup.map (NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L) (U n)
      (MonoidHom.id (NK.GlobalCFT.IdeleClassGroup K)) (by simpa using hnorm n)
  have hρ_mk' : ∀ (n : ℕ) (c : NK.GlobalCFT.IdeleClassGroup K),
      ρ n (QuotientGroup.mk' _ c) = QuotientGroup.mk' _ c := by
    intro n c
    change (QuotientGroup.map (NK.GlobalCFT.Idele.normClassSubgroup K ↥(M n).L) (U n)
        (MonoidHom.id (NK.GlobalCFT.IdeleClassGroup K)) _)
        (QuotientGroup.mk' _ c) = QuotientGroup.mk' _ c
    rw [QuotientGroup.map_mk', QuotientGroup.mk'_apply]
    exact (QuotientGroup.mk'_apply _ c).symm
  have hρsurj : ∀ n, Function.Surjective (ρ n) := by
    intro n y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (U n) y
    exact ⟨QuotientGroup.mk' _ c, hρ_mk' n c⟩
  -- ## Step 7: the corrected compatible isomorphisms `C_K ⧸ U n ≅ (ℤ/2^n)^r`
  let G : ℕ → Type := fun n => NK.GlobalCFT.IdeleClassGroup K ⧸ U n
  haveI hGfin : ∀ n, Fintype (G n) := fun n =>
    Fintype.ofEquiv (Multiplicative (Fin r → ZMod (2 ^ n))) (hUlev n).some.symm.toEquiv
  let qG : ∀ n, G (n + 1) →* G n := fun n =>
    QuotientGroup.map (U (n + 1)) (U n) (MonoidHom.id (NK.GlobalCFT.IdeleClassGroup K))
      (by simpa using hUanti n)
  have hqG_mk' : ∀ (n : ℕ) (c : NK.GlobalCFT.IdeleClassGroup K),
      qG n (QuotientGroup.mk' _ c) = QuotientGroup.mk' _ c := by
    intro n c
    change (QuotientGroup.map (U (n + 1)) (U n)
        (MonoidHom.id (NK.GlobalCFT.IdeleClassGroup K)) _)
        (QuotientGroup.mk' _ c) = QuotientGroup.mk' _ c
    rw [QuotientGroup.map_mk', QuotientGroup.mk'_apply]
    exact (QuotientGroup.mk'_apply _ c).symm
  have hqG : ∀ n, Function.Surjective (qG n) := by
    intro n y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (U n) y
    exact ⟨QuotientGroup.mk' _ c, hqG_mk' n c⟩
  let Ht : ℕ → Type := fun n => Multiplicative (Fin r → ZMod (2 ^ n))
  let isoG : ∀ n, G n ≃* Multiplicative (Fin r → ZMod (2 ^ n)) := fun n => (hUlev n).some
  let isoH : ∀ n, Ht n ≃* Multiplicative (Fin r → ZMod (2 ^ n)) := fun n => MulEquiv.refl _
  let eGH : ∀ n, G n ≃* Ht n := fun n => (isoG n).trans (isoH n).symm
  obtain ⟨φ, hφ⟩ := hTower G Ht qG (fun n => towerRed r n) hqG
    (fun n => towerRed_surjective r n) isoG isoH eGH
  have hφ_fun : ∀ (n : ℕ) (w : NK.GlobalCFT.IdeleClassGroup K ⧸ U (n + 1)),
      φ n (qG n w) = towerRed r n (φ (n + 1) w) := by
    intro n w
    have h1 := congrFun (congrArg
      (fun f : G (n + 1) →* Multiplicative (Fin r → ZMod (2 ^ n)) => ⇑f) (hφ n)) w
    rwa [MonoidHom.comp_apply, MonoidHom.comp_apply] at h1
  -- ## Step 8: the level surjections `θ n : Γ_K ↠ (ℤ/2^n)^r`
  have hρnat_fun : ∀ (n : ℕ) (y : NK.GlobalCFT.IdeleClassGroup K ⧸
      NK.GlobalCFT.Idele.normClassSubgroup K ↥(M (n + 1)).L),
      ρ n (qN n y) = qG n (ρ (n + 1) y) := by
    intro n y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective
      (NK.GlobalCFT.Idele.normClassSubgroup K ↥(M (n + 1)).L) y
    rw [hqN_mk' n c, hρ_mk' n c, hρ_mk' (n + 1) c, hqG_mk' n c]
  have hαnat_fun : ∀ (n : ℕ) (y : NK.GlobalCFT.IdeleClassGroup K ⧸
      NK.GlobalCFT.Idele.normClassSubgroup K ↥(M (n + 1)).L),
      (α n) (qN n y) = (NK.Reconstruct.ellRestrict 2 (M n) (M (n + 1)) (hMle n))
        ((α (n + 1)) y) := by
    intro n y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective
      (NK.GlobalCFT.Idele.normClassSubgroup K ↥(M (n + 1)).L) y
    rw [hqN_mk' n c, hα_apply n c, hα_apply (n + 1) c]
    exact congrFun (congrArg (fun f : NK.GlobalCFT.IdeleClassGroup K →*
        ↥(NK.Reconstruct.LevelEllPart (M n).L 2) => ⇑f)
        (hcoh (M n) (M (n + 1)) (hMp n) (hMp (n + 1)) (hMle n))) c
  let θ' : ∀ n, ↥(NK.Reconstruct.LevelEllPart (M n).L 2) →*
      Multiplicative (Fin r → ZMod (2 ^ n)) :=
    fun n => (φ n).toMonoidHom.comp ((ρ n).comp (α n).symm.toMonoidHom)
  let θ : ∀ n, NK.Reconstruct.Gamma K Ω 2 →* Multiplicative (Fin r → ZMod (2 ^ n)) :=
    fun n => (θ' n).comp (NK.Reconstruct.Gamma.proj (M n))
  have hθc : ∀ n, Continuous ⇑(θ n) := by
    intro n
    have h1 : Continuous ⇑(θ' n) := continuous_of_discreteTopology
    exact h1.comp (NK.Reconstruct.continuous_proj 2 (M n))
  have hθs : ∀ n, Function.Surjective (θ n) := by
    intro n z
    obtain ⟨w, hw⟩ := (φ n).surjective z
    obtain ⟨y, hy⟩ := hρsurj n w
    obtain ⟨v, hv⟩ := (α n).symm.surjective y
    obtain ⟨x, hx⟩ := NK.Reconstruct.proj_surjective (K := K) (K' := Ω) 2 (M n) v
    refine ⟨x, ?_⟩
    change (φ n) (ρ n ((α n).symm (NK.Reconstruct.Gamma.proj (M n) x))) = z
    rw [hx, hv, hy, hw]
  have hθstep : ∀ (n : ℕ) (x : NK.Reconstruct.Gamma K Ω 2),
      θ n x = towerRed r n (θ (n + 1) x) := by
    intro n x
    have hproj := NK.Reconstruct.Gamma.proj_compatible (M n) (M (n + 1)) (hMle n) x
    have hαy : (α (n + 1)) ((α (n + 1)).symm (NK.Reconstruct.Gamma.proj (M (n + 1)) x))
        = NK.Reconstruct.Gamma.proj (M (n + 1)) x := MulEquiv.apply_symm_apply _ _
    have hkey : (α n) (qN n ((α (n + 1)).symm (NK.Reconstruct.Gamma.proj (M (n + 1)) x)))
        = NK.Reconstruct.Gamma.proj (M n) x := by
      rw [hαnat_fun n ((α (n + 1)).symm (NK.Reconstruct.Gamma.proj (M (n + 1)) x)),
        hαy, hproj]
    have hsymm : (α n).symm (NK.Reconstruct.Gamma.proj (M n) x)
        = qN n ((α (n + 1)).symm (NK.Reconstruct.Gamma.proj (M (n + 1)) x)) := by
      rw [← hkey, MulEquiv.symm_apply_apply]
    change (φ n) (ρ n ((α n).symm (NK.Reconstruct.Gamma.proj (M n) x)))
        = towerRed r n ((φ (n + 1)) (ρ (n + 1)
            ((α (n + 1)).symm (NK.Reconstruct.Gamma.proj (M (n + 1)) x))))
    rw [hsymm, hρnat_fun, hφ_fun]
  refine le_dualRank_gamma_of_compatible_levelHom r Ω K θ hθc hθs ?_
  intro n x
  rw [hθstep n x, towerRed_toAdd]

end NK.NUV2.TowerRank
