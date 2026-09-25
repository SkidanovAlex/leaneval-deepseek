import Mathlib
import Submission.NK.NUV2.TowerRank.towerIso
import Submission.NK.NUV2.TowerRank.towerCompatible
import Submission.NK.NUV2.TowerRank.le_dualRank_gamma_of_nested_levels
import Submission.NK.NUV2.Idg.exists_continuous_surjective_of_le_dualRank
import Submission.NK.NUV2.Idg.exists_nested_levels_of_nested_gamma_subgroups
import Submission.NK.NUV2.ArtinBridge.isOpen_normClassSubgroup
import Submission.NK.NUV2.ArtinBridge.normClassSubgroup_le_of_intermediateField_le
import Submission.NK.NUV2.ArtinBridge.dualEquivOfKills
import Submission.NK.RankTheoryDeep.exists_addHom_padicInt_lift
import Submission.NK.RankTheoryDeep.continuous_of_toZModPow_comp
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.NK.Reconstruct.galToGamma_continuous

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped Topology

namespace NK.NUV2.TowerRank

noncomputable section

/-! ## The reduction `ℤ_2^r → (ℤ/2^n)^r` -/

/-- **The reduction `ℤ_2^r → (ℤ/2^n)^r`**, as a homomorphism of the multiplicative groups. -/
def redMul (r n : ℕ) :
    Multiplicative (Fin r → PadicInt 2) →* Multiplicative (Fin r → ZMod (2 ^ n)) :=
  AddMonoidHom.toMultiplicative
    { toFun := fun x i => PadicInt.toZModPow (p := 2) n (x i)
      map_zero' := by funext i; simp
      map_add' := fun a b => by funext i; simp }

@[simp] theorem redMul_toAdd (r n : ℕ) (x : Multiplicative (Fin r → PadicInt 2)) :
    (redMul r n x).toAdd = fun i => PadicInt.toZModPow (p := 2) n (x.toAdd i) := rfl

/-- `PadicInt.toZModPow n` is surjective. -/
theorem toZModPow_surjective (n : ℕ) : Function.Surjective (PadicInt.toZModPow (p := 2) n) := by
  intro y
  refine ⟨((y.val : ℕ) : ℤ_[2]), ?_⟩
  rw [map_natCast]
  exact ZMod.natCast_zmod_val y

/-- The reduction `ℤ_2^r → (ℤ/2^n)^r` is surjective. -/
theorem redMul_surjective (r n : ℕ) : Function.Surjective (redMul r n) := by
  intro y
  have hy : ∀ i : Fin r, ∃ x : PadicInt 2, PadicInt.toZModPow (p := 2) n x = y.toAdd i :=
    fun i => toZModPow_surjective n (y.toAdd i)
  choose x hx using hy
  refine ⟨Multiplicative.ofAdd x, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  rw [redMul_toAdd]
  exact hx i

/-- The reduction `ℤ_2^r → (ℤ/2^n)^r` is continuous. -/
theorem continuous_redMul (r n : ℕ) : Continuous ⇑(redMul r n) := by
  have h : ⇑(redMul r n) = fun x : Multiplicative (Fin r → PadicInt 2) =>
      fun i => PadicInt.toZModPow (p := 2) n (x.toAdd i) := rfl
  rw [h]
  exact continuous_pi fun i =>
    (NK.NUV2.ArtinBridge.DualKillsAux.continuous_padicInt_toZModPow 2 n).comp
      (continuous_apply i)

/-- The reductions are compatible with the transition maps of the standard tower. -/
theorem redMul_comp_apply (r m n : ℕ) (hmn : m ≤ n)
    (y : Multiplicative (Fin r → PadicInt 2)) :
    (redMul r m y).toAdd = coordRed r m n ((redMul r n y).toAdd) := by
  funext i
  rw [redMul_toAdd, redMul_toAdd, coordRed_apply, redAdd_of_le hmn]
  exact (congrFun (congrArg (fun f : PadicInt 2 →+* ZMod (2 ^ m) => ⇑f)
    (PadicInt.zmod_cast_comp_toZModPow m n hmn)) (y.toAdd i)).symm

/-- Composing the reductions. -/
theorem redMul_comp (r m n : ℕ) (hmn : m ≤ n) :
    redMul r m = (AddMonoidHom.toMultiplicative (coordRed r m n)).comp (redMul r n) := by
  refine MonoidHom.ext fun y => Multiplicative.toAdd.injective (funext fun i => ?_)
  rw [MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply]
  exact congrFun (redMul_comp_apply r m n hmn y) i


/-- **Evaluation of a continuous `ℤ_2`-valued character at a point**, as a `ℤ_2`-linear map. -/
def evalLinear (G : Type*) [CommGroup G] [TopologicalSpace G] (x : G) :
    NK.Reconstruct.Dual G 2 →ₗ[PadicInt 2] PadicInt 2 where
  toFun u := u.1 (Additive.ofMul x)
  map_add' u v := rfl
  map_smul' a u := NK.RankTheoryDeep.smul_dual_apply a u (Additive.ofMul x)

@[simp] theorem evalLinear_apply {G : Type*} [CommGroup G] [TopologicalSpace G] (x : G)
    (u : NK.Reconstruct.Dual G 2) : evalLinear G x u = u.1 (Additive.ofMul x) := rfl

/-! ## The half (A) of `ArtinDualBridge` -/

theorem le_dualRank_idele_of_gamma (r : ℕ) (hTower : NK.NUV2.TowerRank.TowerCompatible r)
    (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsGalois K Ω]
    (h : (r : Cardinal) ≤ NK.RankTheoryDeep.dualRank (NK.Reconstruct.Gamma K Ω 2) 2) :
    (r : Cardinal) ≤ NK.RankTheoryDeep.dualRank (NK.GlobalCFT.IdeleClassGroup K) 2 := by
  classical
  -- ## Step 1: a continuous surjection `Γ_K ↠ ℤ_2^r`
  obtain ⟨Φ, hΦc, hΦs⟩ :=
    NK.NUV2.Idg.exists_continuous_surjective_of_le_dualRank (G := NK.Reconstruct.Gamma K Ω 2) r h
  -- ## Step 2: the tower of open subgroups of `Γ_K` with quotients `(ℤ/2^n)^r`
  let Φn : ∀ n, NK.Reconstruct.Gamma K Ω 2 →* Multiplicative (Fin r → ZMod (2 ^ n)) :=
    fun n => (redMul r n).comp Φ
  have hΦnc : ∀ n, Continuous ⇑(Φn n) := fun n => (continuous_redMul r n).comp hΦc
  have hΦns : ∀ n, Function.Surjective (Φn n) := fun n => (redMul_surjective r n).comp hΦs
  let W : ℕ → Subgroup (NK.Reconstruct.Gamma K Ω 2) := fun n => (Φn n).ker
  have hWopen : ∀ n, IsOpen (W n : Set (NK.Reconstruct.Gamma K Ω 2)) := fun n => by
    show IsOpen ((Φn n) ⁻¹' ({1} : Set (Multiplicative (Fin r → ZMod (2 ^ n)))))
    exact (hΦnc n).isOpen_preimage _ (isOpen_discrete _)
  have hanti : ∀ n, W (n+1) ≤ W n := by
    intro n x hx
    have hx' : (redMul r (n+1)) (Φ x) = 1 := by
      simpa only [W, MonoidHom.mem_ker, Φn, MonoidHom.comp_apply] using hx
    have hx2 : ((redMul r (n+1)) (Φ x)).toAdd = 0 := by
      rw [hx']
      rfl
    have h3 := redMul_comp_apply r n (n+1) (Nat.le_succ n) (Φ x)
    rw [hx2, map_zero] at h3
    simp only [W, MonoidHom.mem_ker, Φn, MonoidHom.comp_apply]
    exact Multiplicative.toAdd.injective (by rw [h3]; rfl)
  have hlev : ∀ n, Nonempty ((NK.Reconstruct.Gamma K Ω 2 ⧸ W n) ≃*
      Multiplicative (Fin r → ZMod (2 ^ n))) := fun n =>
    ⟨QuotientGroup.quotientKerEquivOfSurjective (Φn n) (hΦns n)⟩
  -- ## Step 3: the levels
  obtain ⟨L, hnest, hgalL, hGalIso⟩ :=
    NK.NUV2.Idg.exists_nested_levels_of_nested_gamma_subgroups r Ω K W hanti hWopen hlev
  haveI hLgal : ∀ n, IsGalois K ↥(L n).L := hgalL
  -- ## Step 4: the norm subgroups and the `C_K`-side isomorphisms
  let N : ℕ → Subgroup (NK.GlobalCFT.IdeleClassGroup K) := fun n =>
    NK.GlobalCFT.Idele.normClassSubgroup K ↥(L n).L
  haveI hNn : ∀ n, (N n).Normal := fun n => Subgroup.normal_of_isMulCommutative _
  have hNopen : ∀ n, IsOpen (N n : Set (NK.GlobalCFT.IdeleClassGroup K)) := fun n =>
    NK.NUV2.ArtinBridge.isOpen_normClassSubgroup
  have hNanti : ∀ n, N (n+1) ≤ N n := fun n =>
    NK.NUV2.ArtinBridge.normClassSubgroup_le_of_intermediateField_le (L n).L (L (n+1)).L
      (hnest n)
  haveI hLcomm : ∀ n, IsMulCommutative (↥(L n).L ≃ₐ[K] ↥(L n).L) := fun n =>
    ⟨⟨fun a b => by
      obtain ⟨e⟩ := hGalIso n
      refine e.injective ?_
      simp only [map_mul]
      exact mul_comm _ _⟩⟩
  let hIso : ∀ n, (NK.GlobalCFT.IdeleClassGroup K ⧸ N n) ≃*
      Multiplicative (Fin r → ZMod (2 ^ n)) := fun n =>
    (NK.GlobalCFTdeep.artinReciprocity_of_fundamentalClassElement hFC (K := K)
        (L := ↥(L n).L)).iso.trans (hGalIso n).some
  -- ## Step 5: the compatibility of the two towers
  let H : ℕ → Type := fun n => NK.GlobalCFT.IdeleClassGroup K ⧸ N n
  haveI hHfin : ∀ n, Fintype (H n) := fun n =>
    Fintype.ofEquiv (Multiplicative (Fin r → ZMod (2 ^ n))) (hIso n).symm
  let qH : ∀ n, H (n+1) →* H n := fun n =>
    QuotientGroup.lift (N (n+1)) (QuotientGroup.mk' (N n))
      (by intro x hx; rw [QuotientGroup.ker_mk']; exact hNanti n hx)
  have hqH : ∀ n, Function.Surjective (qH n) := by
    intro n y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N n) y
    exact ⟨QuotientGroup.mk' (N (n+1)) x, by
      rw [QuotientGroup.mk'_apply]
      exact QuotientGroup.lift_mk' _ _ x⟩
  let G : ℕ → Type := fun n => Multiplicative (Fin r → ZMod (2 ^ n))
  let isoG : ∀ n, G n ≃* Multiplicative (Fin r → ZMod (2 ^ n)) := fun n => MulEquiv.refl _
  let eGH : ∀ n, G n ≃* H n := fun n => (isoG n).trans (hIso n).symm
  obtain ⟨φ, hφ⟩ := hTower G H (fun n => towerRed r n) qH
    (fun n => towerRed_surjective r n) hqH isoG hIso eGH
  -- ## Step 6: the maps `C_K → (ℤ/2^n)^r`
  let ψ : ∀ n, NK.GlobalCFT.IdeleClassGroup K →* Multiplicative (Fin r → ZMod (2 ^ n)) :=
    fun n => (φ n).symm.toMonoidHom.comp (QuotientGroup.mk' (N n))
  have hψsurj : ∀ n, Function.Surjective (ψ n) := fun n =>
    (φ n).symm.surjective.comp (QuotientGroup.mk'_surjective (N n))
  have hψcont : ∀ n, Continuous ⇑(ψ n) := by
    intro n
    haveI : DiscreteTopology (NK.GlobalCFT.IdeleClassGroup K ⧸ N n) :=
      QuotientGroup.discreteTopology (hNopen n)
    have h1 : Continuous fun y : NK.GlobalCFT.IdeleClassGroup K ⧸ N n => (φ n).symm y :=
      continuous_of_discreteTopology
    have h2 : Continuous (QuotientGroup.mk' (N n) :
        NK.GlobalCFT.IdeleClassGroup K → NK.GlobalCFT.IdeleClassGroup K ⧸ N n) := by
      rw [QuotientGroup.coe_mk']
      exact QuotientGroup.continuous_mk
    exact h1.comp h2
  -- the level-by-level coherence of `ψ`
  have hψstep : ∀ n (x : NK.GlobalCFT.IdeleClassGroup K),
      ψ n x = towerRed r n (ψ (n+1) x) := by
    intro n x
    refine (φ n).injective ?_
    have h1 : (φ n) (ψ n x) = QuotientGroup.mk' (N n) x :=
      MulEquiv.apply_symm_apply (φ n) _
    have h2 : (φ n) (towerRed r n (ψ (n+1) x)) = QuotientGroup.mk' (N n) x := by
      have hpoint := DFunLike.congr_fun (hφ n) (ψ (n+1) x)
      have h3 : (φ n) (towerRed r n (ψ (n+1) x))
          = qH n (φ (n+1) (ψ (n+1) x)) := hpoint
      rw [h3]
      have h4 : (φ (n+1)) (ψ (n+1) x) = QuotientGroup.mk' (N (n+1)) x :=
        MulEquiv.apply_symm_apply (φ (n+1)) _
      rw [h4]
      rw [QuotientGroup.mk'_apply]
      exact QuotientGroup.lift_mk' _ _ x
    rw [h1, h2]
  have hψcompat : ∀ n (x : NK.GlobalCFT.IdeleClassGroup K),
      (ψ n x).toAdd = coordRed r n (n+1) ((ψ (n+1) x).toAdd) := by
    intro n x
    rw [hψstep n x, towerRed_toAdd]
  have hψcompatmn : ∀ (m n : ℕ) (hmn : m ≤ n) (x : NK.GlobalCFT.IdeleClassGroup K),
      (ψ m x).toAdd = coordRed r m n ((ψ n x).toAdd) := by
    intro m n hmn x
    have key : ∀ k (hmk : m ≤ k), (ψ m x).toAdd = coordRed r m k ((ψ k x).toAdd) := by
      intro k hmk
      induction k, hmk using Nat.le_induction with
      | base => rw [coordRed_self]
      | succ j hmj ih =>
          rw [ih, hψcompat j x]
          exact coordRed_comp r m j (j + 1) hmj (Nat.le_succ j) ((ψ (j + 1) x).toAdd)
    exact key n hmn
  -- ## Step 7: the coordinates and their lifts to `ℤ_2`
  let Fi : ∀ (i : Fin r) (n : ℕ),
      Additive (NK.GlobalCFT.IdeleClassGroup K) →+ ZMod (2 ^ n) :=
    fun i n => (Pi.evalAddMonoidHom (fun _ : Fin r => ZMod (2 ^ n)) i).comp
      (MonoidHom.toAdditive (ψ n))
  have hFi_apply : ∀ (i : Fin r) (n : ℕ) (x : Additive (NK.GlobalCFT.IdeleClassGroup K)),
      Fi i n x = (ψ n (Additive.toMul x)).toAdd i := fun i n x => rfl
  have hcontFi : ∀ (i : Fin r) (n : ℕ), Continuous ⇑(Fi i n) := by
    intro i n
    have h2 : Continuous fun y : Multiplicative (Fin r → ZMod (2 ^ n)) => y.toAdd i :=
      continuous_of_discreteTopology
    have h3 : ⇑(Fi i n) = fun x : Additive (NK.GlobalCFT.IdeleClassGroup K) =>
        (ψ n (Additive.toMul x)).toAdd i := rfl
    rw [h3]
    exact h2.comp (hψcont n)
  have hcastcompat : ∀ (i : Fin r) (m n : ℕ) (hmn : m ≤ n)
      (x : Additive (NK.GlobalCFT.IdeleClassGroup K)),
      Fi i m x = ZMod.castHom (pow_dvd_pow 2 hmn) (ZMod (2 ^ m)) (Fi i n x) := by
    intro i m n hmn x
    rw [hFi_apply i n x]
    have h1 : Fi i m x = coordRed r m n ((ψ n (Additive.toMul x)).toAdd) i := by
      rw [hFi_apply i m x]
      exact congrFun (hψcompatmn m n hmn (Additive.toMul x)) i
    rw [h1, coordRed_apply, redAdd_of_le hmn]
  have hlift : ∀ i : Fin r, ∃ g : Additive (NK.GlobalCFT.IdeleClassGroup K) →+ PadicInt 2,
      ∀ (n : ℕ) (x : Additive (NK.GlobalCFT.IdeleClassGroup K)),
        PadicInt.toZModPow n (g x) = Fi i n x := fun i =>
    NK.RankTheoryDeep.exists_addHom_padicInt_lift (Fi i) (fun m n hmn x => hcastcompat i m n hmn x)
  choose χhom hχhom using hlift
  have hcontχ : ∀ i : Fin r, Continuous ⇑(χhom i) := fun i =>
    NK.RankTheoryDeep.continuous_of_toZModPow_comp (χhom i) (Fi i) (fun n => hcontFi i n)
      (fun n x => hχhom i n x)
  let χ : Fin r → NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup K) 2 :=
    fun i => ⟨χhom i, hcontχ i⟩
  -- ## Step 8: the characters are `ℤ_2`-linearly independent
  have hkey : ∀ (i : Fin r) (n : ℕ) (x : NK.GlobalCFT.IdeleClassGroup K),
      PadicInt.toZModPow n ((χ i).1 (Additive.ofMul x)) = (ψ n x).toAdd i := by
    intro i n x
    rw [hχhom i n (Additive.ofMul x), hFi_apply]
    rfl
  have hindep : LinearIndependent (PadicInt 2) χ := by
    rw [linearIndependent_iff']
    intro s g hg j hj
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    obtain ⟨x, hx⟩ := hψsurj n
      (Multiplicative.ofAdd (fun i : Fin r => if i = j then 1 else 0))
    have hx' : (ψ n x).toAdd = fun i => if i = j then 1 else 0 := by
      rw [hx]
      rfl
    have hval : ∑ i ∈ s, g i * (χ i).1 (Additive.ofMul x) = 0 := by
      have h4 : (∑ i ∈ s, (evalLinear (NK.GlobalCFT.IdeleClassGroup K) x) (g i • χ i)) = 0 := by
        have h5 := congrArg (evalLinear (NK.GlobalCFT.IdeleClassGroup K) x) hg
        simpa only [map_sum, map_zero] using h5
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_smul, smul_eq_mul])] at h4
      exact h4
    have hval2 : ∑ i ∈ s, PadicInt.toZModPow n (g i) * ((ψ n x).toAdd i) = 0 := by
      have h := congrArg (fun u : PadicInt 2 => PadicInt.toZModPow (p := 2) n u) hval
      rw [map_zero, map_sum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul]
      congr 1
      exact (hkey i n x).symm
    rw [hx'] at hval2
    simp only [mul_ite, mul_one, mul_zero] at hval2
    rw [Finset.sum_ite_eq' s j (fun i : Fin r => PadicInt.toZModPow (p := 2) n (g i))] at hval2
    rw [if_pos hj] at hval2
    simpa using hval2
  rw [NK.RankTheoryDeep.dualRank]
  exact Module.le_rank_iff.mpr ⟨χ, hindep⟩

end

end NK.NUV2.TowerRank
