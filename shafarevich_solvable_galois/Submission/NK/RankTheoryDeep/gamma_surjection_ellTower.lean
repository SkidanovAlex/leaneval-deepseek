import Mathlib
import Submission.NK.RankTheoryDeep.ProductRank
import Submission.NK.RankTheoryDeep.TowerArc
import Submission.NK.RankTheoryDeep.expHom_surjective
import Submission.NK.RankTheoryDeep.exists_linearMap_of_groupHom
import Submission.NK.RankTheoryDeep.jointHom_surjective
import Submission.NK.RankTheoryDeep.levelCoordHom_ellRestrict
import Submission.NK.Reconstruct.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Γ_ℚ` maps onto the `2`-adic tower product
-/

attribute [local instance 10] DivisionRing.toRatAlgebra

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.RankTheoryDeep

open scoped Pointwise

universe u

section Assembly

variable (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The joint level map is surjective.**  Every element of the product `∏_{n < N} Multiplicative
(ZMod (2 ^ (n + 1)))` is of `2`-power order, so the surjectivity of the joint map on the abelianised
level passes to its `2`-primary part. -/
theorem jointLevelHom_surjective_self (N : ℕ) : Function.Surjective (jointLevelHom Ω N) := by
  intro y
  have hsurj : Function.Surjective (Abelianization.lift (jointHom Ω N)) := by
    intro w
    obtain ⟨σ, hσ⟩ := jointHom_surjective Ω N w
    exact ⟨Abelianization.of σ, by rw [Abelianization.lift_apply_of]; exact hσ⟩
  have hy : y ∈ NK.Reconstruct.ellPart
      (∀ n : Fin N, Multiplicative (ZMod (2 ^ (n.val + 1)))) 2 := by
    rw [NK.Reconstruct.mem_ellPart_iff]
    refine ⟨Finset.univ.sup fun n : Fin N => n.val + 1, ?_⟩
    funext n
    simp only [Pi.pow_apply, Pi.one_apply]
    obtain ⟨d, hd⟩ : ∃ d, Finset.univ.sup (fun n : Fin N => n.val + 1) = (n.val + 1) + d :=
      ⟨_, (Nat.add_sub_cancel' (Finset.le_sup (Finset.mem_univ n))).symm⟩
    have h2 : 2 ^ (n.val + 1 + d) = 2 ^ (n.val + 1) * 2 ^ d := by rw [pow_add]
    rw [hd, h2, pow_mul]
    have h1 : (y n) ^ (2 ^ (n.val + 1)) = 1 := by
      have h := pow_card_eq_one (x := y n)
      rwa [Fintype.card_multiplicative, ZMod.card] at h
    rw [h1, one_pow]
  obtain ⟨z, hzmem, hz⟩ := NK.Reconstruct.projSurj_ellPart_map_surj 2
    (Abelianization.lift (jointHom Ω N)) hsurj y hy
  exact ⟨⟨z, hzmem⟩, hz⟩


/-- The linear form of the `n`-th coordinate map of the `N`-th level. -/
noncomputable def levelCoordLin (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) :
    Additive (NK.Reconstruct.LevelEllPart (cycLevel Ω N).L 2) →ₗ[PadicInt 2] ZMod (2 ^ n) :=
  Classical.choose (exists_linearMap_of_groupHom (levelCoordHom Ω n N hn hN))

theorem levelCoordLin_apply (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N)
    (x : NK.Reconstruct.LevelEllPart (cycLevel Ω N).L 2) :
    levelCoordLin Ω n N hn hN (Additive.ofMul x)
      = (levelCoordHom Ω n N hn hN x : ZMod (2 ^ n)) :=
  Classical.choose_spec (exists_linearMap_of_groupHom (levelCoordHom Ω n N hn hN)) x

/-- The additive projection `Γ_ℚ → Γ_{L,2}`. -/
noncomputable def projAdd (L : NK.Reconstruct.FrobLevel ℚ Ω) :
    Additive (NK.Reconstruct.Gamma ℚ Ω 2) →ₗ[PadicInt 2]
      Additive (NK.Reconstruct.LevelEllPart L.L 2) where
  toFun x := Additive.ofMul (NK.Reconstruct.Gamma.proj L (Additive.toMul x))
  map_add' a b := rfl
  map_smul' c x := rfl

theorem projAdd_apply (L : NK.Reconstruct.FrobLevel ℚ Ω)
    (x : Additive (NK.Reconstruct.Gamma ℚ Ω 2)) :
    projAdd Ω L x = Additive.ofMul (NK.Reconstruct.Gamma.proj L (Additive.toMul x)) := rfl

theorem projAdd_surjective (L : NK.Reconstruct.FrobLevel ℚ Ω) :
    Function.Surjective (projAdd Ω L) := by
  intro z
  obtain ⟨f, hf⟩ := NK.Reconstruct.proj_surjective (K := ℚ) (K' := Ω) 2 L (Additive.toMul z)
  exact ⟨Additive.ofMul f,
    by rw [projAdd_apply, toMul_ofMul, hf, ofMul_toMul]⟩

theorem continuous_projAdd (L : NK.Reconstruct.FrobLevel ℚ Ω) : Continuous (projAdd Ω L) :=
  continuous_ofMul.comp
    ((NK.Reconstruct.continuous_proj (ℓ := 2) L).comp (continuous_toMul (X := NK.Reconstruct.Gamma ℚ Ω 2)))

/-- The `n`-th coordinate linear form on `Γ_ℚ`. -/
noncomputable def PhiCoord (n : ℕ) :
    Additive (NK.Reconstruct.Gamma ℚ Ω 2) →ₗ[PadicInt 2] ZMod (2 ^ n) :=
  if h : 1 ≤ n then (levelCoordLin Ω n n h le_rfl).comp (projAdd Ω (cycLevel Ω n)) else 0

theorem PhiCoord_apply (n : ℕ) (hn : 1 ≤ n) (x : Additive (NK.Reconstruct.Gamma ℚ Ω 2)) :
    PhiCoord Ω n x
      = levelCoordLin Ω n n hn le_rfl (projAdd Ω (cycLevel Ω n) x) := by
  simp only [PhiCoord, dif_pos hn, LinearMap.comp_apply]

theorem continuous_PhiCoord (n : ℕ) : Continuous (PhiCoord Ω n) := by
  by_cases hn : 1 ≤ n
  · rw [PhiCoord, dif_pos hn]
    exact (continuous_of_discreteTopology : Continuous (levelCoordLin Ω n n hn le_rfl)).comp
      (continuous_projAdd Ω (cycLevel Ω n))
  · rw [PhiCoord, dif_neg hn]
    exact continuous_const

/-- **The components of the joint level map**: the `n`-th component of `jointLevelHom` is the
coordinate map of the level. -/
theorem jointLevelHom_apply (N : ℕ) (z : NK.Reconstruct.LevelEllPart (cycLevel Ω N).L 2)
    (n : Fin N) :
    jointLevelHom Ω N z n
      = Multiplicative.ofAdd ((levelCoordHom Ω (n.val + 1) N (by omega) (by omega) z :
          ZMod (2 ^ (n.val + 1)))) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(↥(cycLevel Ω N).L/ℚ),
      Abelianization.of σ = Subgroup.subtype _ z :=
    QuotientGroup.mk_surjective (Subgroup.subtype _ z)
  have h1 : jointLevelHom Ω N z = jointHom Ω N σ := by
    show (Abelianization.lift (jointHom Ω N)).comp (Subgroup.subtype _) z = jointHom Ω N σ
    rw [MonoidHom.comp_apply, ← hσ, Abelianization.lift_apply_of]
  have h2 : (levelCoordHom Ω (n.val + 1) N (by omega) (by omega)) z
      = coordPrime (n.val + 1) N (by omega) (by omega) (expHom Ω N σ) := by
    show (coordPrime (n.val + 1) N (by omega) (by omega)).comp
      ((Abelianization.lift (expHom Ω N)).comp (Subgroup.subtype _)) z = _
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← hσ, Abelianization.lift_apply_of]
  rw [h1, h2]
  rfl

/-- **The first `N` coordinates of `Φ` are surjective.**  The joint map
`Γ_ℚ → ∏_{n ≤ N} ℤ/2 ^ n` factors through the projection to the `N`-th level, where it is the
product of the coordinate characters, which is onto because the `N`-th level is
`ℚ(ζ_{q 0 ⋯ q (N-1)})` with `Gal ≅ ∏_i (ℤ/q i)^×` (CRT) and each `(ℤ/q i)^×` has order divisible by
`2 ^ (i + 1)`. -/
theorem jointSurjective (N : ℕ) :
    Function.Surjective (fun x : Additive (NK.Reconstruct.Gamma ℚ Ω 2) =>
      fun n : Fin N => PhiCoord Ω (n.val + 1) x) := by
  intro y
  obtain ⟨z, hz⟩ := jointLevelHom_surjective_self Ω N (fun n : Fin N => Multiplicative.ofAdd (y n))
  obtain ⟨x, hx⟩ := projAdd_surjective Ω (cycLevel Ω N) z
  refine ⟨x, funext fun n => ?_⟩
  show PhiCoord Ω (n.val + 1) x = y n
  rw [PhiCoord_apply Ω (n.val + 1) (by omega)]
  have hsmall : projAdd Ω (cycLevel Ω (n.val + 1)) x
      = Additive.ofMul (NK.Reconstruct.ellRestrict 2 (cycLevel Ω (n.val + 1)) (cycLevel Ω N)
          (cycLevel_mono Ω (by omega)) (Additive.toMul (projAdd Ω (cycLevel Ω N) x))) := by
    rw [projAdd_apply, projAdd_apply]
    congr 1
    exact (NK.Reconstruct.Gamma.proj_compatible (cycLevel Ω (n.val + 1)) (cycLevel Ω N)
      (cycLevel_mono Ω (by omega)) (Additive.toMul x)).symm
  rw [hsmall, levelCoordLin_apply]
  rw [← MonoidHom.comp_apply, levelCoordHom_ellRestrict Ω (n := n.val + 1) (N := N)
    (by omega) (by omega)]
  rw [hx]
  have h3 := jointLevelHom_apply Ω N z n
  rw [hz] at h3
  have h4 : ((levelCoordHom Ω (n.val + 1) N (by omega) (by omega)) z : ZMod (2 ^ (n.val + 1)))
      = y n := by
    exact Multiplicative.ofAdd.injective h3.symm
  exact h4

/-- **`Φ`**: the `ℤ_2`-linear map `Γ_ℚ → ∏_n ℤ/2 ^ n` whose `n`-th coordinate is the `n`-th
coordinate character of the level `ℚ(ζ_{towerMod n})`. -/
noncomputable def Phi : Additive (NK.Reconstruct.Gamma ℚ Ω 2) →ₗ[PadicInt 2] EllTower 2 :=
  LinearMap.pi (fun n => PhiCoord Ω n)

theorem Phi_apply (x : Additive (NK.Reconstruct.Gamma ℚ Ω 2)) (n : ℕ) :
    Phi Ω x n = PhiCoord Ω n x := rfl

/-- **`Φ` is surjective.**  For `y ∈ ∏_n ℤ/2 ^ n` the sets
`U N = {x | ∀ n ≤ N, Φ x n = y n}` are closed (continuity of the coordinates), nested and
nonempty (by `jointSurjective`), so by compactness of `Γ_ℚ` their intersection is nonempty; any
element of it maps to `y`. -/
theorem Phi_surjective : Function.Surjective (Phi Ω) := by
  intro y
  set U : ℕ → Set (Additive (NK.Reconstruct.Gamma ℚ Ω 2)) :=
    fun N => {x | ∀ n ≤ N, PhiCoord Ω n x = y n} with hU
  have hUclosed : ∀ N, IsClosed (U N) := by
    intro N
    have hset : U N = ⋂ n ∈ Finset.range (N + 1), {x | PhiCoord Ω n x = y n} := by
      ext x
      rw [hU]
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range]
      exact ⟨fun h n hn => h n (by omega), fun h n hn => h n (by omega)⟩
    rw [hset]
    exact isClosed_iInter fun n => isClosed_iInter fun _ =>
      isClosed_eq (continuous_PhiCoord Ω n) continuous_const
  have hUne : ∀ N, (U N).Nonempty := by
    intro N
    obtain ⟨x, hx⟩ := jointSurjective Ω N (fun n : Fin N => y (n.val + 1))
    refine ⟨x, ?_⟩
    rw [hU]
    intro n hn
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      haveI : Subsingleton (ZMod (2 ^ 0)) := (ZMod.subsingleton_iff (n := 2 ^ 0)).mpr rfl
      exact Subsingleton.elim _ _
    · have h1 := congrFun hx (⟨n - 1, by omega⟩ : Fin N)
      have h2 : ((⟨n - 1, by omega⟩ : Fin N).val + 1) = n := by
        simp [Nat.sub_add_cancel hnpos]
      exact h2 ▸ h1
  have hmono : ∀ {N N' : ℕ}, N ≤ N' → U N' ⊆ U N := by
    intro N N' h x hx
    rw [hU] at hx ⊢
    exact fun n hn => hx n (le_trans hn h)
  have hfip : ∀ u : Finset ℕ, (⋂ N ∈ u, U N).Nonempty := by
    intro u
    obtain ⟨x, hx⟩ := hUne (u.sup id)
    exact ⟨x, Set.mem_iInter₂.mpr fun N hN => hmono (Finset.le_sup (f := id) hN) hx⟩
  have hne : (⋂ N, U N).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    obtain ⟨u, hu⟩ := isCompact_univ.elim_finite_subfamily_closed U hUclosed (by simpa using hcon)
    obtain ⟨x, hx⟩ := hfip u
    exact Set.disjoint_left.mp hu (Set.mem_univ x) hx
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, funext fun n => ?_⟩
  have h1 : x ∈ U n := Set.mem_iInter.mp hx n
  rw [hU] at h1
  exact h1 n le_rfl

/-- **The ℓ-adic tower product is a quotient of `Γ_ℚ`.**

`NK.RankTheoryDeep.EllTower 2 = ∀ n : ℕ, ZMod (2 ^ n)` is the product of the cyclic `2`-groups of
unbounded exponent, endowed with the `ℤ_2`-module structure in which `a : ℤ_2` acts on the `n`-th
factor through the reduction `PadicInt.toZModPow n a`
(`NK.RankTheoryDeep.instModulePadicIntZModPow`), and `NK.Reconstruct.Gamma ℚ Ω 2` is
Shimizu's `Γ_ℚ`, the projective limit of the `2`-parts of the abelianisations of the finite Galois
levels of `Ω/ℚ` (`Submission/Work/Reconstruct/GammaObject.lean`).

The statement says that there is a **surjective `ℤ_2`-linear map `Γ_ℚ ↠ ∏_n ℤ/2^n`**.

Why it is true: take distinct odd primes `q_n` with `2^{n+1} ∣ q_n - 1` (e.g. a prime divisor of the
Fermat number `2^{2^n}+1`); the nested tower `M_N = ℚ(ζ_{q_0 ⋯ q_N})` of cyclotomic fields has
`Gal(M_N/ℚ) ≅ (ℤ/q_0⋯q_N)^× ≅ ∏_{i≤N}(ℤ/q_i)^×` by CRT, and each `(ℤ/q_i)^×` is *cyclic* of order
`q_i - 1`, so its `2`-part is `ℤ/2^{v₂(q_i-1)}` with `v₂(q_i-1) ≥ i+1`.  Hence
`Γ_{M_N} ≅ ∏_{i≤N} ℤ/2^{v₂(q_i-1)}`, the transition maps are the projections, and reducing
`ℤ/2^{v₂(q_i-1)} → ℤ/2^{i+1}` gives a compatible family of surjections and, in the limit, a
surjection `Γ_ℚ ↠ ∏_i ℤ/2^{i+1}`; reindexing gives `EllTower 2`.  The maps are `ℤ_2`-linear because
the reduction `ℤ/2^m → ℤ/2^n` for `n ≤ m` is compatible with `PadicInt.toZModPow`
(`PadicInt.zmod_cast_comp_toZModPow`), and `Γ_ℚ → Γ_L` is `ℤ_2`-linear by construction
(`NK.Reconstruct.projAdd`).  Surjectivity of `Γ_ℚ → lim_N Γ_{M_N}` needs no cofinality: the image
is compact, hence closed, and projects onto every finite stage.

This is the *arithmetic crux* of the refutation of `NK.ShimizuRank.GammaTFRankFinite`: combined
with `NK.RankTheoryDeep.aleph0_le_rank_of_surjective_tower` it shows
`ℵ₀ ≤ rank_{ℤ_2} (Γ_ℚ ⧸ torsion)`. -/
theorem gamma_surjection_ellTower (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] :
    ∃ Φ : Additive (NK.Reconstruct.Gamma ℚ Ω 2) →ₗ[PadicInt 2] NK.RankTheoryDeep.EllTower 2,
      Function.Surjective Φ :=
  ⟨Phi Ω, Phi_surjective Ω⟩

end Assembly

end NK.RankTheoryDeep
