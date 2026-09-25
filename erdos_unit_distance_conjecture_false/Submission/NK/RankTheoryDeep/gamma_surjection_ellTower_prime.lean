import Mathlib
import Submission.NK.RankTheoryDeep.ProductRank
import Submission.NK.RankTheoryDeep.gamma_surjection_ellTower
import Submission.NK.RankTheoryDeep.PrimeTower.LevelCoords
import Submission.NK.RankTheoryDeep.PrimeTower.expHom_surjective
import Submission.NK.RankTheoryDeep.PrimeTower.exists_linearMap_of_groupHom
import Submission.NK.RankTheoryDeep.PrimeTower.jointHom_surjective
import Submission.NK.RankTheoryDeep.PrimeTower.levelCoordHom_ellRestrict
import Submission.NK.Reconstruct.All

/-!
# The ℓ-adic tower product is a quotient of `Γ_ℚ`, for every prime `ℓ`

The ℓ-generalisation of `Submission/Work/RankTheoryDeep/gamma_surjection_ellTower.lean`: the same
assembly (`jointLevelHom_surjective_self`, `levelCoordLin`, `projAdd`, `PhiCoord`, `Phi`,
`Phi_surjective`) with the `2`-adic cyclotomic tower of `TowerArc.lean` replaced by the ℓ-adic
tower `towerPrime ℓ n` of `Submission/Work/RankTheoryDeep/PrimeTower/Defs.lean` and the modules
built on it.  The helpers are placed in the `NK.RankTheoryDeep.PrimeTower` namespace so that
they coexist with their `ℓ = 2` counterparts.
-/

attribute [local instance 10] DivisionRing.toRatAlgebra

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.RankTheoryDeep.PrimeTower

open scoped Pointwise

universe u

section Assembly

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The joint level map is surjective.**  Every element of the product
`∏_{n < N} Multiplicative (ZMod (ℓ ^ (n + 1)))` is of `ℓ`-power order, so the surjectivity of the
joint map on the abelianised level passes to its `ℓ`-primary part. -/
theorem jointLevelHom_surjective_self (N : ℕ) : Function.Surjective (jointLevelHom ℓ Ω N) := by
  intro y
  have hsurj : Function.Surjective (Abelianization.lift (jointHom ℓ Ω N)) := by
    intro w
    obtain ⟨σ, hσ⟩ := jointHom_surjective ℓ Ω N w
    exact ⟨Abelianization.of σ, by rw [Abelianization.lift_apply_of]; exact hσ⟩
  have hy : y ∈ NK.Reconstruct.ellPart
      (∀ n : Fin N, Multiplicative (ZMod (ℓ ^ (n.val + 1)))) ℓ := by
    rw [NK.Reconstruct.mem_ellPart_iff]
    refine ⟨Finset.univ.sup fun n : Fin N => n.val + 1, ?_⟩
    funext n
    simp only [Pi.pow_apply, Pi.one_apply]
    obtain ⟨d, hd⟩ : ∃ d, Finset.univ.sup (fun n : Fin N => n.val + 1) = (n.val + 1) + d :=
      ⟨_, (Nat.add_sub_cancel' (Finset.le_sup (Finset.mem_univ n))).symm⟩
    have h2 : ℓ ^ (n.val + 1 + d) = ℓ ^ (n.val + 1) * ℓ ^ d := by rw [pow_add]
    rw [hd, h2, pow_mul]
    have h1 : (y n) ^ (ℓ ^ (n.val + 1)) = 1 := by
      have h := pow_card_eq_one (x := y n)
      rwa [Fintype.card_multiplicative, ZMod.card] at h
    rw [h1, one_pow]
  obtain ⟨z, hzmem, hz⟩ := NK.Reconstruct.projSurj_ellPart_map_surj ℓ
    (Abelianization.lift (jointHom ℓ Ω N)) hsurj y hy
  exact ⟨⟨z, hzmem⟩, hz⟩

/-- The linear form of the `n`-th coordinate map of the `N`-th level. -/
noncomputable def levelCoordLin (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) :
    Additive (NK.Reconstruct.LevelEllPart (cycLevel ℓ Ω N).L ℓ) →ₗ[PadicInt ℓ] ZMod (ℓ ^ n) :=
  Classical.choose (exists_linearMap_of_groupHom ℓ (levelCoordHom ℓ Ω n N hn hN))

theorem levelCoordLin_apply (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N)
    (x : NK.Reconstruct.LevelEllPart (cycLevel ℓ Ω N).L ℓ) :
    levelCoordLin ℓ Ω n N hn hN (Additive.ofMul x)
      = (levelCoordHom ℓ Ω n N hn hN x : ZMod (ℓ ^ n)) :=
  Classical.choose_spec (exists_linearMap_of_groupHom ℓ (levelCoordHom ℓ Ω n N hn hN)) x

/-- The additive projection `Γ_ℚ → Γ_{L,ℓ}`. -/
noncomputable def projAdd (L : NK.Reconstruct.FrobLevel ℚ Ω) :
    Additive (NK.Reconstruct.Gamma ℚ Ω ℓ) →ₗ[PadicInt ℓ]
      Additive (NK.Reconstruct.LevelEllPart L.L ℓ) where
  toFun x := Additive.ofMul (NK.Reconstruct.Gamma.proj L (Additive.toMul x))
  map_add' a b := rfl
  map_smul' c x := rfl

theorem projAdd_apply (L : NK.Reconstruct.FrobLevel ℚ Ω)
    (x : Additive (NK.Reconstruct.Gamma ℚ Ω ℓ)) :
    projAdd ℓ Ω L x = Additive.ofMul (NK.Reconstruct.Gamma.proj L (Additive.toMul x)) := rfl

theorem projAdd_surjective (L : NK.Reconstruct.FrobLevel ℚ Ω) :
    Function.Surjective (projAdd ℓ Ω L) := by
  intro z
  obtain ⟨f, hf⟩ := NK.Reconstruct.proj_surjective (K := ℚ) (K' := Ω) ℓ L (Additive.toMul z)
  exact ⟨Additive.ofMul f,
    by rw [projAdd_apply, toMul_ofMul, hf, ofMul_toMul]⟩

theorem continuous_projAdd (L : NK.Reconstruct.FrobLevel ℚ Ω) : Continuous (projAdd ℓ Ω L) :=
  continuous_ofMul.comp
    ((NK.Reconstruct.continuous_proj (ℓ := ℓ) L).comp
      (continuous_toMul (X := NK.Reconstruct.Gamma ℚ Ω ℓ)))

/-- The `n`-th coordinate linear form on `Γ_ℚ`. -/
noncomputable def PhiCoord (n : ℕ) :
    Additive (NK.Reconstruct.Gamma ℚ Ω ℓ) →ₗ[PadicInt ℓ] ZMod (ℓ ^ n) :=
  if h : 1 ≤ n then (levelCoordLin ℓ Ω n n h le_rfl).comp (projAdd ℓ Ω (cycLevel ℓ Ω n)) else 0

theorem PhiCoord_apply (n : ℕ) (hn : 1 ≤ n) (x : Additive (NK.Reconstruct.Gamma ℚ Ω ℓ)) :
    PhiCoord ℓ Ω n x
      = levelCoordLin ℓ Ω n n hn le_rfl (projAdd ℓ Ω (cycLevel ℓ Ω n) x) := by
  simp only [PhiCoord, dif_pos hn, LinearMap.comp_apply]

theorem continuous_PhiCoord (n : ℕ) : Continuous (PhiCoord ℓ Ω n) := by
  by_cases hn : 1 ≤ n
  · rw [PhiCoord, dif_pos hn]
    exact (continuous_of_discreteTopology : Continuous (levelCoordLin ℓ Ω n n hn le_rfl)).comp
      (continuous_projAdd ℓ Ω (cycLevel ℓ Ω n))
  · rw [PhiCoord, dif_neg hn]
    exact continuous_const

/-- **The components of the joint level map**: the `n`-th component of `jointLevelHom` is the
coordinate map of the level. -/
theorem jointLevelHom_apply (N : ℕ) (z : NK.Reconstruct.LevelEllPart (cycLevel ℓ Ω N).L ℓ)
    (n : Fin N) :
    jointLevelHom ℓ Ω N z n
      = Multiplicative.ofAdd ((levelCoordHom ℓ Ω (n.val + 1) N (by omega) (by omega) z :
          ZMod (ℓ ^ (n.val + 1)))) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(↥(cycLevel ℓ Ω N).L/ℚ),
      Abelianization.of σ = Subgroup.subtype _ z :=
    QuotientGroup.mk_surjective (Subgroup.subtype _ z)
  have h1 : jointLevelHom ℓ Ω N z = jointHom ℓ Ω N σ := by
    show (Abelianization.lift (jointHom ℓ Ω N)).comp (Subgroup.subtype _) z = jointHom ℓ Ω N σ
    rw [MonoidHom.comp_apply, ← hσ, Abelianization.lift_apply_of]
  have h2 : (levelCoordHom ℓ Ω (n.val + 1) N (by omega) (by omega)) z
      = coordPrime ℓ (n.val + 1) N (by omega) (by omega) (expHom ℓ Ω N σ) := by
    show (coordPrime ℓ (n.val + 1) N (by omega) (by omega)).comp
      ((Abelianization.lift (expHom ℓ Ω N)).comp (Subgroup.subtype _)) z = _
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← hσ, Abelianization.lift_apply_of]
  rw [h1, h2]
  rfl

/-- **The first `N` coordinates of `Φ` are surjective.** -/
theorem jointSurjective (N : ℕ) :
    Function.Surjective (fun x : Additive (NK.Reconstruct.Gamma ℚ Ω ℓ) =>
      fun n : Fin N => PhiCoord ℓ Ω (n.val + 1) x) := by
  intro y
  obtain ⟨z, hz⟩ := jointLevelHom_surjective_self ℓ Ω N (fun n : Fin N => Multiplicative.ofAdd (y n))
  obtain ⟨x, hx⟩ := projAdd_surjective ℓ Ω (cycLevel ℓ Ω N) z
  refine ⟨x, funext fun n => ?_⟩
  show PhiCoord ℓ Ω (n.val + 1) x = y n
  rw [PhiCoord_apply ℓ Ω (n.val + 1) (by omega)]
  have hsmall : projAdd ℓ Ω (cycLevel ℓ Ω (n.val + 1)) x
      = Additive.ofMul (NK.Reconstruct.ellRestrict ℓ (cycLevel ℓ Ω (n.val + 1))
          (cycLevel ℓ Ω N) (cycLevel_mono ℓ Ω (by omega))
          (Additive.toMul (projAdd ℓ Ω (cycLevel ℓ Ω N) x))) := by
    rw [projAdd_apply, projAdd_apply]
    congr 1
    exact (NK.Reconstruct.Gamma.proj_compatible (cycLevel ℓ Ω (n.val + 1)) (cycLevel ℓ Ω N)
      (cycLevel_mono ℓ Ω (by omega)) (Additive.toMul x)).symm
  rw [hsmall, levelCoordLin_apply]
  rw [← MonoidHom.comp_apply, levelCoordHom_ellRestrict ℓ Ω (n := n.val + 1) (N := N)
    (by omega) (by omega)]
  rw [hx]
  have h3 := jointLevelHom_apply ℓ Ω N z n
  rw [hz] at h3
  have h4 : ((levelCoordHom ℓ Ω (n.val + 1) N (by omega) (by omega)) z : ZMod (ℓ ^ (n.val + 1)))
      = y n := by
    exact Multiplicative.ofAdd.injective h3.symm
  exact h4

/-- **`Φ`**: the `ℤ_ℓ`-linear map `Γ_ℚ → ∏_n ℤ/ℓ ^ n` whose `n`-th coordinate is the `n`-th
coordinate character of the level `ℚ(ζ_{towerMod ℓ n})`. -/
noncomputable def Phi : Additive (NK.Reconstruct.Gamma ℚ Ω ℓ) →ₗ[PadicInt ℓ]
    NK.RankTheoryDeep.EllTower ℓ :=
  LinearMap.pi (fun n => PhiCoord ℓ Ω n)

theorem Phi_apply (x : Additive (NK.Reconstruct.Gamma ℚ Ω ℓ)) (n : ℕ) :
    Phi ℓ Ω x n = PhiCoord ℓ Ω n x := rfl

/-- **`Φ` is surjective.**  For `y ∈ ∏_n ℤ/ℓ ^ n` the sets `U N = {x | ∀ n ≤ N, Φ x n = y n}` are
closed (continuity of the coordinates), nested and nonempty (by `jointSurjective`), so by
compactness of `Γ_ℚ` their intersection is nonempty; any element of it maps to `y`. -/
theorem Phi_surjective : Function.Surjective (Phi ℓ Ω) := by
  intro y
  set U : ℕ → Set (Additive (NK.Reconstruct.Gamma ℚ Ω ℓ)) :=
    fun N => {x | ∀ n ≤ N, PhiCoord ℓ Ω n x = y n} with hU
  have hUclosed : ∀ N, IsClosed (U N) := by
    intro N
    have hset : U N = ⋂ n ∈ Finset.range (N + 1), {x | PhiCoord ℓ Ω n x = y n} := by
      ext x
      rw [hU]
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range]
      exact ⟨fun h n hn => h n (by omega), fun h n hn => h n (by omega)⟩
    rw [hset]
    exact isClosed_iInter fun n => isClosed_iInter fun _ =>
      isClosed_eq (continuous_PhiCoord ℓ Ω n) continuous_const
  have hUne : ∀ N, (U N).Nonempty := by
    intro N
    obtain ⟨x, hx⟩ := jointSurjective ℓ Ω N (fun n : Fin N => y (n.val + 1))
    refine ⟨x, ?_⟩
    rw [hU]
    intro n hn
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      haveI : Subsingleton (ZMod (ℓ ^ 0)) := (ZMod.subsingleton_iff (n := ℓ ^ 0)).mpr rfl
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

end Assembly

end NK.RankTheoryDeep.PrimeTower

namespace NK.RankTheoryDeep

open scoped Pointwise

universe u

/-- **The ℓ-adic tower product is a quotient of `Γ_ℚ`, for every prime `ℓ`.**

This generalises `NK.RankTheoryDeep.gamma_surjection_ellTower` (the case `ℓ = 2`) to an arbitrary
prime: there is a surjective `ℤ_ℓ`-linear map

  `Γ_ℚ = NK.Reconstruct.Gamma ℚ Ω ℓ ↠ ∏_n ℤ/ℓ^n = NK.RankTheoryDeep.EllTower ℓ`.

Construction (uniform in `ℓ`).  Take distinct primes `q_n` with `ℓ^{n+1} ∣ q_n − 1`.  Then
`M_N = ℚ(ζ_{q_0⋯q_N})` is a finite Galois (indeed abelian) level of `Ω/ℚ` with
`Gal(M_N/ℚ) ≅ (ℤ/q_0⋯q_N)^× ≅ ∏_{i≤N} (ℤ/q_i)^×` by CRT; each `(ℤ/q_i)^×` is cyclic of order
`q_i − 1`, so its `ℓ`-part is `ℤ/ℓ^{v_ℓ(q_i−1)}` with `v_ℓ(q_i − 1) ≥ i+1`.  Hence
`Γ_{M_N} = LevelEllPart (M_N) ℓ ≅ ∏_{i≤N} ℤ/ℓ^{v_ℓ(q_i−1)}`, the transition maps are the
projections, and reducing `ℤ/ℓ^{v_ℓ(q_i−1)} → ℤ/ℓ^{i+1}` gives a compatible family of surjections,
hence a surjection `Γ_ℚ ↠ ∏_i ℤ/ℓ^{i+1} ≅ ∏_n ℤ/ℓ^n`.  Surjectivity of `Γ_ℚ → lim_N Γ_{M_N}`
needs no cofinality (the image is compact, hence closed and hits every finite stage).  The maps are
`ℤ_ℓ`-linear by `NK.Reconstruct.projAdd`, `NK.Reconstruct.ellRestrictAdd_smul` and
`PadicInt.cast_toZModPow`.

For `ℓ = 2` this is `NK.RankTheoryDeep.gamma_surjection_ellTower` (`gamma_surjection_ellTower.lean`
plus the auxiliary modules `TowerArc`, `expHom_surjective`, `jointHom_surjective`,
`levelCoordHom_ellRestrict`, `exists_linearMap_of_groupHom`, `card_gal_adjoin_eq_totient`,
`autToPow_castHom_pow`, `exists_zeta_tower`, `fermat_prime_dvd_sub_one`); the generalisation needs
the `ℓ`-versions of those modules.  For `ℓ` odd, primes `q` with `ℓ^k ∣ q − 1` are obtained from
prime divisors of `Φ_{ℓ^k}(ℓ)` (`ord_q(ℓ) = ℓ^k`, hence `q ≠ ℓ` and `ℓ^k ∣ q − 1`; the values
`Φ_{ℓ^k}(ℓ)` are pairwise coprime, so distinct `k` give distinct primes).  The `ℓ = 2` proof can be
copied and adapted (replace `2` by `ℓ`), which is the recommended route: for `ℓ = 2` use the prime
divisors of the Fermat numbers `2^{2^n}+1`, for odd `ℓ` the prime divisors of `Φ_{ℓ^{k}}(ℓ)`.

Consequence (for the writer of this area, not part of this lemma): combined with
`NK.RankTheoryDeep.aleph0_le_rank_of_surjective_tower` this refutes
`NK.ShimizuRank.GammaTFRankFinite Ω ℓ` and hence `NK.ShimizuRank.Residuals Ω ℓ` for every prime
`ℓ`, not only for `ℓ = 2`. -/
theorem gamma_surjection_ellTower_prime (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [Field Ω]
    [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] :
    ∃ Φ : Additive (NK.Reconstruct.Gamma ℚ Ω ℓ) →ₗ[PadicInt ℓ] NK.RankTheoryDeep.EllTower ℓ,
      Function.Surjective Φ :=
  ⟨PrimeTower.Phi ℓ Ω, PrimeTower.Phi_surjective ℓ Ω⟩

end NK.RankTheoryDeep
