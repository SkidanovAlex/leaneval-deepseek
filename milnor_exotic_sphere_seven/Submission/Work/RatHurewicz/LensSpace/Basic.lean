import Mathlib
import Submission.Work.RatHurewicz.LensSpace.Char
import Submission.Work.RatHurewicz.complexEuclideanIsometry
import Submission.Work.Serre.Defs
import Submission.Work.Serre.sphOneAspherical
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.StemsB.isSerreFibration_of_isCoveringMap
import Submission.Work.StemsB.sphSimplyConnected
import Submission.Work.RatHurewicz.coverRangeTransfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The lens space `S^{2N+3}/μₙ` as a free quotient of the unit sphere

We construct, for `1 ≤ n` and any `N`, the `(2N+3)`-dimensional lens space
`L = S^{2N+3}/μₙ = S^{2N+3}/(ZMod n)` as the quotient of the unit sphere of `ℂ^{N+2} ≅ ℝ^{2N+4}`
by the free action of the `n`-th roots of unity by scalar multiplication.  The quotient map is a
covering map with `n` sheets; consequently `L` is a range model of `K(ZMod n, 1)` up to degree
`2N` (`IsEMSpaceUpTo`) which is rationally acyclic in degrees `1, …, 2N`.  This is the model
needed for the transfer argument of `Work.Serre.SerreC3Finite`.

The scalar multiplication is transported to the *real* sphere `S^{2N+3}` (Mathlib's and the
workspace's sphere lemmas apply directly to it) through a real linear isometry
`ℂ^{N+2} ≅ ℝ^{2N+4}`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- `ℝ^{2N+4}`, the ambient space of the sphere `S^{2N+3}`. -/
abbrev lensAmb (N : ℕ) : Type := EuclideanSpace ℝ (Fin (2 * N + 3 + 1))

/-- The sphere `S^{2N+3}`, the total space of the lens-space construction. -/
abbrev lensTotal (N : ℕ) : Type := Metric.sphere (0 : lensAmb N) 1

theorem two_mul_add_two (N : ℕ) : 2 * (N + 2) = 2 * N + 3 + 1 := by ring

/-- **The real linear isometry `ℂ^{N+2} ≅ ℝ^{2N+4}`** obtained from the integer-indexed one by
reindexing `Fin (2(N+2)) ≃ Fin (2N+4)`. -/
def cIso (N : ℕ) : EuclideanSpace ℂ (Fin (N + 2)) ≃ₗᵢ[ℝ] lensAmb N :=
  (Classical.choice (complexEuclideanIsometry (N + 2))).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.cast (congrArg Fin (two_mul_add_two N))))

/-- Scalar multiplication of `ℝ^{2N+4}` transported from `ℂ^{N+2}` by `cIso`. -/
def lensAct (n N : ℕ) [NeZero n] (g : Multiplicative (ZMod n)) (x : lensAmb N) : lensAmb N :=
  cIso N ((phi n (NeZero.ne n) g : ℂ) • (cIso N).symm x)

theorem norm_eq_one_of_mem_lensTotal {N : ℕ} (x : lensTotal N) : ‖(x : lensAmb N)‖ = 1 := by
  have h := x.2
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
  exact h

theorem lensAct_mem (n N : ℕ) [NeZero n] (g : Multiplicative (ZMod n)) (x : lensTotal N) :
    lensAct n N g x.1 ∈ Metric.sphere (0 : lensAmb N) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero, lensAct, (cIso N).norm_map, norm_smul,
    (cIso N).symm.norm_map, phi_norm, one_mul, norm_eq_one_of_mem_lensTotal x]

theorem lensAct_one (n N : ℕ) [NeZero n] (x : lensAmb N) :
    lensAct n N 1 x = x := by
  rw [lensAct, map_one, Units.val_one, one_smul, (cIso N).apply_symm_apply]

theorem lensAct_mul (n N : ℕ) [NeZero n] (g h : Multiplicative (ZMod n)) (x : lensAmb N) :
    lensAct n N (g * h) x = lensAct n N g (lensAct n N h x) := by
  show cIso N ((phi n (NeZero.ne n) (g * h) : ℂ) • (cIso N).symm x)
    = cIso N ((phi n (NeZero.ne n) g : ℂ) • (cIso N).symm
        (cIso N ((phi n (NeZero.ne n) h : ℂ) • (cIso N).symm x)))
  rw [map_mul, Units.val_mul, (cIso N).symm_apply_apply, ← smul_smul]

theorem lensAct_injective (n N : ℕ) [NeZero n] (g : Multiplicative (ZMod n)) :
    Function.Injective (lensAct n N g) := by
  intro x y h
  have h' : (phi n (NeZero.ne n) g : ℂ) • (cIso N).symm x
      = (phi n (NeZero.ne n) g : ℂ) • (cIso N).symm y := (cIso N).injective h
  have hφ : (phi n (NeZero.ne n) g : ℂ) ≠ 0 := by
    simpa using Units.ne_zero (phi n (NeZero.ne n) g)
  have h2 : (cIso N).symm x = (cIso N).symm y := by
    have h3 := congrArg (fun z => ((phi n (NeZero.ne n) g : ℂ))⁻¹ • z) h'
    rwa [inv_smul_smul₀ hφ, inv_smul_smul₀ hφ] at h3
  exact (cIso N).symm.injective h2

/-- **The action of `ZMod n` on the sphere `S^{2N+3}`.** -/
noncomputable instance lensSMul (n N : ℕ) [NeZero n] :
    SMul (Multiplicative (ZMod n)) (lensTotal N) where
  smul g x := ⟨lensAct n N g x.1, lensAct_mem n N g x⟩

noncomputable instance lensMulAction (n N : ℕ) [NeZero n] :
    MulAction (Multiplicative (ZMod n)) (lensTotal N) where
  one_smul x := by
    apply Subtype.ext
    show lensAct n N 1 x.1 = x.1
    exact lensAct_one n N x.1
  mul_smul g h x := by
    apply Subtype.ext
    show lensAct n N (g * h) x.1 = lensAct n N g ((h • x : lensTotal N) : lensAmb N)
    exact lensAct_mul n N g h x.1

noncomputable instance lensContinuousConstSMul (n N : ℕ) [NeZero n] :
    ContinuousConstSMul (Multiplicative (ZMod n)) (lensTotal N) where
  continuous_const_smul g := by
    refine Continuous.subtype_mk ?_ (fun x => lensAct_mem n N g x)
    exact (cIso N).continuous.comp (((continuous_const_smul
      ((phi n (NeZero.ne n) g : ℂ))).comp (cIso N).symm.continuous).comp continuous_subtype_val)

noncomputable instance lensCancelSMul (n N : ℕ) [NeZero n] :
    IsCancelSMul (Multiplicative (ZMod n)) (lensTotal N) where
  left_cancel' g x y h := by
    have h' : lensAct n N g x.1 = lensAct n N g y.1 := congrArg Subtype.val h
    exact Subtype.ext (lensAct_injective n N g h')
  right_cancel' g g' x h := by
    have h' : lensAct n N g x.1 = lensAct n N g' x.1 := congrArg Subtype.val h
    have h2 : (phi n (NeZero.ne n) g : ℂ) • (cIso N).symm x.1
        = (phi n (NeZero.ne n) g' : ℂ) • (cIso N).symm x.1 := (cIso N).injective h'
    have h3 : ((phi n (NeZero.ne n) g : ℂ) - (phi n (NeZero.ne n) g' : ℂ))
        • (cIso N).symm x.1 = 0 := by
      rw [sub_smul, h2, sub_self]
    have hne : (cIso N).symm x.1 ≠ 0 := by
      intro hz
      have hx0 : x.1 = 0 := by rw [← (cIso N).apply_symm_apply x.1, hz, map_zero]
      have h1 := norm_eq_one_of_mem_lensTotal x
      rw [hx0, norm_zero] at h1
      norm_num at h1
    have h4 : (phi n (NeZero.ne n) g : ℂ) - (phi n (NeZero.ne n) g' : ℂ) = 0 := by
      by_contra hc
      exact hne ((smul_eq_zero.mp h3).resolve_left hc)
    have h5 : phi n (NeZero.ne n) g = phi n (NeZero.ne n) g' :=
      Units.ext (sub_eq_zero.mp h4)
    exact phi_injective n (NeZero.ne n) h5

/-- **The lens space** `L = S^{2N+3}/μₙ`. -/
abbrev lensSpace (n N : ℕ) [NeZero n] : Type :=
  Quotient (MulAction.orbitRel (Multiplicative (ZMod n)) (lensTotal N))

/-- The quotient (covering) map `S^{2N+3} → L`. -/
def lensProj (n N : ℕ) [NeZero n] : C(lensTotal N, lensSpace n N) :=
  ⟨Quotient.mk _, continuous_quot_mk⟩

theorem isQuotientCoveringMap_lensProj (n N : ℕ) [NeZero n] :
    IsQuotientCoveringMap (lensProj n N) (Multiplicative (ZMod n)) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem isCoveringMap_lensProj (n N : ℕ) [NeZero n] : IsCoveringMap (lensProj n N) :=
  IsQuotientCoveringMap.isCoveringMap (lensProj n N) _ (isQuotientCoveringMap_lensProj n N)

theorem lensProj_surjective (n N : ℕ) [NeZero n] : Function.Surjective (lensProj n N) :=
  Quotient.mk_surjective

instance lensTotalSimplyConnected (N : ℕ) : SimplyConnectedSpace (lensTotal N) :=
  Work.StemsB.sphSimplyConnected (2 * N + 3) (by omega)

instance lensTotalPathConnected (N : ℕ) : PathConnectedSpace (lensTotal N) :=
  inferInstance

instance lensSpacePathConnected (n N : ℕ) [NeZero n] : PathConnectedSpace (lensSpace n N) := by
  have h : IsPathConnected (Set.univ : Set (lensSpace n N)) := by
    have h1 : IsPathConnected (Set.univ : Set (lensTotal N)) := by
      rw [← pathConnectedSpace_iff_univ]; infer_instance
    have h2 := h1.image (lensProj n N).continuous
    rwa [Set.image_univ, Set.range_eq_univ.mpr (lensProj_surjective n N)] at h2
  rw [pathConnectedSpace_iff_univ]
  exact h

theorem card_lensFibre (n N : ℕ) [NeZero n] (x : lensSpace n N) :
    Nat.card ↥((lensProj n N) ⁻¹' {x}) = n := by
  obtain ⟨e, he⟩ := lensProj_surjective n N x
  have h := (isQuotientCoveringMap_lensProj n N).fiberEquivGroup (x := x) ⟨e, he⟩
  rw [Nat.card_congr h, Nat.card_eq_fintype_card, Fintype.card_congr (Multiplicative.toAdd)]
  exact ZMod.card n

end

end Work.RatHurewicz
