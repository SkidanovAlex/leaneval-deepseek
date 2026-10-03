/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The subgroup inclusion `U(H) ⊆ U(G)` from a coset diagonal homomorphism

Given a right-coset decomposition `C` of `G` over a subgroup `H` and a `ℂ`-algebra
homomorphism `Φ : N(H) → N(G)` which acts cosetwise on `ℓ²(G)` (`hΦform`), preserves the
involution (`hΦstar`), agrees with the left regular representations (`hΦ`) and is injective
(`hΦinj`), this file constructs the subgroup data of the envelope:
`Nonempty (EnvelopeInclusion G U(G) ι_G H)`.

The ring `U(H)` is the Ore localisation `N(H)[(nzd)⁻¹]`; `Φ` sends non-zero-divisors of `N(H)`
to non-zero-divisors of `N(G)` (`Work.ORVonNeumann.Rep.Phi_mem_nonZeroDivisors`), hence extends
to a ring homomorphism `diagExt : U(H) → U(G)`.  The extension is injective, `*`-preserving and
compatible with the structure maps, and Linnell independence is proved by clearing denominators
and evaluating at `δ₁`, where the terms lie in pairwise orthogonal coset subspaces
(`Work.ORVonNeumann.Rep.e_inner_eq_zero`).
-/
import Mathlib
import Submission.Work.ORVonNeumann.Envelope
import Submission.Work.ORVonNeumann.Rep.CosetData
import Submission.Work.ORVonNeumann.Rep.CountableVonNeumannOre
import Submission.Work.ORVonNeumann.Rep.delta1_separating
import Submission.Work.ORVonNeumann.Rep.HilbertBasis
import Submission.Work.ORVonNeumann.Rep.Orthonormal
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.U
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.UStar
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.starRegularAffiliated
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.posDefAffiliated
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.rankAffiliated
import Submission.Work.ORVonNeumann.Rep.e_inner_eq_zero
import Submission.Work.ORVonNeumann.Rep.Phi_mem_nonZeroDivisors
import Submission.Work.ORVonNeumann.Rep.oreCommonDenom
import Submission.Work.Rep.Ore.denseRange_of_injective
import Submission.Work.Rep.Ore.injective_of_mem_nonZeroDivisors
import Submission.Work.ORVonNeumann.Ore.star_oreLocalization
import Submission.Work.ORVonNeumann.Ore.star_mem_nonZeroDivisors

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ORVonNeumann.VonNeumannAlgebra

open Work.ORVonNeumann

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]
variable {H : Subgroup G}

/-- The map on non-zero-divisors induced by `Φ`. -/
noncomputable def diagNzd (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q),
      ∀ y : l2 ↥H, (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y)) :
    nonZeroDivisors (Rep.countableGroupVonNeumann (G := ↥H)).N →*
      nonZeroDivisors (Rep.countableGroupVonNeumann (G := G)).N where
  toFun s := ⟨Φ (s : (Rep.countableGroupVonNeumann (G := ↥H)).N),
    Rep.Phi_mem_nonZeroDivisors C Φ hΦstar hΦform
      (s := (s : (Rep.countableGroupVonNeumann (G := ↥H)).N)) s.2⟩
  map_one' := Subtype.ext (map_one Φ.toRingHom)
  map_mul' s t := Subtype.ext
    (map_mul Φ.toRingHom (s : (Rep.countableGroupVonNeumann (G := ↥H)).N)
      (t : (Rep.countableGroupVonNeumann (G := ↥H)).N))

/-- The ring homomorphism `N(H) → U(G)` underlying the extension of `Φ`. -/
noncomputable def diagF (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G)) :
    (Rep.countableGroupVonNeumann (G := ↥H)).N →+*
      (Rep.countableGroupVonNeumann (G := G)).affiliated :=
  (numU (Rep.countableGroupVonNeumann (G := G))).comp Φ.toRingHom

/-- The image of the non-zero-divisors of `N(H)` in the units of `U(G)`. -/
noncomputable def diagFS (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q),
      ∀ y : l2 ↥H, (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y)) :
    nonZeroDivisors (Rep.countableGroupVonNeumann (G := ↥H)).N →*
      ((Rep.countableGroupVonNeumann (G := G)).affiliated)ˣ :=
  (Ore.numUnitHom (S := nonZeroDivisors (Rep.countableGroupVonNeumann (G := G)).N)).comp
    (diagNzd C Φ hΦstar hΦform)

theorem diagHF (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q),
      ∀ y : l2 ↥H, (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y))
    (s : nonZeroDivisors (Rep.countableGroupVonNeumann (G := ↥H)).N) :
    diagF C Φ (s : (Rep.countableGroupVonNeumann (G := ↥H)).N)
      = ↑(diagFS C Φ hΦstar hΦform s) :=
  rfl

/-- The extension of `Φ` to the algebras of affiliated operators. -/
noncomputable def diagExt (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q),
      ∀ y : l2 ↥H, (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y)) :
    (Rep.countableGroupVonNeumann (G := ↥H)).affiliated →+*
      (Rep.countableGroupVonNeumann (G := G)).affiliated :=
  OreLocalization.universalHom (diagF C Φ) (diagFS C Φ hΦstar hΦform)
    (diagHF C Φ hΦstar hΦform)

theorem diagExt_commutes (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q),
      ∀ y : l2 ↥H, (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y))
    (r : (Rep.countableGroupVonNeumann (G := ↥H)).N) :
    diagExt C Φ hΦstar hΦform
        (numU (Rep.countableGroupVonNeumann (G := ↥H)) r)
      = numU (Rep.countableGroupVonNeumann (G := G)) (Φ r) :=
  OreLocalization.universalHom_commutes _ _ _

theorem diagExt_star (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q),
      ∀ y : l2 ↥H, (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y))
    (y : (Rep.countableGroupVonNeumann (G := ↥H)).affiliated) :
    diagExt C Φ hΦstar hΦform (star y) = star (diagExt C Φ hΦstar hΦform y) := by
  let η : (Rep.countableGroupVonNeumann (G := ↥H)).affiliated →+*
      (Rep.countableGroupVonNeumann (G := G)).affiliated :=
    { toFun := fun x => star (diagExt C Φ hΦstar hΦform (star x))
      map_one' := by simp
      map_zero' := by simp
      map_add' := by intro a b; simp only [star_add, map_add]
      map_mul' := by intro a b; simp only [star_mul, map_mul] }
  have hnum : ∀ r : (Rep.countableGroupVonNeumann (G := ↥H)).N,
      η (OreLocalization.numeratorHom r)
        = numU (Rep.countableGroupVonNeumann (G := G)) (Φ r) := by
    intro r
    have hstarH : star (numU (Rep.countableGroupVonNeumann (G := ↥H)) r)
        = numU (Rep.countableGroupVonNeumann (G := ↥H)) (star r) :=
      Work.ORVonNeumann.VonNeumannAlgebra.affiliated_star_numerator
        (Rep.countableGroupVonNeumann (G := ↥H)) r
    show star (diagExt C Φ hΦstar hΦform
        (star (numU (Rep.countableGroupVonNeumann (G := ↥H)) r)))
        = numU (Rep.countableGroupVonNeumann (G := G)) (Φ r)
    calc star (diagExt C Φ hΦstar hΦform
            (star (numU (Rep.countableGroupVonNeumann (G := ↥H)) r)))
        = star (diagExt C Φ hΦstar hΦform
            (numU (Rep.countableGroupVonNeumann (G := ↥H)) (star r))) :=
          congrArg (fun z => star (diagExt C Φ hΦstar hΦform z)) hstarH
      _ = star (numU (Rep.countableGroupVonNeumann (G := G)) (Φ (star r))) :=
          congrArg star (diagExt_commutes C Φ hΦstar hΦform (star r))
      _ = star (numU (Rep.countableGroupVonNeumann (G := G)) (star (Φ r))) :=
          congrArg (fun z => star (numU (Rep.countableGroupVonNeumann (G := G)) z))
            (hΦstar r)
      _ = star (star (numU (Rep.countableGroupVonNeumann (G := G)) (Φ r))) :=
          (congrArg star (Work.ORVonNeumann.VonNeumannAlgebra.affiliated_star_numerator
            (Rep.countableGroupVonNeumann (G := G)) (Φ r))).symm
      _ = numU (Rep.countableGroupVonNeumann (G := G)) (Φ r) := star_star _
  have huniq : η = diagExt C Φ hΦstar hΦform :=
    OreLocalization.universalHom_unique (diagF C Φ) (diagFS C Φ hΦstar hΦform)
      (diagHF C Φ hΦstar hΦform) η hnum
  calc diagExt C Φ hΦstar hΦform (star y) = η (star y) := by rw [huniq]
    _ = star (diagExt C Φ hΦstar hΦform y) := by simp [η]

theorem diagExt_injective (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q),
      ∀ y : l2 ↥H, (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y))
    (hΦinj : Function.Injective Φ) :
    Function.Injective (diagExt C Φ hΦstar hΦform) := by
  intro y z hyz
  have h0 : diagExt C Φ hΦstar hΦform (y - z) = 0 := by rw [map_sub, hyz, sub_self]
  have h1 : y - z = 0 := by
    refine OreLocalization.ind
      (X := (Rep.countableGroupVonNeumann (G := ↥H)).N)
      (β := fun w => diagExt C Φ hΦstar hΦform w = 0 → w = 0) ?_ (y - z) h0
    intro a s ha
    have ha' : (diagFS C Φ hΦstar hΦform s)⁻¹ *
        numU (Rep.countableGroupVonNeumann (G := G)) (Φ a) = 0 := by
      have hr : diagExt C Φ hΦstar hΦform (a /ₒ s) =
          (diagFS C Φ hΦstar hΦform s)⁻¹ *
          numU (Rep.countableGroupVonNeumann (G := G)) (Φ a) := rfl
      rw [hr] at ha
      exact ha
    have h2 : numU (Rep.countableGroupVonNeumann (G := G)) (Φ a) = 0 := by
      have h3 : (diagFS C Φ hΦstar hΦform s) *
          ((diagFS C Φ hΦstar hΦform s)⁻¹ *
          numU (Rep.countableGroupVonNeumann (G := G)) (Φ a)) = 0 := by
        rw [ha', mul_zero]
      rw [← mul_assoc, Units.mul_inv, one_mul] at h3
      exact h3
    have h4 : Φ a = 0 := by
      apply Work.ORVonNeumann.Ext.numU_injective
        (S := nonZeroDivisors (Rep.countableGroupVonNeumann (G := G)).N) le_rfl
      rw [h2]
      exact (map_zero (OreLocalization.numeratorRingHom (S := nonZeroDivisors
        (Rep.countableGroupVonNeumann (G := G)).N))).symm
    have h5 : a = 0 := by
      apply hΦinj
      rw [h4]
      exact (map_zero Φ).symm
    rw [h5, OreLocalization.zero_oreDiv]
  exact sub_eq_zero.mp h1

theorem diagExt_toU (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦ : ∀ (h : ↥H), Φ ⟨Rep.leftRegOp h, Rep.leftRegOp_mem_groupVonNeumann h⟩
      = ⟨Rep.leftRegOp (h : G), Rep.leftRegOp_mem_groupVonNeumann (h : G)⟩)
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q),
      ∀ y : l2 ↥H, (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y))
    (h : ↥H) (c : ℂ) :
    diagExt C Φ hΦstar hΦform
        (toU (Rep.countableGroupVonNeumann (G := ↥H)) (MonoidAlgebra.single h c))
      = toU (Rep.countableGroupVonNeumann (G := G)) (MonoidAlgebra.single (h : G) c) := by
  have h1 : toU (Rep.countableGroupVonNeumann (G := ↥H)) (MonoidAlgebra.single h c)
      = numU (Rep.countableGroupVonNeumann (G := ↥H))
          ((Rep.countableGroupVonNeumann (G := ↥H)).lift (MonoidAlgebra.single h c)) :=
    toU_apply _ _
  have h2 : toU (Rep.countableGroupVonNeumann (G := G)) (MonoidAlgebra.single (h : G) c)
      = numU (Rep.countableGroupVonNeumann (G := G))
          ((Rep.countableGroupVonNeumann (G := G)).lift (MonoidAlgebra.single (h : G) c)) :=
    toU_apply _ _
  rw [h1, h2, diagExt_commutes]
  congr 1
  rw [GroupVonNeumannAlgebra.lift_single, GroupVonNeumannAlgebra.lift_single]
  rw [show Φ (c • (Rep.countableGroupVonNeumann (G := ↥H)).ρ h)
      = c • Φ ((Rep.countableGroupVonNeumann (G := ↥H)).ρ h) from
    map_smul Φ c ((Rep.countableGroupVonNeumann (G := ↥H)).ρ h)]
  congr 1
  show Φ (Rep.leftRegularHom (G := ↥H) h) = Rep.leftRegularHom (G := G) (h : G)
  rw [show Rep.leftRegularHom (G := ↥H) h
      = ⟨Rep.leftRegOp h, Rep.leftRegOp_mem_groupVonNeumann h⟩ from
      Subtype.ext (Rep.leftRegularHom_coe h),
    show Rep.leftRegularHom (G := G) (h : G)
      = ⟨Rep.leftRegOp (h : G), Rep.leftRegOp_mem_groupVonNeumann (h : G)⟩ from
      Subtype.ext (Rep.leftRegularHom_coe (h : G))]
  exact hΦ h

theorem diag_sum_ne_zero (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q),
      ∀ y : l2 ↥H, (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y))
    (n : ℕ) (q : Fin (n + 1) → G) (hq : ∀ i j, q i * (q j)⁻¹ ∈ H → i = j)
    (b : Fin (n + 1) → ↥(groupVonNeumann ↥H)) (hb : ∀ i, b i ≠ 0) :
    (∑ i, Φ (b i) * Rep.leftRegularHom (G := G) (q i)) ≠ 0 := by
  intro hX
  have hterm : ∀ i : Fin (n + 1),
      (((Φ (b i) * Rep.leftRegularHom (G := G) (q i) : ↥(groupVonNeumann G))) : boundedEnd G)
          (delta1 G)
        = C.e (C.qpart (q i)) ((b i : boundedEnd ↥H) (Rep.deltaG (C.hpart (q i)))) := by
    intro i
    rw [show ((Φ (b i) * Rep.leftRegularHom (G := G) (q i) : ↥(groupVonNeumann G)) :
        boundedEnd G) = (Φ (b i) : boundedEnd G) *
          (Rep.leftRegularHom (G := G) (q i) : boundedEnd G) from rfl]
    rw [mul_apply_eq_comp, Rep.leftRegularHom_coe, Rep.leftRegOp_delta1]
    rw [show Rep.deltaG (q i) = C.E (q i) (Rep.deltaG (C.hpart (q i))) from
      (C.E_delta_self (q i)).symm]
    show (Φ (b i) : boundedEnd G) (C.e (C.qpart (q i)) (Rep.deltaG (C.hpart (q i)))) = _
    rw [hΦform (b i) (C.qpart (q i)) (Rep.deltaG (C.hpart (q i)))]
  have hsumval : (((∑ i, Φ (b i) * Rep.leftRegularHom (G := G) (q i)) :
        ↥(groupVonNeumann G)) : boundedEnd G) (delta1 G)
      = ∑ i, C.e (C.qpart (q i)) ((b i : boundedEnd ↥H) (Rep.deltaG (C.hpart (q i)))) := by
    have hcoe : ((∑ i, Φ (b i) * Rep.leftRegularHom (G := G) (q i) :
          ↥(groupVonNeumann G)) : boundedEnd G)
        = ∑ i, ((Φ (b i) * Rep.leftRegularHom (G := G) (q i) :
            ↥(groupVonNeumann G)) : boundedEnd G) :=
      map_sum ((groupVonNeumann G).toSubalgebra).val _ _
    rw [hcoe]
    exact (ContinuousLinearMap.sum_apply Finset.univ
      (fun i => ((Φ (b i) * Rep.leftRegularHom (G := G) (q i) :
        ↥(groupVonNeumann G)) : boundedEnd G)) (delta1 G)).trans
      (Finset.sum_congr rfl (fun i _ => hterm i))
  have hv : ∀ i, C.e (C.qpart (q i))
      ((b i : boundedEnd ↥H) (Rep.deltaG (C.hpart (q i)))) ≠ 0 := by
    intro i h0
    have hw : (b i : boundedEnd ↥H) (Rep.deltaG (C.hpart (q i))) = 0 :=
      (C.e (C.qpart (q i))).injective (by rw [h0, map_zero])
    have hw2 : ((b i * Rep.leftRegularHom (G := ↥H) (C.hpart (q i)) :
          ↥(groupVonNeumann ↥H)) : boundedEnd ↥H) (delta1 ↥H) = 0 := by
      rw [show ((b i * Rep.leftRegularHom (G := ↥H) (C.hpart (q i)) :
            ↥(groupVonNeumann ↥H)) : boundedEnd ↥H)
          = (b i : boundedEnd ↥H) *
            (Rep.leftRegularHom (G := ↥H) (C.hpart (q i)) : boundedEnd ↥H) from rfl]
      rw [mul_apply_eq_comp, Rep.leftRegularHom_coe, Rep.leftRegOp_delta1]
      exact hw
    have hz : b i * Rep.leftRegularHom (G := ↥H) (C.hpart (q i)) = 0 :=
      Rep.delta1_separating (G := ↥H) _ hw2
    have hu : IsUnit (Rep.leftRegularHom (G := ↥H) (C.hpart (q i))) :=
      GroupVonNeumannAlgebra.isUnit_ρ (Rep.countableGroupVonNeumann (G := ↥H))
        (C.hpart (q i))
    exact hb i ((hu.mul_left_eq_zero).mp hz)
  have hqpart : ∀ i j : Fin (n + 1), i ≠ j →
      C.qpart (q i) ≠ C.qpart (q j) :=
    fun i j hij => C.qpart_ne_of_not_mem (q i) (q j) (fun hmem => hij (hq i j hmem))
  have horth : ∀ i j : Fin (n + 1), i ≠ j →
      inner ℂ (C.e (C.qpart (q i)) ((b i : boundedEnd ↥H) (Rep.deltaG (C.hpart (q i)))))
        (C.e (C.qpart (q j)) ((b j : boundedEnd ↥H) (Rep.deltaG (C.hpart (q j))))) = 0 :=
    fun i j hij => Rep.e_inner_eq_zero C (hqpart i j hij) _ _
  have hsum_ne : (∑ i, C.e (C.qpart (q i))
      ((b i : boundedEnd ↥H) (Rep.deltaG (C.hpart (q i))))) ≠ 0 := by
    intro h0
    let j : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
    have h1 : inner ℂ (C.e (C.qpart (q j)) ((b j : boundedEnd ↥H) (Rep.deltaG (C.hpart (q j)))))
        (∑ i, C.e (C.qpart (q i))
          ((b i : boundedEnd ↥H) (Rep.deltaG (C.hpart (q i))))) = 0 := by
      rw [h0, inner_zero_right]
    rw [inner_sum] at h1
    have h2 : inner ℂ (C.e (C.qpart (q j)) ((b j : boundedEnd ↥H) (Rep.deltaG (C.hpart (q j)))))
        (C.e (C.qpart (q j)) ((b j : boundedEnd ↥H) (Rep.deltaG (C.hpart (q j))))) = 0 := by
      rw [Finset.sum_eq_single j (fun i _ hij => horth j i (Ne.symm hij))
        (fun hj => absurd (Finset.mem_univ j) hj)] at h1
      exact h1
    exact hv j (inner_self_eq_zero.mp h2)
  have hval0 : (((∑ i, Φ (b i) * Rep.leftRegularHom (G := G) (q i)) :
        ↥(groupVonNeumann G)) : boundedEnd G) (delta1 G) = 0 := by
    rw [hX]; simp
  rw [hsumval] at hval0
  exact hsum_ne hval0

theorem diagExt_linnell (C : Rep.CosetData G H)
    (Φ : ↥(groupVonNeumann ↥H) →ₐ[ℂ] ↥(groupVonNeumann G))
    (hΦ : ∀ (h : ↥H), Φ ⟨Rep.leftRegOp h, Rep.leftRegOp_mem_groupVonNeumann h⟩
      = ⟨Rep.leftRegOp (h : G), Rep.leftRegOp_mem_groupVonNeumann (h : G)⟩)
    (hΦstar : ∀ b : ↥(groupVonNeumann ↥H), Φ (star b) = star (Φ b))
    (hΦform : ∀ (b : ↥(groupVonNeumann ↥H)) (q : C.Q),
      ∀ y : l2 ↥H, (Φ b : boundedEnd G) (C.e q y) = C.e q ((b : boundedEnd ↥H) y)) :
    LinnellIndependent H (Rep.countableGroupVonNeumann (G := ↥H)).affiliated
      (Rep.countableGroupVonNeumann (G := G)).affiliated
      (diagExt C Φ hΦstar hΦform)
      (toU (Rep.countableGroupVonNeumann (G := G))) := by
  intro n q d hd hq
  have hrep : ∀ i : Fin (n + 1), ∃ (a : (Rep.countableGroupVonNeumann (G := ↥H)).N)
      (s : nonZeroDivisors (Rep.countableGroupVonNeumann (G := ↥H)).N),
      d i = (a /ₒ s : (Rep.countableGroupVonNeumann (G := ↥H)).affiliated) := by
    intro i
    exact OreLocalization.ind (X := (Rep.countableGroupVonNeumann (G := ↥H)).N)
      (β := fun y : (Rep.countableGroupVonNeumann (G := ↥H)).affiliated =>
        ∃ (a : (Rep.countableGroupVonNeumann (G := ↥H)).N)
          (s : nonZeroDivisors (Rep.countableGroupVonNeumann (G := ↥H)).N),
          y = (a /ₒ s : (Rep.countableGroupVonNeumann (G := ↥H)).affiliated))
      (fun a s => ⟨a, s, rfl⟩) (d i)
  choose a s hs using hrep
  obtain ⟨e, t, b, hte, hbs⟩ := Rep.oreCommonDenom
    (S := nonZeroDivisors (Rep.countableGroupVonNeumann (G := ↥H)).N) le_rfl a s
  have hdbe : ∀ i, d i = (b i /ₒ e : (Rep.countableGroupVonNeumann (G := ↥H)).affiliated) :=
    fun i => (hs i).trans (hbs i)
  have hb : ∀ i, b i ≠ 0 := by
    intro i hbi
    have hz : d i = 0 := by
      rw [hdbe i, hbi, OreLocalization.zero_oreDiv]
    exact hd i hz
  set u : ((Rep.countableGroupVonNeumann (G := G)).affiliated)ˣ :=
    diagFS C Φ hΦstar hΦform e with hu_def
  have happ : ∀ i, diagExt C Φ hΦstar hΦform (d i)
      = (↑u⁻¹ : (Rep.countableGroupVonNeumann (G := G)).affiliated) *
        numU (Rep.countableGroupVonNeumann (G := G)) (Φ (b i)) := by
    intro i
    rw [hdbe i]
    rfl
  have htoU : ∀ i, toU (Rep.countableGroupVonNeumann (G := G))
        (MonoidAlgebra.single (q i) 1)
      = numU (Rep.countableGroupVonNeumann (G := G)) (Rep.leftRegularHom (G := G) (q i)) := by
    intro i
    have h1 : toU (Rep.countableGroupVonNeumann (G := G)) (MonoidAlgebra.single (q i) 1)
        = numU (Rep.countableGroupVonNeumann (G := G))
            ((Rep.countableGroupVonNeumann (G := G)).lift (MonoidAlgebra.single (q i) 1)) :=
      toU_apply _ _
    rw [h1, GroupVonNeumannAlgebra.lift_single, one_smul]
    rfl
  have hterm2 : ∀ i, diagExt C Φ hΦstar hΦform (d i) *
        toU (Rep.countableGroupVonNeumann (G := G)) (MonoidAlgebra.single (q i) 1)
      = (↑u⁻¹ : (Rep.countableGroupVonNeumann (G := G)).affiliated) *
        numU (Rep.countableGroupVonNeumann (G := G))
          (Φ (b i) * Rep.leftRegularHom (G := G) (q i)) := by
    intro i
    rw [happ i, htoU i, mul_assoc]
    rw [show numU (Rep.countableGroupVonNeumann (G := G)) (Φ (b i)) *
          numU (Rep.countableGroupVonNeumann (G := G)) (Rep.leftRegularHom (G := G) (q i))
        = numU (Rep.countableGroupVonNeumann (G := G))
          (Φ (b i) * Rep.leftRegularHom (G := G) (q i)) from
      (map_mul (numU (Rep.countableGroupVonNeumann (G := G))) _ _).symm]
  have hsum : (∑ i, diagExt C Φ hΦstar hΦform (d i) *
        toU (Rep.countableGroupVonNeumann (G := G)) (MonoidAlgebra.single (q i) 1))
      = (↑u⁻¹ : (Rep.countableGroupVonNeumann (G := G)).affiliated) *
        numU (Rep.countableGroupVonNeumann (G := G))
          (∑ i, Φ (b i) * Rep.leftRegularHom (G := G) (q i)) := by
    rw [Finset.sum_congr rfl (fun i _ => hterm2 i), ← Finset.mul_sum]
    congr 1
    exact (map_sum (numU (Rep.countableGroupVonNeumann (G := G))) _ _).symm
  intro hzero
  have hX : (∑ i, Φ (b i) * Rep.leftRegularHom (G := G) (q i)) ≠ 0 :=
    diag_sum_ne_zero C Φ hΦstar hΦform n q hq b hb
  have hnum : numU (Rep.countableGroupVonNeumann (G := G))
      (∑ i, Φ (b i) * Rep.leftRegularHom (G := G) (q i)) ≠ 0 := by
    intro h
    refine hX ?_
    exact (Work.ORVonNeumann.Ext.numU_injective
      (S := nonZeroDivisors (Rep.countableGroupVonNeumann (G := G)).N) le_rfl)
      (h.trans (map_zero (numU (Rep.countableGroupVonNeumann (G := G)))).symm)
  have hzero' : (↑u⁻¹ : (Rep.countableGroupVonNeumann (G := G)).affiliated) *
      numU (Rep.countableGroupVonNeumann (G := G))
        (∑ i, Φ (b i) * Rep.leftRegularHom (G := G) (q i)) = 0 := by
    rw [← hsum]; exact hzero
  refine hnum ?_
  have hkey : ((↑u : (Rep.countableGroupVonNeumann (G := G)).affiliated) *
      ↑u⁻¹) = 1 := by rw [Units.mul_inv]
  have := congrArg (fun w => (↑u : (Rep.countableGroupVonNeumann (G := G)).affiliated) * w)
    hzero'
  rw [mul_zero, ← mul_assoc, hkey, one_mul] at this
  exact this

/-- **The subgroup data of the envelope from a coset diagonal homomorphism.**  Given the right
coset decomposition `C : CosetData G H` and a `Φ : N(H) →ₐ[ℂ] N(G)` which is compatible with the
left regular representations (`hΦ`), `*`-preserving (`hΦstar`), injective (`hΦinj`) and acts
cosetwise (`hΦform`), the algebra `V = U(H) = N(H)[(nzd)⁻¹]` together with the extension
`U(H) →+* U(G)` of `Φ` is an `EnvelopeInclusion G U(G) ι_G H`. -/
theorem exists_envelopeInclusion_of_diagHom {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (H : Subgroup G) (C : Work.ORVonNeumann.Rep.CosetData G H) (Φ : ↥(Work.ORVonNeumann.groupVonNeumann ↥H) →ₐ[ℂ] ↥(Work.ORVonNeumann.groupVonNeumann G)) (hΦ : ∀ (h : ↥H), Φ ⟨Work.ORVonNeumann.Rep.leftRegOp h, Work.ORVonNeumann.Rep.leftRegOp_mem_groupVonNeumann h⟩ = ⟨Work.ORVonNeumann.Rep.leftRegOp (h : G), Work.ORVonNeumann.Rep.leftRegOp_mem_groupVonNeumann (h : G)⟩) (hΦstar : ∀ b : ↥(Work.ORVonNeumann.groupVonNeumann ↥H), Φ (star b) = star (Φ b)) (hΦinj : Function.Injective Φ) (hΦform : ∀ (b : ↥(Work.ORVonNeumann.groupVonNeumann ↥H)) (q : C.Q), ∀ y : Work.ORVonNeumann.l2 ↥H, (Φ b : Work.ORVonNeumann.boundedEnd G) (C.e q y) = C.e q ((b : Work.ORVonNeumann.boundedEnd ↥H) y)) : Nonempty (Work.ORVonNeumann.EnvelopeInclusion G (Work.ORVonNeumann.Rep.countableGroupVonNeumann (G := G)).affiliated (Work.ORVonNeumann.VonNeumannAlgebra.toU (Work.ORVonNeumann.Rep.countableGroupVonNeumann (G := G))) H) := by
  refine ⟨{ V := (Rep.countableGroupVonNeumann (G := ↥H)).affiliated
            ringV := inferInstance
            starV := instStarRingAffiliated _
            algebraV := inferInstance
            ιH := toU (Rep.countableGroupVonNeumann (G := ↥H))
            ιH_injective := toU_injective _
            ιH_star := fun x =>
              (toU_star (Rep.countableGroupVonNeumann (G := ↥H)) x).symm
            ιH_algebraMap := toU_algebraMap _
            starRegularV := isStarRegularRing_affiliated _
            posDefV := posDefAffiliated (G := ↥H)
            rkV := (rankAffiliated (G := ↥H)).choose
            rkV_faithful := (rankAffiliated (G := ↥H)).choose_spec
            φ := diagExt C Φ hΦstar hΦform
            φ_injective := diagExt_injective C Φ hΦstar hΦform hΦinj
            φ_star := fun v => diagExt_star C Φ hΦstar hΦform v
            φ_ι := fun h c => diagExt_toU C Φ hΦ hΦstar hΦform h c
            linnell := diagExt_linnell C Φ hΦ hΦstar hΦform }⟩

end Work.ORVonNeumann.VonNeumannAlgebra
