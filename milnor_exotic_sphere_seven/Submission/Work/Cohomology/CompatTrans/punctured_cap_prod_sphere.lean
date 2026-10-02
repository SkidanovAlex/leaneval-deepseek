import Mathlib
import Submission.Work.Cohomology.CompatTrans.prodSphereDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The punctured product of two caps is homotopy equivalent to a sphere

Let `capA m = {x ∈ S^(m+1) : x_m > -1/2}` be the cap of the unit sphere of `ℝ^(m+1)`
(`Work.Cohomology.capA`), a contractible open piece of `S^(m+1)`.  The product
`Vset p q = capA p × capA q ⊆ S^(p+1) × S^(q+1) = PSph p q` is a `(p+q)`-dimensional open ball
around the base point `ptP p q = (N_p, N_q)`; removing the point therefore leaves a space
homotopy equivalent to `S^(p+q-1)`.

This is the geometric input to the Mayer–Vietoris computation of the (co)homology of a product
of spheres: it identifies `H̃_*(Vset \ {pt})` with the homology of a sphere, which produces the
connecting homomorphism of the Mayer–Vietoris sequence.

## Strategy

* `capTgtHomeo m` identifies the cap `capA m` with the target region `tgtSet (1/2) ⊆ ℝ^m` of
  stereographic projection from the south pole (`Work.Cohomology.sphereCapContractible`), and
  sends the north pole `sphN m` to the origin.  This is a `def` rather than an anonymous
  homeomorphism so that the image of the north pole can be recorded (`capTgtHomeo_sphN`).

* `euclidSplit p q` is the canonical linear homeomorphism
  `ℝ^p × ℝ^q → ℝ^(p+q)` (concatenation of coordinates), written as a `def` so that the
  elaborator never has to unfold the (large) body of `EuclideanSpace.finAddEquivProd`.

* `punctured_convex_homotopyEquiv` is the general fact that for a nonempty open convex set `C`
  containing the origin, `C \ {0}` is homotopy equivalent to the unit sphere: radial projection
  `x ↦ ‖x‖⁻¹ • x` is a homotopy inverse to `u ↦ δ • u` for a small `δ > 0`, the straight-line
  homotopy being a convex combination of `(δ/‖x‖) • x` and `x`, both of which lie in `C`.

* The homeomorphism of the punctured sets is assembled from
  `Homeomorph.Set.prod` (flattening `capA p ×ˢ capA q` to the product of the two caps) and
  `Homeomorph.subtype` (restriction to the complement of a point).

## Main result

* `Work.Cohomology.punctured_cap_prod_sphere`
-/

open scoped Topology
open scoped unitInterval

namespace Work.Cohomology

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. Splitting `ℝ^(p+q)` into `ℝ^p × ℝ^q` -/

/-- The canonical linear homeomorphism `ℝ^p × ℝ^q ≅ ℝ^(p+q)` (concatenation of coordinates).

It is kept as a `def` so that its (large) body is never unfolded by the elaborator. -/
def euclidSplit (p q : ℕ) :
    (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + q)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p) (m := q)).symm

/-- The underlying function of `euclidSplit` agrees with that of its associated homeomorphism. -/
lemma euclidSplit_homeo_coe (p q : ℕ) :
    ⇑(euclidSplit p q).toHomeomorph = ⇑(euclidSplit p q) := rfl

/-- The underlying function of `euclidSplit` agrees with that of the associated linear map. -/
lemma euclidSplit_lmap_coe (p q : ℕ) :
    ⇑(euclidSplit p q).toLinearEquiv.toLinearMap = ⇑(euclidSplit p q) := rfl

/-! ## 2. The cap and its stereographic model -/

/-- Stereographic projection from the south pole identifies the cap
`{x ∈ S^(m+1) : x_m > -1/2}` with the region `tgtSet (1/2)` of `ℝ^m`. -/
def capSetTgtHomeo (m : ℕ) : ↥(capSet (m := m) (1/2)) ≃ₜ ↥(tgtSet (m := m) (1/2)) where
  toFun := fun x => ⟨stereoFwd x.1, stereoFwd_mem (m := m) (by norm_num) x.1 x.2.1 x.2.2⟩
  invFun := fun y => ⟨stereoInv y.1, stereoInv_mem (m := m) y.1 y.2⟩
  left_inv := fun x => Subtype.ext (stereoInv_stereoFwd (m := m) x.1 x.2.1 (by linarith [x.2.2]))
  right_inv := fun y => Subtype.ext (stereoFwd_stereoInv (m := m) y.1)
  continuous_toFun := Continuous.subtype_mk
    (continuousOn_stereoFwd (m := m) (by norm_num)).domRestrict
    (fun x => stereoFwd_mem (m := m) (by norm_num) x.1 x.2.1 x.2.2)
  continuous_invFun := Continuous.subtype_mk (continuous_stereoInv.comp continuous_subtype_val)
    (fun y => stereoInv_mem (m := m) y.1 y.2)

/-- The cap `capA m` is homeomorphic to the region `tgtSet (1/2) ⊆ ℝ^m`. -/
def capTgtHomeo (m : ℕ) : ↥(capA m) ≃ₜ ↥(tgtSet (m := m) (1/2)) :=
  (flatHomeo (q := sphSet (m + 1))
    (P := fun x : EuclideanSpace ℝ (Fin (m + 1)) => x (Fin.last m) > -(1/2))).trans
    (capSetTgtHomeo m)

/-- The homeomorphism `capTgtHomeo` sends the north pole to the origin. -/
lemma capTgtHomeo_sphN (m : ℕ) :
    capTgtHomeo m ⟨sphN m, sphN_mem_capA m⟩ = (⟨(0 : EuclideanSpace ℝ (Fin m)), by
      show (1 - 1/2) * ‖(0 : EuclideanSpace ℝ (Fin m))‖ ^ 2 < 1 + 1/2
      rw [norm_zero]; norm_num⟩ : ↥(tgtSet (m := m) (1/2))) := by
  rw [show capTgtHomeo m ⟨sphN m, sphN_mem_capA m⟩ =
      (⟨stereoFwd (Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin m)) 1), _⟩ :
        ↥(tgtSet (m := m) (1/2))) from rfl]
  ext
  simp only [stereoFwd]
  rw [Work.Cohomology.strip_snocLp]
  simp

/-! ## 3. Puncturing an open convex set containing the origin -/

/-- **A punctured open convex set containing the origin is homotopy equivalent to the unit
sphere.**

Radial projection `x ↦ ‖x‖⁻¹ • x` onto the unit sphere is a homotopy inverse to the dilation
`u ↦ δ • u` for a small `δ > 0` (with `δ•u ∈ C` because `‖δ•u‖ = δ` is smaller than the radius
of a ball around `0` contained in `C`).  The straight-line homotopy
`(t, x) ↦ ((1-t)·(δ/‖x‖) + t) • x = (1-t) • ((δ/‖x‖) • x) + t • x` stays in `C \ {0}` because it
is a convex combination of the two points `(δ/‖x‖) • x` and `x` of `C`, and its coefficient is
strictly positive. -/
theorem punctured_convex_homotopyEquiv (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n)))
    (hopen : IsOpen C) (hconv : Convex ℝ C) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ C) :
    Nonempty (ContinuousMap.HomotopyEquiv {x : EuclideanSpace ℝ (Fin n) // x ∈ C ∧ x ≠ 0}
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hopen 0 h0
  obtain ⟨δ, hδpos, hδε⟩ : ∃ δ > 0, δ < ε := ⟨ε/2, by linarith, by linarith⟩
  have sphere_norm_eq_one : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    intro x
    have h := Metric.mem_sphere.mp x.2
    rwa [dist_zero_right] at h
  have hsp : ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      (u : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    intro u h
    have := sphere_norm_eq_one u
    rw [h, norm_zero] at this
    norm_num at this
  have hwsp : ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      δ • (u : EuclideanSpace ℝ (Fin n)) ∈ C := by
    intro u
    apply hε
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hδpos.le,
      sphere_norm_eq_one u, mul_one]
    exact hδε
  have hcont_delta : Continuous fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      δ • (u : EuclideanSpace ℝ (Fin n)) := by fun_prop
  have hw : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → (δ / ‖x‖) • x ∈ C := by
    intro x hx
    apply hε
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
    rw [div_mul_cancel₀]
    · exact hδε
    · exact norm_ne_zero_iff.mpr hx
  have hne : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → δ • x ≠ 0 := by
    intro x hx h
    have h1 : ‖δ • x‖ = 0 := by rw [h, norm_zero]
    rw [norm_smul, Real.norm_of_nonneg hδpos.le, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact hδpos.ne' h1
    · exact hx (norm_eq_zero.mp h1)
  let toFun : C({x : EuclideanSpace ℝ (Fin n) // x ∈ C ∧ x ≠ 0},
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    ⟨fun x => ⟨‖(x : EuclideanSpace ℝ (Fin n))‖⁻¹ • (x : EuclideanSpace ℝ (Fin n)), by
        rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
          Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr x.2.2)]⟩,
      Continuous.subtype_mk
        ((continuous_subtype_val.norm.inv₀
          (fun x : {x : EuclideanSpace ℝ (Fin n) // x ∈ C ∧ x ≠ 0} =>
            norm_ne_zero_iff.mpr x.2.2)).smul continuous_subtype_val)
        (fun x => by
          change ‖(x : EuclideanSpace ℝ (Fin n))‖⁻¹ • (x : EuclideanSpace ℝ (Fin n)) ∈
            Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
          rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
            Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr x.2.2)])⟩
  let invFun : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      {x : EuclideanSpace ℝ (Fin n) // x ∈ C ∧ x ≠ 0}) :=
    ⟨fun u => ⟨δ • (u : EuclideanSpace ℝ (Fin n)), hwsp u, hne _ (hsp u)⟩,
      Continuous.subtype_mk hcont_delta (fun u => ⟨hwsp u, hne _ (hsp u)⟩)⟩
  refine ⟨{ toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_ }⟩
  · let hval : I × {x : EuclideanSpace ℝ (Fin n) // x ∈ C ∧ x ≠ 0} → EuclideanSpace ℝ (Fin n) :=
      fun p => ((1 - (p.1 : ℝ)) * (δ / ‖(p.2 : EuclideanSpace ℝ (Fin n))‖) + (p.1 : ℝ))
        • (p.2 : EuclideanSpace ℝ (Fin n))
    have hval_mem : ∀ p : I × {x : EuclideanSpace ℝ (Fin n) // x ∈ C ∧ x ≠ 0}, hval p ∈ C := by
      intro p
      have ht0 : 0 ≤ (p.1 : ℝ) := p.1.2.1
      have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
      have hxc : (p.2 : EuclideanSpace ℝ (Fin n)) ∈ C := p.2.2.1
      have hxn : (p.2 : EuclideanSpace ℝ (Fin n)) ≠ 0 := p.2.2.2
      have hw' : (δ / ‖(p.2 : EuclideanSpace ℝ (Fin n))‖) • (p.2 : EuclideanSpace ℝ (Fin n)) ∈ C :=
        hw _ hxn
      have hcomb : hval p =
          (1 - (p.1 : ℝ)) • ((δ / ‖(p.2 : EuclideanSpace ℝ (Fin n))‖) • (p.2 : EuclideanSpace ℝ (Fin n)))
            + (p.1 : ℝ) • (p.2 : EuclideanSpace ℝ (Fin n)) := by
        simp only [hval, smul_smul]
        rw [add_smul]
      rw [hcomb]
      exact hconv hw' hxc (by linarith) ht0 (by ring)
    have hval_ne : ∀ p : I × {x : EuclideanSpace ℝ (Fin n) // x ∈ C ∧ x ≠ 0}, hval p ≠ 0 := by
      intro p h
      have ht0 : 0 ≤ (p.1 : ℝ) := p.1.2.1
      have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
      have hxn : (p.2 : EuclideanSpace ℝ (Fin n)) ≠ 0 := p.2.2.2
      have hδn : 0 < δ / ‖(p.2 : EuclideanSpace ℝ (Fin n))‖ := div_pos hδpos (norm_pos_iff.mpr hxn)
      have hc : 0 < (1 - (p.1 : ℝ)) * (δ / ‖(p.2 : EuclideanSpace ℝ (Fin n))‖) + (p.1 : ℝ) := by
        rcases eq_or_lt_of_le ht0 with h0' | h0'
        · rw [← h0']; simpa using hδn
        · have h1 : 0 ≤ (1 - (p.1 : ℝ)) * (δ / ‖(p.2 : EuclideanSpace ℝ (Fin n))‖) :=
            mul_nonneg (by linarith) hδn.le
          linarith
      exact smul_ne_zero (ne_of_gt hc) hxn h
    have hcont : Continuous hval := by
      have ht : Continuous fun p : I × {x : EuclideanSpace ℝ (Fin n) // x ∈ C ∧ x ≠ 0} =>
          (p.1 : ℝ) := continuous_subtype_val.comp continuous_fst
      have hx : Continuous fun p : I × {x : EuclideanSpace ℝ (Fin n) // x ∈ C ∧ x ≠ 0} =>
          (p.2 : EuclideanSpace ℝ (Fin n)) := continuous_subtype_val.comp continuous_snd
      have hn : Continuous fun p : I × {x : EuclideanSpace ℝ (Fin n) // x ∈ C ∧ x ≠ 0} =>
          (δ / ‖(p.2 : EuclideanSpace ℝ (Fin n))‖) :=
        continuous_const.div hx.norm (fun p => norm_ne_zero_iff.mpr p.2.2.2)
      have hh : Continuous fun p : I × {x : EuclideanSpace ℝ (Fin n) // x ∈ C ∧ x ≠ 0} =>
          ((1 - (p.1 : ℝ)) * (δ / ‖(p.2 : EuclideanSpace ℝ (Fin n))‖) + (p.1 : ℝ))
            • (p.2 : EuclideanSpace ℝ (Fin n)) := ((continuous_const.sub ht).mul hn).add ht |>.smul hx
      simpa only [hval] using hh
    refine ⟨ContinuousMap.Homotopy.mk
      ⟨fun p => ⟨hval p, hval_mem p, hval_ne p⟩,
        Continuous.subtype_mk hcont (fun p => ⟨hval_mem p, hval_ne p⟩)⟩ ?_ ?_⟩
    · intro x
      apply Subtype.ext
      change hval (0, x) = (invFun (toFun x) : EuclideanSpace ℝ (Fin n))
      simp only [hval, invFun, toFun, ContinuousMap.coe_mk]
      rw [div_eq_mul_inv, smul_smul]
      norm_num
    · intro x
      apply Subtype.ext
      change hval (1, x) = (x : EuclideanSpace ℝ (Fin n))
      simp only [hval]
      rw [show ((1 : I) : ℝ) = 1 by rfl]
      simp
  · have hcomp : toFun.comp invFun =
        ContinuousMap.id (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      apply ContinuousMap.ext
      intro u
      apply Subtype.ext
      change ‖δ • (u : EuclideanSpace ℝ (Fin n))‖⁻¹ • (δ • (u : EuclideanSpace ℝ (Fin n)))
        = (u : EuclideanSpace ℝ (Fin n))
      rw [norm_smul, Real.norm_of_nonneg hδpos.le, sphere_norm_eq_one u, mul_one, smul_smul,
        inv_mul_cancel₀ hδpos.ne', one_smul]
    rw [hcomp]

/-! ## 4. The punctured product of the two caps -/

set_option maxHeartbeats 800000 in
/-- **The punctured product cap `Vset p q \ {ptP p q}` is homotopy equivalent to `S^(p+q-1)`.**

The identifying homeomorphism is
`Vset p q \ {pt} ≅ (tgtSet p (1/2) × tgtSet q (1/2)) \ {0} ≅ C \ {0}` for the open convex
neighbourhood `C = euclidSplit p q '' (tgtSet p (1/2) × tgtSet q (1/2))` of `0` in `ℝ^(p+q)`,
which is homeomorphic to `S^(p+q-1)` by `punctured_convex_homotopyEquiv`. -/
theorem punctured_cap_prod_sphere (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Nonempty (ContinuousMap.HomotopyEquiv
      {z : ↥(PSph p q) // z ∈ Vset p q ∧ z ≠ ptP p q}
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (p + q))) 1)) := by
  set Bp : Set (EuclideanSpace ℝ (Fin p)) := tgtSet (m := p) (1/2) with hBp
  set Bq : Set (EuclideanSpace ℝ (Fin q)) := tgtSet (m := q) (1/2) with hBq
  set Lh : (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃ₜ
      EuclideanSpace ℝ (Fin (p + q)) := (euclidSplit p q).toHomeomorph with hLh
  set C : Set (EuclideanSpace ℝ (Fin (p + q))) := Lh '' (Bp ×ˢ Bq) with hC
  have hBp_open : IsOpen Bp := by
    rw [hBp]
    show IsOpen {y : EuclideanSpace ℝ (Fin p) | (1 - 1/2) * ‖y‖ ^ 2 < 1 + 1/2}
    exact isOpen_lt (by fun_prop) (by fun_prop)
  have hBq_open : IsOpen Bq := by
    rw [hBq]
    show IsOpen {y : EuclideanSpace ℝ (Fin q) | (1 - 1/2) * ‖y‖ ^ 2 < 1 + 1/2}
    exact isOpen_lt (by fun_prop) (by fun_prop)
  have hBp_conv : Convex ℝ Bp := by rw [hBp]; exact tgtSet_convex (by norm_num)
  have hBq_conv : Convex ℝ Bq := by rw [hBq]; exact tgtSet_convex (by norm_num)
  have h0Bp : (0 : EuclideanSpace ℝ (Fin p)) ∈ Bp := by
    rw [hBp]
    show (1 - 1/2) * ‖(0 : EuclideanSpace ℝ (Fin p))‖ ^ 2 < 1 + 1/2
    rw [norm_zero]; norm_num
  have h0Bq : (0 : EuclideanSpace ℝ (Fin q)) ∈ Bq := by
    rw [hBq]
    show (1 - 1/2) * ‖(0 : EuclideanSpace ℝ (Fin q))‖ ^ 2 < 1 + 1/2
    rw [norm_zero]; norm_num
  have hC_open : IsOpen C := by
    rw [hC, hLh]
    exact (euclidSplit p q).toHomeomorph.isOpenMap _ (hBp_open.prod hBq_open)
  have hC_conv : Convex ℝ C := by
    rw [hC]
    have Lh_eq : ⇑Lh = ⇑(euclidSplit p q) := by rw [hLh, euclidSplit_homeo_coe p q]
    rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩ a b ha hb hab
    exact ⟨a • x' + b • y', hBp_conv.prod hBq_conv hx' hy' ha hb hab, by
      rw [Lh_eq]; simp only [map_add, map_smul]⟩
  have hiff : ∀ x : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q),
      x ∈ Bp ×ˢ Bq ↔ Lh x ∈ C := by
    intro x
    rw [hC]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => by
      obtain rfl := Lh.injective hyx; exact hy⟩
  have hC0 : (0 : EuclideanSpace ℝ (Fin (p + q))) ∈ C := by
    rw [hC]
    exact ⟨(0, 0), ⟨h0Bp, h0Bq⟩,
      by rw [hLh, euclidSplit_homeo_coe p q]; exact map_zero (euclidSplit p q)⟩
  set g : ↥(capA p) × ↥(capA q) ≃ₜ ↥C :=
    ((capTgtHomeo p).prodCongr (capTgtHomeo q)).trans
      (((Homeomorph.Set.prod Bp Bq).symm).trans (Lh.subtype hiff)) with hg
  set pt : ↥(capA p) × ↥(capA q) :=
    (⟨sphN p, sphN_mem_capA p⟩, ⟨sphN q, sphN_mem_capA q⟩) with hpt
  have gpt : g pt = (⟨0, hC0⟩ : ↥C) := by
    have h1 : ((capTgtHomeo p).prodCongr (capTgtHomeo q)) pt
        = ((⟨0, h0Bp⟩ : ↥Bp), (⟨0, h0Bq⟩ : ↥Bq)) := by
      show ((capTgtHomeo p) ⟨sphN p, sphN_mem_capA p⟩,
        (capTgtHomeo q) ⟨sphN q, sphN_mem_capA q⟩) = _
      rw [capTgtHomeo_sphN p, capTgtHomeo_sphN q]
    have h2 : (Homeomorph.Set.prod Bp Bq).symm ((⟨0, h0Bp⟩ : ↥Bp), (⟨0, h0Bq⟩ : ↥Bq))
        = (⟨(0, 0), ⟨h0Bp, h0Bq⟩⟩ : ↥(Bp ×ˢ Bq)) := by
      apply Subtype.ext; rfl
    have h3 : (Lh.subtype hiff) (⟨(0, 0), ⟨h0Bp, h0Bq⟩⟩ : ↥(Bp ×ˢ Bq)) = (⟨0, hC0⟩ : ↥C) := by
      apply Subtype.ext
      show Lh ((0, 0) : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) = 0
      rw [hLh, euclidSplit_homeo_coe p q]
      exact map_zero (euclidSplit p q)
    show g pt = _
    rw [hg, Homeomorph.trans_apply, Homeomorph.trans_apply, h1, h2, h3]
  -- the punctured product of the caps, via the complement of a point
  set ptB : ↥(capA p ×ˢ capA q) :=
    ⟨(sphN p, sphN q), ⟨sphN_mem_capA p, sphN_mem_capA q⟩⟩ with hptB
  have hsp : (Homeomorph.Set.prod (capA p) (capA q)) ptB = pt := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  have hiff2 : ∀ z : ↥(capA p ×ˢ capA q),
      ((z : ↥(PSph p q)) ≠ ptP p q) ↔ ((Homeomorph.Set.prod (capA p) (capA q)) z ≠ pt) := by
    intro z
    have hz : ((z : ↥(PSph p q)) = ptP p q) ↔ z = ptB := by
      rw [Subtype.ext_iff]; rfl
    rw [ne_eq, ne_eq, hz,
      show ((Homeomorph.Set.prod (capA p) (capA q)) z = pt) ↔ (z = ptB) from by
        rw [← hsp]; exact (Homeomorph.Set.prod (capA p) (capA q)).injective.eq_iff]
  have e12 : {z : ↥(PSph p q) // z ∈ Vset p q ∧ z ≠ ptP p q} ≃ₜ
      {w : ↥(capA p) × ↥(capA q) // w ≠ pt} :=
    (flatHomeo (q := fun z : ↥(PSph p q) => z ∈ capA p ×ˢ capA q)
      (P := fun z => z ≠ ptP p q)).symm.trans
      ((Homeomorph.Set.prod (capA p) (capA q)).subtype hiff2)
  have hiff3 : ∀ w : ↥(capA p) × ↥(capA q),
      (w ≠ pt) ↔ ((↑(g w) : EuclideanSpace ℝ (Fin (p + q))) ≠ 0) := by
    intro w
    have hzero : ((↑(g w) : EuclideanSpace ℝ (Fin (p + q))) = 0) ↔ (g w = (⟨0, hC0⟩ : ↥C)) := by
      constructor
      · intro h; exact Subtype.ext h
      · intro h; rw [h]
    rw [ne_eq, ne_eq, hzero, ← gpt, g.injective.eq_iff]
  have e3 : {w : ↥(capA p) × ↥(capA q) // w ≠ pt} ≃ₜ
      {x : ↥C // (↑x : EuclideanSpace ℝ (Fin (p + q))) ≠ 0} := g.subtype hiff3
  have e4 : {x : ↥C // (↑x : EuclideanSpace ℝ (Fin (p + q))) ≠ 0} ≃ₜ
      {x : EuclideanSpace ℝ (Fin (p + q)) // x ∈ C ∧ x ≠ 0} :=
    flatHomeo (q := fun x : EuclideanSpace ℝ (Fin (p + q)) => x ∈ C) (P := fun x => x ≠ 0)
  obtain ⟨he⟩ := punctured_convex_homotopyEquiv (p + q) C hC_open hC_conv hC0
  exact ⟨((e12.trans e3).trans e4).toHomotopyEquiv.trans he⟩

end

end Work.Cohomology
