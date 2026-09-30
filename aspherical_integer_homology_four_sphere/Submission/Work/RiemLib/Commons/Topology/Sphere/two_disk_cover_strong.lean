import Mathlib
import Submission.Work.RiemLib.Commons.Topology.Sphere.radial_extension
import Submission.Work.RiemLib.Commons.Topology.Sphere.two_disk_cover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Topology.Sphere

open Set Metric

namespace TwoDiskStrong

abbrev eball (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 1
abbrev bsphere (n : ℕ) : Set (eball n) := Metric.sphere (0 : eball n) 1
abbrev esphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := Metric.sphere 0 1

lemma bsphere_mem_iff (n : ℕ) (x : eball n) :
    x ∈ bsphere n ↔ ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  rw [Metric.mem_sphere, Subtype.dist_eq, dist_eq_norm]
  simp

lemma mem_closedBall_of_norm_eq_one {n : ℕ} {v : EuclideanSpace ℝ (Fin n)}
    (hv : ‖v‖ = 1) : v ∈ eball n := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hv]

/-- The canonical homeomorphism between the boundary of the closed unit ball `D^n` (a subtype of
the ball) and the unit sphere `S^{n-1}` of the ambient space. -/
noncomputable def sphToE (n : ℕ) (u : bsphere n) : esphere n :=
  ⟨(u.1 : EuclideanSpace ℝ (Fin n)), by
    rw [mem_sphere_zero_iff_norm]
    exact (bsphere_mem_iff n u.1).mp u.2⟩

noncomputable def sphToB (n : ℕ) (v : esphere n) : bsphere n :=
  ⟨⟨v.1, mem_closedBall_of_norm_eq_one (mem_sphere_zero_iff_norm.mp v.2)⟩, by
    rw [bsphere_mem_iff]
    exact mem_sphere_zero_iff_norm.mp v.2⟩

@[simp] lemma sphToE_coe (n : ℕ) (u : bsphere n) :
    ((sphToE n u : esphere n) : EuclideanSpace ℝ (Fin n))
      = (u.1 : EuclideanSpace ℝ (Fin n)) := rfl

@[simp] lemma sphToB_coe (n : ℕ) (v : esphere n) :
    ((sphToB n v : bsphere n).1 : EuclideanSpace ℝ (Fin n)) = v.1 := rfl

@[simp] lemma sphToB_val (n : ℕ) (v : esphere n) :
    ((sphToB n v : bsphere n) : eball n)
      = ⟨v.1, mem_closedBall_of_norm_eq_one (mem_sphere_zero_iff_norm.mp v.2)⟩ := rfl

lemma sphToB_sphToE (n : ℕ) (u : bsphere n) : sphToB n (sphToE n u) = u := by
  apply Subtype.ext; apply Subtype.ext; rfl

lemma sphToE_sphToB (n : ℕ) (v : esphere n) : sphToE n (sphToB n v) = v := by
  apply Subtype.ext; rfl

noncomputable def sphEquiv (n : ℕ) : bsphere n ≃ₜ esphere n where
  toFun := sphToE n
  invFun := sphToB n
  left_inv := sphToB_sphToE n
  right_inv := sphToE_sphToB n
  continuous_toFun := Continuous.subtype_mk
      (f := fun u : bsphere n => (u.1 : EuclideanSpace ℝ (Fin n)))
      ((continuous_subtype_val (p := fun x : EuclideanSpace ℝ (Fin n) => x ∈ eball n)).comp
        (continuous_subtype_val (p := fun x : eball n => x ∈ bsphere n)))
      (fun u => mem_sphere_zero_iff_norm.mpr ((bsphere_mem_iff n u.1).mp u.2))
  continuous_invFun := Continuous.subtype_mk
      (f := fun v : esphere n => (⟨v.1, mem_closedBall_of_norm_eq_one
        (mem_sphere_zero_iff_norm.mp v.2)⟩ : eball n))
      (Continuous.subtype_mk
        (continuous_subtype_val (p := fun x : EuclideanSpace ℝ (Fin n) => x ∈ esphere n)) _)
      (fun v => (bsphere_mem_iff n _).mpr (mem_sphere_zero_iff_norm.mp v.2))

lemma continuous_sphToB (n : ℕ) : Continuous (sphToB n) := (sphEquiv n).symm.continuous

lemma continuous_sphToE (n : ℕ) : Continuous (sphToE n) := (sphEquiv n).continuous

instance instCompactSpaceEsphere (n : ℕ) : CompactSpace (esphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)

def toEsphere {n : ℕ} (z : eball n) (hz : z ∈ bsphere n) : esphere n :=
  ⟨(z : EuclideanSpace ℝ (Fin n)),
    mem_sphere_zero_iff_norm.mpr ((bsphere_mem_iff n z).mp hz)⟩

@[simp] lemma toEsphere_coe {n : ℕ} (z : eball n) (hz : z ∈ bsphere n) :
    ((toEsphere z hz : esphere n) : EuclideanSpace ℝ (Fin n))
      = (z : EuclideanSpace ℝ (Fin n)) := rfl

/-! ### Elementary consequences of the two disk charts covering `X` -/

variable {X : Type*} [TopologicalSpace X] {n : ℕ} {A B : Set X}

lemma mem_B_of_eA_sphere (eA : A ≃ₜ eball n) (eB : B ≃ₜ eball n)
    (hAc : A ∩ B = eA ⁻¹' bsphere n) (hBc : A ∩ B = eB ⁻¹' bsphere n)
    (x : A) (hx : eA x ∈ bsphere n) : (x : X) ∈ B := by
  have h : (x : X) ∈ A ∩ B := by
    rw [hAc]
    exact ⟨x, hx, rfl⟩
  exact h.2

lemma mem_A_of_eB_sphere (eA : A ≃ₜ eball n) (eB : B ≃ₜ eball n)
    (hAc : A ∩ B = eA ⁻¹' bsphere n) (hBc : A ∩ B = eB ⁻¹' bsphere n)
    (y : B) (hy : eB y ∈ bsphere n) : (y : X) ∈ A := by
  have h : (y : X) ∈ A ∩ B := by
    rw [hBc]
    exact ⟨y, hy, rfl⟩
  exact h.1

lemma eB_mem_sphere_of_mem_A (eA : A ≃ₜ eball n) (eB : B ≃ₜ eball n)
    (hAc : A ∩ B = eA ⁻¹' bsphere n) (hBc : A ∩ B = eB ⁻¹' bsphere n)
    (y : B) (hy : (y : X) ∈ A) : eB y ∈ bsphere n := by
  have h : (y : X) ∈ A ∩ B := ⟨hy, y.2⟩
  rw [hBc] at h
  obtain ⟨b, hb, hby⟩ := h
  have hby' : b = y := Subtype.ext hby
  rw [← hby']
  exact hb

lemma eA_mem_sphere_of_mem_B (eA : A ≃ₜ eball n) (eB : B ≃ₜ eball n)
    (hAc : A ∩ B = eA ⁻¹' bsphere n) (hBc : A ∩ B = eB ⁻¹' bsphere n)
    (x : A) (hx : (x : X) ∈ B) : eA x ∈ bsphere n := by
  have h : (x : X) ∈ A ∩ B := ⟨x.2, hx⟩
  rw [hAc] at h
  obtain ⟨a, ha, hax⟩ := h
  have hax' : a = x := Subtype.ext hax
  rw [← hax']
  exact ha

/-! ### The gluing homeomorphism of the boundary sphere -/

/-- The boundary gluing `eB ∘ eA⁻¹`, as a self-homeomorphism of the unit sphere. -/
noncomputable def psiFun (eA : A ≃ₜ eball n) (eB : B ≃ₜ eball n)
    (hAc : A ∩ B = eA ⁻¹' bsphere n) (hBc : A ∩ B = eB ⁻¹' bsphere n)
    (v : esphere n) : esphere n :=
  let y : B := eB.symm (sphToB n v).1
  let hy : eB y ∈ bsphere n := by
    rw [show eB y = (sphToB n v).1 from Homeomorph.apply_symm_apply eB (sphToB n v).1]
    exact (sphToB n v).2
  let a : A := ⟨(y : X), mem_A_of_eB_sphere eA eB hAc hBc y hy⟩
  let ha : eA a ∈ bsphere n := eA_mem_sphere_of_mem_B eA eB hAc hBc a y.2
  ⟨(eA a : eball n), mem_sphere_zero_iff_norm.mpr ((bsphere_mem_iff n (eA a)).mp ha)⟩

noncomputable def psiInvFun (eA : A ≃ₜ eball n) (eB : B ≃ₜ eball n)
    (hAc : A ∩ B = eA ⁻¹' bsphere n) (hBc : A ∩ B = eB ⁻¹' bsphere n)
    (v : esphere n) : esphere n :=
  let x : A := eA.symm (sphToB n v).1
  let hx : eA x ∈ bsphere n := by
    rw [show eA x = (sphToB n v).1 from Homeomorph.apply_symm_apply eA (sphToB n v).1]
    exact (sphToB n v).2
  let b : B := ⟨(x : X), mem_B_of_eA_sphere eA eB hAc hBc x hx⟩
  let hb : eB b ∈ bsphere n := eB_mem_sphere_of_mem_A eA eB hAc hBc b x.2
  ⟨(eB b : eball n), mem_sphere_zero_iff_norm.mpr ((bsphere_mem_iff n (eB b)).mp hb)⟩

lemma psiInvFun_psiFun (eA : A ≃ₜ eball n) (eB : B ≃ₜ eball n)
    (hAc : A ∩ B = eA ⁻¹' bsphere n) (hBc : A ∩ B = eB ⁻¹' bsphere n)
    (v : esphere n) : psiInvFun eA eB hAc hBc (psiFun eA eB hAc hBc v) = v := by
  apply Subtype.ext
  simp only [psiFun, psiInvFun, sphToB_val, sphToB_coe, Homeomorph.symm_apply_apply,
    Homeomorph.apply_symm_apply, Subtype.coe_eta]

lemma psiFun_psiInvFun (eA : A ≃ₜ eball n) (eB : B ≃ₜ eball n)
    (hAc : A ∩ B = eA ⁻¹' bsphere n) (hBc : A ∩ B = eB ⁻¹' bsphere n)
    (v : esphere n) : psiFun eA eB hAc hBc (psiInvFun eA eB hAc hBc v) = v := by
  apply Subtype.ext
  simp only [psiFun, psiInvFun, sphToB_val, sphToB_coe, Homeomorph.symm_apply_apply,
    Homeomorph.apply_symm_apply, Subtype.coe_eta]

lemma continuous_psiFun (eA : A ≃ₜ eball n) (eB : B ≃ₜ eball n)
    (hAc : A ∩ B = eA ⁻¹' bsphere n) (hBc : A ∩ B = eB ⁻¹' bsphere n) :
    Continuous (psiFun eA eB hAc hBc) := by
  refine Continuous.subtype_mk
    (f := fun v : esphere n =>
      ((psiFun eA eB hAc hBc v : esphere n) : EuclideanSpace ℝ (Fin n))) ?_ ?_
  · have h1 : Continuous fun v : esphere n => ((sphToB n v : bsphere n) : eball n) :=
      continuous_subtype_val.comp (continuous_sphToB n)
    have h2 : Continuous fun v : esphere n => eB.symm ((sphToB n v : bsphere n) : eball n) :=
      eB.symm.continuous.comp h1
    have h3 : Continuous fun v : esphere n =>
        (eB.symm ((sphToB n v : bsphere n) : eball n) : X) :=
      continuous_subtype_val.comp h2
    have h4 : Continuous fun v : esphere n =>
        (⟨(eB.symm ((sphToB n v : bsphere n) : eball n) : X),
          mem_A_of_eB_sphere eA eB hAc hBc _ (by
            rw [show eB (eB.symm ((sphToB n v : bsphere n) : eball n))
                = ((sphToB n v : bsphere n) : eball n)
                from Homeomorph.apply_symm_apply eB _]
            exact (sphToB n v).2)⟩ : A) :=
      Continuous.subtype_mk h3 _
    have h5 : Continuous fun v : esphere n =>
        ((eA (⟨(eB.symm ((sphToB n v : bsphere n) : eball n) : X),
          mem_A_of_eB_sphere eA eB hAc hBc _ (by
            rw [show eB (eB.symm ((sphToB n v : bsphere n) : eball n))
                = ((sphToB n v : bsphere n) : eball n)
                from Homeomorph.apply_symm_apply eB _]
            exact (sphToB n v).2)⟩ : A) : eball n) : EuclideanSpace ℝ (Fin n)) :=
      continuous_subtype_val.comp (eA.continuous.comp h4)
    simpa only [psiFun] using h5

noncomputable def psiHomeomorph (eA : A ≃ₜ eball n) (eB : B ≃ₜ eball n)
    (hAc : A ∩ B = eA ⁻¹' bsphere n) (hBc : A ∩ B = eB ⁻¹' bsphere n) :
    esphere n ≃ₜ esphere n :=
  Continuous.homeoOfEquivCompactToT2
    (f := { toFun := psiFun eA eB hAc hBc
            invFun := psiInvFun eA eB hAc hBc
            left_inv := psiInvFun_psiFun eA eB hAc hBc
            right_inv := psiFun_psiInvFun eA eB hAc hBc })
    (continuous_psiFun eA eB hAc hBc)

@[simp] lemma psiHomeomorph_apply (eA : A ≃ₜ eball n) (eB : B ≃ₜ eball n)
    (hAc : A ∩ B = eA ⁻¹' bsphere n) (hBc : A ∩ B = eB ⁻¹' bsphere n) (v : esphere n) :
    psiHomeomorph eA eB hAc hBc v = psiFun eA eB hAc hBc v := rfl

lemma psiFun_apply_eB (eA : A ≃ₜ eball n) (eB : B ≃ₜ eball n)
    (hAc : A ∩ B = eA ⁻¹' bsphere n) (hBc : A ∩ B = eB ⁻¹' bsphere n)
    (y : B) (hyA : (y : X) ∈ A) (hz : eB y ∈ bsphere n) :
    ((psiFun eA eB hAc hBc (toEsphere (eB y) hz) : esphere n) : EuclideanSpace ℝ (Fin n))
      = (eA ⟨(y : X), hyA⟩ : EuclideanSpace ℝ (Fin n)) := by
  simp only [psiFun]
  congr 1
  congr 1
  apply Subtype.ext
  change (↑(eB.symm ((sphToB n (toEsphere (eB y) hz) : bsphere n) : eball n)) : X) = (↑y : X)
  rw [show ((sphToB n (toEsphere (eB y) hz) : bsphere n) : eball n) = eB y
        from Subtype.ext rfl, Homeomorph.symm_apply_apply]

/-! ### The radial extension and the resulting disk chart -/

lemma ballHomeomorph_inclusion (ψ : esphere n ≃ₜ esphere n) (v : esphere n) :
    ballHomeomorph ψ (Set.inclusion Metric.sphere_subset_closedBall v)
      = Set.inclusion Metric.sphere_subset_closedBall (ψ v) := by
  apply Subtype.ext
  simpa [ballHomeomorph_apply, ballMap] using coneMap_sphere ψ v

lemma ballHomeomorph_preimage_bsphere (ψ : esphere n ≃ₜ esphere n) :
    (ballHomeomorph ψ) ⁻¹' bsphere n = bsphere n := by
  ext z
  rw [Set.mem_preimage, bsphere_mem_iff, bsphere_mem_iff]
  have h : ((ballHomeomorph ψ z : eball n) : EuclideanSpace ℝ (Fin n))
      = coneMap ψ (z : EuclideanSpace ℝ (Fin n)) := rfl
  rw [h, norm_coneMap]

lemma ballHomeomorph_mem_bsphere_iff (ψ : esphere n ≃ₜ esphere n) (z : eball n) :
    ballHomeomorph ψ z ∈ bsphere n ↔ z ∈ bsphere n := by
  rw [← Set.mem_preimage, ballHomeomorph_preimage_bsphere]

end TwoDiskStrong

open TwoDiskStrong in
/-- **The double of a ball is a sphere, without a compatibility hypothesis on the two charts.**
Same setting as `Commons.Topology.Sphere.two_disk_cover` (`X` compact Hausdorff, `X = A ∪ B` with
`A`, `B` closed and homeomorphic to the closed unit ball `D^n` of `EuclideanSpace ℝ (Fin n)`, the
common part `A ∩ B` being exactly the boundary sphere of each), but now the two disk charts need
*not* agree on `A ∩ B`: the gluing homeomorphism `eB ∘ eA⁻¹` of the boundary sphere is absorbed by
the radial extension (`Commons.Topology.Sphere.radial_extension`), which extends it to a
homeomorphism of `D^n`; replacing `eB` by `Ψ ∘ eB` makes the two charts agree on `A ∩ B`, so
`Commons.Topology.Sphere.two_disk_cover` applies. -/
theorem two_disk_cover_strong {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∪ B = Set.univ)
    (eA : A ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (eB : B ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hAc : A ∩ B = eA ⁻¹' (Metric.sphere (0 : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) 1) 1))
    (hBc : A ∩ B = eB ⁻¹' (Metric.sphere (0 : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) 1) 1)) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  classical
  have hAc' : A ∩ B = eA ⁻¹' bsphere n := hAc
  have hBc' : A ∩ B = eB ⁻¹' bsphere n := hBc
  have hpre : (eB.trans (ballHomeomorph (psiHomeomorph eA eB hAc' hBc'))) ⁻¹' bsphere n
      = eB ⁻¹' bsphere n := by
    ext z
    rw [Set.mem_preimage, Set.mem_preimage, Homeomorph.trans_apply]
    exact ballHomeomorph_mem_bsphere_iff _ (eB z)
  have hBc'' : A ∩ B
      = (eB.trans (ballHomeomorph (psiHomeomorph eA eB hAc' hBc'))) ⁻¹' bsphere n := by
    rw [hpre]
    exact hBc'
  have hagree : ∀ (x : A) (y : B), (x : X) = (y : X) →
      eA x = eB.trans (ballHomeomorph (psiHomeomorph eA eB hAc' hBc')) y := by
    intro x y hxy
    have hyA : (y : X) ∈ A := by rw [← hxy]; exact x.2
    have hz : eB y ∈ bsphere n := eB_mem_sphere_of_mem_A eA eB hAc' hBc' y hyA
    have hΦ : ballHomeomorph (psiHomeomorph eA eB hAc' hBc') (eB y)
        = Set.inclusion Metric.sphere_subset_closedBall
            (psiHomeomorph eA eB hAc' hBc' (toEsphere (eB y) hz)) := by
      conv_lhs => rw [← show Set.inclusion Metric.sphere_subset_closedBall
            (toEsphere (eB y) hz) = eB y from Subtype.ext rfl]
      exact ballHomeomorph_inclusion _ _
    have heq : ballHomeomorph (psiHomeomorph eA eB hAc' hBc') (eB y) = eA x := by
      rw [hΦ]
      apply Subtype.ext
      show ((psiHomeomorph eA eB hAc' hBc' (toEsphere (eB y) hz) : esphere n)
          : EuclideanSpace ℝ (Fin n)) = (eA x : EuclideanSpace ℝ (Fin n))
      rw [psiHomeomorph_apply, psiFun_apply_eB eA eB hAc' hBc' y hyA hz]
      rw [show x = ⟨(y : X), hyA⟩ from (Subtype.ext hxy.symm).symm]
    exact heq.symm
  exact two_disk_cover hA hB hAB eA
    (eB.trans (ballHomeomorph (psiHomeomorph eA eB hAc' hBc'))) hAc' hBc'' hagree

end Commons.Topology.Sphere
