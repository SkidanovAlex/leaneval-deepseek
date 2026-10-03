import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.NCForm
import Submission.Work.ORLocInd.CohenLyndon.hnnSetup
import Submission.Work.ORLocInd.CohenLyndon.stabNcl_hedge_hninv
import Submission.Work.ORLocInd.CohenLyndon.hnnStruct

set_option autoImplicit false

universe u

namespace Work.ORLocInd.CohenLyndon

open Quiver
open HNNExtension

/-! ## Auxiliary facts about the normal closures -/

section Aux

variable {K : Type u} [Group K] {A B : Subgroup K} {φ : A ≃* B} {r : K}

/-- `of` carries the normal closure of `r` into the normal closure of `of r`. -/
theorem map_of_Mcl_le_Ncl :
    (Mcl (r := r)).map (HNNExtension.of (A := A) (B := B) (φ := φ)) ≤
      Ncl (A := A) (B := B) (φ := φ) (r := r) := by
  haveI : (Subgroup.comap (HNNExtension.of (A := A) (B := B) (φ := φ))
      (Ncl (A := A) (B := B) (φ := φ) (r := r))).Normal :=
    Subgroup.normalClosure_normal.comap _
  rw [Subgroup.map_le_iff_le_comap]
  refine Subgroup.normalClosure_le_normal ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact Subgroup.subset_normalClosure (Set.mem_singleton (HNNExtension.of r))

/-- The preimage in `K` of `⟪of r⟫` is `⟪r⟫_K`. -/
theorem comap_of_Ncl_eq_Mcl
    (hA : Subgroup.normalClosure ({r} : Set K) ⊓ A = ⊥)
    (hB : Subgroup.normalClosure ({r} : Set K) ⊓ B = ⊥) :
    Subgroup.comap (HNNExtension.of (A := A) (B := B) (φ := φ))
        (Ncl (A := A) (B := B) (φ := φ) (r := r)) = Mcl (r := r) := by
  refine le_antisymm ?_ ?_
  · intro m hm
    have h : (HNNExtension.of m : HNNExtension K A B φ) ∈
        (Mcl (r := r)).map (HNNExtension.of (A := A) (B := B) (φ := φ)) := by
      rw [← hnn_inf_range_eq (A := A) (B := B) (φ := φ) (r := r) hA hB]
      exact ⟨hm, ⟨m, rfl⟩⟩
    obtain ⟨m', hm', hm'e⟩ := Subgroup.mem_map.mp h
    rwa [HNNExtension.of_injective (A := A) (B := B) φ hm'e] at hm'
  · intro m hm
    exact map_of_Mcl_le_Ncl (Subgroup.mem_map.mpr ⟨m, hm, rfl⟩)

end Aux

/-! ## The free basis of `⟪r⟫_K` provided by the Cohen--Lyndon hypothesis -/

section Assembly

variable {K : Type u} [Group K] {A B : Subgroup K} {φ : A ≃* B} {r : K}

/-- The free basis of `⟪r⟫_K` provided by the Cohen--Lyndon hypothesis. -/
noncomputable def clBasis (h : Work.CohenLyndon.CohenLyndonNC r) :
    FreeGroupBasis ↥(h.choose) ↥(Mcl (r := r)) :=
  FreeGroupBasis.ofRepr (h.choose_spec.2.choose.symm)

theorem clBasis_apply (h : Work.CohenLyndon.CohenLyndonNC r) (t : ↥(h.choose)) :
    (((clBasis (r := r) h) t : ↥(Mcl (r := r))) : K) =
      (t : K) * r * (t : K)⁻¹ :=
  h.choose_spec.2.choose_spec t

/-- **The centralizer of `of r` in the HNN extension.** -/
theorem centralizer_of (hr : r ≠ 1) (hA : Subgroup.normalClosure ({r} : Set K) ⊓ A = ⊥)
    (hB : Subgroup.normalClosure ({r} : Set K) ⊓ B = ⊥) :
    Subgroup.centralizer ({HNNExtension.of r} : Set (HNNExtension K A B φ)) =
      (Subgroup.centralizer ({r} : Set K)).map
        (HNNExtension.of (A := A) (B := B) (φ := φ)) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
  constructor
  · intro hx
    have hx' : x * HNNExtension.of r * x⁻¹ ∈
        (HNNExtension.of (A := A) (B := B) (φ := φ)).range := by
      rw [hx, mul_assoc, mul_inv_cancel, mul_one]
      exact ⟨r, rfl⟩
    obtain ⟨k, hk⟩ := hnn_conj_mem_range (A := A) (B := B) (φ := φ) (r := r) hA hB
      (Subgroup.subset_normalClosure (Set.mem_singleton r)) hr hx'
    refine ⟨k, ?_, hk⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : (HNNExtension.of (A := A) (B := B) (φ := φ) (k * r) :
        HNNExtension K A B φ) = HNNExtension.of (r * k) := by
      rw [map_mul, map_mul, hk]
      exact hx
    exact HNNExtension.of_injective (A := A) (B := B) φ h2
  · rintro ⟨k, hk, rfl⟩
    have hkr : k * r = r * k := Subgroup.mem_centralizer_singleton_iff.mp hk
    rw [← map_mul, ← map_mul]
    exact congrArg (HNNExtension.of (A := A) (B := B) (φ := φ)) hkr

/-- **The quotient graph of the `Ncl`-action on the Bass--Serre tree is a tree** (JL Lemma 4.1). -/
theorem isTree_orbitV_Ncl :
    Work.ORBassSerre.IsTree
      (Work.ORBassSerre.orbitV ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))
        (Work.ORBassSerre.HNN.VSet (G := K) (A := A) (B := B) (φ := φ))) := by
  haveI : (Ncl (A := A) (B := B) (φ := φ) (r := r)).Normal :=
    Subgroup.normalClosure_normal
  refine Work.ORBassSerre.Action.isTree_orbitV_of_normalClosure_elliptic
    (G := HNNExtension K A B φ)
    (V := (Work.ORBassSerre.HNN.VSet (G := K) (A := A) (B := B) (φ := φ)))
    (bsGraph_isTree (A := A) (B := B) (φ := φ))
    (Ncl (A := A) (B := B) (φ := φ) (r := r))
    ({HNNExtension.of r} : Set (HNNExtension K A B φ)) ?_ rfl
  rintro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  exact ⟨baseV (A := A) (B := B) (φ := φ),
    rho_fixes_base (A := A) (B := B) (φ := φ) (r := r)⟩

end Assembly

/-! ## The coproduct basis -/

section CoprodBasis

/-- The element of `FreeGroupBasis.coprodI` attached to an element of one of the factors. -/
theorem freeGroupBasis_coprodI_apply {ι : Type u} {X : ι → Type u} {G : ι → Type u}
    [∀ i, Group (G i)] (B : ∀ i, FreeGroupBasis (X i) (G i)) (i : ι) (x : X i) :
    (Monoid.CoprodI.FreeGroupBasis.coprodI B) ⟨i, x⟩ = Monoid.CoprodI.of (B i x) := by
  change (FreeGroup.lift fun y : Σ i, X i => Monoid.CoprodI.of (B y.1 y.2))
    (FreeGroup.of ⟨i, x⟩) = _
  rw [FreeGroup.lift_apply_of]

end CoprodBasis

/-! ## The transfer theorem -/

/-- **Karrass--Solitar transfer of the Cohen--Lyndon property to an HNN extension.**
Let `K` be a group, `A B ≤ K` and `φ : A ≃* B`.  If `r ≠ 1` has the Cohen--Lyndon property in `K`
and if the normal closure `M := ⟪r⟫_K` meets both `A` and `B` trivially, then the image `of r` of
`r` in the HNN extension `K ∗_φ` has the Cohen--Lyndon property there.

This is Karrass--Solitar 1972, Theorem 1 (HNN case); see Antolín--Dicks--Linnell, arXiv:1002.1934,
Lemma 1 and Theorem 5.3, and Putnam, *One-relator groups*, equation (6.1): `⟪of r⟫_{K∗_φ}` is the
free product, over the `(⟪of r⟫, K)`-double cosets, of the conjugates of `M`, and
`⟪of r⟫_{K∗_φ} ∩ K = M`.  The hypotheses `M ⊓ A = ⊥` and `M ⊓ B = ⊥` are exactly the
Freiheitssatz input which makes that free product an ordinary one (no amalgamation). -/
theorem cohenLyndonNC_hnn {K : Type u} [Group K] (A B : Subgroup K) (φ : A ≃* B) {r : K}
    (hr : r ≠ 1) (h : Work.CohenLyndon.CohenLyndonNC r)
    (hA : Subgroup.normalClosure ({r} : Set K) ⊓ A = ⊥)
    (hB : Subgroup.normalClosure ({r} : Set K) ⊓ B = ⊥) :
    Work.CohenLyndon.CohenLyndonNC (HNNExtension.of r : HNNExtension K A B φ) := by
  classical
  haveI : Nonempty (Work.ORBassSerre.HNN.VSet (G := K) (A := A) (B := B) (φ := φ)) :=
    ⟨baseV (A := A) (B := B) (φ := φ)⟩
  -- the Bass--Serre structure theorem for the action of `Ncl` on the Bass--Serre tree
  obtain ⟨Ω, x, hcov, hinj, e₀, he₀⟩ :=
    hnn_struct
      (Γ := ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)))
      (V := Work.ORBassSerre.HNN.VSet (G := K) (A := A) (B := B) (φ := φ))
      (bsGraph_isTree (A := A) (B := B) (φ := φ))
      (stabNcl_hedge_hninv.{u, u, u} (A := A) (B := B) (φ := φ) (r := r) hA hB).2
      (stabNcl_hedge_hninv.{u, u, u} (A := A) (B := B) (φ := φ) (r := r) hA hB).1
      (isTree_orbitV_Ncl.{u, u} (A := A) (B := B) (φ := φ) (r := r))
  -- a lift of the vertices `x i` to elements of the HNN extension
  let gp : Ω → HNNExtension K A B φ := fun i => Quotient.out (x i)
  have hgp : ∀ i : Ω, Work.ORBassSerre.HNN.qmk (gp i) = x i := fun i => Quotient.out_eq (x i)
  -- the stabilizer of `x i` is a conjugate of `of Mcl`
  have hstabv : ∀ i : Ω,
      MulAction.stabilizer ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)) (x i) =
        (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (gp i)))
          (Subgroup.map (HNNExtension.of (A := A) (B := B) (φ := φ)) (Mcl (r := r)))).comap
            (Ncl (A := A) (B := B) (φ := φ) (r := r)).subtype := by
    intro i
    rw [← hgp i, ← vtxOf_eq_qmk (A := A) (B := B) (φ := φ) (gp i)]
    exact stabilizerNcl_vtx (A := A) (B := B) (φ := φ) (r := r) hA hB (gp i)
  have hMN : (Mcl (r := r)).map (HNNExtension.of (A := A) (B := B) (φ := φ)) ≤
      Ncl (A := A) (B := B) (φ := φ) (r := r) := map_of_Mcl_le_Ncl
  have hgen_mem : ∀ (i : Ω) {m : K}, m ∈ Mcl (r := r) →
      gp i * HNNExtension.of m * (gp i)⁻¹ ∈ Ncl (A := A) (B := B) (φ := φ) (r := r) := by
    intro i m hm
    have hmem1 : HNNExtension.of m ∈ (Mcl (r := r)).map
        (HNNExtension.of (A := A) (B := B) (φ := φ)) :=
      Subgroup.mem_map.mpr ⟨m, hm, rfl⟩
    exact (Subgroup.normalClosure_normal
      (s := ({HNNExtension.of r} : Set (HNNExtension K A B φ)))).conj_mem _
      (hMN hmem1) (gp i)
  have hstab_mem : ∀ (i : Ω) {m : K}, (hm : m ∈ Mcl (r := r)) →
      (⟨gp i * HNNExtension.of m * (gp i)⁻¹, hgen_mem i hm⟩ :
        ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)))
        ∈ MulAction.stabilizer ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)) (x i) := by
    intro i m hm
    have hmem1 : HNNExtension.of m ∈ (Mcl (r := r)).map
        (HNNExtension.of (A := A) (B := B) (φ := φ)) :=
      Subgroup.mem_map.mpr ⟨m, hm, rfl⟩
    rw [hstabv i]
    refine Subgroup.mem_comap.mpr ?_
    refine Subgroup.mem_map.mpr ⟨HNNExtension.of m, hmem1, ?_⟩
    show MulAut.conj (gp i) (HNNExtension.of m) = gp i * HNNExtension.of m * (gp i)⁻¹
    rw [MulAut.conj_apply]
  -- the inverse of the above
  have hstab_inv : ∀ (i : Ω)
      (z : ↥(MulAction.stabilizer ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)) (x i))),
      ∃ m : K, m ∈ Mcl (r := r) ∧
        HNNExtension.of m =
          (gp i)⁻¹ * ((z : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) :
            HNNExtension K A B φ) * gp i := by
    intro i z
    have hz : ((z : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) :
        HNNExtension K A B φ) ∈
        (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (gp i)))
          (Subgroup.map (HNNExtension.of (A := A) (B := B) (φ := φ)) (Mcl (r := r)))) := by
      have h2 : (z : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) ∈
          (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (gp i)))
            (Subgroup.map (HNNExtension.of (A := A) (B := B) (φ := φ))
              (Mcl (r := r)))).comap
              (Ncl (A := A) (B := B) (φ := φ) (r := r)).subtype := by
        rw [← hstabv i]
        exact z.2
      exact Subgroup.mem_comap.mp h2
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hz
    obtain ⟨m, hm, hme⟩ := Subgroup.mem_map.mp hy
    refine ⟨m, hm, ?_⟩
    rw [← hme] at hye
    have hye' : MulAut.conj (gp i) (HNNExtension.of m) =
        ((z : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) : HNNExtension K A B φ) := hye
    rw [MulAut.conj_apply] at hye'
    rw [← hye']
    group
  -- the multiplication equivalence `⟪r⟫_K ≃* Stab (x i)`
  let mapΨ : ∀ i : Ω, ↥(Mcl (r := r)) →*
      ↥(MulAction.stabilizer ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)) (x i)) := by
    intro i
    refine { toFun := ?_, map_one' := ?_, map_mul' := ?_ }
    · intro m
      exact ⟨⟨gp i * HNNExtension.of (m : K) * (gp i)⁻¹, hgen_mem i m.2⟩, hstab_mem i m.2⟩
    · refine Subtype.ext (Subtype.ext ?_)
      simp
    · intro a b
      refine Subtype.ext (Subtype.ext ?_)
      show gp i * HNNExtension.of ((a * b : ↥(Mcl (r := r))) : K) * (gp i)⁻¹ =
        (gp i * HNNExtension.of (a : K) * (gp i)⁻¹) *
          (gp i * HNNExtension.of (b : K) * (gp i)⁻¹)
      rw [Subgroup.coe_mul, map_mul]
      group
  have mapΨ_apply : ∀ (i : Ω) (m : ↥(Mcl (r := r))),
      (((mapΨ i m : ↥(MulAction.stabilizer ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))
        (x i))) : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) : HNNExtension K A B φ) =
      gp i * HNNExtension.of (m : K) * (gp i)⁻¹ := fun i m => rfl
  have inj_mapΨ : ∀ i : Ω, Function.Injective (mapΨ i) := by
    intro i a b hab
    have h2 : gp i * HNNExtension.of (a : K) * (gp i)⁻¹ =
        gp i * HNNExtension.of (b : K) * (gp i)⁻¹ := by
      have h3 := congrArg (fun w : ↥(MulAction.stabilizer
        ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)) (x i)) =>
          ((w : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) :
            HNNExtension K A B φ)) hab
      simpa only [mapΨ_apply] using h3
    exact Subtype.ext (HNNExtension.of_injective (A := A) (B := B) φ
      (mul_left_cancel (mul_right_cancel h2)))
  have surj_mapΨ : ∀ i : Ω, Function.Surjective (mapΨ i) := by
    intro i z
    obtain ⟨m, hm, hme⟩ := hstab_inv i z
    refine ⟨⟨m, hm⟩, Subtype.ext (Subtype.ext ?_)⟩
    show gp i * HNNExtension.of m * (gp i)⁻¹ =
      ((z : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) : HNNExtension K A B φ)
    rw [hme]
    group
  let Ψ : ∀ i : Ω, ↥(Mcl (r := r)) ≃*
      ↥(MulAction.stabilizer ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)) (x i)) :=
    fun i => MulEquiv.ofBijective (mapΨ i) ⟨inj_mapΨ i, surj_mapΨ i⟩
  have hΨ : ∀ (i : Ω) (m : ↥(Mcl (r := r))),
      (((Ψ i m : ↥(MulAction.stabilizer ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)) (x i))) :
        ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) : HNNExtension K A B φ) =
      gp i * HNNExtension.of (m : K) * (gp i)⁻¹ := fun i m => mapΨ_apply i m
  -- the basis of each vertex stabilizer
  let basis : ∀ i : Ω, FreeGroupBasis ↥(h.choose)
      ↥(MulAction.stabilizer ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)) (x i)) :=
    fun i => (clBasis (r := r) h).map (Ψ i)
  have hbasis : ∀ (i : Ω) (t : ↥(h.choose)),
      (((basis i t : ↥(MulAction.stabilizer ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))
          (x i))) : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) : HNNExtension K A B φ) =
      (gp i * HNNExtension.of (t : K)) * HNNExtension.of r *
        (gp i * HNNExtension.of (t : K))⁻¹ := by
    intro i t
    rw [show basis i t = Ψ i (clBasis (r := r) h t) from FreeGroupBasis.map_apply _ _ _]
    rw [hΨ]
    rw [clBasis_apply (r := r) h t, map_mul, map_mul, map_inv]
    group
  -- the free product of the vertex stabilizers
  let Bfree : FreeGroupBasis (Σ i : Ω, ↥(h.choose))
      (Monoid.CoprodI (fun i : Ω => ↥(MulAction.stabilizer
        ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)) (x i)))) :=
    Monoid.CoprodI.FreeGroupBasis.coprodI basis
  let Bcop : FreeGroupBasis (Σ i : Ω, ↥(h.choose))
      ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)) := Bfree.map e₀
  have hcop_apply : ∀ (i : Ω) (t : ↥(h.choose)),
      Bcop ⟨i, t⟩ = (basis i t :
        ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) := by
    intro i t
    show e₀ (Bfree ⟨i, t⟩) = _
    have h1 := freeGroupBasis_coprodI_apply (ι := Ω) (X := fun _ : Ω => ↥(h.choose))
        (G := fun i : Ω => ↥(MulAction.stabilizer
          ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)) (x i))) basis i t
    rw [h1, he₀]
  have hBcoeff : ∀ (p : Σ i : Ω, ↥(h.choose)),
      (((Bcop p : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) : HNNExtension K A B φ)) =
      (gp p.1 * HNNExtension.of (p.2 : K)) * HNNExtension.of r *
        (gp p.1 * HNNExtension.of (p.2 : K))⁻¹ := by
    rintro ⟨i, t⟩
    rw [hcop_apply i t]
    exact hbasis i t
  -- the reindexing along the map `(i,t) ↦ gp i * of t`
  let Tf : (Σ i : Ω, ↥(h.choose)) → HNNExtension K A B φ :=
    fun p => gp p.1 * HNNExtension.of (p.2 : K)
  have hTf_inj : Function.Injective Tf := by
    rintro ⟨i, t⟩ ⟨j, s⟩ hab
    have hab' : gp i * HNNExtension.of (t : K) = gp j * HNNExtension.of (s : K) := hab
    have h1 : Work.ORBassSerre.HNN.qmk (gp i) = Work.ORBassSerre.HNN.qmk (gp j) := by
      have h2 : Work.ORBassSerre.HNN.qmk (gp i * HNNExtension.of (t : K)) =
          Work.ORBassSerre.HNN.qmk (gp j * HNNExtension.of (s : K)) := by rw [hab']
      rwa [Work.ORBassSerre.HNN.qmk_mul_of, Work.ORBassSerre.HNN.qmk_mul_of] at h2
    have hij : i = j := hinj i j ⟨1, by rw [← hgp i, ← hgp j, h1, one_smul]⟩
    subst hij
    have hts : t = s := Subtype.ext (HNNExtension.of_injective (A := A) (B := B) φ
      (mul_left_cancel hab'))
    subst hts
    rfl
  let T' : Set (HNNExtension K A B φ) := Set.range Tf
  let ee : (Σ i : Ω, ↥(h.choose)) ≃ ↥T' := Equiv.ofInjective Tf hTf_inj
  have hee : ∀ t : ↥T', Tf (ee.symm t) = (t : HNNExtension K A B φ) := by
    intro t
    have h1 : ((ee (ee.symm t) : ↥T') : HNNExtension K A B φ) =
        (t : HNNExtension K A B φ) := by
      rw [Equiv.apply_symm_apply]
    exact h1
  have hBtr : ∀ t : ↥T', ((((Bcop.reindex ee) t :
        ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) : HNNExtension K A B φ)) =
      (t : HNNExtension K A B φ) * HNNExtension.of r * (t : HNNExtension K A B φ)⁻¹ := by
    intro t
    have ht : gp (ee.symm t).1 * HNNExtension.of ((ee.symm t).2 : K) =
        (t : HNNExtension K A B φ) := hee t
    have h1 : (Bcop.reindex ee) t = Bcop (ee.symm t) :=
      FreeGroupBasis.reindex_apply Bcop ee t
    rw [h1, hBcoeff (ee.symm t), ht]
  -- the transversal property
  let P : Subgroup (HNNExtension K A B φ) :=
    Subgroup.normalClosure ({HNNExtension.of r} : Set (HNNExtension K A B φ)) ⊔
      Subgroup.centralizer ({HNNExtension.of r} : Set (HNNExtension K A B φ))
  let Q : Subgroup K :=
    Subgroup.normalClosure ({r} : Set K) ⊔ Subgroup.centralizer ({r} : Set K)
  have hP_char : ∀ y : HNNExtension K A B φ, y ∈ P ↔
      ∃ n ∈ Ncl (A := A) (B := B) (φ := φ) (r := r),
        ∃ c ∈ Subgroup.centralizer ({r} : Set K), y = n * HNNExtension.of c := by
    intro y
    have hPeq : P = Ncl (A := A) (B := B) (φ := φ) (r := r) ⊔
        (Subgroup.centralizer ({r} : Set K)).map (HNNExtension.of (A := A) (B := B) (φ := φ)) := by
      show Subgroup.normalClosure ({HNNExtension.of r} : Set (HNNExtension K A B φ)) ⊔
        Subgroup.centralizer ({HNNExtension.of r} : Set (HNNExtension K A B φ)) = _
      rw [centralizer_of (A := A) (B := B) (φ := φ) hr hA hB]
    rw [hPeq, Subgroup.mem_sup_of_normal_left]
    constructor
    · rintro ⟨n, hn, z, hz, hyz⟩
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
      exact ⟨n, hn, c, hc, hyz.symm⟩
    · rintro ⟨n, hn, c, hc, rfl⟩
      exact ⟨n, hn, HNNExtension.of c, Subgroup.mem_map.mpr ⟨c, hc, rfl⟩, rfl⟩
  have hCof_char : ∀ y : HNNExtension K A B φ,
      y ∈ (Ncl (A := A) (B := B) (φ := φ) (r := r) ⊔
        (Subgroup.centralizer ({r} : Set K)).map
          (HNNExtension.of (A := A) (B := B) (φ := φ))) ↔
      ∃ n ∈ Ncl (A := A) (B := B) (φ := φ) (r := r),
        ∃ c ∈ Subgroup.centralizer ({r} : Set K), y = n * HNNExtension.of c := by
    intro y
    rw [Subgroup.mem_sup_of_normal_left]
    constructor
    · rintro ⟨n, hn, z, hz, h⟩
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
      exact ⟨n, hn, c, hc, h.symm⟩
    · rintro ⟨n, hn, c, hc, rfl⟩
      exact ⟨n, hn, HNNExtension.of c, Subgroup.mem_map.mpr ⟨c, hc, rfl⟩, rfl⟩
  have hof_sup : ∀ y : K, HNNExtension.of y ∈
      (Ncl (A := A) (B := B) (φ := φ) (r := r) ⊔
        (Subgroup.centralizer ({r} : Set K)).map
          (HNNExtension.of (A := A) (B := B) (φ := φ))) ↔ y ∈ Q := by
    intro y
    rw [hCof_char]
    constructor
    · rintro ⟨n, hn, c, hc, hyc⟩
      have h1 : HNNExtension.of (y * c⁻¹) ∈ Ncl (A := A) (B := B) (φ := φ) (r := r) := by
        have hthis : (n : HNNExtension K A B φ) =
            HNNExtension.of y * (HNNExtension.of c)⁻¹ := by rw [hyc]; group
        rw [map_mul, map_inv, ← hthis]
        exact hn
      have h2 : y * c⁻¹ ∈ Mcl (r := r) := by
        rw [← comap_of_Ncl_eq_Mcl (A := A) (B := B) (φ := φ) (r := r) hA hB]
        exact h1
      exact Subgroup.mem_sup_of_normal_left.mpr
        ⟨y * c⁻¹, h2, c, hc, by group⟩
    · rintro hy
      obtain ⟨m, hm, c, hc, hmc⟩ := Subgroup.mem_sup_of_normal_left.mp hy
      refine ⟨HNNExtension.of m, ?_, c, hc, ?_⟩
      · exact hMN (Subgroup.mem_map.mpr ⟨m, hm, rfl⟩)
      · rw [← hmc, map_mul]
  -- transport of the `K`-side Cohen--Lyndon condition through `of`
  have hkey : ∀ (k s : K) (n : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))),
      HNNExtension.of k⁻¹ * (n : HNNExtension K A B φ) * HNNExtension.of s ∈ P ↔
      k⁻¹ * s ∈ Q := by
    intro k s n
    have hmain : HNNExtension.of k⁻¹ * (n : HNNExtension K A B φ) * HNNExtension.of s ∈ P ↔
        HNNExtension.of (k⁻¹ * s) ∈ (Ncl (A := A) (B := B) (φ := φ) (r := r) ⊔
          (Subgroup.centralizer ({r} : Set K)).map
            (HNNExtension.of (A := A) (B := B) (φ := φ))) := by
      rw [hP_char, hCof_char]
      constructor
      · rintro ⟨a, ha, c, hc, hac⟩
        have hs : HNNExtension.of s =
            (n : HNNExtension K A B φ)⁻¹ * HNNExtension.of k *
              (a : HNNExtension K A B φ) * HNNExtension.of c := by
          calc HNNExtension.of s
              = (HNNExtension.of k⁻¹ * (n : HNNExtension K A B φ))⁻¹ *
                  (HNNExtension.of k⁻¹ * (n : HNNExtension K A B φ) *
                    HNNExtension.of s) := by group
            _ = (HNNExtension.of k⁻¹ * (n : HNNExtension K A B φ))⁻¹ *
                  ((a : HNNExtension K A B φ) * HNNExtension.of c) := by rw [hac]
            _ = (n : HNNExtension K A B φ)⁻¹ * HNNExtension.of k *
                  (a : HNNExtension K A B φ) * HNNExtension.of c := by
                  simp only [map_inv, inv_inv]; group
        refine ⟨HNNExtension.of k⁻¹ * (n : HNNExtension K A B φ)⁻¹ *
            HNNExtension.of k * (a : HNNExtension K A B φ), ?_, c, hc, ?_⟩
        · refine (Ncl (A := A) (B := B) (φ := φ) (r := r)).mul_mem ?_ ha
          simpa using (Subgroup.normalClosure_normal
            (s := ({HNNExtension.of r} : Set (HNNExtension K A B φ)))).conj_mem _
            (Subgroup.inv_mem _ n.2) (HNNExtension.of k⁻¹)
        · rw [map_mul, hs]; group
      · rintro ⟨a, ha, c, hc, hac⟩
        have h2 : HNNExtension.of k⁻¹ * HNNExtension.of s =
            (a : HNNExtension K A B φ) * HNNExtension.of c := by
          rw [← map_mul, hac]
        refine ⟨HNNExtension.of k⁻¹ * (n : HNNExtension K A B φ) * HNNExtension.of k *
          (a : HNNExtension K A B φ), ?_, c, hc, ?_⟩
        · refine (Ncl (A := A) (B := B) (φ := φ) (r := r)).mul_mem ?_ ha
          simpa using (Subgroup.normalClosure_normal
            (s := ({HNNExtension.of r} : Set (HNNExtension K A B φ)))).conj_mem _ n.2
            (HNNExtension.of k⁻¹)
        · calc HNNExtension.of k⁻¹ * (n : HNNExtension K A B φ) * HNNExtension.of s
              = HNNExtension.of k⁻¹ * (n : HNNExtension K A B φ) * HNNExtension.of k *
                  (HNNExtension.of k⁻¹ * HNNExtension.of s) := by
                  simp only [map_inv, inv_inv]; group
            _ = HNNExtension.of k⁻¹ * (n : HNNExtension K A B φ) * HNNExtension.of k *
                  ((a : HNNExtension K A B φ) * HNNExtension.of c) := by rw [h2]
            _ = (HNNExtension.of k⁻¹ * (n : HNNExtension K A B φ) *
                  HNNExtension.of k * (a : HNNExtension K A B φ)) *
                  HNNExtension.of c := by
                  simp only [map_inv, inv_inv]; group
    rw [hmain, hof_sup]
  -- the double-coset index determined by an element
  have hNK : ∀ (i j : Ω) (n : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) (m : K),
      (gp i)⁻¹ * gp j = (n : HNNExtension K A B φ) * HNNExtension.of m → i = j := by
    intro i j n m hnm
    have hgpj : gp j = gp i * (n : HNNExtension K A B φ) * HNNExtension.of m := by
      calc gp j = gp i * ((gp i)⁻¹ * gp j) := by group
        _ = gp i * ((n : HNNExtension K A B φ) * HNNExtension.of m) := by rw [hnm]
        _ = gp i * (n : HNNExtension K A B φ) * HNNExtension.of m := by group
    have hNclMem : gp i * (n : HNNExtension K A B φ) * (gp i)⁻¹ ∈
        Ncl (A := A) (B := B) (φ := φ) (r := r) :=
      (Subgroup.normalClosure_normal
        (s := ({HNNExtension.of r} : Set (HNNExtension K A B φ)))).conj_mem _ n.2 (gp i)
    have hq : ∃ γ : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)), x j = γ • x i := by
      refine ⟨⟨gp i * (n : HNNExtension K A B φ) * (gp i)⁻¹, hNclMem⟩, ?_⟩
      have h2 : Work.ORBassSerre.HNN.qmk (gp j) = Work.ORBassSerre.HNN.qmk
            ((gp i * (n : HNNExtension K A B φ) * (gp i)⁻¹) * gp i) := by
        rw [hgpj, Work.ORBassSerre.HNN.qmk_mul_of]
        congr 1
        group
      calc x j = Work.ORBassSerre.HNN.qmk (gp j) := (hgp j).symm
        _ = Work.ORBassSerre.HNN.qmk
              ((gp i * (n : HNNExtension K A B φ) * (gp i)⁻¹) * gp i) := h2
        _ = (⟨gp i * (n : HNNExtension K A B φ) * (gp i)⁻¹, hNclMem⟩ :
              ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)))
              • Work.ORBassSerre.HNN.qmk (gp i) := rfl
        _ = (⟨gp i * (n : HNNExtension K A B φ) * (gp i)⁻¹, hNclMem⟩ :
              ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) • x i := by rw [hgp i]
    exact (hinj j i hq).symm
  -- the decomposition of an arbitrary element
  have hdecomp : ∀ u : HNNExtension K A B φ, ∃ i : Ω,
      ∃ γ : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r)), ∃ k : K,
      u = (γ : HNNExtension K A B φ) * gp i * HNNExtension.of k := by
    intro u
    obtain ⟨i, γ, hγ⟩ := hcov (u • baseV (A := A) (B := B) (φ := φ))
    refine ⟨i, γ, ?_⟩
    have h1 : Work.ORBassSerre.HNN.qmk u =
        Work.ORBassSerre.HNN.qmk ((γ : HNNExtension K A B φ) * gp i) := by
      have h3 : u • baseV (A := A) (B := B) (φ := φ) =
          (γ : HNNExtension K A B φ) • Work.ORBassSerre.HNN.qmk (gp i) := by
        rw [hgp i]
        exact hγ
      have h4 := h3
      rw [Work.ORBassSerre.HNN.smul_qmk, Work.ORBassSerre.HNN.smul_qmk, mul_one] at h4
      exact h4
    obtain ⟨m, hm⟩ := Work.ORBassSerre.HNN.exists_eq_mul_of_qmk_eq h1
    refine ⟨m⁻¹, ?_⟩
    have h5 : u = (γ : HNNExtension K A B φ) * gp i * (HNNExtension.of m)⁻¹ := by
      rw [hm]; group
    rw [h5, map_inv]
  -- the two numerical lemmas
  have hdiff : ∀ (u : HNNExtension K A B φ) (i : Ω)
      (γ : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) (k : K)
      (_ : u = (γ : HNNExtension K A B φ) * gp i * HNNExtension.of k) (j : Ω) (s : K),
      u⁻¹ * (gp j * HNNExtension.of s) ∈ P → i = j := by
    intro u i γ k hu j s hmem
    have h1 : u⁻¹ * (gp j * HNNExtension.of s) = HNNExtension.of k⁻¹ *
        ((gp i)⁻¹ * (γ : HNNExtension K A B φ)⁻¹ * gp j) * HNNExtension.of s := by
      rw [hu]; simp only [map_inv, inv_inv]; group
    rw [h1] at hmem
    rw [hP_char] at hmem
    obtain ⟨n, hn, c, hc, hnc⟩ := hmem
    have hw : (gp i)⁻¹ * (γ : HNNExtension K A B φ)⁻¹ * gp j ∈
        (Ncl (A := A) (B := B) (φ := φ) (r := r) ⊔
          (HNNExtension.of (A := A) (B := B) (φ := φ)).range) := by
      refine Subgroup.mem_sup_of_normal_left.mpr
        ⟨HNNExtension.of k * n * HNNExtension.of k⁻¹, ?_,
          HNNExtension.of (k * c * s⁻¹), ⟨k * c * s⁻¹, rfl⟩, ?_⟩
      · exact (Subgroup.normalClosure_normal
          (s := ({HNNExtension.of r} : Set (HNNExtension K A B φ)))).conj_mem _
          hn (HNNExtension.of k)
      · calc (HNNExtension.of k * n * HNNExtension.of k⁻¹) *
              HNNExtension.of (k * c * s⁻¹)
            = HNNExtension.of k * n * HNNExtension.of c * HNNExtension.of s⁻¹ := by
              rw [map_mul, map_mul]; simp only [map_inv, inv_inv]; group
          _ = HNNExtension.of k *
                (n * HNNExtension.of c) * HNNExtension.of s⁻¹ := by
                simp only [map_inv, inv_inv]; group
          _ = HNNExtension.of k *
                (HNNExtension.of k⁻¹ *
                  ((gp i)⁻¹ * (γ : HNNExtension K A B φ)⁻¹ * gp j) *
                    HNNExtension.of s) * HNNExtension.of s⁻¹ := by rw [← hnc]
          _ = (gp i)⁻¹ * (γ : HNNExtension K A B φ)⁻¹ * gp j := by
                simp only [map_inv, inv_inv]; group
    rw [Subgroup.mem_sup_of_normal_left] at hw
    obtain ⟨n', hn', z, hz, hnz⟩ := hw
    obtain ⟨m, rfl⟩ := hz
    refine hNK i j ⟨(gp i)⁻¹ * (γ : HNNExtension K A B φ) * gp i * n', ?_⟩ m ?_
    · refine (Ncl (A := A) (B := B) (φ := φ) (r := r)).mul_mem ?_ hn'
      simpa using (Subgroup.normalClosure_normal
          (s := ({HNNExtension.of r} : Set (HNNExtension K A B φ)))).conj_mem _
          γ.2 (gp i)⁻¹
    · calc (gp i)⁻¹ * gp j
            = ((gp i)⁻¹ * (γ : HNNExtension K A B φ) * gp i) *
                ((gp i)⁻¹ * (γ : HNNExtension K A B φ)⁻¹ * gp j) := by group
        _ = ((gp i)⁻¹ * (γ : HNNExtension K A B φ) * gp i) *
                (n' * HNNExtension.of m) := by rw [hnz]
        _ = ((gp i)⁻¹ * (γ : HNNExtension K A B φ) * gp i * n') *
                HNNExtension.of m := by group
  have hsame : ∀ (u : HNNExtension K A B φ) (i : Ω)
      (γ : ↥(Ncl (A := A) (B := B) (φ := φ) (r := r))) (k : K)
      (_ : u = (γ : HNNExtension K A B φ) * gp i * HNNExtension.of k) (s : K),
      u⁻¹ * (gp i * HNNExtension.of s) ∈ P ↔ k⁻¹ * s ∈ Q := by
    intro u i γ k hu s
    have h1 : u⁻¹ * (gp i * HNNExtension.of s) = HNNExtension.of k⁻¹ *
        ((gp i)⁻¹ * (γ : HNNExtension K A B φ)⁻¹ * gp i) * HNNExtension.of s := by
      rw [hu]; simp only [map_inv, inv_inv]; group
    have hn : (gp i)⁻¹ * (γ : HNNExtension K A B φ)⁻¹ * gp i ∈
        Ncl (A := A) (B := B) (φ := φ) (r := r) := by
      simpa using (Subgroup.normalClosure_normal
        (s := ({HNNExtension.of r} : Set (HNNExtension K A B φ)))).conj_mem _
        (Subgroup.inv_mem _ γ.2) (gp i)⁻¹
    rw [h1]
    exact hkey k s ⟨(gp i)⁻¹ * (γ : HNNExtension K A B φ)⁻¹ * gp i, hn⟩
  -- the transversal property
  have htrans : ∀ u : HNNExtension K A B φ, ∃! t' : HNNExtension K A B φ,
      t' ∈ T' ∧ u⁻¹ * t' ∈ P := by
    intro u
    obtain ⟨i, γ, k, hu⟩ := hdecomp u
    obtain ⟨s, hs, huniq⟩ := h.choose_spec.1 k
    refine ⟨gp i * HNNExtension.of s, ⟨⟨⟨i, ⟨s, hs.1⟩⟩, rfl⟩, ?_⟩, ?_⟩
    · exact (hsame u i γ k hu s).mpr hs.2
    · rintro y ⟨hy, hymem⟩
      obtain ⟨⟨j, s'⟩, hs'⟩ := hy
      have hy2 : u⁻¹ * (gp j * HNNExtension.of (s' : K)) ∈ P := by
        have h := hymem
        rw [← hs'] at h
        exact h
      have hij : i = j := hdiff u i γ k hu j (s' : K) hy2
      have hQ : k⁻¹ * (s' : K) ∈ Q := (hsame u i γ k hu (s' : K)).mp (by rw [hij]; exact hy2)
      have hss : (s' : K) = s := huniq (s' : K) ⟨s'.2, hQ⟩
      rw [← hs']
      show gp j * HNNExtension.of (s' : K) = gp i * HNNExtension.of s
      rw [← hij, hss]
  refine ⟨T', htrans, (Bcop.reindex ee).repr.symm, ?_⟩
  intro t
  exact hBtr t

end Work.ORLocInd.CohenLyndon
