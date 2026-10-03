/-
# The Laurent datum of the torsion setting, from a `LinnellDatum`

This file constructs, for a `LinnellDatum L : LinnellDatum K G U`, a subgroup `G' ⊴ G` of finite
index which is torsion free, and a hypothesis `hdiv` (nonzero elements of `D H` are units for
torsion free `H`), the `Work.ORTorsion.LaurentBase` attached to every subgroup `H ≤ G` and every
surjection `φ : H ↠ ℤ`.

The construction uses the five delegated ingredients

* `oreCondition` — the right Ore condition for `R = ⟨D N ∪ gen H⟩` (the twisted Laurent ring);
* `commonDenomInR` — common right denominators in `R` for finite families in `D H`;
* `span_D_of_finiteIndex_right` — the finite-index decomposition with right coefficients;
* `coordExists` — the degree coordinates on `R`;
* `torsionPieceSetup` — the group-theoretic set-up with `H₀ = H ⊓ G'`, `N₀ = Nsub φ ⊓ G'`.
-/
import Submission.Work.ORFinal.TorsionData.Defs
import Submission.Work.ORFinal.TorsionData.oreCondition
import Submission.Work.ORFinal.TorsionData.commonDenomInR
import Submission.Work.ORFinal.TorsionData.span_D_of_finiteIndex_right
import Submission.Work.ORFinal.TorsionData.coordExists
import Submission.Work.ORFinal.TorsionData.torsionPieceSetup

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORFinal.TorsionData

open Work.ORLinnell

noncomputable section

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Nontrivial U]
  [Algebra K U]

/-- A chosen preimage of `1` under a surjection `φ : H ↠ ℤ`. -/
def sOf {H : Subgroup G} (φ : H →* Multiplicative ℤ) (hφ : Function.Surjective φ) : H :=
  Classical.choose (hφ (Multiplicative.ofAdd 1))

theorem sOf_spec {H : Subgroup G} (φ : H →* Multiplicative ℤ) (hφ : Function.Surjective φ) :
    φ (sOf φ hφ) = Multiplicative.ofAdd 1 :=
  Classical.choose_spec (hφ (Multiplicative.ofAdd 1))

/-- The powers of a preimage of `1` meet every coset of `ker φ`. -/
theorem mem_ker_mul_zpow_of_surjective {H : Subgroup G} (φ : H →* Multiplicative ℤ)
    (s : H) (hs : φ s = Multiplicative.ofAdd 1) :
    ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ (Nsub φ).subgroupOf H := by
  intro h
  obtain ⟨j, hj⟩ : ∃ j : ℤ, φ h = Multiplicative.ofAdd j :=
    ⟨Multiplicative.toAdd (φ h), ofAdd_toAdd (φ h)⟩
  refine ⟨j, ?_⟩
  rw [subgroupOf_Nsub φ, MonoidHom.mem_ker, map_mul, map_zpow, hs, hj]
  have hzpow : (Multiplicative.ofAdd (1 : ℤ)) ^ (-j) = Multiplicative.ofAdd (-j) := by
    rw [← ofAdd_zsmul, zsmul_eq_mul, mul_one]
    simp
  rw [hzpow, ofAdd_neg, mul_inv_cancel]

/-- `φ (s ^ k) = ofAdd k` for a preimage of `1`. -/
theorem map_zpow_of_surjective {H : Subgroup G} (φ : H →* Multiplicative ℤ)
    (s : H) (hs : φ s = Multiplicative.ofAdd 1) (k : ℤ) :
    φ (s ^ k) = Multiplicative.ofAdd k := by
  rw [map_zpow, hs, ← ofAdd_zsmul, zsmul_eq_mul, mul_one]
  simp

/-- The degree coordinates on `R = ⟨D N ∪ gen H⟩`, chosen from `coordExists`. -/
def coordOf (L : LinnellDatum K G U) (N H : Subgroup G) (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) :
    ℤ → (↥(TorsionRsub L N H) →ₗ[K] ↥(Dsub L N)) :=
  Classical.choose (coordExists L N H hNH hNn s hs hs0)

theorem coordOf_shift (L : LinnellDatum K G U) (N H : Subgroup G) (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) :
    ∀ (i k : ℤ) (y : ↥(TorsionRsub L N H)),
      coordOf L N H hNH hNn s hs hs0 i (rightMulU L N H s k y)
        = coordOf L N H hNH hNn s hs hs0 (i - k) y :=
  (Classical.choose_spec (coordExists L N H hNH hNn s hs hs0)).1

theorem coordOf_base (L : LinnellDatum K G U) (N H : Subgroup G) (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) :
    ∀ (i k : ℤ) (d : ↥(Dsub L N)),
      coordOf L N H hNH hNn s hs hs0 i (rightMulU L N H s k
          ⟨(d : U), Dsub_le_TorsionRsub L N H d.2⟩) = if i = k then d else 0 :=
  (Classical.choose_spec (coordExists L N H hNH hNn s hs hs0)).2.1

theorem coordOf_expand (L : LinnellDatum K G U) (N H : Subgroup G) (hNH : N ≤ H)
    (hNn : (N.subgroupOf H).Normal) (s : H)
    (hs : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ N.subgroupOf H)
    (hs0 : ∀ k : ℤ, s ^ k ∈ N.subgroupOf H → k = 0) :
    ∀ y : ↥(TorsionRsub L N H), ∃ S : Finset ℤ,
      ∑ i ∈ S, rightMulU L N H s i
          ⟨((coordOf L N H hNH hNn s hs hs0 i y : ↥(Dsub L N)) : U),
            Dsub_le_TorsionRsub L N H (coordOf L N H hNH hNn s hs hs0 i y).2⟩ = y :=
  (Classical.choose_spec (coordExists L N H hNH hNn s hs hs0)).2.2

/-- **The Laurent datum** attached to a subgroup `H ≤ G` and a surjection `φ : H ↠ ℤ`.

`N = Nsub φ` is the kernel of `φ`, `s` a preimage of `1`, `R = ⟨D N ∪ gen H⟩` the Laurent
subring, and the coordinates are the degree components of the unique Laurent expansion of an
element of `R`.  The common-denominator property is proved by going down to the torsion free
finite-index piece `H₀ = H ⊓ G'`. -/
def laurentBaseOf (L : LinnellDatum K G U) (G' : Subgroup G) [G'.Normal] [G'.FiniteIndex]
    (hG'tf : Work.ORLocInd.IsTorsionFree G')
    (hdiv : ∀ H : Subgroup G, Work.ORLocInd.IsTorsionFree H → ∀ x : ↥(L.D H), x ≠ 0 → IsUnit x)
    (H : Subgroup G) (φ : H →* Multiplicative ℤ) (hφ : Function.Surjective φ) :
    Work.ORTorsion.LaurentBase K U G L.gen (Dsub L) H φ := by
  classical
  let s := sOf φ hφ
  have hs : φ s = Multiplicative.ofAdd 1 := sOf_spec φ hφ
  have hφext : IsExtensionByZ (Nsub φ) H := ⟨φ, hφ, (subgroupOf_Nsub φ).symm⟩
  have hs_mem : ∀ h : H, ∃ j : ℤ, h * s ^ (-j) ∈ (Nsub φ).subgroupOf H :=
    mem_ker_mul_zpow_of_surjective φ s hs
  have hs_zpow : ∀ k : ℤ, φ (s ^ k) = Multiplicative.ofAdd k :=
    map_zpow_of_surjective φ s hs
  have hs0 : ∀ k : ℤ, s ^ k ∈ (Nsub φ).subgroupOf H → k = 0 :=
    Laurent.sPow_mem_subgroupOf hφext s hs_mem
  refine ⟨Nsub φ, rfl, s, hs, hs_zpow, TorsionRsub L (Nsub φ) H,
    Dsub_le_TorsionRsub L (Nsub φ) H, TorsionRsub_le_Dsub L (Nsub_le φ),
    gen_mem_TorsionRsub L (Nsub φ) H, rightMulU L (Nsub φ) H s, ?_, ?_,
    coordOf L (Nsub φ) H (Nsub_le φ) (normal_subgroupOf_Nsub φ) s hs_mem hs0,
    coordOf_shift L (Nsub φ) H (Nsub_le φ) (normal_subgroupOf_Nsub φ) s hs_mem hs0,
    coordOf_base L (Nsub φ) H (Nsub_le φ) (normal_subgroupOf_Nsub φ) s hs_mem hs0,
    coordOf_expand L (Nsub φ) H (Nsub_le φ) (normal_subgroupOf_Nsub φ) s hs_mem hs0, ?_⟩
  · intro j y
    exact rightMulU_coe L (Nsub φ) H s j y
  · intro j y
    exact rightMulU_neg L (Nsub φ) H s j y
  · intro m x
    obtain ⟨hH₀norm, hH₀fin, hN₀le, hN₀norm, _hExt₀, s₀, hs₀_mem, hs₀_zero⟩ :=
      torsionPieceSetup G' hG'tf H φ hφ
    have htfH₀ : Work.ORLocInd.IsTorsionFree ↥(H ⊓ G') := isTorsionFree_inf G' hG'tf H
    have htfN₀ : Work.ORLocInd.IsTorsionFree ↥(Nsub φ ⊓ G') :=
      isTorsionFree_inf G' hG'tf (Nsub φ)
    have hdivH₀ : ∀ y : ↥(L.D (H ⊓ G')), y ≠ 0 → IsUnit y := hdiv (H ⊓ G') htfH₀
    have hdivN₀ : ∀ y : ↥(L.D (Nsub φ ⊓ G')), y ≠ 0 → IsUnit y := hdiv (Nsub φ ⊓ G') htfN₀
    have hore := oreCondition L hN₀le hN₀norm hdivN₀ s₀ hs₀_mem hs₀_zero
    choose c hc using fun k =>
      span_D_of_finiteIndex_right L (inf_le_left : H ⊓ G' ≤ H) hH₀norm hH₀fin hdivH₀
        (x k : U) (x k).2
    let Q := H ⧸ (H ⊓ G').subgroupOf H
    letI : Fintype Q := Fintype.ofFinite Q
    let δ : Fin m × Q → U := fun p => (c p.1 p.2 : U)
    have hδmem : ∀ p : Fin m × Q, δ p ∈ L.D (H ⊓ G') := fun p => (c p.1 p.2).2
    let ι := Fin m × Q
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let δ' : Fin (Fintype.card ι) → ↥(L.D (H ⊓ G')) := fun j => ⟨δ (e.symm j), hδmem _⟩
    obtain ⟨t, htR₀, htne, hδt⟩ := commonDenomInR L hN₀le hdivH₀ hore (Fintype.card ι) δ'
    have htD₀ : t ∈ L.D (H ⊓ G') := TorsionR_le_D L hN₀le htR₀
    have htD : t ∈ L.D H := L.D_mono inf_le_left htD₀
    refine ⟨⟨t, htD⟩, ?_, ?_, ?_⟩
    · intro h0
      exact htne (congrArg Subtype.val h0)
    · exact isUnit_of_mem_Dsub_of_le L inf_le_left hdivH₀ htD₀ htne
    · intro k
      rw [mem_TorsionRsub_iff]
      show ((x k : U) * t) ∈ TorsionR L (Nsub φ) H
      rw [hc k, Finsupp.sum_mul, Finsupp.sum]
      apply Subring.sum_mem
      intro q _
      rw [mul_assoc]
      refine (TorsionR L (Nsub φ) H).mul_mem
        (Subring.subset_closure (Set.mem_union_right _ ⟨Quotient.out q, rfl⟩)) ?_
      have hmem := hδt (e (k, q))
      have hval : δ' (e (k, q)) = c k q := by
        simp only [δ', δ, Equiv.symm_apply_apply]
      rw [hval] at hmem
      exact TorsionR_mono L inf_le_left inf_le_left hmem

end

end Work.ORFinal.TorsionData
