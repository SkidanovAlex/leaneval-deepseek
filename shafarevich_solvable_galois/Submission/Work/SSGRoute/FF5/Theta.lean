import Mathlib
import Submission.Work.SSGRoute.FF5.UnivPort
import Submission.Work.SSGRoute.UnivPortCore
import Submission.Work.SSGRoute.freeLie_regular_odd
import Submission.Work.SSGRoute.lieSpanNested
import Submission.Work.SSGRoute.FF5.MagLTMapDomain
import Submission.Work.SSGRoute.freeAssocMap_mem_nestedSpan
import Submission.Work.SSGRoute.freeAssocMap_mem_wordSpan
import Submission.Work.SSGRoute.pSeries_inter_lcs_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The degree-`j` Magnus component `θ` of an element of `γ_j`
-/

noncomputable section

open Work.SSGRoute.prop5

namespace Work.SSGRoute.diagOdd

universe u

variable {X : Type u}

/-! ## Elementary span facts -/

theorem lieSpan_le_wordSpan (X : Type u) (j : ℕ) : lieSpan X j ≤ wordSpan (X := X) j := by
  refine Submodule.span_le.mpr ?_
  rintro a ⟨c, hc, rfl⟩
  rw [← hc]
  exact Work.SSGRoute.brkMon_mem_wordSpan c

theorem nestedSpan_le_wordSpan (X : Type u) (j : ℕ) :
    nestedSpan (X := X) j ≤ wordSpan (X := X) j := by
  rw [nestedSpan_eq_lieSpan]
  exact lieSpan_le_wordSpan X j

/-- The degree-`j` part of the free Lie lattice injects into the truncation
`FreeAssoc X ⧸ fil X (j+1)`. -/
theorem nestedSpan_mk_injective (X : Type u) (j : ℕ) {b b' : FreeAssoc X}
    (hb : b ∈ nestedSpan (X := X) j) (hb' : b' ∈ nestedSpan (X := X) j)
    (h : Ideal.Quotient.mk (fil X (j + 1)) b = Ideal.Quotient.mk (fil X (j + 1)) b') :
    b = b' := by
  have hsub : b - b' ∈ nestedSpan (X := X) j := Submodule.sub_mem _ hb hb'
  have hfil : b - b' ∈ fil X (j + 1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h, sub_self]
  exact sub_eq_zero.mp (Work.SSGRoute.UpCore.eq_zero_of_mem_wordSpan_of_mem_fil
    (nestedSpan_le_wordSpan X j hsub) hfil)

/-- `magLT` is `magLead` at the next index. -/
theorem magLT_eq_magLead (X : Type u) (j : ℕ) (y : FreeGroup X) :
    magLT X j y = magLead (j + 1) y := by
  simp only [magLT, magLead]

/-! ## The nested span is contained in the Magnus image -/

/-- Every element of the degree-`j` part of the free Lie lattice is the Magnus leading term of an
element of `γ_j`. -/
theorem exists_magLead_of_mem_nestedSpan (X : Type u) (j : ℕ) (hj : 1 ≤ j) {a : FreeAssoc X}
    (ha : a ∈ nestedSpan (X := X) j) :
    ∃ w ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1),
      magLead (j + 1) w = (Ideal.Quotient.mk (fil X (j + 1))) a := by
  have ha' : a ∈ Submodule.span ℤ
      {a : FreeAssoc X | ∃ w : List X, w.length = j ∧ a = lnMon w} := ha
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha'
  · rintro a ⟨w, hwlen, rfl⟩
    refine ⟨lc w, ?_, ?_⟩
    · cases w with
      | nil => rw [lc]; exact Subgroup.one_mem _
      | cons x rest =>
          rw [lc_eq_gpFold]
          have hmem := gpFold_mem (X := X) rest 1 le_rfl (u := FreeGroup.of x)
            (Subgroup.mem_top _)
          rw [show 1 + rest.length - 1 = j - 1 from by
            simp only [List.length_cons] at hwlen; omega] at hmem
          exact hmem
    · have h := magLead_lc_congr (X := X) (j + 1) (w := w) (by omega) (by omega)
      rw [show w.length + 1 = j + 1 from by omega] at h
      have hzero : magLead (j + 1) (lc w)
          - (Ideal.Quotient.mk (fil X (j + 1))) (lnMon w) = 0 :=
        mem_filq_self_eq_zero' (by simpa using h)
      exact sub_eq_zero.mp hzero
  · exact ⟨1, Subgroup.one_mem _, by rw [magLead_one, map_zero]⟩
  · intro a b _ _ iha ihb
    obtain ⟨w₁, hw₁, he₁⟩ := iha
    obtain ⟨w₂, hw₂, he₂⟩ := ihb
    refine ⟨w₁ * w₂, Subgroup.mul_mem _ hw₁ hw₂, ?_⟩
    rw [magLead_mul (j + 1) j hj (by omega) (by omega) hw₁ hw₂, he₁, he₂, map_add]
  · intro c a _ iha
    obtain ⟨w, hw, he⟩ := iha
    rcases lt_or_ge 0 c with hc | hc
    · refine ⟨w ^ c.toNat, Subgroup.pow_mem _ hw _, ?_⟩
      have hc' : ((c.toNat : ℤ)) = c := Int.toNat_of_nonneg (le_of_lt hc)
      rw [magLead_pow (j + 1) j c.toNat hj (by omega) (by omega) hw, he, hc', map_zsmul,
        zsmul_eq_mul]
    · refine ⟨(w ^ (-c).toNat)⁻¹, Subgroup.inv_mem _ (Subgroup.pow_mem _ hw _), ?_⟩
      have hc'' : (((-c).toNat : ℤ)) = -c := Int.toNat_of_nonneg (by omega)
      rw [magLead_inv (j + 1) j hj (by omega) (by omega) (Subgroup.pow_mem _ hw _),
        magLead_pow (j + 1) j (-c).toNat hj (by omega) (by omega) hw, he, hc'', map_zsmul,
        zsmul_eq_mul]
      have hcast : (((-c : ℤ)) : FreeAssoc X ⧸ fil X (j + 1))
          = -(c : FreeAssoc X ⧸ fil X (j + 1)) := by push_cast; ring_nf
      rw [hcast, ← neg_mul, neg_neg]

theorem exists_magLT_of_mem_nestedSpan (X : Type u) (j : ℕ) (hj : 1 ≤ j) {a : FreeAssoc X}
    (ha : a ∈ nestedSpan (X := X) j) :
    ∃ w ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1),
      magLT X j w = (Ideal.Quotient.mk (fil X (j + 1))) a := by
  obtain ⟨w, hw, he⟩ := exists_magLead_of_mem_nestedSpan X j hj ha
  exact ⟨w, hw, by rw [magLT_eq_magLead]; exact he⟩

/-! ## The degree-`j` Magnus component -/

theorem exists_theta (X : Type u) (j : ℕ) (hj : 1 ≤ j) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    ∃ b : FreeAssoc X, b ∈ nestedSpan (X := X) j ∧
      Ideal.Quotient.mk (fil X (j + 1)) b = magLT X j y := by
  have hmem : magLT X j y ∈ filq X (j + 1) j := adj_magLT_mem_filq X j hj hy
  obtain ⟨a₀, ha₀, ha₀eq⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hmem
  refine ⟨degPart j a₀, ?_, ?_⟩
  · exact degPart_mem_nestedSpan_of_magLead j hj (j + 1) le_rfl y hy a₀ ha₀
      (by rw [ha₀eq, magLT_eq_magLead])
  · have hdiff : a₀ - degPart j a₀ ∈ fil X (j + 1) := sub_degPart_mem_fil ha₀
    have hzero : Ideal.Quotient.mk (fil X (j + 1)) (a₀ - degPart j a₀) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hdiff
    rw [map_sub, sub_eq_zero] at hzero
    rw [← ha₀eq]
    exact hzero.symm

/-- The degree-`j` Magnus component of `y ∈ γ_j`: the unique element of `nestedSpan X j` whose
image in `FreeAssoc X ⧸ fil X (j+1)` is `magLT X j y`. -/
noncomputable def theta (X : Type u) (j : ℕ) (hj : 1 ≤ j) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) : FreeAssoc X :=
  Classical.choose (exists_theta X j hj y hy)

theorem theta_mem (X : Type u) (j : ℕ) (hj : 1 ≤ j) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    theta X j hj y hy ∈ nestedSpan (X := X) j :=
  (Classical.choose_spec (exists_theta X j hj y hy)).1

theorem theta_mk (X : Type u) (j : ℕ) (hj : 1 ≤ j) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    Ideal.Quotient.mk (fil X (j + 1)) (theta X j hj y hy) = magLT X j y :=
  (Classical.choose_spec (exists_theta X j hj y hy)).2

theorem theta_mem_wordSpan (X : Type u) (j : ℕ) (hj : 1 ≤ j) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    theta X j hj y hy ∈ wordSpan (X := X) j :=
  nestedSpan_le_wordSpan X j (theta_mem X j hj y hy)

/-- Characterisation: `θ y` is the unique element of `nestedSpan X j` lifting `magLT X j y`. -/
theorem theta_unique (X : Type u) (j : ℕ) (hj : 1 ≤ j) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
    {b : FreeAssoc X} (hb : b ∈ nestedSpan (X := X) j)
    (h : Ideal.Quotient.mk (fil X (j + 1)) b = magLT X j y) :
    b = theta X j hj y hy :=
  nestedSpan_mk_injective X j hb (theta_mem X j hj y hy) (by rw [h, theta_mk])

theorem theta_congr {X : Type u} (j : ℕ) (hj : 1 ≤ j) {y y' : FreeGroup X} (h : y = y')
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
    (hy' : y' ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    theta X j hj y hy = theta X j hj y' hy' := by
  cases h
  rw [Subsingleton.elim hy hy']

theorem theta_mul (X : Type u) (j : ℕ) (hj : 1 ≤ j) (y z : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    theta X j hj (y * z) (Subgroup.mul_mem _ hy hz)
      = theta X j hj y hy + theta X j hj z hz := by
  have h1 : Ideal.Quotient.mk (fil X (j + 1)) (theta X j hj y hy + theta X j hj z hz)
      = magLT X j (y * z) := by
    rw [map_add, theta_mk X j hj y hy, theta_mk X j hj z hz, adj_magLT_mul X j hj hy hz]
  exact (theta_unique X j hj (y * z) (Subgroup.mul_mem _ hy hz)
    (Submodule.add_mem _ (theta_mem X j hj y hy) (theta_mem X j hj z hz)) h1).symm

theorem theta_one (X : Type u) (j : ℕ) (hj : 1 ≤ j) :
    theta X j hj 1 (Subgroup.one_mem _) = 0 :=
  (theta_unique X j hj 1 (Subgroup.one_mem _) (Submodule.zero_mem _)
    (by rw [map_zero, adj_magLT_one X j])).symm

theorem theta_inv (X : Type u) (j : ℕ) (hj : 1 ≤ j) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    theta X j hj y⁻¹ (Subgroup.inv_mem _ hy) = - theta X j hj y hy :=
  (theta_unique X j hj y⁻¹ (Subgroup.inv_mem _ hy) (Submodule.neg_mem _ (theta_mem X j hj y hy))
    (by rw [map_neg, theta_mk X j hj y hy, adj_magLT_inv X j hj hy])).symm

theorem theta_zero_iff (X : Type u) (j : ℕ) (hj : 1 ≤ j) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    theta X j hj y hy = 0 ↔ y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
  constructor
  · intro h
    have hzero : magLead (j + 1) y = 0 := by
      rw [← magLT_eq_magLead, ← theta_mk X j hj y hy, h, map_zero]
    exact Work.SSGRoute.UpCore.mem_Gam_iff.mp
      (Work.SSGRoute.UpCore.magnusCore_aux X j hj y
        (Work.SSGRoute.UpCore.mem_Gam_iff.mpr hy) hzero)
  · intro h
    exact (theta_unique X j hj y hy (Submodule.zero_mem _)
      (by rw [map_zero, adj_magLT_eq_zero_of_mem_succ X j h])).symm

theorem theta_surj (X : Type u) (j : ℕ) (hj : 1 ≤ j) {b : FreeAssoc X}
    (hb : b ∈ nestedSpan (X := X) j) :
    ∃ (y : FreeGroup X) (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)),
      theta X j hj y hy = b := by
  obtain ⟨y, hy, heq⟩ := exists_magLT_of_mem_nestedSpan X j hj hb
  exact ⟨y, hy, (theta_unique X j hj y hy hb heq.symm).symm⟩

/-! ## Equivariance under relabelling -/

theorem redZ_freeAssocMap (X : Type u) (σ : X ≃ X) (a : FreeAssoc X) :
    redZ X (freeAssocMap σ a) = wordBarσ X σ (redZ X a) := by
  induction a using MonoidAlgebra.induction_on with
  | of m =>
      rw [MonoidAlgebra.of_apply ℤ (FreeMonoid X) m, freeAssocMap,
        MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, redZ_single,
        redZ_single, wordBarσ_single]
  | add a b iha ihb =>
      rw [map_add, map_add (redZ X), map_add (redZ X), map_add (wordBarσ X σ), iha, ihb]
  | smul c a iha =>
      rw [map_zsmul, map_zsmul, iha, map_zsmul, ← map_zsmul]

theorem freeGroupCongr_mem (X : Type u) (σ : X ≃ X) (j : ℕ) {y : FreeGroup X}
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    FreeGroup.freeGroupCongr σ y
      ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) :=
  Work.SSGRoute.map_lcs_le (FreeGroup.freeGroupCongr σ).toMonoidHom (j - 1)
    (Subgroup.mem_map_of_mem _ hy)

/-- `θ` is equivariant for relabelling of the generators. -/
theorem theta_natural (X : Type u) (σ : X ≃ X) (j : ℕ) (hj : 1 ≤ j) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    theta X j hj (FreeGroup.freeGroupCongr σ y) (freeGroupCongr_mem X σ j hy)
      = freeAssocMap σ (theta X j hj y hy) := by
  refine nestedSpan_mk_injective X j (theta_mem X j hj _ _)
    (Work.SSGRoute.freeAssocMap_mem_nestedSpan σ j (theta_mem X j hj y hy)) ?_
  rw [theta_mk X j hj (FreeGroup.freeGroupCongr σ y) (freeGroupCongr_mem X σ j hy)]
  exact (Work.SSGRoute.magLT_mapDomain σ j hj y (theta X j hj y hy)
    (theta_mk X j hj y hy)).symm

end Work.SSGRoute.diagOdd
