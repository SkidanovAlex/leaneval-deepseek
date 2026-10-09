import Mathlib
import Submission.Work.Shrinking.PCentral
import Submission.Work.SSGRoute.prop5.magnusFramework
import Submission.Work.SSGRoute.prop5.magnus_mem_one_add
import Submission.Work.SSGRoute.prop5.magnus_unitCongr_isolated
import Submission.Work.SSGRoute.prop5.magnus_leadingTerm
import Submission.Work.SSGRoute.prop5.mw.Defs
import Submission.Work.SSGRoute.prop5.mw.psi_mem_VspanSize
import Submission.Work.SSGRoute.prop5.lowerCentralSeriesCore
import Submission.Work.SSGRoute.prop5.lctf.coreDefs
import Submission.Work.SSGRoute.prop5.lctf.mltMonGrp
import Submission.Work.SSGRoute.prop5.lctf.lamSpan
import Submission.Work.SSGRoute.prop5.witt.Basic
import Submission.Work.SSGRoute.prop5.witt.Vocab
import Submission.Work.SSGRoute.hallSpan_saturated
import Submission.Work.SSGRoute.magLT_pSeries_divisible
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped commutatorElement
namespace Work.SSGRoute.SSPow

open Work.SSGRoute.prop5

attribute [local instance 100] LieRing.ofAssociativeRing

variable {X : Type}

/-- The paper's `γ_k` (Mathlib indexing: `lowerCentralSeries (k-1)`). -/
abbrev gam (X : Type) (k : ℕ) : Subgroup (FreeGroup X) :=
  (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries k

/-- The `ℤ`-span of the commutator monomials `monBrk X h` for `h` a Hall tree of size `j`. -/
def hallSpan (X : Type) [LinearOrder X] (j : ℕ) : Submodule ℤ (FreeAssoc X) :=
  Submodule.span ℤ {b : FreeAssoc X |
    ∃ h : Magma X, IsHall h ∧ Magma.size h = j ∧ b = monBrk X h}

/-! ## Homogeneity of the bracketed monomial -/

/-- Every word occurring in `monBrk X c` has length `Magma.size c`. -/
theorem monBrk_coeff_length (c : Magma X) {w : FreeMonoid X}
    (h : (monBrk X c).coeff w ≠ 0) : w.length = Magma.size c := by
  classical
  have hmain : ∀ (c : Magma X) (v : FreeMonoid X), v ∈ (monBrk X c).coeff.support →
      v.length = Magma.size c := by
    intro c
    induction c with
    | gen x =>
        intro v hv
        rw [monBrk_gen] at hv
        rw [Finsupp.mem_support_iff] at hv
        rw [MonoidAlgebra.coeff_single] at hv
        have hv' : v = FreeMonoid.of x := by
          by_contra hne
          exact hv (Finsupp.single_eq_of_ne hne)
        rw [hv']
        simp
    | mul a b iha ihb =>
        intro v hv
        rw [monBrk_mul, MonoidAlgebra.coeff_sub] at hv
        rcases Finset.mem_union.mp (Finsupp.support_sub hv) with hv | hv
        · rcases Finset.mem_mul.mp
            (MonoidAlgebra.support_coeff_mul_subset (monBrk X a) (monBrk X b) hv) with
            ⟨u, hu, u', hu', rfl⟩
          rw [FreeMonoid.length_mul, iha u hu, ihb u' hu', Magma.size_mul]
        · rcases Finset.mem_mul.mp
            (MonoidAlgebra.support_coeff_mul_subset (monBrk X b) (monBrk X a) hv) with
            ⟨u, hu, u', hu', rfl⟩
          rw [FreeMonoid.length_mul, ihb u hu, iha u' hu', Magma.size_mul, Nat.add_comm]
  exact hmain c w (Finsupp.mem_support_iff.mpr h)

/-- Elements of `hallSpan X j` have no coefficients outside words of length `j`. -/
theorem hallSpan_coeff_eq_zero {X : Type} [LinearOrder X] {j : ℕ} {a : FreeAssoc X}
    (ha : a ∈ hallSpan X j)
    {w : FreeMonoid X} (hw : w.length ≠ j) : a.coeff w = 0 := by
  classical
  have key : ∀ a ∈ hallSpan X j, ∀ w : FreeMonoid X, w.length ≠ j → a.coeff w = 0 := by
    intro a ha
    refine Submodule.span_induction (p := fun a _ => ∀ w : FreeMonoid X, w.length ≠ j →
      a.coeff w = 0) ?_ ?_ ?_ ?_ ha
    · rintro b ⟨h, hH, hsz, rfl⟩ w hw
      by_contra hne
      exact hw (by rw [monBrk_coeff_length h hne, hsz])
    · intro w hw; rw [MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    · intro x y _ _ hx hy w hw
      rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, hx w hw, hy w hw, add_zero]
    · intro c x _ hx w hw
      rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, hx w hw, smul_zero]
  exact key a ha w hw

/-! ## Extraction of a finite presentation in the Hall span -/

/-- An element of the Hall span is a finite `ℤ`-linear combination of the `monBrk` of Hall trees
of size `j`. -/
theorem exists_finsupp_of_mem_hallSpan {X : Type} [LinearOrder X] {j : ℕ} {a : FreeAssoc X}
    (ha : a ∈ hallSpan X j) :
    ∃ d : {h : Magma X // IsHall h ∧ Magma.size h = j} →₀ ℤ,
      a = ∑ h ∈ d.support, d h • monBrk X h.1 := by
  rw [hallSpan] at ha
  have ha' : a ∈ Submodule.span ℤ
      (Set.range (fun h : {h : Magma X // IsHall h ∧ Magma.size h = j} => monBrk X h.1)) := by
    refine Submodule.span_mono ?_ ha
    rintro b ⟨h, hH, hsz, rfl⟩
    exact ⟨⟨h, hH, hsz⟩, rfl⟩
  rw [← Finsupp.range_linearCombination (ℤ)
    (v := fun h : {h : Magma X // IsHall h ∧ Magma.size h = j} => monBrk X h.1)] at ha'
  obtain ⟨d, hd⟩ := ha'
  refine ⟨d, ?_⟩
  rw [← hd, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset d (Finset.Subset.refl _) (fun h r => r • monBrk X h.1)
      (by simp)]
/-- Coefficients are additive over finite sums. -/
theorem sum_coeff {ι : Type} (s : Finset ι) (f : ι → MonoidAlgebra ℤ (FreeMonoid X))
    (W : FreeMonoid X) : (∑ i ∈ s, f i).coeff W = ∑ i ∈ s, (f i).coeff W := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has, MonoidAlgebra.coeff_add, Finsupp.add_apply,
      ih]

/-! ## Saturation of the Hall span -/

/-- The leading term of the bracketed monomial of a Hall tree: the foliage occurs with coefficient
`1` and every smaller word with coefficient `0`. -/
theorem hall_lead {X : Type} [LinearOrder X] {h : Magma X} (hH : IsHall h) :
    (monBrk X h).coeff (FreeMonoid.ofList (Magma.foliage h)) = 1 ∧
      ∀ (w : List X), w < Magma.foliage h → (monBrk X h).coeff (FreeMonoid.ofList w) = 0 :=
  mw.hlead_monBrk h hH

/-- The bracket monomial of an arbitrary tree of size `j` lies in the Hall span of degree `j`. -/
theorem monBrk_mem_hallSpan {X : Type} [LinearOrder X] (c : Magma X) :
    monBrk X c ∈ hallSpan X (Magma.size c) := by
  have h := mw.psi_mem_VspanSize (fun c : Magma X => monBrk X c)
    (fun a b => monBrk_mul a b) c
  rw [mw.VspanSize] at h
  refine Submodule.span_mono ?_ h
  rintro b ⟨h, rfl⟩
  exact ⟨h.1, h.2.1, h.2.2, rfl⟩

/-- The Hall span of degree `j` is contained in the `j`-th length filtration piece. -/
theorem hallSpan_le_fil {X : Type} [LinearOrder X] (j : ℕ) :
    (hallSpan X j : Set (FreeAssoc X)) ⊆ (fil X j : Set (FreeAssoc X)) := by
  intro b hb
  simp only [hallSpan] at hb
  refine Submodule.span_induction (p := fun b _ => b ∈ (fil X j : Set (FreeAssoc X)))
    ?_ ?_ ?_ ?_ hb
  · rintro b ⟨h, hH, hsz, rfl⟩
    have hfil := lctf.monBrk_mem_fil X h
    rwa [hsz] at hfil
  · exact (fil X j).zero_mem
  · intro x y _ _ hx hy
    exact (fil X j).add_mem hx hy
  · intro r x _ hx
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left (fil X j) ((r : ℤ) : FreeAssoc X) hx

theorem hallSpan_sat {X : Type} [LinearOrder X] (j : ℕ) (n : ℤ) (hn : n ≠ 0)
    (a : FreeAssoc X) (ha : a ∈ hallSpan X j) (hdiv : ∀ w : FreeMonoid X, n ∣ a.coeff w) :
    ∃ b ∈ hallSpan X j, a = n • b :=
  Work.SSGRoute.hallSpan_saturated (X := X) j n hn a ha hdiv

/-! ## The image of the Hall span under the Magnus leading term -/

/-- Every element of the Hall span of degree `j` is the Magnus leading term of an element of
`γ_{j-1}`. -/
theorem exists_gamma_of_hallSpan {X : Type} [LinearOrder X] (j : ℕ) (hj : 1 ≤ j)
    {b : FreeAssoc X} (hb : b ∈ hallSpan X j) :
    ∃ w ∈ gam X (j-1), magLT X j w = Ideal.Quotient.mk (fil X (j+1)) b := by
  classical
  have hb' : b ∈ Submodule.span ℤ {b : FreeAssoc X |
      ∃ h : Magma X, IsHall h ∧ Magma.size h = j ∧ b = monBrk X h} := by
    simpa [hallSpan] using hb
  revert hb'
  refine Submodule.span_induction (p := fun b _ => ∃ w ∈ gam X (j-1),
    magLT X j w = Ideal.Quotient.mk (fil X (j+1)) b) ?_ ?_ ?_ ?_
  · rintro b ⟨h, hH, hsz, rfl⟩
    refine ⟨lctf.monGrp X h, ?_, ?_⟩
    · have hmem' : lctf.monGrp X h ∈ lctf.Gam X (j-1) := by
        simpa [hsz] using lctf.monGrp_mem_Gam (X := X) h
      show lctf.monGrp X h ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)
      exact hmem'
    · have hsub := lctf.mlt_monGrp_sub_mem X (j+1) h (by rw [hsz])
      have hzero : lctf.mlt (j+1) (lctf.monGrp X h)
          - Ideal.Quotient.mk (fil X (j+1)) (monBrk X h) = 0 := by
        refine lctf.mem_filq_self_eq_zero ?_
        simpa [hsz] using hsub
      have := sub_eq_zero.mp hzero
      simpa [magLT, lctf.mlt] using this
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [magLT_one, map_zero]
  · rintro b₁ b₂ _ _ ⟨w₁, hw₁, he₁⟩ ⟨w₂, hw₂, he₂⟩
    refine ⟨w₁ * w₂, Subgroup.mul_mem _ hw₁ hw₂, ?_⟩
    rw [magLT_mul X j hj hw₁ hw₂, he₁, he₂, map_add]
  · rintro r b _ ⟨w, hw, he⟩
    rcases lt_or_ge 0 r with hr | hr
    · refine ⟨w ^ r.toNat, Subgroup.pow_mem _ hw _, ?_⟩
      have hr' : ((r.toNat : ℤ)) = r := Int.toNat_of_nonneg (le_of_lt hr)
      rw [magLT_pow X j hj r.toNat hw, he, hr', map_zsmul, zsmul_eq_mul]
    · refine ⟨(w ^ (-r).toNat)⁻¹, Subgroup.inv_mem _ (Subgroup.pow_mem _ hw _), ?_⟩
      have hr'' : (((-r).toNat : ℤ)) = -r := Int.toNat_of_nonneg (by omega)
      rw [magLT_inv X j hj (Subgroup.pow_mem _ hw _), magLT_pow X j hj (-r).toNat hw, he,
        hr'', map_zsmul, zsmul_eq_mul]
      rw [Int.cast_neg, ← neg_mul, neg_neg]

/-- The Magnus leading term of an element of `γ_{j-1}` is invariant under conjugation. -/
theorem magLT_conj {X : Type} (j : ℕ) (hj : 1 ≤ j) {g u : FreeGroup X}
    (hg : g ∈ gam X (j-1)) :
    magLT X j (u * g * u⁻¹) = magLT X j g := by
  have hconj : u * g * u⁻¹ ∈ gam X (j-1) :=
    Subgroup.Normal.conj_mem (inferInstance : (gam X (j-1)).Normal) g hg u
  have hcomm : ⁅u, g⁆ ∈ gam X j := by
    have h1 : ⁅u, g⁆ ∈ ⁅(⊤ : Subgroup (FreeGroup X)), gam X (j-1)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top u) hg
    rw [Subgroup.commutator_comm] at h1
    rwa [← Subgroup.lowerCentralSeries_succ (n := j-1), show j - 1 + 1 = j from by omega] at h1
  have hker : magLT X j ⁅u, g⁆ = 0 := magLT_eq_zero_of_mem_succ X j hcomm
  have hprod : magLT X j (u * g * u⁻¹ * g⁻¹) = magLT X j ⁅u, g⁆ := rfl
  have hmul : magLT X j (u * g * u⁻¹ * g⁻¹)
      = magLT X j (u * g * u⁻¹) + magLT X j g⁻¹ := magLT_mul X j hj hconj (Subgroup.inv_mem _ hg)
  rw [← hprod, hmul, magLT_inv X j hj hg] at hker
  exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact hker)


/-- The length ideal is contained in the length-support submodule. -/
theorem fil_le_filz_sspow (X : Type) (N : ℕ) : (fil X N : Set (FreeAssoc X)) ⊆ filz X N := by
  rw [fil_eq_filI]
  exact fun a ha => ha

/-! ## The leading term of `γ_{j-1}` lies in the image of the Hall span -/

/-- The normal closure of the weight-`j` monomials is contained in `γ_{j-1}`. -/
theorem normalClosure_monGrpSet_le {X : Type} [LinearOrder X] (j : ℕ) (hj : 1 ≤ j) :
    Subgroup.normalClosure (lctf.monGrpSet X j) ≤ gam X (j-1) := by
  haveI : (gam X (j-1)).Normal := graded.Gam_normal (G := FreeGroup X) (j - 1)
  refine Subgroup.normalClosure_le_normal ?_
  rintro s ⟨c, hc, rfl⟩
  have h := lctf.monGrp_mem_Gam (X := X) c
  rw [hc] at h
  exact h

/-- The Magnus leading term of an element of the normal closure of the weight-`j` monomials comes
from the Hall span. -/
theorem magLT_mem_normalClosure {X : Type} [LinearOrder X] (j : ℕ) (hj : 1 ≤ j) {s : FreeGroup X}
    (hs : s ∈ Subgroup.normalClosure (lctf.monGrpSet X j)) :
    ∃ b ∈ hallSpan X j, Ideal.Quotient.mk (fil X (j+1)) b = magLT X j s := by
  classical
  let Good : Subgroup (FreeGroup X) :=
    { carrier := {s | s ∈ gam X (j-1) ∧ ∃ b ∈ hallSpan X j,
        Ideal.Quotient.mk (fil X (j+1)) b = magLT X j s}
      mul_mem' := by
        rintro s t ⟨hsg, b, hb, hbs⟩ ⟨htg, c, hc, hct⟩
        refine ⟨Subgroup.mul_mem _ hsg htg, b + c, Submodule.add_mem _ hb hc, ?_⟩
        rw [magLT_mul X j hj hsg htg, ← hbs, ← hct, map_add]
      one_mem' := by
        refine ⟨Subgroup.one_mem _, 0, Submodule.zero_mem _, ?_⟩
        rw [magLT_one, map_zero]
      inv_mem' := by
        rintro s ⟨hsg, b, hb, hbs⟩
        refine ⟨Subgroup.inv_mem _ hsg, -b, Submodule.neg_mem _ hb, ?_⟩
        rw [magLT_inv X j hj hsg, ← hbs, map_neg] }
  have hnormal : Good.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨hng, b, hb, hbn⟩ := hn
    refine ⟨Subgroup.Normal.conj_mem (inferInstance) n hng g, b, hb, ?_⟩
    rw [magLT_conj (X := X) j hj hng, hbn]
  have hgen : lctf.monGrpSet X j ⊆ (Good : Set (FreeGroup X)) := by
    rintro s ⟨c, hc, rfl⟩
    have hmem : lctf.monGrp X c ∈ gam X (j-1) := by
      have h := lctf.monGrp_mem_Gam (X := X) c
      rw [hc] at h
      exact h
    refine ⟨hmem, monBrk X c, hc ▸ monBrk_mem_hallSpan c, ?_⟩
    have hsub := lctf.mlt_monGrp_sub_mem X (j+1) c (by rw [hc])
    have hzero : lctf.mlt (j+1) (lctf.monGrp X c)
        - Ideal.Quotient.mk (fil X (j+1)) (monBrk X c) = 0 := by
      refine lctf.mem_filq_self_eq_zero ?_
      simpa [hc] using hsub
    have h1 := sub_eq_zero.mp hzero
    simpa [magLT, lctf.mlt] using h1.symm
  have hmem := Subgroup.normalClosure_le_normal hgen hs
  exact (show s ∈ gam X (j-1) ∧ ∃ b ∈ hallSpan X j,
      Ideal.Quotient.mk (fil X (j+1)) b = magLT X j s from hmem).2

/-- The Magnus leading term of an element of `γ_{j-1}` comes from the Hall span. -/
theorem magLT_mem_mkHallSpan {X : Type} [LinearOrder X] (j : ℕ) (hj : 1 ≤ j) {y : FreeGroup X}
    (hy : y ∈ gam X (j-1)) :
    ∃ b ∈ hallSpan X j, Ideal.Quotient.mk (fil X (j+1)) b = magLT X j y := by
  classical
  haveI : (gam X j).Normal := graded.Gam_normal (G := FreeGroup X) j
  have hy' : y ∈ Subgroup.normalClosure (lctf.monGrpSet X j) ⊔ gam X j := by
    have := lctf.lcs_le_normalClosure_sup X (j-1) hy
    simpa [gam, lctf.Gam, graded.Gam, show j - 1 + 1 = j from by omega] using this
  obtain ⟨s, hs, t, ht, hst⟩ := (Subgroup.mem_sup_of_normal_right
    (s := Subgroup.normalClosure (lctf.monGrpSet X j)) (t := gam X j)).mp hy'
  have hsg : s ∈ gam X (j-1) := normalClosure_monGrpSet_le j hj hs
  have htg : t ∈ gam X (j-1) :=
    Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup (FreeGroup X)) (by omega) ht
  obtain ⟨b, hb, hbeq⟩ := magLT_mem_normalClosure j hj hs
  refine ⟨b, hb, ?_⟩
  rw [← hst, magLT_mul X j hj hsg htg, hbeq, magLT_eq_zero_of_mem_succ X j ht, add_zero]

/-! ## Torsion-freeness of the graded pieces and purity -/

/-- The filtered pieces `filq X N k` (`k ≤ N`) are torsion free. -/
theorem filq_torsion {X : Type} {N k : ℕ} (hk : k ≤ N) {n : ℤ} (hn : n ≠ 0)
    {z : FreeAssoc X ⧸ fil X N} (hz : z ∈ filq X N k) (h : n • z = 0) : z = 0 := by
  obtain ⟨c, -, hceq⟩ := mem_filq_iff.mp hz
  have hnc : n • c ∈ fil X N := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_zsmul, hceq, h]
  have hnf : n • c ∈ filz X N := fil_le_filz_sspow X N hnc
  have hcz : c ∈ filz X N := by
    rw [mem_filz_iff] at hnf ⊢
    intro w hw
    exact hnf w (by
      rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_ne_zero hn hw)
  rw [← hceq]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (filz_le_fil X N hcz)

/-- Multiplication by a nonzero integer is injective on `filq X N k` for `k ≤ N`. -/
theorem filq_zsmul_injective {X : Type} {N k : ℕ} (hk : k ≤ N) {n : ℤ} (hn : n ≠ 0)
    {x y : FreeAssoc X ⧸ fil X N} (hx : x ∈ filq X N k) (hy : y ∈ filq X N k)
    (h : n • x = n • y) : x = y :=
  sub_eq_zero.mp (filq_torsion hk hn (Submodule.sub_mem _ hx hy) (by rw [smul_sub, h, sub_self]))

/-- **Purity.**  If the Magnus leading term of `y ∈ γ_{j-1}` is `n` times an element of the
degree-`j` part (`n > 0`), then that element is itself the leading term of an element of
`γ_{j-1}`. -/
theorem purity_aux {X : Type} [LinearOrder X] (j : ℕ) (hj : 1 ≤ j) (n : ℕ) (hn : 0 < n)
    {y : FreeGroup X} (hy : y ∈ gam X (j-1)) {a : FreeAssoc X ⧸ fil X (j+1)}
    (ha : a ∈ filq X (j+1) j) (h : magLT X j y = ((n : ℤ)) • a) :
    ∃ w ∈ gam X (j-1), magLT X j w = a := by
  classical
  obtain ⟨b₀, hb₀, hb₀eq⟩ := magLT_mem_mkHallSpan j hj hy
  obtain ⟨c, -, hceq⟩ := mem_filq_iff.mp ha
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  have hdiff : b₀ - (n : ℤ) • c ∈ fil X (j+1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_zsmul,
      show Ideal.Quotient.mk (fil X (j+1)) b₀ = magLT X j y from hb₀eq, h, hceq, sub_self]
  have hdiv : ∀ w : FreeMonoid X, (n : ℤ) ∣ b₀.coeff w := by
    intro w
    by_cases hw : w.length = j
    · have hf : (b₀ - (n : ℤ) • c) ∈ filz X (j+1) := fil_le_filz_sspow X (j+1) hdiff
      have hzero : (b₀ - (n : ℤ) • c).coeff w = 0 := by
        by_contra hne
        have := (mem_filz_iff.mp hf) w hne
        omega
      have h0 : b₀.coeff w = (n : ℤ) * c.coeff w := by
        rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, MonoidAlgebra.coeff_smul,
          Finsupp.smul_apply, smul_eq_mul, sub_eq_zero] at hzero
        exact hzero
      exact ⟨c.coeff w, h0⟩
    · rw [hallSpan_coeff_eq_zero hb₀ hw]
      exact dvd_zero _
  obtain ⟨b, hb, hbeq⟩ := hallSpan_sat j (n : ℤ) hnz b₀ hb₀ hdiv
  have hmb : Ideal.Quotient.mk (fil X (j+1)) b = a := by
    refine filq_zsmul_injective (X := X) (N := j+1) (k := j) (show j ≤ j+1 from by omega) hnz ?_ ha ?_
    · exact Ideal.mem_map_of_mem _ (hallSpan_le_fil j hb)
    · have h1 : (n : ℤ) • (Ideal.Quotient.mk (fil X (j+1)) b)
          = Ideal.Quotient.mk (fil X (j+1)) b₀ := by
        rw [← map_zsmul, ← hbeq]
      rw [h1, hb₀eq, h]
  obtain ⟨w, hw, hweq⟩ := exists_gamma_of_hallSpan j hj hb
  exact ⟨w, hw, by rw [hweq, hmb]⟩


end Work.SSGRoute.SSPow

namespace Work.SSGRoute

open SSGRoute

open scoped commutatorElement

/-- The subgroup generated by the `n`-th powers of the elements of `H`, in the form used below. -/
private theorem mem_powSubgroup_iff {P : Type*} [Group P] (n : ℕ) (H : Subgroup P) {x : P} :
    x ∈ Work.Shrinking.powSubgroup n H ↔
      x ∈ Subgroup.closure {y : P | ∃ h ∈ H, h ^ n = y} := Iff.rfl

private theorem mem_powSubgroup_of_mem {P : Type*} [Group P] {n : ℕ} {H : Subgroup P} {h : P}
    (hh : h ∈ H) : h ^ n ∈ Work.Shrinking.powSubgroup n H :=
  Subgroup.subset_closure ⟨h, hh, rfl⟩

theorem pSeries_inter_centralSeries_pow (p : ℕ) [Fact p.Prime] (X : Type) (i j : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) :
    Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) ⊓
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)
      ≤ Work.Shrinking.powSubgroup (p ^ (i - j))
          ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
        ⊔ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
  classical
  obtain ⟨instLO, -⟩ := exists_wellFoundedLT X
  letI := instLO
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxP, hxγ⟩ := hx
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hn : 0 < p ^ (i - j) := pow_pos hp _
  -- the leading term of `x` is divisible by `p ^ (i - j)`
  obtain ⟨a, ha, haeq⟩ :=
    magLT_pSeries_divisible p X i j hj hji hxP hxγ
  -- purity: the quotient is realised by an element of `γ_{j-1}`
  obtain ⟨w, hw, hweq⟩ :=
    SSPow.purity_aux j hj (p ^ (i - j)) hn hxγ ha (by
      rw [haeq, Nat.cast_pow])
  -- the difference has trivial leading term, hence lies in `γ_j`
  set z : FreeGroup X := x * (w ^ (p ^ (i - j)))⁻¹ with hz
  have hzγ : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) :=
    Subgroup.mul_mem _ hxγ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hw _))
  have hwinv : (w ^ (p ^ (i - j)))⁻¹ ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) :=
    Subgroup.inv_mem _ (Subgroup.pow_mem _ hw _)
  have hxn : Work.SSGRoute.prop5.magLT X j x = ((p ^ (i - j) : ℕ) : ℤ) • a := by
    rw [haeq, Nat.cast_pow]
  have hwn : Work.SSGRoute.prop5.magLT X j (w ^ (p ^ (i - j))) = ((p ^ (i - j) : ℕ) : ℤ) • a := by
    rw [Work.SSGRoute.prop5.magLT_pow X j hj (p ^ (i - j)) hw, hweq, zsmul_eq_mul]
  have hzlt : Work.SSGRoute.prop5.magLT X j z = 0 := by
    rw [hz, Work.SSGRoute.prop5.magLT_mul X j hj hxγ hwinv,
      Work.SSGRoute.prop5.magLT_inv X j hj (Subgroup.pow_mem _ hw _), hwn, hxn]
    abel
  have hzmem : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
    -- the Magnus kernel
    have h := Work.SSGRoute.prop5.mcore.magnusCore_aux X j hj z
      (by simpa [Work.SSGRoute.prop5.graded.Gam] using hzγ)
      (by simpa [Work.SSGRoute.prop5.magLT, Work.SSGRoute.prop5.magLead] using hzlt)
    simpa [Work.SSGRoute.prop5.graded.Gam] using h
  -- assemble
  have hdecomp : x = z * w ^ (p ^ (i - j)) := by rw [hz]; group
  rw [hdecomp]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right hzmem)
    (Subgroup.mem_sup_left (mem_powSubgroup_of_mem hw))

end Work.SSGRoute
