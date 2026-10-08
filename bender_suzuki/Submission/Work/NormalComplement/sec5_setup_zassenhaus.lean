import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.sec5_zass_centV
import Submission.Work.NormalComplement.sec5_zass_centD
import Submission.Work.ThreePoints.sec4_prop3_cd_ne_bot
import Submission.Work.ThmF.ChV12.isZassenhaus_of_centD_eq_bot
import Submission.Work.Models.models
import Submission.Work.PSU3.StageA.modelDataBorel
import Submission.Work.ThompsonFrobenius.isSolvable_of_minimal_oddCore_ne_bot
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.stronglyEmbedded_map_of_surjective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

theorem isSimpleBenderGroup_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : LeanEval.GroupTheory.Defs.IsSimpleBenderGroup X) :
    LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y := by
  cases h with
  | isPSL2 n hn e' => exact IsSimpleBenderGroup.isPSL2 n hn (e.symm.trans e')
  | isSuzuki n hn e' => exact IsSimpleBenderGroup.isSuzuki n hn (e.symm.trans e')
  | isPSU3 n hn e' => exact IsSimpleBenderGroup.isPSU3 n hn (e.symm.trans e')

/-- **Peterfalvi I Ch. III §5 Prop. 2 (a), the Zassenhaus clause** (p.184).  With `C = C_G(A)`,
`F₀ = O^{2'}(C)`, `L = (F₀ ⊓ H).subgroupOf F₀` and `Z = Z(F₀)`, for **every** surjection
`φ : F₀ →* Y` with `φ.ker = Z(F₀)` (so `Y ≃* F₀/Z(F₀)` is the simple Bender group of `hC4` P3(c)),
the image `K = L.map φ` is a Zassenhaus subgroup of `Y`, i.e. the pointwise stabiliser in `Y` of
three distinct points of `Y ⧸ K` is trivial.

Proof.  `hC4` P3(c) at `X = A` gives `oddCore F₀ = Z(F₀)` (hence `Z(F₀)` has odd order) and a
simple Bender group `F₀/Z(F₀)`; `hC4` P1(b) at `X = A`, `F = F₀`, `g = 1` makes
`L = F₀ ⊓ H` strongly embedded in `F₀`, whence `Z(F₀) ≤ L` (a central element outside `L` would
have `L^z = L`, giving both `Odd |L|` and `Even |L|`).  Then
* `K = L.map φ` is strongly embedded in `Y` (`stronglyEmbedded_map_of_surjective`, the kernel
  `Z(F₀)` being central of odd order and contained in `L`);
* `t ∈ F₀` (it is an involution of `C_G(A) = C`), `t̄ = φ t` is an involution outside `K`;
* `Y` is 2-transitive on `Y ⧸ K` (`modelDataBorel` + `BenderPair.isMultiplyPretransitive_two`);
* `ModelFactsProp` (`Work.Models.models_prop`) supplies `S` with `K = S ⋊ twoPoint K t̄`, `S` a
  2-group, so `IsSplitRankOne K S t̄`;
* `centD K t̄ = ⊥` (`sec5_zass_centD`), because `centD L t = F₀ ⊓ V` is contained in `Z(F₀)` by
  `sec5_zass_centV` (`F₀ ∩ V ≤ Z(F₀)`, the source's "`[A,P] ≠ 1`" step);
* hence `IsZassenhaus K` by the general criterion
  `Work.ThmF.ChV12.isZassenhaus_of_centD_eq_bot`. -/
theorem sec5_setup_zassenhaus (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    let C : Subgroup G := Subgroup.centralizer (A : Set G)
    let F₀ : Subgroup G := (Submission.Blueprint.oddResidual ↥C).map C.subtype
    ∀ (Y : Type) [Group Y] [Finite Y] (φ : F₀ →* Y),
      Function.Surjective φ → φ.ker = Subgroup.center ↥F₀ →
      Submission.Blueprint.IsZassenhaus (((F₀ ⊓ H).subgroupOf F₀).map φ) := by
  classical
  intro C F₀ Y instY instFinY φ hsurj hker
  -- `L = (F₀ ⊓ H).subgroupOf F₀`
  let L : Subgroup ↥F₀ := (F₀ ⊓ H).subgroupOf F₀
  -- the `k`-witness of Ch. II §4 Prop. 3 at `X = A`
  have hbig : 2 ≤ (Design.CK H t A).ncard := by
    have hp2 : 2 ≤ p := h.prime.two_le
    have h4 : 4 ≤ 2 ^ p := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp2
    have hck : (Design.CK H t A).ncard = 2 ^ p - 1 := h.A_CK
    omega
  have hwit : ∃ k ∈ invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (A : Set G) := by
    obtain ⟨k, hkS, hk1⟩ : ∃ k ∈ Design.CK H t A, k ≠ 1 := by
      by_contra hc
      push_neg at hc
      have hsub : Design.CK H t A ⊆ ({1} : Set G) := fun x hx => by
        rw [Set.mem_singleton_iff]; exact hc x hx
      have hle : (Design.CK H t A).ncard ≤ 1 := by
        calc (Design.CK H t A).ncard ≤ ({1} : Set G).ncard := Set.ncard_le_ncard hsub
          _ = 1 := Set.ncard_singleton 1
      omega
    exact ⟨k, hkS.1, hk1, Subgroup.centralizer_le_normalizer (A : Set G) hkS.2⟩
  -- Ch. II §4 Prop. 3 (c) at `X = A`
  have hP3A := (hC4 G h.sit H h.se t h.invol h.notMem).2.2.2.1 A h.A_ne h.A_le hwit
  have hcore : Submission.Blueprint.oddCore ↥F₀ = Subgroup.center ↥F₀ := hP3A.2.2.1.1
  have hoddZ : Odd (Nat.card ↥(Subgroup.center ↥F₀)) := by
    have hoo := Work.ThompsonFrobenius.odd_oddCore ↥F₀
    rwa [hcore] at hoo
  have ht0 : t ∈ F₀ :=
    Work.ThreePoints.involutions_le_p3F A
      ⟨Work.ThreePoints.mem_centralizer_of_le_centD h.A_le, h.invol⟩
  have hconj1 : Submission.Blueprint.conj (1 : G) H = H := by
    rw [Submission.Blueprint.conj]
    ext x
    simp
  -- Ch. II §4 Prop. 1 (b) at `X = A`, `F = F₀`, `g = 1`: `L` is strongly embedded in `F₀`
  have hLemb : IsStronglyEmbedded L := by
    have h3 := Work.ThreePoints.three_le_fixedPts_of_le_centD h.se h.invol h.notMem h.A_le
    have hinv : involutions (Subgroup.centralizer (A : Set G) : Set G) ⊆ (F₀ : Set G) :=
      Work.ThreePoints.involutions_le_p3F A
    have hnorm : F₀ ≤ Subgroup.normalizer (A : Set G) :=
      Work.ThreePoints.p3cd_p3F_le_normalizer A
    have hAH : A ≤ Submission.Blueprint.conj (1 : G) H := by
      rw [hconj1]
      exact h.A_le.trans (inf_le_left.trans inf_le_left)
    have h := (hC4 G h.sit H h.se t h.invol h.notMem).1 A F₀ h3 hinv hnorm 1 hAH
    rwa [hconj1] at h
  -- `Z(F₀) ≤ L`
  have hZL : Subgroup.center ↥F₀ ≤ L := by
    intro z hz
    by_contra hzL
    have hodd := hLemb.2.2 z hzL
    have hLz : L.map (MulAut.conj z).toMonoidHom = L := by
      have hfix : ∀ x : ↥F₀, (MulAut.conj z) x = x := by
        intro x
        have hc : x * z = z * x := Subgroup.mem_center_iff.mp hz x
        rw [MulAut.conj_apply, hc.symm, mul_assoc, mul_inv_cancel, mul_one]
      have hcong : (MulAut.conj z).toMonoidHom = MonoidHom.id ↥F₀ := MonoidHom.ext hfix
      rw [hcong, Subgroup.map_id]
    rw [hLz, inf_idem] at hodd
    exact (Nat.not_odd_iff_even.mpr hLemb.2.1) hodd
  -- strong embedding of `K = L.map φ` in `Y`
  have hKemb : IsStronglyEmbedded (L.map φ) := by
    obtain ⟨h1, h2, h3⟩ :=
      Commons.GroupTheory.StronglyEmbedded.stronglyEmbedded_map_of_surjective φ hsurj L
        hLemb.1 hLemb.2.1 hLemb.2.2 (by rw [hker]; exact hZL) (by rw [hker])
        (by rw [hker]; exact hoddZ)
    exact ⟨h1, h2, h3⟩
  -- `Y` is a simple Bender group
  obtain ⟨Y', instY', φ', hsurj', hker', hbend'⟩ := hP3A.2.2.1.2
  have hbendY : IsSimpleBenderGroup Y := by
    have hkerEq : φ.ker = φ'.ker := by rw [hker, hker']
    let e₁ : (↥F₀ ⧸ φ.ker) ≃* Y := QuotientGroup.quotientKerEquivOfSurjective φ hsurj
    let e₂ : (↥F₀ ⧸ φ'.ker) ≃* Y' := QuotientGroup.quotientKerEquivOfSurjective φ' hsurj'
    let e₃ : (↥F₀ ⧸ φ.ker) ≃* (↥F₀ ⧸ φ'.ker) := QuotientGroup.quotientMulEquivOfEq hkerEq
    exact isSimpleBenderGroup_of_mulEquiv (e₂.symm.trans (e₃.symm.trans e₁)) hbend'
  -- the involution `t̄ = φ t` and its properties
  let t' : ↥F₀ := ⟨t, ht0⟩
  have ht'2 : orderOf t' = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      apply Subtype.ext
      show t * t = 1
      rw [← pow_two, ← h.invol, pow_orderOf_eq_one]
    · intro h1
      apply h.notMem
      rw [show t = 1 from congrArg (Subtype.val) h1]
      exact Subgroup.one_mem H
  have ht'L : t' ∉ L := fun hmem => h.notMem (Subgroup.mem_subgroupOf.mp hmem).2
  set Kimg : Subgroup Y := L.map φ with hKdef
  have htbarK : φ t' ∉ Kimg := by
    rw [hKdef]
    intro hφ
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp hφ
    have hkerl : t' * l⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlx, mul_inv_cancel]
    have hLmem : t' * l⁻¹ ∈ L := by
      rw [hker] at hkerl
      exact hZL hkerl
    exact ht'L (by simpa using L.mul_mem hLmem hl)
  have htbar2 : orderOf (φ t') = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two, ← map_mul]
      have ht2 : t' * t' = 1 := by
        apply Subtype.ext
        show t * t = 1
        rw [← pow_two, ← h.invol, pow_orderOf_eq_one]
      rw [ht2, map_one]
    · intro h1
      exact htbarK (by rw [h1]; exact Subgroup.one_mem Kimg)
  -- `centD Kimg (φ t') = ⊥`
  have hcent : Subgroup.centralizer ({t'} : Set ↥F₀) ⊓ (L ⊓ L.map (MulAut.conj t').toMonoidHom) ≤
      Subgroup.center ↥F₀ := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxL, hxLt⟩ := Subgroup.mem_inf.mp hx2
    refine sec5_zass_centV hFT hC4 h x ?_
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_subgroupOf.mp hxL).2, ?_⟩
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxLt
      refine Subgroup.mem_map.mpr ⟨(y : G), (Subgroup.mem_subgroupOf.mp hy).2, ?_⟩
      have hcoe : (((MulAut.conj t') y : ↥F₀) : G) = (MulAut.conj t) (y : G) := by
        rw [MulAut.conj_apply, MulAut.conj_apply]
        rfl
      show (MulAut.conj t) (y : G) = (x : G)
      rw [← hcoe]
      exact congrArg Subtype.val hyx
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 : t' * x = x * t' := (Subgroup.mem_centralizer_iff.mp hx1) t' (Set.mem_singleton t')
      exact congrArg (Subtype.val) h1
  have hcentD : Submission.Blueprint.centD Kimg (φ t') = ⊥ := by
    rw [hKdef]
    exact sec5_zass_centD φ hsurj hker hoddZ hZL ht'2 hcent
  -- the split rank-one datum from `ModelFactsProp`
  obtain ⟨-, -, -, hMF⟩ := Work.Models.models_prop Y hbendY
  obtain ⟨-, hMFt⟩ := hMF Kimg hKemb
  obtain ⟨S, K', hS2, hSle, hSnorm, hSinf, hSsup, -, -, -⟩ := hMFt (φ t') htbar2 htbarK
  have h2trans : MulAction.IsMultiplyPretransitive Y (Y ⧸ Kimg) 2 := by
    obtain ⟨Pmd, hPB⟩ := Work.PSU3.StageA.modelDataBorel hbendY hKemb
    rw [← hPB]
    exact Pmd.isMultiplyPretransitive_two
  have hsplit : Submission.Blueprint.IsSplitRankOne Kimg S (φ t') :=
    ⟨hKemb, h2trans, htbar2, htbarK, hSle, hSnorm, hSinf, hSsup⟩
  exact Work.ThmF.ChV12.isZassenhaus_of_centD_eq_bot hsplit hS2 hcentD

end Work.NormalComplement
