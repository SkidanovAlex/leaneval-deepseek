import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.p3Normal_of_chIIFourP3Subnormal
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.NormalComplement.section3_prop2
import Submission.Work.LocalPrelim.card_map_mul_card_inf_ker
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_conj_map
import Submission.Work.ThreePoints.sec4_prop3_cd_ne_bot
import Submission.Work.NormalComplement.sec5_setup_invol
import Submission.Work.NormalComplement.sec5_setup_p3F_center
import Submission.Work.NormalComplement.sec5_setup_zassenhaus
import Submission.Work.NormalComplement.sec5_setup_invol_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-- **Strong embeddedness passes to the image.**  If `φ : X →* Z` is a homomorphism whose kernel
`N` (of odd order) is contained in the subgroup `L ≤ X`, then `L.map φ` is strongly embedded in `Z`
whenever `L` is strongly embedded in `X`.

(The oddness of `|N|` makes `|L.map φ| = |L| / |N|` even; oddness of the intersections transports
because `φ.ker ≤ L` makes `Subgroup.map φ` commute with `⊓`.)  This is the transport used in
`sec5_setup` with `X = ↥F₀`, `Z = Y`, `N = Z(F₀)`, `L = F₀ ⊓ H`. -/
theorem isStronglyEmbedded_map_of_surjective {X Z : Type} [Group X] [Finite X] [Group Z] [Finite Z]
    (φ : X →* Z) (hsurj : Function.Surjective φ) {N : Subgroup X} (hker : φ.ker = N)
    (hodd : Odd (Nat.card N)) {L : Subgroup X} (hNL : N ≤ L)
    (hL : IsStronglyEmbedded L) :
    IsStronglyEmbedded (L.map φ) := by
  have hkerL : φ.ker ≤ L := by rw [hker]; exact hNL
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    have h1 := Subgroup.comap_map_eq_self (f := φ) hkerL
    rw [htop, Subgroup.comap_top] at h1
    exact hL.1 h1.symm
  · have hM : Nat.card (L.map φ) * Nat.card ↥(L ⊓ φ.ker) = Nat.card L :=
      Work.LocalPrelim.card_map_mul_card_inf_ker φ L
    have hinf : L ⊓ φ.ker = N := by rw [hker, inf_eq_right.mpr hNL]
    rw [hinf] at hM
    have h2 : 2 ∣ Nat.card (L.map φ) := by
      have h2L : 2 ∣ Nat.card L := even_iff_two_dvd.mp hL.2.1
      rw [← hM] at h2L
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2L with h | h
      · exact h
      · exact absurd (even_iff_two_dvd.mpr h) (Nat.not_even_iff_odd.mpr hodd)
    exact even_iff_two_dvd.mpr h2
  · intro g hg
    obtain ⟨x, rfl⟩ := hsurj g
    have hxL : x ∉ L := fun hx => hg (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    have hoddA := hL.2.2 x hxL
    have hB : Subgroup.map φ (L ⊓ Subgroup.map (MulAut.conj x).toMonoidHom L)
        = Subgroup.map φ L ⊓ Subgroup.map (MulAut.conj (φ x)).toMonoidHom (Subgroup.map φ L) := by
      rw [Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le φ L
        (Subgroup.map (MulAut.conj x).toMonoidHom L) hkerL]
      rw [Commons.GroupTheory.Subgroup.map_conj_map φ L x]
    have hdvd : Nat.card ↥(Subgroup.map φ L ⊓
          Subgroup.map (MulAut.conj (φ x)).toMonoidHom (Subgroup.map φ L))
        ∣ Nat.card ↥(L ⊓ Subgroup.map (MulAut.conj x).toMonoidHom L) := by
      rw [← hB]
      exact Subgroup.card_map_dvd _ φ
    exact Nat.not_even_iff_odd.mp fun hev =>
      (Nat.not_even_iff_odd.mpr hoddA)
        (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp hev) hdvd))

/-- **Ch. II §4 Prop. 1 (b) at `X = A`, `F = O^{2'}(C_G(A))`, `g = 1`**: `F₀ ⊓ H` is strongly
embedded in `F₀ = C_{F₀}… = O^{2'}(C_G(A))`.  (`hC4` P1(b) needs `3 ≤ |fixedPts H A|`
(Prop. 2 of Ch. II §4 / `three_le_fixedPts_of_le_centD`), `Inv C_G(A) ⊆ F₀`, `F₀ ≤ N_G(A)`, and
`A ≤ H`.) -/
theorem p3F_inf_stronglyEmbedded (hC4 : Submission.Blueprint.ChIIFourProp) {G : Type}
    [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}
    {r : ℕ} (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    IsStronglyEmbedded ((Work.ThreePoints.p3F A ⊓ H).subgroupOf (Work.ThreePoints.p3F A)) := by
  have h3 : 3 ≤ (fixedPts H A).ncard :=
    Work.ThreePoints.three_le_fixedPts_of_le_centD h.se h.invol h.notMem h.A_le
  have hinv : involutions (Subgroup.centralizer (A : Set G) : Set G) ⊆
      Work.ThreePoints.p3F A := Work.ThreePoints.involutions_le_p3F A
  have hnorm : Work.ThreePoints.p3F A ≤ Subgroup.normalizer (A : Set G) := by
    intro x hx
    rw [Work.ThreePoints.mem_p3F] at hx
    obtain ⟨c, _hc, rfl⟩ := hx
    exact Subgroup.centralizer_le_normalizer (A : Set G) c.2
  have hres := (hC4 G h.sit H h.se t h.invol h.notMem).1 A (Work.ThreePoints.p3F A)
    h3 hinv hnorm 1 (by simpa using (h.A_le.trans (le_trans inf_le_left inf_le_left) : A ≤ H))
  simpa using hres

/-- The involutions of `L.subgroupOf F` are exactly the involutions of `L` (for `L ≤ F`), so the
two sets have the same cardinality. -/
theorem involutions_ncard_subgroupOf_eq {G : Type} [Group G] {F L : Subgroup G} (hLF : L ≤ F) :
    (Submission.Blueprint.involutions ((L.subgroupOf F : Subgroup ↥F) : Set ↥F)).ncard =
      (Submission.Blueprint.involutions (L : Set G)).ncard := by
  refine Set.ncard_congr (fun x _ => (x : G)) ?_ ?_ ?_
  · intro x hx
    rw [Submission.Blueprint.involutions, Set.mem_setOf_eq] at hx ⊢
    exact ⟨Subgroup.mem_subgroupOf.mp hx.1,
      (orderOf_injective F.subtype F.subtype_injective x).trans hx.2⟩
  · intro a b _ _ hab
    exact Subtype.ext hab
  · intro b hb
    rw [Submission.Blueprint.involutions, Set.mem_setOf_eq] at hb
    exact ⟨⟨b, hLF hb.1⟩,
      ⟨Subgroup.mem_subgroupOf.mpr hb.1,
        (orderOf_injective F.subtype F.subtype_injective ⟨b, hLF hb.1⟩).symm.trans hb.2⟩,
      rfl⟩

/-- **Peterfalvi I Ch. III §5 Proposition 2 (a), Bender-group input** (p.184), merged with the
existence and uniqueness of the involution `u`: there is a unique `u ∈ H` with `orderOf u = 2`
centralising `V = centD H t` (because `|Inv N_H(V)| = |N_K(V)| = 1`, `P` being fixed-point-free on
`K`), and with `C = C_G(A)`, `F₀ = O^{2'}(C)` (as a subgroup of `G`), the quotient `F₀/Z(F₀)` is a
simple Bender group `Y`, the image of `F₀ ⊓ H` is strongly embedded in `Y` and `Y` is a Zassenhaus
group on its cosets, with `|Inv| = |C_K(A)| = 2^p - 1`; the images of `u` and `t` are involutions,
that of `t` outside `K`.  Route in `_design/Sec5.lean` (`sec5_invol_CHV`, `sec5_prop2a_bender`):
Ch. II §4 Prop. 3 (c) (`ChIIFourProp`, `X = A`, `N_K(A) ⊇ C_K(A) ≠ 1`) gives `F₀/Z(F₀)` simple
Bender and the Sylow structure; `[A,P] = F(V) ≠ 1` shows the pointwise stabiliser of three points
of `Ω_A` lies in `F₀ ⊓ V = F₀ ⊓ A ≤ Z(F₀)`, so `Y` is Zassenhaus; the strong embedding is
transported along `F₀ → F₀/Z(F₀)` (`Submission.Work.ThreePoints.isStronglyEmbedded_map_quotient`). -/
theorem sec5_setup (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    (∃! u : G, u ∈ H ∧ orderOf u = 2 ∧
        u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) ∧
      ∃ (u : G) (_ : u ∈ H ∧ orderOf u = 2 ∧
          u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)),
        let C : Subgroup G := Subgroup.centralizer (A : Set G)
        let F₀ : Subgroup G := (Submission.Blueprint.oddResidual ↥C).map C.subtype
        ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (φ : F₀ →* Y) (K : Subgroup Y),
          Function.Surjective φ ∧ φ.ker = Subgroup.center ↥F₀ ∧
          LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y ∧
          LeanEval.GroupTheory.Defs.IsStronglyEmbedded K ∧
          Submission.Blueprint.IsZassenhaus K ∧
          (Submission.Blueprint.involutions (K : Set Y)).ncard = 2 ^ p - 1 ∧
          ∃ (hu0 : u ∈ F₀) (ht0 : t ∈ F₀),
            φ ⟨u, hu0⟩ ∈ K ∧ orderOf (φ ⟨u, hu0⟩) = 2 ∧ φ ⟨t, ht0⟩ ∉ K ∧
            orderOf (φ ⟨t, ht0⟩) = 2 ∧
            ∀ x : F₀, (x : G) ∈ H → φ x ∈ K := by
  classical
  -- ## the unique involution `u ∈ C_H(V)`
  have hInvol : ∃! u : G, u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) :=
    sec5_setup_invol hFT hC4 hP3 h
  refine ⟨hInvol, ?_⟩
  obtain ⟨u, hu, _huniq⟩ := hInvol
  refine ⟨u, hu, ?_⟩
  -- ## match the `let`-binders of the goal
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  let F₀ : Subgroup G := (Submission.Blueprint.oddResidual ↥C).map C.subtype
  change ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (φ : F₀ →* Y) (K : Subgroup Y),
      Function.Surjective φ ∧ φ.ker = Subgroup.center ↥F₀ ∧
      LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y ∧
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded K ∧
      Submission.Blueprint.IsZassenhaus K ∧
      (Submission.Blueprint.involutions (K : Set Y)).ncard = 2 ^ p - 1 ∧
      ∃ (hu0 : u ∈ F₀) (ht0 : t ∈ F₀),
        φ ⟨u, hu0⟩ ∈ K ∧ orderOf (φ ⟨u, hu0⟩) = 2 ∧ φ ⟨t, ht0⟩ ∉ K ∧
        orderOf (φ ⟨t, ht0⟩) = 2 ∧
        ∀ x : F₀, (x : G) ∈ H → φ x ∈ K
  -- ## `N_K(A) ≠ 1`, so that Ch. II §4 Prop. 3 applies at `X = A`
  have hNK : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t,
      k ≠ 1 ∧ k ∈ Subgroup.normalizer (A : Set G) := by
    have hcard : (Design.CK H t A).ncard = 2 ^ p - 1 := h.A_CK
    have h1mem : (1 : G) ∈ Design.CK H t A :=
      ⟨⟨(Submission.Blueprint.twoPoint H t).one_mem, by simp⟩,
        (Subgroup.centralizer (A : Set G)).one_mem⟩
    have hpow : 2 ^ p - 1 ≠ 1 := by
      have h4 : 4 ≤ 2 ^ p := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) h.prime.two_le
      omega
    obtain ⟨k, hk, hk1⟩ : ∃ k ∈ Design.CK H t A, k ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have hsingle : Design.CK H t A = {1} := Set.eq_singleton_iff_unique_mem.mpr ⟨h1mem, hcon⟩
      rw [hsingle, Set.ncard_singleton] at hcard
      exact hpow hcard.symm
    exact ⟨k, hk.1, hk1, Subgroup.centralizer_le_normalizer (A : Set G) hk.2⟩
  -- ## Ch. II §4 Prop. 3 at `X = A`: the Bender-group datum
  obtain ⟨_hNG, _hSyl, hBend, _hCyc⟩ :=
    (hC4 G h.sit H h.se t h.invol h.notMem).2.2.2.1 A h.A_ne h.A_le hNK
  obtain ⟨_hZc, Y, hYgrp, φ, hφsurj, hφker, hYbender⟩ := hBend
  letI : Group Y := hYgrp
  haveI : Finite Y := Finite.of_surjective φ hφsurj
  have hYfin : Finite Y := Finite.of_surjective φ hφsurj
  -- ## the subgroup `L = (F₀ ⊓ H).subgroupOf F₀` is strongly embedded in `F₀`
  have hLse : IsStronglyEmbedded ((F₀ ⊓ H).subgroupOf F₀) := p3F_inf_stronglyEmbedded hC4 h
  -- ## the centre of `F₀` sits inside `L` and has odd order
  have hZle : Subgroup.center ↥F₀ ≤ (F₀ ⊓ H).subgroupOf F₀ :=
    (sec5_setup_p3F_center hFT hC4 h).2.1
  have hZodd : Odd (Nat.card (Subgroup.center ↥F₀)) :=
    (sec5_setup_p3F_center hFT hC4 h).2.2
  -- ## `K = L.map φ` is strongly embedded in `Y` and Zassenhaus
  have hKse : IsStronglyEmbedded (((F₀ ⊓ H).subgroupOf F₀).map φ) :=
    isStronglyEmbedded_map_of_surjective φ hφsurj hφker hZodd hZle hLse
  have hKzass : Submission.Blueprint.IsZassenhaus (((F₀ ⊓ H).subgroupOf F₀).map φ) :=
    sec5_setup_zassenhaus hFT hC4 hP3 h Y φ hφsurj hφker
  -- ## the involution count `|Inv K| = 2^p - 1`
  have hLcard : (Submission.Blueprint.involutions ((F₀ ⊓ H : Subgroup G) : Set G)).ncard
      = 2 ^ p - 1 :=
    (sec5_setup_p3F_center hFT hC4 h).1
  have hKcard : (Submission.Blueprint.involutions
      ((((F₀ ⊓ H).subgroupOf F₀).map φ : Subgroup Y) : Set Y)).ncard = 2 ^ p - 1 := by
    have hmap : {z : Y | z ∈ (((F₀ ⊓ H).subgroupOf F₀).map φ : Subgroup Y) ∧
          orderOf z = 2}.ncard
        = {x : ↥F₀ | x ∈ (F₀ ⊓ H).subgroupOf F₀ ∧ orderOf x = 2}.ncard :=
      sec5_setup_invol_card (X := ↥F₀) (Z := Y) φ hφker le_rfl hZodd hZle
    have htrans : {x : ↥F₀ | x ∈ (F₀ ⊓ H).subgroupOf F₀ ∧ orderOf x = 2}.ncard
        = (Submission.Blueprint.involutions ((F₀ ⊓ H : Subgroup G) : Set G)).ncard := by
      rw [Submission.Blueprint.involutions]
      exact involutions_ncard_subgroupOf_eq (F := F₀) (L := F₀ ⊓ H) inf_le_left
    rw [show (Submission.Blueprint.involutions
        ((((F₀ ⊓ H).subgroupOf F₀).map φ : Subgroup Y) : Set Y)).ncard
        = {z : Y | z ∈ (((F₀ ⊓ H).subgroupOf F₀).map φ : Subgroup Y) ∧
            orderOf z = 2}.ncard from rfl, hmap, htrans, hLcard]
  -- ## `u` and `t` lie in `F₀`
  have huC : u ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp hu.2.2) a (h.A_le ha)
  have hu2 : u * u = 1 := by
    have hh := pow_orderOf_eq_one u
    rw [hu.2.1] at hh
    simpa [pow_two] using hh
  have hu0 : u ∈ F₀ := by
    refine Subgroup.mem_map.mpr ⟨⟨u, huC⟩, ?_, rfl⟩
    exact (Work.Reductions.oddResidual_basic (G := ↥C)).2.2.2 ⟨u, huC⟩ (Subtype.ext hu2)
  have htC : t ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (h.A_le ha)).2
  have ht2 : t * t = 1 := by
    have hh := pow_orderOf_eq_one t
    rw [h.invol] at hh
    simpa [pow_two] using hh
  have ht0 : t ∈ F₀ := by
    refine Subgroup.mem_map.mpr ⟨⟨t, htC⟩, ?_, rfl⟩
    exact (Work.Reductions.oddResidual_basic (G := ↥C)).2.2.2 ⟨t, htC⟩ (Subtype.ext ht2)
  -- ## the images of `u` and `t`
  have hφuK : φ ⟨u, hu0⟩ ∈ ((F₀ ⊓ H).subgroupOf F₀).map φ :=
    Subgroup.mem_map.mpr ⟨⟨u, hu0⟩, by rw [Subgroup.mem_subgroupOf]; exact ⟨hu0, hu.1⟩, rfl⟩
  have hφtK : φ ⟨t, ht0⟩ ∉ ((F₀ ⊓ H).subgroupOf F₀).map φ := by
    intro hmem
    have hcomap : Subgroup.comap φ (((F₀ ⊓ H).subgroupOf F₀).map φ)
        = (F₀ ⊓ H).subgroupOf F₀ :=
      Subgroup.comap_map_eq_self (f := φ) (H := (F₀ ⊓ H).subgroupOf F₀)
        (by rw [hφker]; exact hZle)
    have hmem' : (⟨t, ht0⟩ : ↥F₀) ∈ (F₀ ⊓ H).subgroupOf F₀ := by
      rw [← hcomap]; exact hmem
    exact h.notMem (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem')).2
  have hord_u : orderOf (⟨u, hu0⟩ : ↥F₀) = 2 :=
    (orderOf_injective F₀.subtype F₀.subtype_injective ⟨u, hu0⟩).symm.trans hu.2.1
  have hord_t : orderOf (⟨t, ht0⟩ : ↥F₀) = 2 :=
    (orderOf_injective F₀.subtype F₀.subtype_injective ⟨t, ht0⟩).symm.trans h.invol
  have hφu_ne : φ ⟨u, hu0⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨u, hu0⟩ : ↥F₀) ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hφker] at hmem
    have hdvd : 2 ∣ Nat.card (Subgroup.center ↥F₀) := by
      rw [← hord_u]; exact Subgroup.orderOf_dvd_natCard _ hmem
    exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr hdvd)
  have hφt_ne : φ ⟨t, ht0⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨t, ht0⟩ : ↥F₀) ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hφker] at hmem
    have hdvd : 2 ∣ Nat.card (Subgroup.center ↥F₀) := by
      rw [← hord_t]; exact Subgroup.orderOf_dvd_natCard _ hmem
    exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr hdvd)
  have hφu2 : orderOf (φ ⟨u, hu0⟩) = 2 := by
    have hd := orderOf_map_dvd φ (⟨u, hu0⟩ : ↥F₀)
    rw [hord_u] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hφu_ne
    · exact h
  have hφt2 : orderOf (φ ⟨t, ht0⟩) = 2 := by
    have hd := orderOf_map_dvd φ (⟨t, ht0⟩ : ↥F₀)
    rw [hord_t] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hφt_ne
    · exact h
  refine ⟨Y, hYgrp, hYfin, φ, ((F₀ ⊓ H).subgroupOf F₀).map φ, hφsurj, hφker, hYbender,
    hKse, hKzass, hKcard, hu0, ht0, hφuK, hφu2, hφtK, hφt2, ?_⟩
  intro x hxH
  exact Subgroup.mem_map.mpr ⟨x, by rw [Subgroup.mem_subgroupOf]; exact ⟨x.2, hxH⟩, rfl⟩

end Work.NormalComplement
