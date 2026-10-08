import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.cardKsetEqInv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

/-! ## Two ingredients

* `conj_image_invertedBy_eq_involutions`: `K = J(D,t) = invertedBy (twoPoint H t) t` sweeps out
  `Inv H` under conjugation (Peterfalvi I Ch. I §2 Prop. 2 (b), witness form: the witness of the
  transitivity lies in `K`, not merely in `D`).  This is the argument of
  `Work.ThmF.Bender.DTransitiveInv` / `Work.ThreePoints.twoPoint_transitive_on_involutions` with
  the witness kept in `K`.

* `le_centralizer_of_odd_index`: the orbit-counting step.  If `S ≤ L` with `L` normalising the
  `2`-group `S`, and `|L : C_L(u)|` is odd, then `S` centralises `u`.  Indeed the `S`-orbit `O` of
  `u` has size dividing `|S|`, hence a power of `2`; and `O` is also the orbit of `u` under
  `S ⊔ M` (`M = L ∩ C_G(u)`, whose elements normalise `S`), so `|O| = |S ⊔ M : M|` divides
  `|L : M|`, which is odd.  Hence `|O| = 1`. -/

/-- For every involution `u ∈ H` the map `x ↦ x * u * x⁻¹` maps `K = invertedBy (twoPoint H t) t`
onto the set of involutions of `H`. -/
private theorem conj_image_invertedBy_eq_involutions {G : Type} [Group G] [Finite G]
    {H : Subgroup G} (hH : IsStronglyEmbedded H) {t u : G} (ht : orderOf t = 2)
    (htH : t ∉ H) (hu : u ∈ involutions (H : Set G)) :
    (fun x => x * u * x⁻¹) '' (invertedBy (twoPoint H t) t) = involutions (H : Set G) := by
  have hK : (invertedBy (twoPoint H t) t).ncard = (involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv hH ht htH
  have hmaps : ∀ x ∈ invertedBy (twoPoint H t) t, x * u * x⁻¹ ∈ involutions (H : Set G) := by
    intro x hx
    have hxH : x ∈ H := (Subgroup.mem_inf.mp hx.1).1
    exact ⟨H.mul_mem (H.mul_mem hxH hu.1) (H.inv_mem hxH),
      by rw [Work.ThmF.Bender.orderOf_conj_eq, hu.2]⟩
  have hinj : Set.InjOn (fun x => x * u * x⁻¹) (invertedBy (twoPoint H t) t) :=
    invertedBy_conj_injective hH ht htH hu.1 hu.2
  have himg : ((fun x => x * u * x⁻¹) '' (invertedBy (twoPoint H t) t)).ncard =
      (involutions (H : Set G)).ncard := by
    rw [Set.InjOn.ncard_image hinj, hK]
  have hsub : (fun x => x * u * x⁻¹) '' (invertedBy (twoPoint H t) t) ⊆
      involutions (H : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmaps x hx
  exact Set.eq_of_subset_of_ncard_le hsub (le_of_eq himg.symm)

/-- **Orbit counting.**  Let `S ≤ L` be subgroups of a finite group, `L` normalising the
`2`-group `S`, and let the index `|L : L ∩ C_G(u)|` be odd.  Then `S` centralises `u`. -/
private theorem le_centralizer_of_odd_index {G : Type} [Group G] [Finite G] {S L : Subgroup G}
    {u : G} (hSL : S ≤ L) (hnorm : L ≤ Subgroup.normalizer (S : Set G)) (hS : IsPGroup 2 S)
    (hodd : Odd ((L ⊓ Subgroup.centralizer ({u} : Set G)).relIndex L)) :
    S ≤ Subgroup.centralizer ({u} : Set G) := by
  classical
  set M : Subgroup G := L ⊓ Subgroup.centralizer ({u} : Set G) with hMdef
  have hML : M ≤ L := by rw [hMdef]; exact inf_le_left
  have hSM : M ≤ Subgroup.normalizer (S : Set G) := le_trans hML hnorm
  have hsupL : S ⊔ M ≤ L := sup_le hSL hML
  -- membership in `M = L ⊓ C_G(u)`
  have hMu : ∀ m ∈ M, m * u * m⁻¹ = u := by
    intro m hm
    have hm1 : m ∈ L ⊓ Subgroup.centralizer ({u} : Set G) := by rwa [hMdef] at hm
    exact mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hm1).2)
  have hMu' : ∀ m : G, m ∈ L → m * u * m⁻¹ = u → m ∈ M := by
    intro m hmL hmc
    rw [hMdef]
    exact ⟨hmL, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hmc)⟩
  letI : MulAction ↥S G := MulAction.compHom G (MulAut.conj.comp S.subtype)
  letI : MulAction ↥(S ⊔ M) G := MulAction.compHom G (MulAut.conj.comp (S ⊔ M).subtype)
  have hsmulS : ∀ (x : ↥S) (g : G), x • g = (x : G) * g * (x : G)⁻¹ := by
    intro x g
    rw [show x • g = (MulAut.conj (x : G)) • g from rfl, MulAut.smul_def, MulAut.conj_apply]
  have hsmulSM : ∀ (x : ↥(S ⊔ M)) (g : G), x • g = (x : G) * g * (x : G)⁻¹ := by
    intro x g
    rw [show x • g = (MulAut.conj (x : G)) • g from rfl, MulAut.smul_def, MulAut.conj_apply]
  -- the orbits of `u` under `S ⊔ M` and under `S` agree
  have horb : MulAction.orbit ↥(S ⊔ M) u = MulAction.orbit ↥S u := by
    ext x
    constructor
    · intro hx
      obtain ⟨h, rfl⟩ := hx
      have hh : (h : G) ∈ (↑(S ⊔ M) : Set G) := h.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left S M hSM, Set.mem_mul] at hh
      obtain ⟨s, hs, m, hm, hsm⟩ := hh
      refine ⟨⟨s, hs⟩, ?_⟩
      have hmc : m * u * m⁻¹ = u := hMu m hm
      simp only [hsmulS, hsmulSM, ← hsm]
      calc s * u * s⁻¹ = s * (m * u * m⁻¹) * s⁻¹ := by rw [hmc]
        _ = (s * m) * u * (s * m)⁻¹ := by group
    · rintro ⟨s, rfl⟩
      exact ⟨⟨(s : G), Subgroup.mem_sup_left s.2⟩, by simp only [hsmulS, hsmulSM]⟩
  -- the stabiliser of `u` in `S ⊔ M` is `M`
  have hstabSM : MulAction.stabilizer ↥(S ⊔ M) u = M.subgroupOf (S ⊔ M) := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hsmulSM]
    constructor
    · intro hh
      exact hMu' (h : G) (hsupL h.2) hh
    · intro hh
      exact hMu (h : G) hh
  -- `|S-orbit| = |S ⊔ M : M|`
  have hd_eq : (MulAction.orbit ↥S u).ncard = M.relIndex (S ⊔ M) := by
    rw [← horb, ← MulAction.index_stabilizer, hstabSM]
    rfl
  -- `|S-orbit|` divides `|S|`
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hdvd2 : (MulAction.orbit ↥S u).ncard ∣ 2 ^ k := by
    rw [← hk, ← MulAction.index_stabilizer ↥S u]
    exact Subgroup.index_dvd_card _
  -- `|S-orbit|` divides `|L : M|`, which is odd
  have hrel : M.relIndex (S ⊔ M) * (S ⊔ M).relIndex L = M.relIndex L :=
    Subgroup.relIndex_mul_relIndex (H := M) (K := S ⊔ M) (L := L) le_sup_right hsupL
  have hdvdM : (MulAction.orbit ↥S u).ncard ∣ M.relIndex L := by
    rw [hd_eq, ← hrel]
    exact dvd_mul_right _ _
  have hoddM : Odd (M.relIndex L) := by rw [hMdef]; exact hodd
  have hoddO : Odd (MulAction.orbit ↥S u).ncard := Work.ThreePoints.Odd.of_dvd hdvdM hoddM
  -- hence `|S-orbit| = 1`
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have hj0 : j = 0 := by
    rcases j with _ | m
    · rfl
    · exfalso
      rw [hj] at hoddO
      exact (odd_iff_not_two_dvd (2 ^ (m + 1))).mp hoddO ⟨2 ^ m, by rw [pow_succ']⟩
  have hd1 : (MulAction.orbit ↥S u).ncard = 1 := by rw [hj, hj0, pow_zero]
  have hsing : MulAction.orbit ↥S u = {u} := by
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp hd1
    have hu_mem : u ∈ ({y} : Set G) := by
      rw [← hy]
      exact ⟨1, one_smul ↥S u⟩
    rw [Set.mem_singleton_iff] at hu_mem
    rw [hy, hu_mem]
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : (⟨s, hs⟩ : ↥S) • u ∈ MulAction.orbit ↥S u := ⟨⟨s, hs⟩, rfl⟩
  simp only [hsing, Set.mem_singleton_iff, hsmulS] at hmem
  exact mul_inv_eq_iff_eq_mul.mp hmem

/-- The `S ⊆ C_H(Inv H)` step of Peterfalvi I Ch. II §4 Prop. 4 (b) (p. 171).  Setting
`D = H ∩ H^t`, `K = J(D,t)` and `C = C_H(Inv H)`: if `S ≤ H` is a `2`-subgroup with
`S ⊓ D = ⊥` and `N_H(X) = S ⋊ N_D(X)` (the shape of Prop. 3 (b)), where `X ≤ C(K)` and
`X ≤ N(S)`, then `S ≤ C`.

Mathematical argument (source, p. 171: "Inv(H) = Inv N_H(X) ⊂ S, and Inv(H) is central in S
since K = N_K(X) acts transitively on Inv(H)"):
put `L = S ⊔ ⟨K⟩`.  Since `K ⊆ D` and `K ⊆ N(X) ≤ N(S)` (from `X ≤ C(K)`), `S ⊴ L` and
`|L : S| = |⟨K⟩|` is odd.  Because `K` acts transitively on `Inv H` (Ch. I §2 Prop. 2 (b),
`Work.ThreePoints.twoPoint_transitive_on_involutions`; the witness lies in `K = invertedBy D t`)
and `K ≤ L ≤ H`, the orbit of any `u ∈ Inv H` under `L` is all of `Inv H`; hence
`|L : (L)_u| = |Inv H|`, which is odd (`|K| = |Inv H|`).  A Sylow `2`-subgroup of `L` therefore
has order `|L|₂ = |(L)_u|₂`, and since `|L : S|` is odd, `S` is such a Sylow; `S ⊴ L` then gives
`S ≤ (L)_u`, i.e. every element of `S` fixes `u`.  As `u` was arbitrary, `S ≤ C`.

Useful helpers: `Work.ThmF.Bender.cardKsetEqInv` (`|K| = |Inv H|`),
`Work.ThmF.Bender.Kset_conj_injective` / `Work.ThreePoints.invertedBy_conj_injective`
(injectivity of `x ↦ x * u * x⁻¹` on `K`, giving the transitivity with witness in `K`),
`IsPGroup.index` (a subgroup of a `2`-group has `2`-power index),
`Subgroup.card_mul_index`, `Subgroup.relIndex_mul_index`. -/
theorem prop4b_S_le_centralizer {G : Type} [Group G] [Finite G]
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) (S X : Subgroup G)
    (hS2 : IsPGroup 2 S) (hSH : S ≤ H)
    (hSN : S ≤ Subgroup.normalizer (X : Set G))
    (hNS : H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G))
    (hSD : S ⊓ Submission.Blueprint.twoPoint H t = ⊥)
    (hA : S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) =
        H ⊓ Subgroup.normalizer (X : Set G))
    (hKX : X ≤ Subgroup.centralizer (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t)) :
    S ≤ H ⊓ Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) := by
  classical
  set L : Subgroup G := H ⊓ Subgroup.normalizer (X : Set G) with hLdef
  have hSL : S ≤ L := by rw [hLdef]; exact le_inf hSH hSN
  have hLH : L ≤ H := by rw [hLdef]; exact inf_le_left
  have hnorm : L ≤ Subgroup.normalizer (S : Set G) := by rw [hLdef]; exact hNS
  -- `K = J(D,t)` lies in `L`
  have hKL : ∀ k ∈ invertedBy (twoPoint H t) t, k ∈ L := by
    intro k hk
    have hkD : k ∈ twoPoint H t := (Work.ThreePoints.mem_invertedBy.mp hk).1
    refine ⟨(Subgroup.mem_inf.mp hkD).1, ?_⟩
    refine Subgroup.centralizer_le_normalizer (X : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact ((Subgroup.mem_centralizer_iff.mp (hKX hx)) k hk).symm
  -- `|Inv H|` is odd (it is `|K|`, which divides the odd number `|D|`)
  have hoddD : Odd (Nat.card (twoPoint H t)) := by
    rw [twoPoint_eq]
    exact IsStronglyEmbedded.odd_card_inf_conj hH htH
  have hoddInv : Odd (involutions (H : Set G)).ncard := by
    have h1 : Nat.card (centD H t : Subgroup G) * (invertedBy (twoPoint H t) t).ncard =
        Nat.card (twoPoint H t) :=
      (card_twoPoint_eq_card_centD_mul_ncard_invertedBy (G := G) hH ht htH).symm
    have h2 : ¬ 2 ∣ (invertedBy (twoPoint H t) t).ncard := by
      intro h2dvd
      have h3 : 2 ∣ Nat.card (centD H t : Subgroup G) * (invertedBy (twoPoint H t) t).ncard :=
        dvd_mul_of_dvd_right h2dvd _
      rw [h1] at h3
      exact (odd_iff_not_two_dvd _).mp hoddD h3
    have h4 : ¬ 2 ∣ (Work.ThmF.Kset H t).ncard := h2
    rw [Work.ThmF.Bender.cardKsetEqInv hH ht htH] at h4
    exact (odd_iff_not_two_dvd _).mpr h4
  letI : MulAction ↥L G := MulAction.compHom G (MulAut.conj.comp L.subtype)
  have hsmulL : ∀ (l : ↥L) (g : G), l • g = (l : G) * g * (l : G)⁻¹ := by
    intro l g
    rw [show l • g = (MulAut.conj (l : G)) • g from rfl, MulAut.smul_def, MulAut.conj_apply]
  -- the orbit of `u ∈ Inv H` under `L` is all of `Inv H`
  have horbitL : ∀ u ∈ involutions (H : Set G),
      MulAction.orbit ↥L u = involutions (H : Set G) := by
    intro u hu
    apply Set.Subset.antisymm
    · rintro x ⟨l, rfl⟩
      simp only [hsmulL]
      exact ⟨H.mul_mem (H.mul_mem (hLH l.2) hu.1) (H.inv_mem (hLH l.2)),
        by rw [Work.ThmF.Bender.orderOf_conj_eq, hu.2]⟩
    · intro v hv
      have hv' : v ∈ (fun x => x * u * x⁻¹) '' (invertedBy (twoPoint H t) t) := by
        rw [conj_image_invertedBy_eq_involutions hH ht htH hu]
        exact hv
      obtain ⟨d, hd, hdv⟩ := hv'
      refine ⟨⟨d, hKL d hd⟩, ?_⟩
      simp only [hsmulL]
      exact hdv
  -- the stabiliser of `u` in `L` is `L ⊓ C_G(u)`
  have hstabL : ∀ u : G, MulAction.stabilizer ↥L u =
      (L ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf L := by
    intro u
    ext l
    simp only [MulAction.mem_stabilizer_iff, hsmulL, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨l.2, mul_inv_eq_iff_eq_mul.mp h⟩
    · rintro ⟨-, h⟩
      exact mul_inv_eq_iff_eq_mul.mpr h
  -- hence the index `|L : C_L(u)| = |Inv H|` is odd for every `u ∈ Inv H`
  have hoddIdx : ∀ u ∈ involutions (H : Set G),
      Odd ((L ⊓ Subgroup.centralizer ({u} : Set G)).relIndex L) := by
    intro u hu
    have h1 : (L ⊓ Subgroup.centralizer ({u} : Set G)).relIndex L =
        (MulAction.orbit ↥L u).ncard := by
      rw [Subgroup.relIndex, ← hstabL u, MulAction.index_stabilizer]
    rw [h1, horbitL u hu]
    exact hoddInv
  -- assembly
  refine le_inf hSH ?_
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hle := le_centralizer_of_odd_index (S := S) (L := L) hSL hnorm hS2 (hoddIdx u hu)
  have hmem : s ∈ Subgroup.centralizer ({u} : Set G) := hle hs
  exact (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm

end Work.ThreePoints
