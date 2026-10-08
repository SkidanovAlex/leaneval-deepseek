import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.appV_prod
import Submission.Work.NormalComplement.appV
import Submission.Work.NormalComplement.section3_prop2
import Submission.Work.NormalComplement.appI_one
import Submission.Work.NormalComplement.appI_four
import Submission.Work.Models.Basic
import Submission.Work.ThmF.Bender.DTransInvAux
import Submission.Work.NormalComplement.sec1_lemma3_fixpts
import Submission.Work.NormalComplement.sec1_lemma3_struct_commute
import Submission.Work.NormalComplement.sec1_lemma3_struct_regular
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.L5Base

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- If `g` fixes `X` pointwise under conjugation then `g` normalises `X`. -/
private lemma mem_normalizer_of_fix {G : Type*} [Group G] {X : Subgroup G} {g : G}
    (h : ∀ x ∈ X, g * x * g⁻¹ = x) : g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro y ⟨z, hz, hyz⟩
    rw [← hyz]
    change g * z * g⁻¹ ∈ X
    rw [h z hz]
    exact hz
  · intro x hx
    exact Subgroup.mem_map.mpr ⟨x, hx,
      by simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h x hx⟩

/-- **Peterfalvi I Ch. III §1 Lemma 3** (p.175).  `1 ≠ X ≤ V`, `N_K(X) ≠ 1`, `1 ≠ P ≤ V`
normalising `X` and fixed-point-free on `N_K(X)`.  Then `|P| = p` is prime,
`|C_K(X)| = |Inv N_H(X)| = 2^p - 1`, and `N_V(X) = C_{N_V(X)}(K₁) ⋊ P` (`K₁ = N_K(X)`).

Route in `_design/Sec3.lean`: `Work.NormalComplement.sec1_lemma3_structure`, then App. V with
`d = 2`, `U = N_D(X)`, `T = K₁` (cyclic, irreducible on `Q = Ω₁(S)` because regular on `Q#`),
`P`; for `1 ≠ P₁ ≤ P`, `C_{K₁}(P₁) = 1` so `P₁` fixes exactly one involution of `Q` (orbit count
with the regular action of `K₁`).

Use `Work.NormalComplement.appV_prod` (the product form `C_U(s) = P ⊔ (U ⊓ C_G(Q))`, with the
correction term `U ⊓ C_G(Q) = C_{N_V(X)}(K₁)`; the design's own `Design.AppVProp`), **not**
`Work.NormalComplement.appV` (the faithful version, whose hypothesis `U ⊓ C_G(Q) = ⊥` fails here
because `C_{N_V(X)}(K₁)` may be non-trivial — indeed §4 Lemma 1 (a) needs it non-trivial).  The
last two conjuncts are the semidirect decomposition `N_V(X) = C_{N_V(X)}(K₁) ⋊ P`; both directions
are needed (`A ⊓ P = ⊥` alone does not give `A ⊔ P = N_V(X)`). -/
theorem sec1_lemma3 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hV : Work.NormalComplement.AppVProp) {G : Type} [Group G] [Finite G]
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) {X P : Subgroup G} (hX : X ≠ ⊥) (hXV : X ≤ Submission.Blueprint.centD H t)
    (hNK : ∃ k ∈ Work.NormalComplement.Design.NK H t X, k ≠ 1) (hP : P ≠ ⊥)
    (hPV : P ≤ Submission.Blueprint.centD H t)
    (hPX : P ≤ Subgroup.normalizer (X : Set G))
    (hfpf : Work.NormalComplement.Design.FpfOn P (Work.NormalComplement.Design.NK H t X)) :
    (Nat.card P).Prime ∧ Work.NormalComplement.Design.NK H t X =
        Work.NormalComplement.Design.CK H t X ∧
      (Work.NormalComplement.Design.CK H t X).ncard = 2 ^ Nat.card P - 1 ∧
      (Submission.Blueprint.involutions
        ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G)).ncard =
        2 ^ Nat.card P - 1 ∧
      (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) ⊓
          Subgroup.centralizer (Work.NormalComplement.Design.NK H t X)) ⊓ P = ⊥ ∧
      (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) ⊓
          Subgroup.centralizer (Work.NormalComplement.Design.NK H t X)) ⊔ P =
        Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) := by
  classical
  -- ## 0. the structural input of §1 Lemma 3 (Ch. II §4 Prop. 3 + `ModelFactsProp`)
  have hStruct : ∃ Q K₁ : Subgroup G,
      (Q : Set G) = insert 1 (Submission.Blueprint.involutions
        ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G)) ∧
      (K₁ : Set G) = Work.NormalComplement.Design.NK H t X ∧
      Work.NormalComplement.Design.NK H t X = Work.NormalComplement.Design.CK H t X ∧
      IsCyclic ↥K₁ ∧
      (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧
      H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (Q : Set G) ∧
      (∀ u ∈ Q, u ≠ 1 → ∀ v ∈ Q, v ≠ 1 → ∃! k : G, k ∈ K₁ ∧ k * u * k⁻¹ = v) ∧
      Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) ⊓
          Subgroup.centralizer (K₁ : Set G) =
        Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) ⊓
          Subgroup.centralizer (Q : Set G) ∧
      Q ≠ ⊥ := by
      classical
      -- ## 0. Abbreviations
      let N : Subgroup G := Subgroup.normalizer (X : Set G)
      let H' : Subgroup G := H ⊓ N
      -- ## 1. The involutions of `H' = N_H(X)` commute pairwise (Ch. II §4 P1(b) + P3(b),(c))
      have hcomm : ∀ a ∈ Submission.Blueprint.involutions (H' : Set G),
          ∀ b ∈ Submission.Blueprint.involutions (H' : Set G), a * b = b * a :=
        sec1_lemma3_struct_commute hC4 hMod hS hH ht htH hX hXV hNK
      -- ## 2. `Q = ⟨Inv H'⟩` is an elementary abelian 2-subgroup of `G`
      obtain ⟨hQ0sq, hQ0comm, hQ0norm, hQ0inv⟩ := Work.ThmF.ChV12.Q0sub_elementary H' hcomm
      have hQ0set : (Work.ThmF.Q0sub H' : Set G) =
          Submission.Blueprint.involutions (H' : Set G) ∪ {1} :=
        Work.ThmF.L5.Q0sub_eq_Q0 (H := H') hcomm
      have hcarrier : (Work.ThmF.Q0sub H' : Set G) =
          insert 1 (Submission.Blueprint.involutions (H' : Set G)) := by
        rw [hQ0set, Set.insert_eq, Set.union_comm]
      -- ## 3. `K₁ = N_K(X) = C_K(X)` is cyclic (Ch. II §4 P3(d)) and acts regularly on `Q#`
      obtain ⟨K₁, hK1set, hK1CK, hK1cyc, hK1reg⟩ :=
        sec1_lemma3_struct_regular hC4 hS hH ht htH hX hXV hNK
      -- ## 4. Membership in `Q`
      have hmemQ : ∀ x : G, x ∈ Work.ThmF.Q0sub H' → x ≠ 1 →
          x ∈ Submission.Blueprint.involutions (H' : Set G) := hQ0inv
      have hQmem : ∀ x : G, x ∈ Submission.Blueprint.involutions (H' : Set G) →
          x ∈ Work.ThmF.Q0sub H' := fun x hx =>
        Subgroup.subset_closure (show x ∈ Work.ThmF.Q0 H' from Or.inl hx)
      -- ## 5. The regular action of `K₁` on `Q#`
      have hregQ : ∀ a ∈ Work.ThmF.Q0sub H', a ≠ 1 → ∀ b ∈ Work.ThmF.Q0sub H', b ≠ 1 →
          ∃! k : G, k ∈ K₁ ∧ k * a * k⁻¹ = b := by
        intro a ha ha1 b hb hb1
        exact hK1reg a (hmemQ a ha ha1) b (hmemQ b hb hb1)
      have hfree : ∀ k ∈ K₁, ∀ x ∈ Work.ThmF.Q0sub H', x ≠ 1 → k * x * k⁻¹ = x → k = 1 := by
        intro k hk x hx hx1 hkx
        have hxInv := hmemQ x hx hx1
        exact (hK1reg x hxInv x hxInv).unique ⟨hk, hkx⟩
          ⟨K₁.one_mem, by rw [one_mul, inv_one, mul_one]⟩
      -- ## 6. The involution `u ∈ Inv(H)` centralising `V` (Ch. II §4 P2(a))
      obtain ⟨u, huInv, hcent⟩ := (hC4 G hS H hH t ht htH).2.1
      have hVcomm : ∀ v ∈ Submission.Blueprint.centD H t, v * u = u * v := by
        intro v hv
        have hv2 : v ∈ Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) :=
          hcent ▸ hv
        exact Subgroup.mem_centralizer_singleton_iff.mp hv2.2
      have huC : u ∈ Subgroup.centralizer (X : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact hVcomm x (hXV hx)
      have huN : u ∈ N := Subgroup.centralizer_le_normalizer (X : Set G) huC
      have huH' : u ∈ H' := ⟨huInv.1, huN⟩
      have hu2 : orderOf u = 2 := huInv.2
      have hu_ne1 : u ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hu2
        exact absurd hu2 (by norm_num)
      have huInv' : u ∈ Submission.Blueprint.involutions (H' : Set G) := ⟨huH', hu2⟩
      have huQ : u ∈ Work.ThmF.Q0sub H' := hQmem u huInv'
      have hQne : Work.ThmF.Q0sub H' ≠ ⊥ := by
        intro hbot
        have hle : Work.ThmF.Q0sub H' ≤ (⊥ : Subgroup G) := le_of_eq hbot
        exact hu_ne1 (Subgroup.mem_bot.mp (hle huQ))
      -- ## 7. `k ∈ K₁` lies in `H'`, and `k * u * k⁻¹` is an involution of `H'`
      have hK1H' : ∀ k ∈ K₁, k ∈ H' := by
        intro k hk
        have hkNK : k ∈ Work.NormalComplement.Design.NK H t X := (le_of_eq hK1set) hk
        have hkD : k ∈ Submission.Blueprint.twoPoint H t :=
          (show k ∈ Submission.Blueprint.twoPoint H t ∧ t * k * t⁻¹ = k⁻¹ from hkNK.1).1
        exact ⟨(Subgroup.mem_inf.mp hkD).1, hkNK.2⟩
      have hkuInv : ∀ k ∈ K₁, k * u * k⁻¹ ∈ Submission.Blueprint.involutions (H' : Set G) := by
        intro k hk
        refine ⟨?_, ?_⟩
        · exact H'.mul_mem (H'.mul_mem (hK1H' k hk) huH') (H'.inv_mem (hK1H' k hk))
        · rw [Work.ThmF.Bender.orderOf_conj_eq, hu2]
      -- ## 8. Conjugation by elements of `V ∩ N_G(X)` preserves `K₁`
      have hVK1 : ∀ y ∈ Submission.Blueprint.centD H t, y ∈ N → ∀ k ∈ K₁, y * k * y⁻¹ ∈ K₁ := by
        intro y hyV _hyN k hk
        have hyD : y ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hyV).1
        have hyt : t * y * t⁻¹ = y := by
          have h : y * t = t * y :=
            Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hyV).2
          calc t * y * t⁻¹ = (t * y) * t⁻¹ := by rw [mul_assoc]
            _ = (y * t) * t⁻¹ := by rw [h.symm]
            _ = y := by group
        have hkNK : k ∈ Work.NormalComplement.Design.NK H t X := (le_of_eq hK1set) hk
        have hkD : k ∈ Submission.Blueprint.twoPoint H t :=
          (show k ∈ Submission.Blueprint.twoPoint H t ∧ t * k * t⁻¹ = k⁻¹ from hkNK.1).1
        have hkt : t * k * t⁻¹ = k⁻¹ :=
          (show k ∈ Submission.Blueprint.twoPoint H t ∧ t * k * t⁻¹ = k⁻¹ from hkNK.1).2
        have hkN : k ∈ N := hkNK.2
        have hmem : y * k * y⁻¹ ∈ Work.NormalComplement.Design.NK H t X := by
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · exact (Submission.Blueprint.twoPoint H t).mul_mem
              ((Submission.Blueprint.twoPoint H t).mul_mem hyD hkD)
              ((Submission.Blueprint.twoPoint H t).inv_mem hyD)
          · calc t * (y * k * y⁻¹) * t⁻¹
                = (t * y * t⁻¹) * (t * k * t⁻¹) * (t * y * t⁻¹)⁻¹ := by group
              _ = y * k⁻¹ * y⁻¹ := by rw [hyt, hkt]
              _ = (y * k * y⁻¹)⁻¹ := by group
          · exact N.mul_mem (N.mul_mem _hyN hkN) (N.inv_mem _hyN)
        exact (le_of_eq hK1set.symm) hmem
      -- ## 9. `N_V(X) ∩ C(K₁) ⊆ N_V(X) ∩ C(Q)`
      have hdirA : ∀ y ∈ Submission.Blueprint.centD H t ⊓ N,
          y ∈ Subgroup.centralizer (K₁ : Set G) →
          y ∈ Subgroup.centralizer ((Work.ThmF.Q0sub H') : Set G) := by
        intro y hy hyK
        have hyV : y ∈ Submission.Blueprint.centD H t := (Subgroup.mem_inf.mp hy).1
        rw [Subgroup.mem_centralizer_iff] at hyK ⊢
        intro x hx
        by_cases hx1 : x = 1
        · subst hx1
          rw [one_mul, mul_one]
        · obtain ⟨k, hkK, hku⟩ := (hregQ u huQ hu_ne1 x hx hx1).exists
          have hyk : y * k * y⁻¹ = k := by
            have h1 : k * y = y * k := hyK k hkK
            calc y * k * y⁻¹ = (y * k) * y⁻¹ := by rw [mul_assoc]
              _ = (k * y) * y⁻¹ := by rw [h1]
              _ = k := by group
          have hyu : y * u * y⁻¹ = u := by
            have h1 : y * u = u * y := hVcomm y hyV
            calc y * u * y⁻¹ = (y * u) * y⁻¹ := by rw [mul_assoc]
              _ = (u * y) * y⁻¹ := by rw [h1]
              _ = u := by group
          have hconj : y * x * y⁻¹ = x := by
            rw [← hku]
            calc y * (k * u * k⁻¹) * y⁻¹
                = (y * k * y⁻¹) * (y * u * y⁻¹) * (y * k * y⁻¹)⁻¹ := by group
              _ = k * u * k⁻¹ := by rw [hyk, hyu]
          calc x * y = (y * x * y⁻¹) * y := by rw [hconj]
            _ = y * x := by group
      -- ## 10. `N_V(X) ∩ C(Q) ⊆ N_V(X) ∩ C(K₁)`
      have hdirB : ∀ y ∈ Submission.Blueprint.centD H t ⊓ N,
          y ∈ Subgroup.centralizer ((Work.ThmF.Q0sub H') : Set G) →
          y ∈ Subgroup.centralizer (K₁ : Set G) := by
        intro y hy hyQ
        have hyV : y ∈ Submission.Blueprint.centD H t := (Subgroup.mem_inf.mp hy).1
        have hyN : y ∈ N := (Subgroup.mem_inf.mp hy).2
        rw [Subgroup.mem_centralizer_iff] at hyQ ⊢
        intro k hk
        have hku2 : orderOf (k * u * k⁻¹) = 2 := by
          rw [Work.ThmF.Bender.orderOf_conj_eq, hu2]
        have hkuQ : k * u * k⁻¹ ∈ Work.ThmF.Q0sub H' := hQmem _ (hkuInv k hk)
        have hku_ne1 : k * u * k⁻¹ ≠ 1 := by
          intro h1
          rw [h1, orderOf_one] at hku2
          exact absurd hku2 (by norm_num)
        have hyu_inv : y⁻¹ * u * y = u := by
          have h1 : y * u = u * y := hVcomm y hyV
          calc y⁻¹ * u * y = y⁻¹ * (u * y) := by rw [mul_assoc]
            _ = y⁻¹ * (y * u) := by rw [← h1]
            _ = u := by group
        have hyx : y * (k * u * k⁻¹) * y⁻¹ = k * u * k⁻¹ := by
          have h1 : (k * u * k⁻¹) * y = y * (k * u * k⁻¹) := hyQ (k * u * k⁻¹) hkuQ
          calc y * (k * u * k⁻¹) * y⁻¹ = ((k * u * k⁻¹) * y) * y⁻¹ := by rw [h1]
            _ = k * u * k⁻¹ := by group
        have hψK : y * k * y⁻¹ ∈ K₁ := hVK1 y hyV hyN k hk
        have heK : (y * k * y⁻¹) * k⁻¹ ∈ K₁ := K₁.mul_mem hψK (K₁.inv_mem hk)
        have hefix : ((y * k * y⁻¹) * k⁻¹) * (k * u * k⁻¹) * ((y * k * y⁻¹) * k⁻¹)⁻¹
            = k * u * k⁻¹ := by
          calc ((y * k * y⁻¹) * k⁻¹) * (k * u * k⁻¹) * ((y * k * y⁻¹) * k⁻¹)⁻¹
              = (y * k * y⁻¹) * u * (y * k * y⁻¹)⁻¹ := by group
            _ = y * (k * (y⁻¹ * u * y) * k⁻¹) * y⁻¹ := by group
            _ = y * (k * u * k⁻¹) * y⁻¹ := by rw [hyu_inv]
            _ = k * u * k⁻¹ := hyx
        have he1 : (y * k * y⁻¹) * k⁻¹ = 1 :=
          hfree _ heK _ hkuQ hku_ne1 hefix
        have hyk : y * k * y⁻¹ = k := by
          calc y * k * y⁻¹ = ((y * k * y⁻¹) * k⁻¹) * k := by group
            _ = 1 * k := by rw [he1]
            _ = k := one_mul k
        calc k * y = (y * k * y⁻¹) * y := by rw [hyk]
          _ = y * k := by group
      -- ## 11. The centralizer identity
      have hcent_eq : Submission.Blueprint.centD H t ⊓ N ⊓ Subgroup.centralizer (K₁ : Set G) =
          Submission.Blueprint.centD H t ⊓ N ⊓
            Subgroup.centralizer ((Work.ThmF.Q0sub H') : Set G) := by
        refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
        · exact ⟨(Subgroup.mem_inf.mp hy).1, hdirA y (Subgroup.mem_inf.mp hy).1 (Subgroup.mem_inf.mp hy).2⟩
        · exact ⟨(Subgroup.mem_inf.mp hy).1, hdirB y (Subgroup.mem_inf.mp hy).1 (Subgroup.mem_inf.mp hy).2⟩
      -- ## 12. `H'` normalises `Q`
      have hnorm : H ⊓ N ≤ Subgroup.normalizer ((Work.ThmF.Q0sub H') : Set G) := by
        rw [Subgroup.le_normalizer_iff]
        intro h hh x hx
        exact hQ0norm h hh x hx
      exact ⟨Work.ThmF.Q0sub H', K₁, hcarrier, hK1set, hK1CK, hK1cyc, hQ0comm, hnorm, hregQ,
        hcent_eq, hQne⟩
  obtain ⟨Q, K₁, hQcar, hK1car, hNKeqCK, hK1cyc, hQcomm, hNQ, hreg, hCV, hQne⟩ := hStruct
  have hK1le : (K₁ : Set G) ⊆ Work.NormalComplement.Design.NK H t X := le_of_eq hK1car
  have hNKle : Work.NormalComplement.Design.NK H t X ⊆ (K₁ : Set G) := le_of_eq hK1car.symm
  -- ## 1. the symmetry `u` of Ch. II §4 Prop. 2 (a)
  obtain ⟨u, huInv, huV⟩ := (hC4 (G := G) hS H hH t ht htH).2.1
  have huH : u ∈ H := huInv.1
  have hu2 : orderOf u = 2 := huInv.2
  have hu1 : u ≠ 1 := by
    intro h; rw [h, orderOf_one] at hu2; exact absurd hu2 (by norm_num)
  have huC : ∀ x ∈ X, u * x * u⁻¹ = x := by
    intro x hx
    have hxV : x ∈ Submission.Blueprint.centD H t := hXV hx
    rw [huV] at hxV
    have hxu : u * x = x * u :=
      (Subgroup.mem_centralizer_iff.mp hxV.2) u (Set.mem_singleton u)
    rw [hxu]; group
  have huNX : u ∈ Subgroup.normalizer (X : Set G) := mem_normalizer_of_fix huC
  have huQ : u ∈ Q := by
    have h : u ∈ (Q : Set G) := by rw [hQcar]; exact Or.inr ⟨⟨huH, huNX⟩, hu2⟩
    exact h
  -- ## 2. the two normalisers `U = N_D(X)`, `V₁ = N_V(X)`
  set U : Subgroup G :=
    Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G) with hUdef
  set V₁ : Subgroup G :=
    Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) with hV1def
  have hP_le_V1 : P ≤ V₁ := by
    intro p hp
    rw [hV1def]
    exact Subgroup.mem_inf.mpr ⟨hPV hp, hPX hp⟩
  have hP_le_U : P ≤ U := by
    intro p hp
    rw [hUdef]
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (hPV hp)).1, hPX hp⟩
  have hPu : P ≤ Subgroup.centralizer ({u} : Set G) := by
    intro p hp
    have h := hPV hp
    rw [huV] at h
    exact h.2
  have huQP : u ∈ Q ⊓ Subgroup.centralizer (P : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨huQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.mp (hPu hp) u (Set.mem_singleton u)).symm
  -- ## 3. `K₁ ≤ U` and `U ≤ N(Q)`
  have hK1leU : K₁ ≤ U := by
    intro k hk
    have hkNK : k ∈ Work.NormalComplement.Design.NK H t X := hK1le hk
    have hkD : k ∈ Submission.Blueprint.twoPoint H t :=
      (Work.Models.mem_invertedBy_iff.mp hkNK.1).1
    rw [hUdef]
    exact Subgroup.mem_inf.mpr ⟨hkD, hkNK.2⟩
  have hU_le_NQ : U ≤ Subgroup.normalizer (Q : Set G) := by
    intro z hz
    rw [hUdef] at hz
    exact hNQ ⟨(Subgroup.mem_inf.mp hz).1.1, (Subgroup.mem_inf.mp hz).2⟩
  -- ## 4. `V₁ ≤ N(K₁)` (App. I (4): `V = C_D(t)` normalises `K = J(D,t)`)
  have hV1_norm : ∀ v ∈ V₁, ∀ k ∈ K₁, v * k * v⁻¹ ∈ K₁ := by
    intro v hv k hk
    have hv' : v ∈ Submission.Blueprint.centD H t ∧ v ∈ Subgroup.normalizer (X : Set G) := by
      rw [hV1def] at hv; exact Subgroup.mem_inf.mp hv
    have hvt : t * v = v * t :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv'.1).2) t (Set.mem_singleton t)
    have hvt' : t * v * t⁻¹ = v := by rw [hvt]; group
    have hkNK : k ∈ Work.NormalComplement.Design.NK H t X := hK1le hk
    obtain ⟨hkD, hkinv⟩ := Work.Models.mem_invertedBy_iff.mp hkNK.1
    have hvD : v ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hv'.1).1
    have h1 : v * k * v⁻¹ ∈ Submission.Blueprint.twoPoint H t :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hvD hkD) (Subgroup.inv_mem _ hvD)
    have h2 : t * (v * k * v⁻¹) * t⁻¹ = (v * k * v⁻¹)⁻¹ := by
      have hvinv : t * v⁻¹ * t⁻¹ = v⁻¹ :=
        (by group : t * v⁻¹ * t⁻¹ = (t * v * t⁻¹)⁻¹).trans (congrArg Inv.inv hvt')
      calc t * (v * k * v⁻¹) * t⁻¹
          = (t * v * t⁻¹) * (t * k * t⁻¹) * (t * v⁻¹ * t⁻¹) := by group
        _ = v * k⁻¹ * v⁻¹ := by rw [hvt', hkinv, hvinv]
        _ = (v * k * v⁻¹)⁻¹ := by group
    have h3 : v * k * v⁻¹ ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t :=
      ⟨h1, h2⟩
    have h4 : v * k * v⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hv'.2 hkNK.2) (Subgroup.inv_mem _ hv'.2)
    exact hNKle ⟨h3, h4⟩
  have hV1_le_NK1 : V₁ ≤ Subgroup.normalizer (K₁ : Set G) :=
    Subgroup.le_normalizer_iff.mpr hV1_norm
  -- ## 5. `U ≤ N(K₁)` (App. I (1): `N_D(X) = N_K(X)·N_V(X)`)
  have hDodd : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) :=
    Work.Models.IsStronglyEmbedded.odd_twoPoint hH htH
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t; rw [ht] at h; simpa [pow_two] using h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htCent : ∀ x ∈ X, t * x * t⁻¹ = x := by
    intro x hx
    have hxV : x ∈ Submission.Blueprint.centD H t := hXV hx
    have hxt : t * x = x * t :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxV).2) t (Set.mem_singleton t)
    rw [hxt]; group
  have htNX : t ∈ Subgroup.normalizer (X : Set G) := mem_normalizer_of_fix htCent
  have hnormU : Work.NormalComplement.NormalizedBy t U := by
    intro x hx
    rw [hUdef] at hx ⊢
    obtain ⟨hxD, hxN⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxH, hxc⟩ := Subgroup.mem_inf.mp hxD
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · have hxt : t * x * t⁻¹ = t⁻¹ * x * t := by rw [hti]
      rw [hxt]
      exact Work.Models.mem_conj_iff.mp hxc
    · rw [Work.Models.mem_conj_iff]
      have h1 : t⁻¹ * (t * x * t⁻¹) * t = x := by group
      rw [h1]; exact hxH
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htNX hxN) (Subgroup.inv_mem _ htNX)
  have hcopU : Nat.Coprime (Nat.card U) 2 := by
    have hle : U ≤ Submission.Blueprint.twoPoint H t := by rw [hUdef]; exact inf_le_left
    exact Nat.coprime_two_right.mpr (Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hle))
  have hU_le_NK1 : U ≤ Subgroup.normalizer (K₁ : Set G) := by
    intro z hz
    obtain ⟨hKappEq, hdec⟩ := (appI_one (d := 2) Nat.prime_two ht hnormU hcopU).2 rfl
    obtain ⟨⟨c, k⟩, ⟨hcC, hcU, hkKapp, hck⟩, -⟩ := hdec z hz
    have hcV1 : c ∈ V₁ := by
      rw [hV1def]
      rw [hUdef] at hcU
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hcU).1, hcC⟩,
        (Subgroup.mem_inf.mp hcU).2⟩
    have hkK1 : k ∈ K₁ := by
      have hkKset : k ∈ Work.NormalComplement.Kset U t := by rw [← hKappEq]; exact hkKapp
      obtain ⟨hkU, hkinv⟩ := Work.Models.mem_invertedBy_iff.mp hkKset
      rw [hUdef] at hkU
      exact hNKle ⟨⟨(Subgroup.mem_inf.mp hkU).1, hkinv⟩, (Subgroup.mem_inf.mp hkU).2⟩
    rw [← hck]
    exact Subgroup.mul_mem _ (hV1_le_NK1 hcV1) (Subgroup.le_normalizer hkK1)
  -- ## 6. `P ⊓ C(Q) = ⊥`
  have hPf : P ⊓ Subgroup.centralizer (Q : Set G) = ⊥ := by
    have hA : V₁ ⊓ Subgroup.centralizer (K₁ : Set G) = V₁ ⊓ Subgroup.centralizer (Q : Set G) := by
      rw [hV1def]; exact hCV
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxP, hxQ⟩ := Subgroup.mem_inf.mp hx
    have hxCK : x ∈ Subgroup.centralizer (K₁ : Set G) := by
      have h2 : x ∈ V₁ ⊓ Subgroup.centralizer (Q : Set G) :=
        Subgroup.mem_inf.mpr ⟨hP_le_V1 hxP, hxQ⟩
      rw [← hA] at h2
      exact (Subgroup.mem_inf.mp h2).2
    obtain ⟨k, hkNK, hk1⟩ := hNK
    have hkK1 : k ∈ K₁ := hNKle hkNK
    have hcomm : x * k * x⁻¹ = k := by
      have hxk : k * x = x * k := (Subgroup.mem_centralizer_iff.mp hxCK) k hkK1
      rw [← hxk]; group
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hk1 (hfpf x hxP hx1 k hkNK hcomm)
  -- ## 7. `|C_Q(P₁)| = 2` for `1 ≠ P₁ ≤ P`
  have hfix : ∀ P₁ : Subgroup G, P₁ ≤ P → P₁ ≠ ⊥ →
      Nat.card ↥(Q ⊓ Subgroup.centralizer (P₁ : Set G)) = 2 :=
    sec1_lemma3_fixpts (H := H) (X := X) (P := P) (Q := Q) (K₁ := K₁) (t := t) (u := u)
      hK1car hQcar hreg hV1_le_NK1 huQ hu1 hP_le_V1 hPu hfpf
  -- ## 8. `K₁` is irreducible on `Q` (it acts regularly on `Q#`)
  have hQexp : ∀ x ∈ Q, x ^ 2 = 1 := by
    intro x hx
    have hx' : x ∈ (Q : Set G) := hx
    rw [hQcar] at hx'
    rcases hx' with hx1 | hxI
    · rw [hx1]; simp
    · have hx2 : orderOf x = 2 := (Work.Models.mem_involutions_iff.mp hxI).2
      rw [← hx2]; exact pow_orderOf_eq_one x
  have hirr : ∀ R : Subgroup G, R ≤ Q → K₁ ≤ Subgroup.normalizer (R : Set G) →
      R = ⊥ ∨ R = Q := by
    intro R hRQ hKR
    by_cases hR : R = ⊥
    · exact Or.inl hR
    · right
      obtain ⟨x, hxR, hx1⟩ : ∃ x ∈ R, x ≠ 1 := by
        by_contra h
        apply hR
        rw [eq_bot_iff]
        intro y hy
        by_contra hy1
        exact h ⟨y, hy, hy1⟩
      have hxQ : x ∈ Q := hRQ hxR
      have hsubset : ∀ b ∈ Q, b ≠ 1 → b ∈ R := by
        intro b hbQ hb1
        obtain ⟨k, hkK1, hkb⟩ := (hreg x hxQ hx1 b hbQ hb1).exists
        have hk := Subgroup.le_normalizer_iff.mp hKR k hkK1 x hxR
        rwa [hkb] at hk
      refine le_antisymm hRQ ?_
      intro b hbQ
      by_cases hb1 : b = 1
      · rw [hb1]; exact R.one_mem
      · exact hsubset b hbQ hb1
  -- ## 9. App. V (d), product form
  obtain ⟨hprime, hcardQ, hcent⟩ :=
    appV_prod (G := G) 2 U Q K₁ P Nat.prime_two hQcomm hQexp hQne hU_le_NQ hK1leU
      hU_le_NK1 hK1cyc hirr hP_le_U hP hPf hfix
  have hUc : U ⊓ Subgroup.centralizer ({u} : Set G) = V₁ := by
    rw [hUdef, hV1def, huV]
    ext x
    simp only [Subgroup.mem_inf, Set.mem_singleton_iff]
    tauto
  have hUcQ : U ⊓ Subgroup.centralizer (Q : Set G) = V₁ ⊓ Subgroup.centralizer (Q : Set G) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxU, hxQ⟩ := Subgroup.mem_inf.mp hx
      have hxCu : x ∈ Subgroup.centralizer ({u} : Set G) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huQ) hxQ
      rw [hUdef] at hxU
      obtain ⟨hxD, hxN⟩ := Subgroup.mem_inf.mp hxU
      refine Subgroup.mem_inf.mpr ⟨?_, hxQ⟩
      rw [hV1def]
      exact Subgroup.mem_inf.mpr ⟨by rw [huV]; exact ⟨hxD, hxCu⟩, hxN⟩
    · intro x hx
      obtain ⟨hxV1, hxQ⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, hxQ⟩
      rw [hV1def] at hxV1
      rw [hUdef]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hxV1).1.1, (Subgroup.mem_inf.mp hxV1).2⟩
  have hV1eq : V₁ = P ⊔ (V₁ ⊓ Subgroup.centralizer (Q : Set G)) :=
    calc V₁ = U ⊓ Subgroup.centralizer ({u} : Set G) := hUc.symm
      _ = P ⊔ (U ⊓ Subgroup.centralizer (Q : Set G)) := hcent u huQP hu1
      _ = P ⊔ (V₁ ⊓ Subgroup.centralizer (Q : Set G)) := by rw [hUcQ]
  -- ## 10. arithmetic for the two cardinality conjuncts
  set S : Set G := Submission.Blueprint.involutions
    ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) with hSdef
  have hQcar' : (Q : Set G) = insert 1 S := by rw [hQcar, hSdef]
  have hconj_mem_S : ∀ a ∈ K₁, a * u * a⁻¹ ∈ S := by
    intro a ha
    have haU : a ∈ U := hK1leU ha
    rw [hUdef] at haU
    obtain ⟨haD, haN⟩ := Subgroup.mem_inf.mp haU
    have haH : a ∈ H := (Subgroup.mem_inf.mp haD).1
    rw [hSdef]
    exact ⟨⟨H.mul_mem (H.mul_mem haH huH) (H.inv_mem haH),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ haN huNX) (Subgroup.inv_mem _ haN)⟩,
      by rw [Work.ThmF.Bender.orderOf_conj_eq, hu2]⟩
  have hconj_ne_one : ∀ a ∈ K₁, a * u * a⁻¹ ≠ 1 := by
    intro a ha h
    have hu_eq : u = 1 := by
      calc u = a⁻¹ * (a * u * a⁻¹) * a := by group
        _ = a⁻¹ * 1 * a := by rw [h]
        _ = 1 := by group
    exact hu1 hu_eq
  have hmemQ : ∀ a ∈ K₁, a * u * a⁻¹ ∈ Q := by
    intro a ha
    have h : a * u * a⁻¹ ∈ (Q : Set G) := by rw [hQcar']; exact Or.inr (hconj_mem_S a ha)
    exact h
  have hbij : Nat.card ↥K₁ = S.ncard := by
    have hf : ∀ k : ↥K₁, (k : G) * u * (k : G)⁻¹ ∈ S := fun k => hconj_mem_S k k.2
    have hinj : Function.Injective (fun k : ↥K₁ => (⟨(k : G) * u * (k : G)⁻¹, hf k⟩ : ↥S)) := by
      intro k k' h
      have hval : (k : G) * u * (k : G)⁻¹ = (k' : G) * u * (k' : G)⁻¹ := congrArg Subtype.val h
      obtain ⟨y, ⟨hyK, hyv⟩, hyuni⟩ :=
        hreg u huQ hu1 ((k : G) * u * (k : G)⁻¹) (hmemQ k k.2) (hconj_ne_one k k.2)
      exact Subtype.ext ((hyuni k ⟨k.2, rfl⟩).trans (hyuni k' ⟨k'.2, hval.symm⟩).symm)
    have hsurj : Function.Surjective (fun k : ↥K₁ => (⟨(k : G) * u * (k : G)⁻¹, hf k⟩ : ↥S)) := by
      intro b
      have hbQ : (b : G) ∈ (Q : Set G) := by rw [hQcar']; exact Or.inr b.2
      have hb1 : (b : G) ≠ 1 := by
        intro h
        have h2 : orderOf (b : G) = 2 := (Work.Models.mem_involutions_iff.mp b.2).2
        rw [h, orderOf_one] at h2
        exact absurd h2 (by norm_num)
      obtain ⟨y, ⟨hyK, hyv⟩, -⟩ := hreg u huQ hu1 (b : G) hbQ hb1
      exact ⟨⟨y, hyK⟩, Subtype.ext hyv⟩
    exact Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
  have hQncard : Nat.card ↥Q = (Q : Set G).ncard := by
    rw [← Set.ncard_univ (α := ↥Q), Set.ncard_coe]
  have hK1ncard : Nat.card ↥K₁ = 2 ^ Nat.card P - 1 := by
    have h1S : (1 : G) ∉ S := by
      rw [hSdef]; exact Work.Models.one_notMem_involutions _
    have h1 : (Q : Set G).ncard = S.ncard + 1 := by
      rw [hQcar']
      exact Set.ncard_insert_of_notMem h1S
    have h2 : (Q : Set G).ncard = Nat.card ↥K₁ + 1 := by rw [h1, ← hbij]
    omega
  have hS_ncard : S.ncard = 2 ^ Nat.card P - 1 := by rw [← hbij]; exact hK1ncard
  -- ## 11. the final conjuncts
  refine ⟨hprime, hNKeqCK, ?_, ?_, ?_, ?_⟩
  · have hset : (Work.NormalComplement.Design.CK H t X) = (K₁ : Set G) :=
      hNKeqCK.symm.trans hK1car.symm
    rw [hset]
    have hcnt : (K₁ : Set G).ncard = Nat.card ↥K₁ :=
      (Set.ncard_coe (K₁ : Set G)).symm.trans (Set.ncard_univ (α := ↥(K₁ : Set G)))
    rw [hcnt]
    exact hK1ncard
  · exact hS_ncard
  · have hA : V₁ ⊓ Subgroup.centralizer (Work.NormalComplement.Design.NK H t X) =
        V₁ ⊓ Subgroup.centralizer (K₁ : Set G) := by
      rw [show (Work.NormalComplement.Design.NK H t X) = (K₁ : Set G) from hK1car.symm]
    rw [hA]
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxV1CK, hxP⟩ := Subgroup.mem_inf.mp hx
    have hxCK : x ∈ Subgroup.centralizer (K₁ : Set G) := (Subgroup.mem_inf.mp hxV1CK).2
    obtain ⟨k, hkNK, hk1⟩ := hNK
    have hkK1 : k ∈ K₁ := hNKle hkNK
    have hcomm : x * k * x⁻¹ = k := by
      have hxk : k * x = x * k := (Subgroup.mem_centralizer_iff.mp hxCK) k hkK1
      rw [← hxk]; group
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hk1 (hfpf x hxP hx1 k hkNK hcomm)
  · have hA : V₁ ⊓ Subgroup.centralizer (Work.NormalComplement.Design.NK H t X) =
        V₁ ⊓ Subgroup.centralizer (Q : Set G) := by
      rw [hV1def, show (Work.NormalComplement.Design.NK H t X) = (K₁ : Set G) from hK1car.symm]
      exact hCV
    rw [hA]
    calc (V₁ ⊓ Subgroup.centralizer (Q : Set G)) ⊔ P
        = P ⊔ (V₁ ⊓ Subgroup.centralizer (Q : Set G)) := by rw [sup_comm]
      _ = V₁ := hV1eq.symm

end Work.NormalComplement
