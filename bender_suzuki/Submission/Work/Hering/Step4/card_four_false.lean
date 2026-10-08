import Mathlib
import Submission.Work.Hering.InvSubgroup
import Submission.Work.Hering.Step4.card_six_mul_centralizer
import Submission.Work.Hering.Step4.centralizer_card_three
import Submission.Work.Hering.Step4.normalizer_zpowers_card_six
import Submission.Work.GroupTheory.order_six_involutions

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Step 4: `|V| = 4` is impossible

Peterfalvi I §2, Step 4.  For a finite group `G` acting doubly transitively on its involutions,
`V = Inv(G) ∪ {1}` (a subgroup by Step 1) is elementary abelian, and `G/C_G(V)` acts
doubly transitively on `V# = Inv(G)`.  If `|V| = 4` we get `G/C_G(V) ≅ S₃` with `C_G(V)` a
2-group, which is impossible: counting elements of order `3` forces `N_G(⟨z⟩)` to have order
`6`, and then `⟨V, z⟩` would be a subgroup of order `12` of it.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs Work.Hering Work.GroupTheory

namespace Work.Hering.Step4

variable {G : Type*} [Group G] [Finite G] {hDT : DTInv G} {h4 : HasFourGroup G}

/-- `V = Inv(G) ∪ {1}` has cardinality `4`, i.e. `G` has exactly three involutions. -/
theorem natCard_involutions_eq_three (hV : Nat.card ↥(invSubgroup hDT h4) = 4) :
    Nat.card {w : G // orderOf w = 2} = 3 := by
  classical
  haveI : Fintype ↥(invSubgroup hDT h4) := Fintype.ofFinite _
  have hbij : {w : G // orderOf w = 2} ≃ {v : ↥(invSubgroup hDT h4) // v ≠ 1} := by
    refine Equiv.ofBijective
      (fun w : {w : G // orderOf w = 2} =>
        ⟨⟨w.1, (mem_invSubgroup hDT h4).mpr (Or.inl w.2)⟩, fun h => by
          have h1 : (w.1 : G) = 1 := by
            have hh := congrArg (fun t : ↥(invSubgroup hDT h4) => (t : G)) h
            simpa using hh
          have h2 : orderOf w.1 = 1 := by rw [h1]; exact orderOf_one
          rw [w.2] at h2
          exact absurd h2 (by norm_num)⟩) ⟨?_, ?_⟩
    · -- injective
      intro w₁ w₂ h
      have h' : (w₁ : G) = (w₂ : G) :=
        congrArg (fun t : {v : ↥(invSubgroup hDT h4) // v ≠ 1} =>
          ((t.1 : ↥(invSubgroup hDT h4)) : G)) h
      exact Subtype.ext h'
    · -- surjective
      intro v
      have h2 : orderOf (((v.1 : ↥(invSubgroup hDT h4)) : G)) = 2 := by
        rcases (mem_invSubgroup hDT h4).mp v.1.2 with h | h
        · exact h
        · exact absurd (by simpa using Subtype.coe_injective h : v.1 = 1) v.2
      exact ⟨⟨(v.1 : G), h2⟩, Subtype.ext (Subtype.ext rfl)⟩
  rw [Nat.card_congr hbij, Nat.card_eq_fintype_card]
  simp only [ne_eq]
  rw [Fintype.card_subtype_compl (fun v : ↥(invSubgroup hDT h4) => v = 1),
    Fintype.card_subtype_eq (1 : ↥(invSubgroup hDT h4)), ← Nat.card_eq_fintype_card, hV]

/-- For an element `z` of order `3`, `V ⊓ ⟨z⟩ = 1`: every element of `V` is `1` or an involution. -/
theorem inf_zpowers_eq_bot_of_orderOf_eq_three {z : G} (hz : orderOf z = 3) :
    invSubgroup hDT h4 ⊓ Subgroup.zpowers z = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxV, hxz⟩ := hx
  rcases (mem_invSubgroup hDT h4).mp hxV with h | h
  · exfalso
    have h3 : orderOf x ∣ 3 := by
      rw [← hz]
      exact orderOf_dvd_of_mem_zpowers hxz
    rw [h] at h3
    obtain ⟨m, hm⟩ := h3
    omega
  · exact h

/-- The centralizer of `z` normalizes `⟨z⟩`. -/
theorem centralizer_le_normalizer_zpowers (z : G) :
    Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hy
  have hyz : y * z * y⁻¹ = z := by
    calc y * z * y⁻¹ = (y * z) * y⁻¹ := by group
      _ = (z * y) * y⁻¹ := by rw [hy]
      _ = z := by group
  have hyz' : y⁻¹ * z * y = z := by
    calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
      _ = y⁻¹ * (y * z) := by rw [← hy]
      _ = z := by group
  have hconj : ∀ k : ℤ, y * z ^ k * y⁻¹ = z ^ k := by
    intro k
    have hMz : (MulAut.conj y) z = z := by
      rw [MulAut.conj_apply]
      exact hyz
    calc y * z ^ k * y⁻¹ = (MulAut.conj y) (z ^ k) := by rw [MulAut.conj_apply]
      _ = ((MulAut.conj y) z) ^ k := by rw [map_zpow]
      _ = z ^ k := by rw [hMz]
  have hconj' : ∀ k : ℤ, y⁻¹ * z ^ k * y = z ^ k := by
    intro k
    have hMz : (MulAut.conj y⁻¹) z = z := by
      rw [MulAut.conj_apply]
      simpa [inv_inv] using hyz'
    calc y⁻¹ * z ^ k * y = (MulAut.conj y⁻¹) (z ^ k) := by rw [MulAut.conj_apply, inv_inv]
      _ = ((MulAut.conj y⁻¹) z) ^ k := by rw [map_zpow]
      _ = z ^ k := by rw [hMz]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [Subgroup.mem_zpowers_iff] at hh ⊢
    obtain ⟨k, hk⟩ := hh
    exact ⟨k, by rw [← hk, hconj k]⟩
  · intro hh
    rw [Subgroup.mem_zpowers_iff] at hh ⊢
    obtain ⟨k, hk⟩ := hh
    refine ⟨k, ?_⟩
    have h2 : y⁻¹ * (y * h * y⁻¹) * y = y⁻¹ * z ^ k * y := by rw [hk]
    have h3 : y⁻¹ * (y * h * y⁻¹) * y = h := by group
    rw [hconj' k, h3] at h2
    exact h2.symm

/-- **Peterfalvi I §2, Step 4**: `|V| = 4` is impossible. -/
theorem card_four_false {G : Type*} [Group G] [Finite G] {hDT : DTInv G} {h4 : HasFourGroup G}
    (hC : ∀ U : Subgroup G, U ≤ invSubgroup hDT h4 → Nat.card U = 4 →
      IsPGroup 2 ↥(Subgroup.centralizer (U : Set G)))
    (hV : Nat.card ↥(invSubgroup hDT h4) = 4) : False := by
  classical
  -- `|G| = 6 * |C_G(V)|`
  have hcardG :
      Nat.card G =
        6 * Nat.card ↥(Subgroup.centralizer (((invSubgroup hDT h4) : Subgroup G) : Set G)) :=
    card_six_mul_centralizer hV
  haveI : Fintype G := Fintype.ofFinite G
  have h3dvd : 3 ∣ Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, hcardG]
    exact ⟨2 * Nat.card ↥(Subgroup.centralizer (((invSubgroup hDT h4) : Subgroup G) : Set G)),
      by ring⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 3 h3dvd
  -- the normalizer `M = N_G(⟨z⟩)`
  set M : Subgroup G := Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) with hM
  have hMcard : Nat.card ↥M = 6 := by
    rw [hM]
    exact normalizer_zpowers_card_six hC hV hz
  have hcz : Nat.card ↥(Subgroup.centralizer ({z} : Set G)) = 3 :=
    centralizer_card_three hC hV hz
  have hCm : Subgroup.centralizer ({z} : Set G) ≤ M := by
    rw [hM]
    exact centralizer_le_normalizer_zpowers z
  have hzM : z ∈ M := by
    rw [hM]
    exact Subgroup.le_normalizer (Subgroup.mem_zpowers z)
  -- `M` is not abelian
  have hMnc : ∃ x y : ↥M, x * y ≠ y * x := by
    obtain ⟨y, hyM, hyC⟩ : ∃ y : G, y ∈ (M : Set G) ∧
        y ∉ (Subgroup.centralizer ({z} : Set G) : Set G) := by
      by_contra hcon
      push Not at hcon
      have hle : M ≤ Subgroup.centralizer ({z} : Set G) := fun y hy => hcon y hy
      have h1 : Nat.card ↥M ≤ Nat.card ↥(Subgroup.centralizer ({z} : Set G)) :=
        Nat.card_le_card_of_injective
          (fun y : ↥M => (⟨y.1, hle y.2⟩ : ↥(Subgroup.centralizer ({z} : Set G))))
          (by
            intro a b hab
            have h : (a : G) = (b : G) :=
              congrArg (fun t : ↥(Subgroup.centralizer ({z} : Set G)) => (t : G)) hab
            exact Subtype.ext h)
      rw [hMcard, hcz] at h1
      omega
    refine ⟨⟨z, hzM⟩, ⟨y, hyM⟩, ?_⟩
    intro hcon
    refine hyC ?_
    change y ∈ Subgroup.centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : z * y = y * z := congrArg (fun t : ↥M => (t : G)) hcon
    exact h.symm
  -- `M` has exactly three involutions, and all involutions of `G` lie in `M`
  have hMinv : Nat.card {x : ↥M // orderOf x = 2} = 3 :=
    order_six_involutions hMcard hMnc
  have hGinv : Nat.card {w : G // orderOf w = 2} = 3 := natCard_involutions_eq_three hV
  have hall : ∀ w : G, orderOf w = 2 → w ∈ M := by
    intro w hw
    by_contra hwM
    have hle : Nat.card {x : ↥M // orderOf x = 2} ≤
        Nat.card {u : {w : G // orderOf w = 2} // u ≠ ⟨w, hw⟩} := by
      refine Nat.card_le_card_of_injective
        (fun x : {x : ↥M // orderOf x = 2} =>
          ⟨⟨(x.1 : G), by rw [Subgroup.orderOf_coe]; exact x.2⟩, ?_⟩) ?_
      · intro hx
        have h : ((x.1 : ↥M) : G) = w :=
          congrArg (fun t : {w : G // orderOf w = 2} => (t : G)) hx
        exact hwM (h ▸ x.1.2)
      · intro a b hab
        have h : ((a.1 : ↥M) : G) = ((b.1 : ↥M) : G) :=
          congrArg (fun t : {u : {w : G // orderOf w = 2} // u ≠ ⟨w, hw⟩} =>
            ((t.1 : {w : G // orderOf w = 2}) : G)) hab
        exact Subtype.ext (Subtype.ext h)
    have hcard2 : Nat.card {u : {w : G // orderOf w = 2} // u ≠ ⟨w, hw⟩} = 2 := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_subtype_compl (fun u : {w : G // orderOf w = 2} => u = ⟨w, hw⟩),
        Fintype.card_subtype_eq (⟨w, hw⟩ : {w : G // orderOf w = 2}), ← Nat.card_eq_fintype_card,
        hGinv]
    rw [hMinv, hcard2] at hle
    omega
  -- `V ≤ M`
  have hVM : invSubgroup hDT h4 ≤ M := by
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]; exact M.one_mem
    · rcases (mem_invSubgroup hDT h4).mp hv with h | h
      · exact hall v h
      · exact absurd h hv1
  have hzle : Subgroup.zpowers z ≤ M := by
    rw [Subgroup.zpowers_le]
    exact hzM
  have hsup : invSubgroup hDT h4 ⊔ Subgroup.zpowers z ≤ M := sup_le hVM hzle
  -- an injection `V × ⟨z⟩ → M`, contradicting `4 * 3 ≤ 6`
  have hdisj := inf_zpowers_eq_bot_of_orderOf_eq_three (hDT := hDT) (h4 := h4) hz
  have hinj : Function.Injective
      (fun p : ↥(invSubgroup hDT h4) × ↥(Subgroup.zpowers z) =>
        ((p.1 : G) * (p.2 : G))) := by
    intro p q hpq
    have h1 : ((q.1 : G))⁻¹ * (p.1 : G) = (q.2 : G) * ((p.2 : G))⁻¹ := by
      have h2 : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := hpq
      calc ((q.1 : G))⁻¹ * (p.1 : G)
          = ((q.1 : G))⁻¹ * ((p.1 : G) * (p.2 : G)) * ((p.2 : G))⁻¹ := by group
        _ = ((q.1 : G))⁻¹ * ((q.1 : G) * (q.2 : G)) * ((p.2 : G))⁻¹ := by rw [h2]
        _ = (q.2 : G) * ((p.2 : G))⁻¹ := by group
    have hbot : ((q.1 : G))⁻¹ * (p.1 : G) ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact ⟨(invSubgroup hDT h4).mul_mem ((invSubgroup hDT h4).inv_mem q.1.2) p.1.2,
        by
          rw [h1]
          exact (Subgroup.zpowers z).mul_mem q.2.2 ((Subgroup.zpowers z).inv_mem p.2.2)⟩
    rw [Subgroup.mem_bot] at hbot
    have hp1 : (p.1 : G) = (q.1 : G) := by
      calc (p.1 : G) = (q.1 : G) * (((q.1 : G))⁻¹ * (p.1 : G)) := by group
        _ = (q.1 : G) := by rw [hbot]; simp
    have hp2 : (p.2 : G) = (q.2 : G) := by
      have h2 : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := hpq
      calc (p.2 : G) = ((p.1 : G))⁻¹ * ((p.1 : G) * (p.2 : G)) := by group
        _ = ((p.1 : G))⁻¹ * ((q.1 : G) * (q.2 : G)) := by rw [h2]
        _ = (q.2 : G) := by rw [hp1]; group
    exact Prod.ext (Subtype.ext hp1) (Subtype.ext hp2)
  have hmem : ∀ p : ↥(invSubgroup hDT h4) × ↥(Subgroup.zpowers z), ((p.1 : G) * (p.2 : G)) ∈ M :=
    fun p => M.mul_mem (hVM p.1.2) (hzle p.2.2)
  have h12 : (12 : ℕ) ≤ 6 := by
    have hle := Nat.card_le_card_of_injective
      (fun p : ↥(invSubgroup hDT h4) × ↥(Subgroup.zpowers z) =>
        (⟨(p.1 : G) * (p.2 : G), hmem p⟩ : ↥M))
      (by
        intro a b hab
        exact hinj (congrArg Subtype.val hab))
    rw [Nat.card_prod, Nat.card_zpowers z, hz, hV, hMcard] at hle
    exact hle
  omega

end Work.Hering.Step4
