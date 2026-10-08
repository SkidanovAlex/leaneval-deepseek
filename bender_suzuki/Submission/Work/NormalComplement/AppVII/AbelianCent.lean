import Mathlib
import Submission.Work.NormalComplement.AppVIIBase
import Submission.Work.Hering.Step5.appVII_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.AppVII

/-- **Peterfalvi Appendix VII, step 2: `P` centralises every proper `P`-invariant subgroup of
`Q`.**

Setting: `A` acts on `K` by group automorphisms, `Q ◁ A`, `P ⊓ Q = ⊥`, `P ⊔ Q = ⊤`, `|P| = p`
prime, `p ∤ |Q|`, `C_K(P) = 1`, `(|K|,|A|) = 1`.  Assume moreover that the action is *faithful*
(`hfaith`).  Then every proper `P`-invariant subgroup `Q' < Q` is centralised by `P`:
`⁅P,Q'⁆ = ⊥`.

Proof route: put `A' := Q' ⊔ P ≤ A`, apply the induction hypothesis `ih` to `↥A'` acting on `K`
(transport of `Q'`,`P` to `↥A'` is via `Subgroup.subgroupOf`; `|A'| = |Q'|·p < |Q|·p = |A|`
since `Q' < Q` and `Q' ⊓ P = ⊥`), obtaining `⁅P,Q'⁆ ≤ ker(A → Aut K)`; faithfulness (`hfaith`)
then gives `⁅P,Q'⁆ = ⊥`. -/
theorem AbelianCent {n : ℕ} (hFT : Submission.Blueprint.FeitThompsonProp)
    (ih : ∀ m < n, AbstractAppVII m)
    {A : Type} [Group A] [Finite A] (P Q : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p : ℕ} (hp : p.Prime)
    (hcardP : Nat.card ↥P = p) (hpQ : ¬ p ∣ Nat.card ↥Q)
    (hodd : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set A))))
    {K : Type} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A))
    (hfix : ∀ k : K, (∀ a ∈ P, a • k = k) → k = 1)
    (hsize : Nat.card A * Nat.card K = n)
    (hfaith : ∀ a : A, (∀ x : K, a • x = x) → a = 1) :
    ∀ Q' : Subgroup A, Q' ≤ Q → Q' ≠ ⊥ → Q' ≠ Q → ⁅P, Q'⁆ ≤ Q' → ⁅P, Q'⁆ = ⊥ := by
  classical
  intro Q' hQ'le _hQ'ne hQ'neQ hcomm
  -- The group `A' = Q' ⊔ P` acting on `K`.
  set A' : Subgroup A := Q' ⊔ P with hA'def
  have hQ'leA' : Q' ≤ A' := by rw [hA'def]; exact le_sup_left
  have hPleA' : P ≤ A' := by rw [hA'def]; exact le_sup_right
  -- `P` normalises `Q'`, since `⁅P, Q'⁆ ≤ Q'`.
  have hPnorm : P ≤ Subgroup.normalizer (Q' : Set A) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left, Subgroup.commutator_comm]
    exact hcomm
  have hA'norm : A' ≤ Subgroup.normalizer (Q' : Set A) := by
    rw [hA'def]
    exact sup_le Subgroup.le_normalizer hPnorm
  -- `A'` is a proper subgroup of `A`: `Q ⊄ Q' ⊔ P`.
  have hA'ne_top : A' ≠ ⊤ := by
    intro htop
    obtain ⟨q, hqQ, hqQ'⟩ : ∃ q ∈ Q, q ∉ Q' := by
      by_contra h
      push_neg at h
      exact hQ'neQ (le_antisymm hQ'le h)
    have hmem : q ∈ (↑A' : Set A) := by rw [htop]; exact Subgroup.mem_top q
    rw [hA'def, Subgroup.coe_mul_of_right_le_normalizer_left Q' P hPnorm] at hmem
    rw [Set.mem_mul] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    -- `hab : a * b = q` with `a ∈ Q'`, `b ∈ P`.
    have hbQ : b ∈ Q := by
      have hba : b = a⁻¹ * q := by rw [← hab]; group
      rw [hba]
      exact Q.mul_mem (Q.inv_mem (hQ'le ha)) hqQ
    have hb_bot : b ∈ (⊥ : Subgroup A) := by
      rw [← hinf]
      exact Subgroup.mem_inf.mpr ⟨hb, hbQ⟩
    rw [Subgroup.mem_bot] at hb_bot
    have hqa : q = a := by rw [← hab, hb_bot, mul_one]
    exact hqQ' (hqa ▸ ha)
  -- hence `|A'| < |A|`.
  have hltA : Nat.card ↥A' < Nat.card A := by
    have h1 : Nat.card ↥A' * A'.index = Nat.card A := Subgroup.card_mul_index A'
    have hne1 : A'.index ≠ 1 := fun h => hA'ne_top (Subgroup.index_eq_one.mp h)
    have hpos : 0 < A'.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hidx : 2 ≤ A'.index := by omega
    have hposc : 0 < Nat.card ↥A' := Nat.card_pos
    have hle : Nat.card ↥A' * 2 ≤ Nat.card A := by
      calc Nat.card ↥A' * 2 ≤ Nat.card ↥A' * A'.index := Nat.mul_le_mul_left _ hidx
        _ = Nat.card A := h1
    omega
  -- The restricted action of `A'` on `K`.
  letI : MulDistribMulAction ↥A' K := restrictAction (K := K) A'
  -- Normality of `Q'` inside `A'`.
  have hQn' : (Q'.subgroupOf A').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ'leA').mpr hA'norm
  -- Trivial intersection and generation inside `A'`.
  have hinf' : P.subgroupOf A' ⊓ Q'.subgroupOf A' = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hx1 : (x : A) ∈ P := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).1
    have hx2 : (x : A) ∈ Q' := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2
    have h3 : (x : A) ∈ (⊥ : Subgroup A) := by
      rw [← hinf]
      exact Subgroup.mem_inf.mpr ⟨hx1, hQ'le hx2⟩
    rw [Subgroup.mem_bot] at h3
    exact Subtype.ext (by simpa using h3)
  have hsup' : P.subgroupOf A' ⊔ Q'.subgroupOf A' = ⊤ := by
    refine Work.Hering.Step5.sup_subgroupOf_of_sup_eq hPleA' hQ'leA' ?_
    rw [sup_comm, ← hA'def]
  -- `|P| = p`.
  have hcardP' : Nat.card ↥(P.subgroupOf A') = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleA').toEquiv]
    exact hcardP
  -- `p ∤ |Q'|`.
  have hpQ' : ¬ p ∣ Nat.card ↥(Q'.subgroupOf A') := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ'leA').toEquiv]
    exact fun h => hpQ (h.trans (Subgroup.card_dvd_of_le hQ'le))
  -- `|C_{Q'}(P)|` is odd.
  have hodd' : Odd (Nat.card ↥(Q'.subgroupOf A' ⊓
      Subgroup.centralizer ((P.subgroupOf A' : Subgroup ↥A') : Set ↥A'))) := by
    rw [Work.Hering.Step5.card_inf_centralizer_subgroupOf (P := P) (Q := Q') (L := A')
      hPleA' hQ'leA']
    exact Odd.of_dvd_nat hodd
      (Subgroup.card_dvd_of_le (inf_le_inf hQ'le le_rfl))
  -- Coprimality survives.
  have hcop' : Nat.Coprime (Nat.card K) (Nat.card ↥A') :=
    hcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card A')
  -- `C_K(P) = 1` survives.
  have hfix' : ∀ k : K, (∀ a ∈ P.subgroupOf A', a • k = k) → k = 1 := by
    intro k hk
    apply hfix
    intro a ha
    have h1 := hk ⟨a, hPleA' ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
    simpa [restrictSmul] using h1
  -- The size decreases.
  have hsize' : Nat.card ↥A' * Nat.card K < n := by
    rw [← hsize]
    exact Nat.mul_lt_mul_of_pos_right hltA Nat.card_pos
  -- Apply the induction hypothesis to `↥A'` acting on `K`.
  have hmain := ih (Nat.card ↥A' * Nat.card K) hsize' hFT ↥A' (P.subgroupOf A')
    (Q'.subgroupOf A') hQn' hinf' hsup' hp hcardP' hpQ' hodd' K hcop' hfix' rfl
  -- Faithfulness kills `⁅P, Q'⁆`.
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  exact hfaith a fun x => by
    have haA' : a ∈ A' := hQ'leA' (hcomm ha)
    have hmem : (⟨a, haA'⟩ : ↥A') ∈ ⁅P.subgroupOf A', Q'.subgroupOf A'⁆ := by
      rw [← Work.Hering.Step5.commutator_subgroupOf_eq hPleA' hQ'leA']
      exact Subgroup.mem_subgroupOf.mpr ha
    have h1 : restrictSmul A' (⟨a, haA'⟩ : ↥A') x = x := hmain x ⟨a, haA'⟩ hmem
    rw [restrictSmul] at h1
    simpa using h1

end Work.NormalComplement.AppVII
