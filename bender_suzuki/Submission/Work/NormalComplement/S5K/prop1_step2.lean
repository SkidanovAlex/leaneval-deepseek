/-
# Peterfalvi I Ch. III §4 Prop. 1, step 2 (p.180)

`Work.NormalComplement.S5K.prop1_step2`: under `Setup45A G H t W p P A`, `P` a `p`-Sylow of
`D = twoPoint H t`, and `h1 : Step1Conc` (step 1 of Prop. 1: `C_A(P) = A ⊓ C_G(P)` is a Hall
subgroup of `N_H(P)` with a normal complement), the subgroup `C_A(P)` must be trivial: if it were
not, `P` would fail to be a `p`-Sylow subgroup of `H`.

Route, exactly as in the source (p.180); all ingredients are in the workspace:

* `C_A(P) ≠ ⊥`: pick a prime `q ∣ |C_A(P)|` and a `q`-Sylow `U ≠ 1` of `C_A(P)`.  By `h1`,
  `C_A(P)` is Hall in `N_H(P) = H ⊓ N_G(P)`, so `U` is a `q`-Sylow of `N_H(P)`
  (`isSylowIn_of_isSylowIn_hall`).
* Formula (∗) `Work.NormalComplement.sec4_prop1_star` gives
  `N_H(U) ⊓ N_H(P) = (S₂ ⊔ P) ⊔ (C_A(P) ⊓ N_H(U)) ≤ C_G(P)`: `S₂` centralises `P` by
  construction, `P` is abelian (it has prime order `p`), and `C_A(P) ≤ C_G(P)`.
* Frattini's argument (`frattini_decomp`) for the normal subgroup `C_H(P) ⊴ N_H(P)` then gives
  `N_H(P) = C_H(P) · (N_H(U) ⊓ N_H(P)) ≤ C_H(P)`, so `N_H(P) = C_H(P)`
  (`normalizer_eq_centralizer`).
* If `P` were a `p`-Sylow of `H`, it would be one of `W` (`P ≤ W ≤ H`), and
  `N_W(P) ≤ N_H(P) = C_H(P) ≤ C_G(P)`; Burnside's normal `p`-complement theorem
  (`Work.NPC.burnside_npc`, via the transfer engine) then produces a normal `p`-complement
  `N' ⊴ W` of `W`, with `N' < W` and `N' ⊔ P = W`, hence `N' ⊔ D = H`.
* `N'` is characteristic in `W` (the normal `p`-complement is the set of `p'`-elements), so
  `H ≤ N_G(N')` (`Work.NormalComplement.isNormalPComplement_map_subtype_normal`) and minimality of
  `W` (`Setup45A.minW`) gives `|W| ≤ |N'| < |W|`: contradiction.
-/
import Mathlib
import Submission.Work.NormalComplement.S5K.Defs
import Submission.Work.NormalComplement.S5K.ca_coprime
import Submission.Work.NormalComplement.sec4_prop1_star
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.appI_two
import Submission.Work.NormalComplement.appI_five_d_corrected
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.NormalComplement.isNormalPComplement_map_subtype_normal
import Submission.Work.NPC.Engine

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open Classical
open scoped Pointwise commutatorElement
open Submission.Blueprint

namespace Work.NormalComplement.S5K

-- Note: `Design.Setup45A` (like the statement of `prop1_step2`) is stated with `G : Type`, so the
-- section variable below must not be universe-polymorphic.
variable {G : Type} [Group G] [Finite G]

/-! ## Elementary index and Sylow bookkeeping -/

/-- `(Q.subgroupOf X).index = Q.relIndex X`, definitionally. -/
lemma subgroupOf_index_eq_relIndex (Q X : Subgroup G) :
    (Q.subgroupOf X).index = Q.relIndex X := rfl

/-- A strictly smaller subgroup has strictly smaller order. -/
lemma card_lt_card_of_lt {H K : Subgroup G} (h : H < K) :
    Nat.card ↥H < Nat.card ↥K := by
  have hdvd : Nat.card ↥H ∣ Nat.card ↥K := by
    rw [← Work.NormalComplement.relIndex_mul_card_of_le' h.1]
    exact dvd_mul_left _ _
  refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) (fun heq => ?_)
  exact (ne_of_lt h) (Subgroup.eq_of_le_of_card_ge h.1 (le_of_eq heq.symm))

/-- If `q ∣ |E|` and `|E|` is coprime to `E.relIndex N`, then `q ∤ E.relIndex N`. -/
lemma not_dvd_relIndex_of_coprime {q : ℕ} {E N : Subgroup G} (hq : q.Prime)
    (hqE : q ∣ Nat.card ↥E) (hcop : Nat.Coprime (Nat.card ↥E) (E.relIndex N)) :
    ¬ q ∣ E.relIndex N := by
  intro hdvd
  have h1 : q ∣ Nat.gcd (Nat.card ↥E) (E.relIndex N) := Nat.dvd_gcd hqE hdvd
  rw [hcop] at h1
  exact hq.ne_one (Nat.dvd_one.mp h1)

/-- **Sylow-ness is inherited from a Hall subgroup**: if `U` is a `q`-Sylow of `E`, `E ≤ N` is a
Hall subgroup of `N` (`|E|` coprime to `E.relIndex N`) and `q ∣ |E|`, then `U` is a `q`-Sylow of
`N`. -/
lemma isSylowIn_of_isSylowIn_hall {q : ℕ} (hq : q.Prime) {U E N : Subgroup G}
    (hU : Work.NormalComplement.IsSylowIn q U E) (hUE : E ≤ N) (hqE : q ∣ Nat.card ↥E)
    (hcop : Nat.Coprime (Nat.card ↥E) (E.relIndex N)) :
    Work.NormalComplement.IsSylowIn q U N := by
  refine ⟨hU.1, hU.2.1.trans hUE, ?_⟩
  rw [subgroupOf_index_eq_relIndex]
  intro hdvd
  have hdvd' : q ∣ U.relIndex E * E.relIndex N := by
    rw [Subgroup.relIndex_mul_relIndex U E N hU.2.1 hUE]
    exact hdvd
  rcases hq.dvd_mul.mp hdvd' with h1 | h1
  · exact hU.2.2 h1
  · exact not_dvd_relIndex_of_coprime hq hqE hcop h1

variable {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}

/-- A subgroup of prime order is cyclic, hence abelian: it is contained in its own centraliser. -/
lemma le_centralizer_self_of_card_prime (hp : p.Prime) (hcard : Nat.card ↥P = p) :
    P ≤ Subgroup.centralizer (P : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic ↥P := isCyclic_of_prime_card hcard
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨y, hy⟩ : ↥P) (⟨x, hx⟩ : ↥P))

/-! ## Step 2, first half: `N_H(P) = C_H(P)` -/

/-- **§4 Prop. 1 step 2, first half**: `N_H(P) = C_H(P)`, given `C_A(P) ≠ ⊥` and that `C_A(P)` is
Hall in `N_H(P)`.  A `q`-Sylow `U ≠ 1` of `C_A(P)` is a `q`-Sylow of `N_H(P)`
(`isSylowIn_of_isSylowIn_hall`); formula (∗) `sec4_prop1_star` gives `N_H(U) ⊓ N_H(P) ≤ C_H(P)`;
Frattini (`frattini_decomp`) gives `N_H(P) = C_H(P)`. -/
lemma normalizer_eq_centralizer (hFT : Submission.Blueprint.FeitThompsonProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (hHall : Nat.Coprime (Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)))
      ((A ⊓ Subgroup.centralizer (P : Set G)).relIndex
        (H ⊓ Subgroup.normalizer (P : Set G))))
    (hCA : (A ⊓ Subgroup.centralizer (P : Set G)) ≠ ⊥) :
    H ⊓ Subgroup.normalizer (P : Set G) = H ⊓ Subgroup.centralizer (P : Set G) := by
  classical
  set E : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G) with hE
  set N : Subgroup G := H ⊓ Subgroup.normalizer (P : Set G) with hN
  set C : Subgroup G := H ⊓ Subgroup.centralizer (P : Set G) with hC
  have hEne : Nat.card ↥E ≠ 1 := fun h1 => hCA (Subgroup.card_eq_one.mp h1)
  obtain ⟨q, hq, hqE⟩ : ∃ q : ℕ, q.Prime ∧ q ∣ Nat.card ↥E := Nat.exists_prime_and_dvd hEne
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨S, -⟩ := IsPGroup.exists_le_sylow (p := q) (P := (⊥ : Subgroup ↥E)) (IsPGroup.of_bot)
  let U : Subgroup G := S.toSubgroup.map E.subtype
  have hUsylE : Work.NormalComplement.IsSylowIn q U E := sylow_toSubgroup_isSylowIn S
  have hUleE : U ≤ E := hUsylE.2.1
  have hqU : q ∣ Nat.card ↥U := by
    have h1 : q ∣ Nat.card ↥(U.subgroupOf E) * (U.subgroupOf E).index := by
      rw [Subgroup.card_mul_index]; exact hqE
    rcases hq.dvd_mul.mp h1 with h2 | h2
    · rwa [show Nat.card ↥(U.subgroupOf E) = Nat.card ↥U from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleE).toEquiv] at h2
    · exact absurd h2 hUsylE.2.2
  have hUne : U ≠ ⊥ := by
    intro hbot
    have h2 : 2 ≤ Nat.card ↥U := le_trans hq.two_le (Nat.le_of_dvd Nat.card_pos hqU)
    rw [hbot, Subgroup.card_bot] at h2
    omega
  have hEH : E ≤ H := inf_le_left.trans (h.A_le.trans (inf_le_left.trans inf_le_left))
  have hENP : E ≤ Subgroup.normalizer (P : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer (P : Set G))
  have hEN : E ≤ N := le_inf hEH hENP
  have hCN : C ≤ N := le_inf inf_le_left
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer (P : Set G)))
  have hUA : U ≤ A ⊓ Subgroup.centralizer (P : Set G) := hUleE
  obtain ⟨S₂, -, -, hS₂cent, hEq⟩ := sec4_prop1_star hFT hP3 h U hUne hUA
  have hPleCP : P ≤ Subgroup.centralizer (P : Set G) :=
    le_centralizer_self_of_card_prime h.prime h.P_card
  have hkey : H ⊓ Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (P : Set G) ≤
      Subgroup.centralizer (P : Set G) := by
    rw [hEq]
    exact sup_le (sup_le (hS₂cent.trans inf_le_right) hPleCP)
      (inf_le_left.trans inf_le_right)
  have hUN : Work.NormalComplement.IsSylowIn q U N :=
    isSylowIn_of_isSylowIn_hall hq hUsylE hEN hqE hHall
  have hUC : U ≤ C := le_inf (hUleE.trans hEH) (hUleE.trans inf_le_right)
  have hUCsyl : Work.NormalComplement.IsSylowIn q U C :=
    sylowIn_of_le_of_le hUN hUC hCN
  have hnorm : ∀ y ∈ N, ∀ m ∈ C, y * m * y⁻¹ ∈ C := by
    intro y hy m hm
    obtain ⟨hyH, hyNP⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨hmH, hmC⟩ := Subgroup.mem_inf.mp hm
    refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hyH hmH) (H.inv_mem hyH), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hry : y⁻¹ * r * y ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hyNP (y⁻¹ * r * y)).mpr
        (show y * (y⁻¹ * r * y) * y⁻¹ ∈ P by
          rw [show y * (y⁻¹ * r * y) * y⁻¹ = r by group]; exact hr)
    have hcomm := (Subgroup.mem_centralizer_iff.mp hmC) (y⁻¹ * r * y) hry
    calc r * (y * m * y⁻¹) = y * ((y⁻¹ * r * y) * m) * y⁻¹ := by group
      _ = y * (m * (y⁻¹ * r * y)) * y⁻¹ := by rw [← hcomm]
      _ = (y * m * y⁻¹) * r := by group
  refine le_antisymm ?_ hCN
  intro y hy
  obtain ⟨m, hm, n, hn, rfl⟩ := frattini_decomp hq hCN hnorm hUCsyl y hy
  have hnC : n ∈ C := by
    obtain ⟨hnNU, hnN⟩ := hn
    obtain ⟨hnH, hnNP⟩ := Subgroup.mem_inf.mp hnN
    exact Subgroup.mem_inf.mpr ⟨hnH, hkey ⟨⟨hnH, hnNU⟩, hnNP⟩⟩
  exact C.mul_mem hm hnC

/-! ## Step 2, second half: Burnside's normal `p`-complement and minimality -/

/-- **§4 Prop. 1 step 2**: if `C_A(P) ≠ ⊥` then `P` is not a `p`-Sylow subgroup of `H`.

`normalizer_eq_centralizer` gives `N_H(P) = C_H(P)`.  If `P` were a `p`-Sylow of `H`, then it is
one of `W` (`P ≤ W ≤ H`), whence `N_W(P) ≤ C_W(P)`, and Burnside's normal `p`-complement theorem
produces `N ⊴ ↥W` with `p ∤ |N|` and `↥W ⧸ N` a `p`-group; `N' := N.map W.subtype` then satisfies
`N' < W` and `N' ⊔ P = W`, so `N' ⊔ D = H`.  Since the normal `p`-complement is characteristic in
`W`, one has `H ≤ N_G(N')`, and `Setup45A.minW` gives `|W| ≤ |N'| < |W|`: contradiction. -/
lemma not_isSylowIn_H (hFT : Submission.Blueprint.FeitThompsonProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (hPsyl : Work.NormalComplement.IsSylowIn p P (Submission.Blueprint.twoPoint H t))
    (hHall : Nat.Coprime (Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)))
      ((A ⊓ Subgroup.centralizer (P : Set G)).relIndex
        (H ⊓ Subgroup.normalizer (P : Set G))))
    (hCA : (A ⊓ Subgroup.centralizer (P : Set G)) ≠ ⊥) :
    ¬ Work.NormalComplement.IsSylowIn p P H := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hNH : H ⊓ Subgroup.normalizer (P : Set G) = H ⊓ Subgroup.centralizer (P : Set G) :=
    normalizer_eq_centralizer hFT hP3 h hHall hCA
  have hPleW : P ≤ W := h.P_le.trans (inf_le_left.trans inf_le_left)
  intro hPsylH
  -- ### `P` is a `p`-Sylow subgroup of `W`
  have hPW : Work.NormalComplement.IsSylowIn p P W := by
    refine ⟨hPsyl.1, hPleW, ?_⟩
    have h0 : (P.subgroupOf H).index = P.relIndex H := rfl
    have h1 : P.relIndex W * W.relIndex H = P.relIndex H :=
      Subgroup.relIndex_mul_relIndex P W H hPleW h.le
    rw [subgroupOf_index_eq_relIndex]
    intro hdvd
    exact hPsylH.2.2 (by rw [h0, ← h1]; exact dvd_mul_of_dvd_left hdvd _)
  -- ### `N_W(P) ≤ C_W(P)`, so Burnside applies to `↥W`
  have hPpsub : IsPGroup p ↥(P.subgroupOf W) :=
    hPsyl.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPleW).symm
  let hSylW : Sylow p ↥W := IsPGroup.toSylow hPpsub hPW.2.2
  have hSylWcar : (hSylW : Subgroup ↥W) = P.subgroupOf W := rfl
  have hcent : Subgroup.normalizer ((hSylW : Subgroup ↥W) : Set ↥W) ≤
      Subgroup.centralizer ((hSylW : Subgroup ↥W) : Set ↥W) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzP : ((z : ↥W) : G) ∈ P := by rw [hSylWcar] at hz; exact hz
    have hyN : ((y : ↥W) : G) ∈ H ⊓ Subgroup.normalizer (P : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨h.le y.2, ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      intro p0
      constructor
      · intro hp0
        have hmem : (⟨p0, hPleW hp0⟩ : ↥W) ∈ (hSylW : Subgroup ↥W) := by
          rw [hSylWcar]; exact hp0
        have h1 := (Subgroup.mem_normalizer_iff.mp hy (⟨p0, hPleW hp0⟩ : ↥W)).mp hmem
        rwa [hSylWcar] at h1
      · intro hp0
        have hmem : (⟨y * p0 * y⁻¹, hPleW hp0⟩ : ↥W) ∈ (hSylW : Subgroup ↥W) := by
          rw [hSylWcar]; exact hp0
        have hyinv : y⁻¹ ∈ Subgroup.normalizer ((hSylW : Subgroup ↥W) : Set ↥W) :=
          (Subgroup.normalizer _).inv_mem hy
        have h1 := (Subgroup.mem_normalizer_iff.mp hyinv
          (⟨y * p0 * y⁻¹, hPleW hp0⟩ : ↥W)).mp hmem
        rw [hSylWcar] at h1
        have h1' : (↑(y⁻¹ * (⟨y * p0 * y⁻¹, hPleW hp0⟩ : ↥W) * y : ↥W) : G) ∈ P :=
          by simpa only [inv_inv] using Subgroup.mem_subgroupOf.mp h1
        have h2 : (↑(y⁻¹ * (⟨y * p0 * y⁻¹, hPleW hp0⟩ : ↥W) * y : ↥W) : G) = p0 := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        exact h2 ▸ h1'
    have hyC : ((y : ↥W) : G) ∈ Subgroup.centralizer (P : Set G) := by
      have h2 := hyN; rw [hNH] at h2; exact h2.2
    have hzy : ((z : ↥W) : G) * ((y : ↥W) : G) = ((y : ↥W) : G) * ((z : ↥W) : G) :=
      (Subgroup.mem_centralizer_iff.mp hyC) ((z : ↥W) : G) hzP
    refine Subtype.ext ?_; exact hzy
  obtain ⟨N, hN⟩ := Work.NPC.burnside_npc hSylW hcent
  haveI : N.Normal := hN.normal
  let N' : Subgroup G := N.map W.subtype
  have hN'mem : N' ≤ W := Subgroup.map_subtype_le N
  have hN'card : Nat.card ↥N' = Nat.card ↥N :=
    Subgroup.card_map_of_injective W.subtype_injective
  have hN'cop : Nat.Coprime (Nat.card ↥N') p := by
    rw [hN'card]; exact hN.coprime_card
  have hN'norm : W ≤ Subgroup.normalizer (N' : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro w hw x hx
    obtain ⟨yy, hyy, hyyx⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨w, hw⟩ * yy * ⟨w, hw⟩⁻¹,
      hN.normal.conj_mem yy hyy ⟨w, hw⟩, ?_⟩
    rw [map_mul, map_mul, map_inv, hyyx]
    rfl
  have hN'P : N' ⊓ P = ⊥ := by
    refine Subgroup.card_eq_one.mp ?_
    have h1 : Nat.card ↥(N' ⊓ P) ∣ p := by
      rw [← h.P_card]; exact Subgroup.card_dvd_of_le inf_le_right
    have h2 : Nat.card ↥(N' ⊓ P) ∣ Nat.card ↥N' := Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime h.prime).mp h1 with h3 | h3
    · exact h3
    · rw [h3] at h2
      exact absurd (hN'cop.symm ▸ Nat.dvd_gcd (dvd_refl p) h2) h.prime.not_dvd_one
  have hsub : N'.subgroupOf W = N :=
    Subgroup.comap_map_eq_self_of_injective W.subtype_injective N
  have hNindex : N.index = p := by
    obtain ⟨k, hk0⟩ := IsPGroup.iff_card.mp hN.isPGroup_quotient
    have hk : N.index = p ^ k := by rw [Subgroup.index_eq_card]; exact hk0
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · exfalso
        have hcardN : Nat.card ↥N = Nat.card ↥W := by
          have hcm := Subgroup.card_mul_index N
          rw [hk, h0, pow_zero, mul_one] at hcm; exact hcm
        have hdiv : p ∣ Nat.card ↥W := h.P_card ▸ Subgroup.card_dvd_of_le hPleW
        exact absurd (hN'cop.symm ▸ Nat.dvd_gcd (dvd_refl p)
          (by rw [hN'card, hcardN]; exact hdiv)) h.prime.not_dvd_one
      · exact hpos
    have h1 : p ^ k ∣ Nat.card ↥W :=
      ⟨Nat.card ↥N, by rw [← hk, mul_comm]; exact (Subgroup.card_mul_index N).symm⟩
    have h2 : ¬ p * p ∣ Nat.card ↥W := by
      intro hdvd
      have hcardW : Nat.card ↥W = (P.subgroupOf W).index * Nat.card ↥P := by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleW).toEquiv]
        exact (Subgroup.index_mul_card (P.subgroupOf W)).symm
      rw [hcardW, h.P_card, mul_comm ((P.subgroupOf W).index) p] at hdvd
      exact hPW.2.2 ((Nat.mul_dvd_mul_iff_left h.prime.pos).mp hdvd)
    have hk_eq : p ^ k = p := by
      have hkle : k ≤ 1 := by
        by_contra hcon
        have hcon' : 2 ≤ k := by omega
        exact h2 (dvd_trans (by simpa [pow_two] using Nat.pow_dvd_pow p hcon') h1)
      have hkk : k = 1 := by omega
      rw [hkk, pow_one]
    exact hk.trans hk_eq
  have hN'index : (N'.subgroupOf W).index = p := by rw [hsub]; exact hNindex
  have hsup : N' ⊔ P = W := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hN'mem hPleW) ?_
    have hcardN'W : Nat.card ↥N' * (N'.subgroupOf W).index = Nat.card ↥W := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN'mem).toEquiv]
      exact Subgroup.card_mul_index (N'.subgroupOf W)
    have hcs : Nat.card ↥(N' ⊔ P) = Nat.card ↥N' * p := by
      have hcs := Work.NormalComplement.card_sup_mul_card_inf (H := N') (K := P)
        (hPleW.trans hN'norm)
      rw [hN'P, Subgroup.card_bot, mul_one, h.P_card] at hcs
      exact hcs
    have hcardN'W' : Nat.card ↥N' * p = Nat.card ↥W := by
      rw [← hN'index]; exact hcardN'W
    exact le_of_eq (hcardN'W'.symm.trans hcs.symm)
  -- ### the normal `p`-complement is characteristic in `W`
  have hN'normH : H ≤ Subgroup.normalizer (N' : Set G) :=
    Work.NormalComplement.isNormalPComplement_map_subtype_normal hN h.normal
  have hsupD : N' ⊔ twoPoint H t = H := by
    refine le_antisymm (sup_le (hN'mem.trans h.le) inf_le_left) ?_
    calc H = W ⊔ twoPoint H t := h.sup.symm
      _ ≤ N' ⊔ twoPoint H t := by
          refine sup_le ?_ le_sup_right
          exact (le_of_eq hsup.symm).trans
            (sup_le_sup_left (h.P_le.trans (inf_le_right.trans inf_le_left)) N')
  have hN'lt : N' < W := by
    refine lt_of_le_of_ne hN'mem ?_
    intro heq
    have hdiv : p ∣ Nat.card ↥W := h.P_card ▸ Subgroup.card_dvd_of_le hPleW
    have hdivN' : p ∣ Nat.card ↥N' := heq ▸ hdiv
    exact absurd (hN'cop.symm ▸ Nat.dvd_gcd (dvd_refl p) hdivN') h.prime.not_dvd_one
  -- ### minimality of `W`
  obtain ⟨-, -, -, hmin⟩ := h.minW
  exact absurd (hmin N' (hN'mem.trans h.le) hN'normH hsupD)
    (not_le_of_gt (card_lt_card_of_lt hN'lt))

/-- **Peterfalvi I Ch. III §4 Prop. 1, step 2** (p.180): the conclusion `Step2Conc H t p P A`
(`Submission/Work/NormalComplement/S5K/Defs.lean`): if `C_A(P) = A ⊓ C_G(P) ≠ 1` then `P` is not a
`p`-Sylow subgroup of `H`.

Route (the source's step 2, p.180):
* Let `U ≠ 1` be a Sylow subgroup of `C_A(P)`.  By `h1 : Step1Conc` (step 1 of Prop. 1),
  `C_A(P)` is Hall in `N_H(P) = H ⊓ N_G(P)`, so `U` is a Sylow subgroup of `N_H(P)`.
* Formula (∗) `Work.NormalComplement.sec4_prop1_star` gives `N_H(U) ⊓ N_H(P) ≤ C_H(P)`
  (the right-hand side is `(S₂ ⊔ P) ⊔ (C_A(P) ⊓ N_H(U))`, and modulo `P` everything centralises
  `P`; `S₂` centralises `P` by construction).
* Frattini: `N_H(P) = C_H(P) · (N_H(U) ⊓ N_H(P)) ≤ C_H(P)`, so every element of `N_H(P)`
  centralises `P`.
* If `P` were a `p`-Sylow of `H`, then (minimality of `W`: `h.minW`, and `H = W ⊔ D`) `P ⊓ W`
  would be a Sylow `p`-subgroup of `W` central in its own normaliser, so Burnside's normal
  `p`-complement result (the NPC input in the workspace) would give a normal `p`-complement of `W`,
  i.e. `O^p(W) < W` with `O^p(W) · D = H`, contradicting the minimality of `W` (`h.minW`) — exactly
  as in `Work.NormalComplement.StrategyProp` (`hStrat`). -/
theorem prop1_step2 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hCC : Work.NormalComplement.ControlCorollaryProp)
    (hStrat : Work.NormalComplement.StrategyProp)
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G}
    {p : ℕ} {P A : Subgroup G}
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (hPsyl : Work.NormalComplement.IsSylowIn p P (Submission.Blueprint.twoPoint H t))
    (h1 : Work.NormalComplement.S5K.Step1Conc H t p P A) :
    Work.NormalComplement.S5K.Step2Conc H t p P A := by
  intro hCA
  exact not_isSylowIn_H hFT hP3 h hPsyl h1.1 hCA

end Work.NormalComplement.S5K
