import Mathlib
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.App1.Defs
import Submission.Work.DoubleTransitivity.App1.app1_1b
import Submission.Work.DoubleTransitivity.App2.app2_1
import Submission.Work.DoubleTransitivity.App2.app2_2
import Submission.Work.DoubleTransitivity.App2.app2_4
import Submission.Work.DoubleTransitivity.App1.app1_2
import Submission.Work.DoubleTransitivity.App1.isSylowSubgroupOf_map_subtype
import Submission.Work.DoubleTransitivity.Sec2.prop2
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.ThreePoints.S4Prop2.sec4_basic
import Submission.Work.ThreePoints.S4Prop2.ncard_involutions_conj
import Submission.Work.ThreePoints.S4Prop2.ncard_invertedBy_eq_ncard_conjOrbit
import Submission.Work.DoubleTransitivity.Sec4.RpDefs
import Submission.Work.DoubleTransitivity.Sec4.RpHelpers

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec4.sec4_lemma2_part1_aux`

Appendix I (2), (3)(a)–(3)(d) and the Ch. I §4 `p`-regular-intersection calculus, transcribed
verbatim (with the same proofs, in a private namespace so that no name is duplicated elsewhere in
the workspace) from
`Submission/Work/ThreePoints/S4Prop2/even_card_normalizer_of_maximal_p_subgroup_gen.lean`.
Used by `Submission/Work/DoubleTransitivity/Sec4/sec4_lemma2_part1.lean`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Pointwise

namespace Work.ThreePoints.S4Prop2.L2P1aux

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary Sylow facts -/

/-- A proper subgroup `R` of a finite `p`-group `S`, with `S ≤ X`, has `p`-divisible index in `X`. -/
theorem dvd_index_of_lt_of_isPGroup {p : ℕ} (hp : p.Prime)
    {R S X : Subgroup G} (hRp : IsPGroup p R) (hSp : IsPGroup p S) (hRS : R < S) (hSX : S ≤ X) :
    p ∣ (R.subgroupOf X).index := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hRX : R ≤ X := hRS.le.trans hSX
  have e1 : Nat.card ↥R * (R.subgroupOf X).index = Nat.card ↥X := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv]
    exact Subgroup.card_mul_index _
  have e2 : Nat.card ↥R * (R.subgroupOf S).index = Nat.card ↥S := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRS.le).toEquiv]
    exact Subgroup.card_mul_index _
  have e3 : Nat.card ↥S * (S.subgroupOf X).index = Nat.card ↥X := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv]
    exact Subgroup.card_mul_index _
  have hmul : (R.subgroupOf X).index = (R.subgroupOf S).index * (S.subgroupOf X).index := by
    refine Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card ↥R from Nat.card_pos) ?_
    calc Nat.card ↥R * (R.subgroupOf X).index
        = Nat.card ↥X := e1
      _ = Nat.card ↥S * (S.subgroupOf X).index := e3.symm
      _ = (Nat.card ↥R * (R.subgroupOf S).index) * (S.subgroupOf X).index := by rw [e2]
      _ = Nat.card ↥R * ((R.subgroupOf S).index * (S.subgroupOf X).index) := by ring
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hRp
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hSp
  have hcardlt : Nat.card ↥R < Nat.card ↥S := by
    have hdvd : Nat.card ↥R ∣ Nat.card ↥S := Subgroup.card_dvd_of_le hRS.le
    refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) ?_
    intro h
    exact hRS.ne (Subgroup.eq_of_le_of_card_ge hRS.le (le_of_eq h.symm))
  have hab : a < b := by
    rw [← Nat.pow_lt_pow_iff_right hp.one_lt, ← ha, ← hb]; exact hcardlt
  have hidx : (R.subgroupOf S).index = p ^ (b - a) := by
    have h := e2
    rw [ha, hb] at h
    have h' : p ^ a * p ^ (b - a) = p ^ b := by rw [← pow_add, Nat.add_sub_cancel' hab.le]
    rw [← h'] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos a) h
  have hdvd : p ∣ p ^ (b - a) := by
    have h : p ^ 1 ∣ p ^ (b - a) := pow_dvd_pow p (by omega)
    simpa using h
  rw [hmul, hidx]
  exact dvd_mul_of_dvd_left hdvd _

/-- If a `p`-subgroup `P ≤ X` is a `p`-Sylow subgroup of its normaliser inside `X`, then it is a
`p`-Sylow subgroup of `X`.  (If not, some strictly larger `p`-subgroup `S ≤ X` would have
`P < N_S(P) ≤ X ⊓ N_G(P)`, contradicting the hypothesis.) -/
theorem isSylow_of_isSylow_normalizer {p : ℕ} (hp : p.Prime) {P X : Subgroup G}
    (hPX : P ≤ X) (hPp : IsPGroup p P)
    (h : ¬ p ∣ (P.subgroupOf (X ⊓ Subgroup.normalizer (P : Set G))).index) :
    ¬ p ∣ (P.subgroupOf X).index := by
  intro hcon
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSX, hSp, hPS⟩ := Work.ThreePoints.exists_pSubgroup_lt_of_dvd_index hp hPp hPX hcon
  have hlt : P < S ⊓ Subgroup.normalizer (P : Set G) := Work.Coprime.lt_inf_normalizer_of_lt hSp hPS
  have hle : S ⊓ Subgroup.normalizer (P : Set G) ≤ X ⊓ Subgroup.normalizer (P : Set G) :=
    inf_le_inf_right _ hSX
  exact h (dvd_index_of_lt_of_isPGroup hp hPp hSp.to_inf_left hlt hle)

/-! ## Ch. I §4: the `p`-regular intersection calculus -/

/-- Orbit–stabiliser for the conjugation action, in the form used in Appendix I (1)(a):
`|u^X| · |C_X(u)| = |X|` — no normalisation hypothesis on `X`. -/
theorem mul_ncard_conjOrbit_ncard_centralizer (X : Subgroup G) (u : G) :
    (Work.DoubleTransitivity.conjOrbit X u).ncard *
      Nat.card ↥(X ⊓ Subgroup.centralizer ({u} : Set G)) = Nat.card ↥X := by
  classical
  letI : MulAction ↥X G :=
    { smul := fun x g => (x : G) * g * (x : G)⁻¹
      one_smul := fun g => by
        show (1 : G) * g * (1 : G)⁻¹ = g
        group
      mul_smul := fun x y g => by
        show ((x : G) * (y : G)) * g * ((x : G) * (y : G))⁻¹ =
          (x : G) * ((y : G) * g * (y : G)⁻¹) * (x : G)⁻¹
        group }
  have horb : MulAction.orbit ↥X u = Work.DoubleTransitivity.conjOrbit X u := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G)⁻¹, X.inv_mem x.2, by
        show (x : G)⁻¹⁻¹ * u * (x : G)⁻¹ = (x : G) * u * (x : G)⁻¹
        rw [inv_inv]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x⁻¹, X.inv_mem hx⟩, by
        show (x⁻¹ : G) * u * (x⁻¹ : G)⁻¹ = x⁻¹ * u * x
        rw [inv_inv]⟩
  have hstab : MulAction.stabilizer ↥X u =
      (X ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf X := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : (x : G) * u * (x : G)⁻¹ = u := h
      refine ⟨x.2, ?_⟩
      calc (x : G) * u = ((x : G) * u * (x : G)⁻¹) * (x : G) := by group
        _ = u * (x : G) := by rw [h']
    · rintro ⟨-, h⟩
      show (x : G) * u * (x : G)⁻¹ = u
      rw [show (x : G) * u * (x : G)⁻¹ = u * ((x : G) * (x : G)⁻¹) by rw [h]; group]
      simp
  have hcard : Nat.card ↥(MulAction.stabilizer ↥X u) =
      Nat.card ↥(X ⊓ Subgroup.centralizer ({u} : Set G)) := by
    rw [hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer ↥X u)
  rw [MulAction.index_stabilizer, horb, hcard] at h2
  calc (Work.DoubleTransitivity.conjOrbit X u).ncard *
        Nat.card ↥(X ⊓ Subgroup.centralizer ({u} : Set G))
      = Nat.card ↥(X ⊓ Subgroup.centralizer ({u} : Set G)) *
        (Work.DoubleTransitivity.conjOrbit X u).ncard := mul_comm _ _
    _ = Nat.card ↥X := h2

/-- `N(Z) ∩ N(Q) ⊆ N(Z ⊓ N(Q))`. -/
theorem mem_normalizer_inf_normalizer {u : G} {Z Q : Subgroup G}
    (hZ : u ∈ Subgroup.normalizer (Z : Set G)) (hQ : u ∈ Subgroup.normalizer (Q : Set G)) :
    u ∈ Subgroup.normalizer (Z ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) := by
  have key : ∀ (g : G), g ∈ Subgroup.normalizer (Z : Set G) →
      g ∈ Subgroup.normalizer (Q : Set G) → ∀ z : G,
      z ∈ Z ⊓ Subgroup.normalizer (Q : Set G) →
      g * z * g⁻¹ ∈ Z ⊓ Subgroup.normalizer (Q : Set G) := by
    intro g hgZ hgQ z hz
    have hgQ' : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) := (Subgroup.normalizer (Q : Set G)).inv_mem hgQ
    refine ⟨(Subgroup.mem_normalizer_iff.mp hgZ z).mp hz.1, Subgroup.mem_normalizer_iff.mpr ?_⟩
    intro y
    have hxN : ∀ y, y ∈ Q ↔ z * y * z⁻¹ ∈ Q := Subgroup.mem_normalizer_iff.mp hz.2
    have hgy : ∀ y, y ∈ Q ↔ g * y * g⁻¹ ∈ Q := Subgroup.mem_normalizer_iff.mp hgQ
    have hgy' : ∀ y, y ∈ Q ↔ g⁻¹ * y * g⁻¹⁻¹ ∈ Q := Subgroup.mem_normalizer_iff.mp hgQ'
    rw [show g * z * g⁻¹ * y * (g * z * g⁻¹)⁻¹ =
        g * (z * (g⁻¹ * y * g) * z⁻¹) * g⁻¹ by group,
      ← hgy (z * (g⁻¹ * y * g) * z⁻¹), ← hxN (g⁻¹ * y * g)]
    simpa using hgy' y
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key u hZ hQ x
  · intro hx
    have h1 : u⁻¹ * (u * x * u⁻¹) * u⁻¹⁻¹ = x := by rw [inv_inv]; group
    exact h1 ▸ key u⁻¹ ((Subgroup.normalizer (Z : Set G)).inv_mem hZ)
      ((Subgroup.normalizer (Q : Set G)).inv_mem hQ) (u * x * u⁻¹) hx

/-- Monotonicity of the order of a subgroup. -/
theorem card_le_card_of_le {H K : Subgroup G} (h : H ≤ K) : Nat.card ↥H ≤ Nat.card ↥K := by
  haveI : Nonempty ↥K := ⟨⟨1, K.one_mem⟩⟩
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le h)

/-- A `p`-Sylow subgroup of `Y` has order the `p`-part of `|Y|`. -/
theorem card_of_isSylowSubgroupOf {p : ℕ} [Fact p.Prime] {R Y : Subgroup G}
    (hR : Work.DoubleTransitivity.IsSylowSubgroupOf p R Y) :
    Nat.card ↥R = p ^ (Nat.card ↥Y).factorization p := by
  obtain ⟨hRY, hRp, hidx⟩ := hR
  haveI : Nonempty ↥R := ⟨⟨1, R.one_mem⟩⟩
  haveI : Nonempty ↥Y := ⟨⟨1, Y.one_mem⟩⟩
  have hne : Nat.card ↥R ≠ 0 := Nat.card_pos.ne'
  have hidxne : (R.subgroupOf Y).index ≠ 0 := fun h => by
    have h1 := Subgroup.card_mul_index (R.subgroupOf Y)
    rw [h, mul_zero] at h1
    exact (Nat.card_pos.ne') h1.symm
  have hcard : Nat.card ↥Y = Nat.card ↥R * (R.subgroupOf Y).index := by
    have h := Subgroup.card_mul_index (R.subgroupOf Y)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRY).toEquiv] at h
    exact h.symm
  have hfac : (Nat.card ↥Y).factorization p = (Nat.card ↥R).factorization p := by
    rw [hcard, Nat.factorization_mul hne hidxne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
  have hpow : Nat.card ↥R = p ^ (Nat.card ↥R).factorization p := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
    rw [hk]
    congr 1
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.Prime.factorization (Fact.out : p.Prime), Finsupp.single_eq_same, mul_one]
  exact hfac.symm ▸ hpow

/-- **Appendix I (2)**, containment clause.  If `Z` is a `u`-invariant subgroup of odd order and
`P ≤ Z` is a `u`-invariant `p`-subgroup, then `P` is contained in a `u`-invariant `p`-Sylow of
`Z`. -/
theorem exists_invariant_sylow_ge {p : ℕ} (hp : p.Prime) {u : G} (hu : orderOf u = 2)
    {Z : Subgroup G} (hZodd : Odd (Nat.card ↥Z))
    (hZu : u ∈ Subgroup.normalizer (Z : Set G))
    {P : Subgroup G} (hPZ : P ≤ Z) (hPp : IsPGroup p P)
    (hPu : u ∈ Subgroup.normalizer (P : Set G)) :
    ∃ Q : Subgroup G, P ≤ Q ∧ Q ≤ Z ∧ IsPGroup p Q ∧ ¬ p ∣ (Q.subgroupOf Z).index ∧
      u ∈ Subgroup.normalizer (Q : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set φ : ℕ → Prop := fun m => ∃ Q : Subgroup G, P ≤ Q ∧ Q ≤ Z ∧ IsPGroup p Q ∧
      u ∈ Subgroup.normalizer (Q : Set G) ∧ Nat.card ↥Q = m with hφ
  have hex : ∃ m, φ m ∧ m ≤ Nat.card ↥Z :=
    ⟨Nat.card ↥P, ⟨⟨P, le_rfl, hPZ, hPp, hPu, rfl⟩,
      card_le_card_of_le hPZ⟩⟩
  obtain ⟨m₀, hm₀φ, hm₀le⟩ := hex
  obtain ⟨Q, hPQ, hQZ, hQp, hQu, hQcard⟩ := Nat.findGreatest_spec hm₀le hm₀φ
  have hQmax : ∀ Q' : Subgroup G, P ≤ Q' → Q' ≤ Z → IsPGroup p Q' →
      u ∈ Subgroup.normalizer (Q' : Set G) → Nat.card ↥Q' ≤ Nat.card ↥Q := by
    intro Q' h1 h2 h3 h4
    have h5 : Nat.card ↥Q' ≤ Nat.card ↥Z := card_le_card_of_le h2
    have h6 : ¬ (Nat.findGreatest φ (Nat.card ↥Z) < Nat.card ↥Q') :=
      fun hlt => Nat.findGreatest_is_greatest hlt h5 ⟨Q', h1, h2, h3, h4, rfl⟩
    have h7 : Nat.card ↥Q' ≤ Nat.findGreatest φ (Nat.card ↥Z) := not_lt.mp h6
    rwa [← hQcard] at h7
  set W : Subgroup G := Z ⊓ Subgroup.normalizer (Q : Set G) with hW
  have hWodd : Odd (Nat.card ↥W) := Odd.of_dvd (Subgroup.card_dvd_of_le inf_le_left) hZodd
  have hQW : Q ≤ W := le_inf hQZ Subgroup.le_normalizer
  have hWu : u ∈ Subgroup.normalizer (W : Set G) := mem_normalizer_inf_normalizer hZu hQu
  obtain ⟨R, hRsyl, hRu, _⟩ :=
    Work.DoubleTransitivity.App1.app1_2 (X := W) (t := u) (d := 2) Nat.prime_two hu
      (Nat.coprime_two_left.mpr hWodd) hWu hp
  have hle : Q ≤ R := by
    have hQw : IsPGroup p ↥(Q.subgroupOf W) :=
      hQp.comap_of_injective W.subtype Subtype.coe_injective
    obtain ⟨R'w, hQR'w⟩ := IsPGroup.exists_le_sylow hQw
    have hR'syl : Work.DoubleTransitivity.IsSylowSubgroupOf p
        (Subgroup.map W.subtype (R'w : Subgroup ↥W)) W :=
      Work.DoubleTransitivity.App1.isSylowSubgroupOf_map_subtype hp R'w
    have hQR' : Q ≤ Subgroup.map W.subtype (R'w : Subgroup ↥W) := by
      have h1 : (Q.subgroupOf W) ≤ (R'w : Subgroup ↥W) := hQR'w
      calc Q = Subgroup.map W.subtype (Q.subgroupOf W) :=
            (Subgroup.map_subgroupOf_eq_of_le hQW).symm
        _ ≤ Subgroup.map W.subtype (R'w : Subgroup ↥W) := Subgroup.map_mono h1
    obtain ⟨d, hdW, hd⟩ :=
      exists_conj_of_isSylowSubgroupOf hp hR'syl.1 hR'syl.2.1 hR'syl.2.2 hRsyl.1 hRsyl.2.1
        hRsyl.2.2
    have hWle : W ≤ Subgroup.normalizer (Q : Set G) := inf_le_right
    have hQconj : Submission.Blueprint.conj d Q = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hWle hdW)
    rw [← hd, ← hQconj]
    exact Subgroup.map_mono hQR'
  have hQsylW : ¬ p ∣ (Q.subgroupOf W).index := by
    have heq : R = Q := (Subgroup.eq_of_le_of_card_ge hle
      (hQmax R (le_trans hPQ hle) (le_trans hRsyl.1 inf_le_left) hRsyl.2.1 hRu)).symm
    rw [← heq]
    exact hRsyl.2.2
  exact ⟨Q, hPQ, hQZ, hQp, isSylow_of_isSylow_normalizer hp hQZ hQp hQsylW, hQu⟩

/-- **Appendix I (3)(a)**.  For a `u`-invariant `p`-Sylow `P` of the `u`-invariant group `Z` of
odd order, `|C_P(u)|` is the `p`-part of `|C_Z(u)|`. -/
theorem card_centralizer_in_invariant_sylow {p : ℕ} (hp : p.Prime) {u : G} (hu : orderOf u = 2)
    {Z P : Subgroup G} (hZodd : Odd (Nat.card ↥Z)) (hZu : u ∈ Subgroup.normalizer (Z : Set G))
    (hPZ : P ≤ Z) (hPp : IsPGroup p P) (hPu : u ∈ Subgroup.normalizer (P : Set G))
    (hsyl : ¬ p ∣ (P.subgroupOf Z).index) :
    Nat.card ↥(P ⊓ Subgroup.centralizer ({u} : Set G)) =
      p ^ (Nat.card ↥(Z ⊓ Subgroup.centralizer ({u} : Set G))).factorization p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := Subgroup.centralizer ({u} : Set G) with hC
  have hCPp : IsPGroup p ↥((P ⊓ C).subgroupOf (Z ⊓ C)) :=
    (hPp.to_inf_left).comap_of_injective (Z ⊓ C).subtype Subtype.coe_injective
  obtain ⟨Rw, hCPRw⟩ := IsPGroup.exists_le_sylow hCPp
  set Q : Subgroup G := Subgroup.map (Z ⊓ C).subtype (Rw : Subgroup ↥(Z ⊓ C)) with hQ
  have hQsyl : Work.DoubleTransitivity.IsSylowSubgroupOf p Q (Z ⊓ C) :=
    Work.DoubleTransitivity.App1.isSylowSubgroupOf_map_subtype hp Rw
  have hCPQ : P ⊓ C ≤ Q := by
    have h1 : (P ⊓ C).subgroupOf (Z ⊓ C) ≤ (Rw : Subgroup ↥(Z ⊓ C)) := hCPRw
    calc P ⊓ C = Subgroup.map (Z ⊓ C).subtype ((P ⊓ C).subgroupOf (Z ⊓ C)) :=
          (Subgroup.map_subgroupOf_eq_of_le (inf_le_inf_right _ hPZ)).symm
      _ ≤ Subgroup.map (Z ⊓ C).subtype (Rw : Subgroup ↥(Z ⊓ C)) := Subgroup.map_mono h1
  have hQZ : Q ≤ Z := le_trans hQsyl.1 inf_le_left
  have hQC : Q ≤ C := le_trans hQsyl.1 inf_le_right
  have hQu : u ∈ Subgroup.normalizer (Q : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro x
    constructor
    · intro hx
      have hxC : u * x = x * u := (Subgroup.mem_centralizer_iff.mp (hQC hx)) u (by simp)
      rw [show u * x * u⁻¹ = x by rw [hxC]; group]
      exact hx
    · intro hx
      have hxC : u * (u * x * u⁻¹) = (u * x * u⁻¹) * u :=
        (Subgroup.mem_centralizer_iff.mp (hQC hx)) u (by simp)
      have h1 : u⁻¹ * (u * x * u⁻¹) * u = u * x * u⁻¹ := by
        calc u⁻¹ * (u * x * u⁻¹) * u = u⁻¹ * (u * (u * x * u⁻¹)) := by rw [hxC]; group
          _ = u * x * u⁻¹ := by group
      have h2 : x = u * x * u⁻¹ := by rw [← h1]; group
      rw [h2]
      exact hx
  obtain ⟨Q', hQQ', hQ'Z, hQ'p, hQ'syl, hQ'u⟩ :=
    exists_invariant_sylow_ge hp hu hZodd hZu hQZ hQsyl.2.1 hQu
  obtain ⟨P₀, _hP₀syl, _hP₀u, hP₀conj⟩ :=
    Work.DoubleTransitivity.App1.app1_2 (X := Z) (t := u) (d := 2) Nat.prime_two hu
      (Nat.coprime_two_left.mpr hZodd) hZu hp
  obtain ⟨v, hv, hvconj⟩ := hP₀conj P ⟨hPZ, hPp, hsyl⟩ hPu
  obtain ⟨w, hw, hwconj⟩ := hP₀conj Q' ⟨hQ'Z, hQ'p, hQ'syl⟩ hQ'u
  have hvw : P₀ = Submission.Blueprint.conj v⁻¹ P := by
    rw [← hvconj, ← conj_mul, inv_mul_cancel, conj_one]
  have hconj : Q' = Submission.Blueprint.conj (w * v⁻¹) P := by
    rw [← hwconj, Work.ThreePoints.conj_mul, hvw]
  have hwC : w * v⁻¹ ∈ C := C.mul_mem hw.2 (C.inv_mem hv.2)
  have hconjC : Submission.Blueprint.conj (w * v⁻¹) C = C :=
    Work.ThreePoints.conj_eq_self_of_mem hwC
  have hcard : Nat.card ↥(Q' ⊓ C) = Nat.card ↥(P ⊓ C) := by
    conv_lhs => rw [hconj, ← hconjC, ← Work.ThreePoints.conj_inf]
    exact Subgroup.card_map_of_injective
      (f := (MulAut.conj (w * v⁻¹)).toMonoidHom) (MulAut.conj (w * v⁻¹)).injective
  have hle1 : Nat.card ↥(P ⊓ C) ≤ Nat.card ↥Q := card_le_card_of_le hCPQ
  have hle2 : Nat.card ↥Q ≤ Nat.card ↥(P ⊓ C) := by
    rw [← hcard]
    exact card_le_card_of_le (le_inf hQQ' (le_trans hQsyl.1 inf_le_right))
  exact (le_antisymm hle1 hle2).trans (card_of_isSylowSubgroupOf hQsyl)

/-- The `p`-adic valuation of `p ^ k`. -/
theorem factorization_pow_self {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p ^ k).factorization p = k := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.Prime.factorization hp, Finsupp.single_eq_same, mul_one]

/-- For a `p`-subgroup `X` normalised by `t`, the orbit `t^X` has order
`p ^ (v_p |X| - v_p |C_X(t)|)`. -/
theorem card_conjOrbit_eq_pow_sub {p : ℕ} (hp : p.Prime) {X : Subgroup G} {t : G}
    (hXp : IsPGroup p X) (ht : t ∈ Subgroup.normalizer (X : Set G)) :
    (Work.DoubleTransitivity.conjOrbit X t).ncard =
      p ^ ((Nat.card ↥X).factorization p -
        (Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G))).factorization p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hXp
  obtain ⟨v, hv⟩ := IsPGroup.iff_card.mp hXp.to_inf_left
  have hmain : (Work.DoubleTransitivity.conjOrbit X t).ncard *
      Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) = Nat.card ↥X :=
    mul_ncard_conjOrbit_ncard_centralizer X t
  rw [hv, ha] at hmain
  have hfacX : (Nat.card ↥X).factorization p = a := by
    rw [ha]; exact factorization_pow_self hp a
  have hfacV : (Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G))).factorization p = v := by
    rw [hv]; exact factorization_pow_self hp v
  have hva : v ≤ a := by
    have hdvd : p ^ v ∣ p ^ a :=
      ⟨_, by rw [mul_comm]; exact hmain.symm⟩
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  have hk : (Work.DoubleTransitivity.conjOrbit X t).ncard = p ^ (a - v) := by
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos v) ?_
    rw [hmain, ← pow_add, Nat.sub_add_cancel hva]
  rw [hk, hfacX, hfacV]

/-- Appendix I (3)(d), `(iii) ⇒ (i)`: an invariant `p`-subgroup `P ≤ D = K ⊓ K^t` whose orbit
`|u^P|` has `p`-part at least that of `|Inv K|` gives a `p`-regular intersection for `D` relative
to `K`. -/
theorem isRegularIntersection_of_invariant {K : Subgroup G} (hK : IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) {t : G} (ht : orderOf t = 2) (htK : t ∉ K)
    (h : ∃ P : Subgroup G, P ≤ twoPoint K t ∧ IsPGroup p P ∧
      ∃ u ∈ Submission.Blueprint.involutions (K : Set G),
        u ∈ Subgroup.normalizer (P : Set G) ∧
        (Submission.Blueprint.involutions (K : Set G)).ncard.factorization p ≤
          (Work.DoubleTransitivity.conjOrbit P u).ncard.factorization p) :
    Work.DoubleTransitivity.IsRegularIntersection p (twoPoint K t) K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPD, hPp, u, hu, hPu, hle⟩ := h
  set D : Subgroup G := twoPoint K t with hD
  have hu2 : orderOf u = 2 := hu.2
  have huK : u ∈ K := hu.1
  have huu : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu2
  have huu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hDodd : Odd (Nat.card ↥D) := by
    have hne : Submission.Blueprint.conj (1 : G) K ≠ Submission.Blueprint.conj t K := by
      rw [conj_one]
      intro hc
      have htm : t ∈ Subgroup.normalizer (K : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hc.symm
      rw [Work.ThreePoints.IsStronglyEmbedded.normalizer_eq hK] at htm
      exact htK htm
    have h1 := card_inf_conj_odd hK (g := 1) (g' := t) hne
    simpa [hD, Submission.Blueprint.twoPoint, conj_one] using h1
  have hB : Work.DoubleTransitivity.IsBender K :=
    ((Work.DoubleTransitivity.isStronglyEmbedded_iff K).mp hK).2
  have hKne : K ≠ ⊤ := ((Work.DoubleTransitivity.isStronglyEmbedded_iff K).mp hK).1
  have huo : (Work.DoubleTransitivity.conjOrbit D u).ncard =
      (Submission.Blueprint.involutions (K : Set G)).ncard := by
    have h1 := (Work.DoubleTransitivity.Sec2.prop2 hB hKne ht htK).2.2 u hu
    simpa [hD, Submission.Blueprint.twoPoint] using h1
  -- `Z = D ⊓ D^u` is `u`-invariant of odd order
  set Z : Subgroup G := D ⊓ Submission.Blueprint.conj u D with hZ
  have hZu : u ∈ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Submission.Blueprint.conj u (D ⊓ Submission.Blueprint.conj u D) =
      D ⊓ Submission.Blueprint.conj u D
    rw [conj_inf, ← conj_mul, huu, conj_one, inf_comm]
  have hZodd : Odd (Nat.card ↥Z) := Odd.of_dvd (Subgroup.card_dvd_of_le inf_le_left) hDodd
  have hPZ : P ≤ Z := by
    refine le_inf hPD ?_
    intro x hx
    have h1 : u * x * u⁻¹ ∈ D := hPD ((Subgroup.mem_normalizer_iff.mp hPu x).mp hx)
    refine Work.ThreePoints.mem_conj_iff.mpr ?_
    rw [huu'] at h1 ⊢
    exact h1
  -- extension to a `u`-invariant `p`-Sylow of `Z`
  obtain ⟨Q, hPQ, hQZ, hQp, hQsyl, hQu⟩ :=
    exists_invariant_sylow_ge hp hu2 hZodd hZu hPZ hPp hPu
  have hQD : Q ≤ D := le_trans hQZ inf_le_left
  -- centralisers
  have hCZ : Z ⊓ Subgroup.centralizer ({u} : Set G) =
      D ⊓ Subgroup.centralizer ({u} : Set G) := by
    rw [hZ]
    ext x
    simp only [Subgroup.mem_inf, mem_conj_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨hxD, -⟩, hx⟩; exact ⟨hxD, hx⟩
    · rintro ⟨hxD, hx⟩
      refine ⟨⟨hxD, ?_⟩, hx⟩
      have h1 : u⁻¹ * x * u = x := by
        calc u⁻¹ * x * u = u⁻¹ * (x * u) := by group
          _ = u⁻¹ * (u * x) := by rw [hx]
          _ = x := by group
      rw [h1]
      exact hxD
  have hcent := card_centralizer_in_invariant_sylow hp hu2 hZodd hZu hQZ hQp hQu hQsyl
  rw [hCZ] at hcent
  -- order computations
  have hDne : Nat.card ↥D ≠ 0 := by
    haveI : Nonempty ↥D := ⟨⟨1, D.one_mem⟩⟩
    exact Nat.card_pos.ne'
  have hCne : Nat.card ↥(D ⊓ Subgroup.centralizer ({u} : Set G)) ≠ 0 := by
    haveI : Nonempty ↥(D ⊓ Subgroup.centralizer ({u} : Set G)) :=
      ⟨⟨1, ⟨D.one_mem, Subgroup.one_mem _⟩⟩⟩
    exact Nat.card_pos.ne'
  have hQne : Nat.card ↥Q ≠ 0 := by
    haveI : Nonempty ↥Q := ⟨⟨1, Q.one_mem⟩⟩
    exact Nat.card_pos.ne'
  have hCQne : Nat.card ↥(Q ⊓ Subgroup.centralizer ({u} : Set G)) ≠ 0 := by
    haveI : Nonempty ↥(Q ⊓ Subgroup.centralizer ({u} : Set G)) :=
      ⟨⟨1, ⟨Q.one_mem, Subgroup.one_mem _⟩⟩⟩
    exact Nat.card_pos.ne'
  have hUQne : (Work.DoubleTransitivity.conjOrbit Q u).ncard ≠ 0 := by
    have hne : (Work.DoubleTransitivity.conjOrbit Q u).Nonempty :=
      ⟨u, Work.DoubleTransitivity.t_mem_conjOrbit⟩
    exact ((Set.ncard_pos (s := Work.DoubleTransitivity.conjOrbit Q u)).mpr hne).ne'
  have hUDne : (Work.DoubleTransitivity.conjOrbit D u).ncard ≠ 0 := by
    have hne : (Work.DoubleTransitivity.conjOrbit D u).Nonempty :=
      ⟨u, Work.DoubleTransitivity.t_mem_conjOrbit⟩
    exact ((Set.ncard_pos (s := Work.DoubleTransitivity.conjOrbit D u)).mpr hne).ne'
  -- `|u^P| ≤ |u^Q|`, and both are powers of `p`
  have hcardPQ : (Work.DoubleTransitivity.conjOrbit P u).ncard ≤
      (Work.DoubleTransitivity.conjOrbit Q u).ncard :=
    Set.ncard_le_ncard (by rintro y ⟨x, hx, rfl⟩; exact ⟨x, hPQ hx, rfl⟩)
  have horb_le : (Work.DoubleTransitivity.conjOrbit P u).ncard.factorization p ≤
      (Work.DoubleTransitivity.conjOrbit Q u).ncard.factorization p := by
    obtain ⟨eP, heP⟩ : ∃ k, (Work.DoubleTransitivity.conjOrbit P u).ncard = p ^ k :=
      ⟨_, card_conjOrbit_eq_pow_sub hp hPp hPu⟩
    obtain ⟨eQ, heQ⟩ : ∃ k, (Work.DoubleTransitivity.conjOrbit Q u).ncard = p ^ k :=
      ⟨_, card_conjOrbit_eq_pow_sub hp hQp hQu⟩
    have h1 : (Work.DoubleTransitivity.conjOrbit P u).ncard =
        p ^ (Work.DoubleTransitivity.conjOrbit P u).ncard.factorization p := by
      rw [heP, factorization_pow_self hp]
    have h2 : (Work.DoubleTransitivity.conjOrbit Q u).ncard =
        p ^ (Work.DoubleTransitivity.conjOrbit Q u).ncard.factorization p := by
      rw [heQ, factorization_pow_self hp]
    rw [h1, h2] at hcardPQ
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcardPQ
  -- `(|Q|)_p = (|D|)_p`
  have hQeqD : (Nat.card ↥Q).factorization p = (Nat.card ↥D).factorization p := by
    have h3 : (Nat.card ↥(Q ⊓ Subgroup.centralizer ({u} : Set G))).factorization p =
        (Nat.card ↥(D ⊓ Subgroup.centralizer ({u} : Set G))).factorization p := by
      rw [hcent, factorization_pow_self hp]
    have hQf : (Nat.card ↥Q).factorization p =
        (Work.DoubleTransitivity.conjOrbit Q u).ncard.factorization p +
        (Nat.card ↥(Q ⊓ Subgroup.centralizer ({u} : Set G))).factorization p := by
      rw [← mul_ncard_conjOrbit_ncard_centralizer Q u, Nat.factorization_mul hUQne hCQne,
        Finsupp.add_apply]
    have hDf : (Nat.card ↥D).factorization p =
        (Work.DoubleTransitivity.conjOrbit D u).ncard.factorization p +
        (Nat.card ↥(D ⊓ Subgroup.centralizer ({u} : Set G))).factorization p := by
      rw [← mul_ncard_conjOrbit_ncard_centralizer D u, Nat.factorization_mul hUDne hCne,
        Finsupp.add_apply]
    have h4 : (Work.DoubleTransitivity.conjOrbit D u).ncard.factorization p ≤
        (Work.DoubleTransitivity.conjOrbit Q u).ncard.factorization p := by
      rw [huo]
      exact le_trans hle horb_le
    have h5 : (Nat.card ↥Q).factorization p ≤ (Nat.card ↥D).factorization p :=
      (Nat.factorization_le_iff_dvd hQne hDne).mpr (Subgroup.card_dvd_of_le hQD) p
    omega
  -- `Q` has the order of a `p`-Sylow of `D`
  have hQcard : Nat.card ↥Q = p ^ (Nat.card ↥D).factorization p := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
    have hk' : k = (Nat.card ↥D).factorization p := by
      have h := hQeqD
      rw [hk, factorization_pow_self hp] at h
      exact h
    rw [hk, hk']
  -- `Q` is a `p`-Sylow of `D`, and `u ∈ N(Q) ⊓ K` is an involution
  refine ⟨Q, ⟨hQD, hQp, ?_⟩, ?_⟩
  · intro hd
    have hindne : (Q.subgroupOf D).index ≠ 0 := fun hh => by
      have h1 := Subgroup.card_mul_index (Q.subgroupOf D)
      rw [hh, mul_zero] at h1
      exact hDne h1.symm
    have h1 : Nat.card ↥D = Nat.card ↥Q * (Q.subgroupOf D).index := by
      have h2 := Subgroup.card_mul_index (Q.subgroupOf D)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQD).toEquiv] at h2
      exact h2.symm
    have h2 : (Nat.card ↥D).factorization p = (Nat.card ↥Q).factorization p +
        (Q.subgroupOf D).index.factorization p := by
      rw [h1, Nat.factorization_mul hQne hindne, Finsupp.add_apply]
    have h3 : (Nat.card ↥Q).factorization p = (Nat.card ↥D).factorization p := by
      rw [hQcard, factorization_pow_self hp]
    have h4 : (Q.subgroupOf D).index.factorization p = 0 := by omega
    obtain ⟨m, hm⟩ := hd
    have hm0 : m ≠ 0 := fun h0 => hindne (by rw [hm, h0, mul_zero])
    rw [hm, Nat.factorization_mul ((Fact.out : p.Prime).pos.ne') hm0, Finsupp.add_apply,
      Nat.Prime.factorization (Fact.out : p.Prime), Finsupp.single_eq_same] at h4
    omega
  · have hm : u ∈ (Subgroup.normalizer (Q : Set G) ⊓ K : Subgroup G) := ⟨hQu, huK⟩
    refine even_iff_two_dvd.mpr ?_
    have hord : orderOf (⟨u, hm⟩ :
        ↥(Subgroup.normalizer (Q : Set G) ⊓ K : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact hu2
    exact dvd_trans (by rw [hord]) (orderOf_dvd_natCard _)

theorem card_conjOrbit_sylow {p : ℕ} (hp : p.Prime) {t : G} (ht : orderOf t = 2)
    {D : Subgroup G} (hDodd : Odd (Nat.card ↥D))
    (htD : t ∈ Subgroup.normalizer (D : Set G))
    {P : Subgroup G} (hPD : P ≤ D) (hPp : IsPGroup p P)
    (htP : t ∈ Subgroup.normalizer (P : Set G))
    (hsyl : ¬ p ∣ (P.subgroupOf D).index) :
    (Work.DoubleTransitivity.conjOrbit P t).ncard =
      p ^ (Work.DoubleTransitivity.conjOrbit D t).ncard.factorization p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hPcard : Nat.card ↥P = p ^ (Nat.card ↥D).factorization p :=
    card_of_isSylowSubgroupOf ⟨hPD, hPp, hsyl⟩
  have hcent := card_centralizer_in_invariant_sylow hp ht hDodd htD hPD hPp htP hsyl
  have hPfac : (Nat.card ↥P).factorization p = (Nat.card ↥D).factorization p := by
    rw [hPcard]; exact factorization_pow_self hp _
  have hCfac : (Nat.card ↥(P ⊓ Subgroup.centralizer ({t} : Set G))).factorization p =
      (Nat.card ↥(D ⊓ Subgroup.centralizer ({t} : Set G))).factorization p := by
    rw [hcent]; exact factorization_pow_self hp _
  have hDne : Nat.card ↥D ≠ 0 := by
    haveI : Nonempty ↥D := ⟨⟨1, D.one_mem⟩⟩
    exact Nat.card_pos.ne'
  have hCDne : Nat.card ↥(D ⊓ Subgroup.centralizer ({t} : Set G)) ≠ 0 := by
    haveI : Nonempty ↥(D ⊓ Subgroup.centralizer ({t} : Set G)) :=
      ⟨⟨1, ⟨D.one_mem, Subgroup.one_mem _⟩⟩⟩
    exact Nat.card_pos.ne'
  have hUDne : (Work.DoubleTransitivity.conjOrbit D t).ncard ≠ 0 := by
    have hne : (Work.DoubleTransitivity.conjOrbit D t).Nonempty :=
      ⟨t, Work.DoubleTransitivity.t_mem_conjOrbit⟩
    exact ((Set.ncard_pos (s := Work.DoubleTransitivity.conjOrbit D t)).mpr hne).ne'
  have hDfac : (Nat.card ↥D).factorization p =
      (Work.DoubleTransitivity.conjOrbit D t).ncard.factorization p +
      (Nat.card ↥(D ⊓ Subgroup.centralizer ({t} : Set G))).factorization p := by
    rw [← mul_ncard_conjOrbit_ncard_centralizer D t, Nat.factorization_mul hUDne hCDne,
      Finsupp.add_apply]
  rw [card_conjOrbit_eq_pow_sub hp hPp htP, hPfac, hCfac]
  congr 1
  omega

end Work.ThreePoints.S4Prop2.L2P1aux
