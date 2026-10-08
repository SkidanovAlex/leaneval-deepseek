/-
# `Submission.Work.NormalComplement.S5K.prop1_step3_aux`

Auxiliary lemmas for the proof of Peterfalvi I Ch. III §4 Prop. 1, step 3
(`Submission/Work/NormalComplement/S5K/prop1_step3.lean`).
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.S5K.prop1_step3_defs
import Submission.Work.NormalComplement.S5K.Defs
import Submission.Work.NormalComplement.S5K.ca_coprime
import Submission.Work.NormalComplement.sec4_prop1_star
import Submission.Work.DoubleTransitivity.App2.app2_5

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Classical
open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.S5K

variable {G : Type} [Group G] [Finite G]

/-! ## General Sylow facts -/

/-- A strict inclusion of subgroups of a finite group gives a strict cardinal inequality. -/
lemma card_lt_card_of_lt {H K : Subgroup G} (h : H < K) : Nat.card ↥H < Nat.card ↥K := by
  have h1 : Nat.card ↥H ≤ Nat.card ↥K := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le h.1)
  rcases lt_or_eq_of_le h1 with h2 | h2
  · exact h2
  · exact absurd (Subgroup.eq_of_le_of_card_ge h.1 (le_of_eq h2.symm)) h.ne

/-- Maximality of a Sylow subgroup, in cardinality form: a `p`-subgroup `Q` of `Y` containing a
Sylow `p`-subgroup `P` of `Y` has `|Q| ≤ |P|`. -/
lemma card_le_card_of_isSylowIn {p : ℕ} (hp : p.Prime) {P Y Q : Subgroup G} (hPY : P ≤ Y)
    (hPp : IsPGroup p P) (hidx : ¬ p ∣ P.relIndex Y) (hQY : Q ≤ Y) (hQp : IsPGroup p Q)
    (hPQ : P ≤ Q) : Nat.card ↥Q ≤ Nat.card ↥P := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := p) (G := ↥Q)).mp hQp
  have h1 : Nat.card ↥P * P.relIndex Y = Nat.card ↥Y := by
    rw [mul_comm]
    exact Work.NormalComplement.relIndex_mul_card_of_le' hPY
  have hdvd : p ^ j ∣ Nat.card ↥P * P.relIndex Y := by
    rw [h1, ← hj]
    exact Subgroup.card_dvd_of_le hQY
  have hcop : Nat.Coprime (p ^ j) (P.relIndex Y) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hidx |>.pow_left j
  have hdvdP : p ^ j ∣ Nat.card ↥P := hcop.dvd_of_dvd_mul_right hdvd
  rw [hj]
  exact Nat.le_of_dvd Nat.card_pos hdvdP

/-- The image in `G` of the normalizer in `S` of `H.subgroupOf S` (`H ≤ S`) is `S ⊓ N_G(H)`. -/
lemma map_normalizer_subgroupOf (H S : Subgroup G) (hHS : H ≤ S) :
    (Subgroup.normalizer (((H.subgroupOf S : Subgroup ↥S) : Set ↥S))).map S.subtype =
      S ⊓ Subgroup.normalizer (H : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro h
    constructor
    · intro hh
      have h1 : (⟨h, hHS hh⟩ : ↥S) ∈ H.subgroupOf S := Subgroup.mem_subgroupOf.mpr hh
      have h2 := (hy _).mp h1
      rw [Subgroup.mem_subgroupOf] at h2
      simpa using h2
    · intro hh
      have hhS : h ∈ S := by
        have h1 : y⁻¹ * (y * h * y⁻¹) * y ∈ S :=
          S.mul_mem (S.mul_mem (S.inv_mem y.2) (hHS hh)) y.2
        have h2 : y⁻¹ * (y * h * y⁻¹) * y = h := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rwa [h2] at h1
      have h1 : (⟨h, hhS⟩ : ↥S) ∈ H.subgroupOf S := by
        refine (hy _).mpr ?_
        rw [Subgroup.mem_subgroupOf]
        simpa using hh
      exact Subgroup.mem_subgroupOf.mp h1
  · intro hx
    obtain ⟨hxS, hxN⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxS⟩, ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro z
    constructor
    · intro hz
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      exact (hxN _).mp hz
    · intro hz
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      exact (hxN _).mpr hz

/-- **A `p`-Sylow subgroup of `X ⊓ N_G(P)` is a `p`-Sylow subgroup of `X`.** -/
lemma isSylowIn_of_isSylowIn_normalizer {p : ℕ} (hp : p.Prime) {P X : Subgroup G}
    (h : Work.NormalComplement.IsSylowIn p P (X ⊓ Subgroup.normalizer (P : Set G))) :
    Work.NormalComplement.IsSylowIn p P X := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hPp, hPle, hidx⟩ := h
  have hPleX : P ≤ X := hPle.trans inf_le_left
  set Y : Subgroup G := X ⊓ Subgroup.normalizer (P : Set G) with hY
  have hPY : P ≤ Y := hPle
  -- a Sylow `S` of `X` containing `P`
  have hsub : IsPGroup p (P.subgroupOf X) :=
    IsPGroup.of_injective hPp (Subgroup.subgroupOfEquivOfLe hPleX).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPleX).injective
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hsub
  set S : Subgroup G := (Q : Subgroup ↥X).map X.subtype with hS
  have hS_le : S ≤ X := Subgroup.map_subtype_le _
  have hSp : IsPGroup p S := Q.isPGroup'.map X.subtype
  have hPS : P ≤ S := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hPleX hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hSidx : ¬ p ∣ S.relIndex X := by
    have heq : S.relIndex X = (Q : Subgroup ↥X).index := by
      have h1 : S.subgroupOf X = (Q : Subgroup ↥X) := by
        ext z
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
        constructor
        · rintro ⟨w, hw, hwz⟩
          exact (Subtype.ext hwz.symm) ▸ hw
        · intro hz
          exact ⟨z, hz, rfl⟩
      exact congrArg Subgroup.index h1
    rw [heq]
    exact Q.not_dvd_index
  refine ⟨hPp, hPleX, ?_⟩
  have htower : P.relIndex S * S.relIndex X = P.relIndex X :=
    Subgroup.relIndex_mul_relIndex P S X hPS hS_le
  have hPSrel : ¬ p ∣ P.relIndex S := by
    intro hcon
    have hPSne : P ≠ S := by
      intro heq
      rw [heq, Subgroup.relIndex_self] at hcon
      exact hp.not_dvd_one hcon
    have hlt : P.subgroupOf S < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro heq
      have heq' : S ≤ P := Subgroup.subgroupOf_eq_top.mp heq
      exact hPSne (le_antisymm hPS heq')
    haveI : Group.IsNilpotent ↥S := IsPGroup.isNilpotent hSp
    have hnc : NormalizerCondition ↥S := Group.normalizerCondition_of_isNilpotent
    set Nn : Subgroup ↥S := Subgroup.normalizer ((P.subgroupOf S : Subgroup ↥S) : Set ↥S) with hNn
    have hne : Nn ≠ P.subgroupOf S := by
      intro heq
      have hself : Subgroup.normalizer ((P.subgroupOf S : Subgroup ↥S) : Set ↥S) = P.subgroupOf S :=
        heq
      exact hlt.ne ((normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) _
        hself)
    have hlt2 : P.subgroupOf S < Nn := lt_of_le_of_ne Subgroup.le_normalizer (Ne.symm hne)
    have hcard_lt : Nat.card ↥(P.subgroupOf S) < Nat.card ↥Nn := card_lt_card_of_lt hlt2
    have hcardP : Nat.card ↥(P.subgroupOf S) = Nat.card ↥P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv
    have hNp : IsPGroup p (Nn.map S.subtype) :=
      (IsPGroup.of_injective hSp Nn.subtype Subtype.coe_injective).map S.subtype
    have hNY : Nn.map S.subtype ≤ Y := by
      have h1 : Nn.map S.subtype = S ⊓ Subgroup.normalizer (P : Set G) := by
        rw [hNn]
        exact map_normalizer_subgroupOf P S hPS
      rw [h1, hY]
      exact le_inf (inf_le_left.trans hS_le) inf_le_right
    have hPN : P ≤ Nn.map S.subtype := by
      have h1 : P.subgroupOf S ≤ Nn := Subgroup.le_normalizer
      calc P = (P.subgroupOf S).map S.subtype := (Subgroup.map_subgroupOf_eq_of_le hPS).symm
        _ ≤ Nn.map S.subtype := Subgroup.map_mono h1
    have hle := card_le_card_of_isSylowIn hp hPY hPp hidx hNY hNp hPN
    have hcardN : Nat.card ↥(Nn.map S.subtype) = Nat.card ↥Nn :=
      Subgroup.card_map_of_injective Subtype.coe_injective
    omega
  show ¬ p ∣ (P.subgroupOf X).index
  intro hcon2
  have hcon2' : p ∣ P.relIndex X := hcon2
  rw [← htower] at hcon2'
  rcases (Nat.Prime.dvd_mul hp).mp hcon2' with h3 | h3
  · exact hPSrel h3
  · exact hSidx h3


/-! ## A fixed-point lemma for actions of `r`-groups

An `r`-group acting on a finite set with cardinality not divisible by `r` has a fixed point: the
class formula writes `|X|` as a sum of orbit sizes, each dividing `|R| = r^k`; without a fixed
point every orbit size is `> 1`, hence divisible by `r`, so `r ∣ |X|`. -/

/-- **A finite `r`-group acting on a finite set of cardinality prime to `r` has a fixed point.**

The orbits partition `X`, each orbit has cardinality dividing `|R|` (orbit-stabiliser), and a
singleton orbit is exactly a fixed point; if there is no fixed point, every orbit has cardinality
`> 1`, hence is divisible by `r`, so `r ∣ |X|` — contradiction. -/
lemma exists_fixedPoint_of_isPGroup {r : ℕ} (hr : r.Prime) {R X : Type*} [Group R] [Finite R]
    [MulAction R X] [Finite X] (hRp : IsPGroup r R) (hX : ¬ r ∣ Nat.card X) :
    ∃ x : X, ∀ g : R, g • x = x := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fintype R := Fintype.ofFinite _
  haveI : Fintype X := Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient R X) := Fintype.ofFinite _
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := r) (G := R)).mp hRp
  by_contra hcon
  push_neg at hcon
  -- the orbits partition `X`
  have hdecomp : Nat.card X =
      ∑ ω : MulAction.orbitRel.Quotient R X, Nat.card ↥(MulAction.orbit R ω.out) := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits R X)]
    exact Nat.card_sigma
  -- each orbit size divides `|R|`
  have hdvd : ∀ ω : MulAction.orbitRel.Quotient R X,
      Nat.card ↥(MulAction.orbit R ω.out) ∣ Nat.card R := by
    intro ω
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group R ω.out
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
    exact ⟨Nat.card ↥(MulAction.stabilizer R ω.out), h.symm⟩
  -- no orbit is a singleton
  have hne : ∀ ω : MulAction.orbitRel.Quotient R X,
      Nat.card ↥(MulAction.orbit R ω.out) ≠ 1 := by
    intro ω hone
    obtain ⟨g₀, hg₀⟩ := hcon ω.out
    have h1 : (MulAction.orbit R ω.out).ncard = 1 := by
      rw [Set.ncard_def]
      exact hone
    rw [Set.ncard_eq_one] at h1
    obtain ⟨y, hy⟩ := h1
    have h2 : g₀ • ω.out ∈ ({y} : Set X) := by
      rw [← hy]
      exact MulAction.mem_orbit ω.out g₀
    have h3 : ω.out ∈ ({y} : Set X) := by
      rw [← hy]
      exact MulAction.mem_orbit_self ω.out
    rw [Set.mem_singleton_iff] at h2 h3
    exact hg₀ (h2.trans h3.symm)
  -- hence `r` divides the sum of the orbit sizes
  have hsum : r ∣ ∑ ω : MulAction.orbitRel.Quotient R X,
      Nat.card ↥(MulAction.orbit R ω.out) := by
    apply Finset.dvd_sum
    intro ω _
    have h1 : Nat.card ↥(MulAction.orbit R ω.out) ∣ r ^ k := by
      rw [← hk]
      exact hdvd ω
    haveI : Nonempty ↥(MulAction.orbit R ω.out) :=
      ⟨⟨ω.out, MulAction.mem_orbit_self ω.out⟩⟩
    have h2 : 1 < Nat.card ↥(MulAction.orbit R ω.out) := by
      have h3 := hne ω
      have h4 : 0 < Nat.card ↥(MulAction.orbit R ω.out) := Nat.card_pos
      omega
    obtain ⟨q, hq, hq1⟩ := Nat.exists_prime_and_dvd h2.ne'
    have hq2 : q ∣ r ^ k := hq1.trans h1
    have hq4 : q ∣ r := hq.dvd_of_dvd_pow hq2
    have hq3 : q = r := by
      rcases (Nat.dvd_prime hr).mp hq4 with h | h
      · exact absurd h hq.ne_one
      · exact h
    rw [← hq3]
    exact hq1
  rw [← hdecomp] at hsum
  exact hX hsum


/-! ## The conjugation action of `N_W(M)` on `M` and the coprime invariant Sylow theorem -/

section InvariantSylow

variable {W : Type} [Group W] [Finite W]

/-- The conjugation homomorphism `R →* MulAut ↥M` induced by `R ≤ N_W(M)`. -/
noncomputable def conjMulAut {M R : Subgroup W} (h : R ≤ Subgroup.normalizer (M : Set W)) :
    ↥R →* MulAut ↥M where
  toFun r :=
    { toFun := fun m => ⟨(r : W) * (m : W) * (r : W)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (h r.2) (m : W)).mp m.2⟩
      invFun := fun m => ⟨(r : W)⁻¹ * (m : W) * (r : W),
        by
          have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (h r.2)) (m : W)).mp m.2
          simpa using h1⟩
      left_inv := by
        intro m
        exact Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group)
      right_inv := by
        intro m
        exact Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group)
      map_mul' := by
        intro m n
        exact Subtype.ext (by
          simp only [Subgroup.coe_mul]
          group) }
  map_one' := by
    ext m
    show (1 : W) * (m : W) * (1 : W)⁻¹ = (m : W)
    simp
  map_mul' := by
    intro a b
    ext m
    show (↑(a * b) : W) * (m : W) * (↑(a * b) : W)⁻¹ =
      (↑a : W) * ((↑b : W) * (m : W) * (↑b : W)⁻¹) * (↑a : W)⁻¹
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

/-- A `p`-subgroup `Q` of a subgroup `M` is contained in a Sylow `p`-subgroup of `M`. -/
lemma exists_sylow_ge {p : ℕ} (hp : p.Prime) {M Q : Subgroup W} (hQM : Q ≤ M)
    (hQp : IsPGroup p Q) :
    ∃ S : Subgroup W, IsPGroup p S ∧ Q ≤ S ∧ S ≤ M ∧ ¬ p ∣ (S.subgroupOf M).index := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hsub : IsPGroup p (Q.subgroupOf M) :=
    IsPGroup.of_injective hQp (Subgroup.subgroupOfEquivOfLe hQM).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQM).injective
  obtain ⟨S₀, hS₀⟩ := IsPGroup.exists_le_sylow hsub
  have hS₀idx : ¬ p ∣ (S₀ : Subgroup ↥M).index := S₀.not_dvd_index
  refine ⟨(S₀ : Subgroup ↥M).map M.subtype, S₀.isPGroup'.map M.subtype, ?_,
    Subgroup.map_subtype_le _, ?_⟩
  · intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hQM hx⟩, hS₀ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · have heq : ((S₀ : Subgroup ↥M).map M.subtype).subgroupOf M = (S₀ : Subgroup ↥M) := by
      ext z
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨w, hw, hwz⟩
        exact (Subtype.ext hwz.symm) ▸ hw
      · intro hz
        exact ⟨z, hz, rfl⟩
    rw [heq]
    exact hS₀idx

/-- **`R`-invariant Sylow subgroups for a coprime action of an `r`-group.**  Let `Q ≤ M` be
subgroups of a finite group `W` with `Q ⊴ M` (encoded as `M ≤ N_W(Q)`), and let `R ≤ W` be an
`r`-group with `R ≤ N_W(M)`, `R ≤ N_W(Q)` and `|R|` coprime to `|M|`.  Then `Q` is contained in
an `R`-invariant Sylow `p`-subgroup `S ≤ M` of `M`. -/
theorem exists_invariant_sylow_of_coprime {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    {M R Q : Subgroup W} (hQ : Q ≤ M) (hQp : IsPGroup p Q)
    (hQnorm : M ≤ Subgroup.normalizer (Q : Set W))
    (hRM : R ≤ Subgroup.normalizer (M : Set W))
    (hRQ : R ≤ Subgroup.normalizer (Q : Set W))
    (hRp : IsPGroup r R) (hcop : Nat.Coprime (Nat.card R) (Nat.card M)) :
    ∃ S : Subgroup W, IsPGroup p S ∧ Q ≤ S ∧ S ≤ M ∧
      R ≤ Subgroup.normalizer (S : Set W) ∧ ¬ p ∣ (S.subgroupOf M).index := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  by_cases hR : R = ⊥
  · obtain ⟨S, h1, h2, h3, h4⟩ := exists_sylow_ge hp hQ hQp
    exact ⟨S, h1, h2, h3, by rw [hR]; exact bot_le, h4⟩
  · -- `r ∣ |R|`, hence `r ∤ |M|`
    have hdvdR : r ∣ Nat.card R := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := r) (G := R)).mp hRp
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        exact hR (Subgroup.card_eq_one.mp hk)
      rw [hk]
      exact dvd_pow_self r hk0
    have hdvdM : ¬ r ∣ Nat.card ↥M := by
      intro hcon
      have h1 : r ∣ Nat.gcd (Nat.card R) (Nat.card ↥M) := Nat.dvd_gcd hdvdR hcon
      rw [hcop] at h1
      exact hr.not_dvd_one h1
    -- the conjugation action of `R` on the Sylow `p`-subgroups of `M`, described as
    -- the subgroups `S ≤ ↥M` with `IsPGroup p S` and `¬ p ∣ S.index`
    obtain ⟨T₀⟩ := Sylow.nonempty (p := p) (G := ↥M)
    have hcard_dvd : Nat.card (Sylow p ↥M) ∣ Nat.card ↥M := by
      let N : Subgroup ↥M := Subgroup.normalizer ((T₀ : Subgroup ↥M) : Set ↥M)
      have hN : Nat.card (Sylow p ↥M) = N.index := Sylow.card_eq_index_normalizer T₀
      rw [hN]
      exact ⟨Nat.card ↥N, (Subgroup.index_mul_card N).symm⟩
    set Y : Type := {S : Subgroup ↥M // IsPGroup p S ∧ ¬ p ∣ S.index} with hYdef
    haveI : Fintype Y := Fintype.ofFinite _
    have hequiv : Y ≃ Sylow p ↥M :=
      { toFun := fun S => IsPGroup.toSylow (P := S.1) S.2.1 S.2.2
        invFun := fun S => ⟨(S : Subgroup ↥M), S.isPGroup', S.not_dvd_index⟩
        left_inv := by
          intro S
          exact Subtype.ext rfl
        right_inv := by
          intro S
          exact Sylow.ext rfl }
    have hcardY : Nat.card Y = Nat.card (Sylow p ↥M) := Nat.card_congr hequiv
    have hnotdvd : ¬ r ∣ Nat.card Y := by
      rw [hcardY]
      exact fun hcon => hdvdM (hcon.trans hcard_dvd)
    -- the action
    have hidx_map : ∀ (S : Subgroup ↥M) (r : ↥R), (S.map (conjMulAut hRM r).toMonoidHom).index =
        S.index := by
      intro S r
      have h1 := Subgroup.relIndex_map_map_of_injective (f := (conjMulAut hRM r).toMonoidHom)
        S ⊤ (conjMulAut hRM r).injective
      simpa using h1
    letI hAct : MulAction ↥R Y :=
      { smul := fun r S => ⟨S.1.map (conjMulAut hRM r).toMonoidHom, S.2.1.map _, by
          rw [hidx_map S.1 r]
          exact S.2.2⟩
        one_smul := by
          intro S
          apply Subtype.ext
          show S.1.map (conjMulAut hRM 1).toMonoidHom = S.1
          rw [map_one]
          exact Subgroup.map_id S.1
        mul_smul := by
          intro a b S
          apply Subtype.ext
          show S.1.map (conjMulAut hRM (a * b)).toMonoidHom =
            (S.1.map (conjMulAut hRM b).toMonoidHom).map (conjMulAut hRM a).toMonoidHom
          rw [map_mul, Subgroup.map_map]
          rfl }
    obtain ⟨S₁, hS₁⟩ := exists_fixedPoint_of_isPGroup hr hRp hnotdvd
    -- the corresponding subgroup of `W`
    set S : Subgroup W := (S₁.1 : Subgroup ↥M).map M.subtype with hSdef
    have hSp : IsPGroup p S := S₁.2.1.map M.subtype
    have hSle : S ≤ M := Subgroup.map_subtype_le _
    have hSidx : ¬ p ∣ (S.subgroupOf M).index := by
      have heq : S.subgroupOf M = (S₁.1 : Subgroup ↥M) := by
        rw [hSdef]
        ext z
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
        constructor
        · rintro ⟨w, hw, hwz⟩
          exact (Subtype.ext hwz.symm) ▸ hw
        · intro hz
          exact ⟨z, hz, rfl⟩
      rw [heq]
      exact S₁.2.2
    -- `Q ≤ S`: `Q` is a normal `p`-subgroup of `M`, hence lies in every Sylow of `M`
    have hQS : Q ≤ S := by
      have hnorm : S ≤ Subgroup.normalizer (Q : Set W) := hSle.trans hQnorm
      have hQSup : IsPGroup p ↥(S ⊔ Q) :=
        IsPGroup.to_sup_of_normal_right' (p := p) (H := S) (K := Q) hSp hQp hnorm
      have hle : S ⊔ Q ≤ M := sup_le hSle hQ
      have hmax := card_le_card_of_isSylowIn hp hSle hSp hSidx hle hQSup le_sup_left
      have heq : S = S ⊔ Q := Subgroup.eq_of_le_of_card_ge le_sup_left hmax
      intro x hx
      rw [heq]
      exact Subgroup.mem_sup_right hx
    -- `R` normalises `S`
    have hfixSub : ∀ r' : ↥R, S₁.1.map (conjMulAut hRM r').toMonoidHom = S₁.1 := fun r' =>
      congrArg (fun U : Y => (U.1 : Subgroup ↥M)) (hS₁ r')
    have hRS : R ≤ Subgroup.normalizer (S : Set W) := by
      intro r hr
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.mp hx
        refine Subgroup.mem_map.mpr ⟨(conjMulAut hRM ⟨r, hr⟩) t, ?_, ?_⟩
        · rw [← hfixSub ⟨r, hr⟩]
          exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
        · have hcoe : M.subtype ((conjMulAut hRM ⟨r, hr⟩) t) =
              r * M.subtype t * r⁻¹ := rfl
          rw [hcoe, htx]
      · intro hx
        obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.mp hx
        refine Subgroup.mem_map.mpr ⟨(conjMulAut hRM ⟨r⁻¹, R.inv_mem hr⟩) t, ?_, ?_⟩
        · rw [← hfixSub ⟨r⁻¹, R.inv_mem hr⟩]
          exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
        · have hcoe : M.subtype ((conjMulAut hRM ⟨r⁻¹, R.inv_mem hr⟩) t) =
              r⁻¹ * M.subtype t * (r⁻¹)⁻¹ := rfl
          rw [hcoe, htx]
          group
    exact ⟨S, hSp, hQS, hSle, hRS, hSidx⟩

end InvariantSylow


/-! ## Step 3, first bullet: an `R`-invariant `p`-subgroup `P ⊊ P₁ ≤ N_H(P)` -/

variable {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}

/-- **Peterfalvi I Ch. III §4 Prop. 1, step 3, first bullet** (p.180).  Let `h : Setup45A`,`hPsyl : IsSylowIn p P (twoPoint H t)`, `h1 : Step1Conc H t p P A` (so `C = C_A(P)` is Hall in
`W' = N_H(P) = H ⊓ N_G(P)` with normal complement `N`), `h2 : Step2Conc`, and let `R` be a
nontrivial Sylow `r`-subgroup of `C_A(P)`.  Then `N` is a normal subgroup of `W'` of order prime to
`R`, `P ≤ N`, and (coprime-action Sylow theorem, `exists_invariant_sylow_of_coprime`) there is a
Sylow `p`-subgroup `P₁` of `N` containing `P` and normalised by `R`.  Since `P` is not a `p`-Sylow
of `H` (step 2), `P` is not a Sylow of `N` either, so `P₁ ⊋ P`. -/
theorem exists_pSubgroup_normalized (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (hPsyl : Work.NormalComplement.IsSylowIn p P (Submission.Blueprint.twoPoint H t))
    (h1 : Work.NormalComplement.S5K.Step1Conc H t p P A)
    (h2 : Work.NormalComplement.S5K.Step2Conc H t p P A) {r : ℕ} (hr : r.Prime) {R : Subgroup G}
    (hRp : Work.NormalComplement.IsSylowIn r R (A ⊓ Subgroup.centralizer (P : Set G)))
    (hRne : R ≠ ⊥) :
    ∃ P₁ : Subgroup G, IsPGroup p P₁ ∧ P ≤ P₁ ∧
      P₁ ≤ H ⊓ Subgroup.normalizer (P : Set G) ∧
      R ≤ Subgroup.normalizer (P₁ : Set G) ∧ ∃ x ∈ P₁, x ∉ P := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨hcopHC, N, hNle, hNW, hNbot, hNsup⟩ := h1
  set C : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G) with hC
  set W' : Subgroup G := H ⊓ Subgroup.normalizer (P : Set G) with hW'
  have hCle : C ≤ W' := by
    refine le_inf ?_ ?_
    · exact inf_le_left.trans (h.A_le.trans (inf_le_left.trans inf_le_left))
    · exact inf_le_right.trans (Subgroup.centralizer_le_normalizer (P : Set G))
  have hcardW' : Nat.card ↥W' = Nat.card ↥N * Nat.card ↥C := by
    have h3 := Work.NormalComplement.card_sup_mul_card_inf (H := N) (K := C) (hCle.trans hNW)
    rw [hNsup, hNbot, Subgroup.card_bot, mul_one] at h3
    exact h3
  have hCcop : Nat.Coprime (Nat.card ↥C) (Nat.card ↥N) := by
    have hrel : C.relIndex W' = Nat.card ↥N := by
      have h1' := Work.NormalComplement.relIndex_mul_card_of_le' hCle
      rw [hcardW'] at h1'
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h1', mul_comm])
    rw [← hrel]
    exact hcopHC
  have hRC : R ≤ C := hRp.2.1
  have hRcopN : Nat.Coprime (Nat.card ↥R) (Nat.card ↥N) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hRC) hCcop
  have hpC : ¬ p ∣ Nat.card ↥C := Work.NormalComplement.S5K.not_dvd_p_card_CA h hPsyl
  have hPleW : P ≤ W' := by
    refine le_inf ?_ ?_
    · exact h.P_le.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
    · exact Subgroup.le_normalizer
  have hPN : P ≤ N := by
    haveI : (N.subgroupOf W').Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr hNW
    intro x hxP
    have hxW : x ∈ W' := hPleW hxP
    have hxWpow : (⟨x, hxW⟩ : ↥W') ^ p = 1 := by
      refine Subtype.ext ?_
      show x ^ p = ((1 : ↥W') : G)
      rw [Subgroup.coe_one]
      exact orderOf_dvd_iff_pow_eq_one.mp
        ((Subgroup.orderOf_dvd_natCard P hxP).trans (by rw [h.P_card]))
    have hcardQuot : Nat.card (↥W' ⧸ N.subgroupOf W') = Nat.card ↥C := by
      have h1 : (N.subgroupOf W').index = Nat.card ↥W' / Nat.card ↥(N.subgroupOf W') :=
        Subgroup.index_eq_card_div _
      have h2 : Nat.card ↥(N.subgroupOf W') = Nat.card ↥N :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv
      have h3 : Nat.card (↥W' ⧸ N.subgroupOf W') = (N.subgroupOf W').index := rfl
      rw [h3, h1, h2, hcardW', Nat.mul_div_cancel_left _ Nat.card_pos]
    have hord : orderOf (QuotientGroup.mk' (N.subgroupOf W') ⟨x, hxW⟩) ∣ p := by
      refine orderOf_dvd_iff_pow_eq_one.mpr ?_
      rw [← map_pow, hxWpow, map_one]
    have hord2 : orderOf (QuotientGroup.mk' (N.subgroupOf W') ⟨x, hxW⟩) ∣ Nat.card ↥C := by
      rw [← hcardQuot]
      have hh := Subgroup.orderOf_dvd_natCard
        (⊤ : Subgroup (↥W' ⧸ N.subgroupOf W'))
        (Subgroup.mem_top (QuotientGroup.mk' (N.subgroupOf W') ⟨x, hxW⟩))
      simpa using hh
    have hgcd : Nat.gcd p (Nat.card ↥C) = 1 :=
      Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd h.prime).mpr hpC)
    have h1 : orderOf (QuotientGroup.mk' (N.subgroupOf W') ⟨x, hxW⟩) = 1 := by
      have h2 : orderOf (QuotientGroup.mk' (N.subgroupOf W') ⟨x, hxW⟩) ∣ 1 := by
        rw [← hgcd]
        exact Nat.dvd_gcd hord hord2
      exact Nat.dvd_one.mp h2
    have h3 : QuotientGroup.mk' (N.subgroupOf W') ⟨x, hxW⟩ = 1 := orderOf_eq_one_iff.mp h1
    have h4 : (⟨x, hxW⟩ : ↥W') ∈ N.subgroupOf W' := (QuotientGroup.eq_one_iff _).mp h3
    exact Subgroup.mem_subgroupOf.mp h4
  obtain ⟨P₁, hP₁p, hPP₁, hP₁N, hP₁R, hP₁syl⟩ :=
    exists_invariant_sylow_of_coprime h.prime hr hPN hPsyl.1
      (hNle.trans inf_le_right)
      (hRC.trans (hCle.trans hNW))
      (hRC.trans (le_trans inf_le_right (Subgroup.centralizer_le_normalizer (P : Set G))))
      hRp.1 hRcopN
  refine ⟨P₁, hP₁p, hPP₁, hP₁N.trans hNle, hP₁R, ?_⟩
  -- `P₁ ≠ P`: otherwise `P` would be a Sylow `p`-subgroup of `N`, hence of `W'`, hence of `H`,
  -- contradicting step 2 (`h2`).
  by_contra hcon
  push_neg at hcon
  have hPeq : P₁ = P := le_antisymm hcon hPP₁
  have hCne : C ≠ ⊥ := fun hc => hRne (le_bot_iff.mp (hc ▸ hRC))
  have hPsylN : ¬ p ∣ P.relIndex N := by
    have hh := hP₁syl
    rw [hPeq] at hh
    exact hh
  have hNcard : Nat.card ↥N = P.relIndex N * p := by
    rw [← Work.NormalComplement.relIndex_mul_card_of_le' hPN, h.P_card]
  have hW'card : Nat.card ↥W' = P.relIndex W' * p := by
    rw [← Work.NormalComplement.relIndex_mul_card_of_le' hPleW, h.P_card]
  have hrel : P.relIndex W' = P.relIndex N * Nat.card ↥C := by
    have h1 : P.relIndex W' * p = (P.relIndex N * Nat.card ↥C) * p := by
      rw [← hW'card, hcardW', hNcard]; ring
    exact Nat.eq_of_mul_eq_mul_right h.prime.pos h1
  have hPsylW' : ¬ p ∣ P.relIndex W' := by
    rw [hrel]
    intro hd
    rcases (Nat.Prime.dvd_mul h.prime).mp hd with hh | hh
    · exact hPsylN hh
    · exact hpC hh
  have hSylH : Work.NormalComplement.IsSylowIn p P H :=
    isSylowIn_of_isSylowIn_normalizer h.prime (X := H)
      (hW' ▸ ⟨hPsyl.1, hPleW, hPsylW'⟩)
  exact h2 hCne hSylH

end Work.NormalComplement.S5K
