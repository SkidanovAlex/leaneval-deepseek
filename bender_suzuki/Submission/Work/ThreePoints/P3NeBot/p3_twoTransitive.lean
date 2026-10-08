import Mathlib
import Submission.Work.ThreePoints.P3NeBot.Basic
import Submission.Work.ThreePoints.P3NeBot.p3_lemma1
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_unconditional
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_nofour
import Submission.Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz
import Submission.Work.ThreePoints.F1EqF.prop2c_of_even
import Submission.Work.ThreePoints.P3Sub.ch1s4_prop1
import Submission.Work.ThreePoints.Omega
import Submission.Work.DoubleTransitivity.Sec4.lemma2_part1
import Submission.Work.DoubleTransitivity.Sec4.not_rp_twoTransitive
import Submission.Work.DoubleTransitivity.Sec4.rp_no_two_fixed_pts
import Submission.Work.DoubleTransitivity.App1.isSylowSubgroupOf_map_subtype

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Work.ThreePoints.P3NeBot

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Elementary facts about the action of `F₁ = ⟨Inv C_G(X)⟩` on `Ω_X`

Throughout, `H` is a strongly embedded subgroup of the finite group `G`, `t ∉ H` is an involution,
`X ≠ ⊥` with `X ≤ V = C_D(t)` (`D = H ⊓ H^t = twoPoint H t`), and `F₁ = ⟨Inv C_G(X)⟩`.
The set `Ω_X = fixedPts H X` is the set of conjugates of `H` containing `X`.
## 2. The two remaining inputs

What is still missing for `p3_twoTransitive` is (in the vocabulary of this file):

* **(Prop. 1 (a))** `Even |M ⊓ C_G(X)|` for every `M ∈ fixedPts H X` with `X ≤ M` (Peterfalvi I
  Ch. II §4 Prop. 1 (a), p. 168).  In the workspace this is `P3NeBot.prop1a_brsz`'s statement,
  whose only unproved input is `s4prop2_input` (`HasFourGroup F` case:
  `Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup`; 2-rank-1 case open).
* **(Prop. 1)** Ch. I §4 Prop. 1 (pp. 154–157): a `p`-subgroup (`p ≠ 2`) with exactly two fixed
  points forces 2-transitivity.  For the groups with a four-group this is Theorem A (`hA`); the
  2-rank-1 case is the source's `R_p = ∅` analysis (§3 Prop. 1 + §4 Lemmas 1–2 + App. II (1),(4)).

Given both, the proof of `p3_twoTransitive` is: (1) `Even |F₁ ⊓ M|` for `M ∈ Ω_X` (transfer of
evenness from `C_G(X)` to `F₁ = ⟨Inv C_G(X)⟩`); (2) `H₁ = F₁ ⊓ H` is strongly embedded in `F₁`
(Ch. II §4 Prop. 1 (b), via `Work.ThreePoints.stronglyEmbedded_subgroupOf_inf_conj`); (3) `F₁` is
transitive on `Ω_X` and `Ω_X ≅ F₁ ⧸ H₁` (Ch. I §2 Lemma 2, using (1)); (4) `k ∈ F₁ ⊓ K` has
exactly two fixed points on `Ω_X` (Prop. 2 (c)); (5) Ch. I §4 Prop. 1 applied to `↥F₁` with
`K := H₁` and `P := ⟨k⟩` gives 2-transitivity of `F₁` on `F₁ ⧸ H₁`, transported back along the
bijection of (3). -/

/-- The fixed point of an involution of `F₁` in `Ω = G ⧸ H` lies in `Ω_X`: for `u ∈ F₁` of order
two, `X ≤ C_G(u) ≤ Stab(ω_u)`. -/
theorem exists_fixedPts_of_involution_mem_p3F1 {H : Subgroup G}
    (hH : IsStronglyEmbedded H) {X : Subgroup G} {u : G} (hu : u ∈ p3F1 X)
    (hu2 : orderOf u = 2) :
    ∃ ω : G ⧸ H, ω ∈ fixedPts H X ∧ u • ω = ω := by
  have huC : u ∈ Subgroup.centralizer (X : Set G) := p3F1_le_centralizer X hu
  have hXC : X ≤ Subgroup.centralizer ({u} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp huC x hx
  obtain ⟨ω, hω⟩ := Set.ncard_eq_one.mp (Work.ThreePoints.ncard_fixedPts_zpowers hH hu2)
  have hfix : u • ω = ω := by
    have hmem : ω ∈ fixedPts H (Subgroup.zpowers u) := by rw [hω]; exact Set.mem_singleton ω
    exact mem_fixedPts.mp hmem u (Subgroup.mem_zpowers u)
  refine ⟨ω, ?_, hfix⟩
  rw [mem_fixedPts_iff_le_stabilizer]
  exact hXC.trans (centralizer_le_stabilizer hH hu2 hfix)

/-- `Ω_X` contains the three distinct points `H`, `H^t` and the point `H(t)` fixed by `t`, for
any `X ≤ V = C_D(t)`. -/
theorem three_le_ncard_fixedPts_of_le_centD {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX : X ≤ centD H t) :
    3 ≤ (fixedPts H X).ncard := by
  classical
  have hXH : X ≤ H := hX.trans (by rw [centD_eq]; exact le_trans inf_le_left inf_le_left)
  have hXt : X ≤ conj t H := hX.trans (by rw [centD_eq]; exact le_trans inf_le_left inf_le_right)
  have hXC : X ≤ Subgroup.centralizer ({t} : Set G) :=
    hX.trans (by rw [centD_eq]; exact inf_le_right)
  have hmem1 : ((1 : G) : G ⧸ H) ∈ fixedPts H X := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, DoubleTransitivity.conj_one]
    exact hXH
  have hmemt : ((t : G) : G ⧸ H) ∈ fixedPts H X := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
    exact hXt
  obtain ⟨ω, hω⟩ := Set.ncard_eq_one.mp (Work.ThreePoints.ncard_fixedPts_zpowers hH ht)
  have htω : t • ω = ω := by
    have hmem : ω ∈ fixedPts H (Subgroup.zpowers t) := by rw [hω]; exact Set.mem_singleton ω
    exact mem_fixedPts.mp hmem t (Subgroup.mem_zpowers t)
  have hmemω : ω ∈ fixedPts H X := by
    rw [mem_fixedPts_iff_le_stabilizer]
    exact hXC.trans (centralizer_le_stabilizer hH ht htω)
  have h1t : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
    intro hcon
    rw [QuotientGroup.eq] at hcon
    exact htH (by simpa using hcon)
  have h1ω : ((1 : G) : G ⧸ H) ≠ ω := by
    intro hcon
    have hmem : t • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by rw [hcon]; exact htω
    rw [DoubleTransitivity.smul_mk_eq_mk_iff, DoubleTransitivity.mem_conj] at hmem
    exact htH (by simpa using hmem)
  have htω' : ((t : G) : G ⧸ H) ≠ ω := by
    intro hcon
    have hmem : t • ((t : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by rw [hcon]; exact htω
    rw [DoubleTransitivity.smul_mk_eq_mk_iff, DoubleTransitivity.mem_conj] at hmem
    rw [inv_mul_cancel, one_mul] at hmem
    exact htH hmem
  have hsub : ({((1 : G) : G ⧸ H), ((t : G) : G ⧸ H), ω} : Set (G ⧸ H)) ⊆ fixedPts H X := by
    intro y hy
    rcases hy with h | h | h
    · rw [h]; exact hmem1
    · rw [h]; exact hmemt
    · rw [h]; exact hmemω
  have hcard : ({((1 : G) : G ⧸ H), ((t : G) : G ⧸ H), ω} : Set (G ⧸ H)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨h1t, h1ω⟩),
        Set.ncard_insert_of_notMem (by
          simp only [Set.mem_singleton_iff]; exact htω'),
        Set.ncard_singleton]
  calc 3 = ({((1 : G) : G ⧸ H), ((t : G) : G ⧸ H), ω} : Set (G ⧸ H)).ncard := hcard.symm
    _ ≤ (fixedPts H X).ncard := Set.ncard_le_ncard hsub

/-- `N_G(X)` (hence `F₁`) preserves `Ω_X`. -/
theorem normalizer_preserves_fixedPts {H X : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (X : Set G)) {ω : G ⧸ H} (hω : ω ∈ fixedPts H X) :
    h • ω ∈ fixedPts H X := by
  rw [mem_fixedPts] at hω ⊢
  intro x hx
  have hxh : h⁻¹ * x * h ∈ X := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) x).mp hx
  calc x • (h • ω) = (x * h) • ω := by rw [mul_smul]
    _ = (h * (h⁻¹ * x * h)) • ω := by rw [show x * h = h * (h⁻¹ * x * h) from by group]
    _ = h • ((h⁻¹ * x * h) • ω) := by rw [mul_smul]
    _ = h • ω := by rw [hω _ hxh]

/-! ## 3. Peterfalvi I Ch. I §4 Prop. 1: the `R_p ≠ ∅` half

The source's Ch. I §4 Prop. 1 (p. 156) reads: `R_p = ∅` iff there is a `p`-subgroup with exactly
two fixed points on `Ω`; and `R_p = ∅` implies that `G` is 2-transitive on `Ω`.  Here `𝒟` is the
set of two-point stabilisers `K ⊓ K^x` (`K^x ≠ K`), and `(D,K') ∈ R_p` means that some `p`-Sylow
`P` of `D` has `|N(P) ⊓ K'|` even (`Work.DoubleTransitivity.IsRegularIntersection`).

The *easy half* of this is the statement below: an even normaliser forces `P` itself to have at
least three fixed points.  Consequently, if `R_p ≠ ∅` then there is a `p`-subgroup with at least
three fixed points. -/

/-- **Peterfalvi I Ch. I §4 Prop. 1 (easy half).**  Let `K ≤ G` be strongly embedded and let
`D = K ⊓ conj g K` be the odd-order stabiliser of the two points `K`, `conj g K` of `Ω = G ⧸ K`
(`g ∉ K`).  If a `p`-Sylow `P` of `D` (`p ≠ 2`) is normalised by an involution of `K` —
equivalently, `|N_G(P) ⊓ K|` is even — then `P` has at least three fixed points on `Ω`.

Indeed, an involution `u ∈ N_G(P) ⊓ K` fixes the point `K` and permutes `Fix(P)`, which contains
`K` and `conj g K`; if `Fix(P)` were exactly this pair, then `u` would also fix `conj g K`, so
`u ∈ K ⊓ conj g K = D`, of odd order — a contradiction. -/
theorem three_le_ncard_fixedPts_of_pSylow_normalizer_even {G : Type} [Group G] [Finite G]
    {K : Subgroup G} (hK : IsStronglyEmbedded K) {g : G} (hg : g ∉ K)
    {p : ℕ} (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : Work.DoubleTransitivity.IsSylowSubgroupOf p P (K ⊓ conj g K))
    (heven : Even (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ K : Subgroup G))) :
    3 ≤ (fixedPts K P).ncard := by
  classical
  -- `D = K ⊓ conj g K` is the stabiliser of the two points `K`, `conj g K`, and has odd order.
  have hconjne : conj (1 : G) K ≠ conj g K := by
    intro hcon
    have hgN : g ∈ Subgroup.normalizer (K : Set G) :=
      (DoubleTransitivity.conj_eq_self_iff_mem_normalizer g K).mp
        (hcon.symm.trans (DoubleTransitivity.conj_one K))
    rw [IsStronglyEmbedded.normalizer_eq hK] at hgN
    exact hg hgN
  have hDodd : Odd (Nat.card (K ⊓ conj g K : Subgroup G)) := by
    simpa [DoubleTransitivity.conj_one] using Work.ThreePoints.card_inf_conj_odd hK hconjne
  have hPK : P ≤ K := hP.1.trans inf_le_left
  have hPg : P ≤ conj g K := hP.1.trans inf_le_right
  have hfix1 : ((1 : G) : G ⧸ K) ∈ fixedPts K P := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, DoubleTransitivity.conj_one]
    exact hPK
  have hfixg : ((g : G) : G ⧸ K) ∈ fixedPts K P := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
    exact hPg
  have hpt : ((1 : G) : G ⧸ K) ≠ ((g : G) : G ⧸ K) := by
    intro hcon
    rw [QuotientGroup.eq] at hcon
    exact hg (by simpa using hcon)
  by_contra hlt
  push_neg at hlt
  -- at least two fixed points, at most two: exactly two, namely `K` and `conj g K`.
  have hsub : ({((1 : G) : G ⧸ K), ((g : G) : G ⧸ K)} : Set (G ⧸ K)) ⊆ fixedPts K P := by
    intro y hy
    rcases hy with h | h
    · rw [h]; exact hfix1
    · rw [h]; exact hfixg
  have h2 : (fixedPts K P).ncard = 2 := by
    have hge : 2 ≤ (fixedPts K P).ncard := by
      calc 2 = ({((1 : G) : G ⧸ K), ((g : G) : G ⧸ K)} : Set (G ⧸ K)).ncard :=
            (Set.ncard_pair hpt).symm
        _ ≤ (fixedPts K P).ncard := Set.ncard_le_ncard hsub
    omega
  have hEq : fixedPts K P = ({((1 : G) : G ⧸ K), ((g : G) : G ⧸ K)} : Set (G ⧸ K)) :=
    (Set.eq_of_subset_of_ncard_le hsub (by rw [h2, Set.ncard_pair hpt])).symm
  -- an involution `u` normalising `P` inside `K`
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  have huN : (u : G) ∈ Subgroup.normalizer (P : Set G) := (Subgroup.mem_inf.mp u.2).1
  have huK : (u : G) ∈ K := (Subgroup.mem_inf.mp u.2).2
  have hu2 : orderOf (u : G) = 2 := (Subgroup.orderOf_coe u).trans hu
  -- `u` fixes the point `K`
  have hu1 : (u : G) • ((1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) := by
    rw [DoubleTransitivity.smul_mk_eq_mk_iff, DoubleTransitivity.conj_one]
    exact huK
  -- `u` permutes `Fix(P)`
  have hperm : ∀ ω ∈ fixedPts K P, (u : G) • ω ∈ fixedPts K P := by
    intro ω hω
    rw [mem_fixedPts] at hω ⊢
    intro y hy
    have hy' : (u : G)⁻¹ * y * (u : G) ∈ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huN) y).mp hy
    have hy'' : ((u : G)⁻¹ * y * (u : G)) • ω = ω := hω _ hy'
    calc y • ((u : G) • ω) = (y * (u : G)) • ω := by rw [mul_smul]
      _ = ((u : G) * ((u : G)⁻¹ * y * (u : G))) • ω := by
            rw [show y * (u : G) = (u : G) * ((u : G)⁻¹ * y * (u : G)) from by group]
      _ = (u : G) • (((u : G)⁻¹ * y * (u : G)) • ω) := by rw [mul_smul]
      _ = (u : G) • ω := by rw [hy'']
  -- so `u` fixes `conj g K` as well, i.e. lies in `D`
  have hug : (u : G) ∈ conj g K := by
    have hmem : (u : G) • ((g : G) : G ⧸ K) ∈ fixedPts K P := hperm _ hfixg
    rw [hEq] at hmem
    rcases hmem with h | h
    · exfalso
      have hsame : (u : G) • ((g : G) : G ⧸ K) = (u : G) • ((1 : G) : G ⧸ K) := by
        rw [h, hu1]
      have hg1 : ((g : G) : G ⧸ K) = ((1 : G) : G ⧸ K) := by
        have := congrArg (fun ω : G ⧸ K => (u : G)⁻¹ • ω) hsame
        simpa using this
      exact hpt hg1.symm
    · exact DoubleTransitivity.smul_mk_eq_mk_iff.mp h
  -- hence `u ∈ D`, of odd order: contradiction
  have huD : (u : G) ∈ (K ⊓ conj g K : Subgroup G) := ⟨huK, hug⟩
  have hdvd : Nat.card (Subgroup.zpowers (u : G) : Subgroup G) ∣
      Nat.card (K ⊓ conj g K : Subgroup G) :=
    Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr huD)
  rw [Nat.card_zpowers, hu2] at hdvd
  exact Nat.not_even_iff_odd.mpr hDodd (even_iff_two_dvd.mpr hdvd)

/-- **Ch. I §4 Prop. 1, Sylow step.**  If some `p`-Sylow `S` of `G` has at least three fixed
points on `Ω = G ⧸ K`, then no `p`-subgroup of `G` fixes exactly two points of `Ω`.

Indeed a `p`-subgroup `R` with exactly two fixed points is contained in a `p`-Sylow `T`, and
`Fix(T) ⊆ Fix(R)` gives `|Fix(T)| ≤ 2`; but all `p`-Sylows are conjugate and conjugation
transports fixed points (`Fix(conj g X) = g • Fix X`), so `|Fix|` takes the same value on `S`
and `T` — contradiction with `3 ≤ |Fix(S)|`. -/
theorem ncard_fixedPts_ne_two_of_sylow_three {G : Type} [Group G] [Finite G] {K : Subgroup G}
    {p : ℕ} (hp : p.Prime) (S : Sylow p G)
    (h3 : 3 ≤ (fixedPts K (S : Subgroup G)).ncard) :
    ∀ R : Subgroup G, IsPGroup p R → (fixedPts K R).ncard ≠ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- conjugating a subgroup transports its fixed points
  have hconj : ∀ (g : G) (X : Subgroup G), fixedPts K (conj g X) = g • fixedPts K X := by
    intro g X
    ext ω
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    constructor
    · intro hω x hx
      have hmem : g * x * g⁻¹ ∈ conj g X := by
        rw [DoubleTransitivity.mem_conj,
          show g⁻¹ * (g * x * g⁻¹) * g = x from by group]
        exact hx
      have h2 : (g * x * g⁻¹) • ω = ω := hω _ hmem
      calc x • (g⁻¹ • ω) = (x * g⁻¹) • ω := by rw [mul_smul]
        _ = (g⁻¹ * (g * x * g⁻¹)) • ω := by
              rw [show x * g⁻¹ = g⁻¹ * (g * x * g⁻¹) from by group]
        _ = g⁻¹ • ((g * x * g⁻¹) • ω) := by rw [mul_smul]
        _ = g⁻¹ • ω := by rw [h2]
    · intro hω y hy
      rw [DoubleTransitivity.mem_conj] at hy
      have h2 : (g⁻¹ * y * g) • (g⁻¹ • ω) = g⁻¹ • ω := hω _ hy
      calc y • ω = (g * (g⁻¹ * y * g) * g⁻¹) • ω := by
            rw [show g * (g⁻¹ * y * g) * g⁻¹ = y from by group]
        _ = g • ((g⁻¹ * y * g) • (g⁻¹ • ω)) := by rw [mul_smul, mul_smul]
        _ = g • (g⁻¹ • ω) := by rw [h2]
        _ = ω := by rw [smul_inv_smul]
  intro R hR h2
  obtain ⟨T, hRT⟩ := IsPGroup.exists_le_sylow hR
  have hle : (fixedPts K (T : Subgroup G)).ncard ≤ (fixedPts K R).ncard :=
    Set.ncard_le_ncard (fixedPts_mono (show R ≤ (T : Subgroup G) from hRT))
  have hcard : (fixedPts K (T : Subgroup G)).ncard = (fixedPts K (S : Subgroup G)).ncard := by
    haveI : MulAction.IsPretransitive G (Sylow p G) := Sylow.isPretransitive_of_finite
    obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) S T
    have hTS : (T : Subgroup G) = conj g (S : Subgroup G) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    rw [hTS, hconj g (S : Subgroup G), Set.ncard_smul_set]
  omega

/-- **Ch. I §4 Lemma 1, the `(c) ⟺ (d)` step.**  Conjugating a `p`-Sylow `Q` of a two-point
stabiliser by an element `d ∈ K` conjugates its normaliser inside `K`, so `|N_G(Q) ⊓ K|` is
invariant.  This is what makes `(D,K) ∈ R_p` a property of the *pair* `(D,K)` rather than of a
chosen `p`-Sylow, so that every `p`-Sylow of `D` inherits the even normaliser. -/
theorem card_normalizer_inf_conj_eq {G : Type} [Group G] {K Q : Subgroup G} {d : G}
    (hd : d ∈ K) :
    Nat.card ↥(Subgroup.normalizer (conj d Q : Set G) ⊓ K) =
      Nat.card ↥(Subgroup.normalizer (Q : Set G) ⊓ K) := by
  have hnorm : Subgroup.normalizer (conj d Q : Set G) =
      conj d (Subgroup.normalizer (Q : Set G)) := by
    ext y
    rw [DoubleTransitivity.mem_conj]
    constructor
    · intro hy
      rw [Subgroup.mem_normalizer_iff'']
      intro z
      constructor
      · intro hz
        have h1 : d * z * d⁻¹ ∈ conj d Q := by
          rw [DoubleTransitivity.mem_conj,
            show d⁻¹ * (d * z * d⁻¹) * d = z from by group]
          exact hz
        have h2 : y⁻¹ * (d * z * d⁻¹) * y ∈ conj d Q :=
          (Subgroup.mem_normalizer_iff''.mp hy (d * z * d⁻¹)).mp h1
        rw [DoubleTransitivity.mem_conj] at h2
        rwa [show d⁻¹ * (y⁻¹ * (d * z * d⁻¹) * y) * d
            = (d⁻¹ * y * d)⁻¹ * z * (d⁻¹ * y * d) from by group] at h2
      · intro hz
        have h2 : y⁻¹ * (d * z * d⁻¹) * y ∈ conj d Q := by
          rw [DoubleTransitivity.mem_conj]
          rw [show d⁻¹ * (y⁻¹ * (d * z * d⁻¹) * y) * d
              = (d⁻¹ * y * d)⁻¹ * z * (d⁻¹ * y * d) from by group]
          exact hz
        have h1 : d * z * d⁻¹ ∈ conj d Q :=
          (Subgroup.mem_normalizer_iff''.mp hy (d * z * d⁻¹)).mpr h2
        rw [DoubleTransitivity.mem_conj] at h1
        rwa [show d⁻¹ * (d * z * d⁻¹) * d = z from by group] at h1
    · intro hy
      rw [Subgroup.mem_normalizer_iff''] at hy
      rw [Subgroup.mem_normalizer_iff'']
      intro z
      constructor
      · intro hz
        have h1 : d⁻¹ * z * d ∈ Q := (DoubleTransitivity.mem_conj d z Q).mp hz
        have h2 : (d⁻¹ * y * d)⁻¹ * (d⁻¹ * z * d) * (d⁻¹ * y * d) ∈ Q :=
          (hy (d⁻¹ * z * d)).mp h1
        rw [DoubleTransitivity.mem_conj]
        rwa [show (d⁻¹ * y * d)⁻¹ * (d⁻¹ * z * d) * (d⁻¹ * y * d)
            = d⁻¹ * (y⁻¹ * z * y) * d from by group] at h2
      · intro hz
        have h2 : (d⁻¹ * y * d)⁻¹ * (d⁻¹ * z * d) * (d⁻¹ * y * d) ∈ Q := by
          rw [← show d⁻¹ * (y⁻¹ * z * y) * d
              = (d⁻¹ * y * d)⁻¹ * (d⁻¹ * z * d) * (d⁻¹ * y * d) from by group]
          rw [DoubleTransitivity.mem_conj] at hz
          exact hz
        have h1 : d⁻¹ * z * d ∈ Q := (hy (d⁻¹ * z * d)).mpr h2
        exact (DoubleTransitivity.mem_conj d z Q).mpr h1
  have hcard' : Subgroup.normalizer (conj d Q : Set G) ⊓ K =
      conj d (Subgroup.normalizer (Q : Set G) ⊓ K) := by
    rw [hnorm, conj_inf, conj_eq_self_of_mem hd]
  have hcard : Subgroup.normalizer (conj d Q : Set G) ⊓ K =
      (Subgroup.normalizer (Q : Set G) ⊓ K).map (MulAut.conj d).toMonoidHom := hcard'
  rw [hcard]
  exact Subgroup.card_map_of_injective (f := (MulAut.conj d).toMonoidHom) (MulAut.conj d).injective

/-- **Ch. I §4 Lemma 2, the promotion (b)+(c).**  Let `K ≤ G` be strongly embedded, `g ∉ K`,
`p ≠ 2`, and let `P ≤ D := K ⊓ conj g K` be a `p`-subgroup maximal among the `p`-subgroups of `G`
with at least three fixed points on `Ω = G ⧸ K`.  If some `p`-Sylow of `D` is normalised by an
involution of `K` (i.e. `(D,K) ∈ R_p` in the sense of the easy half), then `P` is a `p`-Sylow
of `D`.

Indeed every `p`-Sylow `Q'` of `D` is `D`-conjugate to the given one, and `card_normalizer_inf_conj_eq`
shows that `|N_G(Q') ⊓ K|` is therefore even; the easy half of Prop. 1 gives `3 ≤ |Fix(Q')|`; a
`p`-Sylow of `D` containing `P` is thus a `p`-subgroup with `≥ 3` fixed points containing `P`, so
maximality forces it to equal `P`. -/
theorem isSylowSubgroupOf_of_maximal_regular {G : Type} [Group G] [Finite G]
    {K : Subgroup G} (hK : IsStronglyEmbedded K) {g : G} (hg : g ∉ K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G} (hPp : IsPGroup p P)
    (hPd : P ≤ K ⊓ conj g K)
    (hPmax : ∀ R : Subgroup G, P ≤ R → IsPGroup p R → 3 ≤ (fixedPts K R).ncard → R = P)
    (hreg : ∃ Q : Subgroup G, Work.DoubleTransitivity.IsSylowSubgroupOf p Q (K ⊓ conj g K) ∧
      Even (Nat.card ↥(Subgroup.normalizer (Q : Set G) ⊓ K))) :
    Work.DoubleTransitivity.IsSylowSubgroupOf p P (K ⊓ conj g K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ, hQeven⟩ := hreg
  -- (b) Sylow conjugacy inside `D` transports the even normaliser to *every* `p`-Sylow of `D`
  have hQeven' : ∀ Q' : Subgroup G,
      Work.DoubleTransitivity.IsSylowSubgroupOf p Q' (K ⊓ conj g K) →
      Even (Nat.card ↥(Subgroup.normalizer (Q' : Set G) ⊓ K)) := by
    intro Q' hQ'
    obtain ⟨e, he, heQ⟩ := Work.ThreePoints.exists_conj_of_isSylowSubgroupOf hp hQ.1 hQ.2.1
      hQ.2.2 hQ'.1 hQ'.2.1 hQ'.2.2
    have heK : e ∈ K := (Subgroup.mem_inf.mp he).1
    rw [← heQ, card_normalizer_inf_conj_eq (K := K) (Q := Q) (d := e) heK]
    exact hQeven
  -- (c) a `p`-Sylow of `D` containing `P` has `≥ 3` fixed points, so maximality applies
  have hPsub : IsPGroup p (P.subgroupOf (K ⊓ conj g K)) :=
    hPp.comap_of_injective (K ⊓ conj g K).subtype Subtype.coe_injective
  obtain ⟨Q₁, hQ₁le⟩ := IsPGroup.exists_le_sylow hPsub
  set Q₁' : Subgroup G := (Q₁ : Subgroup ↥(K ⊓ conj g K)).map (K ⊓ conj g K).subtype with hQ₁'def
  have hQ₁'syl : Work.DoubleTransitivity.IsSylowSubgroupOf p Q₁' (K ⊓ conj g K) :=
    Work.DoubleTransitivity.App1.isSylowSubgroupOf_map_subtype hp Q₁
  have hle : P ≤ Q₁' := by
    rw [hQ₁'def, ← Subgroup.map_subgroupOf_eq_of_le hPd]
    exact Subgroup.map_mono hQ₁le
  have h3 : 3 ≤ (fixedPts K Q₁').ncard :=
    three_le_ncard_fixedPts_of_pSylow_normalizer_even hK hg hp2 hQ₁'syl (hQeven' Q₁' hQ₁'syl)
  have heq : Q₁' = P := hPmax Q₁' hle hQ₁'syl.2.1 h3
  rw [heq] at hQ₁'syl
  exact hQ₁'syl

/-- **Ch. I §4 Prop. 1, final Sylow-extension step.**  If `P` is a `p`-Sylow of a subgroup `D`,
`S` is a `p`-Sylow of `G` with `P ≤ S ≤ D`, then `S = P`.  (A `p`-group containing a `p`-Sylow
of `D` and inside `D` must equal it; `Sylow.is_maximal'` applied inside `↥D`.) -/
theorem eq_of_isSylowSubgroupOf_le {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P D S : Subgroup G} (hPD : Work.DoubleTransitivity.IsSylowSubgroupOf p P D)
    (hS : Work.DoubleTransitivity.IsSylowSubgroupOf p S ⊤) (hPS : P ≤ S) (hSD : S ≤ D) :
    S = P := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hPsub : IsPGroup p (P.subgroupOf D) :=
    hPD.2.1.comap_of_injective D.subtype Subtype.coe_injective
  have hSsub : IsPGroup p (S.subgroupOf D) :=
    hS.2.1.comap_of_injective D.subtype Subtype.coe_injective
  have hle : P.subgroupOf D ≤ S.subgroupOf D := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hPS (Subgroup.mem_subgroupOf.mp hx))
  have heq : S.subgroupOf D = P.subgroupOf D :=
    (IsPGroup.toSylow hPsub hPD.2.2).is_maximal' hSsub hle
  calc S = (S.subgroupOf D).map D.subtype := (Subgroup.map_subgroupOf_eq_of_le hSD).symm
    _ = (P.subgroupOf D).map D.subtype := by rw [heq]
    _ = P := Subgroup.map_subgroupOf_eq_of_le hPD.1

/-- **Ch. I §4 Prop. 1, final Sylow-extension step (consequence).**  If `P` (a `p`-Sylow of `D`)
has at least three fixed points on `Ω = G ⧸ K` and lies in a `p`-Sylow `S` of `G` with
`S ≤ D`, then `P` itself is a `p`-Sylow of `G` with at least three fixed points. -/
theorem exists_isSylowSubgroupOf_top_three_fixedPts {G : Type} [Group G] [Finite G]
    {K : Subgroup G} {p : ℕ} (hp : p.Prime) {P D S : Subgroup G}
    (hPD : Work.DoubleTransitivity.IsSylowSubgroupOf p P D)
    (hS : Work.DoubleTransitivity.IsSylowSubgroupOf p S ⊤) (hPS : P ≤ S) (hSD : S ≤ D)
    (h3 : 3 ≤ (fixedPts K P).ncard) :
    ∃ S' : Subgroup G, Work.DoubleTransitivity.IsSylowSubgroupOf p S' ⊤ ∧
      3 ≤ (fixedPts K S').ncard := by
  refine ⟨P, ?_, h3⟩
  rw [eq_of_isSylowSubgroupOf_le hp hPD hS hPS hSD] at hS
  exact hS

/-! ## 4. Ch. I §4 Prop. 2, unconditional, and Prop. 1 (a) for `X`

The pieces above are the ones the *source* uses (§4 Prop. 1 (a) is deduced in the source from
Ch. I §4 Prop. 2 (p. 156) in the group `F₁ = C_G(Y)·P`).  Ch. I §4 Prop. 2 is available in the
workspace in three forms: the `HasFourGroup` case
(`Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_unconditional`, using Theorem A),
the `¬ HasFourGroup` case
(`Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_nofour`, using
`Work.ThreePoints.S4Prop2.no_two_fixed_pts`), and the `¬ HasFourGroup` case *given* that no
`p`-subgroup has exactly two fixed points
(`Work.ThreePoints.even_card_normalizer_nofour_of_no_two_fixed`).

Both are replaced here by a single unconditional statement `p3_prop2_general`: split on whether
`𝓡_p ≠ ∅` (Ch. I §4 Lemma 2 in the "no two fixed points" formulation, see
`Work.DoubleTransitivity.Sec4.rp_no_two_fixed_pts`).  If `𝓡_p ≠ ∅` we apply the reduced
`2`-rank-`1` assembly; if `𝓡_p = ∅` then Ch. I §4 Prop. 1 (a)
(`Work.DoubleTransitivity.Sec4.not_rp_twoTransitive`) makes `F` `2`-transitive on `Ω = F ⧸ K`,
and the argument of the `HasFourGroup` case goes through verbatim (App. II (6) + Ch. I §3
Prop. 1).  This is exactly the source's Case 1 / Case 2 dichotomy for Prop. 2. -/

/-- **Ch. I §4 Prop. 2** (p. 156–157), unconditional form: for a finite group `F`, a strongly
embedded `K ≤ F`, a prime `p ≠ 2` and a `p`-subgroup `Q ≤ K` maximal among the `p`-subgroups of
`K` with at least three fixed points of `Ω = F ⧸ K`, the normaliser `N_K(Q)` has even order. -/
theorem p3_prop2_general {F : Type} [Group F] [Finite F]
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) {K : Subgroup F}
    (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : Subgroup F} (hQK : Q ≤ K) (hQp : IsPGroup p Q)
    (hQ3 : 3 ≤ (fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
      3 ≤ (fixedPts K R).ncard → R = Q) :
    Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) := by
  classical
  have h1 : Work.DoubleTransitivity.Sec4.Sec4Lemma2Part1 p K :=
    Work.DoubleTransitivity.Sec4.lemma2_part1 hBrSz hK hp hp2
  by_cases hRp : Work.DoubleTransitivity.Sec4.Rp p K
  · -- Case 2 of the source: `𝓡_p ≠ ∅`, so no `p`-subgroup fixes exactly two points.
    exact Work.ThreePoints.even_card_normalizer_nofour_of_no_two_fixed hK hp hp2 hQK hQp hQ3
      hQmax (fun P hPp => Work.DoubleTransitivity.Sec4.rp_no_two_fixed_pts hBrSz hK hp hp2 h1
        hRp P hPp) hBrSz
  · -- Case 1 of the source: `𝓡_p = ∅`, so `F` is `2`-transitive on `Ω = F ⧸ K`.
    haveI : Fintype (F ⧸ K) := Fintype.ofFinite _
    set M : Subgroup F := Subgroup.normalizer (Q : Set F) with hMdef
    have hstab : MulAction.stabilizer F (((1 : F)) : F ⧸ K) = K := by
      rw [Work.ThreePoints.stabilizer_mk K 1, Work.ThreePoints.conj_one]
    have h2tr : MulAction.IsMultiplyPretransitive F (F ⧸ K) 2 :=
      Work.DoubleTransitivity.Sec4.not_rp_twoTransitive hBrSz hK hp hp2 h1 hRp
    -- App. II (6): maximality in `F` and transitivity of `N_F(Q)` on `Ω_Q`
    obtain ⟨hQmaxF, htransF⟩ := app2_6_general (X := F) (E := F ⧸ K) (p := p) hp h2tr
      (P := Q) hQp (by rw [hstab]; exact hQK) hQ3
      (fun R hRg hRa hR3 hQR => by
        have hRK : R ≤ K := by rw [← hstab]; exact hRa
        rw [hQmax R hQR hRK hRg hR3])
    -- Ch. I §3 Prop. 1
    obtain ⟨ω, hω, heven⟩ := sec3_prop1_transitive_unconditional hK hp hp2 hQp hQ3
      (fun R hQR hRg hR3 => hQmaxF R hQR hRg hR3) htransF
    have hωK : (((1 : F)) : F ⧸ K) ∈ Submission.Blueprint.fixedPts K Q := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, hstab]
      exact hQK
    obtain ⟨n, hnM, hn⟩ := htransF (((1 : F)) : F ⧸ K) hωK ω hω
    -- all point stabilisers of `N_F(Q)` on `Ω_Q` have the same order
    have hcard_eq : Nat.card (MulAction.stabilizer F ω ⊓ M : Subgroup F) =
        Nat.card (MulAction.stabilizer F (((1 : F)) : F ⧸ K) ⊓ M : Subgroup F) := by
      have hnM' : n ∈ M := hnM
      have hMconj : conj n M = M := by
        have hstep : ∀ u ∈ M, conj u M ≤ M := by
          intro u hu m hm
          rw [mem_conj_iff] at hm
          have h := M.mul_mem (M.mul_mem hu hm) (M.inv_mem hu)
          rwa [show u * (u⁻¹ * m * u) * u⁻¹ = m from by group] at h
        refine le_antisymm (hstep n hnM') ?_
        calc M = conj n (conj n⁻¹ M) := by rw [← conj_mul, mul_inv_cancel, conj_one]
          _ ≤ conj n M := Subgroup.map_mono (hstep n⁻¹ (M.inv_mem hnM'))
      have h1' : MulAction.stabilizer F ω =
          conj n (MulAction.stabilizer F (((1 : F)) : F ⧸ K)) := by
        rw [← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj n (((1 : F)) : F ⧸ K), hn]
      have key2 : MulAction.stabilizer F ω ⊓ M =
          conj n (MulAction.stabilizer F (((1 : F)) : F ⧸ K) ⊓ M) := by
        rw [conj_inf, ← h1', hMconj]
      rw [key2]
      exact Subgroup.card_map_of_injective (MulAut.conj n).injective
    have hevenK : Even (Nat.card (K ⊓ M : Subgroup F)) := by
      rw [← hstab, ← hcard_eq]
      exact heven
    -- `N_K(Q)` is isomorphic to its image in `F`, which is `K ⊓ N_F(Q)`
    have hmap : (Subgroup.normalizer (Q.subgroupOf K : Set K)).map K.subtype = K ⊓ M := by
      ext x
      rw [Subgroup.mem_map, Subgroup.mem_inf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.2, ?_⟩
        rw [hMdef, Subgroup.mem_normalizer_iff_map_conj_eq]
        have hy' : (Q.subgroupOf K).map (MulAut.conj y).toMonoidHom = Q.subgroupOf K :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
        calc Q.map (MulAut.conj (y : F)).toMonoidHom
            = ((Q.subgroupOf K).map K.subtype).map (MulAut.conj (y : F)).toMonoidHom := by
              conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hQK]
          _ = (Q.subgroupOf K).map ((MulAut.conj (y : F)).toMonoidHom.comp K.subtype) := by
              rw [Subgroup.map_map]
          _ = (Q.subgroupOf K).map (K.subtype.comp (MulAut.conj y).toMonoidHom) := by
              rw [show (MulAut.conj (y : F)).toMonoidHom.comp K.subtype =
                K.subtype.comp (MulAut.conj y).toMonoidHom from by
                  ext z
                  simp [MulAut.conj_apply]]
          _ = ((Q.subgroupOf K).map (MulAut.conj y).toMonoidHom).map K.subtype := by
              rw [Subgroup.map_map]
          _ = (Q.subgroupOf K).map K.subtype := by rw [hy']
          _ = Q := Subgroup.map_subgroupOf_eq_of_le hQK
      · rintro ⟨hxK, hxN⟩
        refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hyQ : (y : F) ∈ Q := Subgroup.mem_subgroupOf.mp hy
          have h1' : x * (y : F) * x⁻¹ ∈ Q :=
            (Subgroup.mem_normalizer_iff.mp hxN) (y : F) |>.mp hyQ
          rw [Subgroup.mem_subgroupOf]
          simpa using h1'
        · intro hy
          have hyQ : x * (y : F) * x⁻¹ ∈ Q := by
            have h := Subgroup.mem_subgroupOf.mp hy
            simpa using h
          have hxi : x⁻¹ ∈ Subgroup.normalizer (Q : Set F) :=
            (Subgroup.normalizer (Q : Set F)).inv_mem hxN
          have h1' : x⁻¹ * (x * (y : F) * x⁻¹) * x⁻¹⁻¹ ∈ Q :=
            (Subgroup.mem_normalizer_iff.mp hxi) (x * (y : F) * x⁻¹) |>.mp hyQ
          have h2' : x⁻¹ * (x * (y : F) * x⁻¹) * x⁻¹⁻¹ = (y : F) := by group
          rw [h2'] at h1'
          exact Subgroup.mem_subgroupOf.mpr h1'
    have hcardfin : Nat.card ↥(Subgroup.normalizer (Q.subgroupOf K : Set K)) =
        Nat.card ↥(K ⊓ M : Subgroup F) := by
      rw [← hmap]
      exact (Subgroup.card_map_of_injective (f := K.subtype) Subtype.coe_injective).symm
    rw [hcardfin]
    exact hevenK

/-- The `Situation`-free form of Ch. I §4 Prop. 2 required by
`Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz`, discharged by
`p3_prop2_general`. -/
theorem p3_s4prop2_input (hBrSz : Submission.Blueprint.BrauerSuzukiProp) :
    ∀ (F : Type) [Group F] [Finite F] {K : Subgroup F},
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded K →
      ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ Q : Subgroup F, Q ≤ K → IsPGroup p Q →
        3 ≤ (fixedPts K Q).ncard →
        (∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
          3 ≤ (fixedPts K R).ncard → R = Q) →
        Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) :=
  fun F _ _ K hK p hp hp2 Q hQK hQp hQ3 hQmax =>
    p3_prop2_general (F := F) (K := K) hBrSz hK hp hp2 hQK hQp hQ3 hQmax

/-- **Ch. II §4 Prop. 1 (a)** (p. 168), with the inputs of this workspace: for `X ≤ H` a subgroup
of odd order with `3 ≤ |Ω_X|` and `M ∈ Ω_X`, the centraliser `M ⊓ C_G(X)` has even order. -/
theorem p3_even_card_centralizer {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (fixedPts H X).ncard) (hM : ∃ g : G, M = conj g H) (hXM : X ≤ M) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
  Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz hFT hC
    (p3_s4prop2_input hBrSz) hS hH hX3 hM hXM

/-- **Ch. II §4 Prop. 1 (b), the strong-embeddedness half**: for `X ≤ H` with `3 ≤ |Ω_X|` and
involution-generated `F` containing `Inv C_G(X)`, the subgroup `F ⊓ M` is strongly embedded in
`F` for `M = H ∈ Ω_X`. -/
theorem p3_stronglyEmbedded_inf_H {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X : Subgroup G}
    (hX3 : 3 ≤ (fixedPts H X).ncard) (hXH : X ≤ H) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      (((Work.ThreePoints.p3F1 X) ⊓ H).subgroupOf (Work.ThreePoints.p3F1 X)) :=
  Work.ThreePoints.Prop1aBrSz.stronglyEmbedded_subgroupOf_inf_conj_of_even_card_at
    (H := H) (X := X) (F := Work.ThreePoints.p3F1 X) (M := H) hH hX3
    (fun u hu => Subgroup.subset_closure hu) hXH ⟨1, by rw [DoubleTransitivity.conj_one]⟩
    (fun M hM hXM => p3_even_card_centralizer hFT hC hBrSz hS hH hX3 hM hXM)

/-- Peterfalvi I Ch. II §4 Prop. 3, part 1), first half of (a): with `X ≠ ⊥`, `X ≤ V = C_D(t)`
and `N_K(X) ≠ 1` (`k ∈ K ∖ {1}` normalising `X`), the group `F₁ = ⟨Inv C_G(X)⟩` acts
2-transitively on the set of fixed points `Ω_X = fixedPts H X` of `X` in `Ω = G ⧸ H`.
This is where the source invokes Ch. I §4 Prop. 1 on `F₁` (its `⟨k⟩` is a `p`-subgroup with
exactly two fixed points).  Route via Theorem A (`hA`) needs `HasFourGroup F₁`, which the source
gets from Appendix III (1) together with Prop. 2 (c) and Lemma 1.  (`Submission.Work.ThreePoints.
even_card_normalizer_of_maximal_p_subgroup` is Ch. I §4 Prop. 2 with `hBrSz`.)
Do not import any module whose closure still contains `hole`. -/
theorem p3_twoTransitive {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub (Work.ThreePoints.p3F1 X)
      (Submission.Blueprint.fixedPts H X) := by
  classical
  -- ### `X ≤ H`, `X ≤ H^t`, and `3 ≤ |Ω_X|`
  have hXH : X ≤ H :=
    hX.trans (by rw [centD_eq]; exact le_trans inf_le_left inf_le_left)
  have hXt : X ≤ conj t H :=
    hX.trans (by rw [centD_eq]; exact le_trans inf_le_left inf_le_right)
  have h3X : 3 ≤ (fixedPts H X).ncard := three_le_ncard_fixedPts_of_le_centD hH ht htH hX
  -- ### Ch. II §4 Prop. 1 (a) at `X`, and the resulting strong-embeddedness of `F₁ ⊓ H`
  have hEV : ∀ M : Subgroup G, (∃ g : G, M = conj g H) → X ≤ M →
      Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
    fun M hM hXM => p3_even_card_centralizer hFT hC hBrSz hS hH h3X hM hXM
  have hSE := p3_stronglyEmbedded_inf_H hFT hC hBrSz hS hH h3X hXH
  -- ### Ch. II §4 Prop. 2 (c): every `x ∈ K#` fixes exactly two points of `Ω`
  have hProp2c : ∀ x ∈ invertedBy (twoPoint H t) t, x ≠ 1 →
      (fixedPts H (Subgroup.zpowers x)).ncard = 2 :=
    fun x hx hx1 => Work.ThreePoints.F1EqF.prop2c_of_even hC hBrSz hS hH ht htH
      (fun X' M hM hXM hX'3 =>
        p3_even_card_centralizer hFT hC hBrSz hS hH hX'3 hM hXM) hx hx1
  -- ### Ch. II §4 Lemma 1: a non-trivial `k ∈ K` normalising `X` lies in `F₁`
  obtain ⟨k, hk, hk1, hkN⟩ := hNX
  have hkF1 : k ∈ p3F1 X := p3_lemma1 hFT hC hA hBrSz hS hH ht htH hX hk hkN
  have hkD : k ∈ twoPoint H t := hk.1
  -- `K = J(D,t)` has odd order, so `orderOf k` is odd
  have hoddD : Odd (Nat.card (twoPoint H t : Subgroup G)) :=
    IsStronglyEmbedded.odd_card_inf_conj hH htH
  have hdvd : orderOf k ∣ Nat.card (twoPoint H t : Subgroup G) := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hkD)
  have hoddk : Odd (orderOf k) := Odd.of_dvd hdvd hoddD
  have hm_ne1 : orderOf k ≠ 1 := fun h => hk1 (orderOf_eq_one_iff.mp h)
  have hm_pos : 0 < orderOf k := orderOf_pos k
  -- replace `k` by a power of prime order `p`
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hm_ne1
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hoddk (even_iff_two_dvd.mpr hpdvd)
  have hp_le_m : p ≤ orderOf k := Nat.le_of_dvd hm_pos hpdvd
  have ha_pos : 0 < orderOf k / p := Nat.div_pos hp_le_m hpprime.pos
  have hmul : orderOf k / p * p = orderOf k := Nat.div_mul_cancel hpdvd
  have hlt : orderOf k / p < orderOf k := Nat.div_lt_self hm_pos hpprime.one_lt
  set k' : G := k ^ (orderOf k / p) with hk'def
  have hk'pow : k' ^ p = 1 := by
    rw [hk'def, ← pow_mul, hmul, pow_orderOf_eq_one]
  have hk'ne : k' ≠ 1 := by
    intro hcon
    have h1 : k ^ (orderOf k / p) = 1 := hcon
    have hd : orderOf k ∣ orderOf k / p := orderOf_dvd_iff_pow_eq_one.mpr h1
    exact absurd (Nat.le_of_dvd ha_pos hd) (not_le.mpr hlt)
  have hk'ord : orderOf k' = p := by
    haveI : Fact p.Prime := ⟨hpprime⟩
    exact orderOf_eq_prime hk'pow hk'ne
  -- `k'` is again an element of `K` inverted by `t`, and lies in `F₁`
  have hk'D : k' ∈ twoPoint H t := Subgroup.pow_mem _ hkD _
  have hk'inv : t * k' * t⁻¹ = k'⁻¹ := by
    have hconj : (MulAut.conj t) k = k⁻¹ := by
      rw [MulAut.conj_apply]; exact hk.2
    calc t * k' * t⁻¹ = (MulAut.conj t) k' := by rw [MulAut.conj_apply]
      _ = ((MulAut.conj t) k) ^ (orderOf k / p) := by rw [hk'def, map_pow]
      _ = (k⁻¹) ^ (orderOf k / p) := by rw [hconj]
      _ = (k ^ (orderOf k / p))⁻¹ := by rw [inv_pow]
      _ = k'⁻¹ := by rw [hk'def]
  have hk'F1 : k' ∈ p3F1 X := Subgroup.pow_mem _ hkF1 _
  have hk'C : k' ∈ invertedBy (twoPoint H t) t := ⟨hk'D, hk'inv⟩
  -- ### `⟨k'⟩` has exactly two fixed points on `Ω_X`
  have hfix2 : (fixedPts H (Subgroup.zpowers k')).ncard = 2 := hProp2c k' hk'C hk'ne
  have hk'H : k' ∈ H := hk'D.1
  have hk'tH : k' ∈ conj t H := hk'D.2
  have hfix : (fixedPts H (Subgroup.zpowers k') ∩ fixedPts H X).ncard = 2 := by
    have h1t : (((1 : G)) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
      intro hcon
      rw [QuotientGroup.eq] at hcon
      exact htH (by simpa using hcon)
    have hmem1' : (((1 : G)) : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers k') := by
      rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, DoubleTransitivity.conj_one]
      exact Subgroup.zpowers_le.mpr hk'H
    have hmemt' : ((t : G) : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers k') := by
      rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
      exact Subgroup.zpowers_le.mpr hk'tH
    have hmem1X : (((1 : G)) : G ⧸ H) ∈ fixedPts H X := by
      rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, DoubleTransitivity.conj_one]
      exact hXH
    have hmemtX : ((t : G) : G ⧸ H) ∈ fixedPts H X := by
      rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
      exact hXt
    have hsub : ({((1 : G) : G ⧸ H), ((t : G) : G ⧸ H)} : Set (G ⧸ H)) ⊆
        fixedPts H (Subgroup.zpowers k') ∩ fixedPts H X := by
      intro y hy
      rcases hy with h | h
      · rw [h]; exact ⟨hmem1', hmem1X⟩
      · rw [h]; exact ⟨hmemt', hmemtX⟩
    have h2 : ({((1 : G) : G ⧸ H), ((t : G) : G ⧸ H)} : Set (G ⧸ H)).ncard = 2 :=
      Set.ncard_pair h1t
    have hle : (fixedPts H (Subgroup.zpowers k') ∩ fixedPts H X).ncard ≤ 2 :=
      le_trans (Set.ncard_le_ncard Set.inter_subset_left) (le_of_eq hfix2)
    exact le_antisymm hle (h2 ▸ Set.ncard_le_ncard hsub)
  -- ### `⟨k'⟩` is an odd `p`-subgroup of `F₁` with exactly two fixed points on `Ω_X`
  have hk'P : IsPGroup p (Subgroup.zpowers k') := by
    haveI : Fact p.Prime := ⟨hpprime⟩
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, hk'ord, pow_one]⟩
  -- ### Ch. I §4 Prop. 1 on `F₁` acting on `Ω_X`
  exact Work.ThreePoints.P3Sub.ch1s4_prop1 (H := H) (X := X) (N := p3F1 X)
    (P := Subgroup.zpowers k') hH hBrSz hXH (p3F1_le_normalizer X)
    (fun u hu => Subgroup.subset_closure hu) hEV hSE hpprime hp2
    (Subgroup.zpowers_le.mpr hk'F1) hk'P hfix

end Work.ThreePoints.P3NeBot
