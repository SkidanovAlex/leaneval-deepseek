import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.canonicalForm
import Submission.Work.DoubleTransitivity.App2.app2_7
import Submission.Work.DoubleTransitivity.App1.app1_1b
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.P3NeBot.p3_twoTransitive

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.lemma2b` — Peterfalvi II, Ch. V §2 Lemma 2 (b)

`N_G(X) = C_G(X) · N_V(X)` for `X ≠ 1` a subgroup of `V = C_D(t)`, with `D = H ⊓ Hᵗ` and
`N_V(X) = V ⊓ N_G(X)`.  The proof is the source's: `C_G(X)` is `2`-transitive on the set
`Ω_X = fixedPts H X` of fixed points of `X` (Lemma 2 (a)), so for `g ∈ N_G(X)` there is
`f ∈ C_G(X)` with `g f` fixing both `H` and `Hᵗ`, i.e. `g f ∈ N_G(X) ⊓ D`; and
`N_G(X) ⊓ D = (V ⊓ N_G(X)) · (K ⊓ N_G(X))` with `K ⊓ N_G(X) ≤ C_G(X)` (Appendix I (1) +
Ch. II §4 Lemma 1).

The results below are the ingredients of that proof:

* `base_regular_data`: at the base pair `(pt H, t·pt H)` the fixed data `(Q, H, D)` satisfies
  Appendix II (7)'s hypothesis (this is Ch. V §2 Lemma 1 (a)'s "`Q` acts regularly on
  `Ω ∖ {pt H}`" and "`H = Q ⋊ D`", both consequences of `IsSplitRankOne`);
* `centralizer_transitive_fixedPts`: `C_G(X)` is *transitive* on `Ω_X`, obtained from
  Appendix II (7)'s "core" (`app2_7_core`) applied to the base pair and the involution `t ∈ C_G(X)`;
* `centralizer_twoTransitive`: `C_G(X)` is `2`-transitive on `Ω_X`, by transferring the
  `2`-transitivity of `C_G(X)` on `C_G(X) ⧸ (C_G(X) ⊓ H)` (`IsBenderFamily.twoTransitive`,
  hypothesis `hfam`) along the orbit map (`ch1s4_transfer`);
* `mem_centralizer_of_mem_invertedBy_normalizer`: Ch. II §4 Lemma 1, forward half
  (`k ∈ K` normalising `X ≤ V` lies in `C_G(X)`);
* `exists_mul_of_mem_twoPoint_inf_normalizer`: Appendix I (1) (`N_D(X) = (V ⊓ N_G(X))·(K ⊓ N_G(X))`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF

variable {G : Type} [Group G] [Finite G]

/-! ## The base point `H` of `Ω = G ⧸ H` -/

/-- The stabiliser of the base point `H` of `Ω = G ⧸ H` is `H`. -/
theorem stabilizer_one {G : Type} [Group G] (H : Subgroup G) :
    MulAction.stabilizer G ((1 : G) : G ⧸ H) = H := by
  rw [Work.ThreePoints.stabilizer_mk H 1, Work.DoubleTransitivity.conj_one]

/-! ## `H = Q ⋊ D`: the factorisation `H = Q·D` -/

theorem exists_mul_Q_twoPoint {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {x : G} (hx : x ∈ H) : ∃ q ∈ Q, ∃ d ∈ twoPoint H t, x = q * d := by
  obtain ⟨p, hp, -⟩ := split_exists_unique_factor h hx
  refine ⟨p.1 * p.2 * p.1⁻¹,
    ((Subgroup.mem_normalizer_iff.mp (h.normal (Subgroup.mem_inf.mp hp.1).1)) p.2).mp hp.2.1,
    p.1, hp.1, ?_⟩
  have h1 : p.1 * p.2 * p.1⁻¹ * p.1 = p.1 * p.2 := by group
  rw [h1, hp.2.2]

theorem existsUnique_mul_Q_twoPoint {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {x : G} (hx : x ∈ H) :
    ∃! q : Q, ∃ d ∈ twoPoint H t, (q : G) * d = x := by
  obtain ⟨q, hq, d, hd, hqd⟩ := exists_mul_Q_twoPoint h hx
  refine ⟨⟨q, hq⟩, ⟨d, hd, hqd.symm⟩, ?_⟩
  rintro ⟨q', hq'⟩ ⟨d', hd', hq'd'⟩
  have h3 : (q' : G) * d' = (q : G) * d := by rw [hq'd', ← hqd]
  have h5 : (q' : G)⁻¹ * ((q' : G) * d') = (q' : G)⁻¹ * ((q : G) * d) := by rw [h3]
  rw [inv_mul_cancel_left] at h5
  have h4 : (q' : G)⁻¹ * q = d' * d⁻¹ := by rw [h5]; group
  have hmem : (q' : G)⁻¹ * q ∈ Q ⊓ twoPoint H t :=
    ⟨Q.mul_mem (Q.inv_mem hq') hq,
      by rw [h4]; exact (twoPoint H t).mul_mem hd' ((twoPoint H t).inv_mem hd)⟩
  rw [h.inf_eq, Subgroup.mem_bot] at hmem
  exact Subtype.ext (inv_mul_eq_one.mp hmem)

/-! ## Every point of `Ω ∖ {pt H}` is `q • (t·pt H)` -/

/-- Every point `x·H ≠ H` of `Ω` is `q • (t·H)` for some `q ∈ Q`: the canonical form
`x = a t y` (`a ∈ H`, `y ∈ Q`) writes `x·H = a·t·H`, and `a = q d` (`q ∈ Q`, `d ∈ D`)
with `d t H = t H`. -/
theorem exists_Q_smul_t {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {x : G} (hx : x ∉ H) :
    ∃ q ∈ Q, (q : G) • ((t : G) : G ⧸ H) = ((x : G) : G ⧸ H) := by
  obtain ⟨p, hp, -⟩ := canonicalForm (Work.ThmF.IsSplitRankOne.toData h) x hx
  obtain ⟨q₁, hq₁, d, hd, hqd⟩ := exists_mul_Q_twoPoint h hp.1
  refine ⟨q₁, hq₁, ?_⟩
  have hdt : t⁻¹ * d * t ∈ H := Work.ThreePoints.mem_conj_iff.mp hd.2
  have hxe : x = q₁ * d * t * p.2 := by
    rw [hqd] at hp
    rw [← hp.2.2]
  rw [show (q₁ : G) • ((t : G) : G ⧸ H) = ((q₁ * t : G) : G ⧸ H) from rfl,
    QuotientGroup.eq, hxe]
  have hcomp : (q₁ * t)⁻¹ * (q₁ * d * t * p.2) = (t⁻¹ * d * t) * p.2 := by group
  rw [hcomp]
  exact H.mul_mem hdt (h.le hp.2.1)

/-! ## Appendix II (7) at the base pair -/

/-- **Peterfalvi II Ch. V §2 Lemma 1 (a) / Appendix II (7) at `(pt H, t·pt H)`.**  The fixed data
`(Q, H, D)` of a split rank-one datum satisfies, at the base pair `a = pt H`, `b = t·pt H`:

* `Q ≤ G_a` and `G_a ≤ N_G(Q)` (`H = Q ⋊ D`);
* `Q` is regular on `Ω ∖ {a}` (Ch. II §4: `Q` is a regular normal subgroup of `H` acting on
  `Ω ∖ {pt H}`);
* every `k ∈ G_a = H` decomposes uniquely as `q·d` with `q ∈ Q`, `d ∈ G_a ⊓ G_b = D`. -/
theorem base_regular_data {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {a b : G ⧸ H}
    (ha : a = ((1 : G) : G ⧸ H)) (hb : b = ((t : G) : G ⧸ H)) :
    Q ≤ MulAction.stabilizer G a ∧
    MulAction.stabilizer G a ≤ Subgroup.normalizer (Q : Set G) ∧
    Work.DoubleTransitivity.IsRegularOnSub Q ({a}ᶜ : Set (G ⧸ H)) ∧
    (∀ k ∈ MulAction.stabilizer G a, ∃! q : Q,
      ∃ d ∈ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b, (q : G) * d = k) := by
  subst ha
  subst hb
  have hS1 : MulAction.stabilizer G ((1 : G) : G ⧸ H) = H := stabilizer_one H
  have hSt : MulAction.stabilizer G ((t : G) : G ⧸ H) = Submission.Blueprint.conj t H :=
    Work.ThreePoints.stabilizer_mk H t
  have htH : t ∉ H := h.not_mem
  refine ⟨fun q hq => by rw [hS1]; exact h.le hq, fun g hg => by rw [hS1] at hg; exact h.normal hg,
    ⟨?_, ?_⟩, ?_⟩
  · intro c hc d hd
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective d
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hc hd
    have hx : x ∉ H := by
      intro hxH
      exact hc (by rw [QuotientGroup.eq]; simpa using H.inv_mem hxH)
    have hy : y ∉ H := by
      intro hyH
      exact hd (by rw [QuotientGroup.eq]; simpa using H.inv_mem hyH)
    obtain ⟨q₁, hq₁, hq₁t⟩ := exists_Q_smul_t h hx
    obtain ⟨q₂, hq₂, hq₂t⟩ := exists_Q_smul_t h hy
    refine ⟨q₂ * q₁⁻¹, Q.mul_mem hq₂ (Q.inv_mem hq₁), ?_⟩
    rw [← hq₁t, ← mul_smul]
    have hgroup : (q₂ * q₁⁻¹) * q₁ = q₂ := by group
    rw [hgroup]
    exact hq₂t
  · intro q hq hfix
    have htne : ((t : G) : G ⧸ H) ≠ ((1 : G) : G ⧸ H) := by
      intro hcon
      refine htH ?_
      have h2 : t⁻¹ * 1 ∈ H := QuotientGroup.eq.mp hcon
      simpa using H.inv_mem h2
    have hqt : ((q * t : G) : G ⧸ H) = ((t : G) : G ⧸ H) :=
      hfix ((t : G) : G ⧸ H) (by simpa using htne)
    have h1 : t⁻¹ * q * t ∈ H := by
      have h2 : (q * t)⁻¹ * t ∈ H := QuotientGroup.eq.mp hqt
      have h3 : ((q * t)⁻¹ * t)⁻¹ = t⁻¹ * q * t := by group
      have hinv : ((q * t)⁻¹ * t)⁻¹ ∈ H := H.inv_mem h2
      rwa [h3] at hinv
    have hmem : q ∈ Q ⊓ twoPoint H t :=
      ⟨hq, ⟨h.le hq, Work.ThreePoints.mem_conj_iff.mpr h1⟩⟩
    rw [h.inf_eq, Subgroup.mem_bot] at hmem
    exact hmem
  · intro k hk
    rw [hS1] at hk
    rw [hS1, hSt]
    exact existsUnique_mul_Q_twoPoint h hk

/-! ## Appendix I (1): `N_G(X) ⊓ D = (V ⊓ N_G(X))·(K ⊓ N_G(X))` -/

/-- **Peterfalvi's `N_D(X) = N_K(X)·N_V(X)`** (Appendix I (1)(b) applied to `D ⊓ N_G(X)`):
every `m ∈ N_G(X)` normalising `X ≤ V` and lying in `D = H ⊓ Hᵗ` is a product `c·y` with
`c ∈ V ⊓ N_G(X)` and `y ∈ J(D,t) ⊓ N_G(X)`. -/
theorem exists_mul_of_mem_twoPoint_inf_normalizer {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) {X : Subgroup G}
    (hXV : X ≤ centD H t) {m : G} (hm : m ∈ twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) :
    ∃ c : G, c ∈ centD H t ⊓ Subgroup.normalizer (X : Set G) ∧
      ∃ y : G, y ∈ invertedBy (twoPoint H t) t ∧ y ∈ Subgroup.normalizer (X : Set G) ∧
        m = c * y := by
  have ht2 : orderOf t = 2 := h.invol
  have hoddD : Odd (Nat.card ↥(twoPoint H t)) := split_odd_card_twoPoint h
  have htC : t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Work.ThreePoints.mem_centD.mp (hXV hx)).2.2
  have htN : t ∈ Subgroup.normalizer (X : Set G) := Subgroup.centralizer_le_normalizer _ htC
  have hmapX : Subgroup.map (↑(MulAut.conj t)) X = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp htN
  have hmapN : Subgroup.map (↑(MulAut.conj t)) (Subgroup.normalizer (X : Set G))
      = Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj t).bijective, hmapX]
  have hmapD : Subgroup.map (↑(MulAut.conj t)) (twoPoint H t) = twoPoint H t :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (normalizes_twoPoint_of_data (Work.ThmF.IsSplitRankOne.toData h))
  have htM : t ∈ Subgroup.normalizer
      ((twoPoint H t ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hmapD, hmapN]
  have hoddM : Odd (Nat.card ↥(twoPoint H t ⊓ Subgroup.normalizer (X : Set G))) :=
    Odd.of_dvd_nat hoddD (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨p, hp⟩ :=
    (Work.DoubleTransitivity.App1.phiMap_bijective ht2 hoddM htM).2 ⟨m, hm⟩
  have hm_eq : (p.1 : G) * (p.2 : G) ^
      Work.DoubleTransitivity.App1.expo (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) = m := by
    have h1 := congrArg (fun z : ↥(twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) => (z : G)) hp
    simpa [Work.DoubleTransitivity.App1.phiMap_apply] using h1
  have hcM : (p.1 : G) ∈ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) := p.1.2.1
  have hcc : (p.1 : G) ∈ Subgroup.centralizer ({t} : Set G) := p.1.2.2
  have hcD : (p.1 : G) ∈ twoPoint H t := (Subgroup.mem_inf.mp hcM).1
  have hcN : (p.1 : G) ∈ Subgroup.normalizer (X : Set G) := (Subgroup.mem_inf.mp hcM).2
  have hyM : (p.2 : G) ^ Work.DoubleTransitivity.App1.expo
      (twoPoint H t ⊓ Subgroup.normalizer (X : Set G))
      ∈ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) :=
    Subgroup.pow_mem _ p.2.2.1 _
  have hyD : (p.2 : G) ^ Work.DoubleTransitivity.App1.expo
      (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) ∈ twoPoint H t :=
    (Subgroup.mem_inf.mp hyM).1
  have hyN : (p.2 : G) ^ Work.DoubleTransitivity.App1.expo
      (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.mem_inf.mp hyM).2
  have hyinv : t * ((p.2 : G) ^ Work.DoubleTransitivity.App1.expo
      (twoPoint H t ⊓ Subgroup.normalizer (X : Set G))) * t⁻¹
      = ((p.2 : G) ^ Work.DoubleTransitivity.App1.expo
        (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)))⁻¹ := by
    rw [← MulAut.conj_apply, map_pow]
    rw [show MulAut.conj t (p.2 : G) = (p.2 : G)⁻¹ by
      rw [MulAut.conj_apply]; exact p.2.2.2]
    rw [inv_pow]
  exact ⟨(p.1 : G),
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hcD, hcc⟩, hcN⟩,
    (p.2 : G) ^ Work.DoubleTransitivity.App1.expo
      (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)),
    ⟨hyD, hyinv⟩, hyN, hm_eq.symm⟩

/-! ## Ch. II §4 Lemma 1: `N_K(X) ⊆ C_G(X)` -/

/-- **Peterfalvi I Ch. II §4 Lemma 1 (p. 169), in the form used here.**  If `X ≤ V = C_D(t)` and
`k ∈ K = J(D,t)` normalises `X`, then `k` centralises `X`.

`t·k` is an involution and `t·(t·k) = k` has odd order (as `k ∈ D`), so `t` and `t·k` are
conjugate by an involution `u ∈ ⟨t, t·k⟩ ≤ N_G(X)`; hence `t·k = u t u⁻¹ ∈ C_G(X)`, and so is
`k = t·(t·k)`. -/
theorem mem_centralizer_of_mem_invertedBy_normalizer {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} (hH : IsStronglyEmbedded H) (ht : orderOf t = 2) (htH : t ∉ H)
    {X : Subgroup G} (hXV : X ≤ centD H t) {k : G} (hk : k ∈ invertedBy (twoPoint H t) t)
    (hkn : k ∈ Subgroup.normalizer (X : Set G)) : k ∈ Subgroup.centralizer (X : Set G) := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht2
  have hkD : k ∈ twoPoint H t := hk.1
  have hkt : t * k * t = k⁻¹ := by simpa [htinv] using hk.2
  have hoddD : Odd (Nat.card ↥(twoPoint H t)) :=
    Work.ThreePoints.IsStronglyEmbedded.odd_card_inf_conj hH htH
  have hdvd : orderOf k ∣ Nat.card ↥(twoPoint H t) := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hkD)
  have hoddk : Odd (orderOf k) := Work.ThreePoints.Odd.of_dvd hdvd hoddD
  have htC : t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Work.ThreePoints.mem_centD.mp (hXV hx)).2.2
  have htN : t ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer (X : Set G) htC
  have htk_ne : t * k ≠ 1 := by
    intro hcon
    have htk_eq : t = k⁻¹ := eq_inv_of_mul_eq_one_left hcon
    refine htH ?_
    rw [htk_eq]
    exact (show twoPoint H t ≤ H from inf_le_left) ((twoPoint H t).inv_mem hkD)
  have htkinv : (t * k)⁻¹ = t * k := by
    rw [mul_inv_rev, htinv, ← hkt, mul_assoc, ht2, mul_one]
  have htk_mul : (t * k) * (t * k) = 1 := by
    have h := mul_inv_cancel (t * k)
    rwa [htkinv] at h
  have htk2 : orderOf (t * k) = 2 := Work.ThreePoints.orderOf_eq_two_of htk_ne htk_mul
  have hmul : t * (t * k) = k := by rw [← mul_assoc, ht2, one_mul]
  have hodd_tk : Odd (orderOf (t * (t * k))) := by rw [hmul]; exact hoddk
  obtain ⟨u, -, huconj, hucl⟩ :=
    Work.ThreePoints.exists_involution_conj_of_odd_orderOf_mul ht htk2 hodd_tk
  have htkN : t * k ∈ Subgroup.normalizer (X : Set G) := Subgroup.mul_mem _ htN hkn
  have hcl : Subgroup.closure ({t, t * k} : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact htN
    · exact htkN
  have huN : u ∈ Subgroup.normalizer (X : Set G) := hcl hucl
  have htkC : t * k ∈ Subgroup.centralizer (X : Set G) := by
    rw [← huconj]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    have hu' := Subgroup.mem_centralizer_iff.mp htC
    have hy' : u⁻¹ * y * u ∈ X := (Subgroup.mem_normalizer_iff''.mp huN y).mp hy
    have h := hu' (u⁻¹ * y * u) hy'
    calc y * (u * t * u⁻¹) = u * ((u⁻¹ * y * u) * t) * u⁻¹ := by group
      _ = u * (t * (u⁻¹ * y * u)) * u⁻¹ := by rw [h]
      _ = (u * t * u⁻¹) * y := by group
  have hprod : t * (t * k) ∈ Subgroup.centralizer (X : Set G) := Subgroup.mul_mem _ htC htkC
  rwa [hmul] at hprod

/-! ## `C_G(X)` is transitive on `Ω_X` -/

/-- **`C_G(X)` is transitive on `Ω_X = fixedPts H X`** for `X ≤ V = C_D(t)`.  By Appendix II (7)'s
core (`app2_7_core`) applied to the base pair, `Q ⊓ C_G(X)` is sharply transitive on
`Ω_X ∖ {H}`; since `t ∈ C_G(X)` and `t • (t·H) = H`, every point of `Ω_X` is `c • H` with
`c ∈ C_G(X)`. -/
theorem centralizer_transitive_fixedPts {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {X : Subgroup G} (hXV : X ≤ centD H t) :
    ∀ ω ∈ fixedPts H X, ∃ l : ↥(Subgroup.centralizer (X : Set G)),
      (l : G) • ((1 : G) : G ⧸ H) = ω := by
  have hXY : X ≤ MulAction.stabilizer G ((1 : G) : G ⧸ H) ⊓
      MulAction.stabilizer G ((t : G) : G ⧸ H) := by
    rw [stabilizer_one H, Work.ThreePoints.stabilizer_mk H t]
    exact fun x hx => Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hXV hx)).1).1,
       (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hXV hx)).1).2⟩
  have huv : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
    intro hcon
    refine h.not_mem ?_
    have h2 : (1 : G)⁻¹ * t ∈ H := QuotientGroup.eq.mp hcon
    simpa using h2
  have hbd := base_regular_data h (a := ((1 : G) : G ⧸ H)) (b := ((t : G) : G ⧸ H)) rfl rfl
  have hcore := Work.DoubleTransitivity.App2.app2_7_core (X := G) (E := G ⧸ H)
    (u := ((1 : G) : G ⧸ H)) (v := ((t : G) : G ⧸ H)) (Q := Q) (Y := X)
    huv hbd.1 hbd.2.1 hbd.2.2.1 hbd.2.2.2 hXY
  have htC : t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Work.ThreePoints.mem_centD.mp (hXV hx)).2.2
  intro ω hω
  by_cases hω0 : ω = ((1 : G) : G ⧸ H)
  · exact ⟨1, by rw [hω0]; simp⟩
  · obtain ⟨q, hqv, -⟩ := hcore.2.2 ω hω hω0
    refine ⟨⟨(q : G) * t, Subgroup.mul_mem _ q.2.2 htC⟩, ?_⟩
    have htv : t • ((1 : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by simp
    show ((q : G) * t) • ((1 : G) : G ⧸ H) = ω
    rw [mul_smul, htv, hqv]

/-! ## `C_G(X)` is `2`-transitive on `Ω_X` -/

/-- **Peterfalvi II Ch. V §2 Lemma 2 (a), `2`-transitivity part.**  If `(C_G(X), C_G(X) ⊓ H)` is a
Bender family (`hfam`), then `C_G(X)` acts `2`-transitively on `Ω_X = fixedPts H X`.  This is the
transfer of the `2`-transitivity of `C_G(X)` on `C_G(X) ⧸ (C_G(X) ⊓ H)` along the orbit map
(`ch1s4_transfer`), using transitivity of `C_G(X)` on `Ω_X`. -/
theorem centralizer_twoTransitive {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {X : Subgroup G} (hXV : X ≤ centD H t)
    (hfam : IsBenderFamily ↥(Subgroup.centralizer (X : Set G))
      ((H ⊓ Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.centralizer (X : Set G)))) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.centralizer (X : Set G)) (fixedPts H X) := by
  have hXH : X ≤ H := fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hXV hx)).1).1
  refine Work.ThreePoints.P3Sub.ch1s4_transfer (L := Subgroup.centralizer (X : Set G)) (H := H)
    (S := fixedPts H X) ?_ ?_ ?_ ?_
  · have h2 := hfam.twoTransitive
    rw [inf_comm] at h2
    exact h2
  · rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, stabilizer_one H]; exact hXH
  · intro l ω hω
    exact Work.ThreePoints.P3NeBot.normalizer_preserves_fixedPts
      (Subgroup.centralizer_le_normalizer (X : Set G) l.2) hω
  · intro ω hω
    exact centralizer_transitive_fixedPts h hXV ω hω

/-! ## Peterfalvi II Ch. V §2 Lemma 2 (b) -/

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem lemma2b {G : Type} [Group G] [Finite G] (hS : Situation G) (hC4 : ChIIFourProp) (H Q : Subgroup G) (t : G) (h : IsSplitRankOne H Q t) (X : Subgroup G) (hXV : X ≤ centD H t) (hXne : X ≠ ⊥) (hfam : IsBenderFamily ↥(Subgroup.centralizer (X : Set G)) ((H ⊓ Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.centralizer (X : Set G)))) : Subgroup.normalizer (X : Set G) = Subgroup.centralizer (X : Set G) ⊔ (centD H t ⊓ Subgroup.normalizer (X : Set G)) := by
  classical
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN
  set V : Subgroup G := centD H t with hV
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer (X : Set G)
  have h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub C (fixedPts H X) :=
    centralizer_twoTransitive h hXV hfam
  have hbase : ((1 : G) : G ⧸ H) ∈ fixedPts H X := by
    rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, stabilizer_one H]
    exact fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hXV hx)).1).1
  have htb : ((t : G) : G ⧸ H) ∈ fixedPts H X := by
    rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, Work.ThreePoints.stabilizer_mk H t]
    exact fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hXV hx)).1).2
  have hne : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
    intro hcon
    refine h.not_mem ?_
    have h2 : (1 : G)⁻¹ * t ∈ H := QuotientGroup.eq.mp hcon
    simpa using h2
  refine le_antisymm ?_ ?_
  · intro g hg
    have hginv : g⁻¹ ∈ N := N.inv_mem hg
    have hb1 : g⁻¹ • ((1 : G) : G ⧸ H) ∈ fixedPts H X :=
      Work.ThreePoints.P3NeBot.normalizer_preserves_fixedPts hginv hbase
    have hb2 : g⁻¹ • ((t : G) : G ⧸ H) ∈ fixedPts H X :=
      Work.ThreePoints.P3NeBot.normalizer_preserves_fixedPts hginv htb
    have hne2 : g⁻¹ • ((1 : G) : G ⧸ H) ≠ g⁻¹ • ((t : G) : G ⧸ H) :=
      fun hcon => hne (MulAction.injective g⁻¹ hcon)
    obtain ⟨y, hyC, hy1, hy2⟩ :=
      h2t ((1 : G) : G ⧸ H) hbase ((t : G) : G ⧸ H) htb hne
        (g⁻¹ • ((1 : G) : G ⧸ H)) hb1 (g⁻¹ • ((t : G) : G ⧸ H)) hb2 hne2
    have hyN : y ∈ N := hCN hyC
    have hgfH : g * y ∈ H := by
      rw [← stabilizer_one H, MulAction.mem_stabilizer_iff]
      rw [mul_smul, hy1, smul_inv_smul]
    have hgfT : g * y ∈ Submission.Blueprint.conj t H := by
      rw [← Work.ThreePoints.stabilizer_mk H t, MulAction.mem_stabilizer_iff]
      rw [mul_smul, hy2, smul_inv_smul]
    have hgfDN : g * y ∈ twoPoint H t ⊓ N :=
      ⟨⟨hgfH, hgfT⟩, N.mul_mem hg hyN⟩
    obtain ⟨c, hc, y', hy'K, hy'N, hgy⟩ := exists_mul_of_mem_twoPoint_inf_normalizer h hXV hgfDN
    have hy'C : y' ∈ C :=
      mem_centralizer_of_mem_invertedBy_normalizer h.stronglyEmbedded h.invol h.not_mem hXV hy'K hy'N
    have hmem3 : g * y ∈ C ⊔ (V ⊓ N) := by
      rw [hgy]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hy'C)
    have hgy_eq : g = (g * y) * y⁻¹ := by group
    rw [hgy_eq]
    exact Subgroup.mul_mem _ hmem3 (Subgroup.mem_sup_left (C.inv_mem hyC))
  · exact sup_le hCN inf_le_right

end Work.ThmF.ChV12
