import Mathlib
import Submission.Work.BSW.Concl

/-!
# Bender's conclusion (1)–(4) gives the Zassenhaus action

This file provides Bender's conclusion (1)–(4) as the predicate `IsBSWConf` (with the witnesses `Q`
and `D` explicit) together with the API and the three Zassenhaus conditions `zass_faithful`,
`zass_card`, `zass_pretransitive`, `zass_twoPoint`; the assembly into
`Work.BSW.BSWDataZassProp` (together with `zass_fix`) is in
`Submission/Work/BSW/Cases/bswDataZassProp.lean`, and `zass_fix` itself in
`Submission/Work/BSW/Cases/DataZass/zass_fix.lean`.

The proof works with the explicit witnesses `Q` (of order `q`, `C_G(Q) = Q`) and `D` (abelian of
order `(q-1)/2`, complement of `Q` in `N_G(Q)`), bundled in `IsBSWConf`, and with
`H := N_G(Q)`.

The group-theoretic core is:
* `|G| = q(q²-1)/2` has `p`-part exactly `q`, so `Q` is a Sylow `p`-subgroup, hence abelian
  because `C_G(Q) = Q`;
* `H = N_G(Q)` has order `q(q-1)/2` and index `q+1`, and `H` is transitive on the Sylow
  `p`-subgroups different from `Q` (orbit–stabilizer, using `|N_G(Q) ∩ N_G(Q')| = (q-1)/2`);
* every element of `H \ Q` has `p'`-order (a counting statement over the Sylow `p`-subgroups),
  and consequently `C_Q(d) = 1` for `d ∈ D#`.

Both enter the fixed-point count: for `g ≠ 1` fixing a point we may take `g ∈ H`, and then `g`
lies in at most one complement of `Q` in `H`.

## The two counts used in 3.7

The five conditions of `ZassHyps2` are isolated as `zass_faithful`, `zass_card`,
`zass_pretransitive`, `zass_fix`, `zass_twoPoint`; the assembly of `bswDataZassProp` from them
is in `Cases/bswDataZassProp.lean`.

The two counts that Bender's remark uses are
* `|N_G(Q) ∩ N_G(Q')| = (q-1)/2` for distinct Sylow `p`-subgroups (needed for the transitivity of
  `H` on the other Sylow subgroups, and hence for double transitivity), and
* the number of `p`-elements of `G` being `q²`,
and both rest on Bender 1974, **3.7** ("a Sylow `p`-subgroup is disjoint from its conjugates").
That statement is *not* derivable from Bender's conclusion (1)–(4) by the obvious argument:
the abstract statement "two distinct abelian Sylow `p`-subgroups of a finite group whose order is
the full `p`-part of `|G|` intersect trivially" is false — `G = A₄` (`p = 2`, `q = 4`) and
`G = S₃ × C₂` (`p = 2`, two Klein four-groups in a group of order `12`) are counterexamples;
even adding self-centrality of the Sylow subgroup does not repair it (`C_{A₄}(V₄) = V₄`, yet
distinct Klein four-groups meet in a `C₂`).  In the source, 3.7 is obtained in §3 (3.5–3.7) from
the full `BSWHyps2` configuration, using the involution counts of 3.1–3.4.

`IsBSWData G q` now records 3.7 as an explicit conjunct (the clause `IsBSWDataQ.disjoint`), so
the two counts above are hypotheses here rather than consequences of (1)–(4); `IsBSWConf` below
carries the same clause.

## The "≤ 2 fixed points" clause

`zass_faithful`, `zass_card`, `zass_pretransitive` and `zass_twoPoint` below are proved; the last
clause (no nonidentity element fixes three points) is `zass_fix`, proved in the companion file
`Submission/Work/BSW/Cases/DataZass/zass_fix.lean`.  The proof needs `C_Q(D) = 1`, i.e.
`Q ⊓ N_G(D) = ⊥`, i.e. `N_G(Q) = Q ⋊ D` a Frobenius group with kernel `Q`, and this is supplied by
the strengthened clause (4) recorded in `IsBSWConf`:

* Bender's (4) is the **equality** `N_G(X) = N_G(D) = D⟨u⟩` for every `1 ≠ X ≤ D` (with `u ∉ D` an
  involution inverting `D`); `IsBSWConf` below records this equality (not merely `≤`) together with
  `N_G(D) = D ⊔ ⟨u⟩`.  Hence `|N_G(D)| = q - 1`, which is coprime to `p` (as `q = p^k`), and so
  `Q ⊓ N_G(D) = ⊥`; in particular `C_Q(D) = 1`.
* The reduction: if `1 ≠ g` fixes a point, conjugate so that `g ∈ N := N_G(Q)`.  A nonidentity
  `p`-element `g ∈ Q#` fixes only one point (a `p`-element normalizing a Sylow `Q'` lies in `Q'`,
  so TI gives `Q' = Q`); for `g ∈ N ∖ Q` with `g_p ≠ 1` the fixed points lie in `Fix(g_p) = {Q}`.
  So only the case `g ∈ D#` remains, where `g` acts on the `q` cosets `≠ N`; those fixed by `g` are
  the conjugates of `Q` normalized by `g`, and the normalizer equation above makes this set have at
  most one element besides `Q` — hence at most two fixed points in total.
* (The earlier note that the clause is *equivalent to* `C_Q(D) = 1` remains true; the point is that
  the strengthened clause (4) now makes this available.)

## API notes (each of these cost an iteration)

* `Subgroup.closure_induction` is the *dependent-motive* form (`p : (g : G) → g ∈ closure k → Prop`);
  for "every element of `H ⊔ K` is a product", `Subgroup.closure_induction_left` is easier: its
  bullets are "multiply on the left by `a ∈ H ∪ K`".
* `Set.ncard_congr`'s injectivity argument binds the two *points* before the two membership proofs:
  `∀ a b (ha : a ∈ s) (hb : b ∈ s), f a ha = f b hb → a = b`.
* The final `Nat.card ↥_ ↔ Set.ncard` step: `rw` cannot match `↥` against `↑↑`; use
  `calc … := Nat.card_coe_set_eq _` and close with `by congr 1` (defeq).  `Nat.card_congr` wants an
  `Equiv`, so a `MulEquiv` needs `.toEquiv`.
* There is no `Nat.card_dvd_of_injective`: for `H ≤ K` go through
  `Subgroup.card_subgroup_dvd_card` applied to `H.subgroupOf K`, then transport across
  `Subgroup.subgroupOfEquivOfLe`.
* `IsPGroup.iff_card` / `IsPGroup.iff_orderOf` are bare iff's, not methods: write
  `IsPGroup.iff_card.mp h`, not `h.iff_card.mp`.
* `G ⧸ N_G(Q)` is a set-quotient, not a group: the base point is `((1 : G) : G ⧸ N_G(Q))`, and
  `MulAction.stabilizer G (↑1)` is the subgroup `N_G(Q)` itself.
* `G`'s `G ⧸ N_G(Q)`-action unfolds definitionally: `g • (x : G ⧸ H) = (g * x : G)`.

A `p`-element fact that 3.7 alone does *not* give, and which the `≤` direction of
`stab_inf_stab_card` needs, is `mem_of_pElement_of_mem_normalizer` below: a `p`-element of
`N_G(Q)` lies in `Q`, because `⟨y⟩ ⊔ Q` is a `p`-subgroup containing the Sylow `Q`.

-/

open scoped MatrixGroups Pointwise

namespace Work.BSW.Cases

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G]

/-- Bender's conclusion (1)–(4) together with 3.7 (the Sylow `p`-subgroup `Q` is disjoint from
its conjugates), with the witnesses `Q` and `D` explicit. -/
def IsBSWConf (q : ℕ) (Q D : Subgroup G) : Prop :=
  Nat.card Q = q ∧ centralizer (Q : Set G) = Q ∧
    (∀ g : G, g ∉ normalizer (Q : Set G) → Q ⊓ conjSub g Q = ⊥) ∧
    IsMulCommutative D ∧
    Nat.card D = (q - 1) / 2 ∧ Q ⊓ D = ⊥ ∧ normalizer (Q : Set G) = Q ⊔ D ∧
    (∀ X : Subgroup G, X ≠ ⊥ → X ≤ D →
      normalizer (X : Set G) = normalizer (D : Set G)) ∧
    (∃ u : G, orderOf u = 2 ∧ u ∉ D ∧ Inverts u D ∧
      normalizer (D : Set G) = D ⊔ zpowers u) ∧
    Nat.card G = q * (q * q - 1) / 2

theorem IsBSWConf.card_Q {q : ℕ} {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D) :
    Nat.card Q = q := h.1

theorem IsBSWConf.centralizer_Q {q : ℕ} {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D) :
    centralizer (Q : Set G) = Q := h.2.1

/-- Bender 3.7: `Q` is disjoint from its conjugates. -/
theorem IsBSWConf.disjoint {q : ℕ} {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D) :
    ∀ g : G, g ∉ normalizer (Q : Set G) → Q ⊓ conjSub g Q = ⊥ := h.2.2.1

theorem IsBSWConf.comm_D {q : ℕ} {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D) :
    IsMulCommutative D := h.2.2.2.1

theorem IsBSWConf.card_D {q : ℕ} {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D) :
    Nat.card D = (q - 1) / 2 := h.2.2.2.2.1

theorem IsBSWConf.inf_bot {q : ℕ} {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D) :
    Q ⊓ D = ⊥ := h.2.2.2.2.2.1

theorem IsBSWConf.normalizer_Q {q : ℕ} {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D) :
    normalizer (Q : Set G) = Q ⊔ D := h.2.2.2.2.2.2.1

theorem IsBSWConf.normalizer_eq {q : ℕ} {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D)
    {X : Subgroup G} (hX : X ≠ ⊥) (hXD : X ≤ D) :
    normalizer (X : Set G) = normalizer (D : Set G) :=
  h.2.2.2.2.2.2.2.1 X hX hXD

theorem IsBSWConf.normalizer_le {q : ℕ} {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D)
    {X : Subgroup G} (hX : X ≠ ⊥) (hXD : X ≤ D) :
    normalizer (X : Set G) ≤ normalizer (D : Set G) :=
  le_of_eq (h.normalizer_eq hX hXD)

theorem IsBSWConf.exists_inverting_strong {q : ℕ} {Q D : Subgroup G}
    (h : IsBSWConf (G := G) q Q D) :
    ∃ u : G, orderOf u = 2 ∧ u ∉ D ∧ Inverts u D ∧ normalizer (D : Set G) = D ⊔ zpowers u :=
  h.2.2.2.2.2.2.2.2.1

theorem IsBSWConf.exists_inverting {q : ℕ} {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D) :
    ∃ u : G, orderOf u = 2 ∧ u ∉ D ∧ Inverts u D :=
  let ⟨u, h1, h2, h3, _⟩ := h.exists_inverting_strong
  ⟨u, h1, h2, h3⟩

theorem IsBSWConf.card_G {q : ℕ} {Q D : Subgroup G} (h : IsBSWConf (G := G) q Q D) :
    Nat.card G = q * (q * q - 1) / 2 := h.2.2.2.2.2.2.2.2.2

/-- `IsBSWData G q` unpacks to the prime power data plus `IsBSWConf`. -/
theorem IsBSWData.exists_conf {q : ℕ} (h : IsBSWData G q) :
    (∃ p k : ℕ, Fact p.Prime ∧ Odd p ∧ q = p ^ k) ∧ 5 ≤ q ∧
      ∃ Q D : Subgroup G, IsBSWConf (G := G) q Q D := by
  obtain ⟨⟨p, k, hfact, hodd, hq⟩, h5, Q, hQcard, hCQ, hdisj, D, hDab, hDcard, hQD, hN, hnorm,
    hu, hGcard⟩ := h
  exact ⟨⟨p, k, hfact, hodd, hq⟩, h5, Q, D,
    ⟨hQcard, hCQ, hdisj, hDab, hDcard, hQD, hN, hnorm, hu, hGcard⟩⟩

/-! ## A cardinality lemma for subgroups with trivial intersection -/

section CardSup

variable {H K : Subgroup G}

/-- If `H ⊓ K = ⊥` and `K` normalizes `H`, then `|H ⊔ K| = |H| * |K|`: every element of `H ⊔ K`
is a product `h * k` (because `K` normalizes `H`), and the multiplication map
`H × K → H ⊔ K` is then a bijection. -/
theorem card_sup_of_inf_bot_of_le_normalizer (hinf : H ⊓ K = ⊥)
    (hK : K ≤ normalizer (H : Set G)) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have hconj : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H := by
    intro k hk h hh
    have hmem := hK hk
    rw [mem_normalizer_iff] at hmem
    exact (hmem h).mp hh
  have hsub : (↑(H ⊔ K) : Set G) ⊆ (H : Set G) * (K : Set G) := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction_left
      (p := fun y _ => y ∈ (H : Set G) * (K : Set G)) ?_ ?_ ?_ hx
    · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
    · intro a ha b hb hmem
      rcases ha with ha | ha
      · obtain ⟨h, hh, k, hk, rfl⟩ := hmem
        exact ⟨a * h, H.mul_mem ha hh, k, hk, by group⟩
      · obtain ⟨h, hh, k, hk, rfl⟩ := hmem
        exact ⟨a * h * a⁻¹, hconj a ha h hh, a * k, K.mul_mem ha hk, by group⟩
    · intro a ha b hb hmem
      rcases ha with ha | ha
      · obtain ⟨h, hh, k, hk, rfl⟩ := hmem
        exact ⟨a⁻¹ * h, H.mul_mem (H.inv_mem ha) hh, k, hk, by group⟩
      · obtain ⟨h, hh, k, hk, rfl⟩ := hmem
        exact ⟨a⁻¹ * h * a, by simpa using hconj a⁻¹ (K.inv_mem ha) h hh, a⁻¹ * k,
          K.mul_mem (K.inv_mem ha) hk, by group⟩
  have hmul : (↑(H ⊔ K) : Set G) = (H : Set G) * (K : Set G) :=
    Set.Subset.antisymm hsub fun z hz => by
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      exact mul_mem_sup ha hb
  have hncard : ((H : Set G) * (K : Set G)).ncard = (H : Set G).ncard * (K : Set G).ncard := by
    rw [← Set.ncard_prod]
    refine (Set.ncard_congr (s := (H : Set G) ×ˢ (K : Set G))
      (t := (H : Set G) * (K : Set G)) (fun p _ => p.1 * p.2) ?_ ?_ ?_).symm
    · rintro ⟨a, b⟩ hp
      rw [Set.mem_prod] at hp
      exact ⟨a, hp.1, b, hp.2, rfl⟩
    · rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ hp hq heq
      rw [Set.mem_prod] at hp hq
      simp only [Prod.fst, Prod.snd] at heq
      have hmem : a₂⁻¹ * a₁ ∈ H ⊓ K := by
        refine ⟨H.mul_mem (H.inv_mem hq.1) hp.1, ?_⟩
        have h6 : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
          have h7 : a₂⁻¹ * (a₁ * b₁) = b₂ := by rw [heq]; group
          calc a₂⁻¹ * a₁ = (a₂⁻¹ * (a₁ * b₁)) * b₁⁻¹ := by group
            _ = b₂ * b₁⁻¹ := by rw [h7]
        rw [h6]
        exact K.mul_mem hq.2 (K.inv_mem hp.2)
      rw [hinf] at hmem
      have ha1 : a₂⁻¹ * a₁ = 1 := Subgroup.mem_bot.mp hmem
      have ha : a₁ = a₂ := by
        calc a₁ = a₂ * (a₂⁻¹ * a₁) := by group
          _ = a₂ * 1 := by rw [ha1]
          _ = a₂ := by simp
      have hb : b₁ = b₂ := by
        have h8 : a₁ * b₁ = a₁ * b₂ := by rw [heq, ha]
        exact mul_left_cancel h8
      exact Prod.ext ha hb
    · rintro z ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), by rw [Set.mem_prod]; exact ⟨ha, hb⟩, rfl⟩
  calc Nat.card ↥(H ⊔ K) = ((↑(H ⊔ K) : Set G)).ncard := Nat.card_coe_set_eq _
    _ = ((H : Set G) * (K : Set G)).ncard := by rw [hmul]
    _ = (H : Set G).ncard * (K : Set G).ncard := hncard
    _ = Nat.card ↥H * Nat.card ↥K := by congr 1

end CardSup

/-! ## The five Zassenhaus conditions

We record them as separate statements about the explicit configuration, so that they can be
established in the companion files. -/

section Conditions

variable {q : ℕ} {Q D : Subgroup G}

/-- The degree of the action is `q + 1`: `|N_G(Q)| = |Q ⊔ D| = q·(q-1)/2` and
`|G| = q(q²-1)/2`. -/
theorem zass_card (h5 : 5 ≤ q) (hodd : Odd q) (h : IsBSWConf (G := G) q Q D) :
    Nat.card (G ⧸ normalizer (Q : Set G)) = q + 1 := by
  have hDle : D ≤ normalizer (Q : Set G) := by
    rw [h.normalizer_Q]; exact le_sup_right
  have hcardH : Nat.card ↥(normalizer (Q : Set G)) = q * ((q - 1) / 2) := by
    rw [h.normalizer_Q, card_sup_of_inf_bot_of_le_normalizer h.inf_bot hDle, h.card_Q,
      h.card_D]
  have hmul := Subgroup.card_mul_index (normalizer (Q : Set G))
  rw [hcardH, h.card_G] at hmul
  have hpos : 0 < q * ((q - 1) / 2) := by
    have h1 : 0 < q := by omega
    have h2 : 0 < (q - 1) / 2 := Nat.div_pos (by omega : 2 ≤ q - 1) (by norm_num : 0 < 2)
    exact Nat.mul_pos h1 h2
  have harith : q * (q * q - 1) / 2 = q * ((q - 1) / 2) * (q + 1) := by
    obtain ⟨t, ht⟩ := hodd
    have h2 : (q - 1) * (q + 1) = q * q - 1 := by
      rw [ht]
      have e1 : 2 * t + 1 - 1 = 2 * t := by omega
      have e2 : 2 * t + 1 + 1 = 2 * (t + 1) := by omega
      rw [e1, e2]
      have e3 : (2 * t + 1) * (2 * t + 1) = 2 * t * (2 * (t + 1)) + 1 := by ring
      rw [e3, Nat.add_sub_cancel]
    have h1 : 2 * ((q - 1) / 2) = q - 1 := by
      rw [ht, show (2 * t + 1 - 1) = 2 * t by omega, Nat.mul_div_right t (by norm_num : 0 < 2)]
    have h3 : q * q - 1 = 2 * ((q - 1) / 2 * (q + 1)) := by
      rw [show 2 * ((q - 1) / 2 * (q + 1)) = 2 * ((q - 1) / 2) * (q + 1) by ring, h1]
      exact h2.symm
    rw [h3]
    have hthis : q * (2 * ((q - 1) / 2 * (q + 1))) / 2 = q * ((q - 1) / 2 * (q + 1)) := by
      rw [show q * (2 * ((q - 1) / 2 * (q + 1))) = 2 * (q * ((q - 1) / 2 * (q + 1))) by ring]
      exact Nat.mul_div_right (q * ((q - 1) / 2 * (q + 1))) (by norm_num : 0 < 2)
    rw [hthis]; ring
  have hmul' : q * ((q - 1) / 2) * (normalizer (Q : Set G)).index
      = q * ((q - 1) / 2) * (q + 1) := by
    rw [← harith]; exact hmul
  have hindex : (normalizer (Q : Set G)).index = q + 1 :=
    Nat.eq_of_mul_eq_mul_left hpos hmul'
  rw [← Subgroup.index_eq_card]
  exact hindex

/-- `H = N_G(Q)` acts faithfully on its coset space: the kernel of the action is the normal core
of `H`, which is a normal subgroup of the simple group `G` contained in the proper subgroup `H`,
hence trivial. -/
theorem zass_faithful (hS : IsSimpleGroup G) (h5 : 5 ≤ q) (hodd : Odd q)
    (h : IsBSWConf (G := G) q Q D) :
    FaithfulSMul G (G ⧸ normalizer (Q : Set G)) := by
  have hcard := zass_card h5 hodd h
  have hHne : normalizer (Q : Set G) ≠ ⊤ := by
    intro htop
    have h1 : Nat.card (G ⧸ normalizer (Q : Set G)) = 1 := by
      rw [htop, ← Subgroup.index_eq_card, Subgroup.index_top]
    omega
  have hcore : (normalizer (Q : Set G)).normalCore = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (normalizer (Q : Set G)).normalCore with hb | ht
    · exact hb
    · exfalso
      have h2 : (⊤ : Subgroup G) ≤ normalizer (Q : Set G) := ht ▸ Subgroup.normalCore_le _
      exact hHne (top_le_iff.mp h2)
  refine ⟨fun {m₁ m₂} hsm => ?_⟩
  have hmem : m₁⁻¹ * m₂ ∈ (normalizer (Q : Set G)).normalCore := by
    rw [Subgroup.normalCore_eq_iInf_comap_conj]
    refine Subgroup.mem_iInf.mpr fun x => ?_
    rw [Subgroup.mem_comap]
    change x * (m₁⁻¹ * m₂) * x⁻¹ ∈ normalizer (Q : Set G)
    have hq := hsm ((x⁻¹ : G) : G ⧸ normalizer (Q : Set G))
    have hq' : (((m₁ * x⁻¹ : G)) : G ⧸ normalizer (Q : Set G))
        = (((m₂ * x⁻¹ : G)) : G ⧸ normalizer (Q : Set G)) := hq
    have hq'' := QuotientGroup.eq.mp hq'
    convert hq'' using 1
    group
  have hone : m₁⁻¹ * m₂ = 1 := by
    rw [hcore] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact inv_mul_eq_one.mp hone

/-- Membership in a conjugate: `x ∈ aQa⁻¹ ↔ a⁻¹xa ∈ Q`. -/
theorem mem_conjSub_iff_H {a x : G} {Q : Subgroup G} :
    x ∈ conjSub a Q ↔ a⁻¹ * x * a ∈ Q := by
  rw [conjSub, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-- Conjugation and normalization commute: `N_G(aQa⁻¹) = a N_G(Q) a⁻¹`.  Not in Mathlib (there is
no `Subgroup.normalizer_map`); it is what lets the two applications of
`mem_of_pElement_of_mem_normalizer` in the `≤` direction of `stab_inf_stab_card` be made at `Q` and
at `conjSub a Q` with the same `p`-part data. -/
theorem normalizer_conjSub_H (a : G) (Q : Subgroup G) :
    normalizer ((conjSub a Q : Subgroup G) : Set G) = conjSub a (normalizer (Q : Set G)) := by
  ext g
  rw [mem_conjSub_iff_H]
  constructor
  · intro hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro q
    have h := hg (a * q * a⁻¹)
    rw [mem_conjSub_iff_H, mem_conjSub_iff_H] at h
    convert h using 2 <;> group
  · intro hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro h
    rw [mem_conjSub_iff_H, mem_conjSub_iff_H]
    have h := hg (a⁻¹ * h * a)
    convert h using 2 <;> group

/-- Elements of a subgroup of order `p^k` have `p`-power order.  (Route: `IsPGroup.iff_orderOf` at
the subtype, then transport `y ^ (p^j) = 1` across the coercion and apply `Nat.dvd_prime_pow` — this
avoids needing the subtype-coercion lemma for `orderOf`.) -/
theorem exists_orderOf_eq_pow_of_mem {p k : ℕ} (hp : p.Prime) {Q : Subgroup G}
    (hQ : Nat.card Q = p ^ k) {y : G} (hy : y ∈ Q) : ∃ j : ℕ, orderOf y = p ^ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQp : IsPGroup p ↥Q := IsPGroup.of_card hQ
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hQp) ⟨y, hy⟩
  have h2 : y ^ (p ^ j) = 1 := by
    have h3 : (⟨y, hy⟩ : ↥Q) ^ (p ^ j) = 1 := by
      rw [← hj]
      exact pow_orderOf_eq_one _
    simpa using Subtype.ext_iff.mp h3
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp ((orderOf_dvd_iff_pow_eq_one).mpr h2)
  exact ⟨i, hi⟩

/-- The stabilizer of the base point of `G ⧸ H` is `H`. -/
theorem stabilizer_base {H : Subgroup G} :
    MulAction.stabilizer G ((1 : G) : G ⧸ H) = H := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  change ((g * 1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) ↔ g ∈ H
  rw [QuotientGroup.eq]
  simp only [mul_one, inv_one, one_mul]
  exact Subgroup.inv_mem_iff _

/-- The stabilizer of the coset `aH` is `aHa⁻¹`. -/
theorem stabilizer_conj {a : G} {H : Subgroup G} :
    MulAction.stabilizer G ((a : G) : G ⧸ H) = conjSub a H := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  change ((g * a : G) : G ⧸ H) = ((a : G) : G ⧸ H) ↔ g ∈ conjSub a H
  rw [QuotientGroup.eq, mem_conjSub_iff_H]
  have h1 : (g * a)⁻¹ * a = (a⁻¹ * g * a)⁻¹ := by group
  rw [h1]
  exact Subgroup.inv_mem_iff _

/-- A `p`-element of the normalizer of a subgroup `Q` whose order is the full `p`-part of
`|N_G(Q)|` already lies in `Q`: the product `Y := ⟨y⟩ ⊔ Q` is a `p`-subgroup containing `Q` (a
`p`-subgroup normalizing another has a `p`-subgroup product), so `|Y| = p^n` divides
`|N_G(Q)| = p^k · m`; as `p ∤ m` this gives `p^n ∣ p^k`, hence `p^n ≤ p^k = |Q| ≤ |Y|`, so
`Y = Q` and `y ∈ Q`. -/
theorem mem_of_pElement_of_mem_normalizer {p k m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m)
    {Q : Subgroup G} (hQ : Nat.card Q = p ^ k)
    (hM : Nat.card (normalizer (Q : Set G)) = p ^ k * m)
    {y : G} (hy : y ∈ normalizer (Q : Set G)) (horder : ∃ j : ℕ, orderOf y = p ^ j) :
    y ∈ Q := by
  obtain ⟨j, hj⟩ := horder
  haveI : Fact p.Prime := ⟨hp⟩
  have hzpM : zpowers y ≤ normalizer (Q : Set G) := Subgroup.zpowers_le.mpr hy
  have hQM : Q ≤ normalizer (Q : Set G) := le_normalizer
  have hYM : zpowers y ⊔ Q ≤ normalizer (Q : Set G) := sup_le hzpM hQM
  have hzpp : IsPGroup p ↥(zpowers y) := IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hQp : IsPGroup p ↥Q := IsPGroup.of_card hQ
  have hYp : IsPGroup p ↥(zpowers y ⊔ Q) :=
    IsPGroup.to_sup_of_normal_right' hzpp hQp hzpM
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hYp
  have hYdvd : Nat.card ↥(zpowers y ⊔ Q) ∣ Nat.card ↥(normalizer (Q : Set G)) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv) ▸
      Subgroup.card_subgroup_dvd_card ((zpowers y ⊔ Q).subgroupOf (normalizer (Q : Set G)))
  have hdvd : p ^ n ∣ p ^ k * m := by
    rw [← hn, ← hM]
    exact hYdvd
  have hcop : Nat.Coprime (p ^ n) m :=
    Nat.Coprime.pow_left n ((hp.coprime_iff_not_dvd).mpr hm)
  have hnle : n ≤ k := by
    refine (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp ?_
    exact hcop.dvd_of_dvd_mul_right hdvd
  have hQleY : Q ≤ zpowers y ⊔ Q := le_sup_right
  have hge : p ^ k ≤ Nat.card ↥(zpowers y ⊔ Q) := by
    rw [← hQ]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hQleY)
      (Subgroup.inclusion_injective hQleY)
  have hYeq : Nat.card ↥(zpowers y ⊔ Q) = p ^ k :=
    le_antisymm (by rw [hn]; exact Nat.pow_le_pow_right hp.pos hnle) hge
  have hQY : Q = zpowers y ⊔ Q :=
    Subgroup.eq_of_le_of_card_ge hQleY (by rw [hYeq, hQ])
  have hyY : y ∈ zpowers y ⊔ Q := Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  rw [← hQY] at hyY
  exact hyY

/-- Conjugation preserves the order of a subgroup. -/
theorem card_conjSub_H {a : G} {Q : Subgroup G} : Nat.card ↥(conjSub a Q) = Nat.card ↥Q := by
  rw [conjSub]
  exact Subgroup.card_map_of_injective (MulAut.conj a).injective

/-- `conjSub` is multiplicative in the conjugating element. -/
theorem conjSub_mul (a b : G) (H : Subgroup G) : conjSub (a * b) H = conjSub a (conjSub b H) := by
  rw [conjSub, conjSub, conjSub, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- Conjugation by `b` preserves cardinalities (the `map` form of `card_conjSub_H`). -/
theorem card_map_conj (b : G) (K : Subgroup G) :
    Nat.card ↥(K.map (MulAut.conj b : G →* G)) = Nat.card ↥K :=
  Subgroup.card_map_of_injective (MulAut.conj b).injective

/-- **Conjugating a two-point stabilizer.**  For a subgroup `H` and elements `a`, `b` one has
`|aHa⁻¹ ⊓ bHb⁻¹| = |H ⊓ (b⁻¹a)H(b⁻¹a)⁻¹|`.  This is the step that moves a pair of cosets
`(aH, bH)` to the pair `(H, (b⁻¹a)H)` — the shape in which `stab_inf_stab_card` applies. -/
theorem card_inf_conjSub_conj (a b : G) (H : Subgroup G) :
    Nat.card ↥(conjSub a H ⊓ conjSub b H) = Nat.card ↥(H ⊓ conjSub (b⁻¹ * a) H) := by
  have hm : (conjSub (b⁻¹ * a) H ⊓ H).map (MulAut.conj b : G →* G)
      = conjSub a H ⊓ conjSub b H := by
    rw [Subgroup.map_inf (conjSub (b⁻¹ * a) H) H (MulAut.conj b : G →* G)
      (show Function.Injective ((MulAut.conj b : G →* G) : G → G) from
        (MulAut.conj b).injective)]
    congr 1
    exact (conjSub_mul b (b⁻¹ * a) H).symm.trans (by rw [show b * (b⁻¹ * a) = a by group])
  rw [← hm, card_map_conj, inf_comm]

/-- The upper bound half of `stab_inf_stab_card`: `|H ⊓ aHa⁻¹| ≤ (q-1)/2` for `H = N_G(Q)`,
`a ∉ H`.  Any `y` in the intersection lies in `N_G(Q) ⊓ N_G(aQa⁻¹)`, so (being a `p`-element of
`Q`) it lies in both `Q` and `aQa⁻¹` — the two facts `mem_of_pElement_of_mem_normalizer` — whence
`y ∈ Q ⊓ aQa⁻¹ = ⊥` by Bender 3.7.  Thus `(H ⊓ aHa⁻¹) ⊓ Q = ⊥` and Lagrange on `Q ⊔ (H ⊓ aHa⁻¹) ≤ H`
gives the bound. -/
theorem card_inf_conj_le {q p k : ℕ} (hp : p.Prime) (hq : q = p ^ k) (h5 : 5 ≤ q) (hodd : Odd q)
    (h : IsBSWConf (G := G) q Q D) {a : G} (ha : a ∉ normalizer (Q : Set G)) :
    Nat.card ↥(normalizer (Q : Set G) ⊓ conjSub a (normalizer (Q : Set G))) ≤ (q - 1) / 2 := by
  have hk : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hq
    omega
  have hQk : Nat.card Q = p ^ k := by rw [h.card_Q, hq]
  have hDle : D ≤ normalizer (Q : Set G) := by rw [h.normalizer_Q]; exact le_sup_right
  have hH : Nat.card ↥(normalizer (Q : Set G)) = p ^ k * ((q - 1) / 2) := by
    rw [h.normalizer_Q, card_sup_of_inf_bot_of_le_normalizer h.inf_bot hDle, h.card_Q, h.card_D, hq]
  have hm2 : 2 * ((q - 1) / 2) = q - 1 := by
    obtain ⟨t, ht⟩ := hodd
    rw [ht, show (2 * t + 1 - 1) = 2 * t by omega,
      Nat.mul_div_right t (by norm_num : 0 < 2)]
  have hpnd : ¬ p ∣ (q - 1) / 2 := by
    intro hdiv
    have h1 : p ∣ q := by
      rw [hq]
      exact ⟨p ^ (k - 1), by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (show 1 ≤ k by omega)]⟩
    have h2 : p ∣ q - 1 := by
      have h3 : p ∣ 2 * ((q - 1) / 2) := dvd_mul_of_dvd_right hdiv 2
      rwa [hm2] at h3
    have := Nat.dvd_sub h1 h2
    rw [show q - (q - 1) = 1 by omega] at this
    exact hp.not_dvd_one this
  have hKQ : (normalizer (Q : Set G) ⊓ conjSub a (normalizer (Q : Set G))) ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨hyH, hyC⟩, hyQ⟩
    have hyC' : y ∈ normalizer ((conjSub a Q : Subgroup G) : Set G) := by
      rw [normalizer_conjSub_H]
      exact hyC
    have hy' : y ∈ conjSub a Q :=
      mem_of_pElement_of_mem_normalizer hp hpnd (by rw [card_conjSub_H, hQk])
        (by rw [normalizer_conjSub_H, card_conjSub_H, hH]) hyC'
        (exists_orderOf_eq_pow_of_mem hp hQk hyQ)
    have hybot : y ∈ Q ⊓ conjSub a Q := ⟨hyQ, hy'⟩
    rw [IsBSWConf.disjoint h a ha] at hybot
    exact Subgroup.mem_bot.mp hybot
  have h1 : Nat.card ↥(Q ⊔ (normalizer (Q : Set G) ⊓ conjSub a (normalizer (Q : Set G))))
      = Nat.card ↥Q * Nat.card ↥(normalizer (Q : Set G) ⊓ conjSub a (normalizer (Q : Set G))) :=
    card_sup_of_inf_bot_of_le_normalizer (H := Q)
      (K := normalizer (Q : Set G) ⊓ conjSub a (normalizer (Q : Set G)))
      (by rw [inf_comm]; exact hKQ) inf_le_left
  have h2 : Nat.card ↥(Q ⊔ (normalizer (Q : Set G) ⊓ conjSub a (normalizer (Q : Set G))))
      ∣ Nat.card ↥(normalizer (Q : Set G)) := by
    have hd := Subgroup.card_subgroup_dvd_card
      ((Q ⊔ (normalizer (Q : Set G) ⊓ conjSub a (normalizer (Q : Set G)))).subgroupOf
        (normalizer (Q : Set G)))
    have hc : Nat.card ↥((Q ⊔ (normalizer (Q : Set G) ⊓ conjSub a (normalizer (Q : Set G)))).subgroupOf
          (normalizer (Q : Set G)))
        = Nat.card ↥(Q ⊔ (normalizer (Q : Set G) ⊓ conjSub a (normalizer (Q : Set G)))) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (H := Q ⊔ (normalizer (Q : Set G) ⊓ conjSub a (normalizer (Q : Set G))))
        (K := normalizer (Q : Set G)) (sup_le le_normalizer inf_le_left)).toEquiv
    rwa [hc] at hd
  have h2le : q * Nat.card ↥(normalizer (Q : Set G) ⊓ conjSub a (normalizer (Q : Set G)))
      ≤ q * ((q - 1) / 2) := by
    have h4 : Nat.card ↥(Q ⊔ (normalizer (Q : Set G) ⊓ conjSub a (normalizer (Q : Set G))))
        ≤ Nat.card ↥(normalizer (Q : Set G)) :=
      Nat.le_of_dvd (by rw [hH]; exact Nat.mul_pos (by omega) (by omega)) h2
    rwa [h1, h.card_Q, hH, ← hq] at h4
  exact Nat.le_of_mul_le_mul_left h2le (by omega)

/-- The `↥H`-stabilizer of the coset `aH` is `H ⊓ aHa⁻¹` viewed inside `↥H` (step (i) of
`card_inf_conj_ge`).  Both sides amount to `a⁻¹ · s · a ∈ H`, which is `mem_conjSub_iff_H`. -/
theorem stabilizer_subtype_eq {a : G} {H : Subgroup G} :
    MulAction.stabilizer ↥H ((a : G) : G ⧸ H) = (H ⊓ conjSub a H).subgroupOf H := by
  ext s
  rw [MulAction.mem_stabilizer_iff]
  have key : ((((s : ↥H) : G) * a : G) : G ⧸ H) = ((a : G) : G ⧸ H) ↔
      a⁻¹ * ((s : ↥H) : G) * a ∈ H := by
    rw [QuotientGroup.eq]
    constructor
    · intro h
      have h' : (a⁻¹ * ((s : ↥H) : G) * a)⁻¹ ∈ H := by simpa [mul_assoc] using h
      simpa using (Subgroup.inv_mem_iff H).mp h'
    · intro h
      have h' : (a⁻¹ * ((s : ↥H) : G) * a)⁻¹ ∈ H := (Subgroup.inv_mem_iff H).mpr h
      simpa [mul_assoc] using h'
  change ((((s : ↥H) : G) * a : G) : G ⧸ H) = ((a : G) : G ⧸ H) ↔
    s ∈ (H ⊓ conjSub a H).subgroupOf H
  rw [key, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_conjSub_iff_H]
  exact ⟨fun h => ⟨s.2, h⟩, fun h => h.2⟩

/-- Cardinality form of `stabilizer_subtype_eq`: the `↥H`-stabilizer of the coset `aH` has the
same cardinality as `H ⊓ aHa⁻¹`. -/
theorem card_stabilizer_subtype_eq {a : G} {H : Subgroup G} :
    Nat.card ↥(MulAction.stabilizer ↥H ((a : G) : G ⧸ H)) = Nat.card ↥(H ⊓ conjSub a H) := by
  rw [stabilizer_subtype_eq]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

/-- The lower bound half of `stab_inf_stab_card`: `(q-1)/2 ≤ |H ⊓ aHa⁻¹|` for `H = N_G(Q)`,
`a ∉ H`.

`↥H` acts on the coset space `G ⧸ H` (`instMulActionSubtypeMem`), so `MulAction.index_stabilizer`
gives `(stabilizer ↥H (aH)).index = (orbit ↥H (aH)).ncard`.  The orbit avoids the base point
(`h • aH = H` would force `a = h⁻¹ · (h · a) ∈ H`), so it lies in the complement of `{H}`, whose
cardinality is `q` by `zass_card` (`|G ⧸ H| = q + 1`).  Hence the index is at most `q`, and
`|H| = |stabilizer| * index ≤ |stabilizer| * q` with `|H| = q·(q-1)/2` cancels `q`; finally
`card_stabilizer_subtype_eq` identifies the two cardinalities. -/
theorem card_inf_conj_ge {q p k : ℕ} (hp : p.Prime) (hq : q = p ^ k) (h5 : 5 ≤ q) (hodd : Odd q)
    (h : IsBSWConf (G := G) q Q D) {a : G} (ha : a ∉ normalizer (Q : Set G)) :
    (q - 1) / 2 ≤ Nat.card ↥(normalizer (Q : Set G) ⊓ conjSub a (normalizer (Q : Set G))) := by
  have hcardH : Nat.card ↥(normalizer (Q : Set G)) = q * ((q - 1) / 2) := by
    have hDle : D ≤ normalizer (Q : Set G) := by rw [h.normalizer_Q]; exact le_sup_right
    rw [h.normalizer_Q, card_sup_of_inf_bot_of_le_normalizer h.inf_bot hDle, h.card_Q, h.card_D]
  have hcardQ : Nat.card (G ⧸ normalizer (Q : Set G)) = q + 1 := zass_card h5 hodd h
  have hne : ((a : G) : G ⧸ normalizer (Q : Set G)) ≠ ((1 : G) : G ⧸ normalizer (Q : Set G)) := by
    intro hc
    exact ha (by simpa using (QuotientGroup.eq).mp hc.symm)
  have horb : (MulAction.orbit ↥(normalizer (Q : Set G))
      ((a : G) : G ⧸ normalizer (Q : Set G))).ncard ≤ q := by
    have hsub : MulAction.orbit ↥(normalizer (Q : Set G)) ((a : G) : G ⧸ normalizer (Q : Set G))
        ⊆ ({((1 : G) : G ⧸ normalizer (Q : Set G))}ᶜ : Set (G ⧸ normalizer (Q : Set G))) := by
      rintro g ⟨m, rfl⟩
      intro hc
      have h1 : ((m : ↥(normalizer (Q : Set G))) : G) * a ∈ normalizer (Q : Set G) := by
        have h1' : (((m : ↥(normalizer (Q : Set G))) : G) * a)⁻¹ ∈ normalizer (Q : Set G) := by
          simpa using (QuotientGroup.eq).mp hc
        simpa using (Subgroup.inv_mem_iff _).mp h1'
      exact ha (by
        have h2 : a = ((m : ↥(normalizer (Q : Set G))) : G)⁻¹ *
            (((m : ↥(normalizer (Q : Set G))) : G) * a) := by group
        rw [h2]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ m.2) h1)
    have hcompl : (({((1 : G) : G ⧸ normalizer (Q : Set G))}ᶜ :
        Set (G ⧸ normalizer (Q : Set G)))).ncard = q := by
      rw [Set.ncard_compl, Set.ncard_singleton, hcardQ]
      omega
    exact le_trans (Set.ncard_le_ncard hsub) (le_of_eq hcompl)
  have hidx := MulAction.index_stabilizer ↥(normalizer (Q : Set G))
    ((a : G) : G ⧸ normalizer (Q : Set G))
  have hle : (MulAction.stabilizer ↥(normalizer (Q : Set G))
      ((a : G) : G ⧸ normalizer (Q : Set G))).index ≤ q := by
    rw [hidx]
    exact horb
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer ↥(normalizer (Q : Set G))
    ((a : G) : G ⧸ normalizer (Q : Set G)))
  have hmain : q * ((q - 1) / 2) ≤ Nat.card ↥(MulAction.stabilizer ↥(normalizer (Q : Set G))
      ((a : G) : G ⧸ normalizer (Q : Set G))) * q := by
    rw [← hcardH, ← hmul]
    exact Nat.mul_le_mul_left _ hle
  have hfin : (q - 1) / 2 ≤ Nat.card ↥(MulAction.stabilizer ↥(normalizer (Q : Set G))
      ((a : G) : G ⧸ normalizer (Q : Set G))) := by
    refine Nat.le_of_mul_le_mul_right ?_ (by omega : 0 < q)
    rwa [mul_comm ((q - 1) / 2) q]
  rwa [card_stabilizer_subtype_eq (a := a) (H := normalizer (Q : Set G))] at hfin

/-- **The coset-stabilizer count** — the shared input of `zass_pretransitive` and `zass_twoPoint`.

For `a ∉ N_G(Q)` the stabilizer in `G` of the two distinct cosets `N_G(Q)` and `a·N_G(Q)` has order
`(q-1)/2`.  Writing `H := N_G(Q)`, this is `|H ⊓ a H a⁻¹| = (q-1)/2`, and both bounds come from
Bender 3.7 (the clause `IsBSWConf.disjoint`):

* `≤`: `H ⊓ aHa⁻¹ ≤ N_G(Q) ⊓ N_G(conjSub a Q)`, and a `p`-element of it lies in
  `Q ⊓ conjSub a Q = ⊥` (3.7, as `a ∉ H`), so the intersection is a `p'`-subgroup of `H = Q ⊔ D`
  meeting `Q` trivially; it therefore injects into `H ⧸ Q ≅ D`, giving `|H ⊓ aHa⁻¹| ≤ |D|`;
* `≥`: the `H`-orbit of the coset `aH` has `|H| / |H ⊓ aHa⁻¹|` elements and is contained in the `q`
  cosets different from `H`, so `|H ⊓ aHa⁻¹| ≥ |H| / q = (q-1)/2`.

Consequently `H` is transitive on the `q` cosets other than `H`: the orbit of `aH` has
`|H| / ((q-1)/2) = q` elements. -/
theorem stab_inf_stab_card {q p k : ℕ} (hp : p.Prime) (hq : q = p ^ k) (h5 : 5 ≤ q)
    (hodd : Odd q) (h : IsBSWConf (G := G) q Q D) {a : G} (ha : a ∉ normalizer (Q : Set G)) :
    Nat.card ↥(MulAction.stabilizer G ((1 : G) : G ⧸ normalizer (Q : Set G))
        ⊓ MulAction.stabilizer G (a : G ⧸ normalizer (Q : Set G))) = (q - 1) / 2 := by
  rw [stabilizer_base, stabilizer_conj]
  exact le_antisymm (card_inf_conj_le hp hq h5 hodd h ha) (card_inf_conj_ge hp hq h5 hodd h ha)

/-- **The orbit computation, in the form that elaborates.**  For a subgroup `H` with `|H| = q·(q-1)/2`
and `|G ⧸ H| = q + 1`, and such that every `↥H`-stabilizer of a coset `xH` with `x ∉ H` has
`(q-1)/2` elements, the `↥H`-orbit of `xH` is *all* the cosets different from `H`.

Stated with `H` as a parameter and the cardinality facts as hypotheses on purpose: writing `N_G(Q)`
out in full inside the co-occurring `MulAction.stabilizer G` and `MulAction.stabilizer ↥H` terms
made `whnf`/`isDefEq` diverge at the instantiation, so the instantiation is done at the call site. -/
theorem orbit_eq_compl {H : Subgroup G} {q : ℕ} (h5 : 5 ≤ q) (hodd : Odd q)
    (hcardH : Nat.card ↥H = q * ((q - 1) / 2)) (hcardQ : Nat.card (G ⧸ H) = q + 1)
    (hstab : ∀ x : G, x ∉ H → Nat.card ↥(MulAction.stabilizer ↥H ((x : G) : G ⧸ H))
      = (q - 1) / 2)
    {x : G} (hx : x ∉ H) :
    MulAction.orbit ↥H ((x : G) : G ⧸ H) = {((1 : G) : G ⧸ H)}ᶜ := by
  have hmpos : 0 < (q - 1) / 2 := by
    obtain ⟨t, ht⟩ := hodd
    rw [ht, show (2 * t + 1 - 1) = 2 * t by omega,
      Nat.mul_div_right t (by norm_num : 0 < 2)]
    omega
  have hidx := MulAction.index_stabilizer ↥H ((x : G) : G ⧸ H)
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer ↥H ((x : G) : G ⧸ H))
  rw [hstab x hx, hidx] at hmul
  have hmul' : (q - 1) / 2 * (MulAction.orbit ↥H ((x : G) : G ⧸ H)).ncard
      = q * ((q - 1) / 2) := hmul.trans hcardH
  have horb : (MulAction.orbit ↥H ((x : G) : G ⧸ H)).ncard = q := by
    have h1 : (q - 1) / 2 * (MulAction.orbit ↥H ((x : G) : G ⧸ H)).ncard
        = (q - 1) / 2 * q := by rw [hmul', mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hmpos h1
  have hsub : MulAction.orbit ↥H ((x : G) : G ⧸ H) ⊆ ({((1 : G) : G ⧸ H)}ᶜ : Set (G ⧸ H)) := by
    rintro g ⟨m, rfl⟩
    intro hc
    have h1 : ((m : ↥H) : G) * x ∈ H := by
      have h1' : (((m : ↥H) : G) * x)⁻¹ ∈ H := by simpa using (QuotientGroup.eq).mp hc
      simpa using (Subgroup.inv_mem_iff _).mp h1'
    have h2 : x = ((m : ↥H) : G)⁻¹ * (((m : ↥H) : G) * x) := by group
    exact hx (by rw [h2]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ m.2) h1)
  have hcompl : (({((1 : G) : G ⧸ H)}ᶜ : Set (G ⧸ H))).ncard = q := by
    rw [Set.ncard_compl, Set.ncard_singleton, hcardQ]
    omega
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [horb, hcompl])

/-- `stab_inf_stab_card` with `H` a parameter, closed by `subst hH` — the form usable at a call
site where `↥H`-stabilizers are in scope. -/
theorem stab_inf_stab_card_H {q p k : ℕ} (hp : p.Prime) (hq : q = p ^ k) (h5 : 5 ≤ q)
    (hodd : Odd q) (h : IsBSWConf (G := G) q Q D) {H : Subgroup G}
    (hH : H = normalizer (Q : Set G)) {a : G} (ha : a ∉ H) :
    Nat.card ↥(MulAction.stabilizer G ((1 : G) : G ⧸ H) ⊓ MulAction.stabilizer G ((a : G) : G ⧸ H))
      = (q - 1) / 2 := by
  subst hH
  exact stab_inf_stab_card hp hq h5 hodd h ha

/-- `card_inf_conj_le` with `H` a parameter. -/
theorem card_inf_conj_le_H {q p k : ℕ} (hp : p.Prime) (hq : q = p ^ k) (h5 : 5 ≤ q)
    (hodd : Odd q) (h : IsBSWConf (G := G) q Q D) {H : Subgroup G}
    (hH : H = normalizer (Q : Set G)) {a : G} (ha : a ∉ H) :
    Nat.card ↥(H ⊓ conjSub a H) ≤ (q - 1) / 2 := by
  subst hH
  exact card_inf_conj_le hp hq h5 hodd h ha

/-- `card_inf_conj_ge` with `H` a parameter. -/
theorem card_inf_conj_ge_H {q p k : ℕ} (hp : p.Prime) (hq : q = p ^ k) (h5 : 5 ≤ q)
    (hodd : Odd q) (h : IsBSWConf (G := G) q Q D) {H : Subgroup G}
    (hH : H = normalizer (Q : Set G)) {a : G} (ha : a ∉ H) :
    (q - 1) / 2 ≤ Nat.card ↥(H ⊓ conjSub a H) := by
  subst hH
  exact card_inf_conj_ge hp hq h5 hodd h ha

/-- The action on the cosets of `N_G(Q)` is doubly transitive. -/
theorem zass_pretransitive {q p k : ℕ} (hp : p.Prime) (hq : q = p ^ k) (h5 : 5 ≤ q) (hodd : Odd q)
    (h : IsBSWConf (G := G) q Q D) :
    MulAction.IsMultiplyPretransitive G (G ⧸ normalizer (Q : Set G)) 2 := by
  have hcardQ : Nat.card (G ⧸ normalizer (Q : Set G)) = q + 1 := zass_card h5 hodd h
  have hcardH : Nat.card ↥(normalizer (Q : Set G)) = q * ((q - 1) / 2) := by
    have hDle : D ≤ normalizer (Q : Set G) := by rw [h.normalizer_Q]; exact le_sup_right
    rw [h.normalizer_Q, card_sup_of_inf_bot_of_le_normalizer h.inf_bot hDle, h.card_Q, h.card_D]
  have hstab : ∀ x : G, x ∉ normalizer (Q : Set G) → Nat.card ↥(MulAction.stabilizer
      ↥(normalizer (Q : Set G)) ((x : G) : G ⧸ normalizer (Q : Set G))) = (q - 1) / 2 := by
    intro x hx
    rw [card_stabilizer_subtype_eq (H := normalizer (Q : Set G))]
    exact le_antisymm (card_inf_conj_le hp hq h5 hodd h hx)
      (card_inf_conj_ge hp hq h5 hodd h hx)
  have htrans : ∀ x : G, x ∉ normalizer (Q : Set G) → ∀ y : G, y ∉ normalizer (Q : Set G) →
      ∃ m : ↥(normalizer (Q : Set G)),
        m • ((x : G) : G ⧸ normalizer (Q : Set G)) = ((y : G) : G ⧸ normalizer (Q : Set G)) := by
    intro x hx y hy
    have horb := orbit_eq_compl (H := normalizer (Q : Set G)) h5 hodd hcardH hcardQ hstab hx
    have hmem : ((y : G) : G ⧸ normalizer (Q : Set G)) ∈
        MulAction.orbit ↥(normalizer (Q : Set G)) ((x : G) : G ⧸ normalizer (Q : Set G)) := by
      rw [horb]
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hc
      exact hy (by simpa using (QuotientGroup.eq).mp hc.symm)
    obtain ⟨m, hm⟩ := MulAction.mem_orbit_iff.mp hmem
    exact ⟨m, hm⟩
  refine MulAction.is_two_pretransitive_iff.mpr ?_
  rintro a b c d hab hcd
  obtain ⟨x, rfl⟩ := Quotient.exists_rep a
  obtain ⟨y, rfl⟩ := Quotient.exists_rep b
  obtain ⟨u, rfl⟩ := Quotient.exists_rep c
  obtain ⟨v, rfl⟩ := Quotient.exists_rep d
  have hxy : x⁻¹ * y ∉ normalizer (Q : Set G) := fun hc => hab (QuotientGroup.eq.mpr hc)
  have huv : u⁻¹ * v ∉ normalizer (Q : Set G) := fun hc => hcd (QuotientGroup.eq.mpr hc)
  obtain ⟨m, hm⟩ := htrans (x⁻¹ * y) hxy (u⁻¹ * v) huv
  refine ⟨u * (m : G) * x⁻¹, ?_, ?_⟩
  · change (((u * (m : G) * x⁻¹) * x : G) : G ⧸ normalizer (Q : Set G))
      = ((u : G) : G ⧸ normalizer (Q : Set G))
    rw [QuotientGroup.eq]
    convert Subgroup.inv_mem _ m.2 using 1
    group
  · change (((u * (m : G) * x⁻¹) * y : G) : G ⧸ normalizer (Q : Set G))
      = ((v : G) : G ⧸ normalizer (Q : Set G))
    have hm' : ((m : G) * (x⁻¹ * y))⁻¹ * (u⁻¹ * v) ∈ normalizer (Q : Set G) := by
      have h := hm
      change (((m : G) * (x⁻¹ * y) : G) : G ⧸ normalizer (Q : Set G))
        = ((u⁻¹ * v : G) : G ⧸ normalizer (Q : Set G)) at h
      exact QuotientGroup.eq.mp h
    rw [QuotientGroup.eq]
    convert hm' using 1
    group

/-- The two-point stabilizers have order `(q-1)/2`.  Stated with `H` as a parameter — writing
`N_G(Q)` out in full inside the co-occurring stabilizer terms makes `isDefEq` diverge, see the
discussion at `orbit_eq_compl`; the instantiation is done at the call site. -/
theorem zass_twoPoint {q : ℕ} {H : Subgroup G} (hodd : Odd q)
    (hstab : ∀ x : G, x ∉ H → Nat.card ↥(H ⊓ conjSub x H) = (q - 1) / 2)
    {x y : G ⧸ H} (hxy : x ≠ y) :
    2 * Nat.card (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y : Subgroup G) = q - 1 := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  obtain ⟨b, rfl⟩ := Quotient.exists_rep y
  have hab : b⁻¹ * a ∉ H := by
    intro hc
    exact hxy (QuotientGroup.eq.mpr (by simpa [mul_inv_rev] using Subgroup.inv_mem _ hc))
  have hmain : Nat.card ↥(MulAction.stabilizer G ((a : G) : G ⧸ H)
      ⊓ MulAction.stabilizer G ((b : G) : G ⧸ H)) = (q - 1) / 2 := by
    rw [stabilizer_conj (a := a) (H := H), stabilizer_conj (a := b) (H := H),
      card_inf_conjSub_conj (a := a) (b := b) (H := H)]
    exact hstab (b⁻¹ * a) hab
  have hm2 : 2 * ((q - 1) / 2) = q - 1 := by
    obtain ⟨t, ht⟩ := hodd
    rw [ht, show (2 * t + 1 - 1) = 2 * t by omega, Nat.mul_div_right t (by norm_num : 0 < 2)]
  rw [hmain, hm2]

end Conditions

end Work.BSW.Cases
