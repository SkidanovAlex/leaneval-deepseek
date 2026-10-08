/-
# BMAX — Bender 1970, 1.6 (Bender 1981, Lemma 2.3 (iii))

Target:

`theorem Work.BMAX.Bender16 : ∀ G [Group G] [Finite G], IsSimpleGroup G → ∀ A B : Subgroup G,
IsCoatom A → IsCoatom B → A ≠ B → fstarIn A ≤ B → fstarIn B ≤ A →
∃ p, p.Prime ∧ IsPGroup p (fstarIn A) ∧ IsPGroup p (fstarIn B)`.

This is Bender 1970, 1.6 in the vocabulary of `Submission.Work.GLUE.Defs`, i.e. with
`fstar = F(X) · layer(X)` where `layer` is the join of the **normal** quasisimple subgroups.

## Reconstructed skeleton of the proof

Write `F_A := F(A) = ⨆_p O_p(A)`, `L_A := layer(A)`, `F*_A := F_A · L_A = fstarIn A`
(and likewise for `B`).  The intended argument (Bender's, with the definitions of this
workspace) is:

1. **Commutation lemmas.**  For `Q ⊴ A` quasisimple and `N ⊴ A` nilpotent (normal in the
   *same* group) one has `[Q,N] = 1` (proved in `Submission/Work/BMAX/LayerCentralizesFitting`;
   in particular `[F_A, L_A] = 1`).  The cross versions needed here are
   `[Q, F_B] = 1` for `Q ⊴ A` quasisimple with `Q ≤ B` (both `Q ≤ N(F_B)` and `F_B ≤ N(Q)`
   hold because `F_B ≤ A` and `Q ≤ B`), and `[L_A, L_B] = 1` (distinct mutual-normalising
   quasisimple subgroups commute).  Both follow from the same three-subgroups argument.
   Hence `L_A ≤ C_G(F*_B)` and `L_B ≤ C_G(F*_A)`.

2. **`L_A = L_B = 1`.**  Since `L_A ≤ C_G(F*_B)` and one expects `C_G(F*_B) ≤ F*_B`
   ("`F*` contains its centralizer"), one gets `L_A ≤ F*_B ∩ C_G(F*_B) = Z(F*_B)`, which
   forces `L_A = 1` (a nontrivial quasisimple group is perfect, hence not abelian); by
   symmetry `L_B = 1`.  Consequently `F*_A = F_A` and `F*_B = F_B` are nilpotent.

3. **`F_A`, `F_B` are `p`-groups for one prime `p`.**  Pick `p ∈ π(F_A)` (if `F_A = 1` then
   any prime works for `A`), put `P := O_p(A)`, `Q := O_p(B)`, `R := O_{p'}(A)`.  Then
   `[R, Q] = 1` (coprime orders, mutual normalisation) and `[R, F_B] = 1`, so `R ≤ C_B(F*_B)`;
   again `C_B(F*_B) ≤ F*_B = F_B`, and in the nilpotent group `F_B` a `p'`-subgroup lies in
   `O_{p'}(F_B) = O_{p'}(B)`.  So `R ≤ O_{p'}(B)`, symmetrically `O_{p'}(B) ≤ R`, whence
   `R = O_{p'}(B)` is normalised by both `A` and `B`, hence by `⟨A,B⟩ = G` (the maximality
   of `A` and `B` gives `A ⊔ B = ⊤`), and `G` simple forces `R = 1` (as `R ≤ A ≠ ⊤`).  Thus
   `F_A = O_p(A)` and `F_B = O_p(B)` are both `p`-groups.

## Status, and the two difficulties

The two steps that are missing are exactly the ones for which the workspace's definitions
differ from Bender's:

* `C_X(F*(X)) ≤ F*(X)` fails for the workspace's `F*`.  The definition of `layer` (join of
  **normal** quasisimple subgroups) can be `1` while `F(X) = 1` and `X ≠ 1` — an explicit
  example is the partition stabiliser `(S_k ≀ C₂) ∩ A_{2k}`, for which `F = layer = 1` — and
  then `C_X(F*(X)) = X ⋬≤ F*(X) = 1`.  This is the same defect that makes Bender 1970, 1.7(i)
  *false* in this vocabulary (see `Submission/Work/BMAX/Bender17Prime.lean` and
  `Bender17ii.lean`, where a counterexample in `A₁₀` is recorded).  For 1.6 the defect is not
  known to produce a counterexample: a GAP search over all maximal-subgroup pairs of every
  simple group of order `< 2000`, together with `A₇`–`A₁₂`, `M₁₁`, `M₁₂`, `M₂₂`,
  `PSL(2,q)` (q ≤ 49), `PSL(3,q)` (q ≤ 5), `PSU(3,3)`, `PSU(4,2)`, `PSp(4,2)`, `PSp(4,3)`,
  `Sz(8)`, found the hypothesis to be satisfied in 26 cases (all of them pairs of `p`-local
  maximal subgroups with `F*` an elementary abelian `p`-group, together with the `A₁₂` pairs
  where one of the two `F*`'s is trivial), and no violation of the conclusion.
* The same search shows that whenever the hypothesis holds and one of `F*(A) = 1`,
  `F*(B) = 1` is degenerate, the other `F*` is a `p`-group (e.g. `A₁₂`: the partition
  stabiliser of order `518400` with `F* = 1` pairs with maximal subgroups of order `23040`
  (`F* = 2⁵`) and `15552` (`F* = 3⁴`)); so the statement may well be true, but this needs an
  argument for the degenerate case that the present file does not supply.

## Characterisation of the defect, and why Bender's route does not transplant

Write `C := C_X(F*(X))`; one always has `C ⊓ F*(X) = Z(F*(X))`, so self-centralisation asks
whether `C` is *exactly* the centre of `F*`.  GAP sweeps (script `_b16defect.g`, using the
workspace's own `Fitting`/`layer` computations) give:

* for **all 1023 groups of order `≤ 96`** in the small-groups library the property **holds**;
* it **fails** for the "wreath-type" groups in which `layer` misses a component:
  `A₅ ≀ C₂`, `A₅ ≀ C₃`, `C₂ × (A₅ ≀ C₂)`, `A₅ × (A₅ ≀ C₂)`, and the partition stabilisers
  `(S_k ≀ C₂) ∩ A_{2k}` (`k = 5, 6`), i.e. the coatoms of `A₁₀`, `A₁₂` of order `14400`,
  `518400`;
* it **holds** for every other maximal subgroup tested (all maximal subgroups of `A₇`–`A₁₂`,
  `M₁₁`, `M₁₂`, `M₂₂`, `PSL(2,q)` `q ≤ 49`, `PSL(3,q)` `q ≤ 5`, `PSU(3,3)`, `PSU(4,2)`,
  `PSp(4,2)`, `PSp(4,3)`, `Sz(8)`, and for `A₅ × A₅`, `A₄ ≀ C₂`, `S₃ ≀ C₂`).

This is the layer/component deviation of `NOTES_BMAX.md` §5.1, in the sharp form

> `C_X(F*(X)) ≤ F*(X)` holds whenever every component of `X` is normal in `X`, equivalently
> `layer(X) = E(X)` (the components-based layer), and can fail otherwise.

**Two consequences, both established by parallel work on this branch:**

1. *The self-centralisation route is dead.*  The natural helper "the pair hypotheses plus
   `F*(B) ≠ ⊥` imply `C_B(F*(B)) ≤ F*(B)`" is **FALSE**: for `G = PSp(4,5)` with `A`, `B`
   maximal subgroups of order `14400` of type `2.(A₅ × A₅).2`, one has `F(B) = Z(B) ≅ C₂`
   (the only non-trivial nilpotent normal subgroup), `layer(B) = ⊥` (the perfect normal
   subgroup `2.(A₅ × A₅)` has non-simple central quotient, and `B` is not perfect), hence
   `F*(B) = Z(B)` is *central*, so `C_B(F*(B)) = B ≰ F*(B)`.  A suitable `A ≠ B` in the same
   class satisfies `F*(A) = Z(A) ≤ B`, `F*(B) = Z(B) ≤ A`.  The conclusion of `Bender16`
   nevertheless *holds* there (`F*(A) = F*(B) = C₂` is a 2-group), so this refutes the
   helper, not the theorem.
2. *The `fstarIn` hypothesis is essential and not reducible to `fittingIn`.*  Already
   `fittingIn A ≤ B` together with `fittingIn B ≤ A` does **not** force a common prime:
   for `G = A₁₀`, `A = A₇:S₃` (`F(A) = C₃`) and `B = A₆:S₄` (`F(B) = C₂ × C₂`) have
   `F(A) ≤ B`, `F(B) ≤ A` but no common `p` — and for `G = M₁₂`, `A ≅ A₄ × S₃`,
   `B ≅ C₂ × S₅` likewise (`F(A) ≅ C₂ × C₂ × C₃`).  In both cases the `fstarIn` hypothesis
   fails precisely because `layer` is non-trivial there, which is why `Bender16` itself is
   untouched.

Consequently the proof has to be run with the `fstarIn` hypothesis throughout, and the two
remaining sub-goals are:

* `Work.BMAX.Bender16_layer_eq_bot` — `L_A = L_B = 1` under the pair hypotheses (delegated;
  GAP checks over all simple groups of order `≤ 4000` plus `A₈`, `PSL(3,4)`, `M₁₂`, `M₁₁`,
  `Sz(8)`, `PSL(3,3)`: no violation, and coatoms with `layer ≠ 1` never satisfy both
  containments);
* the "nilpotent core" in the remaining regime: `L_A = L_B = 1` (so `F* = F`) and
  `F_A ≤ B`, `F_B ≤ A` should force `F_A`, `F_B` to be `p`-groups for one prime.  This is
  Bender's step 2–3, and *his* proof uses the (false) self-centralisation, so it needs a new
  argument; the `PSp(4,5)` and `A₁₀`/`M₁₂` configurations above are the shapes to keep in
  mind when searching for it (central `C₂`s give 2-groups; genuinely different primes in
  `A₁₀`/`M₁₂` come with `layer ≠ 1`).

The helpers proved below are the coprime-commutation lemma, the cross (different ambient
subgroups) commutation lemmas and the layer-lifting lemmas that any such proof will use.
The helpers proved below are the coprime-commutation lemma and the cross (different ambient
subgroups) commutation lemmas, which the steps above use.
-/
import Mathlib
import Submission.Work.BMAX.Defs

set_option linter.style.haveILetI false

namespace Work.BMAX

open Subgroup

/-- **Coprime-order subgroups that normalize each other commute.**

If `X ≤ N_G(Y)` and `Y ≤ N_G(X)` then `⁅X, Y⁆ ≤ X ⊓ Y` (each `⁅x,y⁆` lies in both `X` and
`Y`), and coprimality of the orders makes the intersection trivial.  This is the
"subgroups of coprime order of `F(A)` and `F(B)` centralize each other" of Bender 1970, 1.6
(in the form used there: `O_{p'}(A)` versus the primary components of `F(B)`). -/
theorem b16_commutator_eq_bot_of_coprime_of_le_normalizer {G : Type*} [Group G] [Finite G]
    {X Y : Subgroup G} (hXY : X ≤ Subgroup.normalizer (Y : Set G))
    (hYX : Y ≤ Subgroup.normalizer (X : Set G))
    (hcop : Nat.Coprime (Nat.card X) (Nat.card Y)) : ⁅X, Y⁆ = ⊥ := by
  have h1 : ⁅X, Y⁆ ≤ Y := (Subgroup.le_normalizer_iff_commutator_le_right).mp hXY
  have h2 : ⁅X, Y⁆ ≤ X := (Subgroup.le_normalizer_iff_commutator_le_left).mp hYX
  have h3 : ⁅X, Y⁆ ≤ X ⊓ Y := le_inf h2 h1
  have hbot : X ⊓ Y = ⊥ := Disjoint.eq_bot (Subgroup.disjoint_of_coprime_natCard hcop)
  rw [hbot] at h3
  exact le_bot_iff.mp h3

/-- The commutator subgroup of `↥H` is everything iff `⁅H, H⁆ = H`. -/
theorem b16_commutator_eq_top_iff {G : Type*} [Group G] (H : Subgroup G) :
    commutator ↥H = ⊤ ↔ ⁅H, H⁆ = H := by
  have h := Subgroup.map_subtype_commutator H
  constructor
  · intro h1
    rw [← h, h1, Subgroup.map_top, Subgroup.range_subtype]
  · intro h1
    refine Subgroup.map_injective (f := H.subtype) Subtype.val_injective ?_
    rw [h, h1, Subgroup.map_top, Subgroup.range_subtype]

/-- **`IsQuasisimple` passes to the subgroup-of version**: if `Q ≤ H` and `Q` is
quasisimple (in `G`), then `Q`, viewed inside `H`, is quasisimple.  This is the transport
needed to run the "distinct quasisimple subgroups commute" argument inside the join `Q ⊔ N`
when the two subgroups are normal only up to their mutual normalizers. -/
theorem b16_isQuasisimple_subgroupOf {G : Type*} [Group G] {Q H : Subgroup G} (hQH : Q ≤ H)
    (hQ : Work.GW2.IsQuasisimple Q) : Work.GW2.IsQuasisimple (Q.subgroupOf H) := by
  obtain ⟨hperf, hsimp⟩ := hQ
  haveI := hsimp
  have hQtop : commutator ↥Q = ⊤ := (b16_commutator_eq_top_iff Q).mpr hperf
  let e : ↥(Q.subgroupOf H) ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQH
  have hcomm : (commutator ↥(Q.subgroupOf H))
      = ⁅(⊤ : Subgroup ↥(Q.subgroupOf H)), (⊤ : Subgroup ↥(Q.subgroupOf H))⁆ := by
    rw [Subgroup.commutator_def]
    rfl
  refine ⟨?_, ?_⟩
  · have hcommQ : (commutator ↥Q) = ⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ := by
      rw [Subgroup.commutator_def]
      rfl
    refine (b16_commutator_eq_top_iff (Q.subgroupOf H)).mp ?_
    refine Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_
    rw [hcomm, Subgroup.map_commutator, Subgroup.map_top e.toMonoidHom,
      MonoidHom.range_eq_top.mpr e.surjective]
    rw [← hcommQ, hQtop]
  · have hcenter : Subgroup.map e.toMonoidHom (Subgroup.center ↥(Q.subgroupOf H))
        = Subgroup.center ↥Q := Subgroup.map_center_eq e
    exact MulEquiv.isSimpleGroup
      (QuotientGroup.congr (Subgroup.center ↥(Q.subgroupOf H)) (Subgroup.center ↥Q) e hcenter)

/-- **A nilpotent normal subgroup commutes with a quasisimple normal subgroup** (of the same
ambient group): `⁅E, N⁆ = 1`.  (This is the same statement as
`Work.BMAX.nilpotent_normal_le_centralizer_of_quasisimple`, reproved here in the `⁅_,_⁆`
form so that the cross version below can transfer it inside a join.) -/
theorem b16_commutator_eq_bot_of_normal_nilpotent_of_normal_quasisimple {X : Type*} [Group X]
    {E N : Subgroup X} (hEn : E.Normal) (hEE : ⁅E, E⁆ = E)
    (hEsimp : IsSimpleGroup (↥E ⧸ Subgroup.center ↥E))
    (hNn : N.Normal) [Group.IsNilpotent ↥N] : ⁅E, N⁆ = ⊥ := by
  haveI := hEn
  haveI := hNn
  set M : Subgroup X := ⁅E, N⁆ with hMdef
  have hME : M ≤ E := Subgroup.commutator_le_left E N
  have hMN : M ≤ N := Subgroup.commutator_le_right E N
  have hMnor : M.Normal := Subgroup.commutator_normal E N
  haveI := hMnor
  set Z : Subgroup ↥E := Subgroup.center ↥E with hZdef
  set ME : Subgroup ↥E := M.subgroupOf E with hMEdef
  have hMEnor : ME.Normal := hMnor.subgroupOf E
  haveI := hMEnor
  have hmapnor : (ME.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map hMEnor _ (QuotientGroup.mk'_surjective Z)
  haveI := hmapnor
  rcases hEsimp.eq_bot_or_eq_top_of_normal (ME.map (QuotientGroup.mk' Z)) with hbot | htop
  · -- case `M ≤ Z(E)`: the three subgroups lemma finishes
    have hMEleZ : ME ≤ Z := by
      have h := (Subgroup.map_eq_bot_iff ME).mp hbot
      rwa [QuotientGroup.ker_mk' Z] at h
    have hMcent : M ≤ Subgroup.centralizer (E : Set X) := by
      intro m hm
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hmE : m ∈ E := hME hm
      have hz : (⟨m, hmE⟩ : ↥E) ∈ ME := hm
      have hzu : (⟨m, hmE⟩ : ↥E) ∈ Z := hMEleZ hz
      have hcomm := Subgroup.mem_center_iff.mp hzu (⟨e, he⟩ : ↥E)
      simpa using congrArg Subtype.val hcomm
    have hMEbot : ⁅M, E⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hMcent
    have h2 : ⁅⁅N, E⁆, E⁆ = ⊥ := by
      rw [Subgroup.commutator_comm N E]
      exact hMEbot
    have h3 : ⁅⁅E, E⁆, N⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate hMEbot h2
    have hMbot : ⁅E, N⁆ = ⊥ := by
      rw [hEE] at h3
      exact h3
    exact hMbot
  · -- case `M Z(E) = E`: then `E ≤ M ≤ N`, contradicting perfect + nilpotent
    exfalso
    have hsup : ME ⊔ Z = ⊤ := by
      have h := QuotientGroup.comap_map_mk' Z ME
      rw [htop, Subgroup.comap_top] at h
      rw [sup_comm] at h
      exact h.symm
    have hsupX : M ⊔ Z.map E.subtype = E := by
      have h1 := congrArg (Subgroup.map E.subtype) hsup
      rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h1
      rw [hMEdef, Subgroup.subgroupOf_map_subtype M E, inf_eq_left.mpr hME] at h1
      exact h1
    have hZm_cen : ⁅Z.map E.subtype, E⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      obtain ⟨z', hz', rfl⟩ := hz
      have hcomm := Subgroup.mem_center_iff.mp hz' (⟨e, he⟩ : ↥E)
      simpa using congrArg Subtype.val hcomm
    have hEEleM : ⁅E, E⁆ ≤ M := by
      have hmono : ⁅E, E⁆ ≤ ⁅M ⊔ Z.map E.subtype, E⁆ :=
        Subgroup.commutator_mono (le_of_eq hsupX.symm) le_rfl
      have hsplit : ⁅M ⊔ Z.map E.subtype, E⁆ = ⁅M, E⁆ ⊔ ⁅Z.map E.subtype, E⁆ :=
        Subgroup.commutator_sup_right M (Z.map E.subtype) E
      have hMEleM : ⁅M, E⁆ ≤ M := Subgroup.commutator_le_left M E
      calc ⁅E, E⁆ ≤ ⁅M ⊔ Z.map E.subtype, E⁆ := hmono
        _ = ⁅M, E⁆ ⊔ ⁅Z.map E.subtype, E⁆ := hsplit
        _ = ⁅M, E⁆ := by rw [hZm_cen, sup_bot_eq]
        _ ≤ M := hMEleM
    have hEM : E ≤ M := le_trans (le_of_eq hEE.symm) hEEleM
    have hEN : E ≤ N := le_trans hEM hMN
    have hEiso : ↥(E.subgroupOf N) ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEN
    haveI : Group.IsNilpotent ↥E := (Group.isNilpotent_congr hEiso).mp inferInstance
    haveI : Nontrivial ↥E := (QuotientGroup.mk'_surjective Z).nontrivial
    haveI : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hEE
    exact Group.IsPerfect.not_isNilpotent ↥E inferInstance

/-- **Cross version**: a quasisimple subgroup and a nilpotent subgroup that normalize each
other commute.  (Here the two groups live in different ambient subgroups, so the statement is
not a formal consequence of the same-group version without passing to the join.) -/
theorem b16_commutator_eq_bot_of_isQuasisimple_of_nilpotent_cross {G : Type*} [Group G]
    {Q N : Subgroup G} (hQ : Work.GW2.IsQuasisimple Q)
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) (hNQ : N ≤ Subgroup.normalizer (Q : Set G))
    [hNnil : Group.IsNilpotent ↥N] : ⁅Q, N⁆ = ⊥ := by
  set H : Subgroup G := Q ⊔ N with hH
  have hQH : Q ≤ H := le_sup_left
  have hNH : N ≤ H := le_sup_right
  have hQn : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff hQH).mpr fun h k hh hk => by
      have hk' : k ∈ Subgroup.normalizer (Q : Set G) := sup_le Subgroup.le_normalizer hNQ hk
      exact (Subgroup.mem_normalizer_iff.mp hk' h).mp hh
  have hNn : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff hNH).mpr fun h k hh hk => by
      have hk' : k ∈ Subgroup.normalizer (N : Set G) := sup_le hQN Subgroup.le_normalizer hk
      exact (Subgroup.mem_normalizer_iff.mp hk' h).mp hh
  haveI : Group.IsNilpotent ↥(N.subgroupOf H) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hNH)).mpr hNnil
  have hQ' : Work.GW2.IsQuasisimple (Q.subgroupOf H) := b16_isQuasisimple_subgroupOf hQH hQ
  have hbot : ⁅(N.subgroupOf H), (Q.subgroupOf H)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact b16_commutator_eq_bot_of_normal_nilpotent_of_normal_quasisimple (E := Q.subgroupOf H)
      (N := N.subgroupOf H) hQn hQ'.1 hQ'.2 hNn
  have hmain : (N.subgroupOf H) ≤ Subgroup.centralizer ((Q.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hnH : (⟨n, hNH hn⟩ : ↥H) ∈ N.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact hn
  have hlocal : (⟨n, hNH hn⟩ : ↥H) ∈
      Subgroup.centralizer ((Q.subgroupOf H : Subgroup ↥H) : Set ↥H) := hmain hnH
  have hcomm := (Subgroup.mem_centralizer_iff.mp hlocal) ⟨q, hQH hq⟩ hq
  exact congrArg Subtype.val hcomm.symm

/-- **Lifting a commutation statement through the layer.**  If every normal quasisimple
subgroup of `A` (viewed as a subgroup of `↥A`) commutes with `K`, then so does the whole layer
`layerIn A`. -/
theorem b16_layerIn_le_centralizer {G : Type*} [Group G] {A K : Subgroup G}
    (h : ∀ E : Subgroup ↥A, E.Normal → Work.GW2.IsQuasisimple E →
      E.map A.subtype ≤ Subgroup.centralizer (K : Set G)) :
    Work.GW2.layerIn A ≤ Subgroup.centralizer (K : Set G) := by
  rw [Work.GW2.layerIn, Work.GW2.layer, Subgroup.map_le_iff_le_comap]
  refine sSup_le ?_
  rintro E ⟨hEn, hEq⟩
  rw [← Subgroup.map_le_iff_le_comap]
  exact h E hEn hEq

/-- A quasisimple subgroup of a commutative subgroup is trivial (a nontrivial quasisimple
group is perfect, hence not commutative). -/
theorem b16_isQuasisimple_eq_bot_of_le_isMulCommutative {G : Type*} [Group G] {Q Z : Subgroup G}
    (hQ : Work.GW2.IsQuasisimple Q) (hZ : IsMulCommutative Z) (hle : Q ≤ Z) : Q = ⊥ := by
  have hcomm : ⁅Q, Q⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr ?_
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_bot]
    refine commutatorElement_eq_one_iff_commute.mpr ?_
    have h1 : (⟨g₁, hle hg₁⟩ : ↥Z) * ⟨g₂, hle hg₂⟩ = ⟨g₂, hle hg₂⟩ * ⟨g₁, hle hg₁⟩ :=
      mul_comm' _ _
    exact congrArg (fun z : ↥Z => (z : G)) h1
  rw [← hQ.1, hcomm]

/-- `IsQuasisimple` is preserved by an injective homomorphism. -/
theorem b16_isQuasisimple_map {G N : Type*} [Group G] [Group N] (f : G →* N)
    (hf : Function.Injective f) {E : Subgroup G} (hE : Work.GW2.IsQuasisimple E) :
    Work.GW2.IsQuasisimple (E.map f) := by
  obtain ⟨hperf, hsimp⟩ := hE
  haveI := hsimp
  refine ⟨?_, ?_⟩
  · rw [← Subgroup.map_commutator E E f, hperf]
  · let eE := Subgroup.equivMapOfInjective E f hf
    have hcen : (Subgroup.center ↥E).map eE.toMonoidHom = Subgroup.center ↥(E.map f) :=
      Subgroup.map_center_eq eE
    exact MulEquiv.isSimpleGroup
      (QuotientGroup.congr (Subgroup.center ↥E) (Subgroup.center ↥(E.map f)) eE hcen).symm

/-- The layer of `A` is generated by perfect subgroups, so if it lies in a commutative
subgroup then it is trivial. -/
theorem b16_layerIn_eq_bot_of_le_isMulCommutative {G : Type*} [Group G] {A Z : Subgroup G}
    (hZ : IsMulCommutative Z) (hle : Work.GW2.layerIn A ≤ Z) : Work.GW2.layerIn A = ⊥ := by
  rw [Work.GW2.layerIn, Work.GW2.layer, Subgroup.map_eq_bot_iff]
  refine sSup_le ?_
  rintro E ⟨hEn, hEq⟩
  have hEsup : E ≤ Work.GW2.layer ↥A := by
    rw [Work.GW2.layer]
    exact le_sSup (show E ∈ {F : Subgroup ↥A | F.Normal ∧ Work.GW2.IsQuasisimple F}
      from ⟨hEn, hEq⟩)
  have hmapZ : E.map A.subtype ≤ Z := le_trans (Subgroup.map_mono hEsup) hle
  have hmapbot : E.map A.subtype = ⊥ :=
    b16_isQuasisimple_eq_bot_of_le_isMulCommutative
      (b16_isQuasisimple_map A.subtype (fun _ _ h => Subtype.ext h) hEq) hZ hmapZ
  exact (Subgroup.map_eq_bot_iff E).mp hmapbot

/-- **A layer commutes with `K`** as soon as all its `normal`-quasisimple generators do.
This is the `⁅_,_⁆` form of `b16_layerIn_le_centralizer`. -/
theorem b16_commutator_layerIn_eq_bot {G : Type*} [Group G] {A K : Subgroup G}
    (h : ∀ E : Subgroup ↥A, E.Normal → Work.GW2.IsQuasisimple E →
      ⁅E.map A.subtype, K⁆ = ⊥) : ⁅Work.GW2.layerIn A, K⁆ = ⊥ := by
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
  refine b16_layerIn_le_centralizer ?_
  intro E hEn hEq
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h E hEn hEq)

/-- **Two layers commute** as soon as all their `normal`-quasisimple generators commute
(pairwise, across the two layers).  This is the form in which the Bender 1.6 proof uses
"distinct quasisimple subgroups commute": `[L_A, L_B] = 1`. -/
theorem b16_commutator_layerIn_layerIn_eq_bot {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ (E : Subgroup ↥A) (F : Subgroup ↥B), E.Normal → F.Normal →
      Work.GW2.IsQuasisimple E → Work.GW2.IsQuasisimple F →
      ⁅E.map A.subtype, F.map B.subtype⁆ = ⊥) :
    ⁅Work.GW2.layerIn A, Work.GW2.layerIn B⁆ = ⊥ := by
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_
  refine b16_layerIn_le_centralizer (A := A) (K := Work.GW2.layerIn B) ?_
  intro E hEn hEq
  rw [Subgroup.le_centralizer_iff]
  refine b16_layerIn_le_centralizer (A := B) (K := E.map A.subtype) ?_
  intro F hFn hFq
  rw [Subgroup.le_centralizer_iff]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h E F hEn hFn hEq hFq)

/-- If the layer of `A` is trivial then `F*(A) = F(A)`: with this workspace's definitions
`fstar X = fitting X ⊔ layer X`, so a vanishing layer collapses `F*` onto the Fitting
subgroup.  Every step of Bender's argument below the two delegated sub-goals uses this. -/
theorem b16_fstarIn_eq_fittingIn_of_layerIn_eq_bot {G : Type*} [Group G] {A : Subgroup G}
    (h : Work.GW2.layerIn A = ⊥) : Work.GW2.fstarIn A = Work.GW2.fittingIn A := by
  simp only [Work.GW2.fstarIn, Work.GW2.fstar, Work.GW2.layerIn, Work.GW2.fittingIn] at *
  rw [sup_comm, Subgroup.map_sup, h, bot_sup_eq]

/- **Bender 1970, 1.6.**  Two different maximal subgroups `A ≠ B` of a finite simple group
`G` with `F*(A) ≤ B` and `F*(B) ≤ A` have `F*(A)` and `F*(B)` both `p`-groups, for one and
the same prime `p` (with the `F*` of this workspace: `fstar X = F(X) · layer(X)`, `layer`
being the join of the *normal* quasisimple subgroups of `X`).

**REMOVED.**  The statement below was requested in round 1 without the `D`-group hypotheses;
its prover refuted it (GAP, `G = PSp(4,5)`), and the corrected form — with
`DihOrCycSylow A/B` and `IsDGroup A/B`, and `LocalToolkit` as a parameter — is
`Work.GW2.Bender16Prop`, proved in `BMAX/Bender16DGroup.lean`.  See
`NOTES_FALSE_Bender17Prop.md`.  The `b16_*` lemmas above are the proved auxiliary facts of
this file and are still used by `Bender16DGroup`. -/
end Work.BMAX
