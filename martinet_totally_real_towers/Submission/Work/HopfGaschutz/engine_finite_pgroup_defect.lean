import Mathlib
import Submission.Work.HopfGaschutz.Defs
import Submission.Commons.GroupTheory.PGroup.pow_mem_frattini
import Submission.Work.RelatorRank.Gaschutz.frattini_nongenerating_of_fg

/-!
# The finite `p`-group engine for the relation-Frattini subgroup, in a possibly infinite
ambient group

**Namespace** `Work.HopfGaschutz`; module
`Submission.Work.HopfGaschutz.engine_finite_pgroup_defect`.

The `S = ∅` case of the *engine* of the relation-rank dictionary
(`Submission/Work/HopfGaschutz/Defs.lean`, `README.md` §2): if `V` is a **finite** normal
`p`-subgroup of an arbitrary group `G` such that the quotient `G ⧸ V` is again a `p`-group, then

  `V ≤ V^p · [V,G]` forces `V = ⊥`.

This is the Nakayama step `V = V^p[V,G] → V = ⊥`, but with the ambient group `G` allowed to be
infinite -- which is exactly the situation in which the engine is consumed: `V` is the *defect*
`K ⧸ ⟪S⟫` of a normal generating set, a finite `p`-group, while the ambient `F ⧸ ⟪S⟫` is a
(finite index in an infinite) extension of `V` by the finite quotient `F ⧸ K`.

## Mathematics

The proof is the classical one: `V` is a finite `p`-group on which the `p`-group `G` acts by
conjugation.  Two facts suffice.

1. *A `p`-group acts on a nontrivial finite `p`-group with nontrivial fixed points.*  Since
   `G ⧸ V` and `V` are `p`-groups, so is `G` (an extension of `p`-groups is a `p`-group,
   `isPGroup_of_isPGroup_quotient`), and the number of conjugation-fixed points of `V` is
   congruent to `|V|` modulo `p` (`IsPGroup.card_modEq_card_fixedPoints`), hence not `1`:
   `V ⊓ Z(G) ≠ ⊥`.  This is where the *finiteness of `V`* is used, and it is used essentially:
   for infinite `V` the statement is false (a Tarski monster is equal to its Frattini subgroup).
2. *Nakayama/descent.*  `N := V ⊓ Z(G)` is a nontrivial normal subgroup of `G`, and the
   hypothesis `V ≤ V^p[V,G]` descends to the quotient `G ⧸ N`, where it reads
   `V/N ≤ (V/N)^p · [V/N, G/N]`.  Applying the statement to `G ⧸ N` (whose subgroup `V/N` is
   strictly smaller) shows `V = N`, i.e. `V ≤ Z(G)`; then `[V,G] = ⊥` and the hypothesis
   becomes `V ≤ V^p ≤ Φ(V)`, so Gaschütz's non-generator property (`V ≤ Φ(V)` forces `V = ⊥`)
   gives the contradiction.

Everything is proved by strong induction on `|V|`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.HopfGaschutz

open scoped commutatorElement

/-! ## An extension of `p`-groups is a `p`-group -/

/-- If `N ⊴ G`, `N` is a `p`-group and `G ⧸ N` is a `p`-group, then `G` is a `p`-group. -/
private lemma isPGroup_of_isPGroup_quotient {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hN : IsPGroup p ↥N) (hq : IsPGroup p (G ⧸ N)) :
    IsPGroup p G := by
  have htop : IsPGroup p ↥(⊤ : Subgroup (G ⧸ N)) := hq.of_equiv Subgroup.topEquiv.symm
  have hker : IsPGroup p ↥(QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']; exact hN
  have hcomap := IsPGroup.comap_of_ker_isPGroup (H := ⊤) htop (QuotientGroup.mk' N) hker
  rw [Subgroup.comap_top] at hcomap
  exact hcomap.of_equiv Subgroup.topEquiv

/-! ## A nontrivial finite `p`-group acted on by a `p`-group has a nontrivial fixed point -/

/-- **The fixed-point step.**  Let `V` be a nontrivial finite normal `p`-subgroup of a group `G`
which is itself a `p`-group.  Then `V` meets the centre of `G` nontrivially.

The conjugation action of `G` on the finite set `↥V` is an action of the `p`-group `G`, so the
number of fixed points is congruent to `|V| ≡ 0` mod `p`; as `1` is a fixed point, there is
another one, and a conjugation-fixed element of `V` is central in `G`. -/
private lemma inf_center_ne_bot_of_finite_pgroup {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) {V : Subgroup G} [V.Normal] (hfin : Finite ↥V) (hV : IsPGroup p ↥V)
    (hne : V ≠ ⊥) : V ⊓ Subgroup.center G ≠ ⊥ := by
  haveI : Finite ↥V := hfin
  haveI hpc : IsPGroup p (ConjAct G) := hG.of_equiv ConjAct.toConjAct
  have hdvd : p ∣ Nat.card ↥V := by
    rcases hV.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hne
    · exact h1
  obtain ⟨b, hb, hbne⟩ :=
    hpc.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥V hdvd (a := (1 : ↥V))
      (by rw [MulAction.mem_fixedPoints]; intro x; exact MulDistribMulAction.smul_one x)
  have hfix : ∀ g : G, g * (b : G) * g⁻¹ = (b : G) := by
    intro g
    have h1 : (ConjAct.toConjAct g) • b = b := (MulAction.mem_fixedPoints.mp hb) _
    have h2 : ((ConjAct.toConjAct g) • b : G) = (b : G) := congrArg Subtype.val h1
    rwa [ConjAct.toConjAct_smul_eq_mulAut_conj, MulAut.conj_apply] at h2
  have hcent : (b : G) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 : g * (b : G) * g⁻¹ * g = (b : G) * g := by rw [hfix g]
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h2
  intro hcon
  have hmem : (b : G) ∈ V ⊓ Subgroup.center G := Subgroup.mem_inf.mpr ⟨b.2, hcent⟩
  rw [hcon, Subgroup.mem_bot] at hmem
  exact hbne (Subtype.ext hmem.symm)

/-! ## Descending the hypothesis to a quotient -/

/-- The hypothesis `V ≤ V^p · [V,G]` descends along any surjection: the image `V.map φ` satisfies
`V.map φ ≤ (V.map φ)^p · [V.map φ, ⊤]`. -/
private lemma map_le_pPower_sup_commutator {G H : Type*} [Group G] [Group H] {p : ℕ}
    (φ : G →* H) (hφ : Function.Surjective φ) {V : Subgroup G}
    (h : V ≤ pPower p V ⊔ ⁅V, ⊤⁆) : V.map φ ≤ pPower p (V.map φ) ⊔ ⁅V.map φ, ⊤⁆ := by
  have h1 : V.map φ ≤ Subgroup.map φ (pPower p V ⊔ ⁅V, (⊤ : Subgroup G)⁆) := Subgroup.map_mono h
  rw [Subgroup.map_sup] at h1
  have hpow : Subgroup.map φ (pPower p V) ≤ pPower p (Subgroup.map φ V) := by
    rw [Subgroup.map_le_iff_le_comap]
    show pPower p V ≤ Subgroup.comap φ (pPower p (Subgroup.map φ V))
    rw [pPower, pPower, Subgroup.closure_le]
    rintro x ⟨k, hk, rfl⟩
    exact Subgroup.subset_closure ⟨φ k, Subgroup.mem_map_of_mem φ hk, (map_pow φ k p).symm⟩
  have hcomm : Subgroup.map φ ⁅V, (⊤ : Subgroup G)⁆ ≤ ⁅Subgroup.map φ V, (⊤ : Subgroup H)⁆ :=
    le_of_eq (by rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective φ hφ])
  exact h1.trans (sup_le (hpow.trans le_sup_left) (hcomm.trans le_sup_right))

/-- **The cardinality of a proper quotient of a subgroup.**  If `N ≤ V` is a nontrivial normal
subgroup of `G` and `V` is finite, then the image of `V` in `G ⧸ N` has strictly smaller
cardinality than `V`. -/
private lemma card_map_quotient_lt {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    {V : Subgroup G} [Finite ↥V] (hNV : N ≤ V) (hN : N ≠ ⊥) :
    Nat.card ↥(V.map (QuotientGroup.mk' N)) < Nat.card ↥V := by
  haveI : Finite ↥N :=
    Finite.of_injective (Subgroup.inclusion hNV) (Subgroup.inclusion_injective hNV)
  have hker : ((QuotientGroup.mk' N).domRestrict V).ker = N.subgroupOf V := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  have hr : ((QuotientGroup.mk' N).domRestrict V).range = V.map (QuotientGroup.mk' N) :=
    MonoidHom.domRestrict_range V (QuotientGroup.mk' N)
  have hiso : Nat.card (↥V ⧸ N.subgroupOf V)
      = Nat.card ↥(V.map (QuotientGroup.mk' N)) := by
    have h := Nat.card_congr
      (QuotientGroup.quotientKerEquivRange ((QuotientGroup.mk' N).domRestrict V)).toEquiv
    rwa [hker, hr] at h
  have hcard : Nat.card ↥V
      = Nat.card ↥(V.map (QuotientGroup.mk' N)) * Nat.card ↥(N.subgroupOf V) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf V), hiso]
  have hker2 : 1 < Nat.card ↥(N.subgroupOf V) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNV).toEquiv]
    exact Subgroup.one_lt_card_iff_ne_bot N |>.mpr hN
  have hposV : 0 < Nat.card ↥V := Nat.card_pos
  have hposA : 0 < Nat.card ↥(V.map (QuotientGroup.mk' N)) := by
    rcases Nat.eq_zero_or_pos (Nat.card ↥(V.map (QuotientGroup.mk' N))) with h | h
    · rw [h, zero_mul] at hcard
      exact absurd hcard hposV.ne'
    · exact h
  calc Nat.card ↥(V.map (QuotientGroup.mk' N))
      < Nat.card ↥(V.map (QuotientGroup.mk' N)) * Nat.card ↥(N.subgroupOf V) :=
        lt_mul_of_one_lt_right hposA hker2
    _ = Nat.card ↥V := hcard.symm

/-! ## The endgame: `V ≤ V^p` for a finite `p`-group forces `V = ⊥` -/

/-- Every `p`-th power of an element of a finite `p`-group lies in the Frattini subgroup
(`Commons.GroupTheory.PGroup.pow_mem_frattini`), so `V ≤ V^p` forces `V ≤ Φ(V)`; Gaschütz's
non-generator property then gives `V = ⊥`. -/
private lemma eq_bot_of_le_pPower_of_finite_pgroup {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {V : Subgroup G} [Finite ↥V] (hV : IsPGroup p ↥V) (h : V ≤ pPower p V) : V = ⊥ := by
  haveI : Fintype ↥V := Fintype.ofFinite _
  have hstep : pPower p V ≤ Subgroup.map V.subtype (frattini ↥V) := by
    rw [pPower, Subgroup.closure_le]
    rintro g ⟨k, hk, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨(⟨k, hk⟩ : ↥V) ^ p, Commons.GroupTheory.PGroup.pow_mem_frattini hV ⟨k, hk⟩,
        Subgroup.coe_pow V ⟨k, hk⟩ p⟩
  have hfratt : frattini ↥V = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ Subgroup.map V.subtype (frattini ↥V) := hstep (h x.2)
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rwa [show y = x from Subtype.ext hyx] at hy
  have htopbot : (⊤ : Subgroup ↥V) = ⊥ := by
    have h := Work.RelatorRank.Gaschutz.frattini_nongenerating_of_fg (G := ↥V)
      (Group.fg_of_finite) (⊥ : Subgroup ↥V) (by rw [hfratt, bot_sup_eq])
    rw [← h]
  refine (Subgroup.eq_bot_iff_forall V).mpr ?_
  intro x hx
  have h1 : (⟨x, hx⟩ : ↥V) ∈ (⊤ : Subgroup ↥V) := trivial
  rw [htopbot] at h1
  simpa using Subgroup.mem_bot.mp h1

/-! ## The induction -/

/-- Strong induction on `|V|`; see the module docstring for the two steps. -/
private theorem engine_aux : ∀ n : ℕ, ∀ (G : Type*) [Group G] (p : ℕ) [Fact p.Prime]
    (V : Subgroup G) [V.Normal], Nat.card ↥V = n → Finite ↥V → IsPGroup p ↥V →
    IsPGroup p (G ⧸ V) → V ≤ pPower p V ⊔ ⁅V, ⊤⁆ → V = ⊥ := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih G _ p _ V _ hcard hfin hV hquot h
  classical
  haveI : Finite ↥V := hfin
  by_contra hne
  have hG : IsPGroup p G := isPGroup_of_isPGroup_quotient hV hquot
  set N : Subgroup G := V ⊓ Subgroup.center G with hNdef
  have hNne : N ≠ ⊥ := inf_center_ne_bot_of_finite_pgroup hG hfin hV hne
  have hNnorm : N.Normal := by
    rw [hNdef]; exact Subgroup.normal_of_le_center inf_le_right
  have hNle : N ≤ V := by rw [hNdef]; exact inf_le_left
  -- `V` is central in `G`
  have hVleCenter : V ≤ Subgroup.center G := by
    by_cases hNV : N = V
    · intro x hx
      exact (Subgroup.mem_inf.mp (hNV.symm ▸ hx)).2
    · -- pass to `G ⧸ N`, where `V` becomes the strictly smaller `V/N`
      letI : N.Normal := hNnorm
      set W : Subgroup (G ⧸ N) := V.map (QuotientGroup.mk' N) with hWdef
      have hWnorm : W.Normal :=
        Subgroup.Normal.map inferInstance (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      letI : W.Normal := hWnorm
      have hsurj : Function.Surjective
          (fun x : ↥V => (⟨QuotientGroup.mk' N (x : G), ⟨(x : G), x.2, rfl⟩⟩ : ↥W)) := by
        rintro ⟨y, hy⟩
        obtain ⟨x, hxV, hxy⟩ := Subgroup.mem_map.mp hy
        exact ⟨⟨x, hxV⟩, Subtype.ext hxy⟩
      haveI hWfin : Finite ↥W := Finite.of_surjective _ hsurj
      have hWp : IsPGroup p ↥W := IsPGroup.map hV (QuotientGroup.mk' N)
      have hWquot : IsPGroup p ((G ⧸ N) ⧸ W) :=
        hquot.of_equiv (QuotientGroup.quotientQuotientEquivQuotient N V hNle).symm
      have hWh : W ≤ pPower p W ⊔ ⁅W, ⊤⁆ :=
        map_le_pPower_sup_commutator _ (QuotientGroup.mk'_surjective N) h
      have hWlt : Nat.card ↥W < n := by
        rw [← hcard]; exact card_map_quotient_lt hNle hNne
      have hWbot : W = ⊥ := ih (Nat.card ↥W) hWlt (G ⧸ N) p W rfl hWfin hWp hWquot hWh
      have hVleN : V ≤ N := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hWbot
        exact hWbot
      intro x hx
      exact (Subgroup.mem_inf.mp (hVleN hx)).2
  -- now `V` is central, so `[V,G] = ⊥` and the hypothesis reads `V ≤ V^p`
  have hcomm : ⁅V, (⊤ : Subgroup G)⁆ = ⊥ :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hVleCenter
  have hpow : V ≤ pPower p V := by
    have h' := h
    rw [hcomm, sup_bot_eq] at h'
    exact h'
  exact hne (eq_bot_of_le_pPower_of_finite_pgroup hV hpow)

/-- **The engine (`S = ∅` case), with the defect a finite `p`-group.**  Let `V` be a finite
normal `p`-subgroup of a group `G` with `G ⧸ V` a `p`-group.  If `V ≤ V^p · [V,G]` then
`V = ⊥`. -/
theorem engine_finite_pgroup_defect {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {V : Subgroup G} [V.Normal] (hfin : Finite ↥V) (hV : IsPGroup p ↥V)
    (hquot : IsPGroup p (G ⧸ V))
    (h : V ≤ Work.HopfGaschutz.pPower p V ⊔ ⁅V, ⊤⁆) : V = ⊥ :=
  engine_aux (Nat.card ↥V) G p V rfl hfin hV hquot h

end Work.HopfGaschutz
