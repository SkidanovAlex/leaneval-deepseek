import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.roundUncolDefs
import Submission.Work.Deep.Conc.Pi

/-!
# `Work.Deep.Kahn.Round.roundUncolMean`

The **first-moment computation** for the activated-but-blocked colour-degree count
`uncolActCount ω x γ` (the paper's `uncolActivatedNbrsRV`).

For the fixed pair `(x,γ)` and an edge `e` of the `γ`-edges through `x`, the probability that
`e` is activated, carries the colour `δ ∈ L e` **and is blocked** is

  `(1/(KΛ)) · (1 - (1 - 1/(KΛ)) ^ #(blkOf e δ))`

(the blockers in `blkOf e δ` are independent coordinates, each activated with colour `δ` with
probability `1/(KΛ)`, and `e` itself is one prescribed coordinate).  Summing over `Λ` colours
and over the at most `D` edges of `colThru x γ` gives the bound

  `E #(uncolActSet ω x γ) ≤ (1/K) (1 - retention) D`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

open Work.Deep.Conc

namespace Round

/-! ## A general product-space computation -/

/-- **One prescribed coordinate and a set of excluded coordinates** in a uniform product space:
the probability that the coordinate `e` takes the value `v e` while every coordinate of `S`
avoids `v` is `1/#(π e) · ∏_{f ∈ S} (1 - 1/#(π f))`. -/
theorem prob_eq_and_ne {ι : Type*} [Fintype ι] [DecidableEq ι] {π : ι → Type*}
    [∀ i, Fintype (π i)] [∀ i, DecidableEq (π i)] (hne : ∀ i, Nonempty (π i))
    (v : ∀ i, π i) (S : Finset ι) (e : ι) (heS : e ∉ S) :
    Work.Deep.Conc.prob {ξ : ∀ i, π i | ξ e = v e ∧ ∀ f ∈ S, ξ f ≠ v f}
      = (1 / (Fintype.card (π e) : ℝ)) * ∏ f ∈ S, (1 - 1 / (Fintype.card (π f) : ℝ)) := by
  classical
  set T : Finset ι := insert e S with hT
  set g : ∀ i : ι, π i → ℝ := fun i a =>
    if i = e then (if a = v i then (1 : ℝ) else 0) else (if a = v i then (0 : ℝ) else 1) with hg
  have hmemT : ∀ i, i ∈ T ↔ i = e ∨ i ∈ S := by
    intro i; rw [hT, Finset.mem_insert]
  have hpt : ∀ ξ : ∀ i, π i,
      ({ξ' : ∀ i, π i | ξ' e = v e ∧ ∀ f ∈ S, ξ' f ≠ v f} : Set (∀ i, π i)).indicator
          (fun _ => (1 : ℝ)) ξ = ∏ i ∈ T, g i (ξ i) := by
    intro ξ
    by_cases hξ : ξ e = v e ∧ ∀ f ∈ S, ξ f ≠ v f
    · rw [Set.indicator_of_mem (s := {ξ' : ∀ i, π i | ξ' e = v e ∧ ∀ f ∈ S, ξ' f ≠ v f}) hξ]
      refine (Finset.prod_eq_one ?_).symm
      intro i hi
      rcases (hmemT i).mp hi with rfl | hiS
      · simp only [hg, if_pos rfl, hξ.1, if_pos]
      · have hie : i ≠ e := fun h => heS (h ▸ hiS)
        simp only [hg, if_neg hie]
        rw [if_neg (hξ.2 i hiS)]
    · rw [Set.indicator_of_notMem (s := {ξ' : ∀ i, π i | ξ' e = v e ∧ ∀ f ∈ S, ξ' f ≠ v f}) hξ]
      symm
      rw [Finset.prod_eq_zero_iff]
      by_cases he : ξ e = v e
      · have hneg : ¬ (∀ f ∈ S, ξ f ≠ v f) := fun hall => hξ ⟨he, hall⟩
        push Not at hneg
        obtain ⟨f, hfS, hf⟩ := hneg
        refine ⟨f, (hmemT f).mpr (Or.inr hfS), ?_⟩
        have hfe : f ≠ e := fun h => heS (h ▸ hfS)
        simp only [hg, if_neg hfe, if_pos hf]
      · exact ⟨e, (hmemT e).mpr (Or.inl rfl), by simp only [hg, if_pos rfl, if_neg he]⟩
  have hpt' : ({ξ : ∀ i, π i | ξ e = v e ∧ ∀ f ∈ S, ξ f ≠ v f} : Set (∀ i, π i)).indicator
      (fun _ => (1 : ℝ)) = fun ξ => ∏ i ∈ T, g i (ξ i) := funext hpt
  have h1 : Work.Deep.Conc.prob {ξ : ∀ i, π i | ξ e = v e ∧ ∀ f ∈ S, ξ f ≠ v f}
      = Work.Deep.Conc.expect (fun ξ : ∀ i, π i => ∏ i ∈ T, g i (ξ i)) := by
    rw [Work.Deep.Conc.prob, hpt']
  rw [h1, Work.Deep.Conc.expect_prod_coord T g hne]
  -- evaluate the two kinds of factors
  have hfac_e : (∑ a : π e, g e a) = 1 := by
    simp only [hg, if_pos rfl]
    rw [Finset.sum_ite_eq' Finset.univ (v e) (fun _ => (1 : ℝ)),
      if_pos (Finset.mem_univ (v e))]
  have hfac_S : ∀ f ∈ S, (∑ a : π f, g f a) = (Fintype.card (π f) : ℝ) - 1 := by
    intro f hf
    have hfe : f ≠ e := fun h => heS (h ▸ hf)
    simp only [hg, if_neg hfe]
    have h1 : (∑ a : π f, (if a = v f then (0 : ℝ) else 1))
        = (∑ _a : π f, (1 : ℝ)) - ∑ a : π f, (if a = v f then (1 : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases h : a = v f <;> simp [h]
    rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite_eq' Finset.univ (v f) (fun _ => (1 : ℝ)),
      if_pos (Finset.mem_univ (v f))]
    ring
  have hprod : (∏ i ∈ T, (∑ a : π i, g i a) / (Fintype.card (π i) : ℝ))
      = (1 / (Fintype.card (π e) : ℝ)) * ∏ f ∈ S, (1 - 1 / (Fintype.card (π f) : ℝ)) := by
    rw [hT, Finset.prod_insert heS, hfac_e]
    congr 1
    refine Finset.prod_congr rfl fun f hf => ?_
    rw [hfac_S f hf]
    have hc : (Fintype.card (π f) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr (hne f)).ne'
    field_simp
  rw [hprod]

/-! ## The activation coordinate -/

variable {n c : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
  {L : 𝓗 → Finset (Fin c)} {K : ℕ}

/-- The coordinate at which the edge `e` is activated with the colour `δ` (an arbitrary
default value outside the list of `e`). -/
def actCoord [NeZero K] (ω₀ : Space K 𝓗 L) (δ : Fin c) (e : 𝓗) : Coord K 𝓗 L e :=
  if h : δ ∈ L e then (0, (Finset.equivFin (L e)) ⟨δ, h⟩) else ω₀ e

lemma actCoord_of_mem [NeZero K] {ω₀ : Space K 𝓗 L} {δ : Fin c} {e : 𝓗} (h : δ ∈ L e) :
    actCoord (K := K) ω₀ δ e = (0, (Finset.equivFin (L e)) ⟨δ, h⟩) := dif_pos h

/-- The colour of `e` is `δ` exactly when the second coordinate of `e` is the `δ`-index. -/
lemma colour_eq_iff [NeZero K] {ω : Space K 𝓗 L} {e : 𝓗} {δ : Fin c} (h : δ ∈ L e) :
    colour ω e = δ ↔ (ω e).2 = (Finset.equivFin (L e)) ⟨δ, h⟩ := by
  constructor
  · intro hc
    have h1 : (Finset.equivFin (L e)).symm (ω e).2
        = (Finset.equivFin (L e)).symm ((Finset.equivFin (L e)) ⟨δ, h⟩) := by
      rw [Equiv.symm_apply_apply]
      apply Subtype.ext
      exact hc
    exact (Finset.equivFin (L e)).symm.injective h1
  · intro hc
    rw [colour, hc]
    simp

/-- The coordinate of `e` is the `δ`-activation exactly when `e` is activated with colour `δ`. -/
lemma eq_actCoord_iff [NeZero K] {ω ω₀ : Space K 𝓗 L} {e : 𝓗} {δ : Fin c} (h : δ ∈ L e) :
    ω e = actCoord (K := K) ω₀ δ e ↔ active ω e ∧ colour ω e = δ := by
  rw [actCoord_of_mem (K := K) (ω₀ := ω₀) h, Prod.ext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (colour_eq_iff (K := K) h).mpr h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (colour_eq_iff (K := K) h).mp h2⟩

/-- **The probability that an edge is activated with a given colour and is blocked.**

`e` carries the colour `δ` and is activated (probability `1/(KΛ)`), and at least one of the
`|blkOf e δ|` blockers is activated with colour `δ` (independently, each with probability
`1/(KΛ)`). -/
lemma prob_act_colour_and_blocked [NeZero K] {Λ : ℕ} (hΛ : ∀ e : 𝓗, (L e).card = Λ)
    (hΛ1 : 1 ≤ Λ) (hK1 : 1 ≤ K) (ω₀ : Space K 𝓗 L) (e : 𝓗) (δ : Fin c) (hδ : δ ∈ L e) :
    Work.Deep.Conc.prob {ω : Space K 𝓗 L | active ω e ∧ colour ω e = δ ∧ ¬ kept ω e}
      = (1 / ((K : ℝ) * (Λ : ℝ))) *
        (1 - (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ (blkOf (L := L) e δ).card) := by
  classical
  have hne : ∀ i : 𝓗, Nonempty (Coord K 𝓗 L i) :=
    fun i => ⟨(0, ⟨0, by rw [hΛ i]; omega⟩)⟩
  set S : Finset 𝓗 := blkOf (L := L) e δ with hS
  have heS : e ∉ S := by
    intro h; exact (mem_blkOf.mp h).1 rfl
  have hcard_i : ∀ i : 𝓗, Fintype.card (Coord K 𝓗 L i) = K * Λ := by
    intro i
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hΛ i]
  set v : ∀ i : 𝓗, Coord K 𝓗 L i := actCoord (K := K) ω₀ δ with hv
  have hprobA : Work.Deep.Conc.prob {ω : Space K 𝓗 L | ω e = v e}
      = 1 / ((K : ℝ) * (Λ : ℝ)) := by
    rw [Work.Deep.Conc.prob_coord_eq e (v e) hne, hcard_i e]
    push_cast
    rfl
  have hprobB : Work.Deep.Conc.prob {ω : Space K 𝓗 L | ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f}
      = (1 / ((K : ℝ) * (Λ : ℝ))) *
        (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ S.card := by
    rw [prob_eq_and_ne hne v S e heS]
    have hprod : (∏ f ∈ S, (1 - 1 / (Fintype.card (Coord K 𝓗 L f) : ℝ)))
        = (1 - 1 / ((K : ℝ) * (Λ : ℝ))) ^ S.card := by
      rw [Finset.prod_congr rfl (fun f _ => by rw [hcard_i f]), Finset.prod_const]
      push_cast
      ring
    rw [hprod, hcard_i e]
    push_cast
    rfl
  -- the event `{active e ∧ colour e = δ ∧ ¬ kept e}` is `A ∩ Bᶜ`
  have hset : {ω : Space K 𝓗 L | active ω e ∧ colour ω e = δ ∧ ¬ kept ω e}
      = {ω : Space K 𝓗 L | ω e = v e} ∩
        ({ω : Space K 𝓗 L | ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f}ᶜ) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨ha, hc, hk⟩
      refine ⟨(eq_actCoord_iff (K := K) hδ).mpr ⟨ha, hc⟩, ?_⟩
      rintro ⟨-, hall⟩
      obtain ⟨g, hgne, hmeet, hgact, hgcol⟩ := exists_blocker_of_not_kept (K := K) ha hk
      have hgδ : δ ∈ L g := by rw [← hc, ← hgcol]; exact colour_mem ω g
      have hgS : g ∈ S := by rw [hS]; exact mem_blkOf.mpr ⟨hgne, hmeet, hgδ⟩
      exact hall g hgS ((eq_actCoord_iff (K := K) hgδ).mpr ⟨hgact, hgcol.trans hc⟩)
    · rintro ⟨heq, hnb⟩
      obtain ⟨ha, hc⟩ := (eq_actCoord_iff (K := K) hδ).mp heq
      refine ⟨ha, hc, fun hk => ?_⟩
      have hex : ∃ f ∈ S, ω f = v f := by
        by_contra hcon
        exact hnb ⟨heq, fun f hf hfv => hcon ⟨f, hf, hfv⟩⟩
      obtain ⟨f, hfS, hfv⟩ := hex
      have hfm : f ∈ blkOf (L := L) e δ := by rw [← hS]; exact hfS
      obtain ⟨hfne, hfmeet, hfδ⟩ := mem_blkOf.mp hfm
      have hfact : active ω f ∧ colour ω f = δ := (eq_actCoord_iff (K := K) hfδ).mp (hv ▸ hfv)
      rw [kept] at hk
      exact hk.2 f hfne hfmeet hfact.1 (hfact.2.trans hc.symm)
  -- indicator identity and subtraction of probabilities
  have hind : ∀ ω : Space K 𝓗 L,
      (({ω : Space K 𝓗 L | ω e = v e} ∩
          ({ω : Space K 𝓗 L | ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f}ᶜ) :
            Set (Space K 𝓗 L)).indicator (fun _ => (1 : ℝ))) ω
        = ({ω : Space K 𝓗 L | ω e = v e} : Set (Space K 𝓗 L)).indicator (fun _ => (1 : ℝ)) ω
          - ({ω : Space K 𝓗 L | ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f} :
              Set (Space K 𝓗 L)).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hA : ω e = v e
    · by_cases hB : ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f
      · rw [Set.indicator_of_notMem (s := {ω : Space K 𝓗 L | ω e = v e} ∩
              ({ω : Space K 𝓗 L | ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f}ᶜ))
            (by simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff];
                exact fun h => h.2 hB),
          Set.indicator_of_mem (s := {ω : Space K 𝓗 L | ω e = v e}) hA,
          Set.indicator_of_mem (s := {ω : Space K 𝓗 L | ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f}) hB]
        norm_num
      · rw [Set.indicator_of_mem (s := {ω : Space K 𝓗 L | ω e = v e} ∩
              ({ω : Space K 𝓗 L | ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f}ᶜ))
            (by simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff];
                exact ⟨hA, hB⟩),
          Set.indicator_of_mem (s := {ω : Space K 𝓗 L | ω e = v e}) hA,
          Set.indicator_of_notMem (s := {ω : Space K 𝓗 L | ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f}) hB]
        norm_num
    · have hB' : ω ∉ ({ω : Space K 𝓗 L | ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f} :
          Set (Space K 𝓗 L)) := fun h => hA h.1
      rw [Set.indicator_of_notMem (s := {ω : Space K 𝓗 L | ω e = v e} ∩
            ({ω : Space K 𝓗 L | ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f}ᶜ))
            (by simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]; exact fun h => hA h.1)
            (fun _ => (1 : ℝ)),
          Set.indicator_of_notMem (s := {ω : Space K 𝓗 L | ω e = v e}) hA (fun _ => (1 : ℝ)),
          Set.indicator_of_notMem (s := {ω : Space K 𝓗 L | ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f})
            hB' (fun _ => (1 : ℝ))]
      simp
  have hdiff : Work.Deep.Conc.prob {ω : Space K 𝓗 L | active ω e ∧ colour ω e = δ ∧ ¬ kept ω e}
      = Work.Deep.Conc.prob {ω : Space K 𝓗 L | ω e = v e}
        - Work.Deep.Conc.prob {ω : Space K 𝓗 L | ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f} := by
    have hsum : (∑ ω : Space K 𝓗 L,
          (({ω : Space K 𝓗 L | ω e = v e} ∩
            ({ω : Space K 𝓗 L | ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f}ᶜ) :
              Set (Space K 𝓗 L)).indicator (fun _ => (1 : ℝ)) ω))
        = (∑ ω : Space K 𝓗 L,
          (({ω : Space K 𝓗 L | ω e = v e} : Set (Space K 𝓗 L)).indicator (fun _ => (1 : ℝ)) ω
            - ({ω : Space K 𝓗 L | ω e = v e ∧ ∀ f ∈ S, ω f ≠ v f} :
                Set (Space K 𝓗 L)).indicator (fun _ => (1 : ℝ)) ω)) :=
      Finset.sum_congr rfl fun ω _ => hind ω
    simp only [Work.Deep.Conc.prob, Work.Deep.Conc.expect]
    rw [hset, hsum, Finset.sum_sub_distrib, sub_div]
  rw [hdiff, hprobA, hprobB]
  ring


/-- **The first-moment bound** for `uncolActCount` at `(x,γ)`. -/
theorem roundUncolMean {n c K C D Λ : ℕ}
    {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗] [NeZero K]
    {L : 𝓗 → Finset (Fin c)} (x : Fin n) (γ : Fin c)
    (hΛ1 : 1 ≤ Λ) (hK1 : 1 ≤ K)
    (hΛ : ∀ e : 𝓗, (L e).card = Λ)
    (hblk : ∀ e ∈ colThru (L := L) x γ, ∀ δ ∈ L e, (blkOf (L := L) e δ).card ≤ C * (D - 1))
    (hcol : (colThru (L := L) x γ).card ≤ D) :
    Work.Deep.Conc.expect (fun ω : Space K 𝓗 L =>
        (uncolActCount (K := K) (L := L) ω x γ : ℝ))
      ≤ (1 / (K : ℝ)) * (1 - retention Λ C D K) * (D : ℝ) := by
  classical
  have hne : ∀ i : 𝓗, Nonempty (Coord K 𝓗 L i) :=
    fun i => ⟨(0, ⟨0, by rw [hΛ i]; omega⟩)⟩
  haveI : Nonempty (Space K 𝓗 L) := ⟨fun i => Classical.choice (hne i)⟩
  set u : ℝ := 1 / ((K : ℝ) * (Λ : ℝ)) with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu1 : u ≤ 1 := by
    rw [hu, div_le_one (by positivity)]
    have h1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    have h2 : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ1
    nlinarith
  -- step 1: `uncolActCount` as a sum of indicators
  have hX : ∀ ω : Space K 𝓗 L, (uncolActCount (K := K) (L := L) ω x γ : ℝ)
      = ∑ e ∈ colThru (L := L) x γ, (if active ω e ∧ ¬ kept ω e then (1 : ℝ) else 0) := by
    intro ω
    have h : uncolActCount (K := K) (L := L) ω x γ
        = ((colThru (L := L) x γ).filter (fun e : 𝓗 => active ω e ∧ ¬ kept ω e)).card := by
      rw [← uncolActSet_card (K := K) (L := L) ω x γ]
      rfl
    rw [h, Finset.card_filter]
    push_cast
    rfl
  -- step 2: the expectation of the sum
  have hExpect : Work.Deep.Conc.expect (fun ω : Space K 𝓗 L =>
        (uncolActCount (K := K) (L := L) ω x γ : ℝ))
      = ∑ e ∈ colThru (L := L) x γ,
          Work.Deep.Conc.prob {ω : Space K 𝓗 L | active ω e ∧ ¬ kept ω e} := by
    rw [funext hX, Work.Deep.Conc.expect_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Work.Deep.Conc.prob]
    refine Work.Deep.Conc.expect_congr fun ω => ?_
    by_cases h : active ω e ∧ ¬ kept ω e
    · rw [Set.indicator_of_mem (s := {ω : Space K 𝓗 L | active ω e ∧ ¬ kept ω e})
        (by simpa using h) (fun _ => (1 : ℝ)), if_pos h]
    · rw [Set.indicator_of_notMem (s := {ω : Space K 𝓗 L | active ω e ∧ ¬ kept ω e})
        (by simpa using h) (fun _ => (1 : ℝ)), if_neg h]
  -- step 3: the per-edge bound
  have hterm : ∀ e ∈ colThru (L := L) x γ,
      Work.Deep.Conc.prob {ω : Space K 𝓗 L | active ω e ∧ ¬ kept ω e}
        ≤ (1 / (K : ℝ)) * (1 - (1 - u) ^ (C * (D - 1))) := by
    intro e he
    have hsub : {ω : Space K 𝓗 L | active ω e ∧ ¬ kept ω e} ⊆
        ⋃ δ : {δ : Fin c // δ ∈ L e},
          {ω : Space K 𝓗 L | active ω e ∧ colour ω e = δ.1 ∧ ¬ kept ω e} := by
      intro ω hω
      exact Set.mem_iUnion.mpr ⟨⟨colour ω e, colour_mem ω e⟩, hω.1, rfl, hω.2⟩
    have h1 : Work.Deep.Conc.prob {ω : Space K 𝓗 L | active ω e ∧ ¬ kept ω e}
        ≤ ∑ δ ∈ L e, Work.Deep.Conc.prob
            {ω : Space K 𝓗 L | active ω e ∧ colour ω e = δ ∧ ¬ kept ω e} := by
      refine le_trans (Work.Deep.Conc.prob_mono hsub) ?_
      refine le_trans (Work.Deep.Conc.prob_iUnion_le _) ?_
      rw [← Finset.sum_subtype (L e) (fun δ => Iff.rfl) (fun δ : Fin c =>
        Work.Deep.Conc.prob
          {ω : Space K 𝓗 L | active ω e ∧ colour ω e = δ ∧ ¬ kept ω e})]
    refine le_trans h1 ?_
    have h2 : (∑ δ ∈ L e, Work.Deep.Conc.prob
          {ω : Space K 𝓗 L | active ω e ∧ colour ω e = δ ∧ ¬ kept ω e})
        ≤ ∑ _δ ∈ L e, u * (1 - (1 - u) ^ (C * (D - 1))) := by
      refine Finset.sum_le_sum fun δ hδ => ?_
      rw [prob_act_colour_and_blocked (K := K) (L := L) hΛ hΛ1 hK1
        (Classical.arbitrary (Space K 𝓗 L)) e δ hδ]
      rw [← hu]
      have hle : (blkOf (L := L) e δ).card ≤ C * (D - 1) := hblk e he δ hδ
      have hpow : (1 - u) ^ (C * (D - 1)) ≤ (1 - u) ^ (blkOf (L := L) e δ).card :=
        pow_le_pow_of_le_one (a := 1 - u) (by linarith) (by linarith) hle
      exact mul_le_mul_of_nonneg_left (by linarith) hu0
    refine le_trans h2 ?_
    rw [Finset.sum_const, hΛ e, nsmul_eq_mul]
    have harith : (Λ : ℝ) * (u * (1 - (1 - u) ^ (C * (D - 1))))
        = (1 / (K : ℝ)) * (1 - (1 - u) ^ (C * (D - 1))) := by
      rw [hu]
      field_simp
    rw [harith]
  -- step 4: sum over the edges and pass to `retention`
  rw [hExpect]
  have hsum_le : (∑ e ∈ colThru (L := L) x γ,
        Work.Deep.Conc.prob {ω : Space K 𝓗 L | active ω e ∧ ¬ kept ω e})
      ≤ ((colThru (L := L) x γ).card : ℝ) *
          ((1 / (K : ℝ)) * (1 - (1 - u) ^ (C * (D - 1)))) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have hret : retention Λ C D K = (1 - u) ^ (C * D) := by
    rw [retention, hu]
    congr 1
    rw [div_div]
  have hpowle : (1 - u) ^ (C * D) ≤ (1 - u) ^ (C * (D - 1)) :=
    pow_le_pow_of_le_one (a := 1 - u) (by linarith) (by linarith)
      (Nat.mul_le_mul_left C (Nat.sub_le D 1))
  refine le_trans hsum_le ?_
  have hcard : ((colThru (L := L) x γ).card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hcol
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK1)
  have hDpos : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hfac : (0 : ℝ) ≤ (1 / (K : ℝ)) * (1 - (1 - u) ^ (C * (D - 1))) := by
    have h1 : (0 : ℝ) ≤ 1 - (1 - u) ^ (C * (D - 1)) := by
      have hle1 : (1 - u) ^ (C * (D - 1)) ≤ 1 :=
        pow_le_one₀ (n := C * (D - 1)) (by linarith : (0:ℝ) ≤ 1 - u)
          (by linarith : 1 - u ≤ 1)
      linarith
    positivity
  have hfacD : (0 : ℝ) ≤ (1 / (K : ℝ)) * (1 - retention Λ C D K) := by
    rw [hret]
    have h1 : (0 : ℝ) ≤ 1 - (1 - u) ^ (C * D) := by
      have hle1 : (1 - u) ^ (C * D) ≤ 1 :=
        pow_le_one₀ (n := C * D) (by linarith : (0:ℝ) ≤ 1 - u) (by linarith : 1 - u ≤ 1)
      linarith
    positivity
  calc ((colThru (L := L) x γ).card : ℝ) * ((1 / (K : ℝ)) * (1 - (1 - u) ^ (C * (D - 1))))
      ≤ (D : ℝ) * ((1 / (K : ℝ)) * (1 - (1 - u) ^ (C * (D - 1)))) :=
        mul_le_mul_of_nonneg_right hcard hfac
    _ ≤ (D : ℝ) * ((1 / (K : ℝ)) * (1 - retention Λ C D K)) := by
        refine mul_le_mul_of_nonneg_left ?_ hDpos
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hret]
        linarith
    _ = (1 / (K : ℝ)) * (1 - retention Λ C D K) * (D : ℝ) := by ring

end Round

end

end Work.Deep.Kahn
