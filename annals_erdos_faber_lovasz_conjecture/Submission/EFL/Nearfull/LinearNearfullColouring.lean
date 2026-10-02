import Lean.Parser.Command
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Disjoint
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF
import Submission.EFL.Nearfull.ExistsMaximalDisjointPairing
import Submission.EFL.Nearfull.ExistsUsefulPairsInClique
import Submission.EFL.Nearfull.PairingOfUsefulFamilyClique
import Submission.EFL.Nearfull.ExistsPairingOfSizeKFamily
import Submission.Commons.Combinatorics.Hypergraph.pairing_of_useful_pairs
import Submission.Commons.Combinatorics.Hypergraph.nearfull_useful_caseA

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators
namespace Commons.Combinatorics.Hypergraph
noncomputable section


variable {n : ℕ}

/-- The ordered pairs of distinct elements of a set `e`. -/
def ordPairs (e : Set (Fin n)) : Finset (Fin n × Fin n) :=
  (e.toFinite.toFinset ×ˢ e.toFinite.toFinset).filter (fun p => p.1 ≠ p.2)

lemma mem_ordPairs (e : Set (Fin n)) (p : Fin n × Fin n) :
    p ∈ ordPairs e ↔ (p.1 ∈ e ∧ p.2 ∈ e ∧ p.1 ≠ p.2) := by
  classical
  rw [ordPairs, Finset.mem_filter, Finset.mem_product, Set.Finite.mem_toFinset,
    Set.Finite.mem_toFinset]
  tauto

lemma card_ordPairs (e : Set (Fin n)) : (ordPairs e).card = e.ncard * (e.ncard - 1) := by
  classical
  have hcard : e.toFinite.toFinset.card = e.ncard := (Set.ncard_eq_toFinset_card e).symm
  have hprod : (e.toFinite.toFinset ×ˢ e.toFinite.toFinset).card
      = e.ncard * e.ncard := by
    rw [Finset.card_product, hcard]
  have hdiag : (e.toFinite.toFinset ×ˢ e.toFinite.toFinset).filter (fun p : Fin n × Fin n => p.1 = p.2)
      = e.toFinite.toFinset.image (fun v => (v, v)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨p.1, h1, by ext <;> simp [h3]⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨hv, hv⟩, rfl⟩
  have hdiagcard : ((e.toFinite.toFinset ×ˢ e.toFinite.toFinset).filter (fun p : Fin n × Fin n => p.1 = p.2)).card
      = e.ncard := by
    rw [hdiag, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h), hcard]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := e.toFinite.toFinset ×ˢ e.toFinite.toFinset) (p := fun p : Fin n × Fin n => p.1 ≠ p.2)
  have hneg : (e.toFinite.toFinset ×ˢ e.toFinite.toFinset).filter (fun p : Fin n × Fin n => ¬ p.1 ≠ p.2)
      = (e.toFinite.toFinset ×ˢ e.toFinite.toFinset).filter (fun p : Fin n × Fin n => p.1 = p.2) := by
    ext p
    by_cases h : p.1 = p.2 <;> simp [h]
  have key : (ordPairs e).card + e.ncard = e.ncard * e.ncard := by
    show ((e.toFinite.toFinset ×ˢ e.toFinite.toFinset).filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).card
        + e.ncard = e.ncard * e.ncard
    rw [hneg, hdiagcard, hprod] at hsum
    exact hsum
  have hsub : (ordPairs e).card = e.ncard * e.ncard - e.ncard := by omega
  rw [hsub, Nat.mul_sub_left_distrib, mul_one]

lemma ordPairs_disjoint {𝓗 : Set (Set (Fin n))}
    (hlin : ∀ e₁ ∈ 𝓗, ∀ e₂ ∈ 𝓗, e₁ ≠ e₂ → (e₁ ∩ e₂).Subsingleton)
    {e₁ e₂ : Set (Fin n)} (h₁ : e₁ ∈ 𝓗) (h₂ : e₂ ∈ 𝓗) (hne : e₁ ≠ e₂) :
    Disjoint (ordPairs e₁) (ordPairs e₂) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rw [mem_ordPairs] at hp1 hp2
  exact hp1.2.2 (hlin e₁ h₁ e₂ h₂ hne ⟨hp1.1, hp2.1⟩ ⟨hp1.2.1, hp2.2.1⟩)

/-- The pairs of distinct vertices of `Fin n`. -/
def distinctPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2)

lemma card_distinctPairs (n : ℕ) : (distinctPairs n).card = n * (n - 1) := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n × Fin n))) (p := fun p : Fin n × Fin n => p.1 ≠ p.2)
  have hdiag : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p : Fin n × Fin n => p.1 = p.2)
      = (Finset.univ : Finset (Fin n)).image (fun v => (v, v)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro h3
      exact ⟨p.1, by ext <;> simp [h3]⟩
    · rintro ⟨v, rfl⟩
      rfl
  have hdiagcard : ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p : Fin n × Fin n => p.1 = p.2)).card = n := by
    rw [hdiag, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h),
      Finset.card_univ, Fintype.card_fin]
  have hneg : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p : Fin n × Fin n => ¬ p.1 ≠ p.2)
      = (Finset.univ : Finset (Fin n × Fin n)).filter (fun p : Fin n × Fin n => p.1 = p.2) := by
    ext p
    by_cases h : p.1 = p.2 <;> simp [h]
  have huniv : (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have key : (distinctPairs n).card + n = n * n := by
    show ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).card + n = n * n
    rw [hneg, hdiagcard, huniv] at hpart
    exact hpart
  have hsub : (distinctPairs n).card = n * n - n := by omega
  rw [hsub, Nat.mul_sub_left_distrib, mul_one]

lemma sum_ordPairs_le {𝓗 : Set (Set (Fin n))} (M : Finset (Set (Fin n)))
    (hM : ∀ e ∈ M, e ∈ 𝓗)
    (hlin : ∀ e₁ ∈ 𝓗, ∀ e₂ ∈ 𝓗, e₁ ≠ e₂ → (e₁ ∩ e₂).Subsingleton) :
    ∑ e ∈ M, (ordPairs e).card ≤ n * (n - 1) := by
  classical
  have hpd : (↑M : Set (Set (Fin n))).PairwiseDisjoint (fun e => ordPairs e) := by
    intro e₁ he₁ e₂ he₂ hne
    exact ordPairs_disjoint hlin (hM e₁ he₁) (hM e₂ he₂) hne
  let D : Finset (Fin n × Fin n) := M.disjiUnion (fun e => ordPairs e) hpd
  have hDcard : D.card = ∑ e ∈ M, (ordPairs e).card := Finset.card_disjiUnion M _ hpd
  have hsub : D ⊆ distinctPairs n := by
    intro p hp
    rw [Finset.mem_disjiUnion] at hp
    obtain ⟨e, -, hep⟩ := hp
    have hmem : p ∈ distinctPairs n ↔ p.1 ≠ p.2 := by simp [distinctPairs]
    rw [hmem]
    rw [mem_ordPairs] at hep
    exact hep.2.2
  have := Finset.card_le_card hsub
  rw [hDcard, card_distinctPairs] at this
  exact this

lemma sum_edgeSize_mul_le {𝓗 : Set (Set (Fin n))} (M : Finset (Set (Fin n)))
    (hM : ∀ e ∈ M, e ∈ 𝓗)
    (hlin : ∀ e₁ ∈ 𝓗, ∀ e₂ ∈ 𝓗, e₁ ≠ e₂ → (e₁ ∩ e₂).Subsingleton) :
    ∑ e ∈ M, e.ncard * (e.ncard - 1) ≤ n * (n - 1) := by
  have h := sum_ordPairs_le M hM hlin
  have hcongr : ∑ e ∈ M, (ordPairs e).card = ∑ e ∈ M, e.ncard * (e.ncard - 1) :=
    Finset.sum_congr rfl (fun e _ => card_ordPairs e)
  rw [hcongr] at h
  exact h

variable {n : ℕ}

/-- The set of edges used by a pairing `σ`. -/
def pairUsed {𝓗 : Set (Set (Fin n))} (t : ℕ)
    (σ : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗}) : Finset (Set (Fin n)) :=
  (Finset.univ : Finset (Fin t × Fin 2)).image (fun p => (σ p.1 p.2 : Set (Fin n)))

/-- The set of edges *not* used by a pairing. -/
def pairFree {𝓗 : Set (Set (Fin n))} (t : ℕ)
    (σ : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗}) : Finset (Set (Fin n)) :=
  𝓗.toFinite.toFinset \ pairUsed t σ

lemma natCard_edgeType (𝓗 : Set (Set (Fin n))) :
    Nat.card {e : Set (Fin n) // e ∈ 𝓗} = 𝓗.toFinite.toFinset.card := by
  classical
  rw [Nat.card_eq_fintype_card, ← Fintype.card_coe 𝓗.toFinite.toFinset]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun e => (Set.Finite.mem_toFinset _).symm))

namespace Pairing

variable {𝓗 : Set (Set (Fin n))} {t : ℕ}
variable {σ : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗}}

lemma pairUsed_card (hinj : Function.Injective (fun p : Fin t × Fin 2 => σ p.1 p.2)) :
    (pairUsed t σ).card = 2 * t := by
  have hinj' : Function.Injective (fun p : Fin t × Fin 2 => (σ p.1 p.2 : Set (Fin n))) :=
    fun p q h => hinj (Subtype.ext h)
  rw [pairUsed, Finset.card_image_of_injective _ hinj', Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  ring

lemma pairUsed_sub : pairUsed t σ ⊆ 𝓗.toFinite.toFinset := by
  intro e he
  rw [pairUsed, Finset.mem_image] at he
  obtain ⟨p, -, rfl⟩ := he
  exact (Set.Finite.mem_toFinset _).2 (σ p.1 p.2).2

lemma pairFree_card (hinj : Function.Injective (fun p : Fin t × Fin 2 => σ p.1 p.2)) :
    (pairFree t σ).card = 𝓗.toFinite.toFinset.card - 2 * t := by
  rw [pairFree, Finset.card_sdiff_of_subset (pairUsed_sub (σ := σ)), pairUsed_card hinj]

/-- The class of an edge under a pairing: either one of the `t` pairs or a singleton. -/
def classOf (t : ℕ) (σ : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗}) :
    {e : Set (Fin n) // e ∈ 𝓗} → (Fin t ⊕ {e : Set (Fin n) // e ∈ pairFree t σ}) :=
  fun e => if h : ∃ i : Fin t, (σ i 0 = e ∨ σ i 1 = e) then Sum.inl (Classical.choose h)
    else Sum.inr ⟨e.1, by
      have heM : e.1 ∈ 𝓗.toFinite.toFinset := (Set.Finite.mem_toFinset _).2 e.2
      refine Finset.mem_sdiff.mpr ⟨heM, fun hmem => ?_⟩
      rw [pairUsed, Finset.mem_image] at hmem
      obtain ⟨p, -, hp⟩ := hmem
      obtain ⟨i, b⟩ := p
      fin_cases b
      · exact h ⟨i, Or.inl (Subtype.ext hp)⟩
      · exact h ⟨i, Or.inr (Subtype.ext hp)⟩⟩

lemma classOf_inl (hsq : ∀ (i j : Fin t) (b b' : Fin 2), σ i b = σ j b' → i = j ∧ b = b')
    (e : {e : Set (Fin n) // e ∈ 𝓗}) (i : Fin t) :
    classOf t σ e = Sum.inl i ↔ (σ i 0 = e ∨ σ i 1 = e) := by
  constructor
  · intro hci
    by_cases h : ∃ j : Fin t, (σ j 0 = e ∨ σ j 1 = e)
    · have hch : Classical.choose h = i := by
        have := hci
        rw [classOf, dif_pos h] at this
        exact Sum.inl.inj this
      rw [← hch]
      exact Classical.choose_spec h
    · rw [classOf, dif_neg h] at hci
      exact absurd hci (by simp)
  · intro h
    have hex : ∃ j : Fin t, (σ j 0 = e ∨ σ j 1 = e) := ⟨i, h⟩
    rw [classOf, dif_pos hex]
    congr 1
    rcases Classical.choose_spec hex with hh | hh <;> rcases h with h' | h'
    · exact (hsq _ _ _ _ (hh.trans h'.symm)).1
    · exact (hsq _ _ _ _ (hh.trans h'.symm)).1
    · exact (hsq _ _ _ _ (hh.trans h'.symm)).1
    · exact (hsq _ _ _ _ (hh.trans h'.symm)).1

lemma classOf_inr (e : {e : Set (Fin n) // e ∈ 𝓗})
    (u : {e : Set (Fin n) // e ∈ pairFree t σ}) :
    classOf t σ e = Sum.inr u ↔ e.1 = u.1 := by
  constructor
  · intro hci
    by_cases h : ∃ j : Fin t, (σ j 0 = e ∨ σ j 1 = e)
    · rw [classOf, dif_pos h] at hci
      exact absurd hci (by simp)
    · rw [classOf, dif_neg h] at hci
      exact congrArg Subtype.val (Sum.inr.inj hci)
  · intro hu
    have hne : ¬ ∃ j : Fin t, (σ j 0 = e ∨ σ j 1 = e) := by
      rintro ⟨j, hj | hj⟩
      · have : u.1 ∈ pairUsed t σ := by
          rw [pairUsed, Finset.mem_image]
          exact ⟨(j, 0), Finset.mem_univ _, by rw [hj]; exact hu⟩
        exact (Finset.mem_sdiff.mp u.2).2 this
      · have : u.1 ∈ pairUsed t σ := by
          rw [pairUsed, Finset.mem_image]
          exact ⟨(j, 1), Finset.mem_univ _, by rw [hj]; exact hu⟩
        exact (Finset.mem_sdiff.mp u.2).2 this
    rw [classOf, dif_neg hne]
    congr 1
    exact Subtype.ext hu

end Pairing

/-- **Colouring from a disjoint pairing.**  If the edges of `𝓗` can be paired up so
that paired edges are disjoint, with `t` pairs, and there are at most `n + t` edges
in total, then `𝓗` has a proper edge-colouring with `n` colours in which every colour
is used at most twice. -/
theorem colour_of_pairing {𝓗 : Set (Set (Fin n))} (t : ℕ)
    (σ : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗})
    (hinj : Function.Injective (fun p : Fin t × Fin 2 => σ p.1 p.2))
    (hdisj : ∀ i : Fin t, Disjoint ((σ i 0 : Set (Fin n))) ((σ i 1 : Set (Fin n))))
    (hcard : Nat.card {e : Set (Fin n) // e ∈ 𝓗} ≤ n + t) :
    ∃ φ : {e : Set (Fin n) // e ∈ 𝓗} → Fin n,
      (∀ e f : {e : Set (Fin n) // e ∈ 𝓗}, e ≠ f →
        (((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty → φ e ≠ φ f)) ∧
      (∀ c : Fin n, Nat.card {e : {e : Set (Fin n) // e ∈ 𝓗} // φ e = c} ≤ 2) := by
  classical
  have hsq : ∀ (i j : Fin t) (b b' : Fin 2), σ i b = σ j b' → i = j ∧ b = b' := by
    intro i j b b' h
    have h2 : (⟨i, b⟩ : Fin t × Fin 2) = ⟨j, b'⟩ := hinj (by simpa using h)
    exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
  have hMcard : 𝓗.toFinite.toFinset.card = Nat.card {e : Set (Fin n) // e ∈ 𝓗} :=
    (natCard_edgeType 𝓗).symm
  have hle : Fintype.card (Fin t ⊕ {e : Set (Fin n) // e ∈ pairFree t σ}) ≤ n := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe (pairFree t σ),
      Pairing.pairFree_card hinj, hMcard]
    have h2t : 2 * t ≤ Nat.card {e : Set (Fin n) // e ∈ 𝓗} := by
      rw [← Pairing.pairUsed_card (σ := σ) hinj, ← hMcard]
      exact Finset.card_le_card Pairing.pairUsed_sub
    omega
  obtain ⟨ψ, hψinj⟩ : ∃ ψ : (Fin t ⊕ {e : Set (Fin n) // e ∈ pairFree t σ}) → Fin n,
      Function.Injective ψ :=
    ⟨fun c => Fin.castLE hle (Fintype.equivFin _ c),
      (Fin.castLE_injective hle).comp (Fintype.equivFin _).injective⟩
  refine ⟨fun e => ψ (Pairing.classOf t σ e), ?_, ?_⟩
  · intro e f hne hmeet hφ
    have hcls : Pairing.classOf t σ e = Pairing.classOf t σ f := hψinj hφ
    rcases hce : Pairing.classOf t σ e with i | u
    · have h1 : σ i 0 = e ∨ σ i 1 = e := (Pairing.classOf_inl hsq e i).1 hce
      have h2 : σ i 0 = f ∨ σ i 1 = f := (Pairing.classOf_inl hsq f i).1 (hcls ▸ hce)
      obtain ⟨x, hx⟩ := hmeet
      rw [Set.mem_inter_iff] at hx
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact hne (h1.symm.trans h2)
      · exfalso
        have hxe : x ∈ (σ i 0 : Set (Fin n)) := by rw [h1]; exact hx.1
        have hxf : x ∈ (σ i 1 : Set (Fin n)) := by rw [h2]; exact hx.2
        exact (Set.disjoint_left.mp (hdisj i)) hxe hxf
      · exfalso
        have hxf : x ∈ (σ i 0 : Set (Fin n)) := by rw [h2]; exact hx.2
        have hxe : x ∈ (σ i 1 : Set (Fin n)) := by rw [h1]; exact hx.1
        exact (Set.disjoint_left.mp (hdisj i)) hxf hxe
      · exact hne (h1.symm.trans h2)
    · have h1 : e.1 = u.1 := (Pairing.classOf_inr e u).1 hce
      have h2 : f.1 = u.1 := (Pairing.classOf_inr f u).1 (hcls.symm.trans hce)
      exact hne (Subtype.ext (h1.trans h2.symm))
  · intro c
    have hfib : Nat.card {e : {e : Set (Fin n) // e ∈ 𝓗} // ψ (Pairing.classOf t σ e) = c}
        = ((Finset.univ : Finset {e : Set (Fin n) // e ∈ 𝓗}).filter
            (fun e => ψ (Pairing.classOf t σ e) = c)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hfib]
    by_cases hc : ∃ cc : (Fin t ⊕ {e : Set (Fin n) // e ∈ pairFree t σ}), ψ cc = c
    · obtain ⟨cc, hcc⟩ := hc
      have hcls_fib : ((Finset.univ : Finset {e : Set (Fin n) // e ∈ 𝓗}).filter
          (fun e => Pairing.classOf t σ e = cc)).card ≤ 2 := by
        rcases cc with i | u
        · have hset : (Finset.univ.filter (fun e : {e : Set (Fin n) // e ∈ 𝓗} =>
              Pairing.classOf t σ e = Sum.inl i)) = {σ i 0, σ i 1} := by
            ext e
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton, Pairing.classOf_inl hsq]
            tauto
          rw [hset]
          exact Finset.card_le_two
        · have hu : u.1 ∈ 𝓗 := (Set.Finite.mem_toFinset _).1 (Finset.mem_sdiff.mp u.2).1
          have hset : (Finset.univ.filter (fun e : {e : Set (Fin n) // e ∈ 𝓗} =>
              Pairing.classOf t σ e = Sum.inr u)) = {⟨u.1, hu⟩} := by
            ext e
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
              Pairing.classOf_inr]
            constructor
            · intro h; exact Subtype.ext h
            · intro h; rw [h]
          rw [hset]
          simp
      calc ((Finset.univ : Finset {e : Set (Fin n) // e ∈ 𝓗}).filter
              (fun e => ψ (Pairing.classOf t σ e) = c)).card
          ≤ ((Finset.univ : Finset {e : Set (Fin n) // e ∈ 𝓗}).filter
              (fun e => Pairing.classOf t σ e = cc)).card := by
            apply Finset.card_le_card
            intro e he
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
            exact hψinj (by rw [he, hcc])
        _ ≤ 2 := hcls_fib
    · push Not at hc
      have hzero : ((Finset.univ : Finset {e : Set (Fin n) // e ∈ 𝓗}).filter
            (fun e => ψ (Pairing.classOf t σ e) = c)).card = 0 := by
        apply Finset.card_eq_zero.mpr
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro he
        exact hc (Pairing.classOf t σ e) he
      omega
/-- Arithmetic helper: `(k-1)^2 + (k-1) + 1 = k^2 - k + 1`. -/
lemma sq_pred (k : ℕ) (hk : 1 ≤ k) : (k - 1) * (k - 1) + (k - 1) + 1 = k * k - k + 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 : 1 + j - 1 = j := by omega
  rw [h1]
  have h2 : (1 + j) * (1 + j) = j * j + 2 * j + 1 := by ring
  rw [h2]
  omega

/-- There is `k` with `k^2 - k + 2 ≤ n ≤ k^2 + k + 1`, and `k ≈ √n`. -/
lemma exists_k_bounds {n : ℕ} (hn : 1000000 ≤ n) :
    ∃ k : ℕ, 4 ≤ k ∧ n ≤ k * k + k + 1 ∧ k * k - k + 2 ≤ n ∧
      (k : ℝ) ≤ Real.sqrt (n : ℝ) + 1 ∧ Real.sqrt (n : ℝ) - 1 ≤ (k : ℝ) := by
  have hex : ∃ k : ℕ, n ≤ k * k + k + 1 := ⟨n, by nlinarith⟩
  set k := Nat.find hex with hkdef
  have hspec : n ≤ k * k + k + 1 := Nat.find_spec hex
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · have := hspec; rw [h] at this; simp at this; omega
    · exact h
  have hlow : k * k - k + 2 ≤ n := by
    have hmin := Nat.find_min hex (m := k - 1) (by omega)
    have hp : (k - 1) * (k - 1) + (k - 1) + 1 = k * k - k + 1 := sq_pred k hk1
    rw [hp] at hmin
    omega
  have hk4 : 4 ≤ k := by
    by_contra h
    have h3 : k ≤ 3 := by omega
    have hb : k * k + k + 1 ≤ 3 * 3 + 3 + 1 := by nlinarith
    omega
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hnupper : (k : ℝ) ≤ Real.sqrt (n : ℝ) + 1 := by
    have hsq : ((k : ℝ) - 1) ^ 2 ≤ (n : ℝ) := by
      have hnat : (k - 1) * (k - 1) ≤ n := by
        have hpk : (k - 1) * (k - 1) ≤ k * k - k + 2 := by nlinarith [sq_pred k hk1]
        omega
      have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast [Nat.cast_sub hk1] at hcast
      nlinarith [hcast]
    have h2 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (by linarith : (0:ℝ) ≤ (k:ℝ) - 1)] at h2
    linarith
  have hnlower : Real.sqrt (n : ℝ) - 1 ≤ (k : ℝ) := by
    have hsq : (n : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
      have hnat : n ≤ (k + 1) * (k + 1) := by nlinarith [hspec]
      have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at hcast
      nlinarith [hcast]
    have h2 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (by linarith : (0:ℝ) ≤ (k:ℝ) + 1)] at h2
    linarith
  exact ⟨k, hk4, hspec, hlow, hnupper, hnlower⟩

/-- `(1-2δ)(n-1) ≤ s(s-1)` where `s = (1-δ)√n`, under `δ^2 √n ≥ 1`. -/
lemma small_pair_bound {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1 / 2)
    (hnd : 1 ≤ δ ^ 2 * Real.sqrt (n : ℝ)) :
    (1 - 2 * δ) * ((n : ℝ) - 1) ≤
      ((1 - δ) * Real.sqrt (n : ℝ)) * (((1 - δ) * Real.sqrt (n : ℝ)) - 1) := by
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
    rw [← pow_two, Real.sq_sqrt (by positivity)]
  have hnn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have h1 : Real.sqrt (n : ℝ) ≤ δ ^ 2 * (n : ℝ) := by nlinarith [hnd, hnn, hsq]
  nlinarith [h1, hnn, hsq, hδ, hδle]

/-- `(1 - 3/√n)(n-1) ≤ k(k-1)`. -/
lemma mid_pair_bound {n k : ℕ} (hn : 1000000 ≤ n) (hk1 : n ≤ k * k + k + 1)
    (hk2 : k * k - k + 2 ≤ n) (hk4 : 4 ≤ k) :
    (1 - 3 / Real.sqrt (n : ℝ)) * ((n : ℝ) - 1) ≤ (k : ℝ) * ((k : ℝ) - 1) := by
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
    rw [← pow_two, Real.sq_sqrt (by positivity)]
  have hnn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hr4 : 4 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by norm_num : (0:ℝ) ≤ 4) (by positivity : (0:ℝ) ≤ (n:ℝ))]
    norm_num
    linarith
  have hrpos : 0 < Real.sqrt (n : ℝ) := by linarith
  have hk4R : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
  have hkub : (k : ℝ) ≤ Real.sqrt (n : ℝ) + 1 := by
    have hsq2 : ((k : ℝ) - 1) ^ 2 ≤ (n : ℝ) := by
      have hnat : (k - 1) * (k - 1) ≤ n := by
        have hpk : (k - 1) * (k - 1) ≤ k * k - k + 2 := by
          have := sq_pred k (by omega : 1 ≤ k)
          nlinarith [this]
        omega
      have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast [Nat.cast_sub (by omega : 1 ≤ k)] at hcast
      nlinarith [hcast]
    have h2 := Real.sqrt_le_sqrt hsq2
    rw [Real.sqrt_sq (by linarith : (0:ℝ) ≤ (k:ℝ) - 1)] at h2
    linarith
  have hgoal_eq : (1 - 3 / Real.sqrt (n : ℝ)) * ((n : ℝ) - 1)
      = ((Real.sqrt (n : ℝ) - 3) * ((n : ℝ) - 1)) / Real.sqrt (n : ℝ) := by
    field_simp
  rw [hgoal_eq, div_le_iff₀ hrpos]
  have hk' : (n : ℝ) - 2 * Real.sqrt (n : ℝ) - 3 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
    have h : (n : ℝ) ≤ (k : ℝ) * (k : ℝ) + (k : ℝ) + 1 := by exact_mod_cast hk1
    nlinarith [h]
  have hkey : (Real.sqrt (n : ℝ) - 3) * ((n : ℝ) - 1)
      ≤ ((n : ℝ) - 2 * Real.sqrt (n : ℝ) - 3) * Real.sqrt (n : ℝ) := by
    nlinarith [hsq, hnn, hr4]
  nlinarith [hk', hkey, hnn]

/-- `n - 1 ≤ (k+1)k`. -/
lemma big_pair_bound {n k : ℕ} (hk1 : n ≤ k * k + k + 1) :
    (n : ℝ) - 1 ≤ ((k : ℝ) + 1) * (k : ℝ) := by
  have h : (n : ℝ) ≤ (k : ℝ) * (k : ℝ) + (k : ℝ) + 1 := by exact_mod_cast hk1
  nlinarith [h]

lemma k_large {n k : ℕ} (hn : 1000000 ≤ n) (hk1 : n ≤ k * k + k + 1) : 1000 ≤ k := by
  by_contra h
  have h1 : k ≤ 999 := by omega
  have h2 : k * k + k + 1 ≤ 999 * 999 + 999 + 1 := by nlinarith
  omega

lemma sqrt_ge_1000 {n : ℕ} (hn : 1000000 ≤ n) : (1000:ℝ) ≤ Real.sqrt (n:ℝ) := by
  rw [Real.le_sqrt (by norm_num : (0:ℝ) ≤ 1000) (by positivity : (0:ℝ) ≤ (n:ℝ))]
  norm_num
  linarith

lemma k_bounds {n k : ℕ} (hk1 : n ≤ k*k+k+1) (hk2 : k*k-k+2 ≤ n) (hk4 : 4 ≤ k) :
    (k:ℝ) ≤ Real.sqrt (n:ℝ) + 1 ∧ Real.sqrt (n:ℝ) - 1 ≤ (k:ℝ) := by
  constructor
  · have hsq2 : ((k:ℝ) - 1)^2 ≤ (n:ℝ) := by
      have hp : (k - 1) * (k - 1) ≤ k * k - k + 2 := by
        have := sq_pred k (by omega : 1 ≤ k); nlinarith [this]
      have hnat : (k - 1) * (k - 1) ≤ n := by omega
      have hc := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast [Nat.cast_sub (by omega : 1 ≤ k)] at hc
      nlinarith [hc]
    have hk4R : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk4
    have h2 := Real.sqrt_le_sqrt hsq2
    rw [Real.sqrt_sq (by linarith : (0:ℝ) ≤ (k:ℝ) - 1)] at h2
    linarith
  · have hnat : n ≤ (k + 1) * (k + 1) := by nlinarith [hk1]
    have hc := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at hc
    have h2 := Real.sqrt_le_sqrt hc
    rw [← pow_two] at h2
    rw [Real.sqrt_sq (by linarith : (0:ℝ) ≤ (k:ℝ) + 1)] at h2
    linarith

lemma arith3 {n k : ℕ} (hk2 : k*k-k+2 ≤ n) (hk4 : 4 ≤ k) :
    ((n:ℝ) - (2*(k:ℝ) - 1)) / ((k:ℝ) - 1) ≤ (n:ℝ) - 2 - ((k:ℝ)-1)^2 := by
  have hk4R : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk4
  have hk1R : 0 < (k:ℝ) - 1 := by linarith
  rw [div_le_iff₀ hk1R]
  have hnat : k*k - k + 2 ≤ n := hk2
  have hc : ((k*k - k : ℕ) : ℝ) + 2 ≤ (n:ℝ) := by exact_mod_cast hnat
  have hsplit : ((k*k - k : ℕ) : ℝ) = (k:ℝ)*((k:ℝ)-1) := by
    rw [Nat.cast_sub (by nlinarith : k ≤ k*k)]
    push_cast
    ring
  rw [hsplit] at hc
  have h2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
  nlinarith [hc, h2]

/-- Cast of the pair-counting function. -/
lemma cast_pairFun (e : Set (Fin n)) (h : 1 ≤ e.ncard) :
    ((e.ncard * (e.ncard - 1) : ℕ) : ℝ) = (e.ncard : ℝ) * ((e.ncard : ℝ) - 1) := by
  rw [Nat.cast_mul, Nat.cast_sub h]
  norm_num

lemma pairSum_cast {M : Finset (Set (Fin n))} (h1 : ∀ e ∈ M, 1 ≤ e.ncard) :
    ((∑ e ∈ M, e.ncard * (e.ncard - 1) : ℕ) : ℝ)
      = ∑ e ∈ M, (e.ncard : ℝ) * ((e.ncard : ℝ) - 1) := by
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl (fun e he => cast_pairFun e (h1 e he))

lemma pairSum_lower {M : Finset (Set (Fin n))} {c : ℝ}
    (h : ∀ e ∈ M, c ≤ (e.ncard : ℝ) * ((e.ncard : ℝ) - 1)) :
    (M.card : ℝ) * c ≤ ∑ e ∈ M, (e.ncard : ℝ) * ((e.ncard : ℝ) - 1) := by
  calc (M.card : ℝ) * c = ∑ _e ∈ M, c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ e ∈ M, (e.ncard : ℝ) * ((e.ncard : ℝ) - 1) := Finset.sum_le_sum h

lemma sqrt_ge_thousand {n : ℕ} (hn : 1000000 ≤ n) : (1000 : ℝ) ≤ Real.sqrt (n : ℝ) := by
  rw [Real.le_sqrt (by norm_num : (0:ℝ) ≤ 1000) (by positivity : (0:ℝ) ≤ (n:ℝ))]
  norm_num
  linarith

lemma sqrt_pos_of {n : ℕ} (hn : 1000000 ≤ n) : (0:ℝ) < Real.sqrt (n : ℝ) := by
  have := sqrt_ge_thousand hn; linarith

lemma one_le_minEdge {n : ℕ} {δ : ℝ} {𝓗 : Set (Set (Fin n))} (hn : 1000000 ≤ n)
    (hδ : 0 < δ) (hδle : δ ≤ 1/8)
    (hsize : ∀ e ∈ 𝓗, (1-δ) * Real.sqrt (n:ℝ) ≤ (e.ncard:ℝ)) :
    ∀ e ∈ 𝓗, 1 ≤ e.ncard := by
  intro e he
  have hr := sqrt_ge_thousand hn
  have h := hsize e he
  have h1 : (1:ℝ) ≤ (e.ncard : ℝ) := by nlinarith
  exact_mod_cast h1

/-- **Volume estimate (i).** -/
lemma estimate_i {n k : ℕ} {δ : ℝ} {𝓗 : Set (Set (Fin n))} {t : ℕ}
    (hn : 1000000 ≤ n) (hδ : 0 < δ) (hδle : δ ≤ 1/8)
    (hnd : 1 ≤ δ ^ 2 * Real.sqrt (n:ℝ)) (hk1 : n ≤ k*k+k+1)
    (hlin : ∀ e₁ ∈ 𝓗, ∀ e₂ ∈ 𝓗, e₁ ≠ e₂ → (e₁∩e₂).Subsingleton)
    (hsize : ∀ e ∈ 𝓗, (1-δ)*Real.sqrt (n:ℝ) ≤ (e.ncard:ℝ))
    (ht : 𝓗.toFinite.toFinset.card = n + t) :
    (t : ℝ) ≤ 2*δ*(((𝓗.toFinite.toFinset).filter (fun e => e.ncard ≤ k)).card : ℝ) := by
  classical
  set M := 𝓗.toFinite.toFinset with hMdef
  have hMmem : ∀ e, e ∈ M ↔ e ∈ 𝓗 := fun e => Set.Finite.mem_toFinset _
  have hone : ∀ e ∈ M, 1 ≤ e.ncard := fun e he => one_le_minEdge hn hδ hδle hsize e ((hMmem e).1 he)
  set A := M.filter (fun e => e.ncard ≤ k) with hAdef
  set B := M.filter (fun e => ¬ e.ncard ≤ k) with hBdef
  have hsum_nat : ∑ e ∈ M, e.ncard * (e.ncard - 1) ≤ n * (n - 1) :=
    sum_edgeSize_mul_le M (fun e he => (hMmem e).1 he) hlin
  have hsum : (∑ e ∈ M, (e.ncard : ℝ) * ((e.ncard : ℝ) - 1)) ≤ (n:ℝ) * ((n:ℝ) - 1) := by
    have hcast : ((n * (n - 1) : ℕ) : ℝ) = (n:ℝ) * ((n:ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [← hcast, ← pairSum_cast (M := M) hone]
    exact_mod_cast hsum_nat
  have hsplit : ∑ e ∈ M, (e.ncard : ℝ) * ((e.ncard : ℝ) - 1)
      = (∑ e ∈ A, (e.ncard : ℝ) * ((e.ncard : ℝ) - 1))
        + (∑ e ∈ B, (e.ncard : ℝ) * ((e.ncard : ℝ) - 1)) := by
    rw [hAdef, hBdef, ← Finset.sum_filter_add_sum_filter_not M (fun e => e.ncard ≤ k)
      (fun e => (e.ncard : ℝ) * ((e.ncard : ℝ) - 1))]
  have hAle : (A.card : ℝ) * ((1 - 2*δ) * ((n:ℝ) - 1))
      ≤ ∑ e ∈ A, (e.ncard : ℝ) * ((e.ncard : ℝ) - 1) :=
    pairSum_lower (M := A) (c := (1 - 2*δ) * ((n:ℝ) - 1))
      (fun e he => by
      have heM : e ∈ M := Finset.mem_of_mem_filter e he
      have hek : e.ncard ≤ k := (Finset.mem_filter.mp he).2
      have hs : (1-δ) * Real.sqrt (n:ℝ) ≤ (e.ncard : ℝ) := hsize e ((hMmem e).1 heM)
      have hb := small_pair_bound (n := n) hδ (by linarith : δ ≤ 1 / 2) hnd
      have hmono : ((1-δ) * Real.sqrt (n:ℝ)) * (((1-δ) * Real.sqrt (n:ℝ)) - 1)
          ≤ (e.ncard : ℝ) * ((e.ncard : ℝ) - 1) := by
        have hs1 : 0 ≤ (e.ncard : ℝ) - (1-δ) * Real.sqrt (n:ℝ) := by linarith
        have hs2 : 0 ≤ (e.ncard : ℝ) + (1-δ) * Real.sqrt (n:ℝ) - 1 := by
          have := sqrt_ge_thousand hn; nlinarith
        have := mul_nonneg hs1 hs2
        nlinarith [this]
      linarith)
  have hBle : (B.card : ℝ) * ((n:ℝ) - 1)
      ≤ ∑ e ∈ B, (e.ncard : ℝ) * ((e.ncard : ℝ) - 1) :=
    pairSum_lower (M := B) (c := (n:ℝ) - 1)
      (fun e he => by
      have heM : e ∈ M := Finset.mem_of_mem_filter e he
      have hek : ¬ e.ncard ≤ k := (Finset.mem_filter.mp he).2
      have hk' : k + 1 ≤ e.ncard := by omega
      have hbig := big_pair_bound hk1
      have : ((k:ℝ) + 1) * (k:ℝ) ≤ (e.ncard : ℝ) * ((e.ncard : ℝ) - 1) := by
        have : ((k:ℝ) + 1) ≤ (e.ncard : ℝ) := by exact_mod_cast hk'
        nlinarith [this]
      linarith [hbig])
  have hcardAB : (A.card : ℝ) + (B.card : ℝ) = ((n:ℝ) + t) := by
    have h1 : A.card + B.card = M.card := by
      rw [hAdef, hBdef]
      exact Finset.card_filter_add_card_filter_not (s := M) (p := fun e => e.ncard ≤ k)
    have h2 : (A.card : ℝ) + (B.card : ℝ) = (M.card : ℝ) := by exact_mod_cast h1
    rw [h2, ht]
    push_cast
    ring
  have hmain : (A.card : ℝ) * ((1 - 2*δ) * ((n:ℝ) - 1)) + (B.card : ℝ) * ((n:ℝ) - 1)
      ≤ (n:ℝ) * ((n:ℝ) - 1) := by
    rw [hsplit] at hsum
    linarith [hsum, hAle, hBle]
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by
    have : (1000000:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hfac : (A.card : ℝ) * ((1 - 2*δ) * ((n:ℝ) - 1)) + (B.card : ℝ) * ((n:ℝ) - 1)
      = ((A.card : ℝ) * (1 - 2*δ) + (B.card : ℝ)) * ((n:ℝ) - 1) := by ring
  rw [hfac] at hmain
  have hfin : (A.card : ℝ) * (1 - 2*δ) + (B.card : ℝ) ≤ (n:ℝ) :=
    le_of_mul_le_mul_right hmain hn1
  linarith [hfin, hcardAB]

/-- **Volume estimate (ii).** -/
lemma estimate_ii {n k : ℕ} {δ : ℝ} {𝓗 : Set (Set (Fin n))} {t : ℕ}
    (hn : 1000000 ≤ n) (hδ : 0 < δ) (hδle : δ ≤ 1/8)
    (hnd : 1 ≤ δ ^ 2 * Real.sqrt (n:ℝ)) (hk1 : n ≤ k*k+k+1) (hk2 : k*k-k+2 ≤ n) (hk4 : 4 ≤ k)
    (hlin : ∀ e₁ ∈ 𝓗, ∀ e₂ ∈ 𝓗, e₁ ≠ e₂ → (e₁∩e₂).Subsingleton)
    (hsize : ∀ e ∈ 𝓗, (1-δ)*Real.sqrt (n:ℝ) ≤ (e.ncard:ℝ))
    (ht : 𝓗.toFinite.toFinset.card = n + t) :
    (t : ℝ) ≤ 2*δ*(((𝓗.toFinite.toFinset).filter (fun e => e.ncard ≤ k-1)).card : ℝ)
      + 3*(((𝓗.toFinite.toFinset).filter (fun e => e.ncard = k)).card : ℝ) / Real.sqrt (n:ℝ) := by
  classical
  set M := 𝓗.toFinite.toFinset with hMdef
  have hMmem : ∀ e, e ∈ M ↔ e ∈ 𝓗 := fun e => Set.Finite.mem_toFinset _
  have hone : ∀ e ∈ M, 1 ≤ e.ncard := fun e he => one_le_minEdge hn hδ hδle hsize e ((hMmem e).1 he)
  have hrpos := sqrt_pos_of hn
  set C := M.filter (fun e => e.ncard ≤ k - 1) with hCdef
  set D := M.filter (fun e => e.ncard = k) with hDdef
  set B := M.filter (fun e => ¬ e.ncard ≤ k) with hBdef
  have hCmem : ∀ x, x ∈ C ↔ x ∈ M ∧ x.ncard ≤ k - 1 := by
    intro x; simp only [hCdef, Finset.mem_filter]
  have hDmem : ∀ x, x ∈ D ↔ x ∈ M ∧ x.ncard = k := by
    intro x; simp only [hDdef, Finset.mem_filter]
  have hBmem : ∀ x, x ∈ B ↔ x ∈ M ∧ ¬ x.ncard ≤ k := by
    intro x; simp only [hBdef, Finset.mem_filter]
  set fR : Set (Fin n) → ℝ := fun e => (e.ncard : ℝ) * ((e.ncard : ℝ) - 1) with hfRdef
  have hsum_nat : ∑ e ∈ M, e.ncard * (e.ncard - 1) ≤ n * (n - 1) :=
    sum_edgeSize_mul_le M (fun e he => (hMmem e).1 he) hlin
  have hsum : (∑ e ∈ M, fR e) ≤ (n:ℝ) * ((n:ℝ) - 1) := by
    have hcast1 : ((n * (n - 1) : ℕ) : ℝ) = (n:ℝ) * ((n:ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
    have hcast2 : ((∑ e ∈ M, e.ncard * (e.ncard - 1) : ℕ) : ℝ) = ∑ e ∈ M, fR e := by
      rw [pairSum_cast (M := M) hone]
    rw [← hcast1, ← hcast2]
    exact_mod_cast hsum_nat
  -- split M into (C ∪ D) and B
  have hsplitB : ∑ e ∈ M, fR e
      = (∑ e ∈ M.filter (fun e => e.ncard ≤ k), fR e) + (∑ e ∈ B, fR e) := by
    rw [← Finset.sum_filter_add_sum_filter_not M (fun e => e.ncard ≤ k) fR]
  have hA1_eq : M.filter (fun e => e.ncard ≤ k) = C ∪ D := by
    ext e
    simp only [hCmem e, hDmem e, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hM, hk⟩
      by_cases h : e.ncard ≤ k - 1
      · exact Or.inl ⟨hM, h⟩
      · exact Or.inr ⟨hM, by omega⟩
    · rintro (⟨hM, h⟩ | ⟨hM, h⟩)
      · exact ⟨hM, by omega⟩
      · exact ⟨hM, by omega⟩
  have hCDdisj : Disjoint C D := by
    rw [Finset.disjoint_left]
    intro e heC heD
    have h1 := (hCmem e).1 heC
    have h2 := (hDmem e).1 heD
    omega
  have hsplitA1 : ∑ e ∈ M.filter (fun e => e.ncard ≤ k), fR e
      = (∑ e ∈ C, fR e) + (∑ e ∈ D, fR e) := by
    rw [hA1_eq, Finset.sum_union hCDdisj]
  have hCsum : (C.card : ℝ) * ((1 - 2*δ) * ((n:ℝ) - 1)) ≤ ∑ e ∈ C, fR e :=
    pairSum_lower (M := C) (c := (1 - 2*δ) * ((n:ℝ) - 1)) (fun x hx => by
      obtain ⟨hxM, hxk⟩ := (hCmem x).1 hx
      have hs : (1-δ) * Real.sqrt (n:ℝ) ≤ (x.ncard : ℝ) := hsize x ((hMmem x).1 hxM)
      have hb := small_pair_bound (n := n) hδ (by linarith : δ ≤ 1 / 2) hnd
      have hmono : ((1-δ) * Real.sqrt (n:ℝ)) * (((1-δ) * Real.sqrt (n:ℝ)) - 1) ≤ fR x := by
        have hs1 : 0 ≤ (x.ncard : ℝ) - (1-δ) * Real.sqrt (n:ℝ) := by linarith
        have hs2 : 0 ≤ (x.ncard : ℝ) + (1-δ) * Real.sqrt (n:ℝ) - 1 := by
          have := sqrt_ge_thousand hn; nlinarith
        have := mul_nonneg hs1 hs2
        rw [hfRdef]; nlinarith [this]
      linarith)
  have hDsum : (D.card : ℝ) * ((1 - 3 / Real.sqrt (n:ℝ)) * ((n:ℝ) - 1)) ≤ ∑ e ∈ D, fR e :=
    pairSum_lower (M := D) (c := (1 - 3 / Real.sqrt (n:ℝ)) * ((n:ℝ) - 1)) (fun x hx => by
      obtain ⟨hxM, hxk⟩ := (hDmem x).1 hx
      have hb := mid_pair_bound hn hk1 hk2 hk4
      have hfk : fR x = (k:ℝ) * ((k:ℝ) - 1) := by
        simp only [hfRdef]
        rw [hxk]
      linarith [hfk])
  have hBsum : (B.card : ℝ) * ((n:ℝ) - 1) ≤ ∑ e ∈ B, fR e :=
    pairSum_lower (M := B) (c := (n:ℝ) - 1) (fun x hx => by
      obtain ⟨hxM, hxk⟩ := (hBmem x).1 hx
      have hk' : k + 1 ≤ x.ncard := by omega
      have hbig := big_pair_bound hk1
      have h2 : ((k:ℝ) + 1) ≤ (x.ncard : ℝ) := by exact_mod_cast hk'
      have : ((k:ℝ) + 1) * (k:ℝ) ≤ fR x := by rw [hfRdef]; nlinarith
      linarith [hbig])
  have hmain : (C.card : ℝ) * ((1 - 2*δ) * ((n:ℝ) - 1))
      + (D.card : ℝ) * ((1 - 3 / Real.sqrt (n:ℝ)) * ((n:ℝ) - 1))
      + (B.card : ℝ) * ((n:ℝ) - 1) ≤ (n:ℝ) * ((n:ℝ) - 1) := by
    rw [hsplitB, hsplitA1] at hsum
    linarith [hsum, hCsum, hDsum, hBsum]
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by
    have : (1000000:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hfac : (C.card : ℝ) * ((1 - 2*δ) * ((n:ℝ) - 1))
      + (D.card : ℝ) * ((1 - 3 / Real.sqrt (n:ℝ)) * ((n:ℝ) - 1))
      + (B.card : ℝ) * ((n:ℝ) - 1)
      = ((C.card : ℝ) * (1 - 2*δ) + (D.card : ℝ) * (1 - 3 / Real.sqrt (n:ℝ))
          + (B.card : ℝ)) * ((n:ℝ) - 1) := by ring
  rw [hfac] at hmain
  have hfin : (C.card : ℝ) * (1 - 2*δ) + (D.card : ℝ) * (1 - 3 / Real.sqrt (n:ℝ))
      + (B.card : ℝ) ≤ (n:ℝ) := le_of_mul_le_mul_right hmain hn1
  have hcard : (C.card : ℝ) + (D.card : ℝ) + (B.card : ℝ) = (n:ℝ) + t := by
    have h1 : C.card + D.card + B.card = M.card := by
      have h2 : C.card + D.card = (M.filter (fun e => e.ncard ≤ k)).card := by
        rw [hA1_eq, Finset.card_union_of_disjoint hCDdisj]
      have h3 : (M.filter (fun e => e.ncard ≤ k)).card + B.card = M.card := by
        rw [hBdef]
        exact Finset.card_filter_add_card_filter_not (s := M) (p := fun e => e.ncard ≤ k)
      omega
    have h2 : (C.card : ℝ) + (D.card : ℝ) + (B.card : ℝ) = (M.card : ℝ) := by exact_mod_cast h1
    rw [h2, ht]; push_cast; ring
  have hmul : (t : ℝ) * Real.sqrt (n:ℝ)
      ≤ 2*δ*(C.card : ℝ)*Real.sqrt (n:ℝ) + 3*(D.card : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hfin (le_of_lt hrpos)
    have h2 : ((C.card : ℝ) * (1 - 2*δ) + (D.card : ℝ) * (1 - 3 / Real.sqrt (n:ℝ)) + (B.card : ℝ)) * Real.sqrt (n:ℝ)
        = ((C.card : ℝ) + (D.card : ℝ) + (B.card : ℝ)) * Real.sqrt (n:ℝ)
          - 2*δ*(C.card : ℝ)*Real.sqrt (n:ℝ) - 3*(D.card : ℝ) := by
      field_simp
      ring
    rw [h2] at h1
    nlinarith [h1, hcard]
  have heq : (2*δ*(C.card : ℝ)*Real.sqrt (n:ℝ) + 3*(D.card : ℝ)) / Real.sqrt (n:ℝ)
      = 2*δ*(C.card : ℝ) + 3*(D.card : ℝ) / Real.sqrt (n:ℝ) := by
    field_simp
  rw [← heq, le_div_iff₀ hrpos]
  exact hmul

/-- Filter-cardinality bridge between the edge set as a finset of sets and as a subtype. -/
lemma card_filter_eq {n : ℕ} (𝓗 : Set (Set (Fin n))) (p : Set (Fin n) → Prop) [DecidablePred p]
    [Fintype {e : Set (Fin n) // e ∈ 𝓗}] :
    (𝓗.toFinite.toFinset.filter p).card
      = (Finset.univ.filter (fun e : {e : Set (Fin n) // e ∈ 𝓗} => p e.1)).card := by
  classical
  rw [← Fintype.card_coe (𝓗.toFinite.toFinset.filter p)]
  rw [show Fintype.card ↥(𝓗.toFinite.toFinset.filter p)
      = Fintype.card {e : {e : Set (Fin n) // e ∈ 𝓗} // p e.1} from
    Fintype.card_congr
      { toFun := fun x => ⟨⟨x.1, (Set.Finite.mem_toFinset _).1 (Finset.mem_filter.mp x.2).1⟩,
            (Finset.mem_filter.mp x.2).2⟩
        invFun := fun y => ⟨y.1.1, Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).2 y.1.2, y.2⟩⟩
        left_inv := by intro x; rfl
        right_inv := by intro y; rfl }]
  rw [Fintype.card_subtype]

/-- Cardinality of a subtype of edges, as the cardinality of the corresponding filter. -/
lemma natCard_subtype_eq {n : ℕ} {𝓗 : Set (Set (Fin n))} (p : Set (Fin n) → Prop)
    [DecidablePred p] [Fintype {e : Set (Fin n) // e ∈ 𝓗}] :
    Nat.card {e : {e : Set (Fin n) // e ∈ 𝓗} // p e.1}
      = (Finset.univ.filter (fun e : {e : Set (Fin n) // e ∈ 𝓗} => p e.1)).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Extracting a smaller pairing from a larger one. -/
lemma pairing_restrict {n : ℕ} {𝓗 : Set (Set (Fin n))} {t t₀ : ℕ} (h : t ≤ t₀)
    (σ₀ : Fin t₀ → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗})
    (hinj : Function.Injective (fun p : Fin t₀ × Fin 2 => σ₀ p.1 p.2))
    (hdisj : ∀ i : Fin t₀, Disjoint ((σ₀ i 0).1 : Set (Fin n)) ((σ₀ i 1).1)) :
    ∃ σ : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗},
      Function.Injective (fun p : Fin t × Fin 2 => σ p.1 p.2) ∧
      (∀ i : Fin t, Disjoint ((σ i 0).1 : Set (Fin n)) ((σ i 1).1)) := by
  refine ⟨fun i b => σ₀ (Fin.castLE h i) b, ?_, ?_⟩
  · rintro ⟨i, a⟩ ⟨j, b⟩ hab
    simp only [Prod.mk.injEq]
    have h2 := hinj (a₁ := (⟨Fin.castLE h i, a⟩ : Fin t₀ × Fin 2))
      (a₂ := (⟨Fin.castLE h j, b⟩ : Fin t₀ × Fin 2)) (by simpa using hab)
    simp only [Prod.mk.injEq] at h2
    exact ⟨Fin.castLE_inj.mp h2.1, h2.2⟩
  · intro i
    exact hdisj (Fin.castLE h i)

theorem commonNbrs_le {n k : ℕ} (𝓗 : Set (Set (Fin n))) {δ : ℝ} {e f : Set (Fin n)}
    (hk1 : n ≤ k * k + k + 1) (hk2 : k * k - k + 2 ≤ n) (hk4 : 4 ≤ k)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 10000) (hn : 1000000 ≤ n)
    (hslack : 1 ≤ δ * (k - 1))
    (hlin : ∀ e₁ ∈ 𝓗, ∀ e₂ ∈ 𝓗, e₁ ≠ e₂ → (e₁ ∩ e₂).Subsingleton)
    (hsize : ∀ g ∈ 𝓗, (1 - δ) * Real.sqrt (n : ℝ) ≤ (g.ncard : ℝ))
    (he : e ∈ 𝓗) (hf : f ∈ 𝓗) (hne : e ≠ f) (hmeet : (e ∩ f).Nonempty)
    (hele : e.ncard ≤ k) (hfle : f.ncard ≤ k)
    (hcase : e.ncard ≤ k - 1 ∨ f.ncard ≤ k - 1 ∨
      ∃ w ∈ e ∩ f, (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} //
          (g : Set (Fin n)).ncard ≤ k - 1 ∧ w ∈ (g : Set (Fin n))} : ℝ) ≤ 1 / (3 * δ)) :
    (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
      (g : Set (Fin n)) ∩ e ≠ ∅ ∧ (g : Set (Fin n)) ∩ f ≠ ∅} : ℝ) ≤ (n : ℝ) - 2 := by
  classical
  have hk2' : 2 ≤ k := by omega
  have hn1 : 1 ≤ n := by omega
  have hδ1 : δ < 1 := by linarith
  obtain ⟨w, hw0⟩ := hmeet
  rw [Set.mem_inter_iff] at hw0
  obtain ⟨hwe, hwf⟩ := hw0
  have hinter : ∀ x ∈ e ∩ f, x = w := fun x hx => hlin e he f hf hne hx ⟨hwe, hwf⟩
  have hwmem : w ∈ e.toFinite.toFinset := (Set.Finite.mem_toFinset _).2 hwe
  have hwfmem : w ∈ f.toFinite.toFinset := (Set.Finite.mem_toFinset _).2 hwf
  -- the family U
  let U : Finset {g : Set (Fin n) // g ∈ 𝓗} := Finset.univ.filter (fun g =>
    (g : Set (Fin n)) ≠ e ∧ (g : Set (Fin n)) ≠ f ∧
    ((g : Set (Fin n)) ∩ e).Nonempty ∧ ((g : Set (Fin n)) ∩ f).Nonempty)
  have hUmem : ∀ g, g ∈ U ↔ ((g : Set (Fin n)) ≠ e ∧ (g : Set (Fin n)) ≠ f ∧
      ((g : Set (Fin n)) ∩ e).Nonempty ∧ ((g : Set (Fin n)) ∩ f).Nonempty) := by
    intro g; simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
  let S1 : Finset {g : Set (Fin n) // g ∈ 𝓗} := U.filter (fun g => w ∈ (g : Set (Fin n)))
  let S2 : Finset {g : Set (Fin n) // g ∈ 𝓗} := U.filter (fun g => w ∉ (g : Set (Fin n)))
  have hUcard : U.card = S1.card + S2.card := by
    simp only [S1, S2]
    exact (Finset.card_filter_add_card_filter_not (s := U)
      (p := fun g : {g : Set (Fin n) // g ∈ 𝓗} => w ∈ (g : Set (Fin n)))).symm
  let W : Finset {g : Set (Fin n) // g ∈ 𝓗} := Finset.univ.filter (fun g : {g : Set (Fin n) // g ∈ 𝓗} =>
    w ∈ (g : Set (Fin n)) ∧ (g : Set (Fin n)) ≠ e ∧ (g : Set (Fin n)) ≠ f)
  have hWmem' : ∀ g, g ∈ W ↔ (w ∈ (g : Set (Fin n)) ∧ (g : Set (Fin n)) ≠ e ∧ (g : Set (Fin n)) ≠ f) := by
    intro g; simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
  have hWsub : W ⊆ (Finset.univ.filter (fun g : {g : Set (Fin n) // g ∈ 𝓗} =>
      w ∈ (g : Set (Fin n)))) := by
    intro g hg
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hWmem' g).1 hg |>.1⟩
  have hWpd : (↑W : Set {g : Set (Fin n) // g ∈ 𝓗}).PairwiseDisjoint
      (fun g => (g : Set (Fin n)).toFinite.toFinset.erase w) := by
    intro g hg h hh hne'
    change Disjoint ((g : Set (Fin n)).toFinite.toFinset.erase w)
      ((h : Set (Fin n)).toFinite.toFinset.erase w)
    rw [Finset.disjoint_left]
    intro x hxg hxh
    have hxg' : x ∈ (g : Set (Fin n)) :=
      (Set.Finite.mem_toFinset (Set.toFinite (g : Set (Fin n)))).1 (Finset.mem_of_mem_erase hxg)
    have hxh' : x ∈ (h : Set (Fin n)) :=
      (Set.Finite.mem_toFinset (Set.toFinite (h : Set (Fin n)))).1 (Finset.mem_of_mem_erase hxh)
    have hxw : x ≠ w := Finset.ne_of_mem_erase hxg
    have hgw : w ∈ (g : Set (Fin n)) := (hWmem' g).1 hg |>.1
    have hhw : w ∈ (h : Set (Fin n)) := (hWmem' h).1 hh |>.1
    have hgh : (g : Set (Fin n)) ≠ (h : Set (Fin n)) := fun hh' => hne' (Subtype.ext hh')
    exact hxw (hlin _ g.2 _ h.2 hgh ⟨hxg', hxh'⟩ ⟨hgw, hhw⟩)
  have hWsum : ∑ g ∈ W, ((g : Set (Fin n)).toFinite.toFinset.erase w).card
      = (W.disjiUnion (fun g => (g : Set (Fin n)).toFinite.toFinset.erase w) hWpd).card :=
    (Finset.card_disjiUnion W _ hWpd).symm
  have hWsum_eq : ∑ g ∈ W, ((g : Set (Fin n)).ncard - 1)
      = ∑ g ∈ W, ((g : Set (Fin n)).toFinite.toFinset.erase w).card := by
    apply Finset.sum_congr rfl
    intro g hg
    rw [Finset.card_erase_of_mem, ← Set.ncard_eq_toFinset_card (g : Set (Fin n)) (Set.toFinite _)]
    exact (Set.Finite.mem_toFinset (Set.toFinite (g : Set (Fin n)))).2 ((hWmem' g).1 hg |>.1)
  -- S1 bound
  have hS1W : S1.card ≤ W.card := by
    apply Finset.card_le_card
    intro g hg
    simp only [S1, Finset.mem_filter] at hg
    obtain ⟨hU, hwg⟩ := hg
    obtain ⟨h1, h2, -, -⟩ := (hUmem g).1 hU
    exact (hWmem' g).2 ⟨hwg, h1, h2⟩
  have hspider : ∑ g ∈ (Finset.univ.filter (fun g : {g : Set (Fin n) // g ∈ 𝓗} =>
      w ∈ (g : Set (Fin n)))), ((g : Set (Fin n)).ncard - 1) ≤ n - 1 := by
    set Wf : Finset {g : Set (Fin n) // g ∈ 𝓗} :=
      Finset.univ.filter (fun g : {g : Set (Fin n) // g ∈ 𝓗} => w ∈ (g : Set (Fin n))) with hWf
    have hWfmem : ∀ g, g ∈ Wf ↔ w ∈ (g : Set (Fin n)) := by
      intro g; simp only [hWf, Finset.mem_filter, Finset.mem_univ, true_and]
    have hpd : (↑Wf : Set {g : Set (Fin n) // g ∈ 𝓗}).PairwiseDisjoint
        (fun g => (g : Set (Fin n)).toFinite.toFinset.erase w) := by
      intro g hg h hh hne'
      change Disjoint ((g : Set (Fin n)).toFinite.toFinset.erase w)
        ((h : Set (Fin n)).toFinite.toFinset.erase w)
      rw [Finset.disjoint_left]
      intro x hxg hxh
      have hxg' : x ∈ (g : Set (Fin n)) :=
        (Set.Finite.mem_toFinset (Set.toFinite (g : Set (Fin n)))).1 (Finset.mem_of_mem_erase hxg)
      have hxh' : x ∈ (h : Set (Fin n)) :=
        (Set.Finite.mem_toFinset (Set.toFinite (h : Set (Fin n)))).1 (Finset.mem_of_mem_erase hxh)
      have hxw : x ≠ w := Finset.ne_of_mem_erase hxg
      have hgw : w ∈ (g : Set (Fin n)) := (hWfmem g).1 hg
      have hhw : w ∈ (h : Set (Fin n)) := (hWfmem h).1 hh
      have hgh : (g : Set (Fin n)) ≠ (h : Set (Fin n)) := fun hh' => hne' (Subtype.ext hh')
      exact hxw (hlin _ g.2 _ h.2 hgh ⟨hxg', hxh'⟩ ⟨hgw, hhw⟩)
    calc ∑ g ∈ Wf, ((g : Set (Fin n)).ncard - 1)
        = ∑ g ∈ Wf, ((g : Set (Fin n)).toFinite.toFinset.erase w).card := by
          apply Finset.sum_congr rfl
          intro g hg
          rw [Finset.card_erase_of_mem, ← Set.ncard_eq_toFinset_card (g : Set (Fin n)) (Set.toFinite _)]
          exact (Set.Finite.mem_toFinset (Set.toFinite (g : Set (Fin n)))).2 ((hWfmem g).1 hg)
      _ = (Wf.disjiUnion (fun g => (g : Set (Fin n)).toFinite.toFinset.erase w) hpd).card :=
          (Finset.card_disjiUnion Wf _ hpd).symm
      _ ≤ ((Finset.univ : Finset (Fin n)).erase w).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_disjiUnion] at hx
          obtain ⟨g, hg, hxg⟩ := hx
          rw [Finset.mem_erase]
          exact ⟨Finset.ne_of_mem_erase hxg, Finset.mem_univ _⟩
      _ = n - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ, Fintype.card_fin]
  have hWsum_le : ∑ g ∈ W, ((g : Set (Fin n)).ncard - 1) ≤ n - 1 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hWsub (fun _ _ _ => Nat.zero_le _)) hspider
  -- S2 bound
  have hS2_bound : S2.card ≤ (e.ncard - 1) * (f.ncard - 1) := by
    have hS2U : ∀ g, g ∈ S2 → g ∈ U := fun g hg => Finset.mem_of_mem_filter g hg
    have hSw : ∀ g, g ∈ S2 → w ∉ (g : Set (Fin n)) := fun g hg => (Finset.mem_filter.mp hg).2
    let X : {g : {g : Set (Fin n) // g ∈ 𝓗} // g ∈ S2} → Fin n := fun g =>
      Classical.choose ((hUmem g.1).1 (hS2U g.1 g.2)).2.2.1
    let Y : {g : {g : Set (Fin n) // g ∈ 𝓗} // g ∈ S2} → Fin n := fun g =>
      Classical.choose ((hUmem g.1).1 (hS2U g.1 g.2)).2.2.2
    have hX : ∀ g, X g ∈ ((g.1 : Set (Fin n)) ∩ e) := fun g => Classical.choose_spec _
    have hY : ∀ g, Y g ∈ ((g.1 : Set (Fin n)) ∩ f) := fun g => Classical.choose_spec _
    have hXw : ∀ g, X g ≠ w := fun g hw => hSw g.1 g.2 (by rw [← hw]; exact (hX g).1)
    have hYw : ∀ g, Y g ≠ w := fun g hw => hSw g.1 g.2 (by rw [← hw]; exact (hY g).1)
    have hmaps : Set.MapsTo (fun g : {g : {g : Set (Fin n) // g ∈ 𝓗} // g ∈ S2} => (X g, Y g))
        ↑(Finset.univ : Finset {g : {g : Set (Fin n) // g ∈ 𝓗} // g ∈ S2})
        ↑((e.toFinite.toFinset.erase w) ×ˢ (f.toFinite.toFinset.erase w)) := by
      intro g _
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_erase]
      exact ⟨⟨hXw g, (Set.Finite.mem_toFinset _).2 (hX g).2⟩,
             ⟨hYw g, (Set.Finite.mem_toFinset _).2 (hY g).2⟩⟩
    have hinj : Set.InjOn (fun g : {g : {g : Set (Fin n) // g ∈ 𝓗} // g ∈ S2} => (X g, Y g))
        ↑(Finset.univ : Finset {g : {g : Set (Fin n) // g ∈ 𝓗} // g ∈ S2}) := by
      intro g _ h _ hg
      have hxy : X g = X h ∧ Y g = Y h := by simpa using hg
      obtain ⟨hx, hy⟩ := hxy
      have hxg : X g ∈ (g.1 : Set (Fin n)) := (hX g).1
      have hxg' : X g ∈ e := (hX g).2
      have hyg : Y g ∈ (g.1 : Set (Fin n)) := (hY g).1
      have hyf : Y g ∈ f := (hY g).2
      have hxy' : X g ≠ Y g := by
        intro hxy'
        have hmem : X g ∈ e ∩ f := by
          rw [Set.mem_inter_iff]
          exact ⟨hxg', by rw [hxy']; exact hyf⟩
        exact hXw g (hinter (X g) hmem)
      have hgh : (g.1 : Set (Fin n)) = (h.1 : Set (Fin n)) := by
        by_contra hne''
        have hsub := hlin _ g.1.2 _ h.1.2 hne''
        have hmem1 : X g ∈ (g.1 : Set (Fin n)) ∩ (h.1 : Set (Fin n)) :=
          ⟨hxg, by rw [hx]; exact (hX h).1⟩
        have hmem2 : Y g ∈ (g.1 : Set (Fin n)) ∩ (h.1 : Set (Fin n)) :=
          ⟨hyg, by rw [hy]; exact (hY h).1⟩
        exact hxy' (hsub hmem1 hmem2)
      exact Subtype.ext (Subtype.ext hgh)
    have hcard := Finset.card_le_card_of_injOn (fun g : {g : {g : Set (Fin n) // g ∈ 𝓗} // g ∈ S2} =>
        (X g, Y g)) hmaps hinj
    rw [Finset.card_univ, Fintype.card_coe, Finset.card_product] at hcard
    rw [Finset.card_erase_of_mem hwmem, Finset.card_erase_of_mem hwfmem] at hcard
    rw [← Set.ncard_eq_toFinset_card e (Set.toFinite e),
      ← Set.ncard_eq_toFinset_card f (Set.toFinite f)] at hcard
    exact hcard
  -- conversion of the goal
  have hUnat : Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // (g : Set (Fin n)) ≠ e ∧ (g : Set (Fin n)) ≠ f ∧
      ((g : Set (Fin n)) ∩ e).Nonempty ∧ ((g : Set (Fin n)) ∩ f).Nonempty} = U.card := by
    rw [natCard_subtype_eq (𝓗 := 𝓗) (p := fun g => (g : Set (Fin n)) ≠ e ∧ (g : Set (Fin n)) ≠ f ∧
      ((g : Set (Fin n)) ∩ e).Nonempty ∧ ((g : Set (Fin n)) ∩ f).Nonempty)]
  have hconv : Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
      (g : Set (Fin n)) ∩ e ≠ ∅ ∧ (g : Set (Fin n)) ∩ f ≠ ∅} =
      Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // (g : Set (Fin n)) ≠ e ∧ (g : Set (Fin n)) ≠ f ∧
      ((g : Set (Fin n)) ∩ e).Nonempty ∧ ((g : Set (Fin n)) ∩ f).Nonempty} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun g => ?_)
    simp only [Set.nonempty_iff_ne_empty]
  rw [hconv, hUnat]
  have hr2 : (1000:ℝ) ≤ Real.sqrt (n:ℝ) := sqrt_ge_1000 hn
  have hone : ∀ g : Set (Fin n), g ∈ 𝓗 → 1 ≤ g.ncard := fun g hg => by
    have h := hsize g hg
    have h2 : (1:ℝ) ≤ (1-δ)*Real.sqrt (n:ℝ) := by nlinarith [hr2, hδsmall]
    have h3 : (1:ℝ) ≤ (g.ncard : ℝ) := by linarith
    exact_mod_cast h3
  have hspos : 0 < (1-δ) * Real.sqrt (n:ℝ) - 1 := by nlinarith [hr2, hδsmall]
  have harith12 : ((n:ℝ) - 1) / ((1-δ)*Real.sqrt (n:ℝ) - 1) + ((k:ℝ)-2)*((k:ℝ)-1) ≤ (n:ℝ) - 2 := by
    have h1 := nearfull_useful_caseA (k := k) (n := n) (δ := δ) (k_large hn hk1) hδ hδsmall hk2 hk1
    linarith [h1]
  have hWbound_common : (W.card : ℝ) ≤ ((n:ℝ) - 1) / ((1-δ)*Real.sqrt (n:ℝ) - 1) := by
    have hterm : ∀ g ∈ W, (1 - δ) * Real.sqrt (n:ℝ) - 1 ≤ ((g : Set (Fin n)).ncard : ℝ) - 1 :=
      fun g hg => by have := hsize _ g.2; linarith
    have h1' : (W.card : ℝ) * ((1 - δ) * Real.sqrt (n:ℝ) - 1)
        ≤ ∑ g ∈ W, (((g : Set (Fin n)).ncard : ℝ) - 1) := by
      calc (W.card : ℝ) * ((1 - δ) * Real.sqrt (n:ℝ) - 1)
          = ∑ _g ∈ W, ((1 - δ) * Real.sqrt (n:ℝ) - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ g ∈ W, (((g : Set (Fin n)).ncard : ℝ) - 1) := Finset.sum_le_sum hterm
    have h2' : ∑ g ∈ W, (((g : Set (Fin n)).ncard : ℝ) - 1) ≤ (n:ℝ) - 1 := by
      have h2 := (Nat.cast_le (α := ℝ)).mpr hWsum_le
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sum, Nat.cast_one] at h2
      calc ∑ g ∈ W, (((g : Set (Fin n)).ncard : ℝ) - 1)
          = ∑ g ∈ W, ((((g : Set (Fin n)).ncard - 1 : ℕ)) : ℝ) := by
            apply Finset.sum_congr rfl
            intro g hg
            have h1g : 1 ≤ (g : Set (Fin n)).ncard := by
              have hh := hsize _ g.2
              have h3 : (1:ℝ) ≤ (g : Set (Fin n)).ncard := by nlinarith [hr2, hδsmall]
              exact_mod_cast h3
            rw [Nat.cast_sub h1g, Nat.cast_one]
        _ ≤ (n:ℝ) - 1 := h2
    rw [le_div_iff₀ hspos]
    linarith [h1', h2']
  by_cases h1 : e.ncard ≤ k - 1
  · -- case (i): |e| ≤ k-1
    have hS2b : (S2.card : ℝ) ≤ ((k:ℝ)-2)*((k:ℝ)-1) := by
      have hcast := (Nat.cast_le (α := ℝ)).mpr hS2_bound
      rw [Nat.cast_mul, Nat.cast_sub (hone e he),
        Nat.cast_sub (hone f hf), Nat.cast_one] at hcast
      have h1 : (e.ncard:ℝ) - 1 ≤ (k:ℝ) - 2 := by
        have h : e.ncard + 1 ≤ k := by omega
        have h2 : ((e.ncard:ℝ) + 1) ≤ (k:ℝ) := by exact_mod_cast h
        linarith
      have h2 : (f.ncard:ℝ) - 1 ≤ (k:ℝ) - 1 := by
        have h2 : (f.ncard:ℝ) ≤ (k:ℝ) := by exact_mod_cast hfle
        linarith
      have h3 : (0:ℝ) ≤ (f.ncard:ℝ) - 1 := by
        have h := hone f hf
        have h2 : (1:ℝ) ≤ (f.ncard:ℝ) := by exact_mod_cast h
        linarith
      have h4 : (0:ℝ) ≤ (k:ℝ) - 2 := by
        have hk4R : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk4
        linarith
      have hmul := mul_le_mul h1 h2 h3 h4
      linarith [hcast, hmul]
    have hUc : (U.card : ℝ) = (S1.card : ℝ) + (S2.card : ℝ) := by rw [hUcard]; push_cast; ring
    have hS1R : (S1.card : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hS1W
    linarith [hUc, hS1R, hS2b, hWbound_common, harith12]
  · by_cases h1' : f.ncard ≤ k - 1
    · -- case (ii): |f| ≤ k-1
      have hS2b : (S2.card : ℝ) ≤ ((k:ℝ)-2)*((k:ℝ)-1) := by
        have hcast := (Nat.cast_le (α := ℝ)).mpr hS2_bound
        rw [Nat.cast_mul, Nat.cast_sub (hone e he),
          Nat.cast_sub (hone f hf), Nat.cast_one] at hcast
        have h1 : (e.ncard:ℝ) - 1 ≤ (k:ℝ) - 1 := by
          have h2 : (e.ncard:ℝ) ≤ (k:ℝ) := by exact_mod_cast hele
          linarith
        have h2 : (f.ncard:ℝ) - 1 ≤ (k:ℝ) - 2 := by
          have h : f.ncard + 1 ≤ k := by omega
          have h2 : ((f.ncard:ℝ) + 1) ≤ (k:ℝ) := by exact_mod_cast h
          linarith
        have h3 : (0:ℝ) ≤ (f.ncard:ℝ) - 1 := by
          have h := hone f hf
          have h2 : (1:ℝ) ≤ (f.ncard:ℝ) := by exact_mod_cast h
          linarith
        have h4 : (0:ℝ) ≤ (k:ℝ) - 1 := by
          have hk4R : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk4
          linarith
        have hmul := mul_le_mul h1 h2 h3 h4
        linarith [hcast, hmul]
      have hUc : (U.card : ℝ) = (S1.card : ℝ) + (S2.card : ℝ) := by rw [hUcard]; push_cast; ring
      have hS1R : (S1.card : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hS1W
      linarith [hUc, hS1R, hS2b, hWbound_common, harith12]
    · have hek : e.ncard = k := by omega
      have hfk : f.ncard = k := by omega
      rcases hcase with h2 | h2 | ⟨w', hw', hm'⟩
      · exact absurd h2 h1
      · exact absurd h2 h1'
      · -- case (iii)
        have hw'eq : w' = w := hinter w' hw'
        rw [hw'eq] at hm'
        have hWsum_ref : ∑ g ∈ W, ((g : Set (Fin n)).ncard - 1) ≤ n - (2*k - 1) := by
          have hunion : ((Finset.univ : Finset (Fin n)) \ (e.toFinite.toFinset ∪ f.toFinite.toFinset)).card = n - (2*k - 1) := by
            have hinter_card : (e.toFinite.toFinset ∩ f.toFinite.toFinset).card = 1 := by
              have hset : e.toFinite.toFinset ∩ f.toFinite.toFinset = {w} := by
                ext x
                simp only [Finset.mem_inter, Finset.mem_singleton, Set.Finite.mem_toFinset]
                constructor
                · rintro ⟨h1, h2⟩; exact hinter x ⟨h1, h2⟩
                · rintro rfl; exact ⟨hwe, hwf⟩
              rw [hset, Finset.card_singleton]
            have hcard : (e.toFinite.toFinset ∪ f.toFinite.toFinset).card = 2 * k - 1 := by
              have h := Finset.card_union_add_card_inter e.toFinite.toFinset f.toFinite.toFinset
              rw [hinter_card, ← Set.ncard_eq_toFinset_card e (Set.toFinite e),
                ← Set.ncard_eq_toFinset_card f (Set.toFinite f), hek, hfk] at h
              omega
            rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hcard]
          calc ∑ g ∈ W, ((g : Set (Fin n)).ncard - 1)
              = (W.disjiUnion (fun g => (g : Set (Fin n)).toFinite.toFinset.erase w) hWpd).card :=
                hWsum_eq.trans hWsum
            _ ≤ ((Finset.univ : Finset (Fin n)) \ (e.toFinite.toFinset ∪ f.toFinite.toFinset)).card := by
                apply Finset.card_le_card
                intro x hx
                rw [Finset.mem_disjiUnion] at hx
                obtain ⟨g, hg, hxg⟩ := hx
                have hxg' : x ∈ (g : Set (Fin n)) :=
                  (Set.Finite.mem_toFinset (Set.toFinite (g : Set (Fin n)))).1 (Finset.mem_of_mem_erase hxg)
                have hxw : x ≠ w := Finset.ne_of_mem_erase hxg
                have hgw : w ∈ (g : Set (Fin n)) := (hWmem' g).1 hg |>.1
                have hgne1 : (g : Set (Fin n)) ≠ e := (hWmem' g).1 hg |>.2.1
                have hgne2 : (g : Set (Fin n)) ≠ f := (hWmem' g).1 hg |>.2.2
                rw [Finset.mem_sdiff, Finset.mem_union]
                refine ⟨Finset.mem_univ _, ?_⟩
                rintro (hxe | hxf)
                · exact hxw (hlin _ g.2 _ he hgne1 ⟨hxg', (Set.Finite.mem_toFinset _).1 hxe⟩ ⟨hgw, hwe⟩)
                · exact hxw (hlin _ g.2 _ hf hgne2 ⟨hxg', (Set.Finite.mem_toFinset _).1 hxf⟩ ⟨hgw, hwf⟩)
            _ = n - (2*k - 1) := hunion
        set Ws : Finset {g : Set (Fin n) // g ∈ 𝓗} := W.filter (fun g => (g : Set (Fin n)).ncard ≤ k - 1) with hWsdef
        have hWsplit : W.card = Ws.card + (W \ Ws).card := by
          have h := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun g : {g : Set (Fin n) // g ∈ 𝓗} =>
            (g : Set (Fin n)).ncard ≤ k - 1) W)
          rw [← hWsdef] at h
          omega
        have hWs_le : (Ws.card : ℝ) ≤ 1 / (3 * δ) := by
          have hsub : Ws ⊆ (Finset.univ.filter (fun g : {g : Set (Fin n) // g ∈ 𝓗} =>
              (g : Set (Fin n)).ncard ≤ k - 1 ∧ w ∈ (g : Set (Fin n)))) := by
            intro g hg
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hg).2, (hWmem' g).1 (Finset.mem_of_mem_filter g hg) |>.1⟩
          have hcard : Ws.card ≤ Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} //
              (g : Set (Fin n)).ncard ≤ k - 1 ∧ w ∈ (g : Set (Fin n))} := by
            rw [natCard_subtype_eq (𝓗 := 𝓗) (p := fun g => g.ncard ≤ k - 1 ∧ w ∈ g)]
            exact Finset.card_le_card hsub
          have h2 : (Ws.card : ℝ) ≤ (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} //
              (g : Set (Fin n)).ncard ≤ k - 1 ∧ w ∈ (g : Set (Fin n))} : ℝ) := by exact_mod_cast hcard
          linarith [h2, hm']
        have hWbound : (W.card : ℝ) ≤ ((n:ℝ) - (2*(k:ℝ) - 1)) / ((k:ℝ) - 1) + 2/3 := by
          have hk1R : 0 < (k:ℝ) - 1 := by
            have hk4R : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk4
            linarith
          have hbig : ∀ g ∈ W \ Ws, ((k:ℝ) - 1) ≤ ((g : Set (Fin n)).ncard : ℝ) - 1 := by
            intro g hg
            rw [Finset.mem_sdiff] at hg
            have hgW : g ∈ W := hg.1
            have h1 : ¬ ((g : Set (Fin n)).ncard ≤ k - 1) := by
              intro hcon
              exact hg.2 (by rw [hWsdef]; exact Finset.mem_filter.mpr ⟨hgW, hcon⟩)
            have h2 : k ≤ (g : Set (Fin n)).ncard := by omega
            have h3 : (k:ℝ) ≤ ((g : Set (Fin n)).ncard : ℝ) := by exact_mod_cast h2
            linarith
          have hsmall : ∀ g ∈ Ws, (1-δ)*Real.sqrt (n:ℝ) - 1 ≤ ((g : Set (Fin n)).ncard : ℝ) - 1 :=
            fun g hg => by have := hsize _ g.2; linarith
          have h1big : ((W \ Ws).card : ℝ) * ((k:ℝ) - 1)
              ≤ ∑ g ∈ W \ Ws, (((g : Set (Fin n)).ncard : ℝ) - 1) := by
            calc ((W \ Ws).card : ℝ) * ((k:ℝ) - 1) = ∑ _g ∈ W \ Ws, ((k:ℝ) - 1) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ _ := Finset.sum_le_sum hbig
          have h2small : (Ws.card : ℝ) * ((1-δ)*Real.sqrt (n:ℝ) - 1)
              ≤ ∑ g ∈ Ws, (((g : Set (Fin n)).ncard : ℝ) - 1) := by
            calc (Ws.card : ℝ) * ((1-δ)*Real.sqrt (n:ℝ) - 1)
                = ∑ _g ∈ Ws, ((1-δ)*Real.sqrt (n:ℝ) - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ _ := Finset.sum_le_sum hsmall
          have hsplit_sum : ∑ g ∈ W, (((g : Set (Fin n)).ncard : ℝ) - 1)
              = ∑ g ∈ W \ Ws, (((g : Set (Fin n)).ncard : ℝ) - 1)
                + ∑ g ∈ Ws, (((g : Set (Fin n)).ncard : ℝ) - 1) := by
            rw [← Finset.sum_sdiff (Finset.filter_subset (fun g : {g : Set (Fin n) // g ∈ 𝓗} =>
              (g : Set (Fin n)).ncard ≤ k - 1) W)]
          have hsumW_cast : ∑ g ∈ W, (((g : Set (Fin n)).ncard : ℝ) - 1) ≤ (n:ℝ) - (2*(k:ℝ) - 1) := by
            have h2 := (Nat.cast_le (α := ℝ)).mpr hWsum_ref
            have h2k : 2 * k - 1 ≤ n := by
              have h : 2 * k ≤ k * k - k + 2 := by
                have h1 : k * k - k + 2 = (k * k + 2) - k := by
                  have hkk1 : k ≤ k * k := Nat.le_mul_of_pos_right k (by omega)
                  omega
                rw [h1, Nat.le_sub_iff_add_le]
                · nlinarith [hk4]
                · omega
              omega
            have h3 := (Nat.cast_le (α := ℝ)).mpr hWsum_ref
            have h5 : ((2 * k - 1 : ℕ) : ℝ) = 2*(k:ℝ) - 1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ 2*k), Nat.cast_mul, Nat.cast_one]
              ring
            rw [Nat.cast_sub h2k, Nat.cast_sum, h5] at h3
            calc ∑ g ∈ W, (((g : Set (Fin n)).ncard : ℝ) - 1)
                = ∑ g ∈ W, ((((g : Set (Fin n)).ncard - 1 : ℕ)) : ℝ) := by
                  apply Finset.sum_congr rfl
                  intro g hg
                  have h1g : 1 ≤ (g : Set (Fin n)).ncard := hone _ g.2
                  rw [Nat.cast_sub h1g, Nat.cast_one]
              _ ≤ (n:ℝ) - (2*(k:ℝ) - 1) := h3
          have hks : (k:ℝ) - (1-δ)*Real.sqrt (n:ℝ) ≤ 2 * δ * ((k:ℝ) - 1) := by
            have h1 : (1-δ)*Real.sqrt (n:ℝ) ≥ (1-δ) * ((k:ℝ) - 1) := by
              have h2 : (k:ℝ) - 1 ≤ Real.sqrt (n:ℝ) := by
                have hp : (k - 1) * (k - 1) ≤ k * k - k + 2 := by
                  have := sq_pred k (by omega : 1 ≤ k); nlinarith [this]
                have hnat : (k - 1) * (k - 1) ≤ n := by omega
                have hc := (Nat.cast_le (α := ℝ)).mpr hnat
                push_cast [Nat.cast_sub (by omega : 1 ≤ k)] at hc
                have h3 := Real.sqrt_le_sqrt hc
                rw [← pow_two] at h3
                rw [Real.sqrt_sq (by linarith : (0:ℝ) ≤ (k:ℝ) - 1)] at h3
                linarith
              nlinarith [h2, hδsmall]
            nlinarith [hslack, hδ1, h1]
          have hkey : ((k:ℝ) - 1) * (W.card : ℝ)
              ≤ (n:ℝ) - (2*(k:ℝ) - 1) + 2/3 * ((k:ℝ) - 1) := by
            have h1 : ((k:ℝ) - 1) * (W.card : ℝ)
                = ((k:ℝ) - 1) * ((W \ Ws).card : ℝ) + ((k:ℝ) - 1) * (Ws.card : ℝ) := by
              have h1' : (W.card : ℝ) = (Ws.card:ℝ) + ((W \ Ws).card : ℝ) := by
                rw [hWsplit]; push_cast; ring
              rw [h1']; ring
            have h2 : ((k:ℝ) - 1) * ((W \ Ws).card : ℝ) ≤ ∑ g ∈ W \ Ws, (((g : Set (Fin n)).ncard : ℝ) - 1) := by
              linarith [h1big]
            have h4 : (2 * δ * ((k:ℝ) - 1)) * (1/(3*δ)) = 2/3 * ((k:ℝ) - 1) := by
              field_simp
            have h3 : ((k:ℝ) - 1) * (Ws.card : ℝ)
                ≤ ∑ g ∈ Ws, (((g : Set (Fin n)).ncard : ℝ) - 1) + (2 * δ * ((k:ℝ) - 1)) * (1/(3*δ)) := by
              have h6 : ((k:ℝ) - 1) - ((1-δ)*Real.sqrt (n:ℝ) - 1) ≤ 2 * δ * ((k:ℝ) - 1) := by linarith [hks]
              have h7 : (0:ℝ) ≤ (Ws.card : ℝ) := by positivity
              have h8 : ((k:ℝ) - 1) * (Ws.card : ℝ) ≤ ((1-δ)*Real.sqrt (n:ℝ) - 1) * (Ws.card : ℝ)
                  + (2 * δ * ((k:ℝ) - 1)) * (Ws.card : ℝ) := by
                nlinarith [h6, h7]
              have h9 : (2 * δ * ((k:ℝ) - 1)) * (Ws.card : ℝ) ≤ (2 * δ * ((k:ℝ) - 1)) * (1/(3*δ)) := by
                have h10 : 0 ≤ 2 * δ * ((k:ℝ) - 1) := by nlinarith [hδ, hk4]
                exact mul_le_mul_of_nonneg_left hWs_le h10
              linarith [h8, h9, h2small, h4]
            linarith [h1, h2, h3, hsumW_cast, hsplit_sum, h4]
          rw [div_add' _ _ _ (ne_of_gt hk1R)]
          rw [le_div_iff₀ hk1R]
          linarith [hkey]
        have hWle : (W.card : ℝ) ≤ (n:ℝ) - 2 - ((k:ℝ) - 1)^2 := by
          have harith3' := arith3 hk2 hk4
          have hkk : (k-1)^2 ≤ n - 2 := by
            have h2 : (k-1)^2 = (k-1)*(k-1) := by ring
            rw [h2]
            have h1 : (k-1)*(k-1) ≤ k*k - k := by nlinarith [sq_pred k (by omega : 1 ≤ k)]
            omega
          have h3 : ((n - 2 - (k-1)^2 : ℕ) : ℝ) = (n:ℝ) - 2 - ((k:ℝ) - 1)^2 := by
            have h5 : (n - 2 - (k-1)^2) + 2 + (k-1)^2 = n := by omega
            have h6 : ((n - 2 - (k-1)^2 : ℕ) : ℝ) + 2 + (((k-1)^2 : ℕ) : ℝ) = (n:ℝ) := by
              exact_mod_cast h5
            have h7 : (((k-1)^2 : ℕ) : ℝ) = ((k:ℝ) - 1)^2 := by
              rw [Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
            linarith [h6, h7]
          have hnat : W.card ≤ n - 2 - (k-1)^2 := by
            by_contra hcon
            push Not at hcon
            have h1 : ((n - 2 - (k-1)^2 : ℕ) : ℝ) + 1 ≤ (W.card : ℝ) := by
              have h2 := (Nat.cast_le (α := ℝ)).mpr (by omega : n - 2 - (k-1)^2 + 1 ≤ W.card)
              push_cast at h2
              linarith
            rw [h3] at h1
            linarith [hWbound, harith3']
          rw [← h3]
          exact_mod_cast hnat
        have hS2b : (S2.card : ℝ) ≤ ((k:ℝ) - 1)^2 := by
          have hcast := (Nat.cast_le (α := ℝ)).mpr hS2_bound
          rw [hek, hfk] at hcast
          have h1 : (((k - 1) * (k - 1) : ℕ) : ℝ) = ((k:ℝ) - 1)^2 := by
            rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
            ring
          rw [h1] at hcast
          exact hcast
        have hUc : (U.card : ℝ) = (S1.card : ℝ) + (S2.card : ℝ) := by rw [hUcard]; push_cast; ring
        have hS1R : (S1.card : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hS1W
        linarith [hUc, hS1R, hS2b, hWle]

/-- Transfer of the common-neighbour cardinality between the "set" and "subtype" formulations. -/
lemma commonNbr_cast {n : ℕ} (𝓗 : Set (Set (Fin n))) (e f : {e : Set (Fin n) // e ∈ 𝓗}) :
    Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // (g : Set (Fin n)) ≠ (e : Set (Fin n)) ∧
        (g : Set (Fin n)) ≠ (f : Set (Fin n)) ∧
        (g : Set (Fin n)) ∩ (e : Set (Fin n)) ≠ (∅ : Set (Fin n)) ∧
        (g : Set (Fin n)) ∩ (f : Set (Fin n)) ≠ (∅ : Set (Fin n))}
      = Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
        (g : Set (Fin n)) ∩ (e : Set (Fin n)) ≠ (∅ : Set (Fin n)) ∧
        (g : Set (Fin n)) ∩ (f : Set (Fin n)) ≠ (∅ : Set (Fin n))} := by
  classical
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun g => by simp only [Subtype.coe_ne_coe]))

theorem linear_nearfull_colouring :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ 𝓗 : Set (Set (Fin n)),
        (∀ e₁ ∈ 𝓗, ∀ e₂ ∈ 𝓗, e₁ ≠ e₂ → (e₁ ∩ e₂).Subsingleton) →
        (∀ e ∈ 𝓗, (1 - δ) * Real.sqrt (n : ℝ) ≤ (e.ncard : ℝ)) →
        ∃ φ : {e // e ∈ 𝓗} → Fin n,
          (∀ e f : {e // e ∈ 𝓗}, e ≠ f →
            (((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty → φ e ≠ φ f)) ∧
          (∀ c : Fin n, Nat.card {e : {e // e ∈ 𝓗} // φ e = c} ≤ 2) := by
  classical
  refine ⟨1 / 10 ^ 8, by norm_num, ?_⟩
  intro δ hδpos hδle
  refine ⟨max 1000000 (Nat.ceil (((δ)⁻¹) ^ 4)), ?_⟩
  intro n hn 𝓗 hlin hsize
  have hn_big : 1000000 ≤ n := le_trans (le_max_left _ _) hn
  have hn_ceil : Nat.ceil (((δ)⁻¹) ^ 4) ≤ n := le_trans (le_max_right _ _) hn
  have hδ1 : δ ≤ 1 / 8 := by linarith
  have hδ2 : δ ≤ 1 / 10000 := by linarith
  have hδsmall : δ ≤ 1 / 10 ^ 8 := hδle
  have hδne : δ ≠ 0 := ne_of_gt hδpos
  have h4inv : ((δ)⁻¹) ^ 4 ≤ (n : ℝ) := by
    have h1 := Nat.le_ceil (((δ)⁻¹) ^ 4)
    have h2 : ((Nat.ceil (((δ)⁻¹) ^ 4) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ceil
    linarith
  have h4 : (1 : ℝ) ≤ δ ^ 4 * (n : ℝ) := by
    have h1 : δ ^ 4 * ((δ)⁻¹) ^ 4 = 1 := by field_simp
    have h2 : δ ^ 4 * ((δ)⁻¹) ^ 4 ≤ δ ^ 4 * (n : ℝ) :=
      mul_le_mul_of_nonneg_left h4inv (by positivity)
    linarith
  have hnd : (1 : ℝ) ≤ δ ^ 2 * Real.sqrt (n : ℝ) := by
    have hsq : (δ ^ 2 * Real.sqrt (n:ℝ)) ^ 2 = δ ^ 4 * (n:ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    have hx0 : 0 ≤ δ ^ 2 * Real.sqrt (n:ℝ) := by positivity
    have h2 : (1:ℝ) ≤ Real.sqrt ((δ ^ 2 * Real.sqrt (n:ℝ))^2) :=
      (Real.le_sqrt (by norm_num) (by positivity)).mpr (by rw [hsq, one_pow]; exact h4)
    rwa [Real.sqrt_sq hx0] at h2
  set m := Nat.card {e : Set (Fin n) // e ∈ 𝓗} with hmdef
  by_cases hmle : m ≤ n
  · have hmle' : Nat.card {e : Set (Fin n) // e ∈ 𝓗} ≤ n := by
      rw [← hmdef]; exact hmle
    exact colour_of_pairing (𝓗 := 𝓗) (t := 0) (fun i => i.elim0)
      (fun p _ => p.1.elim0) (fun i => i.elim0) (by simpa using hmle')
  · have hmgt : n < m := not_le.mp hmle
    set t := m - n with htdef
    have hmt : m = n + t := by omega
    have hcardE : n + t ≤ Nat.card {e : Set (Fin n) // e ∈ 𝓗} := by omega
    obtain ⟨k, hk4, hk1, hk2, hkupper, hklower⟩ := exists_k_bounds hn_big
    have hslack : 1 ≤ δ * ((k:ℝ) - 1) := by
      have h1 : Real.sqrt (n:ℝ) - 2 ≤ (k:ℝ) - 1 := by linarith [hklower]
      have h3 : 1/δ ≤ δ * Real.sqrt (n:ℝ) := by
        rw [div_le_iff₀ hδpos]; linarith [hnd]
      have h4 : δ * (Real.sqrt (n:ℝ) - 2) ≤ δ * ((k:ℝ) - 1) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hδpos)
      have h6 : (1:ℝ) + 2*δ ≤ 1/δ := by
        rw [le_div_iff₀ hδpos]
        nlinarith [hδle, hδpos]
      linarith [h3, h4, h6]
    let Aall : Finset {e : Set (Fin n) // e ∈ 𝓗} :=
      (Finset.univ : Finset {e : Set (Fin n) // e ∈ 𝓗}).filter (fun e => (e : Set (Fin n)).ncard ≤ k)
    let Aminus : Finset {e : Set (Fin n) // e ∈ 𝓗} :=
      (Finset.univ : Finset {e : Set (Fin n) // e ∈ 𝓗}).filter (fun e => (e : Set (Fin n)).ncard ≤ k - 1)
    let Aplus : Finset {e : Set (Fin n) // e ∈ 𝓗} :=
      (Finset.univ : Finset {e : Set (Fin n) // e ∈ 𝓗}).filter (fun e => (e : Set (Fin n)).ncard = k)
    have hAall_eq : Aall.card = (Finset.univ.filter
        (fun e : {e : Set (Fin n) // e ∈ 𝓗} => (e : Set (Fin n)).ncard ≤ k)).card := rfl
    have hAminus_eq : Aminus.card = (Finset.univ.filter
        (fun e : {e : Set (Fin n) // e ∈ 𝓗} => (e : Set (Fin n)).ncard ≤ k - 1)).card := rfl
    have hAplus_eq : Aplus.card = (Finset.univ.filter
        (fun e : {e : Set (Fin n) // e ∈ 𝓗} => (e : Set (Fin n)).ncard = k)).card := rfl
    have hAall_mem : ∀ e, e ∈ Aall ↔ (e : Set (Fin n)).ncard ≤ k := by
      intro e; simp only [Aall, Finset.mem_filter, Finset.mem_univ, true_and]
    have hAminus_mem : ∀ e, e ∈ Aminus ↔ (e : Set (Fin n)).ncard ≤ k - 1 := by
      intro e; simp only [Aminus, Finset.mem_filter, Finset.mem_univ, true_and]
    have hAplus_mem : ∀ e, e ∈ Aplus ↔ (e : Set (Fin n)).ncard = k := by
      intro e; simp only [Aplus, Finset.mem_filter, Finset.mem_univ, true_and]
    have hMcard' : 𝓗.toFinite.toFinset.card = n + t := by
      rw [← natCard_edgeType 𝓗]; exact hmt
    have hest1 : (t : ℝ) ≤ 2 * δ * (Aall.card : ℝ) := by
      have h := estimate_i (𝓗 := 𝓗) (t := t) (k := k) hn_big hδpos hδ1 hnd hk1 hlin hsize hMcard'
      rwa [card_filter_eq 𝓗 (fun e => e.ncard ≤ k)] at h
    have hest2 : (t : ℝ) ≤ 2 * δ * (Aminus.card : ℝ)
        + 3 * (Aplus.card : ℝ) / Real.sqrt (n:ℝ) := by
      have h := estimate_ii (𝓗 := 𝓗) (t := t) (k := k) hn_big hδpos hδ1 hnd hk1 hk2 hk4 hlin hsize hMcard'
      rwa [card_filter_eq 𝓗 (fun e => e.ncard ≤ k - 1), card_filter_eq 𝓗 (fun e => e.ncard = k)] at h
    have hcrit : ∀ e f : {e : Set (Fin n) // e ∈ 𝓗}, e ≠ f →
        (e : Set (Fin n)).ncard = k → (f : Set (Fin n)).ncard = k →
        ∀ w ∈ (e : Set (Fin n)) ∩ (f : Set (Fin n)),
          (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} //
            (g : Set (Fin n)).ncard ≤ k - 1 ∧ w ∈ (g : Set (Fin n))} : ℝ) < 1 / (4 * δ) →
          (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
            (g : Set (Fin n)) ∩ (e : Set (Fin n)) ≠ (∅ : Set (Fin n)) ∧
            (g : Set (Fin n)) ∩ (f : Set (Fin n)) ≠ (∅ : Set (Fin n))} : ℝ) ≤ (n : ℝ) - 2 := by
      intro e f hne hek hfk w hw hlt
      have hcase : (e : Set (Fin n)).ncard ≤ k - 1 ∨ (f : Set (Fin n)).ncard ≤ k - 1 ∨
          ∃ w' ∈ (e : Set (Fin n)) ∩ (f : Set (Fin n)),
            (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} //
              (g : Set (Fin n)).ncard ≤ k - 1 ∧ w' ∈ (g : Set (Fin n))} : ℝ) ≤ 1 / (3 * δ) := by
        right; right
        refine ⟨w, hw, ?_⟩
        have h1 : (1:ℝ) / (4 * δ) ≤ 1 / (3 * δ) := by
          rw [one_div, one_div]
          exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (by linarith [hδpos])
        linarith
      have h_set := commonNbrs_le 𝓗 hk1 hk2 hk4 hδpos hδ2 hn_big hslack hlin hsize e.2 f.2
        (fun h => hne (Subtype.ext h)) ⟨w, hw⟩ (by rw [hek]) (by rw [hfk]) hcase
      rw [← commonNbr_cast 𝓗 e f]
      exact h_set
    have hexistence : ∃ σ : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗},
        Function.Injective (fun p : Fin t × Fin 2 => σ p.1 p.2) ∧
        (∀ i : Fin t, Disjoint ((σ i 0).1 : Set (Fin n)) ((σ i 1).1)) := by
      by_cases hc1 : Aminus.card ≤ 300
      · have husefulAall : ∀ e ∈ Aall, ∀ f ∈ Aall, e ≠ f →
            (((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty →
            (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
              (g : Set (Fin n)) ∩ (e : Set (Fin n)) ≠ (∅ : Set (Fin n)) ∧
              (g : Set (Fin n)) ∩ (f : Set (Fin n)) ≠ (∅ : Set (Fin n))} : ℝ) ≤ (n : ℝ) - 2) := by
          intro e he f hf hne hmeet
          have hek : (e : Set (Fin n)).ncard ≤ k := (hAall_mem e).1 he
          have hfk : (f : Set (Fin n)).ncard ≤ k := (hAall_mem f).1 hf
          have hcase : (e : Set (Fin n)).ncard ≤ k - 1 ∨ (f : Set (Fin n)).ncard ≤ k - 1 ∨
              ∃ w ∈ (e : Set (Fin n)) ∩ (f : Set (Fin n)),
                (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} //
                  (g : Set (Fin n)).ncard ≤ k - 1 ∧ w ∈ (g : Set (Fin n))} : ℝ) ≤ 1 / (3 * δ) := by
            right; right
            obtain ⟨w, hw⟩ := hmeet
            refine ⟨w, hw, ?_⟩
            have hcount : Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} //
                (g : Set (Fin n)).ncard ≤ k - 1 ∧ w ∈ (g : Set (Fin n))} ≤ Aminus.card := by
              rw [natCard_subtype_eq (𝓗 := 𝓗) (p := fun g => g.ncard ≤ k - 1 ∧ w ∈ g)]
              apply Finset.card_le_card
              intro g hg
              rw [hAminus_mem g]
              exact (Finset.mem_filter.mp hg).2.1
            have h1 : (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} //
                (g : Set (Fin n)).ncard ≤ k - 1 ∧ w ∈ (g : Set (Fin n))} : ℝ) ≤ 300 := by
              have hc := (Nat.cast_le (α := ℝ)).mpr hcount
              have h300 : (Aminus.card : ℝ) ≤ 300 := by exact_mod_cast hc1
              linarith
            have h2 : (300 : ℝ) ≤ 1 / (3 * δ) := by
              rw [le_div_iff₀ (by positivity : (0:ℝ) < 3 * δ)]
              nlinarith [hδ2]
            linarith
          have h_set := commonNbrs_le 𝓗 hk1 hk2 hk4 hδpos hδ2 hn_big hslack hlin hsize e.2 f.2
            (fun h => hne (Subtype.ext h)) hmeet hek hfk hcase
          rw [← commonNbr_cast 𝓗 e f]
          exact h_set
        have h4t : 4 * t ≤ Aall.card := by
          have h1 : ((4 * t : ℕ) : ℝ) ≤ (Aall.card : ℝ) := by
            have h2 : (4 * (t : ℝ)) ≤ (Aall.card : ℝ) := by nlinarith [hest1, hδ1]
            push_cast
            linarith
          exact_mod_cast h1
        exact pairing_of_useful_family_clique 𝓗 t Aall h4t husefulAall hcardE
      · have husefulAminus : ∀ e ∈ Aminus, ∀ f ∈ Aminus, e ≠ f →
            (((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty →
            (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
              (g : Set (Fin n)) ∩ (e : Set (Fin n)) ≠ (∅ : Set (Fin n)) ∧
              (g : Set (Fin n)) ∩ (f : Set (Fin n)) ≠ (∅ : Set (Fin n))} : ℝ) ≤ (n : ℝ) - 2) := by
          intro e he f hf hne hmeet
          have hek : (e : Set (Fin n)).ncard ≤ k := by have := (hAminus_mem e).1 he; omega
          have hfk : (f : Set (Fin n)).ncard ≤ k := by have := (hAminus_mem f).1 hf; omega
          have hcase : (e : Set (Fin n)).ncard ≤ k - 1 ∨ (f : Set (Fin n)).ncard ≤ k - 1 ∨
              ∃ w ∈ (e : Set (Fin n)) ∩ (f : Set (Fin n)),
                (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} //
                  (g : Set (Fin n)).ncard ≤ k - 1 ∧ w ∈ (g : Set (Fin n))} : ℝ) ≤ 1 / (3 * δ) :=
            Or.inl ((hAminus_mem e).1 he)
          have h_set := commonNbrs_le 𝓗 hk1 hk2 hk4 hδpos hδ2 hn_big hslack hlin hsize e.2 f.2
            (fun h => hne (Subtype.ext h)) hmeet hek hfk hcase
          rw [← commonNbr_cast 𝓗 e f]
          exact h_set
        by_cases hc2 : (Aplus.card : ℝ) ≤ Real.sqrt (n:ℝ) * (Aminus.card : ℝ) / 15
        · have h4t : 4 * t ≤ Aminus.card := by
            have hr : 0 < Real.sqrt (n:ℝ) := sqrt_pos_of hn_big
            have h1 : (t : ℝ) * Real.sqrt (n:ℝ) ≤ (Aminus.card : ℝ) * Real.sqrt (n:ℝ) / 4 := by
              have h2 := mul_le_mul_of_nonneg_right hest2 (le_of_lt hr)
              have heq : (2 * δ * (Aminus.card : ℝ) + 3 * (Aplus.card : ℝ) / Real.sqrt (n:ℝ))
                  * Real.sqrt (n:ℝ)
                  = 2 * δ * (Aminus.card : ℝ) * Real.sqrt (n:ℝ) + 3 * (Aplus.card : ℝ) := by
                rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hr)]
              rw [heq] at h2
              nlinarith [h2, hc2, hr, hδ1]
            have h3 := (le_div_iff₀ hr).mpr h1
            have heq2 : ((Aminus.card : ℝ) * Real.sqrt (n:ℝ) / 4) / Real.sqrt (n:ℝ)
                = (Aminus.card : ℝ) / 4 := by
              have h : ((Aminus.card : ℝ) * Real.sqrt (n:ℝ) / 4) / Real.sqrt (n:ℝ)
                  = (Aminus.card : ℝ) * (Real.sqrt (n:ℝ) / Real.sqrt (n:ℝ)) / 4 := by ring
              rw [h, div_self (ne_of_gt hr), mul_one]
            have : (t : ℝ) ≤ (Aminus.card : ℝ) / 4 := by linarith [h3, heq2]
            have h4 : ((4 * t : ℕ) : ℝ) ≤ (Aminus.card : ℝ) := by push_cast; linarith
            exact_mod_cast h4
          exact pairing_of_useful_family_clique 𝓗 t Aminus h4t husefulAminus hcardE
        · have h301 : 301 ≤ Aminus.card := by omega
          have hAminus_le : (Nat.card {e : {e : Set (Fin n) // e ∈ 𝓗} //
              (e : Set (Fin n)).ncard ≤ k - 1} : ℝ) ≤ 15 * (Aplus.card : ℝ) / Real.sqrt n := by
            have hEq : Nat.card {e : {e : Set (Fin n) // e ∈ 𝓗} //
                (e : Set (Fin n)).ncard ≤ k - 1} = Aminus.card := by
              rw [natCard_subtype_eq (𝓗 := 𝓗) (p := fun g => g.ncard ≤ k - 1)]
            rw [hEq]
            have hlt : Real.sqrt (n:ℝ) * (Aminus.card : ℝ) / 15 < (Aplus.card : ℝ) := not_le.mp hc2
            have hr : 0 < Real.sqrt (n:ℝ) := sqrt_pos_of hn_big
            rw [le_div_iff₀ hr]
            nlinarith [hlt, hr]
          have hbigA : 20 * Real.sqrt n < (Aplus.card : ℝ) := by
            have hlt : Real.sqrt (n:ℝ) * (Aminus.card : ℝ) / 15 < (Aplus.card : ℝ) := not_le.mp hc2
            have hr : 0 < Real.sqrt (n:ℝ) := sqrt_pos_of hn_big
            have h300 : (300:ℝ) < (Aminus.card : ℝ) := by
              exact_mod_cast (by omega : (300:ℕ) < Aminus.card)
            nlinarith [hlt, hr, h300]
          have ht_lt : 2 * (t : ℝ) * Real.sqrt n < 8 * (Aplus.card : ℝ) := by
            have hr : 0 < Real.sqrt (n:ℝ) := sqrt_pos_of hn_big
            have hlt : Real.sqrt (n:ℝ) * (Aminus.card : ℝ) / 15 < (Aplus.card : ℝ) := not_le.mp hc2
            have h1 : (t : ℝ) * Real.sqrt n < 4 * (Aplus.card : ℝ) := by
              have h2 := mul_le_mul_of_nonneg_right hest2 (le_of_lt hr)
              have heq : (2 * δ * (Aminus.card : ℝ) + 3 * (Aplus.card : ℝ) / Real.sqrt (n:ℝ))
                  * Real.sqrt (n:ℝ)
                  = 2 * δ * (Aminus.card : ℝ) * Real.sqrt (n:ℝ) + 3 * (Aplus.card : ℝ) := by
                rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hr)]
              rw [heq] at h2
              have h4 : (Aminus.card : ℝ) * Real.sqrt (n:ℝ) < 15 * (Aplus.card : ℝ) := by
                rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 15)] at hlt
                linarith [hlt]
              have h5 : 2 * δ * (15 * (Aplus.card : ℝ)) ≤ (Aplus.card : ℝ) := by
                nlinarith [hδ1, hbigA]
              nlinarith [h2, h4, h5, hδpos]
            nlinarith [h1, hr]
          obtain ⟨t₀, σ₀, hinj₀, hdisj₀, hclique₀⟩ := exists_maximal_disjoint_pairing 𝓗
          by_cases ht₀ : t ≤ t₀
          · exact pairing_restrict ht₀ σ₀ hinj₀ hdisj₀
          · push Not at ht₀
            exact exists_pairing_of_size_k_family 𝓗 Aplus hδpos hδsmall hn_big hk4 hkupper hklower
              hlin (fun e he => (hAplus_mem e).1 he) hAminus_le hbigA ht_lt hcardE σ₀ hinj₀ hdisj₀
              hclique₀ ht₀ hcrit
    obtain ⟨σ, hσinj, hσdisj⟩ := hexistence
    have hcardE2 : Nat.card {e : Set (Fin n) // e ∈ 𝓗} ≤ n + t := by omega
    exact colour_of_pairing t σ hσinj hσdisj hcardE2

end
end Commons.Combinatorics.Hypergraph
