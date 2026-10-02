import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.Defs
import Submission.EFL.ClassicalBounds

/-!
# Kahn's theorem in list form from its restriction to edges of size at least two

`KahnCoreStatement` is Kahn's list-colouring theorem for linear hypergraphs all
of whose edges have size at least two; `KahnListStatement` is the same statement
without that hypothesis.  This file shows that the former implies the latter.

The argument is a two-step greedy construction.  Write `𝓗c` for the
subhypergraph of edges of size at least two ("the core") and `𝓢` for the
remaining edges, which have size `0` or `1`.

* colour the core with `KahnCoreStatement` applied to the restricted lists;
* each edge of `𝓢` is either empty or a singleton `{v}`, and the only earlier
  colours that can obstruct it are those of the at most `Δ(𝓗) ≤ D` core edges
  through `v`; since its list has at least `(1+β)D > D` colours, a free colour
  remains.  (Two distinct edges of `𝓢` are disjoint, so no further obstruction
  arises.)
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture
  (edgeSize hypergraphDegree hypergraphMaxDegree hypergraphDegree_le_maxDegree
   hypergraphMaxDegree_mono verts mem_verts eq_singleton_of_edgeSize_eq_one
   eq_empty_of_edgeSize_eq_zero)

theorem kahnList_of_kahnCore (h : ErdosFaberLovaszConjecture.KahnCoreStatement) :
    ErdosFaberLovaszConjecture.KahnListStatement := by
  classical
  intro β hβ r hr
  obtain ⟨D₀, hD₀, hcore⟩ := h β hβ r hr
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD n 𝓗 hlin hdeg hsize c hc L hL
  -- The core: the edges of size at least two.
  set 𝓗c : ErdosFaberLovaszConjecture.Hypergraph (Fin n) := {e ∈ 𝓗 | 2 ≤ edgeSize e}
    with h𝓗cdef
  have hsub : 𝓗c ⊆ 𝓗 := fun e he => he.1
  have hDpos : 0 < D := lt_of_lt_of_le hD₀ hD
  have hβD : D < (1 + β) * D := by nlinarith
  -- The core satisfies the hypotheses of `KahnCoreStatement`.
  have hlin_c : 𝓗c.IsLinear := hlin.mono hsub
  have hdeg_c : ((hypergraphMaxDegree 𝓗c : ℕ) : ℝ) ≤ D := by
    have hmono : ((hypergraphMaxDegree 𝓗c : ℕ) : ℝ) ≤ ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) := by
      exact_mod_cast hypergraphMaxDegree_mono hsub
    linarith
  have hsize2_c : ∀ e : 𝓗c, 2 ≤ edgeSize (e : Set (Fin n)) := fun e => e.2.2
  have hsize_c : ∀ e : 𝓗c, (edgeSize (e : Set (Fin n)) : ℝ) ≤ (r : ℝ) :=
    fun e => hsize ⟨(e : Set (Fin n)), hsub e.2⟩
  -- The lists restricted to the core.
  let Lc : 𝓗c → Finset (Fin c) := fun e => L ⟨(e : Set (Fin n)), hsub e.2⟩
  have hLc : ∀ e : 𝓗c, (1 + β) * D ≤ ((Lc e).card : ℝ) :=
    fun e => hL ⟨(e : Set (Fin n)), hsub e.2⟩
  obtain ⟨φc, hφc⟩ : ∃ φ : 𝓗c.Coloring (Fin c), ∀ e : 𝓗c, φ.labels e ∈ Lc e :=
    hcore D hD n 𝓗c hlin_c hdeg_c hsize2_c hsize_c c hc Lc hLc
  -- An edge which is not in the core has size at most one.
  have small_of_not_mem : ∀ e : 𝓗, (e : Set (Fin n)) ∉ 𝓗c → edgeSize (e : Set (Fin n)) ≤ 1 := by
    intro e he
    have h2 : ¬ (2 ≤ edgeSize (e : Set (Fin n))) := fun hk => he ⟨e.2, hk⟩
    omega
  -- Every edge of size at most one can be given a colour of its own list which
  -- is not used on any core edge meeting it.
  have key : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ 1 → ∃ a : Fin c, a ∈ L e ∧
      ∀ e' : 𝓗c, (((e' : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty → φc.labels e' ≠ a) := by
    intro e he1
    have hLpos : 0 < (L e).card := by
      have h1 : (0 : ℝ) < (1 + β) * D := mul_pos (by linarith) hDpos
      have h2 : (0 : ℝ) < ((L e).card : ℝ) := lt_of_lt_of_le h1 (hL e)
      exact_mod_cast h2
    by_cases hne : (e : Set (Fin n)).Nonempty
    · obtain ⟨v, hv⟩ := hne
      have he1eq : edgeSize (e : Set (Fin n)) = 1 := by
        have hone : 1 ≤ edgeSize (e : Set (Fin n)) := by
          have hpos : 0 < (verts (e : Set (Fin n))).card :=
            Finset.card_pos.mpr ⟨v, (mem_verts (e : Set (Fin n)) v).mpr hv⟩
          simpa [edgeSize] using hpos
        omega
      have hes : (e : Set (Fin n)) = {v} := eq_singleton_of_edgeSize_eq_one hv he1eq
      -- The colours used on core edges through `v`.
      haveI : Fintype ↥𝓗c := (Set.toFinite 𝓗c).fintype
      set T : Finset (Fin c) :=
        (Finset.univ.filter (fun e' : ↥𝓗c => v ∈ (e' : Set (Fin n)))).image
          (fun e' => φc.labels e') with hTdef
      have hTcard_le : T.card ≤ hypergraphMaxDegree 𝓗 := by
        have h1 : T.card ≤
            (Finset.univ.filter (fun e' : ↥𝓗c => v ∈ (e' : Set (Fin n)))).card :=
          Finset.card_image_le
        have h2 : (Finset.univ.filter (fun e' : ↥𝓗c => v ∈ (e' : Set (Fin n)))).card =
            Fintype.card {e' : ↥𝓗c // v ∈ (e' : Set (Fin n))} :=
          (Fintype.card_subtype _).symm
        have h3 : Nat.card {e' : ↥𝓗c // v ∈ (e' : Set (Fin n))} = hypergraphDegree 𝓗c v := rfl
        have h4 : Fintype.card {e' : ↥𝓗c // v ∈ (e' : Set (Fin n))} =
            Nat.card {e' : ↥𝓗c // v ∈ (e' : Set (Fin n))} := Nat.card_eq_fintype_card.symm
        have h5 : hypergraphDegree 𝓗c v ≤ hypergraphMaxDegree 𝓗c :=
          hypergraphDegree_le_maxDegree 𝓗c v
        have h6 : hypergraphMaxDegree 𝓗c ≤ hypergraphMaxDegree 𝓗 := hypergraphMaxDegree_mono hsub
        omega
      have hTcard : T.card < (L e).card := by
        by_contra hcon
        have h1 : ((L e).card : ℝ) ≤ (T.card : ℝ) := by
          exact_mod_cast Nat.le_of_not_lt hcon
        have h2 : (T.card : ℝ) ≤ ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) := by exact_mod_cast hTcard_le
        nlinarith [hβD, hdeg, hL e]
      obtain ⟨a, haL, haT⟩ : ∃ a ∈ L e, a ∉ T := by
        by_contra hcon
        have hsubT : ∀ a ∈ L e, a ∈ T := by
          intro a ha
          by_contra haT
          exact hcon ⟨a, ha, haT⟩
        have : (L e).card ≤ T.card := Finset.card_le_card hsubT
        omega
      refine ⟨a, haL, ?_⟩
      intro e' hint
      have hv' : v ∈ (e' : Set (Fin n)) := by
        obtain ⟨x, hx⟩ := hint
        have hxv : x = v := by
          have hx2 : x ∈ ({v} : Set (Fin n)) := by rw [← hes]; exact hx.2
          simpa using hx2
        rw [hxv] at hx
        exact hx.1
      intro hcontr
      rw [hTdef] at haT
      exact haT (hcontr ▸ (Finset.mem_image.mpr ⟨e', by simp [hv'], rfl⟩))
    · have he0 : edgeSize (e : Set (Fin n)) = 0 := by
        have hcard : (verts (e : Set (Fin n))).card = 0 := by
          by_contra hc
          obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
          exact hne ⟨w, (mem_verts (e : Set (Fin n)) w).mp hw⟩
        simpa [edgeSize] using hcard
      have hes : (e : Set (Fin n)) = ∅ := eq_empty_of_edgeSize_eq_zero he0
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hLpos
      refine ⟨a, ha, ?_⟩
      intro e' hint
      rw [hes] at hint
      exact absurd hint (by simp)
  -- Assemble the colouring.
  refine ⟨⟨fun e => if h : (e : Set (Fin n)) ∈ 𝓗c then
        φc.labels ⟨(e : Set (Fin n)), h⟩
      else Classical.choose (key e (small_of_not_mem e h)), ?_⟩, ?_⟩
  · intro e₁ e₂ hne hint
    by_cases h₁ : (e₁ : Set (Fin n)) ∈ 𝓗c
    · by_cases h₂ : (e₂ : Set (Fin n)) ∈ 𝓗c
      · rw [dif_pos h₁, dif_pos h₂]
        refine φc.isColoring ⟨(e₁ : Set (Fin n)), h₁⟩ ⟨(e₂ : Set (Fin n)), h₂⟩ ?_ ?_
        · intro heq
          exact hne (Subtype.ext (congrArg (fun x : ↥𝓗c => (x : Set (Fin n))) heq))
        · simpa using hint
      · rw [dif_pos h₁, dif_neg h₂]
        exact (Classical.choose_spec (key e₂ (small_of_not_mem e₂ h₂))).2
          ⟨(e₁ : Set (Fin n)), h₁⟩ (by simpa using hint)
    · by_cases h₂ : (e₂ : Set (Fin n)) ∈ 𝓗c
      · rw [dif_neg h₁, dif_pos h₂]
        intro hcontra
        exact (Classical.choose_spec (key e₁ (small_of_not_mem e₁ h₁))).2
          ⟨(e₂ : Set (Fin n)), h₂⟩ (by rw [Set.inter_comm]; exact hint) hcontra.symm
      · rw [dif_neg h₁, dif_neg h₂]
        exfalso
        obtain ⟨x, hx⟩ := hint
        have hx₁ : x ∈ (e₁ : Set (Fin n)) := hx.1
        have hx₂ : x ∈ (e₂ : Set (Fin n)) := hx.2
        have h1eq : edgeSize (e₁ : Set (Fin n)) = 1 := by
          have hone : 1 ≤ edgeSize (e₁ : Set (Fin n)) := by
            have hpos : 0 < (verts (e₁ : Set (Fin n))).card :=
              Finset.card_pos.mpr ⟨x, (mem_verts (e₁ : Set (Fin n)) x).mpr hx₁⟩
            simpa [edgeSize] using hpos
          have := small_of_not_mem e₁ h₁
          omega
        have h2eq : edgeSize (e₂ : Set (Fin n)) = 1 := by
          have hone : 1 ≤ edgeSize (e₂ : Set (Fin n)) := by
            have hpos : 0 < (verts (e₂ : Set (Fin n))).card :=
              Finset.card_pos.mpr ⟨x, (mem_verts (e₂ : Set (Fin n)) x).mpr hx₂⟩
            simpa [edgeSize] using hpos
          have := small_of_not_mem e₂ h₂
          omega
        have he₁ : (e₁ : Set (Fin n)) = {x} := eq_singleton_of_edgeSize_eq_one hx₁ h1eq
        have he₂ : (e₂ : Set (Fin n)) = {x} := eq_singleton_of_edgeSize_eq_one hx₂ h2eq
        exact hne (Subtype.ext (by rw [he₁, he₂]))
  · intro e
    dsimp only
    by_cases h : (e : Set (Fin n)) ∈ 𝓗c
    · rw [dif_pos h]
      have heq : (⟨(e : Set (Fin n)), hsub h⟩ : ↥𝓗) = e := Subtype.ext rfl
      have hmem : φc.labels ⟨(e : Set (Fin n)), h⟩ ∈ L ⟨(e : Set (Fin n)), hsub h⟩ :=
        hφc ⟨(e : Set (Fin n)), h⟩
      rwa [heq] at hmem
    · rw [dif_neg h]
      exact (Classical.choose_spec (key e (small_of_not_mem e h))).1

end Work.Deep.Kahn
