import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

set_option linter.unusedVariables false

namespace Commons.Combinatorics.SimpleGraph

open Finset

variable {V α : Type*}

/-- Hall's theorem in "min-degree" form: if in a bipartite relation between `s` and `T` every
element of `s` has at least `dA` partners, every element of `T` has at least `dB` partners,
`s.card ≤ T.card` and `s.card ≤ dA + dB`, then there is an injective selection from `s` into `T`
along the relation. -/
lemma hall_min_degree_aux {A B : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset A) (T : Finset B) (Rd : A → B → Prop) [DecidableRel Rd] (dA dB : ℕ)
    (hcard : s.card ≤ T.card)
    (hA : ∀ a ∈ s, dA ≤ (T.filter (Rd a)).card)
    (hB : ∀ b ∈ T, dB ≤ (s.filter (fun a => Rd a b)).card)
    (hsum : s.card ≤ dA + dB) :
    ∃ f : {a // a ∈ s} → B, (∀ a, f a ∈ T ∧ Rd a.1 (f a)) ∧ Function.Injective f := by
  classical
  let t : {a // a ∈ s} → Finset B := fun a => T.filter (fun b => Rd a.1 b)
  have hmain : ∀ s' : Finset {a // a ∈ s}, s'.card ≤ (s'.biUnion t).card := by
    intro s'
    by_contra hcon
    rw [not_le] at hcon
    set U' : Finset B := s'.biUnion t with hU'
    set S'' : Finset A := s'.image (Subtype.val) with hS''
    have hS''card : S''.card = s'.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hS''sub : S'' ⊆ s := by
      intro a ha
      rw [hS'', Finset.mem_image] at ha
      obtain ⟨a', -, rfl⟩ := ha
      exact a'.2
    have hs'le : s'.card ≤ s.card := by
      rw [← hS''card]
      exact Finset.card_le_card hS''sub
    have hU'T : U' ⊆ T := by
      intro b hb
      rw [hU', Finset.mem_biUnion] at hb
      obtain ⟨a, -, hba⟩ := hb
      exact (Finset.mem_filter.mp hba).1
    have hcard_sdiff : (T \ U').card = T.card - U'.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hU'T]
    have hnonempty : (T \ U').Nonempty := by
      apply Finset.card_pos.mp
      rw [hcard_sdiff]
      omega
    obtain ⟨b₀, hb₀mem⟩ := hnonempty
    rw [Finset.mem_sdiff] at hb₀mem
    obtain ⟨hb₀T, hb₀U'⟩ := hb₀mem
    have hdB : dB ≤ (s.filter (fun a => Rd a b₀)).card := hB b₀ hb₀T
    have hpos : 0 < s'.card := lt_of_le_of_lt (Nat.zero_le _) hcon
    obtain ⟨a₀, ha₀⟩ := Finset.card_pos.mp hpos
    have hta₀ : t a₀ ⊆ U' := by
      intro b hb
      rw [hU', Finset.mem_biUnion]
      exact ⟨a₀, ha₀, hb⟩
    have hdA : dA ≤ U'.card := le_trans (hA a₀.1 a₀.2) (Finset.card_le_card hta₀)
    have hdisj : Disjoint (s.filter (fun a => Rd a b₀)) S'' := by
      rw [Finset.disjoint_left]
      intro a ha haS''
      rw [Finset.mem_filter] at ha
      rw [hS'', Finset.mem_image] at haS''
      obtain ⟨a', ha', rfl⟩ := haS''
      have hb : b₀ ∈ t a' := by
        rw [Finset.mem_filter]
        exact ⟨hb₀T, ha.2⟩
      have : b₀ ∈ U' := by
        rw [hU', Finset.mem_biUnion]
        exact ⟨a', ha', hb⟩
      exact hb₀U' this
    have hcardfilter : (s.filter (fun a => Rd a b₀)).card ≤ s.card - s'.card := by
      have h1 : (s.filter (fun a => Rd a b₀)).card + S''.card ≤ s.card := by
        have hsub1 : s.filter (fun a => Rd a b₀) ⊆ s := Finset.filter_subset _ _
        have h2 : (s.filter (fun a => Rd a b₀)) ∪ S'' ⊆ s := Finset.union_subset hsub1 hS''sub
        have h3 : ((s.filter (fun a => Rd a b₀)) ∪ S'').card
            = (s.filter (fun a => Rd a b₀)).card + S''.card :=
          Finset.card_union_of_disjoint hdisj
        rw [← h3]
        exact Finset.card_le_card h2
      rw [hS''card] at h1
      omega
    omega
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hmain
  exact ⟨f, fun a => Finset.mem_filter.mp (hfmem a), hfinj⟩

/-- The set of colours of the edges from `v` to a vertex of `S`, as assigned by `ψ`. -/
def colorStar [Fintype V] [DecidableEq V] [DecidableEq α] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ψ : Sym2 V → α) (S : Finset V) (v : V) : Finset α :=
  ((G.neighborFinset v).filter (fun u => u ∈ S)).image (fun u => ψ (s(v, u)))

lemma mem_colorStar [Fintype V] [DecidableEq V] [DecidableEq α] {G : SimpleGraph V} [DecidableRel G.Adj]
    {ψ : Sym2 V → α} {S : Finset V} {v : V} {c : α} :
    c ∈ colorStar G ψ S v ↔ ∃ u, G.Adj v u ∧ u ∈ S ∧ ψ (s(v, u)) = c := by
  classical
  simp only [colorStar, Finset.mem_image, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨u, ⟨hadj, huS⟩, rfl⟩; exact ⟨u, hadj, huS, rfl⟩
  · rintro ⟨u, hadj, huS, rfl⟩; exact ⟨u, ⟨hadj, huS⟩, rfl⟩

lemma card_colorStar_le_S [Fintype V] [DecidableEq V] [DecidableEq α] {G : SimpleGraph V} [DecidableRel G.Adj]
    (ψ : Sym2 V → α) (S : Finset V) (v : V) :
    (colorStar G ψ S v).card ≤ S.card := by
  classical
  calc (colorStar G ψ S v).card
      ≤ ((G.neighborFinset v).filter (fun u => u ∈ S)).card := Finset.card_image_le
    _ ≤ S.card := Finset.card_le_card (fun u hu => (Finset.mem_filter.mp hu).2)

/-- The invariant maintained during the induction: `ψ` correctly colours (in the sense of the
theorem) all edges of `G` meeting `S`. -/
def Good {V α : Type*} [Fintype V] (G : SimpleGraph V) (C : Finset α) (Cw : V → Finset α)
    (S : Finset V) (ψ : Sym2 V → α) : Prop :=
  (∀ e ∈ G.edgeSet, (∃ u ∈ e, u ∈ S) → ψ e ∈ C) ∧
  (∀ e ∈ G.edgeSet, (∃ u ∈ e, u ∈ S) → ∀ v, v ∈ e → ψ e ∉ Cw v) ∧
  (∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet, (∃ u ∈ e₁, u ∈ S) → (∃ u ∈ e₂, u ∈ S) →
      e₁ ≠ e₂ → (∃ v, v ∈ e₁ ∧ v ∈ e₂) → ψ e₁ ≠ ψ e₂)

lemma Good_empty [Fintype V] (G : SimpleGraph V) (C : Finset α) (Cw : V → Finset α)
    (ψ : Sym2 V → α) : Good G C Cw ∅ ψ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro e - ⟨u, -, hu⟩; exact absurd hu (Finset.notMem_empty u)
  · rintro e - ⟨u, -, hu⟩; exact absurd hu (Finset.notMem_empty u)
  · rintro e₁ - e₂ - ⟨u, -, hu⟩ - - -; exact absurd hu (Finset.notMem_empty u)

/-- Number of vertices `v` with a fixed colour `c` in `colorStar G ψ S v` is at most `S.card`. -/
lemma card_colorStar_fixed_color_le_S [Fintype V] [DecidableEq V] [DecidableEq α] {G : SimpleGraph V}
    [DecidableRel G.Adj] {C : Finset α} {Cw : V → Finset α} {S : Finset V} {ψ : Sym2 V → α}
    (hψ : Good G C Cw S ψ) (c : α) :
    ((Finset.univ : Finset V).filter (fun v => c ∈ colorStar G ψ S v)).card ≤ S.card := by
  classical
  set F : Finset V := (Finset.univ : Finset V).filter (fun v => c ∈ colorStar G ψ S v) with hF
  set Gt : V → Finset V := fun u =>
    (Finset.univ : Finset V).filter (fun v => G.Adj v u ∧ ψ (s(v, u)) = c) with hGt
  have hsub : F ⊆ S.biUnion Gt := by
    intro v hv
    rw [hF, Finset.mem_filter] at hv
    obtain ⟨-, hv⟩ := hv
    rw [mem_colorStar] at hv
    obtain ⟨u, hadj, huS, hpsi⟩ := hv
    rw [Finset.mem_biUnion]
    exact ⟨u, huS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj, hpsi⟩⟩
  calc F.card ≤ (S.biUnion Gt).card := Finset.card_le_card hsub
    _ ≤ ∑ u ∈ S, (Gt u).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ S, 1 := by
        apply Finset.sum_le_sum
        intro u hu
        rw [Finset.card_le_one]
        intro v1 hv1 v2 hv2
        rw [hGt, Finset.mem_filter] at hv1 hv2
        obtain ⟨-, h1, hp1⟩ := hv1
        obtain ⟨-, h2, hp2⟩ := hv2
        by_contra hne
        have he1 : s(v1, u) ∈ G.edgeSet := by
          rw [SimpleGraph.mem_edgeSet]; exact h1
        have he2 : s(v2, u) ∈ G.edgeSet := by
          rw [SimpleGraph.mem_edgeSet]; exact h2
        have hw1 : ∃ w ∈ s(v1, u), w ∈ S := ⟨u, Sym2.mem_mk_right v1 u, hu⟩
        have hw2 : ∃ w ∈ s(v2, u), w ∈ S := ⟨u, Sym2.mem_mk_right v2 u, hu⟩
        have hsh : ∃ w, w ∈ s(v1, u) ∧ w ∈ s(v2, u) :=
          ⟨u, Sym2.mem_mk_right v1 u, Sym2.mem_mk_right v2 u⟩
        have hene : s(v1, u) ≠ s(v2, u) := by
          intro h
          apply hne
          rw [Sym2.eq_iff] at h
          rcases h with ⟨h1', -⟩ | ⟨h3, -⟩
          · exact h1'
          · exact absurd h3 (G.ne_of_adj h1)
        have := hψ.2.2 _ he1 _ he2 hw1 hw2 hene hsh
        exact this (by rw [hp1, hp2])
    _ = S.card := by simp

theorem hall_based_finishing {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset α) (Cw : V → Finset α) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hC : 7 * δ * (Fintype.card V : ℝ) ≤ (C.card : ℝ))
    (hU : ∃ U : Finset V, (U.card : ℝ) ≤ δ * (Fintype.card V : ℝ) ∧
      ∀ e ∈ G.edgeSet, ∃ u ∈ (e : Sym2 V), u ∈ U)
    (hdeg : ∀ w : V, (G.degree w : ℝ) ≤ (C.card : ℝ) - ((Cw w).card : ℝ))
    (hCw : ∀ w : V, ((Cw w).card : ℝ) ≤ δ * (Fintype.card V : ℝ))
    (hCcol : ∀ c ∈ C, (((Finset.univ : Finset V).filter (fun w => c ∈ Cw w)).card : ℝ) ≤
      δ * (Fintype.card V : ℝ)) :
    ∃ φ : G.edgeSet → α,
      (∀ e : G.edgeSet, φ e ∈ C) ∧
      (∀ e₁ e₂ : G.edgeSet, e₁ ≠ e₂ →
        (∃ v : V, v ∈ (e₁ : Sym2 V) ∧ v ∈ (e₂ : Sym2 V)) → φ e₁ ≠ φ e₂) ∧
      (∀ e : G.edgeSet, ∀ v : V, v ∈ (e : Sym2 V) → φ e ∉ Cw v) := by
  classical
  obtain ⟨U, hUcard, hUcover⟩ := hU
  have hnR : (0 : ℝ) ≤ (Fintype.card V : ℝ) := by positivity
  have hFun : Nonempty (Sym2 V → α) := by
    rcases isEmpty_or_nonempty α with hα | hα
    · have hC0 : C = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun c _ => hα.false c)
      have hcard0 : (C.card : ℝ) = 0 := by simp [hC0]
      have hineq : 7 * δ * (Fintype.card V : ℝ) ≤ 0 := by rw [← hcard0]; exact hC
      have hn0 : (Fintype.card V : ℝ) = 0 := by nlinarith [hδ0, hδ1, hnR, hineq]
      have hV0 : Fintype.card V = 0 := by exact_mod_cast hn0
      have hEmptyV : IsEmpty V := Fintype.card_eq_zero_iff.mp hV0
      have hEmptyS2 : IsEmpty (Sym2 V) := ⟨fun z => Sym2.ind (fun a _ => hEmptyV.false a) z⟩
      exact ⟨fun z => (hEmptyS2.false z).elim⟩
    · exact ⟨fun _ => Classical.choice hα⟩
  have key : ∀ S : Finset V, S ⊆ U → ∃ ψ : Sym2 V → α, Good G C Cw S ψ := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; exact ⟨Classical.choice hFun, Good_empty G C Cw _⟩
    | insert a S ha ih =>
      intro hSU
      have hSU' : S ⊆ U := fun x hx => hSU (Finset.mem_insert_of_mem hx)
      have haU : a ∈ U := hSU (Finset.mem_insert_self a S)
      obtain ⟨ψ, hψ⟩ := ih hSU'
      have hSreal : (S.card : ℝ) ≤ δ * (Fintype.card V : ℝ) := by
        have h1 : (S.card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast Finset.card_le_card hSU'
        linarith [hUcard]
      set New : Finset V := (G.neighborFinset a).filter (fun v => v ∉ S) with hNew
      set Y : Finset α := Cw a ∪ colorStar G ψ S a with hY
      have memNew : ∀ v : V, v ∈ New ↔ G.Adj a v ∧ v ∉ S := by
        intro v; rw [hNew, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      set NS : Finset V := (G.neighborFinset a).filter (fun v => v ∈ S) with hNS
      have hcolorStar_eq : colorStar G ψ S a = NS.image (fun u => ψ (s(a, u))) := by
        rw [colorStar, hNS]
      have hNSle : NS.card ≤ (G.neighborFinset a).card := Finset.card_filter_le _ _
      have hNewcard : New.card = (G.neighborFinset a).card - NS.card := by
        rw [hNew, hNS, Finset.filter_not, Finset.card_sdiff,
          Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]
      have hNewcardR : (New.card : ℝ) = (G.degree a : ℝ) - (NS.card : ℝ) := by
        rw [hNewcard, Nat.cast_sub hNSle, G.card_neighborFinset_eq_degree]
      have hCstar_le_NS : (colorStar G ψ S a).card ≤ NS.card := by
        rw [hcolorStar_eq]; exact Finset.card_image_le
      have hCstar_le_NSR : ((colorStar G ψ S a).card : ℝ) ≤ (NS.card : ℝ) := by
        exact_mod_cast hCstar_le_NS
      have hCstar_real : ((colorStar G ψ S a).card : ℝ) ≤ δ * (Fintype.card V : ℝ) := by
        have h := card_colorStar_le_S (G := G) ψ S a
        have h2 : ((colorStar G ψ S a).card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast h
        linarith [hSreal]
      have hYle : ((Y ∩ C).card : ℝ) ≤ ((Cw a).card : ℝ) + ((colorStar G ψ S a).card : ℝ) := by
        have h2 : (Y ∩ C).card ≤ (Cw a).card + (colorStar G ψ S a).card := by
          refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
          intro c hc
          rw [Finset.mem_inter] at hc
          rw [hY] at hc
          exact hc.1
        calc ((Y ∩ C).card : ℝ) ≤ (((Cw a).card + (colorStar G ψ S a).card : ℕ) : ℝ) := by
              exact_mod_cast h2
          _ = ((Cw a).card : ℝ) + ((colorStar G ψ S a).card : ℝ) := by push_cast; ring
      have hCdiv : (C.card : ℝ) - ((Cw a).card : ℝ) - ((colorStar G ψ S a).card : ℝ) ≤
          ((C \ Y).card : ℝ) := by
        have hCY : (C \ Y).card = C.card - (Y ∩ C).card := Finset.card_sdiff
        have hsub : (Y ∩ C).card ≤ C.card := Finset.card_le_card Finset.inter_subset_right
        rw [hCY, Nat.cast_sub hsub]
        linarith [hYle]
      have hBreal : 5 * δ * (Fintype.card V : ℝ) ≤ ((C \ Y).card : ℝ) := by
        have := hCw a
        linarith [hC, hCdiv, hCstar_real, hYle]
      have hNew_le_B : New.card ≤ (C \ Y).card := by
        have hR : (New.card : ℝ) ≤ ((C \ Y).card : ℝ) := by
          rw [hNewcardR]
          linarith [hdeg a, hCstar_le_NSR, hCdiv]
        exact_mod_cast hR
      set dA : ℕ := ⌈3 * δ * (Fintype.card V : ℝ)⌉₊ with hdA
      set dB : ℕ := New.card - dA with hdB
      have hAr : (3 : ℝ) * δ * (Fintype.card V : ℝ) ≤ (dA : ℝ) := by
        rw [hdA]; exact Nat.le_ceil _
      have hA : ∀ v ∈ New,
          dA ≤ ((C \ Y).filter (fun c => c ∉ Cw v ∧ c ∉ colorStar G ψ S v)).card := by
        intro v hv
        have hCstar_v : ((colorStar G ψ S v).card : ℝ) ≤ δ * (Fintype.card V : ℝ) := by
          have h := card_colorStar_le_S (G := G) ψ S v
          have h2 : ((colorStar G ψ S v).card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast h
          linarith [hSreal]
        rw [hdA, Nat.ceil_le]
        have hfilter : (C \ Y).filter (fun c => c ∉ Cw v ∧ c ∉ colorStar G ψ S v) =
            (C \ Y) \ (Cw v ∪ colorStar G ψ S v) := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union]
          tauto
        rw [hfilter]
        have hZ : (((Cw v ∪ colorStar G ψ S v)).card : ℝ) ≤
            δ * (Fintype.card V : ℝ) + δ * (Fintype.card V : ℝ) := by
          have hcu := Finset.card_union_le (Cw v) (colorStar G ψ S v)
          have hcast : ((Cw v ∪ colorStar G ψ S v).card : ℝ) ≤
              ((Cw v).card : ℝ) + ((colorStar G ψ S v).card : ℝ) := by
            calc ((Cw v ∪ colorStar G ψ S v).card : ℝ)
                ≤ (((Cw v).card + (colorStar G ψ S v).card : ℕ) : ℝ) := by exact_mod_cast hcu
              _ = ((Cw v).card : ℝ) + ((colorStar G ψ S v).card : ℝ) := by push_cast; ring
          linarith [hcast, hCw v, hCstar_v]
        have hZsub : (Cw v ∪ colorStar G ψ S v) ∩ (C \ Y) ⊆ C \ Y := Finset.inter_subset_right
        have hZint_le : ((Cw v ∪ colorStar G ψ S v) ∩ (C \ Y)).card ≤ (C \ Y).card :=
          Finset.card_le_card hZsub
        have hZint : (((Cw v ∪ colorStar G ψ S v) ∩ (C \ Y)).card : ℝ) ≤
            δ * (Fintype.card V : ℝ) + δ * (Fintype.card V : ℝ) := by
          have h1 : ((Cw v ∪ colorStar G ψ S v) ∩ (C \ Y)).card ≤
              (Cw v ∪ colorStar G ψ S v).card :=
            Finset.card_le_card Finset.inter_subset_left
          have h2 : (((Cw v ∪ colorStar G ψ S v) ∩ (C \ Y)).card : ℝ) ≤
              ((Cw v ∪ colorStar G ψ S v).card : ℝ) := by exact_mod_cast h1
          linarith [h2, hZ]
        rw [Finset.card_sdiff, Nat.cast_sub hZint_le]
        linarith [hBreal, hZint]
      have hB : ∀ c ∈ C \ Y,
          dB ≤ (New.filter (fun v => c ∉ Cw v ∧ c ∉ colorStar G ψ S v)).card := by
        intro c hcCY
        have hcC : c ∈ C := (Finset.mem_sdiff.mp hcCY).1
        set Zc : Finset V := ((Finset.univ : Finset V).filter (fun v => c ∈ Cw v)) ∪
            ((Finset.univ : Finset V).filter (fun v => c ∈ colorStar G ψ S v)) with hZc
        have hrest_sub : New.filter (fun v => ¬ (c ∉ Cw v ∧ c ∉ colorStar G ψ S v)) ⊆ Zc := by
          intro v hv
          rw [Finset.mem_filter] at hv
          obtain ⟨-, hv⟩ := hv
          rw [hZc, Finset.mem_union]
          by_cases hcw : c ∈ Cw v
          · left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcw⟩
          · right
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              by by_contra hcs; exact hv ⟨hcw, hcs⟩⟩
        have hZc_card : (Zc.card : ℝ) ≤ δ * (Fintype.card V : ℝ) + δ * (Fintype.card V : ℝ) := by
          have hCwBad : (((Finset.univ : Finset V).filter (fun v => c ∈ Cw v)).card : ℝ) ≤
              δ * (Fintype.card V : ℝ) := hCcol c hcC
          have hCstarBad : (((Finset.univ : Finset V).filter
              (fun v => c ∈ colorStar G ψ S v)).card : ℝ) ≤ δ * (Fintype.card V : ℝ) := by
            have h := card_colorStar_fixed_color_le_S hψ c
            have h2 : (((Finset.univ : Finset V).filter
                (fun v => c ∈ colorStar G ψ S v)).card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast h
            linarith [hSreal]
          have hcu := Finset.card_union_le
            ((Finset.univ : Finset V).filter (fun v => c ∈ Cw v))
            ((Finset.univ : Finset V).filter (fun v => c ∈ colorStar G ψ S v))
          have hcast : ((((Finset.univ : Finset V).filter (fun v => c ∈ Cw v)) ∪
              ((Finset.univ : Finset V).filter (fun v => c ∈ colorStar G ψ S v))).card : ℝ) ≤
              δ * (Fintype.card V : ℝ) + δ * (Fintype.card V : ℝ) := by
            have hc : ((((Finset.univ : Finset V).filter (fun v => c ∈ Cw v)) ∪
                ((Finset.univ : Finset V).filter (fun v => c ∈ colorStar G ψ S v))).card : ℝ) ≤
                ((((Finset.univ : Finset V).filter (fun v => c ∈ Cw v)).card : ℝ) +
                (((Finset.univ : Finset V).filter (fun v => c ∈ colorStar G ψ S v)).card : ℝ)) := by
              calc _ ≤ ((((Finset.univ : Finset V).filter (fun v => c ∈ Cw v)).card +
                    ((Finset.univ : Finset V).filter (fun v => c ∈ colorStar G ψ S v)).card : ℕ) : ℝ) := by
                      exact_mod_cast hcu
                _ = _ := by push_cast; ring
            linarith [hc, hCwBad, hCstarBad]
          rw [hZc]
          exact hcast
        have hcardsplit : (New.filter (fun v => c ∉ Cw v ∧ c ∉ colorStar G ψ S v)).card +
            (New.filter (fun v => ¬ (c ∉ Cw v ∧ c ∉ colorStar G ψ S v))).card = New.card :=
          Finset.card_filter_add_card_filter_not _
        rw [hdB, Nat.sub_le_iff_le_add]
        have hrestR : ((New.filter (fun v => ¬ (c ∉ Cw v ∧ c ∉ colorStar G ψ S v))).card : ℝ) ≤
            (Zc.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hrest_sub
        have hNs : (New.card : ℝ) =
            ((New.filter (fun v => c ∉ Cw v ∧ c ∉ colorStar G ψ S v)).card : ℝ) +
            ((New.filter (fun v => ¬ (c ∉ Cw v ∧ c ∉ colorStar G ψ S v))).card : ℝ) := by
          rw [← hcardsplit]; push_cast; ring
        have : (New.card : ℝ) ≤
            ((New.filter (fun v => c ∉ Cw v ∧ c ∉ colorStar G ψ S v)).card : ℝ) + (dA : ℝ) := by
          linarith [hNs, hrestR, hZc_card, hAr]
        exact_mod_cast this
      have hsum : New.card ≤ dA + dB := by rw [hdB]; omega
      obtain ⟨f, hf, hfinj⟩ := hall_min_degree_aux New (C \ Y)
          (fun v c => c ∉ Cw v ∧ c ∉ colorStar G ψ S v) dA dB hNew_le_B hA hB hsum
      let F0 : V → α := fun v => if hv : v ∈ New then f ⟨v, hv⟩ else ψ (s(a, v))
      let ψ' : Sym2 V → α := fun e =>
        if h : ∃ v : V, v ∈ New ∧ e = s(a, v) then F0 (Classical.choose h) else ψ e
      have hF0 : ∀ v (hv : v ∈ New), F0 v = f ⟨v, hv⟩ := by
        intro v hv; dsimp only [F0]; rw [dif_pos hv]
      have hpsi'_new : ∀ v (hv : v ∈ New), ψ' (s(a, v)) = f ⟨v, hv⟩ := by
        intro v hv
        have hex : ∃ w : V, w ∈ New ∧ s(a, v) = s(a, w) := ⟨v, hv, rfl⟩
        have hcv : Classical.choose hex = v := by
          have heq : s(a, v) = s(a, Classical.choose hex) :=
            (Classical.choose_spec hex).2
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨-, h2⟩ | ⟨-, h4⟩
          · exact h2.symm
          · exact absurd h4.symm (G.ne_of_adj ((memNew v).mp hv).1)
        dsimp only [ψ']
        rw [dif_pos hex, hcv, hF0 v hv]
      have hpsi'_old : ∀ e, ¬(∃ v : V, v ∈ New ∧ e = s(a, v)) → ψ' e = ψ e := by
        intro e hne
        dsimp only [ψ']
        rw [dif_neg hne]
      have hOld : ∀ e ∈ G.edgeSet, (∃ u ∈ e, u ∈ insert a S) →
          ¬(∃ v : V, v ∈ New ∧ e = s(a, v)) → (∃ u ∈ e, u ∈ S) := by
        intro e he hwit hne
        obtain ⟨u, hue, huS'⟩ := hwit
        rcases Finset.mem_insert.mp huS' with hua | huS
        · rw [hua] at hue
          have hwmem : Sym2.Mem.other hue ∈ e := Sym2.other_mem hue
          have hweq : s(a, Sym2.Mem.other hue) = e := Sym2.other_spec hue
          by_cases hwS : Sym2.Mem.other hue ∈ S
          · exact ⟨Sym2.Mem.other hue, hwmem, hwS⟩
          · exfalso
            apply hne
            refine ⟨Sym2.Mem.other hue, ?_, hweq.symm⟩
            rw [memNew]
            refine ⟨?_, hwS⟩
            have : s(a, Sym2.Mem.other hue) ∈ G.edgeSet := by rw [hweq]; exact he
            exact (SimpleGraph.mem_edgeSet G).mp this
        · exact ⟨u, hue, huS⟩
      have new_old_ne : ∀ (w : V) (hw : w ∈ New) (eo : Sym2 V),
          eo ∈ G.edgeSet → (∃ u ∈ eo, u ∈ S) →
          (∃ x, x ∈ s(a, w) ∧ x ∈ eo) → ψ' (s(a, w)) ≠ ψ' eo := by
        intro w hw eo heo hwo hshare
        rw [hpsi'_new w hw]
        have hOld' : ¬(∃ v : V, v ∈ New ∧ eo = s(a, v)) := by
          rintro ⟨v, hv, hvq⟩
          obtain ⟨u, hueo, huS⟩ := hwo
          have hmem : u ∈ s(a, v) := by rw [← hvq]; exact hueo
          rw [Sym2.mem_iff] at hmem
          rcases hmem with hua | huv
          · rw [hua] at huS; exact ha huS
          · rw [huv] at huS; exact ((memNew v).mp hv).2 huS
        rw [hpsi'_old eo hOld']
        obtain ⟨x, hx1, hx2⟩ := hshare
        rw [Sym2.mem_iff] at hx1
        rcases hx1 with hxa | hxw
        · rw [hxa] at hx2
          obtain ⟨u, hueo, huS⟩ := hwo
          have hne_au : a ≠ u := fun h => ha (h ▸ huS)
          have heq2 : eo = s(a, u) := (Sym2.mem_and_mem_iff hne_au).mp ⟨hx2, hueo⟩
          rw [heq2]
          intro hcf
          have heo' : s(a, u) ∈ G.edgeSet := by rw [← heq2]; exact heo
          have hadj : G.Adj a u := (SimpleGraph.mem_edgeSet G).mp heo'
          have hmem : ψ (s(a, u)) ∈ colorStar G ψ S a := by
            rw [mem_colorStar]; exact ⟨u, hadj, huS, rfl⟩
          exact (Finset.mem_sdiff.mp (hf ⟨w, hw⟩).1).2
            (Finset.mem_union_right _ (hcf.symm ▸ hmem))
        · rw [hxw] at hx2
          obtain ⟨u, hueo, huS⟩ := hwo
          have hne_wu : w ≠ u := fun h => ((memNew w).mp hw).2 (h ▸ huS)
          have heq2 : eo = s(w, u) := (Sym2.mem_and_mem_iff hne_wu).mp ⟨hx2, hueo⟩
          rw [heq2]
          intro hcf
          have heo' : s(w, u) ∈ G.edgeSet := by rw [← heq2]; exact heo
          have hadj : G.Adj w u := (SimpleGraph.mem_edgeSet G).mp heo'
          have hmem : ψ (s(w, u)) ∈ colorStar G ψ S w := by
            rw [mem_colorStar]; exact ⟨u, hadj, huS, rfl⟩
          exact (hf ⟨w, hw⟩).2.2 (hcf.symm ▸ hmem)
      refine ⟨ψ', ?_, ?_, ?_⟩
      · intro e he hwit
        by_cases hne : ∃ v : V, v ∈ New ∧ e = s(a, v)
        · obtain ⟨v, hv, rfl⟩ := hne
          rw [hpsi'_new v hv]
          exact (Finset.mem_sdiff.mp (hf ⟨v, hv⟩).1).1
        · obtain ⟨u, hue, huS⟩ := hOld e he hwit hne
          rw [hpsi'_old e hne]
          exact hψ.1 e he ⟨u, hue, huS⟩
      · intro e he hwit w hwe
        by_cases hne : ∃ v : V, v ∈ New ∧ e = s(a, v)
        · obtain ⟨v, hv, rfl⟩ := hne
          rw [hpsi'_new v hv]
          rw [Sym2.mem_iff] at hwe
          rcases hwe with hwa | hwv
          · rw [hwa]; intro hc
            exact (Finset.mem_sdiff.mp (hf ⟨v, hv⟩).1).2 (Finset.mem_union_left _ hc)
          · rw [hwv]; exact (hf ⟨v, hv⟩).2.1
        · obtain ⟨u, hue, huS⟩ := hOld e he hwit hne
          rw [hpsi'_old e hne]
          exact hψ.2.1 e he ⟨u, hue, huS⟩ w hwe
      · intro e₁ he₁ e₂ he₂ hw₁ hw₂ hne12 hshare
        by_cases hne1 : ∃ v : V, v ∈ New ∧ e₁ = s(a, v)
        · obtain ⟨v₁, hv₁, rfl⟩ := hne1
          by_cases hne2 : ∃ v : V, v ∈ New ∧ e₂ = s(a, v)
          · obtain ⟨v₂, hv₂, rfl⟩ := hne2
            rw [hpsi'_new v₁ hv₁, hpsi'_new v₂ hv₂]
            intro hfeq
            have hv : v₁ = v₂ := Subtype.ext_iff.mp (hfinj hfeq)
            exact hne12 (by rw [hv])
          · exact new_old_ne v₁ hv₁ e₂ he₂ (hOld e₂ he₂ hw₂ hne2) hshare
        · by_cases hne2 : ∃ v : V, v ∈ New ∧ e₂ = s(a, v)
          · obtain ⟨v₂, hv₂, rfl⟩ := hne2
            exact Ne.symm (new_old_ne v₂ hv₂ e₁ he₁ (hOld e₁ he₁ hw₁ hne1)
              (by obtain ⟨x, hx1, hx2⟩ := hshare; exact ⟨x, hx2, hx1⟩))
          · rw [hpsi'_old e₁ hne1, hpsi'_old e₂ hne2]
            exact hψ.2.2 e₁ he₁ e₂ he₂ (hOld e₁ he₁ hw₁ hne1) (hOld e₂ he₂ hw₂ hne2)
              hne12 hshare
  obtain ⟨ψ, hψ⟩ := key U (subset_refl U)
  refine ⟨fun e => ψ e.1, ?_, ?_, ?_⟩
  · intro e
    obtain ⟨u, hue, huU⟩ := hUcover e.1 e.2
    exact hψ.1 e.1 e.2 ⟨u, hue, huU⟩
  · intro e₁ e₂ hne hsh
    obtain ⟨u₁, hu₁, hu₁U⟩ := hUcover e₁.1 e₁.2
    obtain ⟨u₂, hu₂, hu₂U⟩ := hUcover e₂.1 e₂.2
    exact hψ.2.2 e₁.1 e₁.2 e₂.1 e₂.2 ⟨u₁, hu₁, hu₁U⟩ ⟨u₂, hu₂, hu₂U⟩
      (fun h => hne (Subtype.ext h)) hsh
  · intro e v hve
    obtain ⟨u, hue, huU⟩ := hUcover e.1 e.2
    exact hψ.2.1 e.1 e.2 ⟨u, hue, huU⟩ v hve

end Commons.Combinatorics.SimpleGraph
