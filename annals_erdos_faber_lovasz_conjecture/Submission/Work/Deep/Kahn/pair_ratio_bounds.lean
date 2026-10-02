import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.FinishSetup

namespace Work.Deep.Kahn

open ErdosFaberLovaszConjecture

noncomputable section

variable {n c : ℕ}

/-- The number of edges of `𝓗` containing the vertex `x` whose list contains the
colour `γ`, written as the cardinality of a subtype.  This is the bridge between
the `Nat.card` formulation of the colour degrees and the `Finset` counts used in
the double counting below. -/
private lemma natCard_subtype_eq_filter_card {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] :
    Nat.card {x : α // P x} = (Finset.univ.filter P).card := by
  classical
  rw [Nat.card_eq_fintype_card]
  have key := Fintype.card_ofFinset (p := {x : α | P x}) (Finset.univ.filter P)
    (fun x => by simp)
  show Fintype.card ↑({x : α | P x} : Set α) = (Finset.univ.filter P).card
  exact key

/-- Two distinct elements of a subtype give cardinality at least two. -/
private lemma two_le_natCard_subtype {α : Type*} [Fintype α] {P : α → Prop} [DecidablePred P]
    {a b : α} (ha : P a) (hb : P b) (hab : a ≠ b) : 2 ≤ Nat.card {x : α // P x} := by
  classical
  rw [Nat.card_eq_fintype_card]
  refine le_trans ?_ (Fintype.card_le_of_injective
    (fun i : Fin 2 => if i = 0 then (⟨a, ha⟩ : {x : α // P x}) else ⟨b, hb⟩) ?_)
  · simp
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff]

/-- **Double counting bound.**  For a finite family `S` of edges all meeting the
edge `e`, the total number of colour coincidences
`∑_{f ∈ S} |L e ∩ L f|` is at most `|L e| · |e| · D`: every such coincidence is a
triple `(f, x, γ)` with `f ∈ S`, `x ∈ f ∩ e` and `γ ∈ L e ∩ L f`, and for a fixed
pair `(x, γ)` there are at most `D` edges through `x` whose list contains `γ`. -/
private lemma sum_inter_card_le {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)} [Fintype 𝓗]
    (L : 𝓗 → Finset (Fin c)) (e : 𝓗) (S : Finset 𝓗) {D : ℝ}
    (hS : ∀ f ∈ S, (verts (f : Set (Fin n)) ∩ verts (e : Set (Fin n))).Nonempty)
    (hcol : ∀ x : Fin n, ∀ γ : Fin c,
      ((Nat.card {g : 𝓗 // x ∈ (g : Set (Fin n)) ∧ γ ∈ L g} : ℕ) : ℝ) ≤ D) :
    ∑ f ∈ S, ((L e ∩ L f).card : ℝ) ≤ ((L e).card : ℝ) * (edgeSize (e : Set (Fin n)) : ℝ) * D := by
  classical
  -- the finset of pairs `(f, γ)` with `f ∈ S` and `γ ∈ L e ∩ L f`
  set A : Finset ((f : 𝓗) × Fin c) := S.sigma (fun f => L e ∩ L f) with hA
  -- the edges containing `x` whose list contains `γ`
  set Fp : Fin n → Fin c → Finset 𝓗 :=
    fun x γ => Finset.univ.filter (fun g : 𝓗 => x ∈ (g : Set (Fin n)) ∧ γ ∈ L g) with hFp
  -- the part of `A` carried by the pair `p = (x, γ)`
  set Ap : Fin n × Fin c → Finset ((f : 𝓗) × Fin c) :=
    fun p => A.filter (fun a => p.1 ∈ (a.1 : Set (Fin n)) ∧ a.2 = p.2) with hAp
  -- the vertex/colour index set
  set B : Finset (Fin n × Fin c) := verts (e : Set (Fin n)) ×ˢ (L e) with hB
  have hAcard : (A.card : ℝ) = ∑ f ∈ S, ((L e ∩ L f).card : ℝ) := by
    rw [hA, Finset.card_sigma]
    push_cast
    rfl
  -- every pair of `A` is counted by some `p ∈ B`
  have hcover : A ⊆ B.biUnion Ap := by
    intro a ha
    rw [hA, Finset.mem_sigma] at ha
    obtain ⟨hfa, ha2⟩ := ha
    rw [Finset.mem_inter] at ha2
    obtain ⟨x, hx⟩ := hS a.1 hfa
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_biUnion]
    refine ⟨(x, a.2), ?_, ?_⟩
    · rw [hB, Finset.mem_product]
      exact ⟨hx.2, ha2.1⟩
    · rw [hAp, Finset.mem_filter]
      exact ⟨by rw [hA]; exact Finset.mem_sigma.mpr ⟨hfa, Finset.mem_inter.mpr ha2⟩,
        (mem_verts (a.1 : Set (Fin n)) x).mp hx.1, rfl⟩
  -- the piece at `p` injects into the edges through `p.1` carrying `p.2`
  have hper : ∀ p ∈ B, (Ap p).card ≤ (Fp p.1 p.2).card := by
    intro p _
    refine Finset.card_le_card_of_injOn (fun a : (f : 𝓗) × Fin c => a.1) ?_ ?_
    · intro a ha
      have ha' : a ∈ A.filter (fun a => p.1 ∈ (a.1 : Set (Fin n)) ∧ a.2 = p.2) := by
        rwa [hAp] at ha
      obtain ⟨haA, hax, haγ⟩ := Finset.mem_filter.mp ha'
      have hmem : a ∈ S.sigma (fun f => L e ∩ L f) := by rwa [hA] at haA
      have h2 : a.2 ∈ L a.1 := by
        have h := (Finset.mem_sigma.mp hmem).2
        rw [Finset.mem_inter] at h
        exact h.2
      have key : a.1 ∈ Fp p.1 p.2 := by
        rw [hFp, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hax, by rw [← haγ]; exact h2⟩
      simpa using key
    · intro a ha b hb hab
      have ha' : a ∈ A.filter (fun a => p.1 ∈ (a.1 : Set (Fin n)) ∧ a.2 = p.2) := by
        rwa [hAp] at ha
      have hb' : b ∈ A.filter (fun a => p.1 ∈ (a.1 : Set (Fin n)) ∧ a.2 = p.2) := by
        rwa [hAp] at hb
      have ha2 : a.2 = p.2 := (Finset.mem_filter.mp ha').2.2
      have hb2 : b.2 = p.2 := (Finset.mem_filter.mp hb').2.2
      have hab' : a.1 = b.1 := hab
      have hsig : (⟨a.1, a.2⟩ : (f : 𝓗) × Fin c) = ⟨b.1, b.2⟩ := by rw [hab', ha2, hb2]
      rw [← Sigma.eta a, hsig]
  calc ∑ f ∈ S, ((L e ∩ L f).card : ℝ)
      = (A.card : ℝ) := hAcard.symm
    _ ≤ ((B.biUnion Ap).card : ℝ) := by exact_mod_cast Finset.card_le_card hcover
    _ ≤ ((∑ p ∈ B, (Ap p).card : ℕ) : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ = ∑ p ∈ B, ((Ap p).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ p ∈ B, ((Fp p.1 p.2).card : ℝ) := by exact_mod_cast Finset.sum_le_sum hper
    _ = ∑ p ∈ B, ((Nat.card {g : 𝓗 // p.1 ∈ (g : Set (Fin n)) ∧ p.2 ∈ L g} : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [hFp, natCard_subtype_eq_filter_card]
    _ ≤ ∑ p ∈ B, D := Finset.sum_le_sum (fun p _ => hcol p.1 p.2)
    _ = ((L e).card : ℝ) * (edgeSize (e : Set (Fin n)) : ℝ) * D := by
          rw [Finset.sum_const, hB, Finset.card_product, nsmul_eq_mul]
          push_cast
          rw [show edgeSize (e : Set (Fin n)) = (verts (e : Set (Fin n))).card from rfl]
          ring

/-- Counting bounds for the finishing step: for a hypergraph `𝓗` on `Fin n` with edges of size
at most `r`, colour degrees `D_x(γ) = #{e ∋ x : γ ∈ L e} ≤ D` and lists of size at least
`8 r D`, the probability `|L e ∩ L f| / (|L e| * |L f|)` that two distinct meeting edges get the
same colour is at most `1/16`, and the sum of those ratios over all edges `f` meeting a fixed
edge `e` is at most `1/8`.

Sketch.  `8 * r * D ≤ |L e|` with `r > 0`, `D > 0` gives `|L e| ≥ 1`, so the denominators are
positive.  First bound: if `L e ∩ L f = ∅` the ratio is `0`; otherwise fix `x ∈ e ∩ f` and
`γ ∈ L e ∩ L f`; the distinct edges `e ≠ f` both lie in `{g : 𝓗 // x ∈ g ∧ γ ∈ L g}`, whose
`Nat.card` is therefore at least `2`, so `2 ≤ D`; also `e ≠ f` are distinct sets, so
`1 ≤ edgeSize e ≤ r`.  Hence `8 r D ≥ 16` and `|L e|, |L f| ≥ 16`, and the ratio is at most
`1 / max (|L e|) (|L f|) ≤ 1/16`.  Second bound: bound `1 / |L f|` by `1 / (8 r D)` and double
count `∑_f |L e ∩ L f|` by pairs `(x, γ)` with `x ∈ e`, `γ ∈ L e`: for fixed `x` and `γ` at
most `D` edges `f` contain `x` and satisfy `γ ∈ L f` (`hcol`), so
`∑_f |L e ∩ L f| ≤ |L e| * |e| * D ≤ |L e| * r * D`; dividing by `|L e| * 8 * r * D` gives
`|e| / (8 r) ≤ 1/8`. -/
theorem pair_ratio_bounds {n c : ℕ} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    [Fintype 𝓗] (L : 𝓗 → Finset (Fin c)) {r D : ℝ} (hr : 0 < r) (hD : 0 < D)
    (hsize : ∀ e : 𝓗, (ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) : ℝ) ≤ r)
    (hcol : ∀ x : Fin n, ∀ γ : Fin c,
      ((Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} : ℕ) : ℝ) ≤ D)
    (hlist : ∀ e : 𝓗, 8 * r * D ≤ ((L e).card : ℝ)) :
    (∀ e f : 𝓗, e ≠ f → ((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty →
      (((L e ∩ L f).card : ℝ) / (((L e).card : ℝ) * ((L f).card : ℝ))) ≤ 1 / 16)
    ∧ (∀ e : 𝓗,
      ∑ f ∈ (Finset.univ.filter (fun f : 𝓗 => f ≠ e ∧
          (ErdosFaberLovaszConjecture.verts (f : Set (Fin n)) ∩
            ErdosFaberLovaszConjecture.verts (e : Set (Fin n))).Nonempty)),
        (((L e ∩ L f).card : ℝ) / (((L e).card : ℝ) * ((L f).card : ℝ))) ≤ 1 / 8) := by
  classical
  constructor
  · -- first bound: two distinct meeting edges share a colour with probability `≤ 1/16`
    intro e f hne hint
    obtain ⟨x, hx⟩ := hint
    rw [Set.mem_inter_iff] at hx
    obtain ⟨hxe, hxf⟩ := hx
    by_cases hempty : L e ∩ L f = ∅
    · rw [hempty, Finset.card_empty]
      norm_num
    · have hnon : (L e ∩ L f).Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨γ, hγ⟩ := hnon
      rw [Finset.mem_inter] at hγ
      obtain ⟨hγe, hγf⟩ := hγ
      -- the two distinct edges `e ≠ f` through `x` carrying `γ` force `2 ≤ D`
      have h2D : (2 : ℝ) ≤ D := by
        have h2 : 2 ≤ Nat.card {g : 𝓗 // x ∈ (g : Set (Fin n)) ∧ γ ∈ L g} :=
          two_le_natCard_subtype ⟨hxe, hγe⟩ ⟨hxf, hγf⟩ hne
        exact le_trans (by exact_mod_cast h2) (hcol x γ)
      -- `x ∈ e` makes `e` nonempty, so `1 ≤ edgeSize e ≤ r`
      have h1r : (1 : ℝ) ≤ r := by
        have h1e : 1 ≤ edgeSize (e : Set (Fin n)) := by
          have hne' : (verts (e : Set (Fin n))).Nonempty := ⟨x, (mem_verts _ x).mpr hxe⟩
          have hpos : 0 < (verts (e : Set (Fin n))).card := Finset.card_pos.mpr hne'
          show 1 ≤ (verts (e : Set (Fin n))).card
          omega
        exact le_trans (by exact_mod_cast h1e) (hsize e)
      have h16 : (16 : ℝ) ≤ 8 * r * D := by nlinarith
      have hLe : (16 : ℝ) ≤ ((L e).card : ℝ) := le_trans h16 (hlist e)
      have hLf : (16 : ℝ) ≤ ((L f).card : ℝ) := le_trans h16 (hlist f)
      have hLepos : (0 : ℝ) < ((L e).card : ℝ) := by linarith
      have hLfpos : (0 : ℝ) < ((L f).card : ℝ) := by linarith
      have hcard : (((L e ∩ L f).card : ℕ) : ℝ) ≤ ((L f).card : ℝ) := by
        exact_mod_cast Finset.card_le_card Finset.inter_subset_right
      rw [div_le_iff₀ (mul_pos hLepos hLfpos)]
      nlinarith [hcard, hLe, hLfpos]
  · -- second bound: the sum over the meeting edges
    intro e
    set S : Finset 𝓗 := Finset.univ.filter (fun f : 𝓗 => f ≠ e ∧
        (ErdosFaberLovaszConjecture.verts (f : Set (Fin n)) ∩
          ErdosFaberLovaszConjecture.verts (e : Set (Fin n))).Nonempty) with hSdef
    have hS : ∀ f ∈ S, (verts (f : Set (Fin n)) ∩ verts (e : Set (Fin n))).Nonempty := by
      intro f hf
      rw [hSdef, Finset.mem_filter] at hf
      exact hf.2.2
    have hcount := sum_inter_card_le (𝓗 := 𝓗) L e S hS hcol
    have hrD : (0 : ℝ) < 8 * r * D := by positivity
    have hLepos : (0 : ℝ) < ((L e).card : ℝ) := lt_of_lt_of_le hrD (hlist e)
    have hden : (0 : ℝ) < ((L e).card : ℝ) * (8 * r * D) := mul_pos hLepos hrD
    have hterm : ∀ f ∈ S,
        ((L e ∩ L f).card : ℝ) / (((L e).card : ℝ) * ((L f).card : ℝ))
          ≤ ((L e ∩ L f).card : ℝ) / (((L e).card : ℝ) * (8 * r * D)) := by
      intro f _
      have hLf : 8 * r * D ≤ ((L f).card : ℝ) := hlist f
      have hLfpos : (0 : ℝ) < ((L f).card : ℝ) := lt_of_lt_of_le hrD hLf
      rw [div_le_div_iff₀ (mul_pos hLepos hLfpos) hden]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLf hLepos.le) (by positivity)
    have hfin : (((L e).card : ℝ) * (edgeSize (e : Set (Fin n)) : ℝ) * D)
        / (((L e).card : ℝ) * (8 * r * D)) ≤ 1 / 8 := by
      rw [div_le_iff₀ hden]
      have key : (1 / 8 : ℝ) * (((L e).card : ℝ) * (8 * r * D))
          = ((L e).card : ℝ) * r * D := by ring
      rw [key]
      have h1 : (edgeSize (e : Set (Fin n)) : ℝ) * D ≤ r * D :=
        mul_le_mul_of_nonneg_right (hsize e) hD.le
      have h2 : ((L e).card : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) * D)
          ≤ ((L e).card : ℝ) * (r * D) := mul_le_mul_of_nonneg_left h1 hLepos.le
      nlinarith [h2]
    calc ∑ f ∈ S, ((L e ∩ L f).card : ℝ) / (((L e).card : ℝ) * ((L f).card : ℝ))
        ≤ ∑ f ∈ S, ((L e ∩ L f).card : ℝ) / (((L e).card : ℝ) * (8 * r * D)) :=
            Finset.sum_le_sum hterm
      _ = (∑ f ∈ S, ((L e ∩ L f).card : ℝ)) / (((L e).card : ℝ) * (8 * r * D)) :=
            (Finset.sum_div S (fun f => ((L e ∩ L f).card : ℝ))
              (((L e).card : ℝ) * (8 * r * D))).symm
      _ ≤ (((L e).card : ℝ) * (edgeSize (e : Set (Fin n)) : ℝ) * D)
            / (((L e).card : ℝ) * (8 * r * D)) := by
            rw [div_le_div_iff₀ hden hden]
            exact mul_le_mul_of_nonneg_right hcount hden.le
      _ ≤ 1 / 8 := hfin

end

end Work.Deep.Kahn
