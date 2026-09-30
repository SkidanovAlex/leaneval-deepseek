import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary graph data for the MRT step 6 (`arc_graph_data`)

From a finite set `Tset` of vertices `(T, q, qf, γ, Ps)` and a finite set `S'` of "pre-edges"
carrying prime witnesses, this file builds a *symmetric* adjacency relation `Adj`, an edge set
`E` of the same size as `S'`, and a prime labelling `pr` with the properties needed for the
closed-walk counting argument.

The only non-trivial point is that the geometry of an edge can be traversed in either
direction: swapping the two primes in the integrality condition is handled by negation
(`IntegralOn` is closed under `-`), while swapping them in the geometry costs a factor `2`
(since the prime ratio lies in `[1/2, 2]`).  That is why the target bound is `200 * L`, whereas
the witness supplied by `S'` only guarantees `100 * L`.
-/

open Polynomial Finset Real
open Work.BMF

namespace Work.N8

/-- Vertex type: pairs `(endpoint, phase-data)` lying in `Tset`. -/
abbrev ArcVtx (Tset : Finset (ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ)) :=
  {v : ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ // v ∈ Tset}

/-- `ArcAdm100 Tset P₁ L q₀ a b`: there is a pair of primes in `[P₁, 2P₁]`, none dividing `q₀`,
such that the dilated phases differ by an integral polynomial and the geometry of the oriented
edge `(a, b)` holds with constant `100 * L`. -/
def ArcAdm100 (Tset : Finset (ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ)) (P₁ L : ℝ) (q₀ : ℕ)
    (a b : ArcVtx Tset) : Prop :=
  ∃ p₁ p₂ : ℕ, IsPrimeIn P₁ (2 * P₁) p₁ ∧ IsPrimeIn P₁ (2 * P₁) p₂ ∧
    ¬ p₁ ∣ q₀ ∧ ¬ p₂ ∣ q₀ ∧
    IntegralOn 1 (dil (p₂ : ℝ) (a.1.2.2.2.2.1) - dil (p₁ : ℝ) (b.1.2.2.2.2.1)) ∧
    |a.1.1 - ((p₂ : ℝ) / (p₁ : ℝ)) * b.1.1| ≤ 100 * L

/-- `ArcAdm200r Tset P₁ L q₀ a b r`: the ordered pair of primes `r` witnesses the edge condition
for the oriented edge `(a, b)` with constant `200 * L`. -/
def ArcAdm200r (Tset : Finset (ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ)) (P₁ L : ℝ) (q₀ : ℕ)
    (a b : ArcVtx Tset) (r : ℕ × ℕ) : Prop :=
  IsPrimeIn P₁ (2 * P₁) r.1 ∧ IsPrimeIn P₁ (2 * P₁) r.2 ∧
    ¬ r.1 ∣ q₀ ∧ ¬ r.2 ∣ q₀ ∧
    IntegralOn 1 (dil ((r.2 : ℕ) : ℝ) (a.1.2.2.2.2.1) - dil ((r.1 : ℕ) : ℝ) (b.1.2.2.2.2.1)) ∧
    |a.1.1 - (((r.2 : ℕ) : ℝ) / ((r.1 : ℕ) : ℝ)) * b.1.1| ≤ 200 * L

/-- `IntegralOn δ` is closed under negation. -/
lemma arc_IntegralOn_neg {δ : ℝ} {γ : ℝ[X]} (h : IntegralOn δ γ) : IntegralOn δ (-γ) := by
  intro n
  obtain ⟨m, hm⟩ := h n
  refine ⟨-m, ?_⟩
  rw [Polynomial.eval_neg, hm, Int.cast_neg]

/-- Reversing an oriented edge costs a factor `2` in the geometry: if the prime ratio `B/A` is in
`[1/2, 2]`, then `|X - (B/A) Y| ≤ 100 L` implies `|Y - (A/B) X| ≤ 200 L`. -/
lemma arc_geom_swap {P₁ A B X Y L : ℝ} (hP₁ : 0 < P₁)
    (hA1 : P₁ ≤ A) (hA2 : A ≤ 2 * P₁) (hB1 : P₁ ≤ B) (_hB2 : B ≤ 2 * P₁)
    (_hL : 0 ≤ L) (h : |X - (B / A) * Y| ≤ 100 * L) :
    |Y - (A / B) * X| ≤ 200 * L := by
  have hA : 0 < A := lt_of_lt_of_le hP₁ hA1
  have hB : 0 < B := lt_of_lt_of_le hP₁ hB1
  have key : Y - (A / B) * X = -(A / B) * (X - (B / A) * Y) := by
    field_simp
    ring
  rw [key, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (le_of_lt hA) (le_of_lt hB))]
  have hle : A / B ≤ 2 := by rw [div_le_iff₀ hB]; nlinarith
  have h1 : A / B * |X - (B / A) * Y| ≤ 2 * |X - (B / A) * Y| :=
    mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  have h2 : (2 : ℝ) * |X - (B / A) * Y| ≤ 2 * (100 * L) :=
    mul_le_mul_of_nonneg_left h (by norm_num)
  linarith

/-- The fibre of the position map `v ↦ v.1.1` over `y` has at most `Kg` elements, because the
second component is injective once the first component is fixed, and each second component lies
in `Fg y`, a set of size at most `Kg`. -/
lemma arc_fiber_card (Tset : Finset (ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ))
    (fam : Finset ℝ) (Fg : ℝ → Finset (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ))
    (Kg : ℕ) (hTsub : ∀ v ∈ Tset, v.1 ∈ fam ∧ v.2 ∈ Fg v.1)
    (hFgcard : ∀ x, (Fg x).card ≤ Kg) (y : ℝ) :
    ((Finset.univ.filter (fun v : ArcVtx Tset => v.1.1 = y)).card : ℝ) ≤ (Kg : ℝ) := by
  classical
  have hsub : (Finset.univ.filter (fun v : ArcVtx Tset => v.1.1 = y)).image (fun v => v.1.2)
      ⊆ Fg y := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    have hv1 : v.1.1 = y := (Finset.mem_filter.mp hv).2
    have h := (hTsub v.1 v.2).2
    rwa [hv1] at h
  have hinj : Set.InjOn (fun v : ArcVtx Tset => v.1.2)
      ↑(Finset.univ.filter (fun v : ArcVtx Tset => v.1.1 = y)) := by
    intro v hv w hw hvw
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv hw
    exact Subtype.ext (Prod.ext (by rw [hv, hw]) hvw)
  have hcard := Finset.card_image_of_injOn hinj
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  calc ((Finset.univ.filter (fun v : ArcVtx Tset => v.1.1 = y)).card : ℝ)
      ≤ ((Fg y).card : ℝ) := by exact_mod_cast hle
    _ ≤ (Kg : ℝ) := by exact_mod_cast (hFgcard y)

/-- The crux: an `Adm100`-admissible oriented edge in either direction yields a pair of primes
satisfying the `200 * L` edge condition for the orientation `(a, b)`.  In the reverse case one
swaps the two primes: integrality follows from negation, the geometry from `arc_geom_swap`. -/
lemma arc_key {Tset : Finset (ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ)} {P₁ L : ℝ} {q₀ : ℕ}
    (hP₁ : 0 < P₁) (hL : 0 < L) (a b : ArcVtx Tset)
    (h : ArcAdm100 Tset P₁ L q₀ a b ∨ ArcAdm100 Tset P₁ L q₀ b a) :
    ∃ r, ArcAdm200r Tset P₁ L q₀ a b r := by
  rcases h with ⟨p₁, p₂, hp1, hp2, hn1, hn2, hint, hgeo⟩ | ⟨p₁, p₂, hp1, hp2, hn1, hn2, hint, hgeo⟩
  · refine ⟨(p₁, p₂), hp1, hp2, hn1, hn2, ?_, ?_⟩
    · simpa using hint
    · have h100 : (100 : ℝ) * L ≤ 200 * L := by nlinarith [hL]
      linarith
  · refine ⟨(p₂, p₁), hp2, hp1, hn2, hn1, ?_, ?_⟩
    · simpa only [neg_sub] using arc_IntegralOn_neg (δ := 1) hint
    · exact arc_geom_swap hP₁ hp1.2.1 hp1.2.2 hp2.2.1 hp2.2.2 hL.le hgeo

/-- The prime labelling associated to an oriented edge: the chosen `200 * L`-witness when it
exists, and `(1, 1)` otherwise. -/
noncomputable def arc_prF (Tset : Finset (ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ))
    (P₁ L : ℝ) (q₀ : ℕ) (a b : ArcVtx Tset) : ℕ × ℕ := by
  classical
  exact if h : ∃ r, ArcAdm200r Tset P₁ L q₀ a b r then Classical.choose h else (1, 1)

/-- The prime labelling satisfies the edge condition on `Adm100`-admissible oriented edges. -/
lemma arc_prF_spec {Tset : Finset (ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ)} {P₁ L : ℝ}
    {q₀ : ℕ} (hP₁ : 0 < P₁) (hL : 0 < L) {a b : ArcVtx Tset}
    (h : ArcAdm100 Tset P₁ L q₀ a b ∨ ArcAdm100 Tset P₁ L q₀ b a) :
    ArcAdm200r Tset P₁ L q₀ a b (arc_prF Tset P₁ L q₀ a b) := by
  have h' : ∃ r, ArcAdm200r Tset P₁ L q₀ a b r := arc_key hP₁ hL a b h
  have heq : arc_prF Tset P₁ L q₀ a b = Classical.choose h' := by
    unfold arc_prF
    exact dif_pos h'
  rw [heq]
  exact Classical.choose_spec h'

theorem arc_graph_data2
    (P₁ L : ℝ) (q₀ : ℕ) (fam : Finset ℝ)
    (Tset : Finset (ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ))
    (S' : Finset ((ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ) ×
      (ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ)))
    (Fg : ℝ → Finset (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ)) (Kg : ℕ) (D : ℝ)
    (hP₁ : 0 < P₁) (hL : 0 < L) (hD : 0 < D)
    (hTsub : ∀ v ∈ Tset, v.1 ∈ fam ∧ v.2 ∈ Fg v.1)
    (hFgcard : ∀ x, (Fg x).card ≤ Kg)
    (hq₀ : ∀ v ∈ Tset, v.2.2.1 = q₀)
    (hsep : ∀ x ∈ fam, ∀ y ∈ fam, x ≠ y → 500 * L ≤ abs (x - y))
    (hposD : ∀ v ∈ Tset, D ≤ v.1)
    (hS'mem : ∀ p ∈ S', p.1 ∈ Tset ∧ p.2 ∈ Tset ∧
      (∃ p₁ p₂ : ℕ, Work.BMF.IsPrimeIn P₁ (2 * P₁) p₁ ∧ Work.BMF.IsPrimeIn P₁ (2 * P₁) p₂ ∧
        p₁ ≠ p₂ ∧ ¬ p₁ ∣ q₀ ∧ ¬ p₂ ∣ q₀ ∧
        Work.BMF.EdgeGeom fam P₁ L ⟨p.1.1, p.2.1, p₁, p₂⟩ ∧
        Work.BMF.IntegralOn 1 (Work.BMF.dil (p₂ : ℝ) p.1.2.2.2.2.1 -
          Work.BMF.dil (p₁ : ℝ) p.2.2.2.2.2.1))) :
    ∃ (Adj : {v : ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ // v ∈ Tset} →
        {v : ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ // v ∈ Tset} → Prop)
      (E : Finset ({v : ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ // v ∈ Tset} ×
        {v : ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ // v ∈ Tset}))
      (pr : {v : ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ // v ∈ Tset} →
        {v : ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ // v ∈ Tset} → ℕ × ℕ)
      (pos : {v : ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ // v ∈ Tset} → ℝ)
      (γ : {v : ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ // v ∈ Tset} → Polynomial ℝ),
      (∀ a b, Adj a b ↔ Adj b a) ∧
      (∀ p ∈ E, Adj p.1 p.2) ∧
      ((S'.card : ℝ) ≤ (E.card : ℝ)) ∧
      (∀ v, pos v = v.1.1) ∧ (∀ v, γ v = v.1.2.2.2.2.1) ∧
      (∀ v, D ≤ pos v) ∧
      (∀ v v', Adj v v' → Work.BMF.IsPrimeIn P₁ (2 * P₁) (pr v v').1 ∧
        Work.BMF.IsPrimeIn P₁ (2 * P₁) (pr v v').2 ∧
        ¬ (pr v v').1 ∣ q₀ ∧ ¬ (pr v v').2 ∣ q₀ ∧
        Work.BMF.IntegralOn 1 (Work.BMF.dil (((pr v v').2 : ℕ) : ℝ) (γ v) -
          Work.BMF.dil (((pr v v').1 : ℕ) : ℝ) (γ v')) ∧
        abs (pos v - (((pr v v').2 : ℕ) : ℝ) / (((pr v v').1 : ℕ) : ℝ) * pos v') ≤ 200 * L) ∧
      (∀ y : ℝ, ((Finset.univ.filter
        (fun v : {v : ℝ × ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ // v ∈ Tset} => pos v = y)).card : ℝ)
        ≤ (Kg : ℝ)) ∧
      (∀ v v', pos v ≠ pos v' → 500 * L ≤ abs (pos v - pos v')) := by
  classical
  let Adj : ArcVtx Tset → ArcVtx Tset → Prop :=
    fun a b => ArcAdm100 Tset P₁ L q₀ a b ∨ ArcAdm100 Tset P₁ L q₀ b a
  set F' : {q // q ∈ S'} → ArcVtx Tset × ArcVtx Tset := fun q =>
      (⟨q.1.1, (hS'mem q.1 q.2).1⟩, ⟨q.1.2, (hS'mem q.1 q.2).2.1⟩) with hF'def
  set E : Finset (ArcVtx Tset × ArcVtx Tset) := S'.attach.image F' with hEdef
  have hF'inj : Function.Injective F' := by
    intro q q' hqq
    have hv1 : q.1.1 = q'.1.1 := by
      have := congrArg Subtype.val (congrArg Prod.fst hqq)
      simpa [hF'def] using this
    have hv2 : q.1.2 = q'.1.2 := by
      have := congrArg Subtype.val (congrArg Prod.snd hqq)
      simpa [hF'def] using this
    exact Subtype.ext (Prod.ext hv1 hv2)
  have hEcard : E.card = S'.card := by
    rw [hEdef, Finset.card_image_of_injective S'.attach hF'inj, Finset.card_attach]
  have hEmem : ∀ p ∈ E, Adj p.1 p.2 := by
    intro p hp
    have hp' : ∃ q ∈ S'.attach, F' q = p := by
      rw [hEdef] at hp
      exact Finset.mem_image.mp hp
    obtain ⟨q, -, hq⟩ := hp'
    rw [← hq]
    change ArcAdm100 Tset P₁ L q₀ (F' q).1 (F' q).2 ∨
      ArcAdm100 Tset P₁ L q₀ (F' q).2 (F' q).1
    apply Or.inl
    obtain ⟨p₁, p₂, hp1, hp2, _hne, hn1, hn2, hedge, hint⟩ := (hS'mem q.1 q.2).2.2
    refine ⟨p₁, p₂, hp1, hp2, hn1, hn2, ?_, ?_⟩
    · simpa [hF'def] using hint
    · obtain ⟨-, -, -, -, -, -, hge⟩ := hedge
      simpa [hF'def] using hge
  refine ⟨Adj, E, arc_prF Tset P₁ L q₀, (fun v => v.1.1), (fun v => v.1.2.2.2.2.1),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    change (ArcAdm100 Tset P₁ L q₀ a b ∨ ArcAdm100 Tset P₁ L q₀ b a) ↔
      (ArcAdm100 Tset P₁ L q₀ b a ∨ ArcAdm100 Tset P₁ L q₀ a b)
    exact or_comm
  · exact hEmem
  · exact_mod_cast hEcard.symm.le
  · intro v; rfl
  · intro v; rfl
  · intro v; exact hposD v.1 v.2
  · intro v v' hv
    exact arc_prF_spec hP₁ hL hv
  · intro y
    exact arc_fiber_card Tset fam Fg Kg hTsub hFgcard y
  · intro v v' hne
    exact hsep v.1.1 (hTsub v.1 v.2).1 v'.1.1 (hTsub v'.1 v'.2).1 hne

end Work.N8
