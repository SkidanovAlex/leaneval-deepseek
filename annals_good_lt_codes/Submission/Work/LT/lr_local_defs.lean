import Mathlib
import Submission.Work.LT.Defs

/-! Local infrastructure for the proof of `Work.LT.lr_local_opt_far`
(DELLM Proposition 4.8 in its quadripartite form).

Vertices are `(α,β,g)`; the A-edge at a vertex in direction `i` and the B-edge in direction `j`
are the two (families of) edges through that vertex.  Everything below is stated in terms of the
*local views* `view W v : Fin Δ × Fin Δ → ZMod 2`.

The key geometric identity is `nA_nB`: the square through a vertex seen in direction `(i,j)` has
the same four corners no matter from which of them it is described. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.LT

open Classical
open scoped BigOperators

variable {G : Type*} [Group G] [Fintype G] {Δ : ℕ}

/-- Vertices of the quadripartite complex: `(α,β,g)`. -/
abbrev Vtx (G : Type*) : Type _ := Fin 2 × Fin 2 × G

/-- Index type of the A-edges `(β,g,i)` and of the B-edges `(α,g,j)`. -/
abbrev EIdx (G : Type*) (Δ : ℕ) : Type _ := Fin 2 × G × Fin Δ

/-- The view of the local-view assignment `W` at vertex `v`. -/
def view {G : Type*} [Group G] {Δ : ℕ}
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) :
    Fin Δ × Fin Δ → ZMod 2 := W v.1 v.2.1 v.2.2

/-- The A-neighbour of `v` in direction `i`. -/
def nA {G : Type*} [Group G] {Δ : ℕ} (A : Fin Δ → G) (v : Vtx G) (i : Fin Δ) : Vtx G :=
  if v.1 = 0 then (1, v.2.1, A i * v.2.2) else (0, v.2.1, (A i)⁻¹ * v.2.2)

/-- The B-neighbour of `v` in direction `j`. -/
def nB {G : Type*} [Group G] {Δ : ℕ} (B : Fin Δ → G) (v : Vtx G) (j : Fin Δ) : Vtx G :=
  if v.2.1 = 0 then (v.1, 1, v.2.2 * B j) else (v.1, 0, v.2.2 * (B j)⁻¹)

/-- The canonical index of the A-edge through `v` in direction `i`. -/
def aIdx {G : Type*} [Group G] {Δ : ℕ} (A : Fin Δ → G) (v : Vtx G) (i : Fin Δ) : EIdx G Δ :=
  if v.1 = 0 then (v.2.1, v.2.2, i) else (v.2.1, (A i)⁻¹ * v.2.2, i)

/-- The canonical index of the B-edge through `v` in direction `j`. -/
def bIdx {G : Type*} [Group G] {Δ : ℕ} (B : Fin Δ → G) (v : Vtx G) (j : Fin Δ) : EIdx G Δ :=
  if v.2.1 = 0 then (v.1, v.2.2, j) else (v.1, v.2.2 * (B j)⁻¹, j)

/-- The endpoint of the A-edge `(β,g,i)` in layer `α`. -/
def aEnd {G : Type*} [Group G] {Δ : ℕ} (A : Fin Δ → G) (p : EIdx G Δ) (α : Fin 2) : Vtx G :=
  (α, p.1, if α = 0 then p.2.1 else A p.2.2 * p.2.1)

/-- The endpoint of the B-edge `(α,g,j)` in layer `β`. -/
def bEnd {G : Type*} [Group G] {Δ : ℕ} (B : Fin Δ → G) (p : EIdx G Δ) (β : Fin 2) : Vtx G :=
  (p.1, β, if β = 0 then p.2.1 else p.2.1 * B p.2.2)

lemma nA_nA (A : Fin Δ → G) (v : Vtx G) (i : Fin Δ) : nA A (nA A v i) i = v := by
  obtain ⟨a,b,g⟩ := v
  fin_cases a <;> simp [nA, inv_mul_cancel_left, mul_inv_cancel_left]

lemma nB_nB (B : Fin Δ → G) (v : Vtx G) (j : Fin Δ) : nB B (nB B v j) j = v := by
  obtain ⟨a,b,g⟩ := v
  fin_cases b <;> simp [nB, mul_inv_cancel_right, inv_mul_cancel_right]

/-- The square through `v` in local coordinates `(i,j)` is the same square when described from any
of its four corners. -/
lemma nA_nB (A : Fin Δ → G) (B : Fin Δ → G) (v : Vtx G) (i j : Fin Δ) :
    nB B (nA A v i) j = nA A (nB B v j) i := by
  obtain ⟨a,b,g⟩ := v
  fin_cases a <;> fin_cases b <;> simp [nA, nB, mul_assoc]

lemma aIdx_aEnd (A : Fin Δ → G) (p : EIdx G Δ) (α : Fin 2) :
    aIdx A (aEnd A p α) p.2.2 = p := by
  obtain ⟨b,g,i⟩ := p
  fin_cases α <;> simp [aIdx, aEnd, inv_mul_cancel_left]

lemma aEnd_aIdx (A : Fin Δ → G) (v : Vtx G) (i : Fin Δ) : aEnd A (aIdx A v i) v.1 = v := by
  obtain ⟨a,b,g⟩ := v
  fin_cases a <;> simp [aIdx, aEnd]

lemma bIdx_bEnd (B : Fin Δ → G) (p : EIdx G Δ) (β : Fin 2) :
    bIdx B (bEnd B p β) p.2.2 = p := by
  obtain ⟨a,g,j⟩ := p
  fin_cases β <;> simp [bIdx, bEnd, mul_inv_cancel_right]

lemma bEnd_bIdx (B : Fin Δ → G) (v : Vtx G) (j : Fin Δ) : bEnd B (bIdx B v j) v.2.1 = v := by
  obtain ⟨a,b,g⟩ := v
  fin_cases b <;> simp [bIdx, bEnd]

/-- The A-edge through `v` in direction `i` is *pointwise* disputed at `(i,j)`. -/
def pdispA {G : Type*} [Group G] {Δ : ℕ} (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) (i j : Fin Δ) : Prop :=
  view W v (i, j) ≠ view W (nA A v i) (i, j)

/-- The B-edge through `v` in direction `j` is *pointwise* disputed at `(i,j)`. -/
def pdispB {G : Type*} [Group G] {Δ : ℕ} (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) (i j : Fin Δ) : Prop :=
  view W v (i, j) ≠ view W (nB B v j) (i, j)

/-- The A-edge through `v` in direction `i` is disputed. -/
def dispAE {G : Type*} [Group G] {Δ : ℕ} (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) (i : Fin Δ) : Prop :=
  ∃ j, pdispA A W v i j

/-- The B-edge through `v` in direction `j` is disputed. -/
def dispBE {G : Type*} [Group G] {Δ : ℕ} (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) (j : Fin Δ) : Prop :=
  ∃ i, pdispB B W v i j

/-- Number of disputed A-edges through `v`. -/
noncomputable def rA {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) : ℕ :=
  (Finset.univ.filter (fun i : Fin Δ => dispAE A W v i)).card

/-- Number of disputed B-edges through `v`. -/
noncomputable def rB {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) : ℕ :=
  (Finset.univ.filter (fun j : Fin Δ => dispBE B W v j)).card

lemma disputeA_aIdx (A : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) (i : Fin Δ) :
    disputeA A W (aIdx A v i).1 (aIdx A v i).2.1 (aIdx A v i).2.2 ↔ dispAE A W v i := by
  obtain ⟨a,b,g⟩ := v
  fin_cases a <;>
    simp [disputeA, dispAE, pdispA, view, aIdx, nA, ne_comm]

lemma disputeB_bIdx (B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) (j : Fin Δ) :
    disputeB B W (bIdx B v j).1 (bIdx B v j).2.1 (bIdx B v j).2.2 ↔ dispBE B W v j := by
  obtain ⟨a,b,g⟩ := v
  fin_cases b <;>
    simp [disputeB, dispBE, pdispB, view, bIdx, nB, ne_comm]

/-- Chain of equalities around a square: a pointwise dispute of an A-edge yields a pointwise
dispute of one of the other three edges of the square. -/
lemma pdispA_far (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) (i j : Fin Δ)
    (h : pdispA A W v i j) :
    pdispB B W v i j ∨ pdispA A W (nB B v j) i j ∨ pdispB B W (nA A v i) i j := by
  by_contra hc
  simp only [pdispA, pdispB, view, not_or, not_ne_iff] at hc h
  obtain ⟨h1, h2, h3⟩ := hc
  rw [nA_nB] at h3
  exact h (h1.trans (h2.trans h3.symm))

/-- Chain of equalities around a square, diagonal form: if the two diagonal neighbours of a
vertex disagree on a square, then one of the two far edges of that square is pointwise disputed. -/
lemma pdispB_far (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) (i j : Fin Δ)
    (h : view W (nA A v i) (i, j) ≠ view W (nB B v j) (i, j)) :
    pdispA A W (nB B v j) i j ∨ pdispB B W (nA A v i) i j := by
  by_contra hc
  simp only [pdispA, pdispB, view, not_or, not_ne_iff] at hc h
  obtain ⟨h1, h2⟩ := hc
  rw [nA_nB] at h2
  exact h (h2.trans h1.symm)

/-- Text-book form of the square chain. -/
lemma ne_or_ne_or_ne {α : Type*} {a b c d : α} (h : a ≠ b) : a ≠ c ∨ b ≠ d ∨ c ≠ d := by
  by_contra hc
  simp only [not_or, not_ne_iff] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  exact h (h1.trans (h3.trans h2.symm))

/-- Short form of the square chain. -/
lemma ne_or_ne_of_ne {α : Type*} {b c d : α} (h : b ≠ c) : b ≠ d ∨ c ≠ d := by
  by_contra hc
  simp only [not_or, not_ne_iff] at hc
  exact h (hc.1.trans hc.2.symm)

/-- The walk on a label class of A-edges: from `(0,g)` go to `(1, g * B j)`, from `(1,g)` go to
`(0, g * (B j)⁻¹)`, each with probability `1/Δ`. -/
noncomputable def classOpB {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G)
    (s : Fin 2 × G → ℝ) : Fin 2 × G → ℝ :=
  fun p => if p.1 = 0 then (∑ j, s (1, p.2 * B j)) / Δ else (∑ j, s (0, p.2 * (B j)⁻¹)) / Δ

/-- The walk on a label class of B-edges: from `(0,g)` go to `(1, A i * g)`, from `(1,g)` go to
`(0, (A i)⁻¹ * g)`, each with probability `1/Δ`. -/
noncomputable def classOpA {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A : Fin Δ → G)
    (s : Fin 2 × G → ℝ) : Fin 2 × G → ℝ :=
  fun p => if p.1 = 0 then (∑ i, s (1, A i * p.2)) / Δ else (∑ i, s (0, (A i)⁻¹ * p.2)) / Δ

/-- The vertex operator `M₀ = ½(M_A + M_B)`: a random step along a random A- or B-edge. -/
noncomputable def M0 {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (h : Vtx G → ℝ) : Vtx G → ℝ :=
  fun v => ((∑ i, h (nA A v i)) + (∑ j, h (nB B v j))) / (2 * Δ)

/-- Total number of disputed edges through `v`, as a real number. -/
noncomputable def Sfun {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) : ℝ :=
  (rA A W v : ℝ) + rB B W v

/-- The `D`-operator (`ℓ¹`-to-`ℓ²` step) applied to `1_R`: the average of `Sfun` over the
`2Δ` edges through a vertex, divided by `2Δ`. -/
noncomputable def gfun {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) : Vtx G → ℝ :=
  fun v => Sfun A B W v / (2 * Δ)

/-- `M₀` applied to `gfun`. -/
noncomputable def Qfun {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) : Vtx G → ℝ :=
  M0 A B (gfun A B W)

/-- Fraction of the squares through the A-edge `p` in which the parallel A-edge is disputed. -/
noncomputable def parA {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (p : EIdx G Δ) : ℝ :=
  ((Finset.univ.filter (fun j : Fin Δ => dispAE A W (nB B (0, p.1, p.2.1) j) p.2.2)).card : ℝ) / Δ

/-- Fraction of the squares through the B-edge `p` in which the parallel B-edge is disputed. -/
noncomputable def parB {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (p : EIdx G Δ) : ℝ :=
  ((Finset.univ.filter (fun i : Fin Δ => dispBE B W (nA A (p.1, 0, p.2.1) i) p.2.2)).card : ℝ) / Δ

/-- The quadratic form of the "parallel edge across a random square" operator: `⟨1_R, M‖ 1_R⟩`. -/
noncomputable def MparForm {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) : ℝ :=
  (∑ p : EIdx G Δ, if disputeA A W p.1 p.2.1 p.2.2 then parA A B W p else 0) +
    (∑ p : EIdx G Δ, if disputeB B W p.1 p.2.1 p.2.2 then parB A B W p else 0)

/-- The quadratic form of `M = Up ∘ M₀ ∘ Down`: `⟨1_R, M 1_R⟩`. -/
noncomputable def MForm {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) : ℝ :=
  (1/2) * ∑ v : Vtx G, Sfun A B W v * Qfun A B W v

/-- Replace the view at `v` by `w`, leaving all other views alone. -/
noncomputable def replaceView {G : Type*} [Group G] {Δ : ℕ}
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G)
    (w : Fin Δ × Fin Δ → ZMod 2) : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2) :=
  fun α β g => if (α, β, g) = v then w else W α β g

/-- The `1_R`-value of the "random endpoint, random neighbour, random incident edge" operator at
the canonical edge `p`: `½ (Q(v) + Q(v'))` with `v, v'` the endpoints of `p`. -/
noncomputable def MstepA {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (p : EIdx G Δ) : ℝ :=
  (Qfun A B W (0, p.1, p.2.1) + Qfun A B W (1, p.1, A p.2.2 * p.2.1)) / 2

/-- Same for a B-edge. -/
noncomputable def MstepB {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (p : EIdx G Δ) : ℝ :=
  (Qfun A B W (p.1, 0, p.2.1) + Qfun A B W (p.1, 1, p.2.1 * B p.2.2)) / 2

end Work.LT
