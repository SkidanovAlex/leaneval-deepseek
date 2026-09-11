import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.LinearAlgebra.Matrix.Hermitian

open Matrix
open Filter
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section

namespace EigenMult

/-!
# Graph-infrastructure specification (reachability-ball / walk / net lemmas)

Balls are defined by *reachability* (`∃ p : H.Walk c v, p.length ≤ r`) so that no junk
vertices (unreachable ones, for which `G.dist` would be `0`) appear.  Every lemma below is proved
in this file (helpers may be added; statements must not be changed).
-/

/-- adjacency of any graph is Hermitian. -/
lemma adj_isHerm_any {W : Type*} (H : SimpleGraph W) : (H.adjMatrix ℝ).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  exact SimpleGraph.isSymm_adjMatrix H

/-- the (reachability) ball of radius `r` around `c` in `G`. -/
def ballSet {V : Type*} (G : SimpleGraph V) (c : V) (r : ℕ) : Set V :=
  {v | ∃ p : G.Walk c v, p.length ≤ r}

/-- the graph induced on the ball. -/
def ballGraph {V : Type*} (G : SimpleGraph V) (c : V) (r : ℕ) :
    SimpleGraph (ballSet G c r) := G.induce (ballSet G c r)

/-- the center element of a ball. -/
def ballCenter {V : Type*} (G : SimpleGraph V) (c : V) (r : ℕ) : ballSet G c r :=
  ⟨c, ⟨SimpleGraph.Walk.nil, by simp⟩⟩

/-- membership in the ball means reachable by a walk of length `≤ r`. -/
lemma mem_ballSet_iff {V : Type*} (G : SimpleGraph V) (c : V) (r : ℕ) (v : V) :
    v ∈ ballSet G c r ↔ ∃ p : G.Walk c v, p.length ≤ r := by
  rfl

/-- adjacency in the ball is adjacency in `G`. -/
lemma ball_adj_iff {V : Type*} (G : SimpleGraph V) (c : V) (r : ℕ) {u v : ballSet G c r} :
    (ballGraph G c r).Adj u v ↔ G.Adj u.1 v.1 := by
  rfl

/-- the vertex type of a ball is nonempty. -/
lemma ballFinset_nonempty {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (c : V) (r : ℕ) :
    (Finset.univ : Finset (ballSet G c r)).Nonempty := by
  exact ⟨ballCenter G c r, Finset.mem_univ _⟩

/-- balls of larger radius contain smaller ones. -/
lemma ballSet_mono {V : Type*} (G : SimpleGraph V) (c : V) {r s : ℕ} (h : r ≤ s) :
    ballSet G c r ⊆ ballSet G c s := by
  intro v hv
  rcases hv with ⟨p, hp⟩
  exact ⟨p, le_trans hp h⟩

/-- every vertex visited by a walk of length `≤ 2r` starting and ending at `w` is in the ball
of radius `r` around `w`. -/
lemma closed_walk_vertices_in_ball {V : Type*} (H : SimpleGraph V) {w : V} {r : ℕ}
    {p : H.Walk w w} (hp : p.length ≤ 2 * r) : ∀ x ∈ p.support, x ∈ ballSet H w r := by
  classical
  intro x hx
  let t := p.takeUntil x hx
  let d := p.dropUntil x hx
  have hsum : t.length + d.length = p.length := by
    rw [show t.length = p.support.idxOf x from by
      simpa [t] using (SimpleGraph.Walk.length_takeUntil (p := p) (w := x) hx),
      show d.length = p.length - p.support.idxOf x from by
      simpa [d] using (SimpleGraph.Walk.length_dropUntil (p := p) (w := x) hx)]
    have hidx_lt : p.support.idxOf x < p.support.length := List.idxOf_lt_length_of_mem hx
    have hlen_supp : p.support.length = p.length + 1 := by simp
    have hidx_le : p.support.idxOf x ≤ p.length := by omega
    exact Nat.add_sub_of_le hidx_le
  by_cases ht_le : t.length ≤ r
  · simpa [ballSet] using ⟨t, ht_le⟩
  · have hd_le : d.length ≤ r := by
      omega
    simpa [ballSet] using ⟨d.reverse, by
      simpa [SimpleGraph.Walk.length_reverse] using hd_le⟩

/-- adjacency powers count walks. -/
lemma adjMatrix_pow_diag {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (w : V) (k : ℕ) :
    (H.adjMatrix ℝ ^ k) w w =
      (Fintype.card {p : H.Walk w w // p.length = k} : ℝ) := by
  classical
  rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk (α := ℝ) (n := k) (u := w) (v := w) (G := H)]
  congr

/-- inducing a walk to a subgraph preserves its length. -/
lemma Walk_length_induce {V : Type*} (G : SimpleGraph V) {s : Set V} {u v : V}
    (p : G.Walk u v) (hw : ∀ x ∈ p.support, x ∈ s) :
    (p.induce s hw).length = p.length := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih]

/-- the diagonal of an even power of the adjacency of `H` is bounded by the corresponding
entry of the ball graph. -/
lemma diag_pow_le_ball {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (w : V) (r : ℕ) :
    (H.adjMatrix ℝ ^ (2 * r)) w w ≤
      ((ballGraph H w r).adjMatrix ℝ ^ (2 * r)) (ballCenter H w r) (ballCenter H w r) := by
  classical
  -- every closed H-walk of length 2r from w stays inside `ballSet H w r`
  -- (closed_walk_vertices_in_ball), so it induces a closed walk of the ball graph.
  -- Mapping an induced walk back along the inclusion of the ball into H recovers the
  -- original walk (`SimpleGraph.Walk.map_induce`), so `f` has a left inverse and is
  -- injective.  The matrix entries are counts of such closed walks, by
  -- `adjMatrix_pow_diag`.
  let f : {p : H.Walk w w // p.length = 2 * r} →
          {q : (ballGraph H w r).Walk (ballCenter H w r) (ballCenter H w r)
            // q.length = 2 * r} := fun x =>
    ⟨x.1.induce (ballSet H w r)
        (fun v hv => closed_walk_vertices_in_ball H (le_of_eq x.2) v hv),
      (Walk_length_induce (G := H) (p := x.1) (s := ballSet H w r)
        (hw := fun v hv => closed_walk_vertices_in_ball H (le_of_eq x.2) v hv)).trans x.2⟩
  let g : {q : (ballGraph H w r).Walk (ballCenter H w r) (ballCenter H w r)
            // q.length = 2 * r} → {p : H.Walk w w // p.length = 2 * r} := fun q =>
    ⟨(q.1.map (SimpleGraph.Embedding.induce (ballSet H w r)).toHom : H.Walk w w),
      (SimpleGraph.Walk.length_map (SimpleGraph.Embedding.induce (ballSet H w r)).toHom
        q.1).trans q.2⟩
  have hgf : Function.LeftInverse g f := by
    intro a
    apply Subtype.ext
    change (a.1.induce (ballSet H w r)
        (fun v hv => closed_walk_vertices_in_ball H (le_of_eq a.2) v hv)).map
        (SimpleGraph.Embedding.induce (ballSet H w r)).toHom = a.1
    exact SimpleGraph.Walk.map_induce (s := ballSet H w r) (w := a.1)
      (fun v hv => closed_walk_vertices_in_ball H (le_of_eq a.2) v hv)
  have hinj : Function.Injective f := hgf.injective
  rw [adjMatrix_pow_diag, adjMatrix_pow_diag]
  exact_mod_cast (Fintype.card_le_of_injective f hinj)

/-- if `U₀ ⊆ U` is maximal (under inclusion) among subsets of `U` whose elements are pairwise
at distance `≥ d`, then every element of `U` is within distance `< d` of some element of `U₀`. -/
lemma maximal_separated_covering {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {d : ℕ} (hd : 0 < d) (U : Set V) (U0 : Finset V)
    (hU0_subset : ∀ u ∈ U0, u ∈ U)
    (hU0_sep : ∀ ⦃u v : V⦄, u ∈ U0 → v ∈ U0 → u ≠ v → d ≤ G.dist u v)
    (hmax : ∀ W : Finset V,
      (∀ u ∈ W, u ∈ U) → (∀ ⦃u v : V⦄, u ∈ W → v ∈ W → u ≠ v → d ≤ G.dist u v)
        → W ⊆ U0) :
    ∀ u : V, u ∈ U → ∃ v ∈ U0, G.dist u v < d := by
  classical
  intro u hu
  by_cases hu0 : u ∈ U0
  · refine ⟨u, hu0, ?_⟩
    rw [G.dist_self]
    exact hd
  · by_contra hcover
    push Not at hcover
    have hfar : ∀ v ∈ U0, d ≤ G.dist u v := by
      intro v hv
      exact hcover v hv
    let W : Finset V := insert u U0
    have hW_U : ∀ w ∈ W, w ∈ U := by
      intro w hw
      simp [W] at hw
      rcases hw with rfl | hwU0
      · exact hu
      · exact hU0_subset w hwU0
    have hW_sep : ∀ ⦃a b : V⦄, a ∈ W → b ∈ W → a ≠ b → d ≤ G.dist a b := by
      intro a b ha hb hab
      simp [W] at ha hb
      rcases ha with rfl | haU0
      · rcases hb with rfl | hbU0
        · exact False.elim (hab rfl)
        · exact hfar b hbU0
      · rcases hb with rfl | hbU0
        · rw [G.dist_comm]
          exact hfar a haU0
        · exact hU0_sep haU0 hbU0 hab
    have hsub : W ⊆ U0 := hmax W hW_U hW_sep
    have huW : u ∈ W := by simp [W]
    exact False.elim (hu0 (hsub huW))

/-- the ball as a finset of vertices. -/
noncomputable def ballFinset {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V) (r : ℕ) :
    Finset V := by
  classical
  exact Finset.univ.filter (fun v : V => v ∈ ballSet G c r)

lemma mem_ballFinset {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V) (r : ℕ) (v : V) :
    v ∈ ballFinset G c r ↔ v ∈ ballSet G c r := by
  classical
  simp [ballFinset]

/-- the ball of radius `r+1` is contained in the ball of radius `r` together with the union
of the radius-`r` balls centred at the neighbours of `c`. -/
lemma ballFinset_succ_subset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (c : V) (n : ℕ) :
    ballFinset G c (n + 1) ⊆
      ballFinset G c n ∪ (G.neighborFinset c).biUnion (fun u : V => ballFinset G u n) := by
  classical
  intro v hv
  rcases (mem_ballFinset G c (n + 1) v).1 hv with ⟨p, hp⟩
  rw [Finset.mem_union]
  by_cases hpn : p.length ≤ n
  · left
    exact (mem_ballFinset G c n v).2 ⟨p, hpn⟩
  · right
    have hlen : p.length = n + 1 := by omega
    have hpne : ¬ p.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      omega
    rcases (SimpleGraph.Walk.not_nil_iff.mp hpne) with ⟨u, hcu, q, hpq⟩
    have hqle : q.length ≤ n := by
      have hlen' : q.length + 1 = n + 1 := by
        simpa [hpq] using hlen
      omega
    rw [Finset.mem_biUnion]
    refine ⟨u, ?_, (mem_ballFinset G u n v).2 ⟨q, hqle⟩⟩
    simpa [SimpleGraph.mem_neighborFinset] using hcu

/-- `(Δ+1)^(n+1) + Δ*(Δ+1)^(n+1) = (Δ+1)^(n+2)`. -/
private lemma geom_pow_add (Δ n : ℕ) :
    (Δ + 1) ^ (n + 1) + Δ * (Δ + 1) ^ (n + 1) = (Δ + 1) ^ (n + 2) := by
  calc
    (Δ + 1) ^ (n + 1) + Δ * (Δ + 1) ^ (n + 1)
        = (Δ + 1) * (Δ + 1) ^ (n + 1) := by ring
    _ = (Δ + 1) ^ (n + 2) := by
      rw [Nat.mul_comm, ← pow_succ]

/-- the finset version of the bound. -/
lemma ballFinset_card_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {Δ : ℕ}
    (hdeg : ∀ v : V, G.degree v ≤ Δ) (c : V) (r : ℕ) :
    (ballFinset G c r).card ≤ (Δ + 1) ^ (r + 1) := by
  classical
  induction r generalizing c with
  | zero =>
      have hcard : (ballFinset G c 0).card = 1 := by
        have heq : ballFinset G c 0 = {c} := by
          ext v
          rw [mem_ballFinset]
          simp [ballSet]
        simp [heq]
      calc
        (ballFinset G c 0).card = 1 := hcard
        _ ≤ (Δ + 1) ^ (0 + 1) := by simp
  | succ n ih =>
      let N : Finset V := G.neighborFinset c
      let B : V → Finset V := fun u => ballFinset G u n
      have hinc : ballFinset G c (n + 1) ⊆ ballFinset G c n ∪ N.biUnion B := by
        simpa [N, B] using ballFinset_succ_subset G c n
      have hdegN : N.card ≤ Δ := by
        simpa [N] using hdeg c
      calc
        (ballFinset G c (n + 1)).card
            ≤ (ballFinset G c n ∪ N.biUnion B).card := Finset.card_le_card hinc
        _ ≤ (ballFinset G c n).card + (N.biUnion B).card := Finset.card_union_le _ _
        _ ≤ (ballFinset G c n).card + N.sum (fun u : V => (B u).card) := by
            exact Nat.add_le_add_left Finset.card_biUnion_le _
        _ ≤ (Δ + 1) ^ (n + 1) + N.sum (fun u : V => (Δ + 1) ^ (n + 1)) := by
            exact Nat.add_le_add (ih c)
              (Finset.sum_le_sum (by intro u hu; exact ih u))
        _ ≤ (Δ + 1) ^ (n + 1) + Δ * (Δ + 1) ^ (n + 1) := by
            rw [Finset.sum_const_nat (fun u hu => rfl)]
            exact Nat.add_le_add_left (Nat.mul_le_mul_right ((Δ + 1) ^ (n + 1)) hdegN) _
        _ = (Δ + 1) ^ (n + 2) := geom_pow_add Δ n

/-- the size of a ball is bounded by `(Δ+1)^(r+1)` under a maximum-degree bound. -/
lemma ball_card_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {Δ : ℕ}
    (hdeg : ∀ v : V, G.degree v ≤ Δ) (c : V) (r : ℕ) :
    Fintype.card (ballSet G c r) ≤ (Δ + 1) ^ (r + 1) := by
  classical
  rw [← Set.toFinset_card (ballSet G c r)]
  rw [show (ballSet G c r).toFinset = ballFinset G c r by
    ext v
    simp [ballFinset]]
  exact ballFinset_card_le G hdeg c r

/-- If `p` is a shortest `u → v` walk, then the vertex reached after `a` steps is at
distance `a` from `u`. -/
private lemma dist_getVert_of_shortest {V : Type*} (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v) (h : p.length = G.dist u v) (a : ℕ) (ha : a ≤ p.length) :
    G.dist u (p.getVert a) = a := by
  classical
  have hlen : (p.take a).length = a := by
    rw [SimpleGraph.Walk.take_length, Nat.min_eq_left ha]
  have hsub : (p.take a).IsSubwalk p := SimpleGraph.Walk.isSubwalk_take p a
  have h1 := SimpleGraph.length_eq_dist_of_subwalk (p₁ := p) (p₂ := p.take a) h hsub
  -- h1 : (p.take a).length = G.dist u (p.getVert a)
  rw [hlen] at h1
  exact h1.symm

/-- If `p` is a shortest `u → v` walk, then the vertices reached after `a` and after `b`
steps (`a ≤ b ≤ p.length`) are at distance `b - a`. -/
private lemma dist_getVert_getVert_of_shortest {V : Type*} (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v) (h : p.length = G.dist u v) (a b : ℕ) (ha : a ≤ b) (hb : b ≤ p.length) :
    G.dist (p.getVert a) (p.getVert b) = b - a := by
  classical
  let q := p.drop a
  have hqlen : q.length = p.length - a := by
    simp [q]
  have hle : b - a ≤ q.length := by
    simp [q, hqlen]
    omega
  have hlen : (q.take (b - a)).length = b - a := by
    rw [SimpleGraph.Walk.take_length, Nat.min_eq_left hle]
  have hsub : (q.take (b - a)).IsSubwalk p := by
    exact (SimpleGraph.Walk.isSubwalk_take q (b - a)).trans (SimpleGraph.Walk.isSubwalk_drop p a)
  have h1 := SimpleGraph.length_eq_dist_of_subwalk (p₁ := p) (p₂ := q.take (b - a)) h hsub
  -- h1 : (q.take (b-a)).length = G.dist (p.getVert a) (q.getVert (b-a))
  rw [hlen] at h1
  have hz : q.getVert (b - a) = p.getVert b := by
    change (p.drop a).getVert (b - a) = p.getVert b
    rw [SimpleGraph.Walk.drop_getVert]
    rw [Nat.add_sub_of_le ha]
  rw [hz] at h1
  exact h1.symm

/-- If `p` is a shortest `u → v` walk, then the vertex reached after `a` steps is at
distance `p.length - a` from `v`. -/
private lemma dist_getVert_end_of_shortest {V : Type*} (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v) (h : p.length = G.dist u v) (a : ℕ) (_ha : a ≤ p.length) :
    G.dist (p.getVert a) v = p.length - a := by
  classical
  let q := p.drop a
  have hlen : q.length = p.length - a := by
    simp [q]
  have hsub : q.IsSubwalk p := SimpleGraph.Walk.isSubwalk_drop p a
  have h1 := SimpleGraph.length_eq_dist_of_subwalk (p₁ := p) (p₂ := q) h hsub
  -- h1 : q.length = G.dist (p.getVert a) v
  rw [hlen] at h1
  exact h1.symm

/-- transitivity of "on the geodesic from `w`" (additive form, using only triangle
inequality; valid in any graph). -/
private lemma between_trans {V : Type*} (G : SimpleGraph V)
    (hconn : ∀ i j : V, G.Reachable i j) {w a b c : V}
    (h1 : G.dist w a + G.dist a b = G.dist w b)
    (h2 : G.dist w b + G.dist b c = G.dist w c) :
    G.dist w a + G.dist a c = G.dist w c := by
  classical
  apply le_antisymm
  · calc
      G.dist w a + G.dist a c ≤ G.dist w a + (G.dist a b + G.dist b c) := by
        exact Nat.add_le_add_left ((hconn a b).dist_triangle_left c) _
      _ = G.dist w c := by omega
  · exact (hconn w a).dist_triangle_left c

/-- recursion used in `net_exists`: peel vertices lying "beyond" a centre `u` chosen
`r` steps from the farthest reachable vertex of the current set. -/
private lemma net_rec {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : ∀ i j : V, G.Reachable i j) (w : V) (r : ℕ) (A : Finset V)
    (hAnc : ∀ x ∈ A, ∀ y : V, G.dist w y + G.dist y x = G.dist w x → y ∈ A) :
    ∃ S : Finset V, S.card ≤ A.card / (r + 1) + 1 ∧
      (∀ z ∈ A, ∃ s ∈ S, G.dist s z ≤ r) := by
  classical
  let P : ℕ → Prop := fun m => ∀ (B : Finset V), B.card = m →
      (∀ x ∈ B, ∀ y : V, G.dist w y + G.dist y x = G.dist w x → y ∈ B) →
      ∃ S : Finset V, S.card ≤ B.card / (r + 1) + 1 ∧
        (∀ z ∈ B, ∃ s ∈ S, G.dist s z ≤ r)
  have hmain : ∀ m : ℕ, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro B hBcard hAncB
      by_cases hBempty : B = ∅
      · subst hBempty
        refine ⟨∅, ?_, ?_⟩
        · simp
        · intro z hz
          simp at hz
      · have hBne : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hBempty
        obtain ⟨x, hxB, hxmax⟩ := Finset.exists_max_image B (fun z => G.dist w z) hBne
        by_cases hxDr : G.dist w x ≤ r
        · refine ⟨{w}, ?_, ?_⟩
          · simp
          · intro z hz
            refine ⟨w, by simp, ?_⟩
            exact le_trans (hxmax z hz) hxDr
        · let D := G.dist w x
          have hDgt : r < D := by
            dsimp [D]
            exact lt_of_not_ge hxDr
          have hDge : r + 1 ≤ D := by omega
          obtain ⟨p, hp⟩ := (hconn w x).exists_walk_length_eq_dist
          have hpD : p.length = D := by
            simpa [D] using hp
          let n := D - r
          have hn_le : n ≤ p.length := by
            dsimp [n]
            rw [hpD]
            omega
          have hn_le_D : n ≤ D := by
            dsimp [n]
            omega
          let u := p.getVert n
          have hdwu : G.dist w u = n := by
            dsimp [u]
            exact dist_getVert_of_shortest G p hpD n hn_le
          -- for j ≤ r, the vertices z_j = p.getVert (n+j) along p beyond u
          let zfun : ℕ → V := fun j => p.getVert (n + j)
          have hd_uz : ∀ j : ℕ, j ≤ r → G.dist u (zfun j) = j := by
            intro j hj
            dsimp [u, zfun]
            have hb : n + j ≤ p.length := by
              rw [hpD]
              dsimp [n]
              omega
            have hd := dist_getVert_getVert_of_shortest G p hpD n (n + j) (by omega) hb
            -- hd : G.dist (p.getVert n) (p.getVert (n + j)) = (n + j) - n
            -- want = j
            have : (n + j) - n = j := by omega
            simpa [this] using hd
          have hd_wz : ∀ j : ℕ, j ≤ r → G.dist w (zfun j) = n + j := by
            intro j hj
            dsimp [zfun]
            have hb : n + j ≤ p.length := by
              rw [hpD]
              dsimp [n]
              omega
            exact dist_getVert_of_shortest G p hpD (n + j) hb
          have hbetween_zx : ∀ j : ℕ, j ≤ r →
              G.dist w (zfun j) + G.dist (zfun j) x = D := by
            intro j hj
            have hb : n + j ≤ p.length := by
              rw [hpD]
              dsimp [n]
              omega
            have hdzx : G.dist (zfun j) x = p.length - (n + j) := by
              simpa [zfun] using (dist_getVert_end_of_shortest G p hpD (n + j) hb)
            have hdwz := hd_wz j hj
            omega
          let RemB := B.filter (fun z => G.dist w u + G.dist u z = G.dist w z)
          let B' := B.filter (fun z => ¬ (G.dist w u + G.dist u z = G.dist w z))
          have hAncB' : ∀ x' ∈ B', ∀ y : V,
              G.dist w y + G.dist y x' = G.dist w x' → y ∈ B' := by
            intro x' hxB' y hbyx'
            have hxB'mem : x' ∈ B := by
              simpa [B'] using (Finset.mem_filter.mp hxB').1
            have hyB : y ∈ B := hAncB x' hxB'mem y hbyx'
            refine Finset.mem_filter.mpr ⟨hyB, ?_⟩
            intro huy
            have hux' : G.dist w u + G.dist u x' = G.dist w x' :=
              between_trans G hconn huy hbyx'
            exact (Finset.mem_filter.mp hxB').2 hux'
          have hRemB_card : (r + 1) ≤ RemB.card := by
            -- the r+1 vertices zfun j (j ≤ r) are pairwise distinct members of RemB
            let T := (Finset.range (r + 1)).image zfun
            have hTsub : T ⊆ RemB := by
              intro t ht
              rcases Finset.mem_image.mp ht with ⟨j, hj, rfl⟩
              have hjr : j ≤ r := by
                simpa using (Finset.mem_range.mp hj)
              refine Finset.mem_filter.mpr ⟨?_, ?_⟩
              · have hzjx := hbetween_zx j hjr
                have hzB : zfun j ∈ B := hAncB x hxB (zfun j) (by simpa [D] using hzjx)
                exact hzB
              · have hduz := hd_uz j hjr
                have hdwz := hd_wz j hjr
                have hdwu' : G.dist w u = n := hdwu
                omega
            have hTinj : Set.InjOn zfun (↑(Finset.range (r + 1)) : Set ℕ) := by
              intro a ha b hb hz
              -- zfun a = zfun b → dist u (zfun a) = dist u (zfun b) → a = b
              have hra : a ≤ r := by simpa using (Finset.mem_range.mp ha)
              have hrb : b ≤ r := by simpa using (Finset.mem_range.mp hb)
              have hda := hd_uz a hra
              have hdb := hd_uz b hrb
              calc
                a = G.dist u (zfun a) := hda.symm
                _ = G.dist u (zfun b) := by rw [hz]
                _ = b := hdb
            have hTcard : T.card = r + 1 := by
              change ((Finset.range (r + 1)).image zfun).card = r + 1
              rw [Finset.card_image_of_injOn hTinj]
              simp
            -- RemB.card ≥ T.card = r + 1
            rw [← hTcard]
            exact Finset.card_le_card hTsub
          have hRemB_le : RemB.card ≤ B.card := by
            exact Finset.card_le_card (Finset.filter_subset _ B)
          have hBcard_ge : (r + 1) ≤ B.card := le_trans hRemB_card hRemB_le
          have hcard_sum : RemB.card + B'.card = B.card := by
            change (B.filter (fun z => G.dist w u + G.dist u z = G.dist w z)).card +
              (B.filter (fun z => ¬ (G.dist w u + G.dist u z = G.dist w z))).card = B.card
            exact Finset.card_filter_add_card_filter_not (s := B)
              (fun z => G.dist w u + G.dist u z = G.dist w z)
          have hB'card_le : B'.card ≤ B.card - (r + 1) := by
            omega
          have hB'lt : B'.card < B.card := by
            omega
          rcases ih B'.card (by omega) B' rfl hAncB' with ⟨S', hS'card, hS'cov⟩
          let S := insert u S'
          refine ⟨S, ?_, ?_⟩
          · -- cardinality of S
            have hcardS : S.card ≤ S'.card + 1 := by
              dsimp [S]
              exact Finset.card_insert_le u S'
            have hkmul : (B'.card / (r + 1) + 1) * (r + 1) ≤ B.card := by
              have hk1 : (B'.card / (r + 1)) * (r + 1) ≤ B'.card := Nat.div_mul_le_self B'.card (r + 1)
              have hk2 : (B'.card / (r + 1)) * (r + 1) ≤ B.card - (r + 1) := le_trans hk1 hB'card_le
              have hk3 : (B'.card / (r + 1) + 1) * (r + 1) =
                  (B'.card / (r + 1)) * (r + 1) + (r + 1) := by ring
              rw [hk3]
              omega
            have hdiv_add : B'.card / (r + 1) + 1 ≤ B.card / (r + 1) := by
              exact (Nat.le_div_iff_mul_le (by omega : 0 < r + 1)).mpr hkmul
            calc
              S.card ≤ S'.card + 1 := hcardS
              _ ≤ B'.card / (r + 1) + 1 + 1 := Nat.add_le_add_right hS'card 1
              _ = B'.card / (r + 1) + 2 := by omega
              _ ≤ B.card / (r + 1) + 1 := by omega
          · -- coverage
            intro z hzB
            by_cases hzRem : z ∈ RemB
            · refine ⟨u, by simp [S], ?_⟩
              -- coverage of RemB by u
              have hzp := (Finset.mem_filter.mp hzRem).2
              have hzD : G.dist w z ≤ D := by
                have hzB' : z ∈ B := (Finset.mem_filter.mp hzRem).1
                exact hxmax z hzB'
              have hnD : D = n + r := by
                dsimp [n]
                omega
              dsimp [u] at hdwu hzp hzD ⊢
              omega
            · have hzB' : z ∈ B' := by
                refine Finset.mem_filter.mpr ⟨hzB, ?_⟩
                intro hpz
                exact hzRem (Finset.mem_filter.mpr ⟨hzB, hpz⟩)
              rcases hS'cov z hzB' with ⟨s, hsS', hsdist⟩
              exact ⟨s, by simp [S, hsS'], hsdist⟩
  exact hmain A.card A rfl hAnc

/-- a connected graph has a small `r`-net: every vertex within distance `r` of the net,
with at most `n/(r+1) + 1` net vertices. -/
lemma net_exists {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : ∀ i j : V, G.Reachable i j) (r : ℕ) :
    ∃ S : Finset V, S.card ≤ (Fintype.card V) / (r + 1) + 1 ∧
      ∀ v : V, ∃ s ∈ S, G.dist s v ≤ r := by
  classical
  by_cases hV : (Finset.univ : Finset V).Nonempty
  · rcases hV with ⟨w, hw⟩
    rcases net_rec G hconn w r (Finset.univ)
      (by intro x hx y hy; simp) with ⟨S, hScard, hScov⟩
    refine ⟨S, ?_, ?_⟩
    · simpa using hScard
    · intro v
      exact hScov v (by simp)
  · refine ⟨∅, ?_, ?_⟩
    · simp
    · intro v
      exfalso
      exact hV ⟨v, by simp⟩

/-- a vertex at distance `r+1` from `c` has a neighbour at distance exactly `r`. -/
lemma exists_neighbor_dist_pred {V : Type*} (G : SimpleGraph V) {c v : V} {r : ℕ}
    (hconn : G.Reachable c v) (hv : G.dist c v = r + 1) :
    ∃ u : V, G.Adj u v ∧ G.dist c u = r := by
  classical
  -- take a shortest walk p : c → v of length r + 1; it ends with an edge u → v whose
  -- prefix of length r is a shortest c → u walk (a shorter one would shorten p).
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist
  have hpl : p.length = r + 1 := hp.trans hv
  have hpne : ¬ p.Nil := by
    exact SimpleGraph.Walk.not_nil_iff_lt_length.mpr (by omega)
  obtain ⟨x0, h0, q0, hp_eq⟩ := (SimpleGraph.Walk.not_nil_iff.mp hpne)
  obtain ⟨x, q, h', hpq⟩ := SimpleGraph.Walk.exists_cons_eq_concat h0 q0
  have hpq' : p = q.concat h' := hp_eq.trans hpq
  have hqlen : q.length = r := by
    have hlen : (q.concat h').length = p.length := by rw [hpq']
    rw [SimpleGraph.Walk.length_concat] at hlen
    omega
  refine ⟨x, h', ?_⟩
  have hupper : G.dist c x ≤ r := by
    simpa [hqlen] using (SimpleGraph.dist_le q)
  have hlow : r ≤ G.dist c x := by
    by_contra hlt
    have hdlt : G.dist c x < r := lt_of_not_ge hlt
    obtain ⟨w1, hw1⟩ := q.reachable.exists_walk_length_eq_dist
    have hlong : (w1.concat h').length ≤ r := by
      rw [SimpleGraph.Walk.length_concat, hw1]
      omega
    have hdv : G.dist c v ≤ (w1.concat h').length := SimpleGraph.dist_le (w1.concat h')
    rw [hv] at hdv
    omega
  omega

/-- walks in an induced subgraph are walks in the ambient graph of the same length. -/
lemma induced_walk_map {V : Type*} (G : SimpleGraph V) (s : Set V) {u v : s}
    (p : (G.induce s).Walk u v) : ∃ q : G.Walk u.1 v.1, q.length = p.length := by
  classical
  refine ⟨p.map (SimpleGraph.Embedding.induce s).toHom, by
    simpa using (SimpleGraph.Walk.length_map (SimpleGraph.Embedding.induce s).toHom p)⟩

/-- if `u` is reachable from `c` by a walk of length `≤ r` then `G.dist c u ≤ r`. -/
lemma dist_le_of_walk_le {V : Type*} (G : SimpleGraph V) {c u : V} {r : ℕ}
    (p : G.Walk c u) (hp : p.length ≤ r) : G.dist c u ≤ r := by
  exact le_trans (G.dist_le p) hp

/-- a shortest walk realises the distance (connected ambient). -/
lemma walk_of_dist {V : Type*} (G : SimpleGraph V) (hconn : ∀ i j : V, G.Reachable i j)
    (u v : V) : ∃ p : G.Walk u v, p.length = G.dist u v := by
  exact (hconn u v).exists_walk_length_eq_dist

end EigenMult

end

end Submission
