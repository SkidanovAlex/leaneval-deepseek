import Submission.Work.FrontierSide

open OptimalMoebius Topology ContDiff
open Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Target (A) — connected-arc direction constancy (GREEN)

The finite-link heart (`chain_frontier_directions_parallel`, FrontierSide)
relates the half-disk directions of the ENDPOINTS of any finite chain of
overlapping half-disks.  This file carries Target (A) to the connected
arc, and proves it.

## Design note: local constancy of the PROJECTIVE direction (no
compactness, no radius regularity)
The naive routes — cover a path `γ : [0,1] → frontier` by the half-disks
and extract a finite chain, or show reachability-by-chains is closed —
both stumble on the same obstruction: the half-disk radius `ρ(e)` need
not be bounded below along the path, so a greedy chain can stall strictly
before the target (example `γ(t) = t`, `ρ(t) = (1−t)/2` for `t < 1`),
and the last link of a chain approaching a limit point is governed by the
radius at the CURRENT point, not at the limit.

The clean resolution: only LOCAL constancy is needed.  The unoriented
direction `d(e) := {w e, −w e}` is locally constant on the frontier set —
if `e, e' ∈ K` with `‖e' − e‖ < ρ e`, the overlap propagation
(`adjacent_frontier_directions_parallel`) forces `w e = ± w e'`.  Fixing
`e₀`, the class set `A := {x | w x = ± w e₀}` and its complement `B` are
both relatively open in `K` (each is a union of half-disk balls over its
own points), disjoint, with `A ∋ e₀`; the preconnectedness of `K`
forbids a split, so `B = ∅`.  This is the standard "a locally constant
function on a preconnected set is constant", applied to the projective
direction — no closedness/limit step, no radius behaviour.

## Contents
* `chain_frontier_directions_parallel_bdd` — the bounded-natural version
  of the chain theorem (data only at indices `≤ n`, links `i < n`),
  proved by induction directly;
* `sign_symm` — `u = ±v` gives `v = ±u`;
* **`preconnected_frontier_directions_parallel`** — **TARGET (A) GREEN**:
  a PRECONNECTED set `K ⊆ frontier (flatComponent f p)` carrying per-point
  half-disk data has the half-disk direction constant up to sign:
  `w e₁ = ± w e₂` for all `e₁, e₂ ∈ K` (the class-set clopen argument
  above).
-/

noncomputable section
namespace Submission.PaperBand

/-- **Bounded finite-chain direction theorem**: the natural-index chain
theorem with hypotheses only at the finitely many chain points
(`∀ i ≤ n` for the data, `∀ i < n` for the links).  Proved by induction:
the step applies `adjacent_frontier_directions_parallel` between indices
`m` and `m+1` and composes with the inductive hypothesis via
`sign_trans`. -/
theorem chain_frontier_directions_parallel_bdd {f : ℝ² → ℝ³} {p : ℝ²} (n : ℕ)
    {e : ℕ → ℝ²} {w : ℕ → ℝ²} {ρ : ℕ → ℝ}
    (heS : ∀ i, i ≤ n → e i ∈ stripInterior)
    (heF : ∀ i, i ≤ n → e i ∈ frontier (flatComponent f p))
    (hw : ∀ i, i ≤ n → ‖w i‖ = 1) (hρ : ∀ i, i ≤ n → 0 < ρ i)
    (heq : ∀ i, i ≤ n → ∀ z : ℝ², z ∈ Metric.ball (e i) (ρ i) →
      (z ∈ flatComponent f p ↔ signedLineFunc (e i) (w i) z < 0))
    (hov : ∀ i, i < n → ‖e (i + 1) - e i‖ < ρ i) :
    w 0 = w n ∨ w 0 = - w n := by
  induction n with
  | zero =>
      left
      rfl
  | succ m ih =>
      have ih' : w 0 = w m ∨ w 0 = - w m := by
        apply ih
        · intro i hi
          exact heS i (le_trans hi (Nat.le_succ m))
        · intro i hi
          exact heF i (le_trans hi (Nat.le_succ m))
        · intro i hi
          exact hw i (le_trans hi (Nat.le_succ m))
        · intro i hi
          exact hρ i (le_trans hi (Nat.le_succ m))
        · intro i hi z hz
          exact heq i (le_trans hi (Nat.le_succ m)) z hz
        · intro i hi
          exact hov i (lt_trans hi (Nat.lt_succ_self m))
      have hm : w m = w (m + 1) ∨ w m = - w (m + 1) :=
        adjacent_frontier_directions_parallel (e₁ := e m) (e₂ := e (m + 1))
          (heF (m + 1) (Nat.le_refl (m + 1))) (hw m (Nat.le_succ m)) (hρ m (Nat.le_succ m))
          (heq m (Nat.le_succ m)) (hw (m + 1) (Nat.le_refl (m + 1))) (hρ (m + 1) (Nat.le_refl (m + 1)))
          (heq (m + 1) (Nat.le_refl (m + 1))) (hov m (Nat.lt_succ_self m))
      exact sign_trans ih' hm

/-- **Sign symmetry**: `u = ±v` gives `v = ±u`. -/
lemma sign_symm {u v : ℝ²} (h : u = v ∨ u = -v) : v = u ∨ v = -u := by
  rcases h with h | h
  · left
    exact h.symm
  · right
    calc
      v = -(-v) := by simp
      _ = -u := by rw [h]

/-- **Target (A): direction constancy on a preconnected frontier set**.
A preconnected set `K` of frontier points of `C = flatComponent f p`
(each `e ∈ K` carrying its half-disk data `(w e, ρ e)` — unit `w e`,
radius `ρ e > 0`, and `z ∈ C ⟺ signedLineFunc e (w e) z < 0` inside
`B(e, ρ e)`) has the half-disk direction constant UP TO SIGN:
`w e₁ = ± w e₂` for all `e₁, e₂ ∈ K`.

Proof (no compactness, no radius regularity): the unoriented direction
`d(e) := {w e, −w e}` is LOCALLY CONSTANT on `K`: if `e, e' ∈ K` with
`‖e' − e‖ < ρ e`, the overlap propagation
`adjacent_frontier_directions_parallel` forces `w e = ± w e'`.  Fixing
`e₀ ∈ K`, the class set `A := {x ∈ K | w x = ± w e₀}` and its complement
`B := K ∖ A` are both RELATIVELY OPEN in `K` (each is a union of
half-disk balls over its own points), disjoint, and `A ∋ e₀`; the
preconnectedness of `K` forbids two nonempty disjoint relatively open
sets covering it, so `B = ∅` and `K ⊆ A`.  (This is the standard
"locally constant on a preconnected set is constant" argument, applied
to the projective direction.) -/
theorem preconnected_frontier_directions_parallel {f : ℝ² → ℝ³} {p : ℝ²}
    {K : Set ℝ²} (hKpre : IsPreconnected K) (hKsub : K ⊆ frontier (flatComponent f p))
    {w : ℝ² → ℝ²} {ρ : ℝ² → ℝ}
    (hw : ∀ e, e ∈ K → ‖w e‖ = 1) (hρ : ∀ e, e ∈ K → 0 < ρ e)
    (heq : ∀ e, e ∈ K → ∀ z : ℝ², z ∈ Metric.ball e (ρ e) →
      (z ∈ flatComponent f p ↔ signedLineFunc e (w e) z < 0)) :
    ∀ e₁, e₁ ∈ K → ∀ e₂, e₂ ∈ K → w e₁ = w e₂ ∨ w e₁ = - w e₂ := by
  by_cases hK : K.Nonempty
  · rcases hK with ⟨e₀, he₀K⟩
    let A : Set ℝ² := {x : ℝ² | x ∈ K ∧ (w x = w e₀ ∨ w x = - w e₀)}
    let B : Set ℝ² := {x : ℝ² | x ∈ K ∧ ¬ (w x = w e₀ ∨ w x = - w e₀)}
    let Uₐ : Set ℝ² := {x : ℝ² | ∃ a ∈ A, x ∈ Metric.ball a (ρ a)}
    let Ub : Set ℝ² := {x : ℝ² | ∃ b ∈ B, x ∈ Metric.ball b (ρ b)}
    -- overlap propagation: two K-points within the radius agree up to sign
    have hlink0 : ∀ a x : ℝ², a ∈ K → x ∈ K → x ∈ Metric.ball a (ρ a) →
        w a = w x ∨ w a = - w x := by
      intro a x haK hxK hxball
      exact adjacent_frontier_directions_parallel (e₁ := a) (e₂ := x)
        (hKsub hxK) (hw a haK) (hρ a haK) (heq a haK)
        (hw x hxK) (hρ x hxK) (heq x hxK) (by
          rw [Metric.mem_ball, dist_eq_norm] at hxball
          exact hxball)
    have hAeq : A = K ∩ Uₐ := by
      apply le_antisymm
      · intro x hx
        exact ⟨hx.1, x, hx, Metric.mem_ball_self (hρ x hx.1)⟩
      · intro x hx
        rcases hx with ⟨hxK, hxU⟩
        rcases hxU with ⟨a, haA, hxball⟩
        refine ⟨hxK, ?_⟩
        have hlink' := hlink0 a x haA.1 hxK hxball
        exact sign_trans (sign_symm hlink') haA.2
    have hBeq : B = K ∩ Ub := by
      apply le_antisymm
      · intro x hx
        exact ⟨hx.1, x, hx, Metric.mem_ball_self (hρ x hx.1)⟩
      · intro x hx
        rcases hx with ⟨hxK, hxU⟩
        rcases hxU with ⟨b, hbB, hxball⟩
        refine ⟨hxK, ?_⟩
        intro hxA
        have hlink' := hlink0 b x hbB.1 hxK hxball
        have hbclass : w b = w e₀ ∨ w b = - w e₀ := sign_trans hlink' hxA
        exact hbB.2 hbclass
    have hUopenₐ : IsOpen Uₐ := by
      rw [show Uₐ = ⋃ a ∈ A, Metric.ball a (ρ a) by
        ext x
        simp [Uₐ]]
      exact isOpen_biUnion (fun a ha => Metric.isOpen_ball)
    have hUopenb : IsOpen Ub := by
      rw [show Ub = ⋃ b ∈ B, Metric.ball b (ρ b) by
        ext x
        simp [Ub]]
      exact isOpen_biUnion (fun b hb => Metric.isOpen_ball)
    have hcov : K ⊆ Uₐ ∪ Ub := by
      intro x hxK
      by_cases hxA : x ∈ A
      · left
        refine ⟨x, hxA, Metric.mem_ball_self (hρ x hxK)⟩
      · right
        refine ⟨x, ⟨hxK, (fun hc => hxA ⟨hxK, hc⟩)⟩, Metric.mem_ball_self (hρ x hxK)⟩
    have hAne : (K ∩ Uₐ).Nonempty := by
      rw [← hAeq]
      exact ⟨e₀, ⟨he₀K, Or.inl rfl⟩⟩
    have hBempty : (K ∩ Ub).Nonempty → False := by
      intro hbne
      rcases hKpre Uₐ Ub hUopenₐ hUopenb hcov hAne hbne with ⟨z, hz⟩
      have hzK : z ∈ K := hz.1
      have hzUa : z ∈ Uₐ := hz.2.1
      have hzUb : z ∈ Ub := hz.2.2
      have hzA : z ∈ A := by
        rw [hAeq]
        exact ⟨hzK, hzUa⟩
      have hzB : z ∈ B := by
        rw [hBeq]
        exact ⟨hzK, hzUb⟩
      exact hzB.2 hzA.2
    -- the class of e₀ is all of K
    have hclass : ∀ e : ℝ², e ∈ K → w e = w e₀ ∨ w e = - w e₀ := by
      intro e heK
      by_contra hnot
      have heB : e ∈ B := ⟨heK, hnot⟩
      have heUb : e ∈ Ub := by
        refine ⟨e, heB, Metric.mem_ball_self (hρ e heK)⟩
      exact hBempty ⟨e, heK, heUb⟩
    intro e₁ he₁K e₂ he₂K
    have h₁ := hclass e₁ he₁K
    have h₂ := hclass e₂ he₂K
    exact sign_trans h₁ (sign_symm h₂)
  · intro e₁ he₁K
    exfalso
    exact hK ⟨e₁, he₁K⟩


end Submission.PaperBand
