import Mathlib
import Submission.OChartGlue
import Submission.OChartTwoStep
import Submission.IntervalChartU

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 800000

/-!
# One-step extension of the interval-coordinate transport along the walk:
the composite over two junctions is the genuine class-coordinate transport
(S117)

The interval-chain exhaustion (`Uₙ` covering each exhaustion step `Eₙ`)
is assembled by induction along the S115 component walk: at every
junction the S116 hinge gives a monotone piece (`oChartJunctionMonoPiece`,
`oChart_trace_overlap_monotoneNbhd`), and the S111 finite-chain transport
(`ChainTransport`) provides the monotone/injective coordinate transport
over aligned stretches.  What remains at each extension step is the
SEMANTIC content: the transported value must be the genuine coordinate of
the same trisecant class in the chart reached — the hinge conjuncts at a
single junction give this one-junction step (`oChartNbhd_piece_coordinate`),
and the present module proves the ATOMIC EXTENSION over two junctions:

**`oChart_two_step_composite_class_coordinate`**: with S102 monotone
neighbourhoods at two consecutive transitions `ch₁ → ch₂ → ch₃` and a
first-piece parameter whose transport lands in the second piece (the
S110 `oChartTwoStepMap` step domain), the composite transport value is
the `ch₃`-coordinate of the same class as the original `ch₁`-parameter:
the class-coordinate semantics survive the two-step composition (each
piece's value is the next chart's coordinate of the same class — S102
`oChartNbhd_piece_coordinate` at both steps — and the transported
parameter equals the `ch₂`-coordinate of the class by value).

Together with the S110 monotonicity/injectivity of the composite
(`oChart_two_step_composite`), this is the one-step extension lemma of
the exhaustion induction: from a start parameter whose class is followed
through a finite chain of walk-adjacent charts (S111), each additional
junction composes one more piece and keeps the transport equal to the
genuine class coordinate; the interval-charted `Uₙ` covering `Eₙ` is
built by carrying this coordinate along the walk and reading off the
trace unions (recorded as the next slice in the ROADMAP session log).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-- **Composite transport is the class-coordinate transport (atomic
one-step extension).**  With S102 monotone neighbourhoods at two
consecutive transitions (`ch₁ → ch₂`, `ch₂ → ch₃`) and a first-piece
parameter `u` whose transport lands in the second piece, the composite
value (`oChartTwoStepMap`) is the `ch₃`-coordinate of the same trisecant
class as the `ch₁`-parameter of `u`: the coordinate semantics survive the
composition (the value of the first piece is the `ch₂`-coordinate of the
class — S102 `oChartNbhd_piece_coordinate` — the transported parameter is
that coordinate by value, and the second piece value is the
`ch₃`-coordinate of the same class). -/
theorem oChart_two_step_composite_class_coordinate {r : ℝ → Space} {c₀ c₁ c₂ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) (ch₃ : OSub1Chart r c₂)
    (x₁ : OChartTransitionDomain ch₁ ch₂) (x₂ : OChartTransitionDomain ch₂ ch₃)
    (nb₁ : OChartMonotoneNbhd ch₁ ch₂ x₁) (nb₂ : OChartMonotoneNbhd ch₂ ch₃ x₂)
    (u : TransportStepDomain (oChartTransitionOnInterval ch₁ ch₂ nb₁.subset nb₁.dom)
      nb₂.lo nb₂.hi) :
    ∃ y : OChartTransitionDomain ch₃ ch₁,
      oChartLift ch₃ y.1 = oChartLift ch₁ ⟨(u.1 : ℝ), nb₁.subset u.1.2⟩ ∧
      (y.1 : ℝ) = oChartTwoStepMap ch₁ ch₂ ch₃ x₁ x₂ nb₁ nb₂ u := by
  let c : OSub r := oChartLift ch₁ ⟨(u.1 : ℝ), nb₁.subset u.1.2⟩
  let w₁ : ChartInterval ch₁.lo ch₁.hi := ⟨(u.1 : ℝ), nb₁.subset u.1.2⟩
  rcases oChartNbhd_piece_coordinate ch₁ ch₂ x₁ nb₁ u.1 with ⟨y₁, hy₁lift, hy₁val⟩
  have hy₁c : oChartLift ch₂ y₁.1 = c := by simpa [c, w₁] using hy₁lift
  let v : ℝ := oChartTransitionOnInterval ch₁ ch₂ nb₁.subset nb₁.dom u.1
  have hveq : (y₁.1 : ℝ) = v := by
    simpa [v] using hy₁val
  have hv₂ : v ∈ Set.Ioo nb₂.lo nb₂.hi := by simpa [v] using u.2
  have hparam : y₁.1 = (⟨v, nb₂.subset hv₂⟩ : ChartInterval ch₂.lo ch₂.hi) := by
    apply Subtype.ext
    exact hveq
  let w₂ : ChartInterval nb₂.lo nb₂.hi := ⟨v, hv₂⟩
  rcases oChartNbhd_piece_coordinate ch₂ ch₃ x₂ nb₂ w₂ with ⟨y₂, hy₂lift, hy₂val⟩
  have hclass : oChartLift ch₂ ⟨(w₂ : ℝ), nb₂.subset w₂.2⟩ = c := by
    have heq : (⟨(w₂ : ℝ), nb₂.subset w₂.2⟩ : ChartInterval ch₂.lo ch₂.hi) = y₁.1 := by
      rw [hparam]
    rw [heq]
    exact hy₁c
  have hy₂c : oChartLift ch₃ y₂.1 = c := by
    rw [hy₂lift]
    exact hclass
  have hval : (y₂.1 : ℝ) = oChartTwoStepMap ch₁ ch₂ ch₃ x₁ x₂ nb₁ nb₂ u := by
    have hmain : (y₂.1 : ℝ) = oChartTransitionOnInterval ch₂ ch₃ nb₂.subset nb₂.dom w₂ := by
      simpa [w₂, v] using hy₂val
    rw [hmain]
    dsimp [oChartTwoStepMap]
  refine ⟨⟨y₂.1, ?_⟩, hy₂c, hval⟩
  rw [hy₂c]
  exact oChartLift_mem_W ch₁ w₁


/-! ## S118/S119 — finite-chain identification: transport infrastructure,
the base case, and the FULL finite-chain identification theorem

(S118 delivered the infrastructure and the `N = 0` base case; S119
completes the induction step, so the identification theorem is proved
in full.)

The full finite-chain identification theorem (chain value over a walk
prefix of `N+1` pieces = the final chart's coordinate of the start class)
is stated in the ROADMAP; the module content here is its infrastructure
and base case:

- `range_map_cons` — the ℕ-indexed ↔ List-indexed cons lemma for range
  maps; `map_eq_of_pointwise` (pointwise-equal functions give equal
  maps);
- `chainValue_of_list_eq` (chain value is invariant under list equality,
  with the element transported), `chainValue_one`, `chainValue_cons` —
  the S111 recursion equations in lemma form;
- **`chain_transport_class_coordinate_base`** — the base case of the
  identification (one junction: `N = 0`): for a parameter `x` of piece
  `k` (the single junction piece between `ch k` and `ch (k+1)`), the
  chain value `(p k).τ x.1` is the `ch (k+1)`-coordinate of the same
  class as the `ch k`-parameter of `x` — exactly the S116 hinge content
  read through the S111 engine.

The induction step (exposing the second piece with `range_map_cons`,
rewriting the chain value by `chainValue_of_list_eq` + `chainValue_cons`,
applying the induction hypothesis at `k+1`, and matching the class by the
S116 `hsem` conjuncts at `k`) is recorded in the ROADMAP as the next
slice. -/

/-- pointwise-equal functions give equal maps. -/
lemma map_eq_of_pointwise {α β : Type*} (f g : α → β) (l : List α) (h : ∀ a, f a = g a) :
    l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp [h a, ih]

/-- chain value is invariant under a list equality (transport). -/
lemma chainValue_of_list_eq {ps qs : List MonoPiece} (h : ps = qs) (x : ChainDomain ps) :
    chainValue ps x = chainValue qs ((congrArg ChainDomain h) ▸ x) := by
  subst qs
  simp

/-- chain value over a single piece (base). -/
lemma chainValue_one (p : MonoPiece) (x : ChainDomain [p]) :
    chainValue [p] x = p.τ x.1 := by
  rfl

/-- chain value recursion over a cons with nonempty tail. -/
lemma chainValue_cons {p q : MonoPiece} {rest : List MonoPiece}
    (x : ChainDomain (p :: q :: rest)) :
    chainValue (p :: q :: rest) x =
      chainValue (q :: rest) ⟨⟨p.τ x.1, x.2.choose⟩, x.2.choose_spec⟩ := by
  rfl

/-- the ℕ-indexed ↔ List-indexed cons lemma for range maps. -/
lemma range_map_cons {α : Type*} (p : ℕ → α) (N : ℕ) :
    (List.range (N + 1)).map p = p 0 :: (List.range N).map (fun j => p (j + 1)) := by
  induction N with
  | zero =>
      rw [List.range_succ]
      rw [List.map_append]
      rw [List.range_zero]
      simp
  | succ N ih =>
      rw [List.range_succ]
      rw [List.map_append]
      rw [ih]
      rw [List.range_succ]
      rw [List.map_append]
      simp

/-- **Base case of the finite-chain identification** (one junction,
`N = 0`): a parameter of the single junction piece transports to the
`ch (k+1)`-coordinate of the same class (the S116 hinge content read
through the S111 engine). -/
theorem chain_transport_class_coordinate_base {r : ℝ → Space} {c : ℕ → OSub r}
    (ch : (i : ℕ) → OSub1Chart r (c i))
    (p : ℕ → MonoPiece)
    (hsub : ∀ i, Set.Ioo (p i).lo (p i).hi ⊆ Set.Ioo (ch i).lo (ch i).hi)
    (hsem : ∀ i (u : ChartInterval (p i).lo (p i).hi),
        oChartLift (ch i) ⟨(u : ℝ), hsub i u.2⟩ ∈ chartTrace (ch (i + 1)) ∧
        ∃ y : OChartTransitionDomain (ch (i + 1)) (ch i),
          oChartLift (ch (i + 1)) y.1 = oChartLift (ch i) ⟨(u : ℝ), hsub i u.2⟩ ∧
          (y.1 : ℝ) = (p i).τ u) (k : ℕ) :
    ∀ x : {x : ChartInterval (p k).lo (p k).hi //
             transports (p k) ((List.range 0).map (fun j => p (k + (j + 1)))) x},
      ∃ y : OChartTransitionDomain (ch (k + 1)) (ch k),
        oChartLift (ch (k + 1)) y.1 = oChartLift (ch k) ⟨(x.1 : ℝ), hsub k x.1.2⟩ ∧
        (y.1 : ℝ) =
          chainValue (p k :: (List.range 0).map (fun j => p (k + (j + 1)))) ⟨x.1, x.2⟩ := by
  intro x
  rcases x with ⟨xk, htr⟩
  rcases hsem k xk with ⟨hin, y, hylift, hyval⟩
  refine ⟨y, ?_, ?_⟩
  · simpa using hylift
  · have hL : p k :: (List.range 0).map (fun j : ℕ => p (k + (j + 1))) = [p k] := by
      rw [List.range_zero]
      simp
    rw [chainValue_of_list_eq hL ⟨xk, htr⟩]
    rw [chainValue_one]
    simpa using hyval


/-- the tail pieces `p (k+1)..p (k+n)` of a chain starting at piece `k`
(def-reducible: `chainTail p k (n+1) = p (k+1) :: chainTail p (k+1) n`,
so the S111 `chainValue` recursion reduces definitionally along it). -/
def chainTail (p : ℕ → MonoPiece) : ℕ → ℕ → List MonoPiece
  | _k, 0 => []
  | k, n+1 => p (k + 1) :: chainTail p (k + 1) n

/-- **Finite-chain transport is the class-coordinate transport (S119).**
With charts `ch i` (for centers `c i`), junction pieces `p i`
(`ch i → ch(i+1)`, interval-embedded by `hsub`), and the class-coordinate
semantics `hsem` (S116), the iterated transport of the S111 engine over
the `n+1` pieces `p k, …, p (k+n)` sends a starting parameter to the
`ch (k+n+1)`-coordinate of the same class as the `ch k`-parameter,
wherever the transport is defined — the full identification whose base
case (`n = 0`) was proved in S118, now completed by the induction step. -/
theorem chain_transport_class_coordinate {r : ℝ → Space} {c : ℕ → OSub r}
    (ch : (i : ℕ) → OSub1Chart r (c i))
    (p : ℕ → MonoPiece)
    (hsub : ∀ i, Set.Ioo (p i).lo (p i).hi ⊆ Set.Ioo (ch i).lo (ch i).hi)
    (hsem : ∀ i (u : ChartInterval (p i).lo (p i).hi),
        oChartLift (ch i) ⟨(u : ℝ), hsub i u.2⟩ ∈ chartTrace (ch (i + 1)) ∧
        ∃ y : OChartTransitionDomain (ch (i + 1)) (ch i),
          oChartLift (ch (i + 1)) y.1 = oChartLift (ch i) ⟨(u : ℝ), hsub i u.2⟩ ∧
          (y.1 : ℝ) = (p i).τ u) :
    ∀ k : ℕ, ∀ n : ℕ,
      ∀ x : {x : ChartInterval (p k).lo (p k).hi //
               transports (p k) (chainTail p k n) x},
        ∃ y : OChartTransitionDomain (ch (k + n + 1)) (ch k),
          oChartLift (ch (k + n + 1)) y.1 =
            oChartLift (ch k) ⟨(x.1 : ℝ), hsub k x.1.2⟩ ∧
          (y.1 : ℝ) = chainValue (p k :: chainTail p k n) ⟨x.1, x.2⟩ := by
  classical
  intro k n
  revert k
  induction n with
  | zero =>
      intro k x
      rcases x with ⟨xk, htr⟩
      rcases hsem k xk with ⟨hin, y, hylift, hyval⟩
      refine ⟨y, ?_, ?_⟩
      · simpa using hylift
      · have hv : chainValue (p k :: chainTail p k 0) ⟨xk, htr⟩ = (p k).τ xk := by
          change chainValue (p k :: ([] : List MonoPiece)) ⟨xk, htr⟩ = (p k).τ xk
          rfl
        rw [hv]
        simpa using hyval
  | succ n ih =>
      intro k x
      have hshift : (k + 1 + n + 1) = (k + (n + 1) + 1) := by omega
      rw [← hshift]
      rcases x with ⟨xk, htr⟩
      let x' : {x' : ChartInterval (p (k + 1)).lo (p (k + 1)).hi //
          transports (p (k + 1)) (chainTail p (k + 1) n) x'} :=
        ⟨⟨(p k).τ xk, htr.choose⟩, htr.choose_spec⟩
      rcases ih (k + 1) x' with ⟨y, hy₁, hy₂⟩
      let c : OSub r := oChartLift (ch k) ⟨(xk : ℝ), hsub k xk.2⟩
      rcases hsem k xk with ⟨hin, y₀, hy₀₁, hy₀₂⟩
      have hchar : oChartLift (ch (k + 1 + n + 1)) y.1 = c := by
        have hparam : (⟨(x'.1 : ℝ), hsub (k + 1) (x').1.2⟩ :
            ChartInterval (ch (k + 1)).lo (ch (k + 1)).hi) = y₀.1 := by
          apply Subtype.ext
          have hv0 : (y₀.1 : ℝ) = (p k).τ xk := by simpa using hy₀₂
          change ((x'.1 : ℝ)) = (y₀.1 : ℝ)
          calc
            (x'.1 : ℝ) = (p k).τ xk := by simp [x']
            _ = (y₀.1 : ℝ) := hv0.symm
        have hlift0 : oChartLift (ch (k + 1)) ⟨(x'.1 : ℝ), hsub (k + 1) (x').1.2⟩ = c := by
          rw [hparam]
          exact hy₀₁
        rw [hlift0] at hy₁
        exact hy₁
      have hval : chainValue (p k :: chainTail p k (n + 1)) ⟨xk, htr⟩ =
          chainValue (p (k + 1) :: chainTail p (k + 1) n) ⟨x'.1, x'.2⟩ := by
        rfl
      refine ⟨⟨y.1, ?_⟩, ?_, ?_⟩
      · rw [hchar]
        exact oChartLift_mem_W (ch k) ⟨(xk : ℝ), hsub k xk.2⟩
      · simpa using hchar
      · rw [hval]
        exact hy₂

end LeanEval.KnotTheory.Quadrisecant
