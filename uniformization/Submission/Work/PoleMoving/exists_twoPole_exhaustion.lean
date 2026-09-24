import Mathlib
import Submission.Work.SimplyConnected.ABS.green_reduction.exists_barrier_regular_precompact_region
import Submission.Work.SimplyConnected.Perron.greenOn
import Submission.Work.Drive.greenExhaustion_locallyBounded

namespace Work.PoleMoving

/-- **A barrier-regular relatively compact connected region.**  An open connected set `Ω` of `X`
with compact closure, not all of `X`, whose every frontier point carries a Dirichlet barrier.  By
`Work.SimplyConnected.Perron.exists_isGreenOn_of_barriers_final` such a region carries a Green
function with *any* prescribed pole inside it. -/
structure TwoPoleRegion (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] where
  Ω : Set X
  isOpen_Ω : IsOpen Ω
  isConnected_Ω : IsConnected Ω
  isCompact_closure : IsCompact (closure Ω)
  ne_univ : Ω ≠ Set.univ
  barrier : ∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
    Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
    ContinuousOn u V ∧ u p = 0

/-- **A Green exhaustion carrying Green functions at two prescribed poles.**  On a non-compact
connected Riemann surface, a nested exhaustion `Ω n` by relatively compact connected open sets,
whose closures are contained in the next member and which cover the surface, carrying Green
functions `gA n` (pole `a`) and `gB n` (pole `b`) on the *same* region `Ω n`, extended by `0`
outside `Ω n`.

ROUTE (all tools are in the tree and can be reused or copied):

* iterate `Work.SimplyConnected.ABS.green_reduction.exists_barrier_regular_precompact_region`
  (sorry-free: for a compact `K` and a point `x₀` it produces an open connected precompact `Ω ⊇
  K ∪ {x₀}` with a barrier at every frontier point), feeding the compact set
  `closure (Ω n) ∪ Kex (n+1) ∪ {a, b}` at step `n` (see `Work.Drive.greenExhaustion_data` and
  `Work.Drive.exists_pair_exhaustion` for the exact pattern);
* `Work.SimplyConnected.Perron.exists_isGreenOn_of_barriers_final` (sorry-free) turns a
  barrier-regular region into a Green function with **any** prescribed pole inside it, so both
  `gA n` and `gB n` exist on the same `Ω n`;
* the `0`-extension is `Work.Drive.IsGreenOn.zeroExtension` (sorry-free; alternatively redo the
  three-line argument).

CAUTION: `Submission.Work.Drive.pairFunction` and `Submission.Work.Drive.pairPoles` define
`Work.Drive.frontier_nonempty_of_ne_univ`, and `Submission.Work.Drive.greenExhaustion_locallyBounded`
defines a name that clashes with them, so importing both families in one file fails.  Pick one side:
either import `greenExhaustion_locallyBounded` (for `IsGreenOn.zeroExtension`) and redo the
`pairFunction`-side exhaustion, or import the `pairFunction`-side lemmas and redo the zero-extension.
-/
theorem exists_twoPole_exhaustion {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (a b : X) :
    ∃ (Ω : ℕ → Set X) (gA gB : ℕ → X → ℝ),
      (∀ n, IsOpen (Ω n)) ∧ (∀ n, IsConnected (Ω n)) ∧
      (∀ n, IsCompact (closure (Ω n))) ∧ (∀ n, closure (Ω n) ⊆ Ω (n + 1)) ∧
      (⋃ n, Ω n) = Set.univ ∧ (∀ n, a ∈ Ω n) ∧ (∀ n, b ∈ Ω n) ∧
      (∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (gA n)) ∧
      (∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) b (gB n)) ∧
      (∀ n, ∀ x : X, x ∉ Ω n → gA n x = 0) ∧ (∀ n, ∀ x : X, x ∉ Ω n → gB n x = 0) := by
  classical
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  haveI : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨Kex⟩ : Nonempty (CompactExhaustion X) := inferInstance
  have hKab : IsCompact ({a, b} : Set X) := by
    simpa using (isCompact_singleton (x := b)).insert a
  -- one step: engulf `closure Ω ∪ Kex (n+1) ∪ {a,b}` by a new barrier-regular region
  have hstep : ∀ (n : ℕ) (D : TwoPoleRegion X),
      ∃ D' : TwoPoleRegion X, closure D.Ω ∪ Kex (n + 1) ∪ ({a, b} : Set X) ⊆ D'.Ω := by
    intro n D
    have hK : IsCompact (closure D.Ω ∪ Kex (n + 1) ∪ ({a, b} : Set X)) :=
      (D.isCompact_closure.union (Kex.isCompact (n + 1))).union hKab
    obtain ⟨Ω, hΩo, hΩc, hΩcomp, hKΩ, hΩne, hbar⟩ :=
      Work.SimplyConnected.ABS.green_reduction.exists_barrier_regular_precompact_region
        (X := X) hX hK a
    exact ⟨⟨Ω, hΩo, hΩc, hΩcomp, hΩne, hbar⟩, fun x hx => hKΩ (Or.inl hx)⟩
  -- the initial region contains `Kex 0 ∪ {a,b}`
  obtain ⟨init, hinit_spec⟩ :
      ∃ D : TwoPoleRegion X, Kex 0 ∪ ({a, b} : Set X) ⊆ D.Ω := by
    have hK : IsCompact (Kex 0 ∪ ({a, b} : Set X)) := (Kex.isCompact 0).union hKab
    obtain ⟨Ω, hΩo, hΩc, hΩcomp, hKΩ, hΩne, hbar⟩ :=
      Work.SimplyConnected.ABS.green_reduction.exists_barrier_regular_precompact_region
        (X := X) hX hK a
    exact ⟨⟨Ω, hΩo, hΩc, hΩcomp, hΩne, hbar⟩, fun x hx => hKΩ (Or.inl hx)⟩
  let D : ℕ → TwoPoleRegion X :=
    fun n => Nat.rec init (fun k ih => Classical.choose (hstep k ih)) n
  have hD : ∀ n : ℕ, D (n + 1) = Classical.choose (hstep n (D n)) := by
    intro n
    change Nat.rec init (fun k ih => Classical.choose (hstep k ih)) (Nat.succ n) =
      Classical.choose (hstep n (Nat.rec init (fun k ih => Classical.choose (hstep k ih)) n))
    rfl
  have hstep_spec : ∀ (n : ℕ) (D : TwoPoleRegion X),
      closure D.Ω ∪ Kex (n + 1) ∪ ({a, b} : Set X) ⊆
        (Classical.choose (hstep n D)).Ω := fun n D => Classical.choose_spec (hstep n D)
  have ha : ∀ n, a ∈ (D n).Ω := by
    intro n
    induction n with
    | zero => exact hinit_spec (Or.inr (by simp))
    | succ k ih =>
      have h := hstep_spec k (D k)
      rw [← hD k] at h
      exact h (Or.inr (by simp))
  have hb : ∀ n, b ∈ (D n).Ω := by
    intro n
    induction n with
    | zero => exact hinit_spec (Or.inr (by simp))
    | succ k ih =>
      have h := hstep_spec k (D k)
      rw [← hD k] at h
      exact h (Or.inr (by simp))
  have hnest : ∀ n, closure ((D n).Ω) ⊆ ((D (n + 1))).Ω := by
    intro n
    have h := hstep_spec n (D n)
    rw [← hD n] at h
    exact fun x hx => h (Or.inl (Or.inl hx))
  have hcover : (⋃ n, (D n).Ω) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨r, hr⟩ := Kex.exists_mem x
    have hr' : x ∈ Kex (r + 1) := ((Kex.subset_interior_succ r).trans interior_subset) hr
    have h := hstep_spec r (D r)
    rw [← hD r] at h
    exact Set.mem_iUnion.mpr ⟨r + 1, h (Or.inl (Or.inr hr'))⟩
  -- Green functions with poles `a` and `b` on each region
  have hEA : ∀ n, ∃ E : X → ℝ,
      Work.SimplyConnected.ABS.IsGreenOn ((D n).Ω) a E := fun n =>
    Work.SimplyConnected.Perron.exists_isGreenOn_of_barriers_final (X := X)
      (D n).isOpen_Ω (D n).isConnected_Ω (D n).ne_univ (D n).isCompact_closure
      (ha n) (D n).barrier
  have hEB : ∀ n, ∃ E : X → ℝ,
      Work.SimplyConnected.ABS.IsGreenOn ((D n).Ω) b E := fun n =>
    Work.SimplyConnected.Perron.exists_isGreenOn_of_barriers_final (X := X)
      (D n).isOpen_Ω (D n).isConnected_Ω (D n).ne_univ (D n).isCompact_closure
      (hb n) (D n).barrier
  refine ⟨fun n => (D n).Ω,
    fun n x => if x ∈ (D n).Ω then (Classical.choose (hEA n)) x else 0,
    fun n x => if x ∈ (D n).Ω then (Classical.choose (hEB n)) x else 0,
    fun n => (D n).isOpen_Ω, fun n => (D n).isConnected_Ω,
    fun n => (D n).isCompact_closure, hnest, hcover, ha, hb, ?_, ?_, ?_, ?_⟩
  · intro n
    exact Work.Drive.IsGreenOn.zeroExtension (D n).isOpen_Ω (Classical.choose_spec (hEA n))
  · intro n
    exact Work.Drive.IsGreenOn.zeroExtension (D n).isOpen_Ω (Classical.choose_spec (hEB n))
  · intro n x hx
    simp [hx]
  · intro n x hx
    simp [hx]

end Work.PoleMoving
