import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.petal_spread_component
import Submission.Work.Horn.petal_image_ne_zero

namespace Work.Horn

set_option linter.unusedVariables false

open Set Filter Topology

noncomputable section

/-- One step of the spread chain: the union of all connected components (inside the open set
`D ∩ G ⁻¹' A i`) that meet `A i`.  Since `A i` is connected and (in the intended application)
mapped into itself by `G`, this union is again open and connected, contains `A i`, and is the
*maximal* preconnected subset of `D ∩ G ⁻¹' (A i)` meeting `A i`. -/
def spreadStep {q : ℕ} (G : ℂ → ℂ) (D : Set ℂ) (A : Fin q → Set ℂ) (i : Fin q) : Set ℂ :=
  ⋃ x ∈ A i, connectedComponentIn (D ∩ G ⁻¹' (A i)) x

/-- The iterated spread chain, starting from the petals `V`. -/
def spreadChain {q : ℕ} (G : ℂ → ℂ) (D : Set ℂ) (V : Fin q → Set ℂ) : ℕ → (Fin q → Set ℂ) :=
  Nat.rec (motive := fun _ => Fin q → Set ℂ) V (fun _ A => spreadStep G D A)

/-- **One step of the spread chain, abstractly.**  If `A : Fin q → Set ℂ` is a family of open,
connected sets contained in `D`, each mapped into itself by `G` (holomorphic on the open `D`) and
pairwise disjoint, then `spreadStep G D A` has the same properties, contains `A`, and
* `G '' spreadStep G D A i ⊆ A i`,
* `spreadStep G D A i` is maximal among the preconnected subsets `C` of `D` with `G '' C ⊆ A i`
  that meet `A i`.

The proofs are purely topological: the components of the open set `D ∩ G ⁻¹' (A i)` that meet the
connected `A i` all coincide (with `connectedComponentIn (D ∩ G ⁻¹' (A i)) x₀`, `x₀ ∈ A i`), so
their union is connected, and the disjointness of the `i`-families is immediate because `G` maps
`spreadStep G D A i` into `A i` and `A i ∩ A j = ∅`. -/
theorem spreadStep_spec {q : ℕ} {G : ℂ → ℂ} {D : Set ℂ} {A : Fin q → Set ℂ}
    (hD : IsOpen D) (hG : DifferentiableOn ℂ G D)
    (hopen : ∀ i, IsOpen (A i)) (hconn : ∀ i, IsConnected (A i))
    (hsub : ∀ i, A i ⊆ D) (hmap : ∀ i, G '' A i ⊆ A i)
    (hdisj : ∀ i j : Fin q, i ≠ j → Disjoint (A i) (A j)) :
    (∀ i, IsOpen (spreadStep G D A i)) ∧
    (∀ i, IsConnected (spreadStep G D A i)) ∧
    (∀ i, spreadStep G D A i ⊆ D) ∧
    (∀ i, A i ⊆ spreadStep G D A i) ∧
    (∀ i, G '' spreadStep G D A i ⊆ A i) ∧
    (∀ i, ∀ C : Set ℂ, IsPreconnected C → C ⊆ D → C ⊆ G ⁻¹' (A i) →
      (A i ∩ C).Nonempty → C ⊆ spreadStep G D A i) ∧
    (∀ i j : Fin q, i ≠ j → Disjoint (spreadStep G D A i) (spreadStep G D A j)) := by
  -- `D ∩ G ⁻¹' (A i)` is open (the germ is holomorphic on the open `D`, `A i` is open)
  have hUopen : ∀ i, IsOpen (D ∩ G ⁻¹' (A i)) :=
    fun i => hG.continuousOn.isOpen_inter_preimage hD (hopen i)
  -- each `A i` sits inside that open set, because `G` maps it into itself
  have hAsubU : ∀ i, A i ⊆ D ∩ G ⁻¹' (A i) := fun i y hy => ⟨hsub i hy, hmap i ⟨y, hy, rfl⟩⟩
  have hstepSub : ∀ i, spreadStep G D A i ⊆ D := by
    intro i z hz
    rw [spreadStep] at hz
    obtain ⟨x, _hx, hzCC⟩ := Set.mem_iUnion₂.mp hz
    exact (connectedComponentIn_subset _ _ hzCC).1
  have hstepOpen : ∀ i, IsOpen (spreadStep G D A i) := by
    intro i
    rw [spreadStep]
    exact isOpen_iUnion fun x => isOpen_iUnion fun _ => (hUopen i).connectedComponentIn
  have hAstep : ∀ i, A i ⊆ spreadStep G D A i := by
    intro i y hy
    rw [spreadStep]
    exact Set.mem_iUnion₂.mpr ⟨y, hy, mem_connectedComponentIn (hAsubU i hy)⟩
  -- connectedness: all the components that meet `A i` are the same component
  have hstepConn : ∀ i, IsConnected (spreadStep G D A i) := by
    intro i
    obtain ⟨x₀, hx₀⟩ := (hconn i).nonempty
    rw [spreadStep]
    have heq : (⋃ x ∈ A i, connectedComponentIn (D ∩ G ⁻¹' (A i)) x)
        = connectedComponentIn (D ∩ G ⁻¹' (A i)) x₀ := by
      apply subset_antisymm
      · intro z hz
        obtain ⟨x, hx, hzCC⟩ := Set.mem_iUnion₂.mp hz
        have hxcc : x ∈ connectedComponentIn (D ∩ G ⁻¹' (A i)) x₀ :=
          IsPreconnected.subset_connectedComponentIn (hconn i).isPreconnected hx₀ (hAsubU i) hx
        rw [connectedComponentIn_eq hxcc]
        exact hzCC
      · intro z hz
        exact Set.mem_iUnion₂.mpr ⟨x₀, hx₀, hz⟩
    rw [heq]
    exact isConnected_connectedComponentIn_iff.mpr (hAsubU i hx₀)
  have hstepMap : ∀ i, G '' spreadStep G D A i ⊆ A i := by
    intro i
    rintro _ ⟨y, hy, rfl⟩
    rw [spreadStep] at hy
    obtain ⟨x, _hx, hyCC⟩ := Set.mem_iUnion₂.mp hy
    exact (connectedComponentIn_subset _ _ hyCC).2
  -- maximality
  have hmax : ∀ i, ∀ C : Set ℂ, IsPreconnected C → C ⊆ D → C ⊆ G ⁻¹' (A i) →
      (A i ∩ C).Nonempty → C ⊆ spreadStep G D A i := by
    intro i C hCpre hCD hCG hmeet
    obtain ⟨y, hyA, hyC⟩ := hmeet
    have hCU : C ⊆ D ∩ G ⁻¹' (A i) := fun z hz => ⟨hCD hz, hCG hz⟩
    intro z hz
    rw [spreadStep]
    exact Set.mem_iUnion₂.mpr ⟨y, hyA,
      IsPreconnected.subset_connectedComponentIn hCpre hyC hCU hz⟩
  -- disjointness: `G` maps the `i`-th spread into the disjoint `A i`
  have hstepDisj : ∀ i j : Fin q, i ≠ j → Disjoint (spreadStep G D A i) (spreadStep G D A j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    exact (Set.disjoint_left.mp (hdisj i j hij) (hstepMap i ⟨z, hzi, rfl⟩))
      (hstepMap j ⟨z, hzj, rfl⟩)
  exact ⟨hstepOpen, hstepConn, hstepSub, hAstep, hstepMap, hmax, hstepDisj⟩

/-- **Nesting of Shishikura's `V^{(i)}_n` chain** (first of the three pieces of the one remaining
input for `Work.Horn.horn_germ_F0`; see `NOTES_GERM_F0.md` §41).

Given the petals `V : Fin q → Set ℂ` of a parabolic germ `G` on the open `D` (`G 0 = 0`, petals
disjoint, `G`-forward-invariant modulo `0`, accumulating at `0`, capturing every basin orbit, with
locally constant entered index, `0 ∉ V i` and `0` outside the basin), there is a doubly indexed
family `W : ℕ → Fin q → Set ℂ` of spreads with

* `W 0 i = V i`, all `W n i` open, connected, contained in `D`;
* `W n i ⊆ W (n+1) i` (increasing);
* `W (n+1) i` is a union of components of `D ∩ G ⁻¹' (W n i)` meeting `W n i` — formalised as the
  maximality clause `∀ C, IsPreconnected C → C ⊆ D → C ⊆ G ⁻¹' (W n i) → (W n i ∩ C).Nonempty →
  C ⊆ W (n+1) i` (the restriction `C ⊆ D` and `C ⊆ G ⁻¹' (W n i)` are the reviewers' fix: `G` is
  unconstrained off `D`, so `D ∩ G ⁻¹' (W n i)` — not `G ⁻¹' (W n i)` — is the open set whose
  components are wanted);
* `G` maps `W (n+1) i` into `W n i ∪ {0}`;
* distinct indices stay disjoint, at the same level: `Disjoint (W n i) (W n j)` for `i ≠ j`.

Existence is elementary: take `W (n+1) i` to be the union of all components of the open set
`D ∩ G ⁻¹' (W n i)` that meet the connected `W n i`; the union is open (components of an open
subset of `ℂ`) and connected (a union of connected sets all meeting the connected `W n i`), and it
contains `W n i` because `G '' W n i ⊆ W n i ∪ {0}` and `0 ∉ V i` (so `G '' (W n i) ⊆ W n i`), so
each point of `W n i` lies in `D ∩ G ⁻¹' (W n i)`.  Maximality is by construction, `G '' W (n+1) i
⊆ W n i` because every component meets `W n i` and `G` is continuous.  Disjointness of the
`i`-chains follows from `hVindex`/`hVdisj` as in `Work.Horn.petal_spread_component`.  **No
properness, no simple connectivity and no critical-point input is claimed here** — this piece is
deliberately purely combinatorial. -/
theorem spread_chain_nesting {G : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    (hD : IsOpen D) (hG : DifferentiableOn ℂ G D) (h0 : (0 : ℂ) ∈ D) (hfix : G 0 = 0)
    (hVopen : ∀ i, IsOpen (V i)) (hVconn : ∀ i, IsConnected (V i)) (hVsub : ∀ i, V i ⊆ D)
    (hVmap : ∀ i, ∀ z ∈ V i, G z ∈ V i ∪ {0})
    (hVne : ∀ i, (0 : ℂ) ∉ V i)
    (hVdisj : ∀ i j : Fin q, i ≠ j → Disjoint (V i) (V j))
    (hVcl : ∀ i, (0 : ℂ) ∈ closure (V i))
    (h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin G D)
    (hVcapture : ∀ z ∈ MandelDim.ParabolicBasin G D, ∃ n : ℕ, G^[n] z ∈ ⋃ i, V i)
    (hVreach : ∀ z ∈ D, (∃ n : ℕ, (∀ k < n, G^[k] z ∈ D) ∧ G^[n] z ∈ ⋃ i, V i) →
      z ∈ MandelDim.ParabolicBasin G D)
    (hVindex : ∀ z ∈ MandelDim.ParabolicBasin G D, ∃ U ∈ nhds z, ∀ w ∈ U, ∀ i : Fin q,
      ((∃ n : ℕ, G^[n] z ∈ V i) ↔ (∃ n : ℕ, G^[n] w ∈ V i))) :
    ∃ W : ℕ → Fin q → Set ℂ,
      (∀ n i, IsOpen (W n i)) ∧ (∀ n i, IsConnected (W n i)) ∧ (∀ n i, W n i ⊆ D) ∧
      (∀ i, W 0 i = V i) ∧
      (∀ n i, W n i ⊆ W (n + 1) i) ∧
      (∀ n i, ∀ C : Set ℂ, IsPreconnected C → C ⊆ D → C ⊆ G ⁻¹' (W n i) →
        (W n i ∩ C).Nonempty → C ⊆ W (n + 1) i) ∧
      (∀ n i, Set.MapsTo G (W (n + 1) i) (W n i ∪ {0})) ∧
      (∀ n i j : Fin q, i ≠ j → Disjoint (W n i) (W n j)) := by
  classical
  -- a point of a petal never maps to `0`
  have hnozero : ∀ i, ∀ z ∈ V i, G z ≠ 0 :=
    petal_image_ne_zero hD hG hVconn hVsub hVcl hVreach h0out
  -- hence `G` maps each petal into itself
  have hGV : ∀ i, G '' V i ⊆ V i := by
    intro i
    rintro _ ⟨y, hy, rfl⟩
    rcases hVmap i y hy with h | h
    · exact h
    · exact absurd h (hnozero i y hy)
  -- the induction invariant
  have key : ∀ n, (∀ i, IsOpen (spreadChain G D V n i)) ∧
      (∀ i, IsConnected (spreadChain G D V n i)) ∧
      (∀ i, spreadChain G D V n i ⊆ D) ∧
      (∀ i, G '' spreadChain G D V n i ⊆ spreadChain G D V n i) ∧
      (∀ i j : Fin q, i ≠ j → Disjoint (spreadChain G D V n i) (spreadChain G D V n j)) := by
    intro n
    induction n with
    | zero => exact ⟨hVopen, hVconn, hVsub, hGV, hVdisj⟩
    | succ n ih =>
      obtain ⟨ho, hc, hs, hm, hd⟩ := ih
      obtain ⟨so, sc, ss, hAst, sm, _hmax, sd⟩ := spreadStep_spec hD hG ho hc hs hm hd
      refine ⟨so, sc, ss, ?_, sd⟩
      intro i
      exact subset_trans (sm i) (hAst i)
  refine ⟨spreadChain G D V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n i; exact (key n).1 i
  · intro n i; exact (key n).2.1 i
  · intro n i; exact (key n).2.2.1 i
  · intro i; rfl
  · intro n i
    obtain ⟨ho, hc, hs, hm, hd⟩ := key n
    obtain ⟨_so, _sc, _ss, hAst, _sm, _hmax, _sd⟩ := spreadStep_spec hD hG ho hc hs hm hd
    exact hAst i
  · intro n i C hCpre hCD hCG hmeet
    obtain ⟨ho, hc, hs, hm, hd⟩ := key n
    obtain ⟨_so, _sc, _ss, _hAst, _sm, hmax, _sd⟩ := spreadStep_spec hD hG ho hc hs hm hd
    exact hmax i C hCpre hCD hCG hmeet
  · intro n i
    obtain ⟨ho, hc, hs, hm, hd⟩ := key n
    obtain ⟨_so, _sc, _ss, _hAst, sm, _hmax, _sd⟩ := spreadStep_spec hD hG ho hc hs hm hd
    intro z hz
    exact Or.inl (sm i ⟨z, hz, rfl⟩)
  · intro n i j hij
    exact (key n).2.2.2.2 i j hij

end

end Work.Horn
