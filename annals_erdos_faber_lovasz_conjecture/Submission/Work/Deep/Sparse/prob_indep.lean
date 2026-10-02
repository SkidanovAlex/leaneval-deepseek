/-
# Independence of events depending on disjoint sets of coordinates

`colSpace V k` is the uniform measure on the colourings `V → Fin k` (the sample space of the
naive colouring procedure, see `Submission/Work/Deep/Sparse/ProbBasic.lean`).  Two random
variables `f ↦ f v` are independent for distinct vertices `v`; more generally every event
that depends only on the coordinates in a set `S` is independent of every event that depends
only on the coordinates in a disjoint set `T`.

This module proves that statement, `prob_indep`:

* `glue S f g` — the colouring that agrees with `f` on `S` and with `g` off `S`;
* `glue_glue` — `glue` is *involutive* in the sense that
  `glue S (glue S f g) (glue S g f) = f`; consequently
  `swapEquiv`, `(f, g) ↦ (glue S f g, glue S g f)`, is a fixed-point-free involution of the
  set of pairs of colourings, i.e. a bijection;
* `hre` — the resulting *reindexing identity*
  `∑ p, G (glue S p.1 p.2) = k^|V| * ∑ h, G h`
  (the map `(f, g) ↦ glue S f g` is `k^|V|`-to-one);
* `prob_indep` — the independence statement, obtained by expanding `prob` as a sum over
  sample points, gluing the two colourings of a pair and reindexing by `swapEquiv`.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic

namespace Work.Deep.Sparse

/-! ## Gluing two colourings along a `Finset` -/

/-- The colouring that agrees with `f` on `S` and with `g` off `S`. -/
private def glue {V : Type*} [DecidableEq V] {k : ℕ} (S : Finset V) (f g : V → Fin k) :
    V → Fin k := fun v => if v ∈ S then f v else g v

private theorem glue_of_mem {V : Type*} [DecidableEq V] {k : ℕ} {S : Finset V}
    {f g : V → Fin k} {v : V} (hv : v ∈ S) : glue S f g v = f v := if_pos hv

private theorem glue_of_notMem {V : Type*} [DecidableEq V] {k : ℕ} {S : Finset V}
    {f g : V → Fin k} {v : V} (hv : v ∉ S) : glue S f g v = g v := if_neg hv

/-- Gluing twice along `S`, with the roles of the two colourings exchanged, yields `f`. -/
private theorem glue_glue {V : Type*} [DecidableEq V] {k : ℕ} {S : Finset V}
    (f g : V → Fin k) : glue S (glue S f g) (glue S g f) = f := by
  funext v
  by_cases hv : v ∈ S
  · rw [glue_of_mem (f := glue S f g) hv, glue_of_mem (f := f) hv]
  · rw [glue_of_notMem (f := glue S f g) hv, glue_of_notMem (f := g) hv]

/-- The involution `(f, g) ↦ (glue S f g, glue S g f)` of the set of pairs of colourings.
It is the bijection used to reindex the double sum in the proof of independence: gluing
loses exactly the information contained in one colouring, so each `f` occurs as a first
component of `glue` exactly `k^|V|` times. -/
private def swapEquiv {V : Type*} [DecidableEq V] (k : ℕ) (S : Finset V) :
    ((V → Fin k) × (V → Fin k)) ≃ ((V → Fin k) × (V → Fin k)) where
  toFun p := (glue S p.1 p.2, glue S p.2 p.1)
  invFun p := (glue S p.1 p.2, glue S p.2 p.1)
  left_inv p := by
    obtain ⟨f, g⟩ := p
    exact Prod.ext (glue_glue f g) (glue_glue g f)
  right_inv p := by
    obtain ⟨f, g⟩ := p
    exact Prod.ext (glue_glue f g) (glue_glue g f)

/-! ## Independence -/

/-- **Independence of events depending on disjoint sets of coordinates.**

If `E` is determined by the coordinates in `S` (whenever `f` and `g` agree on `S`, either
both lie in `E` or neither does) and `E'` is determined by the coordinates in a disjoint set
`T`, then `E` and `E'` are independent for the uniform random colouring of `V`. -/
theorem prob_indep {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} [Nonempty (V → Fin k)]
    {S T : Finset V} (hST : Disjoint S T) {E E' : Set (V → Fin k)}
    (hE : ∀ f g : V → Fin k, (∀ v ∈ S, f v = g v) → (f ∈ E ↔ g ∈ E))
    (hE' : ∀ f g : V → Fin k, (∀ v ∈ T, f v = g v) → (f ∈ E' ↔ g ∈ E')) :
    (Work.Deep.Sparse.colSpace (V := V) k).prob (E ∩ E')
      = (Work.Deep.Sparse.colSpace (V := V) k).prob E
        * (Work.Deep.Sparse.colSpace (V := V) k).prob E' := by
  classical
  -- The measure is uniform, with mass `(Fintype.card (V → Fin k))⁻¹`.
  have hNne : (Fintype.card (V → Fin k) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmass : ∀ h : V → Fin k,
      (colSpace (V := V) k).mass h = (Fintype.card (V → Fin k) : ℝ)⁻¹ :=
    fun h => by rw [colSpace_mass]
  -- The indicator of `E` is invariant under replacing `f` by `glue S f g`.
  have hinvE : ∀ f g : V → Fin k,
      E.indicator (colSpace (V := V) k).mass (glue S f g)
        = E.indicator (colSpace (V := V) k).mass f := by
    intro f g
    have hiff : f ∈ E ↔ glue S f g ∈ E :=
      hE f (glue S f g) (fun v hv => (glue_of_mem (f := f) (g := g) hv).symm)
    by_cases h : glue S f g ∈ E
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mpr h), hmass, hmass]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hf => h (hiff.mp hf))]
  -- The indicator of `E'` is invariant under replacing `g` by `glue S f g`
  -- (here `S` and `T` are disjoint).
  have hinvE' : ∀ f g : V → Fin k,
      E'.indicator (colSpace (V := V) k).mass (glue S f g)
        = E'.indicator (colSpace (V := V) k).mass g := by
    intro f g
    have hiff : g ∈ E' ↔ glue S f g ∈ E' :=
      hE' g (glue S f g)
        (fun v hv => (glue_of_notMem (f := f) (g := g) (Finset.disjoint_right.mp hST hv)).symm)
    by_cases h : glue S f g ∈ E'
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mpr h), hmass, hmass]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hg => h (hiff.mp hg))]
  -- Pointwise, the product of the two indicators at a common point is the indicator of the
  -- intersection, up to the constant mass.
  have hpoint : ∀ h : V → Fin k,
      E.indicator (colSpace (V := V) k).mass h * E'.indicator (colSpace (V := V) k).mass h
        = (colSpace (V := V) k).mass h
            * (E ∩ E').indicator (colSpace (V := V) k).mass h := by
    intro h
    by_cases h1 : h ∈ E
    · by_cases h2 : h ∈ E'
      · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
          Set.indicator_of_mem (Set.mem_inter h1 h2)]
      · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
          Set.indicator_of_notMem (fun hm => h2 hm.2), mul_zero]
    · rw [Set.indicator_of_notMem h1, zero_mul,
        Set.indicator_of_notMem (fun hm => h1 hm.1), mul_zero]
  -- Reindexing: `(f, g) ↦ glue S f g` is `k^|V|`-to-one.
  have hre : ∀ G : (V → Fin k) → ℝ,
      ∑ p : (V → Fin k) × (V → Fin k), G (glue S p.1 p.2)
        = (Fintype.card (V → Fin k) : ℝ) * ∑ h : V → Fin k, G h := by
    intro G
    have h1 : ∑ p : (V → Fin k) × (V → Fin k), G (glue S p.1 p.2)
        = ∑ p : (V → Fin k) × (V → Fin k),
            G (glue S (swapEquiv k S p).1 (swapEquiv k S p).2) :=
      (Equiv.sum_comp (swapEquiv k S) (fun p => G (glue S p.1 p.2))).symm
    rw [h1]
    have h2 : ∀ p : (V → Fin k) × (V → Fin k),
        G (glue S (swapEquiv k S p).1 (swapEquiv k S p).2) = G p.1 := by
      intro p
      have hp : glue S (swapEquiv k S p).1 (swapEquiv k S p).2 = p.1 := by
        simp only [swapEquiv]
        exact glue_glue p.1 p.2
      rw [hp]
    rw [Finset.sum_congr rfl (fun p _ => h2 p)]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have key : (colSpace (V := V) k).prob E * (colSpace (V := V) k).prob E'
      = (colSpace (V := V) k).prob (E ∩ E') := by
    calc (colSpace (V := V) k).prob E * (colSpace (V := V) k).prob E'
        = ∑ p : (V → Fin k) × (V → Fin k),
            E.indicator (colSpace (V := V) k).mass p.1
              * E'.indicator (colSpace (V := V) k).mass p.2 := by
          rw [FinSpace.prob, FinSpace.prob, Finset.sum_mul_sum]
          rw [Fintype.sum_prod_type]
      _ = ∑ p : (V → Fin k) × (V → Fin k),
            E.indicator (colSpace (V := V) k).mass (glue S p.1 p.2)
              * E'.indicator (colSpace (V := V) k).mass (glue S p.1 p.2) := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [hinvE p.1 p.2, hinvE' p.1 p.2]
      _ = ∑ p : (V → Fin k) × (V → Fin k),
            (colSpace (V := V) k).mass (glue S p.1 p.2)
              * (E ∩ E').indicator (colSpace (V := V) k).mass (glue S p.1 p.2) := by
          refine Finset.sum_congr rfl (fun p _ => hpoint (glue S p.1 p.2))
      _ = (Fintype.card (V → Fin k) : ℝ)⁻¹
            * ∑ p : (V → Fin k) × (V → Fin k),
                (E ∩ E').indicator (colSpace (V := V) k).mass (glue S p.1 p.2) := by
          simp only [hmass]
          rw [← Finset.mul_sum]
      _ = (Fintype.card (V → Fin k) : ℝ)⁻¹
            * ((Fintype.card (V → Fin k) : ℝ)
                * ∑ h : V → Fin k, (E ∩ E').indicator (colSpace (V := V) k).mass h) := by
          rw [hre]
      _ = ((Fintype.card (V → Fin k) : ℝ)⁻¹ * (Fintype.card (V → Fin k) : ℝ))
            * ∑ h : V → Fin k, (E ∩ E').indicator (colSpace (V := V) k).mass h := by
          rw [mul_assoc]
      _ = ∑ h : V → Fin k, (E ∩ E').indicator (colSpace (V := V) k).mass h := by
          rw [inv_mul_cancel₀ hNne, one_mul]
      _ = (colSpace (V := V) k).prob (E ∩ E') := by
          rw [FinSpace.prob]
  exact key.symm

end Work.Deep.Sparse
