import Submission.EFL.Reservoir

/-!
# The types of reservoirs (Definition 11.2, `def:reservoir_type`)

The paper distinguishes three types of reservoirs, according to the structure
of the hypergraph `𝓗`:

* **Type A₁** — a pseudorandom reservoir (Definition 11.1);
* **Type A₂** — `R_res = R_abs ∪ R_reg` with `R_abs` a `(ρ/2, ξ, ξ, ε)`-absorber
  that is additionally lower `(ρ/2, ξ, G')`-regular and `R_reg` a
  `(ρ, ξ, ε, R_abs, 𝓥)`-regularising reservoir;
* **Type B** — an absorber.

Here `G = 𝓗^{(2)}` and `G'` is the spanning subgraph consisting of the edges
of `G` incident to a vertex of `U = V_+^{(1-ε)}(G)` (`incidentTwo`).
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- A `(ρ, ξ, ε, 𝓥)`-reservoir of **Type A₁**: a pseudorandom reservoir, i.e.
`R_res ⊆ E(G)`, `d_{R_res}(v) = ρ d_G(v) ± ξn` for every vertex, and
`R_res ∩ E(G')` is a `(ρ, ξ, ξ, ε)`-absorber for `𝓥`. -/
def IsReservoirTypeA1 (𝓗 Rres : Hypergraph (Fin n)) (𝓥 : Set (Set (Fin n)))
    (ρ ξ ε : ℝ) : Prop :=
  Rres ⊆ 𝓗.pow2 ∧ IsPseudoReservoir 𝓗 (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) Rres 𝓥 ρ ξ

/-- A `(ρ, ξ, ε, 𝓥)`-reservoir of **Type A₂**: `R_res = R_abs ∪ R_reg` where
`R_abs` is a `(ρ/2, ξ, ξ, ε)`-absorber for `𝓥` that is also lower
`(ρ/2, ξ, G')`-regular and `R_reg` is a `(ρ, ξ, ε, R_abs, 𝓥)`-regularising
reservoir. -/
def IsReservoirTypeA2 (𝓗 Rres : Hypergraph (Fin n)) (𝓥 : Set (Set (Fin n)))
    (ρ ξ ε : ℝ) : Prop :=
  Rres ⊆ 𝓗.pow2 ∧ ∃ Rabs Rreg : Hypergraph (Fin n),
    Rres = Rabs ∪ Rreg ∧
    IsAbsorber (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) Rabs 𝓥 (ρ / 2) ξ ξ ∧
    LowerRegular (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) Rabs (ρ / 2) ξ ∧
    IsRegularising 𝓗 Rabs Rreg ρ ξ ε

/-- A `(ρ, ξ, ε, 𝓥)`-reservoir of **Type B**: `R_res` is a `(ρ, ξ, ξ, ε)`-absorber
for `𝓥`. -/
def IsReservoirTypeB (𝓗 Rres : Hypergraph (Fin n)) (𝓥 : Set (Set (Fin n)))
    (ρ ξ ε : ℝ) : Prop :=
  IsAbsorber (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) Rres 𝓥 ρ ξ ξ

theorem IsReservoirTypeA1.subset_pow2 {𝓗 Rres : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {ρ ξ ε : ℝ} (h : IsReservoirTypeA1 𝓗 Rres 𝓥 ρ ξ ε) :
    Rres ⊆ 𝓗.pow2 := h.1

theorem IsReservoirTypeA2.subset_pow2 {𝓗 Rres : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {ρ ξ ε : ℝ} (h : IsReservoirTypeA2 𝓗 Rres 𝓥 ρ ξ ε) :
    Rres ⊆ 𝓗.pow2 := h.1

theorem IsReservoirTypeB.subset_pow2 {𝓗 Rres : Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {ρ ξ ε : ℝ} (h : IsReservoirTypeB 𝓗 Rres 𝓥 ρ ξ ε) :
    Rres ⊆ 𝓗.pow2 := fun e he => (h.1 he).1

/-- The neighbourhood of `w` in `G'` is the same as in `G` when `w ∈ U`. -/
theorem degAt_incidentTwo_eq (𝓗 : Hypergraph (Fin n)) {U : Set (Fin n)} {w : Fin n}
    (hw : w ∈ U) : degAt (incidentTwo 𝓗 U) w = degAt 𝓗.pow2 w := by
  have heq : nbrs (incidentTwo 𝓗 U) w = nbrs 𝓗.pow2 w := by
    ext x
    constructor
    · intro hx
      exact (mem_incidentTwo.mp hx).1
    · intro hx
      exact mem_incidentTwo.mpr ⟨hx, w, by simp, hw⟩
  show (nbrs (incidentTwo 𝓗 U) w).ncard = (nbrs 𝓗.pow2 w).ncard
  rw [heq]

theorem incidentTwo_subset_pow2 (𝓗 : Hypergraph (Fin n)) (U : Set (Fin n)) :
    incidentTwo 𝓗 U ⊆ 𝓗.pow2 := fun _ h => h.1

end

end ErdosFaberLovaszConjecture
