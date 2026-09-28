import Mathlib
import Submission.Work.RatHurewicz.AvoidOrigin.Chart
import Submission.Work.RatHurewicz.AvoidOrigin.chartInjective

/-!
# The chart pieces of a cell of the cycle model

The chart neighbourhood `V = chartNhd D i S x hS` of a cell `(i,S)` of the model is the image of
the open chart ball around `x` in the face `S` of the cell `i`.  To prove that `V` is a
neighbourhood of its points *along the skeleton* one has to describe the whole class of a point of
the chart through the charts of the other cells that meet `(i,S)` in the same stratum, and this file
fixes that vocabulary.

For a chain `ChainTrans D i S j τ` (a sequence of gluings that identifies the face `S` of the cell
`i` with a face of the cell `j`), the *transport along the chain* sends a point `y` of the face `S`
to a point of the face `imageTau τ` of `j` (this is `Work.RatHurewicz.transportPt`, and
`Work.RatHurewicz.AvoidOrigin.chainTrans` says that this construction gives exactly the class of a
point of the cell).  The *chart piece* of the chain is the set of raw points of the cell `j` whose
support contains `imageTau τ` and which lie within the chart radius of the transported chart centre;
its class is contained in `V`, and the chart pieces, together with the part of `Raw D` that does not
lie over the `(S.card-1)`-skeleton, form a saturated open set of `Raw D` whose image in the model
has trace exactly `V` on the skeleton.

* `imageTau τ` is the image of `τ`;
* `invFun τ u` is the *inverse* transport: the weight vector of the face `S` of `i` whose mass at
  `t` is the mass of `u` at `τ t` (it is the inverse of `transportFun · τ` on the vectors supported
  in `imageTau τ`);
* `ChainDatum D i S` bundles a cell `j` reached from `(i,S)` together with the vertex map;
* `chartPiece` and `chartNhdPre` are the pieces and their union;
* `skelPre D S` is the preimage in `Raw D` of the `(S.card-1)`-skeleton.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.AvoidOrigin

open Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- The image of a vertex map `τ` defined on the support `S`. -/
def imageTau {S : Finset (Fin (n + 2))} (τ : {t // t ∈ S} → Fin (n + 2)) :
    Finset (Fin (n + 2)) :=
  S.attach.image τ

theorem mem_imageTau {S : Finset (Fin (n + 2))} {τ : {t // t ∈ S} → Fin (n + 2)}
    {w : Fin (n + 2)} : w ∈ imageTau τ ↔ ∃ t, τ t = w := by
  simp [imageTau]

theorem card_imageTau {S : Finset (Fin (n + 2))} (τ : {t // t ∈ S} → Fin (n + 2))
    (hτ : Function.Injective τ) : (imageTau τ).card = S.card := by
  rw [imageTau, Finset.card_image_of_injective _ hτ, Finset.card_attach]

/-- **The inverse transport.**  The weight vector of the face `S` whose mass at `t ∈ S` is the mass
of the vector `u` at `τ t`. -/
def invFun {S : Finset (Fin (n + 2))} (τ : {t // t ∈ S} → Fin (n + 2))
    (u : Fin (n + 2) → ℝ) : Fin (n + 2) → ℝ :=
  fun v => if h : v ∈ S then u (τ ⟨v, h⟩) else 0

theorem invFun_of_mem {S : Finset (Fin (n + 2))} {τ : {t // t ∈ S} → Fin (n + 2)}
    {u : Fin (n + 2) → ℝ} {v : Fin (n + 2)} (h : v ∈ S) :
    invFun τ u v = u (τ ⟨v, h⟩) := dif_pos h

theorem invFun_of_notMem {S : Finset (Fin (n + 2))} {τ : {t // t ∈ S} → Fin (n + 2)}
    {u : Fin (n + 2) → ℝ} {v : Fin (n + 2)} (h : v ∉ S) : invFun τ u v = 0 := dif_neg h

/-- **A chain datum**: a cell `j` reached from the cell `(i,S)` by a chain of gluings, together with
the vertex map of the chain. -/
structure ChainDatum (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2))) where
  /-- the cell reached by the chain -/
  j : D.Idx
  /-- the vertex map of the chain -/
  τ : {t // t ∈ S} → Fin (n + 2)
  /-- the vertex map of a chain is injective -/
  inj : Function.Injective τ
  /-- the chain itself -/
  chain : ChainTrans D i S j τ

namespace ChainDatum

/-- The transport of the chart centre along the chain. -/
def center {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    (c : ChainDatum D i S) (x : stdSimplex ℝ (Fin (n + 2))) (hx : ptSupport x = S) :
    stdSimplex ℝ (Fin (n + 2)) :=
  transportPt x hx c.τ c.inj

theorem center_apply {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    (c : ChainDatum D i S) (x : stdSimplex ℝ (Fin (n + 2))) (hx : ptSupport x = S)
    (w : Fin (n + 2)) :
    (c.center x hx : Fin (n + 2) → ℝ) w
      = ∑ t : {t // t ∈ S}, if c.τ t = w then (x : Fin (n + 2) → ℝ) t else 0 := rfl

theorem ptSupport_center {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    (c : ChainDatum D i S) (x : stdSimplex ℝ (Fin (n + 2))) (hx : ptSupport x = S) :
    ptSupport (c.center x hx) = imageTau c.τ :=
  transportPtSupp x hx c.τ c.inj

/-- **The trivial chain datum.** -/
def refl (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2))) : ChainDatum D i S where
  j := i
  τ := fun t => t.1
  inj := fun _ _ h => Subtype.ext h
  chain := ChainTrans.refl

@[simp] theorem center_refl {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    (x : stdSimplex ℝ (Fin (n + 2))) (hx : ptSupport x = S) :
    (refl D i S).center x hx = x :=
  transportPt_id x hx (fun _ _ h => Subtype.ext h)

end ChainDatum

/-- **The chart piece of a chain datum**: the raw points of the cell `c.j` whose support contains
`imageTau c.τ` and whose distance to the transported chart centre is smaller than the chart
radius. -/
def chartPiece (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2)))
    (x : stdSimplex ℝ (Fin (n + 2))) (hx : ptSupport x = S) (hS : 2 < S.card)
    (c : ChainDatum D i S) : Set (Raw D) :=
  {a | ∃ u : stdSimplex ℝ (Fin (n + 2)),
    a = Sum.inl ⟨c.j, u⟩ ∧
    (∀ v ∈ imageTau c.τ, (u : Fin (n + 2) → ℝ) v ≠ 0) ∧
    ‖(u : Fin (n + 2) → ℝ) - (c.center x hx : Fin (n + 2) → ℝ)‖ < eps S x hS}

/-- **The union of the chart pieces** over all the chains issued from `(i,S)`. -/
def chartNhdPre (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2)))
    (x : stdSimplex ℝ (Fin (n + 2))) (hx : ptSupport x = S) (hS : 2 < S.card) : Set (Raw D) :=
  ⋃ c : ChainDatum D i S, chartPiece D i S x hx hS c

theorem mem_chartNhdPre {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    {x : stdSimplex ℝ (Fin (n + 2))} {hx : ptSupport x = S} {hS : 2 < S.card} {a : Raw D} :
    a ∈ chartNhdPre D i S x hx hS ↔ ∃ c : ChainDatum D i S, a ∈ chartPiece D i S x hx hS c :=
  Set.mem_iUnion

/-- The preimage in `Raw D` of the `(S.card - 1)`-skeleton of the model. -/
def skelPre (D : MData X n x₀) (S : Finset (Fin (n + 2))) : Set (Raw D) :=
  Quotient.mk'' ⁻¹' skel D (S.card - 1)

theorem mem_skelPre {D : MData X n x₀} {S : Finset (Fin (n + 2))} {a : Raw D} :
    a ∈ skelPre D S ↔ Quotient.mk'' a ∈ skel D (S.card - 1) := Iff.rfl

/-- The preimage of the skeleton is saturated for the gluing relation. -/
theorem eqvGen_skelPre {D : MData X n x₀} {S : Finset (Fin (n + 2))} {a b : Raw D}
    (h : Relation.EqvGen (modelRel D) a b) (ha : a ∈ skelPre D S) : b ∈ skelPre D S := by
  rw [mem_skelPre] at ha ⊢
  rwa [show Quotient.mk'' b = Quotient.mk'' a from Quotient.sound' (Relation.EqvGen.symm _ _ h)]

end

end Work.RatHurewicz.AvoidOrigin
