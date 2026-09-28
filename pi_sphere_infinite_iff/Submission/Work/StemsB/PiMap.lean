import Mathlib
import Submission.Work.StemsB.Fibrations

/-!
# The named map of homotopy groups induced by a continuous map, and the LES interface

Mathlib defines `HomotopyGroup N X x` but gives **no** functoriality: there is no named induced map
`π_n(X,x) → π_n(Y, f x)` for a continuous `f : X → Y` (a previous session in this directory
proved only an *existential* form, `Work.StemsB.exists_homotopyGroupHom`).  Every exactness
statement about homotopy groups needs the named map, so we provide it here:

* `Work.StemsB.πmap f n x : HomotopyGroup (Fin (n+1)) X x →* HomotopyGroup (Fin (n+1)) Y (f x)`;
* `Work.StemsB.πmap_id_apply`, `Work.StemsB.πmap_comp_apply` — functoriality.

We also record the **interface** of the long exact homotopy sequence of a Serre fibration,
`Work.StemsB.FibrationLES`, in the basepoint-friendly form: the base point of `B` is `p e₀`, so
that the fibre is `fibre p (p e₀)` with base point `fibrePoint p e₀` and no basepoint transport is
needed to state the exactness.  The sequence is

  `π_{k+2}(F) → π_{k+2}(E) → π_{k+2}(B) →^{∂} π_{k+1}(F) → π_{k+1}(E) → π_{k+1}(B)`

for every `k`, exact at each of the three displayed middle terms.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.StemsB

noncomputable section

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Postcomposition with a continuous map, on generalized loops.  Declared as an `abbrev` so
that the projection `(genLoopMap f n γ).1` is definitionally `f.comp γ.1` at every transparency
level (this is needed for the well-definedness proof of `Quotient.map` below). -/
abbrev genLoopMap (f : C(X, Y)) (n : ℕ) {x : X} (γ : Ω^ (Fin n) X x) : Ω^ (Fin n) Y (f x) :=
  ⟨f.comp γ.1, fun y hy => by rw [ContinuousMap.comp_apply, γ.2 y hy]⟩

@[simp]
theorem genLoopMap_apply (f : C(X, Y)) (n : ℕ) {x : X} (γ : Ω^ (Fin n) X x) (y : Fin n → I) :
    genLoopMap f n γ y = f (γ y) := rfl

theorem genLoopMap_const (f : C(X, Y)) (n : ℕ) (x : X) :
    genLoopMap f n (GenLoop.const (N := Fin n) (X := X) (x := x)) = GenLoop.const := by
  apply GenLoop.ext
  intro t
  rfl

theorem genLoopMap_transAt (f : C(X, Y)) (n : ℕ) {x : X} (i : Fin n)
    (p q : Ω^ (Fin n) X x) :
    genLoopMap f n (GenLoop.transAt i p q)
      = GenLoop.transAt i (genLoopMap f n p) (genLoopMap f n q) := by
  apply GenLoop.ext
  intro t
  change f ((GenLoop.transAt i p q) t)
    = (GenLoop.transAt i (genLoopMap f n p) (genLoopMap f n q)) t
  simp only [GenLoop.transAt, GenLoop.copy, ContinuousMap.coe_mk, GenLoop.mk_apply,
    genLoopMap_apply]
  split_ifs <;> rfl

/-- **The map `π_n(X,x) → π_n(Y, f x)` induced by a continuous map `f : X → Y`.**  Absent from
Mathlib at this revision; needed for every exactness statement about homotopy groups. -/
def πmap (f : C(X, Y)) (n : ℕ) (x : X) :
    HomotopyGroup (Fin (n + 1)) X x →* HomotopyGroup (Fin (n + 1)) Y (f x) where
  toFun := Quotient.map (genLoopMap f (n + 1))
    (fun a b h => by
      change (genLoopMap f (n + 1) a).1.HomotopicRel (genLoopMap f (n + 1) b).1
        (Cube.boundary (Fin (n + 1)))
      change a.1.HomotopicRel b.1 (Cube.boundary (Fin (n + 1))) at h
      exact h.comp_continuousMap f)
  map_one' := by
    rw [HomotopyGroup.one_def (N := Fin (n + 1)) (x := x),
      HomotopyGroup.one_def (N := Fin (n + 1)) (x := f x)]
    simp only [Quotient.map_mk]
    rw [genLoopMap_const]
  map_mul' := by
    intro a b
    refine Quotient.inductionOn₂ a b fun p q => ?_
    simp only [HomotopyGroup.mul_spec (i := (0 : Fin (n + 1))), Quotient.map_mk]
    rw [genLoopMap_transAt]

@[simp]
theorem πmap_apply_mk (f : C(X, Y)) (n : ℕ) (x : X) (γ : Ω^ (Fin (n + 1)) X x) :
    πmap f n x ⟦γ⟧ = ⟦genLoopMap f (n + 1) γ⟧ := rfl

theorem πmap_id_apply (n : ℕ) (x : X) (a : HomotopyGroup (Fin (n + 1)) X x) :
    πmap (ContinuousMap.id X) n x a = a := by
  induction a using Quotient.inductionOn with
  | h p => rfl

theorem πmap_comp_apply (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) (x : X)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    πmap (g.comp f) n x a = πmap g n (f x) (πmap f n x a) := by
  induction a using Quotient.inductionOn with
  | h p => rfl

/-! ## Transport of homotopy groups along equalities of base points -/

/-- Transport of homotopy groups along an equality of base points: the isomorphism
`π_{n+1}(X,x) ≃* π_{n+1}(X,y)` induced by an *equality* `h : x = y` (as opposed to a path, which
is the subject of the separate lemma `Work.StemsB.basepoint_transport`). -/
def homotopyGroupCast {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y) (n : ℕ) :
    HomotopyGroup (Fin (n + 1)) X x ≃* HomotopyGroup (Fin (n + 1)) X y :=
  h ▸ MulEquiv.refl _

@[simp]
theorem homotopyGroupCast_rfl {X : Type*} [TopologicalSpace X] {x : X} (n : ℕ) :
    homotopyGroupCast (rfl : x = x) n = MulEquiv.refl _ := rfl

/-- **Congruence for `πmap` along an equality of the maps.**  If `f = g` as continuous maps then
`πmap f` and `πmap g` differ only by the transport of the base point. -/
theorem πmap_congr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f = g) (n : ℕ) (x : X)
    (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupCast (congrArg (fun k : C(X, Y) => k x) h) n (πmap f n x a)
      = πmap g n x a := by
  subst h
  simp

/-! ## The fibre base point and the LES interface -/

/-- The base point of the fibre `p ⁻¹' {p e₀}`, induced by a point `e₀ : E`.  Using this base
point (rather than an arbitrary one in `fibre p b₀`) makes all the maps of the long exact sequence
typecheck without any basepoint transport, since `fibreIncl p (p e₀) (fibrePoint p e₀) = e₀`
definitionally. -/
def fibrePoint {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) : fibre p (p e₀) := ⟨e₀, rfl⟩

@[simp]
theorem fibreIncl_fibrePoint {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) : fibreIncl p (p e₀) (fibrePoint p e₀) = e₀ := rfl

/-- **The interface of the long exact homotopy sequence of a Serre fibration.**  For every `k`
there is a connecting homomorphism `∂ : π_{k+2}(B) →* π_{k+1}(F)` such that

* `π_{k+2}(F) → π_{k+2}(E) → π_{k+2}(B)` is exact at `π_{k+2}(E)`;
* `π_{k+2}(E) → π_{k+2}(B) → π_{k+1}(F)` is exact at `π_{k+2}(B)`;
* `π_{k+2}(B) → π_{k+1}(F) → π_{k+1}(E)` is exact at `π_{k+1}(F)`.

(The base points are chosen as `e₀ ∈ E`, `p e₀ ∈ B` and `fibrePoint p e₀ ∈ fibre p (p e₀)`.) -/
def FibrationLES {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) : Prop :=
  ∀ k : ℕ,
    ∃ d : HomotopyGroup (Fin (k + 2)) B (p e₀) →*
        HomotopyGroup (Fin (k + 1)) (fibre p (p e₀)) (fibrePoint p e₀),
      Function.MulExact (πmap (fibreIncl p (p e₀)) (k + 1) (fibrePoint p e₀))
          (πmap p (k + 1) e₀) ∧
      Function.MulExact (πmap p (k + 1) e₀) d ∧
      Function.MulExact d (πmap (fibreIncl p (p e₀)) k (fibrePoint p e₀))

end

end Work.StemsB
