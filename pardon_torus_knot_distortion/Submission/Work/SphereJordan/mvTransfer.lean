import Mathlib
import Submission.Work.SphereJordan.mayerVietorisDefs

/-!
# The Mayer–Vietoris transfer at `H₀` for a two-set cover

For a topological space `X` and two sets `U, V ⊆ X` with `U ∪ V = X`, the **transfer** sends a
subdivided path to an element of `H₀(U ∩ V) := H0 (U ∩ V)`: subdivide the path into pieces, each
lying in `U` or in `V`; then the `U`-labelled pieces contribute the *signed* sum `[end] - [start]`
of the `H₀(U ∩ V)` classes of their endpoints.  This is the chain-level description of the
Mayer–Vietoris connecting homomorphism `H₁(X) → H₀(U ∩ V)`; its image is exactly the kernel of the
components map `H0PairMap U V`.

## Contents

* `Side` — which set of the cover a piece lies in;
* `h0cls W x` — the class in `H₀(W)` of a point of `W`, and `0` for points outside `W`;
* `SData U V γ` — a labelled subdivision of a path `γ` (cut points + a side for each piece, with
  the piece of `γ` lying in that side);
* `SData.transfer` — the transfer of such a datum.

The main theorems about the transfer (`transfer_mem_ker`, `transfer_homotopic`,
`ker_le_range_transfer`) are proved in companion files.
-/

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

namespace Work.SphereJordan

open Set

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- Which of the two sets of the cover a piece of a subdivided path lies in. -/
inductive Side where
  | U
  | V
  deriving DecidableEq

/-- The class in `H₀(W)` of a point of `W`, and `0` for a point outside `W`. -/
def h0cls (W : Set X) (x : X) : H0 W :=
  if hx : x ∈ W then FreeAbelianGroup.of (ConnectedComponents.mk ⟨x, hx⟩) else 0

theorem h0cls_of_mem {W : Set X} {x : X} (hx : x ∈ W) :
    h0cls W x = FreeAbelianGroup.of (ConnectedComponents.mk ⟨x, hx⟩) := by
  rw [h0cls]
  exact dif_pos hx

theorem h0cls_of_notMem {W : Set X} {x : X} (hx : x ∉ W) : h0cls W x = 0 := by
  rw [h0cls]
  exact dif_neg hx

/-- Points of `W` that are joined by a path in `W` have the same class in `H₀(W)`. -/
theorem h0cls_eq_of_joinedIn {W : Set X} {x y : X} (hx : x ∈ W) (hy : y ∈ W)
    (h : JoinedIn W x y) : h0cls W x = h0cls W y := by
  obtain ⟨γ⟩ := JoinedIn.joined_subtype h
  have hmem : (⟨x, hx⟩ : W) ∈ connectedComponent (⟨y, hy⟩ : W) :=
    (isConnected_range γ.continuous).subset_connectedComponent ⟨1, γ.target⟩ ⟨0, γ.source⟩
  have key : (ConnectedComponents.mk (⟨x, hx⟩ : W)) = ConnectedComponents.mk (⟨y, hy⟩ : W) :=
    ConnectedComponents.coe_eq_coe'.mpr hmem
  rw [h0cls_of_mem hx, h0cls_of_mem hy, key]

/-- The coordinate pairing `⟨x, y⟩ = ∑_C x_C y_C` on `H₀(W)`. -/
def pairing {W : Set X} (x y : H0 W) : ℤ :=
  x.toFinsupp.sum fun c k => k * (y.toFinsupp c)

/-- A case analysis for two distinct elements of `{U, V}`. -/
theorem side_ne_cases {b b' : Side} (h : b ≠ b') :
    (b = Side.U ∧ b' = Side.V) ∨ (b = Side.V ∧ b' = Side.U) := by
  cases b <;> cases b' <;> first
    | exact absurd rfl h
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr ⟨rfl, rfl⟩

/-- A **labelled subdivision** of a path: cut points `t 0 < … < t n`, and for each of the `n` pieces
a side of the cover; the validity condition says that the piece of the path lies in that side. -/
structure SData {a b : X} (U V : Set X) (γ : Path a b) where
  n : ℕ
  t : Fin (n + 1) → unitInterval
  mono : StrictMono t
  t0 : t 0 = 0
  tn : t (Fin.last n) = 1
  side : Fin n → Side
  validU : ∀ i, side i = Side.U →
    ∀ s : unitInterval, t i.castSucc ≤ s → s ≤ t i.succ → γ s ∈ U
  validV : ∀ i, side i = Side.V →
    ∀ s : unitInterval, t i.castSucc ≤ s → s ≤ t i.succ → γ s ∈ V

namespace SData

variable {U V : Set X} {a b : X} {γ : Path a b}

/-- The transfer of a labelled subdivision: the signed sum of the `H₀(U ∩ V)` classes of the
endpoints of the `U`-labelled pieces. -/
def transfer (d : SData U V γ) : H0 (U ∩ V) :=
  ∑ i : Fin d.n, if d.side i = Side.U then
    (h0cls (U ∩ V) (γ (d.t i.succ)) - h0cls (U ∩ V) (γ (d.t i.castSucc))) else 0

/-- The interval of a piece is nonempty. -/
theorem le_t (d : SData U V γ) (i : Fin d.n) : d.t i.castSucc ≤ d.t i.succ :=
  (d.mono i.castSucc_lt_succ).le

/-- Two consecutive pieces of a subdivision share their common cut point. -/
theorem castSucc_succ_eq (d : SData U V γ) {i : Fin d.n} (h : i.val + 1 < d.n) :
    (⟨i.val + 1, h⟩ : Fin d.n).castSucc = i.succ := by
  apply Fin.ext
  simp [Fin.val_castSucc]

/-- The point of the subdivision at a side change lies in `U ∩ V`. -/
theorem mem_inter_of_side_ne {d : SData U V γ} {i : Fin d.n} (h : i.val + 1 < d.n)
    (hne : d.side i ≠ d.side ⟨i.val + 1, h⟩) : γ (d.t i.succ) ∈ U ∩ V := by
  have hcast := d.castSucc_succ_eq h
  rcases side_ne_cases hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨d.validU i h1 (d.t i.succ) (d.le_t i) le_rfl, ?_⟩
    rw [← hcast]
    exact d.validV ⟨i.val + 1, h⟩ h2 _ le_rfl (d.le_t ⟨i.val + 1, h⟩)
  · refine ⟨?_, d.validV i h1 (d.t i.succ) (d.le_t i) le_rfl⟩
    rw [← hcast]
    exact d.validU ⟨i.val + 1, h⟩ h2 _ le_rfl (d.le_t ⟨i.val + 1, h⟩)

/-- All interior cut points of a subdivision at a side change lie in `U ∩ V`. -/
theorem mem_inter_of_side_ne' {d : SData U V γ} {i : Fin d.n} (hi : 0 < i.val)
    (hne : d.side ⟨i.val - 1, by omega⟩ ≠ d.side i) :
    γ (d.t i.castSucc) ∈ U ∩ V := by
  have hk1 : (⟨i.val - 1, by omega⟩ : Fin d.n).val + 1 = i.val := by
    simp only [Fin.val_mk]; omega
  have hlast : (⟨(⟨i.val - 1, by omega⟩ : Fin d.n).val + 1, by omega⟩ : Fin d.n) = i :=
    Fin.ext hk1
  have hmem := mem_inter_of_side_ne (d := d) (i := ⟨i.val - 1, by omega⟩) (by omega)
    (by rw [hlast]; exact hne)
  have hsucc : (⟨i.val - 1, by omega⟩ : Fin d.n).succ = i.castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  rwa [hsucc] at hmem

end SData

end

end Work.SphereJordan
