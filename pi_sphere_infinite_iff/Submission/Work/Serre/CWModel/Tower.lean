import Mathlib
import Submission.Work.Serre.CWModel.Gen
import Submission.Work.Serre.CWModel.Kill
import Submission.Work.Serre.bijective_piMapN_of_joined

/-!
# The model tower, and the CW model of a space in a homotopy range

Iterating the generator and killing steps of `Submission/Work/Serre/CWModel/Gen.lean` and
`.../Kill.lean` produces, for a `(b-1)`-connected space `B` (`b ≥ 2`), a cell complex `Γ` with a map
`g : Γ → B` which is a bijection on `π_i` for every `i ≤ N`, with all cells of dimension `≥ b`.
-/

open scoped Topology Topology.Homotopy unitInterval
open Work.RatHurewicz

namespace Work.Serre.CWModel

noncomputable section

/-- **The model tower.**  `towerA k` is the stage of the model at level `b - 2 + k`, i.e. with
`π_{j+1}(g)` bijective for `j ≤ b - 2 + k`.  Each step attaches cells of dimension `≥ b`. -/
def towerA (B : Type) [TopologicalSpace B] (b₀ : B) (b : ℕ) (hb : 2 ≤ b)
    (hB : ∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) B b₀)) :
    (k : ℕ) → StA B b₀ (b - 2 + k) :=
  Nat.rec (baseState B b₀ b hb hB) (fun _ ih => killStep (genStep ih))

/-- **The CW model in a homotopy range.**  For a `(b-1)`-connected space `B` (`b ≥ 2`) and any `N`
there is a path connected space `Γ`, a point `γ₀` and a map `g : Γ → B` with `g γ₀ = b₀` which
induces a bijection on `π_i` for every `i ≤ N` *at every base point* of `Γ`. -/
theorem exists_model (B : Type) [TopologicalSpace B] (b₀ : B) (b : ℕ) (hb : 2 ≤ b)
    (hB : ∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) B b₀)) (N : ℕ) :
    ∃ (Γ : Type) (_ : TopologicalSpace Γ) (γ₀ : Γ) (g : C(Γ, B)),
      g γ₀ = b₀ ∧ PathConnectedSpace Γ ∧
        (∀ i : ℕ, i ≤ N → ∀ x : Γ, Function.Bijective (piMapN g i x)) := by
  classical
  set st := towerA B b₀ b hb hB (N + 2) with hst
  -- `B` is path connected, and so is `Γ`
  have hZ : Subsingleton (ZerothHomotopy B) := by
    haveI := hB 0 (by omega : 0 < b)
    refine ⟨fun a b => ?_⟩
    exact (HomotopyGroup.pi0EquivZerothHomotopy (X := B) (x := b₀)).symm.injective
      (Subsingleton.elim _ _)
  haveI hconnB : PathConnectedSpace B :=
    pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk b₀⟩, hZ⟩
  haveI hconnΓ : PathConnectedSpace st.Y := st.conn
  refine ⟨st.Y, st.inst, st.y₀, st.g, st.gbase, st.conn, ?_⟩
  intro i hi x
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · -- `π_0`: both sides are singletons (both spaces are path connected)
    rw [h0]
    have h1 : Subsingleton (HomotopyGroup (Fin 0) st.Y x) :=
      (HomotopyGroup.pi0EquivZerothHomotopy (X := st.Y) (x := x)).injective.subsingleton
    have h2 : Subsingleton (HomotopyGroup (Fin 0) B (st.g x)) :=
      (HomotopyGroup.pi0EquivZerothHomotopy (X := B) (x := st.g x)).injective.subsingleton
    exact ⟨fun a b _ => h1.elim a b, fun y => ⟨default, h2.elim _ _⟩⟩
  · -- `π_i` for `i ≥ 1`, at an arbitrary base point: transfer along path connectedness
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact bijective_piMapN_of_joined st.g (PathConnectedSpace.joined st.y₀ x) (j + 1)
      (st.bij j (by omega))

end

end Work.Serre.CWModel
