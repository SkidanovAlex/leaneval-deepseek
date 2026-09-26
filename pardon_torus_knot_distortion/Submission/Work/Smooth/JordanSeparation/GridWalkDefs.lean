import Mathlib

/-!
# Closed walks on a scaled unit square lattice, and their geometric realization

We set up the combinatorial notion of a closed walk on the lattice `ℤ × ℤ` (unit steps in the four
coordinate directions), scaled by a *mesh* `c > 0`, together with its geometric realization in `ℂ`
as the polygonal path joining the successive vertices.  This is the combinatorial substrate for the
polygonal decomposition of loops in an open set: a loop in an open set `U` of `ℂ` is freely
homotopic to the realization of such a walk (a "staircase" approximation, for a mesh small enough
that the walk fits in `U`), and a closed walk decomposes into simple cycles.

* `gpt` — the point of `ℂ` attached to a lattice point;
* `GridStep` — the adjacency relation of the lattice graph;
* `GridWalk` — a closed walk (vertices, mesh `c`, adjacency, closedness);
* `GridWalk.IsSimpleCycle` — no repeated vertex; `GridWalk.IsSubCycleEdges` — only edges of `W`;
* `segPath` — the straight segment between two points of `ℂ`, as a `Path`;
* `walkPath` — the realization of a walk, as a `Path` in `ℂ`;
* `FreeHomotopic` — free homotopy of loops at possibly different base points;
* `Path.liftU` — lifting a path of `ℂ` that stays in `U` to the subtype `↥U`;
* `GridWalk.loopIn` — the realization of a walk as a loop in `↥U`.
-/

open Set

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- The complex number attached to a lattice point. -/
def gpt (p : ℤ × ℤ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

theorem gpt_injective : Function.Injective gpt := by
  intro p q h
  have h1 : (p.1 : ℝ) = (q.1 : ℝ) := by
    have := congrArg Complex.re h
    simpa [gpt, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im] using this
  have h2 : (p.2 : ℝ) = (q.2 : ℝ) := by
    have := congrArg Complex.im h
    simpa [gpt, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im] using this
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- `GridStep p q` : `q` is obtained from `p` by one unit step of the square lattice. -/
def GridStep (p q : ℤ × ℤ) : Prop :=
  (p.1 = q.1 ∧ (q.2 = p.2 + 1 ∨ p.2 = q.2 + 1)) ∨
    (p.2 = q.2 ∧ (q.1 = p.1 + 1 ∨ p.1 = q.1 + 1))

theorem gridStep_symm {p q : ℤ × ℤ} (h : GridStep p q) : GridStep q p := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · exact Or.inl ⟨h1.symm, Or.inr h2⟩
  · exact Or.inl ⟨h1.symm, Or.inl h2⟩
  · exact Or.inr ⟨h1.symm, Or.inr h2⟩
  · exact Or.inr ⟨h1.symm, Or.inl h2⟩

theorem gridStep_gpt {p q : ℤ × ℤ} (h : GridStep p q) : ‖gpt q - gpt p‖ = 1 := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · have hq1 : (q.1 : ℂ) = (p.1 : ℂ) := by rw [h1]
    have hq2 : (q.2 : ℂ) = (p.2 : ℂ) + 1 := by rw [h2]; push_cast; ring
    have : gpt q - gpt p = Complex.I := by simp only [gpt, hq1, hq2]; ring
    rw [this, Complex.norm_I]
  · have hq1 : (q.1 : ℂ) = (p.1 : ℂ) := by rw [h1]
    have hq2 : (p.2 : ℂ) = (q.2 : ℂ) + 1 := by rw [h2]; push_cast; ring
    have : gpt q - gpt p = -Complex.I := by simp only [gpt, hq1, hq2]; ring
    rw [this, norm_neg, Complex.norm_I]
  · have hq1 : (q.2 : ℂ) = (p.2 : ℂ) := by rw [h1]
    have hq2 : (q.1 : ℂ) = (p.1 : ℂ) + 1 := by rw [h2]; push_cast; ring
    have : gpt q - gpt p = 1 := by simp only [gpt, hq1, hq2]; ring
    rw [this, norm_one]
  · have hq1 : (q.2 : ℂ) = (p.2 : ℂ) := by rw [h1]
    have hq2 : (p.1 : ℂ) = (q.1 : ℂ) + 1 := by rw [h2]; push_cast; ring
    have : gpt q - gpt p = -1 := by simp only [gpt, hq1, hq2]; ring
    rw [this, norm_neg, norm_one]

/-- A closed walk in the square lattice, scaled by the mesh `c > 0`. -/
structure GridWalk where
  /-- number of edges -/
  n : ℕ
  /-- at least one edge -/
  pos : 0 < n
  /-- the mesh -/
  c : ℝ
  /-- the mesh is positive -/
  cpos : 0 < c
  /-- the vertices -/
  v : Fin (n + 1) → ℤ × ℤ
  /-- consecutive vertices are lattice neighbours -/
  step : ∀ i : Fin n, GridStep (v i.castSucc) (v i.succ)
  /-- the walk is closed -/
  closed : v 0 = v (Fin.last n)

namespace GridWalk

variable (W : GridWalk)

/-- The `i`-th vertex of the walk, as a point of `ℂ` (scaled by the mesh). -/
def pt (i : Fin (W.n + 1)) : ℂ := W.c * gpt (W.v i)

theorem pt_last_eq : W.pt (Fin.last W.n) = W.pt 0 := by
  show W.c * gpt (W.v (Fin.last W.n)) = W.c * gpt (W.v 0)
  rw [← W.closed]

/-- A walk is a *simple cycle* if its vertices (except the coincident first and last) are pairwise
distinct. -/
def IsSimpleCycle : Prop :=
  ∀ i j : Fin W.n, W.v i.castSucc = W.v j.castSucc → i = j

/-- `C` uses only edges of `W` (in either direction). -/
def IsSubCycleEdges (C : GridWalk) : Prop :=
  ∀ i : Fin C.n, ∃ j : Fin W.n,
    (C.v i.castSucc = W.v j.castSucc ∧ C.v i.succ = W.v j.succ) ∨
    (C.v i.castSucc = W.v j.succ ∧ C.v i.succ = W.v j.castSucc)

end GridWalk

/-- The straight segment from `p` to `q` in `ℂ`. -/
def segPath (p q : ℂ) : Path p q := Path.segment p q

theorem segPath_range (p q : ℂ) : Set.range (segPath p q) = segment ℝ p q :=
  Path.range_segment p q

theorem segPath_mem_segment (p q z : ℂ) (hz : z ∈ Set.range (segPath p q)) :
    z ∈ segment ℝ p q := by
  rw [← segPath_range]; exact hz

/-- The geometric realization of a lattice walk with mesh `c`, from its first to its last vertex. -/
def walkPath : ∀ (c : ℝ) (n : ℕ) (v : Fin (n + 1) → ℤ × ℤ),
    Path (c * gpt (v 0)) (c * gpt (v (Fin.last n)))
  | c, 0, v => Path.refl (c * gpt (v 0))
  | c, n + 1, v =>
      (walkPath c n (fun i => v i.castSucc)).trans
        (segPath (c * gpt (v ⟨n, by omega⟩)) (c * gpt (v (Fin.last (n + 1)))))

/-- Two loops of a space (at possibly different base points) are *freely homotopic* if the
conjugate of the first by some path joining the base points is homotopic to the second. -/
def FreeHomotopic {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x x) (q : Path y y) : Prop :=
  ∃ (a : Path x y), Path.Homotopic (a.symm.trans (p.trans a)) q

/-- Lift a path in `ℂ` to the subtype `↥U`, given that it takes all its values in `U`. -/
def Path.liftU {U : Set ℂ} {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) (p : Path a b)
    (hp : ∀ t, p t ∈ U) : Path (⟨a, ha⟩ : ↥U) (⟨b, hb⟩ : ↥U) where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := Continuous.subtype_mk p.continuous hp
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

namespace GridWalk

variable (W : GridWalk)

/-- The realization of a grid walk as a loop in the subtype `↥U`, given that the walk stays in
`U`. -/
def loopIn {U : Set ℂ} (hbase : W.pt 0 ∈ U)
    (hlast : W.pt (Fin.last W.n) ∈ U) (hval : ∀ t, walkPath W.c W.n W.v t ∈ U) :
    Path (⟨W.pt 0, hbase⟩ : ↥U) (⟨W.pt 0, hbase⟩ : ↥U) :=
  Path.cast (Path.liftU hbase hlast (walkPath W.c W.n W.v) hval) rfl
    (Subtype.ext (by show W.c * gpt (W.v 0) = W.c * gpt (W.v (Fin.last W.n))
                     rw [W.closed]))

end GridWalk

end

end Work.Smooth.JordanSeparation
