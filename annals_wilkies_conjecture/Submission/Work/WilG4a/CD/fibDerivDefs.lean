/-
  WilG4a / CD / `fibDerivDefs` — the vocabulary of the target `fibDerivGraph_mem`.

  Target (`Work.WilG4a.CD.fibDerivGraph_mem`): for a `p`-parameter family `f` whose graph is
  `Ω F0 D (p+2)`-definable, the set of `w = (l, x, y) ∈ ℝ^{p+2}` such that the slice `f_l` is
  `C^j` at `x` and `y = f_l^{(j)}(x)` is `Ω a (b.eval ![D,j]) (p+2)` with `a, b` depending only
  on `p, F0`.

  The *joint* derivative atoms (`SharpDeriv`) are the only `j`-uniform atoms available, so the
  proof has to convert the *fibre* condition (= a condition on the one-variable function
  `t ↦ f l t`) into a condition about the joint function.  The vocabulary introduced here:

  * `fibDerivSet f j`           — the target set `T_j(f) ⊆ ℝ^{p+2}`;
  * `fibGerm f j`               — `Γ ⊆ ℝ^{p+1}`: the punctured fibre neighbourhood of `(l,x)`
                                  lies in the joint `C^j` locus `smoothLocus f j`.  On `Γ` the
                                  slice is `C^j` on a punctured neighbourhood, so
                                  `Work.WilG4a.CD.punctured_contDiffAt` converts the fibre
                                  condition into limits along the fibre;
  * `fibLimitSet f A`           — the `Ω`-construction "the `A`-values along the fibre tend to
                                  the last coordinate" (this is exactly the set constructed by
                                  `Submission.Work.WilG4a.CD.fibreLimitEqMem`);
  * `fibCauchySet f A`          — the companion "the `A`-values along the fibre are Cauchy"
                                  (exactly the set of `Submission.Work.WilG4a.CD.fibreLimitMem`);
  * `fibValLim f`, `fibValC f`  — the value limit of `f` itself, and the resulting "the family
                                  is continuous in `x`" locus;
  * `fibLimSet f m`             — the limit of the `m`-th joint `x`-derivative along the fibre;
  * `fibMainSet f j`            — the `Ω`-approximation `R` of `T_j(f)`: `Γ`, `fibValC`, and the
                                  limits of the first `j` joint `x`-derivatives.  The proof of
                                  the target shows `T_j = R` on `Γ × ℝ`, and exhibits the part
                                  of `T_j` outside `Γ × ℝ` (which lies over *thin* parameter
                                  cells of a cylindrical decomposition) as a pullback of the
                                  same statement with fewer parameters.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a.CD
open WilkiesDesign

/-! ## The target set -/

/-- `T_j(f)`: the graph of the `j`-th fibre derivative of the family `f`. -/
def fibDerivSet {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) : Set (Fin (p + 2) → ℝ) :=
  {w | ContDiffAt ℝ j (fun x : ℝ => f (Fin.init (Fin.init w)) x) ((Fin.init w) (Fin.last p)) ∧
    w (Fin.last (p + 1)) =
      iteratedDeriv j (fun x : ℝ => f (Fin.init (Fin.init w)) x) ((Fin.init w) (Fin.last p))}

/-- `Γ_j(f)`: the points `(l,x)` whose punctured fibre neighbourhood is contained in the
interior of the joint `C^j` locus. -/
def fibGerm {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) : Set (Fin (p + 1) → ℝ) :=
  {z | ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, t ≠ z (Fin.last p) →
    |t - z (Fin.last p)| < ρ → Fin.snoc (Fin.init z) t ∈ Work.WilG4a.smoothLocus f j}

/-! ## The two generic `Ω`-constructions along a fibre -/

/-- For a set `A ⊆ ℝ^{p+2}`, the set of `w : ℝ^{p+2}` such that the `A`-values along the fibre
`t ↦ Fin.snoc (Fin.snoc (Fin.init (Fin.init w)) t) v` tend to `w (Fin.last (p+1))` as `t` tends
to `(Fin.init w) (Fin.last p)`.  This is the set handled by
`Submission.Work.WilG4a.CD.fibreLimitEqMem`. -/
def fibLimitSet {p : ℕ} (A : Set (Fin (p + 2) → ℝ)) : Set (Fin (p + 2) → ℝ) :=
  {w | ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ t : ℝ, t ≠ (Fin.init w) (Fin.last p) →
      |t - (Fin.init w) (Fin.last p)| < δ →
      ∀ v : ℝ, Fin.snoc (Fin.snoc (Fin.init (Fin.init w)) t) v ∈ A →
        |v - w (Fin.last (p + 1))| ≤ ε}

/-- For a set `A ⊆ ℝ^{p+2}`, the set of `z : ℝ^{p+1}` such that the `A`-values along the fibre
over `z` are Cauchy at `z (Fin.last p)`.  This is the set handled by
`Submission.Work.WilG4a.CD.fibreLimitMem`. -/
def fibCauchySet {p : ℕ} (A : Set (Fin (p + 2) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  {z | ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t t' : ℝ, t ≠ z (Fin.last p) →
    t' ≠ z (Fin.last p) → |t - z (Fin.last p)| < δ → |t' - z (Fin.last p)| < δ →
    ∀ v v' : ℝ, Fin.snoc (Fin.snoc (Fin.init z) t) v ∈ A →
      Fin.snoc (Fin.snoc (Fin.init z) t') v' ∈ A → |v - v'| ≤ ε}

/-- The value limit of the family along the fibre: `w = (l,x,y)` belongs to `fibValLim f` iff
`f l t → y` as `t → x` (`t ≠ x`). -/
def fibValLim {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 2) → ℝ) :=
  fibLimitSet (Work.WilG4a.graphFam f)

/-- The set of `(l,x)` for which the family is continuous in `x` along the fibre, i.e. the limit
of `t ↦ f l t` at `x` exists and equals `f l x`. -/
def fibValC {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 1) → ℝ) :=
  projLast (fibValLim f ∩ Work.WilG4a.graphFam f)

/-- The limit of the `m`-th joint `x`-derivative along the fibre. -/
def fibLimSet {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (m : ℕ) : Set (Fin (p + 2) → ℝ) :=
  fibLimitSet (Work.WilG4a.derivGraphSet f m)

/-- The Cauchy condition for the `m`-th joint `x`-derivative along the fibre. -/
def fibCauchy {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (m : ℕ) : Set (Fin (p + 1) → ℝ) :=
  fibCauchySet (Work.WilG4a.derivGraphSet f m)

/-! ## The `Ω`-approximation `R` of the target -/

/-- `R_j(f)`: the candidate `Ω`-definable approximation of `T_j(f)` — the fibre germ, the
fibre continuity of `f` itself, the limit of the `j`-th joint `x`-derivative along the fibre,
and the existence of the limits of all the lower joint `x`-derivatives along the fibre. -/
def fibMainSet {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) : Set (Fin (p + 2) → ℝ) :=
  {w | Fin.init w ∈ fibGerm f j ∧ Fin.init w ∈ fibValC f ∧ w ∈ fibLimSet f j ∧
    ∀ m ∈ Finset.Icc 1 j, Fin.init w ∈ projLast (fibLimSet f m)}

/-! ## Parametrisation of a thin parameter cell -/

/-- The graph of a parametrisation `Ψ : ℝ^k → ℝ^p`, in the layout produced by
`Work.WilG1.Choice.G1_choice_proved` (first `k` coordinates the parameter `u`, last `p`
coordinates the value `Ψ u`). -/
def paramGraph {p k : ℕ} (Ψ : (Fin k → ℝ) → (Fin p → ℝ)) : Set (Fin (k + p) → ℝ) :=
  {z | ∀ j : Fin p, z (Fin.natAdd k j) = Ψ (z ∘ Fin.castAdd p) j}

/-- The coordinate map `Fin (k+2) → Fin (p+2)` which sends the parameter coordinates `0..k-1`
to `e 0 .. e (k-1)`, the coordinate `k` to `p` (the `x`-coordinate) and `k+1` to `p+1` (the
value coordinate).  It is used to read the `(k+2)`-tuple `(l ∘ e, x, y)` off a `(p+2)`-tuple
`(l, x, y)`. -/
def cutIdx (p k : ℕ) (e : Fin k ↪ Fin p) : Fin (k + 2) → Fin (p + 2) :=
  Fin.addCases (fun i : Fin k => ⟨(e i).val, by have := (e i).isLt; omega⟩)
    (fun i : Fin 2 => ⟨p + (i : ℕ), by have := i.isLt; omega⟩)

@[simp] theorem mem_paramGraph {p k : ℕ} (Ψ : (Fin k → ℝ) → (Fin p → ℝ))
    (z : Fin (k + p) → ℝ) :
    z ∈ paramGraph Ψ ↔ ∀ j : Fin p, z (Fin.natAdd k j) = Ψ (z ∘ Fin.castAdd p) j :=
  Iff.rfl

@[simp] theorem mem_fibDerivSet {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ)
    (w : Fin (p + 2) → ℝ) :
    w ∈ fibDerivSet f j ↔
      ContDiffAt ℝ j (fun x : ℝ => f (Fin.init (Fin.init w)) x) ((Fin.init w) (Fin.last p)) ∧
      w (Fin.last (p + 1)) =
        iteratedDeriv j (fun x : ℝ => f (Fin.init (Fin.init w)) x)
          ((Fin.init w) (Fin.last p)) := Iff.rfl

@[simp] theorem mem_fibGerm {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ)
    (z : Fin (p + 1) → ℝ) :
    z ∈ fibGerm f j ↔ ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, t ≠ z (Fin.last p) →
      |t - z (Fin.last p)| < ρ → Fin.snoc (Fin.init z) t ∈ Work.WilG4a.smoothLocus f j :=
  Iff.rfl

@[simp] theorem mem_fibLimSet {p : ℕ} (A : Set (Fin (p + 2) → ℝ)) (w : Fin (p + 2) → ℝ) :
    w ∈ fibLimitSet A ↔ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, t ≠ (Fin.init w) (Fin.last p) →
        |t - (Fin.init w) (Fin.last p)| < δ →
        ∀ v : ℝ, Fin.snoc (Fin.snoc (Fin.init (Fin.init w)) t) v ∈ A →
          |v - w (Fin.last (p + 1))| ≤ ε :=
  Iff.rfl

@[simp] theorem mem_fibCauchySet {p : ℕ} (A : Set (Fin (p + 2) → ℝ)) (z : Fin (p + 1) → ℝ) :
    z ∈ fibCauchySet A ↔ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t t' : ℝ, t ≠ z (Fin.last p) →
      t' ≠ z (Fin.last p) → |t - z (Fin.last p)| < δ → |t' - z (Fin.last p)| < δ →
      ∀ v v' : ℝ, Fin.snoc (Fin.snoc (Fin.init z) t) v ∈ A →
        Fin.snoc (Fin.snoc (Fin.init z) t') v' ∈ A → |v - v'| ≤ ε := Iff.rfl

@[simp] theorem mem_fibMainSet {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ)
    (w : Fin (p + 2) → ℝ) :
    w ∈ fibMainSet f j ↔ Fin.init w ∈ fibGerm f j ∧ Fin.init w ∈ fibValC f ∧
      w ∈ fibLimSet f j ∧ ∀ m ∈ Finset.Icc 1 j, Fin.init w ∈ projLast (fibLimSet f m) :=
  Iff.rfl

end Work.WilG4a.CD
