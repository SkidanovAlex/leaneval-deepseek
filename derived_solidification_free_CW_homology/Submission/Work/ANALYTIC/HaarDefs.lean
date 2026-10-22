import Mathlib
import Submission.Work.ATOM.ZS.Data

/-!
# The "Haar/Schauder" basis of `C(T,ℤ)` and its dual (AN3, REFS/03 §4)

For an infinite light profinite set `T` we use the level structure of `Work.ATOM.LevelData`
(`s₀`, `e n`, `A n`, the enumeration `a j` of `D \ {s₀}` and the level `lvl j = lv (a j)`) to
define, following REFS/03 §4:

* `par T j` — the "parent" `e_{n(j)-1}(a_j)` of the `j`-th new point `a_j` (and `s₀` when
  `n(j) = 0`), i.e. the map `β` of `Submission/Work/ATOM/ZS/Topo/Defs.lean` at the point `a_j`;
* `phi T j : LC T → ℤ` — the functional `λ ↦ λ(a_j) − λ(par j)`;
* `fCyl T j : LC T` — the *cylinder* `C_j = π_{n(j)}⁻¹(π_{n(j)} a_j)`, i.e. the locally constant
  function which is `1` on the level-`n(j)` fibre of `a_j` and `0` elsewhere.

The theory (proved in `haar_biorth` and `haar_expand`) is that these are *dual bases*:
`phi i (fCyl j) = δᵢⱼ` and every `λ` is the finite sum `Σ_j (phi j λ) • fCyl j + (λ s₀) • 1`, i.e.
`{fCyl j | j : ℕ} ∪ {1}` is a ℤ-basis of `C(T,ℤ)` whose dual coordinates are the `phi j`'s together
with the evaluation at `s₀`.  This is the input for the identification `ℤ■[T] ≅ ∏ℤ` of
REFS/03 §4.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

namespace Haar

/-- The ℤ-module of locally constant `ℤ`-valued functions on a light profinite set; these are the
sections of `C(T,ℤ)_disc = Cdisc T` at the point.

It is placed inside the `Haar` namespace (rather than at the top level of `Work.ANALYTIC`)
because `Submission/Work/ANALYTIC/preSolid_setup.lean` already uses the name
`Work.ANALYTIC.LC` for the functor `CochainComplex LightCondAb ℤ ⥤ CochainComplex LightCondAb ℤ`;
any module importing both that file (e.g. through `Main.lean`, `Unconditional.lean`,
`cBounded_solidEquiv.lean`) and this one would otherwise clash. -/
abbrev LC (T : LightProfinite.{0}) : Type := LocallyConstant ↥T ℤ

variable (T : LightProfinite.{0}) [Infinite T]

/-- The "parent" of the `j`-th enumerated new point `a_j`: `e_{n(j)-1} a_j` when `n(j) ≥ 1`, and
the base point `s₀` when `n(j) = 0`.  (This is the map `β` of `Work.ATOM.betaFun` at the point
`(j, a_j)`.) -/
def par (j : ℕ) : ↥T :=
  if h : Work.ATOM.lvl T j = 0 then (Work.ATOM.levelData T).s₀
  else Work.ATOM.e T (Work.ATOM.lvl T j - 1) ((Work.ATOM.levelData T).a j)

/-- **The functional `φ_j`** of REFS/03 §4: `φ_j(λ) = λ(a_j) − λ(p_j)`, with `p_j = par j`. -/
def phi (j : ℕ) (lam : LC T) : ℤ :=
  lam ((Work.ATOM.levelData T).a j) - lam (par T j)

/-- **The cylinder `C_j`**: the level-`n(j)` fibre of `a_j`, i.e. the clopen set
`π_{n(j)}⁻¹ {π_{n(j)} a_j}`. -/
def cyl (j : ℕ) : Set ↥T :=
  {x | T.proj (Work.ATOM.lvl T j) x
        = T.proj (Work.ATOM.lvl T j) ((Work.ATOM.levelData T).a j)}

theorem isClopen_cyl (j : ℕ) : IsClopen (cyl T j) := by
  haveI : DiscreteTopology ↥(T.component (Work.ATOM.lvl T j)) :=
    Work.ATOM.instDiscreteComponent T (Work.ATOM.lvl T j)
  have hcont : Continuous (fun x : ↥T => T.proj (Work.ATOM.lvl T j) x) :=
    (T.proj (Work.ATOM.lvl T j)).hom.hom.continuous
  have h : cyl T j = (fun x : ↥T => T.proj (Work.ATOM.lvl T j) x) ⁻¹'
      ({(T.proj (Work.ATOM.lvl T j)) ((Work.ATOM.levelData T).a j)} :
        Set ↥(T.component (Work.ATOM.lvl T j))) := rfl
  rw [h]
  exact ⟨isClosed_discrete _ |> IsClosed.preimage hcont, isOpen_discrete _ |> IsOpen.preimage hcont⟩

/-- **The dual basis element `f_j`**: the indicator of the cylinder `C_j`. -/
def fCyl (j : ℕ) : LC T :=
  ⟨fun x => if T.proj (Work.ATOM.lvl T j) x
      = T.proj (Work.ATOM.lvl T j) ((Work.ATOM.levelData T).a j) then 1 else 0, by
    rw [IsLocallyConstant.iff_continuous]
    haveI : DiscreteTopology ↥(T.component (Work.ATOM.lvl T j)) :=
      Work.ATOM.instDiscreteComponent T (Work.ATOM.lvl T j)
    have h1 : Continuous (fun y : ↥(T.component (Work.ATOM.lvl T j)) =>
        if y = (T.proj (Work.ATOM.lvl T j)) ((Work.ATOM.levelData T).a j) then (1:ℤ) else 0) :=
      continuous_of_discreteTopology
    exact h1.comp (T.proj (Work.ATOM.lvl T j)).hom.hom.continuous⟩

/-- The defining values of `f_j`. -/
theorem fCyl_apply (j : ℕ) (x : ↥T) :
    fCyl T j x = if T.proj (Work.ATOM.lvl T j) x
        = T.proj (Work.ATOM.lvl T j) ((Work.ATOM.levelData T).a j) then 1 else 0 := rfl

/-- `a_j` lies in its own cylinder. -/
theorem fCyl_mem_cyl (j : ℕ) : (Work.ATOM.levelData T).a j ∈ cyl T j := rfl

/-- `f_j(a_j) = 1`. -/
theorem fCyl_self (j : ℕ) : fCyl T j ((Work.ATOM.levelData T).a j) = 1 := by
  rw [fCyl_apply, if_pos rfl]

/-- **`f_j(s₀) = 0`**: the base point is not in any cylinder (it is not an `a_j`).
This is what lets the coordinate maps `κ_j` (the "evaluation at `f_j`", see
`Work.ATOM.ZS.Unred.LocallyConstantIndicator`) factor through the reduced quotient
`ℤ̃[T] = ℤ[T]/ℤ[s₀]`. -/
theorem fCyl_s₀ (j : ℕ) : fCyl T j ((Work.ATOM.levelData T).s₀) = 0 := by
  rw [fCyl_apply]
  have h : ¬ (T.proj (Work.ATOM.lvl T j) ((Work.ATOM.levelData T).s₀)
      = T.proj (Work.ATOM.lvl T j) ((Work.ATOM.levelData T).a j)) := by
    intro hc
    have hfix := (Work.ATOM.levelData T).e_fix (Work.ATOM.lvl T j)
    have halv : Work.ATOM.e T (Work.ATOM.lvl T j) ((Work.ATOM.levelData T).a j)
        = (Work.ATOM.levelData T).a j := (Work.ATOM.levelData T).e_lv_a j
    rw [Work.ATOM.e_apply] at hfix halv
    rw [hc] at hfix
    exact Work.ATOM.levelData_a_ne (S := T) j ((hfix.symm.trans halv).symm)
  rw [if_neg h]

/-! ## The index set `ℕ ∪ {∞}`: one extra index for the constant function -/

/-- The index set for the basis: the enumerated new points together with one extra index `∞`,
which accounts for the constant function `1` (the "missing" generator: the functionals `phi j`
all vanish on the constants). -/
abbrev JIdx : Type := OnePoint ℕ

/-- The index `∞`. -/
abbrev inf : JIdx := (∞ : OnePoint ℕ)

/-- The `ℕ`-indexed functional, extended at `∞` by the evaluation at `s₀`. -/
def phiJ (j : JIdx) (lam : LC T) : ℤ :=
  j.elim (lam ((Work.ATOM.levelData T).s₀)) (fun j => phi T j lam)

/-- The `ℕ`-indexed basis element, extended at `∞` by the constant function `1`. -/
def fJ (j : JIdx) : LC T :=
  j.elim (1 : LC T) (fun j => fCyl T j)

@[simp] theorem phiJ_inf (lam : LC T) : phiJ T inf lam = lam ((Work.ATOM.levelData T).s₀) := rfl

@[simp] theorem phiJ_coe (j : ℕ) (lam : LC T) : phiJ T (j : JIdx) lam = phi T j lam := rfl

@[simp] theorem fJ_inf : fJ T inf = 1 := rfl

@[simp] theorem fJ_coe (j : ℕ) : fJ T (j : JIdx) = fCyl T j := rfl

end Haar

end Work.ANALYTIC
