/-
  Area C2 (WilC2): `meetsDefinable_dcl`.

  In a structure whose definable subsets of the line are finite unions of convex sets (here:
  `LRc`-definable subsets of every model of `TR`, which is what `C2_models_ominimal_proved`
  delivers), the definable closure `Dcl A` of a parameter set meets every nonempty
  `Dcl A`-definable subset of the line: `Dcl A` satisfies the Tarski–Vaught condition, hence is
  an elementary substructure of `M`.

  Proof.
  * `Dcl` is *idempotent*: `Dcl (Dcl A) = Dcl A`.  This is `Work.WilC4.dcl_idem` transported
    along the (harmless) difference of the two formalisations of "singleton definable"
    (`Dcl A = {x | A.Definable LRc {fun _ : Fin 1 => x}}`), see `dcl_eq_WilC4`.
  * Given a nonempty `Dcl A`-definable `D`, the parametric extraction `definable_fin_params_of`
    writes `D` as a fibre of an `LRc`-formula `φ` in finitely many parameters `v`, all of them
    lying in `Dcl A`.
  * *Definable choice* (`definable_choice_fibre`) then selects an element `y` of the nonempty
    fibre in a way that depends definably on the parameters: `y` is the unique solution of a
    formula with the parameters `v`.
  * Uniqueness makes `{y}` `Dcl A`-definable, i.e. `y ∈ Dcl (Dcl A) = Dcl A`, and `y ∈ D` by
    construction.

  Besides the definitions of the area, the only inputs are the two proved results
  `Work.WilC2.definable_choice_fibre` (definable choice on fibres) and `Work.WilC4.dcl_idem`
  (idempotence of the definable closure).
-/
import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.definable_choice_fibre
import Submission.Work.WilC2.Main
import Submission.Work.WilC2.Uniform
import Submission.Work.WilC4.dcl_idem

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign WilkiesDesign.CG

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]

/-! ## 1. The two formulations of the definable closure agree -/

/-- The set of `Fin 1`-tuples whose `0`-th coordinate lies in `{x}` is the singleton of the
constant tuple `fun _ => x`.  This is the only bridge needed between the `Set.Definable₁`
formulation of "the singleton `{x}` is definable" and the explicit tuple formulation used by
`Work.WilC4.Dcl`. -/
lemma setOf_mem_singleton_eq_const (x : M) :
    ({v : Fin 1 → M | v 0 ∈ ({x} : Set M)} : Set (Fin 1 → M)) = {fun _ : Fin 1 => x} := by
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    rw [Subsingleton.elim i 0]
    exact h
  · intro h
    rw [h]

/-- `Work.WilC2.Dcl` (singletons as `Set.Definable₁`) and `Work.WilC4.Dcl` (singletons as
constant `Fin 1`-tuples) define the same closure of a parameter set. -/
lemma dcl_eq_WilC4 (A : Set M) : Work.WilC4.Dcl (∅ : Set M) A = Dcl A := by
  ext x
  simp only [Work.WilC4.Dcl, Work.WilC4.DefinableElt, Set.empty_union, mem_dcl, Set.Definable₁,
    Set.mem_ofPred_eq, setOf_mem_singleton_eq_const]

/-- `Work.WilC4.Dcl S ∅` is symmetric in its first argument: the two parameter sets are
unioned. -/
lemma wilC4_dcl_swap (A : Set M) :
    Work.WilC4.Dcl A (∅ : Set M) = Work.WilC4.Dcl (∅ : Set M) A := by
  simp only [Work.WilC4.Dcl, Work.WilC4.DefinableElt, Set.union_empty, Set.empty_union]

/-- **Idempotence of the definable closure**, transported from `Work.WilC4.dcl_idem`. -/
lemma dcl_idem (A : Set M) : Dcl (Dcl A) = Dcl A := by
  have h1 : Work.WilC4.Dcl (∅ : Set M) A = Dcl A := dcl_eq_WilC4 A
  have h2 : Work.WilC4.Dcl (∅ : Set M) (Dcl A) = Dcl (Dcl A) := dcl_eq_WilC4 (Dcl A)
  have h3 : Work.WilC4.Dcl (Dcl A) (∅ : Set M) = Work.WilC4.Dcl (∅ : Set M) A := by
    have h := Work.WilC4.dcl_idem (M := M) (∅ : Set M) A (∅ : Set M)
    rw [h1, Set.union_empty] at h
    exact h
  rw [← h2, ← wilC4_dcl_swap (Dcl A), h3, h1]

/-! ## 2. Finite parameters whose defining formula holds -/

/-- **Finitely many parameters in `T` suffice.**  Every `T`-definable `X ⊆ M¹` is the fibre of
an `LRc`-formula in finitely many parameters, all of them lying in `T`.  (Same proof as
`definable_fin_params`, but with the parameter set `T` in place of `Set.univ`.) -/
lemma definable_fin_params_of {T : Set M} {X : Set (Fin 1 → M)} (h : T.Definable LRc X) :
    ∃ (n : ℕ) (φ : ParamFormula n) (v : Fin n → M),
      (∀ i, v i ∈ T) ∧ X = {x : Fin 1 → M | φ.Realize (Sum.elim v x)} := by
  classical
  obtain ⟨ψ, hψ⟩ :=
    (Set.definable_iff_exists_formula_sum (A := T) (L := LRc) (α := Fin 1)).mp h
  obtain ⟨n, σ, χ, hχ⟩ := exists_fin_relabel_elim (L := LRc) (M := M) (k := 1) ψ
  refine ⟨n, χ, (Subtype.val : ↥T → M) ∘ σ, fun i => (σ i).2, ?_⟩
  rw [hψ]
  ext x
  simp only [Set.mem_ofPred_eq]
  exact (hχ (Subtype.val : ↥T → M) x).symm

/-- **A parametric formula with parameters in `A` gives an `A`-definable set**: the fibre
`{v | φ.Realize (Sum.elim c v)}` is definable over `A` as soon as every `c i` lies in `A`.
This is the reverse direction of `definable_fin_params_of`, proved by renaming the parameter
block of `φ` onto constants of the language `L[[A]]`. -/
lemma definable_of_param_formula {L : FirstOrder.Language} {N : Type} [L.Structure N]
    {A : Set N} {γ α : Type*} (c : γ → N) (hc : ∀ i, c i ∈ A) (φ : L.Formula (γ ⊕ α)) :
    A.Definable L {v : α → N | φ.Realize (Sum.elim c v)} := by
  refine (Set.definable_iff_exists_formula_sum (A := A) (L := L) (α := α)).mpr
    ⟨φ.relabel (Sum.map (fun i => (⟨c i, hc i⟩ : A)) id), ?_⟩
  ext v
  simp only [Set.mem_ofPred_eq]
  rw [Formula.realize_relabel]
  have h : Sum.elim c v = (Sum.elim Subtype.val v) ∘
      Sum.map (fun i => (⟨c i, hc i⟩ : A)) id := by
    funext a
    rcases a with i | b <;> rfl
  rw [h]

/-! ## 3. The main result -/

theorem meetsDefinable_dcl
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hC0 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc X → WilkiesDesign.RExpExist X)
    (hUF : WilkiesDesign.CG.UnifFiniteRExp)
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [M ⊨ WilkiesDesign.CG.TR] (A : Set M) :
    FirstOrder.Language.MeetsDefinable (L := WilkiesDesign.CG.LRc) (Dcl A) := by
  classical
  intro D hDne hDdef
  -- `D` is the fibre of a parametric formula in finitely many parameters, all in `Dcl A`.
  obtain ⟨n, φ, v, hv, hD⟩ :=
    definable_fin_params_of (T := Dcl A) (X := {u : Fin 1 → M | u 0 ∈ D}) hDdef
  have hmem : ∀ y : M, y ∈ D ↔ φ.Realize (Sum.elim v (fun _ => y)) := fun y =>
    Set.ext_iff.mp hD (fun _ : Fin 1 => y)
  -- the fibre of `φ` at `v` is nonempty
  have hne : ∃ y : M, φ.Realize (Sum.elim v (fun _ => y)) :=
    let ⟨y, hy⟩ := hDne; ⟨y, (hmem y).mp hy⟩
  -- definable choice on the fibres of `φ`
  obtain ⟨ψ, hψ⟩ := definable_choice_fibre (M := M) hR hC0 hUF φ
  obtain ⟨y, ⟨hyψ, hyφ⟩, hyuniq⟩ := hψ v hne
  refine ⟨y, (hmem y).mpr hyφ, ?_⟩
  -- `{y}` is `Dcl A`-definable, since `y` is the unique solution of `ψ(v, ·)` among the
  -- solutions of `ψ(v, ·) ∧ φ(v, ·)`.
  have hset : ({u : Fin 1 → M | ψ.Realize (Sum.elim v u)} ∩
      {u : Fin 1 → M | φ.Realize (Sum.elim v u)}) = {fun _ : Fin 1 => y} := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hu : u = fun _ : Fin 1 => u 0 := by
        funext i; rw [Subsingleton.elim i 0]
      have h1' : ψ.Realize (Sum.elim v (fun _ : Fin 1 => u 0)) := by rw [← hu]; exact h1
      have h2' : φ.Realize (Sum.elim v (fun _ : Fin 1 => u 0)) := by rw [← hu]; exact h2
      have h0 : u 0 = y := hyuniq (u 0) ⟨h1', h2'⟩
      funext i
      rw [Subsingleton.elim i 0]
      exact h0
    · intro hu
      subst hu
      exact ⟨hyψ, hyφ⟩
  have hyDcl : y ∈ Dcl (Dcl A) := by
    rw [mem_dcl, Set.Definable₁, setOf_mem_singleton_eq_const y, ← hset]
    exact (definable_of_param_formula v hv ψ).inter (definable_of_param_formula v hv φ)
  rwa [dcl_idem A] at hyDcl

end Work.WilC2
