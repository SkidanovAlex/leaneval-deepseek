/-
  WilC5 — finite satisfiability of the type of an element over a partial elementary map.

  Given a partial elementary map `τ : B → M` (`B ⊆ N`) and a point `m ∈ M`, the fibres of the
  *type of `m` over `B`* — the set of formulas `ψ` of `L[[B]]` with one free variable satisfiable
  at `m` over the parameters `τ(B)` — are finitely satisfiable in `N` over the parameters `B`.

  This is the finite-satisfiability input to the one-point extension step `elemOn_extend`: the
  finite conjunction of a finite fragment is existentially quantified in the single free variable,
  producing a formula of `L[[B]]` (no free variables), which is transported across the elementary
  map `τ` by elementarity.
-/
import Mathlib
import Submission.Work.WilC5.ExtSatAux

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open FirstOrder Language

/-- **Finite satisfiability across a partial elementary map.**  If `τ : B → M` is elementary
(`B ⊆ N`) and the tuple `(m)` realizes in `M` a finite set `F` of formulas of `L[[B]]` with one
free variable (over the parameters `τ(B)`), then `(x)` realizes `F` in `N` for some `x : Fin 1 → N`
(over the parameters `B`).

Concretely: the conjunction `Φ` of the fragment satisfies `Φ(τ(b̄), m)`, hence
`∃ y Φ(τ(b̄), y)` holds in `M`; elementarity transfers it to `N`, giving the required `x`. -/
theorem finSat_of_elemOn {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M]
    [L.Structure N] {B : Set N} {τ : B → M} (h : @ElemOn L M N _ _ B τ) (m : M) :
    ∀ F : Finset (L.Formula (B ⊕ Fin 1)),
      (∀ ψ ∈ F, ψ.Realize (Sum.elim τ (fun _ : Fin 1 => m))) →
      ∃ x : Fin 1 → N, ∀ ψ ∈ F, ψ.Realize (Sum.elim (Subtype.val : B → N) x) := by
  intro F hF
  classical
  haveI : Finite {ψ : L.Formula (B ⊕ Fin 1) // ψ ∈ F} := F.finite_toSet.to_subtype
  set w : B ⊕ Fin 1 → M := Sum.elim τ (fun _ : Fin 1 => m) with hw
  -- the conjunction of the finite fragment
  set Φ : L.Formula (B ⊕ Fin 1) :=
    Formula.iInf (fun ψ : {ψ : L.Formula (B ⊕ Fin 1) // ψ ∈ F} => ψ.1) with hΦ
  have hΦw : Φ.Realize w := by
    rw [hΦ, Formula.realize_iInf]
    intro ψ
    exact hF ψ.1 ψ.2
  -- existentially quantify the single free variable: a formula of `L[[B]]` with no free variables
  have hEx : (Φ.iExs (Fin 1)).Realize τ := by
    rw [Formula.realize_iExs]
    exact ⟨fun _ : Fin 1 => m, hΦw⟩
  -- elementarity transports it to `N`
  have hExN : (Φ.iExs (Fin 1)).Realize (Subtype.val : B → N) := (h _).mpr hEx
  obtain ⟨x, hx⟩ := (Formula.realize_iExs).mp hExN
  refine ⟨x, fun ψ hψ => ?_⟩
  rw [hΦ] at hx
  exact (Formula.realize_iInf).mp hx ⟨ψ, hψ⟩

end Work.WilC5
