import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1S.BoxQWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.BoxSpectralDefs`

The *joint components* of the commuting family of box projections
`(Pᵢ)_{i ∈ Fin N}`, `(Qᵢ)_{i ∈ Fin N}` (`Pᵢ = boxPInd`, `Qᵢ = boxQInd`):

    boxComp V A S Φ  :=  (∏_{i ∈ S} Pᵢ) ((∏_{j ∉ S} Qⱼ) Φ) ,

realised as a `List.foldr` of the operators over `List.finRange N` (the projections commute, so the
order is irrelevant; the fold makes the definition deterministic and lets every property be proved
by list induction).

These are the objects needed by the *sharp* (operator-`√`) completion of squares of FS
`lm:appinteractionestimate` (FS l.3726–3740): the eigenvalue of `n₀ = ΣⱼPⱼ` on the range of
`boxComp V A S` is `S.card`, so `Σ_S g(S.card) • boxComp V A S Φ` is `g(n₀)Φ` for every
`g : ℕ → ℝ`.  The properties themselves (idempotence, self-adjointness, orthogonality, the
acting rules for `Pᵢ`/`Qᵢ`, and `Σ_S boxComp_S = ∏ᵢ1_A(xᵢ)`) are stated and requested separately.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The **joint component** of `Φ` for the subset of slots `S`:
`(∏_{i∈S}Pᵢ)(∏_{j∉S}Qⱼ)Φ`, written as a fold of the operator list over `List.finRange N`. -/
noncomputable def boxComp {N : ℕ} (V : ℝ) (A : Set E3) (S : Finset (Fin N))
    (Φ : Submission.BoseGases.X N → ℝ) : Submission.BoseGases.X N → ℝ :=
  (List.finRange N).foldl
    (fun g i => (if i ∈ S then Work.UBBInputs8.boxPInd V A i
      else Work.UBBInputs8.boxQInd V A i) g) Φ

/-- `boxComp` as a recursion on the slot list (definitional unfolding target). -/
noncomputable def boxCompAux {N : ℕ} (V : ℝ) (A : Set E3) (S : Finset (Fin N)) :
    List (Fin N) → (Submission.BoseGases.X N → ℝ) → (Submission.BoseGases.X N → ℝ)
  | [], Φ => Φ
  | i :: l, Φ => boxCompAux V A S l
      ((if i ∈ S then Work.UBBInputs8.boxPInd V A i
        else Work.UBBInputs8.boxQInd V A i) Φ)

@[simp] theorem boxCompAux_nil {N : ℕ} (V : ℝ) (A : Set E3) (S : Finset (Fin N))
    (Φ : Submission.BoseGases.X N → ℝ) : boxCompAux V A S [] Φ = Φ := rfl

theorem boxCompAux_cons {N : ℕ} (V : ℝ) (A : Set E3) (S : Finset (Fin N))
    (i : Fin N) (l : List (Fin N)) (Φ : Submission.BoseGases.X N → ℝ) :
    boxCompAux V A S (i :: l) Φ
      = boxCompAux V A S l ((if i ∈ S then Work.UBBInputs8.boxPInd V A i
          else Work.UBBInputs8.boxQInd V A i) Φ) := rfl

theorem boxComp_eq_aux {N : ℕ} (V : ℝ) (A : Set E3) (S : Finset (Fin N))
    (Φ : Submission.BoseGases.X N → ℝ) :
    boxComp V A S Φ = boxCompAux V A S (List.finRange N) Φ := by
  unfold boxComp
  induction List.finRange N generalizing Φ with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons]
    exact ih ((if i ∈ S then Work.UBBInputs8.boxPInd V A i
      else Work.UBBInputs8.boxQInd V A i) Φ)

/-- Membership in `List.finRange`: the fold ranges over all slots. -/
theorem mem_list_finRange {N : ℕ} (i : Fin N) : i ∈ List.finRange N :=
  List.mem_finRange i

/-! ## The **3-way** joint components `ψ_{S,T}` (the ones that span everything)

The 2-way family `boxComp` above spans only the "in-box" subspace `∏ᵢ1_A(xᵢ)`.  The counts
`S`, `n₊`, `Pc` of the corpus are integrals over the **big** box, so they also see the part of
`Φ` lying outside `A` in at least one slot.  The full joint decomposition of the commuting family
`(Pᵢ, Qᵢ, Rᵢ)ᵢ` (`Rᵢ :=` multiplication by `1 − 1_A(xᵢ)`, `Pᵢ+Qᵢ+Rᵢ = 1`) is indexed by a pair
`(S,T)` of disjoint finsets (`U := univ ∖ (S∪T)`):

    ψ_{S,T} := (∏_{i∈S}Pᵢ)(∏_{j∈T}Qⱼ)(∏_{k∈U}Rₖ) Φ .

Then `n₀ = ΣⱼPⱼ` acts on `ψ_{S,T}` by `|S|`, `n₊ = ΣⱼQⱼ` by `|T|`, and
`Σ_{(S,T)} ψ_{S,T} = Φ` (no `∏1_A` factor!), which is what the sharp (operator-`√`) step needs. -/

/-- The "outside" projection `Rᵢ`: multiplication by `1 − 1_A(xᵢ)`. -/
noncomputable def boxOut {N : ℕ} (A : Set E3) (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) : Submission.BoseGases.X N → ℝ :=
  fun x => (1 - A.indicator (fun _ => (1 : ℝ)) (x i)) * Φ x

/-- The **3-way joint component** `ψ_{S,T} = (∏_{i∈S}Pᵢ)(∏_{j∈T}Qⱼ)(∏_{k∉S∪T}Rₖ) Φ`
(folded over `List.finRange N`; the projections commute). -/
noncomputable def boxCompT {N : ℕ} (V : ℝ) (A : Set E3) (S T : Finset (Fin N))
    (Φ : Submission.BoseGases.X N → ℝ) : Submission.BoseGases.X N → ℝ :=
  (List.finRange N).foldl
    (fun g i => (if i ∈ S then Work.UBBInputs8.boxPInd V A i
      else if i ∈ T then Work.UBBInputs8.boxQInd V A i
      else boxOut A i) g) Φ

/-- The **functional calculus of `n₀ = ΣⱼPⱼ`** at the box projections: for `g : ℕ → ℝ`,
`boxNOp V A g Φ := Σ_{(S,T)} g(|S|) • ψ_{S,T}` — the operator `g(n₀)` applied to `Φ`
(the components `ψ_{S,T}` are the joint eigenfunctions of `n₀`, with eigenvalue `|S|`). -/
noncomputable def boxNOp {N : ℕ} (V : ℝ) (A : Set E3) (g : ℕ → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) : Submission.BoseGases.X N → ℝ :=
  fun x => ∑ p ∈ (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter
      (fun p => Disjoint p.1 p.2), g p.1.card * boxCompT V A p.1 p.2 Φ x

end Work.BoseFixB1S
