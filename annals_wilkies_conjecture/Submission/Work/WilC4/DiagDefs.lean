/-
  WilC4/DiagDefs : the definitions and infrastructure behind `Work.WilC4.Diag_definable`.

  `Work.WilC4.Diag Y B₀ ρ R ⊆ ℝ²` is (roughly) the graph of the infimum of the candidate
  values `Cand Y B₀ ρ β`.  This file fixes:

  * the fact that in `LRc = (ring ⊕ rexp)[[ℝ]]` every real is a *constant of the language*, so
    an `univ`-definable set is already `∅`-definable (`definable_univ_iff_empty`); this lets one
    work with all of ℝ as parameters and only convert at the very end;
  * the `univ`-definability of polynomial (in)equalities with real coefficients
    (`definable_eval_eq_LRc`, `definable_eval_pos_LRc`, `definable_le_LRc`);
  * `GrSub1`, the analogue of `Work.WilC4.GrSub` for a `(k+1)`-ary family (the breakpoint
    family `B₀` has no value slot);
  * the "division" relation `IsDivR a b q ↔ a / b = q` on ℝ (division by zero is `0` in Lean,
    so this is *exactly* the graph of division);
  * the index type `CandIdx k` of the "body" of the candidate formula, its slots, and the body
    set `CandBody`;
  * the graph `CandG Y B₀ ρ = {(β,y) | y ∈ Cand Y B₀ ρ β}` of the candidate set.

  The quantifier bookkeeping (projecting `CandBody` down to `Fin 2 → ℝ` and matching it against
  `CandG`) and the assembly of `Diag` are done in `Work.WilC4.Diag_definable`.
-/
import Mathlib
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.crit_def_bad_aux
import Submission.Work.WilkiesI.Basic

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)

variable {k : ℕ}

/-! ## 1. `univ`-definability is `∅`-definability in `LRc` -/

/-- The constant symbols of `constantsOn univ` send every real to the corresponding constant
symbol of `LRc`. -/
def univConstLHom : constantsOn (Set.univ : Set ℝ) →ᴸ LRc where
  onFunction := fun {n} c =>
    match n, c with
    | 0, c => LR.con (c : ℝ)

instance univConstLHom_exp : univConstLHom.IsExpansionOn ℝ where
  map_onFunction := fun {n} f x => by
    match n, f with
    | 0, f => rfl
  map_onRelation := fun {n} R => isEmptyElim R

/-- Collapse the extra copy of the constants of `ℝ` inside `LRc[[univ]]` onto the constants
already present in `LRc`. -/
def univToLRc : LRc[[(Set.univ : Set ℝ)]] →ᴸ LRc :=
  LHom.sumElim (LHom.id LRc) univConstLHom

instance univToLRc_exp : univToLRc.IsExpansionOn ℝ :=
  LHom.sumElim_isExpansionOn (LHom.id LRc) univConstLHom ℝ

/-- **In `LRc` every real is a constant of the language**, so definability with all of `ℝ` as
parameters is the same as definability with none. -/
theorem definable_univ_iff_empty {α : Type} {s : Set (α → ℝ)} :
    (Set.univ : Set ℝ).Definable LRc s ↔ (∅ : Set ℝ).Definable LRc s := by
  refine ⟨fun h => ?_, fun h => h.mono (Set.subset_univ _)⟩
  rw [Set.definable_iff_empty_definable_with_params] at h
  exact h.map_expansion univToLRc

/-! ## 2. Polynomial (in)equalities with real coefficients are `univ`-definable -/

/-- The zero set of a polynomial with real coefficients is `univ`-definable in `LRc`. -/
theorem definable_eval_eq_LRc {σ : Type*} (P : MvPolynomial σ ℝ) (c : ℝ) :
    (Set.univ : Set ℝ).Definable LRc {x : σ → ℝ | (MvPolynomial.eval x) P = c} :=
  (WilkiesI.definable_eval_eq P c).map_expansion (WilC2.ringToLRc)

/-- The positivity set of a polynomial with real coefficients is `univ`-definable in `LRc`. -/
theorem definable_eval_pos_LRc {σ : Type*} (P : MvPolynomial σ ℝ) :
    (Set.univ : Set ℝ).Definable LRc {x : σ → ℝ | 0 < (MvPolynomial.eval x) P} :=
  (WilkiesI.definable_eval_pos P).map_expansion (WilC2.ringToLRc)

/-- A polynomial inequality with real coefficients is `univ`-definable in `LRc`. -/
theorem definable_le_LRc {σ : Type*} (P Q : MvPolynomial σ ℝ) :
    (Set.univ : Set ℝ).Definable LRc
      {x : σ → ℝ | (MvPolynomial.eval x) P ≤ (MvPolynomial.eval x) Q} := by
  have h : {x : σ → ℝ | (MvPolynomial.eval x) P ≤ (MvPolynomial.eval x) Q}
      = ({x : σ → ℝ | 0 < (MvPolynomial.eval x) (P - Q)})ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, MvPolynomial.eval_sub, not_lt]
    constructor <;> intro hx <;> linarith
  rw [h]
  exact (definable_eval_pos_LRc (P - Q)).compl

/-- A polynomial disequality with real coefficients is `univ`-definable in `LRc`. -/
theorem definable_ne_LRc {σ : Type*} (P Q : MvPolynomial σ ℝ) :
    (Set.univ : Set ℝ).Definable LRc
      {x : σ → ℝ | (MvPolynomial.eval x) P ≠ (MvPolynomial.eval x) Q} := by
  have h : {x : σ → ℝ | (MvPolynomial.eval x) P ≠ (MvPolynomial.eval x) Q}
      = ({x : σ → ℝ | (MvPolynomial.eval x) (P - Q) = 0})ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, MvPolynomial.eval_sub, sub_eq_zero]
  rw [h]
  exact (definable_eval_eq_LRc (P - Q) 0).compl

/-! ## 3. Substituting coordinates into a `(k+1)`-ary family -/

/-- `GrSub1 B emb a` is the set of `u : ρ → ℝ` for which the tuple `(u a, u ∘ emb)` lies in `B`:
the argument `u a` and the parameter tail read off along `emb`.  This is `GrSub` for a family
`B ⊆ ℝ^{k+1}` (the breakpoint family `B₀` has no value slot). -/
def GrSub1 (B : Set (Fin (k+1) → ℝ)) {ρ : Type} (emb : Fin k → ρ) (a : ρ) :
    Set (ρ → ℝ) :=
  {u | Fin.cons (u a) (u ∘ emb) ∈ B}

theorem GrSub1_definable {B : Set (Fin (k+1) → ℝ)} {ρ : Type}
    (hB : (∅ : Set ℝ).Definable LRc B) (emb : Fin k → ρ) (a : ρ) :
    (∅ : Set ℝ).Definable LRc (GrSub1 B emb a) := by
  have h := hB.preimage_comp (Fin.cons a emb)
  have hset : GrSub1 B emb a = (fun g : ρ → ℝ => g ∘ (Fin.cons a emb)) ⁻¹' B := by
    ext u
    simp only [Set.mem_preimage, GrSub1, Set.mem_ofPred_eq]
    have hcomp : u ∘ (Fin.cons a emb) = Fin.cons (u a) (u ∘ emb) := by
      funext i
      induction i using Fin.cases with
      | zero => rfl
      | succ j => rfl
    rw [hcomp]
  rw [hset]; exact h

/-! ## 4. The division relation on ℝ -/

/-- `IsDivR a b q` says that `q` is the quotient `a / b`.  Since Lean's division is total with
`a / 0 = 0`, this is exactly `a / b = q`; concretely
`(b = 0 ∧ q = 0) ∨ (b ≠ 0 ∧ q * b = a)`. -/
def IsDivR (a b q : ℝ) : Prop := (b = 0 ∧ q = 0) ∨ (b ≠ 0 ∧ q * b = a)

theorem isDivR_iff (a b q : ℝ) : IsDivR a b q ↔ a / b = q := by
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨hb, hq⟩)
    · simp
    · rw [div_eq_iff hb]; exact hq.symm
  · intro h
    by_cases hb : b = 0
    · subst hb; simp at h; exact Or.inl ⟨rfl, h.symm⟩
    · exact Or.inr ⟨hb, ((div_eq_iff hb).mp h).symm⟩

/-- The set `{(a,b,q) | IsDivR a b q}` is definable. -/
theorem definable_isDivR {σ : Type*} (i j l : σ) :
    (Set.univ : Set ℝ).Definable LRc
      {u : σ → ℝ | IsDivR (u i) (u j) (u l)} := by
  have h1 : (Set.univ : Set ℝ).Definable LRc
      ({u : σ → ℝ | (MvPolynomial.eval u) (MvPolynomial.X j) = 0} ∩
        {u : σ → ℝ | (MvPolynomial.eval u) (MvPolynomial.X l) = 0}) :=
    (definable_eval_eq_LRc (MvPolynomial.X j) 0).inter
      (definable_eval_eq_LRc (MvPolynomial.X l) 0)
  have h2 : (Set.univ : Set ℝ).Definable LRc
      ({u : σ → ℝ | (MvPolynomial.eval u) (MvPolynomial.X j) ≠
          (MvPolynomial.eval u) (0 : MvPolynomial σ ℝ)} ∩
        {u : σ → ℝ | (MvPolynomial.eval u)
          (MvPolynomial.X l * MvPolynomial.X j - MvPolynomial.X i) = 0}) :=
    (definable_ne_LRc (MvPolynomial.X j) 0).inter
      (definable_eval_eq_LRc (MvPolynomial.X l * MvPolynomial.X j - MvPolynomial.X i) 0)
  have h := h1.union h2
  have hset : ({u : σ → ℝ | (MvPolynomial.eval u) (MvPolynomial.X j) = 0} ∩
        {u : σ → ℝ | (MvPolynomial.eval u) (MvPolynomial.X l) = 0} ∪
        ({u : σ → ℝ | (MvPolynomial.eval u) (MvPolynomial.X j) ≠
            (MvPolynomial.eval u) (0 : MvPolynomial σ ℝ)} ∩
          {u : σ → ℝ | (MvPolynomial.eval u)
            (MvPolynomial.X l * MvPolynomial.X j - MvPolynomial.X i) = 0}))
      = {u : σ → ℝ | IsDivR (u i) (u j) (u l)} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, MvPolynomial.eval_X,
      MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_zero, IsDivR]
    constructor
    · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inr ⟨ha, by linarith [hb]⟩
    · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inr ⟨ha, by linarith [hb]⟩
  rw [hset] at h
  exact h

/-! ## 5. The index type and slots of the candidate body -/

/-- The index type of the body of the candidate formula.
`Fin 2` carries `(β, y)`, `Fin (k+5)` carries `(c, x, u, v, z, q₀)`, `Fin 6` carries
`(b, q₁, t, t₂, y₁, y₂)` and `Fin 2` carries `(q, q⁻¹)`. -/
abbrev CandIdx (k : ℕ) := ((Fin 2 ⊕ Fin (k + 5)) ⊕ Fin 6) ⊕ Fin 2

/-- The slot of `β = v 0`. -/
def cβ : CandIdx k := Sum.inl (Sum.inl (Sum.inl (0 : Fin 2)))
/-- The slot of the candidate value `y = v 1`. -/
def cy : CandIdx k := Sum.inl (Sum.inl (Sum.inl (1 : Fin 2)))
/-- The slot of the parameter `c i`. -/
def cc (i : Fin k) : CandIdx k :=
  Sum.inl (Sum.inl (Sum.inr (Fin.castLE (Nat.le_add_right k 5) i)))
/-- The slot of `x`. -/
def cx : CandIdx k := Sum.inl (Sum.inl (Sum.inr (Fin.natAdd k (0 : Fin 5))))
/-- The slot of `u` (the value at `x`). -/
def cu : CandIdx k := Sum.inl (Sum.inl (Sum.inr (Fin.natAdd k (1 : Fin 5))))
/-- The slot of `v` (the value at `x * β`). -/
def cv : CandIdx k := Sum.inl (Sum.inl (Sum.inr (Fin.natAdd k (2 : Fin 5))))
/-- The slot of `z = x * β`. -/
def cz : CandIdx k := Sum.inl (Sum.inl (Sum.inr (Fin.natAdd k (3 : Fin 5))))
/-- The slot of `q₀ = x / β`. -/
def cq0 : CandIdx k := Sum.inl (Sum.inl (Sum.inr (Fin.natAdd k (4 : Fin 5))))
/-- The slot of `b` (the breakpoint tested by `IsDeepR`). -/
def cb : CandIdx k := Sum.inl (Sum.inr (0 : Fin 6))
/-- The slot of `q₁ = x / (2β)`. -/
def cq1 : CandIdx k := Sum.inl (Sum.inr (1 : Fin 6))
/-- The slot of `t` (the point of the window). -/
def ct : CandIdx k := Sum.inl (Sum.inr (2 : Fin 6))
/-- The slot of `t₂ = 2t`. -/
def ct2 : CandIdx k := Sum.inl (Sum.inr (3 : Fin 6))
/-- The slot of `y₁` (the value at `t`). -/
def cy1 : CandIdx k := Sum.inl (Sum.inr (4 : Fin 6))
/-- The slot of `y₂` (the value at `2t`). -/
def cy2 : CandIdx k := Sum.inl (Sum.inr (5 : Fin 6))
/-- The slot of `q = y₂ / y₁`. -/
def cqq : CandIdx k := Sum.inr (0 : Fin 2)
/-- The slot of `β⁻¹ = 1 / β`. -/
def cpinv : CandIdx k := Sum.inr (1 : Fin 2)

/-- The parameter map `Fin (k+1) → CandIdx k`: its head is unused, its tail reads off `cc`.
It is the `emb` of `GrSub Y emb a b` for the family `Y`. -/
def embC : Fin (k+1) → CandIdx k := Fin.cons cβ cc

/-- Membership of the breakpoint `b` (with parameter tail `c`) in `B₀`, in the `CandIdx k`
context. -/
def Bmem (B₀ : Set (Fin (k+1) → ℝ)) : Set (CandIdx k → ℝ) := GrSub1 B₀ cc cb

/-! ## 6. The body of the candidate formula -/

/-- The "body" set of the candidate formula: all the (in)equalities and `Y`/`B₀`-memberships,
with *every* quantified variable free.  Projecting it down (see `Work.WilC4.Diag_definable`)
gives the graph of `Cand`. -/
def CandBody (Y : Set (Fin (k+2) → ℝ)) (B₀ : Set (Fin (k+1) → ℝ)) (ρ : ℝ) :
    Set (CandIdx k → ℝ) :=
  {g | 0 < g cx ∧ g ∈ GrSub Y embC cx cu ∧ g ∈ GrSub Y embC cz cv ∧
       g cz = g cx * g cβ ∧ g cv = g cu * g cy ∧ IsDivR (g cx) (g cβ) (g cq0) ∧
       ¬(g ∈ Bmem B₀ ∧ IsDivR (g cx) (2 * g cβ) (g cq1) ∧ g cq1 ≤ g cb ∧
           g cb ≤ 2 * g cβ * g cx) ∧
       (¬(g cq0 ≤ g ct ∧ g ct ≤ g cz ∧ g ct2 = g ct + g ct ∧
            g ∈ GrSub Y embC ct cy1 ∧ g ∈ GrSub Y embC ct2 cy2 ∧ g cy1 ≠ 0) ∨
        (IsDivR (g cy2) (g cy1) (g cqq) ∧ IsDivR 1 (g cβ) (g cpinv) ∧
           g cqq ≤ g cpinv + ρ ∧ ρ ≤ g cqq + g cpinv))}

/-! ## 7. The graph of `Cand` -/

/-- The graph of the candidate set `Cand Y B₀ ρ`: `(β, y) ∈ CandG ↔ y ∈ Cand Y B₀ ρ β`. -/
def CandG (Y : Set (Fin (k+2) → ℝ)) (B₀ : Set (Fin (k+1) → ℝ)) (ρ : ℝ) :
    Set (Fin 2 → ℝ) :=
  {v | v 1 ∈ Cand Y B₀ ρ (v 0)}

end Work.WilC4
