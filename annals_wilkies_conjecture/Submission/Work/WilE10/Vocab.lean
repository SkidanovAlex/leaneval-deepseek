/-
  WilE10 — generic (index-type-polymorphic) version of the frozen vocabulary, together with the
  transport to the frozen `SemiPf` along an equivalence of index types.

  The construction of `E10_rexp_to_subpf` is done with the ambient index type a *structured* sum
  type (so that the coordinate blocks have readable names), and transported here.
-/
import Submission.Work.WilE10.Psi

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE10

open WilkiesDesign WilkiesDesign.E

/-! ## Generic chains and semi-Pfaffian sets -/

/-- An exp-affine chain over an arbitrary index type of coordinates. -/
structure EAChainI (α : Type*) (r : ℕ) where
  a : Fin r → α → ℝ
  b : Fin r → ℝ

def EAChainI.ell {α : Type*} [Fintype α] {r : ℕ} (c : EAChainI α r) (j : Fin r)
    (x : α → ℝ) : ℝ :=
  ∑ i, c.a j i * x i + c.b j

def eaEvalI {α : Type*} [Fintype α] {r : ℕ} (c : EAChainI α r)
    (Q : MvPolynomial (α ⊕ Fin r) ℝ) (x : α → ℝ) : ℝ :=
  MvPolynomial.eval (Sum.elim x (fun j => Real.exp (c.ell j x))) Q

/-- A basic set: equations and strict inequalities. -/
structure BasicI (α : Type*) (r : ℕ) where
  eqs : List (MvPolynomial (α ⊕ Fin r) ℝ)
  pos : List (MvPolynomial (α ⊕ Fin r) ℝ)

def BasicI.holds {α : Type*} [Fintype α] {r : ℕ} (c : EAChainI α r) (B : BasicI α r)
    (x : α → ℝ) : Prop :=
  (∀ f ∈ B.eqs, eaEvalI c f x = 0) ∧ (∀ g ∈ B.pos, 0 < eaEvalI c g x)

/-- A restricted semi-Pfaffian set in DNF, intersected with the closed cube. -/
structure SemiPfI (α : Type*) where
  r : ℕ
  c : EAChainI α r
  basics : List (BasicI α r)

def SemiPfI.set {α : Type*} [Fintype α] (X : SemiPfI α) : Set (α → ℝ) :=
  {x | (∀ i, |x i| ≤ 1) ∧ ∃ B ∈ X.basics, BasicI.holds X.c B x}

theorem SemiPfI.mem_set {α : Type*} [Fintype α] {X : SemiPfI α} {x : α → ℝ} :
    x ∈ X.set ↔ (∀ i, |x i| ≤ 1) ∧ ∃ B ∈ X.basics, BasicI.holds X.c B x := Iff.rfl

/-! ## Transport along an equivalence of index types -/

variable {α β : Type*}

def EAChainI.tr (e : α ≃ β) {r : ℕ} (c : EAChainI α r) : EAChainI β r :=
  ⟨fun j k => c.a j (e.symm k), c.b⟩

theorem EAChainI.ell_tr [Fintype α] [Fintype β] (e : α ≃ β) {r : ℕ} (c : EAChainI α r)
    (j : Fin r) (x : β → ℝ) :
    (c.tr e).ell j x = c.ell j (x ∘ ⇑e) := by
  simp only [EAChainI.ell, EAChainI.tr]
  rw [← Equiv.sum_comp e (fun k : β => c.a j (e.symm k) * x k)]
  simp

theorem eaEvalI_rename_tr [Fintype α] [Fintype β] (e : α ≃ β) {r : ℕ} (c : EAChainI α r)
    (Q : MvPolynomial (α ⊕ Fin r) ℝ) (x : β → ℝ) :
    eaEvalI (c.tr e) (MvPolynomial.rename (Sum.map ⇑e id) Q) x = eaEvalI c Q (x ∘ ⇑e) := by
  have h : (Sum.elim x (fun j => Real.exp ((c.tr e).ell j x))) ∘ Sum.map ⇑e id
      = Sum.elim (x ∘ ⇑e) (fun j => Real.exp (c.ell j (x ∘ ⇑e))) := by
    funext q
    rcases q with a | j
    · rfl
    · simp [EAChainI.ell_tr e c j x]
  rw [eaEvalI, eaEvalI, MvPolynomial.eval_rename, h]

def BasicI.tr (e : α ≃ β) {r : ℕ} (B : BasicI α r) : BasicI β r :=
  ⟨B.eqs.map (MvPolynomial.rename (Sum.map ⇑e id)),
   B.pos.map (MvPolynomial.rename (Sum.map ⇑e id))⟩

theorem BasicI.holds_tr [Fintype α] [Fintype β] (e : α ≃ β) {r : ℕ} (c : EAChainI α r)
    (B : BasicI α r) (x : β → ℝ) :
    BasicI.holds (c.tr e) (B.tr e) x ↔ BasicI.holds c B (x ∘ ⇑e) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro f hf
      rw [← eaEvalI_rename_tr e c f x]
      exact h.1 _ (List.mem_map_of_mem hf)
    · intro g hg
      rw [← eaEvalI_rename_tr e c g x]
      exact h.2 _ (List.mem_map_of_mem hg)
  · intro h
    refine ⟨?_, ?_⟩
    · intro f hf
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      rw [eaEvalI_rename_tr e c g x]
      exact h.1 g hg
    · intro f hf
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      rw [eaEvalI_rename_tr e c g x]
      exact h.2 g hg

/-! ## Transport to the frozen `SemiPf` -/

variable {K : ℕ}

def toChain [Fintype α] (e : α ≃ Fin K) {r : ℕ} (c : EAChainI α r) :
    EAChain K r :=
  ⟨fun j k => c.a j (e.symm k), c.b⟩

def toBasic (e : α ≃ Fin K) {r : ℕ} (B : BasicI α r) : Basic K r :=
  ⟨B.eqs.map (MvPolynomial.rename (Sum.map ⇑e id)),
   B.pos.map (MvPolynomial.rename (Sum.map ⇑e id))⟩

def toSemiPf [Fintype α] (e : α ≃ Fin K) (X : SemiPfI α) : SemiPf K :=
  ⟨X.r, toChain e X.c, X.basics.map (toBasic e)⟩

theorem Basic_holds_toBasic [Fintype α] (e : α ≃ Fin K) {r : ℕ} (c : EAChainI α r)
    (B : BasicI α r) (x : Fin K → ℝ) :
    Basic.holds (toChain e c) (toBasic e B) x ↔ BasicI.holds c B (x ∘ ⇑e) := by
  show BasicI.holds (c.tr e) (B.tr e) x ↔ BasicI.holds c B (x ∘ ⇑e)
  exact BasicI.holds_tr e c B x

theorem toSemiPf_set [Fintype α] (e : α ≃ Fin K) (X : SemiPfI α) :
    (toSemiPf e X).set = {x : Fin K → ℝ | x ∘ ⇑e ∈ X.set} := by
  ext x
  simp only [SemiPf.set, cubeC, SemiPfI.set, Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨fun a => (Equiv.forall_congr_right e).mpr h.1 a, by
      obtain ⟨B, hB, hBh⟩ := h.2
      obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
      exact ⟨B₀, hB₀, (Basic_holds_toBasic e X.c B₀ x).mp hBh⟩⟩
  · intro h
    exact ⟨(Equiv.forall_congr_right e).mp h.1, by
      obtain ⟨B₀, hB₀, hB₀h⟩ := h.2
      exact ⟨toBasic e B₀, List.mem_map_of_mem hB₀,
        (Basic_holds_toBasic e X.c B₀ x).mpr hB₀h⟩⟩

end Work.WilE10
