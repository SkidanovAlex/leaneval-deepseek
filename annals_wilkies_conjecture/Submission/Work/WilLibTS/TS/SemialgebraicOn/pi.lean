import Mathlib
import Submission.Work.WilLibTS.TS.Pair

namespace Work.WilLibTS.TS.SemialgebraicOn

theorem pi {α ι κ : Type*} [Finite α] [Finite κ] {B : Set (ι → ℝ)}
    (hB : Work.WilLibTS.TS.PolynomialSignSet (id : (ι → ℝ) → ι → ℝ) B)
    (f : α → (ι → ℝ) → (κ → ℝ))
    (hf : ∀ a, Work.WilLibTS.TS.SemialgebraicOn B (f a)) :
    Work.WilLibTS.TS.SemialgebraicOn B (fun x => fun p : α × κ => f p.1 x p.2) := by
  classical
  let Y := (ι → ℝ) × ((α × κ) → ℝ)
  let d : Y → (ι ⊕ (α × κ)) → ℝ := fun z => Sum.elim z.1 z.2
  have hT : Work.WilLibTS.TS.PolynomialSignSet d {z : Y | z.1 ∈ B} :=
    hB.coordinate_preimage (fun z : Y => z.1) Sum.inl (by intro z i; rfl)
  have hS : ∀ a : α, Work.WilLibTS.TS.PolynomialSignSet d
      {z : Y | z.1 ∈ B ∧ (fun k => z.2 (a,k)) = f a z.1} := by
    intro a
    exact (hf a).coordinate_preimage (fun z : Y => (z.1, fun k => z.2 (a,k)))
      (Sum.map id (fun k => (a,k))) (by intro z i; cases i <;> rfl)
  have hAll : Work.WilLibTS.TS.PolynomialSignSet d
      {z : Y | ∀ a : α, z.1 ∈ B ∧ (fun k => z.2 (a,k)) = f a z.1} :=
    Work.WilLibTS.TS.PolynomialSignSet.forall_finite
      (fun a (z : Y) => z.1 ∈ B ∧ (fun k => z.2 (a,k)) = f a z.1) hS
  have hmain : Work.WilLibTS.TS.PolynomialSignSet d
      ({z : Y | z.1 ∈ B} ∩ {z : Y | ∀ a : α, z.1 ∈ B ∧ (fun k => z.2 (a,k)) = f a z.1}) :=
    hT.inter hAll
  have heq : ({z : Y | z.1 ∈ B} ∩ {z : Y | ∀ a : α, z.1 ∈ B ∧ (fun k => z.2 (a,k)) = f a z.1})
      = {z : Y | z.1 ∈ B ∧ z.2 = fun p : α × κ => f p.1 z.1 p.2} := by
    ext z
    constructor
    · rintro ⟨hzb, ha⟩
      refine ⟨hzb, ?_⟩
      funext p
      obtain ⟨a,k⟩ := p
      exact congrFun (ha a).2 k
    · rintro ⟨hzb, hz2⟩
      refine ⟨hzb, fun a => ⟨hzb, ?_⟩⟩
      funext k
      exact congrFun hz2 (a,k)
  unfold Work.WilLibTS.TS.SemialgebraicOn
  rw [← heq]
  exact hmain

end Work.WilLibTS.TS.SemialgebraicOn
