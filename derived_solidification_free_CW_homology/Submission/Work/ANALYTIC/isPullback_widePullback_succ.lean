import Mathlib

namespace Work.ANALYTIC

open CategoryTheory Limits in
theorem isPullback_widePullback_succ {C : Type*} [Category C] {Z : C} {n : ℕ}
    {X : Fin (n + 1) → C} (φ : ∀ i, X i ⟶ Z)
    [HasWidePullback Z X φ]
    [HasWidePullback Z (fun i : Fin n => X i.succ) (fun i : Fin n => φ i.succ)] :
    IsPullback
      (WidePullback.lift (WidePullback.base φ)
        (fun i : Fin n => WidePullback.π φ i.succ) (by simp))
      (WidePullback.π φ 0)
      (WidePullback.base (fun i : Fin n => φ i.succ))
      (φ 0) := by
  -- The square commutes: `lift ≫ base_(tail) = base` and `π 0 ≫ φ 0 = base`.
  have hcomm : WidePullback.lift (WidePullback.base φ)
        (fun i : Fin n => WidePullback.π φ i.succ) (by simp) ≫
      WidePullback.base (fun i : Fin n => φ i.succ) = WidePullback.π φ 0 ≫ φ 0 := by
    rw [WidePullback.lift_base, WidePullback.π_arrow]
  refine IsPullback.of_isLimit' ⟨hcomm⟩ ?_
  -- Given a cone `s` over `W_(n) --base_tail--> Z <--φ 0-- X 0`, build the induced map to the
  -- wide pullback `W_(n+1)` by extending the family of projections by `s.snd` at `0`.
  let hlift : ∀ s : PullbackCone (WidePullback.base (fun i : Fin n => φ i.succ)) (φ 0),
      s.pt ⟶ widePullback Z X φ := fun s =>
    WidePullback.lift (s.snd ≫ φ 0)
      (fun j => Fin.cases s.snd
        (fun i => s.fst ≫ WidePullback.π (fun i : Fin n => φ i.succ) i) j)
      (by
        intro j
        induction j using Fin.cases with
        | zero => simp
        | succ i => simp [WidePullback.π_arrow, s.condition])
  have hLbase : WidePullback.lift (WidePullback.base φ)
        (fun i : Fin n => WidePullback.π φ i.succ) (by simp) ≫
      WidePullback.base (fun i : Fin n => φ i.succ) = WidePullback.base φ :=
    WidePullback.lift_base (fun i : Fin n => φ i.succ) (WidePullback.base φ)
      (fun i : Fin n => WidePullback.π φ i.succ) (by simp)
  refine PullbackCone.IsLimit.mk hcomm hlift ?_ ?_ ?_
  · -- the lift projects to `s.fst` on the tail
    intro s
    refine WidePullback.hom_ext (fun i : Fin n => φ i.succ) _ _ ?_ ?_
    · intro i
      simp only [Category.assoc, WidePullback.lift_π, hlift, Fin.cases_succ]
    · simp only [Category.assoc, WidePullback.lift_base, hlift, s.condition]
  · -- and to `s.snd` at `0`
    intro s
    simp only [hlift, WidePullback.lift_π, Fin.cases_zero]
  · -- uniqueness
    intro s m hm1 hm2
    refine WidePullback.hom_ext φ _ _ ?_ ?_
    · intro j
      induction j using Fin.cases with
      | zero => simp only [hm2, hlift, WidePullback.lift_π, Fin.cases_zero]
      | succ i => simp only [Category.assoc, WidePullback.lift_π, ← hm1, hlift, Fin.cases_succ]
    · calc m ≫ WidePullback.base φ
        = m ≫ (WidePullback.lift (WidePullback.base φ)
            (fun i : Fin n => WidePullback.π φ i.succ) (by simp) ≫
              WidePullback.base (fun i : Fin n => φ i.succ)) := by rw [hLbase]
        _ = (m ≫ WidePullback.lift (WidePullback.base φ)
            (fun i : Fin n => WidePullback.π φ i.succ) (by simp)) ≫
              WidePullback.base (fun i : Fin n => φ i.succ) := by rw [Category.assoc]
        _ = s.fst ≫ WidePullback.base (fun i : Fin n => φ i.succ) := by rw [hm1]
        _ = s.snd ≫ φ 0 := s.condition
        _ = hlift s ≫ WidePullback.base φ := by simp only [hlift, WidePullback.lift_base]

end Work.ANALYTIC
