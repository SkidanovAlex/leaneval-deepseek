import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.OSubKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov.RicFlip

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

/-- The atom `O.atomEval G t Φ.τ F` is definitionally the `ord`-th δ-tower `deltaTowerM G t ord`
applied to the `Φ.τ`-reindexed argument tuple. -/
private lemma atomEval_eq_deltaTowerM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {a b ord : ℕ}
    (Φ : Work.Diff.EXT.ConnCov.RicFlip.O.OSub a b ord)
    (F : Fin a → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) :
    Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t Φ.τ F
      = Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t ord
          (fun m : Fin ord => F (Φ.τ (Fin.castAdd 2 m)))
          (F (Φ.τ (Fin.natAdd ord 0))) (F (Φ.τ (Fin.natAdd ord 1))) := rfl

theorem SlotAddP_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {a b ord : ℕ}
    (Φ : Work.Diff.EXT.ConnCov.RicFlip.O.OSub a b ord)
    {X : Work.Diff.EXT.ConnCov.AMB.Fam (I := I) (M := M) b}
    (hX : Work.Diff.EXT.ConnCov.AMB.SlotAddP (I := I) (M := M) X)
    (hatom_sm : ∀ (F : Fin a → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)),
      (∀ j, Work.Diff.EXT.ATower.SmE I M (F j)) →
      Work.Diff.EXT.ATower.SmE I M
        (Work.Diff.EXT.ConnCov.RicFlip.O.atomEval G t Φ.τ F))
    (hatom_add : ∀ (j : Fin (ord + 2))
      (v : Fin (ord + 2) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
      (W W' : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) → Work.Diff.EXT.ATower.SmE I M W →
      Work.Diff.EXT.ATower.SmE I M W' →
      (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t ord
          (fun l : Fin ord => (Function.update v j (W + W')) (Fin.castAdd 2 l))
          ((Function.update v j (W + W')) (Fin.natAdd ord 0))
          ((Function.update v j (W + W')) (Fin.natAdd ord 1))
        = Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t ord
            (fun l : Fin ord => (Function.update v j W) (Fin.castAdd 2 l))
            ((Function.update v j W) (Fin.natAdd ord 0)) ((Function.update v j W) (Fin.natAdd ord 1))
          + Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t ord
              (fun l : Fin ord => (Function.update v j W') (Fin.castAdd 2 l))
              ((Function.update v j W') (Fin.natAdd ord 0))
              ((Function.update v j W') (Fin.natAdd ord 1)))) :
    Work.Diff.EXT.ConnCov.AMB.SlotAddP (I := I) (M := M)
      (fun (F : Fin a → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) =>
        X (Work.Diff.EXT.ConnCov.RicFlip.O.OSub.eval G t Φ F)) := by
  intro j H W W' hH hW hW' x
  change X (O.OSub.eval G t Φ (Function.update H j (W + W'))) x
    = X (O.OSub.eval G t Φ (Function.update H j W)) x
      + X (O.OSub.eval G t Φ (Function.update H j W')) x
  -- smoothness of the components of `Φ.eval G t F`
  have hsmEval : ∀ (F : Fin a → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (F i)) →
      ∀ k, Work.Diff.EXT.ATower.SmE I M (O.OSub.eval G t Φ F k) := by
    intro F hF k
    by_cases hk : k = Φ.idx
    · rw [hk, O.OSub.eval_atom Φ F]; exact hatom_sm F hF
    · rw [O.OSub.eval_slot Φ F hk]; exact hF _
  -- every input slot is either used by the atom or is a projection slot
  obtain ⟨u, hu⟩ := Φ.bij.2 j
  rcases u with l | ⟨i, hi⟩
  · -- `j = Φ.τ l`: the update changes the atom, and `hatom_add` splits it
    have hj : Φ.τ l = j := by simpa using hu
    rw [← hj]
    rw [O.OSub.eval_update_atom (G := G) (t := t) Φ H l (W + W'),
        O.OSub.eval_update_atom (G := G) (t := t) Φ H l W,
        O.OSub.eval_update_atom (G := G) (t := t) Φ H l W']
    have hUp : ∀ (Z : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)) (m' : Fin (ord + 2)),
        (Function.update H (Φ.τ l) Z) (Φ.τ m')
          = (Function.update (fun m'' : Fin (ord + 2) => H (Φ.τ m'')) l Z) m' := by
      intro Z m'
      by_cases h : m' = l
      · rw [h, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne (fun hc => h (Φ.τ_inj hc)) Z H,
            Function.update_of_ne h Z (fun m'' : Fin (ord + 2) => H (Φ.τ m''))]
    have key : ∀ Z : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M),
        O.atomEval G t Φ.τ (Function.update H (Φ.τ l) Z)
          = deltaTowerM G t ord
              (fun m : Fin ord => (Function.update (fun m'' : Fin (ord + 2) => H (Φ.τ m'')) l Z)
                (Fin.castAdd 2 m))
              ((Function.update (fun m'' : Fin (ord + 2) => H (Φ.τ m'')) l Z) (Fin.natAdd ord 0))
              ((Function.update (fun m'' : Fin (ord + 2) => H (Φ.τ m'')) l Z) (Fin.natAdd ord 1)) := by
      intro Z
      rw [atomEval_eq_deltaTowerM]
      rw [show (fun m : Fin ord => (Function.update H (Φ.τ l) Z) (Φ.τ (Fin.castAdd 2 m)))
            = (fun m : Fin ord => (Function.update (fun m'' : Fin (ord + 2) => H (Φ.τ m'')) l Z)
                (Fin.castAdd 2 m)) from by funext m; exact hUp Z (Fin.castAdd 2 m),
          show (Function.update H (Φ.τ l) Z) (Φ.τ (Fin.natAdd ord 0))
            = (Function.update (fun m'' : Fin (ord + 2) => H (Φ.τ m'')) l Z) (Fin.natAdd ord 0)
            from hUp Z _,
          show (Function.update H (Φ.τ l) Z) (Φ.τ (Fin.natAdd ord 1))
            = (Function.update (fun m'' : Fin (ord + 2) => H (Φ.τ m'')) l Z) (Fin.natAdd ord 1)
            from hUp Z _]
    have hsum : O.atomEval G t Φ.τ (Function.update H (Φ.τ l) (W + W'))
        = O.atomEval G t Φ.τ (Function.update H (Φ.τ l) W)
          + O.atomEval G t Φ.τ (Function.update H (Φ.τ l) W') := by
      rw [key (W + W'), key W, key W']
      exact hatom_add l (fun m'' : Fin (ord + 2) => H (Φ.τ m'')) W W'
        (fun m'' => hH _) hW hW'
    have hUWs : ∀ k, Work.Diff.EXT.ATower.SmE I M (Function.update H (Φ.τ l) W k) := by
      intro k
      by_cases h : k = Φ.τ l
      · rw [h, Function.update_self]; exact hW
      · rw [Function.update_of_ne h W H]; exact hH k
    have hUWs' : ∀ k, Work.Diff.EXT.ATower.SmE I M (Function.update H (Φ.τ l) W' k) := by
      intro k
      by_cases h : k = Φ.τ l
      · rw [h, Function.update_self]; exact hW'
      · rw [Function.update_of_ne h W' H]; exact hH k
    rw [hsum]
    exact hX Φ.idx (O.OSub.eval G t Φ H) (O.atomEval G t Φ.τ (Function.update H (Φ.τ l) W))
      (O.atomEval G t Φ.τ (Function.update H (Φ.τ l) W'))
      (hsmEval H hH) (hatom_sm _ hUWs) (hatom_sm _ hUWs') x
  · -- `j = Φ.σ i`: only the projection component `i` changes
    have hj : Φ.σ i = j := by simpa using hu
    rw [← hj]
    rw [O.OSub.eval_update_slot (G := G) (t := t) Φ H i hi (W + W'),
        O.OSub.eval_update_slot (G := G) (t := t) Φ H i hi W,
        O.OSub.eval_update_slot (G := G) (t := t) Φ H i hi W']
    exact hX i (O.OSub.eval G t Φ H) W W' (hsmEval H hH) hW hW' x

end Work.Diff.EXT.ConnCov.RicFlip
