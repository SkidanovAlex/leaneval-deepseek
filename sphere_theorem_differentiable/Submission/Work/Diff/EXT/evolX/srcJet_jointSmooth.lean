import Mathlib
import Submission.Work.Diff.EXT.evolX.srcStauDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evolX

theorem srcJet_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {Hf : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V)
    (hG : Work.Diff.EXT.JointMet Hf V) (hHeven : ∀ τ, Hf (-τ) = Hf τ)
    {k : ℕ} {x : M} (hx : (0, x) ∈ V)
    (hbase : ∀ (Ψ : ℝ → Fin (k + 4) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ i, Work.Diff.EXT.JointField (fun τ => Ψ τ i) V) → (∀ τ, Ψ (-τ) = Ψ τ) →
      Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M => Work.Diff.EXT.evolX.srcStau Hf k p.1 (Ψ p.1) p.2) 0 x)
    (hmvf : ∀ {Φ : ℝ × M → ℝ} {W : ℝ → Work.Diff.EXT.TField (I := I) (M := M)} {t₀ : ℝ} {y : M},
      Work.Diff.EXT.JointSmoothAt I M Φ t₀ y →
      ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => (⟨p.2, W p.1 p.2⟩ : TangentBundle I M)) (t₀, y) →
      Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M => mvfderiv I (fun y' : M => Φ (p.1, y')) p.2 (W p.1 p.2)) t₀ y) :
    ∀ (l : ℕ) (Ψ : ℝ → Fin ((k + 4) + l) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ i, Work.Diff.EXT.JointField (fun τ => Ψ τ i) V) → (∀ τ, Ψ (-τ) = Ψ τ) →
      Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M => Work.Diff.EXT.jetAll (Hf p.1) l (k + 4) (Work.Diff.EXT.evolX.srcStau Hf k p.1) (Ψ p.1) p.2) 0 x := by
  -- Induction on the jet order `l`.  The base case `l = 0` is the hypothesis `hbase` (the joint
  -- smoothness of `srcStau` itself); the step unfolds `jetAll (l+1)` as an `extStep`, whose
  -- `mvfderiv` term is handled by `hmvf` and whose Leibniz-correction sum by the induction
  -- hypothesis, the two needed closures being `jointField_update_dirF` (fields) and evenness.
  intro l
  induction l with
  | zero =>
      intro Ψ hΨ hΨeven
      exact hbase Ψ hΨ hΨeven
  | succ l ih =>
      intro Ψ hΨ hΨeven
      -- the family obtained by dropping the first slot of the tuple (the differentiation slot)
      have hsub : ∀ i : Fin ((k + 4) + l),
          Work.Diff.EXT.JointField
            (fun τ => (fun i : Fin ((k + 4) + l) => Ψ τ i.succ) i) V :=
        fun i => hΨ i.succ
      have hsubEven : ∀ τ, (fun i : Fin ((k + 4) + l) => Ψ (-τ) i.succ)
          = (fun i : Fin ((k + 4) + l) => Ψ τ i.succ) :=
        fun τ => by rw [hΨeven τ]
      -- the `mvfderiv` term of `extStep` on the level-`l` jet
      have hmv : Work.Diff.EXT.JointSmoothAt I M
          (fun p : ℝ × M => mvfderiv I (fun y' : M =>
              Work.Diff.EXT.jetAll (Hf p.1) l (k + 4) (Work.Diff.EXT.evolX.srcStau Hf k p.1)
                (fun i : Fin ((k + 4) + l) => Ψ p.1 i.succ) y') p.2 ((Ψ p.1) 0 p.2)) 0 x :=
        hmvf (Φ := fun p : ℝ × M =>
              Work.Diff.EXT.jetAll (Hf p.1) l (k + 4) (Work.Diff.EXT.evolX.srcStau Hf k p.1)
                (fun i : Fin ((k + 4) + l) => Ψ p.1 i.succ) p.2)
          (W := fun τ : ℝ => Ψ τ 0)
          (ih (fun τ => fun i : Fin ((k + 4) + l) => Ψ τ i.succ) hsub hsubEven)
          ((hΨ 0).contMDiffAt (hV.mem_nhds hx))
      -- the Leibniz-correction sum, term by term
      have hsum : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × M => ∑ s : Fin ((k + 4) + l),
            Work.Diff.EXT.jetAll (Hf p.1) l (k + 4) (Work.Diff.EXT.evolX.srcStau Hf k p.1)
              (Function.update (fun i : Fin ((k + 4) + l) => Ψ p.1 i.succ) s
                (Work.Diff.EXT.dirF (Hf p.1) ((fun i : Fin ((k + 4) + l) => Ψ p.1 i.succ) s)
                  (Ψ p.1 0))) p.2) (0, x) := by
        refine ContMDiffAt.sum (t := Finset.univ) (fun s _ => ?_)
        exact ih (fun τ => Function.update (fun i : Fin ((k + 4) + l) => Ψ τ i.succ) s
            (Work.Diff.EXT.dirF (Hf τ) ((fun i : Fin ((k + 4) + l) => Ψ τ i.succ) s) (Ψ τ 0)))
          (Work.Diff.EXT.evolX.jointField_update_dirF (I := I) (M := M) hLC hV hG hsub (hΨ 0) s)
          (fun τ => by rw [hΨeven τ, hHeven τ])
      refine (hmv.sub hsum).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun p => ?_))
      show mvfderiv I (fun y' : M =>
              Work.Diff.EXT.jetAll (Hf p.1) l (k + 4) (Work.Diff.EXT.evolX.srcStau Hf k p.1)
                (fun i : Fin ((k + 4) + l) => Ψ p.1 i.succ) y') p.2 ((Ψ p.1) 0 p.2)
          - (∑ s : Fin ((k + 4) + l),
              Work.Diff.EXT.jetAll (Hf p.1) l (k + 4) (Work.Diff.EXT.evolX.srcStau Hf k p.1)
                (Function.update (fun i : Fin ((k + 4) + l) => Ψ p.1 i.succ) s
                  (Work.Diff.EXT.dirF (Hf p.1) ((fun i : Fin ((k + 4) + l) => Ψ p.1 i.succ) s)
                    (Ψ p.1 0))) p.2)
        = Work.Diff.EXT.jetAll (Hf p.1) (l + 1) (k + 4) (Work.Diff.EXT.evolX.srcStau Hf k p.1)
            (Ψ p.1) p.2
      simp only [Work.Diff.EXT.jetAll, Work.Diff.EXT.extStep, Pi.sub_apply, Finset.sum_apply]

end Work.Diff.EXT.evolX
