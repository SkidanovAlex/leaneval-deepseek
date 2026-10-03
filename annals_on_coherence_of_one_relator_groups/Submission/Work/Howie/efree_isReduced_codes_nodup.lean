import Mathlib
import Submission.Work.Howie.Defs
import Submission.Work.ORLocInd.Howie.exists_split_arrowList

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Howie

open Quiver

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- Auxiliary step of `efree_isReduced_codes_nodup`: if `p` is an `e`-free path and `p.cons E` is
reduced and `e`-free, then the arrow `E` itself does not occur in `p`.

Otherwise `p` splits as `q₁ · E · q₂`, so that `q₂ · E` is a nonempty reduced closed path of
`Γ ∖ e`, contradicting the forest hypothesis `hfor`. -/
theorem efree_cons_not_mem_aux (P : Work.ORLocInd.Howie.Presentation V) (c : P.α)
    (hfor : ∀ (y : V) (q : Work.ORLocInd.Howie.dpath (P.keepCode c) y y),
      q.IsReduced → q.length = 0)
    {a b d : V} {p : Quiver.Path a b} {E : b ⟶ d}
    (hred : (p.cons E).IsReduced) (hf : EFree P c (p.cons E)) :
    Quiver.Total.mk b d E ∉ p.arrowList := by
  intro hE
  obtain ⟨q₁, q₂, hp, -⟩ :=
    Work.ORLocInd.Howie.exists_split_arrowList p (Quiver.Total.mk b d E) hE
  have hcons : (p.cons E) = q₁.comp (E.toPath.comp (q₂.cons E)) := by
    rw [hp]
    simp only [Quiver.Path.comp_cons]
  have hred' : (q₁.comp (E.toPath.comp (q₂.cons E))).IsReduced := hcons ▸ hred
  have hf' : EFree P c (q₁.comp (E.toPath.comp (q₂.cons E))) := hcons ▸ hf
  have hM : EFree P c (E.toPath.comp (q₂.cons E)) :=
    (EFree.of_comp (P := P) (c := c) hf').2
  have hB : EFree P c (q₂.cons E) := (EFree.of_comp (P := P) (c := c) hM).2
  have hrM : (E.toPath.comp (q₂.cons E)).IsReduced := isReduced_of_comp_right hred'
  have hrB : (q₂.cons E).IsReduced := isReduced_of_comp_right hrM
  have hnil := closed_efree_isReduced_eq_nil P c hfor hrB hB
  have hlen := congrArg Quiver.Path.length hnil
  simp only [Quiver.Path.length_cons, Quiver.Path.length_nil] at hlen
  omega

/-- Auxiliary step of `efree_isReduced_codes_nodup`: if `p` is an `e`-free path and `p.cons E` is
reduced and `e`-free, then the reverse of `E` does not occur in `p`.

Otherwise `p` splits as `q₁ · E⁻¹ · q₂` with `q₂` a closed reduced `e`-free path, which is empty by
`hfor`; then `p.cons E = q₁ · E⁻¹ · E` has a backtrack, contradicting reducedness. -/
theorem efree_cons_reverse_not_mem_aux (P : Work.ORLocInd.Howie.Presentation V) (c : P.α)
    (hfor : ∀ (y : V) (q : Work.ORLocInd.Howie.dpath (P.keepCode c) y y),
      q.IsReduced → q.length = 0)
    {a b d : V} {p : Quiver.Path a b} {E : b ⟶ d}
    (hred : (p.cons E).IsReduced) (hf : EFree P c (p.cons E)) :
    Quiver.totalReverse (Quiver.Total.mk b d E) ∉ p.arrowList := by
  intro hE
  have hE' : Quiver.Total.mk d b (Quiver.reverse E) ∈ p.arrowList := by
    simpa [Quiver.totalReverse_mk] using hE
  obtain ⟨q₁, q₂, hp, -⟩ :=
    Work.ORLocInd.Howie.exists_split_arrowList p (Quiver.Total.mk d b (Quiver.reverse E)) hE'
  have hred0 : (p.comp E.toPath).IsReduced := hred
  have hred_p : p.IsReduced := hred0.of_comp
  have hp_red : (q₁.comp ((Quiver.reverse E).toPath.comp q₂)).IsReduced := hp ▸ hred_p
  have hr₂ : q₂.IsReduced := isReduced_of_comp_right (isReduced_of_comp_right hp_red)
  have hf0 : EFree P c (p.comp E.toPath) := hf
  have hf_p : EFree P c p := (EFree.of_comp (P := P) (c := c) hf0).1
  have hf_q : EFree P c (q₁.comp ((Quiver.reverse E).toPath.comp q₂)) := hp ▸ hf_p
  have hf₂ : EFree P c q₂ :=
    (EFree.of_comp (P := P) (c := c)
      ((EFree.of_comp (P := P) (c := c) hf_q).2)).2
  have hnil := closed_efree_isReduced_eq_nil P c hfor hr₂ hf₂
  have hp' : p = q₁.comp ((Quiver.reverse E).toPath) := by
    rw [hp, hnil, Quiver.Path.comp_nil]
  have hpc : p.cons E = q₁.comp (((Quiver.reverse E).toPath).comp E.toPath) := by
    rw [hp', Quiver.Path.cons_eq_comp_toPath, Quiver.Path.comp_assoc]
  have hred2 : (q₁.comp (((Quiver.reverse E).toPath).comp E.toPath)).IsReduced := hpc ▸ hred
  have hjc : Quiver.Path.JoinConflict ((Quiver.reverse E).toPath) (E.toPath) :=
    ⟨d, Quiver.Path.nil, Quiver.reverse E, Quiver.Path.nil, rfl, by simp⟩
  exact (Quiver.Path.joinConflict_not_isReduced hjc) (isReduced_of_comp_right hred2)

theorem efree_isReduced_codes_nodup {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (c : P.α) (hsep : P.CodeSeparates)
    (hfor : ∀ (y : V) (q : Work.ORLocInd.Howie.dpath (P.keepCode c) y y),
      q.IsReduced → q.length = 0)
    {a b : V} {p : Quiver.Path a b} (hp : p.IsReduced) (hpfree : Work.Howie.EFree P c p) :
    (p.arrowList.map P.edgeOf).Nodup := by
  have main : ∀ {b : V} (p : Quiver.Path a b), p.IsReduced → EFree P c p →
      (p.arrowList.map P.edgeOf).Nodup := by
    intro b p
    induction p with
    | nil => intro _ _; simp
    | cons p' E ih =>
      intro hred hf
      have hred' : (p'.comp E.toPath).IsReduced := hred
      have hf' : EFree P c (p'.comp E.toPath) := hf
      have ih' := ih hred'.of_comp (EFree.of_comp (P := P) (c := c) hf').1
      have hnot : P.edgeOf (Quiver.Total.mk _ _ E) ∉ p'.arrowList.map P.edgeOf := by
        intro hmem
        obtain ⟨g, hg, hge⟩ := List.mem_map.mp hmem
        rcases hsep g (Quiver.Total.mk _ _ E) hge with heq | hrev
        · exact efree_cons_not_mem_aux P c hfor hred hf (heq ▸ hg)
        · exact efree_cons_reverse_not_mem_aux P c hfor hred hf (hrev ▸ hg)
      rw [Quiver.Path.arrowList_cons, List.map_append, List.map_cons, List.map_nil,
        List.nodup_append]
      refine ⟨ih', List.nodup_singleton _, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      intro hxy
      exact hnot (hxy ▸ hx)
  exact main p hp hpfree

end Work.Howie
