import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.serreC0Tools
import Submission.Work.Serre.piMapN_monoidHom
import Submission.Work.Serre.subsingleton_pi0_loopSpace_of_pi1
import Submission.Work.Stems.homotopyGroup_loop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The C0 construction in range form: assembly steps

* `connected_attachCells`: attaching `(k+2)`-cells to a `k`-connected space keeps it `k`-connected;
* `exists_isEMSpaceUpTo_of_piIso`: the Postnikov truncation in range form (`Work.Serre.serreC0Range`
  from a space whose `π_m` is already `A` and whose lower homotopy groups vanish).
-/

open scoped Topology unitInterval

namespace Work.Serre

/-- **The inclusion into an attachment of `(k+2)`-cells preserves `k`-connectivity.** -/
theorem connected_attachCells {k : ℕ} (W : Type) [TopologicalSpace W] (w₀ : W) (ι : Type)
    (g : ι → C(Work.RatHurewicz.cellSphere k, W))
    (hW : ∀ j, j ≤ k → Subsingleton (HomotopyGroup (Fin j) W w₀)) :
    ∀ j, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (Work.RatHurewicz.attachCells k W ι g)
      (Work.RatHurewicz.attachIncl k W ι g w₀)) := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    haveI : Subsingleton (HomotopyGroup (Fin 0) W w₀) := hW 0 (by omega)
    exact (Work.Serre.attachIncl_pi0_bijective k W ι g w₀).surjective.subsingleton
  · have hb := Work.Serre.attachIncl_piMap_bijective_of_compress k W ι g w₀ j hpos hj
    haveI : Subsingleton (HomotopyGroup (Fin ((j - 1) + 1)) W w₀) := by
      rw [Nat.sub_add_cancel hpos]
      exact hW j hj
    have hcast : HomotopyGroup (Fin j) (Work.RatHurewicz.attachCells k W ι g)
        (Work.RatHurewicz.attachIncl k W ι g w₀) =
        HomotopyGroup (Fin ((j - 1) + 1)) (Work.RatHurewicz.attachCells k W ι g)
        (Work.RatHurewicz.attachIncl k W ι g w₀) := by rw [Nat.sub_add_cancel hpos]
    rw [hcast]
    exact hb.surjective.subsingleton

/-- **Postnikov truncation in range form.**  A space `X` (with `π_i(X) = 0` for `i < m` and
`π_m(X) ≃* A`) can be replaced by a space whose `π_m` is `A` and whose `π_i` vanish for `i < m` and
for `m < i ≤ N`. -/
theorem exists_isEMSpaceUpTo_of_piIso {A : Type} [AddCommGroup A] {m N : ℕ} (hm : 1 ≤ m)
    (hmN : m ≤ N) {X : Type} [TopologicalSpace X] (x₀ : X)
    (hconn : ∀ j, j < m → Subsingleton (HomotopyGroup (Fin j) X x₀))
    (hiso : letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
      Nonempty (HomotopyGroup (Fin m) X x₀ ≃* Multiplicative A)) :
    ∃ (P : Type) (_ : TopologicalSpace P) (p : P), IsEMSpaceUpTo A m (by omega) N P p := by
  obtain ⟨hF⟩ := hiso
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  obtain ⟨P, topP, g, hg1, hg2, _⟩ := serrePostnikovTower_strong (N - m) m N X rfl hmN
  have hbij : Function.Bijective
      (piMapN g m x₀ : HomotopyGroup (Fin m) X x₀ → HomotopyGroup (Fin m) P (g x₀)) :=
    hg1 m le_rfl x₀
  refine ⟨P, topP, g x₀, ?_, ?_⟩
  · obtain ⟨F, hFeq⟩ := piMapN_monoidHom g m x₀
    have hbijF : Function.Bijective F := by
      rw [show ⇑F = piMapN g m x₀ from funext hFeq]
      exact hbij
    exact ⟨(MulEquiv.ofBijective F hbijF).symm.trans hF⟩
  · intro i hi hmi
    rcases Nat.lt_or_ge i m with hlt | hge
    · haveI : Subsingleton (HomotopyGroup (Fin i) X x₀) := hconn i hlt
      exact (hg1 i (le_of_lt hlt) x₀).surjective.subsingleton
    · exact hg2 i (lt_of_le_of_ne hge (Ne.symm hi))
        (hmi.resolve_left (not_lt.mpr hge)) (g x₀)

/-- **Degree `1` from degree `2`.**  If `X` is a model of `K(A,2)` up to degree `N+1`, then its
loop space is a model of `K(A,1)` up to degree `N`. -/
theorem exists_isEMSpaceUpTo_one {A : Type} [AddCommGroup A] {N : ℕ} (hN : 1 ≤ N)
    {X : Type} [TopologicalSpace X] (x : X) (hx : IsEMSpaceUpTo A 2 (by omega) (N + 1) X x) :
    ∃ (P : Type) (_ : TopologicalSpace P) (p : P), IsEMSpaceUpTo A 1 (by omega) N P p := by
  refine exists_isEMSpaceUpTo_of_piIso (A := A) (m := 1) (N := N) (X := Path x x) le_rfl hN
    (Path.refl x) ?_ ?_
  · intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact Work.Serre.subsingleton_pi0_loopSpace_of_pi1 x
      (hx.2 1 (by norm_num) (Or.inl (by norm_num)))
  · obtain ⟨e2⟩ := hx.1
    obtain ⟨eloop⟩ := Work.Stems.homotopyGroup_loop (n := 1) x
    exact ⟨eloop.symm.trans e2⟩

end Work.Serre
