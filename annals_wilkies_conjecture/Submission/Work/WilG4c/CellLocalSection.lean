import Mathlib
import Submission.Work.WilG4c.DS.Points
import Submission.Work.Wilkies.Defs

namespace Work.WilG4c

/-- **A continuous local section of a cylindrical cell over its projection.**  Let
`κ ⊆ ℝ^{m+N}` be a cylindrical cell (frozen vocabulary `WilkiesDesign.IsCell`), and let
`w0 : ℝ^m`, `y0 : ℝ^N` with `(w0, y0) ∈ κ` and `y0` in the open set `U ⊆ ℝ^N`.  If the fibre
of `κ` over the parameters is nonempty on a whole ball around `w0` (equivalently `w0` lies in
the interior of the projection of `κ`), then there is a continuous section of `κ` over an
open neighbourhood `O` of `w0` taking the value `y0` at `w0` and values in `U`. -/
theorem CellLocalSection :
    ∀ (N : ℕ) (m : ℕ) (κ : Set (Fin (m + N) → ℝ)),
    WilkiesDesign.IsCell (m + N) κ →
    ∀ (w0 : Fin m → ℝ) (y0 : Fin N → ℝ) (U : Set (Fin N → ℝ)),
      IsOpen U → Fin.append w0 y0 ∈ κ → y0 ∈ U →
      (∃ ε : ℝ, 0 < ε ∧ ∀ w : Fin m → ℝ, dist w w0 < ε →
          ∃ y : Fin N → ℝ, Fin.append w y ∈ κ) →
      ∃ (O : Set (Fin m → ℝ)) (γ : (Fin m → ℝ) → (Fin N → ℝ)),
        IsOpen O ∧ w0 ∈ O ∧ γ w0 = y0 ∧ ContinuousOn γ O ∧
          (∀ w ∈ O, γ w ∈ U ∧ Fin.append w (γ w) ∈ κ) := by
  intro N
  induction N with
  | zero =>
    intro m κ hκ w0 y0 U hU hmem hy0U hfib
    obtain ⟨ε, hεpos, hε⟩ := hfib
    refine ⟨Metric.ball w0 ε, fun _ => y0, Metric.isOpen_ball, Metric.mem_ball_self hεpos,
      rfl, continuousOn_const, ?_⟩
    intro w hw
    refine ⟨hy0U, ?_⟩
    obtain ⟨y, hy⟩ := hε w hw
    change Fin.append w y0 ∈ κ
    rw [← Subsingleton.elim y y0]
    exact hy
  | succ N ih =>
    intro m κ hκ w0 y0 U hU hmem hy0U hfib
    cases hκ with
    | graph hC f hf =>
      rename_i C
      have hfib' : ∃ ε : ℝ, 0 < ε ∧ ∀ w : Fin m → ℝ, dist w w0 < ε →
          ∃ y : Fin N → ℝ, Fin.append w y ∈ C := by
        obtain ⟨ε, hεpos, hε⟩ := hfib
        exact ⟨ε, hεpos, fun w hw => by
          obtain ⟨y, hy⟩ := hε w hw
          exact ⟨Fin.init y, by rw [← DS.init_append m N w y]; exact hy.1⟩⟩
      have hmem' : Fin.append w0 (Fin.init y0) ∈ C := by
        have h := hmem.1
        rwa [DS.init_append m N w0 y0] at h
      obtain ⟨O', γ', hO'open, hw0O', hγ'0, hγ'cont, hγ'prop⟩ :=
        ih m C hC w0 (Fin.init y0) Set.univ isOpen_univ hmem' (Set.mem_univ _) hfib'
      have hgcont : ContinuousOn (fun w : Fin m → ℝ => Fin.append w (γ' w)) O' := by
        rw [continuousOn_pi]
        intro k
        cases k using Fin.addCases with
        | left i => simp only [Fin.append_left]; exact (continuous_apply i).continuousOn
        | right j => simp only [Fin.append_right]; exact (continuousOn_pi.mp hγ'cont) j
      have hgmap : Set.MapsTo (fun w : Fin m → ℝ => Fin.append w (γ' w)) O' C :=
        fun w hw => (hγ'prop w hw).2
      have hcont2 : ContinuousOn (fun w : Fin m → ℝ => f (Fin.append w (γ' w))) O' :=
        ContinuousOn.comp hf hgcont hgmap
      have hγcont : ContinuousOn (fun w : Fin m → ℝ =>
          (Fin.snoc (γ' w) (f (Fin.append w (γ' w))) : Fin (N+1) → ℝ)) O' :=
        ContinuousOn.finSnoc (n := N) (X := fun _ : Fin (N+1) => ℝ) (f := γ')
          (g := fun w : Fin m → ℝ => f (Fin.append w (γ' w))) hγ'cont hcont2
      have hlast2 : (Fin.append w0 y0 : Fin (m + (N+1)) → ℝ) (Fin.last (Nat.add m N)) =
          y0 (Fin.last N) := by
        conv_lhs => rw [← Fin.snoc_init_self y0]
        rw [Fin.append_snoc, Fin.snoc_last]
      have hγ0 : Fin.snoc (γ' w0) (f (Fin.append w0 (γ' w0))) = y0 := by
        have hfeq : f (Fin.append w0 (Fin.init y0)) = y0 (Fin.last N) := by
          have h1 := hmem.2
          rw [DS.init_append m N w0 y0, hlast2] at h1
          exact h1.symm
        rw [hγ'0, hfeq]
        exact Fin.snoc_init_self y0
      refine ⟨O' ∩ (fun w : Fin m → ℝ =>
          (Fin.snoc (γ' w) (f (Fin.append w (γ' w))) : Fin (N+1) → ℝ)) ⁻¹' U,
        (fun w => (Fin.snoc (γ' w) (f (Fin.append w (γ' w))) : Fin (N+1) → ℝ)),
        ?_, ?_, hγ0, ?_, ?_⟩
      · exact hγcont.isOpen_inter_preimage hO'open hU
      · refine ⟨hw0O', ?_⟩
        change Fin.snoc (γ' w0) (f (Fin.append w0 (γ' w0))) ∈ U
        rw [hγ0]; exact hy0U
      · exact hγcont.mono Set.inter_subset_left
      · intro w hw
        have hw' : w ∈ O' := hw.1
        refine ⟨hw.2, ?_⟩
        dsimp only
        refine ⟨?_, ?_⟩
        · rw [Fin.append_snoc w (γ' w) (f (Fin.append w (γ' w))), Fin.init_snoc]
          exact (hγ'prop w hw').2
        · rw [Fin.append_snoc w (γ' w) (f (Fin.append w (γ' w))), Fin.snoc_last, Fin.init_snoc]
    | band hC a b ha hb hab =>
      rename_i C
      have hfib' : ∃ ε : ℝ, 0 < ε ∧ ∀ w : Fin m → ℝ, dist w w0 < ε →
          ∃ y : Fin N → ℝ, Fin.append w y ∈ C := by
        obtain ⟨ε, hεpos, hε⟩ := hfib
        exact ⟨ε, hεpos, fun w hw => by
          obtain ⟨y, hy⟩ := hε w hw
          exact ⟨Fin.init y, by rw [← DS.init_append m N w y]; exact hy.1⟩⟩
      have hmem' : Fin.append w0 (Fin.init y0) ∈ C := by
        have h := hmem.1
        rwa [DS.init_append m N w0 y0] at h
      obtain ⟨O', γ', hO'open, hw0O', hγ'0, hγ'cont, hγ'prop⟩ :=
        ih m C hC w0 (Fin.init y0) Set.univ isOpen_univ hmem' (Set.mem_univ _) hfib'
      have hlast2 : (Fin.append w0 y0 : Fin (m + (N+1)) → ℝ) (Fin.last (Nat.add m N)) =
          y0 (Fin.last N) := by
        conv_lhs => rw [← Fin.snoc_init_self y0]
        rw [Fin.append_snoc, Fin.snoc_last]
      have hlt_a0 : a (Fin.append w0 (Fin.init y0)) < ((y0 (Fin.last N) : ℝ) : EReal) := by
        have h1 := hmem.2.1
        rw [DS.init_append m N w0 y0, hlast2] at h1
        exact h1
      have hlt_b0 : ((y0 (Fin.last N) : ℝ) : EReal) < b (Fin.append w0 (Fin.init y0)) := by
        have h1 := hmem.2.2
        rw [DS.init_append m N w0 y0, hlast2] at h1
        exact h1
      have hGcont : ContinuousOn (fun w : Fin m → ℝ => Fin.append w (γ' w)) O' := by
        rw [continuousOn_pi]
        intro k
        cases k using Fin.addCases with
        | left i => simp only [Fin.append_left]; exact (continuous_apply i).continuousOn
        | right j => simp only [Fin.append_right]; exact (continuousOn_pi.mp hγ'cont) j
      have hGmap : Set.MapsTo (fun w : Fin m → ℝ => Fin.append w (γ' w)) O' C :=
        fun w hw => (hγ'prop w hw).2
      have haG : ContinuousOn (fun w : Fin m → ℝ => a (Fin.append w (γ' w))) O' :=
        ContinuousOn.comp ha hGcont hGmap
      have hbG : ContinuousOn (fun w : Fin m → ℝ => b (Fin.append w (γ' w))) O' :=
        ContinuousOn.comp hb hGcont hGmap
      set P : Set (Fin m → ℝ) :=
        (O' ∩ (fun w : Fin m → ℝ => a (Fin.append w (γ' w))) ⁻¹'
            Set.Iio ((y0 (Fin.last N) : ℝ) : EReal))
        ∩ (O' ∩ (fun w : Fin m → ℝ => b (Fin.append w (γ' w))) ⁻¹'
            Set.Ioi ((y0 (Fin.last N) : ℝ) : EReal)) with hPdef
      have hP : IsOpen P := by
        rw [hPdef]
        exact (haG.isOpen_inter_preimage hO'open isOpen_Iio).inter
          (hbG.isOpen_inter_preimage hO'open isOpen_Ioi)
      have hPsub : P ⊆ O' := by
        rw [hPdef]; intro w hw; exact hw.1.1
      have hPmem : ∀ w ∈ P, a (Fin.append w (γ' w)) < ((y0 (Fin.last N) : ℝ) : EReal) ∧
          ((y0 (Fin.last N) : ℝ) : EReal) < b (Fin.append w (γ' w)) := by
        intro w hw
        rw [hPdef] at hw
        refine ⟨?_, ?_⟩
        · simpa only [Set.mem_preimage, Set.mem_Iio] using hw.1.2
        · simpa only [Set.mem_preimage, Set.mem_Ioi] using hw.2.2
      have hP0 : w0 ∈ P := by
        rw [hPdef]
        refine ⟨⟨hw0O', ?_⟩, ⟨hw0O', ?_⟩⟩
        · simp only [Set.mem_preimage]; rw [hγ'0]; exact hlt_a0
        · simp only [Set.mem_preimage]; rw [hγ'0]; exact hlt_b0
      have hγcontP : ContinuousOn (fun w : Fin m → ℝ =>
          (Fin.snoc (γ' w) (y0 (Fin.last N)) : Fin (N+1) → ℝ)) P :=
        ContinuousOn.finSnoc (n := N) (X := fun _ : Fin (N+1) => ℝ) (f := γ')
          (g := fun _ : Fin m → ℝ => y0 (Fin.last N)) (hγ'cont.mono hPsub) continuousOn_const
      have hγval : Fin.snoc (γ' w0) (y0 (Fin.last N)) = y0 := by
        rw [hγ'0]; exact Fin.snoc_init_self y0
      refine ⟨P ∩ (fun w : Fin m → ℝ =>
          (Fin.snoc (γ' w) (y0 (Fin.last N)) : Fin (N+1) → ℝ)) ⁻¹' U,
        (fun w => (Fin.snoc (γ' w) (y0 (Fin.last N)) : Fin (N+1) → ℝ)),
        ?_, ?_, hγval, ?_, ?_⟩
      · exact hγcontP.isOpen_inter_preimage hP hU
      · refine ⟨hP0, ?_⟩
        change Fin.snoc (γ' w0) (y0 (Fin.last N)) ∈ U
        rw [hγval]; exact hy0U
      · exact hγcontP.mono Set.inter_subset_left
      · intro w hw
        have hwP : w ∈ P := hw.1
        refine ⟨hw.2, ?_⟩
        dsimp only
        refine ⟨?_, ?_, ?_⟩
        · rw [Fin.append_snoc w (γ' w) (y0 (Fin.last N)), Fin.init_snoc]
          exact (hγ'prop w (hPsub hwP)).2
        · rw [Fin.append_snoc w (γ' w) (y0 (Fin.last N)), Fin.snoc_last, Fin.init_snoc]
          exact (hPmem w hwP).1
        · rw [Fin.append_snoc w (γ' w) (y0 (Fin.last N)), Fin.snoc_last, Fin.init_snoc]
          exact (hPmem w hwP).2

end Work.WilG4c
