import Mathlib
import Submission.Work.WilE7.coreLT_succ.fiberCut_subset_closure
import Submission.Work.WilE7.FiberCutInputs

namespace Work.CoreStep

theorem fiberCut_len
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧
        L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set)
    (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (n m : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)), X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.SemiPf (n + m)),
        L.length ≤ b.eval X.deg ∧
        (∀ Xh ∈ L, Xh.set ⊆ closure X.set ∧ Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧
          ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
        WilkiesDesign.E.projFirst n m '' X.set =
          ⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set := by
  obtain ⟨a5, b5, h5⟩ := hE5 F
  obtain ⟨a, b, hb⟩ :=
    Work.WilE7.coreLT_succ.cover_cut_deg_clos hE2 hE5 hE6 Work.WilE7.frontierDrop_proved
      Work.WilE7.critDrop_proved' Work.WilE7.critWitness_proved' (max a5 F) F
  refine ⟨a, (1 + b5) * (b.comp b5), ?_⟩
  intro n m X hX
  obtain ⟨Ys, hYlen, hgood, hset, -⟩ := h5 n m X hX
  have hfmt : ∀ S ∈ Ys, S.X.fmt ≤ max a5 F := fun S hS =>
    le_trans (hgood S hS).1 (le_max_left _ _)
  have hdeg : ∀ S ∈ Ys, S.deg ≤ b5.eval X.deg := fun S hS => (hgood S hS).2.1
  have hbud : ∀ S ∈ Ys, S.j < m → m - S.j ≤ F := by
    intro S hS _
    have h1 : m ≤ X.fmt := by rw [WilkiesDesign.E.SemiPf.fmt]; omega
    exact le_trans (Nat.sub_le m S.j) (le_trans h1 hX)
  have hU : ∀ S ∈ Ys, closure S.X.set ⊆ closure X.set := by
    intro S hS
    apply closure_mono
    intro z hz
    rw [hset]
    exact Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hS, hz⟩⟩
  obtain ⟨L, hlen, hpieces, hcov, hsub⟩ :=
    hb F (max a5 F) n m (closure X.set) Ys (b5.eval X.deg) le_rfl le_rfl
      (fun S hS => (hgood S hS).2.2) hfmt hdeg hbud hU
  refine ⟨L, ?_, ?_, ?_⟩
  · rw [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
      Work.WilE7.Deg.eval_comp_eval]
    calc L.length ≤ Ys.length * b.eval (b5.eval X.deg) := hlen
      _ ≤ b5.eval X.deg * b.eval (b5.eval X.deg) := Nat.mul_le_mul_right _ hYlen
      _ ≤ (1 + b5.eval X.deg) * b.eval (b5.eval X.deg) :=
            Nat.mul_le_mul_right _ (Nat.le_add_left (b5.eval X.deg) 1)
  · intro Xh hXh
    obtain ⟨hsubU, hf, hd, hfin⟩ := hpieces Xh hXh
    refine ⟨hsubU, hf, ?_, hfin⟩
    rw [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
      Work.WilE7.Deg.eval_comp_eval]
    calc Xh.deg ≤ b.eval (b5.eval X.deg) := hd
      _ ≤ (1 + b5.eval X.deg) * b.eval (b5.eval X.deg) :=
            Nat.le_mul_of_pos_left _ (by omega)
  · have hunion : WilkiesDesign.E.projFirst n m '' X.set =
        ⋃ S ∈ Ys, WilkiesDesign.E.projFirst n m '' S.X.set := by
      rw [hset]
      ext x
      simp only [Set.mem_image, Set.mem_iUnion]
      constructor
      · rintro ⟨z, ⟨S, hS, hzS⟩, rfl⟩
        exact ⟨S, hS, z, hzS, rfl⟩
      · rintro ⟨S, hS, z, hzS, rfl⟩
        exact ⟨z, ⟨S, hS, hzS⟩, rfl⟩
    refine Set.Subset.antisymm ?_ ?_
    · rw [hunion]; exact hcov
    · intro x hx
      have h1 : x ∈ ⋃ S ∈ Ys,
          WilkiesDesign.E.projFirst n m '' (WilkiesDesign.E.fiberClosure S.X.set) := hsub hx
      simp only [Set.mem_iUnion] at h1
      obtain ⟨S, hS, hxS⟩ := h1
      rw [Work.WilE7.closureProj_proved' n m S.X.set] at hxS
      rw [hunion]
      exact Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hS, hxS⟩⟩

end Work.CoreStep
