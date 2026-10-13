import Mathlib
import Submission.Work.WilE7.DecompDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7.CoreStep

/-- If `x ∈ C` and the real number `t` lies strictly between the two consecutive levels
`lvl s x (Fin.castSucc i)` and `lvl s x i.succ`, then `t` is different from every level of
the family at `x`.  Indeed the levels are strictly increasing, and every index is either
`≤ Fin.castSucc i` or `≥ i.succ`. -/
lemma lvl_ne_of_between {n q : ℕ} {C : Set (Fin n → ℝ)}
    (s : Fin q → (Fin n → ℝ) → ℝ)
    (hmono : ∀ x ∈ C, StrictMono fun i : Fin q => s i x)
    (hbnd : ∀ (i : Fin q) (x : Fin n → ℝ), x ∈ C → |s i x| < 1)
    {x : Fin n → ℝ} (hx : x ∈ C) {i : Fin (q + 1)} {t : ℝ}
    (h1 : Work.WilE7.lvl s x (Fin.castSucc i) < t)
    (h2 : t < Work.WilE7.lvl s x i.succ) :
    ∀ j : Fin (q + 2), t ≠ Work.WilE7.lvl s x j := by
  intro j
  have hsml : StrictMono (Work.WilE7.lvl s x) :=
    Work.WilE7.strictMono_lvl (hmono x hx) (fun k => hbnd k x hx)
  rcases Fin.succ_le_or_le_castSucc j i with hj | hj
  · exact ne_of_lt (h2.trans_le (hsml.monotone hj))
  · exact (ne_of_lt ((hsml.monotone hj).trans_lt h1)).symm

theorem bandCell_subset_or_disjoint_of_interior {n q : ℕ} (C : Set (Fin n → ℝ))
    (hCpre : IsPreconnected C) (s : Fin q → (Fin n → ℝ) → ℝ)
    (hcont : ∀ i, ContinuousOn (s i) C)
    (hmono : ∀ x ∈ C, StrictMono fun i : Fin q => s i x)
    (hbnd : ∀ (i : Fin q) (x : Fin n → ℝ), x ∈ C → |s i x| < 1)
    (U : Set (Fin (n + 1) → ℝ))
    (hUcl : ∀ y ∈ Work.WilE7.cyl C, y ∈ closure U → y ∈ U)
    (hint : ∀ y ∈ Work.WilE7.cyl C, y ∈ U →
      (∀ j : Fin (q + 2), y (Fin.last n) ≠ Work.WilE7.lvl s (Fin.init y) j) →
      ∃ W ∈ nhds y, W ∩ Work.WilE7.cyl C ⊆ U) :
    ∀ i : Fin (q + 1),
      Work.WilE7.bd C (fun x => Work.WilE7.lvl s x (Fin.castSucc i))
          (fun x => Work.WilE7.lvl s x i.succ) ⊆ U ∨
        Disjoint (Work.WilE7.bd C (fun x => Work.WilE7.lvl s x (Fin.castSucc i))
          (fun x => Work.WilE7.lvl s x i.succ)) U := by
  intro i
  set B : Set (Fin (n + 1) → ℝ) := Work.WilE7.bd C
    (fun x => Work.WilE7.lvl s x (Fin.castSucc i))
    (fun x => Work.WilE7.lvl s x i.succ) with hB
  -- membership in the band cell, unfolded
  have hBmem : ∀ z : Fin (n + 1) → ℝ, z ∈ B ↔ Fin.init z ∈ C ∧
      Work.WilE7.lvl s (Fin.init z) (Fin.castSucc i) < z (Fin.last n) ∧
      z (Fin.last n) < Work.WilE7.lvl s (Fin.init z) i.succ := by
    intro z
    rw [hB]
    simp only [Work.WilE7.bd, Set.mem_ofPred_eq]
  -- every band cell lies in the cylinder
  have hBcyl : B ⊆ Work.WilE7.cyl C := by
    intro z hz
    obtain ⟨hxC, h1, h2⟩ := (hBmem z).mp hz
    have hbl := Work.WilE7.abs_lvl_le_one (s := s) (x := Fin.init z)
      (fun k => hbnd k (Fin.init z) hxC) (Fin.castSucc i)
    have hbr := Work.WilE7.abs_lvl_le_one (s := s) (x := Fin.init z)
      (fun k => hbnd k (Fin.init z) hxC) i.succ
    change Fin.init z ∈ C ∧ |z (Fin.last n)| ≤ 1
    exact ⟨hxC, abs_le.mpr ⟨by linarith [(abs_le.mp hbl).1, h1],
      by linarith [(abs_le.mp hbr).2, h2]⟩⟩
  -- the band cell is preconnected
  have hBpre : IsPreconnected B := by
    have hcont_a : ContinuousOn (fun x : Fin n → ℝ =>
        ((Work.WilE7.lvl s x (Fin.castSucc i) : ℝ) : EReal)) C :=
      continuous_coe_real_ereal.comp_continuousOn'
        (Work.WilE7.continuous_lvl hcont (Fin.castSucc i))
    have hcont_b : ContinuousOn (fun x : Fin n → ℝ =>
        ((Work.WilE7.lvl s x i.succ : ℝ) : EReal)) C :=
      continuous_coe_real_ereal.comp_continuousOn'
        (Work.WilE7.continuous_lvl hcont i.succ)
    have hab : ∀ x ∈ C, ((Work.WilE7.lvl s x (Fin.castSucc i) : ℝ) : EReal) <
        ((Work.WilE7.lvl s x i.succ : ℝ) : EReal) := by
      intro x hx
      exact EReal.coe_lt_coe_iff.mpr
        (Work.WilE7.strictMono_lvl (hmono x hx) (fun k => hbnd k x hx)
          (Fin.castSucc_lt_succ_iff.mpr le_rfl))
    have hband := isPreconnected_band_fin hCpre
      (fun x : Fin n → ℝ => ((Work.WilE7.lvl s x (Fin.castSucc i) : ℝ) : EReal))
      (fun x : Fin n → ℝ => ((Work.WilE7.lvl s x i.succ : ℝ) : EReal))
      hcont_a hcont_b hab
    have hsetB : B = {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧
        ((Work.WilE7.lvl s (Fin.init z) (Fin.castSucc i) : ℝ) : EReal) <
          ((z (Fin.last n) : ℝ) : EReal) ∧
        ((z (Fin.last n) : ℝ) : EReal) <
          ((Work.WilE7.lvl s (Fin.init z) i.succ : ℝ) : EReal)} := by
      rw [hB]
      ext z
      simp only [Work.WilE7.bd, Set.mem_ofPred_eq, EReal.coe_lt_coe_iff]
    rw [hsetB]
    exact hband
  -- the set of points of `U` that are interior points of `U` inside the cylinder
  set O₁ : Set (Fin (n + 1) → ℝ) :=
    ⋃₀ {W : Set (Fin (n + 1) → ℝ) | IsOpen W ∧ W ∩ Work.WilE7.cyl C ⊆ U} with hO₁
  have hO₁open : IsOpen O₁ := by
    rw [hO₁]
    exact isOpen_sUnion (fun W hW => hW.1)
  have hO₁U : O₁ ∩ Work.WilE7.cyl C ⊆ U := by
    intro z hz
    obtain ⟨hzO, hzcyl⟩ := hz
    rw [hO₁] at hzO
    obtain ⟨W, hW, hzW⟩ := Set.mem_sUnion.mp hzO
    exact hW.2 ⟨hzW, hzcyl⟩
  have hBU : B ∩ U ⊆ O₁ := by
    intro z hz
    obtain ⟨hzB, hzU⟩ := hz
    obtain ⟨hxC, h1, h2⟩ := (hBmem z).mp hzB
    have hne : ∀ j : Fin (q + 2), z (Fin.last n) ≠ Work.WilE7.lvl s (Fin.init z) j :=
      lvl_ne_of_between s hmono hbnd hxC h1 h2
    obtain ⟨W, hWnhds, hWsub⟩ := hint z (hBcyl hzB) hzU hne
    obtain ⟨V, hVsub, hVopen, hzV⟩ := mem_nhds_iff.mp hWnhds
    rw [hO₁]
    exact Set.mem_sUnion.mpr ⟨V, ⟨hVopen, fun y hy => hWsub ⟨hVsub hy.1, hy.2⟩⟩, hzV⟩
  -- the preconnected band cell meets one of the two open pieces
  have hcover : B ⊆ O₁ ∪ (closure U)ᶜ := by
    intro z hzB
    by_cases hzU : z ∈ U
    · exact Or.inl (hBU ⟨hzB, hzU⟩)
    · exact Or.inr (fun hzcl => hzU (hUcl z (hBcyl hzB) hzcl))
  have hdisj : B ∩ (O₁ ∩ (closure U)ᶜ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    obtain ⟨hzB, hzO, hzcl⟩ := hz
    exact hzcl (subset_closure (hO₁U ⟨hzO, hBcyl hzB⟩))
  rcases (isPreconnected_iff_subset_of_disjoint.mp hBpre) O₁ (closure U)ᶜ
      hO₁open isClosed_closure.isOpen_compl hcover hdisj with hsub | hsub
  · left
    intro z hz
    exact hO₁U ⟨hsub hz, hBcyl hz⟩
  · right
    rw [Set.disjoint_left]
    intro z hzB hzU
    exact hsub hzB (subset_closure hzU)

end Work.WilE7.CoreStep
