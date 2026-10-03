import Mathlib
import Submission.Work.Peluse.LadderA.supportIn_iterDelta

namespace Work.Peluse.LadderA

open Work.Peluse (arithIcc)

/-- **The size of a direction of the `B`-part.**  A direction `c[M₁] = {c·1, …, c·M₁}` of the
concatenation ladder, `c = ∑_{s ∈ ω} p_{s.1}(a)·a''_s`, has every element of absolute value at
most `|c|·M₁ ≤ #(Slot ι k)·D·N`:  on the box `|a''_s| < M₂` and the shift bound
`|p_i(a)|·M₁·M₂ ≤ D·N` this is `∑_s |p_{s.1}(a)|·M₂·M₁ ≤ |ω|·D·N ≤ #(Slot ι k)·D·N`. -/
private lemma coef_natAbs_mul_le {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (p : ι → (Fin n → ℤ) → ℤ) {M₁ M₂ D N : ℕ} {a : Fin n → ℤ}
    (a'' : Work.Peluse.UControl.Slot ι k → ℤ)
    (hbox : ∀ s : Work.Peluse.UControl.Slot ι k, |a'' s| < (M₂ : ℤ))
    (hp : ∀ i : ι, |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ))
    (ω : Finset (Work.Peluse.UControl.Slot ι k)) :
    (∑ s ∈ ω, p s.1 a * a'' s).natAbs * M₁
      ≤ Fintype.card (Work.Peluse.UControl.Slot ι k) * D * N := by
  -- the box hypothesis, in the non-strict form `|a'' s| ≤ M₂`
  have hb : ∀ s : Work.Peluse.UControl.Slot ι k, |a'' s| ≤ (M₂ : ℤ) := by
    intro s
    obtain ⟨h1, h2⟩ := abs_lt.mp (hbox s)
    exact abs_le.mpr ⟨le_of_lt h1, by omega⟩
  -- triangle inequality for the sum
  have h1 : |∑ s ∈ ω, p s.1 a * a'' s| ≤ ∑ s ∈ ω, |p s.1 a| * |a'' s| := by
    calc |∑ s ∈ ω, p s.1 a * a'' s| ≤ ∑ s ∈ ω, |p s.1 a * a'' s| :=
          Finset.abs_sum_le_sum_abs (fun s => p s.1 a * a'' s) ω
      _ = ∑ s ∈ ω, |p s.1 a| * |a'' s| := Finset.sum_congr rfl (fun s _ => abs_mul _ _)
  -- termwise bound, summed, then multiplied by `M₁`
  have h2 : (∑ s ∈ ω, |p s.1 a| * |a'' s|) * (M₁ : ℤ)
      ≤ ∑ _s ∈ ω, (D : ℤ) * (N : ℤ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun s _ => ?_)
    have hterm : |p s.1 a| * |a'' s| ≤ |p s.1 a| * (M₂ : ℤ) :=
      mul_le_mul_of_nonneg_left (hb s) (abs_nonneg _)
    have hM₁ : (0 : ℤ) ≤ (M₁ : ℤ) := by positivity
    calc |p s.1 a| * |a'' s| * (M₁ : ℤ)
        ≤ |p s.1 a| * (M₂ : ℤ) * (M₁ : ℤ) := mul_le_mul_of_nonneg_right hterm hM₁
      _ = |p s.1 a| * (M₁ : ℤ) * (M₂ : ℤ) := by ring
      _ ≤ (D : ℤ) * (N : ℤ) := hp s.1
  -- `|ω| ≤ #(Slot ι k)`
  have h3 : (∑ _s ∈ ω, (D : ℤ) * (N : ℤ))
      ≤ (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) * D * N := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : (ω.card : ℤ) ≤ (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) := by
      exact_mod_cast Finset.card_le_univ ω
    calc (ω.card : ℤ) * ((D : ℤ) * (N : ℤ))
        ≤ (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) * ((D : ℤ) * (N : ℤ)) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (Fintype.card (Work.Peluse.UControl.Slot ι k) : ℤ) * D * N := by ring
  -- transport to `ℕ`
  have h5 : ((∑ s ∈ ω, p s.1 a * a'' s).natAbs : ℤ) * (M₁ : ℤ)
      ≤ ((Fintype.card (Work.Peluse.UControl.Slot ι k) * D * N : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    push_cast
    calc |∑ s ∈ ω, p s.1 a * a'' s| * (M₁ : ℤ)
        ≤ (∑ s ∈ ω, |p s.1 a| * |a'' s|) * (M₁ : ℤ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ _ := h2
      _ ≤ _ := h3
  exact_mod_cast h5

theorem iterDelta_bounds {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : Work.Peluse.UControl.SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ)
    {M₁ M₂ N D m : ℕ} {a : Fin n → ℤ} (a'' : Work.Peluse.UControl.Slot ι k → ℤ)
    (s₀ : Work.Peluse.UControl.Slot ι k) (hm : Fintype.card (Work.Peluse.UControl.FamIdx kω) = m)
    (f : ℤ → ℂ) (hf : Work.Peluse.SupportIn f N) (hfb : ∀ x : ℤ, ‖f x‖ ≤ 1)
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hNM : M₁ ≤ N)
    (hbox : ∀ s : Work.Peluse.UControl.Slot ι k, |a'' s| < (M₂ : ℤ))
    (hp : ∀ i : ι, |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ))
    (sh : (j : Fin (Fintype.card (Work.Peluse.LadderA.BIdx k kω s₀))) →
        ↥(Work.Peluse.LadderA.QBfin k kω p M₁ a a'' s₀ j) ×
          ↥(Work.Peluse.LadderA.QBfin k kω p M₁ a a'' s₀ j)) :
    Work.Peluse.SupportIn (Work.Peluse.Ulower.iterDelta (Fintype.card (Work.Peluse.LadderA.BIdx k kω s₀))
        (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f)
      ((m * (Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 1) + 1) * N) ∧
    (∀ x : ℤ, ‖Work.Peluse.Ulower.iterDelta (Fintype.card (Work.Peluse.LadderA.BIdx k kω s₀))
        (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f x‖ ≤ 1) := by
  classical
  constructor
  · -- every shift of the peel lies in a direction of the `B`-part, hence in `[-(K·D+1)N, (K·D+1)N]`
    have hshift : ∀ j : Fin (Fintype.card (Work.Peluse.LadderA.BIdx k kω s₀)),
        ((sh j).1 : ℤ).natAbs ≤ (Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 1) * N ∧
        ((sh j).2 : ℤ).natAbs ≤ (Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 1) * N := by
      intro j
      have hbound : ∀ u : ↥(Work.Peluse.LadderA.QBfin k kω p M₁ a a'' s₀ j),
          (u : ℤ).natAbs ≤ (Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 1) * N := by
        intro u
        -- the direction containing `u`
        have hxmem : (u : ℤ) ∈ arithIcc
            (∑ s ∈ (((Fintype.equivFin (Work.Peluse.LadderA.BIdx k kω s₀)).symm j).1.1),
              p s.1 a * a'' s) M₁ := by
          have h := u.2
          simpa [Work.Peluse.LadderA.QBfin, Work.Peluse.LadderA.qB,
            Work.Peluse.UControl.pDir] using h
        obtain ⟨t, ht, hxt⟩ := Finset.mem_image.mp hxmem
        obtain ⟨-, ht2⟩ := Finset.mem_Icc.mp ht
        rw [← hxt]
        calc ((∑ s ∈ (((Fintype.equivFin (Work.Peluse.LadderA.BIdx k kω s₀)).symm j).1.1),
                p s.1 a * a'' s) * (t : ℤ)).natAbs
            = (∑ s ∈ (((Fintype.equivFin (Work.Peluse.LadderA.BIdx k kω s₀)).symm j).1.1),
                p s.1 a * a'' s).natAbs * t := by rw [Int.natAbs_mul, Int.natAbs_natCast]
          _ ≤ (∑ s ∈ (((Fintype.equivFin (Work.Peluse.LadderA.BIdx k kω s₀)).symm j).1.1),
                p s.1 a * a'' s).natAbs * M₁ := Nat.mul_le_mul_left _ ht2
          _ ≤ Fintype.card (Work.Peluse.UControl.Slot ι k) * D * N :=
              coef_natAbs_mul_le k p a'' hbox hp _
          _ ≤ (Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 1) * N :=
              Nat.mul_le_mul_right N (Nat.le_succ _)
      exact ⟨hbound _, hbound _⟩
    -- `#(BIdx) ≤ m`, the hypothesis's index set containing the `B`-part
    have hcard : Fintype.card (Work.Peluse.LadderA.BIdx k kω s₀) ≤ m := by
      rw [← hm]
      refine Fintype.card_le_of_injective
        (fun y : Work.Peluse.LadderA.BIdx k kω s₀ =>
          (⟨y.1.1, y.2⟩ : Work.Peluse.UControl.FamIdx kω)) ?_
      intro y z h
      obtain ⟨h1, h2⟩ := Sigma.mk.inj h
      exact Sigma.ext (Subtype.ext h1) h2
    -- the support grows by one shift interval per peel
    refine (supportIn_iterDelta (k := Fintype.card (Work.Peluse.LadderA.BIdx k kω s₀))
      (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) hf hshift).mono ?_
    calc N + Fintype.card (Work.Peluse.LadderA.BIdx k kω s₀) *
            ((Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 1) * N)
        ≤ N + m * ((Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 1) * N) :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hcard) N
      _ = (m * (Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 1) + 1) * N := by ring
  · -- the iterated difference of a `1`-bounded function is `1`-bounded
    intro x
    exact Work.Peluse.Ulower.norm_iterDelta_le_one _ _ _ hfb x

end Work.Peluse.LadderA
