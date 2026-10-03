import Mathlib
import Submission.Work.Peluse.ladderA_peel

open scoped BigOperators
open Work.Peluse Work.Peluse.UControl

namespace Work.Peluse.LadderA

/-! ## The abstract averaging step

The conclusion of Peluse's Lemma 5.7 asks for a lower bound of the form
`(1/|A|)(1/|B|) ∑_{a,b} W a b ≥ (1/|A|)(1/|B|) ∑_{a,b ∈ G} c` for a *positive density* subset
`G ⊆ A × B₀` of the parameter box, where the box `B` is fibred over `B₀` along the value of the
peeled coordinate.  The counting lemma below is the purely combinatorial content of that step: if
`B` splits as `I × B₀` (`|B| = K|B₀|`, `K > 0`) and every row sum over `B` is `K` times the row sum
over `B₀` (the peeled coordinate is averaged out), then the average over `G` is bounded by the
average over `B`. -/
private theorem avg_sum_abstract {α β : Type} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B B0 : Finset β) (G : Finset (α × β))
    (c K : ℝ) (W : α → β → ℝ)
    (hW : ∀ a b, 0 ≤ W a b)
    (hG : G ⊆ A.product B0)
    (hpt : ∀ q ∈ G, c ≤ W q.1 q.2)
    (hK : 0 < K)
    (hmul : (B.card : ℝ) = K * (B0.card : ℝ))
    (hsum : ∀ a, ∑ b ∈ B, W a b = K * ∑ b ∈ B0, W a b) :
    (A.card : ℝ)⁻¹ * (B0.card : ℝ)⁻¹ * (G.card : ℝ) * c ≤
      (A.card : ℝ)⁻¹ * (B.card : ℝ)⁻¹ * ∑ a ∈ A, ∑ b ∈ B, W a b := by
  classical
  set S : ℝ := ∑ a ∈ A, ∑ b ∈ B0, W a b with hS
  -- the sum over the positive-density subset `G` is at most the full sum over `B₀`
  have hGsum : (G.card : ℝ) * c ≤ S := by
    rw [hS]
    calc (G.card : ℝ) * c = ∑ q ∈ G, c := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ q ∈ G, W q.1 q.2 := Finset.sum_le_sum (fun q hq => hpt q hq)
      _ ≤ ∑ q ∈ A.product B0, W q.1 q.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hG (fun q _ _ => hW q.1 q.2)
      _ = ∑ a ∈ A, ∑ b ∈ B0, W a b := Finset.sum_product A B0 (fun q => W q.1 q.2)
  -- averaging out the peeled coordinate
  have hsumAll : ∑ a ∈ A, ∑ b ∈ B, W a b = K * S := by
    rw [hS, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => hsum a)
  have hKne : K ≠ 0 := ne_of_gt hK
  -- `|B|⁻¹ * K = |B₀|⁻¹`
  have key : (B.card : ℝ)⁻¹ * (K * S) = (B0.card : ℝ)⁻¹ * S := by
    rw [hmul, mul_inv]
    rw [show K⁻¹ * (B0.card : ℝ)⁻¹ * (K * S) = (B0.card : ℝ)⁻¹ * S * (K⁻¹ * K) from by ring]
    rw [inv_mul_cancel₀ hKne, mul_one]
  calc (A.card : ℝ)⁻¹ * (B0.card : ℝ)⁻¹ * (G.card : ℝ) * c
      = (A.card : ℝ)⁻¹ * ((B0.card : ℝ)⁻¹ * ((G.card : ℝ) * c)) := by ring
    _ ≤ (A.card : ℝ)⁻¹ * ((B0.card : ℝ)⁻¹ * S) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg A.card))
        exact mul_le_mul_of_nonneg_left hGsum (inv_nonneg.mpr (Nat.cast_nonneg B0.card))
    _ = (A.card : ℝ)⁻¹ * ((B.card : ℝ)⁻¹ * ∑ a ∈ A, ∑ b ∈ B, W a b) := by
        rw [hsumAll, key]
    _ = (A.card : ℝ)⁻¹ * (B.card : ℝ)⁻¹ * ∑ a ∈ A, ∑ b ∈ B, W a b := by ring

/-- The Gowers box norm is nonnegative (it is the `2^t`-th root of a modulus). -/
private lemma boxNorm_nonneg' (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    0 ≤ boxNorm t Q S f := by
  rw [boxNorm, boxNormPow]
  exact Real.rpow_nonneg (norm_nonneg _) _

/-- The direction family `conclDir` of Peluse's Lemma 5.7's conclusion does not depend on the
coordinate of the peeled slot `s₀`: every subset `ω` of the conclusion's index type omits `s₀`, so
only the coordinates `s ≠ s₀` are summed over. -/
private lemma conclDir_update {ι : Type} [Fintype ι] [DecidableEq ι] {k : ι → ℕ} {n : ℕ}
    (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ)
    (s₀ : Slot ι k) (t' : ℕ) (a : Fin n → ℤ) (b : Slot ι k → ℤ) (x : ℤ)
    (kω : SlotSet ι k → ℕ) :
    conclDir p M₁ M₂ γ' s₀ t' a (Function.update b s₀ x) (kω := kω)
      = conclDir p M₁ M₂ γ' s₀ t' a b (kω := kω) := by
  funext j
  cases j with
  | inl i => simp [conclDir]
  | inr w =>
    obtain ⟨ω, r⟩ := w
    simp only [conclDir]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Function.update_of_ne]
    intro h
    exact ω.2.2 (h ▸ hs)

/-- Consequently the box norm of the conclusion is unchanged when the peeled coordinate is
reassigned. -/
private lemma boxNorm_conclDir_update {ι : Type} [Fintype ι] [DecidableEq ι] {k : ι → ℕ} {n : ℕ}
    (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ N : ℕ) (γ' : ℝ)
    (s₀ : Slot ι k) (t' : ℕ) (f : (Fin n → ℤ) → ℤ → ℂ) (a : Fin n → ℤ)
    (b : Slot ι k → ℤ) (x : ℤ) :
    boxNorm (Fintype.card (ConclIdx s₀ kω t'))
      (fun j => conclDir p M₁ M₂ γ' s₀ t' a (Function.update b s₀ x)
        ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j))
      (symIcc N) (f a)
    = boxNorm (Fintype.card (ConclIdx s₀ kω t'))
      (fun j => conclDir p M₁ M₂ γ' s₀ t' a b
        ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j))
      (symIcc N) (f a) := by
  have h : (fun j => conclDir p M₁ M₂ γ' s₀ t' a (Function.update b s₀ x)
        ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j))
      = (fun j => conclDir p M₁ M₂ γ' s₀ t' a b
        ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j)) := by
    funext j
    exact congrFun (conclDir_update p M₁ M₂ γ' s₀ t' a b x kω) _
  rw [h]

theorem concl_avg_sum {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : Work.Peluse.UControl.SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (D : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι k) (tbig : ℕ)
    (Adata : Finset (Fin n → ℤ)) (M₁ M₂ N : ℕ) (γ' BB : ℝ) (f : (Fin n → ℤ) → ℤ → ℂ)
    (hBB : 0 ≤ BB) (hM₂ : 1 ≤ M₂)
    (G : Finset ((Fin n → ℤ) × (Work.Peluse.UControl.Slot ι k → ℤ)))
    (hG : G ⊆ Adata.product
      ((Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)))
    (hpoint : ∀ q ∈ G, ∀ b₀ ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
        BB ≤ Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω tbig))
          (fun j => Work.Peluse.UControl.conclDir p M₁ M₂ γ' s₀ tbig q.1
            (Function.update q.2 s₀ b₀)
            ((Fintype.equivFin (Work.Peluse.UControl.ConclIdx s₀ kω tbig)).symm j))
          (Work.Peluse.symIcc N) (f q.1)) :
    ((Adata.card : ℝ))⁻¹ *
        (((Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).card : ℝ)⁻¹ *
        (G.card : ℝ) * BB
      ≤ ((Adata.card : ℝ))⁻¹ * ((Work.Peluse.UControl.paramBox (k := k) M₂).card : ℝ)⁻¹ *
        ∑ a ∈ Adata, ∑ b ∈ Work.Peluse.UControl.paramBox (k := k) M₂,
          Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω tbig))
            (fun j => Work.Peluse.UControl.conclDir p M₁ M₂ γ' s₀ tbig a b
              ((Fintype.equivFin (Work.Peluse.UControl.ConclIdx s₀ kω tbig)).symm j))
            (Work.Peluse.symIcc N) (f a) := by
  classical
  -- the parameter box `paramBox M₂` and its fibre over `a'' s₀ = 0`, and the value range `Ioo`
  set Ioo : Finset ℤ := Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ) with hIoo
  set PB : Finset (Slot ι k → ℤ) := paramBox (k := k) M₂ with hPB
  set PF : Finset (Slot ι k → ℤ) := PB.filter (fun a'' => a'' s₀ = 0) with hPF
  have hG' : G ⊆ Adata.product PF := hG
  -- `0` is an admissible value of the peeled coordinate
  have hz : (0 : ℤ) ∈ Ioo := by
    rw [hIoo, Finset.mem_Ioo]
    have h0 : (0 : ℤ) < (M₂ : ℤ) := by exact_mod_cast hM₂
    exact ⟨by omega, h0⟩
  -- the box is a product: `|paramBox| = |Ioo| · |fibre|`
  have hcardNat : PB.card = Ioo.card * PF.card := by
    have h := Work.Peluse.LadderA.sum_paramBox_split (k := k) M₂ s₀ (M := ℕ) (G := fun _ => 1)
    rw [← hPB, ← hIoo, ← hPF] at h
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have hcardR : (PB.card : ℝ) = (Ioo.card : ℝ) * (PF.card : ℝ) := by
    rw [hcardNat]; push_cast; ring
  have hIoo_pos : 0 < (Ioo.card : ℝ) := by
    have : 0 < Ioo.card := Finset.card_pos.mpr ⟨0, hz⟩
    exact_mod_cast this
  -- and the `s₀`-coordinate is averaged out of every row sum
  have hsum : ∀ a : Fin n → ℤ,
      ∑ b ∈ PB, boxNorm (Fintype.card (ConclIdx s₀ kω tbig))
          (fun j => conclDir p M₁ M₂ γ' s₀ tbig a b
            ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j))
          (symIcc N) (f a)
        = (Ioo.card : ℝ) * ∑ b ∈ PF, boxNorm (Fintype.card (ConclIdx s₀ kω tbig))
          (fun j => conclDir p M₁ M₂ γ' s₀ tbig a b
            ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j))
          (symIcc N) (f a) := by
    intro a
    have h := Work.Peluse.LadderA.sum_paramBox_split (k := k) M₂ s₀ (M := ℝ)
        (G := fun b => boxNorm (Fintype.card (ConclIdx s₀ kω tbig))
          (fun j => conclDir p M₁ M₂ γ' s₀ tbig a b
            ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j))
          (symIcc N) (f a))
    rw [← hPB, ← hIoo, ← hPF] at h
    rw [h]
    have hc : ∀ a₀ ∈ Ioo,
        (∑ a'' ∈ PF, boxNorm (Fintype.card (ConclIdx s₀ kω tbig))
          (fun j => conclDir p M₁ M₂ γ' s₀ tbig a (Function.update a'' s₀ a₀)
            ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j))
          (symIcc N) (f a))
        = ∑ a'' ∈ PF, boxNorm (Fintype.card (ConclIdx s₀ kω tbig))
          (fun j => conclDir p M₁ M₂ γ' s₀ tbig a a''
            ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j))
          (symIcc N) (f a) := by
      intro a₀ _
      refine Finset.sum_congr rfl fun a'' _ => ?_
      exact boxNorm_conclDir_update kω p M₁ M₂ N γ' s₀ tbig f a a'' a₀
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
  -- the pointwise hypothesis, at the admissible value `b₀ = 0`
  have hpt : ∀ q ∈ G, BB ≤ boxNorm (Fintype.card (ConclIdx s₀ kω tbig))
          (fun j => conclDir p M₁ M₂ γ' s₀ tbig q.1 q.2
            ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j))
          (symIcc N) (f q.1) := by
    intro q hq
    have hh := hpoint q hq 0 hz
    rwa [boxNorm_conclDir_update kω p M₁ M₂ N γ' s₀ tbig f q.1 q.2 0] at hh
  exact avg_sum_abstract Adata PB PF G BB (Ioo.card : ℝ)
    (fun a b => boxNorm (Fintype.card (ConclIdx s₀ kω tbig))
      (fun j => conclDir p M₁ M₂ γ' s₀ tbig a b
        ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j))
      (symIcc N) (f a))
    (fun a b => boxNorm_nonneg' _ _ _ _)
    hG' hpt hIoo_pos hcardR hsum

end Work.Peluse.LadderA
