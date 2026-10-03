
import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.Defs

/-!
# The "fan" decomposition of Peluse's square set along the first coordinate

`thetaFan` is the finite-combinatorics identity behind the induction step of the sharp
dual--difference interchange: the sum over the level-`(σ+1)` cube set `ThetaSet (σ+1) D H` can
be re-indexed as the sum over the level-`σ` triples `k'` of the box (which record the *tails* of
the three level-`(σ+1)` shift vectors) followed by the sum over the level-`1` cube set of the
*column* `colFibre σ D H k'` of `k'` (which records the `0`-th coordinates).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe.sharpStep

noncomputable section

open Finset

open Work.Peluse.Ulower

/-- The *tail triple* of a level-`(σ+1)` triple: the three vectors with their `0`-th coordinate
removed. -/
def tailTriple {σ : ℕ} (k : (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ)) :
    (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ) :=
  (Fin.tail k.1, Fin.tail k.2.1, Fin.tail k.2.2)

/-- The *head triple* of a level-`(σ+1)` triple: the three constant one-dimensional vectors
recording the `0`-th coordinates. -/
def headTriple {σ : ℕ} (k : (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ)) :
    (Fin 1 → ℤ) × (Fin 1 → ℤ) × (Fin 1 → ℤ) :=
  (fun _ => k.1 0, fun _ => k.2.1 0, fun _ => k.2.2 0)

/-- The *reassembly* of a level-`σ` triple `k'` and a level-`1` triple `k''`. -/
def recon {σ : ℕ} (k' : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ))
    (k'' : (Fin 1 → ℤ) × (Fin 1 → ℤ) × (Fin 1 → ℤ)) :
    (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ) :=
  (Fin.cons (k''.1 0) k'.1, Fin.cons (k''.2.1 0) k'.2.1, Fin.cons (k''.2.2 0) k'.2.2)

lemma recon_tail_head {σ : ℕ}
    (k : (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ)) :
    recon (tailTriple k) (headTriple k) = k := by
  simp only [recon, tailTriple, headTriple, Fin.cons_self_tail]

lemma tail_recon {σ : ℕ} (k' : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ))
    (k'' : (Fin 1 → ℤ) × (Fin 1 → ℤ) × (Fin 1 → ℤ)) :
    tailTriple (recon k' k'') = k' := by
  simp only [recon, tailTriple, Fin.tail_cons]

lemma fun_fin_one (f : Fin 1 → ℤ) : (fun _ => f 0) = f := by
  funext i; rw [Subsingleton.elim i 0]

lemma head_recon {σ : ℕ} (k' : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ))
    (k'' : (Fin 1 → ℤ) × (Fin 1 → ℤ) × (Fin 1 → ℤ)) :
    headTriple (recon k' k'') = k'' := by
  simp only [headTriple, recon, Fin.cons_zero]
  exact Prod.ext (fun_fin_one k''.1) (Prod.ext (fun_fin_one k''.2.1) (fun_fin_one k''.2.2))

lemma mem_thetaSet_iff {s D : ℕ} {H : Finset ((Fin s → ℤ) × (Fin s → ℤ))}
    {k : (Fin s → ℤ) × (Fin s → ℤ) × (Fin s → ℤ)} :
    k ∈ ThetaSet s D H ↔ k.1 ∈ thetaBox s D ∧ k.2.1 ∈ thetaBox s D ∧ k.2.2 ∈ thetaBox s D ∧
      ∀ ω : Fin s → Bool, (k.1, thetaSel ω k.2.1 k.2.2) ∈ H := by
  simp only [ThetaSet, thetaBox, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
    Fintype.mem_piFinset]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, h3⟩, h4⟩

lemma mem_thetaBox_one {D : ℕ} {f : Fin 1 → ℤ} :
    f ∈ thetaBox 1 D ↔ f 0 ∈ Finset.Icc (1 : ℤ) (D : ℤ) := by
  rw [mem_thetaBox, Fin.forall_fin_one]

lemma mem_rowFibre {σ D : ℕ} {H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ))} {a b : ℤ}
    {p : (Fin σ → ℤ) × (Fin σ → ℤ)} :
    p ∈ Work.Peluse.Ulower.StepLe.rowFibre σ D H a b ↔
      p.1 ∈ thetaBox σ D ∧ p.2 ∈ thetaBox σ D ∧
        (Fin.cons a p.1, Fin.cons b p.2) ∈ H := by
  simp only [Work.Peluse.Ulower.StepLe.rowFibre, Finset.mem_filter, Finset.mem_product, and_assoc]

lemma mem_colFibre {σ D : ℕ} {H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ))}
    {k' : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)} {ab : (Fin 1 → ℤ) × (Fin 1 → ℤ)} :
    ab ∈ Work.Peluse.Ulower.StepLe.colFibre σ D H k' ↔
      ab.1 ∈ thetaBox 1 D ∧ ab.2 ∈ thetaBox 1 D ∧
        k' ∈ ThetaSet σ D (Work.Peluse.Ulower.StepLe.rowFibre σ D H (ab.1 0) (ab.2 0)) := by
  simp only [Work.Peluse.Ulower.StepLe.colFibre, Finset.mem_filter, Finset.mem_product, and_assoc]

lemma cons_row_sel {σ : ℕ} (k : (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ))
    (ω₁ : Fin 1 → Bool) (ω₂ : Fin σ → Bool) :
    (Fin.cons (k.1 0) (Fin.tail k.1),
      Fin.cons (if ω₁ 0 then k.2.1 0 else k.2.2 0)
        (thetaSel ω₂ (Fin.tail k.2.1) (Fin.tail k.2.2)))
    = (k.1, thetaSel (Fin.cons (ω₁ 0) ω₂) k.2.1 k.2.2) := by
  rw [Prod.mk.injEq]
  refine ⟨Fin.cons_self_tail k.1, ?_⟩
  conv_rhs => rw [← Fin.cons_self_tail k.2.1, ← Fin.cons_self_tail k.2.2, thetaSel_cons]

lemma recon_sel {σ : ℕ} (k' : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ))
    (k'' : (Fin 1 → ℤ) × (Fin 1 → ℤ) × (Fin 1 → ℤ)) (ω : Fin (σ+1) → Bool) :
    thetaSel ω (Fin.cons (k''.2.1 0) k'.2.1) (Fin.cons (k''.2.2 0) k'.2.2)
      = Fin.cons (if ω 0 then k''.2.1 0 else k''.2.2 0)
          (thetaSel (Fin.tail ω) k'.2.1 k'.2.2) := by
  conv_lhs => rw [← Fin.cons_self_tail ω, thetaSel_cons]

lemma tail_head_mem {σ D : ℕ} {H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ))}
    {k : (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ)}
    (hk : k ∈ ThetaSet (σ+1) D H) :
    tailTriple k ∈ (thetaBox σ D ×ˢ (thetaBox σ D ×ˢ thetaBox σ D)) ∧
      headTriple k ∈ ThetaSet 1 D (Work.Peluse.Ulower.StepLe.colFibre σ D H (tailTriple k)) := by
  obtain ⟨h1, h2, h3, hcond⟩ := mem_thetaSet_iff.mp hk
  have ht1 := tail_mem_thetaBox h1
  have ht2 := tail_mem_thetaBox h2
  have ht3 := tail_mem_thetaBox h3
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_product, Finset.mem_product]
    exact ⟨ht1, ht2, ht3⟩
  · rw [mem_thetaSet_iff]
    have hA : (headTriple k).1 ∈ thetaBox 1 D := by
      rw [mem_thetaBox_one]; exact mem_thetaBox.mp h1 0
    have hB : (headTriple k).2.1 ∈ thetaBox 1 D := by
      rw [mem_thetaBox_one]; exact mem_thetaBox.mp h2 0
    have hC : (headTriple k).2.2 ∈ thetaBox 1 D := by
      rw [mem_thetaBox_one]; exact mem_thetaBox.mp h3 0
    refine ⟨hA, hB, hC, fun ω₁ => ?_⟩
    rw [mem_colFibre]
    refine ⟨hA, thetaSel_mem_thetaBox hB hC ω₁, ?_⟩
    rw [mem_thetaSet_iff]
    refine ⟨ht1, ht2, ht3, fun ω₂ => ?_⟩
    rw [mem_rowFibre]
    refine ⟨ht1, thetaSel_mem_thetaBox ht2 ht3 ω₂, ?_⟩
    show (Fin.cons (k.1 0) (Fin.tail k.1),
      Fin.cons (if ω₁ 0 then k.2.1 0 else k.2.2 0)
        (thetaSel ω₂ (Fin.tail k.2.1) (Fin.tail k.2.2))) ∈ H
    rw [cons_row_sel k ω₁ ω₂]
    exact hcond (Fin.cons (ω₁ 0) ω₂)

lemma recon_mem {σ D : ℕ} {H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ))}
    {k' : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)}
    (hk' : k' ∈ (thetaBox σ D ×ˢ (thetaBox σ D ×ˢ thetaBox σ D)))
    {k'' : (Fin 1 → ℤ) × (Fin 1 → ℤ) × (Fin 1 → ℤ)}
    (hk'' : k'' ∈ ThetaSet 1 D (Work.Peluse.Ulower.StepLe.colFibre σ D H k')) :
    recon k' k'' ∈ ThetaSet (σ+1) D H := by
  obtain ⟨hk'1, hk'23⟩ := Finset.mem_product.mp hk'
  obtain ⟨hk'2, hk'3⟩ := Finset.mem_product.mp hk'23
  obtain ⟨h''1, h''2, h''3, h''cond⟩ := mem_thetaSet_iff.mp hk''
  have hA : k''.1 0 ∈ Finset.Icc (1:ℤ) (D:ℤ) := mem_thetaBox_one.mp h''1
  have hB : k''.2.1 0 ∈ Finset.Icc (1:ℤ) (D:ℤ) := mem_thetaBox_one.mp h''2
  have hC : k''.2.2 0 ∈ Finset.Icc (1:ℤ) (D:ℤ) := mem_thetaBox_one.mp h''3
  rw [mem_thetaSet_iff]
  refine ⟨cons_mem_thetaBox hA hk'1, cons_mem_thetaBox hB hk'2, cons_mem_thetaBox hC hk'3, ?_⟩
  intro ω
  show (Fin.cons (k''.1 0) k'.1,
      thetaSel ω (Fin.cons (k''.2.1 0) k'.2.1) (Fin.cons (k''.2.2 0) k'.2.2)) ∈ H
  rw [recon_sel k' k'' ω]
  have hcf := h''cond (fun _ : Fin 1 => ω 0)
  rw [mem_colFibre] at hcf
  obtain ⟨-, -, hTS⟩ := hcf
  rw [mem_thetaSet_iff] at hTS
  obtain ⟨-, -, -, hrow⟩ := hTS
  have hrf := hrow (Fin.tail ω)
  rw [mem_rowFibre] at hrf
  obtain ⟨-, -, hH⟩ := hrf
  exact hH

theorem thetaFan {σ D : ℕ}
    (H : Finset ((Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ)))
    {M : Type*} [AddCommMonoid M]
    (f : (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ) × (Fin (σ+1) → ℤ) → M) :
    (∑ k ∈ Work.Peluse.Ulower.ThetaSet (σ+1) D H, f k)
      = ∑ k' ∈ (Work.Peluse.Ulower.thetaBox σ D ×ˢ (Work.Peluse.Ulower.thetaBox σ D ×ˢ
              Work.Peluse.Ulower.thetaBox σ D)),
          ∑ k'' ∈ Work.Peluse.Ulower.ThetaSet 1 D
              (Work.Peluse.Ulower.StepLe.colFibre σ D H k'),
            f (Fin.cons (k''.1 0) k'.1, Fin.cons (k''.2.1 0) k'.2.1,
               Fin.cons (k''.2.2 0) k'.2.2) := by
  classical
  change (∑ k ∈ Work.Peluse.Ulower.ThetaSet (σ+1) D H, f k)
      = ∑ k' ∈ (Work.Peluse.Ulower.thetaBox σ D ×ˢ (Work.Peluse.Ulower.thetaBox σ D ×ˢ
              Work.Peluse.Ulower.thetaBox σ D)),
          ∑ k'' ∈ Work.Peluse.Ulower.ThetaSet 1 D
              (Work.Peluse.Ulower.StepLe.colFibre σ D H k'),
            f (recon k' k'')
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun k _ => (⟨tailTriple k, headTriple k⟩ : Sigma _)) ?_ ?_ ?_ ?_
  · intro k hk
    exact Finset.mem_sigma.mpr (tail_head_mem hk)
  · intro k₁ hk₁ k₂ hk₂ heq
    have h1 : tailTriple k₁ = tailTriple k₂ := congrArg Sigma.fst heq
    have h2 : headTriple k₁ = headTriple k₂ := congrArg Sigma.snd heq
    calc k₁ = recon (tailTriple k₁) (headTriple k₁) := (recon_tail_head k₁).symm
      _ = recon (tailTriple k₂) (headTriple k₂) := by rw [h1, h2]
      _ = k₂ := recon_tail_head k₂
  · rintro ⟨b1, b2⟩ hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_sigma.mp hb
    exact ⟨recon b1 b2, recon_mem hb1 hb2, by rw [tail_recon, head_recon]⟩
  · intro k hk
    show f k = f (recon (tailTriple k) (headTriple k))
    rw [recon_tail_head]

end

end Work.Peluse.Ulower.StepLe.sharpStep
