import Mathlib
import Submission.Work.Peluse.Prop36SW.boxNormPowPeelFamily

/-!
# The peel's parameter box projects onto the state's box, with uniform fibres

One peel of the §5 chain (`Work.Peluse.Prop36SW.PeelSlot s₀` in place of `ι`) removes the slot `s₀`
from the state's slot set.  The parameter box `paramBox M` is the product `∏ (Ioo (-M) M)` over the
slots, so the peel *adds* one coordinate (`s₀`), and reading a box point only on the surviving slots
is a uniform map: every fibre of

`peelProj s₀ : (Slot ι 1 → ℤ) → (Slot (PeelSlot s₀) 1 → ℤ)`,  `peelProj s₀ b k = b k.1.1`

has cardinality `#(Ioo (-M) M) = 2M-1` (the value at `s₀` is free), while the boxes have
cardinalities differing by exactly that factor.  Hence the *average* of `Ψ` over the peeled state's
box is the average of `Ψ ∘ peelProj` over the state's box — which is the statement below.

The proof is a bijection: the map

`(c, y) ↦ peelExt s₀ c y`,  `peelExt s₀ c y x = if x = s₀ then y else c (the peeled slot of x)`

is injective, sends `Box(PeelSlot) ×ˢ Ioo` onto `Box(ι)` (`peelExt_mem`), and satisfies
`peelProj s₀ (peelExt s₀ c y) = c`, `peelExt s₀ (peelProj s₀ b) (b s₀) = b`.  The average identity
then follows from `Finset.sum_image`, `Finset.sum_product`, `Finset.card_product`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The projection of a parameter-box point of the state onto the peeled state's box: read the
function on the slots that survive the peel. -/
private def peelProj (s₀ : Slot ι (fun _ => 1)) :
    (Slot ι (fun _ => 1) → ℤ) → (Slot (PeelSlot s₀) (fun _ => 1) → ℤ) :=
  fun b k => b k.1.1

/-- The extension of a peeled box point by a value at the removed slot. -/
private def peelExt (s₀ : Slot ι (fun _ => 1)) (c : Slot (PeelSlot s₀) (fun _ => 1) → ℤ) (y : ℤ) :
    Slot ι (fun _ => 1) → ℤ :=
  fun x => if h : x = s₀ then y else c ⟨⟨x, h⟩, 0⟩

private lemma peelExt_self {s₀ : Slot ι (fun _ => 1)}
    (c : Slot (PeelSlot s₀) (fun _ => 1) → ℤ) (y : ℤ) : peelExt s₀ c y s₀ = y := by
  simp [peelExt]

private lemma peelExt_of_ne {s₀ : Slot ι (fun _ => 1)}
    (c : Slot (PeelSlot s₀) (fun _ => 1) → ℤ) (y : ℤ)
    {x : Slot ι (fun _ => 1)} (h : x ≠ s₀) : peelExt s₀ c y x = c ⟨⟨x, h⟩, 0⟩ := by
  simp only [peelExt]
  exact dif_neg h

private lemma peelExt_emb {s₀ : Slot ι (fun _ => 1)}
    (c : Slot (PeelSlot s₀) (fun _ => 1) → ℤ) (y : ℤ)
    (k : Slot (PeelSlot s₀) (fun _ => 1)) : peelExt s₀ c y k.1.1 = c k := by
  rw [peelExt_of_ne c y k.1.2]
  congr 1
  obtain ⟨y, r⟩ := k
  exact Sigma.ext (Subtype.ext rfl) (heq_of_eq (Subsingleton.elim 0 r))

private lemma peelProj_peelExt {s₀ : Slot ι (fun _ => 1)}
    (c : Slot (PeelSlot s₀) (fun _ => 1) → ℤ) (y : ℤ) :
    peelProj s₀ (peelExt s₀ c y) = c := by
  funext k
  exact peelExt_emb c y k

private lemma peelExt_peelProj {s₀ : Slot ι (fun _ => 1)} (b : Slot ι (fun _ => 1) → ℤ) :
    peelExt s₀ (peelProj s₀ b) (b s₀) = b := by
  funext x
  by_cases h : x = s₀
  · subst h; rw [peelExt_self]
  · rw [peelExt_of_ne (peelProj s₀ b) (b s₀) h]
    rfl

private lemma peelExt_injective {s₀ : Slot ι (fun _ => 1)} :
    Function.Injective
      (fun p : (Slot (PeelSlot s₀) (fun _ => 1) → ℤ) × ℤ => peelExt s₀ p.1 p.2) := by
  rintro ⟨c, y⟩ ⟨c', y'⟩ h
  have h' : peelExt s₀ c y = peelExt s₀ c' y' := h
  have hy : y = y' := by
    have h2 := congrFun h' s₀
    rwa [peelExt_self c y, peelExt_self c' y'] at h2
  have hc : c = c' := by
    have h2 := congrArg (peelProj s₀) h'
    rw [peelProj_peelExt, peelProj_peelExt] at h2
    exact h2
  rw [hc, hy]

/-- The bijection between the state's box and the peeled state's box times the (free) value at the
removed slot. -/
private lemma peelExt_mem {M : ℕ} {s₀ : Slot ι (fun _ => 1)}
    (c : Slot (PeelSlot s₀) (fun _ => 1) → ℤ) (y : ℤ) :
    peelExt s₀ c y ∈ paramBox (k := fun _ : ι => 1) M
      ↔ c ∈ paramBox (k := fun _ : PeelSlot s₀ => 1) M ∧
        y ∈ Finset.Ioo (-(M : ℤ)) (M : ℤ) := by
  rw [paramBox, Fintype.mem_piFinset, paramBox, Fintype.mem_piFinset]
  constructor
  · intro h
    exact ⟨fun k => by rw [← peelExt_emb c y k]; exact h k.1.1,
      by rw [← peelExt_self c y]; exact h s₀⟩
  · rintro ⟨hc, hy⟩ x
    by_cases hx : x = s₀
    · subst hx; rwa [peelExt_self]
    · rw [peelExt_of_ne c y hx]; exact hc _

theorem averageParamBoxPeelProj {ι : Type} [Fintype ι] [DecidableEq ι]
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (M : ℕ) (hM : 1 ≤ M)
    (Ψ : (Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) → ℤ) → ℝ) :
    ((Work.Peluse.UControl.paramBox (k := fun _ : Work.Peluse.Prop36SW.PeelSlot s₀ => 1) M).card : ℝ)⁻¹ *
        ∑ a' ∈ Work.Peluse.UControl.paramBox (k := fun _ : Work.Peluse.Prop36SW.PeelSlot s₀ => 1) M,
          Ψ a'
      = ((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M).card : ℝ)⁻¹ *
        ∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M,
          Ψ (fun k : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) => b k.1.1) := by
  classical
  set B : Finset (Slot ι (fun _ => 1) → ℤ) := paramBox (k := fun _ : ι => 1) M with hB
  set B' : Finset (Slot (PeelSlot s₀) (fun _ => 1) → ℤ) :=
    paramBox (k := fun _ : PeelSlot s₀ => 1) M with hB'
  set S : Finset ℤ := Finset.Ioo (-(M : ℤ)) (M : ℤ) with hS
  -- the two boxes are matched by the bijection `peelExt`
  have hbij : B = (B' ×ˢ S).image
      (fun p : (Slot (PeelSlot s₀) (fun _ => 1) → ℤ) × ℤ => peelExt s₀ p.1 p.2) := by
    rw [hB, hB', hS]
    apply Finset.Subset.antisymm
    · intro b hb
      rw [Finset.mem_image]
      have hb' : ∀ x, b x ∈ Finset.Ioo (-(M : ℤ)) (M : ℤ) := by
        rwa [paramBox, Fintype.mem_piFinset] at hb
      refine ⟨(peelProj s₀ b, b s₀), ?_, ?_⟩
      · rw [Finset.mem_product]
        exact ⟨by rw [paramBox, Fintype.mem_piFinset]; exact fun k => hb' k.1.1, hb' s₀⟩
      · exact peelExt_peelProj (s₀ := s₀) b
    · rintro b hb
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
      rw [Finset.mem_product] at hp
      exact (peelExt_mem p.1 p.2).mpr hp
  -- the sum over the state's box factors through the uniform fibres
  have hsum : ∑ b ∈ B, Ψ (fun k : Slot (PeelSlot s₀) (fun _ => 1) => b k.1.1)
      = (S.card : ℝ) * ∑ c ∈ B', Ψ c := by
    change ∑ b ∈ B, Ψ (peelProj s₀ b) = (S.card : ℝ) * ∑ c ∈ B', Ψ c
    rw [hbij]
    rw [Finset.sum_image (f := fun b => Ψ (peelProj s₀ b))
      (fun x _ y _ hxy => (peelExt_injective (s₀ := s₀)) hxy)]
    rw [show (∑ x ∈ B' ×ˢ S, Ψ (peelProj s₀ (peelExt s₀ x.1 x.2)))
        = ∑ x ∈ B' ×ˢ S, Ψ x.1 from
      Finset.sum_congr rfl fun x _ => by rw [peelProj_peelExt]]
    rw [Finset.sum_product]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.mul_sum]
  -- the cardinality identity
  have hcard : (B.card : ℝ) = (B'.card : ℝ) * (S.card : ℝ) := by
    rw [hbij, Finset.card_image_of_injective _ (peelExt_injective (s₀ := s₀)), Finset.card_product]
    push_cast
    ring
  -- the free slot contributes `S.card ≥ 1` box points, and cancels
  have hSpos : 0 < S.card :=
    Finset.card_pos.mpr ⟨0, by rw [hS, Finset.mem_Ioo]; omega⟩
  have hSne : (S.card : ℝ) ≠ 0 := by exact_mod_cast hSpos.ne'
  have hcancel : (S.card : ℝ)⁻¹ * (S.card : ℝ) = 1 := inv_mul_cancel₀ hSne
  rw [hsum, hcard, mul_inv_rev]
  rw [show ((S.card : ℝ)⁻¹ * (B'.card : ℝ)⁻¹) * ((S.card : ℝ) * ∑ c ∈ B', Ψ c)
      = ((S.card : ℝ)⁻¹ * (S.card : ℝ)) * ((B'.card : ℝ)⁻¹ * ∑ c ∈ B', Ψ c) from by ring]
  rw [hcancel, one_mul]

end

end Work.Peluse.Prop36SW
