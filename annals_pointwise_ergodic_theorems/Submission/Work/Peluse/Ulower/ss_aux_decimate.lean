import Mathlib
import Submission.Work.Peluse.Ulower.boxNormPow_two_dilate
import Submission.Work.Peluse.Ulower.Defs

open scoped BigOperators

namespace Work.Peluse.Ulower

/-- Elementary pigeonhole: if a sum of `n > 0` real numbers dominates `X`, then one of the
terms dominates the average `X/n`. -/
private theorem ss_aux_pigeonhole {n : ℕ} (hn : 0 < n) {g : ℕ → ℝ} {X : ℝ}
    (hX : X ≤ ∑ r ∈ Finset.range n, g r) : ∃ r < n, X / n ≤ g r := by
  by_contra h
  push_neg at h
  have hsum : ∑ r ∈ Finset.range n, g r < ∑ r ∈ Finset.range n, (X / n : ℝ) := by
    refine Finset.sum_lt_sum (fun r hr => le_of_lt (h r (Finset.mem_range.mp hr)))
      ⟨0, Finset.mem_range.mpr hn, h 0 hn⟩
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have : (n : ℝ) * (X / n) = X := by field_simp
  linarith

/-- **The dilation/pigeonhole step of the `U²`-inverse entry.**  Let `c ≠ 0`, `D ≥ 1`, `F` `1`-bounded
and supported in `[-L,L]`, and suppose the second-order box norm of `F` at the arithmetic-progression
shift set `c[D]` is at least `δ > 0`.  Then there is a residue `r < |c|` such that the decimated
function `z ↦ F (c z + r)` has box norm at the plain shift set `[D]` and the support radius
`L'' := max (L / |c| + 1) D` at least

`|symIcc L| / (|c| · |symIcc L''|) · δ`.

Route: the dilation identity `Work.Peluse.Ulower.boxNormPow_two_dilate` writes the box norm at
`arithIcc c D` and radius `L` as the *average* `|symIcc L|⁻¹ ∑_{r < |c|} |symIcc (L/|c|+1)| · β_r`
of `|c|` box norms `β_r` of the decimates at radius `L/|c|+1`; pigeonholing over `r` gives
`β_r ≥ |symIcc L| δ / (|c| · |symIcc (L/|c|+1)|)`, and the exact rescaling
`β_r^{S'} = (|S|/|S'|) β_r^{S}` (`boxNormPow_eq_mul_card`, which needs only `S'.Nonempty`) passes
from the radius `L/|c|+1` to `L'' = max (L/|c|+1) D`, giving exactly the displayed constant. -/
theorem ss_aux_decimate {c : ℤ} (hc : c ≠ 0) {D L : ℕ} (hD : 1 ≤ D) {F : ℤ → ℂ}
    (hFs : Work.Peluse.SupportIn F L) (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1) {δ : ℝ}
    (hδ0 : 0 < δ)
    (hbox : δ ≤ Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Work.Peluse.arithIcc c D)
      (Work.Peluse.symIcc L) F) :
    ∃ r : ℕ, r < c.natAbs ∧
      ((Work.Peluse.symIcc L).card : ℝ) /
          ((c.natAbs : ℝ) * ((Work.Peluse.symIcc (max (L / c.natAbs + 1) D)).card : ℝ)) * δ ≤
        Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Work.Peluse.arithIcc 1 D)
          (Work.Peluse.symIcc (max (L / c.natAbs + 1) D)) (fun z : ℤ => F (c * z + (r : ℤ))) := by
  classical
  have _ := hF1
  have _ := hδ0
  have hmem : ∀ M : ℕ, (0 : ℤ) ∈ symIcc M := by
    intro M; rw [symIcc, Finset.mem_Icc]; constructor <;> simp
  have hSne : (symIcc L).Nonempty := ⟨0, hmem L⟩
  have hS1ne : (symIcc (L / c.natAbs + 1)).Nonempty := ⟨0, hmem _⟩
  have hS2ne : (symIcc (max (L / c.natAbs + 1) D)).Nonempty := ⟨0, hmem _⟩
  have hSpos : (0 : ℝ) < ((symIcc L).card : ℝ) := by
    have := Finset.card_pos.mpr hSne; exact_mod_cast this
  have hS1ne' : ((symIcc (L / c.natAbs + 1)).card : ℝ) ≠ 0 := by
    have := Finset.card_pos.mpr hS1ne; positivity
  have hS2pos : (0 : ℝ) < ((symIcc (max (L / c.natAbs + 1) D)).card : ℝ) := by
    have := Finset.card_pos.mpr hS2ne; exact_mod_cast this
  have hdil := boxNormPow_two_dilate hc hD F hFs
  -- the box norm of each decimate at the two windows differs by the exact ratio of the cards
  have hterm : ∀ r : ℕ, ((symIcc (L / c.natAbs + 1)).card : ℝ) *
        boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L / c.natAbs + 1))
          (fun z : ℤ => F (c * z + (r : ℤ)))
      = ((symIcc (max (L / c.natAbs + 1) D)).card : ℝ) *
        boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (max (L / c.natAbs + 1) D))
          (fun z : ℤ => F (c * z + (r : ℤ))) := by
    intro r
    have h := boxNormPow_eq_mul_card 2 (fun _ : Fin 2 => arithIcc 1 D)
      (symIcc (L / c.natAbs + 1)) (symIcc (max (L / c.natAbs + 1) D))
      (fun z : ℤ => F (c * z + (r : ℤ))) hS2ne
    rw [h]
    rw [← mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hS1ne']
  have hsum_eq : (∑ r ∈ Finset.range c.natAbs,
        ((symIcc (L / c.natAbs + 1)).card : ℝ) *
          boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L / c.natAbs + 1))
            (fun z : ℤ => F (c * z + (r : ℤ))))
      = ∑ r ∈ Finset.range c.natAbs,
        ((symIcc (max (L / c.natAbs + 1) D)).card : ℝ) *
          boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (max (L / c.natAbs + 1) D))
            (fun z : ℤ => F (c * z + (r : ℤ))) :=
    Finset.sum_congr rfl (fun r _ => hterm r)
  -- the dilation identity turns the hypothesis into `δ ≤ |S|⁻¹ · T`
  have hδT : δ ≤ ((symIcc L).card : ℝ)⁻¹ * (∑ r ∈ Finset.range c.natAbs,
        ((symIcc (max (L / c.natAbs + 1) D)).card : ℝ) *
          boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (max (L / c.natAbs + 1) D))
            (fun z : ℤ => F (c * z + (r : ℤ)))) := by
    have h := hbox
    rwa [hdil, hsum_eq] at h
  -- hence `|S| δ ≤ T`
  have hdom : ((symIcc L).card : ℝ) * δ ≤ ∑ r ∈ Finset.range c.natAbs,
        ((symIcc (max (L / c.natAbs + 1) D)).card : ℝ) *
          boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (max (L / c.natAbs + 1) D))
            (fun z : ℤ => F (c * z + (r : ℤ))) := by
    have h2 := mul_le_mul_of_nonneg_left hδT (le_of_lt hSpos)
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hSpos), one_mul] at h2
  -- pigeonhole over the `|c|` residues
  obtain ⟨r, hr, hge⟩ := ss_aux_pigeonhole (Int.natAbs_pos.mpr hc) hdom
  refine ⟨r, hr, ?_⟩
  have hge' : ((symIcc L).card : ℝ) * δ / (c.natAbs : ℝ) ≤
      boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (max (L / c.natAbs + 1) D))
        (fun z : ℤ => F (c * z + (r : ℤ))) * ((symIcc (max (L / c.natAbs + 1) D)).card : ℝ) :=
    hge.trans_eq (mul_comm _ _)
  have hβ : ((symIcc L).card : ℝ) * δ / (c.natAbs : ℝ) /
        ((symIcc (max (L / c.natAbs + 1) D)).card : ℝ) ≤
      boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (max (L / c.natAbs + 1) D))
        (fun z : ℤ => F (c * z + (r : ℤ))) := (div_le_iff₀ hS2pos).mpr hge'
  calc ((symIcc L).card : ℝ) /
          ((c.natAbs : ℝ) * ((symIcc (max (L / c.natAbs + 1) D)).card : ℝ)) * δ
      = ((symIcc L).card : ℝ) * δ / (c.natAbs : ℝ) /
          ((symIcc (max (L / c.natAbs + 1) D)).card : ℝ) := by ring
    _ ≤ boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (max (L / c.natAbs + 1) D))
        (fun z : ℤ => F (c * z + (r : ℤ))) := hβ

end Work.Peluse.Ulower
