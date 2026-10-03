import Mathlib
import Submission.Work.Peluse.SwapC.concatGlue

/-!
# The truncated corner family and the plain corner family have the same box product

`cUBI` differs from `cUB` only at the *mixed* corners: there `cUB` is the constant `1` while `cUBI`
is the indicator of the window `mixWin x₀ dH0 N = x₀ + dH0 + symIcc (3N)`.  The point of this file
is that the two definitions nevertheless give the *same* product over all sign patterns, at every
base point `y`: if the factor of `cUB` at some mixed corner is multiplied by such an indicator, the
product only changes when all the individual (`cUB`-)factors are nonzero; but whenever the factors
at the three corners `(ε,0)`, `(0,ε')` and `(0,0)` are nonzero, the base points at those corners are
all in the translate `x₀ + symIcc N` of the support of `f`, and then the point of the mixed corner
`(ε,ε')` — being `p(ε,0) + p(0,ε') − p(0,0)` — lies in `x₀ + dH0 + symIcc (3N) = mixWin`, so the
indicator is `1` and the factor is unchanged.  The slack of `3` in the definition of `mixWin` is
exactly what this computation needs.

-/

namespace Work.Peluse.SwapC

open Work.Peluse

open scoped BigOperators

/-! ## Iterates of the conjugation -/

private lemma star_iterate_one (n : ℕ) : (star^[n]) (1 : ℂ) = 1 :=
  Function.IsFixedPt.iterate (show star (1 : ℂ) = 1 by simp) n

private lemma star_iterate_zero (n : ℕ) : (star^[n]) (0 : ℂ) = 0 :=
  Function.IsFixedPt.iterate (show star (0 : ℂ) = 0 by simp) n

private lemma star_iterate_ite (n : ℕ) (P : Prop) [Decidable P] :
    (star^[n]) (if P then (1 : ℂ) else 0) = if P then (1 : ℂ) else 0 := by
  by_cases h : P
  · rw [if_pos h]; exact star_iterate_one n
  · rw [if_neg h]; exact star_iterate_zero n

/-! ## The four branches of `cUB` -/

private lemma cUB_apply_both {s : ℕ} (f : ℤ → ℂ) (dH0 dH1 : ℤ) (ε ε' : Fin s → Bool)
    (hε : ∀ j, ε j = false) (hε' : ∀ j, ε' j = false) (z : ℤ) :
    cUB s f dH0 dH1 ε ε' z = star (f (z + dH0)) * f (z + dH1) := by
  unfold cUB
  rw [if_pos ⟨hε, hε'⟩]

private lemma cUB_apply_left {s : ℕ} (f : ℤ → ℂ) (dH0 dH1 : ℤ) (ε ε' : Fin s → Bool)
    (hε' : ∀ j, ε' j = false) (hε : ¬ ∀ j, ε j = false) (z : ℤ) :
    cUB s f dH0 dH1 ε ε' z = f z * star (f (z + dH0)) := by
  unfold cUB
  rw [if_neg (fun h => hε h.1), if_pos hε']

private lemma cUB_apply_right {s : ℕ} (f : ℤ → ℂ) (dH0 dH1 : ℤ) (ε ε' : Fin s → Bool)
    (hε : ∀ j, ε j = false) (hε' : ¬ ∀ j, ε' j = false) (z : ℤ) :
    cUB s f dH0 dH1 ε ε' z = star (f z) * f (z + dH1) := by
  unfold cUB
  rw [if_neg (fun h => hε' h.2), if_neg hε', if_pos hε]

private lemma cUB_apply_mixed {s : ℕ} (f : ℤ → ℂ) (dH0 dH1 : ℤ) (ε ε' : Fin s → Bool)
    (hε : ¬ ∀ j, ε j = false) (hε' : ¬ ∀ j, ε' j = false) (z : ℤ) :
    cUB s f dH0 dH1 ε ε' z = 1 := by
  unfold cUB
  rw [if_neg (fun h => hε h.1), if_neg hε', if_neg hε]

/-! ## The two branches of `cUBI` -/

private lemma cUBI_eq_cUB {s : ℕ} {f : ℤ → ℂ} {x₀ dH0 dH1 : ℤ} {N : ℕ} {ε ε' : Fin s → Bool}
    (h : (∀ j, ε j = false) ∨ (∀ j, ε' j = false)) :
    cUBI s f x₀ dH0 dH1 N ε ε' = cUB s f dH0 dH1 ε ε' := by
  unfold cUBI
  rw [if_pos h]

private lemma cUBI_apply_mixed {s : ℕ} (f : ℤ → ℂ) (x₀ dH0 dH1 : ℤ) (N : ℕ) (ε ε' : Fin s → Bool)
    (h : ¬ ((∀ j, ε j = false) ∨ (∀ j, ε' j = false))) (z : ℤ) :
    cUBI s f x₀ dH0 dH1 N ε ε' z = if z ∈ mixWin x₀ dH0 N then 1 else 0 := by
  unfold cUBI
  rw [if_neg h]

private lemma weight_false {s : ℕ} : weight (fun _ : Fin s => false) = 0 := by
  simp [weight]

/-! ## The support of `f` -/

/-- A nonzero value of `f` forces its argument into the translate `x₀ + symIcc N` of the support. -/
private lemma support_bounds {N : ℕ} {x₀ : ℤ} {f : ℤ → ℂ}
    (hsup : ∀ x : ℤ, x ∉ (symIcc N).map (Equiv.addRight x₀).toEmbedding → f x = 0)
    {x : ℤ} (hx : f x ≠ 0) : -(N : ℤ) ≤ x - x₀ ∧ x - x₀ ≤ (N : ℤ) := by
  have hmem : x ∈ (symIcc N).map (Equiv.addRight x₀).toEmbedding := by
    by_contra h
    exact hx (hsup x h)
  obtain ⟨a, ha, hax⟩ := Finset.mem_map.mp hmem
  have hax' : a + x₀ = x := hax
  have haz : a = x - x₀ := by omega
  rw [← haz]
  exact Finset.mem_Icc.mp ha

set_option maxHeartbeats 1000000 in
theorem cUBIprodEq (s : ℕ) (x₀ dH0 dH1 : ℤ) (N : ℕ) (f : ℤ → ℂ)
    (hsup : ∀ x : ℤ, x ∉ (Work.Peluse.symIcc N).map (Equiv.addRight x₀).toEmbedding → f x = 0)
    (gL gL' gR gR' : Fin s → ℤ) (y : ℤ) :
    (∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool,
        (star^[Work.Peluse.weight ε + Work.Peluse.weight ε'])
          (Work.Peluse.SwapC.cUBI s f x₀ dH0 dH1 N ε ε'
            (y + Work.Peluse.cornerShift gL gL' ε + Work.Peluse.cornerShift gR gR' ε')))
      = (∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool,
        (star^[Work.Peluse.weight ε + Work.Peluse.weight ε'])
          (Work.Peluse.SwapC.cUB s f dH0 dH1 ε ε'
            (y + Work.Peluse.cornerShift gL gL' ε + Work.Peluse.cornerShift gR gR' ε'))) := by
  classical
  -- the all-`false` sign pattern, the indicator of `mixWin`, and the correction factor
  set zeroF : Fin s → Bool := fun _ => false with hzeroF
  set Ind : ((Fin s → Bool) × (Fin s → Bool)) → ℂ :=
    (fun p => if y + cornerShift gL gL' p.1 + cornerShift gR gR' p.2 ∈ mixWin x₀ dH0 N
      then 1 else 0) with hInd
  set mul : ((Fin s → Bool) × (Fin s → Bool)) → ℂ :=
    (fun p => if p.1 = zeroF ∨ p.2 = zeroF then 1 else Ind p) with hmul
  -- **the pointwise factorisation**: at the non-mixed corners the two families agree and `mul = 1`,
  -- at the mixed ones `cUB = 1` and `mul` is the indicator
  have hfac : ∀ ε ε' : Fin s → Bool,
      (star^[weight ε + weight ε'])
        (cUBI s f x₀ dH0 dH1 N ε ε' (y + cornerShift gL gL' ε + cornerShift gR gR' ε'))
      = (star^[weight ε + weight ε'])
        (cUB s f dH0 dH1 ε ε' (y + cornerShift gL gL' ε + cornerShift gR gR' ε'))
        * mul (ε, ε') := by
    intro ε ε'
    by_cases hmix : ε = zeroF ∨ ε' = zeroF
    · have hnm : (∀ j, ε j = false) ∨ (∀ j, ε' j = false) := by
        rcases hmix with h | h
        · left; intro j; rw [h]
        · right; intro j; rw [h]
      rw [cUBI_eq_cUB hnm]
      simp only [hmul]
      rw [if_pos hmix, mul_one]
    · have hε : ε ≠ zeroF := fun h => hmix (Or.inl h)
      have hε' : ε' ≠ zeroF := fun h => hmix (Or.inr h)
      have hnε : ¬ ∀ j, ε j = false := fun h => hε (funext fun j => h j)
      have hnε' : ¬ ∀ j, ε' j = false := fun h => hε' (funext fun j => h j)
      rw [cUBI_apply_mixed f x₀ dH0 dH1 N ε ε' (not_or.mpr ⟨hnε, hnε'⟩),
        cUB_apply_mixed f dH0 dH1 ε ε' hnε hnε']
      simp only [hmul]
      rw [if_neg hmix]
      simp only [hInd]
      rw [star_iterate_ite, star_iterate_one, one_mul]
  -- **the two products differ by the product of the correction factors**
  have hL : (∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool,
        (star^[weight ε + weight ε'])
          (cUBI s f x₀ dH0 dH1 N ε ε' (y + cornerShift gL gL' ε + cornerShift gR gR' ε')))
      = (∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool,
          (star^[weight ε + weight ε'])
            (cUB s f dH0 dH1 ε ε' (y + cornerShift gL gL' ε + cornerShift gR gR' ε')))
        * (∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool, mul (ε, ε')) := by
    simp_rw [hfac]
    simp_rw [Finset.prod_mul_distrib]
  rw [hL]
  -- either the `cUB`-product already vanishes, or all its factors are nonzero and then all the
  -- mixed corners have their base point inside `mixWin`
  by_cases hB : (∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool,
        (star^[weight ε + weight ε'])
          (cUB s f dH0 dH1 ε ε' (y + cornerShift gL gL' ε + cornerShift gR gR' ε'))) = 0
  · rw [hB, zero_mul]
  · have hKBne : ∀ ε ε' : Fin s → Bool,
        (star^[weight ε + weight ε'])
          (cUB s f dH0 dH1 ε ε' (y + cornerShift gL gL' ε + cornerShift gR gR' ε')) ≠ 0 := by
      intro ε ε'
      have h1 := (Finset.prod_ne_zero_iff.mp hB) ε (Finset.mem_univ ε)
      exact (Finset.prod_ne_zero_iff.mp h1) ε' (Finset.mem_univ ε')
    have hmul_one : ∀ ε ε' : Fin s → Bool, mul (ε, ε') = 1 := by
      intro ε ε'
      by_cases hmix : ε = zeroF ∨ ε' = zeroF
      · simp only [hmul]; rw [if_pos hmix]
      · have hε : ε ≠ zeroF := fun h => hmix (Or.inl h)
        have hε' : ε' ≠ zeroF := fun h => hmix (Or.inr h)
        have hnε : ¬ ∀ j, ε j = false := fun h => hε (funext fun j => h j)
        have hnε' : ¬ ∀ j, ε' j = false := fun h => hε' (funext fun j => h j)
        -- the three nonzero factors at the corners `(ε,0)`, `(0,ε')` and `(0,0)`
        have hA : f (y + cornerShift gL gL' ε + cornerShift gR gR' zeroF) ≠ 0 := by
          intro hf0
          refine hKBne ε zeroF ?_
          rw [cUB_apply_left f dH0 dH1 ε zeroF (fun j => rfl) hnε
                (y + cornerShift gL gL' ε + cornerShift gR gR' zeroF), hf0, zero_mul]
          exact star_iterate_zero _
        have hB' : f (y + cornerShift gL gL' zeroF + cornerShift gR gR' ε') ≠ 0 := by
          intro hf0
          refine hKBne zeroF ε' ?_
          rw [cUB_apply_right f dH0 dH1 zeroF ε' (fun j => rfl) hnε'
                (y + cornerShift gL gL' zeroF + cornerShift gR gR' ε'), hf0, star_zero, zero_mul]
          exact star_iterate_zero _
        have hC : f (y + cornerShift gL gL' zeroF + cornerShift gR gR' zeroF + dH0) ≠ 0 := by
          intro hf0
          refine hKBne zeroF zeroF ?_
          rw [cUB_apply_both f dH0 dH1 zeroF zeroF (fun j => rfl) (fun j => rfl)
                (y + cornerShift gL gL' zeroF + cornerShift gR gR' zeroF), hf0, star_zero, zero_mul]
          exact star_iterate_zero _
        -- hence the three base points lie in the translate `x₀ + symIcc N` of the support
        obtain ⟨hA1, hA2⟩ := support_bounds hsup hA
        obtain ⟨hB1, hB2⟩ := support_bounds hsup hB'
        obtain ⟨hC1, hC2⟩ := support_bounds hsup hC
        -- and the mixed base point is `p(ε,0) + p(0,ε') − p(0,0)`, so it lies in `mixWin`
        have hmem : y + cornerShift gL gL' ε + cornerShift gR gR' ε' ∈ mixWin x₀ dH0 N := by
          rw [mixWin, Finset.mem_map]
          refine ⟨y + cornerShift gL gL' ε + cornerShift gR gR' ε' - (x₀ + dH0), ?_, ?_⟩
          · rw [symIcc, Finset.mem_Icc]
            push_cast
            have hkey : y + cornerShift gL gL' ε + cornerShift gR gR' ε' - (x₀ + dH0)
                = ((y + cornerShift gL gL' ε + cornerShift gR gR' zeroF) - x₀)
                  + ((y + cornerShift gL gL' zeroF + cornerShift gR gR' ε') - x₀)
                  - ((y + cornerShift gL gL' zeroF + cornerShift gR gR' zeroF + dH0) - x₀) := by
              ring
            constructor <;> linarith [hA1, hA2, hB1, hB2, hC1, hC2, hkey]
          · show (Equiv.addRight (x₀ + dH0))
                (y + cornerShift gL gL' ε + cornerShift gR gR' ε' - (x₀ + dH0))
              = y + cornerShift gL gL' ε + cornerShift gR gR' ε'
            rw [Equiv.coe_addRight]; ring
        simp only [hmul]
        rw [if_neg hmix]
        simp only [hInd]
        rw [if_pos hmem]
    have hprod : (∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool, mul (ε, ε')) = 1 := by
      apply Finset.prod_eq_one
      intro ε _
      apply Finset.prod_eq_one
      intro ε' _
      exact hmul_one ε ε'
    rw [hprod, mul_one]

end Work.Peluse.SwapC
