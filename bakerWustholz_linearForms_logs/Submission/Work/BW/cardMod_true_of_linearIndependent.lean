import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-- Collision-free case `ε = true` with at least two independent rows: if `θ i = exp (ℓ i)` with
`ℓ₁,…,ℓ_N` `ℚ`-linearly independent and the rows of `M` are `ℚ`-linearly independent, then the
classes of `{0,…,S}·γ` modulo `G' = G_a × ker 𝒵` are pairwise distinct, so `cardMod` is `S + 1`.
(An integral relation `d·(row_j · ℓ) ∈ 2πiℤ` for two independent rows would eliminate `2πi` and
produce a nontrivial `ℚ`-relation among the `ℓᵢ`.) -/
theorem cardMod_true_of_linearIndependent {N ρ S : ℕ} (hρ : 2 ≤ ρ) (M : Fin ρ → Fin N → ℤ)
    (hM : LinearIndependent ℚ (fun j i => (M j i : ℚ))) (ℓ : Fin N → ℂ)
    (hℓ : LinearIndependent ℚ ℓ) :
    cardMod true M (fun i => Complex.exp (ℓ i)) S = S + 1 := by
  classical
  unfold cardMod
  simp only [ite_true]
  rw [Finset.card_image_of_injOn]
  · simp
  · -- Injectivity: two indices `a ≠ b` in `{0,…,S}` never give the same class.
    intro a _ b _ hab
    by_contra hne
    -- the second components of the two classes agree
    have hfun : (fun j : Fin ρ => ∏ i, (Complex.exp (ℓ i)) ^ ((a : ℤ) * M j i))
        = (fun j : Fin ρ => ∏ i, (Complex.exp (ℓ i)) ^ ((b : ℤ) * M j i)) := by
      have := congrArg Prod.snd hab
      simpa using this
    set L : Fin ρ → ℂ := fun j => ∑ i, (M j i : ℂ) * ℓ i with hL
    -- the product over `i` evaluates to `exp (s * L j)`
    have hprod : ∀ (s : ℕ) (j : Fin ρ),
        ∏ i, (Complex.exp (ℓ i)) ^ ((s : ℤ) * M j i) = Complex.exp ((s : ℂ) * L j) := by
      intro s j
      simp only [hL]
      rw [Finset.prod_congr rfl (fun i _ => (Complex.exp_int_mul (ℓ i) ((s : ℤ) * M j i)).symm)]
      rw [← Complex.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring
    have hfun' : ∀ j : Fin ρ, Complex.exp ((a : ℂ) * L j) = Complex.exp ((b : ℂ) * L j) := by
      intro j
      rw [← hprod a j, ← hprod b j]
      exact congrFun hfun j
    have hD : ((b : ℂ) - (a : ℂ)) ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hne))
    -- consequently `exp ((b - a) * L j) = 1` for every `j`
    have hexp1 : ∀ j : Fin ρ, Complex.exp (((b : ℂ) - (a : ℂ)) * L j) = 1 := by
      intro j
      have h := hfun' j
      have hB : (b : ℂ) * L j = (a : ℂ) * L j + ((b : ℂ) - (a : ℂ)) * L j := by ring
      rw [hB, Complex.exp_add] at h
      refine mul_left_cancel₀ (Complex.exp_ne_zero ((a : ℂ) * L j)) ?_
      rw [mul_one]
      exact h.symm
    have hj0 : 0 < ρ := by omega
    have hj1 : 1 < ρ := by omega
    set j0 : Fin ρ := ⟨0, hj0⟩ with hj0def
    set j1 : Fin ρ := ⟨1, hj1⟩ with hj1def
    -- two independent rows give `(b - a) L j0 ∈ 2πiℤ` and `(b - a) L j1 ∈ 2πiℤ`
    obtain ⟨n0, hEn0⟩ := Complex.exp_eq_one_iff.mp (hexp1 j0)
    obtain ⟨n1, hEn1⟩ := Complex.exp_eq_one_iff.mp (hexp1 j1)
    -- eliminate `2πi` between the two relations
    have hrel : (n1 : ℂ) * L j0 - (n0 : ℂ) * L j1 = 0 := by
      have h : ((b : ℂ) - (a : ℂ)) * ((n1 : ℂ) * L j0 - (n0 : ℂ) * L j1) = 0 := by
        have e1 : ((b : ℂ) - (a : ℂ)) * ((n1 : ℂ) * L j0)
            = (n1 : ℂ) * (((b : ℂ) - (a : ℂ)) * L j0) := by ring
        have e2 : ((b : ℂ) - (a : ℂ)) * ((n0 : ℂ) * L j1)
            = (n0 : ℂ) * (((b : ℂ) - (a : ℂ)) * L j1) := by ring
        rw [mul_sub, e1, e2, hEn0, hEn1]
        ring
      exact (mul_eq_zero.mp h).resolve_left hD
    -- this is a rational relation among the `ℓᵢ`
    have hrel2 : ∑ i, ((n1 * M j0 i - n0 * M j1 i : ℤ) : ℂ) * ℓ i = 0 := by
      rw [← hrel]
      simp only [hL]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring
    have hcoeff : ∀ i, ((n1 * M j0 i - n0 * M j1 i : ℤ) : ℚ) = 0 := by
      intro i
      refine (Fintype.linearIndependent_iff.mp hℓ)
        (fun i => ((n1 * M j0 i - n0 * M j1 i : ℤ) : ℚ)) ?_ i
      rw [← hrel2]
      apply Finset.sum_congr rfl
      intro i _
      rw [Rat.smul_def]
      push_cast
      ring
    -- so the two rows are proportional over `ℚ`
    have hrows : (n1 : ℚ) • (fun i => (M j0 i : ℚ)) - (n0 : ℚ) • (fun i => (M j1 i : ℚ)) = 0 := by
      funext i
      have h := hcoeff i
      push_cast at h
      simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
    -- independence of the rows forces `n0 = n1 = 0`
    let f2 : Fin 2 → Fin ρ := ![j0, j1]
    have hf2 : Function.Injective f2 := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [f2]
    have hpair : LinearIndependent ℚ (fun t : Fin 2 => (fun i => (M (f2 t) i : ℚ))) :=
      hM.comp f2 hf2
    have hsum2 : ∑ t : Fin 2, (if t = 0 then (n1 : ℚ) else -(n0 : ℚ)) •
        (fun i => (M (f2 t) i : ℚ)) = 0 := by
      have e0 : f2 0 = j0 := by simp [f2]
      have e1 : f2 1 = j1 := by simp [f2]
      rw [Fin.sum_univ_two, e0, e1]
      simpa [neg_smul, sub_eq_add_neg] using hrows
    have key := (Fintype.linearIndependent_iff.mp hpair)
      (fun t : Fin 2 => if t = 0 then (n1 : ℚ) else -(n0 : ℚ)) hsum2
    have hn1 : n1 = 0 := by
      have h := key 0
      simpa using h
    have hn0 : n0 = 0 := by
      have h := key 1
      have h' : -(n0 : ℚ) = 0 := by simpa using h
      have h'' : (n0 : ℚ) = 0 := neg_eq_zero.mp h'
      exact_mod_cast h''
    -- hence `L j0 = 0`, i.e. `∑ M j0 i * ℓ i = 0`, contradicting independence of the `ℓᵢ`
    have hL0 : L j0 = 0 := by
      have h : ((b : ℂ) - (a : ℂ)) * L j0 = 0 := by
        rw [hEn0, hn0]; simp
      exact (mul_eq_zero.mp h).resolve_left hD
    have hrow0 : (fun i => (M j0 i : ℚ)) = 0 := by
      funext i
      have e : ∑ i, (((M j0 i : ℤ)) : ℚ) • ℓ i = L j0 := by
        simp only [hL]
        apply Finset.sum_congr rfl
        intro i _
        rw [Rat.smul_def]
        push_cast
        ring
      have hsum3 : ∑ i, (((M j0 i : ℤ)) : ℚ) • ℓ i = 0 := by rw [e, hL0]
      exact (Fintype.linearIndependent_iff.mp hℓ) (fun i => ((M j0 i : ℤ) : ℚ)) hsum3 i
    exact hM.ne_zero j0 hrow0

end Work.BW
