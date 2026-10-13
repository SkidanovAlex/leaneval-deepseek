import Mathlib
import Submission.Work.WilE10.RexpSubDefs
import Submission.Work.WilE10.BranchEval.branchPoly_eval

namespace Work.WilE10.RexpSub

open Work.WilE10 WilkiesDesign WilkiesDesign.E

/-- **Reverse direction of `E10_rexp_to_subpf`.**  A point of the semi-Pfaffian set `W n m P`
whose first `n` compactified coordinates come from `psiV t` determines values `y` of the
remaining coordinates with `rexpPolyEval P (Fin.append t y) = 0`.  This is the projection
statement `projFirst n (rd n m) '' (W n m P).set = psiV ⁻¹' {x | ∃ y, rexpPolyEval P (x,y) = 0}`
for points of the form `(psiV t, v)`. -/
theorem exists_rexp_of_mem_W (n m : ℕ) (P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ)
    (t : Fin n → ℝ) (v : Fin (Work.WilE10.rd n m) → ℝ)
    (h : Fin.append (WilkiesDesign.E.psiV t) v ∈ (Work.WilE10.W n m P).set) :
    ∃ y : Fin m → ℝ, WilkiesDesign.rexpPolyEval P (Fin.append t y) = 0 := by
  set x : Fin (Kdim n m) → ℝ := Fin.append (psiV t) v with hx
  simp only [W, SemiPf.set, Set.mem_setOf_eq] at h
  obtain ⟨-, B, hB, hBh⟩ := h
  obtain ⟨ε, -, rfl⟩ := List.mem_map.mp hB
  -- the compactified coordinates come from `psi`
  have hxuu : ∀ i : Fin n, x (uu n m i) = psi (t i) := by
    intro i
    rw [hx, uu_eq, Fin.append_left]
    rfl
  -- the six families of conditions, extracted from the basic set
  have htag : ∀ i : Fin (n + m), ε i = true → x (ut n m i) ^ 2 + x (uq n m i) ^ 2 = 1 := by
    intro i hi
    have h1 := hBh.1 (tagEq n m i) (by
      simp only [basicOf, eqsOf, List.mem_append, List.mem_cons]
      exact Or.inr (Or.inl (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by simp [hi]⟩)))
    simp [eaEval, tagEq, Xa] at h1
    linarith
  have hrelA : ∀ i : Fin n, ε (Fin.castAdd m i) = true →
      x (uu n m i) ^ 2 * (1 + x (ut n m (Fin.castAdd m i)) ^ 2)
        = x (ut n m (Fin.castAdd m i)) ^ 2 := by
    intro i hi
    have h1 := hBh.1 (relA n m i) (by
      simp only [basicOf, eqsOf, List.mem_append, List.mem_cons]
      exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by simp [hi]⟩)))
    simp [eaEval, relA, Xa] at h1
    linarith
  have hrelB : ∀ i : Fin n, ε (Fin.castAdd m i) = true →
      ∃ w : ℝ, x (uu n m i) * x (ut n m (Fin.castAdd m i)) = w ^ 2 := by
    intro i hi
    have h1 := hBh.1 (relB n m i) (by
      simp only [basicOf, eqsOf, List.mem_append, List.mem_cons]
      exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by simp [hi]⟩)))
    simp [eaEval, relB, Xa] at h1
    exact ⟨x (uw n m i), by linarith⟩
  have hrelC : ∀ i : Fin n, ε (Fin.castAdd m i) = false →
      x (uu n m i) ^ 2 * (1 + x (us n m (Fin.castAdd m i)) ^ 2) = 1 := by
    intro i hi
    have h1 := hBh.1 (relC n m i) (by
      simp only [basicOf, eqsOf, List.mem_append, List.mem_cons]
      exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by simp [hi]⟩)))
    simp [eaEval, relC, Xa] at h1
    linarith
  have hposS : ∀ j : Fin (n + m), ε j = false → |x (us n m j)| < 1 := by
    intro j hj
    have h1 := hBh.2 (posS n m j) (by
      simp only [basicOf, posOf, List.mem_append]
      exact Or.inl (List.mem_flatMap.mpr ⟨j, List.mem_finRange j, by simp [hj]⟩))
    simpa [eaEval, posS, Xa] using h1
  have hsNZ : ∀ j : Fin (n + m), ε j = false → 0 < x (us n m j) ^ 2 := by
    intro j hj
    have h1 := hBh.2 (sNZ n m j) (by
      simp only [basicOf, posOf, List.mem_append]
      exact Or.inl (List.mem_flatMap.mpr ⟨j, List.mem_finRange j, by simp [hj]⟩))
    simpa [eaEval, sNZ, Xa] using h1
  have hposSign : ∀ i : Fin n, ε (Fin.castAdd m i) = false →
      0 < x (uu n m i) * x (us n m (Fin.castAdd m i)) := by
    intro i hi
    have h1 := hBh.2 (posSign n m i) (by
      simp only [basicOf, posOf, List.mem_append]
      exact Or.inr (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by simp [hi]⟩))
    simpa [eaEval, posSign, Xa] using h1
  -- the value of the `j`-th argument, reconstructed from its block
  set T : Fin (n + m) → ℝ :=
    fun j => if ε j then x (ut n m j) else (x (us n m j))⁻¹ with hT
  -- on the first `n` coordinates `T` agrees with `t`
  have hTc : ∀ i : Fin n, T (Fin.castAdd m i) = t i := by
    intro i
    by_cases hε : ε (Fin.castAdd m i) = true
    · have hTv : T (Fin.castAdd m i) = x (ut n m (Fin.castAdd m i)) := by simp [hT, hε]
      rw [hTv]
      obtain ⟨w, hw⟩ := hrelB i hε
      have hpsi : x (uu n m i) = psi (x (ut n m (Fin.castAdd m i))) :=
        psi_eq_of_sq (hrelA i hε) (by rw [hw]; positivity)
      rw [hxuu i] at hpsi
      exact (psi_injective hpsi).symm
    · have hεf : ε (Fin.castAdd m i) = false := by
        cases hv : ε (Fin.castAdd m i) <;> simp_all
      have hTv : T (Fin.castAdd m i) = (x (us n m (Fin.castAdd m i)))⁻¹ := by simp [hT, hεf]
      rw [hTv]
      obtain ⟨hu, -⟩ := psi_recip_eq (hrelC i hεf) (hposSign i hεf) (hposS (Fin.castAdd m i) hεf)
      rw [hxuu i] at hu
      exact (psi_injective hu).symm
  set S : Fin (n + m) → ℝ := fun j => x (us n m j) with hS
  -- the equation of the branch polynomial vanishes
  have hbr : eaEval (chain n m) (branchPoly (degb P) ε (ut n m) (us n m) id P) x = 0 :=
    hBh.1 (branchPoly (degb P) ε (ut n m) (us n m) id P) (by simp [basicOf, eqsOf])
  -- `branchPoly_eval` rewrites it as `(∏ S^D) * rexpPolyEval P T = 0`
  have key := Work.WilE10.BranchEval.branchPoly_eval (degb P) ε (ut n m) (us n m)
      (id : Fin (n + m) → Fin (n + m)) P T S (fun j => Real.exp ((chain n m).ell j x)) x
      (fun i hi => by simp [hT, hi])
      (fun i hi => by rw [hT, ell_chain]; simp [hi])
      (fun i hi => by
        have hTv : T i = x (ut n m i) := by simp [hT, hi]
        rw [hTv]
        have h1 : (x (ut n m i)) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x (uq n m i)), htag i hi]
        exact (sq_le_one_iff_abs_le_one _).mp h1)
      (fun i hi => by simp [hS])
      (fun i hi => by
        have hs0 : x (us n m i) ≠ 0 := by
          have hp := hsNZ i hi
          intro h0; rw [h0] at hp; norm_num at hp
        have hSv : S i = x (us n m i) := by simp [hS]
        have hTv : T i = (x (us n m i))⁻¹ := by simp [hT, hi]
        rw [hSv, hTv]
        exact mul_inv_cancel₀ hs0)
      (fun i hi => by
        have hs0 : x (us n m i) ≠ 0 := by
          have hp := hsNZ i hi
          intro h0; rw [h0] at hp; norm_num at hp
        have hTv : T i = (x (us n m i))⁻¹ := by simp [hT, hi]
        rw [hTv, abs_inv, inv_eq_one_div]
        exact (one_lt_div (abs_pos.mpr hs0)).mpr (hposS i hi))
      (fun i mm hm => le_degb P hm i)
  have key2 : (∏ i ∈ Finset.univ.filter (fun i => ε i = false), S i ^ degb P) *
      MvPolynomial.eval (Sum.elim T (fun i => rexp (T i))) P = 0 := by
    rw [← key]
    exact hbr
  -- the product is nonzero: every large reciprocal is nonzero
  have hne : (∏ i ∈ Finset.univ.filter (fun i => ε i = false), S i ^ degb P) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    rw [Finset.mem_filter] at hi
    refine pow_ne_zero _ ?_
    have hp := hsNZ i hi.2
    have hSv : S i = x (us n m i) := by simp [hS]
    rw [hSv]
    intro h0; rw [h0] at hp; norm_num at hp
  have hrexp : MvPolynomial.eval (Sum.elim T (fun i => rexp (T i))) P = 0 := by
    rcases mul_eq_zero.mp key2 with h' | h'
    · exact absurd h' hne
    · exact h'
  refine ⟨fun j => T (Fin.natAdd n j), ?_⟩
  have hTeq : T = Fin.append t (fun j => T (Fin.natAdd n j)) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro i
      rw [Fin.append_left]; exact hTc i
    · intro j
      simp [Fin.append_right]
  rw [← hTeq]
  simpa only [WilkiesDesign.rexpPolyEval] using hrexp

end Work.WilE10.RexpSub
