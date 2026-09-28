import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.Q44Child.lam_attained
import Submission.Work.HP.Q44Child.gam_rank
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.BridgeDefs

/-!
# A witness form outside `W(L)` (`Work.HP.Q44Child.witness_outside`)

`witness_outside`: for a rank-`3` lattice `L ⊆ ℤ^5`, vectors `x y ∈ L` and a radius `J` with
`λ_{56}(Γ_{x,y}) ≤ J`, there is a non-zero form `a ∈ Γ_{x,y} = Gam 4 4 x y` of norm at most `J`
that does *not* vanish identically on `L`.

The mathematics: `Γ_{x,y}` has rank `68 = 70 - 2 ≥ 56`, so `λ_{56}(Γ_{x,y}) ≤ J` produces `56`
independent forms in `Γ_{x,y}` of norm at most `J` (per-vector attainment of the successive
minima, `Work.HP.Q44Child.lamAttained_aux`).  The forms vanishing on all of `L` form the
sublattice `vanishOn L = W(L)^⊥` of rank `55 = 70 - 15` (a quartic form on the rank-`3` lattice
`L` is a quartic form in three variables, a space of dimension `15`); since `56 > 55`, one of
the `56` forms does not vanish on `L`.  The rank bound `rk (vanishOn L) ≤ 55` is proved here as
`vanish_rank_aux`, by exhibiting the `3`-dimensional `ℚ`-span `V` of `L`, the `15`-dimensional
space `Ω.range` of restrictions of quartics to `V` (with `ker Ω = ℚ ⊗ (vanishOn L)`), and
transferring rank-nullity from `ℚ` back to `ℤ`.

The lemma itself was the requested statement; the helper lemmas above it in this file are the
pieces of that argument.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.HP.Q44Child

open MvPolynomial Finset



/-- Every homogeneous degree-`4` polynomial in `n+1` variables lies in the span of the
degree-`4` monomials. -/
lemma homogeneous_mem_span_monomial_aux (n : ℕ) {P : MvPolynomial (Fin (n+1)) ℚ}
    (hP : P.IsHomogeneous 4) :
    P ∈ Submodule.span ℚ (Set.range fun m : Mon 4 n => MvPolynomial.monomial m.toFinsupp (1 : ℚ)) := by
  classical
  have h1 : P = ∑ d ∈ P.support with d.degree = 4, MvPolynomial.monomial d (P.coeff d) := by
    have := MvPolynomial.homogeneousComponent_apply (n := 4) P
    rw [← this, MvPolynomial.homogeneousComponent_eq_self hP]
  rw [h1]
  have h2 : ∑ d ∈ P.support with d.degree = 4, MvPolynomial.monomial d (P.coeff d)
      = ∑ d ∈ (Finset.univ.image (fun m : Mon 4 n => m.toFinsupp)),
          MvPolynomial.monomial d (P.coeff d) := by
    apply Finset.sum_subset
    · intro d hd
      obtain ⟨-, hddeg⟩ := Finset.mem_filter.mp hd
      have hdsum : ∑ i, d i = 4 := by
        rw [← Finsupp.degree_eq_sum]; exact hddeg
      have hdi : ∀ i, d i ≤ 4 := fun i =>
        le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)) (le_of_eq hdsum)
      refine Finset.mem_image.mpr ⟨⟨fun i => ⟨d i, by have := hdi i; omega⟩, ?_⟩, Finset.mem_univ _, ?_⟩
      · exact hdsum
      · ext i; simp [Mon_toFinsupp_apply]
    · intro d hd hnot
      have hddeg : d.degree = 4 := by
        obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hd
        rw [← hm]; exact Mon_degree_toFinsupp m
      have hdsupp : d ∉ P.support := by
        intro hc
        exact hnot (Finset.mem_filter.mpr ⟨hc, hddeg⟩)
      rw [show MvPolynomial.monomial d (P.coeff d)
            = MvPolynomial.C (P.coeff d) * MvPolynomial.monomial d (1:ℚ) from by
          rw [MvPolynomial.C_mul_monomial, mul_one],
        show P.coeff d = 0 from MvPolynomial.notMem_support_iff.mp hdsupp]
      simp
  rw [h2]
  rw [Finset.sum_image (g := fun m : Mon 4 n => m.toFinsupp)
        (f := fun d => MvPolynomial.monomial d (P.coeff d))
        (fun x _ y _ hxy => Mon_toFinsupp_injective hxy)]
  refine Submodule.sum_mem _ (fun m _ => ?_)
  rw [show MvPolynomial.monomial m.toFinsupp (P.coeff m.toFinsupp)
        = (P.coeff m.toFinsupp) • MvPolynomial.monomial m.toFinsupp (1:ℚ) from by
      rw [← MvPolynomial.C_mul', MvPolynomial.C_mul_monomial, mul_one]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

/-- Given three `ℚ`-linearly independent vectors in `ℚ^5` there are dual vectors. -/
lemma exists_dual_vectors_aux (v : Fin 3 → (Fin 5 → ℚ)) (hv : LinearIndependent ℚ v) :
    ∃ m : Fin 3 → (Fin 5 → ℚ), ∀ j k : Fin 3, ∑ i, m k i * v j i = if j = k then (1 : ℚ) else 0 := by
  classical
  let B : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) :=
    { toFun := fun c i => ∑ j, c j * v j i
      map_add' := by intro c c'; funext i; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro a c; funext i; simp [Finset.mul_sum, mul_assoc] }
  have hBv : ∀ j : Fin 3, B (Pi.single j (1:ℚ) : Fin 3 → ℚ) = v j := by
    intro j; funext i
    show (∑ j', (Pi.single j (1:ℚ) : Fin 3 → ℚ) j' * v j' i) = v j i
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hB : B.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have hvc : ∑ j, c j • v j = 0 := by
      funext i; simpa [B, Finset.sum_apply] using congrFun hc i
    funext i
    exact (Fintype.linearIndependent_iff.mp hv) c hvc i
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective B hB
  refine ⟨fun k i => (g (Pi.single i (1:ℚ) : Fin 5 → ℚ)) k, ?_⟩
  intro j k
  have hL : ∑ i, (g (Pi.single i (1:ℚ) : Fin 5 → ℚ)) k * v j i
      = (∑ i, v j i • g (Pi.single i (1:ℚ) : Fin 5 → ℚ)) k := by
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => by simp [Pi.smul_apply, mul_comm])
  have hsum : (∑ i, v j i • (Pi.single i (1:ℚ) : Fin 5 → ℚ)) = v j := by
    funext i'
    rw [Finset.sum_apply, Finset.sum_eq_single i']
    · simp
    · intro b _ hb
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (Ne.symm hb), mul_zero]
    · intro h'; exact absurd (Finset.mem_univ i') h'
  have hmain : (∑ i, v j i • g (Pi.single i (1:ℚ) : Fin 5 → ℚ))
      = g (∑ i, v j i • (Pi.single i (1:ℚ) : Fin 5 → ℚ)) := by
    rw [map_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
  have h3 : (g (v j)) k = (Pi.single j (1:ℚ) : Fin 3 → ℚ) k := by
    rw [← hBv j]
    exact congrFun (LinearMap.congr_fun hg (Pi.single j (1:ℚ) : Fin 3 → ℚ)) k
  rw [hL, hmain, hsum, h3]
  by_cases h : j = k
  · rw [h, Pi.single_eq_same, if_pos rfl]
  · rw [Pi.single_eq_of_ne (fun hh => h hh.symm), if_neg h]



/-- A monomial is the product of the corresponding powers of the variables. -/
lemma monomial_eq_prod_aux {n : ℕ} (s : Fin (n+1) →₀ ℕ) :
    MvPolynomial.monomial s (1:ℚ) = ∏ i : Fin (n+1), MvPolynomial.X i ^ (s i) := by
  have h := MvPolynomial.prod_X_pow_eq_monomial (s := s) (R := ℚ)
  rw [Finset.prod_subset (s₁ := s.support) (s₂ := Finset.univ) (Finset.subset_univ _)
    (fun i _ hi => by rw [Finsupp.notMem_support_iff] at hi; rw [hi, pow_zero])] at h
  exact h.symm

/-- Evaluation commutes with scalar multiplication. -/
lemma eval_smul_C_aux {σ : Type*} (c : σ → ℚ) (r : ℚ) (p : MvPolynomial σ ℚ) :
    MvPolynomial.eval c (r • p) = r * MvPolynomial.eval c p := by
  rw [← MvPolynomial.C_mul', map_mul, MvPolynomial.eval_C]

/-- The rank of `vanishOn L` is at most `55` for a rank-`3` lattice `L ⊆ ℤ^5`. -/
theorem vanish_rank_aux (L : Submodule ℤ (Fin 5 → ℤ)) (hL : Work.HP.rk L = 3) :
    Work.HP.rk (Work.HP.vanishOn L) ≤ 55 := by
  classical
  obtain ⟨v, hvL, hvI⟩ := exists_linIndep_card L (i := 3) (by rw [hL])
  let vQ : Fin 3 → (Fin 5 → ℚ) := fun j => ⇑(algebraMap ℤ ℚ) ∘ v j
  have hvQ : LinearIndependent ℚ vQ := by
    have h := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ)).mpr hvI
    simpa only [vQ] using h
  obtain ⟨mu, hmu⟩ := exists_dual_vectors_aux vQ hvQ
  -- the linear forms on `ℚ^3`
  let Lin : Fin 5 → MvPolynomial (Fin 3) ℚ :=
    fun i => ∑ j : Fin 3, MvPolynomial.C (vQ j i) * MvPolynomial.X j
  have hLin1 : ∀ i : Fin 5, (Lin i).IsHomogeneous 1 := by
    intro i
    show (∑ j : Fin 3, MvPolynomial.C (vQ j i) * MvPolynomial.X j).IsHomogeneous 1
    refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun j _ => ?_)
    simpa using (MvPolynomial.isHomogeneous_C (Fin 3) (vQ j i)).mul
      (MvPolynomial.isHomogeneous_X ℚ j)
  -- the generators of the image
  let G : Mon 4 4 → MvPolynomial (Fin 3) ℚ := fun mm => ∏ i : Fin 5, (Lin i) ^ (mm.1 i : ℕ)
  have hG_eq : ∀ mm : Mon 4 4, G mm = ∏ i : Fin 5, (Lin i) ^ (mm.1 i : ℕ) := fun mm => rfl
  have hGhom : ∀ mm : Mon 4 4, (G mm).IsHomogeneous 4 := by
    intro mm
    have h : (∏ i : Fin 5, (Lin i) ^ (mm.1 i : ℕ)).IsHomogeneous (∑ i : Fin 5, (mm.1 i : ℕ)) := by
      refine MvPolynomial.IsHomogeneous.prod Finset.univ (fun i : Fin 5 => (Lin i) ^ (mm.1 i : ℕ))
        (fun i => (mm.1 i : ℕ)) (fun i _ => ?_)
      simpa using (hLin1 i).pow (mm.1 i : ℕ)
    simpa [hG_eq mm, mm.2] using h
  -- the restriction map
  let Ω : (Mon 4 4 → ℚ) →ₗ[ℚ] MvPolynomial (Fin 3) ℚ := Fintype.linearCombination ℚ G
  have hΩ_apply : ∀ a : Mon 4 4 → ℚ, Ω a = ∑ mm, a mm • G mm :=
    fun a => Fintype.linearCombination_apply ℚ G a
  have hrange : Ω.range = Submodule.span ℚ (Set.range G) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨a, rfl⟩ := hy
      rw [hΩ_apply]
      exact Submodule.sum_mem _ (fun mm _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨mm, rfl⟩))
    · rw [Submodule.span_le]
      rintro y ⟨mm, rfl⟩
      refine LinearMap.mem_range.mpr ⟨Pi.single mm (1:ℚ), ?_⟩
      rw [hΩ_apply, Finset.sum_eq_single mm]
      · simp
      · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_smul]
      · intro h; exact absurd (Finset.mem_univ mm) h
  -- the model space of degree-`4` forms in three variables
  let P : Submodule ℚ (MvPolynomial (Fin 3) ℚ) :=
    Submodule.span ℚ (Set.range fun e : Mon 4 2 => MvPolynomial.monomial e.toFinsupp (1:ℚ))
  have hP_eq : P = Submodule.span ℚ (Set.range fun e : Mon 4 2 =>
      MvPolynomial.monomial e.toFinsupp (1:ℚ)) := rfl
  haveI hPfin : Module.Finite ℚ P :=
    Module.Finite.of_fg (hP_eq ▸ Submodule.fg_span (Set.finite_range _))
  haveI hΩfin : Module.Finite ℚ Ω.range :=
    hrange ▸ Module.Finite.of_fg (Submodule.fg_span (Set.finite_range G))
  -- (A) the image lies in the model space
  have hA : Ω.range ≤ P := by
    rw [hrange, hP_eq, Submodule.span_le]
    rintro y ⟨mm, rfl⟩
    exact homogeneous_mem_span_monomial_aux 2 (hGhom mm)
  -- the 15 monomials are linearly independent
  have hcard : Fintype.card (Mon 4 2) = 15 := by decide
  have hlin : LinearIndependent ℚ (fun e : Mon 4 2 => MvPolynomial.monomial e.toFinsupp (1:ℚ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg e
    have h1 : (∑ b : Mon 4 2, g b • MvPolynomial.monomial b.toFinsupp (1:ℚ)).coeff e.toFinsupp
        = (0 : MvPolynomial (Fin 3) ℚ).coeff e.toFinsupp := by rw [hg]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single e] at h1
    · rw [MvPolynomial.coeff_monomial, if_pos rfl] at h1
      simpa using h1
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg (fun hc => hb (Mon_toFinsupp_injective hc)), smul_zero]
    · intro h; exact absurd (Finset.mem_univ e) h
  -- (B) the monomials lie in the image
  have hB : ∀ e : Mon 4 2, MvPolynomial.monomial e.toFinsupp (1:ℚ) ∈ Ω.range := by
    intro e
    let Q : Fin 3 → MvPolynomial (Fin 5) ℚ := fun k =>
      ∑ i : Fin 5, MvPolynomial.C (mu k i) * MvPolynomial.X i
    have hQ1 : ∀ k, (Q k).IsHomogeneous 1 := by
      intro k
      show (∑ i : Fin 5, MvPolynomial.C (mu k i) * MvPolynomial.X i).IsHomogeneous 1
      refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => ?_)
      simpa using (MvPolynomial.isHomogeneous_C (Fin 5) (mu k i)).mul
        (MvPolynomial.isHomogeneous_X ℚ i)
    have hQhom : (∏ k : Fin 3, (Q k) ^ (e.1 k : ℕ)).IsHomogeneous 4 := by
      have h : (∏ k : Fin 3, (Q k) ^ (e.1 k : ℕ)).IsHomogeneous (∑ k : Fin 3, (e.1 k : ℕ)) := by
        refine MvPolynomial.IsHomogeneous.prod Finset.univ (fun k : Fin 3 => (Q k) ^ (e.1 k : ℕ))
          (fun k => (e.1 k : ℕ)) (fun k _ => ?_)
        simpa using (hQ1 k).pow (e.1 k : ℕ)
      simpa [e.2] using h
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun ℚ).mp (homogeneous_mem_span_monomial_aux 4 hQhom)
    refine ⟨c, ?_⟩
    rw [hΩ_apply]
    let ψ : MvPolynomial (Fin 5) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ := MvPolynomial.aeval Lin
    have hψX : ∀ i : Fin 5, ψ (MvPolynomial.X i) = Lin i := by
      intro i; show MvPolynomial.aeval Lin (MvPolynomial.X i) = Lin i
      exact MvPolynomial.aeval_X Lin i
    have hG_apply : ∀ mm : Mon 4 4, G mm = ∏ i : Fin 5, (Lin i) ^ (mm.1 i : ℕ) := fun mm => rfl
    have hψ_mon : ∀ mm : Mon 4 4, ψ (MvPolynomial.monomial mm.toFinsupp (1:ℚ)) = G mm := by
      intro mm
      rw [monomial_eq_prod_aux (n := 4) mm.toFinsupp, map_prod, hG_apply mm]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [map_pow, hψX, Mon_toFinsupp_apply]
    have hψQ : ∀ k : Fin 3, ψ (Q k) = MvPolynomial.X k := by
      intro k
      have hψ : ψ (Q k) = ∑ i : Fin 5, MvPolynomial.C (mu k i) * Lin i := by
        show MvPolynomial.aeval Lin
          (∑ i : Fin 5, MvPolynomial.C (mu k i) * MvPolynomial.X i) = _
        rw [map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_X (f := Lin) i]
      rw [hψ]
      have h2 : (∑ i : Fin 5, MvPolynomial.C (mu k i) * Lin i)
          = ∑ j : Fin 3, MvPolynomial.C (∑ i : Fin 5, mu k i * vQ j i) * MvPolynomial.X j := by
        have h3 : ∀ i : Fin 5, MvPolynomial.C (mu k i) * Lin i
            = ∑ j : Fin 3, MvPolynomial.C (mu k i * vQ j i) * MvPolynomial.X j := by
          intro i
          rw [show Lin i = ∑ j : Fin 3, MvPolynomial.C (vQ j i) * MvPolynomial.X j from rfl]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [show MvPolynomial.C (mu k i) * (MvPolynomial.C (vQ j i) * MvPolynomial.X j)
              = MvPolynomial.C (mu k i * vQ j i) * MvPolynomial.X j from by
            rw [← mul_assoc, ← map_mul]]
        rw [Finset.sum_congr rfl (fun i _ => h3 i), Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← Finset.sum_mul]
        congr 1
        rw [← map_sum]
      rw [h2, Finset.sum_eq_single k]
      · rw [hmu k k, if_pos rfl, map_one, one_mul]
      · intro b _ hb
        rw [hmu b k, if_neg hb, map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ k) h
    have hψprod : ψ (∏ k : Fin 3, (Q k) ^ (e.1 k : ℕ))
        = MvPolynomial.monomial e.toFinsupp (1:ℚ) := by
      rw [map_prod, monomial_eq_prod_aux (n := 2) e.toFinsupp]
      refine Finset.prod_congr rfl (fun k _ => ?_)
      rw [map_pow, hψQ, Mon_toFinsupp_apply]
    have hmain : ψ (∑ mm, c mm • MvPolynomial.monomial mm.toFinsupp (1:ℚ)) = ∑ mm, c mm • G mm := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun mm _ => by rw [map_smul, hψ_mon])
    rw [← hmain, hc, hψprod]
  have hBle : P ≤ Ω.range := by
    rw [hP_eq, Submodule.span_le]
    rintro y ⟨e, rfl⟩
    exact hB e
  have hfinP : Module.finrank ℚ P = 15 := by
    rw [hP_eq, finrank_span_eq_card hlin, hcard]
  have hrank15 : Module.finrank ℚ Ω.range = 15 := by
    apply le_antisymm
    · rw [← hfinP]; exact Submodule.finrank_mono hA
    · rw [← hfinP]; exact Submodule.finrank_mono hBle
  have hker : Module.finrank ℚ Ω.ker = 55 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker Ω
    rw [hrank15, Module.finrank_fintype_fun_eq_card, card_Mon_four_four] at hrn
    omega
  -- elements of `vanishOn L` lie in the kernel
  have hC : ∀ a : Mon 4 4 → ℤ, a ∈ Work.HP.vanishOn L →
      (fun mm => (a mm : ℚ)) ∈ Ω.ker := by
    intro a ha
    rw [LinearMap.mem_ker]
    rw [MvPolynomial.funext_set_iff (s := fun _ : Fin 3 => Set.range (Int.cast : ℤ → ℚ))
      (fun _ => Set.infinite_range_of_injective (f := (Int.cast : ℤ → ℚ)) Int.cast_injective)]
    intro c hc
    rw [map_zero]
    simp only [Set.mem_pi, Set.mem_univ, true_implies] at hc
    choose k hk using hc
    have hceq : c = fun j => ((k j : ℤ) : ℚ) := by funext j; exact (hk j).symm
    rw [hceq]
    have hev : MvPolynomial.eval (fun j => ((k j : ℤ) : ℚ)) (Ω (fun mm => (a mm : ℚ)))
        = ((formEval 4 4 a (fun i => ∑ j, k j * v j i) : ℤ) : ℚ) := by
      rw [hΩ_apply, map_sum]
      have hterm : ∀ mm : Mon 4 4,
          MvPolynomial.eval (fun j => ((k j : ℤ) : ℚ)) ((a mm : ℚ) • G mm)
          = (a mm : ℚ) * ∏ i : Fin 5,
              (MvPolynomial.eval (fun j => ((k j : ℤ) : ℚ)) (Lin i)) ^ (mm.1 i : ℕ) := by
        intro mm
        rw [eval_smul_C_aux, hG_eq mm, map_prod]
        refine congrArg (fun z => (a mm : ℚ) * z) ?_
        exact Finset.prod_congr rfl (fun i _ => by rw [map_pow])
      rw [Finset.sum_congr rfl (fun mm _ => hterm mm)]
      rw [formEval]
      simp only [Int.cast_sum, Int.cast_mul]
      refine Finset.sum_congr rfl (fun mm _ => ?_)
      refine congrArg (fun z => (a mm : ℚ) * z) ?_
      simp only [veronese, Int.cast_prod, Int.cast_pow, Int.cast_sum, Int.cast_mul]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      refine congrArg (fun z => z ^ (mm.1 i : ℕ)) ?_
      have hLi : MvPolynomial.eval (fun j => ((k j : ℤ) : ℚ)) (Lin i)
          = ∑ j : Fin 3, vQ j i * ((k j : ℤ) : ℚ) := by
        show MvPolynomial.eval _ (∑ j : Fin 3, MvPolynomial.C (vQ j i) * MvPolynomial.X j) = _
        rw [map_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      rw [hLi]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [show vQ j i = ((v j i : ℤ) : ℚ) from by
        simp only [vQ, Function.comp_apply, algebraMap_int_eq]
        exact eq_intCast (Int.castRingHom ℚ) _]
      exact mul_comm _ _
    rw [hev]
    have hzero : formEval 4 4 a (fun i => ∑ j, k j * v j i) = 0 := by
      refine (mem_vanishOn (L := L) (a := a)).mp ha ⟨fun i => ∑ j, k j * v j i, ?_⟩
      have : (fun i => ∑ j, k j * v j i) = ∑ j : Fin 3, k j • v j := by
        funext i
        rw [Finset.sum_apply]
        exact Finset.sum_congr rfl (fun j _ => rfl)
      rw [this]
      exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hvL j))
    rw [hzero, Int.cast_zero]
  -- transfer
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Mon 4 4)) (Work.HP.vanishOn L)
  have hbasis : Module.finrank ℤ (Work.HP.vanishOn L) = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hle : n ≤ 55 := by
    have hbLI : LinearIndependent ℤ (fun i : Fin n => (b i : Mon 4 4 → ℤ)) :=
      b.linearIndependent.map' (Work.HP.vanishOn L).subtype
        (LinearMap.ker_eq_bot'.mpr (fun m hm => Subtype.coe_injective hm))
    have hfind : LinearIndependent ℚ (fun i : Fin n =>
        fun mm : Mon 4 4 => ((b i : Mon 4 4 → ℤ) mm : ℚ)) :=
      (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ)).mpr hbLI
    have hmem : ∀ i : Fin n, (fun mm : Mon 4 4 => ((b i : Mon 4 4 → ℤ) mm : ℚ)) ∈ Ω.ker :=
      fun i => hC _ (b i).2
    let g : Fin n → Ω.ker := fun i => ⟨_, hmem i⟩
    have hg : LinearIndependent ℚ g := by
      apply LinearIndependent.of_comp (Ω.ker).subtype
      have : ((Ω.ker).subtype : Ω.ker → (Mon 4 4 → ℚ)) ∘ g
          = fun i => fun mm : Mon 4 4 => ((b i : Mon 4 4 → ℤ) mm : ℚ) := by
        funext i mm; rfl
      rw [this]; exact hfind
    have hfin := LinearIndependent.fintype_card_le_finrank hg
    simp only [Fintype.card_fin] at hfin
    rw [hker] at hfin
    exact hfin
  rw [Work.HP.rk, hbasis]
  exact hle



/-- **The requested statement.**  For a rank-`3` lattice `L ⊆ ℤ^5`, vectors `x y ∈ L` and a
radius `J` with `λ_{56}(Γ_{x,y}) ≤ J`, there is a non-zero form `a ∈ Γ_{x,y}` of norm at most
`J` which does not vanish identically on `L`. -/
theorem witness_outside (L : Submodule ℤ (Fin 5 → ℤ)) (hL : Work.HP.rk L = 3)
    (x y : Fin 5 → ℤ) (hx : x ∈ L) (hy : y ∈ L) (J : ℝ)
    (hJ : Work.HP.lam (Work.HP.Gam 4 4 x y) 56 ≤ J) :
    ∃ a : Work.HP.Mon 4 4 → ℤ, a ∈ Work.HP.Gam 4 4 x y ∧ a ≠ 0 ∧ Work.HP.eNorm a ≤ J ∧
      a ∉ Work.HP.vanishOn L := by
  have hrank : 56 ≤ Work.HP.rk (Work.HP.Gam 4 4 x y) := gam_rank x y
  obtain ⟨f, hfL, hfI, hfb⟩ := lamAttained_aux (Work.HP.Gam 4 4 x y) (i := 56) hrank
  have hbJ : ∀ j : Fin 56, Work.HP.eNorm (f j) ≤ J := fun j => (hfb j).trans hJ
  by_contra hcon
  push Not at hcon
  have h56 : (56 : ℕ) ≤ Work.HP.rk (Work.HP.vanishOn L) := by
    have hmem : ∀ i, f i ∈ Work.HP.vanishOn L :=
      fun i => hcon (f i) (hfL i) (hfI.ne_zero i) (hbJ i)
    let g : Fin 56 → (Work.HP.vanishOn L) := fun i => ⟨f i, hmem i⟩
    have hcomp : ((Work.HP.vanishOn L).subtype : (Work.HP.vanishOn L) → (Mon 4 4 → ℤ)) ∘ g = f := by
      funext i; rfl
    have hg : LinearIndependent ℤ g := by
      apply LinearIndependent.of_comp ((Work.HP.vanishOn L).subtype)
      rw [hcomp]; exact hfI
    exact LinearIndependent.fintype_card_le_finrank hg
  have h55 := vanish_rank_aux L hL
  omega

end Work.HP.Q44Child
