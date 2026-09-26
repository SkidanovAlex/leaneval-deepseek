import Mathlib
import Submission.Work.PinchLemma3.ClosedDiscA.potential_helpers

/-!
# A closed curve in the union of two inessential regions meeting in two pieces

`winding_psi_eq_zero_of_two_component_inter`: if `A`, `B` are carrier-open path connected
regions of a parametrised torus with vanishing winding span, and `A ∩ B = K₁ ∪ K₂` with `K₁`,
`K₂` path connected and disjoint, then every closed curve `γ` of the torus whose image lies in
`A ∪ B` has its winding killed by any linear functional `ψ` which kills the winding of a fixed
"test loop" running from `K₁` to `K₂` through `A` and back through `B`.

This is the curve-level form (Mayer-Vietoris) of the fact that the image of `H₁(A ∪ B)` in
`H₁(T²)` is spanned by (the image of) a single class: `H₁(A)` and `H₁(B)` die, and the two
components of the intersection `A ∩ B` contribute exactly one extra generator.

The proof uses the developing potential of `A` and of `B`: since both regions are inessential the
`ψ`-image of the displacement of a path inside them depends only on the endpoints
(`potential_helpers`), and the two potentials agree on the two "gates" `K₁`, `K₂` — on `K₁`
because a path inside `K₁` is a path in both `A` and `B`, on `K₂` because the discrepancy is
exactly the `ψ`-image of the winding of a loop passing through `K₁` and `K₂`, which `ψ` kills.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped unitInterval

namespace Work.PinchLemma3.ClosedDiscA

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

theorem winding_psi_eq_zero_of_two_component_inter
    {A B : Set R3} (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier)
    (hAop : Work.SurgeryInvariance.IsOpenInCarrier P A)
    (hBop : Work.SurgeryInvariance.IsOpenInCarrier P B)
    (hApc : IsPathConnected A) (hBpc : IsPathConnected B)
    (hVA : Work.SurgeryInvariance.WindingSpan P A = ⊥)
    (hVB : Work.SurgeryInvariance.WindingSpan P B = ⊥)
    {K₁ K₂ : Set R3} (hK₁c : K₁ ⊆ P.carrier) (hK₂c : K₂ ⊆ P.carrier)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂)
    (hinter : A ∩ B = K₁ ∪ K₂)
    {a b : P.carrier} (ha : (a : R3) ∈ K₁) (hb : (b : R3) ∈ K₂)
    (cA : Path a b) (hcA : ∀ t : unitInterval, ((cA t) : R3) ∈ A)
    (cB : Path a b) (hcB : ∀ t : unitInterval, ((cB t) : R3) ∈ B)
    {W : Type*} [AddCommGroup W] [Module ℝ W] (ψ : (ℝ × ℝ) →ₗ[ℝ] W)
    (hψw : psiDisp ψ (cA.trans cB.symm) = 0)
    (γ : Work.CoreTopology.ClosedCurve P) (hγ : ∀ t : ℝ, γ t ∈ A ∪ B) :
    ψ (((Work.SurgeryInvariance.windingOf P γ).1 : ℝ),
       ((Work.SurgeryInvariance.windingOf P γ).2 : ℝ)) = 0 := by
  have haAB : (a : R3) ∈ A ∩ B := hinter.symm ▸ Set.mem_union_left K₂ ha
  have hK₁A : K₁ ⊆ A := fun x hx => (hinter.symm ▸ Set.mem_union_left K₂ hx).1
  have hK₁B : K₁ ⊆ B := fun x hx => (hinter.symm ▸ Set.mem_union_left K₂ hx).2
  have hK₂A : K₂ ⊆ A := fun x hx => (hinter.symm ▸ Set.mem_union_right K₁ hx).1
  have hK₂B : K₂ ⊆ B := fun x hx => (hinter.symm ▸ Set.mem_union_right K₁ hx).2
  -- the two potentials agree on the first gate
  have hFAeqK1 : ∀ (x : P.carrier) (hx : (x : R3) ∈ K₁),
      potential hAc hApc a haAB.1 ψ ⟨x, hK₁A hx⟩
        = potential hBc hBpc a haAB.2 ψ ⟨x, hK₁B hx⟩ := by
    intro x hx
    have hκ := potentialPath_mem (P := P) hK₁c hK₁pc a ha x hx
    rw [potential_eq_of_path hAc hApc hVA a haAB.1 ψ (hK₁A hx)
          (potentialPath hK₁c hK₁pc a ha x hx) (fun t => hK₁A (hκ t)),
        potential_eq_of_path hBc hBpc hVB a haAB.2 ψ (hK₁B hx)
          (potentialPath hK₁c hK₁pc a ha x hx) (fun t => hK₁B (hκ t))]
  -- the two potentials agree on the second gate, using the test loop
  have hFAeqK2 : ∀ (x : P.carrier) (hx : (x : R3) ∈ K₂),
      potential hAc hApc a haAB.1 ψ ⟨x, hK₂A hx⟩
        = potential hBc hBpc a haAB.2 ψ ⟨x, hK₂B hx⟩ := by
    intro x hx
    have hκ := potentialPath_mem (P := P) hK₂c hK₂pc b hb x hx
    have eA := potential_spec (x := b) (y := x) hAc hApc hVA a haAB.1 ψ (hK₂A hb) (hK₂A hx)
      (potentialPath hK₂c hK₂pc b hb x hx) (fun t => hK₂A (hκ t))
    have eB := potential_spec (x := b) (y := x) hBc hBpc hVB a haAB.2 ψ (hK₂B hb) (hK₂B hx)
      (potentialPath hK₂c hK₂pc b hb x hx) (fun t => hK₂B (hκ t))
    rw [potential_eq_of_path hAc hApc hVA a haAB.1 ψ (hK₂A hb) cA hcA] at eA
    rw [potential_eq_of_path hBc hBpc hVB a haAB.2 ψ (hK₂B hb) cB hcB] at eB
    have eA' : potential hAc hApc a haAB.1 ψ ⟨x, hK₂A hx⟩
        = psiDisp ψ (potentialPath hK₂c hK₂pc b hb x hx) + psiDisp ψ cA := by
      rw [eA]; abel
    have eB' : potential hBc hBpc a haAB.2 ψ ⟨x, hK₂B hx⟩
        = psiDisp ψ (potentialPath hK₂c hK₂pc b hb x hx) + psiDisp ψ cB := by
      rw [eB]; abel
    have hcd : psiDisp ψ cA = psiDisp ψ cB := by
      have h := hψw
      rw [psiDisp_trans, psiDisp_symm] at h
      exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)
    rw [eA', eB', hcd]
  -- the combined statement on the whole intersection
  have hFAeqFB : ∀ (x : P.carrier) (hx : (x : R3) ∈ A ∩ B),
      potential hAc hApc a haAB.1 ψ ⟨x, hx.1⟩ = potential hBc hBpc a haAB.2 ψ ⟨x, hx.2⟩ := by
    intro x hx
    have hxu : (x : R3) ∈ K₁ ∪ K₂ := hinter ▸ hx
    rcases hxu with hxK1 | hxK2
    · rw [potential_congr hAc hApc a haAB.1 ψ hx.1 (hK₁A hxK1),
          potential_congr hBc hBpc a haAB.2 ψ hx.2 (hK₁B hxK1)]
      exact hFAeqK1 x hxK1
    · rw [potential_congr hAc hApc a haAB.1 ψ hx.1 (hK₂A hxK2),
          potential_congr hBc hBpc a haAB.2 ψ hx.2 (hK₂B hxK2)]
      exact hFAeqK2 x hxK2
  rcases exists_alternating_partition hAop hBop γ hγ with hγA | hγB | ⟨k, hk, s, hs0, hslast, hmono, hArcA, hArcB⟩
  · have hmem : (((Work.SurgeryInvariance.windingOf P γ).1 : ℚ),
        ((Work.SurgeryInvariance.windingOf P γ).2 : ℚ)) ∈ Work.SurgeryInvariance.WindingSpan P A :=
      Submodule.subset_span ⟨γ, hγA, rfl⟩
    rw [hVA, Submodule.mem_bot] at hmem
    have hv : (((Work.SurgeryInvariance.windingOf P γ).1 : ℝ),
        ((Work.SurgeryInvariance.windingOf P γ).2 : ℝ)) = 0 := by
      rw [Work.SurgeryInvariance.intPair_cast_eq_zero_iff] at hmem
      rw [hmem]; simp
    rw [hv]
    exact map_zero ψ
  · have hmem : (((Work.SurgeryInvariance.windingOf P γ).1 : ℚ),
        ((Work.SurgeryInvariance.windingOf P γ).2 : ℚ)) ∈ Work.SurgeryInvariance.WindingSpan P B :=
      Submodule.subset_span ⟨γ, hγB, rfl⟩
    rw [hVB, Submodule.mem_bot] at hmem
    have hv : (((Work.SurgeryInvariance.windingOf P γ).1 : ℝ),
        ((Work.SurgeryInvariance.windingOf P γ).2 : ℝ)) = 0 := by
      rw [Work.SurgeryInvariance.intPair_cast_eq_zero_iff] at hmem
      rw [hmem]; simp
    rw [hv]
    exact map_zero ψ
  · -- the alternating partition
    obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ
    set Lam : ℝ → ℝ × ℝ := fun t => (L.Θ t, L.Φ t) with hLamdef
    have hLamc : Continuous Lam := L.contΘ.prodMk L.contΦ
    have hLammem : ∀ t : ℝ, Work.TorusCover.psiMap P.psi (Lam t) = γ t := by
      intro t; simp only [hLamdef, Work.TorusCover.psiMap]; exact L.lifts t
    set pt : ℕ → P.carrier := fun i => ⟨γ (s i), γ.mem (s i)⟩ with hptdef
    have hs01 : s 0 ≤ s 1 := le_of_lt (hmono 0 1 (by omega) (by omega) (by omega))
    have hpt2k : pt (2 * k) = pt 0 := by
      refine Subtype.ext ?_
      show γ (s (2 * k)) = γ (s 0)
      rw [hslast]
      exact γ.periodic (s 0)
    have hA_even : ∀ j : ℕ, j ≤ k → γ (s (2 * j)) ∈ A := by
      intro j hj
      rcases lt_or_eq_of_le hj with hj' | hj'
      · exact hArcA j hj' (s (2 * j)) (le_refl _)
          (le_of_lt (hmono (2 * j) (2 * j + 1) (by omega) (by omega) (by omega)))
      · rw [hj', hslast, γ.periodic (s 0)]
        exact hArcA 0 hk (s 0) (le_refl _) hs01
    have hB_even : ∀ j : ℕ, j ≤ k → γ (s (2 * j)) ∈ B := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with hj' | hj'
      · rw [hj', ← γ.periodic (s 0), ← hslast]
        exact hArcB (k - 1) (by omega) (s (2 * k))
          (le_of_lt (hmono (2 * (k - 1) + 1) (2 * k) (by omega) (by omega) (by omega)))
          (le_of_eq (by congr 1; omega))
      · exact hArcB (j - 1) (by omega) (s (2 * j))
          (le_of_lt (hmono (2 * (j - 1) + 1) (2 * j) (by omega) (by omega) (by omega)))
          (le_of_eq (by congr 1; omega))
    have hA_odd : ∀ j : ℕ, j < k → γ (s (2 * j + 1)) ∈ A := fun j hj =>
      hArcA j hj (s (2 * j + 1))
        (le_of_lt (hmono (2 * j) (2 * j + 1) (by omega) (by omega) (by omega))) (le_refl _)
    have hB_odd : ∀ j : ℕ, j < k → γ (s (2 * j + 1)) ∈ B := fun j hj =>
      hArcB j hj (s (2 * j + 1)) (le_refl _)
        (le_of_lt (hmono (2 * j + 1) (2 * j + 2) (by omega) (by omega) (by omega)))
    have hAbd : ∀ i : ℕ, i ≤ 2 * k → (pt i : R3) ∈ A := by
      intro i hi
      rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
      · subst hj
        rw [show j + j = 2 * j from by omega]
        exact hA_even j (by omega)
      · subst hj
        exact hA_odd j (by omega)
    have hBbd : ∀ i : ℕ, i ≤ 2 * k → (pt i : R3) ∈ B := by
      intro i hi
      rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
      · subst hj
        rw [show j + j = 2 * j from by omega]
        exact hB_even j (by omega)
      · subst hj
        exact hB_odd j (by omega)
    have hABbd : ∀ i : ℕ, i ≤ 2 * k → (pt i : R3) ∈ A ∩ B :=
      fun i hi => ⟨hAbd i hi, hBbd i hi⟩
    -- the potential as a function of the index
    let g : ℕ → W := fun i => if h : i ≤ 2 * k then
      potential hAc hApc a haAB.1 ψ ⟨pt i, hAbd i h⟩ else 0
    have hg : ∀ i (h : i ≤ 2 * k), g i = potential hAc hApc a haAB.1 ψ ⟨pt i, hAbd i h⟩ := by
      intro i h; simp only [g]; rw [dif_pos h]
    -- passing from the `B`-potential back to the `A`-potential on the intersection
    have hFBFA : ∀ (x : P.carrier) (hxA : (x : R3) ∈ A) (hxB : (x : R3) ∈ B),
        potential hBc hBpc a haAB.2 ψ ⟨x, hxB⟩ = potential hAc hApc a haAB.1 ψ ⟨x, hxA⟩ := by
      intro x hxA hxB
      have hxAB : (x : R3) ∈ A ∩ B := ⟨hxA, hxB⟩
      rw [potential_congr hBc hBpc a haAB.2 ψ hxB hxAB.2,
          potential_congr hAc hApc a haAB.1 ψ hxA hxAB.1]
      exact (hFAeqFB x hxAB).symm
    -- the step identity
    have hstep : ∀ i : ℕ, i < 2 * k → ψ (Lam (s (i + 1))) - ψ (Lam (s i)) = g (i + 1) - g i := by
      intro i hi
      rw [← psiDisp_subArc ψ γ (s i) (s (i + 1)) Lam hLamc hLammem]
      rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
      · have hje : i = 2 * j := by omega
        have hjk : j < k := by omega
        rw [hje]
        rw [hg (2 * j + 1) (by omega), hg (2 * j) (by omega)]
        refine potential_spec hAc hApc hVA a haAB.1 ψ (hx := hAbd (2 * j) (by omega))
          (hy := hAbd (2 * j + 1) (by omega)) (subArc γ (s (2 * j)) (s (2 * j + 1))) ?_
        exact subArc_coe_mem γ (le_of_lt (hmono (2 * j) (2 * j + 1) (by omega) (by omega) (by omega)))
          (fun t ht1 ht2 => hArcA j hjk t ht1 ht2)
      · have hjo : i = 2 * j + 1 := by omega
        have hjk : j < k := by omega
        rw [hjo]
        have hstep1 : (2 * j + 1) + 1 = 2 * j + 2 := by omega
        rw [hstep1]
        rw [hg (2 * j + 2) (by omega), hg (2 * j + 1) (by omega)]
        rw [potential_spec (x := pt (2 * j + 1)) (y := pt (2 * j + 2)) hBc hBpc hVB a haAB.2 ψ
          (hx := hBbd (2 * j + 1) (by omega)) (hy := hBbd (2 * j + 2) (by omega))
          (subArc γ (s (2 * j + 1)) (s (2 * j + 2)))
          (subArc_coe_mem γ (le_of_lt (hmono (2 * j + 1) (2 * j + 2) (by omega) (by omega) (by omega)))
            (fun t ht1 ht2 => hArcB j hjk t ht1 ht2))]
        rw [hFBFA (pt (2 * j + 2)) (hAbd (2 * j + 2) (by omega)) (hBbd (2 * j + 2) (by omega)),
            hFBFA (pt (2 * j + 1)) (hAbd (2 * j + 1) (by omega)) (hBbd (2 * j + 1) (by omega))]
    have hsum_eq : (∑ i ∈ Finset.range (2 * k), (ψ (Lam (s (i + 1))) - ψ (Lam (s i))))
        = ∑ i ∈ Finset.range (2 * k), (g (i + 1) - g i) :=
      Finset.sum_congr rfl (fun i hi => hstep i (Finset.mem_range.mp hi))
    rw [Finset.sum_range_sub (fun i => ψ (Lam (s i))) (2 * k),
        Finset.sum_range_sub g (2 * k)] at hsum_eq
    have hg2k : g (2 * k) = g 0 := by
      rw [hg (2 * k) (by omega), hg 0 (by omega)]
      exact congrArg _ (Subtype.ext hpt2k)
    rw [hg2k, sub_self] at hsum_eq
    have hzero : ψ (Work.TorusCover.periodShift (Work.SurgeryInvariance.windingOf P γ)) = 0 := by
      have hh := hsum_eq
      have hper : Lam (s (2 * k)) = Lam (s 0)
          + Work.TorusCover.periodShift (Work.SurgeryInvariance.windingOf P γ) := by
        have h := L.period_shift_winding (s 0)
        have hw := Work.SurgeryInvariance.windingOf_eq P γ L
        rw [hslast, hw]
        ext <;> simp [hLamdef, Work.TorusCover.periodShift, h.1, h.2]
      rw [hper, map_add, add_sub_cancel_left] at hh
      exact hh
    rw [show Work.TorusCover.periodShift (Work.SurgeryInvariance.windingOf P γ)
        = (2 * Real.pi) • ((((Work.SurgeryInvariance.windingOf P γ).1 : ℝ),
            ((Work.SurgeryInvariance.windingOf P γ).2 : ℝ)) : ℝ × ℝ) from by
          ext <;> simp [Work.TorusCover.periodShift, smul_eq_mul, mul_comm],
      map_smul] at hzero
    exact (smul_eq_zero.mp hzero).resolve_left (by positivity)

end

end Work.PinchLemma3.ClosedDiscA
