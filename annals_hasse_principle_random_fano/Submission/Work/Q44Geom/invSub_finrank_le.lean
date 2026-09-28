import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.ReducDefs

/-!
# The invariance subspace of an irreducible quartic form in 5 variables has dimension `≤ 3`

`invSub f` is the space of directions `w` with `f(x + t w) = f(x)` for all `x, t`.  For a nonzero
irreducible degree-`4` form `f = formOf 4 4 c` we show `finrank ℚ (invSub f) ≤ 3`.

The proof linearises the defining property: if `w ∈ invSub f` then the directional derivative
`Σ i, w i • ∂ᵢ f` vanishes (this is the coefficient of `t` in `f(x + t w)`), hence
`invSub f ≤ ker Φ` for `Φ w = Σ i, w i • ∂ᵢ f`.  Rank–nullity then forces `dim (invSub f) ≤ 3`
unless the partial derivatives span a space of dimension `≤ 1`.  In that case Euler's identity
`Σ i, X i • ∂ᵢ f = 4 f` factors `f` as a product of two non-units, contradicting irreducibility.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MvPolynomial

namespace Work.Q44Geom

/-! ## The directional derivative linear map -/

/-- `Φ f w = Σ i, w i • ∂ᵢ f`, the directional derivative of `f` along `w`. -/
def formPhi (f : MvPolynomial (Fin 5) ℚ) : (Fin 5 → ℚ) →ₗ[ℚ] MvPolynomial (Fin 5) ℚ where
  toFun w := ∑ i, w i • MvPolynomial.pderiv i f
  map_add' u v := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    show (∑ i : Fin 5, (a • v) i • MvPolynomial.pderiv i f)
        = a • (∑ i : Fin 5, v i • MvPolynomial.pderiv i f)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.smul_apply]
    show (a * v i) • MvPolynomial.pderiv i f = a • (v i • MvPolynomial.pderiv i f)
    rw [smul_smul]

@[simp] lemma formPhi_apply (f : MvPolynomial (Fin 5) ℚ) (w : Fin 5 → ℚ) :
    formPhi f w = ∑ i, w i • MvPolynomial.pderiv i f := rfl

/-! ## The chain rule for `aeval` and a derivation -/

/-- Chain rule: for a derivation `d` on a commutative `ℚ`-algebra `R`, a point `g` and a
polynomial `p`, the derivative of `aeval g p` is `Σ i, (aeval g (∂ᵢ p)) * (d (g i))`. -/
theorem aeval_pderiv_chain_rule {R : Type*} [CommRing R] [Algebra ℚ R]
    (d : Derivation ℚ R R) (g : Fin 5 → R) (p : MvPolynomial (Fin 5) ℚ) :
    d (MvPolynomial.aeval g p)
      = ∑ i, MvPolynomial.aeval g (MvPolynomial.pderiv i p) * d (g i) := by
  refine MvPolynomial.induction_on (motive := fun x =>
    d (MvPolynomial.aeval g x)
      = ∑ i, MvPolynomial.aeval g (MvPolynomial.pderiv i x) * d (g i)) p ?_ ?_ ?_
  · intro a
    rw [MvPolynomial.aeval_C]
    have h0 : d (algebraMap ℚ R a) = 0 := d.map_algebraMap a
    rw [h0]
    simp
  · intro p q hp hq
    have key : (∑ i : Fin 5, MvPolynomial.aeval g (MvPolynomial.pderiv i (p + q)) * d (g i))
        = (∑ i : Fin 5, MvPolynomial.aeval g (MvPolynomial.pderiv i p) * d (g i))
          + ∑ i : Fin 5, MvPolynomial.aeval g (MvPolynomial.pderiv i q) * d (g i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [map_add, add_mul]
    rw [key, ← hp, ← hq]
    simp only [map_add]
  · intro p n hp
    have key : (∑ i : Fin 5,
        MvPolynomial.aeval g (MvPolynomial.pderiv i (MvPolynomial.X n : MvPolynomial (Fin 5) ℚ)) * d (g i))
        = d (g n) := by
      rw [Finset.sum_eq_single n]
      · rw [MvPolynomial.pderiv_X_self, map_one, one_mul]
      · intro i _ hi
        rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hi), map_zero, zero_mul]
      · intro hn; exact absurd (Finset.mem_univ n) hn
    rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, hp, smul_eq_mul]
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.aeval_X]
    rw [show (∑ i : Fin 5, (MvPolynomial.aeval g (MvPolynomial.pderiv i p) * g n
              + MvPolynomial.aeval g p * MvPolynomial.aeval g (MvPolynomial.pderiv i (MvPolynomial.X n : MvPolynomial (Fin 5) ℚ)))
              * d (g i))
          = (∑ i : Fin 5, MvPolynomial.aeval g (MvPolynomial.pderiv i p) * d (g i)) * g n
            + MvPolynomial.aeval g p
              * (∑ i : Fin 5,
                  MvPolynomial.aeval g (MvPolynomial.pderiv i (MvPolynomial.X n : MvPolynomial (Fin 5) ℚ)) * d (g i))
        from by
          rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)]
    rw [key, ← hp]
    ring

/-! ## Linearisation of the invariance property -/

/-- If `w` is an invariance direction of `f`, the directional derivative of `f` along `w`
vanishes. -/
theorem sum_smul_pderiv_eq_zero_of_mem_invSub (f : MvPolynomial (Fin 5) ℚ) (w : Fin 5 → ℚ)
    (hw : w ∈ invSub f) : (∑ i, w i • pderiv i f) = 0 := by
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  let psi : Fin 5 → MvPolynomial (Fin 1) ℚ := fun i => C (x i) + C (w i) * X 0
  have hpsi : ∀ i, psi i = C (x i) + C (w i) * X 0 := fun i => rfl
  have hq_eq : MvPolynomial.aeval psi f = C (MvPolynomial.eval x f) := by
    apply MvPolynomial.funext
    intro t
    rw [MvPolynomial.map_aeval]
    have h1 : (MvPolynomial.eval t).comp (algebraMap ℚ (MvPolynomial (Fin 1) ℚ))
        = RingHom.id ℚ := by
      ext a; simp
    have h2 : (fun i => MvPolynomial.eval t (psi i)) = fun i => (x + (t 0) • w) i := by
      funext i
      rw [hpsi i]
      simp only [Pi.add_apply, Pi.smul_apply, map_add, map_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_X]
      ring
    rw [h1, h2, MvPolynomial.eval_C]
    exact hw x (t 0)
  have hchain := aeval_pderiv_chain_rule (MvPolynomial.pderiv (0 : Fin 1)) psi f
  rw [hq_eq, MvPolynomial.pderiv_C] at hchain
  have hpsi_pd : ∀ i : Fin 5, MvPolynomial.pderiv (0 : Fin 1) (psi i) = C (w i) := by
    intro i
    rw [hpsi i]
    simp
  simp only [hpsi_pd] at hchain
  have hcc : ∀ h : MvPolynomial (Fin 5) ℚ,
      MvPolynomial.eval (0 : Fin 1 → ℚ) (MvPolynomial.aeval psi h) = MvPolynomial.eval x h := by
    intro h
    rw [MvPolynomial.map_aeval]
    have h1 : (MvPolynomial.eval (0 : Fin 1 → ℚ)).comp (algebraMap ℚ (MvPolynomial (Fin 1) ℚ))
        = RingHom.id ℚ := by ext a; simp
    have h2 : (fun i => MvPolynomial.eval (0 : Fin 1 → ℚ) (psi i)) = x := by
      funext i; rw [hpsi i]; simp
    rw [h1, h2]
    rfl
  have hfin := congrArg (MvPolynomial.eval (0 : Fin 1 → ℚ)) hchain
  simp only [map_zero, map_sum, map_mul, MvPolynomial.eval_C, hcc] at hfin
  rw [map_sum]
  rw [show (∑ i, MvPolynomial.eval x (w i • MvPolynomial.pderiv i f))
      = ∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i f) * w i from
    Finset.sum_congr rfl (fun i _ => by
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
      ring)]
  exact hfin.symm

/-! ## Reducibility from degenerate partial derivatives -/

/-- A nonzero homogeneous polynomial of positive degree is not a unit. -/
theorem not_isUnit_of_isHomogeneous {n : ℕ} (hn : n ≠ 0) {g : MvPolynomial (Fin 5) ℚ}
    (hg : g.IsHomogeneous n) : ¬ IsUnit g := by
  intro hu
  have h1 : MvPolynomial.constantCoeff g = g.coeff 0 := MvPolynomial.constantCoeff_eq g
  have h2 : g.coeff 0 = 0 := by
    have hd : (0 : Fin 5 →₀ ℕ).degree ≠ n := by
      rw [show (0 : Fin 5 →₀ ℕ).degree = 0 from map_zero Finsupp.degree]
      exact fun h => hn h.symm
    exact hg.coeff_eq_zero hd
  have h3 : MvPolynomial.constantCoeff g ≠ 0 := (hu.map MvPolynomial.constantCoeff).ne_zero
  exact h3 (by rw [h1, h2])

/-- If the partial derivatives of a nonzero homogeneous degree-`4` form `f` span a space of
dimension `≤ 1`, then `f` is reducible. -/
theorem not_irreducible_of_pderiv_span_finrank_le_one (f : MvPolynomial (Fin 5) ℚ)
    (hf4 : f.IsHomogeneous 4) (hf : f ≠ 0)
    (h : Module.finrank ℚ (Submodule.span ℚ (Set.range fun i : Fin 5 => MvPolynomial.pderiv i f))
      ≤ 1) : ¬ Irreducible f := by
  let V' : Submodule ℚ (MvPolynomial (Fin 5) ℚ) :=
    Submodule.span ℚ (Set.range fun i : Fin 5 => MvPolynomial.pderiv i f)
  haveI hfin : FiniteDimensional ℚ ↥V' :=
    Module.Finite.span_of_finite ℚ (Set.finite_range (fun i : Fin 5 => MvPolynomial.pderiv i f))
  by_cases hbot : V' = ⊥
  · exfalso
    have hall : ∀ i : Fin 5, MvPolynomial.pderiv i f = 0 := by
      intro i
      have hi : MvPolynomial.pderiv i f ∈ V' := Submodule.subset_span (Set.mem_range_self i)
      rw [hbot] at hi; simpa using hi
    have heuler := hf4.sum_X_mul_pderiv
    rw [Finset.sum_eq_zero (fun i _ => by rw [hall i, mul_zero])] at heuler
    have h4 : (4 : ℚ) • f = 0 := (Nat.cast_smul_eq_nsmul ℚ 4 f).trans heuler.symm
    exact hf ((smul_eq_zero.mp h4).resolve_left (by norm_num))
  · intro hirr
    have hex : ∃ i : Fin 5, MvPolynomial.pderiv i f ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hbot (by
        show Submodule.span ℚ (Set.range fun i : Fin 5 => MvPolynomial.pderiv i f) = ⊥
        rw [Submodule.span_eq_bot]
        rintro _ ⟨i, rfl⟩
        exact hc i)
    obtain ⟨i₀, hi₀⟩ := hex
    have hV'_eq : V' = ℚ ∙ MvPolynomial.pderiv i₀ f := by
      have hle : ℚ ∙ MvPolynomial.pderiv i₀ f ≤ V' := by
        rw [Submodule.span_le]; rintro _ rfl; exact Submodule.subset_span (Set.mem_range_self i₀)
      have hfr : Module.finrank ℚ (ℚ ∙ MvPolynomial.pderiv i₀ f) = 1 :=
        finrank_span_singleton hi₀
      exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hfr]; exact h)).symm
    have hc : ∀ i : Fin 5, ∃ cc : ℚ, cc • MvPolynomial.pderiv i₀ f = MvPolynomial.pderiv i f := by
      intro i
      have hi : MvPolynomial.pderiv i f ∈ V' := Submodule.subset_span (Set.mem_range_self i)
      rw [hV'_eq] at hi
      exact Submodule.mem_span_singleton.mp hi
    choose c hc' using hc
    have hL : (∑ i : Fin 5, c i • X i) * MvPolynomial.pderiv i₀ f = 4 • f := by
      rw [← hf4.sum_X_mul_pderiv, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← hc' i, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
      ring
    have h4f : (4 : ℕ) • f = MvPolynomial.C ((4 : ℕ) : ℚ) * f :=
      (Nat.cast_smul_eq_nsmul ℚ 4 f).symm.trans (MvPolynomial.smul_eq_C_mul f ((4 : ℕ) : ℚ))
    have hf_eq : f = (MvPolynomial.C (1/4 : ℚ) * (∑ i : Fin 5, c i • X i))
        * MvPolynomial.pderiv i₀ f := by
      have h5 : MvPolynomial.C (1/4 : ℚ) * ((4 : ℕ) • f) = f := by
        rw [h4f, ← mul_assoc, ← MvPolynomial.C_mul,
          show (1/4 : ℚ) * ((4 : ℕ) : ℚ) = 1 by norm_num, MvPolynomial.C_1, one_mul]
      have h6 := congrArg (fun z => MvPolynomial.C (1/4 : ℚ) * z) hL
      rw [h5, ← mul_assoc] at h6
      exact h6.symm
    by_cases hL0 : (∑ i : Fin 5, c i • (MvPolynomial.X i : MvPolynomial (Fin 5) ℚ)) = 0
    · exfalso
      have hzero : f = 0 := by
        rw [hf_eq, hL0]; simp
      exact hf hzero
    · have hL_hom : (∑ i : Fin 5, c i • (MvPolynomial.X i : MvPolynomial (Fin 5) ℚ)).IsHomogeneous 1 := by
        apply MvPolynomial.IsHomogeneous.sum
        intro i _
        rw [MvPolynomial.smul_eq_C_mul]
        simpa using (MvPolynomial.isHomogeneous_C (Fin 5) (c i)).mul
          (MvPolynomial.isHomogeneous_X ℚ i)
      have hb_nonunit : ¬ IsUnit (MvPolynomial.C (1/4 : ℚ)
          * (∑ i : Fin 5, c i • (MvPolynomial.X i : MvPolynomial (Fin 5) ℚ))) :=
        not_isUnit_of_isHomogeneous (n := 1) (by norm_num)
          (by simpa using (MvPolynomial.isHomogeneous_C (Fin 5) (1/4 : ℚ)).mul hL_hom)
      have hp_nonunit : ¬ IsUnit (MvPolynomial.pderiv i₀ f) :=
        not_isUnit_of_isHomogeneous (n := 3) (by norm_num) (by simpa using hf4.pderiv (i := i₀))
      exact hb_nonunit ((hirr.isUnit_or_isUnit hf_eq).resolve_right hp_nonunit)

/-! ## The main theorem -/

theorem invSub_finrank_le (c : Work.HP.Mon 4 4 → ℤ) (hc : Work.HP.formOf 4 4 c ≠ 0)
    (hirr : Irreducible (Work.HP.formOf 4 4 c)) :
    Module.finrank ℚ (Work.Q44Geom.invSub (Work.Q44Geom.f44 c)) ≤ 3 := by
  show Module.finrank ℚ (invSub (Work.HP.formOf 4 4 c)) ≤ 3
  set f : MvPolynomial (Fin 5) ℚ := Work.HP.formOf 4 4 c with hf_def
  have hf_ne : f ≠ 0 := by rw [hf_def]; exact hc
  have hirr' : Irreducible f := hf_def.symm ▸ hirr
  have hf4 : f.IsHomogeneous 4 := by
    rw [hf_def, formOf_eq_polyOfR]
    exact isHomogeneous_polyOfR (fun m : Work.HP.Mon 4 4 => (c m : ℚ))
  have hker : invSub f ≤ (formPhi f).ker := by
    intro w hw
    rw [LinearMap.mem_ker, formPhi_apply]
    exact sum_smul_pderiv_eq_zero_of_mem_invSub f w hw
  have hspan_le : Submodule.span ℚ (Set.range fun i : Fin 5 => MvPolynomial.pderiv i f)
      ≤ (formPhi f).range := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    rw [formPhi_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, zero_smul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hrange_le : (formPhi f).range
      ≤ Submodule.span ℚ (Set.range fun i : Fin 5 => MvPolynomial.pderiv i f) := by
    intro y hy
    obtain ⟨w, rfl⟩ := hy
    rw [formPhi_apply]
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ (w i) (Submodule.subset_span (Set.mem_range_self i)))
  have hspan_eq : Submodule.span ℚ (Set.range fun i : Fin 5 => MvPolynomial.pderiv i f)
      = (formPhi f).range := le_antisymm hspan_le hrange_le
  have hrn := LinearMap.finrank_range_add_finrank_ker (formPhi f)
  rw [Module.finrank_fin_fun] at hrn
  by_contra hcon
  push_neg at hcon
  have hker_big : 4 ≤ Module.finrank ℚ ↥(formPhi f).ker :=
    le_trans hcon (Submodule.finrank_mono hker)
  have hrange_small : Module.finrank ℚ ↥(formPhi f).range ≤ 1 := by omega
  have hspan_small : Module.finrank ℚ
      (Submodule.span ℚ (Set.range fun i : Fin 5 => MvPolynomial.pderiv i f)) ≤ 1 := by
    rw [hspan_eq]; exact hrange_small
  exact (not_irreducible_of_pderiv_span_finrank_le_one f hf4 hf_ne hspan_small) hirr'

end Work.Q44Geom
