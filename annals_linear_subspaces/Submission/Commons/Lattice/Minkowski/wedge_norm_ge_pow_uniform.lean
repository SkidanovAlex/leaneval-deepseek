import Mathlib
import Submission.Commons.Lattice.Minkowski.minkowski_second_upper
import Submission.Commons.Lattice.Minkowski.wedge_norm_ge_prod_successiveMinimum
import Submission.Commons.Lattice.Minkowski.covolume_span_basis_eq_wedge
import Submission.Commons.Lattice.SuccessiveMinima.linearIndependent_real_of_int
import Submission.Commons.Lattice.SuccessiveMinima.successiveMinimum_eq_of_carrier_eq
import Submission.Commons.Lattice.SuccessiveMinima.sublattice_ge
import Submission.Commons.Analysis.InnerProductSpace.unitBall_volume_eq_dim

noncomputable section

open MeasureTheory Metric Module
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Commons.Lattice.Minkowski

/-- An independent family of `finrank`-many vectors spans the whole space. -/
private lemma span_top_of_li_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℕ} (v : Fin r → E) (hv : LinearIndependent ℝ v)
    (hfin : Module.finrank ℝ E = r) : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
  classical
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  have hfinS : Module.finrank ℝ S = r := by
    rw [finrank_span_eq_card (R := ℝ) (b := v) hv]
    simp
  have hq : Module.finrank ℝ (E ⧸ S) ≤ 0 := by
    have h := Module.finrank_quotient_add_finrank_le (R := ℝ) (M := E) (N := S)
    rw [hfinS, hfin] at h
    omega
  have hq0 : Module.finrank ℝ (E ⧸ S) = 0 := le_antisymm hq (Nat.zero_le _)
  have hsub : Subsingleton (E ⧸ S) := (Module.finrank_zero_iff (R := ℝ) (M := E ⧸ S)).mp hq0
  intro x _
  have hz : (S.mkQ x : E ⧸ S) = 0 := Subsingleton.elim _ _
  have hmem : x ∈ S := by
    have hz0 : (Submodule.Quotient.mk x : E ⧸ S) = 0 := by simpa [Submodule.mkQ_apply] using hz
    exact (Submodule.Quotient.mk_eq_zero (p := S)).1 hz0
  simpa [S] using hmem

/-- The `0`-fold wedge product has norm one. -/
private lemma norm_iMulti_zero {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (u : Fin 0 → F) : ‖exteriorPower.ιMulti ℝ 0 u‖ = 1 := by
  have hsq : ‖exteriorPower.ιMulti ℝ 0 u‖ ^ 2 = 1 := by
    calc
      ‖exteriorPower.ιMulti ℝ 0 u‖ ^ 2 =
          inner ℝ (exteriorPower.ιMulti ℝ 0 u) (exteriorPower.ιMulti ℝ 0 u) := by
        exact (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (exteriorPower.ιMulti ℝ 0 u)).symm
      _ = (Matrix.gram ℝ u).det := by rw [exteriorPower.inner_ιMulti_self]
      _ = (1 : Matrix (Fin 0) (Fin 0) ℝ).det := by
        congr 1
        exact Subsingleton.elim _ _
      _ = 1 := by simp
  have hnn : 0 ≤ ‖exteriorPower.ιMulti ℝ 0 u‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖exteriorPower.ιMulti ℝ 0 u‖)]

/-- The volume of the closed unit ball in a finite-dimensional real inner product space of
dimension `k` is `√π ^ k / Γ (k/2 + 1)`. -/
private lemma unitBall_volume_eq_sqrt_pi_pow {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    {k : ℕ} (hk : 0 < k) (hfin : Module.finrank ℝ F = k) :
    ENNReal.toReal (MeasureTheory.volume (Metric.closedBall (0 : F) 1)) =
      Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1) := by
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [Commons.Analysis.InnerProductSpace.unitBall_volume_eq_dim (E := F) hfin]
  rw [EuclideanSpace.volume_closedBall (x := (0 : EuclideanSpace ℝ (Fin k))) (r := 1)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [one_pow, Fintype.card_fin, one_mul]
  exact ENNReal.toReal_ofReal (le_of_lt (by
    have hG : 0 < Real.Gamma ((k : ℝ) / 2 + 1) := by
      apply Real.Gamma_pos_of_pos
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    positivity))

theorem wedge_norm_ge_pow_uniform {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {c : ℝ} (hc : 0 ≤ c)
    (h1 : c ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) L 1)
    (w : Fin k → L) (hw : LinearIndependent ℤ w) :
    (Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1) / (2 : ℝ) ^ (2 * k)) * c ^ k ≤
      ‖exteriorPower.ιMulti ℝ k (fun i => (w i : E))‖ := by
  classical
  set v : Fin k → E := fun i => (w i : E) with hv
  have hvli : LinearIndependent ℝ v :=
    Commons.Lattice.SuccessiveMinima.linearIndependent_real_of_int L w hw
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    rw [norm_iMulti_zero v]
    simp [Real.Gamma_one]
  · let V : Submodule ℝ E := Submodule.span ℝ (Set.range v)
    let vV : Fin k → V := fun i => ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
    have hvV : LinearIndependent ℝ vV := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hgE : (∑ i : Fin k, g i • v i) = 0 := by
        have hg' := congrArg (fun x : V => (x : E)) hg
        simpa [vV] using hg'
      exact (Fintype.linearIndependent_iff.mp hvli) g hgE
    have hfinV : Module.finrank ℝ V = k := by
      dsimp [V]
      rw [finrank_span_eq_card (R := ℝ) (b := v) hvli]
      simp
    have hspV : ⊤ ≤ Submodule.span ℝ (Set.range vV) := span_top_of_li_gen vV hvV hfinV
    let b : Module.Basis (Fin k) ℝ V := Module.Basis.mk hvV hspV
    have hbcoe : ∀ i, ((b i : V) : E) = v i := by
      intro i
      have h := congr_fun (Module.Basis.coe_mk hvV hspV) i
      exact congrArg (fun x : V => (x : E)) h
    let W : Submodule ℤ V := Submodule.span ℤ (Set.range b)
    haveI : DiscreteTopology W := by dsimp only [W]; infer_instance
    haveI : IsZLattice ℝ W := by dsimp only [W]; infer_instance
    haveI : Nontrivial V := by
      rw [← Module.finrank_pos_iff (R := ℝ) (M := V), hfinV]
      exact hk
    letI : MeasurableSpace V := borel V
    haveI : BorelSpace V := ⟨rfl⟩
    -- positivity of the lattice rank
    have hkL : k ≤ Module.finrank ℤ L := by
      haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
      simpa using hw.fintype_card_le_finrank (R := ℤ)
    -- Minkowski's second theorem (upper bound) for `W` inside `V`
    have hmin : (∏ i : Fin k,
          Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W (i.val + 1)) *
          ENNReal.toReal (volume (Metric.closedBall (0 : V) 1)) ≤
        (2 : ℝ) ^ (2 * k) * ZLattice.covolume W := by
      refine minkowski_second_upper (d := k) hk (E := V) (L := W) ?_
      rw [ZLattice.rank ℝ W]
      exact hfinV
    -- the covolume of `W` inside `V` is the ambient wedge norm of `w`
    have hcov : ZLattice.covolume W = ‖exteriorPower.ιMulti ℝ k v‖ := by
      have h := covolume_span_basis_eq_wedge (E := E) V b
      have hfam : (fun i => ((b i : V) : E)) = v := funext (fun i => hbcoe i)
      simpa [W, hfam] using h
    -- the lattice `W` inside `V` is the image of `span ℤ (range w)`
    let WE : Submodule ℤ E := Submodule.span ℤ (Set.range v)
    have hWE_le : WE ≤ L := by
      rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      exact (w i).2
    have hmap : WE = W.map (V.subtype.restrictScalars ℤ) := by
      dsimp only [WE, W]
      rw [Submodule.map_span]
      congr 1
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨b i, ⟨i, rfl⟩, by simpa using (hbcoe i)⟩
      · rintro ⟨y, ⟨i, rfl⟩, hxy⟩
        exact ⟨i, (hbcoe i).symm.trans hxy⟩
    -- `λᵢ(L) ≤ λᵢ(W_V)` for `i ≤ k`
    have hlam : ∀ j : Fin k,
        Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) L (j.val + 1) ≤
        Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W (j.val + 1) := by
      intro j
      have hjk : j.val + 1 ≤ k := by omega
      have hnonempty : (Commons.Lattice.SuccessiveMinima.successiveMinimumSet WE
          (j.val + 1)).Nonempty := by
        have hvint : LinearIndependent ℤ v :=
          hw.map' (L.subtype) (LinearMap.ker_eq_bot.mpr (fun x y hxy => L.injective_subtype hxy))
        refine Commons.Lattice.SuccessiveMinima.successiveMinimumSet_nonempty_of_exists_linearIndependent
          WE (j.val + 1) (fun a => ⟨v (Fin.castLEEmb hjk a),
            Submodule.subset_span (Set.mem_range_self _)⟩)
          (hvint.comp (Fin.castLEEmb hjk) (Fin.castLEEmb hjk).injective)
          (∑ a : Fin (j.val + 1), ‖v (Fin.castLEEmb hjk a)‖) ?_ ?_
        · intro a
          exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin (j.val + 1))))
            (f := fun b : Fin (j.val + 1) => ‖v (Fin.castLEEmb hjk b)‖)
            (fun b _ => norm_nonneg _) (Finset.mem_univ a)
        · exact Finset.sum_nonneg (fun b (_ : b ∈ (Finset.univ : Finset (Fin (j.val + 1)))) =>
            norm_nonneg _)
      have h1' : Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) L (j.val + 1) ≤
          Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) WE (j.val + 1) :=
        Commons.Lattice.SuccessiveMinima.sublattice_ge WE L hWE_le (j.val + 1) hnonempty
      have h2' : Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) WE (j.val + 1) =
          Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W (j.val + 1) :=
        (Commons.Lattice.SuccessiveMinima.successiveMinimum_eq_of_carrier_eq W WE hmap
          (j.val + 1)).symm
      linarith
    -- lower bound for the product of successive minima of `W` in terms of `c`
    have hprod_c : c ^ k ≤ ∏ i : Fin k,
        Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W (i.val + 1) := by
      have hconst : c ^ k = ∏ _i : Fin k, c := by
        rw [Finset.prod_const]
        simp
      rw [hconst]
      refine Finset.prod_le_prod (fun i _ => hc) (fun i _ => ?_)
      have hm : 1 ≤ i.val + 1 := by omega
      have hmfin : i.val + 1 ≤ Module.finrank ℤ L := by have := i.isLt; omega
      have hmono := Commons.Lattice.SuccessiveMinima.successiveMinimum_mono L hm hmfin
      exact le_trans (le_trans h1 hmono) (hlam i)
    -- the exact value of the unit ball volume in `V`
    have hvol : ENNReal.toReal (volume (Metric.closedBall (0 : V) 1)) =
        Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1) :=
      unitBall_volume_eq_sqrt_pi_pow (F := V) hk hfinV
    have hγpos : 0 < Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1) := by
      have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
      have hG : 0 < Real.Gamma ((k : ℝ) / 2 + 1) := by
        apply Real.Gamma_pos_of_pos
        positivity
      exact div_pos (pow_pos hsqrt k) hG
    have h2k : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
    rw [hcov] at hmin
    have step1 : (Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1)) * c ^ k ≤
        (∏ i : Fin k, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W
          (i.val + 1)) * ENNReal.toReal (volume (Metric.closedBall (0 : V) 1)) := by
      rw [hvol]
      calc (Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1)) * c ^ k
          ≤ (Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1)) *
            (∏ i : Fin k, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W
              (i.val + 1)) := mul_le_mul_of_nonneg_left hprod_c (le_of_lt hγpos)
        _ = (∏ i : Fin k, Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W
              (i.val + 1)) * (Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1)) :=
            mul_comm _ _
    have step2 : (Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1)) * c ^ k ≤
        (2 : ℝ) ^ (2 * k) * ‖exteriorPower.ιMulti ℝ k v‖ := le_trans step1 hmin
    rw [div_mul_eq_mul_div, div_le_iff₀ h2k]
    calc (Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1)) * c ^ k
        ≤ (2 : ℝ) ^ (2 * k) * ‖exteriorPower.ιMulti ℝ k v‖ := step2
      _ = ‖exteriorPower.ιMulti ℝ k v‖ * (2 : ℝ) ^ (2 * k) := mul_comm _ _

end Commons.Lattice.Minkowski
