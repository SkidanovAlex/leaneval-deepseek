import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.lamR_witness
import Submission.Work.HP.Vero.lamR_dual_Gam_two
import Submission.Work.HP.Vero.lam_Gam_veronese_le
import Submission.Work.HP.Vero.lam_latOrth_veronese_le
import Submission.Work.HP.Vero.finrank_latOrth
import Submission.Work.HP.Vero.LamAux
import Submission.Work.HP.Vero.dualLat_nonempty
import Submission.Work.HP.HP3.dual_proj_int_vec
import Submission.Work.HP.HP3.dual_mem_dotR_eq_zero
import Submission.Work.HP.detgam_span_pair_wedgeNorm
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.Lat.exists_rk_two
import Submission.Work.HP.Lat.exists_rk_three
import Submission.Work.HP.Lat.card_Mon
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.Lat.detL_inf_latOrth
import Submission.Work.HP.Lat.transference_exact
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.Sig2.gam_rank_det
import Submission.Work.HP.Vero.gcdMinors2_veronese

/-!
# N04. Veronese lattices: key bounds for one and two vectors, and the determinant of `Γ_{x,y}`

Proved by assembling the following delegated/shared results:
* `Work.HP.Lat.transference_exact` : Banaszczyk transference (exact constant `R`);
* `Work.HP.Lat.detL_inf_latOrth`, `Work.HP.EE.gcdMinors_veronese` : the determinant of `Γ_{x,y}`;
* `Work.HP.Vero.lamR_dual_latOrth_ge`, `Work.HP.Vero.lamR_dual_Gam_two` : the first successive
  minimum of the two dual lattices;
* `Work.HP.Vero.lamR_witness` : extraction of integral witnesses from a successive minimum;
* `Work.HP.Vero.lam_latOrth_veronese_le`, `Work.HP.Vero.lam_Gam_veronese_le` : the `Θ`/`Ψ` lifts.
-/

set_option autoImplicit false

noncomputable section

open Filter

namespace Work.HP

/-! ## Small helpers -/

theorem ne_of_linInd {ι : Type*} [Fintype ι] (x y : ι → ℤ)
    (h : LinearIndependent ℤ ![x, y]) : x ≠ y := by
  intro hxy
  have h2 := (Fintype.linearIndependent_iff.mp h) ![1, -1]
  have hsum : (∑ i, (![1, -1] : Fin 2 → ℤ) i • (![x, y] i)) = 0 := by
    simp [Fin.sum_univ_two, hxy]
  have := h2 hsum 0
  simp at this

theorem ne_neg_of_linInd {ι : Type*} [Fintype ι] (x y : ι → ℤ)
    (h : LinearIndependent ℤ ![x, y]) : x ≠ -y := by
  intro hxy
  have h2 := (Fintype.linearIndependent_iff.mp h) ![1, 1]
  have hsum : (∑ i, (![1, 1] : Fin 2 → ℤ) i • (![x, y] i)) = 0 := by
    simp [Fin.sum_univ_two, hxy]
  have := h2 hsum 0
  simp at this

/-- The realification of an integral lattice has the same rank. -/
theorem finrank_realify {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℤ)) :
    Module.finrank ℤ (realify L) = Module.finrank ℤ L := by
  have hrange : LinearMap.range (intCastPi.comp (L.subtype)) = realify L := by
    ext x
    simp only [LinearMap.mem_range, realify, Submodule.mem_map]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
  rw [← hrange]
  exact LinearMap.finrank_range_of_inj (by
    intro a b hab
    apply Subtype.ext
    funext i
    have h := congrFun hab i
    simp only [LinearMap.coe_comp, Function.comp_apply, intCastPi_apply] at h
    exact_mod_cast h)

/-- Integer vectors belong to the standard lattice `ℤ^ι ⊆ ℝ^ι`. -/
theorem mem_span_basisFun_of_int {ι : Type*} [Fintype ι] (v : ι → ℤ) :
    (fun i => (v i : ℝ)) ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) := by
  classical
  have : (fun i => (v i : ℝ)) = ∑ i, v i • (Pi.basisFun ℝ ι i) := by
    ext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp [Pi.basisFun_apply, Pi.single_eq_same]
    · intro b _ hb
      simp only [Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_of_ne' hb, smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The realification of an integral lattice is discrete. -/
theorem discreteTopology_realify {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℤ)) :
    DiscreteTopology ↥(realify L) := by
  classical
  have hmem : ∀ x : ↥(realify L), (x : ι → ℝ) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) := by
    intro x
    obtain ⟨v, _, hvx⟩ := Submodule.mem_map.mp x.2
    rw [← hvx]
    exact mem_span_basisFun_of_int v
  refine DiscreteTopology.of_continuous_injective
    (f := fun x : ↥(realify L) =>
      (⟨(x : ι → ℝ), hmem x⟩ : ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))))) ?_ ?_
  · exact Continuous.subtype_mk continuous_subtype_val _
  · intro a b hab
    exact Subtype.ext (congrArg
      (fun z : ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) => (z : ι → ℝ)) hab)

/-- Every lattice of rank `k` contains `k` independent vectors. -/
theorem exists_indep_of_finrank {ι : Type*} [Fintype ι] (Λ : Submodule ℤ (ι → ℤ)) {k : ℕ}
    (h : Module.finrank ℤ Λ = k) :
    ∃ f : Fin k → (ι → ℤ), (∀ j, f j ∈ Λ) ∧ LinearIndependent ℤ f := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = Fintype.card (Fin k) := by
    rw [Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := Λ), h]
  let e : Module.Free.ChooseBasisIndex ℤ Λ ≃ Fin k := Fintype.equivOfCardEq hcard
  refine ⟨fun j => ((b.reindex e) j : ι → ℤ), fun j => ((b.reindex e) j).2, ?_⟩
  exact ((b.reindex e).linearIndependent).map' (Submodule.subtype Λ) (by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.coe_injective)

/-- The successive minima are nonnegative. -/
theorem lamR_nonneg {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ)) (i : ℕ) : 0 ≤ lamR L i := by
  rw [lamR]
  by_cases h : ({r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (ι → ℝ),
      (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r} : Set ℝ).Nonempty
  · exact le_csInf h (fun r hr => hr.1)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

/-- `max A⁻¹ B⁻¹ * min A B = 1` for positive `A, B`. -/
theorem max_inv_inv_mul_min {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    max A⁻¹ B⁻¹ * min A B = 1 := by
  rcases le_total A B with h | h
  · rw [min_eq_left h, max_eq_left]
    · exact inv_mul_cancel₀ (ne_of_gt hA)
    · rw [inv_le_inv₀ hB hA]; exact h
  · rw [min_eq_right h, max_eq_right]
    · exact inv_mul_cancel₀ (ne_of_gt hB)
    · rw [inv_le_inv₀ hA hB]; exact h

/-- Every determinant is at least one. -/
theorem one_le_dmin {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (S : Set (ι → ℤ))
    (h : ∃ L : Submodule ℤ (ι → ℤ), rk L = r ∧ S ⊆ L) : 1 ≤ dmin r S := by
  obtain ⟨L, hL1, hL2⟩ := h
  refine le_csInf ⟨detL L, L, hL1, hL2, rfl⟩ ?_
  rintro D ⟨L', h1, h2, rfl⟩
  exact Lat.detL_ge_one L'

end Work.HP

namespace Work.HP

variable {ι : Type*} [Fintype ι]

lemma rk_span_pair (x w : ι → ℤ) (h : LinearIndependent ℤ ![x, w]) :
    rk (Submodule.span ℤ ({x, w} : Set (ι → ℤ))) = 2 := by
  have hspan : Submodule.span ℤ ({x, w} : Set (ι → ℤ))
      = Submodule.span ℤ (Set.range ![x, w]) := by
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  rw [rk, hspan, finrank_span_eq_card h, Fintype.card_fin]

lemma dmin_le_detL {r : ℕ} {S : Set (ι → ℤ)} {L : Submodule ℤ (ι → ℤ)}
    (hr : rk L = r) (hS : S ⊆ L) : dmin r S ≤ detL L := by
  classical
  rw [dmin]
  refine csInf_le ?_ ⟨L, hr, hS, rfl⟩
  refine ⟨1, ?_⟩
  rintro D ⟨M, _, _, rfl⟩
  exact Lat.detL_ge_one M

/-- The shear identity: if `toR w = u - s • toR x` and `u ⊥ x`, then the covolume of `x, w` is
`‖x‖·‖u‖`. -/
lemma wedgeNorm_sub_smul (x w : ι → ℤ) (u : ι → ℝ) (s : ℝ)
    (hw : toR w = u - s • toR x) (horth : dotR u (toR x) = 0) :
    wedgeNorm x w = eNorm x * rNorm u := by
  have hx2 : (eNorm x) ^ 2 = ∑ i, ((x i : ℝ)) ^ 2 := by
    rw [eNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  have hu2 : (rNorm u) ^ 2 = ∑ i, (u i) ^ 2 := by
    rw [rNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  have hw2 : (eNorm w) ^ 2 = (rNorm u) ^ 2 + s ^ 2 * (eNorm x) ^ 2 := by
    have hcast : eNorm w = rNorm (toR w) := rfl
    rw [hcast, rNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), hu2, hx2, hw]
    simp only [Pi.sub_apply, Pi.smul_apply, toR, smul_eq_mul]
    have : ∀ i, (u i - s * (x i : ℝ)) ^ 2
        = (u i) ^ 2 - 2 * s * (u i * (x i : ℝ)) + s ^ 2 * ((x i : ℝ)) ^ 2 := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    have hsum : ∑ i, u i * (x i : ℝ) = 0 := by
      rw [← horth]; rfl
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
    ring
  have hcross : dotR (toR x) (toR w) = -s * (eNorm x) ^ 2 := by
    rw [hw]
    simp only [dotR, Pi.sub_apply, Pi.smul_apply, toR, smul_eq_mul]
    have : ∀ i, (x i : ℝ) * (u i - s * (x i : ℝ))
        = (x i : ℝ) * u i - s * ((x i : ℝ) * (x i : ℝ)) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hsum : ∑ i, (x i : ℝ) * u i = 0 := by
      rw [← horth]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [hsum, hx2]; ring
  rw [wedgeNorm, hw2, hcross]
  have : (eNorm x) ^ 2 * ((rNorm u) ^ 2 + s ^ 2 * (eNorm x) ^ 2) - (-s * (eNorm x) ^ 2) ^ 2
      = (eNorm x * rNorm u) ^ 2 := by ring
  have hsq : (0 : ℝ) ≤ eNorm x * rNorm u :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [this, Real.sqrt_sq hsq]

end Work.HP

namespace Work.HP

variable {ι : Type*} [Fintype ι]

-- helper: independence extraction (copied from veronese_key.lean for the scratch test)
theorem exists_indep_of_finrank_aux {ι : Type*} [Fintype ι] (Λ : Submodule ℤ (ι → ℤ)) {k : ℕ}
    (h : Module.finrank ℤ Λ = k) :
    ∃ f : Fin k → (ι → ℤ), (∀ j, f j ∈ Λ) ∧ LinearIndependent ℤ f := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = Fintype.card (Fin k) := by
    rw [Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := Λ), h]
  let e : Module.Free.ChooseBasisIndex ℤ Λ ≃ Fin k := Fintype.equivOfCardEq hcard
  refine ⟨fun j => ((b.reindex e) j : ι → ℤ), fun j => ((b.reindex e) j).2, ?_⟩
  exact ((b.reindex e).linearIndependent).map' (Submodule.subtype Λ) (by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.coe_injective)

lemma dotR_comm' (a b : ι → ℝ) : dotR a b = dotR b a := by
  simp only [dotR]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma dotR_add_right' (a b c : ι → ℝ) : dotR a (b + c) = dotR a b + dotR a c := by
  simp only [dotR, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dotR_smul_right' (t : ℝ) (a b : ι → ℝ) : dotR a (t • b) = t * dotR a b := by
  simp only [dotR, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma dotR_sub_right' (a b c : ι → ℝ) : dotR a (b - c) = dotR a b - dotR a c := by
  simp only [dotR, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem lamR_dual_latOrth_aux {n : ℕ} (hn : 1 ≤ n) (x : Fin (n + 1) → ℤ) (hx : IsPrim x) :
    dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) / eNorm x
      ≤ lamR (dualLat (realify (latOrth x))) 1 := by
  classical
  have hx0 : x ≠ 0 := isPrim_ne_zero hx
  have hxpos : 0 < eNorm x := eNorm_pos_of_ne_zero hx0
  refine Vero.le_lamR_one _ ?hne ?_
  · obtain ⟨f, hfL, hfI⟩ := exists_indep_of_finrank_aux (latOrth x) (k := n)
      (by rw [Vero.finrank_latOrth x hx0, Fintype.card_fin]; omega)
    have hfne : f ⟨0, by omega⟩ ≠ 0 := hfI.ne_zero ⟨0, by omega⟩
    refine ⟨intCastPi (f ⟨0, by omega⟩), Vero.realify_le_dualLat _
      (Submodule.mem_map_of_mem (hfL _)), ?_⟩
    intro hcon
    apply hfne
    funext i
    have := congrFun hcon i
    simpa [intCastPi] using this
  · intro v hv hv0
    rw [div_le_iff₀ hxpos]
    obtain ⟨w, s, hw⟩ := HP3.dual_proj_int_vec n x hx v hv
    have horth : dotR v (toR x) = 0 := HP3.dual_mem_dotR_eq_zero x v hv
    have hvd : ∀ i, (w i : ℝ) = v i - s * (x i : ℝ) := by
      intro i
      have h := congrFun hw i
      simpa [toR, Pi.sub_apply, Pi.smul_apply] using h
    have hxx : dotR (toR x) (toR x) = (eNorm x) ^ 2 := by
      have h1 : dotR (toR x) (toR x) = ∑ i, ((x i : ℝ)) ^ 2 := by
        simp only [dotR, toR, pow_two]
      rw [h1, eNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
    have hxne : dotR (toR x) (toR x) ≠ 0 := by
      rw [hxx]; exact pow_ne_zero 2 (ne_of_gt hxpos)
    have hind : LinearIndependent ℤ ![x, w] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      have hcast : (a : ℝ) • toR x + (b : ℝ) • toR w = 0 := by
        have h := congrArg toR hab
        ext i
        have hi := congrFun h i
        simp only [toR, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
        push_cast at hi
        simpa using hi
      rw [hw] at hcast
      have hp : dotR (toR x) ((a : ℝ) • toR x + (b : ℝ) • (v - s • toR x)) = 0 := by
        rw [hcast]; simp [dotR]
      simp only [dotR_add_right', dotR_smul_right', dotR_sub_right'] at hp
      rw [dotR_comm' (toR x) v, horth] at hp
      have hA : (a : ℝ) = (b : ℝ) * s := by
        have hfac : ((a : ℝ) - (b : ℝ) * s) * dotR (toR x) (toR x) = 0 := by nlinarith [hp]
        rcases mul_eq_zero.mp hfac with h | h
        · linarith
        · exact absurd h hxne
      have hbv : (b : ℝ) • v = 0 := by
        have hcancel : (b : ℝ) • v = (a : ℝ) • toR x + (b : ℝ) • (v - s • toR x) := by
          rw [hA]; module
        rw [hcancel, hcast]
      rcases smul_eq_zero.mp hbv with h | h
      · refine ⟨?_, by exact_mod_cast h⟩
        have : (a : ℝ) = 0 := by rw [hA, h]; ring
        exact_mod_cast this
      · exact absurd h hv0
    have hdmin : dmin 2 ({x} : Set (Fin (n + 1) → ℤ))
        ≤ detL (Submodule.span ℤ ({x, w} : Set (Fin (n + 1) → ℤ))) :=
      dmin_le_detL (rk_span_pair x w hind) (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact Submodule.subset_span (by simp))
    rw [detgam_span_pair_wedgeNorm x w hind, wedgeNorm_sub_smul x w v s hw horth] at hdmin
    simpa [mul_comm] using hdmin

/-- N04. Veronese lattices: key bounds for one and two vectors, and the determinant of `Γ_{x,y}`. -/
theorem veronese_key (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n) (x y : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y]) :
    lam (Gam d n x y) (NN d n - 2) ≤ muXY n x y ∧
    lam (latOrth (veronese d n x)) (NN d n - 1) ≤ n * eNorm x / dmin 2 {x} ∧
    detL (Gam d n x y) = wedgeNorm (veronese d n x) (veronese d n y) / |(gcdMinors2 x y : ℝ)| := by
  classical
  have hxne : x ≠ y := ne_of_linInd x y hxy
  have hxne' : x ≠ -y := ne_neg_of_linInd x y hxy
  have hν : LinearIndependent ℤ ![veronese d n x, veronese d n y] :=
    Sig2.nu_indep d n hd x y hx hy hxne hxne'
  have hν2 : LinearIndependent ℤ ![veronese 2 n x, veronese 2 n y] :=
    Sig2.nu_indep 2 n (by omega) x y hx hy hxne hxne'
  have hx0 : x ≠ 0 := isPrim_ne_zero hx
  have hy0 : y ≠ 0 := isPrim_ne_zero hy
  have hxpos : 0 < eNorm x := eNorm_pos_of_ne_zero hx0
  have hypos : 0 < eNorm y := eNorm_pos_of_ne_zero hy0
  have hcard : Fintype.card (Fin (n + 1)) = n + 1 := Fintype.card_fin _
  -- positivity of the three `dmin` quantities
  have hd2x : 0 < dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := by
    refine lt_of_lt_of_le one_pos (one_le_dmin 2 _ ?_)
    obtain ⟨L, hL1, hL2⟩ := Lat.exists_rk_two x hx0 (by rw [hcard]; omega)
    exact ⟨L, hL1, by intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hL2⟩
  have hspan : Submodule.span ℤ ({x, y} : Set (Fin (n + 1) → ℤ))
      = Submodule.span ℤ (Set.range ![x, y]) := by
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  have hrkspan : rk (Submodule.span ℤ ({x, y} : Set (Fin (n + 1) → ℤ))) = 2 := by
    rw [rk, hspan, finrank_span_eq_card hxy, Fintype.card_fin]
  have hd2xy : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) := by
    refine lt_of_lt_of_le one_pos (one_le_dmin 2 _ ?_)
    refine ⟨_, hrkspan, ?_⟩
    intro z hz
    rw [hspan]
    exact Submodule.subset_span (by
      rcases hz with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)
  have hd3xy : 0 < dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) := by
    refine lt_of_lt_of_le one_pos (one_le_dmin 3 _ ?_)
    obtain ⟨L, hL1, hL2, hL3⟩ := Lat.exists_rk_three x y hxy (by rw [hcard]; omega)
    exact ⟨L, hL1, by
      intro z hz
      rcases hz with rfl | rfl
      · exact hL2
      · exact hL3⟩
  refine ⟨?_, ?_, ?_⟩
  · -- ## Conjunct 1: the two-vector bound
    have hRle : NN 2 n - 2 ≤ n ^ 2 := by
      have h1 : NN 2 n = (n + 2) * (n + 1) / 2 := by
        rw [show NN 2 n = (n + 2).choose 2 from Lat.card_Mon 2 n, Nat.choose_two_right]
        norm_num [Nat.add_sub_cancel]
      have h2 : (n + 2) * (n + 1) ≤ 2 * (n ^ 2 + 2) + 1 := by nlinarith [hn]
      have h3 : NN 2 n ≤ n ^ 2 + 2 := by
        rw [h1, Nat.div_le_iff_le_mul_add_pred (by norm_num : (0 : ℕ) < 2)]
        omega
      omega
    have hrk2 : Module.finrank ℤ (Gam 2 n x y) = NN 2 n - 2 :=
      (Sig2.gam_rank_det 2 n x y hν2).1
    have hR2 : Module.finrank ℤ (realify (Gam 2 n x y)) = NN 2 n - 2 := by
      rw [finrank_realify, hrk2]
    haveI hdisc := discreteTopology_realify (Gam 2 n x y)
    have htr := (Lat.transference_exact (realify (Gam 2 n x y)) (NN 2 n - 2) hR2).2
    have hdual := Vero.lamR_dual_Gam_two n hn x y hx hy hxy
    set A : ℝ := dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) / dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) with hA
    set B : ℝ := dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y) with hB
    have hApos : 0 < A := by rw [hA]; exact div_pos hd3xy hd2xy
    have hBpos : 0 < B := by rw [hB]; exact div_pos (pow_pos hd2xy 2) (mul_pos hxpos hypos)
    have hμeq : muXY n x y = 3 * (n : ℝ) ^ 2 * max A⁻¹ B⁻¹ := by
      rw [muXY, hA, hB, inv_div, inv_div]
    have hdual' : (1 / 3) * min A B ≤ lamR (dualLat (realify (Gam 2 n x y))) 1 := by
      rw [hA, hB]; exact hdual
    have hBbound : lamR (realify (Gam 2 n x y)) (NN 2 n - 2) ≤ muXY n x y := by
      have hminpos : 0 < (1 / 3 : ℝ) * min A B :=
        mul_pos (by norm_num) (lt_min hApos hBpos)
      have h1 : lamR (realify (Gam 2 n x y)) (NN 2 n - 2) ≤
          ((NN 2 n - 2 : ℕ) : ℝ) / ((1 / 3) * min A B) := by
        rw [le_div_iff₀ hminpos]
        calc lamR (realify (Gam 2 n x y)) (NN 2 n - 2) * ((1 / 3) * min A B)
            ≤ lamR (realify (Gam 2 n x y)) (NN 2 n - 2)
                * lamR (dualLat (realify (Gam 2 n x y))) 1 :=
              mul_le_mul_of_nonneg_left hdual' (lamR_nonneg _ _)
          _ ≤ ((NN 2 n - 2 : ℕ) : ℝ) := htr
      refine le_trans h1 ?_
      rw [hμeq]
      rw [div_le_iff₀ hminpos]
      have hkey : max A⁻¹ B⁻¹ * ((1 / 3) * min A B) = 1 / 3 := by
        have h := max_inv_inv_mul_min hApos hBpos
        calc max A⁻¹ B⁻¹ * ((1 / 3) * min A B)
            = (1 / 3) * (max A⁻¹ B⁻¹ * min A B) := by ring
          _ = (1 / 3) * 1 := by rw [h]
          _ = 1 / 3 := by ring
      have hexp : 3 * (n : ℝ) ^ 2 * max A⁻¹ B⁻¹ * ((1 / 3) * min A B) = (n : ℝ) ^ 2 := by
        calc 3 * (n : ℝ) ^ 2 * max A⁻¹ B⁻¹ * ((1 / 3) * min A B)
            = (n : ℝ) ^ 2 * (3 * (max A⁻¹ B⁻¹ * ((1 / 3) * min A B))) := by ring
          _ = (n : ℝ) ^ 2 * (3 * (1 / 3)) := by rw [hkey]
          _ = (n : ℝ) ^ 2 := by ring
      have hRle' : ((NN 2 n - 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hRle
      calc ((NN 2 n - 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := hRle'
        _ = 3 * (n : ℝ) ^ 2 * max A⁻¹ B⁻¹ * ((1 / 3) * min A B) := hexp.symm
    obtain ⟨a, ha, hai, han⟩ := Vero.lamR_witness (Gam 2 n x y) (NN 2 n - 2)
      (by obtain ⟨f, hf, hfi⟩ := exists_indep_of_finrank (Gam 2 n x y) hrk2
          exact ⟨f, hf, hfi⟩) hBbound
    exact Vero.lam_Gam_veronese_le d n hd hn x y hx hy hxy (muXY n x y)
      (by rw [hμeq]; positivity) a ha hai han
  · -- ## Conjunct 2: the one-vector bound
    have hR1 : Module.finrank ℤ (realify (latOrth x)) = n := by
      rw [finrank_realify, Vero.finrank_latOrth x hx0, hcard]
      omega
    haveI hdisc := discreteTopology_realify (latOrth x)
    have htr := (Lat.transference_exact (realify (latOrth x)) n hR1).2
    have hdual := lamR_dual_latOrth_aux (by omega) x hx
    have hcpos : 0 < dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) / eNorm x := div_pos hd2x hxpos
    have hB : lamR (realify (latOrth x)) n ≤ n * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := by
      have h1 : lamR (realify (latOrth x)) n * (dmin 2 ({x} : Set (Fin (n+1) → ℤ)) / eNorm x) ≤ n :=
        le_trans (mul_le_mul_of_nonneg_left hdual (lamR_nonneg _ _)) htr
      have h2 : lamR (realify (latOrth x)) n * dmin 2 ({x} : Set (Fin (n+1) → ℤ)) ≤ n * eNorm x := by
        have h3 := mul_le_mul_of_nonneg_right h1 (le_of_lt hxpos)
        rwa [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hxpos)] at h3
      rw [le_div_iff₀ hd2x]
      exact h2
    obtain ⟨a, ha, hai, han⟩ := Vero.lamR_witness (latOrth x) n
      (exists_indep_of_finrank (latOrth x) (by rw [Vero.finrank_latOrth x hx0, hcard]; omega)) hB
    have hB0 : (0 : ℝ) ≤ n * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) :=
      le_of_lt (div_pos (mul_pos (by positivity) hxpos) hd2x)
    exact Vero.lam_latOrth_veronese_le d n (by omega) (by omega) x hx _ hB0 a ha hai han
  · -- ## Conjunct 3: the determinant of `Γ_{x,y}`
    rw [show Gam d n x y = latOrth (veronese d n x) ⊓ latOrth (veronese d n y) from rfl,
      Lat.detL_inf_latOrth (veronese d n x) (veronese d n y) hν,
      Vero.gcdMinors2_veronese d n (by omega) (by omega) x y hx hy]

end Work.HP
