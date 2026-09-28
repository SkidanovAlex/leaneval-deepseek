import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.HP3.VeroProdDefs
import Submission.Work.HP.HP3.DotLinDefs
import Submission.Work.HP.Vero.lamR_witness
import Submission.Work.HP.Vero.finrank_latOrth
import Submission.Work.HP.Vero.span_realify_latOrth_inf
import Submission.Work.HP.Vero.dualLat_nonempty
import Submission.Work.HP.Vero.LamAux
import Submission.Work.HP.HP3.lam_eq_lamR
import Submission.Work.HP.HP3.dmin_le_norm_mul_dual
import Submission.Work.HP.HP3.dmin_two_singleton_pos
import Submission.Work.HP.HP3.discreteTopology_realify
import Submission.Work.HP.Transf.lamR_dual_le
import Submission.Work.HP.HP3.veronese_prod_span
import Submission.Work.HP.HP3.prodVecR_pair
import Submission.Work.HP.HP3.veronese_addE
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Vero.MulDefs

/-!
# The lattice of degree-`d` forms vanishing at `x` has small successive minima

For primitive `x ∈ ℤ^{n+1}`, the lattice `Λ_{ν(x)} = latOrth (veronese d n x) ⊆ ℤ^{N}` (`N = NN d n`)
of degree-`d` forms vanishing at `x` has rank `N-1`, and its last successive minimum is bounded by
`K · n · ‖x‖ / 𝔡₂(x)` (paper: Browning–Le Boudec–Sawin, "Key lemma one vector").

The proof has two halves.

* The `d = 1` bound: `latOrth x` has `n` independent vectors of norm `≤ C/λ₁(dualLat)`; this is the
  transference bound `λ_n(Λ)·λ₁(Λ^*) ≤ C` (delegated as `Work.HP.Transf.lamR_dual_le`), combined
  with `𝔡₂(x) ≤ ‖x‖·‖u‖` for every nonzero dual vector `u`
  (`Work.HP.HP3.dmin_le_norm_mul_dual`).
* The product construction: for `m : Mon (d-1) n` and `c ∈ latOrth x`, the degree-`d` form
  `X^m·⟨c,X⟩` vanishes at `x` and its coefficient vector `prodVec d n m c` has norm `eNorm c`;
  these span the whole space of degree-`d` forms vanishing at `x`, so `NN d n - 1 ≤ n · NN (d-1) n`
  of them are independent, all of norm `≤ C/λ₁`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP

/-- The two defining properties of `prodVec d n m c` (the coefficient vector of `X^m · ⟨c,X⟩`):
its evaluation at `x` is `veronese (d-1) n x m * ∑ j, c j * x j`, and its Euclidean norm is that
of `c` (the map `c ↦ prodVec d n m c` is a coordinate embedding). -/
theorem veronese_prod_api (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n)
    (c : Fin (n + 1) → ℤ) (x : Fin (n + 1) → ℤ) :
    formEval d n (prodVec d n m c) x = veronese (d - 1) n x m * ∑ j, c j * x j ∧
    eNorm (prodVec d n m c) = eNorm c := by
  have hA : ∀ m' : Mon d n,
      prodVec d n m c m' = ∑ k, if m' = addE d n hd m k then c k else 0 :=
    fun m' => HP3.prodVec_apply d n hd m c m'
  have hinj : Function.Injective (fun k => addE d n hd m k) := by
    intro a b hab
    have h1 : ((addE d n hd m a).1 a : ℕ) = (m.1 a : ℕ) + 1 := by
      rw [addE_val]; simp
    have h2 : ((addE d n hd m b).1 a : ℕ) = (m.1 a : ℕ) + (if a = b then 1 else 0) :=
      addE_val d n hd m b a
    have hab' : addE d n hd m a = addE d n hd m b := hab
    have h3 : ((addE d n hd m a).1 a : ℕ) = ((addE d n hd m b).1 a : ℕ) := by rw [hab']
    rw [h1, h2] at h3
    by_cases h : a = b
    · exact h
    · rw [if_neg h] at h3
      omega
  constructor
  · rw [formEval]
    have h1 : ∀ m' : Mon d n,
        (prodVec d n m c m' : ℤ) * veronese d n x m'
          = ∑ k, (if m' = addE d n hd m k then c k * veronese d n x m' else 0) := by
      intro m'
      rw [hA m', Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by
        by_cases h : m' = addE d n hd m k
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, zero_mul]
    refine (Finset.sum_congr rfl (fun m' _ => h1 m')).trans ?_
    rw [Finset.sum_comm]
    have h2 : ∀ k : Fin (n + 1),
        (∑ m' : Mon d n, (if m' = addE d n hd m k then c k * veronese d n x m' else 0))
          = c k * (veronese (d - 1) n x m * x k) := by
      intro k
      rw [Finset.sum_eq_single (addE d n hd m k)]
      · rw [if_pos rfl, HP3.veronese_addE]
      · intro b _ hb
        rw [if_neg hb]
      · intro hb
        exact absurd (Finset.mem_univ _) hb
    refine (Finset.sum_congr rfl (fun k _ => h2 k)).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rw [eNorm, eNorm]
    congr 1
    have key : ∀ m' : Mon d n, ((prodVec d n m c m' : ℝ)) ^ 2
        = ∑ k, ((if m' = addE d n hd m k then c k else 0 : ℤ) : ℝ) ^ 2 := by
      intro m'
      rw [hA m']
      push_cast
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single k]
      · ring
      · intro k' _ hk'
        have hz : (if m' = addE d n hd m k then c k else 0)
            * (if m' = addE d n hd m k' then c k' else 0) = 0 := by
          by_cases h1 : m' = addE d n hd m k
          · by_cases h2 : m' = addE d n hd m k'
            · exact absurd (hinj (h1.symm.trans h2)).symm hk'
            · rw [if_pos h1, if_neg h2, mul_zero]
          · rw [if_neg h1, zero_mul]
        exact_mod_cast hz
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    refine (Finset.sum_congr rfl (fun m' _ => key m')).trans ?_
    rw [Finset.sum_comm]
    have h3 : ∀ k : Fin (n + 1),
        (∑ m' : Mon d n, ((if m' = addE d n hd m k then c k else 0 : ℤ) : ℝ) ^ 2)
          = ((c k : ℝ)) ^ 2 := by
      intro k
      rw [Finset.sum_eq_single (addE d n hd m k)]
      · simp
      · intro b _ hb
        rw [if_neg hb]
        simp
      · intro hb
        exact absurd (Finset.mem_univ _) hb
    exact (Finset.sum_congr rfl (fun k _ => h3 k)).trans rfl
end Work.HP

namespace Work.HP

/-- The monomial `X_i^d` as an element of `Mon d n`. -/
private def powMon (d n : ℕ) (i : Fin (n + 1)) : Mon d n where
  val j := ⟨if j = i then d else 0, by split <;> omega⟩
  property := by rw [Finset.sum_ite_eq']; simp

private lemma veronese_powMon {R : Type*} [CommSemiring R] (d n : ℕ) (i : Fin (n + 1))
    (x : Fin (n + 1) → R) : veronese d n x (powMon d n i) = x i ^ d := by
  simp only [veronese]
  rw [Finset.prod_eq_single i]
  · simp [powMon]
  · intro j _ hji
    simp [powMon, hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

end Work.HP

namespace Work.HP

/-! ## Small lattice/Veronese helpers (self-contained) -/

/-- A primitive integer vector is nonzero. -/
private lemma isPrim_ne_zero' {ι : Type*} [Fintype ι] {v : ι → ℤ} (h : IsPrim v) : v ≠ 0 := by
  intro hv
  have h0 : Finset.univ.gcd v = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun x _ => by rw [hv]; rfl)
  rw [IsPrim] at h
  omega

/-- From a finite family whose `ℝ`-span has dimension `D` one extracts `D` linearly independent
members of the family. -/
lemma exists_linearIndependent_fin_of_span_range' {κ M : Type*} [Fintype κ] [AddCommGroup M]
    [Module ℝ M] [FiniteDimensional ℝ M] (v : κ → M) (D : ℕ)
    (h : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = D) :
    ∃ f : Fin D → M, LinearIndependent ℝ f ∧ ∀ i, f i ∈ Set.range v := by
  classical
  obtain ⟨f, hf_mem, -, hf_ind⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range v)
  exact ⟨fun i => f (Fin.cast h.symm i), hf_ind.comp _ (Fin.cast_injective h.symm),
    fun i => hf_mem _⟩

/-- `intCastPi` commutes with finite sums of `ℤ`-multiples. -/
lemma intCastPi_sum_smul' {κ ι : Type*} [Fintype κ] [Fintype ι]
    (c : κ → ℤ) (v : κ → ι → ℤ) :
    intCastPi (∑ k, c k • v k) = ∑ k, (c k : ℝ) • intCastPi (v k) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by ext i; simp [intCastPi, zsmul_eq_mul]

/-- `ℤ`-linear independence follows from `ℝ`-linear independence of the realified family. -/
lemma linearIndependent_int_of_intCastPi' {κ ι : Type*} [Fintype κ] [Fintype ι]
    {f : κ → ι → ℤ} (h : LinearIndependent ℝ (fun k => intCastPi (f k))) :
    LinearIndependent ℤ f := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  have key : ∑ k, (g k : ℝ) • intCastPi (f k) = 0 := by
    rw [← intCastPi_sum_smul' g f, hg, map_zero]
  intro k
  exact_mod_cast h _ key k

theorem lam_latOrth_veronese_le (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : Fin (n + 1) → ℤ, IsPrim x →
      lam (latOrth (veronese d n x)) (NN d n - 1) ≤ K * (n * eNorm x / dmin 2 {x}) := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨C, hCpos, hC⟩ := Transf.lamR_dual_le (ι := Fin (n + 1)) n
  refine ⟨C * n, by positivity, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := isPrim_ne_zero' hx
  have hEx : 0 < eNorm x := eNorm_pos_of_ne_zero hx0
  -- a nonzero vector of the dual of `latOrth x`
  have hdual : ∃ u ∈ dualLat (realify (latOrth x)), u ≠ 0 := by
    obtain ⟨u, hu0, huorth⟩ := Vero.exists_ne_zero_orthogonal (n := n) hn2 hx0
    have humem : u ∈ latOrth x := by
      rw [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply]
      simp only [smul_eq_mul]
      exact huorth
    refine ⟨intCastPi u, Vero.realify_le_dualLat (latOrth x) (Submodule.mem_map_of_mem humem), ?_⟩
    intro h
    apply hu0
    funext i
    have := congrFun h i
    simpa [intCastPi] using this
  -- (ii) `𝔡₂(x)/‖x‖ ≤ λ₁(dual)`
  have hrho_ge : dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) / eNorm x
      ≤ lamR (dualLat (realify (latOrth x))) 1 := by
    refine Vero.le_lamR_one _ hdual ?_
    intro v hv hv0
    rw [div_le_iff₀ hEx, mul_comm (rNorm v) (eNorm x)]
    exact HP3.dmin_le_norm_mul_dual n x hx v hv hv0
  have hdmin_pos : 0 < dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := HP3.dmin_two_singleton_pos hn1 x hx0
  have hrho_pos : 0 < lamR (dualLat (realify (latOrth x))) 1 :=
    lt_of_lt_of_le (div_pos hdmin_pos hEx) hrho_ge
  have hdmin_le : dmin 2 ({x} : Set (Fin (n + 1) → ℤ))
      ≤ eNorm x * lamR (dualLat (realify (latOrth x))) 1 := by
    have h := hrho_ge
    rw [div_le_iff₀ hEx,
      mul_comm (lamR (dualLat (realify (latOrth x))) 1) (eNorm x)] at h
    exact h
  -- rank hypothesis for the transference bound
  have hrank : n ≤ Module.finrank ℝ
      (Submodule.span ℝ (realify (latOrth x) : Set (Fin (n + 1) → ℝ))) := by
    have h1 : Module.finrank ℤ (latOrth x) = n := by
      rw [Vero.finrank_latOrth x hx0]
      simp
    have h2 := Vero.finrank_span_image_intCastPi (latOrth x)
    rw [h1] at h2
    have h3 : Submodule.span ℝ (realify (latOrth x) : Set (Fin (n + 1) → ℝ))
        = Submodule.span ℝ (⇑intCastPi '' (latOrth x : Set (Fin (n + 1) → ℤ))) := by
      congr 1
    rw [h3, h2]
  obtain ⟨f, hfL, hfLI, hfB⟩ := hC (realify (latOrth x)) (HP3.discreteTopology_realify _) hrank
  have hlamR : lamR (realify (latOrth x)) n ≤ C / lamR (dualLat (realify (latOrth x))) 1 := by
    refine csInf_le ⟨0, fun r hr => hr.1⟩ ?_
    exact ⟨by positivity, f, hfL, hfLI, fun j => by
      rw [le_div_iff₀ hrho_pos]
      exact hfB j⟩
  have hne : ∃ g : Fin n → (Fin (n + 1) → ℤ), (∀ j, g j ∈ latOrth x) ∧ LinearIndependent ℤ g := by
    choose g hgmem hgeq using fun j => Submodule.mem_map.mp (hfL j)
    refine ⟨g, hgmem, ?_⟩
    have h2 : LinearIndependent ℝ (fun j => intCastPi (g j)) := by
      have h3 : (fun j => intCastPi (g j)) = f := funext hgeq
      rw [h3]
      exact hfLI
    exact (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (v := g)).mp h2
  obtain ⟨c, hcL, hcLI, hcB⟩ := Vero.lamR_witness (latOrth x) n hne hlamR
  -- the product construction
  have hspan := HP3.veronese_prod_span d n hd x hx c hcL hcLI
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx0
  have hν : veronese d n x (powMon d n i₀) ≠ 0 := by
    rw [veronese_powMon]
    exact pow_ne_zero d hi₀
  have hF : evalLin d n x (Pi.single (powMon d n i₀) (1 : ℝ)) ≠ 0 := by
    intro h
    apply hν
    have h' : ((veronese d n x (powMon d n i₀) : ℤ) : ℝ) = 0 := by
      have hh := h
      simp only [evalLin, LinearMap.coe_mk, AddHom.coe_mk] at hh
      rw [Finset.sum_eq_single (powMon d n i₀)] at hh
      · simpa using hh
      · intro m _ hm
        rw [Pi.single_eq_of_ne (i := powMon d n i₀) (i' := m) hm]
        simp
      · intro hm
        exact absurd (Finset.mem_univ _) hm
    exact_mod_cast h'
  have hker_rank : Module.finrank ℝ (LinearMap.ker (evalLin d n x)) = NN d n - 1 := by
    have htot : Module.finrank ℝ (Mon d n → ℝ) = NN d n := Module.finrank_fintype_fun_eq_card ℝ
    have hadd := LinearMap.finrank_range_add_finrank_ker (evalLin d n x)
    have hrange_le : Module.finrank ℝ (LinearMap.range (evalLin d n x)) ≤ 1 := by
      have h := Submodule.finrank_le (R := ℝ) (LinearMap.range (evalLin d n x))
      rwa [Module.finrank_self] at h
    have hrange_ge : 1 ≤ Module.finrank ℝ (LinearMap.range (evalLin d n x)) := by
      have h2 : Module.finrank ℝ (Submodule.span ℝ {evalLin d n x (Pi.single (powMon d n i₀) 1)})
          ≤ Module.finrank ℝ (LinearMap.range (evalLin d n x)) :=
        Submodule.finrank_mono (by
          rw [Submodule.span_le]
          rintro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact ⟨_, rfl⟩)
      rw [finrank_span_singleton hF] at h2
      exact h2
    have hrange : Module.finrank ℝ (LinearMap.range (evalLin d n x)) = 1 :=
      le_antisymm hrange_le hrange_ge
    rw [hrange, htot] at hadd
    omega
  have hspanfin : Module.finrank ℝ (Submodule.span ℝ
        (Set.range (fun p : Mon (d - 1) n × Fin n => prodVecR d n p.1 (c p.2)))) = NN d n - 1 := by
    rw [hspan]
    exact hker_rank
  obtain ⟨F, hFLI, hFmem⟩ := exists_linearIndependent_fin_of_span_range'
    (κ := Mon (d - 1) n × Fin n) (M := Mon d n → ℝ)
    (fun p => prodVecR d n p.1 (c p.2)) (NN d n - 1) hspanfin
  choose p hp using hFmem
  let g : Fin (NN d n - 1) → (Mon d n → ℤ) := fun i => prodVec d n (p i).1 (c (p i).2)
  have hgc : (fun i => intCastPi (g i)) = F := by
    funext i
    rw [← hp i]
    rfl
  have hgI : LinearIndependent ℤ g :=
    linearIndependent_int_of_intCastPi' (by rw [hgc]; exact hFLI)
  have hgL : ∀ i, g i ∈ latOrth (veronese d n x) := by
    intro i
    have h := (veronese_prod_api d n (by omega) (p i).1 (c (p i).2) x).1
    have hc : ∑ j, (c (p i).2) j * x j = 0 := by
      have hcl := hcL (p i).2
      rw [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply] at hcl
      simpa only [smul_eq_mul] using hcl
    rw [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply]
    simp only [smul_eq_mul]
    change formEval d n (prodVec d n (p i).1 (c (p i).2)) x = 0
    rw [h, hc, mul_zero]
  have hgB : ∀ i, eNorm (g i) ≤ C / lamR (dualLat (realify (latOrth x))) 1 := by
    intro i
    have h := (veronese_prod_api d n (by omega) (p i).1 (c (p i).2) x).2
    rw [h]
    exact hcB (p i).2
  have hmain : lam (latOrth (veronese d n x)) (NN d n - 1)
      ≤ C / lamR (dualLat (realify (latOrth x))) 1 := by
    rw [lam_eq_sInf]
    refine csInf_le (bddBelow_lamSet _ _) ?_
    exact ⟨by positivity, g, hgL, hgI, hgB⟩
  -- final arithmetic
  have hρ : 1 / lamR (dualLat (realify (latOrth x))) 1
      ≤ eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := by
    rw [div_le_iff₀ hrho_pos, div_mul_eq_mul_div, one_le_div hdmin_pos]
    exact hdmin_le
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hdn : (0 : ℝ) < eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) :=
    div_pos hEx hdmin_pos
  calc lam (latOrth (veronese d n x)) (NN d n - 1)
      ≤ C / lamR (dualLat (realify (latOrth x))) 1 := hmain
    _ = C * (1 / lamR (dualLat (realify (latOrth x))) 1) := by rw [mul_one_div]
    _ ≤ C * (eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))) :=
        mul_le_mul_of_nonneg_left hρ (le_of_lt hCpos)
    _ ≤ C * n * (n * (eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) := by
        have hA : 0 ≤ eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := le_of_lt hdn
        have h1 : eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))
            ≤ n * (n * (eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) := by
          have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
          have h2 : (1 : ℝ) ≤ n * n := by nlinarith [hn2R]
          calc eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))
              = 1 * (eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))) := by ring
            _ ≤ (n * n) * (eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))) :=
                mul_le_mul_of_nonneg_right h2 hA
            _ = n * (n * (eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) := by ring
        calc C * (eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))
            ≤ C * (n * (n * (eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))))) :=
              mul_le_mul_of_nonneg_left h1 (le_of_lt hCpos)
          _ = C * n * (n * (eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) := by ring
    _ = C * n * (n * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))) := by ring

end Work.HP
