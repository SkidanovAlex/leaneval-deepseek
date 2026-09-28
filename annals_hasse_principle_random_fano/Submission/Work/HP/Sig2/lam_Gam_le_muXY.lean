import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.HP3.VeroProdDefs
import Submission.Work.HP.Sig2.VeroMon
import Submission.Work.HP.Sig2.veronese_proportional
import Submission.Work.HP.Sig2.transference_extreme
import Submission.Work.HP.Sig2.GamTwo_dual_lam1
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.Sig2.gam_rank_det
import Submission.Work.HP.MDBasic.mem_Gam_iff
import Submission.Work.HP.HP3.lam_eq_lamR
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Lat.card_Mon
import Submission.Work.HP.Lat.exists_rk_three
import Submission.Work.HP.HP3.discreteTopology_realify
import Submission.Work.HP.Vero.span_realify_latOrth_inf
import Submission.Work.HP.Transf.Basic

/-!
# The key geometry-of-numbers lemma for two vectors

`Work.HP.Sig2.lam_Gam_le_muXY` : for `d ≥ 2`, `d ≤ n` and primitive `ℤ`-linearly independent
`x, y ∈ ℤ^{n+1}` we have `lam (Gam d n x y) (NN d n - 2) ≤ muXY n x y`.

The proof follows Browning--Le Boudec--Sawin, *The Hasse principle for random Fano hypersurfaces*,
Annals 2023, Section 3 (the two-vector key lemma).  The file is organised as follows.

* `monAddE`, `monSubE`, `shiftG`, `shift1`, `shiftZ` : multiplication of a coefficient vector by a
  monomial `X_i`, together with its basic properties (isometry for the Euclidean norm,
  multiplicativity against the Veronese map, integrality).
* `VR d n x y` : the real vector space of degree-`d` forms vanishing at `x` and at `y`.  It has
  real dimension `NN d n - 2` (`finrank_VR`), contains the realification of `Gam d n x y`
  (`realify_subset_VR`) and serves as the ambient space for the lifting from degree `2` to degree
  `d` used below (see `VR_eq_iSup_shift`).
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.HP.Sig2

open Work.HP

variable {n : ℕ}

/-- `β + e_i`, the exponent vector of `X_i · X^β`, as an element of `Mon d n` for `β : Mon (d-1) n`. -/
def monAddE {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (β : Mon (d - 1) n) : Mon d n :=
  monOfNat d n (fun j => (β.1 j : ℕ) + (if j = i then 1 else 0)) (by
    rw [Finset.sum_add_distrib, β.2]
    have : ∑ j : Fin (n + 1), (if j = i then 1 else 0) = 1 := by simp
    rw [this]; omega)

@[simp] theorem monAddE_apply {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1))
    (β : Mon (d - 1) n) (j : Fin (n + 1)) :
    ((monAddE d hd i β).1 j : ℕ) = (β.1 j : ℕ) + (if j = i then 1 else 0) := rfl

/-- `m - e_i`, the exponent vector of `X^m / X_i`, for `m : Mon d n` with `m_i ≥ 1`. -/
def monSubE {n : ℕ} (d : ℕ) (i : Fin (n + 1)) (m : Mon d n)
    (hm : 1 ≤ (m.1 i : ℕ)) : Mon (d - 1) n :=
  monOfNat (d - 1) n (fun j => (m.1 j : ℕ) - (if j = i then 1 else 0)) (by
    have hle : ∀ j, (if j = i then 1 else 0) ≤ (m.1 j : ℕ) := by
      intro j; by_cases hji : j = i
      · subst hji; simpa using hm
      · simp [hji]
    rw [Finset.sum_tsub_distrib Finset.univ (fun j _ => hle j), m.2]
    have : ∑ j : Fin (n + 1), (if j = i then 1 else 0) = 1 := by simp
    rw [this])

@[simp] theorem monSubE_apply {n : ℕ} (d : ℕ) (i : Fin (n + 1)) (m : Mon d n)
    (hm : 1 ≤ (m.1 i : ℕ)) (j : Fin (n + 1)) :
    ((monSubE d i m hm).1 j : ℕ) = (m.1 j : ℕ) - (if j = i then 1 else 0) := rfl

theorem monSubE_monAddE {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (β : Mon (d - 1) n)
    (h : 1 ≤ ((monAddE d hd i β).1 i : ℕ)) : monSubE d i (monAddE d hd i β) h = β := by
  ext j
  simp only [monSubE_apply, monAddE_apply]
  by_cases hji : j = i
  · subst hji; simp
  · simp [hji]

theorem monAddE_monSubE {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (m : Mon d n)
    (hm : 1 ≤ (m.1 i : ℕ)) : monAddE d hd i (monSubE d i m hm) = m := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp only [monAddE_apply, monSubE_apply]
    simp
    omega
  · simp only [monAddE_apply, monSubE_apply]
    simp [hji]

theorem monAddE_injective {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) :
    Function.Injective (monAddE d hd i : Mon (d - 1) n → Mon d n) := by
  intro β γ h
  ext j
  have hj : ((monAddE d hd i β).1 j : ℕ) = ((monAddE d hd i γ).1 j : ℕ) := by rw [h]
  simp only [monAddE_apply] at hj
  by_cases hji : j = i
  · subst hji; omega
  · simpa [hji] using hj

theorem veronese_monAddE {n : ℕ} {R : Type*} [CommSemiring R] (d : ℕ) (hd : 1 ≤ d)
    (i : Fin (n + 1)) (β : Mon (d - 1) n) (z : Fin (n + 1) → R) :
    veronese d n z (monAddE d hd i β) = z i * veronese (d - 1) n z β := by
  have key : ∀ j : Fin (n + 1), z j ^ ((β.1 j : ℕ) + (if j = i then 1 else 0))
      = z j ^ (β.1 j : ℕ) * z j ^ (if j = i then 1 else 0) := fun j => pow_add _ _ _
  have h2 : (∏ j, z j ^ (if j = i then 1 else 0)) = z i := by
    rw [Finset.prod_eq_single i (fun b _ hb => by simp [hb])
          (fun h => absurd (Finset.mem_univ i) h)]
    simp
  rw [monAddE, veronese_monOfNat, veronese, Finset.prod_congr rfl (fun j _ => key j),
      Finset.prod_mul_distrib, h2, mul_comm]


section shifts

/-- Multiplication by `X_i` on coefficient vectors, over an arbitrary zero-carrying type:
`(shiftG u) m = u (m - e_i)` when `m_i ≥ 1`, and `0` otherwise. -/
def shiftG {R : Type*} [Zero R] {n : ℕ} (d : ℕ) (i : Fin (n + 1))
    (u : Mon (d - 1) n → R) : Mon d n → R :=
  fun m => if h : 1 ≤ (m.1 i : ℕ) then u (monSubE d i m h) else 0

theorem shiftG_apply {R : Type*} [Zero R] {n : ℕ} (d : ℕ) (i : Fin (n + 1))
    (u : Mon (d - 1) n → R) (m : Mon d n) :
    shiftG d i u m = (if h : 1 ≤ (m.1 i : ℕ) then u (monSubE d i m h) else 0) := rfl

theorem sum_shiftG {R M : Type*} [Zero R] [AddCommMonoid M] {n : ℕ} (d : ℕ) (hd : 1 ≤ d)
    (i : Fin (n + 1)) (u : Mon (d - 1) n → R) (f : Mon d n → R → M) (hf : ∀ m, f m 0 = 0) :
    ∑ m : Mon d n, f m (shiftG d i u m) = ∑ β : Mon (d - 1) n, f (monAddE d hd i β) (u β) := by
  have key : ∀ m : Mon d n, f m (shiftG d i u m)
      = ∑ β : Mon (d - 1) n, (if monAddE d hd i β = m then f m (u β) else 0) := by
    intro m
    by_cases hm : 1 ≤ (m.1 i : ℕ)
    · rw [shiftG_apply, dif_pos hm]
      rw [Finset.sum_eq_single (monSubE d i m hm)]
      · simp [monAddE_monSubE d hd i m hm]
      · intro β _ hβ
        rw [if_neg]
        intro hc
        exact hβ (monAddE_injective d hd i (by rw [hc, monAddE_monSubE d hd i m hm]))
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [shiftG_apply, dif_neg hm, hf]
      rw [Finset.sum_eq_zero]
      · intro β _
        rw [if_neg]
        intro hc
        exact hm (by rw [← hc]; simp [monAddE_apply])
  calc ∑ m : Mon d n, f m (shiftG d i u m)
      = ∑ m : Mon d n, ∑ β : Mon (d - 1) n,
          (if monAddE d hd i β = m then f m (u β) else 0) :=
        Finset.sum_congr rfl (fun m _ => key m)
    _ = ∑ β : Mon (d - 1) n, ∑ m : Mon d n,
          (if monAddE d hd i β = m then f m (u β) else 0) := Finset.sum_comm
    _ = ∑ β : Mon (d - 1) n, f (monAddE d hd i β) (u β) := by
        refine Finset.sum_congr rfl (fun β _ => ?_)
        rw [Finset.sum_ite_eq]
        simp

theorem shiftG_monAddE {R : Type*} [Zero R] {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1))
    (u : Mon (d - 1) n → R) (β : Mon (d - 1) n) :
    shiftG d i u (monAddE d hd i β) = u β := by
  have h : 1 ≤ ((monAddE d hd i β).1 i : ℕ) := by simp
  rw [shiftG_apply, dif_pos h, monSubE_monAddE d hd i β h]

/-- Multiplication by `X_i` as a linear map over `ℝ`. -/
def shift1 {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) :
    (Mon (d - 1) n → ℝ) →ₗ[ℝ] (Mon d n → ℝ) where
  toFun := shiftG d i
  map_add' u v := by
    funext m
    simp only [Pi.add_apply]
    rw [shiftG_apply, shiftG_apply, shiftG_apply]
    by_cases h : 1 ≤ (m.1 i : ℕ) <;> simp [h]
  map_smul' c u := by
    funext m
    simp only [Pi.smul_apply]
    rw [shiftG_apply, shiftG_apply]
    by_cases h : 1 ≤ (m.1 i : ℕ) <;> simp [h]

/-- Multiplication by `X_i` as a linear map over `ℤ`. -/
def shiftZ {n : ℕ} (d : ℕ) (i : Fin (n + 1)) :
    (Mon (d - 1) n → ℤ) →ₗ[ℤ] (Mon d n → ℤ) where
  toFun := shiftG d i
  map_add' u v := by
    funext m
    simp only [Pi.add_apply]
    rw [shiftG_apply, shiftG_apply, shiftG_apply]
    by_cases h : 1 ≤ (m.1 i : ℕ) <;> simp [h]
  map_smul' c u := by
    funext m
    simp only [Pi.smul_apply]
    rw [shiftG_apply, shiftG_apply]
    by_cases h : 1 ≤ (m.1 i : ℕ) <;> simp [h]

@[simp] theorem shift1_apply {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1))
    (u : Mon (d - 1) n → ℝ) (m : Mon d n) :
    shift1 d hd i u m = (if h : 1 ≤ (m.1 i : ℕ) then u (monSubE d i m h) else 0) := rfl

@[simp] theorem shiftZ_apply {n : ℕ} (d : ℕ) (i : Fin (n + 1)) (u : Mon (d - 1) n → ℤ)
    (m : Mon d n) :
    shiftZ d i u m = (if h : 1 ≤ (m.1 i : ℕ) then u (monSubE d i m h) else 0) := rfl

theorem sum_shift1 {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (u : Mon (d - 1) n → ℝ)
    (f : Mon d n → ℝ → ℝ) (hf : ∀ m, f m 0 = 0) :
    ∑ m : Mon d n, f m (shift1 d hd i u m) = ∑ β : Mon (d - 1) n, f (monAddE d hd i β) (u β) :=
  sum_shiftG d hd i u f hf

theorem sum_shiftZ {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (u : Mon (d - 1) n → ℤ)
    (M : Type*) [AddCommMonoid M] (f : Mon d n → ℤ → M) (hf : ∀ m, f m 0 = 0) :
    ∑ m : Mon d n, f m (shiftZ d i u m) = ∑ β : Mon (d - 1) n, f (monAddE d hd i β) (u β) :=
  sum_shiftG d hd i u f hf

theorem shift1_monAddE {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (u : Mon (d - 1) n → ℝ)
    (β : Mon (d - 1) n) : shift1 d hd i u (monAddE d hd i β) = u β :=
  shiftG_monAddE d hd i u β

theorem shiftZ_monAddE {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (u : Mon (d - 1) n → ℤ)
    (β : Mon (d - 1) n) : shiftZ d i u (monAddE d hd i β) = u β :=
  shiftG_monAddE d hd i u β

theorem rNorm_shift1 {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (u : Mon (d - 1) n → ℝ) :
    rNorm (shift1 d hd i u) = rNorm u := by
  unfold rNorm
  congr 1
  rw [sum_shift1 d hd i u (fun _ x => x ^ 2) (by intro m; ring)]

theorem sum_veronese_shift1 {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1))
    (u : Mon (d - 1) n → ℝ) (z : Fin (n + 1) → ℝ) :
    (∑ m : Mon d n, shift1 d hd i u m * veronese d n z m)
      = z i * ∑ β : Mon (d - 1) n, u β * veronese (d - 1) n z β := by
  rw [sum_shift1 d hd i u (fun m x => x * veronese d n z m) (by intro m; ring)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [veronese_monAddE d hd i β z]
  ring

theorem sum_veronese_shiftZ {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1))
    (u : Mon (d - 1) n → ℤ) (z : Fin (n + 1) → ℤ) :
    (∑ m : Mon d n, shiftZ d i u m * veronese d n z m)
      = z i * ∑ β : Mon (d - 1) n, u β * veronese (d - 1) n z β := by
  rw [sum_shiftZ d hd i u ℤ (fun m x => x * veronese d n z m) (by intro m; ring)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [veronese_monAddE d hd i β z]
  ring

theorem shift1_coe {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (u : Mon (d - 1) n → ℤ) :
    shift1 d hd i (fun β => (u β : ℝ)) = fun m => ((shiftZ d i u m : ℤ) : ℝ) := by
  funext m
  rw [shift1_apply, shiftZ_apply]
  by_cases h : 1 ≤ (m.1 i : ℕ) <;> simp [h]

end shifts

/-- The space of degree-`d` forms (coefficient vectors) vanishing at `x` and at `y`. -/
def VR (d n : ℕ) (x y : Fin (n + 1) → ℤ) : Submodule ℝ (Mon d n → ℝ) :=
  (evalLin d n x).ker ⊓ (evalLin d n y).ker

theorem mem_VR {d n : ℕ} {x y : Fin (n + 1) → ℤ} {F : Mon d n → ℝ} :
    F ∈ VR d n x y ↔ (∑ m : Mon d n, F m * ((veronese d n x m : ℤ) : ℝ) = 0 ∧
      ∑ m : Mon d n, F m * ((veronese d n y m : ℤ) : ℝ) = 0) := by
  simp only [VR, Submodule.mem_inf, LinearMap.mem_ker]
  exact Iff.rfl

theorem evalLin_single {d n : ℕ} (x : Fin (n + 1) → ℤ) (m : Mon d n) :
    evalLin d n x (Pi.single m 1) = ((veronese d n x m : ℤ) : ℝ) := by
  show (∑ m' : Mon d n, (Pi.single m 1 : Mon d n → ℝ) m' * ((veronese d n x m' : ℤ) : ℝ))
      = ((veronese d n x m : ℤ) : ℝ)
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ m) h

theorem linInd_evalLin {d n : ℕ} (x y : Fin (n + 1) → ℤ)
    (h : LinearIndependent ℝ ![(fun m => ((veronese d n x m : ℤ) : ℝ)),
        (fun m => ((veronese d n y m : ℤ) : ℝ))]) :
    LinearIndependent ℝ ![evalLin d n x, evalLin d n y] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro a b hab
  refine h a b ?_
  funext m
  have hm := congrArg (fun (φ : (Mon d n → ℝ) →ₗ[ℝ] ℝ) => φ (Pi.single m 1)) hab
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply] at hm
  rw [evalLin_single, evalLin_single] at hm
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hm

/-- The space of forms vanishing at two points, as a kernel of two independent functionals, has
codimension two. -/
theorem finrank_VR_add_two (d n : ℕ) (x y : Fin (n + 1) → ℤ)
    (h : LinearIndependent ℝ ![evalLin d n x, evalLin d n y]) :
    Module.finrank ℝ ↥(VR d n x y) + 2 = NN d n := by
  classical
  set f := evalLin d n x with hfdef
  set g := evalLin d n y with hgdef
  have hh : LinearIndependent ℝ ![f, g] := by simpa [hfdef, hgdef] using h
  have hVR : VR d n x y = f.ker ⊓ g.ker := by simp only [VR, hfdef, hgdef]
  rw [hVR]
  have hf : f ≠ 0 := by
    intro h0
    have h1 : (1 : ℝ) • f + (0 : ℝ) • g = 0 := by rw [h0]; simp
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hh) 1 0 h1).1
  have hg : g ≠ 0 := by
    intro h0
    have h1 : (0 : ℝ) • f + (1 : ℝ) • g = 0 := by rw [h0]; simp
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hh) 0 1 h1).2
  have hg' : g.comp (LinearMap.ker f).subtype ≠ 0 := by
    intro h0
    have hle : LinearMap.ker f ≤ LinearMap.ker g := by
      intro v hv
      have h2 : (g.comp (LinearMap.ker f).subtype) ⟨v, hv⟩ = 0 := by rw [h0]; rfl
      simpa [LinearMap.comp_apply] using h2
    have hmem : g ∈ Submodule.span ℝ {f} := by
      have h0 := FiniteDimensional.mem_span_of_iInf_ker_le_ker (𝕜 := ℝ)
        (L := ![f]) (K := g) (by simpa using hle)
      simpa using h0
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have h1 : (-c) • f + (1 : ℝ) • g = 0 := by
      have h2 : (-c) • f = -(c • f) := neg_smul c f
      simp [h2, hc]
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hh) (-c) 1 h1).2
  have hsup : LinearMap.ker f ⊔ LinearMap.ker g = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    obtain ⟨w, hw⟩ := LinearMap.surjective hg' (- g v)
    have hw' : g w = - g v := by
      have h2 := hw
      simpa [LinearMap.comp_apply] using h2
    refine Submodule.mem_sup.mpr ⟨-w, Submodule.neg_mem _ w.2, v + w, ?_, ?_⟩
    · rw [LinearMap.mem_ker, map_add, hw']; abel
    · abel
  have h1 : Module.finrank ℝ ↥(LinearMap.ker f) + 1 = Module.finrank ℝ (Mon d n → ℝ) :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have h2 : Module.finrank ℝ ↥(LinearMap.ker g) + 1 = Module.finrank ℝ (Mon d n → ℝ) :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hg
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) (LinearMap.ker g)
  rw [hsup, finrank_top] at h3
  have hV : Module.finrank ℝ (Mon d n → ℝ) = NN d n := Module.finrank_fintype_fun_eq_card ℝ
  omega

theorem shift1_mem_VR {d n : ℕ} (x y : Fin (n + 1) → ℤ) (hd : 1 ≤ d) (i : Fin (n + 1))
    {u : Mon (d - 1) n → ℝ} (hu : u ∈ VR (d - 1) n x y) : shift1 d hd i u ∈ VR d n x y := by
  have hconv : ∀ (k : ℕ) (z : Fin (n + 1) → ℤ) (m : Mon k n),
      veronese k n (fun i => (z i : ℝ)) m = ((veronese k n z m : ℤ) : ℝ) := by
    intro k z m
    simp only [veronese]
    push_cast
    rfl
  have hsum : ∀ (z : Fin (n + 1) → ℤ),
      (∑ β : Mon (d - 1) n, u β * veronese (d - 1) n (fun i => (z i : ℝ)) β)
        = ∑ β : Mon (d - 1) n, u β * ((veronese (d - 1) n z β : ℤ) : ℝ) :=
    fun z => Finset.sum_congr rfl (fun β _ => by rw [hconv])
  rw [mem_VR] at hu ⊢
  constructor
  · rw [show (∑ m : Mon d n, shift1 d hd i u m * ((veronese d n x m : ℤ) : ℝ))
          = ∑ m : Mon d n, shift1 d hd i u m * veronese d n (fun i => (x i : ℝ)) m from
        Finset.sum_congr rfl (fun m _ => by rw [← hconv])]
    rw [sum_veronese_shift1 d hd i u (fun i => (x i : ℝ)), hsum x, hu.1, mul_zero]
  · rw [show (∑ m : Mon d n, shift1 d hd i u m * ((veronese d n y m : ℤ) : ℝ))
          = ∑ m : Mon d n, shift1 d hd i u m * veronese d n (fun i => (y i : ℝ)) m from
        Finset.sum_congr rfl (fun m _ => by rw [← hconv])]
    rw [sum_veronese_shift1 d hd i u (fun i => (y i : ℝ)), hsum y, hu.2, mul_zero]

theorem realify_subset_VR {d n : ℕ} (x y : Fin (n + 1) → ℤ) :
    (realify (Gam d n x y) : Set (Mon d n → ℝ)) ⊆ VR d n x y := by
  intro F hF
  obtain ⟨w, hw, rfl⟩ := hF
  change intCastPi w ∈ VR d n x y
  rw [mem_VR]
  have hw' := (Work.HP.MDBasic.mem_Gam_iff d n x y w).mp hw
  have hcast : ∀ (z : Fin (n + 1) → ℤ),
      (∑ m : Mon d n, (intCastPi w) m * ((veronese d n z m : ℤ) : ℝ))
        = ((formEval d n w z : ℤ) : ℝ) := by
    intro z
    have h1 : ((formEval d n w z : ℤ) : ℝ)
        = ∑ m : Mon d n, ((w m : ℝ) * ((veronese d n z m : ℤ) : ℝ)) := by
      have h2 : formEval d n w z = ∑ m : Mon d n, w m * veronese d n z m := rfl
      rw [h2]
      push_cast
      rfl
    rw [h1]
    exact Finset.sum_congr rfl (fun m _ => by simp [intCastPi_apply])
  refine ⟨?_, ?_⟩
  · rw [hcast x, hw'.1]; simp
  · rw [hcast y, hw'.2]; simp



/-! ## Integrality of the shift -/

/-- `shiftZ` preserves `Gam`: multiplying a form vanishing at `x` and `y` by `X_i` again gives a
form vanishing at `x` and `y`.  Stated with the source degree `b` explicit (the target being
`b + 1`) so that it composes without `Nat` subtraction bookkeeping. -/
theorem shiftZ_mem_Gam {b n : ℕ} (x y : Fin (n + 1) → ℤ) (hd1 : 1 ≤ b + 1) (i : Fin (n + 1))
    {w : Mon b n → ℤ} (hw : w ∈ Gam b n x y) : shiftZ (b + 1) i w ∈ Gam (b + 1) n x y := by
  rw [Work.HP.MDBasic.mem_Gam_iff] at hw ⊢
  constructor
  · show (∑ m : Mon (b + 1) n, shiftZ (b + 1) i w m * veronese (b + 1) n x m) = 0
    rw [sum_veronese_shiftZ (d := b + 1) hd1 i w x,
      show (∑ β : Mon ((b + 1) - 1) n, w β * veronese ((b + 1) - 1) n x β)
        = formEval b n w x from rfl, hw.1, mul_zero]
  · show (∑ m : Mon (b + 1) n, shiftZ (b + 1) i w m * veronese (b + 1) n y m) = 0
    rw [sum_veronese_shiftZ (d := b + 1) hd1 i w y,
      show (∑ β : Mon ((b + 1) - 1) n, w β * veronese ((b + 1) - 1) n y β)
        = formEval b n w y from rfl, hw.2, mul_zero]

/-- The shift of an integer vector is the realification of the integer shift. -/
theorem shift1_intCastPi {b n : ℕ} (hd1 : 1 ≤ b + 1) (i : Fin (n + 1)) (w : Mon b n → ℤ) :
    shift1 (b + 1) hd1 i (intCastPi w) = intCastPi (shiftZ (b + 1) i w) := by
  have h1 : shift1 (b + 1) hd1 i (fun β => (w β : ℝ))
      = fun m => ((shiftZ (b + 1) i w m : ℤ) : ℝ) := by
    rw [shift1_coe (d := b + 1) (hd := hd1) (i := i) (u := w)]
  rw [show intCastPi w = (fun β => (w β : ℝ)) from rfl]
  exact h1.trans rfl



/-! ## The `Ψ`-lift, inlined

The following material proves `VR_eq_iSup_shift` (the span statement
`Σᵢ Xᵢ·VR(d-1) = VR(d)`).  It was proved in the sibling module
`Submission/Work/HP/Sig2/VR_eq_iSup_shift.lean` and its helper files, which import this
one (they need `Mon`, `evalLin`, `shift1`, `VR`); since that module therefore cannot be
imported here, the material is reproduced inside the namespace `LiftAux` (which also keeps
the names distinct from the originals). -/

namespace LiftAux

-- (inlined from `Submission/Work/HP/Sig2/VRDefs.lean`)
open Work.HP

variable {n : ℕ}

/-- The partial Euler (derivative) operator: `(D_i F) β = ((β i : ℕ) + 1) * F (β + e_i) / d`.

This is `1/d` times the `i`-th formal partial derivative of the degree-`d` form with coefficient
vector `F`; it satisfies Euler's identity `∑ i, X_i · (D_i F) = F`
(see `Work.HP.Sig2.eulerD_sum_shift1`). -/
def eulerD (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) :
    (Mon d n → ℝ) →ₗ[ℝ] (Mon (d - 1) n → ℝ) where
  toFun F := fun β => ((β.1 i : ℕ) + 1 : ℝ) * F (monAddE d hd i β) / (d : ℝ)
  map_add' F G := by
    funext β
    simp only [Pi.add_apply]
    ring
  map_smul' c F := by
    funext β
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem eulerD_apply (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (F : Mon d n → ℝ)
    (β : Mon (d - 1) n) :
    eulerD d hd i F β = ((β.1 i : ℕ) + 1 : ℝ) * F (monAddE d hd i β) / (d : ℝ) := rfl

/-- The Veronese map commutes with the coercion `ℤ → ℝ`. -/
theorem veronese_intCastR (d n : ℕ) (x : Fin (n + 1) → ℤ) (m : Mon d n) :
    veronese d n (fun i => (x i : ℝ)) m = ((veronese d n x m : ℤ) : ℝ) := by
  simp only [veronese]
  push_cast
  rfl

/-- Evaluation at `x` of the shifted vector `X_i · u` is `x_i` times the evaluation of `u`. -/
theorem evalLin_shift1 {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (i : Fin (n + 1)) (u : Mon (d - 1) n → ℝ)
    (x : Fin (n + 1) → ℤ) :
    evalLin d n x (shift1 d hd i u) = (x i : ℝ) * evalLin (d - 1) n x u := by
  have h1 : evalLin d n x (shift1 d hd i u)
      = ∑ m : Mon d n, shift1 d hd i u m * veronese d n (fun j => (x j : ℝ)) m := by
    simp only [evalLin]
    exact Finset.sum_congr rfl (fun m _ => by rw [veronese_intCastR])
  have h2 : evalLin (d - 1) n x u
      = ∑ m : Mon (d - 1) n, u m * veronese (d - 1) n (fun j => (x j : ℝ)) m := by
    simp only [evalLin]
    exact Finset.sum_congr rfl (fun m _ => by rw [veronese_intCastR])
  rw [h1, h2, sum_veronese_shift1 d hd i u (fun j => (x j : ℝ))]

/-- `ℤ`-linear independence of integer vectors implies `ℝ`-linear independence of their images. -/
theorem real_linearIndependent {n : ℕ} (x y : Fin (n + 1) → ℤ)
    (h : LinearIndependent ℤ ![x, y]) :
    LinearIndependent ℝ ![(fun i => (x i : ℝ)), (fun i => (y i : ℝ))] := by
  have h1 : LinearIndependent ℝ (fun i : Fin 2 => ((algebraMap ℤ ℝ) ∘ ![x, y] i)) :=
    (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (v := ![x, y])).mpr h
  have h2 : (fun i : Fin 2 => ((algebraMap ℤ ℝ) ∘ ![x, y] i))
      = ![(fun i => (x i : ℝ)), (fun i => (y i : ℝ))] := by
    funext i
    fin_cases i <;> rfl
  rwa [h2] at h1

-- (inlined from `Submission/Work/HP/Sig2/eulerD_sum_shift1.lean`)
open Work.HP

/-- Euler's identity for the partial Euler operators `eulerD d hd i` and the multiplications by
`X_i` (`shift1 d hd i`):  `∑ i, X_i · (D_i F) = F`, i.e. `∑ i, shift1 d hd i (eulerD d hd i F) = F`.

Both sides are functions on `Mon d n`; at a monomial `m` the `i`-th term is `m_i · F m / d` when
`m_i ≥ 1` and `0` otherwise, and `∑ i, m_i = d`. -/
theorem eulerD_sum_shift1 {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (F : Mon d n → ℝ) :
    ∑ i : Fin (n + 1), shift1 d hd i (eulerD d hd i F) = F := by
  funext m
  rw [Finset.sum_apply]
  have hterm : ∀ i : Fin (n + 1),
      shift1 d hd i (eulerD d hd i F) m = (m.1 i : ℝ) * F m / (d : ℝ) := by
    intro i
    rw [shift1_apply]
    by_cases h : 1 ≤ (m.1 i : ℕ)
    · rw [dif_pos h, eulerD_apply, monAddE_monSubE d hd i m h]
      have hsub : (((monSubE d i m h).1 i : ℕ)) = (m.1 i : ℕ) - 1 := by
        simp [monSubE_apply]
      have hcast : (((monSubE d i m h).1 i : ℕ) + 1 : ℝ) = (m.1 i : ℝ) := by
        rw [hsub]
        have h1 : (((m.1 i : ℕ) - 1 : ℕ) : ℝ) = (m.1 i : ℝ) - 1 := by
          rw [Nat.cast_sub h, Nat.cast_one]
        rw [h1]; ring
      rw [hcast]
    · rw [dif_neg h]
      have hz : (m.1 i : ℕ) = 0 := by omega
      simp [hz]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hsum : ∑ i : Fin (n + 1), (m.1 i : ℝ) = (d : ℝ) := by
    have h := congrArg (fun s : ℕ => (s : ℝ)) m.2
    simpa [Nat.cast_sum] using h
  rw [← Finset.sum_div, ← Finset.sum_mul, hsum]
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  field_simp

-- (inlined from `Submission/Work/HP/Sig2/exists_form_two_values.lean`)
open Work.HP

/-- **Two independent functionals attain any pair of values.**  If `f g : V →ₗ[ℝ] ℝ` are linearly
independent then for every `a b : ℝ` there is `C : V` with `f C = a` and `g C = b`.

(Equivalently: the map `C ↦ (f C, g C)` is surjective, since otherwise its image — a proper
subspace of `ℝ²` — would be contained in a line, giving a nontrivial relation `cf + dg = 0`.  The
proof below is the direct one: choose `v₀` with `f v₀ = 1` and write `w = g v₀`; if `g` agreed with
`w · f` on all of `V` then `g - w · f = 0` would be a nontrivial relation, so there is `u` with
`g u ≠ w · f u`; then `u₀ = u - (f u) · v₀` satisfies `f u₀ = 0` and `g u₀ = g u - w · f u ≠ 0`,
and `C = a · v₀ + ((b - a w)/(g u₀)) · u₀` works.) -/
theorem exists_pair_values_of_linearIndependent {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f g : V →ₗ[ℝ] ℝ) (h : LinearIndependent ℝ ![f, g]) (a b : ℝ) :
    ∃ C : V, f C = a ∧ g C = b := by
  rw [LinearIndependent.pair_iff] at h
  have hf : f ≠ 0 := by
    intro h0
    exact one_ne_zero (h 1 0 (by rw [h0]; simp)).1
  -- a vector on which `f` does not vanish, rescaled so that `f v₀ = 1`
  obtain ⟨v, hv⟩ : ∃ v : V, f v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf (LinearMap.ext hc)
  obtain ⟨v₀, hv₀f⟩ : ∃ v₀ : V, f v₀ = 1 :=
    ⟨(f v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]⟩
  set w : ℝ := g v₀ with hw
  -- `g` does not agree with `w · f` on all of `V` (else they would be dependent)
  have hgu : ∃ u : V, g u - w * f u ≠ 0 := by
    by_contra hc
    push Not at hc
    have hgf : g = w • f := LinearMap.ext fun u => by
      have hu := hc u
      rw [sub_eq_zero] at hu
      rw [hu, LinearMap.smul_apply, smul_eq_mul]
    have h1 : (-w) • f + (1 : ℝ) • g = 0 := by
      rw [hgf]
      ext x
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul]
      ring
    exact one_ne_zero (h (-w) 1 h1).2
  obtain ⟨u, hu⟩ := hgu
  -- `u₀` lies in `ker f` and still separates `g` from `w · f`
  obtain ⟨u₀, hu₀f, hu₀g⟩ : ∃ u₀ : V, f u₀ = 0 ∧ g u₀ = g u - w * f u :=
    ⟨u - (f u) • v₀,
      by rw [map_sub, map_smul, hv₀f, smul_eq_mul, mul_one, sub_self],
      by rw [map_sub, map_smul, smul_eq_mul, ← hw]; ring⟩
  refine ⟨a • v₀ + ((b - a * w) / (g u - w * f u)) • u₀, ?_, ?_⟩
  · rw [map_add, map_smul, map_smul, hv₀f, hu₀f, smul_eq_mul, smul_eq_mul]
    ring
  · rw [map_add, map_smul, map_smul, ← hw, hu₀g, smul_eq_mul, smul_eq_mul,
      div_mul_cancel₀ _ hu]
    ring

/-- Independence of `x, y` over `ℝ` implies independence of the evaluation functionals
`evalLin k n x`, `evalLin k n y` (for `k ≥ 1`).

A relation `α · evalLin x + β · evalLin y = 0` evaluated at the monomial `Pi.single m 1` gives
`α · ν(x)_m + β · ν(y)_m = 0` for every `m : Mon k n`.  If `α ≠ 0` this is the proportionality
`ν(x) = (-β/α) ν(y)`, and `veronese_proportional` (with `α ≠ 0` forcing `β ≠ 0`) turns it into
`x = μ • y`, contradicting independence. -/
theorem linInd_evalLin_of_real {n k : ℕ} (hk : 1 ≤ k) (x y : Fin (n + 1) → ℤ)
    (hxy : LinearIndependent ℝ ![(fun i => (x i : ℝ)), (fun i => (y i : ℝ))]) :
    LinearIndependent ℝ ![evalLin k n x, evalLin k n y] := by
  set xr : Fin (n + 1) → ℝ := fun i => (x i : ℝ) with hxr
  set yr : Fin (n + 1) → ℝ := fun i => (y i : ℝ) with hyr
  rw [LinearIndependent.pair_iff] at hxy ⊢
  have hx0 : xr ≠ 0 := fun h0 => one_ne_zero (hxy 1 0 (by rw [h0]; simp)).1
  have hy0 : yr ≠ 0 := fun h0 => one_ne_zero (hxy 0 1 (by rw [h0]; simp)).2
  have hnx : veronese k n xr ≠ 0 := veronese_ne_zero k n hk hx0
  have hny : veronese k n yr ≠ 0 := veronese_ne_zero k n hk hy0
  intro α β hαβ
  have hcoe : ∀ m : Mon k n, α * veronese k n xr m + β * veronese k n yr m = 0 := by
    intro m
    have h := congrArg (fun (φ : (Mon k n → ℝ) →ₗ[ℝ] ℝ) => φ (Pi.single m 1)) hαβ
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply] at h
    rw [evalLin_single, evalLin_single, smul_eq_mul, smul_eq_mul] at h
    rw [← veronese_intCastR k n x m, ← veronese_intCastR k n y m] at h
    simpa only [← hxr, ← hyr] using h
  -- the proportionality `ν(x) = λ · ν(y)` once the coefficient of `ν(y)` is nonzero
  have keyβ : ∀ {α β : ℝ}, (∀ m, α * veronese k n xr m + β * veronese k n yr m = 0) → β ≠ 0 →
      ∃ μ : ℝ, xr = μ • yr := by
    intro α β hc hβ
    by_cases hα : α = 0
    · have hz : veronese k n yr = 0 := by
        funext m
        have hm := hc m
        rw [hα, zero_mul, zero_add] at hm
        exact (mul_eq_zero.mp hm).resolve_left hβ
      exact absurd hz hny
    · have hprop : ∀ m : Mon k n, veronese k n xr m = (-β / α) * veronese k n yr m := by
        intro m
        have hm := hc m
        have h1 : α * veronese k n xr m = -(β * veronese k n yr m) := by linarith
        rw [show (-β / α) * veronese k n yr m = -(β * veronese k n yr m) / α by ring,
          eq_div_iff hα]
        linarith
      obtain ⟨μ, hμ⟩ := veronese_proportional k n hk xr yr hy0
        (div_ne_zero (neg_ne_zero.mpr hβ) hα) hprop
      exact ⟨μ, hμ⟩
  have keyα : ∀ {α β : ℝ}, (∀ m, α * veronese k n xr m + β * veronese k n yr m = 0) → α ≠ 0 →
      ∃ μ : ℝ, xr = μ • yr := by
    intro α β hc hα
    by_cases hβ : β = 0
    · have hz : veronese k n xr = 0 := by
        funext m
        have hm := hc m
        rw [hβ, zero_mul, add_zero] at hm
        exact (mul_eq_zero.mp hm).resolve_left hα
      exact absurd hz hnx
    · have hprop : ∀ m : Mon k n, veronese k n xr m = (-β / α) * veronese k n yr m := by
        intro m
        have hm := hc m
        have h1 : α * veronese k n xr m = -(β * veronese k n yr m) := by linarith
        rw [show (-β / α) * veronese k n yr m = -(β * veronese k n yr m) / α by ring,
          eq_div_iff hα]
        linarith
      obtain ⟨μ, hμ⟩ := veronese_proportional k n hk xr yr hy0
        (div_ne_zero (neg_ne_zero.mpr hβ) hα) hprop
      exact ⟨μ, hμ⟩
  constructor
  · by_contra hα
    obtain ⟨μ, hμ⟩ := keyα hcoe hα
    exact one_ne_zero (hxy 1 (-μ) (by rw [hμ]; simp)).1
  · by_contra hβ
    obtain ⟨μ, hμ⟩ := keyβ hcoe hβ
    exact one_ne_zero (hxy 1 (-μ) (by rw [hμ]; simp)).1

theorem exists_form_two_values {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (x y : Fin (n + 1) → ℤ)
    (hxy : LinearIndependent ℝ ![(fun i => (x i : ℝ)), (fun i => (y i : ℝ))]) (a b : ℝ) :
    ∃ C : Mon k n → ℝ, evalLin k n x C = a ∧ evalLin k n y C = b :=
  exists_pair_values_of_linearIndependent (evalLin k n x) (evalLin k n y)
    (linInd_evalLin_of_real hk x y hxy) a b

-- (inlined from `Submission/Work/HP/Sig2/shift1_shift1_swap.lean`)
/-- The two ways of multiplying a degree-`(d-2)` coefficient vector by `X_i` and then by `X_j`
(whence giving a degree-`d` vector) agree: `X_i (X_j c) = X_j (X_i c)`. -/
theorem shift1_shift1_swap {n : ℕ} (d : ℕ) (hd : 2 ≤ d) (i j : Fin (n + 1))
    (c : Mon (d - 2) n → ℝ) :
    shift1 d (by omega) i (shift1 (d - 1) (by omega) j c)
      = shift1 d (by omega) j (shift1 (d - 1) (by omega) i c) := by
  funext m
  simp only [shift1_apply]
  -- Iterated `monSubE` (removing `e_i` and then `e_j`) is symmetric in `i` and `j`.
  have core : ∀ (hi : 1 ≤ (m.1 i : ℕ)) (hj : 1 ≤ (m.1 j : ℕ))
      (h1 : 1 ≤ ((monSubE d i m hi).1 j : ℕ)) (h2 : 1 ≤ ((monSubE d j m hj).1 i : ℕ)),
      monSubE (d - 1) j (monSubE d i m hi) h1 = monSubE (d - 1) i (monSubE d j m hj) h2 := by
    intro hi hj h1 h2
    apply Subtype.ext
    funext k
    apply Fin.ext
    simp only [monSubE_apply]
    rw [tsub_right_comm]
  by_cases hij : i = j
  · subst hij; rfl
  · by_cases hmi : 1 ≤ (m.1 i : ℕ)
    · by_cases hmj : 1 ≤ (m.1 j : ℕ)
      · have h1 : 1 ≤ ((monSubE d i m hmi).1 j : ℕ) := by
          rw [monSubE_apply]; rw [if_neg (Ne.symm hij), tsub_zero]; exact hmj
        have h2 : 1 ≤ ((monSubE d j m hmj).1 i : ℕ) := by
          rw [monSubE_apply]; rw [if_neg hij, tsub_zero]; exact hmi
        rw [dif_pos hmi, dif_pos hmj, dif_pos h1, dif_pos h2, core hmi hmj h1 h2]
      · have h1 : ¬ (1 ≤ ((monSubE d i m hmi).1 j : ℕ)) := by
          rw [monSubE_apply]; rw [if_neg (Ne.symm hij), tsub_zero]; exact hmj
        rw [dif_pos hmi, dif_neg hmj, dif_neg h1]
    · rw [dif_neg hmi]
      by_cases hmj : 1 ≤ (m.1 j : ℕ)
      · have h2 : ¬ (1 ≤ ((monSubE d j m hmj).1 i : ℕ)) := by
          rw [monSubE_apply]; rw [if_neg hij, tsub_zero]; exact hmi
        rw [dif_pos hmj, dif_neg h2]
      · rw [dif_neg hmj]

-- (inlined from `Submission/Work/HP/Sig2/VR_eq_iSup_shift.lean`)
open Work.HP

variable {n : ℕ}

/-- For a nonzero real vector `x` and a vector `p` orthogonal to it there is a skew-symmetric
matrix `A` with `A x = -p`.  Explicitly `A i j = (x i * p j - p i * x j) / ‖x‖²`. -/
theorem exists_skew_of_orthogonal {n : ℕ} (x p : Fin (n + 1) → ℝ) (hx : x ≠ 0)
    (h : ∑ j, x j * p j = 0) :
    ∃ A : Fin (n + 1) → Fin (n + 1) → ℝ, (∀ i j, A j i = -A i j) ∧
      (∀ i, ∑ j, A i j * x j = -p i) := by
  set S := ∑ j, x j ^ 2 with hS
  have hSpos : 0 < S := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    refine lt_of_lt_of_le (sq_pos_of_ne_zero hj) ?_
    rw [hS]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ j)
  have hSne : S ≠ 0 := ne_of_gt hSpos
  refine ⟨fun i j => (x i * p j - p i * x j) / S, ?_, ?_⟩
  · intro i j
    field_simp <;> try ring
  · intro i
    have hpx : ∑ j, p j * x j = 0 := by
      rw [← h]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    have h1 : ∀ j, (x i * p j - p i * x j) / S * x j
        = (x i * (p j * x j) - p i * x j ^ 2) / S := by
      intro j
      ring_nf
    rw [Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.sum_div, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hpx, ← hS]
    field_simp <;> try ring

/-- Euler's identity on values: `∑ i, x_i · (D_i F)(x) = F(x)`. -/
theorem eulerD_evalLin_sum {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (F : Mon d n → ℝ)
    (x : Fin (n + 1) → ℤ) :
    ∑ i : Fin (n + 1), (x i : ℝ) * evalLin (d - 1) n x (eulerD d hd i F)
      = evalLin d n x F := by
  conv_rhs => rw [← eulerD_sum_shift1 d hd F]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => (evalLin_shift1 d hd i (eulerD d hd i F) x).symm)

theorem VR_eq_iSup_shift (d : ℕ) (hd : 3 ≤ d) (n : ℕ) (x y : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y]) :
    VR d n x y
      = ⨆ i : Fin (n + 1), Submodule.map (shift1 d (by omega) i) (VR (d - 1) n x y) := by
  have hd1 : 1 ≤ d := by omega
  have hd1' : 1 ≤ d - 1 := by omega
  have hd2 : 2 ≤ d := by omega
  have hd3 : 1 ≤ d - 2 := by omega
  -- inputs from sibling files
  have hform : ∀ (k : ℕ) (hk : 1 ≤ k) (a b : ℝ),
      ∃ C : Mon k n → ℝ, evalLin k n x C = a ∧ evalLin k n y C = b := by
    intro k hk a b
    exact exists_form_two_values k hk x y (real_linearIndependent x y hxy) a b
  have hswap : ∀ (i j : Fin (n + 1)) (cc : Mon (d - 2) n → ℝ),
      shift1 d hd1 i (shift1 (d - 1) hd1' j cc)
        = shift1 d hd1 j (shift1 (d - 1) hd1' i cc) := by
    intro i j cc
    exact shift1_shift1_swap d hd2 i j cc
  apply le_antisymm
  · -- `VR d ⊆ Σᵢ Xᵢ · VR (d-1)`
    intro F hF
    rw [VR, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker] at hF
    have hpx : ∑ j, (x j : ℝ) * evalLin (d - 1) n x (eulerD d hd1 j F) = 0 := by
      rw [eulerD_evalLin_sum d hd1 F x, hF.1]
    have hqy : ∑ j, (y j : ℝ) * evalLin (d - 1) n y (eulerD d hd1 j F) = 0 := by
      rw [eulerD_evalLin_sum d hd1 F y, hF.2]
    have hx0' : (fun i => (x i : ℝ)) ≠ 0 := by
      intro hz
      refine isPrim_ne_zero hx (funext fun i => ?_)
      exact Int.cast_eq_zero.mp (congrFun hz i)
    have hy0' : (fun i => (y i : ℝ)) ≠ 0 := by
      intro hz
      refine isPrim_ne_zero hy (funext fun i => ?_)
      exact Int.cast_eq_zero.mp (congrFun hz i)
    have hxyℝ : LinearIndependent ℝ ![(fun i => (x i : ℝ)), (fun i => (y i : ℝ))] :=
      real_linearIndependent x y hxy
    obtain ⟨A, hAskew, hAx⟩ := exists_skew_of_orthogonal (fun i => (x i : ℝ))
      (fun i => evalLin (d - 1) n x (eulerD d hd1 i F)) hx0' hpx
    obtain ⟨B, hBskew, hBy⟩ := exists_skew_of_orthogonal (fun i => (y i : ℝ))
      (fun i => evalLin (d - 1) n y (eulerD d hd1 i F)) hy0' hqy
    have hAii : ∀ i, A i i = 0 := by
      intro i
      have h1 := hAskew i i
      linarith
    have hBii : ∀ i, B i i = 0 := by
      intro i
      have h1 := hBskew i i
      linarith
    obtain ⟨P, hPx, hPy⟩ := hform (d - 2) hd3 1 0
    obtain ⟨Q, hQx, hQy⟩ := hform (d - 2) hd3 0 1
    set c : Fin (n + 1) → Fin (n + 1) → (Mon (d - 2) n → ℝ) :=
      fun i j => A i j • P + B i j • Q with hc
    have hcx : ∀ i j, evalLin (d - 2) n x (c i j) = A i j := by
      intro i j
      rw [hc]
      simp only [map_add, map_smul, hPx, hQx, smul_eq_mul, mul_one, mul_zero, add_zero]
    have hcy : ∀ i j, evalLin (d - 2) n y (c i j) = B i j := by
      intro i j
      rw [hc]
      simp only [map_add, map_smul, hPy, hQy, smul_eq_mul, mul_one, mul_zero, zero_add]
    have hcanti : ∀ i j, c j i = - c i j := by
      intro i j
      simp only [hc]
      rw [hAskew i j, hBskew i j, neg_smul, neg_smul, neg_add_rev, add_comm]
    set r : Fin (n + 1) → (Mon (d - 1) n → ℝ) :=
      fun i => ∑ j, shift1 (d - 1) hd1' j (c i j) with hr
    have hu_mem : ∀ i, eulerD d hd1 i F + r i ∈ VR (d - 1) n x y := by
      intro i
      rw [mem_VR]
      constructor
      · show evalLin (d - 1) n x (eulerD d hd1 i F + r i) = 0
        rw [map_add, hr, map_sum]
        rw [Finset.sum_congr rfl (fun j _ => evalLin_shift1 (d - 1) hd1' j (c i j) x)]
        have hst : ∀ j : Fin (n + 1),
            (x j : ℝ) * evalLin (d - 1 - 1) n x (c i j) = A i j * (x j : ℝ) := by
          intro j
          show (x j : ℝ) * evalLin (d - 2) n x (c i j) = A i j * (x j : ℝ)
          rw [hcx i j, mul_comm]
        rw [Finset.sum_congr rfl (fun j _ => hst j), hAx i]
        exact add_neg_cancel _
      · show evalLin (d - 1) n y (eulerD d hd1 i F + r i) = 0
        rw [map_add, hr, map_sum]
        rw [Finset.sum_congr rfl (fun j _ => evalLin_shift1 (d - 1) hd1' j (c i j) y)]
        have hst : ∀ j : Fin (n + 1),
            (y j : ℝ) * evalLin (d - 1 - 1) n y (c i j) = B i j * (y j : ℝ) := by
          intro j
          show (y j : ℝ) * evalLin (d - 2) n y (c i j) = B i j * (y j : ℝ)
          rw [hcy i j, mul_comm]
        rw [Finset.sum_congr rfl (fun j _ => hst j), hBy i]
        exact add_neg_cancel _
    have hsum : ∑ i, shift1 d hd1 i (eulerD d hd1 i F + r i) = F := by
      have hsplit : ∀ i, shift1 d hd1 i (eulerD d hd1 i F + r i)
          = shift1 d hd1 i (eulerD d hd1 i F)
            + ∑ j, shift1 d hd1 i (shift1 (d - 1) hd1' j (c i j)) := by
        intro i
        rw [hr, map_add, map_sum]
      rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
        eulerD_sum_shift1 d hd1 F]
      have htel : ∑ i, ∑ j, shift1 d hd1 i (shift1 (d - 1) hd1' j (c i j)) = 0 := by
        have hpt : ∀ i j, shift1 d hd1 j (shift1 (d - 1) hd1' i (c j i))
            = - shift1 d hd1 i (shift1 (d - 1) hd1' j (c i j)) := by
          intro i j
          rw [hcanti i j]
          simp only [map_neg]
          rw [neg_inj]
          exact (hswap i j (c i j)).symm
        have hA : (∑ i, ∑ j, shift1 d hd1 i (shift1 (d - 1) hd1' j (c i j)))
            = - (∑ i, ∑ j, shift1 d hd1 i (shift1 (d - 1) hd1' j (c i j))) := by
          have hstep : (∑ i, ∑ j, shift1 d hd1 i (shift1 (d - 1) hd1' j (c i j)))
              = ∑ i, ∑ j, shift1 d hd1 j (shift1 (d - 1) hd1' i (c j i)) := by
            rw [Finset.sum_comm]
          have hstep2 : (∑ i, ∑ j, shift1 d hd1 j (shift1 (d - 1) hd1' i (c j i)))
              = - (∑ i, ∑ j, shift1 d hd1 i (shift1 (d - 1) hd1' j (c i j))) := by
            rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
            simp only [Finset.sum_neg_distrib]
          exact hstep.trans hstep2
        exact funext fun m => by
          show (∑ i, ∑ j, shift1 d hd1 i (shift1 (d - 1) hd1' j (c i j))) m = 0
          have h2 := congrFun hA m
          simp only [Pi.neg_apply] at h2
          linarith
      rw [htel, add_zero]
    rw [← hsum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact le_iSup (fun i => Submodule.map (shift1 d (by omega) i) (VR (d - 1) n x y)) i
      (Submodule.mem_map_of_mem (hu_mem i))
  · -- `Σᵢ Xᵢ · VR (d-1) ⊆ VR d`
    refine iSup_le (fun i => ?_)
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    exact shift1_mem_VR x y (by omega) i hv

end LiftAux

/-! ## The shared ingredients (proved in sibling files)

These three statements are delegated lemmas living in sibling files of this directory; while they
are in flight the statements are repeated here.  When they are available they are imported and
these copies are deleted.

* `transference_extreme` : Banaszczyk's transference theorem (extreme cases), `Lat.transference`;
* `GamTwo_dual_lam1` : the paper's two-case lower bound for `λ₁(Γ_{x,y}*)` at `d = 2`;
* `VR_eq_iSup_shift` : the `Ψ`-lift, `Σᵢ Xᵢ·VR(d-1) = VR(d)`.
-/







/-! ## Elementary arithmetic -/

private lemma min_mul_max_inv (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : min a b * max a⁻¹ b⁻¹ = 1 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left ((inv_le_inv₀ hb ha).mpr h), mul_inv_cancel₀ (ne_of_gt ha)]
  · rw [min_eq_right h, max_eq_right ((inv_le_inv₀ ha hb).mpr h), mul_inv_cancel₀ (ne_of_gt hb)]

private lemma B_mul_muXY (n : ℕ) (x y : Fin (n + 1) → ℤ) (hx : 0 < eNorm x) (hy : 0 < eNorm y)
    (hd2 : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
    (hd3 : 0 < dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) :
    (1 / 3 * min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
          dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
        (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))) * muXY n x y
      = (n : ℝ) ^ 2 := by
  have hA : 0 < dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
      dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) := div_pos hd3 hd2
  have hB : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y) :=
    div_pos (pow_pos hd2 2) (mul_pos hx hy)
  have hkey := min_mul_max_inv (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
      dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
    (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y)) hA hB
  have hμ : muXY n x y = 3 * (n : ℝ) ^ 2 *
      max (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) / dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))⁻¹
        (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))⁻¹ := by
    rw [muXY]
    simp only [inv_div]
  rw [hμ]
  calc (1 / 3 * min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
          dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
        (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))) *
        (3 * (n : ℝ) ^ 2 * max (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
            dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))⁻¹
          (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))⁻¹)
      = (n : ℝ) ^ 2 * (min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
            dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
          (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y)) *
          max (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
            dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))⁻¹
            (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))⁻¹) := by
        ring
    _ = (n : ℝ) ^ 2 := by rw [hkey]; ring

lemma muXY_pos_of (n : ℕ) (x y : Fin (n + 1) → ℤ) (hx : 0 < eNorm x) (hy : 0 < eNorm y)
    (hd2 : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
    (hd3 : 0 < dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) : 0 ≤ muXY n x y := by
  have hB : 0 < 1 / 3 * min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
      dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
      (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y)) :=
    mul_pos (by norm_num)
      (lt_min (div_pos hd3 hd2) (div_pos (pow_pos hd2 2) (mul_pos hx hy)))
  have hid := B_mul_muXY n x y hx hy hd2 hd3
  nlinarith [sq_nonneg (n : ℝ), hid]

private lemma one_le_dmin_two_pair (n : ℕ) (x y : Fin (n + 1) → ℤ)
    (h : LinearIndependent ℤ ![x, y]) : 1 ≤ dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) := by
  set L : Submodule ℤ (Fin (n + 1) → ℤ) := Submodule.span ℤ (Set.range ![x, y]) with hL
  have hrk : rk L = 2 := by
    rw [hL, rk, finrank_span_eq_card h, Fintype.card_fin]
  have hsub : ({x, y} : Set (Fin (n + 1) → ℤ)) ⊆ L := by
    rintro z (rfl | rfl)
    · exact Submodule.subset_span ⟨0, by simp⟩
    · exact Submodule.subset_span ⟨1, by simp⟩
  rw [dmin]
  refine le_csInf ⟨detL L, L, hrk, hsub, rfl⟩ ?_
  rintro D ⟨L', -, -, rfl⟩
  exact Work.HP.Lat.detL_ge_one L'

private lemma one_le_dmin_three_pair (n : ℕ) (x y : Fin (n + 1) → ℤ)
    (h : LinearIndependent ℤ ![x, y]) (hcard : 3 ≤ Fintype.card (Fin (n + 1))) :
    1 ≤ dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) := by
  obtain ⟨L, hLrk, hxL, hyL⟩ := Work.HP.Lat.exists_rk_three x y h hcard
  have hsub : ({x, y} : Set (Fin (n + 1) → ℤ)) ⊆ L := by
    rintro z (rfl | rfl)
    · exact hxL
    · exact hyL
  rw [dmin]
  refine le_csInf ⟨detL L, L, hLrk, hsub, rfl⟩ ?_
  rintro D ⟨L', -, -, rfl⟩
  exact Work.HP.Lat.detL_ge_one L'

lemma NN_two_sub_two_le (n : ℕ) : NN 2 n - 2 ≤ n ^ 2 := by
  have h2 : NN 2 n = (n + 2) * (n + 1) / 2 := by
    rw [NN, Work.HP.Lat.card_Mon, Nat.choose_two_right, show (n + 2) - 1 = n + 1 by omega]
  rw [h2]
  rcases lt_or_ge n 3 with hlt | hge
  · interval_cases n <;> norm_num
  · have h3 : (n + 2) * (n + 1) ≤ 2 * (n ^ 2 + 2) := by
      have : (0 : ℤ) ≤ ((n : ℤ) - 1) * ((n : ℤ) - 2) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
    have h4 : (n + 2) * (n + 1) / 2 ≤ n ^ 2 + 2 := Nat.div_le_of_le_mul h3
    omega

/-! ## `lam` versus `lamR`, and the rank of a realification -/

theorem lam_eq_lamR_realify {ι : Type*} [Fintype ι] (Λ : Submodule ℤ (ι → ℤ)) (i : ℕ) :
    lam Λ i = lamR (realify Λ) i := by
  rw [lam, lamR]
  exact congrArg sInf (Work.HP.HP3.lamSet_eq Λ i)

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

theorem finrank_span_realify_Gam (d n : ℕ) (x y : Fin (n + 1) → ℤ)
    (h : LinearIndependent ℤ ![veronese d n x, veronese d n y]) :
    Module.finrank ℝ (Submodule.span ℝ (realify (Gam d n x y) : Set (Mon d n → ℝ)))
      = NN d n - 2 := by
  have hset : ((realify (Gam d n x y) : Submodule ℤ (Mon d n → ℝ)) : Set (Mon d n → ℝ))
      = intCastPi '' ((Gam d n x y) : Set (Mon d n → ℤ)) := rfl
  rw [hset, Work.HP.Vero.finrank_span_image_intCastPi]
  exact (gam_rank_det d n x y h).1


/-- `muXY` is nonnegative. -/
private theorem muXY_nonneg (n : ℕ) (hn : 2 ≤ n) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x)
    (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y]) : 0 ≤ muXY n x y := by
  have hxpos : 0 < eNorm x := eNorm_pos_iff.mpr (isPrim_ne_zero hx)
  have hypos : 0 < eNorm y := eNorm_pos_iff.mpr (isPrim_ne_zero hy)
  have hd2 : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) :=
    lt_of_lt_of_le one_pos (one_le_dmin_two_pair n x y hxy)
  have hcard3 : 3 ≤ Fintype.card (Fin (n + 1)) := by simp; omega
  have hd3 : 0 < dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) :=
    lt_of_lt_of_le one_pos (one_le_dmin_three_pair n x y hxy hcard3)
  exact muXY_pos_of n x y hxpos hypos hd2 hd3

/-! ## The `d = 2` step with the sharp constant -/

theorem ne_of_linInd {m : ℕ} (x y : Fin (m + 1) → ℤ) (h : LinearIndependent ℤ ![x, y]) :
    x ≠ y := by
  intro hxy
  have h2 := (Fintype.linearIndependent_iff.mp h) ![1, -1]
  have hsum : (∑ i, (![1, -1] : Fin 2 → ℤ) i • (![x, y] i)) = 0 := by
    simp [Fin.sum_univ_two, hxy]
  have := h2 hsum 0
  simp at this

theorem ne_neg_of_linInd {m : ℕ} (x y : Fin (m + 1) → ℤ) (h : LinearIndependent ℤ ![x, y]) :
    x ≠ -y := by
  intro hxy
  have h2 := (Fintype.linearIndependent_iff.mp h) ![1, 1]
  have hsum : (∑ i, (![1, 1] : Fin 2 → ℤ) i • (![x, y] i)) = 0 := by
    simp [Fin.sum_univ_two, hxy]
  have := h2 hsum 0
  simp at this

theorem linInd_evalLin_of (d n : ℕ) (x y : Fin (n + 1) → ℤ)
    (hν : LinearIndependent ℤ ![veronese d n x, veronese d n y]) :
    LinearIndependent ℝ ![evalLin d n x, evalLin d n y] := by
  refine linInd_evalLin (d := d) (n := n) x y ?_
  have h1 := Work.HP.Vero.linInd_intCastPi hν
  have h2 : (fun j : Fin 2 => intCastPi (![veronese d n x, veronese d n y] j))
      = ![(fun m => ((veronese d n x m : ℤ) : ℝ)),
          (fun m => ((veronese d n y m : ℤ) : ℝ))] := by
    funext j
    fin_cases j <;> rfl
  rwa [h2] at h1

theorem finrank_VR (d n : ℕ) (x y : Fin (n + 1) → ℤ)
    (hν : LinearIndependent ℤ ![veronese d n x, veronese d n y]) :
    Module.finrank ℝ (VR d n x y) = NN d n - 2 := by
  have h := finrank_VR_add_two d n x y (linInd_evalLin_of d n x y hν)
  omega

theorem lamR_Gam_two_le_muXY (n : ℕ) (hn : 2 ≤ n) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x)
    (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y]) :
    lamR (realify (Gam 2 n x y)) (NN 2 n - 2) ≤ muXY n x y := by
  have hν : LinearIndependent ℤ ![veronese 2 n x, veronese 2 n y] :=
    nu_indep 2 n (by norm_num) x y hx hy (ne_of_linInd x y hxy) (ne_neg_of_linInd x y hxy)
  have hxpos : 0 < eNorm x := eNorm_pos_iff.mpr (isPrim_ne_zero hx)
  have hypos : 0 < eNorm y := eNorm_pos_iff.mpr (isPrim_ne_zero hy)
  have hd2 : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) :=
    lt_of_lt_of_le one_pos (one_le_dmin_two_pair n x y hxy)
  have hcard3 : 3 ≤ Fintype.card (Fin (n + 1)) := by simp; omega
  have hd3 : 0 < dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) :=
    lt_of_lt_of_le one_pos (one_le_dmin_three_pair n x y hxy hcard3)
  set B : ℝ := 1 / 3 * min (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) /
      dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
      (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y)) with hBdef
  have hBpos : 0 < B := by
    rw [hBdef]
    exact mul_pos (by norm_num : (0 : ℝ) < 1 / 3)
      (lt_min (div_pos hd3 hd2) (div_pos (pow_pos hd2 2) (mul_pos hxpos hypos)))
  have hdual := GamTwo_dual_lam1 n hn x y hx hy hxy
  have hdualB : B ≤ lamR (dualLat (realify (Gam 2 n x y))) 1 := by
    rw [hBdef]
    exact hdual
  haveI : DiscreteTopology (realify (Gam 2 n x y)) := Work.HP.HP3.discreteTopology_realify _
  have hfinZ : Module.finrank ℤ (realify (Gam 2 n x y)) = NN 2 n - 2 := by
    rw [finrank_realify (Gam 2 n x y)]
    exact (gam_rank_det 2 n x y hν).1
  obtain ⟨-, htr⟩ := transference_extreme (realify (Gam 2 n x y)) (NN 2 n - 2) hfinZ
  have h1 : lamR (realify (Gam 2 n x y)) (NN 2 n - 2) * B ≤ ((NN 2 n - 2 : ℕ) : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hdualB (Work.HP.Transf.lamR_nonneg _ _)) htr
  have h2 : lamR (realify (Gam 2 n x y)) (NN 2 n - 2) ≤ ((NN 2 n - 2 : ℕ) : ℝ) / B := by
    rw [le_div_iff₀ hBpos]
    exact h1
  have hid : B * muXY n x y = (n : ℝ) ^ 2 := by
    rw [hBdef]
    exact B_mul_muXY n x y hxpos hypos hd2 hd3
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    positivity
  have h3 : ((NN 2 n - 2 : ℕ) : ℝ) / B = ((NN 2 n - 2 : ℕ) : ℝ) * muXY n x y / (n : ℝ) ^ 2 := by
    rw [div_eq_div_iff hBpos.ne' hn2.ne']
    rw [← hid]
    ring
  have hR : ((NN 2 n - 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h := NN_two_sub_two_le n
    have h' : ((NN 2 n - 2 : ℕ) : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := Nat.cast_le.mpr h
    simpa [Nat.cast_pow] using h'
  have hμ := muXY_pos_of n x y hxpos hypos hd2 hd3
  calc lamR (realify (Gam 2 n x y)) (NN 2 n - 2)
      ≤ ((NN 2 n - 2 : ℕ) : ℝ) / B := h2
    _ = ((NN 2 n - 2 : ℕ) : ℝ) * muXY n x y / (n : ℝ) ^ 2 := h3
    _ ≤ (n : ℝ) ^ 2 * muXY n x y / (n : ℝ) ^ 2 := by
        gcongr
    _ = muXY n x y := by
        rw [mul_div_cancel_left₀ _ hn2.ne']

/-! ## Witness extraction -/

lemma exists_witnesses_le_add {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ)) (i : ℕ)
    (hne : ∃ f : Fin i → (ι → ℝ), (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f)
    {B ε : ℝ} (hε : 0 < ε) (h : lamR L i ≤ B) :
    ∃ f : Fin i → (ι → ℝ), (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧
      ∀ j, rNorm (f j) ≤ B + ε := by
  have hS : (setOf fun r : ℝ => 0 ≤ r ∧ ∃ f : Fin i → (ι → ℝ),
      (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r).Nonempty := by
    obtain ⟨f, hfL, hfI⟩ := hne
    exact ⟨∑ j, rNorm (f j), Finset.sum_nonneg (fun j _ => Work.HP.Transf.rNorm_nonneg _),
      f, hfL, hfI,
      fun j => Finset.single_le_sum (fun k _ => Work.HP.Transf.rNorm_nonneg _)
        (Finset.mem_univ j)⟩
  rw [lamR] at h
  obtain ⟨r, ⟨hr0, f, hfL, hfI, hfr⟩, hrc⟩ :=
    exists_lt_of_csInf_lt hS (lt_of_le_of_lt h (lt_add_of_pos_right B hε))
  exact ⟨f, hfL, hfI, fun j => (hfr j).trans hrc.le⟩


/-! ## The lift from `d = 2` to general `d` -/

lemma exists_indep_realify_Gam_two (n : ℕ) (x y : Fin (n + 1) → ℤ)
    (hν : LinearIndependent ℤ ![veronese 2 n x, veronese 2 n y]) :
    ∃ a : Fin (NN 2 n - 2) → (Mon 2 n → ℝ), (∀ j, a j ∈ realify (Gam 2 n x y)) ∧
      LinearIndependent ℝ a := by
  obtain ⟨k, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Mon 2 n)) (Gam 2 n x y)
  have hk : k = NN 2 n - 2 := by
    have h1 : Module.finrank ℤ (Gam 2 n x y) = k := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    rw [← h1]
    exact (gam_rank_det 2 n x y hν).1
  refine ⟨fun j => intCastPi ((b (Fin.cast hk.symm j) : ↥(Gam 2 n x y)) : Mon 2 n → ℤ), ?_, ?_⟩
  · intro j
    exact Submodule.mem_map_of_mem (b (Fin.cast hk.symm j)).2
  · have hb : LinearIndependent ℤ (fun j : Fin k => ((b j : ↥(Gam 2 n x y)) : Mon 2 n → ℤ)) :=
      b.linearIndependent.map' (Submodule.subtype _) (by
        rw [LinearMap.ker_eq_bot]
        exact Subtype.coe_injective)
    have hre : LinearIndependent ℤ (fun j : Fin (NN 2 n - 2) =>
        ((b (Fin.cast hk.symm j) : ↥(Gam 2 n x y)) : Mon 2 n → ℤ)) := by
      have hcomp := hb.comp (Fin.cast hk.symm) (fun a b hab => by simpa using hab)
      simpa [Function.comp_def] using hcomp
    exact Work.HP.Vero.linInd_intCastPi hre

theorem span_shift_eq (d : ℕ) (hd1 : 1 ≤ d + 1) (hd : 2 ≤ d) (x y : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y])
    {S : Set (Mon d n → ℝ)} (hS : Submodule.span ℝ S = VR d n x y) :
    Submodule.span ℝ (⋃ i : Fin (n + 1), (shift1 (d + 1) hd1 i) '' S)
      = VR (d + 1) n x y := by
  have h3 : 3 ≤ d + 1 := by omega
  have h1 : Submodule.span ℝ (⋃ i : Fin (n + 1), (shift1 (d + 1) hd1 i) '' S)
      = ⨆ i : Fin (n + 1), Submodule.map (shift1 (d + 1) hd1 i) (Submodule.span ℝ S) := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro v hv
      simp only [Set.mem_iUnion] at hv
      obtain ⟨i, w, hwS, rfl⟩ := hv
      exact Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem (Submodule.subset_span hwS))
    · refine iSup_le fun i => ?_
      rw [Submodule.map_span]
      exact Submodule.span_mono (Set.subset_iUnion (fun i => (shift1 (d + 1) hd1 i) '' S) i)
  rw [h1, hS]
  exact (LiftAux.VR_eq_iSup_shift (d + 1) h3 n x y hx hy hxy).symm

theorem shift1_mem_realify {d n : ℕ} (hd1 : 1 ≤ d + 1) (x y : Fin (n + 1) → ℤ)
    (i : Fin (n + 1)) {v : Mon d n → ℝ} (hv : v ∈ realify (Gam d n x y)) :
    shift1 (d + 1) hd1 i v ∈ realify (Gam (d + 1) n x y) := by
  obtain ⟨w, hw, rfl⟩ := hv
  rw [shift1_intCastPi hd1 i w]
  exact Submodule.mem_map_of_mem (shiftZ_mem_Gam x y hd1 i hw)

theorem lamR_le_of_spanning {d n : ℕ} (x y : Fin (n + 1) → ℤ) {B : ℝ} (hB : 0 ≤ B)
    (S : Set (Mon d n → ℝ)) (hSsub : S ⊆ ↑(realify (Gam d n x y)))
    (hSnorm : ∀ v ∈ S, rNorm v ≤ B) (hSdim : Module.finrank ℝ (VR d n x y) = NN d n - 2)
    (hSspan : Submodule.span ℝ S = VR d n x y) :
    lamR (realify (Gam d n x y)) (NN d n - 2) ≤ B := by
  classical
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℝ (S : Set (Mon d n → ℝ))
  have hbspan' : Submodule.span ℝ b = VR d n x y := by rw [hbspan, hSspan]
  have hbfin : b.Finite := hbli.finite
  haveI : Fintype ↥b := hbfin.fintype
  have hrange : Set.range (Subtype.val : ↥b → (Mon d n → ℝ)) = b := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩; exact w.2
    · intro hv; exact ⟨⟨v, hv⟩, rfl⟩
  have hcard : Fintype.card ↥b = NN d n - 2 := by
    have h1 := finrank_span_eq_card hbli
    rw [hrange] at h1
    rw [← h1, hbspan']; exact hSdim
  set e := Fintype.equivFin ↥b with he
  set φ : Fin (NN d n - 2) → (Mon d n → ℝ) :=
    fun j => (e.symm (Fin.cast hcard.symm j) : Mon d n → ℝ) with hφ
  have hφS : ∀ j, φ j ∈ S := fun j => hbS (e.symm (Fin.cast hcard.symm j)).2
  have hφi : LinearIndependent ℝ φ := by
    have h1 : φ = (Subtype.val : ↥b → (Mon d n → ℝ)) ∘
        (fun j => e.symm (Fin.cast hcard.symm j)) := by
      funext j; rfl
    rw [h1]
    exact hbli.comp _ (fun a b hab => by
      exact Fin.cast_injective hcard.symm (e.symm.injective hab))
  have hφn : ∀ j, rNorm (φ j) ≤ B := fun j => hSnorm _ (hφS j)
  rw [lamR]
  refine csInf_le (Work.HP.Transf.bddBelow_lamRset _ _) ⟨hB, φ, fun j => ?_, hφi, hφn⟩
  exact hSsub (hφS j)

theorem lamR_Gam_le_of_two (d n : ℕ) (hd : 2 ≤ d) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x)
    (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y]) (B : ℝ) (hB : 0 ≤ B)
    (h2 : lamR (realify (Gam 2 n x y)) (NN 2 n - 2) ≤ B) :
    lamR (realify (Gam d n x y)) (NN d n - 2) ≤ B := by
  have hνd : LinearIndependent ℤ ![veronese d n x, veronese d n y] :=
    nu_indep d n hd x y hx hy (ne_of_linInd x y hxy) (ne_neg_of_linInd x y hxy)
  have hν2 : LinearIndependent ℤ ![veronese 2 n x, veronese 2 n y] :=
    nu_indep 2 n (by norm_num) x y hx hy (ne_of_linInd x y hxy) (ne_neg_of_linInd x y hxy)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a0, ha0, ha0i⟩ := exists_indep_realify_Gam_two n x y hν2
  obtain ⟨a, ha, hai, han⟩ :=
    exists_witnesses_le_add (realify (Gam 2 n x y)) (NN 2 n - 2) ⟨a0, ha0, ha0i⟩ hε h2
  have key : ∀ d' : ℕ, 2 ≤ d' → ∃ S : Set (Mon d' n → ℝ),
      S ⊆ ↑(realify (Gam d' n x y)) ∧ (∀ v ∈ S, rNorm v ≤ B + ε) ∧
      Submodule.span ℝ S = VR d' n x y := by
    intro d' hd'
    induction d', hd' using Nat.le_induction with
    | base =>
        refine ⟨Set.range a, ?_, ?_, ?_⟩
        · rintro v ⟨j, rfl⟩; exact ha j
        · rintro v ⟨j, rfl⟩; exact han j
        · refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
          · rw [Submodule.span_le]
            rintro v ⟨j, rfl⟩
            exact realify_subset_VR x y (ha j)
          · rw [finrank_span_eq_card hai, finrank_VR 2 n x y hν2]
            simp
    | succ k hk ih =>
        obtain ⟨S, hSsub, hSnorm, hSspan⟩ := ih
        have hk1 : 1 ≤ k + 1 := by omega
        refine ⟨⋃ i : Fin (n + 1), (shift1 (k + 1) hk1 i) '' S, ?_, ?_, ?_⟩
        · rintro v hv
          simp only [Set.mem_iUnion] at hv
          obtain ⟨i, w, hwS, rfl⟩ := hv
          exact shift1_mem_realify hk1 x y i (hSsub hwS)
        · rintro v hv
          simp only [Set.mem_iUnion] at hv
          obtain ⟨i, w, hwS, rfl⟩ := hv
          rw [rNorm_shift1]
          exact hSnorm w hwS
        · exact span_shift_eq k hk1 hk x y hx hy hxy hSspan
  obtain ⟨S, hSsub, hSnorm, hSspan⟩ := key d hd
  exact lamR_le_of_spanning x y (by linarith) S hSsub hSnorm (finrank_VR d n x y hνd) hSspan


/-- **Key lemma, two vectors** (Browning–Le Boudec–Sawin, §3.3).  For primitive, `ℤ`-linearly
independent `x, y ∈ ℤ^{n+1}` the `(N_{d,n}-2)`-nd successive minimum of
`Γ_{x,y} = Λ_{ν(x)} ∩ Λ_{ν(y)} = Gam d n x y` is at most `μ(x,y) = muXY n x y`. -/
theorem lam_Gam_le_muXY (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (x y : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y]) :
    lam (Gam d n x y) (NN d n - 2) ≤ muXY n x y := by
  have hn : 2 ≤ n := le_trans hd hdn
  rw [lam_eq_lamR_realify (Gam d n x y) (NN d n - 2)]
  exact lamR_Gam_le_of_two d n hd x y hx hy hxy (muXY n x y)
    (muXY_nonneg n hn x y hx hy hxy) (lamR_Gam_two_le_muXY n hn x y hx hy hxy)

end Work.HP.Sig2
