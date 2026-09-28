import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.HP3.DotLinDefs
import Submission.Work.HP.HP3.VeroProdDefs
import Submission.Work.HP.HP3.VeroProdExtra
import Submission.Work.HP.HP3.cond_iff_eq_addE
import Submission.Work.HP.HP3.prodVecR_pair
import Submission.Work.HP.Vero.finrank_latOrth
import Submission.Work.HP.Vero.span_realify_latOrth_inf
import Submission.Work.HP.Vero.ThetaDefs

set_option autoImplicit false
noncomputable section
open Finset

namespace Work.HP.Vero

/-! ## General helpers -/

/-- A primitive integer vector is nonzero. -/
lemma isPrim_ne_zero {ι : Type*} [Fintype ι] {v : ι → ℤ} (h : IsPrim v) : v ≠ 0 := by
  intro hv
  have h0 : Finset.univ.gcd v = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun x _ => by rw [hv]; rfl)
  rw [IsPrim] at h
  omega

/-- From a finite family whose `ℝ`-span has dimension `D` one extracts `D` linearly independent
members of the family: a basis of the span can be chosen inside a spanning set. -/
lemma exists_linearIndependent_fin_of_span_range {κ M : Type*} [Fintype κ] [AddCommGroup M]
    [Module ℝ M] [FiniteDimensional ℝ M] (v : κ → M) (D : ℕ)
    (h : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = D) :
    ∃ f : Fin D → M, LinearIndependent ℝ f ∧ ∀ i, f i ∈ Set.range v := by
  classical
  obtain ⟨f, hf_mem, -, hf_ind⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range v)
  exact ⟨fun i => f (Fin.cast h.symm i), hf_ind.comp _ (Fin.cast_injective h.symm),
    fun i => hf_mem _⟩

/-- `intCastPi` commutes with finite sums of `ℤ`-multiples. -/
lemma intCastPi_sum_smul {κ ι : Type*} [Fintype κ] [Fintype ι]
    (c : κ → ℤ) (v : κ → ι → ℤ) :
    intCastPi (∑ k, c k • v k) = ∑ k, (c k : ℝ) • intCastPi (v k) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by ext i; simp [intCastPi, zsmul_eq_mul]

/-- `ℤ`-linear independence follows from `ℝ`-linear independence of the realified family. -/
lemma linearIndependent_int_of_intCastPi {κ ι : Type*} [Fintype κ] [Fintype ι]
    {f : κ → ι → ℤ} (h : LinearIndependent ℝ (fun k => intCastPi (f k))) :
    LinearIndependent ℤ f := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  have key : ∑ k, (g k : ℝ) • intCastPi (f k) = 0 := by
    rw [← intCastPi_sum_smul g f, hg, map_zero]
  intro k
  exact_mod_cast h _ key k

/-- `v ∈ latOrth x ↔ ⟨v,x⟩ = 0`, where `⟨v,x⟩ = ∑ i, v i * x i`. -/
private lemma mem_latOrth_iff (n : ℕ) (v x : Fin (n + 1) → ℤ) :
    v ∈ latOrth x ↔ ∑ i, v i * x i = 0 := by
  simp only [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply, zsmul_eq_mul,
    Int.cast_id]

/-- The same for the Veronese lattice: `A ∈ latOrth (ν_d(x)) ↔ f_A(x) = 0`. -/
lemma mem_latOrth_veronese_iff (d n : ℕ) (A : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) :
    A ∈ latOrth (veronese d n x) ↔ formEval d n A x = 0 := by
  simp only [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply, formEval,
    Int.cast_id, zsmul_eq_mul]

/-- **The `Θ` map, one monomial.**  The coefficient vector of `X^m · ⟨c,X⟩` satisfies
`⟨prodVec, ν_d(x)⟩ = ν_{d-1}(x)(m)·⟨c,x⟩` and has the same Euclidean norm as `c`. -/
theorem prodVec_eval_eNorm (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n)
    (c : Fin (n + 1) → ℤ) (x : Fin (n + 1) → ℤ) :
    formEval d n (prodVec d n m c) x = veronese (d - 1) n x m * ∑ j, c j * x j ∧
    eNorm (prodVec d n m c) = eNorm c := by
  have hpi : ∀ m' : Mon d n, prodVec d n m c m'
      = ∑ k : Fin (n + 1), (if m' = addE d n hd m k then c k else 0) :=
    fun m' => HP3.prodVec_apply d n hd m c m'
  have hinj : Function.Injective (fun k : Fin (n + 1) => addE d n hd m k) := by
    intro k k' hkk'
    have h1 : ((addE d n hd m k).1 k : ℕ) = (m.1 k : ℕ) + 1 := by
      rw [addE_val]; simp
    have h3 : ((addE d n hd m k').1 k : ℕ) = (m.1 k : ℕ) + (if k = k' then 1 else 0) :=
      addE_val d n hd m k' k
    have h4 := congrArg (fun m' : Mon d n => (m'.1 k : ℕ)) hkk'
    rw [h1, h3] at h4
    by_contra hne
    rw [if_neg hne, add_zero] at h4
    omega
  constructor
  · have hcalc : formEval d n (prodVec d n m c) x
        = ∑ m' : Mon d n, (∑ k : Fin (n + 1),
            (if m' = addE d n hd m k then c k else 0)) * veronese d n x m' := by
      simp only [formEval, Int.cast_id]
      exact Finset.sum_congr rfl (fun m' _ => by rw [hpi m'])
    rw [hcalc]
    calc ∑ m' : Mon d n, (∑ k : Fin (n + 1),
            (if m' = addE d n hd m k then c k else 0)) * veronese d n x m'
        = ∑ k : Fin (n + 1), c k * veronese d n x (addE d n hd m k) := by
          rw [Finset.sum_congr rfl (fun m' _ => Finset.sum_mul ..), Finset.sum_comm]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.sum_eq_single (addE d n hd m k)]
          · simp
          · intro m' _ hm'; simp [hm']
          · intro h; exact absurd (Finset.mem_univ _) h
      _ = veronese (d - 1) n x m * ∑ k : Fin (n + 1), c k * x k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [veronese_addE]; ring
  · have hpt : ∀ m' : Mon d n, ((prodVec d n m c m' : ℤ) : ℝ)
        = ∑ k : Fin (n + 1), (if m' = addE d n hd m k then ((c k : ℤ) : ℝ) else 0) := by
      intro m'
      rw [hpi m', Int.cast_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases h : m' = addE d n hd m k <;> simp [h]
    have hsupp : ∀ m' : Mon d n, (∑ k : Fin (n + 1),
          (if m' = addE d n hd m k then ((c k : ℤ) : ℝ) else 0)) ^ 2
        = ∑ k : Fin (n + 1),
            (if m' = addE d n hd m k then ((c k : ℤ) : ℝ) ^ 2 else 0) := by
      intro m'
      by_cases hex : ∃ k : Fin (n + 1), m' = addE d n hd m k
      · obtain ⟨k₀, hk₀⟩ := hex
        have hne : ∀ k, k ≠ k₀ → m' ≠ addE d n hd m k := by
          intro k hk hh
          refine hk (hinj ?_)
          change addE d n hd m k = addE d n hd m k₀
          rw [← hh, hk₀]
        have h1 : (∑ k : Fin (n + 1),
              (if m' = addE d n hd m k then ((c k : ℤ) : ℝ) else 0)) = ((c k₀ : ℤ) : ℝ) := by
          rw [Finset.sum_eq_single k₀]
          · rw [if_pos hk₀]
          · intro k _ hk; simp [hne k hk]
          · intro h; exact absurd (Finset.mem_univ k₀) h
        have h2 : (∑ k : Fin (n + 1),
              (if m' = addE d n hd m k then ((c k : ℤ) : ℝ) ^ 2 else 0))
            = ((c k₀ : ℤ) : ℝ) ^ 2 := by
          rw [Finset.sum_eq_single k₀]
          · rw [if_pos hk₀]
          · intro k _ hk; simp [hne k hk]
          · intro h; exact absurd (Finset.mem_univ k₀) h
        rw [h1, h2]
      · rw [not_exists] at hex
        refine Eq.trans (congrArg (· ^ 2) (Finset.sum_eq_zero (fun k _ => ?_))) ?_
        · exact if_neg (hex k)
        · rw [Finset.sum_eq_zero (fun k _ => ?_), zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
          exact if_neg (hex k)
    have hsum2 : ∑ m' : Mon d n, ((prodVec d n m c m' : ℤ) : ℝ) ^ 2
        = ∑ k : Fin (n + 1), ((c k : ℤ) : ℝ) ^ 2 := by
      rw [Finset.sum_congr rfl (fun m' _ => by rw [hpt m', hsupp m']), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_eq_single (addE d n hd m k)]
      · rw [if_pos rfl]
      · intro m' _ hm'; rw [if_neg hm']
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [eNorm]
    rw [hsum2]

/-- A nonzero functional into a field has a kernel of codimension one. -/
lemma finrank_ker_functional {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (f : V →ₗ[ℝ] ℝ) (hf : f ≠ 0) :
    Module.finrank ℝ (LinearMap.ker f) = Module.finrank ℝ V - 1 := by
  obtain ⟨v, hv0⟩ : ∃ v, f v ≠ 0 := by
    by_contra hcon
    exact hf (LinearMap.ext fun v => by
      by_contra hv
      exact hcon ⟨v, hv⟩)
  have hle : Module.finrank ℝ (LinearMap.range f) ≤ 1 := by
    have h := Submodule.finrank_le (R := ℝ) (LinearMap.range f)
    rwa [Module.finrank_self] at h
  have hge : 1 ≤ Module.finrank ℝ (LinearMap.range f) := by
    have h2 : Module.finrank ℝ (Submodule.span ℝ {f v}) ≤ Module.finrank ℝ (LinearMap.range f) :=
      Submodule.finrank_mono (by
        rw [Submodule.span_le]
        rintro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨v, rfl⟩)
    rw [finrank_span_singleton hv0] at h2
    exact h2
  have hrange : Module.finrank ℝ (LinearMap.range f) = 1 := le_antisymm hle hge
  have hadd := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hadd
  omega

/-- `finrank` of the hyperplane `(ℝ ν_d(x))^⊥` in the space of degree-`d` forms. -/
theorem finrank_ker_evalLin (d n : ℕ) (hd : 1 ≤ d) (x : Fin (n + 1) → ℤ) (hx : x ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (evalLin d n x)) = NN d n - 1 := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have hν : veronese d n x (powMon d n i₀) ≠ 0 := by
    rw [veronese_powMon]; exact pow_ne_zero d hi₀
  have hne : evalLin d n x ≠ 0 := by
    intro h
    have h1 : evalLin d n x (Pi.single (powMon d n i₀) (1 : ℝ)) = 0 := by rw [h]; rfl
    have hval : evalLin d n x (Pi.single (powMon d n i₀) (1 : ℝ))
        = ((veronese d n x (powMon d n i₀) : ℤ) : ℝ) := by
      simp only [evalLin, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single (powMon d n i₀)]
      · rw [Pi.single_eq_same, one_mul]
      · intro m _ hm
        rw [Pi.single_eq_of_ne hm, zero_mul]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [hval] at h1
    exact hν (by exact_mod_cast h1)
  rw [finrank_ker_functional (evalLin d n x) hne, Module.finrank_fintype_fun_eq_card ℝ]

/-- `dotLin x` is a nonzero functional for `x ≠ 0`. -/
lemma dotLin_ne_zero (n : ℕ) (x : Fin (n + 1) → ℤ) (hx : x ≠ 0) : dotLin x ≠ 0 := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  intro h
  have h1 : dotLin x (Pi.single i₀ (1 : ℝ)) = (x i₀ : ℝ) := by
    rw [dotLin_apply]
    rw [Finset.sum_eq_single i₀]
    · rw [Pi.single_eq_same, mul_one]
    · intro k _ hk
      have hz : (Pi.single i₀ (1 : ℝ) : Fin (n + 1) → ℝ) k = 0 := by simp [hk]
      rw [hz, mul_zero]
    · intro hh; exact absurd (Finset.mem_univ i₀) hh
  have h2 : dotLin x (Pi.single i₀ (1 : ℝ)) = 0 := by rw [h]; rfl
  rw [h1] at h2
  exact (by exact_mod_cast hi₀ : (x i₀ : ℝ) ≠ 0) h2

/-- The `n` vectors `a j ∈ latOrth x` `ℝ`-span the hyperplane `x^⊥`. -/
theorem span_intCastPi_a_eq_ker_dotLin (n : ℕ) (x : Fin (n + 1) → ℤ) (hx : IsPrim x)
    (a : Fin n → (Fin (n + 1) → ℤ)) (ha : ∀ j, a j ∈ latOrth x)
    (hai : LinearIndependent ℤ a) :
    Submodule.span ℝ (Set.range (fun j : Fin n => intCastPi (a j)))
      = LinearMap.ker (dotLin x) := by
  have hx0 : x ≠ 0 := isPrim_ne_zero hx
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro u ⟨j, rfl⟩
    show intCastPi (a j) ∈ LinearMap.ker (dotLin x)
    rw [LinearMap.mem_ker]
    have h2 : (∑ i, ((a j i * x i : ℤ) : ℝ)) = 0 := by
      rw [← Int.cast_sum, (mem_latOrth_iff n (a j) x).mp (ha j), Int.cast_zero]
    have h3 : (∑ i, (x i : ℝ) * (a j i : ℝ)) = 0 := by
      have hpt : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
          ((a j i * x i : ℤ) : ℝ) = (x i : ℝ) * (a j i : ℝ) := by
        intro i _
        rw [Int.cast_mul]
        ring
      rw [Finset.sum_congr rfl hpt] at h2
      exact h2
    simpa only [dotLin_apply, intCastPi_apply] using h3
  · have h1 : Module.finrank ℝ
        (Submodule.span ℝ (Set.range (fun j : Fin n => intCastPi (a j)))) = n := by
      rw [finrank_span_eq_card (linInd_intCastPi hai), Fintype.card_fin]
    have h2 : Module.finrank ℝ (LinearMap.ker (dotLin x)) = n := by
      have hk := finrank_ker_functional (dotLin x) (dotLin_ne_zero n x hx0)
      rw [Module.finrank_fintype_fun_eq_card ℝ, Fintype.card_fin] at hk
      simpa using hk
    rw [h1, h2]

/-! ## The `d ≥ 2` spanning statement -/

/-- A monomial different from `X_{i₀}^d` has a positive exponent in some other coordinate. -/
lemma exists_coord_pos {d n : ℕ} {i₀ : Fin (n + 1)} {m' : Mon d n}
    (hm : m' ≠ powMon d n i₀) : ∃ j : Fin (n + 1), j ≠ i₀ ∧ 1 ≤ (m'.1 j : ℕ) := by
  by_contra h
  rw [not_exists] at h
  have hall : ∀ j, j ≠ i₀ → (m'.1 j : ℕ) = 0 := by
    intro j hj
    have h2 : ¬ (1 ≤ (m'.1 j : ℕ)) := fun h1 => h j ⟨hj, h1⟩
    omega
  have hi₀ : (m'.1 i₀ : ℕ) = d := by
    have hz : ∑ i ∈ Finset.univ.erase i₀, (m'.1 i : ℕ) = 0 :=
      Finset.sum_eq_zero (fun i hi => hall i (Finset.mem_erase.mp hi).1)
    have h2 := Finset.sum_erase_add (Finset.univ : Finset (Fin (n + 1)))
      (fun i => (m'.1 i : ℕ)) (Finset.mem_univ i₀)
    rw [m'.2] at h2
    omega
  refine hm ?_
  refine Subtype.ext (funext fun i => Fin.ext ?_)
  show (m'.1 i : ℕ) = ((powMon d n i₀).1 i : ℕ)
  rw [powMon_val]
  by_cases hi : i = i₀
  · subst hi
    rw [if_pos rfl, hi₀]
  · rw [if_neg hi, hall i hi]

/-- For `d ≥ 2`, the coefficient vectors of the degree-`d` forms `X^m · ⟨a_j, X⟩`
(`m` of degree `d-1`, `j : Fin n`) `ℝ`-span the space of degree-`d` forms vanishing at `x`. -/
theorem prodVec_span_eq_ker (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x : Fin (n + 1) → ℤ) (hx : IsPrim x) (a : Fin n → (Fin (n + 1) → ℤ))
    (ha : ∀ j, a j ∈ latOrth x) (hai : LinearIndependent ℤ a) :
    Submodule.span ℝ (Set.range (fun p : Mon (d - 1) n × Fin n => prodVecR d n p.1 (a p.2)))
      = LinearMap.ker (evalLin d n x) := by
  have hd1 : 1 ≤ d := by omega
  have hx0 : x ≠ 0 := isPrim_ne_zero hx
  have hW : Submodule.span ℝ (Set.range (fun j : Fin n => intCastPi (a j)))
      = LinearMap.ker (dotLin x) := span_intCastPi_a_eq_ker_dotLin n x hx a ha hai
  set S : Submodule ℝ (Mon d n → ℝ) := Submodule.span ℝ
    (Set.range (fun p : Mon (d - 1) n × Fin n => mulVecR d n hd1 p.1 (intCastPi (a p.2))))
    with hSdef
  have hrange : Set.range (fun p : Mon (d - 1) n × Fin n => mulVecR d n hd1 p.1 (intCastPi (a p.2)))
      = Set.range (fun p : Mon (d - 1) n × Fin n => prodVecR d n p.1 (a p.2)) := by
    ext y
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨p, by
        show prodVecR d n p.1 (a p.2) = y
        rw [← mulVecR_intCastPi d n hd1 p.1 (a p.2)]
        exact hp⟩
    · rintro ⟨p, hp⟩
      exact ⟨p, by
        show mulVecR d n hd1 p.1 (intCastPi (a p.2)) = y
        rw [mulVecR_intCastPi d n hd1 p.1 (a p.2)]
        exact hp⟩
  have hS_eq : S = Submodule.span ℝ
      (Set.range (fun p : Mon (d - 1) n × Fin n => prodVecR d n p.1 (a p.2))) := by
    rw [hSdef, hrange]
  have hmulW : ∀ (m : Mon (d - 1) n) {L : Fin (n + 1) → ℝ}, L ∈ LinearMap.ker (dotLin x) →
      mulVecR d n hd1 m L ∈ S := by
    intro m L hL
    have hsub : Submodule.span ℝ (Set.range (fun j : Fin n => intCastPi (a j)))
        ≤ Submodule.comap (mulVecR d n hd1 m) S := by
      rw [Submodule.span_le]
      rintro y ⟨j, rfl⟩
      exact Submodule.subset_span ⟨(m, j), rfl⟩
    exact Submodule.mem_comap.mp (hsub (by rw [hW]; exact hL))
  have hle : S ≤ LinearMap.ker (evalLin d n x) := by
    rw [hSdef, Submodule.span_le]
    rintro y ⟨p, rfl⟩
    show mulVecR d n hd1 p.1 (intCastPi (a p.2)) ∈ LinearMap.ker (evalLin d n x)
    rw [mulVecR_intCastPi, LinearMap.mem_ker, evalLin_prodVecR]
    have hpe := (prodVec_eval_eNorm d n hd1 p.1 (a p.2) x).1
    have hax := (mem_latOrth_iff n (a p.2) x).mp (ha p.2)
    rw [hpe, hax, mul_zero, Int.cast_zero]
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx0
  have hxi : (x i₀ : ℝ) ≠ 0 := by exact_mod_cast hi₀
  have hLj : ∀ j : Fin (n + 1), (fun k => (x i₀ : ℝ) * (if k = j then 1 else 0)
      - (x j : ℝ) * (if k = i₀ then 1 else 0)) ∈ LinearMap.ker (dotLin x) := by
    intro j
    rw [LinearMap.mem_ker]
    exact dotLin_L n x i₀ j
  have hrel : ∀ (q : Mon (d - 1) n) (j : Fin (n + 1)),
      (x i₀ : ℝ) • (Pi.single (addE d n hd1 q j) (1 : ℝ))
        - (x j : ℝ) • (Pi.single (addE d n hd1 q i₀) (1 : ℝ)) ∈ S := by
    intro q j
    rw [← mulVecR_L d n hd1 i₀ j x q]
    exact hmulW q (hLj j)
  set sf : Mon d n → ℕ := fun m' => ∑ i ∈ Finset.univ.erase i₀, (m'.1 i : ℕ) with hsf
  set sg : Mon (d - 1) n → ℕ := fun m => ∑ i ∈ Finset.univ.erase i₀, (m.1 i : ℕ) with hsg
  have hsf_eq : ∀ q : Mon (d - 1) n, sf (addE d n hd1 q i₀) = sg q := by
    intro q
    have hsum : ∀ i ∈ Finset.univ.erase i₀,
        ((addE d n hd1 q i₀).1 i : ℕ) = (q.1 i : ℕ) := by
      intro i hi
      rw [addE_val, if_neg (Finset.mem_erase.mp hi).1, add_zero]
    simp only [hsf, hsg]
    rw [Finset.sum_congr rfl hsum]
  have hsf_ne : ∀ (q : Mon (d - 1) n) (j : Fin (n + 1)), j ≠ i₀ →
      sf (addE d n hd1 q j) = sg q + 1 := by
    intro q j hj
    have hmem : j ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    have hpt : ∀ i : Fin (n + 1),
        ((addE d n hd1 q j).1 i : ℕ) = (q.1 i : ℕ) + (if i = j then 1 else 0) :=
      fun i => addE_val d n hd1 q j i
    simp only [hsf, hsg]
    rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib,
      Finset.sum_ite_eq' (Finset.univ.erase i₀) j (fun _ => (1 : ℕ)), if_pos hmem]
  have hkey : ∀ m' : Mon d n,
      veroneseR d n x (powMon d n i₀) • (Pi.single m' (1 : ℝ))
        - veroneseR d n x m' • (Pi.single (powMon d n i₀) (1 : ℝ)) ∈ S := by
    intro m'
    refine Nat.strongRecOn (motive := fun k => ∀ m'' : Mon d n, sf m'' = k →
        veroneseR d n x (powMon d n i₀) • (Pi.single m'' (1 : ℝ))
          - veroneseR d n x m'' • (Pi.single (powMon d n i₀) (1 : ℝ)) ∈ S)
      (sf m') (fun k ih m'' hk => ?_) m' rfl
    by_cases hm0 : m'' = powMon d n i₀
    · subst hm0
      rw [sub_self]
      exact Submodule.zero_mem _
    · obtain ⟨j, hjne, hjpos⟩ := exists_coord_pos hm0
      set q : Mon (d - 1) n := subE d n m'' j hjpos with hqdef
      have hqj : addE d n hd1 q j = m'' := addE_subE d n hd1 m'' j hjpos
      have hrel' : (x i₀ : ℝ) • (Pi.single m'' (1 : ℝ))
          - (x j : ℝ) • (Pi.single (addE d n hd1 q i₀) (1 : ℝ)) ∈ S := by
        have h := hrel q j
        rwa [hqj] at h
      have hslt : sf (addE d n hd1 q i₀) < k := by
        have h1 : sf (addE d n hd1 q j) = sg q + 1 := hsf_ne q j hjne
        rw [hqj, hk] at h1
        rw [hsf_eq q]
        omega
      have hIH := ih (sf (addE d n hd1 q i₀)) hslt (addE d n hd1 q i₀) rfl
      have hνrel : (x j : ℝ) * veroneseR d n x (addE d n hd1 q i₀)
          = (x i₀ : ℝ) * veroneseR d n x m'' := by
        rw [← hqj, veroneseR_addE d n hd1 q j x, veroneseR_addE d n hd1 q i₀ x]
        ring
      have hmem1 : veroneseR d n x (powMon d n i₀) •
            ((x i₀ : ℝ) • (Pi.single m'' (1 : ℝ))
              - (x j : ℝ) • (Pi.single (addE d n hd1 q i₀) (1 : ℝ)))
          + (x j : ℝ) • (veroneseR d n x (powMon d n i₀) • (Pi.single (addE d n hd1 q i₀) (1 : ℝ))
              - veroneseR d n x (addE d n hd1 q i₀) • (Pi.single (powMon d n i₀) (1 : ℝ))) ∈ S :=
        Submodule.add_mem _ (Submodule.smul_mem _ _ hrel') (Submodule.smul_mem _ _ hIH)
      have hEq : veroneseR d n x (powMon d n i₀) •
            ((x i₀ : ℝ) • (Pi.single m'' (1 : ℝ))
              - (x j : ℝ) • (Pi.single (addE d n hd1 q i₀) (1 : ℝ)))
          + (x j : ℝ) • (veroneseR d n x (powMon d n i₀) • (Pi.single (addE d n hd1 q i₀) (1 : ℝ))
              - veroneseR d n x (addE d n hd1 q i₀) • (Pi.single (powMon d n i₀) (1 : ℝ)))
          = (x i₀ : ℝ) • (veroneseR d n x (powMon d n i₀) • (Pi.single m'' (1 : ℝ))
              - veroneseR d n x m'' • (Pi.single (powMon d n i₀) (1 : ℝ))) := by
        simp only [smul_sub, smul_smul]
        rw [hνrel]
        module
      rw [hEq] at hmem1
      exact (Submodule.smul_mem_iff S hxi).mp hmem1
  have hge : LinearMap.ker (evalLin d n x) ≤ S := by
    intro F hF
    have hν₀ : veroneseR d n x (powMon d n i₀) ≠ 0 := by
      have h : veronese d n x (powMon d n i₀) ≠ 0 := by
        rw [veronese_powMon]; exact pow_ne_zero d hi₀
      simpa only [veroneseR] using
        (by exact_mod_cast h : ((veronese d n x (powMon d n i₀) : ℤ) : ℝ) ≠ 0)
    have hbasis : F = ∑ m' : Mon d n, F m' • (Pi.single m' (1 : ℝ)) := by
      conv_lhs => rw [← (Pi.basisFun ℝ (Mon d n)).sum_repr F]
      simp [Pi.basisFun_repr, Pi.basisFun_apply]
    have hsplit : (∑ m' : Mon d n, F m' • (veroneseR d n x (powMon d n i₀) • (Pi.single m' (1 : ℝ))
          - veroneseR d n x m' • (Pi.single (powMon d n i₀) (1 : ℝ))))
        = (∑ m' : Mon d n, F m' • (veroneseR d n x (powMon d n i₀) • (Pi.single m' (1 : ℝ))))
          - (∑ m' : Mon d n, F m' • (veroneseR d n x m' • (Pi.single (powMon d n i₀) (1 : ℝ)))) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun m' _ => ?_)
      rw [smul_sub]
    have hfirst : (∑ m' : Mon d n, F m' • (veroneseR d n x (powMon d n i₀) • (Pi.single m' (1 : ℝ))))
        = veroneseR d n x (powMon d n i₀) • F := by
      conv_rhs => rw [hbasis]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun m' _ => ?_)
      rw [smul_comm]
    have hsecond : (∑ m' : Mon d n,
        F m' • (veroneseR d n x m' • (Pi.single (powMon d n i₀) (1 : ℝ)))) = 0 := by
      have ha : ∀ m' : Mon d n, F m' • (veroneseR d n x m' • (Pi.single (powMon d n i₀) (1 : ℝ)))
          = (F m' * veroneseR d n x m') • (Pi.single (powMon d n i₀) (1 : ℝ)) := by
        intro m'; rw [smul_smul]
      rw [Finset.sum_congr rfl (fun m' _ => ha m'), ← Finset.sum_smul]
      have hz : (∑ m' : Mon d n, F m' * veroneseR d n x m') = 0 := by
        have hh := hF
        rw [LinearMap.mem_ker] at hh
        simpa only [evalLin, LinearMap.coe_mk, AddHom.coe_mk, veroneseR] using hh
      rw [hz, zero_smul]
    have hsum : (∑ m' : Mon d n, F m' • (veroneseR d n x (powMon d n i₀) • (Pi.single m' (1 : ℝ))
          - veroneseR d n x m' • (Pi.single (powMon d n i₀) (1 : ℝ)))) ∈ S :=
      Submodule.sum_mem _ (fun m' _ => Submodule.smul_mem _ _ (hkey m'))
    have hmem : veroneseR d n x (powMon d n i₀) • F ∈ S := by
      rw [hsplit, hfirst, hsecond, sub_zero] at hsum
      exact hsum
    exact (Submodule.smul_mem_iff S hν₀).mp hmem
  have hmain : S = LinearMap.ker (evalLin d n x) := le_antisymm hle hge
  rw [← hS_eq]
  exact hmain

/-! ## The `d = 1` spanning statement -/

/-- The degree-zero monomial `1`. -/
def zeroMon (n : ℕ) : Mon 0 n := ⟨fun _ => ⟨0, by omega⟩, by simp⟩

@[simp] lemma zeroMon_val (n : ℕ) (i : Fin (n + 1)) : ((zeroMon n).1 i : ℕ) = 0 := rfl

lemma subsingleton_Mon_zero (n : ℕ) : Subsingleton (Mon 0 n) := by
  refine ⟨fun a b => Subtype.ext (funext fun i => Fin.ext ?_)⟩
  have ha : (a.1 i : ℕ) = 0 := by
    have hle := Finset.single_le_sum (f := fun j => (a.1 j : ℕ))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [a.2] at hle
    omega
  have hb : (b.1 i : ℕ) = 0 := by
    have hle := Finset.single_le_sum (f := fun j => (b.1 j : ℕ))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [b.2] at hle
    omega
  omega

/-- `k ↦ m + e_k` is injective. -/
lemma addE_injective (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) :
    Function.Injective (fun k : Fin (n + 1) => addE d n hd m k) := by
  intro k k' hkk'
  have h1 : ((addE d n hd m k).1 k : ℕ) = (m.1 k : ℕ) + 1 := by
    rw [addE_val]; simp
  have h3 : ((addE d n hd m k').1 k : ℕ) = (m.1 k : ℕ) + (if k = k' then 1 else 0) :=
    addE_val d n hd m k' k
  have h4 := congrArg (fun m' : Mon d n => (m'.1 k : ℕ)) hkk'
  rw [h1, h3] at h4
  by_contra hne
  rw [if_neg hne, add_zero] at h4
  omega

/-- Every degree-one monomial is `e_k` for some `k`. -/
lemma addE_zeroMon_surjective (n : ℕ) :
    Function.Surjective (fun k : Fin (n + 1) => addE 1 n le_rfl (zeroMon n) k) := by
  intro m'
  have hex : ∃ k : Fin (n + 1), 1 ≤ (m'.1 k : ℕ) := by
    by_contra h
    rw [not_exists] at h
    have h0 : ∑ i, (m'.1 i : ℕ) = 0 :=
      Finset.sum_eq_zero (fun i _ => by have := h i; omega)
    rw [m'.2] at h0
    omega
  obtain ⟨k, hk⟩ := hex
  have hk1 : (m'.1 k : ℕ) = 1 := by
    have := (m'.1 k).isLt
    omega
  refine ⟨k, ?_⟩
  refine Subtype.ext (funext fun i => Fin.ext ?_)
  show ((addE 1 n le_rfl (zeroMon n) k).1 i : ℕ) = (m'.1 i : ℕ)
  rw [addE_val, zeroMon_val, zero_add]
  by_cases hi : i = k
  · subst hi
    rw [if_pos rfl, hk1]
  · rw [if_neg hi]
    have hzero : (m'.1 i : ℕ) = 0 := by
      have hle : (m'.1 k : ℕ) + (m'.1 i : ℕ) ≤ ∑ j, (m'.1 j : ℕ) := by
        have hpair : ∑ j ∈ ({k, i} : Finset (Fin (n + 1))), (m'.1 j : ℕ)
            = (m'.1 k : ℕ) + (m'.1 i : ℕ) := Finset.sum_pair (Ne.symm hi)
        rw [← hpair]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro j hj; simp
        · intro j _ _; exact Nat.zero_le _
      omega
    omega

lemma veroneseR_zeroMon (n : ℕ) (x : Fin (n + 1) → ℤ) : veroneseR 0 n x (zeroMon n) = 1 := by
  simp [veroneseR, veronese, zeroMon_val]

/-- The pairing identity: `⟨X^m·⟨L,X⟩, ν_d(x)⟩ = ν_{d-1}(x)(m)·⟨L,x⟩`. -/
lemma evalLin_mulVecR (d n : ℕ) (hd : 1 ≤ d) (m : Mon (d - 1) n) (L : Fin (n + 1) → ℝ)
    (x : Fin (n + 1) → ℤ) :
    evalLin d n x (mulVecR d n hd m L) = veroneseR (d - 1) n x m * dotLin x L := by
  have hcalc : evalLin d n x (mulVecR d n hd m L)
      = ∑ k : Fin (n + 1), L k * veroneseR d n x (addE d n hd m k) := by
    simp only [evalLin, LinearMap.coe_mk, AddHom.coe_mk, mulVecR_apply]
    rw [Finset.sum_congr rfl (fun m' _ => Finset.sum_mul ..), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_eq_single (addE d n hd m k)]
    · simp [veroneseR]
    · intro m' _ hm'; rw [if_neg hm', zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hstep : ∀ k : Fin (n + 1), L k * veroneseR d n x (addE d n hd m k)
      = L k * (veroneseR (d - 1) n x m * (x k : ℝ)) := by
    intro k; rw [veroneseR_addE]
  rw [hcalc, Finset.sum_congr rfl (fun k _ => hstep k), dotLin_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- `mulVecR` at the degree-one monomial `e_k` is the identity, after reindexing. -/
lemma mulVecR_zeroMon_apply (n : ℕ) (F : Mon 1 n → ℝ) :
    mulVecR 1 n le_rfl (zeroMon n)
      (fun k => F (addE 1 n le_rfl (zeroMon n) k)) = F := by
  funext m'
  rw [mulVecR_apply]
  obtain ⟨k₀, hk₀⟩ := addE_zeroMon_surjective n m'
  have hk₀' : addE 1 n le_rfl (zeroMon n) k₀ = m' := hk₀
  rw [Finset.sum_eq_single k₀]
  · rw [if_pos hk₀'.symm, hk₀']
  · intro k _ hk
    have hne : m' ≠ addE 1 n le_rfl (zeroMon n) k := by
      intro hh
      have heq : addE 1 n le_rfl (zeroMon n) k = addE 1 n le_rfl (zeroMon n) k₀ := by
        rw [← hh, hk₀']
      exact hk (addE_injective 1 n le_rfl (zeroMon n) heq)
    rw [if_neg hne]
  · intro h; exact absurd (Finset.mem_univ k₀) h

/-- For `d = 1`, the coefficient vectors of the linear forms `⟨a_j,X⟩` (read off in the degree-`1`
monomial basis) span the space of linear forms vanishing at `x`. -/
theorem prodVec_span_eq_ker_one (n : ℕ) (hn : 1 ≤ n)
    (x : Fin (n + 1) → ℤ) (hx : IsPrim x) (a : Fin n → (Fin (n + 1) → ℤ))
    (ha : ∀ j, a j ∈ latOrth x) (hai : LinearIndependent ℤ a) :
    Submodule.span ℝ (Set.range (fun p : Mon 0 n × Fin n => prodVecR 1 n p.1 (a p.2)))
      = LinearMap.ker (evalLin 1 n x) := by
  haveI : Subsingleton (Mon 0 n) := subsingleton_Mon_zero n
  have hW : Submodule.span ℝ (Set.range (fun j : Fin n => intCastPi (a j)))
      = LinearMap.ker (dotLin x) := span_intCastPi_a_eq_ker_dotLin n x hx a ha hai
  have hrange1 : Set.range (fun p : Mon 0 n × Fin n => prodVecR 1 n p.1 (a p.2))
      = Set.range (fun j : Fin n => prodVecR 1 n (zeroMon n) (a j)) := by
    ext y; constructor
    · rintro ⟨p, hp⟩
      refine ⟨p.2, ?_⟩
      show prodVecR 1 n (zeroMon n) (a p.2) = y
      rw [← Subsingleton.elim p.1 (zeroMon n)]
      exact hp
    · rintro ⟨j, hj⟩
      exact ⟨(zeroMon n, j), hj⟩
  have hrange2 : Set.range (fun j : Fin n => prodVecR 1 n (zeroMon n) (a j))
      = Set.range (fun j : Fin n => mulVecR 1 n le_rfl (zeroMon n) (intCastPi (a j))) := by
    ext y; constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      show mulVecR 1 n le_rfl (zeroMon n) (intCastPi (a j)) = y
      rw [mulVecR_intCastPi]
      exact hj
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      show prodVecR 1 n (zeroMon n) (a j) = y
      rw [← mulVecR_intCastPi 1 n le_rfl (zeroMon n) (a j)]
      exact hj
  have himg : (mulVecR 1 n le_rfl (zeroMon n)) '' (Set.range (fun j : Fin n => intCastPi (a j)))
      = Set.range (fun j : Fin n => mulVecR 1 n le_rfl (zeroMon n) (intCastPi (a j))) := by
    ext y; constructor
    · rintro ⟨u, ⟨j, hj⟩, h2⟩
      have hj' : intCastPi (a j) = u := hj
      refine ⟨j, ?_⟩
      show mulVecR 1 n le_rfl (zeroMon n) (intCastPi (a j)) = y
      rw [hj']
      exact h2
    · rintro ⟨j, hj⟩
      exact ⟨intCastPi (a j), ⟨j, rfl⟩, hj⟩
  rw [hrange1, hrange2, ← himg, ← Submodule.map_span, hW]
  refine le_antisymm ?_ ?_
  · intro F hF
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hF
    rw [LinearMap.mem_ker]
    rw [evalLin_mulVecR, veroneseR_zeroMon, one_mul]
    rw [LinearMap.mem_ker] at hu
    exact hu
  · intro F hF
    refine Submodule.mem_map.mpr ⟨fun k => F (addE 1 n le_rfl (zeroMon n) k), ?_, ?_⟩
    · rw [LinearMap.mem_ker]
      have h1 := evalLin_mulVecR 1 n le_rfl (zeroMon n)
        (fun k => F (addE 1 n le_rfl (zeroMon n) k)) x
      rw [veroneseR_zeroMon, one_mul, mulVecR_zeroMon_apply] at h1
      rw [← h1]
      rw [LinearMap.mem_ker] at hF
      exact hF
    · exact mulVecR_zeroMon_apply n F

/-! ## The main theorem -/

/-- **The `Θ`-lift (one vector).**  If `n ≥ 1` and `Λ_x = latOrth x` contains `n` `ℤ`-independent
vectors `a j` of norm at most `B`, then `Λ_{ν_d(x)} = latOrth (veronese d n x)` contains
`NN d n - 1` `ℤ`-independent vectors of norm at most `B`, so its `(NN d n - 1)`-st successive
minimum is at most `B`. -/
theorem lam_latOrth_veronese_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (x : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (B : ℝ) (hB : 0 ≤ B) (a : Fin n → (Fin (n + 1) → ℤ))
    (ha : ∀ j, a j ∈ latOrth x) (hai : LinearIndependent ℤ a)
    (han : ∀ j, eNorm (a j) ≤ B) :
    lam (latOrth (veronese d n x)) (NN d n - 1) ≤ B := by
  have hx0 : x ≠ 0 := isPrim_ne_zero hx
  have hspan :
      Submodule.span ℝ (Set.range (fun p : Mon (d - 1) n × Fin n => prodVecR d n p.1 (a p.2)))
        = LinearMap.ker (evalLin d n x) := by
    rcases eq_or_lt_of_le hd with h | h
    · subst h
      exact prodVec_span_eq_ker_one n hn x hx a ha hai
    · exact prodVec_span_eq_ker d n (by omega) hn x hx a ha hai
  have hfin : Module.finrank ℝ
      (Submodule.span ℝ (Set.range (fun p : Mon (d - 1) n × Fin n => prodVecR d n p.1 (a p.2))))
      = NN d n - 1 := by
    rw [hspan]
    exact finrank_ker_evalLin d n (by omega) x hx0
  obtain ⟨f, hfind, hfmem⟩ :=
    exists_linearIndependent_fin_of_span_range
      (fun p : Mon (d - 1) n × Fin n => prodVecR d n p.1 (a p.2)) (NN d n - 1) hfin
  have hmem' : ∀ i : Fin (NN d n - 1),
      ∃ p : Mon (d - 1) n × Fin n, prodVecR d n p.1 (a p.2) = f i :=
    fun i => Set.mem_range.mp (hfmem i)
  choose g hg using hmem'
  let G : Fin (NN d n - 1) → (Mon d n → ℤ) := fun i => prodVec d n (g i).1 (a (g i).2)
  have hGcast : ∀ i, intCastPi (G i) = f i := fun i => by
    change intCastPi (prodVec d n (g i).1 (a (g i).2)) = f i
    rw [show intCastPi (prodVec d n (g i).1 (a (g i).2))
        = prodVecR d n (g i).1 (a (g i).2) from rfl, hg i]
  have hGind : LinearIndependent ℤ G := by
    refine linearIndependent_int_of_intCastPi ?_
    have hfun : (fun i => intCastPi (G i)) = f := funext hGcast
    rw [hfun]
    exact hfind
  have hGmem : ∀ i, G i ∈ latOrth (veronese d n x) := by
    intro i
    rw [mem_latOrth_veronese_iff d n (G i) x]
    change formEval d n (prodVec d n (g i).1 (a (g i).2)) x = 0
    have hpe := (prodVec_eval_eNorm d n hd (g i).1 (a (g i).2) x).1
    have hax := (mem_latOrth_iff n (a (g i).2) x).mp (ha (g i).2)
    rw [hpe, hax, mul_zero]
  have hGnorm : ∀ i, eNorm (G i) ≤ B := fun i => by
    change eNorm (prodVec d n (g i).1 (a (g i).2)) ≤ B
    rw [(prodVec_eval_eNorm d n hd (g i).1 (a (g i).2) x).2]
    exact han (g i).2
  rw [lam]
  exact csInf_le ⟨0, fun _ hr => hr.1⟩ ⟨hB, G, hGmem, hGind, hGnorm⟩

end Work.HP.Vero
