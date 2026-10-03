import Mathlib
import Submission.Work.ORLyndon.fm_certificate
import Submission.Work.ORLyndon.fm_step

set_option autoImplicit false

namespace Work.ORLyndon

open scoped BigOperators

/-- The family obtained from `a : ι → κ → ℚ` by Fourier–Motzkin elimination of the coordinate `k`:
rows `i` with `a i k = 0` are kept (projected to the complement of `k`), and for every pair
`(i, i')` with `0 < a i k` and `a i' k < 0` the resolvent row `a i k • β i' - a i' k • β i` is
added. -/
def projFam {κ ι : Type*} (a : ι → κ → ℚ) (k : κ) :
    ({i : ι // a i k = 0} ⊕ {p : ι × ι // 0 < a p.1 k ∧ a p.2 k < 0}) →
      ({j : κ // j ≠ k} → ℚ) :=
  fun e => match e with
    | Sum.inl i => fun j => a i.1 j.1
    | Sum.inr p => fun j => a p.1.1 k * a p.1.2 j.1 - a p.1.2 k * a p.1.1 j.1

theorem gordan_aux : ∀ (n : ℕ) {κ ι : Type*} [Fintype κ] [Fintype ι],
    Fintype.card κ = n → (a : ι → κ → ℚ) →
    (¬ ∃ lam : ι → ℚ, (∀ i, 0 ≤ lam i) ∧ lam ≠ 0 ∧ (∑ i, lam i • a i) = 0) →
    ∃ x : κ → ℚ, ∀ i, (∑ j, a i j * x j) > 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro κ ι _ _ hcard a h
    classical
    rcases Nat.eq_zero_or_pos (Fintype.card κ) with h0 | hpos
    · haveI hκ : IsEmpty κ := Fintype.card_eq_zero_iff.mp h0
      haveI hι : IsEmpty ι := by
        by_contra hne
        obtain ⟨i⟩ := not_isEmpty_iff.mp hne
        refine h ⟨fun i' => if i' = i then 1 else 0, ?_, ?_, ?_⟩
        · intro i'; by_cases h : i' = i <;> simp [h]
        · intro hzero
          have h1 : (1 : ℚ) = 0 := by simpa using congrFun hzero i
          exact one_ne_zero h1
        · ext j
          exact isEmptyElim j
      exact ⟨fun j => isEmptyElim j, fun i => isEmptyElim i⟩
    · obtain ⟨k⟩ := Fintype.card_pos_iff.mp hpos
      have h' : ¬ ∃ lam : ({i : ι // a i k = 0} ⊕
            {p : ι × ι // 0 < a p.1 k ∧ a p.2 k < 0}) → ℚ,
          (∀ e, 0 ≤ lam e) ∧ lam ≠ 0 ∧ (∑ e, lam e • projFam a k e) = 0 := by
        rintro ⟨lam, hlam0, hlamne, hlamsum⟩
        have hsum' : ∀ j : {j : κ // j ≠ k},
            (∑ e, lam e * (match e with
              | Sum.inl i => a i.1 j.1
              | Sum.inr p => a p.1.1 k * a p.1.2 j.1 - a p.1.2 k * a p.1.1 j.1)) = 0 := by
          intro j
          have h1 : (∑ e, lam e * projFam a k e j) = 0 := by
            have h2 : (∑ e, lam e • projFam a k e) j = 0 := by rw [hlamsum]; rfl
            simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h2
          have hcongr : (∑ e, lam e * (match e with
              | Sum.inl i => a i.1 j.1
              | Sum.inr p => a p.1.1 k * a p.1.2 j.1 - a p.1.2 k * a p.1.1 j.1))
              = ∑ e, lam e * projFam a k e j := by
            refine Finset.sum_congr rfl ?_
            intro e _
            cases e with
            | inl i => simp [projFam]
            | inr p => simp [projFam]
          rw [hcongr, h1]
        obtain ⟨ν, hν0, hνne, hν⟩ := fm_certificate a k lam hlam0 hlamne hsum'
        exact h ⟨ν, hν0, hνne, by
          ext j
          simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hν j⟩
      have hlt : Fintype.card {j : κ // j ≠ k} < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (p := fun j => j ≠ k) (x := k) (by simp)
      obtain ⟨y, hy⟩ := ih (Fintype.card {j : κ // j ≠ k}) hlt rfl (projFam a k) h'
      have hP : ∀ i, a i k = 0 → 0 < ∑ j : {j : κ // j ≠ k}, a i j.1 * y j := by
        intro i hi
        have h3 := hy (Sum.inl ⟨i, hi⟩)
        simpa only [projFam] using h3
      have hM : ∀ i i', 0 < a i k → a i' k < 0 →
          (∑ j : {j : κ // j ≠ k}, (a i' k) * a i j.1 * y j) <
            (∑ j : {j : κ // j ≠ k}, (a i k) * a i' j.1 * y j) := by
        intro i i' hi hi'
        have h3 := hy (Sum.inr ⟨(i, i'), ⟨hi, hi'⟩⟩)
        simp only [projFam] at h3
        have hsplit : (∑ j : {j : κ // j ≠ k}, (a i k * a i' j.1 - a i' k * a i j.1) * y j)
            = (∑ j : {j : κ // j ≠ k}, a i k * a i' j.1 * y j)
              - (∑ j : {j : κ // j ≠ k}, a i' k * a i j.1 * y j) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
        rw [hsplit] at h3
        linarith
      obtain ⟨x, hx⟩ := fm_step a k y hP hM
      exact ⟨x, hx⟩

/-- Gordan's theorem over `ℚ` for a finite-dimensional space. -/
theorem gordan_core {ι W : Type*} [Fintype ι] [AddCommGroup W] [Module ℚ W]
    [FiniteDimensional ℚ W] (φ : ι → Module.Dual ℚ W)
    (h : ¬ ∃ μ : ι → ℚ, (∀ i, 0 ≤ μ i) ∧ μ ≠ 0 ∧ (∑ i, μ i • φ i) = 0) :
    ∃ w : W, ∀ i, φ i w > 0 := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℚ W)) ℚ W := Module.finBasis ℚ W
  let a : ι → Fin (Module.finrank ℚ W) → ℚ := fun i j => φ i (b j)
  have ha : ¬ ∃ μ : ι → ℚ, (∀ i, 0 ≤ μ i) ∧ μ ≠ 0 ∧ (∑ i, μ i • a i) = 0 := by
    rintro ⟨μ, hμ0, hμne, hμsum⟩
    refine h ⟨μ, hμ0, hμne, ?_⟩
    refine LinearMap.ext_on b.span_eq ?_
    intro x hx
    obtain ⟨j, rfl⟩ := hx
    have h2 : (∑ i, μ i • a i) j = 0 := by rw [hμsum]; rfl
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.zero_apply, a] using h2
  obtain ⟨x, hx⟩ := gordan_aux (Fintype.card (Fin (Module.finrank ℚ W))) rfl a ha
  refine ⟨∑ j, x j • b j, fun i => ?_⟩
  have hcomm : (∑ j, x j * a i j) = (∑ j, a i j * x j) :=
    Finset.sum_congr rfl (fun j _ => mul_comm (x j) (a i j))
  have hval : φ i (∑ j, x j • b j) = ∑ j, x j * a i j := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [map_smul, smul_eq_mul]
  rw [hval, hcomm]
  exact hx i

theorem gordan_negative_separation {ι : Type*} [Fintype ι] {E : Type*} [AddCommGroup E]
    [Module ℚ E] (ell : ι → Module.Dual ℚ E)
    (h : ¬ ∃ mu : ι → ℚ, (∀ i, 0 ≤ mu i) ∧ mu ≠ 0 ∧ ∑ i, mu i • ell i = 0) :
    ∃ u : E, ∀ i, ell i u < 0 := by
  classical
  let Φ : E →ₗ[ℚ] (ι → ℚ) := LinearMap.pi ell
  let φ : ι → Module.Dual ℚ ↥(Φ.range) := fun i => (LinearMap.proj i).comp (Φ.range).subtype
  have hφ : ¬ ∃ μ : ι → ℚ, (∀ i, 0 ≤ μ i) ∧ μ ≠ 0 ∧ (∑ i, μ i • φ i) = 0 := by
    rintro ⟨μ, hμ0, hμne, hμsum⟩
    refine h ⟨μ, hμ0, hμne, ?_⟩
    have key : ∀ u : E, (∑ i, μ i • ell i) u
        = (∑ i, μ i • φ i) ⟨Φ u, LinearMap.mem_range.mpr ⟨u, rfl⟩⟩ := by
      intro u
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, φ, LinearMap.comp_apply,
        Submodule.subtype_apply, LinearMap.proj_apply, Φ, LinearMap.pi_apply]
    ext u
    have h1 : (∑ i, μ i • φ i) ⟨Φ u, LinearMap.mem_range.mpr ⟨u, rfl⟩⟩ = 0 := by
      rw [hμsum]; rfl
    rw [key u, h1]
    exact (LinearMap.zero_apply u).symm
  obtain ⟨y, hy⟩ := gordan_core φ hφ
  obtain ⟨u₀, hu₀⟩ := LinearMap.mem_range.mp y.2
  refine ⟨-u₀, fun i => ?_⟩
  have h1 : ell i u₀ = y.1 i := by
    have h2 := congrFun hu₀ i
    simpa only [Φ, LinearMap.pi_apply] using h2
  have h2 : 0 < y.1 i := by
    have h3 := hy i
    simpa only [φ, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply] using h3
  rw [map_neg, h1]
  linarith

end Work.ORLyndon
