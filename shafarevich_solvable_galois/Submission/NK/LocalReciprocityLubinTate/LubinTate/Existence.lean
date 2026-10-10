import Mathlib.RingTheory.MvPowerSeries.Substitution
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Step
import Submission.NK.LocalReciprocityLubinTate.ModPi.coeff_Dsub_mem_span
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Existence of a solution of Milne's Lemma I.2.11

The degree induction of Milne's Lemma 2.11: starting from the linear form `φ₁`, one solves the
equation `f ∘ φ = φ ∘ (X ↦ g(X))` degree by degree.  Divisibility of the coefficients of the
discrepancy by `π` (`coeff_Dsub_mem_span`) is what makes the correction at each degree solvable.
-/

open MvPowerSeries

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

variable {A : Type u} [CommRing A]

section Existence

variable {π : A} {q n : ℕ}

/-- Divisibility transfer: any element of `(π)` is divisible by `π - π^m` for `m ≥ 2`. -/
theorem dvd_pi_sub_pi_pow (hπ : NK.LocalReciprocityLubinTate.IsLubinTateCoeff π q)
    {m : ℕ} (hm : 2 ≤ m) {x : A} (hx : x ∈ Ideal.span {π}) :
    (π - π ^ m) ∣ x := by
  have hm1' : 1 ≤ m - 1 := by omega
  obtain ⟨u, hu⟩ := hπ.1 (m - 1) hm1'
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hx
  refine ⟨↑u⁻¹ * d, ?_⟩
  have hm1 : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos (n := m) (by omega)
  have hπu : π - π ^ m = π * ↑u := by
    rw [hu, mul_sub, mul_one, ← pow_succ', hm1]
  rw [hd, hπu, mul_assoc, ← mul_assoc (↑u) (↑u⁻¹) d, Units.mul_inv, one_mul]

/-- The correction coefficient `-(π - π^m)^{-1} x` (a choice, available when `π - π^m ∣ x`). -/
noncomputable def corrCoeff (π : A) (m : ℕ) (x : A) : A := by
  classical
  exact if h : (π - π ^ m) ∣ x then -(Classical.choose h) else 0

/-- The defining property of `corrCoeff`. -/
theorem mul_corrCoeff {π : A} {m : ℕ} {x : A} (h : (π - π ^ m) ∣ x) :
    (π - π ^ m) * corrCoeff π m x = -x := by
  classical
  have hspec : (π - π ^ m) * Classical.choose h = x := (Classical.choose_spec h).symm
  rw [corrCoeff, dif_pos h, mul_neg, hspec]

/-- The defining property of `corrCoeff`, in the other order. -/
theorem corrCoeff_mul {π : A} {m : ℕ} {x : A} (h : (π - π ^ m) ∣ x) :
    corrCoeff π m x * (π - π ^ m) = -x := by
  rw [mul_comm, mul_corrCoeff h]

/-- The degree-`m` correction of the discrepancy `F`. -/
noncomputable def corr (π : A) (m : ℕ) (F : MvPowerSeries (Fin n) A) :
    MvPowerSeries (Fin n) A :=
  fun s => if s.degree = m then corrCoeff π m (MvPowerSeries.coeff s F) else 0

theorem corr_coeff {π : A} {m : ℕ} (F : MvPowerSeries (Fin n) A) {s : Fin n →₀ ℕ}
    (hs : s.degree = m) :
    MvPowerSeries.coeff s (corr π m F) = corrCoeff π m (MvPowerSeries.coeff s F) := by
  show (if s.degree = m then corrCoeff π m (F s) else 0) = corrCoeff π m (F s)
  rw [if_pos hs]

theorem corr_coeff_of_ne {π : A} {m : ℕ} (F : MvPowerSeries (Fin n) A) {s : Fin n →₀ ℕ}
    (hs : s.degree ≠ m) : MvPowerSeries.coeff s (corr π m F) = 0 := by
  show (if s.degree = m then corrCoeff π m (F s) else 0) = 0
  rw [if_neg hs]

theorem corr_orderGe {π : A} {m : ℕ} (hm : 1 ≤ m) (F : MvPowerSeries (Fin n) A) :
    OrderGe m (corr π m F) := by
  intro s hs
  rw [corr_coeff_of_ne F (by omega)]

theorem corr_constantCoeff {π : A} {m : ℕ} (hm : 1 ≤ m) (F : MvPowerSeries (Fin n) A) :
    (corr π m F).constantCoeff = 0 := by
  have h0 : (0 : Fin n →₀ ℕ).degree = 0 := by simp
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    corr_coeff_of_ne F (by omega)]

/-- The sequence of partial solutions. -/
noncomputable def seq (π : A) (f g : MvPowerSeries (Fin 1) A) (φ₁ : MvPowerSeries (Fin n) A) :
    ℕ → MvPowerSeries (Fin n) A
  | 0 => φ₁
  | k + 1 => seq π f g φ₁ k + corr π (k + 2) (Dsub n f g (seq π f g φ₁ k))

theorem seq_zero (π : A) (f g : MvPowerSeries (Fin 1) A) (φ₁ : MvPowerSeries (Fin n) A) :
    seq π f g φ₁ 0 = φ₁ := rfl

theorem seq_succ (π : A) (f g : MvPowerSeries (Fin 1) A) (φ₁ : MvPowerSeries (Fin n) A)
    (k : ℕ) :
    seq π f g φ₁ (k + 1)
      = seq π f g φ₁ k + corr π (k + 2) (Dsub n f g (seq π f g φ₁ k)) := rfl

theorem seq_constantCoeff {π : A} {f g : MvPowerSeries (Fin 1) A} {φ₁ : MvPowerSeries (Fin n) A}
    (hφ₁ : φ₁.constantCoeff = 0) (k : ℕ) : (seq π f g φ₁ k).constantCoeff = 0 := by
  induction k with
  | zero => rw [seq_zero]; exact hφ₁
  | succ k ih =>
    rw [seq_succ, map_add, ih, corr_constantCoeff (π := π) (m := k + 2) (by omega), add_zero]

/-- One step of the partial solutions does not change the coefficients of degree `≤ k+1`. -/
theorem seq_step {π : A} {f g : MvPowerSeries (Fin 1) A} {φ₁ : MvPowerSeries (Fin n) A}
    (hφ₁ : φ₁.constantCoeff = 0) (k : ℕ) {s : Fin n →₀ ℕ} (hs : s.degree ≤ k + 1) :
    MvPowerSeries.coeff s (seq π f g φ₁ (k + 1))
      = MvPowerSeries.coeff s (seq π f g φ₁ k) := by
  rw [seq_succ, map_add,
    corr_coeff_of_ne (Dsub n f g (seq π f g φ₁ k)) (by omega), add_zero]

/-- The partial solutions are compatible: the coefficient of degree `≤ k+1` is already final. -/
theorem seq_stable {π : A} {f g : MvPowerSeries (Fin 1) A} {φ₁ : MvPowerSeries (Fin n) A}
    {k l : ℕ} (hkl : k ≤ l) (hφ₁ : φ₁.constantCoeff = 0) {s : Fin n →₀ ℕ}
    (hs : s.degree ≤ k + 1) :
    MvPowerSeries.coeff s (seq π f g φ₁ l) = MvPowerSeries.coeff s (seq π f g φ₁ k) := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l _ ih =>
    rw [seq_step (π := π) (f := f) (g := g) (φ₁ := φ₁) hφ₁ l (s := s) (by omega)]
    exact ih

/-- The initial partial solution `φ₁` satisfies the equation modulo terms of degree `2`. -/
theorem orderGe_two_Dsub_φ₁ {π : A} {q : ℕ} {f g : MvPowerSeries (Fin 1) A}
    (hf : NK.LocalReciprocityLubinTate.IsLubinTateSeries π q f)
    (hg : NK.LocalReciprocityLubinTate.IsLubinTateSeries π q g)
    {φ₁ : MvPowerSeries (Fin n) A} (hφ₁ : OrderGe 1 φ₁) :
    OrderGe 2 (Dsub n f g φ₁) := by
  have hf' : OrderGe 2 (f - MvPowerSeries.C π * MvPowerSeries.X (0 : Fin 1)) :=
    orderGe_two_sub_C_mul_X hf.1 hf.2.1
  have h0 : Dsub n f g (0 : MvPowerSeries (Fin n) A) = 0 := by
    have hz : (![0] : Fin 1 → MvPowerSeries (Fin n) A) = 0 := by
      funext j; fin_cases j; rfl
    have hf0 : MvPowerSeries.subst (![0] : Fin 1 → MvPowerSeries (Fin n) A) f = 0 := by
      rw [hz]
      exact MvPowerSeries.subst_zero_of_constantCoeff_zero hf.1
    have hg0 : MvPowerSeries.subst (gSub n g) (0 : MvPowerSeries (Fin n) A) = 0 := by
      rw [← MvPowerSeries.substAlgHom_apply
        (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => gSub_constantCoeff hg.1 i)]
      exact map_zero _
    rw [Dsub, hf0, hg0, sub_zero]
  intro s hs
  have h := coeff_Dsub_add (π := π) hf' hg.1 hg.2.1 (ψ := (0 : MvPowerSeries (Fin n) A))
    (δ := φ₁) (m := 1) le_rfl (orderGe_zero 1) hφ₁ s (by omega)
  rw [zero_add, h0] at h
  simpa using h

/-- The main induction: the partial solution `seq k` satisfies the equation modulo terms of
degree `k+2`. -/
theorem seq_orderGe {π : A} {q : ℕ} {f g : MvPowerSeries (Fin 1) A}
    (hπ : NK.LocalReciprocityLubinTate.IsLubinTateCoeff π q)
    (hpow : NK.LocalReciprocityLubinTate.IsFrobeniusPower π q)
    (hf : NK.LocalReciprocityLubinTate.IsLubinTateSeries π q f)
    (hg : NK.LocalReciprocityLubinTate.IsLubinTateSeries π q g)
    {φ₁ : MvPowerSeries (Fin n) A} (hφ₁ : OrderGe 1 φ₁) (k : ℕ) :
    OrderGe (k + 2) (Dsub n f g (seq π f g φ₁ k)) := by
  have hcc : φ₁.constantCoeff = 0 := hφ₁.constantCoeff
  have hf' : OrderGe 2 (f - MvPowerSeries.C π * MvPowerSeries.X (0 : Fin 1)) :=
    orderGe_two_sub_C_mul_X hf.1 hf.2.1
  induction k with
  | zero => simpa [seq_zero] using orderGe_two_Dsub_φ₁ hf hg hφ₁
  | succ k ih =>
    rw [seq_succ]
    intro s hs
    have h := coeff_Dsub_add (π := π) hf' hg.1 hg.2.1
      (ψ := seq π f g φ₁ k) (δ := corr π (k + 2) (Dsub n f g (seq π f g φ₁ k)))
      (m := k + 2) (by omega)
      (OrderGe.of_constantCoeff (seq_constantCoeff (π := π) hcc k))
      (corr_orderGe (π := π) (m := k + 2) (by omega) _) s (by omega)
    rcases eq_or_lt_of_le (show s.degree ≤ k + 2 by omega) with hsd | hsd
    · rw [h, corr_coeff _ hsd,
        corrCoeff_mul (dvd_pi_sub_pi_pow hπ (Nat.le_add_left 2 k)
          (NK.LocalReciprocityLubinTate.ModPi.coeff_Dsub_mem_span hπ hpow hf hg
            (seq_constantCoeff (π := π) hcc k) s)),
        add_neg_cancel]
    · rw [h, ih s (by omega), corr_coeff_of_ne _ (by omega), zero_mul, add_zero]

/-- The discrepancy `D` only depends on the coefficients of degree `< M` of its argument. -/
theorem coeff_Dsub_congr {π : A} {q n : ℕ} {f g : MvPowerSeries (Fin 1) A}
    (hf : NK.LocalReciprocityLubinTate.IsLubinTateSeries π q f)
    (hg : NK.LocalReciprocityLubinTate.IsLubinTateSeries π q g)
    {M : ℕ} (hM : 1 ≤ M) {φ ψ : MvPowerSeries (Fin n) A}
    (hφ : OrderGe 1 φ) (hψ : OrderGe 1 ψ) (h : OrderGe M (φ - ψ)) :
    OrderGe M (Dsub n f g φ - Dsub n f g ψ) := by
  have hf1 : OrderGe 1 f := OrderGe.of_constantCoeff hf.1
  have hG1 : ∀ i : Fin n, OrderGe 1 (gSub n g i) := fun i =>
    OrderGe.of_constantCoeff (gSub_constantCoeff hg.1 i)
  have hsubG : MvPowerSeries.HasSubst (gSub n g) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => gSub_constantCoeff hg.1 i
  have hfpart : OrderGe M (MvPowerSeries.subst ![φ] f - MvPowerSeries.subst ![ψ] f) := by
    have hgain := OrderGe.subst_sub (τ := Fin n) (a := (![φ] : Fin 1 → MvPowerSeries (Fin n) A))
      (b := (![ψ] : Fin 1 → MvPowerSeries (Fin n) A)) (q := f) (k := M) (κ := 1)
      hM (le_refl 1) (fun i => by fin_cases i; simpa using hφ)
      (fun i => by fin_cases i; simpa using hψ) (fun i => by fin_cases i; simpa using h) hf1
    exact hgain.mono (by omega)
  have hgpart : OrderGe M
      (MvPowerSeries.subst (gSub n g) φ - MvPowerSeries.subst (gSub n g) ψ) := by
    rw [← MvPowerSeries.subst_sub hsubG]
    exact OrderGe.subst hG1 h
  have hdecomp : Dsub n f g φ - Dsub n f g ψ
      = (MvPowerSeries.subst ![φ] f - MvPowerSeries.subst ![ψ] f)
        - (MvPowerSeries.subst (gSub n g) φ - MvPowerSeries.subst (gSub n g) ψ) := by
    simp only [Dsub]
    ring
  rw [hdecomp]
  exact hfpart.sub hgpart

/-- Unfolding `Dsub n f g φ = 0` into the substitution identity of Milne's Lemma 2.11. -/
theorem Dsub_eq_zero_iff {n : ℕ} {f g : MvPowerSeries (Fin 1) A} {φ : MvPowerSeries (Fin n) A} :
    Dsub n f g φ = 0 ↔
      MvPowerSeries.subst ![φ] f
        = φ.subst (fun i => MvPowerSeries.subst ![MvPowerSeries.X i] g) := by
  have h : gSub n g = fun i => MvPowerSeries.subst ![MvPowerSeries.X i] g := rfl
  rw [Dsub, sub_eq_zero, h]

/-- **Existence** in Milne's Lemma 2.11. -/
theorem exists_sol {π : A} {q : ℕ} {f g : MvPowerSeries (Fin 1) A}
    (hπ : NK.LocalReciprocityLubinTate.IsLubinTateCoeff π q)
    (hpow : NK.LocalReciprocityLubinTate.IsFrobeniusPower π q)
    (hf : NK.LocalReciprocityLubinTate.IsLubinTateSeries π q f)
    (hg : NK.LocalReciprocityLubinTate.IsLubinTateSeries π q g)
    {φ₁ : MvPowerSeries (Fin n) A} (hφ₁ : φ₁.constantCoeff = 0 ∧
      ∀ s : Fin n →₀ ℕ, 2 ≤ s.degree → MvPowerSeries.coeff s φ₁ = 0) :
    ∃ φ : MvPowerSeries (Fin n) A,
      (∀ s : Fin n →₀ ℕ, s.degree ≤ 1 →
        MvPowerSeries.coeff s φ = MvPowerSeries.coeff s φ₁) ∧
      Dsub n f g φ = 0 := by
  have hcc : φ₁.constantCoeff = 0 := hφ₁.1
  have hφ₁' : OrderGe 1 φ₁ := OrderGe.of_constantCoeff hcc
  let φ : MvPowerSeries (Fin n) A := fun s => MvPowerSeries.coeff s (seq π f g φ₁ s.degree)
  have hφeval : ∀ t : Fin n →₀ ℕ,
      MvPowerSeries.coeff t φ = MvPowerSeries.coeff t (seq π f g φ₁ t.degree) := fun t => rfl
  have hφ1mg : OrderGe 1 φ := by
    intro t ht
    rw [hφeval t]
    have ht0 : t = 0 := by
      ext i
      have h1 := Finsupp.le_degree i t
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    subst ht0
    rw [show ((0 : Fin n →₀ ℕ).degree) = 0 from by simp, seq_zero]
    exact hcc
  refine ⟨φ, ?_, ?_⟩
  · intro s hs
    rw [hφeval s]
    exact (seq_stable (π := π) (f := f) (g := g) (φ₁ := φ₁) (k := 0) (l := s.degree)
      (Nat.zero_le _) hcc (s := s) (by omega)).trans (by rw [seq_zero])
  · ext s
    have hagree : OrderGe (s.degree + 1) (φ - seq π f g φ₁ s.degree) := by
      intro t ht
      rw [map_sub, hφeval t,
        seq_stable (π := π) (f := f) (g := g) (φ₁ := φ₁) (k := t.degree) (l := s.degree)
          (by omega) hcc (s := t) (by omega), sub_self]
    have hcongr := coeff_Dsub_congr hf hg (M := s.degree + 1) (by omega) hφ1mg
      (OrderGe.of_constantCoeff (seq_constantCoeff (π := π) hcc s.degree)) hagree
    have hval := hcongr s (by omega)
    rw [map_sub, sub_eq_zero] at hval
    rw [hval]
    exact seq_orderGe hπ hpow hf hg hφ₁' s.degree s (by omega)

end Existence

end NK.LocalReciprocityLubinTate.LubinTate
