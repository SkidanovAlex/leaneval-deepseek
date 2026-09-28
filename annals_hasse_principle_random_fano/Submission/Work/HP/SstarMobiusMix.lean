import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.SstarAux.dvd_mul_iff_dvd_div_gcd

set_option autoImplicit false
noncomputable section

open Filter Finset MeasureTheory
open scoped RealInnerProductSpace

attribute [local instance] Classical.propDecidable

namespace Work.HP

/-! ## Elementary scaling lemmas for `eNorm`, `rNorm`, `toR`, `dotR`, `Cgam` -/

lemma eNorm_nsmul {ι : Type*} [Fintype ι] (v : ι → ℤ) (m : ℕ) :
    eNorm (m • v) = (m : ℝ) * eNorm v := by
  unfold eNorm
  have h1 : (∑ i, (((m • v) i : ℤ) : ℝ) ^ 2) = (m : ℝ) ^ 2 * ∑ i, ((v i : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h2 : ((m • v) i : ℤ) = m * v i := by simp
    rw [h2]
    push_cast
    ring
  rw [h1, Real.sqrt_mul (sq_nonneg (m : ℝ)), Real.sqrt_sq (Nat.cast_nonneg m)]

lemma rNorm_nsmul {ι : Type*} [Fintype ι] (v : ι → ℝ) (m : ℕ) :
    rNorm (m • v) = (m : ℝ) * rNorm v := by
  unfold rNorm
  have h1 : (∑ i, ((m • v) i) ^ 2) = (m : ℝ) ^ 2 * ∑ i, (v i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h2 : (m • v) i = (m : ℝ) * v i := by simp
    rw [h2]; ring
  rw [h1, Real.sqrt_mul (sq_nonneg (m : ℝ)), Real.sqrt_sq (Nat.cast_nonneg m)]

lemma toR_nsmul {ι : Type*} (v : ι → ℤ) (m : ℕ) : toR (m • v) = m • toR v := by
  funext i
  simp [toR, nsmul_eq_mul]

lemma dotR_nsmul {ι : Type*} [Fintype ι] (v t : ι → ℝ) (m : ℕ) :
    dotR v (m • t) = (m : ℝ) * dotR v t := by
  simp only [dotR]
  have h : ∀ i, (m • t) i = (m : ℝ) * t i := fun i => by simp
  simp_rw [h]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma Cgam_nsmul {ι : Type*} [Fintype ι] {v t : ι → ℝ} {γ : ℝ} {m : ℕ} (hm : 1 ≤ m) :
    (m • t) ∈ Cgam v γ ↔ t ∈ Cgam v γ := by
  simp only [Cgam, Set.mem_setOf_eq]
  rw [dotR_nsmul, rNorm_nsmul, abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
  have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have key : rNorm v * ((m : ℝ) * rNorm t) / (2 * γ) = (m : ℝ) * (rNorm v * rNorm t / (2 * γ)) := by
    ring
  rw [key]
  exact mul_le_mul_iff_right₀ hm'

lemma TmixSet_nsmul (d n : ℕ) [DecidableEq (Mon d n)] (y : Fin (n + 1) → ℤ)
    (A α : ℝ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (b : Mon d n → ℤ) :
    b ∈ TmixSet d n y (A / ℓ) α ↔ (ℓ • b) ∈ TmixSet d n y A α := by
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  rw [TmixSet, TmixSet]
  simp only [Set.mem_setOf_eq]
  have h2 : toR (ℓ • b) ∈ Cgam (toR (veronese d n y)) α ↔
      toR b ∈ Cgam (toR (veronese d n y)) α := by
    rw [toR_nsmul]; exact Cgam_nsmul hℓ
  rw [eNorm_nsmul, h2]
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨by rw [mul_comm]; exact (le_div_iff₀ hℓ').mp h, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨(le_div_iff₀ hℓ').mpr (by rw [mul_comm]; exact h), hc⟩

/-! ## Lattice scaling lemmas -/

lemma mem_latMod_iff_M {ι : Type*} [Fintype ι] (c : ι → ℤ) (Q : ℕ) (b : ι → ℤ) :
    b ∈ latMod c Q ↔ (Q : ℤ) ∣ Fintype.linearCombination ℤ c b := by
  rw [latMod, Submodule.mem_comap, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have ha' : a * (Q : ℤ) = Fintype.linearCombination ℤ c b := by simpa [smul_eq_mul] using ha
    rw [← ha', mul_comm]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simp only [smul_eq_mul]
    rw [hk, mul_comm]

lemma latMod_nsmul {ι : Type*} [Fintype ι] (c b : ι → ℤ) (Q ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (ℓ • b) ∈ latMod c Q ↔ b ∈ latMod c (Q / Nat.gcd ℓ Q) := by
  rw [mem_latMod_iff_M, mem_latMod_iff_M]
  have hmap : Fintype.linearCombination ℤ c (ℓ • b)
      = (ℓ : ℤ) * Fintype.linearCombination ℤ c b := by
    rw [map_nsmul, nsmul_eq_mul]
  rw [hmap]
  exact SstarAux.dvd_mul_iff_dvd_div_gcd ℓ Q hℓ _

lemma latOrth_nsmul {ι : Type*} [Fintype ι] (c b : ι → ℤ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (ℓ • b) ∈ latOrth c ↔ b ∈ latOrth c := by
  simp only [latOrth, LinearMap.mem_ker]
  have hmap : Fintype.linearCombination ℤ c (ℓ • b)
      = (ℓ : ℤ) * Fintype.linearCombination ℤ c b := by
    rw [map_nsmul, nsmul_eq_mul]
  rw [hmap]
  have hℓint : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left hℓint
  · intro h; rw [h, mul_zero]

lemma GamMix_nsmul (d n : ℕ) [DecidableEq (Mon d n)] (x y : Fin (n + 1) → ℤ)
    (Q ℓ : ℕ) (hℓ : 1 ≤ ℓ) (b : Mon d n → ℤ) :
    b ∈ GamMix d n x y (Q / Nat.gcd ℓ Q) ↔ (ℓ • b) ∈ GamMix d n x y Q := by
  rw [GamMix, GamMix, Submodule.mem_inf, Submodule.mem_inf]
  exact and_congr (latOrth_nsmul (veronese d n x) b hℓ).symm
    (latMod_nsmul (veronese d n y) b Q ℓ hℓ).symm

/-! ## Primitivity -/

lemma IsPrim.ne_zero {ι : Type*} [Fintype ι] {v : ι → ℤ} (h : IsPrim v) : v ≠ 0 := by
  rintro rfl
  rw [IsPrim] at h
  have hz : Finset.univ.gcd (0 : ι → ℤ) = 0 := by
    rw [Finset.gcd_eq_zero_iff]; intro x _; rfl
  rw [hz] at h
  exact one_ne_zero h.symm

lemma natAbs_cast_le_eNorm {ι : Type*} [Fintype ι] (v : ι → ℤ) (i : ι) :
    ((v i).natAbs : ℝ) ≤ eNorm v := by
  have h : ((v i).natAbs : ℝ) = |(v i : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [h]
  exact abs_apply_le_eNorm v i

lemma IsPrim.nsmul_ne_zero {ι : Type*} {v : ι → ℤ} {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : v ≠ 0) :
    (ℓ • v) ≠ 0 := by
  intro h0
  apply h
  funext i
  have h1 : (ℓ : ℤ) * v i = 0 := by
    have := congrFun h0 i
    simpa [Pi.zero_apply, nsmul_eq_mul] using this
  exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast hℓ)

/-! ## Möbius sums -/

lemma sum_divisors_moebius (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (R := ℝ)
    (f := (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) (x := n)
  rw [ArithmeticFunction.coe_moebius_mul_coe_zeta] at h
  have h2 : (1 : ArithmeticFunction ℝ) n = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) := h
  rw [← h2, ArithmeticFunction.one_apply]

lemma moebius_sum_prim {ι : Type*} [Fintype ι] (v : ι → ℤ) (hv : v ≠ 0)
    (A : ℝ) (hA : eNorm v ≤ A) [Decidable (IsPrim v)] :
    ∑ ℓ ∈ (Finset.Icc 1 ⌊A⌋₊).filter (fun (ℓ : ℕ) => ∀ i, (ℓ : ℤ) ∣ v i),
        (ArithmeticFunction.moebius ℓ : ℝ) = if IsPrim v then 1 else 0 := by
  set g : ℤ := Finset.univ.gcd v with hg
  have hg0 : g ≠ 0 := by
    intro h
    have hv0 : Finset.univ.gcd v = 0 := by rw [← hg, h]
    apply hv
    funext i
    exact (Finset.gcd_eq_zero_iff.mp hv0) i (Finset.mem_univ i)
  have hgnn : 0 ≤ g := by rw [hg]; exact Finset.Int.finsetGcd_nonneg
  have hgcd : g = (g.toNat : ℤ) := (Int.toNat_of_nonneg hgnn).symm
  have hgvd : ∀ i, g ∣ v i := fun i => by rw [hg]; exact Finset.gcd_dvd (Finset.mem_univ i)
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
  have hset : (Finset.Icc 1 ⌊A⌋₊).filter (fun (ℓ : ℕ) => ∀ i, (ℓ : ℤ) ∣ v i)
      = g.toNat.divisors := by
    ext ℓ
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨?_, ?_⟩
      · have hdiv : (ℓ : ℤ) ∣ g := by
          rw [hg]; exact Finset.dvd_gcd (fun i _ => h3 i)
        have hdiv' : (ℓ : ℤ) ∣ (g.toNat : ℤ) := by rwa [Int.toNat_of_nonneg hgnn]
        have hnat := Int.natCast_dvd.mp hdiv'
        rwa [Int.natAbs_natCast] at hnat
      · intro hz
        exact hg0 (by rw [hgcd, hz]; simp)
    · rintro ⟨hdvd, hne⟩
      have h1g : (ℓ : ℤ) ∣ g := by
        have h1 : (ℓ : ℤ) ∣ (g.toNat : ℤ) := by exact_mod_cast hdvd
        rwa [Int.toNat_of_nonneg hgnn] at h1
      have hgle : g.toNat ≤ (v i₀).natAbs := by
        have hgv : g ∣ v i₀ := hgvd i₀
        have hgv' : (g.toNat : ℤ) ∣ v i₀ := by rwa [← Int.toNat_of_nonneg hgnn] at hgv
        exact Nat.le_of_dvd (Int.natAbs_pos.mpr hi₀) (Int.natCast_dvd.mp hgv')
      have hgA : (g.toNat : ℝ) ≤ A := by
        calc (g.toNat : ℝ) ≤ ((v i₀).natAbs : ℝ) := by exact_mod_cast hgle
          _ ≤ eNorm v := natAbs_cast_le_eNorm v i₀
          _ ≤ A := hA
      have hle : ℓ ≤ g.toNat := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hne), le_trans hle (Nat.le_floor hgA)⟩,
        fun i => dvd_trans h1g (hgvd i)⟩
  rw [hset, sum_divisors_moebius]
  have hiff : IsPrim v ↔ g.toNat = 1 := by
    rw [IsPrim, ← hg, hgcd]
    exact Int.ofNat_inj
  by_cases hp : IsPrim v
  · rw [if_pos hp, if_pos (hiff.mp hp)]
  · rw [if_neg hp, if_neg (fun h => hp (hiff.mpr h))]

/-! ## The height box -/

/-- The box of integer vectors of coordinates bounded by `⌈max A 0⌉`. -/
def nBox (d n : ℕ) [DecidableEq (Mon d n)] (A : ℝ) : Finset (Mon d n → ℤ) :=
  Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(⌈max A 0⌉₊ : ℤ)) (⌈max A 0⌉₊ : ℤ))

lemma mem_nBox_of_eNorm_le {d n : ℕ} [DecidableEq (Mon d n)] {A : ℝ} {a : Mon d n → ℤ}
    (ha : eNorm a ≤ A) : a ∈ nBox d n A := by
  rw [nBox, Fintype.mem_piFinset]
  intro m
  rw [Finset.mem_Icc]
  set M : ℕ := ⌈max A 0⌉₊ with hM
  have hMle : A ≤ (M : ℝ) := le_trans (le_max_left A 0) (Nat.le_ceil _)
  have h1 : |(a m : ℝ)| ≤ (M : ℝ) := le_trans (abs_apply_le_eNorm a m) (le_trans ha hMle)
  obtain ⟨h2, h3⟩ := abs_le.mp h1
  exact ⟨by exact_mod_cast h2, by exact_mod_cast h3⟩

/-! ## Converting `Sstar` / `Sk` to sums over the box -/

lemma Sstar_eq_sum_nBox (d n : ℕ) [DecidableEq (Mon d n)] (k : ℕ)
    (L : Submodule ℤ (Mon d n → ℤ)) (R : Set (Mon d n → ℤ)) {A : ℝ}
    (hR : ∀ a, a ∈ R → eNorm a ≤ A) :
    Sstar d n k L R = ∑ a ∈ nBox d n A,
      (if a ∈ L ∧ IsPrim a ∧ a ∈ R then 1 / eNorm a ^ k else 0) := by
  classical
  rw [Sstar, finsum_mem_def]
  have hbox : Function.support (Set.indicator {a : Mon d n → ℤ | a ∈ L ∧ IsPrim a ∧ a ∈ R}
      (fun a => 1 / eNorm a ^ k)) ⊆ ↑(nBox d n A) := by
    intro a ha
    rw [Function.mem_support] at ha
    by_contra hb
    apply ha
    rw [Set.indicator_apply, if_neg (fun hmem => hb (mem_nBox_of_eNorm_le (hR a hmem.2.2)))]
  rw [finsum_eq_finsetSum_of_support_subset _ hbox]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Set.indicator_apply]
  by_cases h : a ∈ L ∧ IsPrim a ∧ a ∈ R
  · have hS : a ∈ {a : Mon d n → ℤ | a ∈ L ∧ IsPrim a ∧ a ∈ R} := h
    rw [if_pos hS, if_pos h]
  · have hS : a ∉ {a : Mon d n → ℤ | a ∈ L ∧ IsPrim a ∧ a ∈ R} := h
    rw [if_neg hS, if_neg h]

lemma Sk_eq_sum_nBox (d n : ℕ) [DecidableEq (Mon d n)] (k : ℕ)
    (L : Submodule ℤ (Mon d n → ℤ)) (R : Set (Mon d n → ℤ)) {A : ℝ}
    (hR : ∀ a, a ∈ R → eNorm a ≤ A) :
    Sk d n k L R = ∑ a ∈ nBox d n A,
      (if a ∈ L ∧ a ≠ 0 ∧ a ∈ R then 1 / eNorm a ^ k else 0) := by
  classical
  rw [Sk, finsum_mem_def]
  have hbox : Function.support (Set.indicator {a : Mon d n → ℤ | a ∈ L ∧ a ≠ 0 ∧ a ∈ R}
      (fun a => 1 / eNorm a ^ k)) ⊆ ↑(nBox d n A) := by
    intro a ha
    rw [Function.mem_support] at ha
    by_contra hb
    apply ha
    rw [Set.indicator_apply, if_neg (fun hmem => hb (mem_nBox_of_eNorm_le (hR a hmem.2.2)))]
  rw [finsum_eq_finsetSum_of_support_subset _ hbox]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Set.indicator_apply]
  by_cases h : a ∈ L ∧ a ≠ 0 ∧ a ∈ R
  · have hS : a ∈ {a : Mon d n → ℤ | a ∈ L ∧ a ≠ 0 ∧ a ∈ R} := h
    rw [if_pos hS, if_pos h]
  · have hS : a ∉ {a : Mon d n → ℤ | a ∈ L ∧ a ≠ 0 ∧ a ∈ R} := h
    rw [if_neg hS, if_neg h]

/-! ## Dividing a vector coordinatewise -/

/-- Coordinatewise integer division by `ℓ`. -/
def divVec {ι : Type*} (ℓ : ℕ) (a : ι → ℤ) : ι → ℤ := fun i => a i / (ℓ : ℤ)

lemma nsmul_divVec {ι : Type*} (ℓ : ℕ) (a : ι → ℤ) (h : ∀ i, (ℓ : ℤ) ∣ a i) :
    ℓ • divVec ℓ a = a := by
  funext i
  rw [show (ℓ • divVec ℓ a) i = (ℓ : ℤ) * (a i / (ℓ : ℤ)) by simp [divVec, nsmul_eq_mul]]
  exact Int.mul_ediv_cancel' (h i)

/-! ## Weight scaling -/

lemma W_nsmul (d n : ℕ) (k ℓ : ℕ) (hℓ : 1 ≤ ℓ) (b : Mon d n → ℤ) :
    (1 / eNorm (ℓ • b) ^ k) = (1 / (ℓ : ℝ) ^ k) * (1 / eNorm b ^ k) := by
  rw [eNorm_nsmul, one_div, one_div, one_div, ← mul_inv, mul_pow]

theorem SstarMobiusMix (d n : ℕ) [DecidableEq (Mon d n)] (x y : Fin (n + 1) → ℤ)
    (k : ℕ) (A α : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) (hA : 1 ≤ A) :
    Sstar d n k (GamMix d n x y Q) (TmixSet d n y A α) =
      ∑ ℓ ∈ Finset.Icc 1 ⌊A⌋₊,
        ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ k) *
          Sk d n k (GamMix d n x y (Q / Nat.gcd ℓ Q)) (TmixSet d n y (A / ℓ) α) := by
  classical
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hLHS := Sstar_eq_sum_nBox (d := d) (n := n) k (GamMix d n x y Q) (TmixSet d n y A α)
      (fun a ha => ha.1)
  rw [hLHS]
  have hstep : ∀ ℓ ∈ Finset.Icc 1 ⌊A⌋₊,
      ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ k) *
        Sk d n k (GamMix d n x y (Q / Nat.gcd ℓ Q)) (TmixSet d n y (A / ℓ) α)
      = ∑ a ∈ nBox d n A,
          (if a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ a ∈ TmixSet d n y A α ∧ (∀ i, (ℓ : ℤ) ∣ a i)
            then (ArithmeticFunction.moebius ℓ : ℝ) * (1 / eNorm a ^ k) else 0) := by
    intro ℓ hℓmem
    have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓmem).1
    have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
    have hℓint : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
    have hℓne : ℓ ≠ 0 := by omega
    rw [Sk_eq_sum_nBox (d := d) (n := n) k (GamMix d n x y (Q / Nat.gcd ℓ Q))
        (TmixSet d n y (A / ℓ) α) (A := A) (fun b hb => by
          have h1 : eNorm b ≤ A / ℓ := hb.1
          have h2 : A / ℓ ≤ A := by
            rw [div_le_iff₀ hℓpos]
            nlinarith [hA0, (by exact_mod_cast hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ))]
          exact le_trans h1 h2)]
    rw [Finset.mul_sum]
    have hper : ∀ b ∈ nBox d n A,
        (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ k *
          (if b ∈ GamMix d n x y (Q / Nat.gcd ℓ Q) ∧ b ≠ 0 ∧ b ∈ TmixSet d n y (A / ℓ) α
            then 1 / eNorm b ^ k else 0)
        = (if (ℓ • b) ∈ GamMix d n x y Q ∧ (ℓ • b) ≠ 0 ∧ (ℓ • b) ∈ TmixSet d n y A α
            then (ArithmeticFunction.moebius ℓ : ℝ) * (1 / eNorm (ℓ • b) ^ k) else 0) := by
      intro b _
      have hcondV : (b ∈ GamMix d n x y (Q / Nat.gcd ℓ Q) ∧ b ≠ 0 ∧ b ∈ TmixSet d n y (A / ℓ) α)
          ↔ ((ℓ • b) ∈ GamMix d n x y Q ∧ (ℓ • b) ≠ 0 ∧ (ℓ • b) ∈ TmixSet d n y A α) := by
        refine and_congr (GamMix_nsmul d n x y Q ℓ hℓ1 b) (and_congr ?_ (TmixSet_nsmul d n y A α ℓ hℓ1 b))
        exact ⟨fun h => IsPrim.nsmul_ne_zero hℓne h, fun h h0 => h (by rw [h0, smul_zero])⟩
      by_cases hc : (ℓ • b) ∈ GamMix d n x y Q ∧ (ℓ • b) ≠ 0 ∧ (ℓ • b) ∈ TmixSet d n y A α
      · have hcL : b ∈ GamMix d n x y (Q / Nat.gcd ℓ Q) ∧ b ≠ 0 ∧ b ∈ TmixSet d n y (A / ℓ) α :=
          hcondV.mpr hc
        rw [if_pos hcL, if_pos hc, W_nsmul d n k ℓ hℓ1 b]
        ring
      · have hcL : ¬(b ∈ GamMix d n x y (Q / Nat.gcd ℓ Q) ∧ b ≠ 0 ∧ b ∈ TmixSet d n y (A / ℓ) α) :=
          fun h => hc (hcondV.mp h)
        rw [if_neg hcL, if_neg hc, mul_zero]
    rw [Finset.sum_congr rfl hper]
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_bij (fun (b : Mon d n → ℤ) (_ : b ∈ _) => ℓ • b) ?_ ?_ ?_ ?_
    · intro b hb
      rw [Finset.mem_filter] at hb ⊢
      exact ⟨mem_nBox_of_eNorm_le hb.2.2.2.1, hb.2.1, hb.2.2.1, hb.2.2.2,
        fun i => by
          have hbi : (ℓ • b) i = (ℓ : ℤ) * b i := by simp [nsmul_eq_mul]
          rw [hbi]; exact ⟨b i, rfl⟩⟩
    · intro b1 _ b2 _ heq
      funext i
      have h := congrFun heq i
      have h2 : (ℓ : ℤ) * b1 i = (ℓ : ℤ) * b2 i := by simpa [nsmul_eq_mul] using h
      exact mul_left_cancel₀ hℓint h2
    · intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨haX, haG, hane, haT, hadiv⟩ := ha
      have hdiv : ℓ • divVec ℓ a = a := nsmul_divVec ℓ a hadiv
      refine ⟨divVec ℓ a, ?_, hdiv⟩
      rw [Finset.mem_filter]
      refine ⟨?_, ?_, ?_, ?_⟩
      · apply mem_nBox_of_eNorm_le
        have hn := eNorm_nsmul (divVec ℓ a) ℓ
        rw [hdiv] at hn
        have h2 : eNorm (divVec ℓ a) ≤ A / ℓ := by
          rw [le_div_iff₀ hℓpos, mul_comm, ← hn]
          exact haT.1
        have h3 : A / ℓ ≤ A := by
          rw [div_le_iff₀ hℓpos]
          nlinarith [hA0, (by exact_mod_cast hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ))]
        exact le_trans h2 h3
      · rw [hdiv]; exact haG
      · rw [hdiv]; exact hane
      · rw [hdiv]; exact haT
    · intro b hb
      rfl
  have hfinal : ∀ a ∈ nBox d n A,
      (if a ∈ GamMix d n x y Q ∧ IsPrim a ∧ a ∈ TmixSet d n y A α then 1 / eNorm a ^ k else 0)
      = ∑ ℓ ∈ Finset.Icc 1 ⌊A⌋₊,
          (if a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ a ∈ TmixSet d n y A α ∧ (∀ i, (ℓ : ℤ) ∣ a i)
            then (ArithmeticFunction.moebius ℓ : ℝ) * (1 / eNorm a ^ k) else 0) := by
    intro a _
    by_cases hbase : a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ a ∈ TmixSet d n y A α
    · obtain ⟨hG, hne, hT⟩ := hbase
      have hthis : ∀ ℓ ∈ Finset.Icc 1 ⌊A⌋₊,
          (if a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ a ∈ TmixSet d n y A α ∧ (∀ i, (ℓ : ℤ) ∣ a i)
            then (ArithmeticFunction.moebius ℓ : ℝ) * (1 / eNorm a ^ k) else 0)
          = (if (∀ i, (ℓ : ℤ) ∣ a i)
              then (ArithmeticFunction.moebius ℓ : ℝ) * (1 / eNorm a ^ k) else 0) := by
        intro ℓ _
        by_cases hd : (∀ i, (ℓ : ℤ) ∣ a i)
        · rw [if_pos (show a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ a ∈ TmixSet d n y A α ∧
              (∀ i, (ℓ : ℤ) ∣ a i) from ⟨hG, hne, hT, hd⟩), if_pos hd]
        · rw [if_neg (show ¬(a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ a ∈ TmixSet d n y A α ∧
              (∀ i, (ℓ : ℤ) ∣ a i)) from fun h => hd h.2.2.2), if_neg hd]
      have hsum : (∑ ℓ ∈ Finset.Icc 1 ⌊A⌋₊,
            (if a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ a ∈ TmixSet d n y A α ∧ (∀ i, (ℓ : ℤ) ∣ a i)
              then (ArithmeticFunction.moebius ℓ : ℝ) * (1 / eNorm a ^ k) else 0))
          = (if IsPrim a then 1 else 0) * (1 / eNorm a ^ k) := by
        rw [Finset.sum_congr rfl hthis]
        rw [← Finset.sum_filter, ← Finset.sum_mul, moebius_sum_prim a hne A hT.1]
      have hL : (if a ∈ GamMix d n x y Q ∧ IsPrim a ∧ a ∈ TmixSet d n y A α
            then 1 / eNorm a ^ k else 0)
          = (if IsPrim a then 1 else 0) * (1 / eNorm a ^ k) := by
        by_cases hp : IsPrim a
        · rw [if_pos ⟨hG, hp, hT⟩, if_pos hp, one_mul]
        · rw [if_neg (fun h => hp h.2.1), if_neg hp, zero_mul]
      rw [hL, hsum]
    · have hL0 : (if a ∈ GamMix d n x y Q ∧ IsPrim a ∧ a ∈ TmixSet d n y A α
            then 1 / eNorm a ^ k else 0) = 0 := by
        rw [if_neg (fun h => hbase ⟨h.1, IsPrim.ne_zero h.2.1, h.2.2⟩)]
      have hsum0 : (∑ ℓ ∈ Finset.Icc 1 ⌊A⌋₊,
            (if a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ a ∈ TmixSet d n y A α ∧ (∀ i, (ℓ : ℤ) ∣ a i)
              then (ArithmeticFunction.moebius ℓ : ℝ) * (1 / eNorm a ^ k) else 0)) = 0 := by
        rw [Finset.sum_eq_zero]
        intro ℓ _
        rw [if_neg (fun hc => hbase ⟨hc.1, hc.2.1, hc.2.2.1⟩)]
      rw [hL0, hsum0]
  rw [Finset.sum_congr rfl hstep]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a ha => hfinal a ha)

end Work.HP
