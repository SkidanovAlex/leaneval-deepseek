import Mathlib
import Submission.Commons.Algebra.Lie.E8_Msub_weight_finrank

namespace Commons.Algebra.Lie

open scoped BigOperators
open Commons.LinearAlgebra.Matrix.Cartan

noncomputable section

/-- The lattice pairing `⟪β,β'⟫ = ∑ i, β i * (A⁻¹ β') i`. -/
def e8pair (β β' : Fin 8 → ℤ) : ℤ := ∑ i, β i * (E8NormTwo.E8inv.mulVec β') i

lemma e8pair_eq_qZ (β : Fin 8 → ℤ) : e8pair β β = E8NormTwo.qZ β := by
  rw [e8pair, E8NormTwo.qZ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => by ring)

/-- For a positive root `β`, `⟪β,β⟫ = 2`. -/
lemma e8pair_self_of_mem_P {β : Fin 8 → ℤ} (hβ : β ∈ E8posRoots.P) : e8pair β β = 2 := by
  rw [e8pair_eq_qZ]
  exact posRoot_qZ ⟨β, hβ⟩

/-- If `n β + m β' = γ` with `β, β'` positive roots and `n,m ≥ 1`, then `n,m ≤ (ht γ).toNat`. -/
lemma nsmul_add_nsmul_le_ht_of_mem_P {β β' γ : Fin 8 → ℤ} (hβ : β ∈ E8posRoots.P)
    (hβ' : β' ∈ E8posRoots.P) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : n • β + m • β' = γ) : n ≤ (E8NormTwo.e8ht γ).toNat ∧ m ≤ (E8NormTwo.e8ht γ).toNat := by
  have hβht : 1 ≤ E8NormTwo.e8ht β := one_le_e8ht_posRoot ⟨β, hβ⟩
  have hβ'ht : 1 ≤ E8NormTwo.e8ht β' := one_le_e8ht_posRoot ⟨β', hβ'⟩
  have hht : E8NormTwo.e8ht γ = (n:ℤ) * E8NormTwo.e8ht β + (m:ℤ) * E8NormTwo.e8ht β' := by
    rw [← h, e8ht_add, e8ht_nsmul, e8ht_nsmul]
  have h0 : 0 ≤ E8NormTwo.e8ht γ := by
    rw [hht]
    have h2 : (0:ℤ) ≤ (m:ℤ) * E8NormTwo.e8ht β' := mul_nonneg (by positivity) (by linarith)
    nlinarith [hβht, hβ'ht, h2]
  have hto : ((E8NormTwo.e8ht γ).toNat : ℤ) = E8NormTwo.e8ht γ := Int.toNat_of_nonneg h0
  constructor
  · apply Int.ofNat_le.mp
    rw [hto, hht]
    have h1 : (n:ℤ) * 1 ≤ (n:ℤ) * E8NormTwo.e8ht β :=
      mul_le_mul_of_nonneg_left hβht (by positivity)
    have h2 : (0:ℤ) ≤ (m:ℤ) * E8NormTwo.e8ht β' := mul_nonneg (by positivity) (by linarith)
    linarith
  · apply Int.ofNat_le.mp
    rw [hto, hht]
    have h1 : (m:ℤ) * 1 ≤ (m:ℤ) * E8NormTwo.e8ht β' :=
      mul_le_mul_of_nonneg_left hβ'ht (by positivity)
    have h2 : (0:ℤ) ≤ (n:ℤ) * E8NormTwo.e8ht β := mul_nonneg (by positivity) (by linarith)
    linarith

/-- If the Kostant partition function of `w` is nonzero then `w` has nonnegative height. -/
theorem E8_KcountP_ht_nonneg (w : Fin 8 → ℤ) (h : E8KostantId.KcountP w ≠ 0) :
    0 ≤ E8NormTwo.e8ht w := by
  have hfin : Nat.card {k : ↥E8posRoots.P → ℕ //
      ∑ α : ↥E8posRoots.P, k α • (α : Fin 8 → ℤ) = w} ≠ 0 := by
    simpa only [E8KostantId.KcountP] using h
  obtain ⟨⟨k, hk⟩⟩ := (Nat.card_ne_zero.mp hfin).1
  rw [← hk, e8ht_sum_nsmul]
  exact Finset.sum_nonneg (fun α _ => mul_nonneg (by positivity) (e8ht_posRoot_nonneg α))

/-- `k ↦ k • β` is injective for a nonzero weight `β`. -/
lemma nsmul_injective_of_ne_zero {β : Fin 8 → ℤ} (hβ : β ≠ 0) :
    Function.Injective (fun k : ℕ => k • β) := by
  intro n m h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hβ
  have hc := congr_fun h i
  simp only [Pi.smul_apply, nsmul_eq_mul] at hc
  have hz : ((n:ℤ) - m) * β i = 0 := by linear_combination hc
  rcases mul_eq_zero.mp hz with h' | h'
  · have : (n:ℤ) = m := by linarith
    omega
  · exact absurd h' hi

/-- The number of pairs `(n,m)` with `n,m ∈ [1,M]` and `n + m = k`, for `1 ≤ k ≤ M+1`. -/
lemma card_antidiag_square (M k : ℕ) (hk1 : 1 ≤ k) (hkM : k ≤ M + 1) :
    (∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M, (if n + m = k then (1:ℤ) else 0))
      = (k:ℤ) - 1 := by
  classical
  have hprod : (∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M, (if n + m = k then (1:ℤ) else 0))
      = ∑ x ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
          (if x.1 + x.2 = k then (1:ℤ) else 0) := by
    rw [Finset.sum_product]
  rw [hprod, Finset.sum_boole]
  have hcard : (((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
      (fun x => x.1 + x.2 = k)).card = (Finset.Icc 1 (k - 1)).card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
      omega
    · intro p hp q hq hpq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp hq
      have h2 : p.2 = q.2 := by omega
      exact Prod.ext hpq h2
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      refine ⟨(j, k - j), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      omega
  rw [hcard, Nat.card_Icc]
  have h : k - 1 + 1 - 1 = k - 1 := by omega
  rw [h]
  omega

lemma sum_comm3 (s t u : Finset ℕ) (F : ℕ → ℕ → ℕ → ℤ) :
    (∑ n ∈ s, ∑ m ∈ t, ∑ k ∈ u, F n m k) = ∑ k ∈ u, ∑ n ∈ s, ∑ m ∈ t, F n m k := by
  calc (∑ n ∈ s, ∑ m ∈ t, ∑ k ∈ u, F n m k)
      = ∑ n ∈ s, ∑ k ∈ u, ∑ m ∈ t, F n m k :=
        Finset.sum_congr rfl (fun n _ => Finset.sum_comm)
    _ = ∑ k ∈ u, ∑ n ∈ s, ∑ m ∈ t, F n m k := Finset.sum_comm

/-- The core combinatorial identity: for a nonzero `β` of height `≥ 1`,
`∑_{n,m} [nβ+mβ=γ] + ∑_n (1-n)[nβ=γ] = 0`. -/
theorem E8_core_pair_identity (β : Fin 8 → ℤ) (hβ : β ≠ 0) (hβ1 : 1 ≤ E8NormTwo.e8ht β)
    (γ : Fin 8 → ℤ) :
    (∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht γ).toNat),
       ∑ m ∈ Finset.Icc 1 ((E8NormTwo.e8ht γ).toNat),
       (if n • β + m • β = γ then (1:ℤ) else 0))
    + (∑ n ∈ Finset.Icc 1 ((E8NormTwo.e8ht γ).toNat),
       (if n • β = γ then (1 - (n:ℤ)) else 0)) = 0 := by
  classical
  set M : ℕ := (E8NormTwo.e8ht γ).toNat with hM
  set χ : ℕ → ℤ := fun k => if k • β = γ then 1 else 0 with hχ
  have hχzero : ∀ k, M < k → χ k = 0 := by
    intro k hk
    rw [hχ]
    simp only
    rw [if_neg]
    intro hkβ
    have heq : (k:ℤ) * E8NormTwo.e8ht β = E8NormTwo.e8ht γ := by
      have : E8NormTwo.e8ht γ = E8NormTwo.e8ht (k • β) := by rw [hkβ]
      rw [this, e8ht_nsmul]
    have hkge : (k:ℤ) ≤ E8NormTwo.e8ht γ := by
      rw [← heq]
      have hk0 : (0:ℤ) ≤ (k:ℤ) := by positivity
      nlinarith [hβ1, hk0]
    have h0 : 0 ≤ E8NormTwo.e8ht γ := le_trans (by positivity) hkge
    have hMeq : M = E8NormTwo.e8ht γ := by rw [hM]; exact Int.toNat_of_nonneg h0
    omega
  have hsecond : (∑ n ∈ Finset.Icc 1 M, (if n • β = γ then (1 - (n:ℤ)) else 0))
      = ∑ n ∈ Finset.Icc 1 M, (1 - (n:ℤ)) * χ n := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hχ]; by_cases h : n • β = γ <;> simp [h]
  have hfirst : (∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
        (if n • β + m • β = γ then (1:ℤ) else 0))
      = ∑ k ∈ Finset.Icc 1 M, ((k:ℤ) - 1) * χ k := by
    have hstep1 : (∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
          (if n • β + m • β = γ then (1:ℤ) else 0))
        = ∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M, χ (n + m) := by
      refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
      show (if n • β + m • β = γ then (1:ℤ) else 0) = (if (n + m) • β = γ then (1:ℤ) else 0)
      rw [add_nsmul]
    have hstep2 : (∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M, χ (n + m))
        = ∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
            ∑ k ∈ Finset.Icc 1 M, (if n + m = k then χ k else 0) := by
      refine Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun m hm => ?_))
      rw [Finset.sum_ite_eq]
      by_cases hmem : n + m ∈ Finset.Icc 1 M
      · rw [if_pos hmem]
      · rw [if_neg hmem]
        apply hχzero
        simp only [Finset.mem_Icc] at hmem hn hm
        omega
    rw [hstep1, hstep2, sum_comm3]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ∈ Finset.Icc 1 M := hk
    simp only [Finset.mem_Icc] at hk'
    have hinner : (∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
          (if n + m = k then χ k else 0))
        = χ k * (∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
          (if n + m = k then (1:ℤ) else 0)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      by_cases h : n + m = k <;> simp [h]
    rw [hinner, card_antidiag_square M k hk'.1 (by omega)]
    ring
  rw [hfirst, hsecond, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  ring

lemma sum_Icc_reduce {f : ℕ → ℤ} {M N : ℕ} (hMN : M ≤ N)
    (h0 : ∀ n, n ∈ Finset.Icc 1 N → M < n → f n = 0) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ n ∈ Finset.Icc 1 M, f n :=
  (Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hMN) (by
    intro x hx hxnot
    apply h0 x hx
    simp only [Finset.mem_Icc] at hx hxnot
    omega)).symm

lemma sum_mul_of_fiber {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (g : ι → κ)
    (f : ι → ℤ) (c : κ → ℤ) :
    ∑ i ∈ s, f i * c (g i) = ∑ k ∈ s.image g, (∑ i ∈ s with g i = k, f i) * c k := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image g)
      (fun i hi => Finset.mem_image_of_mem g hi) (fun i => f i * c (g i))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h1 : (∑ i ∈ s with g i = k, f i * c (g i)) = ∑ i ∈ s with g i = k, f i * c k := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_filter] at hi
    rw [hi.2]
  rw [h1, Finset.sum_mul]

/-- The `γ`-coefficient of the first (pair) sum. -/
def Acoef (N : ℕ) (γ : Fin 8 → ℤ) : ℤ :=
  ∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
    (if n • β + m • β' = γ then e8pair β β' else 0)

/-- The `γ`-coefficient of the second (height) sum. -/
def Bcoef (N : ℕ) (γ : Fin 8 → ℤ) : ℤ :=
  ∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N, (if n • β = γ then E8NormTwo.e8ht β else 0)

/-- The `γ`-coefficient of the third (index) sum. -/
def Ccoef (N : ℕ) (γ : Fin 8 → ℤ) : ℤ :=
  ∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N, (if n • β = γ then (n:ℤ) else 0)

/-- The first summand of the hypothesis `hcrux`, as a function of `γ` (range parametrised). -/
def Fcoef (M : ℕ) (γ : Fin 8 → ℤ) : ℤ :=
  ∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P,
    ∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
    (if n • β + m • β' = γ then (if β = β' then 0 else e8pair β β') else 0)

/-- The second summand of the hypothesis `hcrux`, as a function of `γ` (range parametrised). -/
def Gcoef (M : ℕ) (γ : Fin 8 → ℤ) : ℤ :=
  ∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 M,
    (if n • β = γ then E8NormTwo.e8ht β - 1 else 0)

lemma Acoef_reduce (N : ℕ) (γ : Fin 8 → ℤ) (hN : (E8NormTwo.e8ht γ).toNat ≤ N) :
    Acoef N γ = Acoef ((E8NormTwo.e8ht γ).toNat) γ := by
  unfold Acoef
  refine Finset.sum_congr rfl (fun β hβ => Finset.sum_congr rfl (fun β' hβ' => ?_))
  rw [sum_Icc_reduce hN (f := fun n => ∑ m ∈ Finset.Icc 1 N,
        (if n • β + m • β' = γ then e8pair β β' else 0)) ?_]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [sum_Icc_reduce hN (f := fun m => (if n • β + m • β' = γ then e8pair β β' else 0)) ?_]
    intro m hm hmgt
    rw [if_neg]
    intro hcon
    have := (nsmul_add_nsmul_le_ht_of_mem_P hβ hβ' (by
      simp only [Finset.mem_Icc] at hn; omega) (by
      simp only [Finset.mem_Icc] at hm; omega) hcon).2
    omega
  · intro n hn hngt
    apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    intro hcon
    have := (nsmul_add_nsmul_le_ht_of_mem_P hβ hβ' (by
      simp only [Finset.mem_Icc] at hn; omega) (by
      simp only [Finset.mem_Icc] at hm; omega) hcon).1
    omega

lemma Bcoef_reduce (N : ℕ) (γ : Fin 8 → ℤ) (hN : (E8NormTwo.e8ht γ).toNat ≤ N) :
    Bcoef N γ = Bcoef ((E8NormTwo.e8ht γ).toNat) γ := by
  unfold Bcoef
  refine Finset.sum_congr rfl (fun β hβ => ?_)
  rw [sum_Icc_reduce hN (f := fun n => (if n • β = γ then E8NormTwo.e8ht β else 0)) ?_]
  intro n hn hngt
  rw [if_neg]
  intro hcon
  have heq : E8NormTwo.e8ht γ = (n:ℤ) * E8NormTwo.e8ht β := by
    rw [← hcon, e8ht_nsmul]
  have hβ1 : 1 ≤ E8NormTwo.e8ht β := one_le_e8ht_posRoot ⟨β, hβ⟩
  have hle : (n:ℤ) ≤ E8NormTwo.e8ht γ := by
    rw [heq]; have hk : (0:ℤ) ≤ (n:ℤ) := by positivity
    nlinarith [hβ1, hk]
  have h0 : 0 ≤ E8NormTwo.e8ht γ := le_trans (by positivity) hle
  have : ((E8NormTwo.e8ht γ).toNat : ℤ) = E8NormTwo.e8ht γ := Int.toNat_of_nonneg h0
  omega

lemma Ccoef_reduce (N : ℕ) (γ : Fin 8 → ℤ) (hN : (E8NormTwo.e8ht γ).toNat ≤ N) :
    Ccoef N γ = Ccoef ((E8NormTwo.e8ht γ).toNat) γ := by
  unfold Ccoef
  refine Finset.sum_congr rfl (fun β hβ => ?_)
  rw [sum_Icc_reduce hN (f := fun n => (if n • β = γ then (n:ℤ) else 0)) ?_]
  intro n hn hngt
  rw [if_neg]
  intro hcon
  have heq : E8NormTwo.e8ht γ = (n:ℤ) * E8NormTwo.e8ht β := by
    rw [← hcon, e8ht_nsmul]
  have hβ1 : 1 ≤ E8NormTwo.e8ht β := one_le_e8ht_posRoot ⟨β, hβ⟩
  have hle : (n:ℤ) ≤ E8NormTwo.e8ht γ := by
    rw [heq]; have hk : (0:ℤ) ≤ (n:ℤ) := by positivity
    nlinarith [hβ1, hk]
  have h0 : 0 ≤ E8NormTwo.e8ht γ := le_trans (by positivity) hle
  have : ((E8NormTwo.e8ht γ).toNat : ℤ) = E8NormTwo.e8ht γ := Int.toNat_of_nonneg h0
  omega

lemma sum_split_diag {ι : Type*} [DecidableEq ι] (s : Finset ι) (G : ι → ι → ℤ) :
    (∑ β ∈ s, ∑ β' ∈ s, G β β') =
      (∑ β ∈ s, ∑ β' ∈ s, (if β = β' then 0 else G β β')) + ∑ β ∈ s, G β β := by
  have hdiag : (∑ β ∈ s, ∑ β' ∈ s, (if β = β' then G β β' else 0)) = ∑ β ∈ s, G β β := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun β' hβ' => ?_)
    rw [Finset.sum_ite_eq' s β' (fun β => G β β'), if_pos hβ']
  have h : (∑ β ∈ s, ∑ β' ∈ s, G β β')
      = (∑ β ∈ s, ∑ β' ∈ s, (if β = β' then 0 else G β β'))
        + (∑ β ∈ s, ∑ β' ∈ s, (if β = β' then G β β' else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun β' _ => ?_)
    by_cases hb : β = β' <;> simp [hb]
  rw [h, hdiag]

lemma diag_off (M : ℕ) (β β' γ : Fin 8 → ℤ) :
    (if β = β' then 0 else ∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
        (if n • β + m • β' = γ then e8pair β β' else 0))
      = ∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
        (if n • β + m • β' = γ then (if β = β' then 0 else e8pair β β') else 0) := by
  by_cases hb : β = β'
  · rw [if_pos hb]
    symm
    refine Finset.sum_eq_zero (fun n _ => Finset.sum_eq_zero (fun m _ => ?_))
    simp [hb]
  · rw [if_neg hb]
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
    by_cases hc : n • β + m • β' = γ
    · rw [if_pos hc, if_pos hc, if_neg hb]
    · rw [if_neg hc, if_neg hc]

lemma Acoef_eq (M : ℕ) (γ : Fin 8 → ℤ) :
    Acoef M γ = Fcoef M γ + ∑ β ∈ E8posRoots.P,
      ∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
        (if n • β + m • β = γ then e8pair β β else 0) := by
  unfold Acoef Fcoef
  rw [sum_split_diag]
  congr 1
  refine Finset.sum_congr rfl (fun β _ => Finset.sum_congr rfl (fun β' _ => ?_))
  exact diag_off M β β' γ

lemma crux_coeff_eq (N : ℕ) (γ : Fin 8 → ℤ) (hN : (E8NormTwo.e8ht γ).toNat ≤ N) :
    Acoef N γ + 2 * Bcoef N γ - 2 * Ccoef N γ
      = Fcoef ((E8NormTwo.e8ht γ).toNat) γ
        + 2 * Gcoef ((E8NormTwo.e8ht γ).toNat) γ := by
  set M : ℕ := (E8NormTwo.e8ht γ).toNat with hM
  rw [Acoef_reduce N γ hN, Bcoef_reduce N γ hN, Ccoef_reduce N γ hN, ← hM]
  have hA := Acoef_eq M γ
  have hdiag : (∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
        (if n • β + m • β = γ then e8pair β β else 0))
      = 2 * (∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
        (if n • β + m • β = γ then (1:ℤ) else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun β hβ => ?_)
    rw [e8pair_self_of_mem_P hβ, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases h : n • β + m • β = γ <;> simp [h]
  have h3 : Bcoef M γ - Ccoef M γ
      = ∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 M,
        (if n • β = γ then E8NormTwo.e8ht β - (n:ℤ) else 0) := by
    unfold Bcoef Ccoef
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : n • β = γ
    · rw [if_pos h, if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, if_neg h]; ring
  have hBC : 2 * Bcoef M γ - 2 * Ccoef M γ
      = 2 * (∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 M,
          (if n • β = γ then E8NormTwo.e8ht β - (n:ℤ) else 0)) := by
    rw [← mul_sub, h3]
  have hG : (∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 M,
        (if n • β = γ then E8NormTwo.e8ht β - (n:ℤ) else 0))
      = Gcoef M γ + (∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 M,
        (if n • β = γ then (1 - (n:ℤ)) else 0)) := by
    unfold Gcoef
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : n • β = γ
    · rw [if_pos h, if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h, if_neg h]; ring
  have hcore : (∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
        (if n • β + m • β = γ then (1:ℤ) else 0))
      + (∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 M,
        (if n • β = γ then (1 - (n:ℤ)) else 0)) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun β hβ => ?_)
    have hh := E8_core_pair_identity β (posRoot_ne_zero ⟨β, hβ⟩)
      (one_le_e8ht_posRoot ⟨β, hβ⟩) γ
    rw [← hM] at hh
    exact hh
  linarith [hA, hdiag, hBC, hG, hcore]

def Aindex (N : ℕ) : Finset (((Fin 8 → ℤ) × (Fin 8 → ℤ)) × (ℕ × ℕ)) :=
  (E8posRoots.P ×ˢ E8posRoots.P) ×ˢ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N)

def Agroup (p : ((Fin 8 → ℤ) × (Fin 8 → ℤ)) × (ℕ × ℕ)) : Fin 8 → ℤ :=
  p.2.1 • p.1.1 + p.2.2 • p.1.2

def TA (N : ℕ) : Finset (Fin 8 → ℤ) := (Aindex N).image Agroup

def Bindex (N : ℕ) : Finset ((Fin 8 → ℤ) × ℕ) := E8posRoots.P ×ˢ Finset.Icc 1 N

def Bgroup (p : (Fin 8 → ℤ) × ℕ) : Fin 8 → ℤ := p.2 • p.1

def TB (N : ℕ) : Finset (Fin 8 → ℤ) := (Bindex N).image Bgroup

lemma Acoef_fiber (N : ℕ) (γ : Fin 8 → ℤ) :
    Acoef N γ = ∑ p ∈ Aindex N with Agroup p = γ, e8pair p.1.1 p.1.2 := by
  rw [Finset.sum_filter]
  unfold Acoef Aindex Agroup
  simp only [Finset.sum_product]

lemma Bcoef_fiber (N : ℕ) (γ : Fin 8 → ℤ) :
    Bcoef N γ = ∑ p ∈ Bindex N with Bgroup p = γ, E8NormTwo.e8ht p.1 := by
  rw [Finset.sum_filter]
  unfold Bcoef Bindex Bgroup
  simp only [Finset.sum_product]

lemma Ccoef_fiber (N : ℕ) (γ : Fin 8 → ℤ) :
    Ccoef N γ = ∑ p ∈ Bindex N with Bgroup p = γ, (p.2 : ℤ) := by
  rw [Finset.sum_filter]
  unfold Ccoef Bindex Bgroup
  simp only [Finset.sum_product]

lemma Acoef_zero (N : ℕ) {γ : Fin 8 → ℤ} (h : γ ∉ TA N) : Acoef N γ = 0 := by
  rw [Acoef_fiber]
  exact Finset.sum_eq_zero (fun p hp => by
    rw [Finset.mem_filter] at hp
    exact absurd (Finset.mem_image_of_mem Agroup hp.1) (by rw [hp.2]; simpa only [TA] using h))

lemma Bcoef_zero (N : ℕ) {γ : Fin 8 → ℤ} (h : γ ∉ TB N) : Bcoef N γ = 0 := by
  rw [Bcoef_fiber]
  exact Finset.sum_eq_zero (fun p hp => by
    rw [Finset.mem_filter] at hp
    exact absurd (Finset.mem_image_of_mem Bgroup hp.1) (by rw [hp.2]; simpa only [TB] using h))

lemma Ccoef_zero (N : ℕ) {γ : Fin 8 → ℤ} (h : γ ∉ TB N) : Ccoef N γ = 0 := by
  rw [Ccoef_fiber]
  exact Finset.sum_eq_zero (fun p hp => by
    rw [Finset.mem_filter] at hp
    exact absurd (Finset.mem_image_of_mem Bgroup hp.1) (by rw [hp.2]; simpa only [TB] using h))

lemma A_fiber (N : ℕ) (δ : Fin 8 → ℤ) :
    (∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        e8pair β β' * (E8KostantId.KcountP (δ - n • β - m • β') : ℤ))
      = ∑ γ ∈ TA N, Acoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ) := by
  have h1 : (∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        e8pair β β' * (E8KostantId.KcountP (δ - n • β - m • β') : ℤ))
      = ∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        e8pair β β' * (E8KostantId.KcountP (δ - (n • β + m • β')) : ℤ) := by
    refine Finset.sum_congr rfl (fun β _ => Finset.sum_congr rfl (fun β' _ =>
      Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))))
    rw [sub_sub]
  rw [h1]
  have h2 : (∑ β ∈ E8posRoots.P, ∑ β' ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        e8pair β β' * (E8KostantId.KcountP (δ - (n • β + m • β')) : ℤ))
      = ∑ p ∈ Aindex N, e8pair p.1.1 p.1.2 * (E8KostantId.KcountP (δ - Agroup p) : ℤ) := by
    simp only [Finset.sum_product, Aindex, Agroup]
  rw [h2, sum_mul_of_fiber (Aindex N) Agroup (fun p => e8pair p.1.1 p.1.2)
        (fun γ => (E8KostantId.KcountP (δ - γ) : ℤ))]
  refine Finset.sum_congr ?_ (fun γ _ => ?_)
  · rw [TA]
  · rw [Acoef_fiber]

lemma B_fiber (N : ℕ) (δ : Fin 8 → ℤ) :
    (∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N,
        E8NormTwo.e8ht β * (E8KostantId.KcountP (δ - n • β) : ℤ))
      = ∑ γ ∈ TB N, Bcoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ) := by
  have h2 : (∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N,
        E8NormTwo.e8ht β * (E8KostantId.KcountP (δ - n • β) : ℤ))
      = ∑ p ∈ Bindex N, E8NormTwo.e8ht p.1 * (E8KostantId.KcountP (δ - Bgroup p) : ℤ) := by
    simp only [Finset.sum_product, Bindex, Bgroup]
  rw [h2, sum_mul_of_fiber (Bindex N) Bgroup (fun p => E8NormTwo.e8ht p.1)
        (fun γ => (E8KostantId.KcountP (δ - γ) : ℤ))]
  refine Finset.sum_congr ?_ (fun γ _ => ?_)
  · rw [TB]
  · rw [Bcoef_fiber]

lemma C_fiber (N : ℕ) (δ : Fin 8 → ℤ) :
    (∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N,
        (n : ℤ) * (E8KostantId.KcountP (δ - n • β) : ℤ))
      = ∑ γ ∈ TB N, Ccoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ) := by
  have h2 : (∑ β ∈ E8posRoots.P, ∑ n ∈ Finset.Icc 1 N,
        (n : ℤ) * (E8KostantId.KcountP (δ - n • β) : ℤ))
      = ∑ p ∈ Bindex N, (p.2 : ℤ) * (E8KostantId.KcountP (δ - Bgroup p) : ℤ) := by
    simp only [Finset.sum_product, Bindex, Bgroup]
  rw [h2, sum_mul_of_fiber (Bindex N) Bgroup (fun p => (p.2 : ℤ))
        (fun γ => (E8KostantId.KcountP (δ - γ) : ℤ))]
  refine Finset.sum_congr ?_ (fun γ _ => ?_)
  · rw [TB]
  · rw [Ccoef_fiber]

theorem E8_Kostant_crux_convolved
    (hcrux : ∀ γ : Fin 8 → ℤ,
      (∑ β ∈ Commons.LinearAlgebra.Matrix.Cartan.E8posRoots.P,
        ∑ β' ∈ Commons.LinearAlgebra.Matrix.Cartan.E8posRoots.P,
        ∑ n ∈ Finset.Icc 1 ((Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8ht γ).toNat),
        ∑ m ∈ Finset.Icc 1 ((Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8ht γ).toNat),
        (if n • β + m • β' = γ then
          (if β = β' then 0 else ∑ i, β i *
            (Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv.mulVec β') i) else 0))
      + 2 * (∑ β ∈ Commons.LinearAlgebra.Matrix.Cartan.E8posRoots.P,
        ∑ n ∈ Finset.Icc 1 ((Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8ht γ).toNat),
        (if n • β = γ then
          (Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8ht β - 1) else 0)) = 0)
    (δ : Fin 8 → ℤ) :
    (∑ β ∈ Commons.LinearAlgebra.Matrix.Cartan.E8posRoots.P,
      ∑ β' ∈ Commons.LinearAlgebra.Matrix.Cartan.E8posRoots.P,
      ∑ n ∈ Finset.Icc 1 ((Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8ht δ).toNat),
      ∑ m ∈ Finset.Icc 1 ((Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8ht δ).toNat),
      (∑ i, β i * (Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv.mulVec β') i) *
        (Commons.Algebra.Lie.E8KostantId.KcountP
          (δ - n • β - m • β') : ℤ))
      + 2 * (∑ β ∈ Commons.LinearAlgebra.Matrix.Cartan.E8posRoots.P,
          ∑ n ∈ Finset.Icc 1 ((Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8ht δ).toNat),
          (Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8ht β) *
            (Commons.Algebra.Lie.E8KostantId.KcountP (δ - n • β) : ℤ))
      = 2 * (∑ β ∈ Commons.LinearAlgebra.Matrix.Cartan.E8posRoots.P,
          ∑ n ∈ Finset.Icc 1 ((Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8ht δ).toNat),
          (n : ℤ) * (Commons.Algebra.Lie.E8KostantId.KcountP (δ - n • β) : ℤ)) := by
  set N : ℕ := (Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8ht δ).toNat with hNdef
  have hA := A_fiber N δ
  have hB := B_fiber N δ
  have hC := C_fiber N δ
  simp only [e8pair] at hA
  have hAe : (∑ γ ∈ TA N, Acoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ))
      = ∑ γ ∈ TA N ∪ TB N, Acoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ) :=
    Finset.sum_subset Finset.subset_union_left (fun γ _ hγ => by
      rw [Acoef_zero N hγ]; ring)
  have hBe : (∑ γ ∈ TB N, Bcoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ))
      = ∑ γ ∈ TA N ∪ TB N, Bcoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ) :=
    Finset.sum_subset Finset.subset_union_right (fun γ _ hγ => by
      rw [Bcoef_zero N hγ]; ring)
  have hCe : (∑ γ ∈ TB N, Ccoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ))
      = ∑ γ ∈ TA N ∪ TB N, Ccoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ) :=
    Finset.sum_subset Finset.subset_union_right (fun γ _ hγ => by
      rw [Ccoef_zero N hγ]; ring)
  rw [hA, hB, hC, hAe, hBe, hCe]
  have hmain : (∑ γ ∈ TA N ∪ TB N, Acoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ))
      + 2 * (∑ γ ∈ TA N ∪ TB N, Bcoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ))
      - 2 * (∑ γ ∈ TA N ∪ TB N, Ccoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ)) = 0 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro γ _
    have hfac : Acoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ)
          + 2 * (Bcoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ))
          - 2 * (Ccoef N γ * (E8KostantId.KcountP (δ - γ) : ℤ))
        = (Acoef N γ + 2 * Bcoef N γ - 2 * Ccoef N γ)
          * (E8KostantId.KcountP (δ - γ) : ℤ) := by ring
    rw [hfac]
    by_cases hK : E8KostantId.KcountP (δ - γ) = 0
    · rw [hK]; simp
    · have hht : 0 ≤ E8NormTwo.e8ht (δ - γ) := E8_KcountP_ht_nonneg (δ - γ) hK
      have hle : (E8NormTwo.e8ht γ).toNat ≤ N := by
        rw [hNdef]
        apply Int.toNat_le_toNat
        have hsub : E8NormTwo.e8ht (δ - γ) = E8NormTwo.e8ht δ - E8NormTwo.e8ht γ := by
          have hh := map_sub htLin δ γ
          simpa only [htLin_apply] using hh
        linarith
      have hcruxγ : Fcoef ((E8NormTwo.e8ht γ).toNat) γ
          + 2 * Gcoef ((E8NormTwo.e8ht γ).toNat) γ = 0 := by
        simpa only [Fcoef, Gcoef, e8pair] using hcrux γ
      have hcoef : Acoef N γ + 2 * Bcoef N γ - 2 * Ccoef N γ = 0 := by
        rw [crux_coeff_eq N γ hle, hcruxγ]
      rw [hcoef]; ring
  linarith [hmain]

end

end Commons.Algebra.Lie
