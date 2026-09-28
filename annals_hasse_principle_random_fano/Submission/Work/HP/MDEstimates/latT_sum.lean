import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.Sig2.num_lattices_of
import Submission.Work.HP.Sig2.minkowski_prod
import Submission.Work.HP.Sig2.Tset_finite
import Submission.Work.HP.kwin_spec
import Submission.Work.HP.ceil_logb_bounds
import Submission.Work.HP.minkowski_upper
import Submission.Work.HP.ballCount_le_pow_rk
import Submission.Work.HP.MDEstimates.dyadic_pair_sum
import Submission.Work.HP.MDEstimates.clog_log_bound
import Submission.Work.HP.MDEstimates.latT_window_facts
import Submission.Work.HP.MDEstimates.latT_window_weight
import Submission.Work.HP.MDEstimates.latT_window_count

namespace Work.HP.MDEstimates

open Work.HP Finset

noncomputable section

/-! ## Auxiliary definitions of the assembly -/

/-- The dyadic window pair `(⌈log₂ λ₁⌉, ⌈log₂ λ₂⌉)` of a lattice. -/
private def winPair (L : Submodule ℤ (Fin 5 → ℤ)) : ℕ × ℕ :=
  (⌈Real.logb 2 (lam L 1)⌉₊, ⌈Real.logb 2 (lam L 2)⌉₊)

/-- The `λ₃`-bound attached to the window `p`. -/
private def s3f (Kmk Δ : ℝ) (p : ℕ × ℕ) : ℝ :=
  max 1 (4 * Kmk * (Δ + 1) / (2:ℝ) ^ (p.1 + p.2))

/-- Number bound of the window `p`. -/
private def Nf (Kq Kmk Δ : ℝ) (p : ℕ × ℕ) : ℝ :=
  Kq * (2:ℝ) ^ (7 * p.1 + 5 * p.2) * (s3f Kmk Δ p) ^ 3

/-- Weight bound of the window `p`. -/
private def Wtf (Z : ℝ) (p : ℕ × ℕ) : ℝ :=
  256 * Z ^ 4 / (2:ℝ) ^ (2 * p.1 + 2 * p.2)

/-! ## Auxiliary lemmas of the assembly -/

private theorem minkowski_prod_ge_one :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ L : Submodule ℤ (Fin 5 → ℤ),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ K * detL L := by
  obtain ⟨K, _hKpos, hK⟩ := Work.HP.Sig2.minkowski_prod (ι := Fin 5)
  refine ⟨max K 1, le_max_right _ _, fun L => ?_⟩
  calc (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ K * detL L := hK L
    _ ≤ max K 1 * detL L := mul_le_mul_of_nonneg_right (le_max_left _ _) (detL_nonneg L)

private lemma winPair_fst (L : Submodule ℤ (Fin 5 → ℤ)) :
    (winPair L).1 = ⌈Real.logb 2 (lam L 1)⌉₊ := rfl

private lemma winPair_snd (L : Submodule ℤ (Fin 5 → ℤ)) :
    (winPair L).2 = ⌈Real.logb 2 (lam L 2)⌉₊ := rfl

/-- The dyadic ratio of powers of two arising from the three-exponent bookkeeping. -/
private lemma ratio_lem (i j : ℕ) :
    (2:ℝ)^(7*i+5*j) / ((2:ℝ)^(3*(i+j)) * (2:ℝ)^(2*i+2*j)) = (2:ℝ)^(2*i) := by
  rw [← pow_add, div_eq_iff (by positivity), ← pow_add]
  congr 1
  omega

/-- Cube of a dyadic power. -/
private lemma two_pow_cube (k : ℕ) :
    ((2:ℝ)^k)^3 = (2:ℝ)^(3*k) := by
  rw [← pow_mul, Nat.mul_comm k 3]

/-- Rearrangement of the per-window term. -/
private lemma term_alg (Kq Z P : ℝ) (i j : ℕ) :
    Kq * 256 * Z^4 * ((2:ℝ)^(7*i+5*j) * (512 * P / (2:ℝ)^(3*(i+j))) / (2:ℝ)^(2*i+2*j))
      = Kq * 256 * 512 * P * Z^4 * (2:ℝ)^(2*i) := by
  have h1 : (2:ℝ)^(7*i+5*j) * (512 * P / (2:ℝ)^(3*(i+j))) / (2:ℝ)^(2*i+2*j)
      = 512 * P * ((2:ℝ)^(7*i+5*j) / ((2:ℝ)^(3*(i+j)) * (2:ℝ)^(2*i+2*j))) := by
    field_simp
    try ring
  rw [h1, ratio_lem i j]
  ring

/-- **The `T`-window sum.** Purely a lattice-counting statement: the number of primitive rank-`3`
sublattices of `ℤ^5` with covolume `≤ Δ + 1` and first two successive minima `≤ Z`, weighted by
`(1 + Z/λ₁)²(1 + Z/λ₂)²`, is `≪ Z⁴ Δ^{11/3} (log Δ)²`. -/
theorem latT_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z Δ : ℝ), 1 ≤ Z → 1 ≤ Δ →
      ∀ (T : Finset (Submodule ℤ (Fin 5 → ℤ))),
        (∀ L ∈ T, IsPrimLat L ∧ rk L = 3 ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ Z ∧ lam L 2 ≤ Z) →
        (∑ L ∈ T, (1 + Z / lam L 1) ^ 2 * (1 + Z / lam L 2) ^ 2)
          ≤ C * Z ^ 4 * Δ ^ ((11 : ℝ) / 3) * Real.log (2 * Δ) ^ 2 := by
  classical
  obtain ⟨Kmk, hKmk1, hmink⟩ := minkowski_prod_ge_one
  obtain ⟨Cd, hCdpos, hCd⟩ := dyadic_pair_sum
  obtain ⟨Clog, hClogpos, hClog⟩ := clog_log_bound Kmk hKmk1
  obtain ⟨Kq, hKqpos, hKq⟩ := latT_window_count Kmk hKmk1 hmink
  refine ⟨256 * 512 * Kq * (4 * Kmk) ^ 3 * Cd * (32 * Kmk) * Clog * (2:ℝ) ^ ((11:ℝ)/3) * 2,
    by positivity, ?_⟩
  intro Z Δ hZ hΔ T hT
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hΔpos : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
  have hlogpos : 0 < Real.log (2 * Δ) := Real.log_pos (by linarith)
  -- ## Step 0: the level `M` attached to `U = 8 Kmk (Δ+1)`
  set U : ℝ := 8 * Kmk * (Δ + 1) with hUdef
  have hU1 : 1 ≤ U := by rw [hUdef]; nlinarith
  set M : ℕ := Nat.clog 2 ⌈U⌉₊ with hMdef
  have hUle : U ≤ (2:ℝ)^M := by
    rw [hMdef]
    calc U ≤ (⌈U⌉₊ : ℝ) := Nat.le_ceil U
      _ ≤ ((2 ^ Nat.clog 2 ⌈U⌉₊ : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) ⌈U⌉₊
      _ = (2:ℝ)^(Nat.clog 2 ⌈U⌉₊) := by push_cast; ring
  have h2M : (2:ℝ)^M ≤ 4 * U := by
    have hcl : Nat.clog 2 ⌈U⌉₊ ≤ ⌈Real.logb 2 U⌉₊ + 1 := by
      rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
      have h1 : U ≤ (2:ℝ)^(⌈Real.logb 2 U⌉₊) := (ceil_logb_bounds hU1).1
      have h2 : (⌈U⌉₊ : ℝ) < U + 1 := Nat.ceil_lt_add_one (le_trans zero_le_one hU1)
      have h3 : (1:ℝ) ≤ (2:ℝ)^(⌈Real.logb 2 U⌉₊) := one_le_pow₀ (by norm_num)
      have h4 : (⌈U⌉₊ : ℝ) ≤ (2:ℝ)^(⌈Real.logb 2 U⌉₊ + 1) := by
        rw [pow_succ]; linarith
      have h5 : ⌈U⌉₊ ≤ 2 ^ (⌈Real.logb 2 U⌉₊ + 1) := by
        have h6 : ((⌈U⌉₊ : ℕ) : ℝ) ≤ ((2 ^ (⌈Real.logb 2 U⌉₊ + 1) : ℕ) : ℝ) := by
          push_cast
          exact h4
        exact_mod_cast h6
      exact h5
    rw [hMdef]
    calc (2:ℝ)^(Nat.clog 2 ⌈U⌉₊) ≤ (2:ℝ)^(⌈Real.logb 2 U⌉₊ + 1) :=
          pow_le_pow_right₀ (by norm_num) hcl
      _ = 2 * (2:ℝ)^(⌈Real.logb 2 U⌉₊) := by rw [pow_succ]; ring
      _ ≤ 2 * (2 * U) := by linarith [(ceil_logb_bounds hU1).2]
      _ = 4 * U := by ring
  have hMlog : ((M : ℝ) + 1) ≤ Clog * Real.log (2 * Δ) := by
    simpa only [hMdef, hUdef] using hClog Δ hΔ
  -- ## Step 1: the window set
  set Kset : Finset (ℕ × ℕ) := (((Finset.range (M + 1)).product (Finset.range (M + 1))).filter
        (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ p.1 + 2 * p.2 ≤ M)) with hKset
  have hmemKset : ∀ L ∈ T, winPair L ∈ Kset := by
    intro L hL
    obtain ⟨hprim, hrk, hdet, hl1, hl2⟩ := hT L hL
    obtain ⟨hij, hpow, h3⟩ := latT_window_facts Kmk hKmk1 hmink L hrk Δ hΔ hdet
    have hpow' : (2:ℝ) ^ ((winPair L).1 + 2 * (winPair L).2) ≤ U := by
      rw [hUdef, winPair_fst L, winPair_snd L]
      exact hpow
    have hij' : (winPair L).1 ≤ (winPair L).2 := by
      rw [winPair_fst L, winPair_snd L]; exact hij
    have hkey : (winPair L).1 + 2 * (winPair L).2 ≤ M := by
      have h2 : (2:ℕ) ^ ((winPair L).1 + 2 * (winPair L).2) ≤ (2:ℕ) ^ M := by
        have h7 : ((2:ℕ) ^ ((winPair L).1 + 2 * (winPair L).2) : ℝ) ≤ ((2:ℕ) ^ M : ℝ) := by
          push_cast
          exact le_trans hpow' hUle
        exact_mod_cast h7
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
    rw [hKset]
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨by rw [Finset.mem_range]; omega, by rw [Finset.mem_range]; omega⟩, hij', hkey⟩
  -- ## Step 2: per-window counting bound
  have hfiber : ∀ p ∈ Kset, ((T.filter (fun L => winPair L = p)).card : ℝ) ≤ Nf Kq Kmk Δ p := by
    intro p hp
    set Sp : Set (Submodule ℤ (Fin 5 → ℤ)) :=
      {L | IsPrimLat L ∧ rk L = 3 ∧ lam L 1 ≤ (2:ℝ)^p.1 ∧ lam L 2 ≤ (2:ℝ)^p.2 ∧
        lam L 3 ≤ max 1 (4 * Kmk * (Δ + 1) / (2:ℝ)^(p.1 + p.2))} with hSp
    have hfin : Sp.Finite := by
      rw [hSp]
      refine (Sig2.Tset_finite (ι := Fin 5) 3 ![((2:ℝ)^p.1), ((2:ℝ)^p.2),
        max 1 (4 * Kmk * (Δ + 1) / (2:ℝ)^(p.1 + p.2))]).subset ?_
      intro L hL
      obtain ⟨h1, h2, h3, h4, h5⟩ := hL
      refine ⟨h1, h2, ?_⟩
      intro j
      fin_cases j
      · simpa using h3
      · simpa using h4
      · simpa using h5
    have hsub : ((T.filter (fun L => winPair L = p) : Finset _) : Set _) ⊆ Sp := by
      intro L hL
      rw [Finset.mem_coe] at hL
      obtain ⟨hLT, hwL⟩ := Finset.mem_filter.mp hL
      obtain ⟨hprim, hrk, hdet, hl1, hl2⟩ := hT L hLT
      obtain ⟨hij, hpow, h3⟩ := latT_window_facts Kmk hKmk1 hmink L hrk Δ hΔ hdet
      have hp1 : (winPair L).1 = p.1 := congrArg Prod.fst hwL
      have hp2 : (winPair L).2 = p.2 := congrArg Prod.snd hwL
      rw [hSp]
      refine ⟨hprim, hrk, ?_, ?_, ?_⟩
      · have h := (ceil_logb_bounds (one_le_lam L (i := 1) (by norm_num) (by omega))).1
        calc lam L 1 ≤ (2:ℝ)^((winPair L).1) := by rw [winPair_fst L]; exact h
          _ ≤ (2:ℝ)^p.1 := by rw [hp1]
      · have h := (ceil_logb_bounds (one_le_lam L (i := 2) (by norm_num) (by omega))).1
        calc lam L 2 ≤ (2:ℝ)^((winPair L).2) := by rw [winPair_snd L]; exact h
          _ ≤ (2:ℝ)^p.2 := by rw [hp2]
      · have heq : (2:ℝ)^(p.1 + p.2)
            = (2:ℝ)^⌈Real.logb 2 (lam L 1)⌉₊ * (2:ℝ)^⌈Real.logb 2 (lam L 2)⌉₊ := by
          rw [pow_add, ← hp1, ← hp2, ← winPair_fst L, ← winPair_snd L]
        rw [heq]
        exact le_trans h3 (le_max_right _ _)
    have hcard : ((T.filter (fun L => winPair L = p)).card : ℝ) ≤ (Sp.ncard : ℝ) := by
      have h1 : (T.filter (fun L => winPair L = p)).card ≤ Sp.ncard := by
        rw [← Set.ncard_coe_finset (T.filter (fun L => winPair L = p))]
        exact Set.ncard_le_ncard hsub hfin
      exact_mod_cast h1
    have h2 : (Sp.ncard : ℝ) ≤ Nf Kq Kmk Δ p := by
      have h := hKq p.1 p.2 Δ hΔ
      have he : (2:ℝ)^p.1 * (2:ℝ)^p.2 = (2:ℝ)^(p.1 + p.2) :=
        (pow_add (2:ℝ) p.1 p.2).symm
      rw [he] at h
      rw [hSp]
      refine le_trans h ?_
      have key : Kq * (2:ℝ)^(7*p.1) * (2:ℝ)^(5*p.2) *
            (max 1 (4 * Kmk * (Δ + 1) / (2:ℝ)^(p.1+p.2)))^3 = Nf Kq Kmk Δ p := by
        simp only [Nf, s3f]
        rw [mul_assoc Kq ((2:ℝ)^(7*p.1)) ((2:ℝ)^(5*p.2)), ← pow_add]
        try ring
      rw [key]
    exact le_trans hcard h2
  -- ## Step 3: the lower bound `s3f ≥ 1/8` on the window set
  have hs3ge : ∀ p ∈ Kset, (1:ℝ)/8 ≤ 4 * Kmk * (Δ + 1) / (2:ℝ)^(p.1 + p.2) := by
    intro p hp
    rw [hKset, Finset.mem_filter] at hp
    obtain ⟨-, _hle, hsum⟩ := hp
    have h3 : (2:ℝ)^(p.1 + 2 * p.2) ≤ (2:ℝ)^M := pow_le_pow_right₀ (by norm_num) hsum
    have h5 : p.1 + p.2 ≤ p.1 + 2 * p.2 := by omega
    have h4 : (2:ℝ)^(p.1 + p.2) ≤ 4 * U :=
      le_trans (pow_le_pow_right₀ (by norm_num) h5) (le_trans h3 h2M)
    rw [le_div_iff₀ (by positivity)]
    have h7 : (1:ℝ)/8 * (2:ℝ)^(p.1 + p.2) ≤ (1:ℝ)/8 * (4 * U) :=
      mul_le_mul_of_nonneg_left h4 (by norm_num)
    rw [hUdef] at h7
    nlinarith [h7, hKmk1, hΔ]
  -- ## Step 4: the per-window term bound
  have hterm : ∀ p ∈ Kset, Nf Kq Kmk Δ p * Wtf Z p
      ≤ (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) * (2:ℝ)^(2*p.1) := by
    intro p hp
    have hs := hs3ge p hp
    have hs3 : (s3f Kmk Δ p)^3 ≤
        512 * (4*Kmk*(Δ+1))^3 / (2:ℝ)^(3*(p.1+p.2)) := by
      have hmax : s3f Kmk Δ p ≤ 8 * (4 * Kmk * (Δ + 1) / (2:ℝ)^(p.1+p.2)) := by
        rw [s3f, max_le_iff]
        exact ⟨by linarith, by linarith⟩
      have hnn : 0 ≤ s3f Kmk Δ p := by
        rw [s3f]; exact le_trans zero_le_one (le_max_left _ _)
      have hcube : (8 * (4 * Kmk * (Δ + 1) / (2:ℝ)^(p.1+p.2)))^3
          = 512 * (4*Kmk*(Δ+1))^3 / (2:ℝ)^(3*(p.1+p.2)) := by
        rw [mul_pow, div_pow, two_pow_cube]
        norm_num
        ring_nf
      refine le_trans (pow_le_pow_left₀ hnn hmax 3) ?_
      rw [hcube]
    have hA : Nf Kq Kmk Δ p * Wtf Z p
        = Kq * 256 * Z^4 * ((2:ℝ)^(7*p.1+5*p.2) * (s3f Kmk Δ p)^3 /
            (2:ℝ)^(2*p.1+2*p.2)) := by
      simp only [Nf, Wtf]
      field_simp
      try ring
    have hB : Kq * 256 * Z^4 * ((2:ℝ)^(7*p.1+5*p.2) * (s3f Kmk Δ p)^3 /
            (2:ℝ)^(2*p.1+2*p.2))
        ≤ Kq * 256 * Z^4 * ((2:ℝ)^(7*p.1+5*p.2) *
            (512 * (4*Kmk*(Δ+1))^3 / (2:ℝ)^(3*(p.1+p.2))) /
            (2:ℝ)^(2*p.1+2*p.2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs3 (by positivity))
        (by positivity)
    have hC : Kq * 256 * Z^4 * ((2:ℝ)^(7*p.1+5*p.2) *
            (512 * (4*Kmk*(Δ+1))^3 / (2:ℝ)^(3*(p.1+p.2))) /
            (2:ℝ)^(2*p.1+2*p.2))
        = (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) * (2:ℝ)^(2*p.1) := by
      have hP : (4*Kmk*(Δ+1))^3 = (4*Kmk)^3 * (Δ+1)^3 := by rw [mul_pow, mul_pow]
      rw [hP]
      calc Kq * 256 * Z^4 * ((2:ℝ)^(7*p.1+5*p.2) *
              (512 * ((4*Kmk)^3 * (Δ+1)^3) / (2:ℝ)^(3*(p.1+p.2))) /
              (2:ℝ)^(2*p.1+2*p.2))
          = Kq * 256 * 512 * ((4*Kmk)^3 * (Δ+1)^3) * Z^4 * (2:ℝ)^(2*p.1) :=
            term_alg Kq Z ((4*Kmk)^3 * (Δ+1)^3) p.1 p.2
        _ = (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) * (2:ℝ)^(2*p.1) := by
            ring
    calc Nf Kq Kmk Δ p * Wtf Z p
        = Kq * 256 * Z^4 * ((2:ℝ)^(7*p.1+5*p.2) * (s3f Kmk Δ p)^3 /
            (2:ℝ)^(2*p.1+2*p.2)) := hA
      _ ≤ Kq * 256 * Z^4 * ((2:ℝ)^(7*p.1+5*p.2) *
            (512 * (4*Kmk*(Δ+1))^3 / (2:ℝ)^(3*(p.1+p.2))) /
            (2:ℝ)^(2*p.1+2*p.2)) := hB
      _ = (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) * (2:ℝ)^(2*p.1) := hC
  -- ## Step 5: the fibre decomposition and the summed bound
  have hsum : (∑ L ∈ T, (1 + Z / lam L 1) ^ 2 * (1 + Z / lam L 2) ^ 2)
      ≤ (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) *
          (∑ p ∈ Kset, (2:ℝ)^(2*p.1)) := by
    have h1 : (∑ L ∈ T, (1 + Z / lam L 1) ^ 2 * (1 + Z / lam L 2) ^ 2)
        = ∑ p ∈ Kset, ∑ L ∈ T.filter (fun L => winPair L = p),
            (1 + Z / lam L 1) ^ 2 * (1 + Z / lam L 2) ^ 2 := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := Kset) (g := winPair) hmemKset
        (fun L => (1 + Z / lam L 1) ^ 2 * (1 + Z / lam L 2) ^ 2)]
    rw [h1]
    calc ∑ p ∈ Kset, ∑ L ∈ T.filter (fun L => winPair L = p),
              (1 + Z / lam L 1) ^ 2 * (1 + Z / lam L 2) ^ 2
        ≤ ∑ p ∈ Kset, Nf Kq Kmk Δ p * Wtf Z p := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          calc ∑ L ∈ T.filter (fun L => winPair L = p),
                    (1 + Z / lam L 1) ^ 2 * (1 + Z / lam L 2) ^ 2
              ≤ ∑ L ∈ T.filter (fun L => winPair L = p), Wtf Z p := by
                refine Finset.sum_le_sum (fun L hL => ?_)
                have hLT : L ∈ T := Finset.mem_of_mem_filter L hL
                obtain ⟨-, hrk, -, hl1, hl2⟩ := hT L hLT
                have hw : winPair L = p := (Finset.mem_filter.mp hL).2
                have h := latT_window_weight Z hZ L hrk hl1 hl2
                rw [← hw]
                simpa only [Wtf, winPair, ← pow_add] using h
            _ = ((T.filter (fun L => winPair L = p)).card : ℝ) * Wtf Z p := by
                rw [Finset.sum_const (Wtf Z p), nsmul_eq_mul]
            _ ≤ Nf Kq Kmk Δ p * Wtf Z p := by
                refine mul_le_mul_of_nonneg_right (hfiber p hp) ?_
                simp only [Wtf]; positivity
      _ ≤ ∑ p ∈ Kset, (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) *
              (2:ℝ)^(2*p.1) := Finset.sum_le_sum hterm
      _ = (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) *
              (∑ p ∈ Kset, (2:ℝ)^(2*p.1)) := by rw [Finset.mul_sum]
  -- ## Step 6: the dyadic pair sum
  have hdyad : (∑ p ∈ Kset, (2:ℝ)^(2*p.1)) ≤ Cd * ((M:ℝ)+1) * (4*U)^((2:ℝ)/3) := by
    rw [hKset]
    refine le_trans (hCd M) ?_
    have h1 : (2:ℝ)^M ≤ 4 * U := h2M
    have h2 : ((2:ℝ)^M)^((2:ℝ)/3) ≤ (4*U)^((2:ℝ)/3) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : 0 ≤ Cd * ((M:ℝ)+1) := by positivity
    exact mul_le_mul_of_nonneg_left h2 h3
  have hU23 : (4*U)^((2:ℝ)/3) ≤ 32 * Kmk * (Δ+1)^((2:ℝ)/3) := by
    have h1 : 4 * U = (32*Kmk) * (Δ+1) := by rw [hUdef]; ring
    rw [h1, Real.mul_rpow (x := 32*Kmk) (y := Δ+1) (z := (2:ℝ)/3)
      (by positivity) (by positivity)]
    calc (32*Kmk)^((2:ℝ)/3) * (Δ+1)^((2:ℝ)/3)
        ≤ (32*Kmk) * (Δ+1)^((2:ℝ)/3) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by linarith) (by norm_num))
            (Real.rpow_nonneg (by linarith) _)
      _ = 32 * Kmk * (Δ+1)^((2:ℝ)/3) := by ring
  -- ## Step 7: the final arithmetic
  have hstep : (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) *
        (∑ p ∈ Kset, (2:ℝ)^(2*p.1))
      ≤ (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) *
        (Cd * ((M:ℝ)+1) * (4*U)^((2:ℝ)/3)) :=
    mul_le_mul_of_nonneg_left hdyad (by positivity)
  have hfin : (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) *
        (Cd * ((M:ℝ)+1) * (4*U)^((2:ℝ)/3))
      ≤ (256 * 512 * Kq * (4 * Kmk) ^ 3 * Cd * (32 * Kmk) * Clog *
          (2:ℝ) ^ ((11:ℝ)/3) * 2) * Z ^ 4 * Δ ^ ((11:ℝ)/3) * (Real.log (2*Δ))^2 := by
    have hb2 : (4*U)^((2:ℝ)/3) ≤ 32 * Kmk * (Δ+1)^((2:ℝ)/3) := hU23
    have hb4 : 0 ≤ Cd * (Clog * Real.log (2 * Δ)) :=
      mul_nonneg (le_of_lt hCdpos) (mul_nonneg (le_of_lt hClogpos) (le_of_lt hlogpos))
    have hb5 : 0 ≤ (4*U)^((2:ℝ)/3) := Real.rpow_nonneg (by positivity) _
    have hmul : Cd * ((M : ℝ) + 1) * (4*U)^((2:ℝ)/3)
        ≤ Cd * (Clog * Real.log (2 * Δ)) * (32 * Kmk * (Δ+1)^((2:ℝ)/3)) := by
      refine mul_le_mul ?_ hb2 hb5 hb4
      exact mul_le_mul_of_nonneg_left hMlog (le_of_lt hCdpos)
    have hA : (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) *
          (Cd * ((M:ℝ)+1) * (4*U)^((2:ℝ)/3))
        ≤ (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) *
          (Cd * (Clog * Real.log (2 * Δ)) * (32 * Kmk * (Δ+1)^((2:ℝ)/3))) :=
      mul_le_mul_of_nonneg_left hmul (by positivity)
    have hpow11 : (Δ+1)^3 * (Δ+1)^((2:ℝ)/3) = (Δ+1)^((11:ℝ)/3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith : (0:ℝ) < Δ + 1)]
      congr 1
      norm_num
    have hdel : (Δ+1)^((11:ℝ)/3) ≤ (2:ℝ)^((11:ℝ)/3) * Δ^((11:ℝ)/3) := by
      have h1 : Δ + 1 ≤ 2 * Δ := by linarith
      calc (Δ+1)^((11:ℝ)/3) ≤ (2*Δ)^((11:ℝ)/3) :=
            Real.rpow_le_rpow (by linarith) h1 (by norm_num)
        _ = (2:ℝ)^((11:ℝ)/3) * Δ^((11:ℝ)/3) :=
            Real.mul_rpow (by norm_num) (le_of_lt hΔpos)
    have hlogsq : Real.log (2 * Δ) ≤ 2 * (Real.log (2 * Δ))^2 := by
      have h1 : (1:ℝ)/2 ≤ Real.log (2 * Δ) := by
        have h2 : Real.log 2 ≤ Real.log (2 * Δ) := Real.log_le_log (by norm_num) (by linarith)
        linarith [Real.log_two_gt_d9]
      nlinarith [h1]
    calc (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) *
          (Cd * ((M:ℝ)+1) * (4*U)^((2:ℝ)/3))
        ≤ (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) *
          (Cd * (Clog * Real.log (2 * Δ)) * (32 * Kmk * (Δ+1)^((2:ℝ)/3))) := hA
      _ = (Kq * 256 * 512 * (4 * Kmk) ^ 3 * Cd * Clog * (32 * Kmk)) * Z ^ 4 *
            ((Δ+1)^3 * (Δ+1)^((2:ℝ)/3)) * Real.log (2*Δ) := by ring
      _ = (Kq * 256 * 512 * (4 * Kmk) ^ 3 * Cd * Clog * (32 * Kmk)) * Z ^ 4 *
            (Δ+1)^((11:ℝ)/3) * Real.log (2*Δ) := by rw [hpow11]
      _ ≤ (Kq * 256 * 512 * (4 * Kmk) ^ 3 * Cd * Clog * (32 * Kmk)) * Z ^ 4 *
            ((2:ℝ)^((11:ℝ)/3) * Δ^((11:ℝ)/3)) * Real.log (2*Δ) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdel (by positivity)) ?_
          exact le_of_lt hlogpos
      _ ≤ (256 * 512 * Kq * (4 * Kmk) ^ 3 * Cd * (32 * Kmk) * Clog *
            (2:ℝ) ^ ((11:ℝ)/3) * 2) * Z ^ 4 * Δ ^ ((11:ℝ)/3) * (Real.log (2*Δ))^2 := by
          have hY : 0 ≤ (Kq * 256 * 512 * (4 * Kmk) ^ 3 * Cd * Clog * (32 * Kmk)) * Z ^ 4 *
              ((2:ℝ)^((11:ℝ)/3) * Δ^((11:ℝ)/3)) := by positivity
          calc (Kq * 256 * 512 * (4 * Kmk) ^ 3 * Cd * Clog * (32 * Kmk)) * Z ^ 4 *
                ((2:ℝ)^((11:ℝ)/3) * Δ^((11:ℝ)/3)) * Real.log (2*Δ)
              ≤ (Kq * 256 * 512 * (4 * Kmk) ^ 3 * Cd * Clog * (32 * Kmk)) * Z ^ 4 *
                ((2:ℝ)^((11:ℝ)/3) * Δ^((11:ℝ)/3)) * (2 * (Real.log (2*Δ))^2) :=
                mul_le_mul_of_nonneg_left hlogsq hY
            _ = (256 * 512 * Kq * (4 * Kmk) ^ 3 * Cd * (32 * Kmk) * Clog *
                (2:ℝ) ^ ((11:ℝ)/3) * 2) * Z ^ 4 * Δ ^ ((11:ℝ)/3) * (Real.log (2*Δ))^2 := by
                ring
  calc (∑ L ∈ T, (1 + Z / lam L 1) ^ 2 * (1 + Z / lam L 2) ^ 2)
      ≤ (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) *
          (∑ p ∈ Kset, (2:ℝ)^(2*p.1)) := hsum
    _ ≤ (Kq * 256 * 512 * (4 * Kmk) ^ 3 * (Δ + 1) ^ 3 * Z ^ 4) *
          (Cd * ((M:ℝ)+1) * (4*U)^((2:ℝ)/3)) := hstep
    _ ≤ (256 * 512 * Kq * (4 * Kmk) ^ 3 * Cd * (32 * Kmk) * Clog *
          (2:ℝ) ^ ((11:ℝ)/3) * 2) * Z ^ 4 * Δ ^ ((11:ℝ)/3) * (Real.log (2*Δ))^2 := hfin

end

end Work.HP.MDEstimates
