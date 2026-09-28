import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDEstimates.detL_one_le
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.Lat.detL_inf_latOrth
import Submission.Work.HP.EELower.PrimBallLower

/-!
# `Work.HP.EE_lower_all`

The lower half of Lemma E of Browning--Le Boudec--Sawin, *The Hasse principle for random Fano
hypersurfaces*, Annals of Math. 197 (2023): for `2 ≤ d ≤ n` with `(d,n) ≠ (2,2)`,

`E_{d,n}(B) = ∑_{(x,y) ∈ Ω_{d,n}(B)} 1 / det(Λ_{ν(x)} ∩ Λ_{ν(y)}) ≫ B²`.

**Proof.**  Put `T = B^{1/(n+1-d)}`; then `Ω_{d,n}(B)` is the set of pairs of primitive `x, y`
with `‖x‖, ‖y‖ ≤ T` and `x ≠ ±y`, and `T^{n+1-d} = B`.

* `#Ξ(B) ≫ T^{n+1}`: the primitive-vector count of `MDEstimates.prim_ball_count_lower` for the
  ball in `ℤ^{n+1}`.
* `Ω_{d,n}(B)` is `Ξ × Ξ` with the diagonal and the anti-diagonal removed, so
  `#Ω ≥ #Ξ² - 2 #Ξ` (each removed slice has at most `#Ξ` elements), hence `#Ω ≫ T^{2n+2}`.
* Every summand is at least `1/(N_{d,n} T^{2d})`: the paper's upper bound
  `det(Λ_{ν(x)} ∩ Λ_{ν(y)}) ≤ ‖ν(x)‖ ‖ν(y)‖` (`Lat.detL_inf_latOrth` and `wedgeNorm ≤ ‖·‖‖·‖`)
  together with `‖ν(z)‖ ≤ √(N_{d,n}) ‖z‖^d` (`eNorm_veronese_bounds`).
* Hence `E_{d,n}(B) ≫ T^{2n+2} / T^{2d} = T^{2(n+1-d)} = B²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MvPolynomial Finset
open scoped BigOperators

namespace Work.HP

/-! ## Elementary facts -/

private lemma eNorm_nonneg' {ι : Type*} [Fintype ι] (v : ι → ℤ) : 0 ≤ eNorm v :=
  Real.sqrt_nonneg _

/-- `(B ^ m) ^ (1/m) = B` for `B ≥ 0`, `m > 0`. -/
private lemma rpow_inv_nat (B : ℝ) (hB : 0 ≤ B) (m : ℕ) (hm : 0 < m) :
    (B ^ m) ^ (1 / (m : ℝ)) = B := by
  have hmne : ((m : ℕ) : ℝ) ≠ 0 := by positivity
  rw [← Real.rpow_natCast B m, ← Real.rpow_mul hB (m : ℝ) (1 / (m : ℝ))]
  rw [show (m : ℝ) * (1 / (m : ℝ)) = 1 by field_simp, Real.rpow_one]

/-- `(B ^ (1/m)) ^ m = B` for `B ≥ 0`, `m > 0`. -/
private lemma rpow_nat_inv (B : ℝ) (hB : 0 ≤ B) (m : ℕ) (hm : 0 < m) :
    (B ^ (1 / (m : ℝ))) ^ m = B := by
  have hmne : ((m : ℕ) : ℝ) ≠ 0 := by positivity
  rw [← Real.rpow_natCast (B ^ (1 / (m : ℝ))) m,
    ← Real.rpow_mul hB (1 / (m : ℝ)) (m : ℝ)]
  rw [show (1 / (m : ℝ)) * (m : ℝ) = 1 by field_simp, Real.rpow_one]

/-- The covolume `wedgeNorm v w` of `ℤv ⊕ ℤw` is at most the product of the norms. -/
private lemma wedgeNorm_le_mul {ι : Type*} [Fintype ι] (v w : ι → ℤ) :
    wedgeNorm v w ≤ eNorm v * eNorm w := by
  have hv : 0 ≤ eNorm v := eNorm_nonneg' v
  have hw : 0 ≤ eNorm w := eNorm_nonneg' w
  have h1 : eNorm v ^ 2 * eNorm w ^ 2 - (dotR (toR v) (toR w)) ^ 2
      ≤ (eNorm v * eNorm w) ^ 2 := by
    rw [mul_pow]
    linarith [sq_nonneg (dotR (toR v) (toR w))]
  calc wedgeNorm v w
      = Real.sqrt (eNorm v ^ 2 * eNorm w ^ 2 - (dotR (toR v) (toR w)) ^ 2) := rfl
    _ ≤ Real.sqrt ((eNorm v * eNorm w) ^ 2) := Real.sqrt_le_sqrt h1
    _ = eNorm v * eNorm w := Real.sqrt_sq (mul_nonneg hv hw)

/-- The paper's upper bound for the determinant of `Γ_{x,y} = Λ_{ν(x)} ∩ Λ_{ν(y)}`:
`det Γ_{x,y} ≤ N_{d,n} · (‖x‖‖y‖)^d` for primitive `x ≠ ±y`. -/
private lemma detL_Gam_le (d n : ℕ) (hd : 2 ≤ d) (x y : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (hy : IsPrim y) (h1 : x ≠ y) (h2 : x ≠ -y) :
    detL (Gam d n x y) ≤ (NN d n : ℝ) * (eNorm x * eNorm y) ^ d := by
  have hli : LinearIndependent ℤ ![veronese d n x, veronese d n y] :=
    Sig2.nu_indep d n hd x y hx hy h1 h2
  have hdet := Lat.detL_inf_latOrth (veronese d n x) (veronese d n y) hli
  have hwn : 0 ≤ wedgeNorm (veronese d n x) (veronese d n y) := Real.sqrt_nonneg _
  -- the gcd of the minors is nonzero, so the division can only decrease the covolume
  have hdet' : detL (Gam d n x y) ≤ wedgeNorm (veronese d n x) (veronese d n y) := by
    rw [show Gam d n x y = latOrth (veronese d n x) ⊓ latOrth (veronese d n y) from rfl, hdet]
    rcases eq_or_ne ((gcdMinors2 (veronese d n x) (veronese d n y) : ℤ) : ℝ) 0 with hg | hg
    · rw [hg, abs_zero, div_zero]
      exact hwn
    · have hne : gcdMinors2 (veronese d n x) (veronese d n y) ≠ 0 := by
        intro h0
        exact hg (by rw [h0]; norm_num)
      have h1g : (1 : ℝ) ≤ |((gcdMinors2 (veronese d n x) (veronese d n y) : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast (Int.one_le_abs hne)
      exact div_le_self hwn h1g
  -- the Veronese norms
  have he1 : eNorm (veronese d n x) ≤ Real.sqrt (NN d n) * eNorm x ^ d := by
    rw [eNorm_eq_rNorm_toR (veronese d n x), toR_veronese, eNorm_eq_rNorm_toR x]
    exact veronese_rNorm_upper d n (toR x)
  have he2 : eNorm (veronese d n y) ≤ Real.sqrt (NN d n) * eNorm y ^ d := by
    rw [eNorm_eq_rNorm_toR (veronese d n y), toR_veronese, eNorm_eq_rNorm_toR y]
    exact veronese_rNorm_upper d n (toR y)
  calc detL (Gam d n x y) ≤ wedgeNorm (veronese d n x) (veronese d n y) := hdet'
    _ ≤ eNorm (veronese d n x) * eNorm (veronese d n y) := wedgeNorm_le_mul _ _
    _ ≤ (Real.sqrt (NN d n) * eNorm x ^ d) * (Real.sqrt (NN d n) * eNorm y ^ d) :=
        mul_le_mul he1 he2 (eNorm_nonneg' _)
          (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (eNorm_nonneg' _) d))
    _ = (NN d n : ℝ) * (eNorm x * eNorm y) ^ d := by
        rw [mul_pow]
        have hs : Real.sqrt (NN d n) * Real.sqrt (NN d n) = (NN d n : ℝ) :=
          Real.mul_self_sqrt (by positivity)
        linear_combination (eNorm x ^ d * eNorm y ^ d) * hs

/-! ## The number of pairs in `Ω_{d,n}(B)` -/

/-- `Ω_{d,n}(B)` is `Ξ_{d,n}(B) × Ξ_{d,n}(B)` with the diagonal and the anti-diagonal removed,
so it has at least `#Ξ² - 2 #Ξ` elements. -/
private lemma ncard_Omega_lower (d n : ℕ) (B : ℝ) :
    ((Xi d n B).ncard : ℝ) ^ 2 - 2 * ((Xi d n B).ncard : ℝ)
      ≤ ((Omega d n B).ncard : ℝ) := by
  classical
  have hXi : (Xi d n B).Finite := (MDBasic.finite_sets d n 0 B (fun _ => True)).2.1
  have hΩ : (Omega d n B).Finite := (MDBasic.finite_sets d n 0 B (fun _ => True)).2.2
  set S : Finset (Fin (n + 1) → ℤ) := hXi.toFinset with hS
  have hmem : ∀ x : Fin (n + 1) → ℤ, x ∈ S ↔ x ∈ Xi d n B := by
    intro x
    rw [hS]
    exact Set.Finite.mem_toFinset hXi
  have hScard : (S.card : ℝ) = ((Xi d n B).ncard : ℝ) := by
    rw [hS, Set.ncard_eq_toFinset_card _ hXi]
  -- the pairs of `S × S` whose entries differ and are not opposite
  set G : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
    (S.product S).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2) with hG
  have hGsub : (G : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))) ⊆ Omega d n B := by
    intro p hp
    rw [hG, Finset.mem_coe] at hp
    obtain ⟨hpS, hp1, hp2⟩ := Finset.mem_filter.mp hp
    obtain ⟨hm1, hm2⟩ := Finset.mem_product.mp hpS
    exact ⟨(hmem p.1).mp hm1, (hmem p.2).mp hm2, hp1, hp2⟩
  have hle : (G.card : ℝ) ≤ ((Omega d n B).ncard : ℝ) := by
    have h := Set.ncard_le_ncard hGsub hΩ
    rw [Set.ncard_coe_finset] at h
    exact_mod_cast h
  -- split the full product into `G` and the complementary (bad) pairs
  have hpart : G.card + ((S.product S).filter (fun p => ¬ (p.1 ≠ p.2 ∧ p.1 ≠ -p.2))).card
      = S.card * S.card := by
    rw [← Finset.card_product, hG]
    exact Finset.card_filter_add_card_filter_not _
  -- the bad pairs number at most `2 #S`
  have hbad : ((S.product S).filter (fun p => ¬ (p.1 ≠ p.2 ∧ p.1 ≠ -p.2))).card
      ≤ 2 * S.card := by
    have heq : (S.product S).filter (fun p => ¬ (p.1 ≠ p.2 ∧ p.1 ≠ -p.2))
        = (S.product S).filter (fun p => p.1 = p.2 ∨ p.1 = -p.2) := by
      refine Finset.filter_congr ?_
      intro p _
      simp only [ne_eq, not_and_or, not_not]
    rw [heq, Finset.filter_or]
    have hdiag : ((S.product S).filter (fun p => p.1 = p.2)).card ≤ S.card := by
      have himg : (S.product S).filter (fun p => p.1 = p.2) = S.image (fun x => (x, x)) := by
        ext p
        rw [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨hpS, h⟩
          obtain ⟨h1, -⟩ := Finset.mem_product.mp hpS
          exact ⟨p.1, h1, Prod.ext rfl h⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨Finset.mem_product.mpr ⟨hx, hx⟩, rfl⟩
      rw [himg, Finset.card_image_of_injective _ (fun x y hxy => (Prod.mk.inj hxy).1)]
    have hanti : ((S.product S).filter (fun p => p.1 = -p.2)).card ≤ S.card := by
      have himg : (S.product S).filter (fun p => p.1 = -p.2)
          = (S.filter (fun x => -x ∈ S)).image (fun x => (x, -x)) := by
        ext p
        rw [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨hpS, h⟩
          obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpS
          exact ⟨p.1, Finset.mem_filter.mpr ⟨h1, by rw [h, neg_neg]; exact h2⟩,
            Prod.ext rfl (by rw [h, neg_neg])⟩
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
          exact ⟨Finset.mem_product.mpr ⟨hx1, hx2⟩, by simp⟩
      rw [himg, Finset.card_image_of_injective _ (fun x y hxy => (Prod.mk.inj hxy).1)]
      exact Finset.card_filter_le _ _
    calc (((S.product S).filter (fun p => p.1 = p.2))
            ∪ ((S.product S).filter (fun p => p.1 = -p.2))).card
        ≤ ((S.product S).filter (fun p => p.1 = p.2)).card
            + ((S.product S).filter (fun p => p.1 = -p.2)).card := Finset.card_union_le _ _
      _ ≤ S.card + S.card := add_le_add hdiag hanti
      _ = 2 * S.card := by ring
  have hGcard : ((S.card : ℝ)) ^ 2 - 2 * (S.card : ℝ) ≤ (G.card : ℝ) := by
    have h1 : (G.card : ℝ)
        = (S.card : ℝ) * (S.card : ℝ)
          - (((S.product S).filter (fun p => ¬ (p.1 ≠ p.2 ∧ p.1 ≠ -p.2))).card : ℝ) := by
      have hc := congrArg (fun k : ℕ => (k : ℝ)) hpart
      push_cast at hc
      linarith
    have h2 : (((S.product S).filter (fun p => ¬ (p.1 ≠ p.2 ∧ p.1 ≠ -p.2))).card : ℝ)
        ≤ 2 * (S.card : ℝ) := by exact_mod_cast hbad
    linarith
  rw [← hScard]
  linarith [hGcard, hle]

/-! ## The lower bound for `E_{d,n}(B)` -/

theorem EE_lower_all (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2)) :
    ∃ c B₀ : ℝ, 0 < c ∧ ∀ B : ℝ, B₀ ≤ B → c * B ^ 2 ≤ EE d n B := by
  -- `n ≥ 3`: `n ≥ d ≥ 2` while `n = 2` forces `(d,n) = (2,2)`
  have hn3 : 3 ≤ n := by
    rcases eq_or_ne n 2 with h | h
    · exfalso
      subst h
      have hd2 : d = 2 := le_antisymm hdn hd
      exact h22 (by rw [hd2])
    · omega
  have hn2 : 2 ≤ n := by omega
  -- the primitive-vector count in `ℤ^{n+1}`
  obtain ⟨c₁, R₀, hc₁, hR₀, hcnt⟩ := EELower.prim_ball_lower_all (n + 1) (by omega)
  -- the pointwise bound on `detL Γ`
  set C : ℝ := (NN d n : ℝ) with hC
  have hCpos : 0 < C := by
    rw [hC]
    exact_mod_cast (by have h := six_le_NN d n hd hdn; omega : 0 < NN d n)
  -- thresholds
  set X : ℝ := max (max 1 (4 / c₁)) R₀ with hX
  have hXpos : 0 < X := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) (le_max_left _ _))
  have hX4 : 4 / c₁ ≤ X := le_trans (le_max_right _ _) (le_max_left _ _)
  have hXR : R₀ ≤ X := le_max_right _ _
  set m : ℕ := n + 1 - d with hm
  have hmpos : 0 < m := by omega
  have hmne : ((m : ℕ) : ℝ) ≠ 0 := by positivity
  have hexp : (1 : ℝ) / ((n : ℝ) + 1 - d) = 1 / (m : ℝ) := by
    congr 1
    rw [hm]
    push_cast [Nat.cast_sub (by omega : d ≤ n + 1)]
    ring
  refine ⟨c₁ ^ 2 / (2 * C), max 1 (X ^ m), div_pos (pow_pos hc₁ 2) (by positivity), ?_⟩
  intro B hB
  have hB1 : 1 ≤ B := le_trans (le_max_left _ _) hB
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB1
  have hBm : X ^ m ≤ B := le_trans (le_max_right _ _) hB
  set T : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hT
  have hT1 : 1 ≤ T := by
    rw [hT]
    calc (1 : ℝ) = 1 ^ (1 / ((n : ℝ) + 1 - d)) := (Real.one_rpow _).symm
      _ ≤ B ^ (1 / ((n : ℝ) + 1 - d)) := by
          apply Real.rpow_le_rpow zero_le_one hB1
          have hdn' : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
          have hpos : (0 : ℝ) < (n : ℝ) + 1 - d := by linarith
          exact le_of_lt (one_div_pos.mpr hpos)
  have hTge : X ≤ T := by
    rw [hT, hexp]
    calc X = (X ^ m) ^ (1 / (m : ℝ)) := (rpow_inv_nat X (le_of_lt hXpos) m hmpos).symm
      _ ≤ B ^ (1 / (m : ℝ)) := Real.rpow_le_rpow (by positivity) hBm (by positivity)
  have hTm : T ^ m = B := by
    rw [hT, hexp]
    exact rpow_nat_inv B (le_of_lt hB0) m hmpos
  have hXieq : Xi d n B = {x : Fin (n + 1) → ℤ | IsPrim x ∧ eNorm x ≤ T} := by
    rw [hT]
    rfl
  have hcount : c₁ * T ^ (n + 1) ≤ ((Xi d n B).ncard : ℝ) := by
    rw [hXieq]
    exact hcnt T (le_trans hXR hTge)
  -- `#Ξ ≥ 4`
  have hP4 : (4 : ℝ) ≤ ((Xi d n B).ncard : ℝ) := by
    have hTle : T ≤ T ^ (n + 1) := by
      calc T = T ^ 1 := (pow_one T).symm
        _ ≤ T ^ (n + 1) := pow_le_pow_right₀ hT1 (by omega)
    have h4T : (4 : ℝ) ≤ c₁ * T := by
      have h1 : c₁ * (4 / c₁) = 4 := by field_simp
      calc (4 : ℝ) = c₁ * (4 / c₁) := h1.symm
        _ ≤ c₁ * T := mul_le_mul_of_nonneg_left (le_trans hX4 hTge) (le_of_lt hc₁)
    linarith [mul_le_mul_of_nonneg_left hTle (le_of_lt hc₁), hcount]
  -- every summand is at least `1/(C T^{2d})`
  have hterm : ∀ p, p ∈ Omega d n B → 1 / (C * T ^ (2 * d)) ≤ 1 / detL (Gam d n p.1 p.2) := by
    intro p hp
    obtain ⟨hp1, hp2, hne, hne'⟩ := hp
    have hdet : detL (Gam d n p.1 p.2) ≤ C * T ^ (2 * d) := by
      have h := detL_Gam_le d n hd p.1 p.2 hp1.1 hp2.1 hne hne'
      have he1 : eNorm p.1 ≤ T := by rw [hT]; exact hp1.2
      have he2 : eNorm p.2 ≤ T := by rw [hT]; exact hp2.2
      have hprod : (eNorm p.1 * eNorm p.2) ^ d ≤ T ^ (2 * d) := by
        have h1 : eNorm p.1 * eNorm p.2 ≤ T * T :=
          mul_le_mul he1 he2 (eNorm_nonneg' _) (le_of_lt (lt_of_lt_of_le one_pos hT1))
        calc (eNorm p.1 * eNorm p.2) ^ d ≤ (T * T) ^ d :=
              pow_le_pow_left₀ (mul_nonneg (eNorm_nonneg' _) (eNorm_nonneg' _)) h1 d
          _ = T ^ (2 * d) := by rw [← sq, pow_mul]
      calc detL (Gam d n p.1 p.2) ≤ C * (eNorm p.1 * eNorm p.2) ^ d := by rw [hC]; exact h
        _ ≤ C * T ^ (2 * d) := mul_le_mul_of_nonneg_left hprod (le_of_lt hCpos)
    exact one_div_le_one_div_of_le
      (lt_of_lt_of_le zero_lt_one (MDEstimates.detL_one_le _)) hdet
  -- `E ≥ #Ω · 1/(C T^{2d})`
  have hEEge : ((Omega d n B).ncard : ℝ) * (1 / (C * T ^ (2 * d))) ≤ EE d n B := by
    have hΩfin : (Omega d n B).Finite := (MDBasic.finite_sets d n 0 B (fun _ => True)).2.2
    set f : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) → ℝ :=
      fun p => 1 / detL (Gam d n p.1 p.2) with hfdef
    have hsupp : Omega d n B ⊆ Function.support f := by
      intro p hp
      rw [Function.mem_support, hfdef]
      simp only
      intro hz
      have h1 := hterm p hp
      rw [hz] at h1
      have h2 : (0 : ℝ) < 1 / (C * T ^ (2 * d)) := by positivity
      linarith
    have hf : (Omega d n B ∩ Function.support f).Finite := hΩfin.inter_of_left _
    have heq : hf.toFinset = hΩfin.toFinset :=
      Set.Finite.toFinset_inj.mpr (Set.inter_eq_left.mpr hsupp)
    have h1 : EE d n B = ∑ p ∈ hf.toFinset, f p := by
      rw [EE]
      exact finsum_mem_eq_sum f hf
    calc ((Omega d n B).ncard : ℝ) * (1 / (C * T ^ (2 * d)))
        = ((hΩfin.toFinset.card : ℕ) : ℝ) * (1 / (C * T ^ (2 * d))) := by
          rw [Set.ncard_eq_toFinset_card _ hΩfin]
      _ = ∑ p ∈ hΩfin.toFinset, (1 / (C * T ^ (2 * d))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ hΩfin.toFinset, f p :=
          Finset.sum_le_sum (fun p hp => hterm p ((Set.Finite.mem_toFinset hΩfin).mp hp))
      _ = EE d n B := by rw [h1, heq]
  -- `#Ω ≥ #Ξ²/2`
  have hOm2 : ((Xi d n B).ncard : ℝ) ^ 2 / 2 ≤ ((Omega d n B).ncard : ℝ) := by
    have h := ncard_Omega_lower d n B
    nlinarith [h, hP4, Nat.cast_nonneg (α := ℝ) (Xi d n B).ncard]
  have hA : c₁ * T ^ d * B ≤ ((Xi d n B).ncard : ℝ) := by
    have hpow : T ^ (n + 1) = T ^ d * T ^ m := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow, hTm] at hcount
    linarith [hcount]
  have hA2 : (c₁ * T ^ d * B) ^ 2 / 2 ≤ ((Omega d n B).ncard : ℝ) := by
    have hnn : 0 ≤ c₁ * T ^ d * B := by positivity
    have hsq := pow_le_pow_left₀ hnn hA 2
    linarith [hsq, hOm2]
  have hD : 0 < C * T ^ (2 * d) := by positivity
  have hkey : (c₁ ^ 2 / (2 * C)) * B ^ 2 * (C * T ^ (2 * d)) = (c₁ * T ^ d * B) ^ 2 / 2 := by
    have hsq : (T ^ d) ^ 2 = T ^ (2 * d) := by
      rw [← pow_mul]
      congr 1
      ring
    rw [mul_pow, mul_pow, hsq]
    field_simp
  have hEE2 : ((Omega d n B).ncard : ℝ) / (C * T ^ (2 * d)) ≤ EE d n B := by
    have h := hEEge
    rwa [mul_one_div] at h
  calc c₁ ^ 2 / (2 * C) * B ^ 2
      = c₁ ^ 2 / (2 * C) * B ^ 2 * (C * T ^ (2 * d)) / (C * T ^ (2 * d)) := by
        field_simp
      _ ≤ ((Omega d n B).ncard : ℝ) / (C * T ^ (2 * d)) := by
        rw [hkey]
        exact div_le_div_of_nonneg_right hA2 (le_of_lt hD)
      _ ≤ EE d n B := hEE2

end Work.HP
