import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.PrimBoxDefs
import Submission.Work.HP.box_card
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.numaux.rk_satLat
import Submission.Work.HP.numaux.detL_le_of_le
import Submission.Work.HP.numaux.detL_span_le_prod
import Submission.Work.HP.MDEstimates.detL_one_le
import Submission.Work.HP.EElow.detL_orthLat

/-!
# `E_{d,n}(B) ≫ B²` (lower half of Lemma E of Browning--Le Boudec--Sawin)

`EE d n B = ∑_{p ∈ Ω_{d,n}(B)} 1 / det (Λ_{ν(x)} ⊓ Λ_{ν(y)})`.  We prove the lower bound
`B² ≤ K · EE d n B` for `B ≥ B₀`, the "trivial" half of the paper's Lemma E.

Route (paper §4.3, proof of Lemma E):
* pointwise, `det Γ_{x,y} ≤ ‖ν(x)‖‖ν(y)‖`: by `EElow.detL_orthLat` (reciprocal covolume),
  `detL (orthLat K) = detL K` for a primitive `K`; here `Γ_{x,y} = orthLat (ℤν(x) + ℤν(y))`,
  so `detL Γ_{x,y} = detL (sat (ℤν(x) ⊕ ℤν(y))) ≤ detL (ℤν(x) ⊕ ℤν(y)) ≤ ‖ν(x)‖‖ν(y)‖`
  (Hadamard);
* `‖ν(x)‖ ≤ √N ‖x‖^d`, so every pair of primitive vectors with `‖x‖, ‖y‖ ≤ T/2`
  (`T = B^{1/(n+1-d)}`) contributes at least `1/((√N (T/2)^d)²)`;
* there are `≫ T^{2(n+1)}` such pairs, while `T^{2(n+1)-2d} = B²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial Finset
open scoped BigOperators

namespace Work.HP.Sig2

/-- Every degree-`d` monomial of `x` is at most `‖x‖ ^ d` in absolute value. -/
lemma abs_veronese_le (d n : ℕ) (x : Fin (n + 1) → ℤ) (m : Mon d n) :
    |(((veronese d n x m : ℤ)) : ℝ)| ≤ (eNorm x) ^ d := by
  have h1 : (((veronese d n x m : ℤ)) : ℝ) = ∏ i, ((x i : ℤ) : ℝ) ^ (m.1 i : ℕ) := by
    rw [veronese]
    push_cast
    rfl
  rw [h1, Finset.abs_prod]
  calc ∏ i, |((x i : ℤ) : ℝ) ^ (m.1 i : ℕ)|
      = ∏ i, |((x i : ℤ) : ℝ)| ^ (m.1 i : ℕ) :=
        Finset.prod_congr rfl fun i _ => abs_pow _ _
    _ ≤ ∏ i, (eNorm x) ^ (m.1 i : ℕ) := by
        gcongr with i
        exact abs_coord_le_eNorm x i
    _ = (eNorm x) ^ d := by
        rw [Finset.prod_pow_eq_pow_sum, m.2]

/-- `‖ν_{d,n}(x)‖ ≤ √N ‖x‖^d`. -/
lemma eNorm_veronese_le (d n : ℕ) (x : Fin (n + 1) → ℤ) :
    eNorm (veronese d n x) ≤ Real.sqrt (NN d n) * (eNorm x) ^ d := by
  have heN : 0 ≤ eNorm x := Real.sqrt_nonneg _
  have hsq : (eNorm (veronese d n x)) ^ 2 ≤ (NN d n : ℝ) * ((eNorm x) ^ d) ^ 2 := by
    rw [eNorm, Real.sq_sqrt (Finset.sum_nonneg fun m _ => sq_nonneg _)]
    calc ∑ m, (((veronese d n x m : ℤ)) : ℝ) ^ 2
        ≤ ∑ _m : Mon d n, ((eNorm x) ^ d) ^ 2 := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_veronese_le d n x m) 2
      _ = (NN d n : ℝ) * ((eNorm x) ^ d) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc eNorm (veronese d n x)
      = Real.sqrt ((eNorm (veronese d n x)) ^ 2) := (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
    _ ≤ Real.sqrt ((NN d n : ℝ) * ((eNorm x) ^ d) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (NN d n) * (eNorm x) ^ d := by
        rw [Real.sqrt_mul (Nat.cast_nonneg (NN d n))]
        congr 1
        exact Real.sqrt_sq (pow_nonneg heN d)

/-- `det Γ_{x,y} ≤ ‖ν(x)‖‖ν(y)‖` for primitive `x ≠ ±y`. -/
lemma detL_Gam_le (d n : ℕ) (hd : 2 ≤ d) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (h1 : x ≠ y) (h2 : x ≠ -y) :
    detL (Gam d n x y) ≤ eNorm (veronese d n x) * eNorm (veronese d n y) := by
  set v : Mon d n → ℤ := veronese d n x with hv
  set w : Mon d n → ℤ := veronese d n y with hw
  have hid : LinearIndependent ℤ ![v, w] := nu_indep d n hd x y hx hy h1 h2
  have hspan : Submodule.span ℤ (Set.range ![v, w])
      = Submodule.span ℤ ({v, w} : Set (Mon d n → ℤ)) := by
    congr 1
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hΓ : Gam d n x y = orthLat (Submodule.span ℤ ({v, w} : Set (Mon d n → ℤ))) := by
    ext a
    simp only [Gam, Submodule.mem_inf, latOrth, LinearMap.mem_ker, mem_orthLat]
    constructor
    · rintro ⟨hva, hwa⟩ z hz
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
      · rintro u (rfl | rfl)
        · simpa [hv, dotI, Fintype.linearCombination_apply, smul_eq_mul] using hva
        · simpa [hw, dotI, Fintype.linearCombination_apply, smul_eq_mul] using hwa
      · simp [dotI]
      · intro p q hp hq ihp ihq
        rw [dotI_add_right, ihp, ihq, add_zero]
      · intro cc p hp ihp
        rw [dotI_smul_right, ihp, mul_zero]
    · intro h
      constructor
      · have hh := h v (Submodule.subset_span (by simp))
        simpa [hv, dotI, Fintype.linearCombination_apply, smul_eq_mul] using hh
      · have hh := h w (Submodule.subset_span (by simp))
        simpa [hw, dotI, Fintype.linearCombination_apply, smul_eq_mul] using hh
  have hsat : orthLat (Submodule.span ℤ ({v, w} : Set (Mon d n → ℤ)))
      = orthLat (satLat (Submodule.span ℤ ({v, w} : Set (Mon d n → ℤ)))) := by
    refine le_antisymm ?_ (orthLat_antitone (le_satLat _))
    intro a ha
    rw [mem_orthLat] at ha ⊢
    intro z hz
    obtain ⟨m, hm, hmz⟩ := mem_satLat.mp hz
    have hh := ha (m • z) hmz
    rw [dotI_smul_right] at hh
    exact (mul_eq_zero.mp hh).resolve_left hm
  calc detL (Gam d n x y)
      = detL (orthLat (satLat (Submodule.span ℤ ({v, w} : Set (Mon d n → ℤ))))) := by
        rw [hΓ, hsat]
    _ = detL (satLat (Submodule.span ℤ ({v, w} : Set (Mon d n → ℤ)))) :=
        EElow.detL_orthLat _ (isPrimLat_satLat _)
    _ ≤ detL (Submodule.span ℤ ({v, w} : Set (Mon d n → ℤ))) :=
        numaux.detL_le_of_le (le_satLat _) (numaux.rk_satLat _).symm
    _ ≤ eNorm v * eNorm w := by
        rw [← hspan]
        have hh := numaux.detL_span_le_prod (b := ![v, w]) hid
        refine le_trans hh ?_
        rw [Fin.prod_univ_two]
        simp

/-- Among the `S.card²` ordered pairs from `S`, at least `S.card (S.card - 2)` have distinct and
non-opposite entries. -/
lemma card_good_pairs {m : ℕ} (S : Finset (Fin m → ℤ)) :
    S.card * (S.card - 2) ≤ ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2)).card := by
  classical
  set A : Finset ((Fin m → ℤ) × (Fin m → ℤ)) := (S ×ˢ S).filter (fun p => p.1 = p.2) with hA
  set B : Finset ((Fin m → ℤ) × (Fin m → ℤ)) := (S ×ˢ S).filter (fun p => p.1 = -p.2) with hB
  have hApred : ∀ p, p ∈ A ↔ (p ∈ S ×ˢ S ∧ p.1 = p.2) := by
    intro p; rw [hA]; exact Finset.mem_filter
  have hBpred : ∀ p, p ∈ B ↔ (p ∈ S ×ˢ S ∧ p.1 = -p.2) := by
    intro p; rw [hB]; exact Finset.mem_filter
  have hsub : (S ×ˢ S) \ (A ∪ B) ⊆ (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2) := by
    intro p hp
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or, Finset.mem_filter] at hp ⊢
    obtain ⟨hpS, hpA, hpB⟩ := hp
    exact ⟨hpS, fun h => hpA ((hApred p).mpr ⟨hpS, h⟩), fun h => hpB ((hBpred p).mpr ⟨hpS, h⟩)⟩
  have h1 : ((S ×ˢ S) \ (A ∪ B)).card ≤ ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2)).card :=
    Finset.card_le_card hsub
  have h2 : ((S ×ˢ S) \ (A ∪ B)).card = (S ×ˢ S).card - (A ∪ B).card :=
    Finset.card_sdiff_of_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hA' : A.card ≤ S.card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (f := fun x => (x, x)))
    intro p hp
    obtain ⟨hpS, hp2⟩ := (hApred p).mp hp
    obtain ⟨h1, -⟩ := Finset.mem_product.mp hpS
    exact Finset.mem_image.mpr ⟨p.1, h1, by ext <;> simp [hp2]⟩
  have hB' : B.card ≤ S.card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (f := fun x => (x, -x)))
    intro p hp
    obtain ⟨hpS, hp2⟩ := (hBpred p).mp hp
    obtain ⟨h1, -⟩ := Finset.mem_product.mp hpS
    exact Finset.mem_image.mpr ⟨p.1, h1, by ext <;> simp [hp2]⟩
  have h3 : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
  have h4 : (S ×ˢ S).card = S.card * S.card := Finset.card_product S S
  have h5 : S.card * (S.card - 2) = S.card * S.card - 2 * S.card := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_comm S.card 2]
  omega

/-- `∑_{2 ≤ g ≤ N} g⁻⁴ ≤ 0.094`; the true value of the tail is `π⁴/90 - 1 = 0.0823…`. -/
private lemma zeta4_sum_le (N : ℕ) :
    ∑ g ∈ Finset.Ico 2 (N + 1), (1 : ℝ) / ((g : ℝ) ^ 4) ≤ (0.094 : ℝ) := by
  have hS : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 4)) := hasSum_zeta_four.summable
  have hshift : Summable (fun k : ℕ => (1 : ℝ) / (((k + 2 : ℕ) : ℝ) ^ 4)) :=
    (summable_nat_add_iff 2).mpr hS
  have hpi : Real.pi ^ 4 / 90 - 1 ≤ (0.094 : ℝ) := by
    have h2 : Real.pi ^ 4 < (3.15 : ℝ) ^ 4 :=
      pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by norm_num)
    nlinarith [h2]
  have htail : ∑' k : ℕ, (1 : ℝ) / (((k + 2 : ℕ) : ℝ) ^ 4) = Real.pi ^ 4 / 90 - 1 := by
    have h := hS.sum_add_tsum_nat_add 2
    rw [hasSum_zeta_four.tsum_eq] at h
    have h2 : ∑ i ∈ Finset.range 2, (1 : ℝ) / ((i : ℝ) ^ 4) = 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    linarith
  have hreindex : ∑ g ∈ Finset.Ico 2 (N + 1), (1 : ℝ) / ((g : ℝ) ^ 4)
      = ∑ k ∈ Finset.range (N + 1 - 2), (1 : ℝ) / (((k + 2 : ℕ) : ℝ) ^ 4) := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_comm]
  rw [hreindex]
  calc ∑ k ∈ Finset.range (N + 1 - 2), (1 : ℝ) / (((k + 2 : ℕ) : ℝ) ^ 4)
      ≤ ∑' k : ℕ, (1 : ℝ) / (((k + 2 : ℕ) : ℝ) ^ 4) :=
        Summable.sum_le_tsum _ (fun i _ => by positivity) hshift
    _ = Real.pi ^ 4 / 90 - 1 := htail
    _ ≤ 0.094 := hpi

/-- `∑_{2 ≤ g ≤ N} (2⌊N/g⌋+1)^m ≤ ½(2N+1)^m` for `m ≥ 4` and `N ≥ 2`: the standard union bound
over common divisors of the coordinates, with the cruder factor `3/(2g)` in place of `1/g`
(so that only `∑ g⁻⁴` is needed). -/
private lemma sum_ratio_le (m N : ℕ) (hm : 4 ≤ m) (hN : 2 ≤ N) :
    ∑ g ∈ Finset.Ico 2 (N + 1), (2 * ((N / g : ℕ) : ℝ) + 1) ^ m
      ≤ (1 / 2) * (2 * (N : ℝ) + 1) ^ m := by
  have hpt : ∀ g ∈ Finset.Ico 2 (N + 1),
      (2 * ((N / g : ℕ) : ℝ) + 1) ^ m ≤ (3 / (2 * (g : ℝ))) ^ 4 * (2 * (N : ℝ) + 1) ^ m := by
    intro g hg
    obtain ⟨hg2, hgN⟩ := Finset.mem_Ico.mp hg
    have hg2R : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg2
    have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
    have hgle : (g : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : g ≤ N)
    have hbase : 2 * ((N / g : ℕ) : ℝ) + 1 ≤ (3 / (2 * (g : ℝ))) * (2 * (N : ℝ) + 1) := by
      have h1 : ((N / g : ℕ) : ℝ) ≤ (N : ℝ) / g := Nat.cast_div_le
      have h3 : 2 * ((N : ℝ) / (g : ℝ)) + 1 = (2 * (N : ℝ) + (g : ℝ)) / (g : ℝ) := by
        field_simp
      have h2 : 2 * ((N / g : ℕ) : ℝ) + 1 ≤ (2 * (N : ℝ) + (g : ℝ)) / (g : ℝ) := by
        rw [← h3]
        linarith
      refine le_trans h2 ?_
      rw [div_le_iff₀ hgpos]
      have h4 : (3 / (2 * (g : ℝ))) * (2 * (N : ℝ) + 1) * (g : ℝ)
          = 3 * (2 * (N : ℝ) + 1) / 2 := by
        field_simp
      rw [h4]
      linarith
    have h0 : 0 ≤ 3 / (2 * (g : ℝ)) := by positivity
    have h3 : 3 / (2 * (g : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    calc (2 * ((N / g : ℕ) : ℝ) + 1) ^ m
        ≤ ((3 / (2 * (g : ℝ))) * (2 * (N : ℝ) + 1)) ^ m :=
          pow_le_pow_left₀ (by positivity) hbase m
      _ = (3 / (2 * (g : ℝ))) ^ m * (2 * (N : ℝ) + 1) ^ m := mul_pow _ _ _
      _ ≤ (3 / (2 * (g : ℝ))) ^ 4 * (2 * (N : ℝ) + 1) ^ m := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact pow_le_pow_of_le_one h0 h3 hm
  calc ∑ g ∈ Finset.Ico 2 (N + 1), (2 * ((N / g : ℕ) : ℝ) + 1) ^ m
      ≤ ∑ g ∈ Finset.Ico 2 (N + 1), (3 / (2 * (g : ℝ))) ^ 4 * (2 * (N : ℝ) + 1) ^ m :=
        Finset.sum_le_sum hpt
    _ = (2 * (N : ℝ) + 1) ^ m * ∑ g ∈ Finset.Ico 2 (N + 1), (3 / (2 * (g : ℝ))) ^ 4 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ => mul_comm _ _
    _ = (2 * (N : ℝ) + 1) ^ m
          * ((3 / 2) ^ 4 * ∑ g ∈ Finset.Ico 2 (N + 1), (1 : ℝ) / ((g : ℝ) ^ 4)) := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g hg => ?_
        obtain ⟨hg2, -⟩ := Finset.mem_Ico.mp hg
        have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 0 < g)
        field_simp
    _ ≤ (2 * (N : ℝ) + 1) ^ m * ((3 / 2) ^ 4 * 0.094) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (zeta4_sum_le N) (by norm_num)) (by positivity)
    _ ≤ (1 / 2) * (2 * (N : ℝ) + 1) ^ m := by
        have h : (3 / 2 : ℝ) ^ 4 * 0.094 ≤ 1 / 2 := by norm_num
        have h2 : (0 : ℝ) ≤ (2 * (N : ℝ) + 1) ^ m := by positivity
        nlinarith [h, h2]

/-- The `g`-divisible vectors of the box of radius `N` number at most those of the box of radius
`N / g`, via the injection `x ↦ x / g`. -/
private lemma box_div_card_le (m N g : ℕ) (hg1 : 1 ≤ g) :
    (((boxFinset N m).filter (fun x => ∀ i, (g : ℤ) ∣ x i)).card : ℕ)
      ≤ (boxFinset (N / g) m).card := by
  have hgpos : (0 : ℤ) < (g : ℤ) := by exact_mod_cast (by omega : 0 < g)
  have hgnn : (0 : ℤ) ≤ (g : ℤ) := le_of_lt hgpos
  refine Finset.card_le_card_of_injOn (fun x : Fin m → ℤ => fun i => x i / (g : ℤ)) ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx
    obtain ⟨hxb, hxd⟩ := hx
    rw [mem_boxFinset] at hxb
    simp only [Finset.mem_coe]
    rw [mem_boxFinset]
    intro i
    have hs : (x i / (g : ℤ)) * (g : ℤ) = x i := Int.ediv_mul_cancel (hxd i)
    have h1 : |x i / (g : ℤ)| * (g : ℤ) = |x i| := by
      calc |x i / (g : ℤ)| * (g : ℤ) = |x i / (g : ℤ)| * |(g : ℤ)| := by rw [abs_of_nonneg hgnn]
        _ = |(x i / (g : ℤ)) * (g : ℤ)| := (abs_mul _ _).symm
        _ = |x i| := by rw [hs]
    rw [Int.natCast_div, Int.le_ediv_iff_mul_le hgpos, h1]
    exact hxb i
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    funext i
    have h1 : (x i / (g : ℤ)) * (g : ℤ) = x i := Int.ediv_mul_cancel (hx.2 i)
    have h2 : (y i / (g : ℤ)) * (g : ℤ) = y i := Int.ediv_mul_cancel (hy.2 i)
    have h3 : x i / (g : ℤ) = y i / (g : ℤ) := congrFun hxy i
    rw [← h1, h3, h2]

/-- Non-primitive vectors in the box are counted by the union over common divisors of the
coordinates. -/
private lemma bad_card_le (m N : ℕ) (hN : 2 ≤ N) :
    (((boxFinset N m).filter (fun x => ¬ IsPrim x)).card : ℝ)
      ≤ ∑ g ∈ Finset.Ico 2 (N + 1), (2 * ((N / g : ℕ) : ℝ) + 1) ^ m := by
  classical
  have hfind : ∀ x ∈ (boxFinset N m).filter (fun x => ¬ IsPrim x),
      ∃ g ∈ Finset.Ico 2 (N + 1), ∀ i, (g : ℤ) ∣ x i := by
    intro x hx
    obtain ⟨hxb, hxnp⟩ := Finset.mem_filter.mp hx
    by_cases hx0 : x = 0
    · refine ⟨2, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩, fun i => ?_⟩
      rw [hx0]
      simp
    · set G : ℤ := Finset.univ.gcd x with hG
      have hdvd : ∀ i, G ∣ x i := fun i => Finset.gcd_dvd (Finset.mem_univ i)
      have hGne1 : G ≠ 1 := hxnp
      have hGne0 : G ≠ 0 := by
        intro h0
        refine hx0 (funext fun i => ?_)
        simpa using (Finset.gcd_eq_zero_iff.mp h0) i (Finset.mem_univ i)
      have hnorm : normalize G = G := Finset.normalize_gcd
      have hnonneg : 0 ≤ G := by
        have h := Int.abs_eq_normalize G
        rw [hnorm] at h
        rw [← h]
        exact abs_nonneg G
      have h2G : (2 : ℤ) ≤ G := by omega
      obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
        by_contra h
        exact hx0 (funext fun i => by simpa using not_not.mp (not_exists.mp h i))
      have hxi : |x i0| ≤ (N : ℤ) := (mem_boxFinset.mp hxb) i0
      have hGN : G ≤ (N : ℤ) := by
        obtain ⟨c, hc⟩ := hdvd i0
        have hcne : c ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hc
          exact hi0 hc
        have hcabs : (1 : ℤ) ≤ |c| := by
          have := abs_pos.mpr hcne
          omega
        have habs : |x i0| = G * |c| := by
          rw [hc, abs_mul, abs_of_nonneg hnonneg]
        rw [habs] at hxi
        have h1 : G * 1 ≤ G * |c| := mul_le_mul_of_nonneg_left hcabs hnonneg
        rw [mul_one] at h1
        linarith
      refine ⟨G.toNat, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, fun i => ?_⟩
      have hcast : ((G.toNat : ℕ) : ℤ) = G := Int.toNat_of_nonneg hnonneg
      rw [hcast]
      exact hdvd i
  have hsub : (boxFinset N m).filter (fun x => ¬ IsPrim x) ⊆
      (Finset.Ico 2 (N + 1)).biUnion
        (fun g => (boxFinset N m).filter (fun x => ∀ i, (g : ℤ) ∣ x i)) := fun x hx => by
    obtain ⟨g, hg, hgx⟩ := hfind x hx
    exact Finset.mem_biUnion.mpr
      ⟨g, hg, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hgx⟩⟩
  calc (((boxFinset N m).filter (fun x => ¬ IsPrim x)).card : ℝ)
      ≤ (((Finset.Ico 2 (N + 1)).biUnion
            (fun g => (boxFinset N m).filter (fun x => ∀ i, (g : ℤ) ∣ x i))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ g ∈ Finset.Ico 2 (N + 1),
            (((boxFinset N m).filter (fun x => ∀ i, (g : ℤ) ∣ x i)).card)) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ g ∈ Finset.Ico 2 (N + 1),
          ((((boxFinset N m).filter (fun x => ∀ i, (g : ℤ) ∣ x i)).card : ℕ) : ℝ) := by
        push_cast
        rfl
    _ ≤ ∑ g ∈ Finset.Ico 2 (N + 1), (2 * ((N / g : ℕ) : ℝ) + 1) ^ m := by
        refine Finset.sum_le_sum fun g hg => ?_
        obtain ⟨hg2, -⟩ := Finset.mem_Ico.mp hg
        have hg1 : 1 ≤ g := by omega
        have hcount := box_div_card_le m N g hg1
        have hc2 : ((boxFinset (N / g) m).card : ℕ) = (2 * (N / g) + 1) ^ m :=
          card_boxFinset (N / g) m
        calc ((((boxFinset N m).filter (fun x => ∀ i, (g : ℤ) ∣ x i)).card : ℕ) : ℝ)
            ≤ (((boxFinset (N / g) m).card : ℕ) : ℝ) := by exact_mod_cast hcount
          _ = (2 * ((N / g : ℕ) : ℝ) + 1) ^ m := by
              rw [hc2]
              push_cast
              ring

/-- The number of primitive vectors of norm at most `X` in `ℤ^m` is `≫ X^m` (`m ≥ 4`). -/
private lemma prim_ball_count_aux (m : ℕ) (hm : 4 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∀ X : ℝ, 2 * Real.sqrt m ≤ X → ∃ S : Finset (Fin m → ℤ),
      (∀ x ∈ S, IsPrim x ∧ eNorm x ≤ X) ∧ c * X ^ m ≤ (S.card : ℝ) := by
  classical
  have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hsp : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmp
  refine ⟨1 / (2 * (2 * Real.sqrt m) ^ m), by positivity, ?_⟩
  intro X hX
  set N : ℕ := ⌊X / Real.sqrt m⌋₊ with hNdef
  have hNge : 2 ≤ N := by
    rw [hNdef]
    apply Nat.le_floor
    rw [le_div_iff₀ hsp]
    simpa using hX
  have hNle : (N : ℝ) ≤ X / Real.sqrt m :=
    Nat.floor_le (le_of_lt (div_pos (by linarith [hsp.le, hX]) hsp))
  set Bx : Finset (Fin m → ℤ) := boxFinset N m with hBx
  set S : Finset (Fin m → ℤ) := Bx.filter IsPrim with hS
  refine ⟨S, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxb, hxp⟩ := Finset.mem_filter.mp (hS ▸ hx)
    refine ⟨hxp, ?_⟩
    have h1 : eNorm x ≤ (N : ℝ) * Real.sqrt m := by
      rw [hBx] at hxb
      exact eNorm_le_of_mem_boxFinset hxb
    have h2 : (N : ℝ) * Real.sqrt m ≤ X := by
      rw [le_div_iff₀ hsp] at hNle
      linarith
    linarith
  · have hsplit : S.card + (Bx.filter (fun x => ¬ IsPrim x)).card = Bx.card := by
      rw [hS]
      exact Finset.card_filter_add_card_filter_not (p := IsPrim)
    have hbadle : (((Bx.filter (fun x => ¬ IsPrim x)).card : ℕ) : ℝ)
        ≤ ∑ g ∈ Finset.Ico 2 (N + 1), (2 * ((N / g : ℕ) : ℝ) + 1) ^ m := by
      rw [hBx]
      exact bad_card_le m N hNge
    have hsumle := sum_ratio_le m N hm hNge
    have hBxcard : (((Bx.card : ℕ)) : ℝ) = (2 * (N : ℝ) + 1) ^ m := by
      have h := (box_card (ι := Fin m) N).1
      simp only [hBx, boxFinset] at h ⊢
      rw [h, Fintype.card_fin]
    have hScard : (1 / 2) * (2 * (N : ℝ) + 1) ^ m ≤ ((S.card : ℕ) : ℝ) := by
      have h1 : ((S.card : ℕ) : ℝ) + (((Bx.filter (fun x => ¬ IsPrim x)).card : ℕ) : ℝ)
          = ((Bx.card : ℕ) : ℝ) := by exact_mod_cast hsplit
      linarith [hbadle, hsumle, hBxcard]
    have hXle : X ≤ (2 * (N : ℝ) + 1) * (2 * Real.sqrt m) := by
      have hNlow : X / Real.sqrt m < (N : ℝ) + 1 := by
        rw [hNdef]
        exact Nat.lt_floor_add_one _
      have h5 : X = (X / Real.sqrt m) * Real.sqrt m := (div_mul_cancel₀ X (ne_of_gt hsp)).symm
      have h2 : (X / Real.sqrt m) * Real.sqrt m ≤ ((N : ℝ) + 1) * Real.sqrt m :=
        mul_le_mul_of_nonneg_right hNlow.le (by linarith [hsp.le])
      have h3 : ((N : ℝ) + 1) * Real.sqrt m ≤ (2 * (N : ℝ) + 1) * (2 * Real.sqrt m) := by
        have h4 : (N : ℝ) + 1 ≤ (2 * (N : ℝ) + 1) * 2 := by linarith
        calc ((N : ℝ) + 1) * Real.sqrt m ≤ ((2 * (N : ℝ) + 1) * 2) * Real.sqrt m :=
              mul_le_mul_of_nonneg_right h4 (by linarith [hsp.le])
          _ = (2 * (N : ℝ) + 1) * (2 * Real.sqrt m) := by ring
      linarith [h2, h3, h5]
    have hXm : X ^ m ≤ ((2 * (N : ℝ) + 1) * (2 * Real.sqrt m)) ^ m :=
      pow_le_pow_left₀ (by linarith [hsp.le, hX]) hXle m
    have hkey : 1 / (2 * (2 * Real.sqrt m) ^ m)
        * (((2 * (N : ℝ) + 1) * (2 * Real.sqrt m)) ^ m)
        = (1 / 2) * (2 * (N : ℝ) + 1) ^ m := by
      have hA : (2 * Real.sqrt m) ^ m ≠ 0 := by positivity
      have hB : ((2 * (N : ℝ) + 1)) ^ m ≠ 0 := by positivity
      have hp : ((2 * (N : ℝ) + 1) * (2 * Real.sqrt m)) ^ m
          = (2 * (N : ℝ) + 1) ^ m * (2 * Real.sqrt m) ^ m := mul_pow _ _ _
      rw [hp]
      field_simp
      try ring
    calc 1 / (2 * (2 * Real.sqrt m) ^ m) * X ^ m
        ≤ 1 / (2 * (2 * Real.sqrt m) ^ m)
            * (((2 * (N : ℝ) + 1) * (2 * Real.sqrt m)) ^ m) :=
          mul_le_mul_of_nonneg_left hXm (by positivity)
      _ = (1 / 2) * (2 * (N : ℝ) + 1) ^ m := hkey
      _ ≤ ((S.card : ℕ) : ℝ) := hScard

/-- **Lower bound for the average of `1/det Γ`**: `E_{d,n}(B) ≫ B²`. -/
theorem EE_lower (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2)) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ B : ℝ, B₀ ≤ B → B ^ 2 ≤ K * EE d n B := by
  have hn3 : 3 ≤ n := by
    rcases eq_or_ne d 2 with h | h
    · subst h
      have h2 : n ≠ 2 := fun hn => h22 (by simp [hn])
      omega
    · omega
  obtain ⟨c, hcpos, hcall⟩ := prim_ball_count_aux (n + 1) (by omega)
  have hNpos : (0 : ℝ) < (NN d n : ℝ) := by
    have h6 := six_le_NN d n hd hdn
    exact_mod_cast (by omega : 0 < NN d n)
  have hcne : c ≠ 0 := ne_of_gt hcpos
  set Tst : ℝ := max (4 * Real.sqrt (((n + 1 : ℕ)) : ℝ))
    (2 * (4 / c) ^ (1 / ((n : ℝ) + 1))) with hTst
  have hTst2 : 4 * Real.sqrt (((n + 1 : ℕ)) : ℝ) ≤ Tst := le_max_left _ _
  have hTst3 : 2 * (4 / c) ^ (1 / ((n : ℝ) + 1)) ≤ Tst := le_max_right _ _
  have hsqrtn : (0 : ℝ) < Real.sqrt (((n + 1 : ℕ)) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hTstpos : 0 < Tst := lt_of_lt_of_le (by linarith [hsqrtn]) hTst2
  have hden : (0 : ℝ) < (n : ℝ) + 1 - d := by
    have h : (d : ℝ) ≤ n := by exact_mod_cast hdn
    linarith
  have hcast : (((n + 1 - d : ℕ)) : ℝ) = (n : ℝ) + 1 - d := by
    rw [Nat.cast_sub (by omega : d ≤ n + 1)]
    push_cast
    ring
  have hKpos : 0 < 2 * (NN d n : ℝ) * 2 ^ (2 * (n + 1 - d)) / c ^ 2 := by positivity
  refine ⟨2 * (NN d n : ℝ) * 2 ^ (2 * (n + 1 - d)) / c ^ 2, max 1 (Tst ^ (n + 1 - d)),
    hKpos, ?_⟩
  intro B hB
  have hB1 : 1 ≤ B := le_trans (le_max_left _ _) hB
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le one_pos hB1
  set T : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hT
  have hTge : Tst ≤ T := by
    have h1 : Tst ^ (n + 1 - d) ≤ B := le_trans (le_max_right _ _) hB
    have hstep : Tst = (Tst ^ (n + 1 - d)) ^ (1 / ((n : ℝ) + 1 - d)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hcast, mul_one_div,
        div_self (ne_of_gt hden), Real.rpow_one]
    rw [hstep, hT]
    exact Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have hX2 : 2 * Real.sqrt (((n + 1 : ℕ)) : ℝ) ≤ T / 2 := by linarith [hTge, hTst2]
  have hTu : (4 / c) ^ (1 / ((n : ℝ) + 1)) ≤ T / 2 := by linarith [hTge, hTst3]
  have hbase : 0 ≤ 4 / c := by positivity
  have hpow4 : ((4 / c) ^ (1 / ((n : ℝ) + 1))) ^ (n + 1) = 4 / c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase, Nat.cast_add, Nat.cast_one, one_div,
      inv_mul_cancel₀ (by positivity : ((n : ℝ) + 1) ≠ 0), Real.rpow_one]
  have ha4 : 4 ≤ c * (T / 2) ^ (n + 1) := by
    have hle : ((4 / c) ^ (1 / ((n : ℝ) + 1))) ^ (n + 1) ≤ (T / 2) ^ (n + 1) :=
      pow_le_pow_left₀ (by positivity) hTu (n + 1)
    rw [hpow4] at hle
    calc 4 = c * (4 / c) := by field_simp
      _ ≤ c * (T / 2) ^ (n + 1) := mul_le_mul_of_nonneg_left hle (le_of_lt hcpos)
  obtain ⟨S, hS, hSc⟩ := hcall (T / 2) hX2
  set P : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
    (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ -p.2) with hPdef
  have hS2 : 2 ≤ S.card := by
    have h4 : (2 : ℝ) ≤ (S.card : ℝ) := by linarith [ha4, hSc]
    exact_mod_cast h4
  have hPcard : (1 / 2) * (c * (T / 2) ^ (n + 1)) ^ 2 ≤ (P.card : ℝ) := by
    have hcp := card_good_pairs S
    have hcast2 : ((S.card * (S.card - 2) : ℕ) : ℝ) = (S.card : ℝ) * ((S.card : ℝ) - 2) := by
      rw [Nat.cast_mul, Nat.cast_sub hS2]
      ring
    have h3 : (1 / 2) * (c * (T / 2) ^ (n + 1)) ^ 2 ≤ (S.card : ℝ) * ((S.card : ℝ) - 2) := by
      nlinarith [hSc, ha4]
    have h4 : (S.card : ℝ) * ((S.card : ℝ) - 2) ≤ (P.card : ℝ) := by
      rw [← hcast2]
      exact_mod_cast hcp
    linarith
  have hMpos : 0 < Real.sqrt (NN d n) * (T / 2) ^ d :=
    mul_pos (Real.sqrt_pos.mpr hNpos) (pow_pos (by linarith) d)
  have hMsq' : (Real.sqrt (NN d n) * (T / 2) ^ d) ^ 2
      = (NN d n : ℝ) * ((T / 2) ^ d) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hNpos)]
  have hdet : ∀ p ∈ P, detL (Gam d n p.1 p.2) ≤ (Real.sqrt (NN d n) * (T / 2) ^ d) ^ 2 := by
    intro p hp
    rw [hPdef] at hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpS, hne1, hne2⟩ := hp
    obtain ⟨hxS, hyS⟩ := Finset.mem_product.mp hpS
    obtain ⟨hx, hxe⟩ := hS p.1 hxS
    obtain ⟨hy, hye⟩ := hS p.2 hyS
    have hgle := detL_Gam_le d n hd p.1 p.2 hx hy hne1 hne2
    have hn1 := eNorm_veronese_le d n p.1
    have hn2 := eNorm_veronese_le d n p.2
    have he1 : (eNorm p.1) ^ d ≤ (T / 2) ^ d :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hxe d
    have he2 : (eNorm p.2) ^ d ≤ (T / 2) ^ d :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hye d
    have hb1 : eNorm (veronese d n p.1) ≤ Real.sqrt (NN d n) * (T / 2) ^ d :=
      le_trans hn1 (mul_le_mul_of_nonneg_left he1 (Real.sqrt_nonneg _))
    have hb2 : eNorm (veronese d n p.2) ≤ Real.sqrt (NN d n) * (T / 2) ^ d :=
      le_trans hn2 (mul_le_mul_of_nonneg_left he2 (Real.sqrt_nonneg _))
    calc detL (Gam d n p.1 p.2)
        ≤ eNorm (veronese d n p.1) * eNorm (veronese d n p.2) := hgle
      _ ≤ (Real.sqrt (NN d n) * (T / 2) ^ d) * (Real.sqrt (NN d n) * (T / 2) ^ d) :=
          mul_le_mul hb1 hb2 (Real.sqrt_nonneg _) (le_of_lt hMpos)
      _ = (Real.sqrt (NN d n) * (T / 2) ^ d) ^ 2 := by rw [pow_two]
  have hGp : ∀ p ∈ P,
      1 / (Real.sqrt (NN d n) * (T / 2) ^ d) ^ 2 ≤ 1 / detL (Gam d n p.1 p.2) := by
    intro p hp
    have hpos : 0 < detL (Gam d n p.1 p.2) := lt_of_lt_of_le one_pos (MDEstimates.detL_one_le _)
    exact one_div_le_one_div_of_le hpos (hdet p hp)
  have hfin : (Omega d n B).Finite := (MDBasic.finite_sets d n B B (fun _ => True)).2.2
  have hEE : EE d n B = ∑ p ∈ hfin.toFinset, 1 / detL (Gam d n p.1 p.2) := by
    rw [EE, finsum_mem_eq_finite_toFinset_sum (fun p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) =>
      1 / detL (Gam d n p.1 p.2)) hfin]
  have hPmem : ∀ p ∈ P, p ∈ Omega d n B := by
    intro p hp
    rw [hPdef] at hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpS, hne1, hne2⟩ := hp
    obtain ⟨hxS, hyS⟩ := Finset.mem_product.mp hpS
    obtain ⟨hx, hxe⟩ := hS p.1 hxS
    obtain ⟨hy, hye⟩ := hS p.2 hyS
    have hxe' : eNorm p.1 ≤ T := by linarith
    have hye' : eNorm p.2 ≤ T := by linarith
    rw [hT] at hxe' hye'
    exact ⟨⟨hx, hxe'⟩, ⟨hy, hye'⟩, hne1, hne2⟩
  have hsubset : P ⊆ hfin.toFinset := fun p hp => by
    rw [Set.Finite.mem_toFinset]
    exact hPmem p hp
  have hle : ∑ p ∈ P, 1 / detL (Gam d n p.1 p.2) ≤
      ∑ p ∈ hfin.toFinset, 1 / detL (Gam d n p.1 p.2) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p hp hnp
    rw [one_div_nonneg]
    exact detL_nonneg_gram _
  have hsumP : (P.card : ℝ) * (1 / (Real.sqrt (NN d n) * (T / 2) ^ d) ^ 2) ≤
      ∑ p ∈ P, 1 / detL (Gam d n p.1 p.2) := by
    have h := Finset.sum_le_sum (fun p hp => hGp p hp)
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have hEEge : (1 / 2) * (c * (T / 2) ^ (n + 1)) ^ 2 /
      (Real.sqrt (NN d n) * (T / 2) ^ d) ^ 2 ≤ EE d n B := by
    have h1 : (1 / 2) * (c * (T / 2) ^ (n + 1)) ^ 2 /
          (Real.sqrt (NN d n) * (T / 2) ^ d) ^ 2 ≤
        (P.card : ℝ) * (1 / (Real.sqrt (NN d n) * (T / 2) ^ d) ^ 2) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right hPcard (by positivity)
    linarith [h1, hsumP, hle, hEE]
  set k := n + 1 - d with hk
  have hTk : T ^ k = B := by
    rw [hT, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hcast, one_div,
      inv_mul_cancel₀ (ne_of_gt hden), Real.rpow_one]
  have huk : (T / 2) ^ k = B / 2 ^ k := by rw [div_pow, hTk]
  have hu : (T / 2) ^ (n + 1) = (B / 2 ^ k) * (T / 2) ^ d := by
    have hexp : n + 1 = k + d := by omega
    rw [hexp, pow_add, huk]
  have h2k : (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 := by
    rw [pow_two, ← pow_add]
    congr 1
    omega
  have hmain : (2 * (NN d n : ℝ) * 2 ^ (2 * k) / c ^ 2) *
      ((1 / 2) * (c * (T / 2) ^ (n + 1)) ^ 2 /
        (Real.sqrt (NN d n) * (T / 2) ^ d) ^ 2) = B ^ 2 := by
    rw [hu, hMsq', h2k]
    have h1 : (2 : ℝ) ^ k ≠ 0 := by positivity
    have h2 : ((T / 2) ^ d) ≠ 0 := by positivity
    have h3 : ((NN d n : ℕ) : ℝ) ≠ 0 := ne_of_gt hNpos
    field_simp
    try ring
  calc B ^ 2 = (2 * (NN d n : ℝ) * 2 ^ (2 * (n + 1 - d)) / c ^ 2) *
        ((1 / 2) * (c * (T / 2) ^ (n + 1)) ^ 2 /
          (Real.sqrt (NN d n) * (T / 2) ^ d) ^ 2) := hmain.symm
    _ ≤ (2 * (NN d n : ℝ) * 2 ^ (2 * (n + 1 - d)) / c ^ 2) * EE d n B :=
        mul_le_mul_of_nonneg_left hEEge (le_of_lt hKpos)

end Work.HP.Sig2
