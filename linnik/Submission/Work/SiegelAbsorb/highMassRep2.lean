import Mathlib
import Submission.Work.SiegelAbsorb.windowInterface
import Submission.Work.SiegelAbsorb.windowMassRegion
import Submission.Work.SiegelAbsorb.windowMassFloor2
import Submission.Work.SiegelAbsorb.windowMassFree2
import Submission.Work.LinnikAreas.pairCountHeight_le_famCount
import Submission.Work.LinnikAreas.BGTZ.RestHighBGTZGenC

namespace Work.SiegelAbsorb

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option maxHeartbeats 8000000

/-- The full geometric sum over a finite set, bounded by the infinite one. -/
private lemma geom_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (A : Finset ℕ) :
    ∑ j ∈ A, r^j ≤ (1 - r)⁻¹ := by
  have hs := summable_geometric_of_lt_one h0 h1
  calc ∑ j ∈ A, r^j ≤ ∑' j : ℕ, r^j := Summable.sum_le_tsum A (fun i _ => by positivity) hs
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one h0 h1

/-- The geometric tail over a finite set of integers `> M`. -/
private lemma geom_tail {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (M : ℕ) (Y : Finset ℕ)
    (hY : ∀ j ∈ Y, M < j) :
    ∑ j ∈ Y, r^j ≤ r^(M+1) / (1 - r) := by
  have hsub : Y ⊆ Finset.Ico (M + 1) (Y.sup id + 1) := by
    intro j hj
    refine Finset.mem_Ico.mpr ⟨?_, ?_⟩
    · have := hY j hj; omega
    · exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity))
    (geom_sum_Ico_le_of_lt_one h0 h1)

/-- The dyadic factor identity: the per-fibre constant `4/(4^j·𝓛²)`, the height factor
`(2^{j+1})^{3/2}` and the geometric weight `(2^{-1/2})^j` combine into the product on the right. -/
private lemma dyadicAlg (C c d 𝓛 : ℝ) (j : ℕ) (h𝓛 : 0 < 𝓛) (Y : ℝ) :
    4 / ((4:ℝ)^j * 𝓛^2) * (C * ((2:ℝ)^(j+1))^(3/2:ℝ) * Real.exp c * Y / d)
      = (4 * (2:ℝ)^(3/2:ℝ) * C * Real.exp c / d) * 𝓛^(-2:ℝ) * ((2:ℝ)^(-(1/2):ℝ))^j * Y := by
  have hrpow : (𝓛^2)⁻¹ = 𝓛^(-2:ℝ) := by
    rw [show 𝓛^2 = 𝓛^((2:ℕ):ℝ) by rw [Real.rpow_natCast]]
    rw [← Real.rpow_neg h𝓛.le]
    norm_num
  have e1 : 4 / ((4:ℝ)^j * 𝓛^2) = 4 * 𝓛^(-2:ℝ) * ((4:ℝ)^j)⁻¹ := by
    rw [div_eq_mul_inv, mul_inv_rev, hrpow]; ring
  rw [e1]
  have e2 : (4 * 𝓛^(-2:ℝ) * ((4:ℝ)^j)⁻¹) * (C * ((2:ℝ)^(j+1))^(3/2:ℝ) * Real.exp c * Y / d)
      = (4 * C * Real.exp c / d * 𝓛^(-2:ℝ)) * ((((2:ℝ)^(j+1))^(3/2:ℝ) * ((4:ℝ)^j)⁻¹) * Y) := by
    ring
  rw [e2, Work.LinnikAreas.BGTZ.dyadic_key_freeC j]
  ring

/-- The per-fibre (`jjC = j`) part of the crude half of the window bound: every member of `F` has
height at most `2^{j+1}` and `λ`-value above the floor `(7/100)𝓛`, so the coefficient-`9/2` count
gives the bound with the two factors `𝓛^{-2}` and `e^{-(7/250)𝓛}`. -/
private lemma fiberHigh {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C₃ : ℝ} (hC₃ : 0 < C₃)
    (hcnt₂ : ∀ (H : ℝ), 1 ≤ H → ∀ t : ℝ, 0 < t → t ≤ Real.log (q : ℝ) →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₃ * Real.exp ((9 / 2) * t) * H ^ (3 / 2 : ℝ))
    {j : ℕ} (F : Finset (DirichletCharacter ℂ q × ℂ))
    (hzmF : ∀ z ∈ F, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hhighF : ∀ z ∈ F, 1 < |z.2.im|)
    (hexcF : ∀ z ∈ F, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (hjj : ∀ z ∈ F, Work.LinnikAreas.BGTZ.jjC z = j)
    (himF : ∀ z ∈ F, |z.2.im| * Real.log (q : ℝ) ≤ ((2:ℝ)^(j+1)) * Real.log (q : ℝ))
    (hflrF : ∀ z ∈ F, (7 / 100) * Real.log (q : ℝ) ≤ Work.LinnikContract.lamOf q z.2) :
    (∑ z ∈ F, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log (q : ℝ) : ℂ))‖)
      ≤ (4 * (2:ℝ)^(3/2:ℝ) * C₃ * Real.exp (9/2) / (1 - Real.exp (-(2/5))))
          * (Real.log (q : ℝ))^(-2:ℝ) * ((2:ℝ)^(-(1/2):ℝ))^j
          * Real.exp (-(7/250) * Real.log (q : ℝ)) := by
  classical
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hlamLF : ∀ z ∈ F, Work.LinnikContract.lamOf q z.2 ≤ Real.log (q:ℝ) := by
    intro z hz
    have h1 : 0 < z.2.re := Work.LinnikAreas.zeroMult_re_pos z.1 (hzmF z hz)
    rw [Work.LinnikContract.lamOf]
    nlinarith [hlog]
  have hmass := Work.SiegelAbsorb.windowMassRegion (q := q) hq χ₁ β₁
    (C := C₃) (H := (2:ℝ)^(j+1)) (a₀ := 49/10) (c := 9/2)
    (Λ := (7/100) * Real.log (q:ℝ)) (L := Real.log (q:ℝ))
    hC₃ (by positivity) (by norm_num) (by norm_num) (by norm_num) (by positivity)
    (fun t ht hL => hcnt₂ ((2:ℝ)^(j+1)) (by exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) t ht hL)
    F hzmF hexcF himF hflrF hlamLF
  rw [show (9/2:ℝ) - 49/10 = -(2/5) by norm_num] at hmass
  have hstep1 : (∑ z ∈ F, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖)
      ≤ ∑ z ∈ F, 4 / ((4:ℝ)^(Work.LinnikAreas.BGTZ.jjC z) * (Real.log (q:ℝ))^2)
          * ((Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
            * Real.exp (-(49/10) * Work.LinnikContract.lamOf q z.2)) :=
    Finset.sum_le_sum (fun z hz => Work.LinnikAreas.BGTZ.kernel_leC hq z (hzmF z hz) (hhighF z hz))
  have hstep2 : (∑ z ∈ F, 4 / ((4:ℝ)^(Work.LinnikAreas.BGTZ.jjC z) * (Real.log (q:ℝ))^2)
          * ((Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
            * Real.exp (-(49/10) * Work.LinnikContract.lamOf q z.2)))
      = 4 / ((4:ℝ)^j * (Real.log (q:ℝ))^2)
          * (∑ z ∈ F, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
            * Real.exp (-(49/10) * Work.LinnikContract.lamOf q z.2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [hjj z hz]
  have hmid : (∑ z ∈ F, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖)
      ≤ 4 / ((4:ℝ)^j * (Real.log (q:ℝ))^2)
          * (C₃ * ((2:ℝ)^(j+1))^(3/2:ℝ) * Real.exp (9/2)
              * Real.exp (-(2/5) * ((7/100) * Real.log (q:ℝ))) / (1 - Real.exp (-(2/5)))) :=
    (le_trans hstep1 hstep2.le).trans (mul_le_mul_of_nonneg_left hmass (by positivity))
  refine hmid.trans ?_
  rw [dyadicAlg C₃ (9/2) (1 - Real.exp (-(2/5))) (Real.log (q:ℝ)) j hlog
        (Real.exp (-(2/5) * ((7/100) * Real.log (q:ℝ))))]
  rw [show -(2/5) * ((7/100) * Real.log (q:ℝ)) = -(7/250) * Real.log (q:ℝ) by ring]

/-- **The `λ > (7/100)𝓛` half of the window bound.**  Only the crude coefficient-`9/2` log-free
count is used, on all of `λ ∈ ((7/100)𝓛, 𝓛]`; the positive floor `(7/100)𝓛` supplies the saving
`e^{-(2/5)·(7/100)𝓛} = e^{-(7/250)𝓛}`.  No repulsion, height separation or `λ₁`-decay is needed. -/
lemma highMassRep2High {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C₃ : ℝ} (hC₃ : 0 < C₃)
    (hcnt₂ : ∀ (H : ℝ), 1 ≤ H → ∀ t : ℝ, 0 < t → t ≤ Real.log (q : ℝ) →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₃ * Real.exp ((9 / 2) * t) * H ^ (3 / 2 : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hhigh : ∀ z ∈ S, 1 < |z.2.im|)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (hfloor : ∀ z ∈ S, (7 / 100) * Real.log (q : ℝ) < Work.LinnikContract.lamOf q z.2) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log (q : ℝ) : ℂ))‖)
      ≤ Work.SiegelAbsorb.K₃high C₃ * Real.exp (-(7 / 250) * Real.log (q : ℝ))
          * (Real.log (q : ℝ)) ^ (-2 : ℝ) := by
  classical
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  set Ks : ℝ := 4 * (2:ℝ)^(3/2:ℝ) * C₃ * Real.exp (9/2) / (1 - Real.exp (-(2/5))) with hKsdef
  have hKsnn : 0 ≤ Ks := by
    rw [hKsdef]
    have h : Real.exp (-(2/5)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    positivity
  have hden : 0 < 1 - (2:ℝ)^(-(1/2):ℝ) := by
    have h : (2:ℝ)^(-(1/2):ℝ) < 1 := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num))
    linarith
  -- dyadic layer index
  have him_lt_of : ∀ (j : ℕ) (z : DirichletCharacter ℂ q × ℂ),
      Work.LinnikAreas.BGTZ.jjC z = j → |z.2.im| < (2:ℝ)^(j+1) := by
    intro j z hjj
    have h1 : Nat.floor |z.2.im| < 2 ^ (Nat.log 2 (Nat.floor |z.2.im|) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
    rw [show Nat.log 2 (Nat.floor |z.2.im|) = j from hjj] at h1
    have h2 : (Nat.floor |z.2.im| : ℝ) + 1 ≤ (2:ℝ)^(j+1) := by exact_mod_cast h1
    have h3 : |z.2.im| < (Nat.floor |z.2.im| : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  -- per-fibre bound
  have hper : ∀ j ∈ S.image Work.LinnikAreas.BGTZ.jjC,
      (∑ z ∈ S.filter (fun z => Work.LinnikAreas.BGTZ.jjC z = j),
          (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
            * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖)
        ≤ Ks * (Real.log (q:ℝ))^(-2:ℝ) * ((2:ℝ)^(-(1/2):ℝ))^j
            * Real.exp (-(7/250) * Real.log (q:ℝ)) := by
    intro j hj
    have h1 : (∑ z ∈ S.filter (fun z => Work.LinnikAreas.BGTZ.jjC z = j),
          (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
            * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖)
        ≤ (4 * (2:ℝ)^(3/2:ℝ) * C₃ * Real.exp (9/2) / (1 - Real.exp (-(2/5))))
            * (Real.log (q:ℝ))^(-2:ℝ) * ((2:ℝ)^(-(1/2):ℝ))^j
            * Real.exp (-(7/250) * Real.log (q:ℝ)) :=
      fiberHigh hq χ₁ β₁ hC₃ hcnt₂ (S.filter (fun z => Work.LinnikAreas.BGTZ.jjC z = j))
        (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
        (fun z hz => hhigh z (Finset.mem_filter.mp hz).1)
        (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
        (fun z hz => (Finset.mem_filter.mp hz).2)
        (fun z hz => mul_le_mul_of_nonneg_right
            ((him_lt_of j z (Finset.mem_filter.mp hz).2).le) hlog.le)
        (fun z hz => le_of_lt (hfloor z (Finset.mem_filter.mp hz).1))
    rw [hKsdef]
    exact h1
  have hGeq : (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖)
      = ∑ j ∈ S.image Work.LinnikAreas.BGTZ.jjC,
          ∑ z ∈ S.filter (fun z => Work.LinnikAreas.BGTZ.jjC z = j),
            (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
              * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖ := by
    exact (Finset.sum_fiberwise_of_maps_to
      (fun z hz => Finset.mem_image_of_mem Work.LinnikAreas.BGTZ.jjC hz)
      (fun z => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖)).symm
  rw [hGeq]
  have hE : 0 ≤ Real.exp (-(7/250) * Real.log (q:ℝ)) := (Real.exp_pos _).le
  have hL2 : 0 ≤ (Real.log (q:ℝ))^(-2:ℝ) := Real.rpow_nonneg hlog.le _
  have hinvnn : 0 ≤ (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹ := inv_nonneg.mpr hden.le
  have hKc : Ks * (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹ ≤ K₃high C₃ := by
    unfold K₃high
    refine le_trans ?_ (le_max_right _ _)
    have hX : (16 : ℝ) * (2:ℝ)^(3/2:ℝ) * C₃ * Real.exp (9/2) / (1 - Real.exp (-(2/5)))
          * (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹
        = 4 * (Ks * (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹) := by
      rw [hKsdef]; ring
    rw [hX]
    have hZnn : 0 ≤ Ks * (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹ := mul_nonneg hKsnn hinvnn
    linarith [hZnn]
  calc ∑ j ∈ S.image Work.LinnikAreas.BGTZ.jjC,
        ∑ z ∈ S.filter (fun z => Work.LinnikAreas.BGTZ.jjC z = j),
          (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
            * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖
      ≤ ∑ j ∈ S.image Work.LinnikAreas.BGTZ.jjC, Ks * (Real.log (q:ℝ))^(-2:ℝ)
          * ((2:ℝ)^(-(1/2):ℝ))^j * Real.exp (-(7/250) * Real.log (q:ℝ)) :=
        Finset.sum_le_sum hper
    _ = Ks * (Real.log (q:ℝ))^(-2:ℝ) * Real.exp (-(7/250) * Real.log (q:ℝ))
          * (∑ j ∈ S.image Work.LinnikAreas.BGTZ.jjC, ((2:ℝ)^(-(1/2):ℝ))^j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        ring
    _ ≤ Ks * (Real.log (q:ℝ))^(-2:ℝ) * Real.exp (-(7/250) * Real.log (q:ℝ))
          * (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹ := by
        refine mul_le_mul_of_nonneg_left (geom_le ?_ ?_ _) ?_
        · positivity
        · linarith [hden]
        · positivity
    _ = Ks * (Real.log (q:ℝ))^(-2:ℝ) * (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹
          * Real.exp (-(7/250) * Real.log (q:ℝ)) := by ring
    _ ≤ K₃high C₃ * Real.exp (-(7/250) * Real.log (q:ℝ)) * (Real.log (q:ℝ))^(-2:ℝ) := by
        calc Ks * (Real.log (q:ℝ))^(-2:ℝ) * (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹
              * Real.exp (-(7/250) * Real.log (q:ℝ))
            = (Ks * (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹) * ((Real.log (q:ℝ))^(-2:ℝ)
                * Real.exp (-(7/250) * Real.log (q:ℝ))) := by ring
          _ ≤ K₃high C₃ * ((Real.log (q:ℝ))^(-2:ℝ) * Real.exp (-(7/250) * Real.log (q:ℝ))) :=
              mul_le_mul_of_nonneg_right hKc (mul_nonneg hL2 hE)
          _ = K₃high C₃ * Real.exp (-(7/250) * Real.log (q:ℝ))
                * (Real.log (q:ℝ))^(-2:ℝ) := by ring

/-- The per-fibre (`jjC = j`) part of the near-line half: every member of `F` has height at most
`2^{j+1}` and `λ`-value at most `(7/100)𝓛`, so the coefficient-`5/2` count (valid only up to
`(7/100)𝓛`) suffices; the floor `min λ > 0` is dropped. -/
private lemma fiberLowFree {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C₂ : ℝ} (hC₂ : 0 < C₂)
    (hcnt₁ : ∀ (H : ℝ), 1 ≤ H → ∀ t : ℝ, 0 < t → t ≤ (7 / 100) * Real.log (q : ℝ) →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₂ * Real.exp ((5 / 2) * t) * H ^ (3 / 2 : ℝ))
    {j : ℕ} (F : Finset (DirichletCharacter ℂ q × ℂ))
    (hzmF : ∀ z ∈ F, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hhighF : ∀ z ∈ F, 1 < |z.2.im|)
    (hexcF : ∀ z ∈ F, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (hjj : ∀ z ∈ F, Work.LinnikAreas.BGTZ.jjC z = j)
    (himF : ∀ z ∈ F, |z.2.im| * Real.log (q : ℝ) ≤ ((2:ℝ)^(j+1)) * Real.log (q : ℝ))
    (hlamL : ∀ z ∈ F, Work.LinnikContract.lamOf q z.2 ≤ (7 / 100) * Real.log (q : ℝ)) :
    (∑ z ∈ F, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log (q : ℝ) : ℂ))‖)
      ≤ (4 * (2:ℝ)^(3/2:ℝ) * C₂ * Real.exp (5/2) / (1 - Real.exp (-(12/5))))
          * (Real.log (q : ℝ))^(-2:ℝ) * ((2:ℝ)^(-(1/2):ℝ))^j := by
  classical
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  rcases F.eq_empty_or_nonempty with hF | hne
  · subst hF
    simp only [Finset.sum_empty]
    have hd : 0 < 1 - Real.exp (-(12/5)) := by
      have h : Real.exp (-(12/5)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      linarith
    positivity
  · have hpos : ∀ z ∈ F, 0 < Work.LinnikContract.lamOf q z.2 := by
      intro z hz
      have h1 : z.2.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one z.1 (hzmF z hz)
      rw [Work.LinnikContract.lamOf]
      exact mul_pos (by linarith) hlog
    set Λ : ℝ := F.inf' hne (fun z => Work.LinnikContract.lamOf q z.2) with hΛdef
    have hΛpos : 0 < Λ := by
      obtain ⟨z, hz, heq⟩ := Finset.exists_mem_eq_inf' hne (fun z => Work.LinnikContract.lamOf q z.2)
      rw [hΛdef, heq]; exact hpos z hz
    have hΛle : ∀ z ∈ F, Λ ≤ Work.LinnikContract.lamOf q z.2 := fun z hz =>
      Finset.inf'_le (s := F) (fun z => Work.LinnikContract.lamOf q z.2) hz
    have hmass := Work.SiegelAbsorb.windowMassRegion (q := q) hq χ₁ β₁
      (C := C₂) (H := (2:ℝ)^(j+1)) (a₀ := 49/10) (c := 5/2)
      (Λ := Λ) (L := (7/100) * Real.log (q:ℝ))
      hC₂ (by positivity) (by norm_num) (by norm_num) (by norm_num) hΛpos
      (fun t ht hL => hcnt₁ ((2:ℝ)^(j+1)) (by exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) t ht hL)
      F hzmF hexcF himF hΛle hlamL
    rw [show (5/2:ℝ) - 49/10 = -(12/5) by norm_num] at hmass
    have hden' : 0 < 1 - Real.exp (-(12/5)) := by
      have h : Real.exp (-(12/5)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      linarith
    have hdrop : Real.exp (-(12/5) * Λ) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hΛpos]
    have hmass' : (∑ z ∈ F, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * Real.exp (-(49/10) * Work.LinnikContract.lamOf q z.2))
        ≤ C₂ * ((2:ℝ)^(j+1)) ^ (3/2:ℝ) * Real.exp (5/2) * 1 / (1 - Real.exp (-(12/5))) := by
      refine hmass.trans ?_
      refine div_le_div_of_nonneg_right ?_ hden'.le
      exact mul_le_mul_of_nonneg_left hdrop (by positivity)
    have hstep1 : (∑ z ∈ F, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
          * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖)
        ≤ ∑ z ∈ F, 4 / ((4:ℝ)^(Work.LinnikAreas.BGTZ.jjC z) * (Real.log (q:ℝ))^2)
            * ((Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
              * Real.exp (-(49/10) * Work.LinnikContract.lamOf q z.2)) :=
      Finset.sum_le_sum (fun z hz => Work.LinnikAreas.BGTZ.kernel_leC hq z (hzmF z hz) (hhighF z hz))
    have hstep2 : (∑ z ∈ F, 4 / ((4:ℝ)^(Work.LinnikAreas.BGTZ.jjC z) * (Real.log (q:ℝ))^2)
            * ((Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
              * Real.exp (-(49/10) * Work.LinnikContract.lamOf q z.2)))
        = 4 / ((4:ℝ)^j * (Real.log (q:ℝ))^2)
            * (∑ z ∈ F, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
              * Real.exp (-(49/10) * Work.LinnikContract.lamOf q z.2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z hz => ?_)
      rw [hjj z hz]
    have hmid : (∑ z ∈ F, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
          * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖)
        ≤ 4 / ((4:ℝ)^j * (Real.log (q:ℝ))^2)
            * (C₂ * ((2:ℝ)^(j+1))^(3/2:ℝ) * Real.exp (5/2) * 1 / (1 - Real.exp (-(12/5)))) :=
      (le_trans hstep1 hstep2.le).trans (mul_le_mul_of_nonneg_left hmass' (by positivity))
    refine hmid.trans (le_of_eq ?_)
    rw [dyadicAlg C₂ (5/2) (1 - Real.exp (-(12/5))) (Real.log (q:ℝ)) j hlog 1]
    ring

/-- **The `λ ≤ (7/100)𝓛` half of the window bound.**  Only the near-line coefficient-`5/2`
log-free count is used (valid up to `t = (7/100)𝓛`); the low dyadic fibres obtain a positive
repulsion floor `Lf j > 0` whose saving `e^{-(12/5)Lf j}` is dominated by
`e^{12C₀/5}·λ₁·2^{5/4}·2^{-j/4}`, while the far fibres (`j > J`, `2^J ≈ q²`) are controlled by the
geometric tail `≤ λ₁`. -/
lemma highMassRep2Low {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ)
    {C₂ C₀ : ℝ} (hC₂ : 0 < C₂) (hC₀ : 0 < C₀)
    (hcnt₁ : ∀ (H : ℝ), 1 ≤ H → ∀ t : ℝ, 0 < t → t ≤ (7 / 100) * Real.log (q : ℝ) →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₂ * Real.exp ((5 / 2) * t) * H ^ (3 / 2 : ℝ))
    (hrepq : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.zeroMult χ ρ ≠ 0 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ Work.LinnikContract.lamOf q ρ →
      (Real.log (1 / Work.LinnikContract.lamOf q (β₁ : ℂ))
          - Real.log (C₀ * ((11 / 5 : ℝ) + (11 / 10 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))))
        / ((11 / 5 : ℝ) + (11 / 10 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))
        ≤ Work.LinnikContract.lamOf q ρ)
    (hlam1pos : 0 < Work.LinnikContract.lamOf q (β₁ : ℂ))
    (hsmall : Work.LinnikContract.lamOf q (β₁ : ℂ) < 1 / (6 * C₀))
    (hlam1lt : Work.LinnikContract.lamOf q (β₁ : ℂ) < 1)
    (hαhalf : Real.log (1 / Work.LinnikContract.lamOf q (β₁ : ℂ)) ≤ Real.log (q : ℝ) / 2)
    (h𝓛big : 20 ≤ Real.log (q : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0)
    (hhigh : ∀ z ∈ S, 1 < |z.2.im|)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ)))
    (hsep : ∀ z ∈ S, Work.LinnikContract.lamOf q z.2 < Work.LinnikContract.lamOf q (β₁ : ℂ) →
      4 * (q : ℝ) ^ 2 ≤ |z.2.im|)
    (hlamL : ∀ z ∈ S, Work.LinnikContract.lamOf q z.2 ≤ (7 / 100) * Real.log (q : ℝ)) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log (q : ℝ) : ℂ))‖)
      ≤ Work.SiegelAbsorb.K₂low C₂ C₀ * Work.LinnikContract.lamOf q (β₁ : ℂ)
          * (Real.log (q : ℝ)) ^ (-2 : ℝ) := by
  classical
  have hlog : 0 < Real.log (q : ℝ) := lt_of_lt_of_le (by norm_num) h𝓛big
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (le_of_lt hq)
  set Ks : ℝ := 4 * (2:ℝ)^(3/2:ℝ) * C₂ * Real.exp (5/2) / (1 - Real.exp (-(12/5))) with hKsdef
  have hKsnn : 0 ≤ Ks := by
    rw [hKsdef]
    have h : Real.exp (-(12/5)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    positivity
  set lam1 : ℝ := Work.LinnikContract.lamOf q (β₁ : ℂ) with hlam1def
  have hlam1pos' : 0 < lam1 := hlam1pos
  have hlam1lt1 : lam1 < 1 := hlam1lt
  set α : ℝ := Real.log (1 / lam1) with hαdef
  have hαpos : 0 < α := by
    rw [hαdef]
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hlam1pos']
    simpa using hlam1lt1
  have hexp_neg : Real.exp (-α) = lam1 := by
    rw [hαdef, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
  have hαle : α ≤ Real.log (q : ℝ) / 2 := by rw [hαdef, hlam1def]; exact hαhalf
  set J : ℕ := Nat.ceil (2 * Real.log (q : ℝ) / Real.log 2) with hJdef
  have hJlt : (J : ℝ) < 2 * Real.log (q : ℝ) / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hJge : 2 * Real.log (q : ℝ) / Real.log 2 ≤ (J : ℝ) := Nat.le_ceil _
  have h2J : (2 : ℝ) ^ (J + 1) ≤ 4 * (q : ℝ) ^ 2 := by
    have h7 : (J : ℝ) + 1 < 2 * Real.log (q : ℝ) / Real.log 2 + 2 := by linarith [hJlt]
    have h8 : (2 : ℝ) ^ (J + 1) ≤ (2 : ℝ) ^ (2 * Real.log (q : ℝ) / Real.log 2 + 2) := by
      rw [← Real.rpow_natCast (2 : ℝ) (J + 1)]
      push_cast
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h7.le
    calc (2 : ℝ) ^ (J + 1) ≤ (2 : ℝ) ^ (2 * Real.log (q : ℝ) / Real.log 2 + 2) := h8
      _ = (2 : ℝ) ^ (2 * Real.log (q : ℝ) / Real.log 2) * (2 : ℝ) ^ (2 : ℝ) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = (q : ℝ) ^ 2 * 4 := by
          congr 1
          · rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
            have h10 : Real.log 2 * (2 * Real.log (q : ℝ) / Real.log 2)
                = 2 * Real.log (q : ℝ) := by field_simp
            have h9 : Real.log ((q : ℝ) ^ 2) = 2 * Real.log (q : ℝ) := by
              rw [Real.log_pow]; ring
            rw [h10, ← h9]
            exact Real.exp_log (by positivity)
          · rw [Real.rpow_two]; norm_num
      _ = 4 * (q : ℝ) ^ 2 := by ring
  set U : ℕ → ℝ := fun j =>
    (11 / 5 : ℝ) + (11 / 10 : ℝ) * (Real.log (5 + (2 : ℝ) ^ (j + 1)) / Real.log (q : ℝ))
    with hUdef
  set Lf : ℕ → ℝ := fun j => (α - Real.log (C₀ * U j)) / U j with hLdef
  have hξnn : ∀ j, 0 ≤ Real.log (5 + (2 : ℝ) ^ (j + 1)) / Real.log (q : ℝ) := by
    intro j
    refine div_nonneg ?_ hlog.le
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by positivity
    linarith
  have hUpos : ∀ j, 0 < U j := by
    intro j; rw [hUdef]; have := hξnn j; nlinarith
  have hUge : ∀ j, (4 / 3 + 1 / 100 : ℝ) ≤ U j := by
    intro j; rw [hUdef]; have := hξnn j; nlinarith
  have hU6 : ∀ j, j ≤ J → U j ≤ 6 := by
    intro j hj
    have h2j : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (J + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hp : 5 + (2 : ℝ) ^ (j + 1) ≤ 20 * (q : ℝ) ^ 2 := by
      have h2 : 5 + 4 * (q : ℝ) ^ 2 ≤ 20 * (q : ℝ) ^ 2 := by nlinarith [hq1]
      linarith
    have hlogp : Real.log (5 + (2 : ℝ) ^ (j + 1)) ≤ Real.log 20 + 2 * Real.log (q : ℝ) := by
      calc Real.log (5 + (2 : ℝ) ^ (j + 1)) ≤ Real.log (20 * (q : ℝ) ^ 2) :=
            Real.log_le_log (by positivity) hp
        _ = Real.log 20 + 2 * Real.log (q : ℝ) := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
            ring
    have hξ6 : Real.log (5 + (2 : ℝ) ^ (j + 1)) / Real.log (q : ℝ) ≤ 2.95 := by
      rw [div_le_iff₀ hlog]
      have h1 : Real.log 20 ≤ 19 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20); linarith
      nlinarith [hlogp, h1, h𝓛big]
    rw [hUdef]
    nlinarith [hξ6]
  have hCU_J : ∀ j, j ≤ J → C₀ * U j < Real.exp α := by
    intro j hj
    have h1 : C₀ * U j ≤ 6 * C₀ := by nlinarith [hU6 j hj, hC₀]
    have h3 : Real.exp α = 1 / lam1 := by rw [hαdef, Real.exp_log (by positivity)]
    have h2 : 6 * C₀ < Real.exp α := by
      rw [h3, lt_div_iff₀ hlam1pos']
      have hs : lam1 < 1 / (6 * C₀) := by rw [hlam1def]; exact hsmall
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 6 * C₀)] at hs
      linarith [hs]
    linarith
  have hLpos : ∀ j, j ≤ J → 0 < Lf j := by
    intro j hj
    rw [hLdef]
    refine div_pos ?_ (hUpos j)
    rw [sub_pos]
    have h5 : Real.log (C₀ * U j) < Real.log (Real.exp α) :=
      Real.log_lt_log (mul_pos hC₀ (hUpos j)) (hCU_J j hj)
    rwa [Real.log_exp] at h5
  have hfloorpos_J : ∀ j, j ≤ J → C₀ * U j ≤ 1 / lam1 := by
    intro j hj
    have h3 : Real.exp α = 1 / lam1 := by rw [hαdef, Real.exp_log (by positivity)]
    rw [← h3]; linarith [hCU_J j hj]
  have him_lt_of : ∀ (j : ℕ) (z : DirichletCharacter ℂ q × ℂ),
      Work.LinnikAreas.BGTZ.jjC z = j → |z.2.im| < (2:ℝ)^(j+1) := by
    intro j z hjj
    have h1 : Nat.floor |z.2.im| < 2 ^ (Nat.log 2 (Nat.floor |z.2.im|) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
    rw [show Nat.log 2 (Nat.floor |z.2.im|) = j from hjj] at h1
    have h2 : (Nat.floor |z.2.im| : ℝ) + 1 ≤ (2:ℝ)^(j+1) := by exact_mod_cast h1
    have h3 : |z.2.im| < (Nat.floor |z.2.im| : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  set Gs : ℕ → ℝ := fun j => ∑ z ∈ S.filter (fun z => Work.LinnikAreas.BGTZ.jjC z = j),
      (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖ with hGsdef
  -- the low fibres `j ≤ J`, with the repulsion floor
  have hfibFloor : ∀ j, j ∈ S.image Work.LinnikAreas.BGTZ.jjC → j ≤ J →
      Gs j ≤ Ks * Real.exp (12 * C₀ / 5) * (2:ℝ)^(5/4:ℝ) * (Real.log (q:ℝ))^(-2:ℝ)
              * lam1 * ((2:ℝ)^(-(1/4):ℝ))^j := by
    intro j hjT hjJ
    show (∑ z ∈ S.filter (fun z => Work.LinnikAreas.BGTZ.jjC z = j),
        (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
          * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖) ≤ _
    set F := S.filter (fun z => Work.LinnikAreas.BGTZ.jjC z = j) with hFdef
    have hzmF : ∀ z ∈ F, Work.LinnikContract.zeroMult z.1 z.2 ≠ 0 :=
      fun z hz => hzm z (Finset.mem_filter.mp hz).1
    have hhighF : ∀ z ∈ F, 1 < |z.2.im| := fun z hz => hhigh z (Finset.mem_filter.mp hz).1
    have hexcF : ∀ z ∈ F, ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ)) :=
      fun z hz => hexc z (Finset.mem_filter.mp hz).1
    have himle : ∀ z ∈ F, |z.2.im| ≤ (2:ℝ)^(j+1) :=
      fun z hz => (him_lt_of j z (Finset.mem_filter.mp hz).2).le
    have himF : ∀ z ∈ F, |z.2.im| * Real.log (q:ℝ) ≤ ((2:ℝ)^(j+1)) * Real.log (q:ℝ) :=
      fun z hz => mul_le_mul_of_nonneg_right (himle z hz) hlog.le
    have hlamLF : ∀ z ∈ F, Work.LinnikContract.lamOf q z.2 ≤ (7/100)*Real.log (q:ℝ) :=
      fun z hz => hlamL z (Finset.mem_filter.mp hz).1
    have hfloorF : ∀ z ∈ F, Lf j ≤ Work.LinnikContract.lamOf q z.2 := by
      intro z hz
      have hge : Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ Work.LinnikContract.lamOf q z.2 := by
        by_contra hcon
        push Not at hcon
        have hs := hsep z (Finset.mem_filter.mp hz).1 hcon
        have h2j : (2:ℝ)^(j+1) ≤ (2:ℝ)^(J+1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have hzlt : |z.2.im| < (2:ℝ)^(J+1) :=
          lt_of_lt_of_le (him_lt_of j z (Finset.mem_filter.mp hz).2) h2j
        linarith [h2J]
      have hrep_apply := Work.LinnikAreas.BGTZ.repulsionFloorHiC (u := 11/5) (v := 11/10)
        (H := (2:ℝ)^(j+1)) χ₁ β₁ (C₀ := C₀) hC₀ (by norm_num) (by norm_num)
        (by exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
        (by have := hξnn j; nlinarith)
        (hrep := hrepq)
        (hfloor0 := by have h := hfloorpos_J j hjJ; rw [hUdef] at h; exact h)
        hq (hzmF z hz) (himle z hz) (hexcF z hz) (hge)
      rw [hLdef, hUdef]
      exact hrep_apply
    have hmass := Work.SiegelAbsorb.windowMassRegion (q := q) hq χ₁ (β₁ : ℂ)
      (C := C₂) (H := (2:ℝ)^(j+1)) (a₀ := 49/10) (c := 5/2)
      (Λ := Lf j) (L := (7/100) * Real.log (q:ℝ))
      hC₂ (by positivity) (by norm_num) (by norm_num) (by norm_num) (hLpos j hjJ)
      (fun t ht hL => hcnt₁ ((2:ℝ)^(j+1)) (by exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) t ht hL)
      F hzmF hexcF himF hfloorF hlamLF
    rw [show (5/2:ℝ) - 49/10 = -(12/5) by norm_num] at hmass
    have hstep1 : (∑ z ∈ F, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
          * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖)
        ≤ ∑ z ∈ F, 4 / ((4:ℝ)^(Work.LinnikAreas.BGTZ.jjC z) * (Real.log (q:ℝ))^2)
            * ((Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
              * Real.exp (-(49/10) * Work.LinnikContract.lamOf q z.2)) :=
      Finset.sum_le_sum (fun z hz => Work.LinnikAreas.BGTZ.kernel_leC hq z (hzmF z hz) (hhighF z hz))
    have hstep2 : (∑ z ∈ F, 4 / ((4:ℝ)^(Work.LinnikAreas.BGTZ.jjC z) * (Real.log (q:ℝ))^2)
            * ((Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
              * Real.exp (-(49/10) * Work.LinnikContract.lamOf q z.2)))
        = 4 / ((4:ℝ)^j * (Real.log (q:ℝ))^2)
            * (∑ z ∈ F, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
              * Real.exp (-(49/10) * Work.LinnikContract.lamOf q z.2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z hz => ?_)
      rw [(Finset.mem_filter.mp hz).2]
    have hmid : (∑ z ∈ F, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
          * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖)
        ≤ 4 / ((4:ℝ)^j * (Real.log (q:ℝ))^2)
            * (C₂ * ((2:ℝ)^(j+1))^(3/2:ℝ) * Real.exp (5/2)
                * Real.exp (-(12/5) * Lf j) / (1 - Real.exp (-(12/5)))) :=
      (le_trans hstep1 hstep2.le).trans (mul_le_mul_of_nonneg_left hmass (by positivity))
    have hdy : 4 / ((4:ℝ)^j * (Real.log (q:ℝ))^2)
            * (C₂ * ((2:ℝ)^(j+1))^(3/2:ℝ) * Real.exp (5/2)
                * Real.exp (-(12/5) * Lf j) / (1 - Real.exp (-(12/5))))
        = Ks * (Real.log (q:ℝ))^(-2:ℝ) * ((2:ℝ)^(-(1/2):ℝ))^j * Real.exp (-(12/5) * Lf j) := by
      rw [hKsdef]
      exact dyadicAlg C₂ (5/2) (1 - Real.exp (-(12/5))) (Real.log (q:ℝ)) j hlog
        (Real.exp (-(12/5) * Lf j))
    have hYexp : Real.exp (-(12/5) * Lf j)
        ≤ Real.exp (12 * C₀ / 5) * (Real.exp (-α)) ^ (12 / (5 * U j)) := by
      have h := Work.LinnikAreas.BGTZ.algPowC (C₀ := C₀) (u := U j) (A := α) hC₀ (hUge j)
      rw [hLdef]; exact h
    have hY : ((2:ℝ)^(-(1/2):ℝ))^j * (Real.exp (-α)) ^ (12 / (5 * U j))
        ≤ Real.exp (-α) * (2:ℝ)^(5/4:ℝ) * ((2:ℝ)^(-(1/4):ℝ))^j := by
      simpa [hUdef] using Work.LinnikAreas.BGTZ.layer_gap2 h𝓛big hαpos hαle j
    have hstep : Ks * (Real.log (q:ℝ))^(-2:ℝ) * ((2:ℝ)^(-(1/2):ℝ))^j
            * Real.exp (-(12/5) * Lf j)
        ≤ Ks * Real.exp (12 * C₀ / 5) * (2:ℝ)^(5/4:ℝ) * (Real.log (q:ℝ))^(-2:ℝ) * lam1
            * ((2:ℝ)^(-(1/4):ℝ))^j := by
      calc Ks * (Real.log (q:ℝ))^(-2:ℝ) * ((2:ℝ)^(-(1/2):ℝ))^j * Real.exp (-(12/5) * Lf j)
          ≤ Ks * (Real.log (q:ℝ))^(-2:ℝ) * ((2:ℝ)^(-(1/2):ℝ))^j
              * (Real.exp (12 * C₀ / 5) * (Real.exp (-α)) ^ (12 / (5 * U j))) :=
            mul_le_mul_of_nonneg_left hYexp (by positivity)
        _ = Ks * Real.exp (12 * C₀ / 5) * (Real.log (q:ℝ))^(-2:ℝ)
              * (((2:ℝ)^(-(1/2):ℝ))^j * (Real.exp (-α)) ^ (12 / (5 * U j))) := by ring
        _ ≤ Ks * Real.exp (12 * C₀ / 5) * (Real.log (q:ℝ))^(-2:ℝ)
              * (Real.exp (-α) * (2:ℝ)^(5/4:ℝ) * ((2:ℝ)^(-(1/4):ℝ))^j) :=
            mul_le_mul_of_nonneg_left hY (by positivity)
        _ = Ks * Real.exp (12 * C₀ / 5) * (2:ℝ)^(5/4:ℝ) * (Real.log (q:ℝ))^(-2:ℝ) * lam1
              * ((2:ℝ)^(-(1/4):ℝ))^j := by rw [hexp_neg]; ring
    exact le_trans (le_trans hmid (le_of_eq hdy)) hstep
  -- the far fibres `J < j`
  have hfibFree : ∀ j, j ∈ S.image Work.LinnikAreas.BGTZ.jjC → ¬ j ≤ J →
      Gs j ≤ Ks * (Real.log (q:ℝ))^(-2:ℝ) * ((2:ℝ)^(-(1/2):ℝ))^j := by
    intro j hjT hnotJ
    show (∑ z ∈ S.filter (fun z => Work.LinnikAreas.BGTZ.jjC z = j),
        (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
          * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖) ≤ _
    have h1 := fiberLowFree hq χ₁ (β₁ : ℂ) hC₂ hcnt₁
      (S.filter (fun z => Work.LinnikAreas.BGTZ.jjC z = j))
      (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
      (fun z hz => hhigh z (Finset.mem_filter.mp hz).1)
      (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
      (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => mul_le_mul_of_nonneg_right
          ((him_lt_of j z (Finset.mem_filter.mp hz).2).le) hlog.le)
      (fun z hz => hlamL z (Finset.mem_filter.mp hz).1)
    rw [hKsdef]
    exact h1
  have hGeq : (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖)
      = ∑ j ∈ S.image Work.LinnikAreas.BGTZ.jjC, Gs j := by
    rw [hGsdef]
    exact (Finset.sum_fiberwise_of_maps_to
      (fun z hz => Finset.mem_image_of_mem Work.LinnikAreas.BGTZ.jjC hz)
      (fun z => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11/2) (3/10) ((1 - z.2) * (Real.log (q:ℝ) : ℂ))‖)).symm
  have hJtail : ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ J ≤ lam1 := by
    have h1 : α ≤ ((J : ℝ) / 2) * Real.log 2 := by
      have h2 : 2 * Real.log (q : ℝ) / Real.log 2 * Real.log 2 = 2 * Real.log (q : ℝ) := by
        field_simp
      nlinarith [hJge, hlog2pos, hαle, hlog]
    have h4 : (2 : ℝ) ^ ((-(1 / 2) : ℝ) * (J : ℝ)) ≤ Real.exp (-α) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.exp_le_exp]
      nlinarith [hlog2pos, h1]
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 2) : ℝ)) J,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← hexp_neg]
    exact h4
  have hA : (∑ j ∈ (S.image Work.LinnikAreas.BGTZ.jjC).filter (fun j => j ≤ J), Gs j)
      ≤ Ks * Real.exp (12 * C₀ / 5) * (2:ℝ)^(5/4:ℝ) * (Real.log (q:ℝ))^(-2:ℝ) * lam1
          * (1 - (2:ℝ)^(-(1/4):ℝ))⁻¹ := by
    have hper : ∀ j ∈ (S.image Work.LinnikAreas.BGTZ.jjC).filter (fun j => j ≤ J),
        Gs j ≤ Ks * Real.exp (12 * C₀ / 5) * (2:ℝ)^(5/4:ℝ) * (Real.log (q:ℝ))^(-2:ℝ)
              * lam1 * ((2:ℝ)^(-(1/4):ℝ))^j :=
      fun j hj => hfibFloor j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
    calc (∑ j ∈ (S.image Work.LinnikAreas.BGTZ.jjC).filter (fun j => j ≤ J), Gs j)
        ≤ ∑ j ∈ (S.image Work.LinnikAreas.BGTZ.jjC).filter (fun j => j ≤ J),
            Ks * Real.exp (12 * C₀ / 5) * (2:ℝ)^(5/4:ℝ) * (Real.log (q:ℝ))^(-2:ℝ)
              * lam1 * ((2:ℝ)^(-(1/4):ℝ))^j := Finset.sum_le_sum hper
      _ = Ks * Real.exp (12 * C₀ / 5) * (2:ℝ)^(5/4:ℝ) * (Real.log (q:ℝ))^(-2:ℝ) * lam1
            * (∑ j ∈ (S.image Work.LinnikAreas.BGTZ.jjC).filter (fun j => j ≤ J),
                ((2:ℝ)^(-(1/4):ℝ))^j) := by
          rw [Finset.mul_sum]
      _ ≤ Ks * Real.exp (12 * C₀ / 5) * (2:ℝ)^(5/4:ℝ) * (Real.log (q:ℝ))^(-2:ℝ) * lam1
            * (1 - (2:ℝ)^(-(1/4):ℝ))⁻¹ := by
          refine mul_le_mul_of_nonneg_left (geom_le ?_ ?_ _) ?_
          · positivity
          · rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
            exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num))
          · positivity
  have hB : (∑ j ∈ (S.image Work.LinnikAreas.BGTZ.jjC).filter (fun j => ¬ j ≤ J), Gs j)
      ≤ Ks * (Real.log (q:ℝ))^(-2:ℝ) * (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹ * lam1 := by
    have hper : ∀ j ∈ (S.image Work.LinnikAreas.BGTZ.jjC).filter (fun j => ¬ j ≤ J),
        Gs j ≤ Ks * (Real.log (q:ℝ))^(-2:ℝ) * ((2:ℝ)^(-(1/2):ℝ))^j :=
      fun j hj => hfibFree j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
    have hrm0 : 0 ≤ (2:ℝ)^(-(1/2):ℝ) := Real.rpow_nonneg (by norm_num) _
    have hrm1 : (2:ℝ)^(-(1/2):ℝ) < 1 := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num))
    calc (∑ j ∈ (S.image Work.LinnikAreas.BGTZ.jjC).filter (fun j => ¬ j ≤ J), Gs j)
        ≤ ∑ j ∈ (S.image Work.LinnikAreas.BGTZ.jjC).filter (fun j => ¬ j ≤ J),
            Ks * (Real.log (q:ℝ))^(-2:ℝ) * ((2:ℝ)^(-(1/2):ℝ))^j := Finset.sum_le_sum hper
      _ = Ks * (Real.log (q:ℝ))^(-2:ℝ)
            * (∑ j ∈ (S.image Work.LinnikAreas.BGTZ.jjC).filter (fun j => ¬ j ≤ J),
                ((2:ℝ)^(-(1/2):ℝ))^j) := by
          rw [Finset.mul_sum]
      _ ≤ Ks * (Real.log (q:ℝ))^(-2:ℝ)
            * (((2:ℝ)^(-(1/2):ℝ))^(J+1) / (1 - (2:ℝ)^(-(1/2):ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · refine geom_tail hrm0 hrm1 J _ ?_
            intro j hj; have := (Finset.mem_filter.mp hj).2; omega
          · positivity
      _ ≤ Ks * (Real.log (q:ℝ))^(-2:ℝ) * (lam1 / (1 - (2:ℝ)^(-(1/2):ℝ))) := by
          refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ ?_) ?_
          · rw [pow_succ]
            calc ((2:ℝ)^(-(1/2):ℝ))^J * (2:ℝ)^(-(1/2):ℝ) ≤ lam1 * 1 :=
                  mul_le_mul hJtail hrm1.le (by positivity) hlam1pos'.le
              _ = lam1 := by ring
          · linarith
          · positivity
      _ = Ks * (Real.log (q:ℝ))^(-2:ℝ) * (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹ * lam1 := by ring
  have hKc : Ks * (Real.exp (12 * C₀ / 5) * (2:ℝ)^(5/4:ℝ) * (1 - (2:ℝ)^(-(1/4):ℝ))⁻¹
        + (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹) ≤ K₂low C₂ C₀ := by
    unfold K₂low
    refine le_trans ?_ (le_max_right _ _)
    have hX : (8 : ℝ) * (2:ℝ)^(3/2:ℝ) * C₂ * Real.exp (5/2) / (1 - Real.exp (-(12/5)))
          * (Real.exp (12*C₀/5) * (2:ℝ)^(5/4:ℝ) * (1 - (2:ℝ)^(-(1/4):ℝ))⁻¹
             + (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹)
        = 2 * (Ks * (Real.exp (12*C₀/5) * (2:ℝ)^(5/4:ℝ) * (1 - (2:ℝ)^(-(1/4):ℝ))⁻¹
             + (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹)) := by
      rw [hKsdef]; ring
    rw [hX]
    have hA1 : 0 < 1 - (2:ℝ)^(-(1/4):ℝ) := by
      have h : (2:ℝ)^(-(1/4):ℝ) < 1 := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num))
      linarith
    have hB1 : 0 < 1 - (2:ℝ)^(-(1/2):ℝ) := by
      have h : (2:ℝ)^(-(1/2):ℝ) < 1 := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num))
      linarith
    have h1 : 0 ≤ Real.exp (12 * C₀ / 5) := (Real.exp_pos _).le
    have h2 : 0 ≤ (2:ℝ)^(5/4:ℝ) := Real.rpow_nonneg (by norm_num) _
    have h3 : 0 ≤ (1 - (2:ℝ)^(-(1/4):ℝ))⁻¹ := inv_nonneg.mpr hA1.le
    have h4 : 0 ≤ (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹ := inv_nonneg.mpr hB1.le
    have hZnn : 0 ≤ Ks * (Real.exp (12*C₀/5) * (2:ℝ)^(5/4:ℝ) * (1 - (2:ℝ)^(-(1/4):ℝ))⁻¹
        + (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹) :=
      mul_nonneg hKsnn (add_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4)
    linarith [hZnn]
  rw [hGeq]
  rw [← Finset.sum_filter_add_sum_filter_not (S.image Work.LinnikAreas.BGTZ.jjC)
        (fun j => j ≤ J) Gs]
  refine le_trans (add_le_add hA hB) ?_
  calc Ks * Real.exp (12 * C₀ / 5) * (2:ℝ)^(5/4:ℝ) * (Real.log (q:ℝ))^(-2:ℝ) * lam1
          * (1 - (2:ℝ)^(-(1/4):ℝ))⁻¹
        + Ks * (Real.log (q:ℝ))^(-2:ℝ) * (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹ * lam1
      = (Ks * (Real.exp (12 * C₀ / 5) * (2:ℝ)^(5/4:ℝ) * (1 - (2:ℝ)^(-(1/4):ℝ))⁻¹
          + (1 - (2:ℝ)^(-(1/2):ℝ))⁻¹)) * lam1 * (Real.log (q:ℝ))^(-2:ℝ) := by ring
    _ ≤ K₂low C₂ C₀ * lam1 * (Real.log (q:ℝ))^(-2:ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hlog.le _)
        exact mul_le_mul_of_nonneg_right hKc hlam1pos'.le

theorem highMassRep2 (C₂ C₃ C₀ : ℝ) (hC₂ : 0 < C₂) (hC₃ : 0 < C₃) (hC₀ : 0 < C₀) :
    Work.SiegelAbsorb.WindowBoundHyp C₂ C₃ C₀ := by
  intro q _ hq χ₁ β₁ hfam₁ hfam₂ hrepq hlam1pos hsmall hlam1lt hαhalf h𝓛big
    S hzm hhigh hexc hsep
  have hlog : 0 < Real.log (q : ℝ) := lt_of_lt_of_le (by norm_num) h𝓛big
  set p : DirichletCharacter ℂ q × ℂ → Prop :=
    fun z => Work.LinnikContract.lamOf q z.2 ≤ (7 / 100) * Real.log (q : ℝ) with hp
  -- the two log-free counts, in the height direction
  have hcnt₂ : ∀ (H : ℝ), 1 ≤ H → ∀ t : ℝ, 0 < t → t ≤ Real.log (q : ℝ) →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ (β₁ : ℂ) t (H * Real.log (q : ℝ))
        ≤ C₃ * Real.exp ((9 / 2) * t) * H ^ (3 / 2 : ℝ) := by
    intro H hH t ht htL
    have hσ1 : 0 ≤ 1 - t / Real.log (q : ℝ) := by
      have h1 : t / Real.log (q : ℝ) ≤ 1 := (div_le_one hlog).mpr htL
      linarith
    have hσ2 : 1 - t / Real.log (q : ℝ) ≤ 1 := by
      have h1 : 0 ≤ t / Real.log (q : ℝ) := div_nonneg ht.le hlog.le
      linarith
    calc Work.LinnikAreas.Siegel.pairCountHeight χ₁ (β₁ : ℂ) t (H * Real.log (q : ℝ))
        ≤ Work.ZeroDensity.famCount q (1 - t / Real.log (q : ℝ))
            ((H * Real.log (q : ℝ)) / Real.log (q : ℝ)) :=
          Work.LinnikAreas.pairCountHeight_le_famCount hq χ₁ (β₁ : ℂ)
      _ = Work.ZeroDensity.famCount q (1 - t / Real.log (q : ℝ)) H := by
          rw [mul_div_cancel_right₀ _ (ne_of_gt hlog)]
      _ ≤ C₃ * Real.exp ((9 / 2) * ((1 - (1 - t / Real.log (q : ℝ))) * Real.log (q : ℝ)))
            * H ^ (3 / 2 : ℝ) := hfam₂ _ _ hσ1 hσ2 hH
      _ = C₃ * Real.exp ((9 / 2) * t) * H ^ (3 / 2 : ℝ) := by
          rw [show (1 - (1 - t / Real.log (q : ℝ))) * Real.log (q : ℝ) = t by
            field_simp; ring]
  have hcnt₁ : ∀ (H : ℝ), 1 ≤ H → ∀ t : ℝ, 0 < t → t ≤ (7 / 100) * Real.log (q : ℝ) →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ (β₁ : ℂ) t (H * Real.log (q : ℝ))
        ≤ C₂ * Real.exp ((5 / 2) * t) * H ^ (3 / 2 : ℝ) := by
    intro H hH t ht htL
    have hσ1 : 93 / 100 ≤ 1 - t / Real.log (q : ℝ) := by
      have h1 : t / Real.log (q : ℝ) ≤ 7 / 100 := (div_le_iff₀ hlog).mpr (by linarith [htL])
      linarith
    have hσ2 : 1 - t / Real.log (q : ℝ) ≤ 1 := by
      have h1 : 0 ≤ t / Real.log (q : ℝ) := div_nonneg ht.le hlog.le
      linarith
    calc Work.LinnikAreas.Siegel.pairCountHeight χ₁ (β₁ : ℂ) t (H * Real.log (q : ℝ))
        ≤ Work.ZeroDensity.famCount q (1 - t / Real.log (q : ℝ))
            ((H * Real.log (q : ℝ)) / Real.log (q : ℝ)) :=
          Work.LinnikAreas.pairCountHeight_le_famCount hq χ₁ (β₁ : ℂ)
      _ = Work.ZeroDensity.famCount q (1 - t / Real.log (q : ℝ)) H := by
          rw [mul_div_cancel_right₀ _ (ne_of_gt hlog)]
      _ ≤ C₂ * Real.exp ((5 / 2) * ((1 - (1 - t / Real.log (q : ℝ))) * Real.log (q : ℝ)))
            * H ^ (3 / 2 : ℝ) := hfam₁ _ _ hσ1 hσ2 hH
      _ = C₂ * Real.exp ((5 / 2) * t) * H ^ (3 / 2 : ℝ) := by
          rw [show (1 - (1 - t / Real.log (q : ℝ))) * Real.log (q : ℝ) = t by
            field_simp; ring]
  -- split the window at `(7/100)𝓛`
  rw [← Finset.sum_filter_add_sum_filter_not S p
      (fun z => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log (q : ℝ) : ℂ))‖)]
  have h1 : (∑ x ∈ S.filter p, (Work.LinnikContract.zeroMult x.1 x.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - x.2) * (Real.log (q : ℝ) : ℂ))‖)
      ≤ Work.SiegelAbsorb.K₂low C₂ C₀ * Work.LinnikContract.lamOf q (β₁ : ℂ)
          * (Real.log (q : ℝ)) ^ (-2 : ℝ) :=
    highMassRep2Low hq χ₁ β₁ hC₂ hC₀
      hcnt₁ hrepq hlam1pos hsmall hlam1lt hαhalf h𝓛big (S.filter p)
      (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
      (fun z hz => hhigh z (Finset.mem_filter.mp hz).1)
      (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
      (fun z hz => hsep z (Finset.mem_filter.mp hz).1)
      (fun z hz => (Finset.mem_filter.mp hz).2)
  have h2 : (∑ x ∈ S.filter (fun z => ¬ p z), (Work.LinnikContract.zeroMult x.1 x.2 : ℝ)
        * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - x.2) * (Real.log (q : ℝ) : ℂ))‖)
      ≤ Work.SiegelAbsorb.K₃high C₃ * Real.exp (-(7 / 250) * Real.log (q : ℝ))
          * (Real.log (q : ℝ)) ^ (-2 : ℝ) :=
    highMassRep2High hq χ₁ (β₁ : ℂ) hC₃ hcnt₂ (S.filter (fun z => ¬ p z))
      (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
      (fun z hz => hhigh z (Finset.mem_filter.mp hz).1)
      (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
      (fun z hz => not_le.mp (Finset.mem_filter.mp hz).2)
  exact le_trans (add_le_add h1 h2) (by refine le_of_eq ?_; ring)

end Work.SiegelAbsorb
