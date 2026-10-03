import Mathlib
import Submission.Work.Analysis.InverseTheory.MajorArcs

/-!
# Injectivity of the `ℤ`-Fourier transform (`𝓕_ℤ`)

Krause–Mirek–Tao, §5–§6.  The paper's frequency-side arguments frequently use the elementary fact
that the Fourier transform `𝓕_ℤ L(ξ) = ∑_x L x · e(-x ξ)` on the frequency circle `ℝ/ℤ` *determines*
`L`: if `𝓕_ℤ L` vanishes identically then `L = 0`.

The proof here is by "smearing at the `M`-th roots of unity".  Since each `ξ_j = j/M` is a
frequency at which `𝓕_ℤ L` vanishes, the average

  `(1/M) ∑_{j<M} e(x₀ j/M) · 𝓕_ℤ L(j/M)`

vanishes; exchanging the finite sum with the absolutely convergent series and evaluating the
geometric sum `∑_{j<M} e((x₀ - x) j/M) = M·1_{M ∣ x₀ - x}` shows that

  `∑_{x ≡ x₀ (M)} L x = 0`   for every `M ≥ 1`.

For `M` larger than the span of a finite set on which `∑_x ‖L x‖` is concentrated, the only
element of the arithmetic progression `x₀ + Mℤ` in that finite set is `x₀` itself, and the
remainder is bounded by the tail of the summable family `‖L ·‖`; letting the finite set grow
(the tail of a summable family tends to `0`) gives `L x₀ = 0`.
-/

set_option autoImplicit false

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory
open scoped BigOperators Topology

/-! ## The character sum at the `M`-th roots of unity -/

/-- `∑_{j < M} e(m j / M) = M` if `M ∣ m`, and `0` otherwise.  Here `e(t) = e^{2πit}` is
Mathlib's `fourier m` evaluated on the frequency circle. -/
theorem sum_fourier_rat_eq (M : ℕ) (hM : M ≠ 0) (m : ℤ) :
    ∑ j ∈ Finset.range M,
      (fourier m (((j : ℝ) / (M : ℝ) : ℝ) : FreqCircle) : ℂ)
      = if (M : ℤ) ∣ m then (M : ℂ) else 0 := by
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / (M : ℂ)) with hzdef
  have hM' : ((M : ℂ)) ≠ 0 := by exact_mod_cast hM
  have hterm : ∀ j : ℕ,
      (fourier m (((j : ℝ) / (M : ℝ) : ℝ) : FreqCircle) : ℂ) = z ^ j := by
    intro j
    rw [fourier_coe_apply]
    have harith : 2 * Real.pi * Complex.I * (m : ℂ) * (((j : ℝ) / (M : ℝ) : ℝ) : ℂ) / (1 : ℝ)
        = (j : ℂ) * (2 * Real.pi * Complex.I * (m : ℂ) / (M : ℂ)) := by
      push_cast
      field_simp
    rw [harith, Complex.exp_nat_mul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  have hzM : z ^ M = 1 := by
    rw [hzdef, ← Complex.exp_nat_mul]
    have harg : (M : ℂ) * (2 * Real.pi * Complex.I * (m : ℂ) / (M : ℂ))
        = (m : ℂ) * (2 * Real.pi * Complex.I) := by field_simp
    rw [harg]
    exact Complex.exp_eq_one_iff.mpr ⟨m, rfl⟩
  have hz1 : z = 1 ↔ (M : ℤ) ∣ m := by
    rw [hzdef, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      have h5 : (2 * Real.pi * Complex.I) * (m : ℂ)
          = (n : ℂ) * (2 * Real.pi * Complex.I) * (M : ℂ) := by
        rw [← hn, div_mul_cancel₀ _ hM']
      have h6 : (m : ℂ) = (n : ℂ) * (M : ℂ) := by
        have h7 : (2 * Real.pi * Complex.I) * (m : ℂ)
            = (2 * Real.pi * Complex.I) * ((n : ℂ) * (M : ℂ)) := by
          rw [h5]; ring
        exact mul_left_cancel₀ Complex.two_pi_I_ne_zero h7
      refine ⟨n, ?_⟩
      have h8 : ((m : ℤ) : ℂ) = ((n * M : ℤ) : ℂ) := by push_cast; exact h6
      have h9 : m = n * M := by exact_mod_cast h8
      rw [h9, mul_comm]
    · rintro ⟨c, rfl⟩
      refine ⟨c, ?_⟩
      push_cast
      field_simp
  by_cases hdiv : (M : ℤ) ∣ m
  · rw [if_pos hdiv]
    have hz1' : z = 1 := hz1.mpr hdiv
    rw [Finset.sum_congr rfl (fun j _ => by rw [hz1', one_pow])]
    simp [Finset.sum_const, Finset.card_range]
  · rw [if_neg hdiv]
    have hzne : z ≠ 1 := fun hh => hdiv (hz1.mp hh)
    have hgeo := geom_sum_mul z M
    rw [hzM, sub_self] at hgeo
    rcases mul_eq_zero.mp hgeo with hh | hh
    · exact hh
    · exact absurd (sub_eq_zero.mp hh) hzne

/-! ## Elementary summability and divisibility helpers -/

/-- Multiplying a summable function by a bounded (`‖·‖ ≤ 1`) function preserves summability. -/
theorem summable_mul_of_bound {L : ℤ → ℂ} (hL : Summable fun x : ℤ => ‖L x‖) {c : ℤ → ℂ}
    (hc : ∀ x, ‖c x‖ ≤ 1) : Summable fun x : ℤ => L x * c x :=
  Summable.of_norm_bounded hL fun x => by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hc x)

/-- The same, for the norms. -/
theorem summable_norm_mul_of_bound {L : ℤ → ℂ} (hL : Summable fun x : ℤ => ‖L x‖) {c : ℤ → ℂ}
    (hc : ∀ x, ‖c x‖ ≤ 1) : Summable fun x : ℤ => ‖L x * c x‖ :=
  Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hc x)) hL

/-- A nonzero multiple of `M` has `natAbs` at least `M`. -/
theorem int_eq_zero_of_dvd_of_natAbs_lt {M : ℕ} {a : ℤ} (h : (M : ℤ) ∣ a) (ha : a.natAbs < M) :
    a = 0 := by
  obtain ⟨c, hc⟩ := h
  have h2 : a.natAbs = M * c.natAbs := by rw [hc, Int.natAbs_mul]; simp
  by_contra hne
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact hne hc
  have hMpos : 0 < M := by
    by_contra hM
    have hM0 : M = 0 := Nat.eq_zero_of_le_zero (not_lt.mp hM)
    subst hM0
    simp only [Nat.zero_mul] at h2
    exact hne (Int.natAbs_eq_zero.mp h2)
  have h3 : M * c.natAbs < M * 1 := by rw [← h2, mul_one]; exact ha
  have h4 : c.natAbs < 1 := (Nat.mul_lt_mul_left hMpos).mp h3
  have h5 : c.natAbs = 0 := by omega
  exact hc0 (Int.natAbs_eq_zero.mp h5)

/-! ## The smearing identity -/

/-- **Smearing identity.**  If `𝓕_ℤ L` vanishes on the frequency circle and `‖L ·‖` is summable,
then for every `M ≥ 1` and every `x₀ : ℤ` the sum of `L` over the congruence class `x₀ mod M`
is `0`.  (The class indicator is written as a function on all of `ℤ` for convenience.) -/
theorem tsum_smear (L : ℤ → ℂ) (hL : Summable fun x : ℤ => ‖L x‖)
    (h : ∀ ξ : FreqCircle, ZFourier L ξ = 0) (M : ℕ) (hM : M ≠ 0) (x₀ : ℤ) :
    ∑' x : ℤ, L x * (if (M : ℤ) ∣ (x₀ - x) then (1 : ℂ) else 0) = 0 := by
  let ξj : ℕ → FreqCircle := fun j => (((j : ℝ) / (M : ℝ) : ℝ) : FreqCircle)
  have hnorm : ∀ (n : ℤ) (ξ : FreqCircle), ‖((fourier n ξ : ℂ))‖ = 1 := by
    intro n ξ
    rw [fourier_apply]
    exact Circle.norm_coe _
  have hsumm : ∀ j : ℕ,
      Summable (fun x : ℤ => (fourier x₀ (ξj j) : ℂ) * (L x * (fourier (-x) (ξj j) : ℂ))) := by
    intro j
    refine Summable.of_norm_bounded hL (fun x => ?_)
    rw [norm_mul, norm_mul, hnorm, hnorm]
    ring_nf
    exact le_rfl
  have hstep1 : ∑ j ∈ Finset.range M,
      (fourier x₀ (ξj j) : ℂ) * ZFourier L (ξj j) = 0 := by
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [h (ξj j), mul_zero]
  have hstep2 : ∑ j ∈ Finset.range M,
      (fourier x₀ (ξj j) : ℂ) * (∑' x : ℤ, L x * (fourier (-x) (ξj j) : ℂ)) = 0 := by
    simpa only [ZFourier] using hstep1
  have hstep3 : ∑ j ∈ Finset.range M,
      (∑' x : ℤ, (fourier x₀ (ξj j) : ℂ) * (L x * (fourier (-x) (ξj j) : ℂ))) = 0 := by
    simpa only [← tsum_mul_left] using hstep2
  have hswap : ∑' x : ℤ, ∑ j ∈ Finset.range M,
        (fourier x₀ (ξj j) : ℂ) * (L x * (fourier (-x) (ξj j) : ℂ))
      = ∑ j ∈ Finset.range M, ∑' x : ℤ,
        (fourier x₀ (ξj j) : ℂ) * (L x * (fourier (-x) (ξj j) : ℂ)) :=
    Summable.tsum_finsetSum (fun j hj => hsumm j)
  have hstep4 : ∑' x : ℤ, ∑ j ∈ Finset.range M,
      (fourier x₀ (ξj j) : ℂ) * (L x * (fourier (-x) (ξj j) : ℂ)) = 0 := by
    rw [hswap]; exact hstep3
  have hinner : ∀ x : ℤ, ∑ j ∈ Finset.range M,
        (fourier x₀ (ξj j) : ℂ) * (L x * (fourier (-x) (ξj j) : ℂ))
      = L x * (if (M : ℤ) ∣ (x₀ - x) then (M : ℂ) else 0) := by
    intro x
    have h1 : ∀ j : ℕ, (fourier x₀ (ξj j) : ℂ) * (L x * (fourier (-x) (ξj j) : ℂ))
        = L x * ((fourier x₀ (ξj j) : ℂ) * (fourier (-x) (ξj j) : ℂ)) := by
      intro j; ring
    rw [Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.mul_sum]
    congr 1
    have h2 : ∀ j : ℕ, (fourier x₀ (ξj j) : ℂ) * (fourier (-x) (ξj j) : ℂ)
        = (fourier (x₀ - x) (ξj j) : ℂ) := by
      intro j
      have hsub : x₀ - x = x₀ + (-x) := by ring
      rw [hsub, fourier_add]
    rw [Finset.sum_congr rfl (fun j _ => h2 j)]
    exact sum_fourier_rat_eq M hM (x₀ - x)
  have hstep5 : ∑' x : ℤ, L x * (if (M : ℤ) ∣ (x₀ - x) then (M : ℂ) else 0) = 0 := by
    simpa only [hinner] using hstep4
  have hpoint : ∀ x : ℤ, L x * (if (M : ℤ) ∣ (x₀ - x) then (M : ℂ) else 0)
      = (M : ℂ) * (L x * (if (M : ℤ) ∣ (x₀ - x) then (1 : ℂ) else 0)) := by
    intro x
    by_cases hx : (M : ℤ) ∣ (x₀ - x) <;> simp [hx, mul_comm]
  have h4 : ∑' x : ℤ, (M : ℂ) * (L x * (if (M : ℤ) ∣ (x₀ - x) then (1 : ℂ) else 0)) = 0 := by
    have hrew : ∑' x : ℤ, (M : ℂ) * (L x * (if (M : ℤ) ∣ (x₀ - x) then (1 : ℂ) else 0))
        = ∑' x : ℤ, L x * (if (M : ℤ) ∣ (x₀ - x) then (M : ℂ) else 0) :=
      tsum_congr (fun x => (hpoint x).symm)
    rw [hrew, hstep5]
  rw [tsum_mul_left] at h4
  exact (mul_eq_zero.mp h4).resolve_left (by exact_mod_cast hM)

/-! ## Injectivity -/

theorem zFourierInj (L : ℤ → ℂ) (hL : Summable fun x : ℤ => ‖L x‖) (h : ∀ ξ : Work.Analysis.InverseTheory.FreqCircle, Work.Analysis.InverseTheory.ZFourier L ξ = 0) : ∀ x : ℤ, L x = 0 := by
  classical
  intro x₀
  have hnorm0 : ‖L x₀‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖L x₀‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    -- the tail of a summable family tends to `0`, so some finite set carries all but `ε` of `‖L‖`
    have htend : Filter.Tendsto (fun s : Finset ℤ => ∑' b : {x : ℤ // x ∉ s}, ‖L b‖)
        Filter.atTop (nhds 0) :=
      tendsto_tsum_compl_atTop_zero (fun x : ℤ => ‖L x‖)
    have hev : ∀ᶠ s : Finset ℤ in Filter.atTop,
        (∑' b : {x : ℤ // x ∉ s}, ‖L b‖) < ‖L x₀‖ :=
      (tendsto_order.1 htend).2 _ hpos
    obtain ⟨s, hs⟩ := Filter.eventually_atTop.1 hev
    have hs' : (∑' b : {x : ℤ // x ∉ s}, ‖L b‖) < ‖L x₀‖ := hs s le_rfl
    -- choose `M` larger than the diameter of `s` around `x₀`
    set M : ℕ := s.sup (fun x => (x₀ - x).natAbs) + 1 with hMdef
    have hM : M ≠ 0 := by rw [hMdef]; exact Nat.succ_ne_zero _
    have hMlt : ∀ x ∈ s, (x₀ - x).natAbs < M := by
      intro x hx
      rw [hMdef]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := fun x => (x₀ - x).natAbs) hx)
    -- the part of the congruence class `x₀ mod M` outside `x₀` itself
    set χ : ℤ → ℂ := fun x => if (M : ℤ) ∣ (x₀ - x) ∧ x ≠ x₀ then (1 : ℂ) else 0 with hχdef
    have hχzero : ∀ x ∈ s, χ x = 0 := by
      intro x hx
      have hlt : (x₀ - x).natAbs < M := hMlt x hx
      simp only [hχdef]
      rw [if_neg]
      rintro ⟨hdvd, hxne⟩
      have hzero : x₀ - x = 0 := int_eq_zero_of_dvd_of_natAbs_lt hdvd hlt
      exact hxne (by omega)
    have hχnorm : ∀ x : ℤ, ‖χ x‖ ≤ 1 := by
      intro x
      simp only [hχdef]
      split <;> simp
    have hψnorm : ∀ x : ℤ, ‖(if x = x₀ then (1 : ℂ) else 0)‖ ≤ 1 := by
      intro x; split <;> simp
    have hsummχ : Summable (fun x : ℤ => L x * χ x) := summable_mul_of_bound hL hχnorm
    have hsummχnorm : Summable (fun x : ℤ => ‖L x * χ x‖) :=
      summable_norm_mul_of_bound hL hχnorm
    have hsummψ : Summable (fun x : ℤ => L x * (if x = x₀ then (1 : ℂ) else 0)) :=
      summable_mul_of_bound hL hψnorm
    have hφ : ∀ x : ℤ, (if (M : ℤ) ∣ (x₀ - x) then (1 : ℂ) else 0)
        = (if x = x₀ then (1 : ℂ) else 0) + χ x := by
      intro x
      by_cases hx : (M : ℤ) ∣ (x₀ - x)
      · by_cases hxx : x = x₀
        · simp [hχdef, hxx]
        · simp [hχdef, hx, hxx]
      · have hne' : x ≠ x₀ := by
          intro hxx
          exact hx ⟨0, by rw [hxx]; ring⟩
        simp [hχdef, hx, hne']
    -- the smeared identity: the class sum splits into `L x₀` plus the "tail" `χ`-sum
    have hsplit : ∑' x : ℤ, L x * (if (M : ℤ) ∣ (x₀ - x) then (1 : ℂ) else 0)
        = L x₀ + ∑' x : ℤ, L x * χ x := by
      calc ∑' x : ℤ, L x * (if (M : ℤ) ∣ (x₀ - x) then (1 : ℂ) else 0)
          = ∑' x : ℤ, (L x * (if x = x₀ then (1 : ℂ) else 0) + L x * χ x) := by
            apply tsum_congr; intro x
            rw [hφ x, mul_add]
        _ = (∑' x : ℤ, L x * (if x = x₀ then (1 : ℂ) else 0)) + ∑' x : ℤ, L x * χ x :=
            Summable.tsum_add hsummψ hsummχ
        _ = L x₀ + ∑' x : ℤ, L x * χ x := by
            rw [tsum_eq_single x₀ (fun b hb => by simp [if_neg hb]), if_pos rfl, mul_one]
    have hsmear := tsum_smear L hL h M hM x₀
    have hLx0 : L x₀ = -∑' x : ℤ, L x * χ x := by
      rw [eq_neg_iff_add_eq_zero]
      exact hsplit.symm.trans hsmear
    -- the `χ`-sum is supported in the complement of `s`, hence bounded by the tail
    have hsummTail : Summable (fun x : ℤ => ‖L x‖ * (if x ∈ s then 0 else 1)) :=
      Summable.of_nonneg_of_le (fun x => by positivity)
        (fun x => by by_cases hx : x ∈ s <;> simp [hx]) hL
    have htail_eq : ∑' x : ℤ, ‖L x‖ * (if x ∈ s then 0 else 1)
        = ∑' b : {x : ℤ // x ∉ s}, ‖L b‖ := by
      have h := Summable.sum_add_tsum_subtype_compl hsummTail s
      have h1 : ∑ x ∈ s, (‖L x‖ * (if x ∈ s then 0 else 1)) = 0 := by
        apply Finset.sum_eq_zero; intro x hx; simp [hx]
      rw [h1, zero_add] at h
      calc ∑' x : ℤ, ‖L x‖ * (if x ∈ s then 0 else 1)
          = ∑' b : {x : ℤ // x ∉ s},
              (‖L (b : ℤ)‖ * (if (b : ℤ) ∈ s then 0 else 1)) := h.symm
        _ = ∑' b : {x : ℤ // x ∉ s}, ‖L (b : ℤ)‖ := tsum_congr (fun b => by simp [b.2])
    have hmain : ‖L x₀‖ ≤ ∑' b : {x : ℤ // x ∉ s}, ‖L b‖ := by
      calc ‖L x₀‖ = ‖∑' x : ℤ, L x * χ x‖ := by rw [hLx0, norm_neg]
        _ ≤ ∑' x : ℤ, ‖L x * χ x‖ := norm_tsum_le_tsum_norm hsummχnorm
        _ ≤ ∑' x : ℤ, ‖L x‖ * (if x ∈ s then 0 else 1) := by
              refine Summable.tsum_le_tsum (fun x => ?_) hsummχnorm hsummTail
              by_cases hx : x ∈ s
              · rw [hχzero x hx]; simp [hx]
              · rw [norm_mul]
                simp only [hx, if_false]
                exact mul_le_mul_of_nonneg_left (hχnorm x) (norm_nonneg _)
        _ = ∑' b : {x : ℤ // x ∉ s}, ‖L b‖ := htail_eq
    exact absurd hmain (not_le.mpr hs')
  exact norm_eq_zero.mp hnorm0

end Work.KMTAreas.A4
