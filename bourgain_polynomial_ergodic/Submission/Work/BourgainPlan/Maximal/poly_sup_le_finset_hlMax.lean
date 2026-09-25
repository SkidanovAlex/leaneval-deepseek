import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_dilation_lp

open MeasureTheory Set
open scoped ENNReal

set_option maxHeartbeats 4000000

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set
open Commons.Analysis.Maximal (hlMax)

/-- **Pointwise maximal bound for a nonconstant polynomial dilation.**  If `q : ℝ[X]` is
nonconstant and nonnegative on `[0,∞)`, then the averages `∫⁻ s in (0,1], ψ (x - q ((N+1) s))`
are dominated, uniformly in `N ∈ ℕ`, by a constant times a finite sum of Hardy–Littlewood
maximal functions of `ψ`, evaluated at the critical values of `q`.

This is the pointwise form of the estimate proved inside `poly_dilation_lp`
(Bourgain (1989), (7.17)). -/
theorem poly_sup_ge_one_le_hlMax {q : Polynomial ℝ} (hdeg : 1 ≤ q.natDegree)
    (hqnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ q.eval x) :
    ∃ K : ℝ, 0 < K ∧ ∃ T : Finset ℝ, ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
      (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1, ψ (x - q.eval (((N + 1 : ℕ) : ℝ) * s)))
        ≤ ENNReal.ofReal K * ∑ c ∈ T, hlMax ψ (x - c) := by
  classical
  have hq'ne : q.derivative ≠ 0 := fun h =>
    (Nat.one_le_iff_ne_zero.mp hdeg) (Polynomial.derivative_eq_zero.mp h)
  obtain ⟨U, cB, C₀, hU1, hcB, hC₀, _hlead, hderivU, hupperU⟩ := poly_growth hqnn hdeg
  have hU0 : 0 ≤ U := le_trans zero_le_one hU1
  obtain ⟨n, a, b, hlt, hsign, hcover⟩ := exists_cover_deriv_ne q hq'ne hU0
  have hLeft := piece_bound_anchor_left piece_le_hlMax_of_deriv_pos
  have hRight := piece_bound_anchor_right hLeft
  have hpiece : ∀ i : Fin n, ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
      ∫⁻ u in Set.Ioc (a i) (b i), ψ (x - q.eval u)
        ≤ ENNReal.ofReal C * (hlMax ψ (x - q.eval (a i)) + hlMax ψ (x - q.eval (b i))) :=
    fun i => cover_piece_bound hLeft hRight q (hlt i) (hsign i)
  set Cp : Fin n → ℝ := fun i => Classical.choose (hpiece i) with hCpdef
  have hCpspec : ∀ i, 0 < Cp i ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
      ∫⁻ u in Set.Ioc (a i) (b i), ψ (x - q.eval u)
        ≤ ENNReal.ofReal (Cp i) * (hlMax ψ (x - q.eval (a i)) + hlMax ψ (x - q.eval (b i))) :=
    fun i => Classical.choose_spec (hpiece i)
  have hSC_nonneg : 0 ≤ ∑ i : Fin n, Cp i :=
    Finset.sum_nonneg fun i _ => (hCpspec i).1.le
  set T : Finset ℝ := (Finset.univ.image fun i : Fin n => q.eval (a i))
      ∪ (Finset.univ.image fun i : Fin n => q.eval (b i)) ∪ {0} with hTdef
  have hTmem_a : ∀ i : Fin n, q.eval (a i) ∈ T := by intro i; rw [hTdef]; simp
  have hTmem_b : ∀ i : Fin n, q.eval (b i) ∈ T := by intro i; rw [hTdef]; simp
  have hT0 : (0:ℝ) ∈ T := by rw [hTdef]; simp
  have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨0, hT0⟩
  obtain ⟨CB, hCB, htail⟩ := tail_le_hlMax q hU1 hcB hC₀ hderivU hupperU
    (fun u hu => hqnn u (le_trans hU0 hu))
  set KA : ℝ := (∑ i : Fin n, Cp i) * ((2 * n : ℕ) : ℝ) with hKAdef
  have hKA_nonneg : 0 ≤ KA := by rw [hKAdef]; positivity
  have hKB_nonneg : 0 ≤ CB := hCB.le
  -- ### Region A: the integral over `(0,U]`
  have hregionA : ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
      ∫⁻ u in Set.Ioc (0:ℝ) U, ψ (x - q.eval u)
        ≤ ENNReal.ofReal KA * ∑ c ∈ T, hlMax ψ (x - c) := by
    intro ψ hψ x
    have hsub : Set.Ioc (0:ℝ) U ⊆ ⋃ i : Fin n, Set.Icc (a i) (b i) :=
      fun v hv => hcover ⟨le_of_lt hv.1, hv.2⟩
    have h1 : ∫⁻ u in Set.Ioc (0:ℝ) U, ψ (x - q.eval u)
        ≤ ∫⁻ u in (⋃ i : Fin n, Set.Icc (a i) (b i)), ψ (x - q.eval u) :=
      lintegral_mono_set hsub
    have h2 : ∫⁻ u in (⋃ i : Fin n, Set.Icc (a i) (b i)), ψ (x - q.eval u)
        ≤ ∑ i : Fin n, ∫⁻ u in Set.Ioc (a i) (b i), ψ (x - q.eval u) := by
      refine le_trans (lintegral_iUnion_le _ _) ?_
      rw [tsum_fintype]
      exact Finset.sum_le_sum fun i _ => le_of_eq (lintegral_Icc_eq_lintegral_Ioc _ _ _)
    have h4 : ∑ i : Fin n, ∫⁻ u in Set.Ioc (a i) (b i), ψ (x - q.eval u)
        ≤ ∑ i : Fin n, ENNReal.ofReal (Cp i)
            * (hlMax ψ (x - q.eval (a i)) + hlMax ψ (x - q.eval (b i))) :=
      Finset.sum_le_sum fun i _ => (hCpspec i).2 ψ hψ x
    have hTsum : ∀ c ∈ T, hlMax ψ (x - c) ≤ ∑ c' ∈ T, hlMax ψ (x - c') :=
      fun c hc => Finset.single_le_sum (f := fun c' => hlMax ψ (x - c'))
        (fun c' _ => bot_le) hc
    have hCp_le : ∀ i : Fin n, ENNReal.ofReal (Cp i) ≤ ENNReal.ofReal (∑ j : Fin n, Cp j) := by
      intro i
      refine ENNReal.ofReal_le_ofReal ?_
      exact Finset.single_le_sum (fun j _ => (hCpspec j).1.le) (Finset.mem_univ i)
    have h5 : ∑ i : Fin n, ENNReal.ofReal (Cp i)
          * (hlMax ψ (x - q.eval (a i)) + hlMax ψ (x - q.eval (b i)))
        ≤ ENNReal.ofReal (∑ j : Fin n, Cp j)
            * ((n : ℝ≥0∞) * (2 * ∑ c ∈ T, hlMax ψ (x - c))) := by
      calc ∑ i : Fin n, ENNReal.ofReal (Cp i)
            * (hlMax ψ (x - q.eval (a i)) + hlMax ψ (x - q.eval (b i)))
          ≤ ∑ _i : Fin n, ENNReal.ofReal (∑ j : Fin n, Cp j)
              * (2 * ∑ c ∈ T, hlMax ψ (x - c)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine mul_le_mul' (hCp_le i) ?_
            have ha := hTsum (q.eval (a i)) (hTmem_a i)
            have hb := hTsum (q.eval (b i)) (hTmem_b i)
            calc hlMax ψ (x - q.eval (a i)) + hlMax ψ (x - q.eval (b i))
                ≤ ∑ c ∈ T, hlMax ψ (x - c) + ∑ c ∈ T, hlMax ψ (x - c) := add_le_add ha hb
              _ = 2 * ∑ c ∈ T, hlMax ψ (x - c) := by rw [two_mul]
        _ = ENNReal.ofReal (∑ j : Fin n, Cp j)
              * ((n : ℝ≥0∞) * (2 * ∑ c ∈ T, hlMax ψ (x - c))) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
            ring
    have h6 : ENNReal.ofReal (∑ j : Fin n, Cp j)
            * ((n : ℝ≥0∞) * (2 * ∑ c ∈ T, hlMax ψ (x - c)))
        ≤ ENNReal.ofReal KA * ∑ c ∈ T, hlMax ψ (x - c) := by
      have hcast : ((n : ℝ≥0∞)) * 2 = ENNReal.ofReal ((2 * n : ℕ) : ℝ) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) from (ENNReal.ofReal_ofNat 2).symm,
          ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
          show (n : ℝ) * 2 = ((2 * n : ℕ) : ℝ) by push_cast; ring]
      have hconst : ENNReal.ofReal (∑ j : Fin n, Cp j) * ((n : ℝ≥0∞) * 2)
          = ENNReal.ofReal KA := by
        rw [hcast, hKAdef, ← ENNReal.ofReal_mul hSC_nonneg]
      calc ENNReal.ofReal (∑ j : Fin n, Cp j) * ((n : ℝ≥0∞) * (2 * ∑ c ∈ T, hlMax ψ (x - c)))
          = (ENNReal.ofReal (∑ j : Fin n, Cp j) * ((n : ℝ≥0∞) * 2))
              * ∑ c ∈ T, hlMax ψ (x - c) := by ring
        _ ≤ ENNReal.ofReal KA * ∑ c ∈ T, hlMax ψ (x - c) := le_of_eq (by rw [hconst])
    exact le_trans h1 (le_trans h2 (le_trans h4 (le_trans h5 h6)))
  -- ### Region B: the tail
  have hregionB : ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ (N x : ℝ), U ≤ N →
      ∫⁻ u in Set.Ioc U N, ψ (x - q.eval u)
        ≤ ENNReal.ofReal (CB * N) * ∑ c ∈ T, hlMax ψ (x - c) := by
    intro ψ hψ N x hN
    refine le_trans (htail ψ hψ N x hN) ?_
    refine mul_le_mul_right ?_ _
    simpa using Finset.single_le_sum (f := fun c' => hlMax ψ (x - c')) (fun c' _ => bot_le) hT0
  -- ### the bound for a single average
  have hmain : ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ (N x : ℝ), 1 ≤ N →
      ∫⁻ u in Set.Ioc (0:ℝ) N, ψ (x - q.eval u)
        ≤ ENNReal.ofReal (KA + CB) * ENNReal.ofReal N * ∑ c ∈ T, hlMax ψ (x - c) := by
    intro ψ hψ N x hN
    have hN1 : (1:ℝ≥0∞) ≤ ENNReal.ofReal N := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hN
    have hKA_le : ENNReal.ofReal KA ≤ ENNReal.ofReal KA * ENNReal.ofReal N := by
      calc ENNReal.ofReal KA = ENNReal.ofReal KA * 1 := (mul_one _).symm
        _ ≤ ENNReal.ofReal KA * ENNReal.ofReal N := mul_le_mul_right hN1 _
    rcases lt_or_ge N U with hNU | hUN
    · have hsubN : Set.Ioc (0:ℝ) N ⊆ Set.Ioc (0:ℝ) U :=
        fun v hv => ⟨hv.1, le_trans hv.2 hNU.le⟩
      have h1 : ∫⁻ u in Set.Ioc (0:ℝ) N, ψ (x - q.eval u)
          ≤ ENNReal.ofReal KA * ∑ c ∈ T, hlMax ψ (x - c) :=
        le_trans (lintegral_mono_set hsubN) (hregionA ψ hψ x)
      have hKN : ENNReal.ofReal KA ≤ ENNReal.ofReal (KA + CB) * ENNReal.ofReal N :=
        calc ENNReal.ofReal KA ≤ ENNReal.ofReal (KA + CB) :=
              ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hKB_nonneg)
          _ = ENNReal.ofReal (KA + CB) * 1 := (mul_one _).symm
          _ ≤ ENNReal.ofReal (KA + CB) * ENNReal.ofReal N := mul_le_mul_right hN1 _
      exact le_trans h1 (mul_le_mul_left hKN _)
    · have hsplit : (∫⁻ u in Set.Ioc (0:ℝ) N, ψ (x - q.eval u))
          ≤ (∫⁻ u in Set.Ioc (0:ℝ) U, ψ (x - q.eval u))
            + (∫⁻ u in Set.Ioc U N, ψ (x - q.eval u)) := by
        have hunion : Set.Ioc (0:ℝ) U ∪ Set.Ioc U N = Set.Ioc (0:ℝ) N := by
          ext y
          simp only [Set.mem_union, Set.mem_Ioc]
          constructor
          · rintro (⟨hy1, hy2⟩ | ⟨hy1, hy2⟩)
            · exact ⟨hy1, hy2.trans hUN⟩
            · exact ⟨lt_trans (lt_of_lt_of_le zero_lt_one hU1) hy1, hy2⟩
          · rintro ⟨hy1, hy2⟩
            rcases lt_trichotomy y U with hy | rfl | hy
            · exact Or.inl ⟨hy1, hy.le⟩
            · exact Or.inl ⟨hy1, le_rfl⟩
            · exact Or.inr ⟨hy, hy2⟩
        rw [← hunion]
        exact lintegral_union_le (fun u : ℝ => ψ (x - q.eval u))
          (Set.Ioc (0:ℝ) U) (Set.Ioc U N)
      have hA := hregionA ψ hψ x
      have hB := hregionB ψ hψ N x hUN
      have hsum : (∫⁻ u in Set.Ioc (0:ℝ) U, ψ (x - q.eval u))
            + (∫⁻ u in Set.Ioc U N, ψ (x - q.eval u))
          ≤ ENNReal.ofReal (KA + CB) * ENNReal.ofReal N * ∑ c ∈ T, hlMax ψ (x - c) := by
        have hstep1 : (∫⁻ u in Set.Ioc (0:ℝ) U, ψ (x - q.eval u))
              + (∫⁻ u in Set.Ioc U N, ψ (x - q.eval u))
            ≤ (ENNReal.ofReal KA * ∑ c ∈ T, hlMax ψ (x - c))
              + (ENNReal.ofReal (CB * N) * ∑ c ∈ T, hlMax ψ (x - c)) := add_le_add hA hB
        calc (∫⁻ u in Set.Ioc (0:ℝ) U, ψ (x - q.eval u))
              + (∫⁻ u in Set.Ioc U N, ψ (x - q.eval u))
            ≤ (ENNReal.ofReal KA + ENNReal.ofReal (CB * N)) * ∑ c ∈ T, hlMax ψ (x - c) := by
              rw [← add_mul] at hstep1
              exact hstep1
          _ ≤ (ENNReal.ofReal KA * ENNReal.ofReal N
                + ENNReal.ofReal CB * ENNReal.ofReal N) * ∑ c ∈ T, hlMax ψ (x - c) := by
              refine mul_le_mul_left ?_ _
              refine add_le_add hKA_le ?_
              rw [ENNReal.ofReal_mul hKB_nonneg]
          _ ≤ ENNReal.ofReal (KA + CB) * ENNReal.ofReal N * ∑ c ∈ T, hlMax ψ (x - c) := by
              rw [← add_mul, ← ENNReal.ofReal_add hKA_nonneg hKB_nonneg, mul_assoc]
      exact le_trans hsplit hsum
  -- ### the averages in the `s`-form
  have hFN : ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ (N : ℕ) (x : ℝ),
      ∫⁻ s in Set.Ioc (0:ℝ) 1, ψ (x - q.eval ((((N + 1 : ℕ) : ℝ)) * s))
        ≤ ENNReal.ofReal (KA + CB) * ∑ c ∈ T, hlMax ψ (x - c) := by
    intro ψ hψ N x
    have hNnpos : (0:ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have hNn1 : (1:ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    have hstep : ∫⁻ s in Set.Ioc (0:ℝ) 1, (fun u : ℝ => ψ (x - q.eval u))
          ((((N + 1 : ℕ) : ℝ)) * s)
        = (ENNReal.ofReal ((N + 1 : ℕ) : ℝ))⁻¹
          * ∫⁻ u in Set.Ioc (0:ℝ) ((N + 1 : ℕ) : ℝ), ψ (x - q.eval u) :=
      lintegral_Ioc_comp_mul (fun u : ℝ => ψ (x - q.eval u)) hNnpos
    rw [show (∫⁻ s in Set.Ioc (0:ℝ) 1,
          ψ (x - q.eval ((((N + 1 : ℕ) : ℝ)) * s)))
        = ∫⁻ s in Set.Ioc (0:ℝ) 1, (fun u : ℝ => ψ (x - q.eval u)) ((((N + 1 : ℕ) : ℝ)) * s)
        from rfl, hstep]
    have hm := hmain ψ hψ ((N + 1 : ℕ) : ℝ) x hNn1
    refine le_trans (mul_le_mul_right hm _) ?_
    rw [show (ENNReal.ofReal ((N + 1 : ℕ) : ℝ))⁻¹
          * (ENNReal.ofReal (KA + CB) * ENNReal.ofReal ((N + 1 : ℕ) : ℝ)
            * ∑ c ∈ T, hlMax ψ (x - c))
        = (ENNReal.ofReal ((N + 1 : ℕ) : ℝ))⁻¹ * ENNReal.ofReal ((N + 1 : ℕ) : ℝ)
          * (ENNReal.ofReal (KA + CB) * ∑ c ∈ T, hlMax ψ (x - c)) from by ring,
      ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top, one_mul]
  exact ⟨KA + CB, by linarith, T, fun ψ hψ x => iSup_le fun N => hFN ψ hψ N x⟩

theorem poly_sup_le_finset_hlMax (P : Polynomial ℤ)
    (hP : ∀ x : ℝ, 0 ≤ x → 0 ≤ (P.map (Int.castRingHom ℝ)).eval x) :
    ∃ K : ℝ, 0 < K ∧ ∃ T D : Finset ℝ, ∀ (ψ : ℝ → ENNReal), Measurable ψ → ∀ x : ℝ,
      (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s)))
        ≤ ENNReal.ofReal K * ∑ c ∈ T, Commons.Analysis.Maximal.hlMax ψ (x - c)
          + ∑ c ∈ D, ψ (x - c) := by
  classical
  rcases eq_or_ne (P.map (Int.castRingHom ℝ)).natDegree 0 with hdeg0 | hdeg0
  · -- constant polynomial: every average equals `ψ (x - q 0)`
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
    have hconst : ∀ y : ℝ, (P.map (Int.castRingHom ℝ)).eval y
        = (P.map (Int.castRingHom ℝ)).eval 0 := by
      intro y
      rw [hC]
      simp
    refine ⟨1, one_pos, ∅, {(P.map (Int.castRingHom ℝ)).eval 0}, fun ψ hψ x => ?_⟩
    have hF : ∀ N : ℕ, (∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s)))
        = ψ (x - (P.map (Int.castRingHom ℝ)).eval 0) := by
      intro N
      have h1 : (∫⁻ s in Set.Ioc (0:ℝ) 1,
            ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s)))
          = ∫⁻ _s in Set.Ioc (0:ℝ) 1, ψ (x - (P.map (Int.castRingHom ℝ)).eval 0) :=
        lintegral_congr fun s => by rw [hconst ((N:ℝ)*s)]
      rw [h1, setLIntegral_const, Real.volume_Ioc]
      simp
    have hsup : (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s)))
        = ψ (x - (P.map (Int.castRingHom ℝ)).eval 0) := by
      rw [show (fun N : ℕ => ∫⁻ s in Set.Ioc (0:ℝ) 1,
            ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s)))
          = fun _ : ℕ => ψ (x - (P.map (Int.castRingHom ℝ)).eval 0) from funext hF]
      exact iSup_const
    rw [hsup, Finset.sum_empty, ENNReal.ofReal_one, one_mul, zero_add, Finset.sum_singleton]
  · -- nonconstant polynomial
    obtain ⟨K, hK, T, hT⟩ :=
      poly_sup_ge_one_le_hlMax (Nat.one_le_iff_ne_zero.mpr hdeg0) hP
    refine ⟨K, hK, T, {(P.map (Int.castRingHom ℝ)).eval 0}, fun ψ hψ x => ?_⟩
    have h0eq : (∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((0:ℕ) : ℝ)) * s)))
        = ψ (x - (P.map (Int.castRingHom ℝ)).eval 0) := by
      have h1 : (∫⁻ s in Set.Ioc (0:ℝ) 1,
            ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((0:ℕ) : ℝ)) * s)))
          = ∫⁻ _s in Set.Ioc (0:ℝ) 1, ψ (x - (P.map (Int.castRingHom ℝ)).eval 0) :=
        lintegral_congr fun s => by simp
      rw [h1, setLIntegral_const, Real.volume_Ioc]
      simp
    have hsplit : (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s)))
        ≤ (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
            ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s)))
          + ∫⁻ s in Set.Ioc (0:ℝ) 1,
              ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((0:ℕ) : ℝ)) * s)) := by
      refine iSup_le fun N => ?_
      rcases N with _ | k
      · exact le_add_self
      · refine le_trans (le_iSup (fun N : ℕ => ∫⁻ s in Set.Ioc (0:ℝ) 1,
            ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s))) k) ?_
        exact le_self_add
    rw [h0eq] at hsplit
    rw [Finset.sum_singleton]
    exact le_trans hsplit (add_le_add (hT ψ hψ x) le_rfl)

end Work.BourgainPlan.Maximal
