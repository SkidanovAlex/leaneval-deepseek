import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.ball_count_small
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.MDEstimates.ballCount_projScale_le
import Submission.Work.HP.MDEstimates.lam_projScale_le
import Submission.Work.HP.MDEstimates.rk_projScale
import Submission.Work.HP.MDEstimates.detL_le_prod_lam

set_option maxHeartbeats 800000

/-!
# `Work.HP.MDEstimates.ball_count_R0`

The lattice point count of Browning--Le Boudec--Sawin, *The Hasse principle for random Fano
hypersurfaces* (Annals 2023), Lemma R0 (second part, with `j₀ = 0`, `M = J = 1/2`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.MDEstimates

open Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A shortest nonzero vector of a nonzero integral lattice exists, and its norm is `lam L 1`. -/
lemma exists_short_vec (L : Submodule ℤ (ι → ℤ)) (hne : L ≠ ⊥) :
    ∃ u : ι → ℤ, u ∈ L ∧ u ≠ 0 ∧ eNorm u = lam L 1 ∧
      ∀ v ∈ L, v ≠ 0 → eNorm u ≤ eNorm v := by
  classical
  obtain ⟨v₀, hv₀L, hv₀ne⟩ := (Submodule.ne_bot_iff L).mp hne
  have hv₀pos : 0 < eNorm v₀ := eNorm_pos_of_ne_zero hv₀ne
  set S : Set (ι → ℤ) := {v | v ∈ L ∧ v ≠ 0 ∧ eNorm v ≤ eNorm v₀} with hS
  have hSfin : S.Finite := by
    refine (Set.Finite.pi fun k : ι => Set.finite_Icc (-⌈eNorm v₀⌉) ⌈eNorm v₀⌉).subset ?_
    intro v hv
    rw [Set.mem_pi]
    intro k _
    obtain ⟨hL, hne', hle⟩ := hv
    rw [Set.mem_Icc]
    have hb : |((v k : ℤ) : ℝ)| ≤ eNorm v₀ := by
      have h1 : ((v k : ℤ) : ℝ) ^ 2 ≤ ∑ i, ((v i : ℤ) : ℝ) ^ 2 :=
        Finset.single_le_sum (fun i _ => sq_nonneg ((v i : ℤ) : ℝ)) (Finset.mem_univ k)
      calc |((v k : ℤ) : ℝ)| = Real.sqrt (((v k : ℤ) : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (∑ i, ((v i : ℤ) : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
        _ = eNorm v := rfl
        _ ≤ eNorm v₀ := hle
    obtain ⟨hlo, hhi⟩ := abs_le.mp hb
    constructor
    · have h : ((-⌈eNorm v₀⌉ : ℤ) : ℝ) ≤ ((v k : ℤ) : ℝ) := by
        push_cast
        exact le_trans (neg_le_neg (Int.le_ceil _)) hlo
      exact_mod_cast h
    · have h : ((v k : ℤ) : ℝ) ≤ ((⌈eNorm v₀⌉ : ℤ) : ℝ) := le_trans hhi (Int.le_ceil _)
      exact_mod_cast h
  have hSne : S.Nonempty := ⟨v₀, hv₀L, hv₀ne, le_refl _⟩
  obtain ⟨u, huS, hmin⟩ := Set.exists_min_image S (fun v => eNorm v) hSfin hSne
  obtain ⟨huL, hune, hue₀⟩ := huS
  refine ⟨u, huL, hune, ?_, ?_⟩
  · refine le_antisymm ?_ (lam_one_le_eNorm L huL hune)
    rw [lam_eq_sInf]
    refine le_csInf ⟨eNorm u, ?_⟩ ?_
    · exact ⟨eNorm_nonneg u, fun _ : Fin 1 => u, fun _ => huL,
        by rw [linearIndependent_unique_iff]; exact hune, fun _ => le_refl _⟩
    · rintro r ⟨hr0, g, hgL, hgind, hgr⟩
      have h0 : g 0 ≠ 0 := hgind.ne_zero 0
      have hgu : eNorm u ≤ eNorm (g 0) := by
        by_cases hle : eNorm (g 0) ≤ eNorm v₀
        · exact hmin (g 0) ⟨hgL 0, h0, hle⟩
        · exact le_trans hue₀ (le_of_lt (lt_of_not_ge hle))
      exact le_trans hgu (hgr 0)
  · intro v hvL hvne
    by_cases hle : eNorm v ≤ eNorm v₀
    · exact hmin v ⟨hvL, hvne, hle⟩
    · exact le_trans hue₀ (le_of_lt (lt_of_not_ge hle))

/-- The successive minima of an integral lattice are at least `1`. -/
lemma one_le_lam (L : Submodule ℤ (ι → ℤ)) {i : ℕ} (hi : 1 ≤ i) (hiR : i ≤ rk L) :
    1 ≤ lam L i := by
  rw [lam_eq_sInf]
  refine le_csInf (lamSet_nonempty L hiR) ?_
  rintro r ⟨hr0, f, hfL, hfind, hfr⟩
  exact le_trans (one_le_eNorm (hfind.ne_zero ⟨0, hi⟩)) (hfr ⟨0, hi⟩)

/-- **Conversion of Schmidt's sum bound into the form of Lemma R0.** -/
theorem sum_le_target {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (R j : ℕ) (Y T : ℝ),
      rk L = R → 1 ≤ R → j ≤ R - 1 → 1 ≤ T → T ≤ Y → lam L R ≤ Y → 0 < detL L →
      detL L ≤ ∏ i ∈ Finset.range R, lam L (i + 1) →
      (∑ k ∈ Finset.range (R + 1), T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1))
        ≤ K * (T ^ (R - j) * Y ^ j / detL L + T ^ (R - 1 - j)) := by
  refine ⟨2 * (Fintype.card ι : ℝ) + 1, by positivity, ?_⟩
  intro L R j Y T hrk hR hj hT hTY hlamR hdet hdetle
  have hlam1 : ∀ i, 1 ≤ i → i ≤ R → 1 ≤ lam L i := fun i hi hiR =>
    one_le_lam L hi (by rw [hrk]; exact hiR)
  set f : ℕ → ℝ := fun k => T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) with hf
  have hcard : (R : ℝ) ≤ (Fintype.card ι : ℝ) := by
    have h := rk_le_card L; rw [hrk] at h; exact_mod_cast h
  have hRrk : R ≤ rk L := by rw [hrk]
  have hY1 : 1 ≤ Y := le_trans hT hTY
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
  have hlampos : ∀ i, 1 ≤ i → i ≤ R → 0 < lam L i := fun i hi1 hiR =>
    lt_of_lt_of_le one_pos (hlam1 i hi1 hiR)
  have hlamle : ∀ i, i ≤ R → lam L i ≤ Y := fun i hi =>
    le_trans (lam_mono L hi hRrk) hlamR
  have hPpos : ∀ k, k ≤ R → 0 < ∏ i ∈ Finset.range k, lam L (i + 1) := by
    intro k hk
    refine Finset.prod_pos fun i hi => ?_
    exact hlampos (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)
  have hP1 : ∀ k, k ≤ R → 1 ≤ ∏ i ∈ Finset.range k, lam L (i + 1) := by
    intro k hk
    refine Finset.one_le_prod₀ fun i hi => ?_
    exact hlam1 (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)
  have hsplit : ∑ k ∈ Finset.range (R + 1), f k
      = (∑ k ∈ Finset.range (R - j), f k)
        + (∑ k ∈ Finset.range (j + 1), f ((R - j) + k)) := by
    have h : R + 1 = (R - j) + (j + 1) := by omega
    rw [h, Finset.sum_range_add]
  rw [hsplit]
  have hfirst : ∑ k ∈ Finset.range (R - j), f k ≤ (R : ℝ) * T ^ (R - 1 - j) := by
    have h1 : ∀ k ∈ Finset.range (R - j), f k ≤ T ^ (R - 1 - j) := by
      intro k hk
      have hkR : k ≤ R - 1 - j := by
        have h1 := Finset.mem_range.mp hk
        omega
      have hk1 : f k ≤ T ^ k := by
        rw [hf]
        simp only
        rw [div_le_iff₀ (hPpos k (by omega))]
        calc T ^ k = T ^ k * 1 := by ring
          _ ≤ T ^ k * ∏ i ∈ Finset.range k, lam L (i + 1) :=
              mul_le_mul_of_nonneg_left (hP1 k (by omega)) (by positivity)
      exact le_trans hk1 (pow_le_pow_right₀ hT hkR)
    calc ∑ k ∈ Finset.range (R - j), f k ≤ ∑ _k ∈ Finset.range (R - j), T ^ (R - 1 - j) :=
          Finset.sum_le_sum h1
      _ = ((R - j : ℕ) : ℝ) * T ^ (R - 1 - j) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (R : ℝ) * T ^ (R - 1 - j) := by
          have hle : ((R - j : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast Nat.sub_le R j
          exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hsecond : ∑ k ∈ Finset.range (j + 1), f ((R - j) + k)
      ≤ (R : ℝ) * (T ^ (R - j) * Y ^ j / detL L) := by
    have h2 : ∀ k ∈ Finset.range (j + 1), f ((R - j) + k) ≤ T ^ (R - j) * Y ^ j / detL L := by
      intro k hk
      have hkj : k ≤ j := by have := Finset.mem_range.mp hk; omega
      set m : ℕ := (R - j) + k with hm
      have hmge : R - j ≤ m := by omega
      have hmR : m ≤ R := by omega
      have hfac : ∏ i ∈ Finset.range R, lam L (i + 1)
          = (∏ i ∈ Finset.range m, lam L (i + 1))
            * ∏ i ∈ Finset.range (R - m), lam L (i + m + 1) := by
        have h := Finset.prod_range_add (fun i => lam L (i + 1)) m (R - m)
        rw [Nat.add_sub_of_le hmR] at h
        rw [h]
        congr 1
        exact Finset.prod_congr rfl fun i _ => by congr 1; omega
      have htail : ∏ i ∈ Finset.range (R - m), lam L (i + m + 1) ≤ Y ^ (R - m) := by
        have h0 : ∀ i ∈ Finset.range (R - m), (0 : ℝ) ≤ lam L (i + m + 1) := by
          intro i hi
          exact le_of_lt (hlampos (i + m + 1) (by omega) (by have := Finset.mem_range.mp hi; omega))
        have h1 : ∀ i ∈ Finset.range (R - m), lam L (i + m + 1) ≤ Y := by
          intro i hi
          exact hlamle (i + m + 1) (by have := Finset.mem_range.mp hi; omega)
        calc ∏ i ∈ Finset.range (R - m), lam L (i + m + 1)
            ≤ ∏ _i ∈ Finset.range (R - m), Y := Finset.prod_le_prod₀ h0 h1
          _ = Y ^ (R - m) := by rw [Finset.prod_const, Finset.card_range]
      have hdetm : detL L ≤ (∏ i ∈ Finset.range m, lam L (i + 1)) * Y ^ (R - m) := by
        rw [hfac] at hdetle
        exact le_trans hdetle (mul_le_mul_of_nonneg_left htail (le_of_lt (hPpos m hmR)))
      have hstep : f m = T ^ m / (∏ i ∈ Finset.range m, lam L (i + 1)) := by simp only [hf]
      rw [hstep]
      have hle1 : T ^ m / (∏ i ∈ Finset.range m, lam L (i + 1))
          ≤ T ^ m * Y ^ (R - m) / detL L := by
        rw [div_le_div_iff₀ (hPpos m hmR) hdet]
        calc T ^ m * detL L
            ≤ T ^ m * ((∏ i ∈ Finset.range m, lam L (i + 1)) * Y ^ (R - m)) :=
              mul_le_mul_of_nonneg_left hdetm (by positivity)
          _ = T ^ m * Y ^ (R - m) * ∏ i ∈ Finset.range m, lam L (i + 1) := by ring
      refine le_trans hle1 (div_le_div_of_nonneg_right ?_ hdet.le)
      have hkey : T ^ (m - (R - j)) ≤ Y ^ (m - (R - j)) :=
        pow_le_pow_left₀ (le_of_lt hTpos) hTY _
      have hexp : T ^ m * Y ^ (R - m) ≤ T ^ (R - j) * Y ^ j := by
        have h1 : T ^ (R - j) * T ^ (m - (R - j)) = T ^ m := by
          rw [← pow_add]; congr 1; omega
        have h2 : Y ^ (m - (R - j)) * Y ^ (R - m) = Y ^ j := by
          rw [← pow_add]; congr 1; omega
        calc T ^ m * Y ^ (R - m)
            = T ^ (R - j) * (T ^ (m - (R - j)) * Y ^ (R - m)) := by
              rw [← h1]; ring
          _ ≤ T ^ (R - j) * (Y ^ (m - (R - j)) * Y ^ (R - m)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_right hkey (by positivity)
          _ = T ^ (R - j) * Y ^ j := by rw [h2]
      exact hexp
    calc ∑ k ∈ Finset.range (j + 1), f ((R - j) + k)
        ≤ ∑ _k ∈ Finset.range (j + 1), T ^ (R - j) * Y ^ j / detL L := Finset.sum_le_sum h2
      _ = ((j + 1 : ℕ) : ℝ) * (T ^ (R - j) * Y ^ j / detL L) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (R : ℝ) * (T ^ (R - j) * Y ^ j / detL L) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : j + 1 ≤ R := by omega
          exact_mod_cast this
  calc (∑ k ∈ Finset.range (R - j), f k) + (∑ k ∈ Finset.range (j + 1), f ((R - j) + k))
      ≤ (R : ℝ) * T ^ (R - 1 - j) + (R : ℝ) * (T ^ (R - j) * Y ^ j / detL L) :=
        add_le_add hfirst hsecond
    _ = (R : ℝ) * (T ^ (R - j) * Y ^ j / detL L + T ^ (R - 1 - j)) := by ring
    _ ≤ (2 * (Fintype.card ι : ℝ) + 1) * (T ^ (R - j) * Y ^ j / detL L + T ^ (R - 1 - j)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith [show (0:ℝ) ≤ T ^ (R - j) * Y ^ j / detL L by positivity, show (0:ℝ) ≤ T ^ (R - 1 - j) by positivity])
        linarith [hcard]

lemma eq_bot_of_rk_eq_zero {L : Submodule ℤ (ι → ℤ)} (h : rk L = 0) : L = ⊥ := by
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L
  have hn : n = 0 := by
    have h1 : Module.finrank ℤ L = n := by
      rw [Module.finrank_eq_card_basis b]; simp
    rw [← h1]; exact h
  subst hn
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hzero : b.repr ⟨x, hx⟩ = 0 := Subsingleton.elim _ _
  have h2 : (⟨x, hx⟩ : L) = 0 := by
    have := congrArg b.repr.symm hzero
    simpa using this
  exact congrArg Subtype.val h2

lemma ballCount_bot (T : ℝ) (hT : 0 ≤ T) : ballCount (⊥ : Submodule ℤ (ι → ℤ)) T = 1 := by
  rw [ballCount]
  have hset : {v : ι → ℤ | v ∈ (⊥ : Submodule ℤ (ι → ℤ)) ∧ eNorm v ≤ T} = {0} := by
    ext v
    constructor
    · rintro ⟨hv, -⟩
      simpa using hv
    · rintro rfl
      refine ⟨Submodule.zero_mem _, ?_⟩
      simpa [eNorm] using hT
  rw [hset, Set.ncard_singleton]

/-- Schmidt's upper bound in sum form, with a constant depending only on the rank bound. -/
theorem ballCount_sum_bound (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)), rk L ≤ N → ∀ T : ℝ, 1 ≤ T →
      (ballCount L T : ℝ) ≤ K * ∑ k ∈ Finset.range (rk L + 1),
        T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := by
  induction N with
  | zero =>
    refine ⟨1, one_pos, ?_⟩
    intro L hL T hT
    have hL0 : rk L = 0 := Nat.le_zero.mp hL
    have hbot : L = ⊥ := eq_bot_of_rk_eq_zero hL0
    subst hbot
    rw [ballCount_bot T (by linarith), hL0]
    norm_num
  | succ n ih =>
    obtain ⟨K, hKpos, hK⟩ := ih
    set d : ℝ := 2 / Real.sqrt 3 with hd
    have hsqpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hdc : d * (Real.sqrt 3 / 2) = 1 := by rw [hd]; field_simp
    have hd1 : 1 ≤ d := by
      rw [hd, le_div_iff₀ hsqpos]
      have h2 : Real.sqrt 3 < 2 := by
        rw [show (2:ℝ) = Real.sqrt 4 by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
    have hdpos : 0 < d := lt_of_lt_of_le one_pos hd1
    refine ⟨K * (3 * d ^ n), by positivity, ?_⟩
    intro L hL T hT
    have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
    by_cases hle : rk L ≤ n
    · have h1 := hK L hle T hT
      have hSnn : 0 ≤ ∑ k ∈ Finset.range (rk L + 1),
          T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) :=
        Finset.sum_nonneg fun k _ => div_nonneg (pow_nonneg (by linarith) k)
          (Finset.prod_nonneg fun i _ => lam_nonneg L (i + 1))
      refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ hSnn)
      refine le_mul_of_one_le_right hKpos.le ?_
      have : (1:ℝ) ≤ d ^ n := one_le_pow₀ hd1
      nlinarith
    · have hrk : rk L = n + 1 := by omega
      have hne : L ≠ ⊥ := by
        intro h
        have h0 : rk (⊥ : Submodule ℤ (ι → ℤ)) = 0 := by rw [rk]; simp
        rw [h, h0] at hrk
        omega
      obtain ⟨u, huL, hu0, hulam, hshort⟩ := exists_short_vec L hne
      set lam1 : ℝ := eNorm u with hlam1
      have hlam1pos : 0 < lam1 := by rw [hlam1]; exact eNorm_pos_of_ne_zero hu0
      have hlam1eq : lam1 = lam L 1 := by rw [hlam1]; exact hulam
      have hlam1ge : 1 ≤ lam1 := by rw [hlam1eq]; exact one_le_lam L le_rfl (by omega)
      set L2 : Submodule ℤ (ι → ℤ) := Submodule.map (projScale u) L with hL2
      have hrk2 : rk L2 = n := by
        rw [hL2, rk_projScale L u huL hu0 hshort, hrk]; omega
      have hcnt := ballCount_projScale_le L u huL hu0 hshort T (by linarith)
      have hT2 : 1 ≤ lam1 ^ 2 * T := by nlinarith
      have hIH := hK L2 (by omega) (lam1 ^ 2 * T) hT2
      set t : ℕ → ℝ := fun k => T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) with ht
      set gg : ℕ → ℝ := fun k => T ^ k / ∏ i ∈ Finset.range k, lam L (i + 2) with hgg
      set g : ℕ → ℝ := fun k => (lam1 ^ 2 * T) ^ k / ∏ i ∈ Finset.range k, lam L2 (i + 1) with hgd
      set S : ℝ := ∑ k ∈ Finset.range (n + 2), t k with hS
      have htnn : ∀ k, 0 ≤ t k := fun k => div_nonneg (pow_nonneg (by linarith) k)
        (Finset.prod_nonneg fun i _ => lam_nonneg L (i + 1))
      have hSnn : 0 ≤ S := by
        rw [hS]; exact Finset.sum_nonneg fun k _ => htnn k
      have hg1 : ∀ k, k ≤ n → g k ≤ d ^ k * gg k := by
        intro k hk
        have hrel : ∀ i ∈ Finset.range k,
            Real.sqrt 3 / 2 * lam1 ^ 2 * lam L (i + 2) ≤ lam L2 (i + 1) := by
          intro i hi
          have hi' : i < k := Finset.mem_range.mp hi
          have hidx : i + 1 ≤ rk L - 1 := by
            have h1 : i + 1 ≤ k := by omega
            have h2 : k ≤ rk L - 1 := by omega
            exact le_trans h1 h2
          have h := lam_projScale_le L u huL hu0 hshort (i + 1) (by omega) hidx
          rw [← hlam1] at h
          exact h
        have hP2 : (Real.sqrt 3 / 2) ^ k * lam1 ^ (2 * k) *
              ∏ i ∈ Finset.range k, lam L (i + 2)
            ≤ ∏ i ∈ Finset.range k, lam L2 (i + 1) := by
          have hprod : ∏ i ∈ Finset.range k, (Real.sqrt 3 / 2 * lam1 ^ 2 * lam L (i + 2))
              ≤ ∏ i ∈ Finset.range k, lam L2 (i + 1) := by
            refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => hrel i hi)
            exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
              (lam_nonneg L (i + 2))
          have heq : ∏ i ∈ Finset.range k, (Real.sqrt 3 / 2 * lam1 ^ 2 * lam L (i + 2))
              = (Real.sqrt 3 / 2) ^ k * lam1 ^ (2 * k)
                * ∏ i ∈ Finset.range k, lam L (i + 2) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, mul_pow, pow_mul]
          rw [← heq]; exact hprod
        have h3 : 0 < ∏ i ∈ Finset.range k, lam L (i + 2) := by
          refine Finset.prod_pos fun i hi => ?_
          have hi' : i < k := Finset.mem_range.mp hi
          exact lt_of_lt_of_le one_pos (one_le_lam L (by omega) (by omega))
        have hP2pos : 0 < ∏ i ∈ Finset.range k, lam L2 (i + 1) :=
          lt_of_lt_of_le (mul_pos (mul_pos (by positivity) (pow_pos hlam1pos _)) h3) hP2
        have hdck : d ^ k * (Real.sqrt 3 / 2) ^ k = 1 := by rw [← mul_pow, hdc, one_pow]
        have hcross : lam1 ^ (2 * k) * ∏ i ∈ Finset.range k, lam L (i + 2)
            ≤ d ^ k * ∏ i ∈ Finset.range k, lam L2 (i + 1) := by
          calc lam1 ^ (2 * k) * ∏ i ∈ Finset.range k, lam L (i + 2)
              = (d ^ k * (Real.sqrt 3 / 2) ^ k)
                  * (lam1 ^ (2 * k) * ∏ i ∈ Finset.range k, lam L (i + 2)) := by
                rw [hdck, one_mul]
            _ = d ^ k * ((Real.sqrt 3 / 2) ^ k * lam1 ^ (2 * k)
                  * ∏ i ∈ Finset.range k, lam L (i + 2)) := by ring
            _ ≤ d ^ k * ∏ i ∈ Finset.range k, lam L2 (i + 1) :=
                mul_le_mul_of_nonneg_left hP2 (pow_nonneg hdpos.le k)
        calc g k = lam1 ^ (2 * k) * T ^ k / ∏ i ∈ Finset.range k, lam L2 (i + 1) := by
              simp only [hgd]
              rw [mul_pow, pow_mul]
          _ ≤ d ^ k * T ^ k / ∏ i ∈ Finset.range k, lam L (i + 2) := by
              rw [div_le_div_iff₀ hP2pos h3]
              calc lam1 ^ (2 * k) * T ^ k * ∏ i ∈ Finset.range k, lam L (i + 2)
                  = T ^ k * (lam1 ^ (2 * k) * ∏ i ∈ Finset.range k, lam L (i + 2)) := by ring
                _ ≤ T ^ k * (d ^ k * ∏ i ∈ Finset.range k, lam L2 (i + 1)) :=
                    mul_le_mul_of_nonneg_left hcross (pow_nonneg hTpos.le k)
                _ = d ^ k * T ^ k * ∏ i ∈ Finset.range k, lam L2 (i + 1) := by ring
          _ = d ^ k * gg k := by simp only [hgg]; ring
      have hg2 : ∀ k, k ≤ n → gg k ≤ t k := by
        intro k hk
        have hle : ∏ i ∈ Finset.range k, lam L (i + 1) ≤ ∏ i ∈ Finset.range k, lam L (i + 2) := by
          refine Finset.prod_le_prod₀ (fun i _ => lam_nonneg L (i + 1)) fun i hi => ?_
          have hi' : i < k := Finset.mem_range.mp hi
          have hidx : i + 2 ≤ rk L := by omega
          exact lam_mono L (by omega) hidx
        have hp1 : 0 < ∏ i ∈ Finset.range k, lam L (i + 1) := by
          refine Finset.prod_pos fun i hi => ?_
          have hi' : i < k := Finset.mem_range.mp hi
          have hidx : i + 1 ≤ rk L := by omega
          exact lt_of_lt_of_le one_pos (one_le_lam L (by omega) hidx)
        have hp2 : 0 < ∏ i ∈ Finset.range k, lam L (i + 2) := by
          refine Finset.prod_pos fun i hi => ?_
          have hi' : i < k := Finset.mem_range.mp hi
          have hidx : i + 2 ≤ rk L := by omega
          exact lt_of_lt_of_le one_pos (one_le_lam L (by omega) hidx)
        simp only [hgg, ht]
        exact div_le_div_of_nonneg_left (pow_nonneg hTpos.le k) hp1 hle
      have hg3 : ∀ k, k ≤ n → T / lam1 * gg k = t (k + 1) := by
        intro k hk
        have h1 : lam L 1 ≠ 0 := by rw [← hlam1eq]; exact ne_of_gt hlam1pos
        have h2 : (∏ i ∈ Finset.range k, lam L (i + 2)) ≠ 0 := by
          refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
          have hi' : i < k := Finset.mem_range.mp hi
          have hidx : i + 2 ≤ rk L := by omega
          exact ne_of_gt (lt_of_lt_of_le one_pos (one_le_lam L (by omega) hidx))
        have h3 : T ≠ 0 := ne_of_gt hTpos
        simp only [hgg, ht, hlam1eq, Finset.prod_range_succ']
        field_simp
        ring
      have hggnn : ∀ k, 0 ≤ gg k := fun k => div_nonneg (pow_nonneg hTpos.le k)
        (Finset.prod_nonneg fun i _ => lam_nonneg L (i + 2))
      have hgs : ∑ k ∈ Finset.range (n + 1), g k ≤ d ^ n * S := by
        have h1 : ∑ k ∈ Finset.range (n + 1), g k
            ≤ ∑ k ∈ Finset.range (n + 1), d ^ n * gg k := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
          refine le_trans (hg1 k hk') ?_
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 hk') (hggnn k)
        have h2 : ∑ k ∈ Finset.range (n + 1), d ^ n * gg k
            ≤ ∑ k ∈ Finset.range (n + 1), d ^ n * t k := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
          exact mul_le_mul_of_nonneg_left (hg2 k hk') (pow_nonneg hdpos.le n)
        have h3 : ∑ k ∈ Finset.range (n + 1), d ^ n * t k
            = d ^ n * ∑ k ∈ Finset.range (n + 1), t k := by rw [Finset.mul_sum]
        have h4 : ∑ k ∈ Finset.range (n + 1), t k ≤ S := by
          rw [hS]
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega)) ?_
          intro i _ _; exact htnn i
        calc ∑ k ∈ Finset.range (n + 1), g k ≤ ∑ k ∈ Finset.range (n + 1), d ^ n * gg k := h1
          _ ≤ ∑ k ∈ Finset.range (n + 1), d ^ n * t k := h2
          _ = d ^ n * ∑ k ∈ Finset.range (n + 1), t k := h3
          _ ≤ d ^ n * S := mul_le_mul_of_nonneg_left h4 (pow_nonneg hdpos.le n)
      have hgT : T / lam1 * (∑ k ∈ Finset.range (n + 1), g k) ≤ d ^ n * S := by
        have h1 : T / lam1 * (∑ k ∈ Finset.range (n + 1), g k)
            ≤ ∑ k ∈ Finset.range (n + 1), d ^ n * t (k + 1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
          calc T / lam1 * g k ≤ T / lam1 * (d ^ n * gg k) := by
                refine mul_le_mul_of_nonneg_left (le_trans (hg1 k hk') ?_) (div_nonneg hTpos.le hlam1pos.le)
                exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hd1 hk') (hggnn k)
            _ = d ^ n * (T / lam1 * gg k) := by ring
            _ = d ^ n * t (k + 1) := by rw [hg3 k hk']
        have h2 : ∑ k ∈ Finset.range (n + 1), d ^ n * t (k + 1) ≤ d ^ n * S := by
          have h5 : S = (∑ k ∈ Finset.range (n + 1), t (k + 1)) + t 0 := by
            rw [hS, Finset.sum_range_succ']
          rw [h5, ← Finset.mul_sum, mul_add]
          exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg hdpos.le n) (htnn 0))
        exact le_trans h1 h2
      have hkey : (2 * T / lam1 + 1) * (∑ k ∈ Finset.range (n + 1), g k) ≤ 3 * d ^ n * S := by
        have e : (2 * T / lam1 + 1) * (∑ k ∈ Finset.range (n + 1), g k)
            = 2 * (T / lam1 * (∑ k ∈ Finset.range (n + 1), g k))
              + (∑ k ∈ Finset.range (n + 1), g k) := by ring
        rw [e]
        linarith [hgT, hgs]
      have hfinal : (ballCount L T : ℝ)
          ≤ K * (3 * d ^ n) * ∑ k ∈ Finset.range (rk L + 1),
              T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := by
        calc (ballCount L T : ℝ) ≤ (2 * T / lam1 + 1) * (ballCount L2 (lam1 ^ 2 * T) : ℝ) := hcnt
          _ ≤ (2 * T / lam1 + 1) * (K * ∑ k ∈ Finset.range (rk L2 + 1), g k) := by
                refine mul_le_mul_of_nonneg_left hIH ?_
                positivity
          _ = K * ((2 * T / lam1 + 1) * ∑ k ∈ Finset.range (n + 1), g k) := by
                rw [hrk2]; ring
          _ ≤ K * (3 * d ^ n * S) := mul_le_mul_of_nonneg_left hkey hKpos.le
          _ = K * (3 * d ^ n) * ∑ k ∈ Finset.range (rk L + 1),
                T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := by
                rw [hS, ht, hrk]; ring
      exact hfinal

/-- The main theorem. -/
theorem ball_count_R0 {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (R j : ℕ) (Y T : ℝ),
      rk L = R → 1 ≤ R → j ≤ R - 1 → 1 ≤ T → T ≤ Y → lam L R ≤ Y → 0 < detL L →
      (ballCount L T : ℝ) ≤ K * (T ^ (R - j) * Y ^ j / detL L + T ^ (R - 1 - j)) := by
  obtain ⟨K1, hK1pos, hK1⟩ := ballCount_sum_bound (ι := ι) (Fintype.card ι)
  obtain ⟨K2, hK2pos, hK2⟩ := sum_le_target (ι := ι)
  refine ⟨K1 * K2, mul_pos hK1pos hK2pos, ?_⟩
  intro L R j Y T hrk hR hj hT hTY hlam hdet
  have h1 := hK1 L (rk_le_card L) T hT
  rw [hrk] at h1
  have h2 := hK2 L R j Y T hrk hR hj hT hTY hlam hdet (by rw [← hrk]; exact detL_le_prod_lam L)
  calc (ballCount L T : ℝ) ≤ K1 * ∑ k ∈ Finset.range (R + 1),
        T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := h1
    _ ≤ K1 * (K2 * (T ^ (R - j) * Y ^ j / detL L + T ^ (R - 1 - j))) :=
        mul_le_mul_of_nonneg_left h2 hK1pos.le
    _ = K1 * K2 * (T ^ (R - j) * Y ^ j / detL L + T ^ (R - 1 - j)) := by ring


end Work.HP.MDEstimates
