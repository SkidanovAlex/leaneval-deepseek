import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Work.GM.Energy.LocalConstancy.localize_smoothedPoly
import Submission.Work.GM.Energy.LocalConstancy.localize_dirichlet
import Submission.Work.GM.Energy.Moments.second_moment_Rfun
import Submission.Work.GM.Energy.EnergyCore.gcd_small
import Submission.Work.GM.Energy.RMoments.Rfun_integral_sq
import Submission.Work.GM.Energy.RMoments.Rfun_integral_pow4
import Submission.Work.GM.Energy.Basic.energy_le_three_mul_cube
import Submission.Work.GM.Energy.Basic.card_sq_le_energy
import Submission.Work.GM.Trace.sep_card_le
import Submission.Work.GM.Energy.EnergyCore2.kpow_facts
import Submission.Work.GM.Energy.EnergyCore2.beta_le
import Submission.Work.GM.Energy.EnergyCore2.arith_A
import Submission.Work.GM.Energy.EnergyCore2.arith_B
import Submission.Work.GM.Energy.EnergyCore2.assembly
import Submission.Work.GM.Energy.EnergyCore2.fourth_moment_Kfree

-- NOTE (imports).  Unlike the original skeleton of this file, `Submission.Work.GM.Energy.EnergyCore.gcd_large` is NOT imported: it is mentioned in the docstring
-- below only as the intended filler of the `hL9` hypothesis, which is taken as a hypothesis here, and its
-- import closure together with that of `EnergyCore.gcd_small` defines `Work.GM.Energy.EnergyCore.card_le_add_one`
-- twice, which is an environment error.  The proof uses `fourth_moment_Kfree` (the `K`-free fourth moment)
-- to build the fourth-moment input of `hL9`.

namespace Work.GM.Energy.EnergyCore2

set_option maxHeartbeats 1600000

/-- **GM §11, Proposition 11.1 (assembly), with the fourth-moment input in the `K`-free defect form.**
Identical statement to `EnergyCore2.assembly` EXCEPT for the `hL9` slot: instead of the `K`-exposed
fourth moment (whose window cost `(K+1)^2` cannot be absorbed -- see the refuted
`GM/Energy/EnergyCore/gcd_large_K`), the slot now takes the *`K`-free* second and fourth moment
hypotheses at a single free exponent `ε₂`.  The proven `EnergyCore.gcd_large` inhabits it:
`hL9 := fun ε₂ hε₂ => Work.GM.Energy.EnergyCore.gcd_large ε₂ hε₂` (note `gcd_large`'s `C₄`/`C₂` are
T-uniform constants, which is exactly what the `K`-free `fourth_moment_Kfree` supplies at exponent
`ε₂ := ε + 2η`).  Concretely this is a copy of the sorry-free file
`GM/Energy/EnergyCore2/assembly.lean` (imported here for its `energy_core`) with these edits, and
nothing else:

* the `hL4`, `hL7` slots and the conclusion are byte-for-byte the `assembly` ones (so the same
  fillers `EnergyCore2.energy_le_R_cube`, `RLocal2.Rfun_local` apply);
* body: the parameter bookkeeping becomes `m ≥ 768/δ`, `ε := δ/32`, `η := δ/64`,
  `ε₂ := ε + 2*η` (= `δ/16`), `hε₂pos`, `hmη : 12 ≤ m*η` (from `m ≥ 768/δ`), and
  `hexp : 12/m + 4ε₂ ≤ δ` (since `12/m ≤ δ/64` and `4ε₂ = δ/4`); the old `hmeps` line disappears;
* `obtain ⟨C4b, hC4bpos, hfourthc⟩ := fourth_moment_Kfree hHB m hm2 ε η hεpos hηpos hmη`
  (instead of `fourth_moment_Rfun`), and `obtain ⟨C9, hC9pos, hL9c⟩ := hL9 ε₂ hε₂pos`;
* the two moment hypotheses handed to `hL9c`: the second-moment one is `hsecondc` *inflated* from
  exponent `ε` to `ε₂` (`T^ε ≤ T^{ε₂}` for `T ≥ 1`), the fourth-moment one is
  `hfourthc CD hCDpos hCDb` (with `CD` the constant of `LocalConstancy.localize_dirichlet`, used only
  as the `Cloc` of the locality hypothesis) with constant `C4b * (CD+1)^2`;
* `hL9app`/`hL9comb`: exponent `(N:ℝ)^(2*ε₂)`, constant
  `C9 * (C2+1)^{1/2} * (C4b*(CD+1)^2+1)^{1/2}`; hence
  `l1 := C9 * (C2+1)^{1/2} * (C4b*(CD+1)^2+1)^{1/2} * 2`, and the `energy_core` call uses
  `(ε := ε₂)`, `(C4b := C4b*(CD+1)^2)`, `(CD := 1)` (so `hl1eq` holds with the factor `(1+1)`), and
  `gcd_small` is called with exponent `ε₂` (or its `N^ε` factors are inflated to `N^{ε₂}`) so that
  the `hgs` hypothesis of `energy_core` matches `ε := ε₂`;
* everything else in the middle of the proof is unchanged. -/
theorem assembly_eta
    (hHB : Submission.GM.HBStatement)
    (hL4 : ∀ (m : ℕ), 2 ≤ m → ∃ C : ℝ, 0 < C ∧
      ∀ (Cloc : ℝ), 0 < Cloc →
      ∀ (N : ℕ), 1 ≤ N → ∀ (W : Finset ℝ),
        (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) → Submission.GM.Separated W 1 →
      ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      (∀ (K : ℝ), 1 ≤ K → ∀ t : ℝ,
        ‖Submission.LargeValues.smoothedPoly N b t‖ ≤
          Cloc * (∫ u in t - K..t + K, ‖Submission.LargeValues.smoothedPoly N b u‖)
            + Cloc / K ^ (m : ℝ) * (∑ n ∈ Finset.Icc N (2 * N), ‖b n‖)) →
      ∀ (V K : ℝ), 1 ≤ K → 0 < V →
        (∀ t ∈ W, V ≤ ‖Submission.LargeValues.smoothedPoly N b t‖) →
        (Submission.GM.energy W : ℝ) ≤
          C * (Cloc + 1) ^ 2 * (K + 1) ^ 2 / V ^ 2 *
              (∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
                ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3)
          + C * (Cloc + 1) ^ 2 * ((2 * N + 1 : ℝ) / K ^ (m : ℝ)) ^ 2 / V ^ 2
              * (Submission.GM.energy W))
    (hL7 : ∀ (m : ℕ), 2 ≤ m → ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
        (∀ t ∈ W, t ∈ Set.Icc 0 T) → ∀ (v : ℝ), v ∈ Set.Icc (1 / 2 : ℝ) 2 → ∀ (K : ℝ), 1 ≤ K →
          ‖Submission.GM.Rfun W v‖ ≤
            C * T * (∫ v' in v - K / T..v + K / T, ‖Submission.GM.Rfun W v'‖)
              + C / K ^ (m : ℝ) * (W.card : ℝ))
    (hL9 : ∀ (ε₂ : ℝ), 0 < ε₂ →
        ∃ C : ℝ, 0 < C ∧
        ∀ (C₂ : ℝ), 0 < C₂ →
        (∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
          (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
          (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
              ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
            ≤ C₂ * T ^ ε₂ * ((W.card : ℝ) ^ 2 * (M : ℝ) + (W.card : ℝ) * (M : ℝ) ^ 2
                + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (M : ℝ))) →
        ∀ (C₄ : ℝ), 0 < C₄ →
        (∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
          (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
          (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
              ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
            ≤ C₄ * T ^ ε₂ * ((W.card : ℝ) ^ 4 * (M : ℝ)
                + (M : ℝ) ^ 2 * (Submission.GM.energy W : ℝ)
                + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
                    * T ^ ((1 : ℝ) / 2) * (M : ℝ))) →
        ∀ (N : ℕ), 100 ≤ N → ∀ (W : Finset ℝ),
          (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
          Submission.GM.Separated W 1 →
          (∑ n1 ∈ Finset.Icc N (2 * N),
              ∑ n2 ∈ (Finset.Icc N (2 * N)).filter
                (fun n2 => (N : ℝ) ^ 2 / Submission.LargeValues.M N ≤ (Nat.gcd n1 n2 : ℝ)),
              ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3)
            ≤ C * (C₂ + 1) ^ ((1 : ℝ) / 2) * (C₄ + 1) ^ ((1 : ℝ) / 2)
                * (N : ℝ) ^ (2 * ε₂) *
                ((N : ℝ) * (W.card : ℝ) ^ 3
                  + (N : ℝ) * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 4)
                      * (W.card : ℝ) ^ ((21 : ℝ) / 8)
                  + (Submission.GM.energy W : ℝ) ^ ((1 : ℝ) / 2) * (W.card : ℝ) ^ ((1 : ℝ) / 2)
                      * (N : ℝ) ^ 2)) :
    Submission.GM.EnergyStatement := by
  -- ### parameters
  intro δ hδ
  obtain ⟨m, hm2, hmge⟩ : ∃ m : ℕ, 2 ≤ m ∧ 768 / δ ≤ (m : ℝ) := by
    obtain ⟨m₀, hm₀⟩ := exists_nat_ge (768 / δ)
    exact ⟨max 2 m₀, le_max_left 2 m₀, le_trans hm₀ (by exact_mod_cast le_max_right 2 m₀)⟩
  set ε : ℝ := δ / 32 with hεdef
  set η : ℝ := δ / 64 with hηdef
  set ε₂ : ℝ := ε + 2 * η with hε₂def
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hηpos : 0 < η := by rw [hηdef]; linarith
  have hε₂pos : 0 < ε₂ := by rw [hε₂def]; linarith
  have hmη : 12 ≤ (m : ℝ) * η := by
    have h2 : 768 ≤ (m : ℝ) * δ := by
      have h1 : 768 / δ ≤ (m : ℝ) := hmge
      rw [div_le_iff₀ hδ] at h1
      linarith
    rw [hηdef]
    nlinarith
  have hε₂16 : ε₂ = δ / 16 := by rw [hε₂def, hεdef, hηdef]; ring
  have hεε₂ : ε ≤ ε₂ := by rw [hε₂def]; linarith
  have hexp : (12 : ℝ) / (m : ℝ) + 4 * ε₂ ≤ δ := by
    rw [hε₂16]
    have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
    have h1 : (12 : ℝ) / (m : ℝ) ≤ δ / 64 := by
      rw [div_le_iff₀ hmpos]
      have h3 : (δ / 64) * (768 / δ) = 12 := by field_simp; ring
      have h4 := mul_le_mul_of_nonneg_left hmge (by positivity : (0 : ℝ) ≤ δ / 64)
      linarith [h3, h4]
    linarith
  -- ### the inputs
  obtain ⟨C4, hC4pos, hL4c⟩ := hL4 m hm2
  obtain ⟨CS, hCSpos, hCSb⟩ := Work.GM.Energy.LocalConstancy.localize_smoothedPoly m hm2
  obtain ⟨CD, hCDpos, hCDb⟩ := Work.GM.Energy.LocalConstancy.localize_dirichlet m hm2
  obtain ⟨C4b, hC4bpos, hfourthc⟩ :=
    fourth_moment_Kfree hHB m hm2 ε η hεpos hηpos hmη
  obtain ⟨C2, hC2pos, hsecondc⟩ := Work.GM.Energy.Moments.second_moment_Rfun hHB ε hεpos
  obtain ⟨C9, hC9pos, hL9c⟩ := hL9 ε₂ hε₂pos
  obtain ⟨Cg, hCgpos, hgcdsc⟩ := Work.GM.Energy.EnergyCore.gcd_small m hm2 ε₂ hε₂pos
  obtain ⟨C7, hC7pos, hL7c⟩ := hL7 m hm2
  obtain ⟨Cm2, hCm2pos, hL2c⟩ := Work.GM.Energy.RMoments.Rfun_integral_sq
  obtain ⟨Cm4, hCm4pos, hL4ic⟩ := Work.GM.Energy.RMoments.Rfun_integral_pow4
  clear hHB hL4 hL7 hL9
  -- ### the two moment hypotheses at the single exponent `ε₂`
  have hsecond_infl : ∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
      (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
      (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
        ≤ C2 * T ^ ε₂ * ((W.card : ℝ) ^ 2 * (M : ℝ) + (W.card : ℝ) * (M : ℝ) ^ 2
            + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (M : ℝ)) := by
    intro M hM T hT W hW hsep
    refine (hsecondc M hM T hT W hW hsep).trans ?_
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have hTe : T ^ ε ≤ T ^ ε₂ := Real.rpow_le_rpow_of_exponent_le hT hεε₂
    have hXnn : 0 ≤ (W.card : ℝ) ^ 2 * (M : ℝ) + (W.card : ℝ) * (M : ℝ) ^ 2
        + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (M : ℝ) := by
      have h1 : (0 : ℝ) ≤ (W.card : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ (M : ℝ) := by positivity
      have h3 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((5 : ℝ) / 4) := Real.rpow_nonneg h1 _
      have h4 : (0 : ℝ) ≤ T ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hTpos) _
      have h5 : (0 : ℝ) ≤ (M : ℝ) ^ 2 := by positivity
      have h6 : (0 : ℝ) ≤ (W.card : ℝ) ^ 2 := by positivity
      have h7 : (0 : ℝ) ≤ (W.card : ℝ) * (M : ℝ) := by positivity
      have h8 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (M : ℝ) :=
        mul_nonneg (mul_nonneg h3 h4) h2
      have h9 : (0 : ℝ) ≤ (W.card : ℝ) ^ 2 * (M : ℝ) := mul_nonneg h6 h2
      have h10 : (0 : ℝ) ≤ (W.card : ℝ) * (M : ℝ) ^ 2 := mul_nonneg h1 h5
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTe hC2pos.le) hXnn
  have hfourth_infl : ∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
      (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
      (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
        ≤ (C4b * (CD + 1) ^ 2) * T ^ ε₂ * ((W.card : ℝ) ^ 4 * (M : ℝ)
            + (M : ℝ) ^ 2 * (Submission.GM.energy W : ℝ)
            + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
                * T ^ ((1 : ℝ) / 2) * (M : ℝ)) := by
    intro M hM T hT W hW hsep
    have h := hfourthc CD hCDpos hCDb M hM T hT W hW hsep
    rw [show ε₂ = ε + 2 * η from hε₂def]
    exact h
  have hC4bnn : 0 < C4b * (CD + 1) ^ 2 := by positivity
  -- ### the constants
  set CR : ℝ := max C7 (max Cm2 (max Cm4 1)) with hCRdef
  have hC7CR : C7 ≤ CR := by rw [hCRdef]; exact le_max_left _ _
  have hCm2CR : Cm2 ≤ CR := by
    rw [hCRdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCm4CR : Cm4 ≤ CR := by
    rw [hCRdef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCRpos : 0 < CR := lt_of_lt_of_le hC7pos hC7CR
  set Θ : ℝ := 20 * (C4 + 1) * (CS + 1) + 1 with hΘdef
  have hΘ1 : 1 ≤ Θ := by rw [hΘdef]; nlinarith [hC4pos, hCSpos]
  have hΘsq : 400 * C4 * (CS + 1) ^ 2 ≤ Θ ^ 2 := by
    rw [hΘdef]
    nlinarith [hC4pos, hCSpos, mul_pos hC4pos hCSpos, sq_nonneg (C4 + 1), sq_nonneg (CS + 1),
      sq_nonneg ((C4 + 1) * (CS + 1))]
  set a1 : ℝ := C4 * (CS + 1) ^ 2 with ha1def
  have ha1nn : 0 ≤ a1 := by rw [ha1def]; positivity
  set g1 : ℝ := Cg * (CR + 1) ^ 4 with hg1def
  have hg1nn : 0 ≤ g1 := by rw [hg1def]; positivity
  set l1 : ℝ := C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2) * 2
    with hl1def
  have hl1nn : 0 ≤ l1 := by rw [hl1def]; positivity
  have hl1eq : l1 = C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2)
      * (1 + 1) := by
    rw [hl1def]; ring
  set CA : ℝ := 262144 * (a1 + 1) ^ 2 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12 with hCAdef
  set CB : ℝ := 512 * (a1 + 1) * (g1 + 1) * (l1 + 1) * (Θ + 1) ^ 6 with hCBdef
  set CF : ℝ := max 8 (CA + CB) with hCFdef
  have hCF8 : 8 ≤ CF := by rw [hCFdef]; exact le_max_left _ _
  refine ⟨CF, lt_of_lt_of_le (by norm_num) hCF8, 100, ?_⟩
  intro N hN100 W hWsub hsep b hb V hVpos hbig
  have hN1 : 1 ≤ N := by omega
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hWsubMN : ∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N) := hWsub
  set T : ℝ := Submission.LargeValues.M N with hTdef
  have hWsubT : ∀ t ∈ W, t ∈ Set.Icc 0 T := by
    intro t ht; rw [hTdef]; exact hWsubMN t ht
  have hT1 : 1 ≤ T := by rw [hTdef]; exact Submission.LargeValues.M_ge_one hN1
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hT3 : T ^ 3 ≤ (N : ℝ) ^ 4 := by rw [hTdef]; exact M_pow_three_le N hN1
  set κ : ℝ := (W.card : ℝ) with hκdef
  have hκnn : 0 ≤ κ := by rw [hκdef]; positivity
  set E : ℝ := (Submission.GM.energy W : ℝ) with hEdef
  have hEnn : 0 ≤ E := by rw [hEdef]; positivity
  set K : ℝ := Θ * (N : ℝ) ^ (1 / (m : ℝ)) with hKdef
  set Λ : ℝ := (N : ℝ) ^ ((12 : ℝ) / (m : ℝ) + 4 * ε₂) with hΛdef
  have hΛle : Λ ≤ (N : ℝ) ^ δ := by
    rw [hΛdef]
    exact Real.rpow_le_rpow_of_exponent_le hN1R hexp
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    exact (kpow_facts (Θ := Θ) (N := (N : ℝ)) (mm := m) hΘ1 hN1R (by omega)).1
  by_cases hVge : 1 ≤ V
  · -- ### Main case
    have hloc : ∀ (K' : ℝ), 1 ≤ K' → ∀ t : ℝ,
        ‖Submission.LargeValues.smoothedPoly N b t‖ ≤
          CS * (∫ u in t - K'..t + K', ‖Submission.LargeValues.smoothedPoly N b u‖)
            + CS / K' ^ (m : ℝ) * (∑ n ∈ Finset.Icc N (2 * N), ‖b n‖) :=
      fun K' hK' t => hCSb N hN1 b hb K' hK' t
    have hL4app := hL4c CS hCSpos N hN1 W hWsubMN hsep b hb hloc V K hK1 hVpos hbig
    rw [← hEdef, ← ha1def] at hL4app
    set Stot : ℝ := ∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
        ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3 with hStotdef
    have hβ : a1 * ((2 * (N : ℝ) + 1) / K ^ (m : ℝ)) ^ 2 / V ^ 2 ≤ 1 / 2 := by
      have hb := beta_le (N := (N : ℝ)) (C4 := C4) (CS := CS) (Θ := Θ) (V := V) (mm := m)
        (le_of_lt hC4pos) (le_of_lt hCSpos) hΘ1 hVge hN1R (by omega) hΘsq
      rw [← ha1def, ← hKdef] at hb
      exact hb
    set D : ℝ := (N : ℝ) ^ 2 / T with hDdef
    have hDTeq : D * T = (N : ℝ) ^ 2 := by
      rw [hDdef, div_mul_cancel₀ _ (ne_of_gt hTpos)]
    have hD1 : 1 ≤ D := by
      have h1 : D = (N : ℝ) ^ (4 / 5 : ℝ) := by
        have h2 : (N : ℝ) ^ 2 = (N : ℝ) ^ ((2 : ℝ)) := (Real.rpow_natCast (N : ℝ) 2).symm
        have h3 : (N : ℝ) ^ ((2 : ℝ)) / (N : ℝ) ^ (6 / 5 : ℝ)
            = (N : ℝ) ^ ((2 : ℝ) - 6 / 5) := (Real.rpow_sub hNpos (2 : ℝ) (6 / 5 : ℝ)).symm
        have h4 : (N : ℝ) ^ ((2 : ℝ) - 6 / 5) = (N : ℝ) ^ (4 / 5 : ℝ) := by norm_num
        rw [hDdef, hTdef, Submission.LargeValues.M, h2, h3, h4]
      rw [h1]
      exact Real.one_le_rpow hN1R (by norm_num)
    have hlocR := loc_of_big (m := m) hC7CR hL7c
    have hL2R := l2_of_big hCm2CR hL2c
    have hL4R := l4_of_big hCm4CR hL4ic
    have hgs := hgcdsc CR hCRpos hlocR hL2R hL4R N hN1 W hWsubMN hsep K hK1 D hD1
    set Ssmall : ℝ := ∑ n1 ∈ Finset.Icc N (2 * N),
        ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => (Nat.gcd n1 n2 : ℝ) ≤ D),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3 with hSsmalldef
    have hL9app : (∑ n1 ∈ Finset.Icc N (2 * N),
        ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => D ≤ (Nat.gcd n1 n2 : ℝ)),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3)
        ≤ C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2)
            * (N : ℝ) ^ (2 * ε₂) *
            ((N : ℝ) * (W.card : ℝ) ^ 3
              + (N : ℝ) * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 4)
                  * (W.card : ℝ) ^ ((21 : ℝ) / 8)
              + (Submission.GM.energy W : ℝ) ^ ((1 : ℝ) / 2) * (W.card : ℝ) ^ ((1 : ℝ) / 2)
                  * (N : ℝ) ^ 2) := by
      have h := hL9c C2 hC2pos hsecond_infl (C4b * (CD + 1) ^ 2) (by positivity) hfourth_infl
        N hN100 W hWsubMN hsep
      rw [← hTdef] at h
      exact h
    set Slarge : ℝ := ∑ n1 ∈ Finset.Icc N (2 * N),
        ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => ¬((Nat.gcd n1 n2 : ℝ) ≤ D)),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3 with hSlargedef
    have hSlarge_le : Slarge ≤ (∑ n1 ∈ Finset.Icc N (2 * N),
        ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => D ≤ (Nat.gcd n1 n2 : ℝ)),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3) := by
      rw [hSlargedef]
      refine Finset.sum_le_sum fun n1 _ => ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro n2 hn2
        simp only [Finset.mem_filter] at hn2 ⊢
        exact ⟨hn2.1, le_of_lt (lt_of_not_ge hn2.2)⟩
      · intro n2 _ _
        positivity
    have hsplit : Stot = Ssmall + Slarge := by
      rw [hStotdef, hSsmalldef, hSlargedef]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n1 _ => ?_
      exact (Finset.sum_filter_add_sum_filter_not _ (fun n2 => (Nat.gcd n1 n2 : ℝ) ≤ D) _).symm
    have hsqrtE : E ^ ((1 : ℝ) / 2) = Real.sqrt E := (Real.sqrt_eq_rpow E).symm
    rw [← hκdef] at hgs
    rw [← hEdef] at hgs
    rw [hsqrtE] at hgs
    rw [← hκdef] at hL9app
    rw [← hEdef] at hL9app
    rw [hsqrtE] at hL9app
    rw [← hTdef] at hL9app
    have hL9comb : Slarge ≤ C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2)
        * (1 + 1) * (N : ℝ) ^ (2 * ε₂) *
        ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
          + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) := by
      refine hSlarge_le.trans (hL9app.trans ?_)
      have hBnn : 0 ≤ (N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
          + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2 := by
        have hTr : 0 ≤ T ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (le_of_lt hTpos) _
        have hκr : 0 ≤ κ ^ ((21 : ℝ) / 8) := Real.rpow_nonneg hκnn _
        have hκh : 0 ≤ κ ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hκnn _
        have h1 : 0 ≤ (N : ℝ) * κ ^ 3 := by positivity
        have h2 : 0 ≤ (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8) := by positivity
        have h3 : 0 ≤ Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2 := by positivity
        linarith
      have hP : 0 ≤ C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2)
          * (N : ℝ) ^ (2 * ε₂) * ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
              + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) := by
        have hN2 : 0 ≤ (N : ℝ) ^ (2 * ε₂) := Real.rpow_nonneg (le_of_lt hNpos) _
        have hsqrt0 : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
        positivity
      have h2 : (1 : ℝ) ≤ 1 + 1 := by norm_num
      have h3 : C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2)
            * (N : ℝ) ^ (2 * ε₂) * ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
              + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) * 1
          ≤ C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2)
            * (N : ℝ) ^ (2 * ε₂) * ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
              + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) * (1 + 1) :=
        mul_le_mul_of_nonneg_left h2 hP
      have h4 : C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2)
            * (N : ℝ) ^ (2 * ε₂) * ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
              + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2)
          = C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2)
            * (N : ℝ) ^ (2 * ε₂) * ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
              + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) * 1 := by ring
      have h5 : C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2)
            * (N : ℝ) ^ (2 * ε₂) * ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
              + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) * (1 + 1)
          = C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2)
            * (1 + 1) * (N : ℝ) ^ (2 * ε₂) *
            ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
              + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) := by ring
      calc C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2)
            * (N : ℝ) ^ (2 * ε₂) * ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
              + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2)
          = C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2)
            * (N : ℝ) ^ (2 * ε₂) * ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
              + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) * 1 := h4
        _ ≤ C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2)
            * (N : ℝ) ^ (2 * ε₂) * ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
              + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) * (1 + 1) := h3
        _ = C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b * (CD + 1) ^ 2 + 1) ^ ((1 : ℝ) / 2)
            * (1 + 1) * (N : ℝ) ^ (2 * ε₂) *
            ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
              + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) := h5
    have hcore := energy_core (N := N) (δ := δ) (ε := ε₂) (m := m) (T := T) (V := V) (D := D)
      (κ := κ) (E := E) (Stot := Stot) (Ssmall := Ssmall) (Slarge := Slarge)
      (a1 := a1) (g1 := g1) (l1 := l1) (Θ := Θ) (K := K) (Λ := Λ)
      (Cg := Cg) (CR := CR) (C9 := C9) (C2 := C2) (C4b := C4b * (CD + 1) ^ 2) (CD := 1)
      hN100 hδ hε₂pos hm2 hT1 hVge hκnn hEnn ha1nn hg1nn hl1nn hΘ1 hg1def hl1eq hDTeq hKdef
      hΛdef hΛle hsplit hL4app hβ hgs hL9comb
    rw [← hCAdef, ← hCBdef, ← hCFdef] at hcore
    exact hcore
  · -- ### Trivial case `V < 1`
    have hVlt : V < 1 := lt_of_not_ge hVge
    exact energy_trivial (N := N) (T := T) (V := V) (κ := κ) (E := E) (CF := CF) (δ := δ)
      hN1 hWsubT hsep hκdef hEdef hT1 hT3 hVpos hVlt hCF8 hδ

end Work.GM.Energy.EnergyCore2
