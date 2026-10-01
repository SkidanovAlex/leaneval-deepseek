import Mathlib
import Submission.Work.LinnikAreas.A7.WBox
import Submission.Work.A7.lamChar_api
import Submission.Work.A7.box_api7
import Submission.Work.A7.Wf_Cf_mono
import Submission.Work.A7.ExpWf_antitone

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-- `Wf λ = w(λ) ≥ 0` whenever `λ ≥ 0` (at `λ = 0` the weight vanishes; for `λ > 0` it is
strictly positive by `Wf_pos`). -/
private lemma Wf_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Work.LinnikAreas.A7.Wf x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, Work.LinnikAreas.A7.Wf, Work.LinnikContract.wHB]; simp
  · exact (Wf_pos h).le

/-- **Area 7: the tail bound.**

The characters of `Aset q R` other than the maximal one `χ₁` all carry their zeros at parameter
`≥ c` (this is HB's `λ₂ ≥ c`, the hypothesis `hLam2`, together with `χ₁² = 1` forcing
`χ₁⁻¹ = χ₁`).  For such a character `χ`, writing `λ_χ = lamChar χ`:

* every box zero has `λ(ρ) ≥ λ_χ`, so `WBox χ ≤ e^{-a λ_χ} · boxAbs χ`
  (`WBox_le_exp_mul_boxAbs`);
* the per-character certificate `hPC` gives `boxAbs χ ≤ (9/100)(B(λ_χ) + η)`;

hence `WBox χ ≤ (9/100)(Φ(λ_χ) + η e^{-a λ_χ})`.  Since `c ≤ λ_χ` and both `Φ/w` and
`e^{-aλ}/w` are antitone (`PhiWf_antitone`, `ExpWf_antitone`),

  `WBox χ ≤ (9/100) (Φ(c)/w(c) + η e^{-ac}/w(c)) · w(λ_χ)`.

Finally `λ_χ ≤ R ≤ lamMax q` shows `Aset q R \ {χ₁} ⊆ hS`, so the density budget `hD1` gives
`Σ_{χ ≠ χ₁} w(λ_χ) ≤ 67/6 + εw`, and the claim follows. -/
theorem tail_le14 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {R c η εw : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : 0 < R) (hRlog : R ≤ Real.log q) (hRmax : R ≤ Work.LinnikContract.lamMax q)
    (hη : 0 ≤ η) (hcpos : 0 < c)
    (hZ1sq : χ₁ ^ 2 = 1)
    (hLam2 : Work.LinnikContract.Lam2Bound χ₁ c)
    (hS : Finset (DirichletCharacter ℂ q))
    (hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, Work.LinnikContract.IsZ χ ρ ∧ Work.LinnikContract.lamOf q ρ ≤ Work.LinnikContract.lamMax q)
    (hD1 : ∑ χ ∈ hS, Work.LinnikContract.wHB (Work.LinnikContract.lamChar χ) ≤ (67:ℝ)/6 + εw)
    (hPC : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, Work.LinnikContract.IsZ χ ρ → lam' ≤ Work.LinnikContract.lamOf q ρ) →
        Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam' + η)) :
    ∑ χ ∈ (Work.LinnikAreas.A7.Aset q R).erase χ₁, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * ((Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw))
        + ((9:ℝ)/100) * η * ((Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw)) := by
  classical
  set T : Finset (DirichletCharacter ℂ q) := Work.LinnikAreas.A7.Aset q R with hT
  have hmemAset : ∀ χ : DirichletCharacter ℂ q, χ ∈ T ↔
      χ ≠ 1 ∧ ∃ ρ : ℂ, Work.LinnikContract.InBox q R ρ ∧ Work.LinnikContract.zeroMult χ ρ ≠ 0 := by
    intro χ
    rw [hT, Work.LinnikAreas.A7.Aset, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, Finset.mem_univ χ⟩, h2⟩
  have hinv : χ₁⁻¹ = χ₁ := by
    have h2 : χ₁ * χ₁ = 1 := by rw [← pow_two]; exact hZ1sq
    exact inv_eq_of_mul_eq_one_right h2
  set C : ℝ := ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c
      + η * (Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c)) with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    have hWfc : 0 < Work.LinnikAreas.A7.Wf c := Wf_pos hcpos
    have hBc : 0 ≤ Work.LinnikContract.Bfun Work.LinnikAreas.A7.Kc c :=
      (Work.LinnikContract.API.Bfun_pos (by norm_num [Work.LinnikAreas.A7.Kc]) hcpos).le
    have h1 : 0 ≤ Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c := by
      rw [Work.LinnikAreas.A7.Phi]
      exact div_nonneg (mul_nonneg (Real.exp_pos _).le hBc) hWfc.le
    have h2 : 0 ≤ η * (Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c) :=
      mul_nonneg hη (div_nonneg (Real.exp_pos _).le hWfc.le)
    exact mul_nonneg (by norm_num) (add_nonneg h1 h2)
  have hpoint : ∀ χ ∈ T.erase χ₁, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ C * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) := by
    intro χ hχmem
    rw [Finset.mem_erase] at hχmem
    obtain ⟨hχne1, hχT⟩ := hχmem
    obtain ⟨hχ1, ρ0, hbox0, hzm0⟩ := (hmemAset χ).mp hχT
    have hZ0 : Work.LinnikContract.IsZ χ ρ0 := box_api7_p1 hq hRlog hχ1 hzm0 hbox0
    have hne : ∃ ρ : ℂ, Work.LinnikContract.IsZ χ ρ := ⟨ρ0, hZ0⟩
    have hχneinv : χ ≠ χ₁⁻¹ := by rw [hinv]; exact hχne1
    obtain ⟨ρstar, hZstar, hstar⟩ := exists_lamChar_eq_lamOf (q := q) hne
    have hlow : c ≤ Work.LinnikContract.lamChar χ := by
      rw [hstar]; exact hLam2 χ ρstar hZstar hχne1 hχneinv
    have hpos : 0 < Work.LinnikContract.lamChar χ := lt_of_lt_of_le hcpos hlow
    have hleR : Work.LinnikContract.lamChar χ ≤ R :=
      le_trans (lamChar_le_lamOf hq hZ0) hbox0.1
    have hWBox : Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
        ≤ Real.exp (-(Work.LinnikAreas.A7.ac * Work.LinnikContract.lamChar χ))
            * Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ :=
      Work.LinnikAreas.A7.WBox_le_exp_mul_boxAbs ((3:ℝ)/10) R χ
        (fun ρ hb hz => lamChar_le_lamOf hq (box_api7_p1 hq hRlog hχ1 hz hb))
    have hba : Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ
        ≤ ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) (Work.LinnikContract.lamChar χ) + η) :=
      hPC χ hχ1 (Work.LinnikContract.lamChar χ) (le_of_lt hpos) hleR
        (fun ρ hZ => lamChar_le_lamOf hq hZ)
    have hstep1 : Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
        ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi (Work.LinnikContract.lamChar χ)
            + η * Real.exp (-(Work.LinnikAreas.A7.ac * Work.LinnikContract.lamChar χ))) := by
      have heq1 : Real.exp (-(Work.LinnikAreas.A7.ac * Work.LinnikContract.lamChar χ))
            * (((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) (Work.LinnikContract.lamChar χ) + η))
          = ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi (Work.LinnikContract.lamChar χ)
              + η * Real.exp (-(Work.LinnikAreas.A7.ac * Work.LinnikContract.lamChar χ))) := by
        rw [Work.LinnikAreas.A7.Phi, Work.LinnikAreas.A7.Kc]; ring
      exact le_trans hWBox (le_trans (mul_le_mul_of_nonneg_left hba (Real.exp_pos _).le) (le_of_eq heq1))
    have hWfpos : 0 < Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) := Wf_pos hpos
    have hWfne : Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) ≠ 0 := ne_of_gt hWfpos
    have h1 : Work.LinnikAreas.A7.Phi (Work.LinnikContract.lamChar χ)
        ≤ (Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c)
            * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) := by
      have h := PhiWf_antitone hcpos hlow
      have hm := mul_le_mul_of_nonneg_right h hWfpos.le
      rwa [div_mul_cancel₀ _ hWfne] at hm
    have h2 : η * Real.exp (-(Work.LinnikAreas.A7.ac * Work.LinnikContract.lamChar χ))
        ≤ η * ((Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c)
            * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)) := by
      apply mul_le_mul_of_nonneg_left _ hη
      have hE : Real.exp (-(Work.LinnikAreas.A7.ac * Work.LinnikContract.lamChar χ))
            / Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)
          ≤ Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c := by
        simpa only [Work.LinnikAreas.A7.ac] using ExpWf_antitone hcpos hlow
      have hm := mul_le_mul_of_nonneg_right hE hWfpos.le
      rwa [div_mul_cancel₀ _ hWfne] at hm
    have hcmp : Work.LinnikAreas.A7.Phi (Work.LinnikContract.lamChar χ)
          + η * Real.exp (-(Work.LinnikAreas.A7.ac * Work.LinnikContract.lamChar χ))
        ≤ (Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c
            + η * (Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c))
          * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) := by
      calc Work.LinnikAreas.A7.Phi (Work.LinnikContract.lamChar χ)
              + η * Real.exp (-(Work.LinnikAreas.A7.ac * Work.LinnikContract.lamChar χ))
          ≤ (Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c)
                * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)
              + η * ((Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c)
                * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)) := add_le_add h1 h2
        _ = (Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c
            + η * (Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c))
          * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) := by ring
    calc Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
        ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi (Work.LinnikContract.lamChar χ)
            + η * Real.exp (-(Work.LinnikAreas.A7.ac * Work.LinnikContract.lamChar χ))) := hstep1
      _ ≤ ((9:ℝ)/100) * ((Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c
            + η * (Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c))
            * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)) :=
          mul_le_mul_of_nonneg_left hcmp (by norm_num)
      _ = C * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) := by rw [hC]; ring
  have hsum1 : ∑ χ ∈ T.erase χ₁, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ∑ χ ∈ T.erase χ₁, C * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) :=
    Finset.sum_le_sum hpoint
  have hsum2 : ∑ χ ∈ T.erase χ₁, C * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)
      = C * ∑ χ ∈ T.erase χ₁, Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) := by
    rw [Finset.mul_sum]
  have hsub : T.erase χ₁ ⊆ hS := by
    intro χ hχ
    rw [Finset.mem_erase] at hχ
    obtain ⟨_, hχT⟩ := hχ
    obtain ⟨hχ1, ρ, hbox, hzm⟩ := (hmemAset χ).mp hχT
    have hZ : Work.LinnikContract.IsZ χ ρ := box_api7_p1 hq hRlog hχ1 hzm hbox
    exact (hSiff χ).mpr ⟨ρ, hZ, le_trans hbox.1 hRmax⟩
  have hsum3 : ∑ χ ∈ T.erase χ₁, Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)
      ≤ ∑ χ ∈ hS, Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun χ _ _ => Wf_nonneg_of_nonneg (lamChar_nonneg_of_hq hq χ))
  have hsum4 : ∑ χ ∈ hS, Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)
      ≤ (67:ℝ)/6 + εw := by
    have h : ∑ χ ∈ hS, Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)
        = ∑ χ ∈ hS, Work.LinnikContract.wHB (Work.LinnikContract.lamChar χ) := rfl
    rw [h]; exact hD1
  have hsum5 : ∑ χ ∈ T.erase χ₁, Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)
      ≤ (67:ℝ)/6 + εw := le_trans hsum3 hsum4
  have hsum6 : C * ∑ χ ∈ T.erase χ₁, Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)
      ≤ C * ((67:ℝ)/6 + εw) := mul_le_mul_of_nonneg_left hsum5 hCnn
  calc ∑ χ ∈ T.erase χ₁, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ∑ χ ∈ T.erase χ₁, C * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) := hsum1
    _ = C * ∑ χ ∈ T.erase χ₁, Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) := hsum2
    _ ≤ C * ((67:ℝ)/6 + εw) := hsum6
    _ = ((9:ℝ)/100) * ((Work.LinnikAreas.A7.Phi c / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw))
        + ((9:ℝ)/100) * η * ((Real.exp (-(Work.LinnikAreas.A7.ac * c)) / Work.LinnikAreas.A7.Wf c) * ((67:ℝ)/6 + εw)) := by
      rw [hC]; ring

end

end Work.A7
