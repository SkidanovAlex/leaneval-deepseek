import Mathlib
import Submission.Work.Peluse.Ulower.steple_aux
import Submission.Work.Peluse.Ulower.lemma74_cubeTerm_iterDelta
import Submission.Work.Peluse.Ulower.dualFn_norm_le_one
import Submission.Work.Peluse.Ulower.StepLe.levelTwoArith
import Submission.Work.Peluse.Ulower.StepLe.denseLevelExtract
import Submission.Work.Peluse.Ulower.StepLe.piFinsetProdSum

namespace Work.Peluse.Ulower.StepLe

set_option maxHeartbeats 4000000

noncomputable section

open scoped BigOperators

open Work.Peluse

/-- An iterated `Δ'`-difference of a `1`-bounded function is `1`-bounded. -/
private lemma norm_iterDelta'_le_one : ∀ (k : ℕ) (sh : Fin k → ℤ × ℤ) (G : ℤ → ℂ),
    (∀ x : ℤ, ‖G x‖ ≤ 1) → ∀ x : ℤ, ‖iterDelta' k sh G x‖ ≤ 1 := by
  intro k
  induction k with
  | zero => intro sh G h x; exact h x
  | succ k ih =>
      intro sh G h x
      have hdef : iterDelta' (k + 1) sh G x =
          star (iterDelta' k (fun i => sh i.succ) G (x + (sh 0).1)) *
            iterDelta' k (fun i => sh i.succ) G (x + (sh 0).2) := rfl
      rw [hdef, norm_mul, norm_star]
      have h1 := ih (fun i => sh i.succ) G h (x + (sh 0).1)
      have h2 := ih (fun i => sh i.succ) G h (x + (sh 0).2)
      nlinarith [norm_nonneg (iterDelta' k (fun i => sh i.succ) G (x + (sh 0).1)),
        norm_nonneg (iterDelta' k (fun i => sh i.succ) G (x + (sh 0).2))]

theorem levelTwoExtract {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h1 : Work.Peluse.PeluseU2Inverse) (K : ℝ) (hK : 1 ≤ K) :
    ∀ σ : ℕ, 1 ≤ σ → ∃ c : ℝ, 0 < c ∧ ∃ p q : ℕ, 1 ≤ p ∧ 1 ≤ q ∧
      ∀ (B Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (θ : ℝ),
        1 ≤ N → 1 ≤ Ns → Work.Peluse.Scaled Ns N P.natDegree → N ≤ Ns →
        1 ≤ D → (D : ℝ) ≤ K * (Ns : ℝ) →
        Work.Peluse.SupportIn f₀ Ns → Work.Peluse.SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        Work.Peluse.dSup P Ns N + 2 * σ * D ≤ B →
        0 < θ → θ ≤ 1 →
        θ ≤ Work.Peluse.boxNormPow (σ + 2) (fun _ : Fin (σ + 2) => Work.Peluse.arithIcc 1 D)
              (Work.Peluse.symIcc B) (Work.Peluse.dualFn N P f₀ f₁) →
        ∃ β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ,
          c * θ ^ p * ((D : ℝ) / (Ns : ℝ)) ^ q ≤
            ((Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹ *
            ((Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹ *
            ∑ u ∈ Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D),
              ∑ v ∈ Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D),
                ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
                  Work.Peluse.cubeTerm u v (Work.Peluse.dualFn N P f₀ f₁) x *
                  Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖ ^ 2 := by
  obtain ⟨Cd, hCdpos, Kd, hKd1, hchar⟩ := char_of_boxNormPow_two h1
  intro σ hσ
  refine ⟨Cd ^ 2 * (4 * (ssAmax P : ℝ) ^ (2 * Kd) * 3 ^ (2 * (Kd - 1)) * 12 ^ (1 + 2 * Kd))⁻¹,
    ?_, 6 * Kd + 2, 2 * Kd, by omega, by omega, ?_⟩
  · have hApos : (0 : ℝ) < (ssAmax P : ℝ) := by exact_mod_cast ssAmax_pos P
    positivity
  intro B Ns N D f₀ f₁ θ hN hNs hSc hNNs hD1 hDK hsupp0 hsupp1 hb0 hb1 hB hθ0 hθ1 hbox
  set Q : Finset ℤ := Work.Peluse.arithIcc 1 D with hQdef
  set F : ℤ → ℂ := Work.Peluse.dualFn N P f₀ f₁ with hFdef
  set L₀ : ℕ := Work.Peluse.dSup P Ns N with hL₀def
  set L' : ℕ := L₀ + 2 * σ * D with hL'def
  set Box : Finset (Fin σ → ℤ) := Fintype.piFinset (fun _ : Fin σ => Q) with hBoxdef
  set level : ℝ := θ * ((Work.Peluse.symIcc L₀).card : ℝ) /
    (2 * ((Work.Peluse.symIcc L').card : ℝ)) with hleveldef
  set X : ℝ := Cd * level ^ Kd * ((D : ℝ) / (L' : ℝ)) ^ Kd * (L' : ℝ) with hXdef
  set Y : ℝ := ((B : ℝ))⁻¹ ^ 2 * X ^ 2 with hYdef
  have hApos : (0 : ℝ) < (ssAmax P : ℝ) := by exact_mod_cast ssAmax_pos P
  have hA1 : (1 : ℝ) ≤ (ssAmax P : ℝ) := by
    have h := three_le_ssAmax P
    exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 3) h)
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD1)
  have hNspos : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNs)
  have hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1 := dualFn_norm_le_one hN P f₀ f₁ hb0 hb1
  have hFspan : ∀ x : ℤ, x ∉ Work.Peluse.symIcc L₀ → F x = 0 := by
    intro x hx
    have hx' : Work.Peluse.dSup P Ns N < x.natAbs := by
      by_contra hcon
      exact hx (by rw [mem_symIcc_iff, hL₀def]; omega)
    rw [hFdef]
    exact Work.Peluse.Tools.dualFn_supportIn (by omega) P f₀ f₁ hsupp0 hsupp1 hNNs x hx'
  have hL₀1 : 1 ≤ L₀ := by rw [hL₀def, Work.Peluse.dSup]; omega
  have hL₀ge1 : (1 : ℝ) ≤ (L₀ : ℝ) := by exact_mod_cast hL₀1
  have hL'1 : 1 ≤ L' := by rw [hL'def]; omega
  have hL'pos : (0 : ℝ) < (L' : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL'1)
  have hB1 : 1 ≤ B := by omega
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB1)
  have hL'LB : L' ≤ L₀ + B := by
    have hB' := hB
    rw [hL'def] at hB'
    omega
  have hL'LB' : (L' : ℝ) ≤ (L₀ : ℝ) + (B : ℝ) := by exact_mod_cast hL'LB
  have hL₀L' : L₀ ≤ L' := by rw [hL'def]; omega
  have hL₀A_nat : L₀ ≤ ssAmax P * Ns := by
    have h := dSup_div_add_one_le (P := P) (hd := by omega) (c := (1 : ℤ)) (by norm_num) hNs hN hSc
    rw [hL₀def]
    simp only [Int.natAbs_one, Nat.div_one] at h
    omega
  have hL₀A : (L₀ : ℝ) ≤ (ssAmax P : ℝ) * (Ns : ℝ) := by
    rw [← Nat.cast_mul]
    exact_mod_cast hL₀A_nat
  have hboxL₀ : θ ≤ boxNormPow (σ + 2) (fun _ : Fin (σ + 2) => Work.Peluse.arithIcc 1 D)
      (Work.Peluse.symIcc L₀) F := by
    have hsub : Work.Peluse.symIcc L₀ ⊆ Work.Peluse.symIcc B := by
      intro x hx
      rw [mem_symIcc_iff] at hx ⊢
      omega
    have hne : (Work.Peluse.symIcc L₀).Nonempty := ⟨0, by rw [mem_symIcc_iff]; simp⟩
    have hle := boxNormPow_le_of_subset (t := σ + 2)
      (Q := fun _ : Fin (σ + 2) => Work.Peluse.arithIcc 1 D) hsub hne F
    exact le_trans hbox hle
  have hcardB : θ * (2 * (B : ℝ) + 1) ≤ 2 * (L₀ : ℝ) + 1 := by
    have h := theta_mul_card_le (t := σ + 2)
      (Q := fun _ : Fin (σ + 2) => Work.Peluse.arithIcc 1 D)
      (B := B) (L₀ := L₀) (F := F) (θ := θ) hF1 hFspan hbox
    rw [card_symIcc, card_symIcc] at h
    push_cast at h
    linarith
  obtain ⟨H, hHsub, hHcard, hHlevel⟩ := denseLevelExtract hσ hD1 hF1 hFspan hθ0 hθ1 hboxL₀
  rw [← hL'def] at hHcard hHlevel
  rw [← hleveldef] at hHcard hHlevel
  rw [← hQdef] at hHsub
  have hlevel_cards : level = θ * (2 * (L₀ : ℝ) + 1) / (2 * (2 * (L' : ℝ) + 1)) := by
    rw [hleveldef, card_symIcc, card_symIcc]
    push_cast
    ring
  have hlevelpos : 0 < level := by
    rw [hlevel_cards]; positivity
  have hlevel1 : level ≤ 1 := by
    rw [hlevel_cards]
    have h1 : θ * (2 * (L₀ : ℝ) + 1) ≤ (2 * (L' : ℝ) + 1) := by
      have h2 : θ * (2 * (L₀ : ℝ) + 1) ≤ 1 * (2 * (L₀ : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hθ1 (by positivity)
      have h3 : (2 * (L₀ : ℝ) + 1) ≤ (2 * (L' : ℝ) + 1) := by
        have h4 : (L₀ : ℝ) ≤ (L' : ℝ) := by exact_mod_cast hL₀L'
        linarith
      linarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (2 * (L' : ℝ) + 1))]
    nlinarith [h1]
  have hlevel_ge : θ ^ 2 / 12 ≤ level := by
    rw [hlevel_cards]
    have hθB : θ * (B : ℝ) ≤ 2 * (L₀ : ℝ) := by
      have h1 : 2 * θ * (B : ℝ) + θ ≤ 2 * (L₀ : ℝ) + 1 := by nlinarith [hcardB]
      nlinarith [h1, hL₀ge1, hθ0]
    have hθL' : θ * (L' : ℝ) ≤ 3 * (L₀ : ℝ) := by
      have h1 : θ * (L' : ℝ) ≤ θ * ((L₀ : ℝ) + (B : ℝ)) :=
        mul_le_mul_of_nonneg_left hL'LB' hθ0.le
      have h2 : θ * ((L₀ : ℝ) + (B : ℝ)) = θ * (L₀ : ℝ) + θ * (B : ℝ) := by ring
      have h3 : θ * (L₀ : ℝ) ≤ (L₀ : ℝ) := by nlinarith [hθ1, hL₀ge1, hθ0]
      linarith [h1, h2, h3, hθB]
    have hθden : θ * (2 * (2 * (L' : ℝ) + 1)) ≤ 24 * (L₀ : ℝ) := by
      nlinarith [hθL', hθ0, hθ1, hL₀ge1]
    have hkey1 : θ ^ 2 * (2 * (2 * (L' : ℝ) + 1)) ≤ 24 * θ * (L₀ : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hθden hθ0.le
      nlinarith [h]
    have hDnpos : (0 : ℝ) < 2 * (2 * (L' : ℝ) + 1) := by positivity
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 12) hDnpos]
    nlinarith [hkey1, hθ0]
  have hlevel_cminθ : (θ / 12) * θ ≤ level := by
    have heq : (θ / 12) * θ = θ ^ 2 / 12 := by ring
    linarith [hlevel_ge]
  have hXnn : 0 ≤ X := by
    rw [hXdef]
    have := hL'pos
    positivity
  have hYnn : 0 ≤ Y := by
    rw [hYdef]; positivity
  have harith := levelTwoArith (K := Kd) hKd1 (cmin := θ / 12) (Cd := Cd) (θ := θ) (eta := level)
    (D := (D : ℝ)) (Ns := (Ns : ℝ)) (L := (L' : ℝ)) (L₀ := (L₀ : ℝ)) (B := (B : ℝ))
    (A := (ssAmax P : ℝ))
    (by positivity) hCdpos hθ0 hθ1 hDpos hNspos hL'pos hBpos hA1 hL₀ge1 hL₀A
    hlevel_cminθ hcardB hL'LB'
  rw [← hXdef] at harith
  have hconst : (θ / 12) ^ (1 + 2 * Kd) * Cd ^ 2 / (4 * (ssAmax P : ℝ) ^ (2 * Kd) * 3 ^ (2 * (Kd - 1)))
        * θ ^ (4 * Kd + 1) * ((D : ℝ) / (Ns : ℝ)) ^ (2 * Kd)
      = Cd ^ 2 * (4 * (ssAmax P : ℝ) ^ (2 * Kd) * 3 ^ (2 * (Kd - 1)) * 12 ^ (1 + 2 * Kd))⁻¹
        * θ ^ (6 * Kd + 2) * ((D : ℝ) / (Ns : ℝ)) ^ (2 * Kd) := by
    rw [div_pow, div_eq_mul_inv]
    simp only [mul_inv_rev]
    rw [show (6 * Kd + 2) = (1 + 2 * Kd) + (4 * Kd + 1) from by ring, pow_add]
    ring
  have hex : ∀ h ∈ H, ∃ β : ℝ, X ≤
      ‖∑' x : ℤ, Work.Peluse.cubeTerm (fun i => (h i).1) (fun i => (h i).2) F x *
        Complex.exp (2 * Real.pi * Complex.I * (β : ℂ) * (x : ℂ))‖ := by
    intro h hh
    have hhI := hHsub hh
    have hmem : ∀ i : Fin σ, (h i).1 ∈ Work.Peluse.arithIcc 1 D ∧
        (h i).2 ∈ Work.Peluse.arithIcc 1 D := by
      intro i
      have hi := Fintype.mem_piFinset.mp hhI i
      exact ⟨(Finset.mem_product.mp hi).1, (Finset.mem_product.mp hi).2⟩
    have hsum_le : (∑ i : Fin σ, ((h i).1.natAbs + (h i).2.natAbs)) ≤ 2 * σ * D := by
      have hterm : ∀ i : Fin σ, ((h i).1.natAbs + (h i).2.natAbs) ≤ 2 * D := by
        intro i
        obtain ⟨ha, hb⟩ := hmem i
        obtain ⟨ha1, ha2⟩ := mem_arithIcc_one.mp ha
        obtain ⟨hb1, hb2⟩ := mem_arithIcc_one.mp hb
        have e1 : (((h i).1.natAbs : ℕ) : ℤ) ≤ (D : ℤ) := by
          rw [Int.natCast_natAbs, abs_of_nonneg (by omega : (0 : ℤ) ≤ (h i).1)]
          exact ha2
        have e2 : (((h i).2.natAbs : ℕ) : ℤ) ≤ (D : ℤ) := by
          rw [Int.natCast_natAbs, abs_of_nonneg (by omega : (0 : ℤ) ≤ (h i).2)]
          exact hb2
        omega
      calc (∑ i : Fin σ, ((h i).1.natAbs + (h i).2.natAbs))
          ≤ ∑ _i : Fin σ, (2 * D) := Finset.sum_le_sum (fun i _ => hterm i)
        _ = σ * (2 * D) := by simp
        _ = 2 * σ * D := by ring
    have hgsupp : Work.Peluse.SupportIn (iterDelta' σ h F) L' := by
      intro x hx
      refine iterDelta'_supportIn σ h hFspan x (fun hxin => ?_)
      rw [mem_symIcc_iff] at hxin
      have h4 : L₀ + (∑ i : Fin σ, ((h i).1.natAbs + (h i).2.natAbs)) ≤ L' := by
        rw [hL'def]; omega
      have h5 : x.natAbs ≤ L' := le_trans hxin h4
      omega
    have hgbd : ∀ x : ℤ, ‖iterDelta' σ h F x‖ ≤ 1 :=
      norm_iterDelta'_le_one σ h F hF1
    have hL'D : (D : ℝ) ≤ (L' : ℝ) := by
      have h6 : D ≤ 2 * σ * D := Nat.le_mul_of_pos_left D (by omega)
      have h7 : 2 * σ * D ≤ L' := by rw [hL'def]; omega
      exact_mod_cast (le_trans h6 h7)
    obtain ⟨β, hβ⟩ := hchar L' D (iterDelta' σ h F) level hL'1 hD1 hL'D hgsupp hgbd
      hlevelpos hlevel1 (hHlevel h hh)
    refine ⟨β, ?_⟩
    rw [hXdef]
    refine le_trans hβ (le_of_eq ?_)
    congr 1
    refine tsum_congr (fun x => ?_)
    have hrew : iterDelta' σ h F x = Work.Peluse.cubeTerm (fun i => (h i).1) (fun i => (h i).2) F x :=
      lemma74_cubeTerm_iterDelta h F x
    have hexp : Complex.exp (2 * Real.pi * Complex.I * (β : ℂ) * (x : ℂ))
        = Complex.exp (2 * Real.pi * Complex.I * β * ((x : ℝ) : ℂ)) := by
      congr 1
    rw [hrew, hexp]
  have hex2 : ∀ u v : (Fin σ → ℤ),
      (∃ h ∈ H, (fun i => (h i).1) = u ∧ (fun i => (h i).2) = v) →
      ∃ β : ℝ, X ≤ ‖∑' x : ℤ, Work.Peluse.cubeTerm u v F x *
        Complex.exp (2 * Real.pi * Complex.I * (β : ℂ) * (x : ℂ))‖ := by
    rintro u v ⟨h, hh, h1, h2⟩
    subst h1; subst h2
    exact hex h hh
  let β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ := fun u v =>
    if hh' : (∃ h ∈ H, (fun i => (h i).1) = u ∧ (fun i => (h i).2) = v)
      then Classical.choose (hex2 u v hh') else 0
  refine ⟨β, ?_⟩
  have hβspec : ∀ h ∈ H, X ≤ ‖∑' x : ℤ,
      Work.Peluse.cubeTerm (fun i => (h i).1) (fun i => (h i).2) F x *
        Complex.exp (2 * Real.pi * Complex.I * (β (fun i => (h i).1) (fun i => (h i).2) : ℂ) * (x : ℂ))‖ := by
    intro h hh
    have hexH : ∃ h' ∈ H, (fun i => (h' i).1) = (fun i => (h i).1) ∧
        (fun i => (h' i).2) = (fun i => (h i).2) := ⟨h, hh, rfl, rfl⟩
    have hβeq : β (fun i => (h i).1) (fun i => (h i).2) =
        Classical.choose (hex2 (fun i => (h i).1) (fun i => (h i).2) hexH) := by
      dsimp only [β]
      rw [dif_pos hexH]
    rw [hβeq]
    exact Classical.choose_spec (hex2 (fun i => (h i).1) (fun i => (h i).2) hexH)
  let S : (Fin σ → ℤ) → (Fin σ → ℤ) → ℂ := fun u v =>
    ∑' x : ℤ, Work.Peluse.cubeTerm u v F x *
      Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))
  let G : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ := fun u v => ‖((B : ℂ))⁻¹ * S u v‖ ^ 2
  have hG_eq : ∀ u v, G u v = ((B : ℝ)⁻¹) ^ 2 * ‖S u v‖ ^ 2 := by
    intro u v
    show ‖((B : ℂ))⁻¹ * S u v‖ ^ 2 = ((B : ℝ)⁻¹) ^ 2 * ‖S u v‖ ^ 2
    rw [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  have hGterm : ∀ h ∈ H, ((B : ℝ)⁻¹) ^ 2 * X ^ 2 ≤
      G (fun i => (h i).1) (fun i => (h i).2) := by
    intro h hh
    have hspec := hβspec h hh
    rw [hG_eq (fun i => (h i).1) (fun i => (h i).2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ ((B : ℝ)⁻¹) ^ 2)
    exact pow_le_pow_left₀ hXnn hspec 2
  have hGsum : (∑ h ∈ H, G (fun i => (h i).1) (fun i => (h i).2)) ≤
      ∑ u ∈ Box, ∑ v ∈ Box, G u v := by
    have hstep := Finset.sum_le_sum_of_subset_of_nonneg (s := H)
      (t := Fintype.piFinset (fun _ : Fin σ => Q.product Q))
      (f := fun p => G (fun i => (p i).1) (fun i => (p i).2)) hHsub
      (fun p _ _ => by
        show (0 : ℝ) ≤ ‖((B : ℂ))⁻¹ * S (fun i => (p i).1) (fun i => (p i).2)‖ ^ 2
        positivity)
    have hreindex : (∑ p ∈ Fintype.piFinset (fun _ : Fin σ => Q.product Q),
        G (fun i => (p i).1) (fun i => (p i).2)) = ∑ u ∈ Box, ∑ v ∈ Box, G u v := by
      rw [hBoxdef]
      exact piFinsetProdSum Q G
    rwa [hreindex] at hstep
  have hsumH : (H.card : ℝ) * Y ≤ ∑ h ∈ H, G (fun i => (h i).1) (fun i => (h i).2) := by
    have h1 : (∑ h ∈ H, Y) ≤ ∑ h ∈ H, G (fun i => (h i).1) (fun i => (h i).2) :=
      Finset.sum_le_sum (fun h hh => by
        rw [hYdef]
        exact hGterm h hh)
    rwa [Finset.sum_const, nsmul_eq_mul] at h1
  have hBoxcard_nat : Box.card = D ^ σ := by
    rw [hBoxdef, Fintype.card_piFinset]
    simp only [hQdef, card_arithIcc_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hBoxcard : (Box.card : ℝ) = (D : ℝ) ^ σ := by
    rw [hBoxcard_nat]
    push_cast
    ring
  have hkey : level * Y ≤ ((Box.card : ℝ))⁻¹ * ((Box.card : ℝ))⁻¹ *
      (∑ u ∈ Box, ∑ v ∈ Box, G u v) := by
    have h2 : ((Box.card : ℝ))⁻¹ * ((Box.card : ℝ))⁻¹ * ((H.card : ℝ) * Y) ≤
        ((Box.card : ℝ))⁻¹ * ((Box.card : ℝ))⁻¹ * (∑ u ∈ Box, ∑ v ∈ Box, G u v) :=
      mul_le_mul_of_nonneg_left (le_trans hsumH hGsum) (by positivity)
    have h3 : ((Box.card : ℝ))⁻¹ * ((Box.card : ℝ))⁻¹ * ((level * (D : ℝ) ^ (2 * σ)) * Y)
        = level * Y := by
      have hDne : (D : ℝ) ^ σ ≠ 0 := by positivity
      rw [hBoxcard, show 2 * σ = σ * 2 from by ring, pow_mul]
      field_simp
    calc level * Y
        = ((Box.card : ℝ))⁻¹ * ((Box.card : ℝ))⁻¹ * ((level * (D : ℝ) ^ (2 * σ)) * Y) := h3.symm
      _ ≤ ((Box.card : ℝ))⁻¹ * ((Box.card : ℝ))⁻¹ * ((H.card : ℝ) * Y) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hHcard hYnn) (by positivity)
      _ ≤ ((Box.card : ℝ))⁻¹ * ((Box.card : ℝ))⁻¹ * (∑ u ∈ Box, ∑ v ∈ Box, G u v) := h2
  have hfinal : Cd ^ 2 * (4 * (ssAmax P : ℝ) ^ (2 * Kd) * 3 ^ (2 * (Kd - 1)) * 12 ^ (1 + 2 * Kd))⁻¹
      * θ ^ (6 * Kd + 2) * ((D : ℝ) / (Ns : ℝ)) ^ (2 * Kd) ≤ level * Y := by
    have heq : (θ / 12) * θ * ((B : ℝ))⁻¹ ^ 2 * X ^ 2 = ((θ / 12) * θ) * Y := by
      rw [hYdef]; ring
    rw [← hconst]
    exact le_trans harith (le_trans (le_of_eq heq) (mul_le_mul_of_nonneg_right hlevel_cminθ hYnn))
  exact le_trans hfinal hkey

end

end Work.Peluse.Ulower.StepLe
