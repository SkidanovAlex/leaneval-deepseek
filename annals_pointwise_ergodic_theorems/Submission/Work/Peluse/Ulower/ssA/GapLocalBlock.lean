import Mathlib
import Submission.Work.Peluse.Ulower.ssA.GapLocalAna
import Submission.Work.Peluse.Ulower.gap_numerics

set_option maxHeartbeats 4000000

namespace Work.Peluse.Ulower.SsA

theorem gap_local_block {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) :
    ∀ (s : ℕ) (hs : 2 ≤ s), ∃ A₀ : ℕ, 1 ≤ A₀ ∧
    ∀ (N N₀ D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ γ : ℝ),
      1 ≤ N → 1 ≤ N₀ → 1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ P.natDegree →
      2 * (N : ℝ) ^ P.natDegree < (N₀ : ℝ) → 0 < δ → δ ≤ 1 → 0 < γ → γ ≤ 1 →
      Work.Peluse.SupportIn f₀ N₀ → Work.Peluse.SupportIn f₁ N₀ →
      (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
      Work.Peluse.Ulower.ManyShiftsHypDensity P s N₀ N D f₀ f₁ δ γ →
      ∃ (a : ℤ) (Ns : ℕ) (δ' γ' : ℝ),
        1 ≤ Ns ∧ (N : ℝ) ≤ (Ns : ℝ) ∧
        (N : ℝ) ^ P.natDegree ≤ (A₀ : ℝ) * (Ns : ℝ) ∧
        (Ns : ℝ) ≤ (A₀ : ℝ) * (N : ℝ) ^ P.natDegree ∧
        a.natAbs ≤ A₀ * N₀ ∧
        0 < δ' ∧ 0 < γ' ∧ δ ≤ (A₀ : ℝ) * δ' ∧ γ * δ ≤ (A₀ : ℝ) * γ' ∧
        Work.Peluse.Ulower.ManyShiftsHypDensity P s Ns N D
          (Work.Peluse.Ulower.gapLocalise f₀ a Ns) (Work.Peluse.Ulower.gapLocalise f₁ a Ns) δ' γ' := by
  intro s hs
  refine ⟨gapA0 P s, ?_, ?_⟩
  · rw [gapA0]; omega
  · intro N N₀ D f₀ f₁ δ γ hN hN₀ hD hDN hgap hδ0 hδ1 hγ0 hγ1 hs0 hs1 hb0 hb1 hhyp
    have hd1 : 1 ≤ P.natDegree := by omega
    have hDle : D ≤ N ^ P.natDegree := by exact_mod_cast hDN
    have hgapN : 2 * N ^ P.natDegree < N₀ := by exact_mod_cast hgap
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNleN₀ : N ≤ N₀ := by
      have hNd : (N : ℝ) ≤ (N : ℝ) ^ P.natDegree := by
        calc (N : ℝ) = (N : ℝ) ^ 1 := by ring
          _ ≤ (N : ℝ) ^ P.natDegree := pow_le_pow_right₀ hNR (by omega)
      have h2 : (N : ℝ) ≤ (N₀ : ℝ) := by linarith
      exact_mod_cast h2
    obtain ⟨H, hHmem, hHcard, hHlev⟩ := hhyp
    obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ := gap_numerics P hd1 s N N₀ D hN hN₀ hDle hgapN
    have hNsGap : gapK0 P N + gapSig P s D ≤ gapHalf P s N :=
      gapK0_add_gapSig_le_gapHalf P hd1 s N D hN hDle
    have hNs : N ≤ gapNs P s N := le_gapNs (P := P) hd1 hN
    have hQpos : 0 < (arithIcc P.leadingCoeff D).card := arithIcc_card_pos (P := P) hD
    have hQposR : (0 : ℝ) < (((arithIcc P.leadingCoeff D).card : ℝ)) := by exact_mod_cast hQpos
    have hQne : (((arithIcc P.leadingCoeff D).card : ℝ)) ≠ 0 := ne_of_gt hQposR
    have hHne : H.Nonempty := by
      by_contra hcontra
      rw [Finset.not_nonempty_iff_eq_empty] at hcontra
      have hc := hHcard
      rw [hcontra, Finset.card_empty] at hc
      have hQ2 : (0 : ℝ) < ((arithIcc P.leadingCoeff D).card : ℝ) ^ (2 * (s - 2)) :=
        pow_pos hQposR _
      have h3 : (0 : ℝ) < γ * ((arithIcc P.leadingCoeff D).card : ℝ) ^ (2 * (s - 2)) :=
        mul_pos hγ0 hQ2
      have hc' : γ * ((arithIcc P.leadingCoeff D).card : ℝ) ^ (2 * (s - 2)) ≤ 0 := by
        simpa using hc
      linarith
    -- local notation
    let lev : ℤ → (Fin (s - 2) → ℤ × ℤ) → ℝ := fun a sh =>
      boxNormPow 2 (fun _ : Fin 2 => arithIcc P.leadingCoeff D)
        (symIcc (dSup P (gapNs P s N) N))
        (iterDelta (s - 2) sh (dualFn N P (gapLocalise f₀ a (gapNs P s N))
          (gapLocalise f₁ a (gapNs P s N))))
    set Tval : ℝ := (((2 * gapHalf P s N + 1 : ℕ) : ℝ) * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ)) * δ
      / ((2 * dSup P (gapNs P s N) N + 1 : ℕ) : ℝ) with hTval
    set del : ℝ := (((2 * gapHalf P s N + 1 : ℕ) : ℝ) * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ)) * δ /
      (2 * ((2 * gapR P s N N₀ D + 1 : ℕ) : ℝ) * ((2 * dSup P (gapNs P s N) N + 1 : ℕ) : ℝ))
      with hdel
    set gam : ℝ := (((2 * gapHalf P s N + 1 : ℕ) : ℝ) * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ)) * δ * γ /
      (8 * ((2 * gapR P s N N₀ D + 1 : ℕ) : ℝ) * ((2 * dSup P (gapNs P s N) N + 1 : ℕ) : ℝ))
      with hgam
    have hSnewpos : (0 : ℝ) < ((2 * dSup P (gapNs P s N) N + 1 : ℕ) : ℝ) := by positivity
    have hSnewne : ((2 * dSup P (gapNs P s N) N + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hSnewpos
    have hSoldpos : (0 : ℝ) < ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) := by positivity
    have hSoldne : ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hSoldpos
    have hAcardpos : (0 : ℝ) < ((2 * gapR P s N N₀ D + 1 : ℕ) : ℝ) := by positivity
    have hAcardne : ((2 * gapR P s N N₀ D + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hAcardpos
    have hl2pos : (0 : ℝ) < ((2 * gapHalf P s N + 1 : ℕ) : ℝ) := by positivity
    have hTpos : 0 < Tval := by rw [hTval]; positivity
    have hdelpos : 0 < del := by rw [hdel]; positivity
    have hgampos : 0 < gam := by rw [hgam]; positivity
    have hcardA : ((symIcc (gapR P s N N₀ D)).card : ℝ) = ((2 * gapR P s N N₀ D + 1 : ℕ) : ℝ) := by
      rw [symIcc_card']
    have hcardSold : ((symIcc (dSup P N₀ N)).card : ℝ) = ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) := by
      rw [symIcc_card']
    have hcardSnew : ((symIcc (dSup P (gapNs P s N) N)).card : ℝ)
        = ((2 * dSup P (gapNs P s N) N + 1 : ℕ) : ℝ) := by
      rw [symIcc_card']
    -- (1) the mass of the original data
    have hmass : ∀ sh ∈ H,
        δ * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) * (((arithIcc P.leadingCoeff D).card : ℝ)) ^ 4
          ≤ gapTot (arithIcc P.leadingCoeff D) (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) := by
      intro sh hsh
      have hmem : ∀ i, (sh i).1 ∈ arithIcc P.leadingCoeff D ∧
          (sh i).2 ∈ arithIcc P.leadingCoeff D := fun i => hHmem sh hsh i
      have h1 : δ ≤ (((symIcc (dSup P N₀ N)).card : ℝ))⁻¹ *
          ((((arithIcc P.leadingCoeff D).card : ℝ))⁻¹ ^ 4 *
            gapTot (arithIcc P.leadingCoeff D) (iterDelta (s - 2) sh (dualFn N P f₀ f₁))) := by
        have h := hHlev sh hsh
        have h2 := boxNormPow_two_eq_gapInner (Q := arithIcc P.leadingCoeff D)
          (S := symIcc (dSup P N₀ N)) (F := iterDelta (s - 2) sh (dualFn N P f₀ f₁))
          (FinSuppZ.of_supportIn (supportIn_iterDelta_dual (P := P) (s := s) (N := N) (N₀ := N₀)
            (D := D) hN hNleN₀ hs0 hs1 hmem))
        rw [h2] at h
        rwa [mul_assoc] at h
      have hQ4pos : (0 : ℝ) < (((arithIcc P.leadingCoeff D).card : ℝ)) ^ 4 := pow_pos hQposR _
      have h3 : δ * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) * (((arithIcc P.leadingCoeff D).card : ℝ)) ^ 4
          ≤ ((((symIcc (dSup P N₀ N)).card : ℝ))⁻¹ *
              ((((arithIcc P.leadingCoeff D).card : ℝ))⁻¹ ^ 4 *
                gapTot (arithIcc P.leadingCoeff D) (iterDelta (s - 2) sh (dualFn N P f₀ f₁))))
              * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) * (((arithIcc P.leadingCoeff D).card : ℝ)) ^ 4 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h1 (le_of_lt hSoldpos)) (le_of_lt hQ4pos)
      have h5 : ((((symIcc (dSup P N₀ N)).card : ℝ))⁻¹ *
              ((((arithIcc P.leadingCoeff D).card : ℝ))⁻¹ ^ 4 *
                gapTot (arithIcc P.leadingCoeff D) (iterDelta (s - 2) sh (dualFn N P f₀ f₁))))
              * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) * (((arithIcc P.leadingCoeff D).card : ℝ)) ^ 4
          = gapTot (arithIcc P.leadingCoeff D) (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) := by
        rw [hcardSold]
        field_simp
      linarith [h3, h5]
    -- (2) the averaging identity
    have havg : ∀ sh : Fin (s - 2) → ℤ × ℤ,
        (∀ i, (sh i).1 ∈ arithIcc P.leadingCoeff D ∧ (sh i).2 ∈ arithIcc P.leadingCoeff D) →
        ∑ a ∈ symIcc (gapR P s N N₀ D),
            gapMass (arithIcc P.leadingCoeff D) (iterDelta (s - 2) sh (dualFn N P f₀ f₁))
              (gapHalf P s N) a
          = ((2 * gapHalf P s N + 1 : ℕ) : ℝ) *
              gapTot (arithIcc P.leadingCoeff D) (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) := by
      intro sh hsh
      have hpair : ∀ a' ∈ arithIcc P.leadingCoeff D, ∀ b' ∈ arithIcc P.leadingCoeff D,
          (∑ a ∈ symIcc (gapR P s N N₀ D), ∑ x ∈ symIcc (gapHalf P s N),
              ‖gapInner (arithIcc P.leadingCoeff D) (iterDelta (s - 2) sh (dualFn N P f₀ f₁))
                a' b' (x + a)‖ ^ 2)
            = ((2 * gapHalf P s N + 1 : ℕ) : ℝ) *
              ∑' x : ℤ, ‖gapInner (arithIcc P.leadingCoeff D)
                (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) a' b' x‖ ^ 2 := by
        intro a' ha' b' hb'
        have hsup0 : SupportIn (iterDelta (s - 2) sh (dualFn N P f₀ f₁))
            (dSup P N₀ N + gapSig P s D) :=
          supportIn_iterDelta_dual (P := P) (s := s) (N := N) (N₀ := N₀) (D := D)
            hN hNleN₀ hs0 hs1 hsh
        refine sum_shift_window_eq (g := fun x : ℤ => ‖gapInner (arithIcc P.leadingCoeff D)
            (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) a' b' x‖ ^ 2)
          (ρ := gapRho P s N N₀ D) (l := gapHalf P s N) (R := gapR P s N N₀ D)
          (fun x => by positivity) ?_ ?_
        · have h5 : gapRho P s N N₀ D
              = dSup P N₀ N + gapSig P s D + 2 * (D * P.leadingCoeff.natAbs) := by
            rw [gapRho]
          rw [h5, gapR]
          omega
        · intro x hx
          rw [gapRho] at hx
          have h0 : gapInner (arithIcc P.leadingCoeff D)
              (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) a' b' x = 0 :=
            inner_support (B := dSup P N₀ N + gapSig P s D) hsup0
              (fun z hz => mem_arithIcc_le hz) ha' hb' x (by omega)
          rw [h0, norm_zero]
          ring
      calc ∑ a ∈ symIcc (gapR P s N N₀ D),
            gapMass (arithIcc P.leadingCoeff D) (iterDelta (s - 2) sh (dualFn N P f₀ f₁))
              (gapHalf P s N) a
          = ∑ a ∈ symIcc (gapR P s N N₀ D), ∑ a' ∈ arithIcc P.leadingCoeff D,
              ∑ b' ∈ arithIcc P.leadingCoeff D, ∑ x ∈ symIcc (gapHalf P s N),
                ‖gapInner (arithIcc P.leadingCoeff D)
                  (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) a' b' (x + a)‖ ^ 2 := by
              simp only [gapMass]
        _ = ∑ a' ∈ arithIcc P.leadingCoeff D, ∑ b' ∈ arithIcc P.leadingCoeff D,
              ∑ a ∈ symIcc (gapR P s N N₀ D), ∑ x ∈ symIcc (gapHalf P s N),
                ‖gapInner (arithIcc P.leadingCoeff D)
                  (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) a' b' (x + a)‖ ^ 2 := by
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl (fun a' _ => Finset.sum_comm)
        _ = ∑ a' ∈ arithIcc P.leadingCoeff D, ∑ b' ∈ arithIcc P.leadingCoeff D,
              ((2 * gapHalf P s N + 1 : ℕ) : ℝ) *
                ∑' x : ℤ, ‖gapInner (arithIcc P.leadingCoeff D)
                  (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) a' b' x‖ ^ 2 :=
              Finset.sum_congr rfl (fun a' ha' =>
                Finset.sum_congr rfl (fun b' hb' => hpair a' ha' b' hb'))
        _ = ((2 * gapHalf P s N + 1 : ℕ) : ℝ) *
              gapTot (arithIcc P.leadingCoeff D)
                (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) := by
              rw [gapTot, Finset.mul_sum]
              refine Finset.sum_congr rfl (fun a' _ => ?_)
              rw [Finset.mul_sum]
    -- (3) the pointwise level comparison
    have hcmp : ∀ sh : Fin (s - 2) → ℤ × ℤ,
        (∀ i, (sh i).1 ∈ arithIcc P.leadingCoeff D ∧ (sh i).2 ∈ arithIcc P.leadingCoeff D) →
        ∀ a ∈ symIcc (gapR P s N N₀ D),
          (((arithIcc P.leadingCoeff D).card : ℝ))⁻¹ ^ 4 *
              gapMass (arithIcc P.leadingCoeff D)
                (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) (gapHalf P s N) a
            ≤ ((2 * dSup P (gapNs P s N) N + 1 : ℕ) : ℝ) * lev a sh := by
      intro sh hsh a _
      have h1 := boxNorm_gapLocalise_ge (P := P) (N₀ := N₀) hs hN hD hNs hNsGap
        (f₀ := f₀) (f₁ := f₁) a hsh
      rw [hcardSnew] at h1
      exact h1
    -- (4) the sum bound
    have hper : ∀ sh ∈ H, Tval ≤ ∑ a ∈ symIcc (gapR P s N N₀ D), lev a sh := by
      intro sh hsh
      rw [hTval]
      have hmem : ∀ i, (sh i).1 ∈ arithIcc P.leadingCoeff D ∧
          (sh i).2 ∈ arithIcc P.leadingCoeff D := fun i => hHmem sh hsh i
      have hm := hmass sh hsh
      have ha := havg sh hmem
      have hsum : (((arithIcc P.leadingCoeff D).card : ℝ))⁻¹ ^ 4 *
            (∑ a ∈ symIcc (gapR P s N N₀ D),
              gapMass (arithIcc P.leadingCoeff D)
                (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) (gapHalf P s N) a)
          ≤ ((2 * dSup P (gapNs P s N) N + 1 : ℕ) : ℝ) *
            (∑ a ∈ symIcc (gapR P s N N₀ D), lev a sh) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_le_sum (fun a ha => hcmp sh hmem a ha)
      rw [ha] at hsum
      have hQ4pos : (0 : ℝ) < (((arithIcc P.leadingCoeff D).card : ℝ)) ^ 4 := pow_pos hQposR _
      have hstep : (((2 * gapHalf P s N + 1 : ℕ) : ℝ)) *
            (δ * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) * (((arithIcc P.leadingCoeff D).card : ℝ)) ^ 4)
          ≤ ((2 * gapHalf P s N + 1 : ℕ) : ℝ) *
            gapTot (arithIcc P.leadingCoeff D) (iterDelta (s - 2) sh (dualFn N P f₀ f₁)) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      have h1 : (((arithIcc P.leadingCoeff D).card : ℝ))⁻¹ ^ 4 *
            (((2 * gapHalf P s N + 1 : ℕ) : ℝ) *
              (δ * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) * (((arithIcc P.leadingCoeff D).card : ℝ)) ^ 4))
          ≤ (((arithIcc P.leadingCoeff D).card : ℝ))⁻¹ ^ 4 *
            (((2 * gapHalf P s N + 1 : ℕ) : ℝ) *
              gapTot (arithIcc P.leadingCoeff D) (iterDelta (s - 2) sh (dualFn N P f₀ f₁))) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
      have h2 : (((arithIcc P.leadingCoeff D).card : ℝ))⁻¹ ^ 4 *
            (((2 * gapHalf P s N + 1 : ℕ) : ℝ) *
              (δ * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) * (((arithIcc P.leadingCoeff D).card : ℝ)) ^ 4))
          = ((2 * gapHalf P s N + 1 : ℕ) : ℝ) * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) * δ := by
        field_simp
      have hmain : ((2 * gapHalf P s N + 1 : ℕ) : ℝ) * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) * δ
          ≤ ((2 * dSup P (gapNs P s N) N + 1 : ℕ) : ℝ) *
            (∑ a ∈ symIcc (gapR P s N N₀ D), lev a sh) := by
        linarith [hsum, h1, h2]
      rw [div_le_iff₀ hSnewpos]
      linarith [hmain]
    -- (5) the uniform upper bound
    have hle2 : ∀ (a : ℤ) (sh : Fin (s - 2) → ℤ × ℤ),
        (∀ i, (sh i).1 ∈ arithIcc P.leadingCoeff D ∧ (sh i).2 ∈ arithIcc P.leadingCoeff D) →
        lev a sh ≤ 2 := by
      intro a sh hsh
      exact boxNorm_gapLocalise_le_two (P := P) hN hNs hDle hb0 hb1 a hsh
    -- (6) Chebyshev
    have hthresh : Tval / (2 * ((symIcc (gapR P s N N₀ D)).card : ℝ)) = del := by
      rw [hdel, hTval, hcardA]
      ring
    have hcheb : ∀ sh ∈ H,
        Tval / 4 ≤ (((symIcc (gapR P s N N₀ D)).filter (fun a => del ≤ lev a sh)).card : ℝ) := by
      intro sh hsh
      have h := card_filter_ge (t := symIcc (gapR P s N N₀ D)) (f := fun a : ℤ => lev a sh)
        (T := Tval) (B := 2) (by norm_num)
        (fun a _ => norm_nonneg _)
        (fun a _ => hle2 a sh (fun i => hHmem sh hsh i))
        (hper sh hsh)
      simp only [hthresh] at h
      have h2 : (2 : ℝ) * 2 = 4 := by norm_num
      rw [h2] at h
      exact h
    -- (7) the pigeonhole
    let hind : ℤ → (Fin (s - 2) → ℤ × ℤ) → ℝ := fun a sh => if del ≤ lev a sh then (1 : ℝ) else 0
    have hfilt : ∀ sh ∈ H, Tval / 4 ≤ ∑ a ∈ symIcc (gapR P s N N₀ D), hind a sh := by
      intro sh hsh
      have h := hcheb sh hsh
      rw [← Finset.sum_boole] at h
      exact h
    obtain ⟨a, haA, hcount⟩ := exists_common_block (t := H)
      (A := symIcc (gapR P s N N₀ D)) (f := hind) (c := Tval / 4)
      ⟨0, by rw [mem_symIcc_iff]; positivity⟩ (fun sh hsh => hfilt sh hsh) hHne
    have hgood : gam * (((arithIcc P.leadingCoeff D).card : ℝ)) ^ (2 * (s - 2))
        ≤ (((H.filter (fun sh => del ≤ lev a sh)).card : ℝ)) := by
      rw [← Finset.sum_boole]
      have hQ2 : (0 : ℝ) < ((arithIcc P.leadingCoeff D).card : ℝ) ^ (2 * (s - 2)) :=
        pow_pos hQposR _
      have hT4 : (0 : ℝ) ≤ Tval / 4 := by positivity
      have h1 : Tval / 4 * (γ * ((arithIcc P.leadingCoeff D).card : ℝ) ^ (2 * (s - 2)))
            / ((symIcc (gapR P s N N₀ D)).card : ℝ)
          ≤ Tval / 4 * (H.card : ℝ) / ((symIcc (gapR P s N N₀ D)).card : ℝ) := by
        refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hHcard hT4) (by positivity)
      have h2 : gam * (((arithIcc P.leadingCoeff D).card : ℝ)) ^ (2 * (s - 2))
          = (Tval / 4 * (γ * ((arithIcc P.leadingCoeff D).card : ℝ) ^ (2 * (s - 2)))
            / ((symIcc (gapR P s N N₀ D)).card : ℝ)) / 2 := by
        rw [hgam, hTval, hcardA]
        field_simp
        ring
      rw [h2, hcardA] at *
      have hX : (0 : ℝ) ≤ Tval / 4 * (γ * ((arithIcc P.leadingCoeff D).card : ℝ) ^ (2 * (s - 2)))
            / ((2 * gapR P s N N₀ D + 1 : ℕ) : ℝ) := by positivity
      exact le_trans (le_trans (div_le_self hX (by norm_num)) h1) hcount
    -- conclusion
    refine ⟨a, gapNs P s N, del, gam, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [gapNs, gapC2]
      exact Nat.mul_pos (by omega) (pow_pos (by omega : 0 < N) _)
    · exact_mod_cast hn2
    · exact_mod_cast hn3
    · exact_mod_cast hn4
    · rw [mem_symIcc_iff] at haA
      have h1 : ((a.natAbs : ℕ) : ℝ) ≤ ((gapR P s N N₀ D : ℕ) : ℝ) := by exact_mod_cast haA
      have h2 : ((gapR P s N N₀ D : ℕ) : ℝ) ≤ (gapA0 P s : ℝ) * (N₀ : ℝ) := by exact_mod_cast hn1
      exact_mod_cast (le_trans h1 h2)
    · exact hdelpos
    · exact hgampos
    · rw [hdel, ← mul_div_assoc]
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * ((2 * gapR P s N N₀ D + 1 : ℕ) : ℝ)
        * ((2 * dSup P (gapNs P s N) N + 1 : ℕ) : ℝ))]
      nlinarith [hn5, hδ0, hl2pos, hSoldpos, hAcardpos, hSnewpos]
    · rw [hgam, ← mul_div_assoc]
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 8 * ((2 * gapR P s N N₀ D + 1 : ℕ) : ℝ)
        * ((2 * dSup P (gapNs P s N) N + 1 : ℕ) : ℝ))]
      have hmult : (γ * δ) * (8 * ((2 * gapR P s N N₀ D + 1 : ℕ) : ℝ)
            * ((2 * dSup P (gapNs P s N) N + 1 : ℕ) : ℝ))
          ≤ (γ * δ) * ((gapA0 P s : ℝ) * (((2 * gapHalf P s N + 1 : ℕ) : ℝ)
            * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hn6 (by positivity)
      have hEq : (γ * δ) * ((gapA0 P s : ℝ) * (((2 * gapHalf P s N + 1 : ℕ) : ℝ)
            * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ)))
          = (gapA0 P s : ℝ) * (((2 * gapHalf P s N + 1 : ℕ) : ℝ)
            * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ) * δ * γ) := by ring
      linarith [hmult, hEq]
    · exact ⟨H.filter (fun sh => del ≤ lev a sh),
        (by
          intro sh hsh i
          have h1 : sh ∈ H := (Finset.mem_filter.mp hsh).1
          exact hHmem sh h1 i),
        hgood,
        (by
          intro sh hsh
          exact (Finset.mem_filter.mp hsh).2)⟩

end Work.Peluse.Ulower.SsA
