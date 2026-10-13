import Mathlib
import Submission.Work.WilE4.CAD.seq_sign_lemmas

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open Classical Filter
open scoped Topology

namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (spec)

variable {m k : ℕ}

/-! ## Elementary facts about the coercion of `SignType` to `ℝ` -/

private theorem sign_coe_sign (s : SignType) : SignType.sign (s : ℝ) = s := by
  rcases s with _ | _ | _ <;> simp [SignType.castHom_apply, sign_pos, sign_neg, sign_zero]

private theorem abs_coe_sign {s : SignType} (hs : s ≠ 0) : |(s : ℝ)| = 1 := by
  rcases s with _ | _ | _ <;> simp_all [SignType.castHom_apply]

private theorem mul_self_sign {s : SignType} (hs : s ≠ 0) : s * s = 1 := by
  rcases s with _ | _ | _ <;> simp_all

private theorem abs_cast_mul {s : SignType} (hs : s ≠ 0) (x : ℝ) (hx : 0 < x) :
    |(s : ℝ) * x| = x := by
  rw [abs_mul, abs_coe_sign hs, one_mul, abs_of_pos hx]

/-- **The bounded case of the sequential closedness.**

Suppose that at every point `x n` of a sequence in `C` converging to `x₀` some witness `t n`
realises the sign vector `v'`, and that `t n → t₀`.  Suppose moreover that for every member that
does not vanish identically on `C` and does vanish at `(x₀, t₀)` the fibre at `x n` has a *unique*
root `hz n` in the disk of radius `ρ` around `t₀` (with the multiplicity of the limit root).  Then
`v'` is realised at `x₀`.

The geometric input (the existence of the common cluster point `hz`, its uniqueness in the disk and
the transfer of multiplicities) is isolated in the hypotheses; it is what the gcd/Sylvester data
provides. -/
theorem seq_closed_bounded (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ) (D : ℕ)
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D)
    (C : Set (Fin m → ℝ))
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((spec (P i) x).coeff j) = SignType.sign ((spec (P i) x').coeff j))
    (v' : Fin k → SignType) (x : ℕ → Fin m → ℝ) (hxC : ∀ n, x n ∈ C) {x₀ : Fin m → ℝ}
    (hx₀ : x₀ ∈ C) (hlim : Filter.Tendsto x Filter.atTop (nhds x₀))
    (t : ℕ → ℝ) (ht : ∀ n, ∀ i : Fin k, SignType.sign ((spec (P i) (x n)).eval (t n)) = v' i)
    {t₀ : ℝ} (htlim : Filter.Tendsto t Filter.atTop (nhds t₀))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hz : ℕ → ℝ) (hzlim : Filter.Tendsto hz Filter.atTop (nhds t₀))
    (hzdisk : ∀ᶠ n in Filter.atTop, |hz n - t₀| < ρ)
    (hzroot : ∀ᶠ n in Filter.atTop, ∀ i : Fin k, (spec (P i) x₀) ≠ 0 →
      (spec (P i) x₀).eval t₀ = 0 → (spec (P i) (x n)).eval (hz n) = 0)
    (hzuniq : ∀ᶠ n in Filter.atTop, ∀ i : Fin k, (spec (P i) x₀) ≠ 0 →
      (spec (P i) x₀).eval t₀ = 0 →
      ∀ w : ℝ, (spec (P i) (x n)).eval w = 0 → |w - t₀| < ρ → w = hz n)
    (hmult : ∀ᶠ n in Filter.atTop, ∀ i : Fin k, (spec (P i) x₀) ≠ 0 →
      (spec (P i) x₀).eval t₀ = 0 →
      (spec (P i) (x n)).rootMultiplicity (hz n) = (spec (P i) x₀).rootMultiplicity t₀)
    (hε : ∃ ε : ℝ, 0 < ε ∧ ε < ρ ∧ ∀ i : Fin k, (spec (P i) x₀) ≠ 0 →
      ∀ w : ℝ, (spec (P i) x₀).eval w = 0 → |w - t₀| ≤ ε → w = t₀) :
    ∃ s : ℝ, ∀ i : Fin k, SignType.sign ((spec (P i) x₀).eval s) = v' i := by
  classical
  have hdeg : ∀ i : Fin k, ∀ y : Fin m → ℝ, (spec (P i) y).natDegree ≤ D :=
    fun i y => spec_natDegree_le_of_degreeOf (P i) D (hD i) y
  have hlim_eval : ∀ i : Fin k, Filter.Tendsto (fun n => (spec (P i) (x n)).eval (t n))
      Filter.atTop (nhds ((spec (P i) x₀).eval t₀)) := fun i =>
    tendsto_spec_eval (P i) D (hdeg i) hlim htlim
  -- (1) a zero coordinate forces the fibre to vanish at the limit point
  have hZW : ∀ i : Fin k, v' i = 0 → (spec (P i) x₀).eval t₀ = 0 := by
    intro i hi
    have hz0 : ∀ n : ℕ, (spec (P i) (x n)).eval (t n) = 0 := fun n => by
      have h := ht n i
      rw [hi] at h
      exact sign_eq_zero_iff.mp h
    exact tendsto_nhds_unique (hlim_eval i)
      (Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => (hz0 n).symm)
        tendsto_const_nhds)
  -- (2) a member vanishing identically on `C` has a zero coordinate
  have hfibzero : ∀ i : Fin k, spec (P i) x₀ = 0 → v' i = 0 := by
    intro i hi
    have h0 : (spec (P i) (x 0)).eval (t 0) = 0 := by
      rw [(spec_eq_zero_iff_on_C hD hcoeff (hxC 0) hx₀).mpr hi]
      simp
    have h := ht 0 i
    rw [h0, sign_zero] at h
    exact h.symm
  -- (3) the sign at a non-vanishing point is the prescribed one
  have hsign : ∀ i : Fin k, (spec (P i) x₀).eval t₀ ≠ 0 →
      SignType.sign ((spec (P i) x₀).eval t₀) = v' i := fun i hne => by
    obtain ⟨n, hn⟩ := (eventually_sign_eq_of_tendsto' (hlim_eval i) hne).exists
    rw [← hn, ht n i]
  by_cases hcase : ∀ i : Fin k, (spec (P i) x₀).eval t₀ = 0 → v' i = 0
  · -- Case I: `t₀` itself is a witness
    refine ⟨t₀, fun i => ?_⟩
    by_cases hi : (spec (P i) x₀).eval t₀ = 0
    · rw [show SignType.sign ((spec (P i) x₀).eval t₀) = 0 from by rw [hi, sign_zero],
        hcase i hi]
    · exact hsign i hi
  · push_neg at hcase
    obtain ⟨i₁, hi₁0, hi₁v⟩ := hcase
    have hi₁ne : spec (P i₁) x₀ ≠ 0 := fun h => hi₁v (hfibzero i₁ h)
    -- (4) no member with a non-vanishing fibre and a zero coordinate vanishes at `t₀`
    have hZempty : ∀ j : Fin k, v' j = 0 → spec (P j) x₀ ≠ 0 → False := by
      intro j hjv hjne
      have hrootj : ∀ᶠ n in Filter.atTop, (spec (P j) (x n)).eval (t n) = 0 :=
        Filter.Eventually.of_forall fun n => by
          have h := ht n j
          rw [hjv] at h
          exact sign_eq_zero_iff.mp h
      have htin : ∀ᶠ n in Filter.atTop, |t n - t₀| < ρ :=
        (htlim.eventually (Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_self]; exact hρ))).mono
          fun n hn => by simpa [Metric.mem_ball, Real.dist_eq] using hn
      obtain ⟨n, h1, h2, h4, htin_n⟩ := (hzroot.and (hzuniq.and (hrootj.and htin))).exists
      have htj : t n = hz n := h2 j hjne (hZW j hjv) (t n) h4 htin_n
      have hroot_i₁ : (spec (P i₁) (x n)).eval (t n) = 0 := by
        rw [htj]
        exact h1 i₁ hi₁ne hi₁0
      have hzero : v' i₁ = 0 := by
        have h := ht n i₁
        rw [hroot_i₁, sign_zero] at h
        exact h.symm
      exact hi₁v hzero
    have hnonzero : ∀ j : Fin k, spec (P j) x₀ ≠ 0 → v' j ≠ 0 := fun j hjne hjv =>
      hZempty j hjv hjne
    -- (5) the geometric data
    obtain ⟨ε, hεpos, hερ, hεroot⟩ := hε
    set ε₂ : ℝ := min (ε / 4) (ρ / 4) with hε₂def
    have hε₂pos : 0 < ε₂ := lt_min (by linarith) (by linarith)
    have hε₂ε : ε₂ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hε₂ρ : ε₂ < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hε₂half : ε₂ < ρ / 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    -- (6) the side relative to the cluster
    set sn : ℕ → SignType := fun n => SignType.sign (t n - hz n) with hsn
    have hsn_freq : ∃ s : SignType, s ≠ 0 ∧ ∃ᶠ n in Filter.atTop, sn n = s := by
      have hne0 : ∀ᶠ n in Filter.atTop, sn n ≠ 0 := by
        filter_upwards [hzroot, hzuniq] with n hr hu h0
        have htn_hz : t n = hz n := by
          have h := sign_eq_zero_iff.mp (by simpa [hsn] using h0)
          linarith
        have hri : (spec (P i₁) (x n)).eval (hz n) = 0 := hr i₁ hi₁ne hi₁0
        have hti : (spec (P i₁) (x n)).eval (t n) ≠ 0 := fun h => hi₁v (by
          have hh := ht n i₁
          rw [h, sign_zero] at hh
          exact hh.symm)
        rw [← htn_hz] at hri
        exact hti hri
      have hpm : ∀ᶠ n in Filter.atTop, sn n = 1 ∨ sn n = -1 := by
        filter_upwards [hne0] with n hn
        rcases lt_trichotomy (t n - hz n) 0 with h | h | h
        · exact Or.inr (by rw [hsn]; exact sign_neg h)
        · exact absurd (by
            show SignType.sign (t n - hz n) = 0
            rw [h, sign_zero]) hn
        · exact Or.inl (by rw [hsn]; exact sign_pos h)
      by_contra hcon
      push_neg at hcon
      have hzero : ∀ᶠ n in Filter.atTop, sn n = 0 := by
        filter_upwards [hpm, hcon 1 (by decide), hcon (-1) (by decide)] with n hn h1 h2
        rcases hn with h | h
        · exact absurd h h1
        · exact absurd h h2
      obtain ⟨n, hn1, hn2⟩ := (hzero.and hne0).exists
      exact hn2 hn1
    obtain ⟨s, hsne, hsfreq⟩ := hsn_freq
    -- (7) the good index
    have hcont : ∀ i : Fin k, Filter.Tendsto
        (fun n => (spec (P i) (x n)).eval (hz n + (s : ℝ) * ε₂)) Filter.atTop
        (nhds ((spec (P i) x₀).eval (t₀ + (s : ℝ) * ε₂))) := fun i =>
      tendsto_spec_eval (P i) D (hdeg i) hlim (hzlim.add tendsto_const_nhds)
    have hgood : ∀ᶠ n in Filter.atTop,
        (|t n - t₀| < ε₂) ∧ (|hz n - t₀| < ε₂) ∧
        (∀ i : Fin k, (spec (P i) x₀) ≠ 0 → (spec (P i) x₀).eval t₀ = 0 →
          (spec (P i) (x n)).eval (hz n) = 0 ∧
          (∀ w : ℝ, (spec (P i) (x n)).eval w = 0 → |w - t₀| < ρ → w = hz n) ∧
          ((spec (P i) (x n)).rootMultiplicity (hz n) =
            (spec (P i) x₀).rootMultiplicity t₀) ∧
          (SignType.sign ((spec (P i) (x n)).eval (hz n + (s : ℝ) * ε₂)) =
            SignType.sign ((spec (P i) x₀).eval (t₀ + (s : ℝ) * ε₂)))) := by
      have htε : ∀ᶠ n in Filter.atTop, |t n - t₀| < ε₂ :=
        (htlim.eventually
          (Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_self]; exact hε₂pos))).mono
          fun n hn => by simpa [Metric.mem_ball, Real.dist_eq] using hn
      have hzε : ∀ᶠ n in Filter.atTop, |hz n - t₀| < ε₂ :=
        (hzlim.eventually
          (Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_self]; exact hε₂pos))).mono
          fun n hn => by simpa [Metric.mem_ball, Real.dist_eq] using hn
      have hsignlim : ∀ᶠ n in Filter.atTop, ∀ i : Fin k, (spec (P i) x₀) ≠ 0 →
          (spec (P i) x₀).eval t₀ = 0 →
          SignType.sign ((spec (P i) (x n)).eval (hz n + (s : ℝ) * ε₂)) =
            SignType.sign ((spec (P i) x₀).eval (t₀ + (s : ℝ) * ε₂)) := by
        refine (Filter.eventually_all).mpr fun i => ?_
        by_cases hine : spec (P i) x₀ = 0
        · exact Filter.Eventually.of_forall fun n _ _ => by
            rw [(spec_eq_zero_iff_on_C hD hcoeff (hxC n) hx₀).mpr hine, hine]
            simp
        · by_cases hi0 : (spec (P i) x₀).eval t₀ = 0
          · have hne : (spec (P i) x₀).eval (t₀ + (s : ℝ) * ε₂) ≠ 0 := by
              intro h0
              have habs : |t₀ + (s : ℝ) * ε₂ - t₀| ≤ ε := by
                rw [show t₀ + (s : ℝ) * ε₂ - t₀ = (s : ℝ) * ε₂ by ring, abs_mul,
                  abs_coe_sign hsne, one_mul, abs_of_pos hε₂pos]
                exact le_of_lt hε₂ε
              have hw : t₀ + (s : ℝ) * ε₂ = t₀ := hεroot i hine (t₀ + (s : ℝ) * ε₂) h0 habs
              have hz0 : (s : ℝ) * ε₂ = 0 := by linarith
              have hs0 : (s : ℝ) = 0 := by
                rcases mul_eq_zero.mp hz0 with h | h
                · exact h
                · exact absurd h (ne_of_gt hε₂pos)
              exact hsne (by rw [← sign_coe_sign s, hs0, sign_zero])
            filter_upwards [eventually_sign_eq_of_tendsto' (hcont i) hne] with n hn _ _
            exact hn
          · exact Filter.Eventually.of_forall fun n _ hi0' => absurd hi0' hi0
      filter_upwards [htε, hzε, hzroot, hzuniq, hmult, hsignlim] with n ht_n hz_n hr hu hm hs
      exact ⟨ht_n, hz_n, fun i hine hi0 => ⟨hr i hine hi0, hu i hine hi0, hm i hine hi0,
        hs i hine hi0⟩⟩
    obtain ⟨n₀, hn₀, hn₀side⟩ := (hgood.and_frequently hsfreq).exists
    obtain ⟨hn₀t, hn₀z, hn₀data⟩ := hn₀
    -- (8) the witness
    refine ⟨t₀ + (s : ℝ) * ε₂, fun i => ?_⟩
    by_cases hfib : spec (P i) x₀ = 0
    · rw [show (spec (P i) x₀).eval (t₀ + (s : ℝ) * ε₂) = 0 from by
          rw [(spec_eq_zero_iff_on_C hD hcoeff hx₀ hx₀).mpr hfib]; simp,
        hfibzero i hfib, sign_zero]
    · by_cases hi0 : (spec (P i) x₀).eval t₀ = 0
      · obtain ⟨hrootn₀, huniqn₀, hmultn₀, hsignn₀⟩ := hn₀data i hfib hi0
        have hprod : 0 < (t n₀ - hz n₀) * (hz n₀ + (s : ℝ) * ε₂ - hz n₀) := by
          have hval : hz n₀ + (s : ℝ) * ε₂ - hz n₀ = (s : ℝ) * ε₂ := by ring
          rw [hval]
          have h1 : SignType.sign ((s : ℝ) * ε₂) = s := by
            rw [sign_mul, sign_coe_sign, sign_pos hε₂pos, mul_one]
          have hside : SignType.sign (t n₀ - hz n₀) = s := hn₀side
          have h2 : SignType.sign ((t n₀ - hz n₀) * ((s : ℝ) * ε₂)) = 1 := by
            rw [sign_mul, h1, hside, mul_self_sign hsne]
          exact sign_eq_one_iff.mp h2
        have hdist : |t n₀ - hz n₀| < ρ := by
          have h1 : |t n₀ - hz n₀| ≤ |t n₀ - t₀| + |hz n₀ - t₀| := by
            have htri := dist_triangle (t n₀) t₀ (hz n₀)
            rwa [Real.dist_eq, Real.dist_eq, Real.dist_eq, abs_sub_comm t₀ (hz n₀)] at htri
          have h2ε : ε₂ < ρ / 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
          linarith
        have hfibn : spec (P i) (x n₀) ≠ 0 := fun h =>
          hfib ((spec_eq_zero_iff_on_C hD hcoeff hx₀ (hxC n₀)).mpr h)
        have hα := sign_eq_of_unique_root (f := spec (P i) (x n₀)) (t₀ := t₀) hfibn hrootn₀
          (fun w hw hwρ => huniqn₀ w hw hwρ) (by linarith [hn₀t, hε₂ρ]) (by
            have htri : dist (hz n₀ + (s : ℝ) * ε₂) t₀
                ≤ dist (hz n₀ + (s : ℝ) * ε₂) (hz n₀) + dist (hz n₀) t₀ :=
              dist_triangle _ _ _
            rw [Real.dist_eq, Real.dist_eq, Real.dist_eq] at htri
            rw [show hz n₀ + (s : ℝ) * ε₂ - hz n₀ = (s : ℝ) * ε₂ by ring,
              abs_cast_mul hsne ε₂ hε₂pos] at htri
            linarith [htri, hn₀z, hε₂half, hρ]) hprod
        rw [ht n₀ i, hsignn₀] at hα
        exact hα.symm
      · -- `t₀` is not a root of this member
        have hsign_t₀ : SignType.sign ((spec (P i) x₀).eval t₀) = v' i := hsign i hi0
        have hno : ∀ w ∈ Set.Icc (t₀ - ε) (t₀ + ε), (spec (P i) x₀).eval w ≠ 0 := by
          intro w hw h0
          have habs : |w - t₀| ≤ ε := by
            rw [abs_le]
            exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
          exact hi0 (by rw [← hεroot i hfib w h0 habs]; exact h0)
        have hmem : t₀ + (s : ℝ) * ε₂ ∈ Set.Icc (t₀ - ε) (t₀ + ε) := by
          have habs : |t₀ + (s : ℝ) * ε₂ - t₀| ≤ ε := by
            rw [show t₀ + (s : ℝ) * ε₂ - t₀ = (s : ℝ) * ε₂ by ring, abs_mul,
              abs_coe_sign hsne, one_mul, abs_of_pos hε₂pos]
            exact le_of_lt hε₂ε
          rw [abs_le] at habs
          exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
        have hsgn := sign_eq_of_no_root_Icc (Polynomial.continuous (spec (P i) x₀))
          (by linarith : t₀ - ε ≤ t₀ + ε) hno
          (show t₀ ∈ Set.Icc (t₀ - ε) (t₀ + ε) from ⟨by linarith, by linarith⟩) hmem
        rw [← hsgn]
        exact hsign_t₀

end Work.WilE4.CAD
