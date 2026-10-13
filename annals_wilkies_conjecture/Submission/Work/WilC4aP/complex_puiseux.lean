import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.Props
import Submission.Work.WilC4aP.PzAlg
import Submission.Work.WilC4aP.branches_shift
import Submission.Work.WilC4aP.branches_mul
import Submission.Work.WilC4aP.branches_newton
import Submission.Work.WilC4aP.newton_step
import Submission.Work.WilC4aP.descent_holCoeffs_div
import Submission.Work.WilC4aP.root_mult
import Submission.Work.WilC4aP.tschirnhausen_reduce

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators Topology

namespace Work.WilC4aP

open Polynomial

/-! ## Eventual factorization

The induction below is carried out in the *germ* form: the factorization is required to hold in a
neighbourhood of `u = 0` and the branches are analytic at `0`. This avoids keeping track of the
radius at every step; the ball-wise statement `FactoredOn` of `Basic` is recovered at the end. -/

/-- Near `u = 0` the fibre of `P` over the ramification `s = u ^ N` is the product of the linear
factors `X - η j u`. -/
def FactoredGerm {m : ℕ} (P : Polynomial (ℂ → ℂ)) (N : ℕ) (η : Fin m → ℂ → ℂ) : Prop :=
  ∀ᶠ u in 𝓝 (0 : ℂ), Pz P (u ^ N) = ∏ j, (X - C (η j u))

lemma factoredGerm_of_ball {m : ℕ} {P : Polynomial (ℂ → ℂ)} {N : ℕ} {η : Fin m → ℂ → ℂ}
    {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ u ∈ Metric.ball (0 : ℂ) ρ, Pz P (u ^ N) = ∏ j, (X - C (η j u))) :
    FactoredGerm P N η := by
  refine Metric.eventually_nhds_iff.mpr ⟨ρ, hρ, ?_⟩
  intro u hu
  exact h u hu

lemma ball_of_factoredGerm {m : ℕ} {P : Polynomial (ℂ → ℂ)} {N : ℕ} {η : Fin m → ℂ → ℂ}
    (h : FactoredGerm P N η) :
    ∃ ρ > 0, ∀ u ∈ Metric.ball (0 : ℂ) ρ, Pz P (u ^ N) = ∏ j, (X - C (η j u)) := by
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨ρ, hρ, fun u hu => hρ' hu⟩

/-- A monic polynomial of degree `m` all of whose lower coefficients vanish to infinite order at
`0` agrees with `X ^ m` on a disk around `0`. -/
lemma Pz_eq_X_pow_on_ball {m : ℕ} {R : Polynomial (ℂ → ℂ)} (hmon : R.Monic)
    (hdeg : R.natDegree = m) (hall : ∀ i : Fin m, analyticOrderAt (R.coeff i) 0 = ⊤) :
    ∃ ρ > 0, ∀ z ∈ Metric.ball (0 : ℂ) ρ, Pz R z = X ^ m := by
  have hcoe : ∀ i : Fin m, ∀ᶠ z in 𝓝 (0 : ℂ), R.coeff i z = 0 :=
    fun i => analyticOrderAt_eq_top.mp (hall i)
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ i ∈ (Finset.univ : Finset (Fin m)), R.coeff i z = 0 :=
    (Filter.eventually_all_finset _).mpr (fun i _ => by simpa using hcoe i)
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ρ, hρ, fun z hz => ?_⟩
  have hz0 : ∀ i ∈ (Finset.univ : Finset (Fin m)), R.coeff i z = 0 :=
    hρ' (Metric.mem_ball.mp hz)
  ext n
  rw [Pz, Polynomial.coeff_map, evAt_apply]
  by_cases h1 : n < m
  · rw [show R.coeff n z = 0 from hz0 ⟨n, h1⟩ (Finset.mem_univ _), Polynomial.coeff_X_pow,
      ite_eq_right (by omega)]
  · rw [not_lt] at h1
    by_cases h2 : n = m
    · subst h2
      rw [Polynomial.coeff_X_pow, ite_eq_left rfl, ← hdeg, hmon.coeff_natDegree]
      simp
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega), Polynomial.coeff_X_pow,
        ite_eq_right (by omega)]
      simp

/-- The complex Puiseux statement in germ form: every monic polynomial with holomorphic
coefficients at `0` has roots given by finitely many functions analytic at `0` after some
ramification `s = u ^ N`, the factorization holding near `u = 0`. -/
lemma puiseux_germ (h5 : ClusterSplitting) :
    ∀ {m : ℕ} (P : Polynomial (ℂ → ℂ)), P.Monic → P.natDegree = m → HolCoeffs P 0 →
      ∃ (N : ℕ) (η : Fin m → ℂ → ℂ), 0 < N ∧ (∀ j, AnalyticAt ℂ (η j) 0) ∧
        FactoredGerm P N η := by
  intro m
  refine Nat.strong_induction_on m ?_
  intro m ih P hmon hdeg hhol
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    have hP1 : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg
    refine ⟨1, Fin.elim0, one_pos, fun j => j.elim0, ?_⟩
    refine Filter.Eventually.of_forall fun u => ?_
    rw [hP1, pow_one]
    simp [Pz]
  · rcases Nat.lt_or_ge m 2 with hm1 | hm2
    · -- `m = 1`: `P = X + C c` and the single branch is `-c`
      obtain rfl : m = 1 := by omega
      have hP : P = X + C (P.coeff 0) := hmon.eq_X_add_C hdeg
      refine ⟨1, fun _ => -(P.coeff 0), one_pos, fun j => (hhol 0).neg, ?_⟩
      refine Filter.Eventually.of_forall fun u => ?_
      rw [pow_one, hP, Pz_add, Pz_X, Pz, Polynomial.map_C, evAt_apply]
      simp [Polynomial.C_neg]
    · -- `m ≥ 2`
      have hp0 : Pz P 0 ≠ 0 := (monic_Pz hmon 0).ne_zero
      have hnat : (Pz P 0).natDegree = m := (natDegree_Pz hmon 0).trans hdeg
      have hdegne : (Pz P 0).degree ≠ 0 := by
        rw [Polynomial.degree_eq_natDegree hp0, hnat]
        exact_mod_cast (by omega : m ≠ 0)
      obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (Pz P 0) hdegne
      have hα0 : (Pz P 0).eval α = 0 := hα
      set k : ℕ := (Pz P 0).rootMultiplicity α with hk
      have hkrs : (Pz P 0).rootMultiplicity α = k := hk.symm
      have hkpos : 0 < k :=
        (Polynomial.rootMultiplicity_pos hp0).mpr (Polynomial.IsRoot.def.mpr hα0)
      have hkle : k ≤ m := by
        have hdvd : (X - C α) ^ k ∣ Pz P 0 := Polynomial.pow_rootMultiplicity_dvd (Pz P 0) α
        have hge := Monic.natDegree_le_of_dvd ((monic_X_sub_C α).pow k) hp0 hdvd
        have hnd : ((X - C α) ^ k).natDegree = k := by
          rw [(monic_X_sub_C α).natDegree_pow, natDegree_X_sub_C, mul_one]
        rwa [hnd, hnat] at hge
      rcases lt_or_eq_of_le hkle with hklt | hkeq
      · -- cluster splitting: `0 < k < m`
        obtain ⟨G, hGmon, hGdeg, hGhol, hGred, H, hHmon, hGH⟩ :=
          h5 P hmon hdeg hhol α k hkrs hkpos
        have hHnat : H.natDegree = m - k := by
          have h := hGmon.natDegree_mul hHmon
          rw [← hGH, hdeg, hGdeg] at h
          omega
        have hHhol : HolCoeffs H 0 := descent_holCoeffs_div hGmon hGH hGhol hhol
        obtain ⟨N₁, η₁, hN₁, hη₁, hfac₁⟩ := ih k hklt G hGmon hGdeg hGhol
        obtain ⟨N₂, η₂, hN₂, hη₂, hfac₂⟩ := ih (m - k) (by omega) H hHmon hHnat hHhol
        obtain ⟨ρ₁, hρ₁, hfac₁'⟩ := ball_of_factoredGerm hfac₁
        obtain ⟨ρ₂, hρ₂, hfac₂'⟩ := ball_of_factoredGerm hfac₂
        obtain ⟨ρ, hρ, hfac⟩ := branches_mul hN₁ hN₂ η₁ η₂ hρ₁ hρ₂ hfac₁' hfac₂'
        have hkm : k + (m - k) = m := by omega
        refine ⟨N₁ * N₂, (fun j : Fin m => combineFamily N₁ N₂ η₁ η₂ ((finCongr hkm).symm j)),
          mul_pos hN₁ hN₂, (fun j => combineFamily_analytic hN₁ hN₂ hη₁ hη₂ _), ?_⟩
        refine factoredGerm_of_ball hρ (fun u hu => ?_)
        rw [hGH, hfac u hu]
        exact (Fintype.prod_equiv ((finCongr hkm).symm)
          (fun j : Fin m => (X - C (combineFamily N₁ N₂ η₁ η₂ ((finCongr hkm).symm j) u)))
          (fun j : Fin (k + (m - k)) => (X - C (combineFamily N₁ N₂ η₁ η₂ j u)))
          (fun _ => rfl)).symm
      · -- pure power: `k = m`
        have hpure : Pz P 0 = (X - C α) ^ m := by
          have h := root_mult.1 (monic_Pz hmon 0) (by rw [hkrs, hkeq]; exact hnat.symm)
          rwa [hnat] at h
        obtain ⟨d, R, hd, hRP, hRmon, hRdeg, hRhol, hRred, hRsub⟩ :=
          tschirnhausen_reduce hm2 P hmon hdeg hhol α hpure
        by_cases hex : ∃ i < m, analyticOrderAt (R.coeff i) 0 ≠ ⊤
        · -- Newton rescaling
          obtain ⟨q, a, R', ρN, hq, ha, hρN, hR'mon, hR'deg, hR'hol, hR'c0, hR'ci, hid⟩ :=
            newton_step hm2 hRmon hRdeg hRhol hRred hRsub hex
          obtain ⟨i₀, hi₀m, hi₀⟩ := hR'ci
          obtain ⟨β, hβpos, hβlt⟩ :=
            root_mult.2 (monic_Pz hR'mon 0) ((natDegree_Pz hR'mon 0).trans hR'deg) hR'c0
              ⟨i₀, hi₀m, hi₀⟩
          obtain ⟨G, hGmon, hGdeg, hGhol, hGred, H, hHmon, hGH⟩ :=
            h5 R' hR'mon hR'deg hR'hol β ((Pz R' 0).rootMultiplicity β) rfl hβpos
          have hHnat : H.natDegree = m - (Pz R' 0).rootMultiplicity β := by
            have h := hGmon.natDegree_mul hHmon
            rw [← hGH, hR'deg, hGdeg] at h
            omega
          have hHhol : HolCoeffs H 0 := descent_holCoeffs_div hGmon hGH hGhol hR'hol
          obtain ⟨N₁, η₁, hN₁, hη₁, hfac₁⟩ :=
            ih (G.natDegree) (by rw [hGdeg]; exact hβlt) G hGmon rfl hGhol
          obtain ⟨N₂, η₂, hN₂, hη₂, hfac₂⟩ :=
            ih (H.natDegree) (by rw [hHnat]; omega) H hHmon rfl hHhol
          obtain ⟨ρ₁, hρ₁, hfac₁'⟩ := ball_of_factoredGerm hfac₁
          obtain ⟨ρ₂, hρ₂, hfac₂'⟩ := ball_of_factoredGerm hfac₂
          obtain ⟨ρ₂', hρ₂', hfac'⟩ := branches_mul hN₁ hN₂ η₁ η₂ hρ₁ hρ₂ hfac₁' hfac₂'
          have hN' : 0 < N₁ * N₂ := mul_pos hN₁ hN₂
          have hkm' : G.natDegree + H.natDegree = m := by omega
          have hηc : ∀ j : Fin m, AnalyticAt ℂ
              (fun u => combineFamily N₁ N₂ η₁ η₂ ((finCongr hkm').symm j) u) 0 :=
            fun j => combineFamily_analytic hN₁ hN₂ hη₁ hη₂ _
          have hfacR' : ∀ t ∈ Metric.ball (0 : ℂ) (min ρN ρ₂'),
              Pz R' (t ^ (N₁ * N₂)) =
                ∏ j : Fin m, (X - C (combineFamily N₁ N₂ η₁ η₂ ((finCongr hkm').symm j) t)) := by
            intro t ht
            rw [hGH, hfac' t (Metric.ball_subset_ball (min_le_right _ _) ht)]
            exact (Fintype.prod_equiv ((finCongr hkm').symm)
              (fun j : Fin m => (X - C (combineFamily N₁ N₂ η₁ η₂ ((finCongr hkm').symm j) t)))
              (fun j : Fin (G.natDegree + H.natDegree) =>
                (X - C (combineFamily N₁ N₂ η₁ η₂ j t)))
              (fun _ => rfl)).symm
          obtain ⟨ρ₃, hρ₃, hfac₃⟩ :=
            branches_newton hq ha hRred hN'
              (fun j : Fin m => combineFamily N₁ N₂ η₁ η₂ ((finCongr hkm').symm j))
              (lt_min hρN hρ₂')
              (fun t ht => hid t (Metric.ball_subset_ball (min_le_left _ _) ht))
              hfacR'
          have hfac₄ : ∀ u ∈ Metric.ball (0 : ℂ) ρ₃,
              Pz (P.comp (X + C d)) (u ^ (q * (N₁ * N₂))) =
                ∏ j : Fin m, (X - C (u ^ (a * (N₁ * N₂))
                  * combineFamily N₁ N₂ η₁ η₂ ((finCongr hkm').symm j) u)) := by
            intro u hu
            rw [← hRP]
            exact hfac₃ u hu
          have hfac₅ := branches_shift P d
            (fun j u => u ^ (a * (N₁ * N₂))
              * combineFamily N₁ N₂ η₁ η₂ ((finCongr hkm').symm j) u) hρ₃ hfac₄
          exact ⟨q * (N₁ * N₂),
            (fun j u => u ^ (a * (N₁ * N₂))
              * combineFamily N₁ N₂ η₁ η₂ ((finCongr hkm').symm j) u
              + d (u ^ (q * (N₁ * N₂)))),
            mul_pos hq hN', fun j =>
              ((analyticAt_id.pow _).mul (hηc j)).add
                (analyticAt_comp_pow hd (mul_pos hq hN')),
            factoredGerm_of_ball hρ₃ hfac₅⟩
        · -- all lower coefficients vanish: the shifted polynomial is `X ^ m` near `0`
          push_neg at hex
          obtain ⟨ρ, hρ, hρ'⟩ := Pz_eq_X_pow_on_ball hRmon hRdeg (fun i => hex i i.isLt)
          have hfac₀ : ∀ u ∈ Metric.ball (0 : ℂ) ρ,
              Pz (P.comp (X + C d)) (u ^ 1) =
                ∏ j : Fin m, (X - C ((fun _ : Fin m => fun _ : ℂ => (0 : ℂ)) j u)) := by
            intro u hu
            rw [pow_one, ← hRP, hρ' u hu]
            simp [prod_fin_const]
          have hfac₁ := branches_shift P d
            (fun _ : Fin m => fun _ : ℂ => (0 : ℂ)) hρ hfac₀
          refine ⟨1, (fun j u => (fun _ : Fin m => fun _ : ℂ => (0 : ℂ)) j u + d (u ^ 1)),
            one_pos, fun j => ?_, factoredGerm_of_ball hρ hfac₁⟩
          exact analyticAt_const.add (analyticAt_comp_pow hd one_pos)

/-- The general complex Puiseux statement, assembled from the three interface Props.

This is a strong induction on `m = P.natDegree`. Call a fibre "good" at `z` when all its roots
are simple. The dichotomy that drives the induction is:

* **some punctured disk is good**: the discriminant `discr (Pz P ·)` is an analytic function
  near `0` (it is a polynomial in the coefficient functions), so if good fibres occur
  arbitrarily close to `0` then the discriminant does not vanish identically near `0`, and
  `h4 : SqfreeBranches` applies directly with `N = m.factorial`;

* **no punctured disk is good**: then the discriminant is identically zero near `0`, so every
  fibre near `0` has a multiple root. Look at the reduction `Pz P 0`:
  - if it has a simple root `α`, then `h2 : SimpleRootLift` splits off one linear factor
    `Y - ζ (z)` with `ζ` holomorphic and `ζ 0 = α`, leaving a monic `P / (Y - ζ)` of degree
    `m - 1`, to which the induction hypothesis applies (its coefficients are holomorphic: the
    division recurrence from the top uses only the leading coefficient `1`);
  - otherwise all roots of the reduction are multiple. Apply `h5 : ClusterSplitting` at a root
    `α` of multiplicity `k`; if `k < m` then `P = G * H` with `G` monic of degree `k` and `H`
    monic of degree `m - k`, both of lower degree and with holomorphic coefficients (`H`'s
    coefficients come from the division recurrence), and the induction hypothesis applies to
    both; if `k = m` then `Pz P 0 = (Y - α) ^ m` and the Newton slope step is applied: shift
    `Y = α + Z`, use Tschirnhausen to kill the coefficient of `Z ^ (m-1)`, take the least
    slope `c = v (b i) / (m - i)` over the non-zero lower coefficients `b i`, at `i₀`, set
    `q = m - i₀`, `a = v (b i₀)`, and substitute `z = t ^ q`, `Z = t ^ a * W`; by minimality
    of the slope the resulting `Q (t, W)` is monic with holomorphic coefficients and satisfies
    `P (t ^ q, α + t ^ a * W) = t ^ (a * m) * Q (t, W)`; its reduction is not a pure power, so
    it has a root of multiplicity `k` with `0 < k < m`, `h5` splits `Q`, and the induction
    hypothesis applies to the two factors. (If the shifted polynomial has no non-zero lower
    coefficient at all, then `P = (Y - α) ^ m` already and `N = 1` works.)

Ramifications multiply along the recursion (substitute `u ↦ u ^ (N' )` to lift a factor's
expansion to a common variable). -/
theorem complex_puiseux (h2 : Work.WilC4aP.SimpleRootLift) (h4 : Work.WilC4aP.SqfreeBranches)
    (h5 : Work.WilC4aP.ClusterSplitting) : Work.WilC4aP.ComplexPuiseux := by
  intro m P hmon hdeg hhol
  obtain ⟨N, η, hN, hη, hfac⟩ := puiseux_germ h5 P hmon hdeg hhol
  obtain ⟨r₁, hr₁, hηb⟩ : ∃ r > 0, ∀ j, AnalyticOnNhd ℂ (η j) (Metric.ball 0 r) := by
    have h : ∀ j : Fin m, ∃ r : ℝ, 0 < r ∧ AnalyticOnNhd ℂ (η j) (Metric.ball 0 r) :=
      fun j => (hη j).exists_ball_analyticOnNhd
    choose r hr hr' using h
    by_cases hne : (Finset.univ : Finset (Fin m)).Nonempty
    · refine ⟨Finset.univ.inf' hne r, ?_, ?_⟩
      · show (0 : ℝ) < Finset.univ.inf' hne r
        rw [Finset.lt_inf'_iff]
        exact fun j _ => hr j
      · intro j
        exact (hr' j).mono (Metric.ball_subset_ball (Finset.inf'_le _ (Finset.mem_univ j)))
    · exact ⟨1, one_pos, fun j => absurd ⟨j, Finset.mem_univ j⟩ hne⟩
  obtain ⟨ρ, hρ, hfacb⟩ := ball_of_factoredGerm hfac
  refine ⟨N, η, min r₁ ρ, hN, lt_min hr₁ hρ, ?_, ?_⟩
  · intro j
    exact (hηb j).mono (Metric.ball_subset_ball (min_le_left _ _))
  · intro u hu
    exact hfacb u (Metric.ball_subset_ball (min_le_right _ _) hu)

end Work.WilC4aP
