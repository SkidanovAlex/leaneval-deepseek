/-
# `Submission.Work.FIArea6Hecke.R.noCompletionOfPsiTrivial`

If `Λ` is an entire completion of the Hecke `L`-function of the Größencharacter
`ψ_m(z) = χ(z)·(z/|z|)^m` (with `χ` a strict character modulo `4d`) in the sense of
`IsCompleted`, then `ψ_m` cannot be trivial on the primary units modulo `4d`.

The reason is the pole of the Hecke `L`-function at `s = 1`: triviality on the primary units
forces `ψ_m` to agree with the principal strict character on *every* primary element (the strictness
of `χ` kills the primary non-units), hence
`L(s,ψ_m) = L(s, principalStrict d) = ζ(s)·L(s,χ₄)·G_d(s)` for `1 < re s`
(`heckeLSeries_principalStrict_eq`).  Since `Λ/heckeArch` is entire and agrees with `heckeLSeries`
on `re s > 1` (identity theorem, `Lam_eq_heckeArch_mul_of_one_lt_re`), multiplying by `σ - 1` and
letting `σ → 1⁺` along the real axis gives `0 = L(1,χ₄)·G_d(1)`, which is nonzero.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivCore
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
import Submission.Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators Topology

/-- **Auxiliary.**  If two Größencharacters agree on every primary element, their Hecke eigenvalue
sums agree. -/
lemma ncp_heckeLam_congr_of_psi_primary {chi chi' : GaussianInt → ℂ} {k k' : ℤ}
    (h : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.psi chi k z = Work.FIArea5.S16Hecke.psi chi' k' z) (n : ℕ) :
    Work.FIArea5.S16Hecke.heckeLam chi k n = Work.FIArea5.S16Hecke.heckeLam chi' k' n := by
  classical
  unfold Work.FIArea5.S16Hecke.heckeLam
  exact Finset.sum_congr rfl fun z hz => h z (Finset.mem_filter.mp hz).2.1

/-- **Auxiliary.**  If two Größencharacters agree on every primary element, their Hecke
`L`-series coincide. -/
lemma ncp_heckeLSeries_eq_of_psi_primary {chi chi' : GaussianInt → ℂ} {k k' : ℤ}
    (h : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.psi chi k z = Work.FIArea5.S16Hecke.psi chi' k' z) :
    Work.FIArea5.S16Hecke.heckeLSeries chi k =
      Work.FIArea5.S16Hecke.heckeLSeries chi' k' := by
  funext s
  simp only [Work.FIArea5.S16Hecke.heckeLSeries]
  exact LSeries_congr (fun {n} _ => ncp_heckeLam_congr_of_psi_primary h n) s

/-- **Auxiliary.**  The finite Euler-factor correction
`G_d(s) = ∏_{p ∣ 4d}(1-p^{-s})(1-χ₄(p)p^{-s})` does not vanish for `0 < re s` (in particular at
`s = 1`).  This is `axisBadPoly_ne_zero` with the hypothesis `1 < re s` relaxed to `0 < re s`; the
same norm argument works because only `p^{-re s} < 1` is used. -/
lemma ncp_axisBadPoly_ne_zero_of_pos_re (d : ℕ) {s : ℂ} (hs : 0 < s.re) :
    axisBadPoly d s ≠ 0 := by
  rw [axisBadPoly_eq_prod_corr]
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  rw [axisBadCorr, if_pos hp]
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp1 : 1 < p := hpp.one_lt
  refine mul_ne_zero ?_ ?_
  · refine sub_ne_zero.mpr fun h => ?_
    have h1 : ‖(p : ℂ) ^ (-s)‖ = 1 := by rw [← h]; simp
    rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re] at h1
    have h2 : (p : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp1) (by linarith)
    linarith
  · intro h
    have h1 : axisChi4 p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
    have hnorm : ‖axisChi4 p * (p : ℂ) ^ (-s)‖ = 1 := by rw [h1]; simp
    have hle : ‖axisChi4 p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-s.re) := by
      rw [norm_mul]
      calc ‖axisChi4 p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
            mul_le_mul_of_nonneg_right (axisChi4_norm_le_one p) (norm_nonneg _)
        _ = ‖(p : ℂ) ^ (-s)‖ := one_mul _
        _ = (p : ℝ) ^ (-s.re) := by
            rw [Complex.norm_natCast_cpow_of_pos hpp.pos, Complex.neg_re]
    have hlt : (p : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp1) (by linarith)
    linarith

/-- **Auxiliary.**  The residue of the Riemann zeta function at `s = 1`, along the real axis from
the right: `(σ - 1)·ζ(σ) → 1` as `σ → 1⁺`. -/
lemma ncp_tendsto_zetaResidue_Ioi :
    Filter.Tendsto (fun σ : ℝ => (((σ : ℂ) - 1) * riemannZeta (σ : ℂ)))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (1 : ℂ)) := by
  have hσC : Filter.Tendsto (fun σ : ℝ => (σ : ℂ)) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds (1 : ℂ)) := by
    have hcont : ContinuousAt Complex.ofReal (1 : ℝ) := Complex.continuous_ofReal.continuousAt
    have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Set.Ioi 1))
    simpa using h
  have hne : Filter.Tendsto (fun σ : ℝ => (σ : ℂ)) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhdsWithin (1 : ℂ) ({1}ᶜ : Set ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hσC, ?_⟩
    refine Filter.eventually_of_mem self_mem_nhdsWithin fun σ hσ => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h' : (σ : ℂ) = ((1 : ℝ) : ℂ) := by simpa using h
    exact absurd (Complex.ofReal_inj.mp h') (ne_of_gt hσ)
  exact riemannZeta_residue_one.comp hne

/-- If an entire function completes the Hecke `L`-function of `ψ_m = χ(·)(·/|·|)^m` and `ψ_m` is
trivial on the primary units modulo `4d`, then `χ` must be a strict character and we reach a
contradiction: such a completion cannot exist.

The proof: triviality forces `ψ_m` to agree with the principal strict character `principalStrict d`
on primary elements, so `L(s,ψ_m) = L(s, principalStrict d) = ζ(s)L(s,χ₄)G_d(s)` on `re s > 1`.
Since `Λ/heckeArch` is entire and equals `L(s,ψ_m)` there (identity theorem,
`Lam_eq_heckeArch_mul_of_one_lt_re`), multiplying by
`σ - 1` and letting `σ → 1⁺` gives `0 = L(1,χ₄)G_d(1) ≠ 0`. -/
theorem noCompletionOfPsiTrivial (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℤ)
    (Lam : ℂ → ℂ) (hadm : Work.FIArea6Hecke.R.IsCompleted d chi m Lam)
    (htriv : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z → Work.FIArea5.S16Hecke.psi chi m z = 1) :
    False := by
  obtain ⟨-, hchi, hAn, hagr⟩ := hadm
  have hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  -- ### Step 1: `ψ_m` agrees with the principal strict character on primary elements.
  have hpsi : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.psi chi m z =
        Work.FIArea5.S16Hecke.psi (Work.FIArea6Hecke.principalStrict d) 0 z := by
    intro z hz
    rw [psi_principalStrict_zero]
    by_cases hu : Work.FIArea5.S16Hecke.IsUnitMod4d d z
    · rw [htriv z hz hu, Work.FIArea6Hecke.principalStrict_of_unit hu]
    · rw [Work.FIArea5.S16Hecke.psi, hchi.2 z hu, zero_mul,
        Work.FIArea6Hecke.principalStrict_of_not_unit hu]
  have hLS : Work.FIArea5.S16Hecke.heckeLSeries chi m =
      Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 :=
    ncp_heckeLSeries_eq_of_psi_primary hpsi
  -- ### Step 2: the classical factorisation on `re s > 1`, with the honest factor `L(·,χ₄)`.
  have hfact : ∀ σ : ℝ, 1 < σ → Work.FIArea5.S16Hecke.heckeLSeries chi m (σ : ℂ) =
      riemannZeta (σ : ℂ) * chi4C.LFunction (σ : ℂ) * axisBadPoly d (σ : ℂ) := by
    intro σ hσ
    have hs : (1 : ℝ) < (σ : ℂ).re := by simpa using hσ
    calc Work.FIArea5.S16Hecke.heckeLSeries chi m (σ : ℂ)
        = Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 (σ : ℂ) :=
          congrFun hLS (σ : ℂ)
      _ = riemannZeta (σ : ℂ) * LSeries axisChi4 (σ : ℂ) * axisBadPoly d (σ : ℂ) :=
          heckeLSeries_principalStrict_eq d hd hs
      _ = riemannZeta (σ : ℂ) * chi4C.LFunction (σ : ℂ) * axisBadPoly d (σ : ℂ) := by
          rw [LSeries_axisChi4_eq_LFunction hs]
  -- ### Step 3: the identity theorem turns the completion hypothesis into a statement on all of
  -- `re s > 1`, and the two sides agree eventually along `σ → 1⁺`.
  have hev : (fun σ : ℝ => ((σ : ℂ) - 1) *
        (Lam (σ : ℂ) / Work.FITop4.Bridge.heckeArch d m (σ : ℂ)))
      =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)]
      (fun σ : ℝ => ((σ : ℂ) - 1) * riemannZeta (σ : ℂ) * chi4C.LFunction (σ : ℂ) *
        axisBadPoly d (σ : ℂ)) := by
    refine Filter.eventually_of_mem self_mem_nhdsWithin fun σ hσ => ?_
    change ((σ : ℂ) - 1) * (Lam (σ : ℂ) / Work.FITop4.Bridge.heckeArch d m (σ : ℂ))
      = ((σ : ℂ) - 1) * riemannZeta (σ : ℂ) * chi4C.LFunction (σ : ℂ) * axisBadPoly d (σ : ℂ)
    have hσ1 : (1 : ℝ) < σ := hσ
    have hs : (1 : ℝ) < (σ : ℂ).re := by simpa using hσ1
    have hpos : (0 : ℝ) < σ := by linarith
    have hne : Work.FITop4.Bridge.heckeArch d m (σ : ℂ) ≠ 0 :=
      heckeArch_ne_zero_of_pos_re d hd m (by simpa using hpos)
    have hid : Lam (σ : ℂ) = Work.FITop4.Bridge.heckeArch d m (σ : ℂ) *
        Work.FIArea5.S16Hecke.heckeLSeries chi m (σ : ℂ) :=
      Lam_eq_heckeArch_mul_of_one_lt_re (chi := chi) (m := m) (Lam := Lam) hd hAn hb hagr hs
    have h1 : Lam (σ : ℂ) / Work.FITop4.Bridge.heckeArch d m (σ : ℂ) =
        Work.FIArea5.S16Hecke.heckeLSeries chi m (σ : ℂ) := by
      rw [hid, mul_div_cancel_left₀ _ hne]
    rw [h1, hfact σ hσ1]
    ring
  -- ### Step 4: the two limits along `σ → 1⁺`.
  have hσC : Filter.Tendsto (fun σ : ℝ => (σ : ℂ)) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds (1 : ℂ)) := by
    have hcont : ContinuousAt Complex.ofReal (1 : ℝ) := Complex.continuous_ofReal.continuousAt
    have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Set.Ioi 1))
    simpa using h
  have hsub : Filter.Tendsto (fun σ : ℝ => (σ : ℂ) - 1) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds 0) := by
    have hconst : Filter.Tendsto (fun _ : ℝ => (1 : ℂ)) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
        (nhds 1) := tendsto_const_nhds
    have h := hσC.sub hconst
    simpa using h
  have hquot : Filter.Tendsto
      (fun σ : ℝ => Lam (σ : ℂ) / Work.FITop4.Bridge.heckeArch d m (σ : ℂ))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds (Lam 1 / Work.FITop4.Bridge.heckeArch d m 1)) := by
    have h1 : Filter.Tendsto (fun σ : ℝ => Lam (σ : ℂ)) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
        (nhds (Lam 1)) :=
      ((hAn.analyticAt Filter.univ_mem).continuousAt.tendsto).comp hσC
    have h2 : Filter.Tendsto (fun σ : ℝ => Work.FITop4.Bridge.heckeArch d m (σ : ℂ))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (Work.FITop4.Bridge.heckeArch d m 1)) :=
      ((heckeArch_differentiableAt_of_pos hd m (by norm_num)).continuousAt.tendsto).comp hσC
    exact h1.div h2 (heckeArch_ne_zero_of_pos_re d hd m (by norm_num))
  have hleft : Filter.Tendsto
      (fun σ : ℝ => ((σ : ℂ) - 1) * (Lam (σ : ℂ) / Work.FITop4.Bridge.heckeArch d m (σ : ℂ)))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds 0) := by
    have h := hsub.mul hquot
    simpa using h
  have hright : Filter.Tendsto
      (fun σ : ℝ => ((σ : ℂ) - 1) * riemannZeta (σ : ℂ) * chi4C.LFunction (σ : ℂ) *
        axisBadPoly d (σ : ℂ))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds (1 * chi4C.LFunction 1 * axisBadPoly d 1)) := by
    have hres : Filter.Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * riemannZeta (σ : ℂ))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds 1) := ncp_tendsto_zetaResidue_Ioi
    have hLχ : Filter.Tendsto (fun σ : ℝ => chi4C.LFunction (σ : ℂ))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (chi4C.LFunction 1)) :=
      (((DirichletCharacter.differentiable_LFunction chi4C_ne_one).continuous).continuousAt.tendsto).comp
        hσC
    have hGa : Filter.Tendsto (fun σ : ℝ => axisBadPoly d (σ : ℂ))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (axisBadPoly d 1)) :=
      ((differentiableAt_axisBadPoly d 1).continuousAt.tendsto).comp hσC
    exact (hres.mul hLχ).mul hGa
  -- ### Step 5: uniqueness of the limit yields `L(1,χ₄)·G_d(1) = 0`, a contradiction.
  have hleft' : Filter.Tendsto
      (fun σ : ℝ => ((σ : ℂ) - 1) * riemannZeta (σ : ℂ) * chi4C.LFunction (σ : ℂ) *
        axisBadPoly d (σ : ℂ))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds 0) :=
    Filter.Tendsto.congr' hev hleft
  haveI : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := nhdsWithin_Ioi_neBot (le_refl (1 : ℝ))
  have huniq : (1 : ℂ) * chi4C.LFunction 1 * axisBadPoly d 1 = 0 :=
    tendsto_nhds_unique hright hleft'
  have hG1 : axisBadPoly d 1 ≠ 0 :=
    ncp_axisBadPoly_ne_zero_of_pos_re d (s := (1 : ℂ)) (by norm_num)
  exact (mul_ne_zero (DirichletCharacter.LFunction_apply_one_ne_zero chi4C_ne_one) hG1)
    (by simpa using huniq)

end Work.FIArea6Hecke.R
