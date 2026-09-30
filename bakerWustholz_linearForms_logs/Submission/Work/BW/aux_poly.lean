import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.ph_ge_nineteen
import Submission.Work.BW.siegel_fintype_ball
import Submission.Work.BW.aux_poly_arith_final
import Submission.Work.BW.discr_term_le_tiny
import Submission.Work.BW.logHeight_intermediate
import Submission.Work.BW.logHeight_one_intermediate
import Submission.Work.BW.ulcm_le_four_pow
import Submission.Work.BW.tijdeman_int
import Submission.Work.BW.norm_Theta_le
import Submission.Work.BW.norm_Delta_le
import Submission.Work.BW.logHeight_intTuple_le
import Submission.Work.BW.logHeight_monomial_le
import Submission.Work.BW.card_multIdx
import Submission.Work.BW.card_auxIdx
import Submission.Work.BW.card_eqnS
import Submission.Work.BW.sum_abs_Icc
import Submission.Work.BW.sum_eqnIdx_abs
import Submission.Work.BW.Mu_ge_Me
import Submission.Work.BW.sysRow_height_bound
import Submission.Work.BW.rowsum_le
import Submission.Work.BW.Qval_eq_sum
import Submission.Work.BW.aux_poly_arith_ball

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive). Route design: BW = Baker–Wüstholz, Crelle 442 (1993); section and lemma numbers are BW's. Shared definitions are in Submission.Work.BW.Defs (namespace Work.BW).
Sibling nodes are dispatched in parallel, each as module Submission.Work.BW.<name> with its statement already in place: liouville_logForm, lehmer_bound, minkowski_basis, kummer_indep, logHeight_intermediate, discriminant_bound, siegel_numberField, small_relation, kummer_reduction, aux_poly, analytic_core, bw_independent, logindep_reduction. multiplicity_prop and group_reduction come later.
If your proof needs a sibling's result, IMPORT its module and use its statement. Do NOT reprove it, and do not restate it under another name. Its sorry disappears when it lands.
The constants are tight (see the notes below): do not weaken any numeric constant in your statement. If you believe the statement is false, give a concrete counterexample.

# aux_poly — BW §12–13 (p. 37–41); 3–6k lines, medium-high risk (numerics)

**Claim.** Under `Standing` and `BH` at `r ≥ 2` with a valid `ι`, there is a nonzero
`p : AuxIdx → K` satisfying (9) and `h(p) ≤ 0.85SD` (12).

## Proof (as formalised)

`D, D₀, Dⱼ, h, S, T` are the §13 parameters.  `F = ℚ(α') ≤ K`, `d = [K:ℚ]`, `d_F = [F:ℚ]`.

1. `h ≥ 19` (`ph_ge_nineteen`) and `σⱼ ≥ 1/d` (`hmod ≥ 1/d`).
2. Siegel's box principle (`siegel_fintype`, from BW L1) over `F` for the linear system whose
   equation `(s,t)` is the row `sysRow` (the coefficients of `Q(s,α'^s;t) = 0` written in `F`);
   the number of equations is `Me = (2S+1)binom(T+r,r)`, the number of unknowns is
   `Mu = h(D₀+1)∏(Dⱼ+1) ≥ 3.3·Me` (`Mu_ge_Me`), so a nontrivial integral solution `x` exists.
3. `Qval_eq_sum` identifies `Qval` with `∑ lm, φ(p lm)·φ(coef lm)`, so the `φ`-image of the
   system gives the vanishing (9) for `p = x` viewed in `K`.
4. Heights: `h_K(p) = [K:F]·h_F(x)` (`logHeight_intermediate`), the Siegel bound splits into the
   discriminant term (`discr_term_le`), the row-sum term (`rowsum_le`, using the row height bound
   `sysRow_height_bound`: `Tijdeman` integrality, `norm_Theta_le`, `norm_Delta_le`,
   `ulcm_le_four_pow`, `logHeight_intTuple_le`, `logHeight_monomial_le`), and the final
   arithmetic (`aux_poly_arith`).
-/

namespace Work.BW

set_option maxHeartbeats 2000000

open Complex Height

open scoped NumberField

/-- BW §12–13: under the standing assumptions and the basic hypothesis at `r ≥ 2`, Siegel's
box principle over `ℚ(α')` gives coefficients `p(λ) ∈ K`, not all zero, with `Q(s, α'^s; t) = 0` for
`|s| ≤ S`, `t₀+⋯+t_{r-1} ≤ T` (BW (9)) and `h(p) ≤ 0.85 S D` (BW (12)). -/
theorem aux_poly {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (c : ℝ) (hst : Standing φ α b k c)
    (hr : 2 ≤ r) (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K) (σ : Fin r → ℝ)
    (hBH : BH φ α b v c r L α' σ) (ι : Fin (r - 1) → Fin n) (hι : IotaOK b k L ι) :
    ∃ p : AuxIdx r (ph (hL b (Module.finrank ℚ K)) v) (pD0 r (Module.finrank ℚ K) σ)
        (pDj r (Module.finrank ℚ K) σ) → K,
      p ≠ 0 ∧
      (∀ (s : ℤ), |s| ≤ (pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v) : ℤ) →
        ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
          t0 + ∑ m, t m ≤ pT r (Module.finrank ℚ K) σ →
          Qval φ b k L ι α' (ph (hL b (Module.finrank ℚ K)) v) (pD0 r (Module.finrank ℚ K) σ)
            (pDj r (Module.finrank ℚ K) σ) p t0 t s = 0) ∧
      Height.logHeight p ≤
        0.85 * (pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v) : ℝ) *
          pD r (Module.finrank ℚ K) σ := by
  classical
  obtain ⟨hn2, hα0, hlindep, hgcd, hbk, hmodmax, hXbwle, hce, hclog⟩ := hst
  obtain ⟨hLind, hbspan, hα'ne, hKum, hσpos, hmodα', hLsum, hκprod⟩ := hBH
  have hst' : Standing φ α b k c :=
    ⟨hn2, hα0, hlindep, hgcd, hbk, hmodmax, hXbwle, hce, hclog⟩
  have hBH' : BH φ α b v c r L α' σ :=
    ⟨hLind, hbspan, hα'ne, hKum, hσpos, hmodα', hLsum, hκprod⟩
  set d : ℕ := Module.finrank ℚ K with hd
  set hh : ℕ := ph (hL b d) v with hhh
  set DD : ℝ := pD r d σ with hDD
  set SS : ℕ := pS r d hh with hSS
  set TT : ℕ := pT r d σ with hTT
  set D0 : ℕ := pD0 r d σ with hD0
  set Dj : Fin r → ℕ := pDj r d σ with hDj
  -- `hh ≥ 19`
  have hh19 : 19 ≤ hh := by
    rw [hhh, hd]
    exact ph_ge_nineteen φ α b k c v ⟨hn2, hα0, hlindep, hgcd, hbk, hmodmax, hXbwle, hce, hclog⟩
  -- `σⱼ ≥ 1/d`
  have hσ1 : ∀ j, 1 / (d : ℝ) ≤ σ j := by
    intro j
    have h := hmodα' j
    rw [hmod] at h
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h
  set F : IntermediateField ℚ K := auxField α' with hF
  haveI : FiniteDimensional ℚ ↥F := inferInstance
  haveI : NumberField ↥F := inferInstance
  -- cardinalities
  have hMu : Fintype.card (AuxIdx r hh D0 Dj) = hh * (D0 + 1) * ∏ j, (Dj j + 1) :=
    card_auxIdx r hh D0 Dj
  obtain ⟨hMe3, hMe_lt⟩ := Mu_ge_Me (K := K) r hh hr hh19 σ hσ1
  have hcard : Fintype.card (AuxEqnIdx r SS TT) < Fintype.card (AuxIdx r hh D0 Dj) := by
    rw [hMu]
    exact hMe_lt
  -- Siegel's box principle over `F = ℚ(α')`
  obtain ⟨x, hxne, hxeq, hxle⟩ := siegel_fintype_ball (F := ↥F) hcard
    (fun (e : AuxEqnIdx r SS TT) (lm : AuxIdx r hh D0 Dj) =>
      (sysRow b k L ι α' hh D0 Dj e lm : ↥F))
  refine ⟨fun lm => ((x lm : ↥F) : K), ?_, ?_, ?_⟩
  · -- the solution is nontrivial
    intro hp
    apply hxne
    funext lm
    have h := congrFun hp lm
    have h1 : (((x lm : 𝓞 ↥F) : ↥F)) = 0 := Subtype.coe_injective h
    exact Subtype.coe_injective h1
  · -- the vanishing of `Q(s, α'^s; t)`
    intro s hs t0 t ht
    have hs' : s ∈ Finset.Icc (-(SS : ℤ)) (SS : ℤ) := by
      rw [Finset.mem_Icc]
      exact abs_le.mp hs
    let e : AuxEqnIdx r SS TT := ⟨⟨s, hs'⟩, ⟨(t0, t), ht⟩⟩
    have he := hxeq e
    have h2 : (∑ lm : AuxIdx r hh D0 Dj,
        φ (((sysRow b k L ι α' hh D0 Dj e lm : ↥F) : K)) *
          φ (((x lm : ↥F) : K))) = 0 := by
      have h3 : (φ.comp (algebraMap ↥F K))
          (∑ lm : AuxIdx r hh D0 Dj,
            (sysRow b k L ι α' hh D0 Dj e lm : ↥F) * ((x lm : ↥F))) = 0 := by
        rw [he, map_zero]
      have hexp : (∑ lm : AuxIdx r hh D0 Dj,
            (φ.comp (algebraMap ↥F K))
              ((sysRow b k L ι α' hh D0 Dj e lm : ↥F) * ((x lm : ↥F)))) =
          ∑ lm, φ (algebraMap ↥F K (sysRow b k L ι α' hh D0 Dj e lm : ↥F)) *
              φ (algebraMap ↥F K ((x lm : ↥F))) := by
        refine Finset.sum_congr rfl (fun lm _ => ?_)
        simp only [RingHom.comp_apply, map_mul]
      rw [map_sum] at h3
      rw [hexp] at h3
      first
        | exact h3
        | simpa only [Subfield.algebraMap_ofSubfield] using h3
        | simpa using h3
    have hq : Qval φ b k L ι α' hh D0 Dj
        (fun lm : AuxIdx r hh D0 Dj => ((x lm : ↥F) : K)) t0 t s
        = ∑ lm : AuxIdx r hh D0 Dj,
            φ (((x lm : ↥F) : K)) *
              φ (((coefF b k L ι α' hh D0 Dj t0 t s lm : auxField α') : K)) :=
      Qval_eq_sum φ α b k L ι α' hh D0 Dj _ t0 t s
    rw [hq]
    have key : (∑ lm : AuxIdx r hh D0 Dj,
        φ (((x lm : ↥F) : K)) *
          φ (((coefF b k L ι α' hh D0 Dj t0 t s lm : auxField α') : K)))
        = ∑ lm : AuxIdx r hh D0 Dj,
            φ (((sysRow b k L ι α' hh D0 Dj e lm : ↥F) : K)) *
              φ (((x lm : ↥F) : K)) := by
      refine Finset.sum_congr rfl (fun lm _ => ?_)
      simp only [sysRow]
      exact mul_comm _ _
    rw [key]
    exact h2
  · -- the height bound
    have h1 : Height.logHeight (fun lm => ((x lm : ↥F) : K)) ≤
        (Module.finrank ↥F K : ℝ) *
            ((1 / 2) * Real.log |((NumberField.discr ↥F : ℤ) : ℝ)|) +
          (Module.finrank ↥F K : ℝ) *
            ((1 / ((Fintype.card (AuxIdx r hh D0 Dj) : ℝ) - Fintype.card (AuxEqnIdx r SS TT))) *
              ∑ e : AuxEqnIdx r SS TT,
                ((1 / 2) * (Module.finrank ℚ ↥F : ℝ) *
                    Real.log (Fintype.card (AuxIdx r hh D0 Dj)) +
                  Height.logHeight (fun lm => (sysRow b k L ι α' hh D0 Dj e lm : ↥F)))) +
          (Module.finrank ↥F K : ℝ) *
            ((Module.finrank ℚ ↥F : ℝ) * Real.log (4 * (Module.finrank ℚ ↥F : ℝ) *
              (Fintype.card (AuxIdx r hh D0 Dj) : ℝ))) := by
      rw [logHeight_intermediate F (fun lm => (x lm : ↥F))]
      calc (Module.finrank ↥F K : ℝ) * Height.logHeight (fun lm => (x lm : ↥F))
          ≤ (Module.finrank ↥F K : ℝ) *
              ((1 / 2) * Real.log |((NumberField.discr ↥F : ℤ) : ℝ)| +
                (1 / ((Fintype.card (AuxIdx r hh D0 Dj) : ℝ) -
                    Fintype.card (AuxEqnIdx r SS TT))) *
                  ∑ i : AuxEqnIdx r SS TT,
                    ((1 / 2) * (Module.finrank ℚ ↥F : ℝ) *
                        Real.log (Fintype.card (AuxIdx r hh D0 Dj)) +
                      Height.logHeight (fun lm => (sysRow b k L ι α' hh D0 Dj i lm : ↥F))) +
                (Module.finrank ℚ ↥F : ℝ) * Real.log (4 * (Module.finrank ℚ ↥F : ℝ) *
                  (Fintype.card (AuxIdx r hh D0 Dj) : ℝ))) :=
            mul_le_mul_of_nonneg_left hxle (by positivity)
        _ = _ := by ring
    have h2 := discr_term_le_tiny (K := K) φ α b k c hst' v L α' σ hBH' hr
    have h3 := rowsum_le (K := K) φ α b k c hst' hr v L α' σ hBH' ι
    have h4 := aux_poly_arith_final (K := K) hr hh hh19 σ hσ1
    -- the transported ball term: `[K:F]·d_F·log(4 d_F Mu) = d·log(4 d_F Mu) ≤ d·log(4 d Mu)`
    have hfd : (Module.finrank ↥F K : ℝ) * (Module.finrank ℚ ↥F : ℝ) = (d : ℝ) := by
      have h := Module.finrank_mul_finrank ℚ ↥F K
      have h2 : (d : ℕ) = Module.finrank ℚ ↥F * Module.finrank ↥F K := by
        rw [show (d : ℕ) = Module.finrank ℚ K from rfl, ← h]
      rw [h2]
      push_cast
      ring
    have heF1 : (1 : ℝ) ≤ (Module.finrank ↥F K : ℝ) := by
      have h : 1 ≤ Module.finrank ↥F K :=
        Nat.one_le_iff_ne_zero.mpr (Module.finrank_pos (R := ↥F) (M := K)).ne'
      exact_mod_cast h
    have hdFpos : (0 : ℝ) < (Module.finrank ℚ ↥F : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := ↥F)
    have hdFle : (Module.finrank ℚ ↥F : ℝ) ≤ (d : ℝ) := by
      calc (Module.finrank ℚ ↥F : ℝ) = (Module.finrank ℚ ↥F : ℝ) * 1 := by ring
        _ ≤ (Module.finrank ℚ ↥F : ℝ) * (Module.finrank ↥F K : ℝ) :=
            mul_le_mul_of_nonneg_left heF1 hdFpos.le
        _ = (d : ℝ) := by rw [mul_comm]; exact hfd
    have hMu1 : (1 : ℝ) ≤ (Fintype.card (AuxIdx r hh D0 Dj) : ℝ) := by
      have hh1 : 1 ≤ hh := le_trans (by norm_num) hh19
      have hne : Nonempty (AuxIdx r hh D0 Dj) :=
        ⟨⟨⟨0, hh1⟩, ⟨0, Nat.succ_pos _⟩, fun _ => ⟨0, Nat.succ_pos _⟩⟩⟩
      have h : 1 ≤ Fintype.card (AuxIdx r hh D0 Dj) := Fintype.card_pos_iff.mpr hne
      exact_mod_cast h
    have h5 : (Module.finrank ↥F K : ℝ) *
        ((Module.finrank ℚ ↥F : ℝ) * Real.log (4 * (Module.finrank ℚ ↥F : ℝ) *
          (Fintype.card (AuxIdx r hh D0 Dj) : ℝ)))
        ≤ (d : ℝ) * Real.log (4 * (d : ℝ) * (Fintype.card (AuxIdx r hh D0 Dj) : ℝ)) := by
      have harg : 4 * (Module.finrank ℚ ↥F : ℝ) * (Fintype.card (AuxIdx r hh D0 Dj) : ℝ) ≤
          4 * (d : ℝ) * (Fintype.card (AuxIdx r hh D0 Dj) : ℝ) := by nlinarith [hdFle, hMu1]
      have hlog := Real.log_le_log (by nlinarith [hdFpos, hMu1]) harg
      calc (Module.finrank ↥F K : ℝ) *
            ((Module.finrank ℚ ↥F : ℝ) * Real.log (4 * (Module.finrank ℚ ↥F : ℝ) *
              (Fintype.card (AuxIdx r hh D0 Dj) : ℝ)))
          = ((Module.finrank ↥F K : ℝ) * (Module.finrank ℚ ↥F : ℝ)) *
              Real.log (4 * (Module.finrank ℚ ↥F : ℝ) *
                (Fintype.card (AuxIdx r hh D0 Dj) : ℝ)) := by ring
        _ = (d : ℝ) * Real.log (4 * (Module.finrank ℚ ↥F : ℝ) *
              (Fintype.card (AuxIdx r hh D0 Dj) : ℝ)) := by rw [hfd]
        _ ≤ (d : ℝ) * Real.log (4 * (d : ℝ) * (Fintype.card (AuxIdx r hh D0 Dj) : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
    simp only [hd, hhh, hSS, hTT, hDD, hD0, hDj] at h1 h2 h3 h4 h5 hMu ⊢
    rw [hMu] at h1 h3 h5
    linarith [h1, h2, h3, h4, h5]

end Work.BW
