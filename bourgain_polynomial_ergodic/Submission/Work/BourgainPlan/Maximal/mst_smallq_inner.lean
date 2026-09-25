import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.Maximal.sigmaN_contains_farey
import Submission.Work.BourgainPlan.Maximal.sigmaN_farey_helpers
import Submission.Work.BourgainPlan.Maximal.memLp_scaled_bump

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

/-- **Real-arithmetic core of the small-denominator step.**  If `|cR · y| ≤ 1/(q · (Ginv · Bpos))`
with `cR > 0`, `q ≥ 1`, `G > 0`, `Ginv = G⁻¹`, `Bneg = Bpos⁻¹` and `Bpos > 0`, then
`|y| ≤ G · Bneg / cR`.  (Read `G = n^γ = Ginv⁻¹` and `Bneg = 2^{-nd} = Bpos⁻¹`: the hypothesis is
`hclose` after dividing by `c = P.leadingCoeff`, and the conclusion is the bound `n^γ 2^{-nd}/c`.) -/
private lemma abs_le_of_abs_mul_le (cR y G Ginv Bpos Bneg : ℝ) (q : ℕ)
    (hcR : 0 < cR) (hq1 : 1 ≤ q) (hG : 0 < G)
    (hGinv : Ginv = G⁻¹) (hB : Bneg = Bpos⁻¹) (hBpos : 0 < Bpos)
    (h : |cR * y| ≤ 1 / ((q : ℝ) * (Ginv * Bpos))) :
    |y| ≤ G * Bneg / cR := by
  have hqR1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  -- reciprocal of the denominator, using `Ginv = G⁻¹`
  have h1 : 1 / ((q : ℝ) * (Ginv * Bpos)) = G * Bneg / (q : ℝ) := by
    rw [hGinv, hB]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [h1] at h
  have h2 : cR * |y| ≤ G * Bneg / (q : ℝ) := by
    calc cR * |y| = |cR * y| := by rw [abs_mul, abs_of_pos hcR]
      _ ≤ G * Bneg / (q : ℝ) := h
  have h3 : |y| ≤ (G * Bneg / (q : ℝ)) / cR := by
    rw [le_div_iff₀ hcR]
    linarith [h2]
  have h4 : (G * Bneg / (q : ℝ)) / cR ≤ G * Bneg / cR := by
    rw [div_div]
    refine div_le_div_of_nonneg_left ?_ hcR ?_
    · rw [hB]
      exact mul_nonneg (le_of_lt hG) (le_of_lt (inv_pos.mpr hBpos))
    · exact le_mul_of_one_le_left (le_of_lt hcR) hqR1
  exact le_trans h3 h4

/-- **The small-denominator regime of the minor-arc bound** (MST §4.1, the case `q < n^γ`). If `a/q` (`1 ≤ q < n^γ`) approximates the scaled frequency `c · iwRep ξ` (`c = P.leadingCoeff > 0`) to within `1/(q · n^{-γ} 2^{n d})`, and `c·q ≤ n^l` (`l` the level parameter, so that `a/(c·q)` is a Farey fraction of denominator `≤ n^l`), and `2^{iwK (mstRho l)} ≤ n^l` (the hypothesis of `farey_cover_by_taoSetS`/`sigmaN_contains_farey` at level `n^l`), then `ξ` lies in the *inner* ball `|iwRep(ξ − β₀)| ≤ (1/4)·2^{-n(d-χ)}` of the point `β₀ = a/(c·q) ∈ 𝒰(n) = mstU l n`.

Witness `β₀ := arcPt (P.leadingCoeff.toNat * q) a`. Its membership in `mstU l n = iwSigma (mstRho l) (n^l) = sigmaLeFinset (taoSetS (mstRho l) (n^l)) (iwK (mstRho l))`: from `hN` and `1 ≤ c.toNat * q ≤ n^l`, `Work.BourgainPlan.IonescuWainger.farey_cover_by_taoSetS` (via `sigmaN_contains_farey`) or directly `Work.BourgainPlan.Maximal.arcPt_mem_sigmaSubAFinset_of_dvd` (`Maximal/sigmaN_farey_helpers.lean`, no coprimality of the numerator needed) gives the membership — note `c.toNat = c` as reals because `hc : 0 < c`. Quantitatively, `hclose` divided by `c > 0` gives `|iwRep ξ − a/(c q)| ≤ n^γ 2^{-nd}/(q c) ≤ n^γ 2^{-nd}/c ≤ hgap ≤ (1/4)2^{-n(d-χ)} < 1/2`, so the class of `iwRep ξ − a/(c q)` has that value as its canonical lift, i.e. `iwRep (ξ − β₀) = iwRep ξ − a/(c q)` (use `AddCircle.liftIoc_coe_apply` and `coe_iwRep`). -/
theorem mst_smallq_inner (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    {χ : ℝ} (hχ : 0 < χ) {γ : ℝ} (hγ : 0 < γ) {l : ℕ} (hl : 1 ≤ l)
    {n : ℕ} {ξ : Work.BourgainPlan.IonescuWainger.Circle} {a : ℤ} {q : ℕ}
    (hq1 : 1 ≤ q) (hqγ : (q : ℝ) < (n : ℝ) ^ γ)
    (hden : P.leadingCoeff.toNat * q ≤ n ^ l)
    (hN : 2 ^ Work.BourgainPlan.Maximal.iwK (Work.BourgainPlan.Maximal.mstRho l) ≤ n ^ l)
    (hgap : (n : ℝ) ^ γ * (2 : ℝ) ^ (-((n : ℝ) * (P.natDegree : ℝ))) / (P.leadingCoeff : ℝ)
              ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ))))
    (hbig : (n : ℝ) ^ γ * (2 : ℝ) ^ (-((n : ℝ) * (P.natDegree : ℝ))) / (P.leadingCoeff : ℝ)
              < 1 / 2)
    (hclose : |(P.leadingCoeff : ℝ) * Work.BourgainPlan.Maximal.iwRep ξ - (a : ℝ) / (q : ℝ)|
                ≤ 1 / ((q : ℝ) * ((n : ℝ) ^ (-γ) * (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ))))) :
    ∃ β₀ ∈ Work.BourgainPlan.Maximal.mstU l n,
      |Work.BourgainPlan.Maximal.iwRep (ξ - β₀)|
        ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ))) := by
  have hcR_pos0 : 0 < (P.leadingCoeff : ℝ) := by exact_mod_cast hc
  have htoNat : ((P.leadingCoeff.toNat : ℤ)) = P.leadingCoeff := Int.toNat_of_nonneg (le_of_lt hc)
  have hcnR0 : ((P.leadingCoeff.toNat : ℕ) : ℝ) = (P.leadingCoeff : ℝ) := by
    rw [← Int.cast_natCast, htoNat]
  -- `n > 0`
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have hqge : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    by_contra h
    have hn0 : (n : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
    rw [hn0, Real.zero_rpow (ne_of_gt hγ)] at hqγ
    linarith
  -- **the witness lies in 𝒰(n)**
  have hmemb : arcPt (P.leadingCoeff.toNat * q) a ∈ mstU l n := by
    have hcnpos : P.leadingCoeff.toNat ≠ 0 := by
      intro h
      have hz : ((P.leadingCoeff.toNat : ℕ) : ℝ) = 0 := by simp [h]
      rw [hcnR0] at hz
      exact hcR_pos0.ne' hz
    have hcn1 : 1 ≤ P.leadingCoeff.toNat := Nat.one_le_iff_ne_zero.mpr hcnpos
    have hq1' : 1 ≤ P.leadingCoeff.toNat * q :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hcnpos (by omega))
    have hmstRho_pos : 0 < mstRho l := by
      rw [mstRho]
      apply div_pos one_pos
      have : (0 : ℕ) < l := lt_of_lt_of_le Nat.zero_lt_one hl
      positivity
    obtain ⟨A, hAS, hAcard, hdiv⟩ :=
      farey_cover_by_taoSetS (mstRho l) hmstRho_pos (n ^ l) (by simpa [iwK] using hN)
        (P.leadingCoeff.toNat * q) hq1' hden
    rw [mstU, iwSigma, sigmaLeFinset, Finset.mem_biUnion]
    refine ⟨A, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hAS, by rw [iwK]; exact hAcard⟩
    · exact arcPt_mem_sigmaSubAFinset_of_dvd hq1' (QA_ne_zero_of_subset_taoSetS hAS) hdiv a
  refine ⟨arcPt (P.leadingCoeff.toNat * q) a, hmemb, ?_⟩
  -- **the quantitative bound**
  set cR : ℝ := (P.leadingCoeff : ℝ) with hcRdef
  set G : ℝ := (n : ℝ) ^ γ with hGdef
  set Ginv : ℝ := (n : ℝ) ^ (-γ) with hGinvDef
  set Bpos : ℝ := (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)) with hBposDef
  set Bneg : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (P.natDegree : ℝ))) with hBnegDef
  set E : ℝ := (2 : ℝ) ^ (-((n : ℝ) * ((P.natDegree : ℝ) - χ))) with hEDef
  have hcnR : ((P.leadingCoeff.toNat : ℕ) : ℝ) = cR := by rw [hcnR0, hcRdef]
  have hcR_pos : 0 < cR := by rw [hcRdef]; exact hcR_pos0
  have hGpos : 0 < G := by rw [hGdef]; exact Real.rpow_pos_of_pos hnpos γ
  have hBpos_pos : 0 < Bpos := by rw [hBposDef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hGinv_eq : Ginv = G⁻¹ := by
    rw [hGinvDef, hGdef, Real.rpow_neg (le_of_lt hnpos)]
  have hBneg_eq : Bneg = Bpos⁻¹ := by
    rw [hBnegDef, hBposDef, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  -- the real number whose class is `ξ - β₀`
  set x : ℝ := iwRep ξ - (a : ℝ) / (((P.leadingCoeff.toNat : ℕ) : ℝ) * (q : ℝ)) with hxdef
  have hx_eq : cR * x = cR * iwRep ξ - (a : ℝ) / (q : ℝ) := by
    rw [hxdef, hcnR]
    field_simp
  have hclose'' : |cR * x| ≤ 1 / ((q : ℝ) * (Ginv * Bpos)) := by
    rw [hx_eq]
    exact hclose
  have hx_bound : |x| ≤ G * Bneg / cR :=
    abs_le_of_abs_mul_le cR x G Ginv Bpos Bneg q hcR_pos hq1 hGpos hGinv_eq hBneg_eq
      hBpos_pos hclose''
  have hx_half : |x| < 1 / 2 := lt_of_le_of_lt hx_bound hbig
  have hxIoc : x ∈ Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
    rw [Set.mem_Ioc]
    have h := abs_lt.mp hx_half
    exact ⟨h.1, by linarith [h.2]⟩
  have hβ₀circ : ξ - arcPt (P.leadingCoeff.toNat * q) a
      = ((x : ℝ) : Work.BourgainPlan.IonescuWainger.Circle) := by
    rw [hxdef, arcPt, Nat.cast_mul]
    conv_lhs => rw [← coe_iwRep ξ]
    rw [← AddCircle.coe_sub (1 : ℝ)]
  have hiwrep : iwRep (ξ - arcPt (P.leadingCoeff.toNat * q) a) = x := by
    rw [hβ₀circ]
    show AddCircle.liftIoc (1 : ℝ) (-(1 / 2)) (fun y : ℝ => y)
      ((x : ℝ) : Work.BourgainPlan.IonescuWainger.Circle) = x
    exact AddCircle.liftIoc_coe_apply (f := fun y : ℝ => y) hxIoc
  rw [hiwrep]
  exact le_trans hx_bound hgap

end Work.BourgainPlan.Maximal
