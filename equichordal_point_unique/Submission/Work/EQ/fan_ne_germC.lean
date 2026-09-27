import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.FanUniform.fan_uniform_estimates
import Submission.Work.EQ.AnalyticTaylor.second_order_remainder
import Submission.Work.EQ.CharVal.charVal_near_zero
import Submission.Work.EQ.fan_sep
import Submission.Work.EQ.FanSep.germ_lip
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.charVal_main
import Submission.Work.EQ.walk_count

set_option maxHeartbeats 1000000

namespace Work.EQ

open Complex Metric Filter
open scoped Topology

noncomputable section

lemma aux_norm_sub_le {E : Type*} [SeminormedAddCommGroup E] (x y z : E) : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
  have h : x - z = (x - y) + (y - z) := by abel
  rw [h]; exact norm_add_le _ _

lemma aux_norm_ofReal (x : ℝ) : ‖(((x:ℝ)) : ℂ)‖ = |x| := RCLike.norm_ofReal x

lemma aux_pair_le {x y : ℂ} {c : ℝ} (hx : ‖x‖ ≤ c) (hy : ‖y‖ ≤ c) : ‖(x,y)‖ ≤ c := by
  rw [Prod.norm_def]; exact max_le hx hy

lemma aux_three {E : Type*} [SeminormedAddCommGroup E] (A B C : E) : ‖B‖ - ‖A‖ - ‖C‖ ≤ ‖A + B + C‖ := by
  have h1 : ‖B‖ ≤ ‖A + B + C‖ + ‖A + C‖ := by
    have h2 := norm_sub_le (A + B + C) (A + C)
    have h3 : A + B + C - (A + C) = B := by abel
    rwa [h3] at h2
  have h4 : ‖A + C‖ ≤ ‖A‖ + ‖C‖ := norm_add_le _ _
  linarith

variable {a : ℝ} {h : ℂ → ℂ} {r : ℝ}

/-- A fan value whose branch word ends in a *non-principal* letter stays a definite distance
away from the germ point with the same linearising parameter: for `ε` ending in `false` and
`‖v‖ < δ`, `fan a h ε v` and `germC a h v` differ by at least `c * ‖v‖`.

Route.  `fan_estimates` (`FanGood`, `fan_centres`) puts `fan a h ε v` within `Ke ‖v‖` of its
centre `fan a h ε 0`, an axis point of `-1/2 + 2ℤ`; `fan_germC_local` puts `germC a h v` within
`K ‖v‖` of `germC a h 0 = (-1/2, 0)`.  If the centre is not `-1/2` the two points are a definite
distance apart and the claim is immediate.  If the centre is `-1/2`, compare second coordinates:
by `charVal_of_closed`/`charVal_props`/`walk_count` the characteristic value `charVal a h ε`
(a product of the walk weights of `ε.reverse`, of modulus `≤ γ ^ (ε.count false)` with `γ < 1`)
is not `1`, because `ε` ends in `false` forces a `false` letter; so the second coordinates differ
in first order, and Cauchy estimates (uniform analyticity of the fan) bound the remainder.

Implementation (this file).  The uniform first-order fan estimates and analyticity on a disc are
`Work.EQ.FanUniform.fan_uniform_estimates` (from the majorant induction of `Work.EQ.fan_sep`),
the uniform second-order remainder is `Work.EQ.AnalyticTaylor.second_order_remainder` (the
Schwarz lemma `Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO` at order `1`), and the
quantitative non-vanishing of `charVal - 1` is `Work.EQ.CharVal.charVal_near_zero`.  The germ's
first-order bounds are `Work.EQ.FanSep.germ_lip`, and `Work.EQ.fan_sep` supplies the "centre
away from `A₁`" case. -/

theorem fan_ne_germC {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ ε : List Bool, ε.getLast? = some false → ∀ v : ℂ, ‖v‖ < δ →
      c * ‖v‖ ≤ ‖Work.EQ.fan a h ε v - Work.EQ.germC a h v‖ := by
  -- ==== basic data ====
  have hA1 : germC a h 0 = ((-1/2 : ℂ), (0:ℂ)) := germC_value ha0 ha1 hh
  obtain ⟨-, -, hgder, -⟩ := germC_diff_at_zero ha0 ha1 hh
  have hD0pos : (0:ℝ) < (1-a)/2 := by linarith
  have hconv1 : ((-1/2 : ℝ) : ℂ) = (-1/2 : ℂ) := by norm_num
  set D0 : ℝ := (1-a)/2 with hD0rdef
  have hD0r0 : 0 < D0 := by rw [hD0rdef]; linarith
  set D0c : ℂ := ((((1-a)/2:ℝ)) : ℂ) with hD0cdef
  have hD0cn : ‖D0c‖ = D0 := by rw [hD0cdef, aux_norm_ofReal, abs_of_pos hD0pos, hD0rdef]
  obtain ⟨δs, hδs0, hsep⟩ := fan_sep ha0 ha1 hh
  obtain ⟨δg, pg, qg, hδg0, hpg0, hqg0, hgerm⟩ := FanSep.germ_lip ha0 ha1 hh
  obtain ⟨ρ, hρ0, hAnC⟩ := germC_analytic ha0 ha1 hh
  obtain ⟨δan, Ke, Lam, hδan0, hKe0, hLam0, hD1⟩ := FanUniform.fan_uniform_estimates ha0 ha1 hh
  have D2 : ∀ (f : ℂ → ℂ) (R M : ℝ), 0 < R → f 0 = 0 → DifferentiableOn ℂ f (Metric.ball 0 R) →
      (∀ z ∈ Metric.ball (0:ℂ) R, ‖f z‖ ≤ M) →
      ∀ v : ℂ, v ∈ Metric.ball (0:ℂ) R → ‖f v - deriv f 0 * v‖ ≤ 2 * M * (‖v‖/R)^2 :=
    fun f R M hR h0 hd hM v hv => AnalyticTaylor.second_order_remainder hR h0 hd hM v hv
  obtain ⟨γ, hγ0, hγ1, hD3⟩ := CharVal.charVal_near_zero ha0 ha1 hh
  have h1mγ : (0:ℝ) < 1 - γ := by linarith
  -- ==== germ Lipschitz constant ====
  set Mg' : ℝ := max pg (qg * ((1+a)/2 + pg*δg)) with hMg'def
  have hMg'0 : 0 < Mg' := lt_of_lt_of_le hpg0 (le_max_left _ _)
  have hger2 : (0:ℝ) < (1+a)/2 + pg*δg := by
    have ha : (0:ℝ) < (1+a)/2 := by linarith
    have hb : (0:ℝ) < pg*δg := mul_pos hpg0 hδg0
    linarith
  have hgerm_lip : ∀ u : ℂ, ‖u‖ < δg → ‖germC a h u - germC a h 0‖ ≤ Mg' * ‖u‖ := by
    intro u hu
    have h1 : ‖(germC a h u).1 - ((-1/2 : ℝ) : ℂ)‖ ≤ pg * ‖u‖ := (hgerm u hu).1
    have h2 : ‖(germC a h u).1 - ((a/2:ℝ):ℂ)‖ ≤ (1+a)/2 + pg*δg := by
      have h3 : ‖(germC a h u).1 - ((a/2:ℝ):ℂ)‖ ≤
          ‖(germC a h u).1 - ((-1/2:ℝ):ℂ)‖ + ‖((-1/2:ℝ):ℂ) - ((a/2:ℝ):ℂ)‖ :=
        aux_norm_sub_le _ _ _
      have h4 : ‖((-1/2:ℝ):ℂ) - ((a/2:ℝ):ℂ)‖ = (1+a)/2 := by
        have he : ((-1/2:ℝ):ℂ) - ((a/2:ℝ):ℂ) = ((-(1+a)/2 : ℝ) : ℂ) := by push_cast; ring
        rw [he, aux_norm_ofReal, abs_of_neg (by linarith : -(1+a)/2 < 0)]
        try ring
      have h5 : pg * ‖u‖ ≤ pg * δg := mul_le_mul_of_nonneg_left (le_of_lt hu) (le_of_lt hpg0)
      linarith
    have h6 : ‖(germC a h u).2‖ ≤ Mg' * ‖u‖ := by
      have h7 := (hgerm u hu).2
      have h9 : qg * ‖u‖ * ‖(germC a h u).1 - ((a/2:ℝ):ℂ)‖ ≤ qg * ‖u‖ * ((1+a)/2 + pg*δg) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hqg0.le (norm_nonneg u))
      have h10 : (qg * ((1+a)/2 + pg*δg)) * ‖u‖ ≤ Mg' * ‖u‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg u)
      linarith
    have h11 : ‖germC a h u - germC a h 0‖ = max ‖(germC a h u).1 - (-1/2:ℂ)‖ ‖(germC a h u).2‖ := by
      rw [hA1, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_zero]
    rw [h11]
    refine max_le ?_ h6
    rw [← hconv1]
    exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg u))
  -- ==== radii and constants ====
  set δa : ℝ := min δg (min δs (3/(16*Mg'))) with hδadef
  have hδa0 : 0 < δa := by
    rw [hδadef]
    exact lt_min hδg0 (lt_min hδs0 (by positivity))
  have hδa_le_g : δa ≤ δg := min_le_left _ _
  have hδa_le_s : δa ≤ δs := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδa_le_316 : δa ≤ 3/(16*Mg') := le_trans (min_le_right _ _) (min_le_right _ _)
  set Rf : ℝ := min δan δs with hRfdef
  have hRf0 : 0 < Rf := lt_min hδan0 hδs0
  have hRf_le_an : Rf ≤ δan := min_le_left _ _
  have hRf_le_s : Rf ≤ δs := min_le_right _ _
  set Mf : ℝ := (1/4 + (1+a)/2)/4 with hMfdef
  have hMf0 : 0 < Mf := by rw [hMfdef]; positivity
  -- ==== fan value bound on the analyticity disc ====
  have hFbound : ∀ (ε : List Bool), fan a h ε 0 = ((-1/2:ℂ),(0:ℂ)) → ∀ z ∈ Metric.ball (0:ℂ) Rf,
      ‖(fan a h ε z).2‖ ≤ Mf := by
    intro ε hc z hz
    have hzs : z ∈ Metric.ball (0:ℂ) δs := Metric.ball_subset_ball hRf_le_s hz
    obtain ⟨-, -, hx, hy⟩ := hsep ε z hzs
    have hc1 : (fan a h ε 0).1 = (-1/2 : ℂ) := by rw [hc]
    have h3 : ‖(fan a h ε z).1 - ((a/2:ℝ):ℂ)‖ ≤ 1/4 + (1+a)/2 := by
      have h4 : ‖(fan a h ε z).1 - ((a/2:ℝ):ℂ)‖ ≤
          ‖(fan a h ε z).1 - (fan a h ε 0).1‖ + ‖(fan a h ε 0).1 - ((a/2:ℝ):ℂ)‖ :=
        aux_norm_sub_le _ _ _
      have h2 : ‖(fan a h ε 0).1 - ((a/2:ℝ):ℂ)‖ = (1+a)/2 := by
        rw [hc1]
        have he : (-1/2:ℂ) - ((a/2:ℝ):ℂ) = ((-(1+a)/2 : ℝ) : ℂ) := by push_cast; ring
        rw [he, aux_norm_ofReal, abs_of_neg (by linarith : -(1+a)/2 < 0)]
        try ring
      linarith
    calc ‖(fan a h ε z).2‖ ≤ ‖(fan a h ε z).1 - ((a/2:ℝ):ℂ)‖/4 := hy
      _ ≤ Mf := by rw [hMfdef]; linarith
  -- ==== fan Taylor remainder ====
  have hFrem : ∀ (ε : List Bool) (v : ℂ), fan a h ε 0 = ((-1/2:ℂ),(0:ℂ)) → v ∈ Metric.ball (0:ℂ) Rf →
      ‖(fan a h ε v).2 - deriv (fun u => (fan a h ε u).2) 0 * v‖ ≤ 2*Mf*(‖v‖/Rf)^2 := by
    intro ε v hc hv
    refine D2 (fun u => (fan a h ε u).2) Rf Mf hRf0 ?_ ?_ ?_ v hv
    · rw [hc]
    · exact ((hD1 ε).1.differentiableOn.mono (Metric.ball_subset_ball hRf_le_an)).snd
    · exact hFbound ε hc
  -- ==== germ Taylor remainder ====
  set Rg : ℝ := min δg ρ with hRgdef
  have hRg0 : 0 < Rg := lt_min hδg0 hρ0
  have hRg_le_g : Rg ≤ δg := min_le_left _ _
  have hRg_le_ρ : Rg ≤ ρ := min_le_right _ _
  set Mg : ℝ := qg * δg * ((1+a)/2 + pg*δg) with hMgdef
  have hMg0 : 0 < Mg := by rw [hMgdef]; exact mul_pos (mul_pos hqg0 hδg0) hger2
  have hGval : ∀ z ∈ Metric.ball (0:ℂ) Rg, ‖(germC a h z).2‖ ≤ Mg := by
    intro z hz
    have hzg : z ∈ Metric.ball (0:ℂ) δg := Metric.ball_subset_ball hRg_le_g hz
    have hzu : ‖z‖ < δg := by rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hzg
    have hdx : ‖(germC a h z).1 - ((-1/2 : ℝ) : ℂ)‖ ≤ pg * ‖z‖ := (hgerm z hzu).1
    have hsq : ‖(germC a h z).1 - ((a/2:ℝ):ℂ)‖ ≤ (1+a)/2 + pg*δg := by
      have h1 : ‖(germC a h z).1 - ((a/2:ℝ):ℂ)‖ ≤
          ‖(germC a h z).1 - ((-1/2:ℝ):ℂ)‖ + ‖((-1/2:ℝ):ℂ) - ((a/2:ℝ):ℂ)‖ := aux_norm_sub_le _ _ _
      have h2 : ‖((-1/2:ℝ):ℂ) - ((a/2:ℝ):ℂ)‖ = (1+a)/2 := by
        have he : ((-1/2:ℝ):ℂ) - ((a/2:ℝ):ℂ) = ((-(1+a)/2 : ℝ) : ℂ) := by push_cast; ring
        rw [he, aux_norm_ofReal, abs_of_neg (by linarith : -(1+a)/2 < 0)]
        try ring
      have h3 : pg * ‖z‖ ≤ pg * δg := mul_le_mul_of_nonneg_left (le_of_lt hzu) (le_of_lt hpg0)
      linarith
    have h5 : ‖(germC a h z).2‖ ≤ qg * ‖z‖ * ((1+a)/2 + pg*δg) :=
      le_trans (hgerm z hzu).2 (mul_le_mul_of_nonneg_left hsq (mul_nonneg hqg0.le (norm_nonneg z)))
    have h6 : qg * ‖z‖ * ((1+a)/2 + pg*δg) ≤ qg * δg * ((1+a)/2 + pg*δg) := by
      have h7 : qg * ‖z‖ ≤ qg * δg := mul_le_mul_of_nonneg_left (le_of_lt hzu) (le_of_lt hqg0)
      exact mul_le_mul_of_nonneg_right h7 hger2.le
    rw [hMgdef]
    linarith [h5, h6]
  have hGrem : ∀ v : ℂ, v ∈ Metric.ball (0:ℂ) Rg →
      ‖(germC a h v).2 - deriv (fun u => (germC a h u).2) 0 * v‖ ≤ 2*Mg*(‖v‖/Rg)^2 := by
    intro v hv
    refine D2 (fun u => (germC a h u).2) Rg Mg hRg0 ?_ ?_ ?_ v hv
    · rw [hA1]
    · exact (hAnC.differentiableOn.mono (Metric.ball_subset_ball hRg_le_ρ)).snd
    · exact hGval
  -- ==== final constants ====
  set Kc : ℝ := 2*Mf/Rf^2 + 2*Mg/Rg^2 with hKcdef
  have hKc0 : 0 < Kc := by
    rw [hKcdef]
    have h1 : 0 < 2*Mf/Rf^2 := div_pos (by linarith) (by positivity)
    have h2 : 0 < 2*Mg/Rg^2 := div_pos (by linarith) (by positivity)
    linarith
  set δb : ℝ := min Rf (min Rg ((1-γ)*D0/(2*Kc))) with hδbdef
  have hδb0 : 0 < δb := by
    rw [hδbdef]
    refine lt_min hRf0 (lt_min hRg0 ?_)
    exact div_pos (mul_pos h1mγ hD0r0) (by linarith)
  have hδb_le_Rf : δb ≤ Rf := min_le_left _ _
  have hδb_le_Rg : δb ≤ Rg := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδb_le_K : δb ≤ (1-γ)*D0/(2*Kc) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hcpos : 0 < (1-γ)*D0/2 := div_pos (mul_pos h1mγ hD0r0) (by norm_num)
  refine ⟨min δa δb, min ((1-γ)*D0/2) (1/δa), lt_min hδa0 hδb0,
    lt_min hcpos (by positivity), ?_⟩
  intro ε hlast v hv
  have hvδa : ‖v‖ < δa := lt_of_lt_of_le hv (min_le_left _ _)
  have hvδb : ‖v‖ < δb := lt_of_lt_of_le hv (min_le_right _ _)
  have hvRf : v ∈ Metric.ball (0:ℂ) Rf := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact lt_of_lt_of_le hvδb hδb_le_Rf
  have hvRg : v ∈ Metric.ball (0:ℂ) Rg := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact lt_of_lt_of_le hvδb hδb_le_Rg
  have hvδs : v ∈ Metric.ball (0:ℂ) δs := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact lt_of_lt_of_le hvδa hδa_le_s
  have hvn : (0:ℝ) ≤ ‖v‖ := norm_nonneg v
  by_cases hcase : fan a h ε 0 = ((-1/2:ℂ),(0:ℂ))
  · -- ======== centre is A1: first order ========
    have hcv := hD3 ε hlast hcase
    obtain ⟨-, -, hx, hy⟩ := hsep ε v hvδs
    have hder : deriv (fun u => (fan a h ε u).2) 0 = charVal a h ε * D0c := by
      obtain ⟨-, -, -, hderiv⟩ := fan_aux ha0 ha1 hh ε
      rw [hderiv, ← charVal_eq_rprod ha0 ha1 hh ε, hgder, hD0cdef]
    have hrem := hFrem ε v hcase hvRf
    have hgre := hGrem v hvRg
    rw [hder] at hrem
    rw [hgder, hD0cdef] at hgre
    -- objects
    set Fv : ℂ := (fan a h ε v).2 with hFvdef
    set Gv : ℂ := (germC a h v).2 with hGvdef
    set De : ℂ := charVal a h ε * D0c with hDedef
    set L : ℂ := De - D0c with hLdef
    have hLlin : L = (charVal a h ε - 1) * D0c := by rw [hLdef, hDedef]; ring
    have hLnorm : ‖L‖ = ‖charVal a h ε - 1‖ * D0 := by rw [hLlin, norm_mul, hD0cn]
    -- the linear term
    have hlin : (1-γ)*D0*‖v‖ ≤ ‖L*v‖ := by
      rw [norm_mul, hLnorm]
      have h1 : (1-γ)*D0 ≤ ‖charVal a h ε - 1‖*D0 := mul_le_mul_of_nonneg_right hcv hD0r0.le
      calc (1-γ)*D0*‖v‖ = ((1-γ)*D0)*‖v‖ := by ring
        _ ≤ (‖charVal a h ε - 1‖*D0)*‖v‖ := mul_le_mul_of_nonneg_right h1 hvn
    -- the split
    have hsplit : Fv - Gv = (Fv - De*v) + (L*v) + (D0c*v - Gv) := by
      rw [hLdef, hDedef]; ring
    have htri : ‖L*v‖ - ‖Fv - De*v‖ - ‖D0c*v - Gv‖ ≤ ‖Fv - Gv‖ := by
      rw [hsplit]; exact aux_three _ _ _
    -- the remainders
    have hAB : ‖Fv - De*v‖ ≤ 2*Mf*(‖v‖/Rf)^2 := by
      rw [hFvdef, hDedef, hD0cdef]; exact hrem
    have hCG : ‖D0c*v - Gv‖ ≤ 2*Mg*(‖v‖/Rg)^2 := by
      rw [hGvdef, hD0cdef, norm_sub_rev]; exact hgre
    -- the quadratic terms are dominated by the linear terms
    have hsq : ‖v‖^2 ≤ δb*‖v‖ := by nlinarith [hvn, le_of_lt hvδb]
    have hB1 : 2*Mf*(‖v‖/Rf)^2 ≤ (2*Mf/Rf^2)*(δb*‖v‖) := by
      have h0 : (0:ℝ) ≤ 2*Mf/Rf^2 := div_nonneg (by linarith) (by positivity)
      have he : 2*Mf*(‖v‖/Rf)^2 = (2*Mf/Rf^2)*‖v‖^2 := by
        field_simp
        try ring
      rw [he]
      exact mul_le_mul_of_nonneg_left hsq h0
    have hB2 : 2*Mg*(‖v‖/Rg)^2 ≤ (2*Mg/Rg^2)*(δb*‖v‖) := by
      have h0 : (0:ℝ) ≤ 2*Mg/Rg^2 := div_nonneg (by linarith) (by positivity)
      have he : 2*Mg*(‖v‖/Rg)^2 = (2*Mg/Rg^2)*‖v‖^2 := by
        field_simp
        try ring
      rw [he]
      exact mul_le_mul_of_nonneg_left hsq h0
    have hKδb : Kc*δb ≤ (1-γ)*D0/2 := by
      have h3 : Kc * ((1-γ)*D0/(2*Kc)) = (1-γ)*D0/2 := by field_simp
      have h4 := mul_le_mul_of_nonneg_left hδb_le_K hKc0.le
      rw [h3] at h4
      exact h4
    have hBc : 2*Mf*(‖v‖/Rf)^2 + 2*Mg*(‖v‖/Rg)^2 ≤ (1-γ)*D0/2*‖v‖ := by
      have h5 : (2*Mf/Rf^2)*(δb*‖v‖) + (2*Mg/Rg^2)*(δb*‖v‖) = (Kc*δb)*‖v‖ := by
        rw [hKcdef]; ring
      have h6 : Kc*δb*‖v‖ ≤ (1-γ)*D0/2*‖v‖ := mul_le_mul_of_nonneg_right hKδb hvn
      linarith [hB1, hB2, h5.le, h5.ge, h6]
    have hfinal : (1-γ)*D0/2*‖v‖ ≤ ‖Fv - Gv‖ := by
      have h4 : ‖L*v‖ - (2*Mf*(‖v‖/Rf)^2 + 2*Mg*(‖v‖/Rg)^2) ≤ ‖Fv - Gv‖ := by
        linarith [htri, hAB, hCG]
      linarith [h4, hlin, hBc]
    calc min ((1-γ)*D0/2) (1/δa) * ‖v‖ ≤ ((1-γ)*D0/2) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hvn
      _ ≤ ‖Fv - Gv‖ := hfinal
      _ ≤ ‖fan a h ε v - germC a h v‖ := by
          have h2 := norm_snd_le (fan a h ε v - germC a h v)
          rw [Prod.snd_sub] at h2
          exact h2
  · -- ======== centre is not A1: definite distance ========
    obtain ⟨hz2, ⟨k, hk1⟩, hx, hy⟩ := hsep ε v hvδs
    have hkne : k ≠ 0 := by
      intro hk0
      apply hcase
      refine Prod.ext ?_ ?_
      · rw [hk1, hk0]; push_cast; norm_num
      · exact hz2
    have hk1' : (fan a h ε 0).1 = ((-1/2 + 2*(k:ℝ) : ℝ) : ℂ) := by
      rw [hk1]; push_cast; ring
    have hcentre : fan a h ε 0 = ((((-1/2 + 2*(k:ℝ)) : ℝ) : ℂ), (0:ℂ)) := Prod.ext hk1' hz2
    have hkabs : (1:ℝ) ≤ |(k:ℝ)| := by
      have hkz : (1:ℤ) ≤ |k| := Int.one_le_abs hkne
      calc (1:ℝ) = ((1:ℤ):ℝ) := by norm_num
        _ ≤ ((|k|:ℤ):ℝ) := by exact_mod_cast hkz
        _ = |(k:ℝ)| := Int.cast_abs
    have hdist : ‖fan a h ε 0 - germC a h 0‖ = 2*|(k:ℝ)| := by
      have hsub : fan a h ε 0 - germC a h 0 = (((2*(k:ℝ) : ℝ) : ℂ), (0:ℂ)) := by
        rw [hcentre, hA1]
        have h1 : ((-1/2 + 2*(k:ℝ) : ℝ) : ℂ) - (-1/2 : ℂ) = ((2*(k:ℝ) : ℝ) : ℂ) := by
          push_cast; ring
        exact Prod.ext (by rw [Prod.fst_sub, h1]) (by simp)
      rw [hsub, Prod.norm_def]
      simp only [norm_zero, max_eq_left (norm_nonneg _)]
      rw [aux_norm_ofReal, abs_mul, abs_two]
    have hdev : ‖fan a h ε v - fan a h ε 0‖ ≤ (2*|(k:ℝ)|)/4 + 5/16 := by
      have hy2 : ‖(fan a h ε v).2‖ ≤ (2*|(k:ℝ)|)/4 + 5/16 := by
        have h2 : ‖(fan a h ε 0).1 - ((a/2:ℝ):ℂ)‖ ≤ 2*|(k:ℝ)| + 1 := by
          rw [hk1']
          have he : ((-1/2 + 2*(k:ℝ) : ℝ) : ℂ) - ((a/2:ℝ):ℂ) =
              (((2*(k:ℝ) - (1+a)/2) : ℝ) : ℂ) := by push_cast; ring
          rw [he, aux_norm_ofReal]
          have h3 : |2*(k:ℝ) - (1+a)/2| ≤ 2*(|(k:ℝ)|) + (1+a)/2 := by
            have h5 : |(2:ℝ)*(k:ℝ)| = 2*|(k:ℝ)| := by rw [abs_mul]; norm_num
            calc |2*(k:ℝ) - (1+a)/2| = |2*(k:ℝ) + (-((1+a)/2))| := by ring_nf
              _ ≤ |2*(k:ℝ)| + |(-((1+a)/2))| := abs_add_le _ _
              _ = 2*|(k:ℝ)| + (1+a)/2 := by
                have h6 : (0:ℝ) < (1+a)/2 := by linarith
                have h7 : |(-((1+a)/2))| = (1+a)/2 := by rw [abs_neg, abs_of_pos h6]
                rw [h5, h7]
          linarith
        have h3 : ‖(fan a h ε v).1 - ((a/2:ℝ):ℂ)‖ ≤ 1/4 + (2*|(k:ℝ)| + 1) := by
          have h4 : ‖(fan a h ε v).1 - ((a/2:ℝ):ℂ)‖ ≤
              ‖(fan a h ε v).1 - (fan a h ε 0).1‖ + ‖(fan a h ε 0).1 - ((a/2:ℝ):ℂ)‖ :=
            aux_norm_sub_le _ _ _
          linarith
        calc ‖(fan a h ε v).2‖ ≤ ‖(fan a h ε v).1 - ((a/2:ℝ):ℂ)‖/4 := hy
          _ ≤ (1/4 + (2*|(k:ℝ)| + 1))/4 := by linarith
          _ = (2*|(k:ℝ)|)/4 + 5/16 := by ring
      have hdx : ‖(fan a h ε v).1 - (fan a h ε 0).1‖ ≤ (2*|(k:ℝ)|)/4 + 5/16 := by
        have h5 : (0:ℝ) ≤ (2*|(k:ℝ)|)/4 + 5/16 := by positivity
        linarith [hx, h5]
      have hpair : ‖fan a h ε v - fan a h ε 0‖ =
          max ‖(fan a h ε v).1 - (fan a h ε 0).1‖ ‖(fan a h ε v).2‖ := by
        rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, hz2, sub_zero]
      rw [hpair]
      exact max_le hdx hy2
    have hger : ‖germC a h v - germC a h 0‖ ≤ Mg'*‖v‖ := hgerm_lip v (lt_of_lt_of_le hvδa hδa_le_g)
    have hbig : 1 ≤ ‖fan a h ε v - germC a h v‖ := by
      have htri : ‖fan a h ε 0 - germC a h 0‖ - ‖fan a h ε v - fan a h ε 0‖
            - ‖germC a h v - germC a h 0‖ ≤ ‖fan a h ε v - germC a h v‖ := by
        have h1 : fan a h ε v - germC a h v =
            (fan a h ε v - fan a h ε 0) + (fan a h ε 0 - germC a h 0)
              + (germC a h 0 - germC a h v) := by abel
        rw [h1, norm_sub_rev (germC a h v) (germC a h 0)]
        exact aux_three (fan a h ε v - fan a h ε 0) (fan a h ε 0 - germC a h 0)
          (germC a h 0 - germC a h v)
      have hMgv : Mg'*‖v‖ ≤ 3/16 := by
        have h1 : ‖v‖ ≤ 3/(16*Mg') := le_of_lt (lt_of_lt_of_le hvδa hδa_le_316)
        have h3 : Mg'*(3/(16*Mg')) = 3/16 := by field_simp
        calc Mg'*‖v‖ ≤ Mg'*(3/(16*Mg')) := mul_le_mul_of_nonneg_left h1 hMg'0.le
          _ = 3/16 := h3
      have h2k : ‖fan a h ε 0 - germC a h 0‖ ≥ 2 := by
        rw [hdist]; nlinarith [hkabs]
      have hbase : (2*|(k:ℝ)|) - ((2*|(k:ℝ)|)/4 + 5/16) - 3/16 ≥ 1 := by
        nlinarith [hkabs]
      linarith [htri, hdev, hger, hMgv, h2k, hbase]
    calc min ((1-γ)*D0/2) (1/δa) * ‖v‖ ≤ (1/δa) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hvn
      _ ≤ (1/δa) * δa := by
          exact mul_le_mul_of_nonneg_left (le_of_lt hvδa) (by positivity)
      _ = 1 := by field_simp
      _ ≤ ‖fan a h ε v - germC a h v‖ := hbig


end

end Work.EQ
