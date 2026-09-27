import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.Defs
import Submission.Work.EQ.LAFree
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.Ladf.wsec_descent
import Submission.Work.EQ.Ladf.wsec_defs
import Submission.Work.EQ.Ladf.candChain_isChain_of_middle
import Submission.Work.EQ.Ladf.candChain_fwdW_bwdW
import Submission.Work.EQ.Ladf.ann_minus_finite_preconnected
import Submission.Work.EQ.regComp_lift_over_annulus
import Submission.Work.EQ.Refl.component_projection_cocountable
import Submission.Work.EQ.bwdFanDefs

/-!
# Finitely many components per value for a fixed reading datum

`Work.EQ.Ladf.la_components_card`: for a fixed reading datum `(f, [], b, M)` over a small annulus
`Ann r₁ r₂` and a fixed value `c`, only finitely many regular components `S` satisfy
`(c, S) ∈ LAFree.DatumSet a h r₁ r₂ M f b`.

## Argument

Fix `zstar` strictly inside the annulus and outside the countable set `P` of `ψ₁`-limits of genuine
punctures of `⁰H`.  For a component `S` of the fibre with witness `q₀` (so `q₀` has both tails
principal from `M`), the local analytic section of `⁰H` through `q₀` supplies a chain `q` of `S`
strictly inside the annulus whose tails are still principal from `M` (`wsec_tails_ball`), and
`Work.EQ.regComp_lift_over_annulus` then transports the tail data along the annulus to `zstar`: there
is `q' ∈ S` with `ψ₁ q' = zstar` whose tails are principal from a common depth `N ≥ M`.

`q'` is a chain of `H0` with value `c` and both tails principal from `N`, so
`LAFree.chain_eq_candChain_canonical` writes it as `candChain a h ε [] s N c zstar` with words of
length `N` — one of finitely many candidates.  Distinct components of the fibre contain distinct
such candidates (components are disjoint), so the fibre is contained in the image of the finite set
of candidates under `connectedComponentIn`.
-/

namespace Work.EQ.Ladf

open Work.EQ Complex Filter _root_.Topology
open scoped Topology

noncomputable section

/-- **A point of the open annulus near a point of the closed annulus.**  For `0 < r₁ < r₂`, every
point `u` of the closed annulus and every radius `ρ > 0`, some `w` in the ball of radius `ρ` about
`u` lies strictly inside the annulus (radial perturbation of `u`). -/
lemma exists_mem_ball_openAnn {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂)
    {u : ℂ} (hu₁ : r₁ ≤ ‖u‖) (hu₂ : ‖u‖ ≤ r₂) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ w : ℂ, w ∈ Metric.ball u ρ ∧ r₁ < ‖w‖ ∧ ‖w‖ < r₂ := by
  have hupos : 0 < ‖u‖ := lt_of_lt_of_le hr₁ hu₁
  have hune : u ≠ 0 := norm_pos_iff.mp hupos
  rcases lt_or_eq_of_le hu₁ with hlt | heq
  · -- move radially inwards
    have hroom : 0 < ‖u‖ - r₁ := by linarith
    set ε : ℝ := min ρ (‖u‖ - r₁) / 2 with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef]
      exact div_pos (lt_min hρ hroom) (by norm_num)
    have hερ : ε < ρ := by
      have h1 : min ρ (‖u‖ - r₁) ≤ ρ := min_le_left _ _
      rw [hεdef]
      linarith
    have hεr : ε < ‖u‖ - r₁ := by
      have h1 : min ρ (‖u‖ - r₁) ≤ ‖u‖ - r₁ := min_le_right _ _
      rw [hεdef]
      linarith
    have hεu : ε < ‖u‖ := by linarith
    have hqlt : ε / ‖u‖ < 1 := by
      rw [div_lt_one hupos]; exact hεu
    have hqpos : (0:ℝ) < 1 - ε / ‖u‖ := by linarith
    have hqneg : (-(ε / ‖u‖) : ℝ) < 0 := by
      have : (0:ℝ) < ε / ‖u‖ := div_pos hεpos hupos
      linarith
    have hnorm : ‖u‖ * (1 - ε / ‖u‖) = ‖u‖ - ε := by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ (ne_of_gt hupos)]
    refine ⟨u * ((1 - ε / ‖u‖ : ℝ) : ℂ), ?_, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have h : u * ((1 - ε / ‖u‖ : ℝ) : ℂ) - u = ((-(ε / ‖u‖) : ℝ) : ℂ) * u := by
        push_cast; ring
      rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hqneg, neg_neg]
      rw [div_mul_cancel₀ _ (ne_of_gt hupos)]
      exact hερ
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos, hnorm]
      linarith
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos, hnorm]
      linarith
  · -- `‖u‖ = r₁`: move radially outwards
    have hu_eq : ‖u‖ = r₁ := heq.symm
    have hroom : 0 < r₂ - r₁ := by linarith
    set ε : ℝ := min ρ (r₂ - r₁) / 2 with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef]
      exact div_pos (lt_min hρ hroom) (by norm_num)
    have hερ : ε < ρ := by
      have h1 : min ρ (r₂ - r₁) ≤ ρ := min_le_left _ _
      rw [hεdef]; linarith
    have hεr : ε < r₂ - r₁ := by
      have h1 : min ρ (r₂ - r₁) ≤ r₂ - r₁ := min_le_right _ _
      rw [hεdef]; linarith
    have hqpos2 : (0:ℝ) < ε / ‖u‖ := div_pos hεpos hupos
    have hone2 : (0:ℝ) < 1 + ε / ‖u‖ := by linarith
    have hnorm2 : ‖u‖ * (1 + ε / ‖u‖) = ‖u‖ + ε := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt hupos)]
    refine ⟨u * ((1 + ε / ‖u‖ : ℝ) : ℂ), ?_, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have h : u * ((1 + ε / ‖u‖ : ℝ) : ℂ) - u = ((ε / ‖u‖ : ℝ) : ℂ) * u := by
        push_cast; ring
      rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos2]
      rw [div_mul_cancel₀ _ (ne_of_gt hupos)]
      exact hερ
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hone2, hnorm2, hu_eq]
      linarith
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hone2, hnorm2, hu_eq]
      linarith

/-- **A point of the open annulus near a point of the closed annulus, avoiding a countable
set.** -/
lemma exists_mem_ball_openAnn_notMem {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂)
    {P : Set ℂ} (hP : P.Countable) {u : ℂ} (hu₁ : r₁ ≤ ‖u‖) (hu₂ : ‖u‖ ≤ r₂) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∃ w : ℂ, w ∈ Metric.ball u ρ ∧ r₁ < ‖w‖ ∧ ‖w‖ < r₂ ∧ w ∉ P := by
  obtain ⟨w₀, hw₀ball, hw₀₁, hw₀₂⟩ := exists_mem_ball_openAnn hr₁ hr₁₂ hu₁ hu₂ hρ
  have hw₀d : dist w₀ u < ρ := by rwa [Metric.mem_ball] at hw₀ball
  set ρ'' : ℝ := min (min ((ρ - dist w₀ u) / 2) ((‖w₀‖ - r₁) / 2)) ((r₂ - ‖w₀‖) / 2)
    with hρ''def
  have hρ''1 : ρ'' ≤ (ρ - dist w₀ u) / 2 :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ''2 : ρ'' ≤ (‖w₀‖ - r₁) / 2 :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ''3 : ρ'' ≤ (r₂ - ‖w₀‖) / 2 := min_le_right _ _
  have hρ''pos : 0 < ρ'' := by
    rw [hρ''def]
    exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  obtain ⟨w, hwball, hwP⟩ := Refl.exists_mem_ball_notMem (x := w₀) hρ''pos hP
  have hdw : dist w w₀ < ρ'' := by rwa [Metric.mem_ball] at hwball
  have hclose : dist w w₀ < (ρ - dist w₀ u) / 2 := lt_of_lt_of_le hdw hρ''1
  have hlow : dist w w₀ < (‖w₀‖ - r₁) / 2 := lt_of_lt_of_le hdw hρ''2
  have hup : dist w w₀ < (r₂ - ‖w₀‖) / 2 := lt_of_lt_of_le hdw hρ''3
  have hdiff : |‖w‖ - ‖w₀‖| ≤ dist w w₀ := by
    rw [dist_eq_norm]
    exact abs_norm_sub_norm_le w w₀
  refine ⟨w, ?_, ?_, ?_, hwP⟩
  · rw [Metric.mem_ball]
    calc dist w u ≤ dist w w₀ + dist w₀ u := dist_triangle _ _ _
      _ < ρ := by linarith
  · have h1 : -(dist w w₀) ≤ ‖w‖ - ‖w₀‖ := (abs_le.mp hdiff).1
    linarith
  · have h1 : ‖w‖ - ‖w₀‖ ≤ dist w w₀ := (abs_le.mp hdiff).2
    linarith

/-- **Finitely many components per value for a fixed reading datum.** -/
theorem la_components_card {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (hpos : 0 < rhoStar a h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r₁ r₂ : ℝ) (M : ℕ) (f b : List Bool),
      0 < r₁ → r₁ < r₂ → r₂ < δ → 1 / eqLam a < r₂ / r₁ → f.length = M → b.length = M →
      (eqLam a : ℝ) ^ M * r₂ < δ →
      (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁ < δ →
      ∀ c : ℂ, {S : Set ChainData | (c, S) ∈ LAFree.DatumSet a h r₁ r₂ M f b}.Finite := by
  classical
  obtain ⟨P, hPc, hlift⟩ := regComp_lift_over_annulus (a := a) (h := h) (r := r) ha0 ha1 hh
  obtain ⟨δW, hδW0, hwsec⟩ := wsec_tails_ball (a := a) (h := h) (r := r) ha0 ha1 hh
  refine ⟨δW, hδW0, ?_⟩
  intro r₁ r₂ M f b hr₁ hr₁₂ hr₂δ hratio hf hb hsm1 hsm2 c
  have hlam_pos : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam_nn : (0 : ℝ) ≤ eqLam a := le_of_lt hlam_pos
  -- the uniform tail floor of the lifting tool
  obtain ⟨n₀, hn₀⟩ := hlift (B := 2 * rhoStar a h) hr₁ hr₁₂
  set N : ℕ := max M n₀ with hNdef
  have hMN : M ≤ N := le_max_left _ _
  have hn₀N : n₀ ≤ N := le_max_right _ _
  -- the comparison point, strictly inside the annulus and outside the puncture values
  have hnorm_r1 : ‖((r₁ : ℝ) : ℂ)‖ = r₁ := Complex.norm_of_nonneg hr₁.le
  have hle_r1 : r₁ ≤ ‖((r₁ : ℝ) : ℂ)‖ := le_of_eq hnorm_r1.symm
  have hle_r2 : ‖((r₁ : ℝ) : ℂ)‖ ≤ r₂ := by rw [hnorm_r1]; exact le_of_lt hr₁₂
  obtain ⟨zstar, -, hz1, hz2, hzP⟩ :=
    exists_mem_ball_openAnn_notMem (r₁ := r₁) (r₂ := r₂) (P := P) (u := ((r₁ : ℝ) : ℂ)) (ρ := 1)
      hr₁ hr₁₂ hPc hle_r1 hle_r2 (by norm_num)
  have hz0 : zstar ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hz1; linarith
  -- the finite set of candidate chains over `zstar`
  set K : Set ChainData := (fun p : List Bool × List Bool =>
      candChain a h p.2 [] p.1 N c zstar) ''
      ({σ : List Bool | σ ∈ fanWords N} ×ˢ {τ : List Bool | τ ∈ fanWords N}) with hKdef
  have hKfin : K.Finite := by
    have h1 : ({σ : List Bool | σ ∈ fanWords N} ×ˢ
        {τ : List Bool | τ ∈ fanWords N}).Finite :=
      (List.finite_toSet (fanWords N)).prod (List.finite_toSet (fanWords N))
    rw [hKdef]
    exact h1.image _
  refine Set.Finite.subset (hKfin.image (fun x : ChainData => connectedComponentIn (H0 a h) x)) ?_
  -- every component of the fibre contains a candidate chain over `zstar`
  rintro S hS
  rw [LAFree.DatumSet, Set.mem_ofPred_eq] at hS
  obtain ⟨hSreg, hcnorm, q₀, hq₀S, hq₀ann, hq₀eq, -, hq₀bwd⟩ := hS
  set u₀ : ℂ := q₀.2.1 with hu₀def
  have hq₀H0 : q₀ ∈ H0 a h := hSreg.1 hq₀S
  have hu₀1 : r₁ ≤ ‖u₀‖ := hq₀ann.1
  have hu₀2 : ‖u₀‖ ≤ r₂ := hq₀ann.2
  have hu₀ne : u₀ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hu₀1; linarith
  have hq₀2 : q₀.2.2 = c / u₀ := by rw [hq₀eq, candChain_psi2]
  -- the junction identity of the witness
  have hJ : bwdP a b (fan a h f u₀) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ M * (c / u₀)) := by
    have h1 := hq₀bwd M le_rfl
    rw [hq₀2] at h1
    have h2 : q₀.1 (-(M : ℤ)) = bwdP a b (fan a h f u₀) := by
      rw [hq₀eq]
      have h3 := candChain_fst_neg a h f [] b M c u₀ (j := M) le_rfl
      rwa [List.take_of_length_le (le_of_eq hb)] at h3
    rw [h2] at h1
    exact h1
  -- the analytic local section of `⁰H` at the witness
  obtain ⟨-, hsect, -, -⟩ := H0_structure (a := a) ha0 ha1 (h := h) (r := r) hh
  obtain ⟨ρs, hρspos, g, hg0, hgmem, hgan, hgψ2, -⟩ := hsect q₀ hq₀H0
  have hcontg : ContinuousOn g (Metric.ball u₀ ρs) := by
    refine ContinuousOn.prodMk ?_ ?_
    · rw [continuousOn_pi]
      intro n
      exact (hgan n).continuousOn
    · refine ContinuousOn.prodMk ?_ ?_
      · exact continuousOn_id.congr (fun z hz => (hgmem z hz).2)
      · exact hgψ2.continuousOn
  have hvalg : ∀ z ∈ Metric.ball u₀ ρs, (g z).2.1 * (g z).2.2 = c := by
    have himg : IsPreconnected (g '' Metric.ball u₀ ρs) :=
      (Metric.isPreconnected_ball (x := u₀) (r := ρs)).image _ hcontg
    have hScomp : S = connectedComponentIn (H0 a h) q₀ := by
      obtain ⟨p, -, hSp⟩ := hSreg.2.1
      have hqcomp : q₀ ∈ connectedComponentIn (H0 a h) p := by rw [← hSp]; exact hq₀S
      calc S = connectedComponentIn (H0 a h) p := hSp
        _ = connectedComponentIn (H0 a h) q₀ := connectedComponentIn_eq hqcomp
    have hsub : g '' Metric.ball u₀ ρs ⊆ S := by
      rw [hScomp]
      refine IsPreconnected.subset_connectedComponentIn himg ⟨u₀, ?_, hg0⟩ ?_
      · exact Metric.mem_ball_self hρspos
      · rintro x ⟨y, hy, rfl⟩
        exact (hgmem y hy).1
    intro z hz
    exact hSreg.2.2 (g z) (hsub ⟨z, hz, rfl⟩)
  have hsectat : IsSectAt a h g u₀ ρs :=
    ⟨hρspos, by rw [hg0]; exact hq₀H0,
      fun z hz => ⟨(hgmem z hz).1, (hgmem z hz).2⟩, hgan, hgψ2⟩
  -- the smallness conditions of `wsec_tails_ball` at the witness
  have hlem_u : (eqLam a : ℝ) ^ M * ‖u₀‖ < δW := by
    have hle : (eqLam a : ℝ) ^ M * ‖u₀‖ ≤ (eqLam a : ℝ) ^ M * r₂ :=
      mul_le_mul_of_nonneg_left hu₀2 (by positivity)
    linarith
  have hlem_c : (eqLam a : ℝ) ^ M * ‖c / u₀‖ < δW := by
    have hcu : ‖c / u₀‖ ≤ 2 * rhoStar a h / r₁ := by
      rw [norm_div]
      exact div_le_div₀ (by positivity) hcnorm hr₁ hu₀1
    have hle : (eqLam a : ℝ) ^ M * ‖c / u₀‖ ≤
        (eqLam a : ℝ) ^ M * (2 * rhoStar a h / r₁) :=
      mul_le_mul_of_nonneg_left hcu (by positivity)
    have heq : (eqLam a : ℝ) ^ M * (2 * rhoStar a h / r₁) =
        (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁ := by ring
    linarith
  -- both tails of the section's chains from depth `M` on
  obtain ⟨ρt, hρtpos, hρtle, htails⟩ :=
    hwsec M f b hf hb hu₀ne hsectat (hg0.trans hq₀eq) hvalg hJ hlem_u hlem_c
  -- a starting chain of `S` strictly inside the annulus, outside the puncture values
  obtain ⟨u₁, hu₁ball, hu₁1, hu₁2, hu₁P⟩ :=
    exists_mem_ball_openAnn_notMem hr₁ hr₁₂ (hPc.union (Set.countable_singleton 0))
      hu₀1 hu₀2 (lt_min hρtpos hρspos)
  have hu₁t : u₁ ∈ Metric.ball u₀ ρt := by
    rw [Metric.mem_ball] at hu₁ball ⊢
    exact lt_of_lt_of_le hu₁ball (min_le_left _ _)
  have hu₁s : u₁ ∈ Metric.ball u₀ ρs := by
    rw [Metric.mem_ball] at hu₁ball ⊢
    exact lt_of_lt_of_le hu₁ball (min_le_right _ _)
  have hu₁0 : u₁ ≠ 0 := fun h0 => hu₁P (Or.inr (by simpa using h0))
  have hu₁P' : u₁ ∉ P := fun h => hu₁P (Or.inl h)
  set q₁ : ChainData := g u₁ with hq₁def
  have hq₁ψ : q₁.2.1 = u₁ := (hgmem u₁ hu₁s).2
  have hq₁S : q₁ ∈ S := by
    have himg : IsPreconnected (g '' Metric.ball u₀ ρs) :=
      (Metric.isPreconnected_ball (x := u₀) (r := ρs)).image _ hcontg
    have hScomp : S = connectedComponentIn (H0 a h) q₀ := by
      obtain ⟨p, -, hSp⟩ := hSreg.2.1
      have hqcomp : q₀ ∈ connectedComponentIn (H0 a h) p := by rw [← hSp]; exact hq₀S
      calc S = connectedComponentIn (H0 a h) p := hSp
        _ = connectedComponentIn (H0 a h) q₀ := connectedComponentIn_eq hqcomp
    have hsub : g '' Metric.ball u₀ ρs ⊆ S := by
      rw [hScomp]
      refine IsPreconnected.subset_connectedComponentIn himg ⟨u₀, ?_, hg0⟩ ?_
      · exact Metric.mem_ball_self hρspos
      · rintro x ⟨y, hy, rfl⟩
        exact (hgmem y hy).1
    exact hsub ⟨u₁, hu₁s, rfl⟩
  have hq₁P : TailP a h q₁ M := by
    show ∀ n : ℕ, M ≤ n → q₁.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * q₁.2.1)
    intro n hn
    rw [hq₁ψ]
    exact (htails u₁ hu₁t).1 n hn
  have hq₁2 : q₁.2.2 = c / u₁ := by
    have h1 := hvalg u₁ hu₁s
    rw [hq₁ψ] at h1
    exact (eq_div_iff hu₁0).mpr (by rw [mul_comm]; exact h1)
  have hq₁B : TailB a h q₁ M := by
    show ∀ n : ℕ, M ≤ n → q₁.1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * q₁.2.2)
    intro n hn
    rw [hq₁2]
    exact (htails u₁ hu₁t).2 n hn
  -- transport along the annulus to `zstar`
  obtain ⟨q', hq'S, hq'ψ, hq'tails⟩ :=
    hn₀ hSreg hcnorm q₁ hq₁S (by rw [hq₁ψ]; exact hu₁1) (by rw [hq₁ψ]; exact hu₁2)
      zstar hz1 hz2 hzP
  have hq'P : TailP a h q' N := by
    show ∀ m : ℕ, N ≤ m → q'.1 (m : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ m * q'.2.1)
    intro m hm
    exact ((hq'tails N hn₀N).1).mp (fun k hk => hq₁P k (le_trans hMN hk)) m hm
  have hq'B : TailB a h q' N := by
    show ∀ m : ℕ, N ≤ m → q'.1 (-(m : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * q'.2.2)
    intro m hm
    exact ((hq'tails N hn₀N).2).mp (fun k hk => hq₁B k (le_trans hMN hk)) m hm
  -- the candidate chain over `zstar` is one of the finitely many candidates
  have hq'chain : IsChain a h q' := isChain_of_mem_H0 (hSreg.1 hq'S)
  have hq'val : q'.2.1 * q'.2.2 = c := hSreg.2.2 q' hq'S
  have hq'eq' : q' = candChain a h (fwdW a N q') [] (bwdW a N q') N c q'.2.1 :=
    LAFree.chain_eq_candChain_canonical ha0 ha1 hq'chain hq'val
      (fun n hn => hq'P n hn) (fun n hn => hq'B n hn)
  have hq'eq : q' = candChain a h (fwdW a N q') [] (bwdW a N q') N c zstar := by
    rw [← hq'ψ]; exact hq'eq' 
  refine ⟨q', ?_, ?_⟩
  · rw [hKdef]
    refine ⟨(bwdW a N q', fwdW a N q'), ?_, hq'eq.symm⟩
    exact ⟨mem_fanWords.mpr (Work.EQ.bwdW_length a N q'),
      mem_fanWords.mpr (Work.EQ.fwdW_length a N q')⟩
  · obtain ⟨p, -, hSp⟩ := hSreg.2.1
    have hqcomp : q' ∈ connectedComponentIn (H0 a h) p := by rw [← hSp]; exact hq'S
    calc connectedComponentIn (H0 a h) q' = connectedComponentIn (H0 a h) p :=
          (connectedComponentIn_eq hqcomp).symm
      _ = S := hSp.symm

end

end Work.EQ.Ladf
