import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.RedProj.complexify_analyticAt
import Submission.Work.TMComp.RedProj.glue_polydisc_single
import Submission.Work.TMComp.RedProj.exists_tube_subset_union_polydiscs
import Submission.Work.TMComp.RedProj.eqzero_of_product_intervals

namespace Work.TMComp.RedProj

open Set Metric

private lemma mem_ball_ofReal {a x r : ℝ} : (x : ℂ) ∈ Metric.ball (a : ℂ) r ↔ |x - a| < r := by
  rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

private lemma ball_inter_real {a b r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hne : (Metric.ball (a : ℂ) r ∩ Metric.ball (b : ℂ) t).Nonempty) :
    ∃ a' b' : ℝ, a' < b' ∧ ∀ x : ℝ, x ∈ Set.Ioo a' b' →
      (x : ℂ) ∈ Metric.ball (a : ℂ) r ∩ Metric.ball (b : ℂ) t := by
  obtain ⟨z, hz1, hz2⟩ := hne
  have hz1' : dist z (a:ℂ) < r := hz1
  have hz2' : dist z (b:ℂ) < t := hz2
  have hab : |a - b| < r + t := by
    have h1 : dist (a:ℂ) (b:ℂ) ≤ dist (a:ℂ) z + dist z (b:ℂ) := dist_triangle _ _ _
    have h2 : dist (a:ℂ) (b:ℂ) = |a - b| := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have e1 : dist (a:ℂ) z < r := by rw [dist_comm]; exact hz1'
    rw [h2] at h1
    linarith
  have hab' : |b - a| < r + t := by rw [abs_sub_comm]; exact hab
  have hrpt : 0 < r + t := by linarith
  set cc : ℝ := a + (b - a) * (r / (r + t)) with hcc
  have hca : |cc - a| < r := by
    have h1 : cc - a = (b - a) * (r / (r + t)) := by rw [hcc]; field_simp; ring
    rw [h1, abs_mul, abs_of_pos (by positivity : (0:ℝ) < r / (r + t))]
    have h2 : |b - a| * (r / (r + t)) < (r + t) * (r / (r + t)) :=
      mul_lt_mul_of_pos_right hab' (by positivity)
    have h3 : (r + t) * (r / (r + t)) = r := by field_simp
    exact h2.trans_eq h3
  have hcb : |cc - b| < t := by
    have h1 : cc - b = (a - b) * (t / (r + t)) := by rw [hcc]; field_simp; ring
    rw [h1, abs_mul, abs_of_pos (by positivity : (0:ℝ) < t / (r + t))]
    have h2 : |a - b| * (t / (r + t)) < (r + t) * (t / (r + t)) :=
      mul_lt_mul_of_pos_right hab (by positivity)
    have h3 : (r + t) * (t / (r + t)) = t := by field_simp
    exact h2.trans_eq h3
  have hcc1 : (cc : ℂ) ∈ Metric.ball (a : ℂ) r := by rw [mem_ball_ofReal]; exact hca
  have hcc2 : (cc : ℂ) ∈ Metric.ball (b : ℂ) t := by rw [mem_ball_ofReal]; exact hcb
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp (isOpen_ball.inter isOpen_ball) (cc : ℂ) ⟨hcc1, hcc2⟩
  refine ⟨cc - ε/2, cc + ε/2, by linarith, fun x hx => ?_⟩
  apply hε
  rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_lt]
  rw [Set.mem_Ioo] at hx
  constructor <;> linarith [hx.1, hx.2]

private lemma periodic_int (f : ℝ × ℝ → ℂ) (hper : ∀ E x, f (E, x + 1) = f (E, x)) :
    ∀ (E y : ℝ) (n : ℤ), f (E, y + n) = f (E, y) := by
  intro E y n
  have hp : Function.Periodic (fun p : ℝ × ℝ => f p) (0, 1) := by
    intro p
    have h : (p + (0,1) : ℝ×ℝ) = (p.1, p.2 + 1) := Prod.ext (by simp) (by simp)
    rw [h]; exact hper p.1 p.2
  have h2 := hp.zsmul n
  have h3 := h2 (E, y)
  simpa [Prod.smul_mk, Prod.mk_add_mk] using h3

theorem complexify_analyticOn (f : ℝ × ℝ → ℂ) (a b c d : ℝ) (hac : a < c) (hcd : c ≤ d) (hdb : d < b)
    (hf : AnalyticOnNhd ℝ f (Set.Ioo a b ×ˢ Set.univ))
    (hper : ∀ E x, f (E, x + 1) = f (E, x)) :
    ∃ (Δ : Set ℂ) (ρ : ℝ) (F : ℂ × ℂ → ℂ), IsOpen Δ ∧
      (Set.Icc c d : Set ℝ) ⊆ {E : ℝ | (E : ℂ) ∈ Δ} ∧ 0 < ρ ∧
      DifferentiableOn ℂ F {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ} ∧
      (∀ E ∈ Set.Icc c d, ∀ x : ℝ, F ((E : ℂ), (x : ℂ)) = f (E, x)) ∧
      (∀ p ∈ {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ}, F (p.1, p.2 + 1) = F (p.1, p.2)) := by
  classical
  have hper_int := periodic_int f hper
  set K : Set (ℝ × ℝ) := Set.Icc c d ×ˢ Set.Icc (0:ℝ) 1 with hKdef
  have hKc : IsCompact K := by rw [hKdef]; exact isCompact_Icc.prod isCompact_Icc
  have hAn : ∀ p : ℝ × ℝ, p ∈ K → AnalyticAt ℝ f p := by
    intro p hp
    rw [hKdef] at hp
    exact hf p ⟨⟨lt_of_lt_of_le hac hp.1.1, lt_of_le_of_lt hp.1.2 hdb⟩, trivial⟩
  have hdata : ∀ p : K, ∃ r : ℝ, ∃ (_ : 0 < r), ∃ F : ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ F (Metric.ball ((p.1.1 : ℂ), (p.1.2 : ℂ)) r) ∧
      (∀ x : ℝ × ℝ, x ∈ Metric.ball p.1 r → F ((x.1 : ℂ), (x.2 : ℂ)) = f x) :=
    fun p => complexify_analyticAt f p.1 (hAn p.1 p.2)
  choose rK hposK Fk hFkAnd using hdata
  have hrKpos : ∀ p : K, 0 < rK p := hposK
  have hFk : ∀ p : K, AnalyticOnNhd ℂ (Fk p) (Metric.ball ((p.1.1 : ℂ), (p.1.2 : ℂ)) (rK p)) :=
    fun p => (hFkAnd p).1
  have hFkr : ∀ p : K, ∀ x : ℝ × ℝ, x ∈ Metric.ball p.1 (rK p) →
      Fk p ((x.1:ℂ),(x.2:ℂ)) = f x := fun p => (hFkAnd p).2
  have hcoverK : K ⊆ ⋃ k : K, Metric.ball k.1 (rK k / 2) := by
    intro p hp
    refine mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
    rw [Metric.mem_ball, dist_self]
    linarith [hrKpos ⟨p, hp⟩]
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun k : K => Metric.ball k.1 (rK k / 2))
    (fun k => Metric.isOpen_ball) hcoverK
  let ι := {k : K // k ∈ t}
  haveI : Fintype ι := inferInstance
  let aE : ι → ℝ := fun k => k.1.1.1
  let bX : ι → ℝ := fun k => k.1.1.2
  let rad : ι → ℝ := fun k => rK k.1 / 2
  have haE : aE = fun k : ι => k.1.1.1 := rfl
  have hbX : bX = fun k : ι => k.1.1.2 := rfl
  have hraddef : rad = fun k : ι => rK k.1 / 2 := rfl
  have hrad : ∀ k : ι, 0 < rad k := fun k => by rw [hraddef]; linarith [hrKpos k.1]
  have hcover : ∀ E₀ ∈ Set.Icc c d, ∀ x₀ ∈ Set.Icc (0:ℝ) 1, ∃ i : ι,
      |E₀ - aE i| < rad i ∧ |x₀ - bX i| < rad i := by
    intro E₀ hE x₀ hx
    have hpK : (E₀, x₀) ∈ K := by rw [hKdef]; exact ⟨hE, hx⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp (ht hpK)
    obtain ⟨hk1, hk2⟩ := mem_iUnion.mp hk
    refine ⟨⟨k, hk1⟩, ?_, ?_⟩
    · rw [Metric.mem_ball, Prod.dist_eq] at hk2
      exact (max_lt_iff.mp hk2).1
    · rw [Metric.mem_ball, Prod.dist_eq] at hk2
      exact (max_lt_iff.mp hk2).2
  let P : ι × ℤ → Set (ℂ × ℂ) := fun k =>
    Metric.ball (aE k.1 : ℂ) (rad k.1) ×ˢ Metric.ball (((bX k.1 + (k.2 : ℝ) : ℝ)) : ℂ) (rad k.1)
  let Fp : ι × ℤ → ℂ × ℂ → ℂ := fun k p => Fk k.1.1 (p.1, p.2 - (k.2 : ℂ))
  have hPdef : P = fun k : ι × ℤ =>
    Metric.ball (aE k.1 : ℂ) (rad k.1) ×ˢ Metric.ball (((bX k.1 + (k.2 : ℝ) : ℝ)) : ℂ) (rad k.1) := rfl
  have hFpdef : Fp = fun (k : ι × ℤ) (p : ℂ × ℂ) => Fk k.1.1 (p.1, p.2 - (k.2 : ℂ)) := rfl
  have hFp : ∀ k : ι × ℤ, AnalyticOnNhd ℂ (Fp k) (P k) := by
    intro k
    have hbase : AnalyticOnNhd ℂ (Fk k.1.1)
        (Metric.ball (aE k.1 : ℂ) (rad k.1) ×ˢ Metric.ball (bX k.1 : ℂ) (rad k.1)) := by
      refine (hFk k.1.1).mono ?_
      simp only [haE, hbX]
      rw [show Metric.ball ((k.1.1.1.1 : ℂ), (k.1.1.1.2 : ℂ)) (rK k.1.1)
            = Metric.ball (k.1.1.1.1 : ℂ) (rK k.1.1) ×ˢ Metric.ball (k.1.1.1.2 : ℂ) (rK k.1.1)
          from (ball_prod_same (k.1.1.1.1 : ℂ) (k.1.1.1.2 : ℂ) (rK k.1.1)).symm]
      exact Set.prod_mono
        (Metric.ball_subset_ball (by rw [hraddef]; linarith [hrKpos k.1.1]))
        (Metric.ball_subset_ball (by rw [hraddef]; linarith [hrKpos k.1.1]))
    have hT : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => (p.1, p.2 - (k.2 : ℂ))) (P k) := by
      have h := (analyticOnNhd_id (𝕜 := ℂ) (s := P k)).sub
        (analyticOnNhd_const (𝕜 := ℂ) (v := ((0 : ℂ), (k.2 : ℂ))) (s := P k))
      have hiff : ((fun x : ℂ × ℂ => x) - (fun _ => ((0 : ℂ), (k.2 : ℂ))))
          = (fun p : ℂ × ℂ => (p.1, p.2 - (k.2 : ℂ))) := by
        funext p
        simp only [Pi.sub_apply]
        exact Prod.ext (by simp) (by simp)
      rwa [hiff] at h
    have hmaps : MapsTo (fun p : ℂ × ℂ => (p.1, p.2 - (k.2 : ℂ))) (P k)
        (Metric.ball (aE k.1 : ℂ) (rad k.1) ×ˢ Metric.ball (bX k.1 : ℂ) (rad k.1)) := by
      intro p hp
      rw [hPdef] at hp
      obtain ⟨hp1, hp2⟩ := mem_prod.mp hp
      rw [mem_prod]
      refine ⟨hp1, ?_⟩
      rw [Metric.mem_ball, Complex.dist_eq] at hp2 ⊢
      rw [show p.2 - (k.2 : ℂ) - (bX k.1 : ℂ)
          = p.2 - (((bX k.1 + (k.2 : ℝ) : ℝ)) : ℂ) by push_cast; ring]
      exact hp2
    have hcomp := hbase.comp hT hmaps
    simpa only [hFpdef, Function.comp_def] using hcomp
  have hFp_real : ∀ k : ι × ℤ, ∀ x : ℝ × ℝ,
      x ∈ Metric.ball (aE k.1, bX k.1 + (k.2 : ℝ)) (rad k.1) → Fp k ((x.1:ℂ),(x.2:ℂ)) = f x := by
    intro k x hx
    have hx' := hx
    rw [Metric.mem_ball, Prod.dist_eq] at hx'
    obtain ⟨hx1, hx2⟩ := max_lt_iff.mp hx'
    rw [Real.dist_eq] at hx1 hx2
    have hmem : (x.1, x.2 - (k.2:ℝ)) ∈ Metric.ball k.1.1.1 (rK k.1.1) := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · rw [Real.dist_eq]
        simp only [haE, hraddef] at hx1
        linarith [hrKpos k.1.1]
      · rw [Real.dist_eq]
        simp only [hbX, hraddef] at hx2
        rw [show x.2 - (k.2:ℝ) - k.1.1.1.2 = x.2 - (k.1.1.1.2 + (k.2:ℝ)) by ring]
        linarith [hrKpos k.1.1]
    have hFpeq : Fp k ((x.1:ℂ),(x.2:ℂ)) = Fk k.1.1 ((x.1:ℂ), ((x.2 - (k.2:ℝ) : ℝ) : ℂ)) := by
      simp only [hFpdef]
      congr 1
      simp only [Complex.ofReal_sub]
      push_cast
      ring
    rw [hFpeq, hFkr k.1.1 (x.1, x.2 - (k.2:ℝ)) hmem]
    have h2 := hper_int x.1 (x.2 - (k.2:ℝ)) k.2
    rw [show x.2 - (k.2:ℝ) + (k.2:ℝ) = x.2 by ring] at h2
    exact h2.symm
  have hagree : ∀ k l : ι × ℤ, (P k ∩ P l).Nonempty → Set.EqOn (Fp k) (Fp l) (P k ∩ P l) := by
    intro k l hne
    obtain ⟨z, hz1, hz2⟩ := hne
    rw [hPdef] at hz1 hz2
    obtain ⟨hz1a, hz1b⟩ := mem_prod.mp hz1
    obtain ⟨hz2a, hz2b⟩ := mem_prod.mp hz2
    have hne1 : (Metric.ball (aE k.1 : ℂ) (rad k.1) ∩ Metric.ball (aE l.1 : ℂ) (rad l.1)).Nonempty :=
      ⟨z.1, ⟨hz1a, hz2a⟩⟩
    have hne2 : (Metric.ball (((bX k.1 + (k.2:ℝ) : ℝ)) : ℂ) (rad k.1) ∩
        Metric.ball (((bX l.1 + (l.2:ℝ) : ℝ)) : ℂ) (rad l.1)).Nonempty :=
      ⟨z.2, ⟨hz1b, hz2b⟩⟩
    obtain ⟨a', b', hab, hIsub⟩ := ball_inter_real (hrad k.1) (hrad l.1) hne1
    obtain ⟨p', q', hpq, hJsub⟩ := ball_inter_real (hrad k.1) (hrad l.1) hne2
    let U1 : Set ℂ := Metric.ball (aE k.1 : ℂ) (rad k.1) ∩ Metric.ball (aE l.1 : ℂ) (rad l.1)
    let U2 : Set ℂ := Metric.ball (((bX k.1 + (k.2:ℝ) : ℝ)) : ℂ) (rad k.1) ∩
        Metric.ball (((bX l.1 + (l.2:ℝ) : ℝ)) : ℂ) (rad l.1)
    have hU1 : U1 = Metric.ball (aE k.1 : ℂ) (rad k.1) ∩ Metric.ball (aE l.1 : ℂ) (rad l.1) := rfl
    have hU2 : U2 = Metric.ball (((bX k.1 + (k.2:ℝ) : ℝ)) : ℂ) (rad k.1) ∩
        Metric.ball (((bX l.1 + (l.2:ℝ) : ℝ)) : ℂ) (rad l.1) := rfl
    have hH : AnalyticOnNhd ℂ (Fp k - Fp l) (U1 ×ˢ U2) := by
      have h1 : AnalyticOnNhd ℂ (Fp k) (U1 ×ˢ U2) := by
        refine (hFp k).mono ?_
        rw [hU1, hPdef]
        exact Set.prod_mono inter_subset_left inter_subset_left
      have h2 : AnalyticOnNhd ℂ (Fp l) (U1 ×ˢ U2) := by
        refine (hFp l).mono ?_
        rw [hU1, hPdef]
        exact Set.prod_mono inter_subset_right inter_subset_right
      exact h1.sub h2
    have hsub : ∀ x ∈ Set.Ioo a' b', ∀ y ∈ Set.Ioo p' q', ((x:ℂ),(y:ℂ)) ∈ U1 ×ˢ U2 := by
      intro x hx y hy
      rw [hU1, mem_prod]
      exact ⟨hIsub x hx, hJsub y hy⟩
    have hzero : ∀ x ∈ Set.Ioo a' b', ∀ y ∈ Set.Ioo p' q', (Fp k - Fp l) ((x:ℂ),(y:ℂ)) = 0 := by
      intro x hx y hy
      obtain ⟨hxk, hxl⟩ := (hIsub x hx)
      obtain ⟨hyk, hyl⟩ := (hJsub y hy)
      have hk1 : (x, y) ∈ Metric.ball (aE k.1, bX k.1 + (k.2:ℝ)) (rad k.1) := by
        rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
        exact ⟨by rw [Real.dist_eq]; exact mem_ball_ofReal.mp hxk,
               by rw [Real.dist_eq]; exact mem_ball_ofReal.mp hyk⟩
      have hk2 : (x, y) ∈ Metric.ball (aE l.1, bX l.1 + (l.2:ℝ)) (rad l.1) := by
        rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
        exact ⟨by rw [Real.dist_eq]; exact mem_ball_ofReal.mp hxl,
               by rw [Real.dist_eq]; exact mem_ball_ofReal.mp hyl⟩
      simp only [Pi.sub_apply]
      rw [hFp_real k (x,y) hk1, hFp_real l (x,y) hk2, sub_self]
    have ho1 : IsOpen U1 := by rw [hU1]; exact isOpen_ball.inter isOpen_ball
    have ho2 : IsOpen U2 := by rw [hU2]; exact isOpen_ball.inter isOpen_ball
    have hc1 : IsPreconnected U1 := by
      rw [hU1]
      exact ((convex_ball (aE k.1 : ℂ) (rad k.1)).inter
        (convex_ball (aE l.1 : ℂ) (rad l.1))).isPreconnected
    have hc2 : IsPreconnected U2 := by
      rw [hU2]
      exact ((convex_ball (((bX k.1 + (k.2:ℝ) : ℝ)) : ℂ) (rad k.1)).inter
        (convex_ball (((bX l.1 + (l.2:ℝ) : ℝ)) : ℂ) (rad l.1))).isPreconnected
    have hres := eqzero_of_product_intervals ho1 ho2 hc1 hc2 hH hab hpq hsub hzero
    intro w hw
    have hwk : w ∈ P k := hw.1
    have hwl : w ∈ P l := hw.2
    rw [hPdef] at hwk hwl
    obtain ⟨hwk1, hwk2⟩ := mem_prod.mp hwk
    obtain ⟨hwl1, hwl2⟩ := mem_prod.mp hwl
    have hwU : w ∈ U1 ×ˢ U2 := by
      rw [hU1, hU2, mem_prod]
      exact ⟨⟨hwk1, hwl1⟩, ⟨hwk2, hwl2⟩⟩
    have hz := hres hwU
    simp only [Pi.sub_apply, Pi.zero_apply] at hz
    exact sub_eq_zero.mp hz
  obtain ⟨G, hG, hGF⟩ := glue_polydisc_single (fun k : ι × ℤ => aE k.1)
      (fun k : ι × ℤ => bX k.1 + (k.2 : ℝ)) (fun k : ι × ℤ => rad k.1)
      (fun k : ι × ℤ => rad k.1) (fun k => hrad k.1) (fun k => hrad k.1) Fp
      (by simpa only [hPdef] using hFp) (by simpa only [hPdef] using hagree)
  obtain ⟨Δ, hΔopen, hΔsub, ρ, hρpos, htube⟩ :=
    exists_tube_subset_union_polydiscs c d hcd aE bX rad rad hrad hrad hcover
  let F : ℂ × ℂ → ℂ := fun p => if p.1 ∈ Δ ∧ |p.2.im| < ρ then G p else 0
  have hFdef : F = fun p : ℂ × ℂ => if p.1 ∈ Δ ∧ |p.2.im| < ρ then G p else 0 := rfl
  have hsubD : {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ} ⊆ ⋃ k : ι × ℤ, P k := by
    intro p hp
    have hp' : p ∈ Δ ×ˢ {w : ℂ | |w.im| < ρ} := by rw [mem_prod]; exact ⟨hp.1, hp.2⟩
    have h := htube hp'
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    obtain ⟨n, hn⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨(i, n), hn⟩
  refine ⟨Δ, ρ, F, hΔopen, hΔsub, hρpos, ?_, ?_, ?_⟩
  · have hGdiff : DifferentiableOn ℂ G {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ} :=
      (hG.mono hsubD).differentiableOn
    refine hGdiff.congr (fun p hp => ?_)
    rw [hFdef]; exact dif_pos hp
  · intro E hE x
    have hEin : (E : ℂ) ∈ Δ := hΔsub hE
    have him : |((x : ℂ)).im| < ρ := by rw [Complex.ofReal_im, abs_zero]; exact hρpos
    have hp : ((E : ℂ), (x : ℂ)) ∈ {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ} := ⟨hEin, him⟩
    rw [show F ((E:ℂ),(x:ℂ)) = G ((E:ℂ),(x:ℂ)) by rw [hFdef]; exact dif_pos hp]
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hsubD hp)
    rw [hGF k hk]
    refine hFp_real k (E, x) ?_
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    rw [hPdef] at hk
    have hk' := mem_prod.mp hk
    exact ⟨by rw [Real.dist_eq]; exact mem_ball_ofReal.mp hk'.1,
           by rw [Real.dist_eq]; exact mem_ball_ofReal.mp hk'.2⟩
  · intro p hp
    have hpim : (p.2 + 1).im = p.2.im := by simp
    have hp' : (p.1, p.2 + 1) ∈ {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ} := by
      refine ⟨hp.1, ?_⟩; rw [hpim]; exact hp.2
    rw [show F (p.1, p.2+1) = G (p.1,p.2+1) by rw [hFdef]; exact dif_pos hp',
        show F (p.1, p.2) = G (p.1,p.2) by rw [hFdef]; exact dif_pos hp]
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hsubD hp)
    have hknext : (p.1, p.2 + 1) ∈ P (k.1, (k.2 : ℤ) + 1) := by
      rw [hPdef] at hk
      obtain ⟨hk1, hk2⟩ := mem_prod.mp hk
      have hk2' : p.2 + 1 ∈ Metric.ball ((((bX k.1 + (((k.2:ℤ)+1 : ℤ) : ℝ)) : ℝ)) : ℂ) (rad k.1) := by
        rw [Metric.mem_ball, Complex.dist_eq] at hk2 ⊢
        rw [show p.2 + 1 - ((((bX k.1 + (((k.2:ℤ)+1 : ℤ) : ℝ)) : ℝ)) : ℂ)
              = p.2 - ((((bX k.1 + (k.2:ℝ)) : ℝ)) : ℂ) by push_cast; ring]
        exact hk2
      rw [hPdef, mem_prod]
      exact ⟨hk1, hk2'⟩
    rw [hGF k hk, hGF (k.1, (k.2 : ℤ) + 1) hknext]
    simp only [hFpdef]
    rw [show (p.2 + 1 - ((((k.2:ℤ)+1 : ℤ) : ℂ))) = (p.2 - (((k.2:ℤ) : ℂ))) by push_cast; ring]

end Work.TMComp.RedProj
