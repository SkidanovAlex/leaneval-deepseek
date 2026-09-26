import Mathlib
import Submission.Work.Drive.SurgeryStrictAux

/-!
# The single surgery step for the weak disc datum, given the one-sidedness of the level

`Work.Drive.WeakDatumStepOfSign` is the cut-and-paste step of Pardon's Lemma 2 in the weak-disc
formulation: given a weak datum `D` and the structural data `InnermostSignData` of its innermost
trace (in particular the *one-sidedness* of the level `levP ∘ D.e` on the outward tube of the
trace), the innermost trace can be removed, producing a weak datum with the same boundary curve and
strictly fewer traces.

The construction is the one described in `Submission/Work/Drive/CleanDiscsWAll.lean`:

* `β` is the pushed null-homotopy of the inessential curve `D.curves i₀`
  (`Work.Drive.pushedNullHomotopy_level`);
* `phiMap β` is the cut-and-paste map: `β` on the cap of the trace, `D.e` off the bounded side;
* `EMap β` is `phiMap β` pushed by the signed amount `deltaFun`, which is non-zero with the sign
  `σ` on the tube around the trace and vanishes on the boundary circle;
* the pushed map still bounds `D.α`, still maps the remaining traces to their curves, and meets
  `F` only along the remaining traces.

This file uses the auxiliary lemmas of `Submission.Work.Drive.WeakDatumStepAux`.
-/

open Classical
open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.SurgStrict
open Work.CoreTopology

theorem WeakDatumStepOfSignStrict (ψ : LeanEval.KnotTheory.PardonDistortion.R3 ≃ₜ LeanEval.KnotTheory.PardonDistortion.R3)
    (PD : Work.Drive.PushData ψ) (D : Work.Drive.WeakDatum ψ) (S : Work.Drive.InnermostSignData ψ PD D)
    (h : 0 < Fintype.card D.ι) (hint : ∀ i t, ‖(D.kappa i).γ t‖ < 1) :
    ∃ D' : Work.Drive.WeakDatum ψ, D'.α = D.α ∧ Fintype.card D'.ι < Fintype.card D.ι ∧
      (∀ i t, ‖(D'.kappa i).γ t‖ < 1) := by
  classical
  -- The pushed null-homotopy of the innermost curve.
  have hσ4 : |S.σ/4| ≤ 1/4 := by rw [abs_div, abs_sigma]; norm_num
  obtain ⟨β, hβbdy, hβlev⟩ :=
    pushedNullHomotopy_level PD (D.curves S.i₀) (D.curves_inessential S.i₀) (S.σ/4) hσ4
  -- Its level everywhere on the disc, boundary included.
  have hβlev_all : ∀ w : Work.InnermostDisk.Disc,
      PD.levP (β w) = 1 + (S.σ/4) * (1 - ‖(w:ℂ)‖) := by
    intro w
    have hwle : ‖(w:ℂ)‖ ≤ 1 := norm_le_one_disc w
    rcases lt_or_eq_of_le hwle with hlt | heq
    · exact hβlev w hlt
    · obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq w heq
      have h1 : β w = (D.curves S.i₀).γ θ := by
        rw [← hθ]
        exact (congrArg β (Subtype.ext rfl)).trans (hβbdy θ)
      have h2 : PD.levP ((D.curves S.i₀).γ θ) = 1 :=
        (PD.hlev _).mpr ((D.curves S.i₀).mem θ)
      rw [h1, h2, heq]
      ring
  have hcontE : Continuous (EMap (S := S) β) := EMap_cont (S := S) hβbdy
  have hδabs : ∀ z : Work.InnermostDisk.Disc, |deltaFun (S := S) z| ≤ 1/4 :=
    deltaFun_abs_le (S := S)
  have hδsign : ∀ z : Work.InnermostDisk.Disc, 0 ≤ S.σ * deltaFun (S := S) z := by
    intro z
    rcases eq_or_ne (deltaFun (S := S) z) 0 with h0 | h0
    · rw [h0]; simp
    · exact le_of_lt (deltaFun_sign (S := S) h0)
  -- The pushed map stays off `F` on the cap of the trace.
  have hE_ne_one_mem : ∀ (z : Work.InnermostDisk.Disc),
      (z:ℂ) ∈ Set.range S.hsch.e → ‖(z:ℂ)‖ < 1 → PD.levP (EMap (S := S) β z) ≠ 1 := by
    intro z hmem hzlt
    set w : Work.InnermostDisk.Disc := phiHome (S := S).symm ⟨(z:ℂ), hmem⟩ with hw
    have hlevΦ : PD.levP (phiMap (S := S) β z) = 1 + (S.σ/4)*(1 - ‖(w:ℂ)‖) := by
      rw [phiMap_of_mem (S := S) hmem, hw]
      exact hβlev_all w
    have hwle : ‖(w:ℂ)‖ ≤ 1 := norm_le_one_disc w
    have hwnn : 0 ≤ ‖(w:ℂ)‖ := norm_nonneg _
    have hIcc : PD.levP (phiMap (S := S) β z) ∈ Set.Icc (1/2:ℝ) (5/4) := by
      rw [hlevΦ]
      rcases S.hσ with hσ | hσ
      · rw [hσ]
        exact ⟨by nlinarith [hwle, hwnn], by nlinarith [hwle, hwnn]⟩
      · rw [hσ]
        exact ⟨by nlinarith [hwle, hwnn], by nlinarith [hwle, hwnn]⟩
    have hshift := PD.hshift (phiMap (S := S) β z) (deltaFun (S := S) z) hIcc (hδabs z)
    have hEl : PD.levP (EMap (S := S) β z)
        = 1 + (S.σ/4)*(1 - ‖(w:ℂ)‖) + deltaFun (S := S) z := by
      rw [EMap_apply, hshift, hlevΦ]
    have hσ4' : S.σ * (S.σ/4) = 1/4 := by
      have := sigma_mul_self (S:=S); field_simp; nlinarith
    have hkey : S.σ * (PD.levP (EMap (S := S) β z) - 1)
        = (1/4)*(1 - ‖(w:ℂ)‖) + S.σ * deltaFun (S := S) z := by
      rw [hEl]
      calc S.σ * (1 + (S.σ/4)*(1 - ‖(w:ℂ)‖) + deltaFun (S := S) z - 1)
          = S.σ * ((S.σ/4)*(1 - ‖(w:ℂ)‖)) + S.σ * deltaFun (S := S) z := by ring
        _ = (S.σ * (S.σ/4)) * (1 - ‖(w:ℂ)‖) + S.σ * deltaFun (S := S) z := by ring
        _ = (1/4)*(1 - ‖(w:ℂ)‖) + S.σ * deltaFun (S := S) z := by rw [hσ4']
    have hpos : 0 < (1/4)*(1 - ‖(w:ℂ)‖) + S.σ * deltaFun (S := S) z := by
      rcases lt_or_eq_of_le hwle with hwlt | hweq
      · have h1 : 0 < (1/4)*(1 - ‖(w:ℂ)‖) := by nlinarith
        linarith [hδsign z]
      · have hmemK : (z:ℂ) ∈ Set.range (D.kappa S.i₀).γ := by
          obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq w hweq
          refine ⟨θ, ?_⟩
          rw [← S.hsch.boundary θ, hθ, hw]
          exact phiHome_symm_val (S := S) ⟨(z:ℂ), hmem⟩
        have hδnz : deltaFun (S := S) z ≠ 0 := deltaFun_ne_zero_of_mem (S := S) hmemK hzlt
        have h2 : 0 < S.σ * deltaFun (S := S) z := deltaFun_sign (S := S) hδnz
        have h3 : 0 ≤ (1/4)*(1 - ‖(w:ℂ)‖) := by nlinarith
        linarith
    intro hcontra
    have hz0 : (1/4)*(1 - ‖(w:ℂ)‖) + S.σ * deltaFun (S := S) z = 0 := by
      rw [← hkey, hcontra]; ring
    linarith
  -- The pushed map stays off `F` on the outward tube of the trace.
  have hE_ne_one_out : ∀ (z : Work.InnermostDisk.Disc),
      (z:ℂ) ∉ Set.range S.hsch.e → ‖(z:ℂ)‖ < 1 →
      Metric.infDist (z:ℂ) (Set.range (D.kappa S.i₀).γ) < S.r →
      PD.levP (EMap (S := S) β z) ≠ 1 := by
    intro z hout hzlt hnear
    have hφz : phiMap (S := S) β z = D.e z := phiMap_of_not_mem (S := S) hout
    have hout' : (z:ℂ) ∉ closure S.hsch.V := by rw [← S.hsch.range_e]; exact hout
    have hsign : 0 < S.σ * (PD.levP (phiMap (S := S) β z) - 1) := by
      rw [hφz]
      exact S.sign (z:ℂ) z.2 hzlt hnear hout'
    rcases S.hσ with hσ | hσ
    · have hgt : 1 < PD.levP (phiMap (S := S) β z) := by
        rw [hσ] at hsign; linarith
      have hδnn : 0 ≤ deltaFun (S := S) z := by
        have := hδsign z; rw [hσ, one_mul] at this; exact this
      have hδle : deltaFun (S := S) z ≤ 1/4 := (abs_le.mp (hδabs z)).2
      intro hcontra
      by_cases hle : PD.levP (phiMap (S := S) β z) ≤ (5/4:ℝ)
      · have hIcc : PD.levP (phiMap (S := S) β z) ∈ Set.Icc (1/2:ℝ) (5/4) :=
          ⟨by linarith, hle⟩
        have hshift := PD.hshift (phiMap (S := S) β z) (deltaFun (S := S) z) hIcc (hδabs z)
        rw [EMap_apply, hshift] at hcontra
        linarith
      · by_cases hge2 : (3/2:ℝ) ≤ PD.levP (phiMap (S := S) β z)
        · have hge := PD.hge (phiMap (S := S) β z) (deltaFun (S := S) z) hge2
          rw [EMap_apply, hge] at hcontra
          linarith
        · have hgt2' : (5/4:ℝ) < PD.levP (phiMap (S := S) β z) := not_le.mp hle
          have hmono := PD.hmono (phiMap (S := S) β z) (deltaFun (S := S) z) hδnn hδle
            (le_of_lt hgt2')
          rw [EMap_apply] at hcontra
          rw [hcontra] at hmono
          linarith
    · have hlt : PD.levP (phiMap (S := S) β z) < 1 := by
        rw [hσ] at hsign; linarith
      have hδnp : deltaFun (S := S) z ≤ 0 := by
        have := hδsign z; rw [hσ] at this; linarith
      have hδge : (-1:ℝ)/4 ≤ deltaFun (S := S) z := by
        have h := (abs_le.mp (hδabs z)).1; linarith
      have hmono := PD.hmono' (phiMap (S := S) β z) (deltaFun (S := S) z) hδge hδnp
        (le_of_lt hlt)
      intro hcontra
      rw [EMap_apply] at hcontra
      rw [hcontra] at hmono
      linarith
  -- The pushed map still bounds `D.α`.
  have hE_bdry : ∀ θ : ℝ, EMap (S := S) β (Work.CoreTopology.circlePoint θ) = D.α.γ θ := by
    intro θ
    have hδ0 : deltaFun (S := S) (Work.CoreTopology.circlePoint θ) = 0 :=
      deltaFun_circlePoint (S := S) θ
    have hz1 : ‖((Work.CoreTopology.circlePoint θ : Work.InnermostDisk.Disc) : ℂ)‖ = 1 := by
      rw [Work.CoreTopology.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
    rw [EMap_apply, hδ0, PD.hzero]
    by_cases hmem : ((Work.CoreTopology.circlePoint θ : Work.InnermostDisk.Disc) : ℂ)
        ∈ Set.range S.hsch.e
    · have hK := mem_trace_of_mem_range_of_norm_one (S := S) hmem hz1
      rw [phiMap_of_mem (S := S) hmem, beta_agrees (S := S) hβbdy hK hmem]
      exact D.boundary θ
    · rw [phiMap_of_not_mem (S := S) hmem]
      exact D.boundary θ
  -- The remaining traces are still mapped to their curves.
  have hE_maps : ∀ (i : {j : D.ι // j ≠ S.i₀}) (t : ℝ),
      EMap (S := S) β ⟨(D.kappa i.1).γ t, D.kappa_mem i.1 t⟩ = (D.curves i.1).γ t := by
    intro i t
    set z : Work.InnermostDisk.Disc := ⟨(D.kappa i.1).γ t, D.kappa_mem i.1 t⟩ with hz
    have hfar : S.r ≤ Metric.infDist (z:ℂ) (Set.range (D.kappa S.i₀).γ) := by
      by_contra hcon
      push Not at hcon
      exact S.avoids i.1 i.2 (z:ℂ) hcon (by rw [hz]; exact ⟨t, rfl⟩)
    have hδ0 : deltaFun (S := S) z = 0 := deltaFun_eq_zero_of_far (S := S) hfar
    have hnotmem : (z:ℂ) ∉ Set.range S.hsch.e := by
      intro hmem
      exact Set.disjoint_left.mp (disjoint_trace_range (S := S) i.2)
        (by rw [hz]; exact ⟨t, rfl⟩) hmem
    rw [EMap_apply, hδ0, PD.hzero, phiMap_of_not_mem (S := S) hnotmem, hz]
    exact D.maps_kappa i.1 t
  -- The open disc misses `F` off the remaining traces.
  have hE_covers : ∀ z : Work.InnermostDisk.Disc, ‖(z:ℂ)‖ < 1 →
      EMap (S := S) β z ∈ (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier →
      ∃ (i : {j : D.ι // j ≠ S.i₀}) (t : ℝ), (D.kappa i.1).γ t = (z:ℂ) := by
    intro z hzlt hEcar
    have hlevE : PD.levP (EMap (S := S) β z) = 1 :=
      (PD.hlev (EMap (S := S) β z)).mpr hEcar
    by_cases hmem : (z:ℂ) ∈ Set.range S.hsch.e
    · exact absurd hlevE (hE_ne_one_mem z hmem hzlt)
    · by_cases hnear : Metric.infDist (z:ℂ) (Set.range (D.kappa S.i₀).γ) < S.r
      · exact absurd hlevE (hE_ne_one_out z hmem hzlt hnear)
      · have hδ0 : deltaFun (S := S) z = 0 :=
          deltaFun_eq_zero_of_far (S := S) (not_lt.mp hnear)
        have hDe : D.e z ∈ (Work.CoreTopology.ParamTorus.mapHomeomorph ψ).carrier := by
          apply (PD.hlev (D.e z)).mp
          have h1 : PD.levP (EMap (S := S) β z) = 1 := hlevE
          rwa [EMap_apply, hδ0, PD.hzero, phiMap_of_not_mem (S := S) hmem] at h1
        obtain ⟨i, t, ht⟩ := D.covers z hzlt hDe
        by_cases hi : i = S.i₀
        · exfalso
          subst hi
          have hrle : S.r ≤ Metric.infDist (z:ℂ) (Set.range (D.kappa S.i₀).γ) := not_lt.mp hnear
          have h0 : Metric.infDist (z:ℂ) (Set.range (D.kappa S.i₀).γ) = 0 := by
            have hle := Metric.infDist_le_dist_of_mem (x := (z:ℂ))
              (show (z:ℂ) ∈ Set.range (D.kappa S.i₀).γ from ⟨t, ht⟩)
            rw [dist_self] at hle
            linarith [Metric.infDist_nonneg (x := (z:ℂ)) (s := Set.range (D.kappa S.i₀).γ)]
          linarith [S.hr, hrle, h0]
        · exact ⟨⟨i, hi⟩, t, ht⟩
  -- The new weak datum.
  let D' : WeakDatum ψ :=
    { α := D.α
      e := ⟨EMap (S := S) β, hcontE⟩
      boundary := hE_bdry
      ι := {j : D.ι // j ≠ S.i₀}
      fintype := inferInstance
      kappa := fun i => D.kappa i.1
      kappa_simple := fun i => D.kappa_simple i.1
      kappa_disj := fun i j hij => D.kappa_disj (fun hc => hij (Subtype.ext hc))
      kappa_mem := fun i t => D.kappa_mem i.1 t
      curves := fun i => D.curves i.1
      curves_simple := fun i => D.curves_simple i.1
      curves_inessential := fun i => D.curves_inessential i.1
      maps_kappa := hE_maps
      covers := hE_covers }
  have hα : D'.α = D.α := rfl
  have hcard : Fintype.card D'.ι < Fintype.card D.ι := by
    have hcard1 : Fintype.card {j : D.ι // j = S.i₀} = 1 := Fintype.card_subtype_eq S.i₀
    have hc : Fintype.card D'.ι = Fintype.card D.ι - 1 := by
      have hcompl := Fintype.card_subtype_compl (fun j : D.ι => j = S.i₀)
      rw [hcard1] at hcompl
      exact hcompl
    rw [hc]; omega
  exact ⟨D', hα, hcard, fun i t => hint i.1 t⟩

end Work.Drive.SurgStrict
